import it.unisa.dia.gas.jpbc.Element;
import it.unisa.dia.gas.jpbc.Pairing;
import it.unisa.dia.gas.plaf.jpbc.pairing.PairingFactory;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class PairBasedLocalVerifiableSignature {
    private static Pairing pairing;
    private static Element g;
    private static Element alpha;
    public static Integer messageNum=10;
    private static Element vklocal;

//    public static Element Hash(String message) {
//
//    }

    public static List<Element> init() {
        pairing = PairingFactory.getPairing("params/curves/a.properties");
        g = pairing.getG1().newRandomElement();

        alpha = pairing.getZr().newRandomElement();

        List<Element> vk = new ArrayList<>();
        vk.add(pairing.getG1().newZeroElement());
        vklocal = pairing.getG1().newZeroElement();
        vk.getFirst().set(g);
        vk.getFirst().powZn(alpha);
        vklocal.set(vk.getFirst());
        for (int i = 1; i < messageNum; i++) {
            vk.add(pairing.getG1().newZeroElement());
            vk.get(i).add(vk.get(i - 1));
            vk.get(i).powZn(alpha);
        }
        return vk;
    }

    public static Element Sign(Element message) {
        Element tmp;
        tmp = pairing.getZr().newZeroElement();
        tmp.set(alpha);
        tmp.add(message);
        tmp.invert();
        Element signature = pairing.getG1().newRandomElement();
        signature.set(g);
        signature.powZn(tmp);
        return signature;
    }

    public static Boolean Verify(Element signature, Element message, List<Element> vk) {
        Element v1, v2, tmp;
        v1 = pairing.getGT().newZeroElement();
        v1.set(pairing.pairing(g, g));
        tmp = pairing.getG1().newZeroElement();
        tmp.set(g);
        tmp.powZn(message);
        tmp.mul(vk.getFirst());
        v2 = pairing.getGT().newZeroElement();
        v2.set(pairing.pairing(signature, tmp));
        return v1.equals(v2);
    }

    public static Element DPP(List<Element> signatures,Integer l, List<Element> messages) {
        Element tmp, tmp2;
        tmp = pairing.getZr().newZeroElement();
        tmp2 = pairing.getG1().newZeroElement();
        List<Element> Powers = new ArrayList<>();
        for (int i = 0; i < l; i++) {
            Powers.add(pairing.getG1().newRandomElement());
            Powers.get(i).set(signatures.get(i));
        }
        for (int i = 0; i < l - 1; i++) {
            for (int j = i + 1; j < l; j++) {
                if(i != j) {
                    tmp.set(messages.get(j));
                    tmp.sub(messages.get(i));
                    tmp.invert();
                    tmp2.set(Powers.get(i));
                    tmp2.sub(Powers.get(j));
                    Powers.get(j).set(tmp2);
                    Powers.get(j).powZn(tmp);
                }
            }
        }
        return Powers.get(l - 1);
    }

    public static Element Aggregate(List<Element> signatures, List<Element> messages, List<Element> vk) {
        int l = signatures.size();
        for (int i = 0; i < l; i++) {
            if (!Verify(signatures.get(i), messages.get(i), vk)) {
                return null;
            }
        }
        return DPP(signatures, l, messages);
    }

    public static List<Element> CalculateCoeff(List<Element> messages) {
        int l = messages.size();
        List<Element> coeffs = new ArrayList<>();
        Element tmp = pairing.getZr().newZeroElement();
        for (int i = 0; i < l + 1; i++) {
            coeffs.add(pairing.getZr().newZeroElement());
        }
        coeffs.getFirst().set(pairing.getZr().newOneElement());
        tmp.set(pairing.getZr().newZeroElement());

        for (int i = 0; i < l; i++) {
            List<Element> newCoeffs = new ArrayList<>();

            for (int j = 0; j < coeffs.size() + 1; j++) {
                newCoeffs.add(pairing.getZr().newZeroElement());
            }

            for (int j = 0; j < l + 1; j++) {
                newCoeffs.get(j + 1).add(coeffs.get(j));
                tmp.set(messages.get(i));
                tmp.mul(coeffs.get(j));
                newCoeffs.get(j).add(tmp);
            }
        }
        return coeffs;
    }

    public static List<Element> CalculateCoeff2(int index, List<Element> messages) {
        int l = messages.size();
        List<Element> coeffs = new ArrayList<>();
        Element tmp;
        for (int i = 0; i < l; i++) {
            coeffs.add(pairing.getZr().newZeroElement());
        }

        coeffs.getFirst().set(pairing.getZr().newOneElement());
        tmp = pairing.getZr().newZeroElement();

        for (int i = 0; i < l; i++) {
            if(index != i) {
                List<Element> newCoeffs = new ArrayList<>();
                for (int j = 0; j < l; j++) {
                    newCoeffs.add(pairing.getZr().newZeroElement());
                }

                for (int j = 0; j < l - 1; j++) {
                    newCoeffs.get(j + 1).add(coeffs.get(j));
                    tmp.set(messages.get(i));
                    tmp.mul(coeffs.get(j));
                    newCoeffs.get(j).add(tmp);
                }
            }
        }
        return coeffs;
    }

    public static Boolean AggVerify(Element signature, List<Element> messages, List<Element> vk) {
        int l = messages.size();
        List<Element> coeffs = CalculateCoeff(messages);
        Element tmp = pairing.getG1().newZeroElement(), prod = pairing.getG1().newZeroElement();
        prod.set(g);
        prod.powZn(coeffs.getFirst());
        for (int i = 0; i < l; i++) {
            tmp.set(vk.get(i));
            tmp.powZn(coeffs.get(i + 1));
            prod.mul(tmp);
        }
        Element v1 = pairing.getGT().newZeroElement(), v2 = pairing.getGT().newZeroElement();
        v1.set(pairing.pairing(g, g));
        v2.set(pairing.pairing(signature, prod));
        System.out.println(v1);
        System.out.println(v2);
        return v1.equals(v2);
    }

    public static List<Element> LocalOpen(int index, List<Element> messages, List<Element> vk) {
        int l = messages.size();
        List<Element> coeffs = CalculateCoeff2(index, messages);
        Element tmp, prod;
        List<Element> aux = new ArrayList<>();
        prod = g;
        prod.powZn(coeffs.getFirst());

        for (int i = 0; i < l - 1; i++) {
            tmp = vk.get(i);
            tmp.powZn(coeffs.get(i + 1));
            prod.mul(tmp);
        }

        aux.add(prod);
        prod.setToOne();
        for (int i = 0; i < l; i++) {
            tmp = vk.get(i);
            tmp.powZn(coeffs.get(i));
            prod.mul(tmp);
        }
        aux.add(prod);
        return aux;
    }

    public static Boolean LocalAggVerify(Element signature, Element message, List<Element> vk, List<Element> aux) {
        Element tmp, v1, v2;
        boolean b1, b2;
        v1 = pairing.pairing(g, g);
        v2 = pairing.getGT().newZeroElement();
        tmp = pairing.getG1().newZeroElement();
        tmp = aux.getFirst();
        tmp.powZn(message);
        tmp.mul(aux.get(1));
        v2 = pairing.pairing(signature, tmp);
        b1 = v1.equals(v2);

        v1 = pairing.pairing(vklocal, aux.getFirst());
        v2 = pairing.pairing(g, aux.get(1));
        b2 = v2.equals(v1);
        return b1 && b2;
    }

    public static Element seqaggsig(List<Element> messages) {
        return null;
    }

    public static String generateRandomString(int length) {
        String character = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
        Random rand = new Random();
        StringBuilder s = new StringBuilder(length);
        for (int i = 0; i < length; i++) {
            s.append(character.charAt(rand.nextInt(character.length())));
        }
        return s.toString();
    }

    public static void main(String[] args) {
        List<Element> vk = init();
        List<Element> mList = new ArrayList<>();
        for (int i = 0; i < messageNum; i++) {
            mList.add(pairing.getZr().newRandomElement());
        }

        long startTime = System.currentTimeMillis();
        List<Element> sigList = new ArrayList<>();
        for (int i = 0; i < messageNum; i++) {
            sigList.add(Sign(mList.get(i)));
        }
        System.out.println("Sign finished.");
        long endTime = System.currentTimeMillis();
        long executionTime = endTime - startTime;
        System.out.println("Sign time: " + executionTime + " ms\n");

        startTime = System.currentTimeMillis();
        for (int i = 0; i < messageNum; i++) {
            System.out.println("Verify result for message " + i + ":" + Verify(sigList.get(i), mList.get(i), vk));
        }
        System.out.println("Verify finished.");
        endTime = System.currentTimeMillis();
        executionTime = endTime - startTime;
        System.out.println("Verify time: " + executionTime + " ms\n");

        startTime = System.currentTimeMillis();
        Element aggsig = pairing.getG1().newOneElement();
        aggsig.set(Aggregate(sigList, mList, vk));
        System.out.println("Aggregate signature: " + aggsig);
        System.out.println("Aggregate finished.");
        endTime = System.currentTimeMillis();
        executionTime = endTime - startTime;
        System.out.println("Aggregate time: " + executionTime + " ms\n");

        startTime = System.currentTimeMillis();
        boolean isValid = AggVerify(aggsig, mList, vk);
        System.out.println("AggVerify result: " + isValid);
        System.out.println("AggVerify finished.");
        endTime = System.currentTimeMillis();
        executionTime = endTime - startTime;
        System.out.println("AggVerify time: " + executionTime + " ms\n");

        startTime = System.currentTimeMillis();
        List<List<Element>> aux = new ArrayList<>();
        for (int i = 0; i < messageNum; i++) {
            aux.add(LocalOpen(i, mList, vk));
        }
        System.out.println("LocalOpen finished.");
        endTime = System.currentTimeMillis();
        executionTime = endTime - startTime;
        System.out.println("LocalOpen time: " + executionTime + " ms\n");

        startTime = System.currentTimeMillis();
        for (int i = 0; i < messageNum; i++) {
            System.out.println("LocalAggVerify result for message " + i + ":" + LocalAggVerify(aggsig, mList.get(i), vk, aux.get(i)));
        }
        System.out.println("LocalAggVerify finished.");
        endTime = System.currentTimeMillis();
        executionTime = endTime - startTime;
        System.out.println("LocalAggVerify time: " + executionTime + " ms\n");
    }
}
