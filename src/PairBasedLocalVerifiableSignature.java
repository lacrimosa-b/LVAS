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
        List<Element> coeffs = new ArrayList<>(l + 1);

        for (int i = 0; i < l + 1; i++) {
            Element elem = pairing.getZr().newElement();
            elem.setToZero();
            coeffs.add(elem);
        }

        coeffs.getFirst().setToOne();

        Element tmp = pairing.getZr().newElement();

        for (Element mi : messages) {
            int currentSize = coeffs.size();
            List<Element> newCoeffs = new ArrayList<>(currentSize + 1);

            for (int i = 0; i < currentSize + 1; i++) {
                Element elem = pairing.getZr().newElement();
                elem.setToZero();
                newCoeffs.add(elem);
            }


            for (int j = 0; j < currentSize; j++) {
                Element coeffJ = coeffs.get(j);
                newCoeffs.get(j + 1).add(coeffJ);
                tmp.set(mi);
                tmp.mul(coeffJ);
                newCoeffs.get(j).add(tmp);
            }

            coeffs = newCoeffs;
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
        return v1.equals(v2);
    }

    public static List<Element> CalculateCoeff2(int index, List<Element> messages) {
        int l = messages.size();
        List<Element> coeffs = new ArrayList<>(l);

        for (int i = 0; i < l; i++) {
            coeffs.add(pairing.getZr().newZeroElement());
        }

        coeffs.getFirst().setToOne();

        Element tmp = pairing.getZr().newElement();

        for (int i = 0; i < l; i++) {
            if (i != index) {
                List<Element> newCoeffs = new ArrayList<>(l);

                for (int j = 0; j < l; j++) {
                    newCoeffs.add(pairing.getZr().newZeroElement());
                }

                for (int j = 0; j < l - 1; j++) {
                    newCoeffs.get(j + 1).add(coeffs.get(j));
                    tmp.set(messages.get(i));
                    tmp.mul(coeffs.get(j));
                    newCoeffs.get(j).add(tmp);
                }

                coeffs = newCoeffs;
            }
        }
        return coeffs;
    }

    public static List<Element> LocalOpen(int index, List<Element> messages, List<Element> vk) {
        int l = messages.size();
        Element aux1 = pairing.getG1().newZeroElement(), aux2 = pairing.getG1().newZeroElement();
        List<Element> coeffs = CalculateCoeff2(index, messages);

        Element prod = pairing.getG1().newElement();
        Element tmp = pairing.getG1().newElement();

        Element generator = pairing.getG1().newElement().set(g);
        prod.set(generator).powZn(coeffs.getFirst());

        for (int i = 0; i < l - 1; i++) {
            tmp.set(vk.get(i)).powZn(coeffs.get(i + 1));
            prod.mul(tmp);
        }
        aux1.set(prod);

        prod.setToOne();
        for (int i = 0; i < l; i++) {
            tmp.set(vk.get(i)).powZn(coeffs.get(i));
            prod.mul(tmp);
        }
        aux2.set(prod);
        List<Element> aux = new ArrayList<>();
        aux.add(aux1);
        aux.add(aux2);
        return aux;
    }

    public static Boolean LocalAggVerify(Element signature, Element message, List<Element> vk, List<Element> aux) {

        Element v1 = pairing.getGT().newElement();
        Element v2 = pairing.getGT().newElement();
        Element tmp = pairing.getG1().newElement();

        Element generator = pairing.getG1().newElement().set(g);
        v1.set(pairing.pairing(generator, generator));

        tmp.set(aux.getFirst()).powZn(message).mul(aux.get(1));
        v2.set(pairing.pairing(signature, tmp));
        boolean b1 = v1.isEqual(v2);
        
        v1.set(pairing.pairing(vklocal, aux.getFirst()));
        v2.set(pairing.pairing(generator, aux.get(1)));
        boolean b2 = v1.isEqual(v2);

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
