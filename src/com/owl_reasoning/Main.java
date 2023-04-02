package com.owl_reasoning;

import com.opencsv.CSVReader;
import com.opencsv.CSVWriter;
import org.jfree.chart.ChartFactory;
import org.jfree.chart.ChartUtilities;
import org.jfree.chart.JFreeChart;
import org.jfree.chart.block.BlockBorder;
import org.jfree.chart.plot.PlotOrientation;
import org.jfree.chart.plot.XYPlot;
import org.jfree.chart.renderer.xy.XYLineAndShapeRenderer;
import org.jfree.chart.title.TextTitle;
import org.jfree.data.xy.XYDataset;
import org.jfree.data.xy.XYSeries;
import org.jfree.data.xy.XYSeriesCollection;
import java.awt.BasicStroke;
import java.awt.Color;
import java.awt.Font;
import openllet.owlapi.OpenlletReasonerFactory;
import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.*;
import uk.ac.manchester.cs.jfact.JFactFactory;

import java.io.*;
import java.lang.management.ManagementFactory;
import java.lang.management.MemoryMXBean;
import java.math.BigDecimal;
import java.math.RoundingMode;
import java.text.DecimalFormat;
import java.text.ParseException;
import java.util.*;
import java.util.stream.Stream;


public class Main{
    static OWLOntologyManager ontologyManager;
    static OWLOntology ontology;
    static OWLDataFactory df;
    static TreeMap<String, double[]> times = new TreeMap<>();


    public static double getProcessCpuLoad(){
        return ManagementFactory.getPlatformMXBean(com.sun.management.OperatingSystemMXBean.class).getCpuLoad();
    }

    public static OWLOntology generateOntology(int n, int m) throws OWLOntologyCreationException {
        Random rand = new Random();
        OWLOntology o = ontologyManager.createOntology();
        // creating all the classes
        for (int i=0; i<n; i++){
            OWLClass c = df.getOWLClass(IRI.create("#Class" + i));
            OWLAxiom declareC = df.getOWLDeclarationAxiom(c);
            // adding declareC to the ontology is necessary to have any output
            AddAxiom addAxiom = new AddAxiom(o, declareC);
            ontologyManager.applyChange(addAxiom);
        }
        // creating subclasses
        for (int i=0; i<Math.floor(n/5); i++) {
            int B = rand.nextInt(n);
            while (B == i) {
                B = rand.nextInt(n);
            }
            OWLClass clsA = df.getOWLClass("#Class" + i);
            OWLClass clsB = df.getOWLClass("#Class" + B);
            //A child, B parent
            OWLAxiom axiom = df.getOWLSubClassOfAxiom(clsA, clsB);
            AddAxiom addAxiom = new AddAxiom(o, axiom);
            ontologyManager.applyChange(addAxiom);
        }
        // creating equivalent
        for (int i=0; i<Math.floor(n/10); i++) {
            int A = rand.nextInt(n);
            int B = rand.nextInt(n);
            while (B == A) {
                B = rand.nextInt(n);
            }
            OWLClass clsA = df.getOWLClass("#Class" + A);
            OWLClass clsB = df.getOWLClass("#Class" + B);
            OWLAxiom axiom = df.getOWLEquivalentClassesAxiom(clsA, clsB);
            AddAxiom addAxiom = new AddAxiom(o, axiom);
            ontologyManager.applyChange(addAxiom);
        }

        // creating individuals
        for (int i=0; i<m; i++){
            int A = i%n;
            OWLClass cls = df.getOWLClass("#Class" + A);
            OWLNamedIndividual individual = df.getOWLNamedIndividual(IRI.create("#Individual" + i));
            OWLAxiom declareI = df.getOWLDeclarationAxiom(individual);
            AddAxiom addDeclaration = new AddAxiom(o, declareI);
            ontologyManager.applyChange(addDeclaration);
            OWLClassAssertionAxiom axiom = df.getOWLClassAssertionAxiom(cls, individual);
            AddAxiom addAxiom = new AddAxiom(o, axiom);
            ontologyManager.applyChange(addAxiom);
        }
        for (int i=0; i<Math.floor(m/2); i++){
            int A = rand.nextInt(m);
            int B = rand.nextInt(m);
            while (B == A) {
                B = rand.nextInt(m);
            }
            OWLIndividual individualA = df.getOWLNamedIndividual("#Individual" + A);
            OWLIndividual individualB = df.getOWLNamedIndividual("#Individual" + B);
            OWLAxiom axiom = df.getOWLDifferentIndividualsAxiom(individualA, individualB);
            AddAxiom addAxiom = new AddAxiom(o, axiom);
            ontologyManager.applyChange(addAxiom);
        }

        for (int i=0; i<Math.floor(m/5); i++) {
            OWLObjectProperty op = df.getOWLObjectProperty(IRI.create("#Property " + i));
            OWLAxiom declare = df.getOWLDeclarationAxiom(op);
            AddAxiom addAxiom = new AddAxiom(o, declare);
            ontologyManager.applyChange(addAxiom);
            OWLObjectPropertyDomainAxiom da = df.getOWLObjectPropertyDomainAxiom(op, df.getOWLClass("#Class" + rand.nextInt(n)));
            addAxiom = new AddAxiom(o, da);
            ontologyManager.applyChange(addAxiom);
            OWLObjectPropertyRangeAxiom ra = df.getOWLObjectPropertyRangeAxiom(op, df.getOWLClass("#Class" + rand.nextInt(n)));
            addAxiom = new AddAxiom(o, ra);
            ontologyManager.applyChange(addAxiom);
        }
        for (int i=0; i<m; i++) {
            int A = rand.nextInt((int)Math.floor(m/5));
            OWLObjectPropertyAssertionAxiom axiom = df.getOWLObjectPropertyAssertionAxiom(df.getOWLObjectProperty("#Property " + A), df.getOWLNamedIndividual("#Individual" + m), df.getOWLNamedIndividual(df.getOWLClass("#Individual" + rand.nextInt(m))));
            AddAxiom addAxiom = new AddAxiom(o, axiom);
            ontologyManager.applyChange(addAxiom);
        }
        return o;
    }

    public static OWLOntology[] getBoxes(OWLOntology ontology) throws OWLOntologyCreationException {
        OWLOntology[] boxes = new OWLOntology[2];
        OWLOntology ABox;
        OWLOntology TBox;
        ABox = ontologyManager.createOntology();
        TBox = ontologyManager.createOntology();
        Set<OWLAxiom> ABoxAxioms = ontology.getABoxAxioms(Imports.INCLUDED);
        Set<OWLAxiom> TBoxAxioms = ontology.getTBoxAxioms(Imports.INCLUDED);
        Object[] axiomsArrayA = ABoxAxioms.toArray();
        Object[] axiomsArrayT = TBoxAxioms.toArray();
        for (int i=0; i<ABoxAxioms.size(); i++){
            Object axiom = axiomsArrayA[i];
            OWLAxiom owlAxiom = (OWLAxiom) axiom;
            ABox.add(owlAxiom);
        }
        for (int i=0; i<TBoxAxioms.size(); i++){
            Object axiom = axiomsArrayT[i];
            OWLAxiom owlAxiom = (OWLAxiom) axiom;
            TBox.add(owlAxiom);
        }
        boxes[0] = ABox;
        boxes[1] = TBox;
        return boxes;
    }

    public static double[] isSatisfiable(OWLReasoner reasoner, OWLOntology owlOntology) {
        Stream<OWLClass> classes = owlOntology.classesInSignature();
        List<OWLClass> classesList = classes.toList();
        long tic = System.currentTimeMillis();
        for (int c=0; c<classesList.size(); c++){
            reasoner.isSatisfiable(classesList.get(c));
        }
        long toc = System.currentTimeMillis();
        long executionTime = toc - tic;
        return new double[]{executionTime, 100*Runtime.getRuntime().totalMemory()/Runtime.getRuntime().maxMemory(), getProcessCpuLoad()};
    }

    public static double[] classify(OWLReasoner reasoner){
        long tic = System.currentTimeMillis();
        reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
        long toc = System.currentTimeMillis();
        long executionTime = toc - tic;
        return new double[]{executionTime, 100*Runtime.getRuntime().totalMemory()/Runtime.getRuntime().maxMemory(), getProcessCpuLoad()};
    }

    public static double[] isConsistent(OWLReasoner reasoner){
        long tic = System.nanoTime();
        reasoner.isConsistent();
        long toc = System.nanoTime();
        long executionTime = toc - tic;
        return new double[]{executionTime/1000, 100*Runtime.getRuntime().totalMemory()/Runtime.getRuntime().maxMemory(), getProcessCpuLoad()};
    }

    public static double[] instanceChecking(OWLReasoner reasoner, OWLAxiom axiom){
        long tic = System.currentTimeMillis();
        reasoner.isEntailed(axiom);
        long toc = System.currentTimeMillis();
        long executionTime = toc - tic;
        return new double[]{executionTime, 100*Runtime.getRuntime().totalMemory()/Runtime.getRuntime().maxMemory(), getProcessCpuLoad()};
    }

    private static JFreeChart createChart(final XYDataset dataset, String title, String yAxis) {

        JFreeChart chart = ChartFactory.createXYLineChart(
                "OWL reasoners comparison",
                "Classes",
                yAxis,
                dataset,
                PlotOrientation.VERTICAL,
                true,
                true,
                false
        );

        XYPlot plot = chart.getXYPlot();

        var renderer = new XYLineAndShapeRenderer();

        renderer.setSeriesPaint(0, Color.RED);
        renderer.setSeriesStroke(0, new BasicStroke(2.0f));
        renderer.setSeriesPaint(1, Color.BLUE);
        renderer.setSeriesStroke(1, new BasicStroke(2.0f));
        renderer.setSeriesPaint(2, Color.GREEN);
        renderer.setSeriesStroke(2, new BasicStroke(2.0f));
        renderer.setSeriesPaint(3, Color.DARK_GRAY);
        renderer.setSeriesStroke(3, new BasicStroke(2.0f));

        plot.setRenderer(renderer);
        plot.setBackgroundPaint(Color.white);
        plot.setRangeGridlinesVisible(false);
        plot.setDomainGridlinesVisible(false);

        chart.getLegend().setFrame(BlockBorder.NONE);

        chart.setTitle(new TextTitle(title,
                        new Font("Serif", Font.BOLD, 18)
                )
        );

        return chart;
    }

    /*public static void writeData(CSVWriter writer, double[] data){
        // add data to csv
        String[] data_i = new String[]{ String.valueOf(data[0]), String.valueOf(data[1]), String.valueOf(data[2])};
        writer.writeNext(data_i);
    }

    public static double[] readData(File file, int iterations, int reps, String type, String r_type) throws IOException{
        System.out.println(iterations + ", " + reps );
        FileReader fr = new FileReader(file);
        BufferedReader br = new BufferedReader(fr);
        double[] d = new double[]{0, 0, 0};
        int step = -3;
        switch (type){
            case "Satisfiability KB":
                step = 0;
                break;
            case "Classify KB":
                step = 1;
                break;
            case "Consistency":
                step = 2;
                break;
            case "Instance Checking":
                step = 3;
                break;
            case "Satisfiability TBox":
                step = 4;
                break;
            case "Classify TBox":
                step = 5;
                break;
            default:
                System.out.println("ERROR 1");
                break;
        }
        int reasoner = -3;
        switch (r_type){
            case "HermiT":
                reasoner = 1;
                break;
            case "Pellet":
                reasoner = 2;
                break;
            case "JFact":
                reasoner = 3;
                break;
            case "ELK":
                reasoner = 4;
                break;
            default:
                System.out.println("ERROR 2");
                break;
        }
        String line = "";
        String[] tempArr;
        for (int i = 0; i<iterations*reps*4*6; i++){
            line = br.readLine();
        }
        int iterator = iterations*reps*4*6;
        if (iterator<(iterations+1)*reps*4*6){
            for (int i = 0; i<step+reasoner; i++){
                line = br.readLine();
                iterator++;
            }
            if(line != null) {
                tempArr = line.split(",");
                int j = 0;
                for (String tempStr : tempArr) {
                    String result = tempStr.replaceAll("\"", "");
                    double value = Double.parseDouble(result);
                    d[j] += value;
                    j++;
                }
            }
            line = br.readLine();
            iterator++;
            if (line != null){
                for (int i = 0; i<24-step-reasoner; i++){
                    line = br.readLine();
                    iterator++;
                }
            }
        }
        for (int l=0; l<d.length; l++){
            d[l] = d[l]/reps;
        }
        br.close();
        fr.close();
        return d;
    }

     */



    public static void main(String[] args) {
        try{
            PrintStream dummyStream = new PrintStream(new OutputStream(){
                public void write(int b) {
                    // NO-OP
                }
            });
            System.setOut(dummyStream);
            //File file = new File("C:/Users/user/IdeaProjects/OWLreasoners/out.csv");
            //FileWriter outputfile = new FileWriter(file);

            OWLReasonerFactory reasonerFactoryHermit = new ReasonerFactory();
            OWLReasoner reasonerH;
            OWLReasonerFactory reasonerFactoryPellet = new OpenlletReasonerFactory();
            OWLReasoner reasonerP;
            OWLReasonerFactory reasonerFactoryJFact = new JFactFactory();
            OWLReasoner reasonerJ;
            OWLReasonerFactory reasonerFactoryELK = new ElkReasonerFactory();
            OWLReasoner reasonerE;

            ontologyManager = OWLManager.createOWLOntologyManager();
            df = ontologyManager.getOWLDataFactory();
            int iterations = 5;
            int step = 5000;
            int reps = 1;

            int m = 1000;
            double[] consistent;
            double[] satisfiable;
            double[] classified;
            double[] instanceChecked;

            for (int k = step; k < step*iterations+1; k += step){
                for (int ont=0; ont<2; ont++) {
                    double d = 0;
                    double[] init = new double[]{d, d, d};
                    times.put(ont + " HermiT classify " + k, init);
                    times.put(ont + " Pellet classify " + k, init);
                    times.put(ont + " JFact classify " + k, init);
                    times.put(ont + " ELK classify " + k, init);

                    times.put(ont + " HermiT satisfiable " + k, init);
                    times.put(ont + " Pellet satisfiable " + k, init);
                    times.put(ont + " JFact satisfiable " + k, init);
                    times.put(ont + " ELK satisfiable " + k, init);

                    if (ont == 0){
                        times.put(ont + " ELK consistency " + k, init);
                        times.put(ont + " HermiT consistency " + k, init);
                        times.put(ont + " Pellet consistency " + k, init);
                        times.put(ont + " JFact consistency " + k, init);

                        times.put(ont + " HermiT instance checking " + k, init);
                        times.put(ont + " Pellet instance checking " + k, init);
                        times.put(ont + " JFact instance checking " + k, init);
                        times.put(ont + " ELK instance checking " + k, init);
                    }
                }
            }

            //CSVWriter writer = new CSVWriter(outputfile);
            for (int rep=0; rep<reps; rep++){
                int n = 0;
                for (int i=0; i<iterations; i++){
                    n += step;
                    ontology = generateOntology(n, m);
                    //ontology = generateOntology(n, (int)Math.floor(n/10));
                    //System.out.println("getAxioms() " + ontology.getAxiomCount());
                    OWLOntology[] boxes = new OWLOntology[2];
                    OWLOntology[] ATboxes = getBoxes(ontology);
                    boxes[0] = ontology;
                    boxes[1] = ATboxes[1]; //TBOX
                    //System.out.println("getAxioms() tbox " + boxes[1].getAxiomCount());
                    for (int ont=0; ont<2; ont++) {
                        reasonerH = reasonerFactoryHermit.createReasoner(boxes[ont]);
                        reasonerP = reasonerFactoryPellet.createReasoner(boxes[ont]);
                        reasonerJ = reasonerFactoryJFact.createReasoner(boxes[ont]);
                        reasonerE = reasonerFactoryELK.createReasoner(boxes[ont]);

                        if (ont != 2) {
                            satisfiable = isSatisfiable(reasonerH, boxes[ont]);
                            //writeData(writer, satisfiable);
                            for (int r=0; r<satisfiable.length; r++){
                                satisfiable[r] += times.get(ont + " HermiT satisfiable " + n)[r];
                                System.out.println("AAA" + satisfiable[r]);
                            }
                            times.put(ont + " HermiT satisfiable " + n, satisfiable);
                            satisfiable = isSatisfiable(reasonerP, boxes[ont]);
                            //writeData(writer, satisfiable);
                            for (int r=0; r<satisfiable.length; r++){
                                satisfiable[r] += times.get(ont + " Pellet satisfiable " + n)[r];
                            }
                            times.put(ont + " Pellet satisfiable " + n, satisfiable);
                            satisfiable = isSatisfiable(reasonerJ, boxes[ont]);
                            //writeData(writer, satisfiable);
                            for (int r=0; r<satisfiable.length; r++){
                                satisfiable[r] += times.get(ont + " JFact satisfiable " + n)[r];
                            }
                            times.put(ont + " JFact satisfiable " + n, satisfiable);
                            satisfiable = isSatisfiable(reasonerE, boxes[ont]);
                            //writeData(writer, satisfiable);
                            for (int r=0; r<satisfiable.length; r++){
                                satisfiable[r] += times.get(ont + " ELK satisfiable " + n)[r];
                            }
                            times.put(ont + " ELK satisfiable " + n, satisfiable);

                            classified = classify(reasonerH);
                            //writeData(writer, classified);
                            for (int r=0; r<classified.length; r++){
                                classified[r] += times.get(ont + " HermiT classify " + n)[r];
                            }
                            times.put(ont + " HermiT classify " + n, classified);
                            classified = classify(reasonerP);
                            //writeData(writer, classified);
                            for (int r=0; r<classified.length; r++){
                                classified[r] += times.get(ont + " Pellet classify " + n)[r];
                            }
                            times.put(ont + " Pellet classify " + n, classified);
                            classified = classify(reasonerJ);
                            //writeData(writer, classified);
                            for (int r=0; r<classified.length; r++){
                                classified[r] += times.get(ont + " JFact classify " + n)[r];
                            }
                            times.put(ont + " JFact classify " + n, classified);
                            classified = classify(reasonerE);
                            //writeData(writer, classified);
                            for (int r=0; r<classified.length; r++){
                                classified[r] += times.get(ont + " ELK classify " + n)[r];
                            }
                            times.put(ont + " ELK classify " + n, classified);
                        }
                        if (ont == 0){
                            consistent = isConsistent(reasonerH);
                            //writeData(writer, consistent);
                            for (int r=0; r<consistent.length; r++){
                                consistent[r] += times.get(ont + " HermiT consistency " + n)[r];
                            }
                            times.put(ont + " HermiT consistency " + n, consistent);
                            consistent = isConsistent(reasonerP);
                            //writeData(writer, consistent);
                            for (int r=0; r<consistent.length; r++){
                                consistent[r] += times.get(ont + " Pellet consistency " + n)[r];
                            }
                            times.put(ont + " Pellet consistency " + n, consistent);
                            consistent = isConsistent(reasonerJ);
                            //writeData(writer, consistent);
                            for (int r=0; r<consistent.length; r++){
                                consistent[r] += times.get(ont + " JFact consistency " + n)[r];
                            }
                            times.put(ont + " JFact consistency " + n, consistent);
                            consistent = isConsistent(reasonerE);
                            //writeData(writer, consistent);
                            for (int r=0; r<consistent.length; r++){
                                consistent[r] += times.get(ont + " ELK consistency " + n)[r];
                            }
                            times.put(ont + " ELK consistency " + n, consistent);
                            Random rnd = new Random();
                            rnd.setSeed(rep);
                            int A = rnd.nextInt(n);
                            int B = rnd. nextInt(m);
                            //int B = rnd. nextInt((int)Math.floor(n/10));
                            OWLClass cls = df.getOWLClass("#Class" + A);
                            OWLNamedIndividual individual = df.getOWLNamedIndividual("#Individual" + B);
                            OWLAxiom axiom =  df.getOWLClassAssertionAxiom(cls, individual);
                            instanceChecked = instanceChecking(reasonerH, axiom);
                            //writeData(writer, instanceChecked);
                            for (int r=0; r<instanceChecked.length; r++){
                                instanceChecked[r] += times.get(ont + " HermiT instance checking " + n)[r];
                            }
                            times.put(ont + " HermiT instance checking " + n, instanceChecked);
                            instanceChecked = instanceChecking(reasonerP, axiom);
                            //writeData(writer, instanceChecked);
                            for (int r=0; r<instanceChecked.length; r++){
                                instanceChecked[r] += times.get(ont + " Pellet instance checking " + n)[r];
                            }
                            times.put(ont + " Pellet instance checking " + n, instanceChecked);
                            instanceChecked = instanceChecking(reasonerH, axiom);
                            //writeData(writer, instanceChecked);
                            for (int r=0; r<instanceChecked.length; r++){
                                instanceChecked[r] += times.get(ont + " JFact instance checking " + n)[r];
                            }
                            times.put(ont + " JFact instance checking " + n, instanceChecked);
                            instanceChecked = instanceChecking(reasonerH, axiom);
                            //writeData(writer, instanceChecked);
                            for (int r=0; r<instanceChecked.length; r++){
                                instanceChecked[r] += times.get(ont + " ELK instance checking " + n)[r];
                            }
                            times.put(ont + " ELK instance checking " + n, instanceChecked);
                        }
                    }
                }
            }
            //writer.close();
            var seriesHermitCons = new XYSeries("Hermit");
            var seriesPelletCons = new XYSeries("Pellet");
            var seriesJFactCons = new XYSeries("JFact");
            var seriesELKCons = new XYSeries("ELK");
            var seriesHermitSat = new XYSeries("Hermit");
            var seriesPelletSat = new XYSeries("Pellet");
            var seriesJFactSat = new XYSeries("JFact");
            var seriesELKSat = new XYSeries("ELK");
            var seriesHermitCla = new XYSeries("Hermit");
            var seriesPelletCla = new XYSeries("Pellet");
            var seriesJFactCla = new XYSeries("JFact");
            var seriesELKCla = new XYSeries("ELK");
            var seriesHermitIC = new XYSeries("Hermit");
            var seriesPelletIC = new XYSeries("Pellet");
            var seriesJFactIC = new XYSeries("JFact");
            var seriesELKIC = new XYSeries("ELK");

            var seriesHermitConsMemory = new XYSeries("Hermit");
            var seriesPelletConsMemory = new XYSeries("Pellet");
            var seriesJFactConsMemory = new XYSeries("JFact");
            var seriesELKConsMemory = new XYSeries("ELK");
            var seriesHermitSatMemory = new XYSeries("Hermit");
            var seriesPelletSatMemory = new XYSeries("Pellet");
            var seriesJFactSatMemory = new XYSeries("JFact");
            var seriesELKSatMemory = new XYSeries("ELK");
            var seriesHermitClaMemory = new XYSeries("Hermit");
            var seriesPelletClaMemory = new XYSeries("Pellet");
            var seriesJFactClaMemory = new XYSeries("JFact");
            var seriesELKClaMemory = new XYSeries("ELK");
            var seriesHermitICMemory = new XYSeries("Hermit");
            var seriesPelletICMemory = new XYSeries("Pellet");
            var seriesJFactICMemory = new XYSeries("JFact");
            var seriesELKICMemory = new XYSeries("ELK");

            var seriesHermitConsCPU = new XYSeries("Hermit");
            var seriesPelletConsCPU = new XYSeries("Pellet");
            var seriesJFactConsCPU = new XYSeries("JFact");
            var seriesELKConsCPU = new XYSeries("ELK");
            var seriesHermitSatCPU = new XYSeries("Hermit");
            var seriesPelletSatCPU = new XYSeries("Pellet");
            var seriesJFactSatCPU = new XYSeries("JFact");
            var seriesELKSatCPU = new XYSeries("ELK");
            var seriesHermitClaCPU = new XYSeries("Hermit");
            var seriesPelletClaCPU = new XYSeries("Pellet");
            var seriesJFactClaCPU = new XYSeries("JFact");
            var seriesELKClaCPU = new XYSeries("ELK");
            var seriesHermitICCPU = new XYSeries("Hermit");
            var seriesPelletICCPU = new XYSeries("Pellet");
            var seriesJFactICCPU = new XYSeries("JFact");
            var seriesELKICCPU = new XYSeries("ELK");

            for (int ont=0; ont<2; ont++) {
                int n = 0;
                seriesHermitCons.clear();
                seriesPelletCons.clear();
                seriesJFactCons.clear();
                seriesELKCons.clear();
                seriesHermitSat.clear();
                seriesPelletSat.clear();
                seriesJFactSat.clear();
                seriesELKSat.clear();
                seriesHermitCla.clear();
                seriesPelletCla.clear();
                seriesJFactCla.clear();
                seriesELKCla.clear();
                seriesHermitIC.clear();
                seriesPelletIC.clear();
                seriesJFactIC.clear();
                seriesELKIC.clear();
                seriesHermitConsMemory.clear();
                seriesPelletConsMemory.clear();
                seriesJFactConsMemory.clear();
                seriesELKConsMemory.clear();
                seriesHermitSatMemory.clear();
                seriesPelletSatMemory.clear();
                seriesJFactSatMemory.clear();
                seriesELKSatMemory.clear();
                seriesHermitClaMemory.clear();
                seriesPelletClaMemory.clear();
                seriesJFactClaMemory.clear();
                seriesELKClaMemory.clear();
                seriesHermitICMemory.clear();
                seriesPelletICMemory.clear();
                seriesJFactICMemory.clear();
                seriesELKICMemory.clear();
                seriesHermitConsCPU.clear();
                seriesPelletConsCPU.clear();
                seriesJFactConsCPU.clear();
                seriesELKConsCPU.clear();
                seriesHermitSatCPU.clear();
                seriesPelletSatCPU.clear();
                seriesJFactSatCPU.clear();
                seriesELKSatCPU.clear();
                seriesHermitClaCPU.clear();
                seriesPelletClaCPU.clear();
                seriesJFactClaCPU.clear();
                seriesELKClaCPU.clear();
                seriesHermitICCPU.clear();
                seriesPelletICCPU.clear();
                seriesJFactICCPU.clear();
                seriesELKICCPU.clear();
                /*
                var seriesHermitCons2 = new XYSeries("Hermit");
                var seriesPelletCons2 = new XYSeries("Pellet");
                var seriesJFactCons2 = new XYSeries("JFact");
                var seriesELKCons2 = new XYSeries("ELK");
                var seriesHermitSat2 = new XYSeries("Hermit");
                var seriesPelletSat2 = new XYSeries("Pellet");
                var seriesJFactSat2 = new XYSeries("JFact");
                var seriesELKSat2 = new XYSeries("ELK");
                var seriesHermitCla2 = new XYSeries("Hermit");
                var seriesPelletCla2 = new XYSeries("Pellet");
                var seriesJFactCla2 = new XYSeries("JFact");
                var seriesELKCla2 = new XYSeries("ELK");
                var seriesHermitIC2 = new XYSeries("Hermit");
                var seriesPelletIC2 = new XYSeries("Pellet");
                var seriesJFactIC2 = new XYSeries("JFact");
                var seriesELKIC2 = new XYSeries("ELK");

                var seriesHermitConsMemory2 = new XYSeries("Hermit");
                var seriesPelletConsMemory2 = new XYSeries("Pellet");
                var seriesJFactConsMemory2 = new XYSeries("JFact");
                var seriesELKConsMemory2 = new XYSeries("ELK");
                var seriesHermitSatMemory2 = new XYSeries("Hermit");
                var seriesPelletSatMemory2 = new XYSeries("Pellet");
                var seriesJFactSatMemory2 = new XYSeries("JFact");
                var seriesELKSatMemory2 = new XYSeries("ELK");
                var seriesHermitClaMemory2 = new XYSeries("Hermit");
                var seriesPelletClaMemory2 = new XYSeries("Pellet");
                var seriesJFactClaMemory2 = new XYSeries("JFact");
                var seriesELKClaMemory2 = new XYSeries("ELK");
                var seriesHermitICMemory2 = new XYSeries("Hermit");
                var seriesPelletICMemory2 = new XYSeries("Pellet");
                var seriesJFactICMemory2 = new XYSeries("JFact");
                var seriesELKICMemory2 = new XYSeries("ELK");

                var seriesHermitConsCPU2 = new XYSeries("Hermit");
                var seriesPelletConsCPU2 = new XYSeries("Pellet");
                var seriesJFactConsCPU2 = new XYSeries("JFact");
                var seriesELKConsCPU2 = new XYSeries("ELK");
                var seriesHermitSatCPU2 = new XYSeries("Hermit");
                var seriesPelletSatCPU2 = new XYSeries("Pellet");
                var seriesJFactSatCPU2 = new XYSeries("JFact");
                var seriesELKSatCPU2 = new XYSeries("ELK");
                var seriesHermitClaCPU2 = new XYSeries("Hermit");
                var seriesPelletClaCPU2 = new XYSeries("Pellet");
                var seriesJFactClaCPU2 = new XYSeries("JFact");
                var seriesELKClaCPU2 = new XYSeries("ELK");
                var seriesHermitICCPU2 = new XYSeries("Hermit");
                var seriesPelletICCPU2 = new XYSeries("Pellet");
                var seriesJFactICCPU2 = new XYSeries("JFact");
                var seriesELKICCPU2 = new XYSeries("ELK");

                for (int i=0; i<iterations; i++) {
                    n += step;
                    String title = null;
                    switch (ont){
                        case 0:
                            title = "KB";
                            break;
                        case 1:
                            title = "TBox";
                            break;
                        case 2:
                            title = "ABox";
                            break;
                    }

 */
                for (int i = 0; i< iterations; i++){
                    n += step;
                    if (ont != 2) {
                        satisfiable = times.get(ont + " HermiT satisfiable " + n);
                        System.out.println(times.get(ont + " HermiT satisfiable " + n)[0]);
                        seriesHermitSat.add(n, satisfiable[0] / reps);
                        seriesHermitSatMemory.add(n, satisfiable[1] / reps);
                        seriesHermitSatCPU.add(n, satisfiable[2] * 100 / reps);

                        satisfiable = times.get(ont + " Pellet satisfiable " + n);
                        seriesPelletSat.add(n, satisfiable[0] / reps);
                        seriesPelletSatMemory.add(n, satisfiable[1] / reps);
                        seriesPelletSatCPU.add(n, satisfiable[2] * 100 / reps);

                        satisfiable = times.get(ont + " JFact satisfiable " + n);
                        seriesJFactSat.add(n, satisfiable[0] / reps);
                        seriesJFactSatMemory.add(n, satisfiable[1] / reps);
                        seriesJFactSatCPU.add(n, satisfiable[2] * 100 / reps);

                        satisfiable = times.get(ont + " ELK satisfiable " + n);
                        seriesELKSat.add(n, satisfiable[0] / reps);
                        seriesELKSatMemory.add(n, satisfiable[1] / reps);
                        seriesELKSatCPU.add(n, satisfiable[2] * 100 / reps);


                        classified = times.get(ont + " HermiT classify " + n);
                        seriesHermitCla.add(n, classified[0] / reps);
                        seriesHermitClaMemory.add(n, classified[1] / reps);
                        seriesHermitClaCPU.add(n, classified[2] * 100 / reps);

                        classified = times.get(ont + " Pellet classify " + n);
                        seriesPelletCla.add(n, classified[0] / reps);
                        seriesPelletClaMemory.add(n, classified[1] / reps);
                        seriesPelletClaCPU.add(n, classified[2] * 100 / reps);

                        classified = times.get(ont + " JFact classify " + n);
                        seriesJFactCla.add(n, classified[0] / reps);
                        seriesJFactClaMemory.add(n, classified[1] / reps);
                        seriesJFactClaCPU.add(n, classified[2] * 100 / reps);

                        classified = times.get(ont + " ELK classify " + n);
                        seriesELKCla.add(n, classified[0] / reps);
                        seriesELKClaMemory.add(n, classified[1] / reps);
                        seriesELKClaCPU.add(n, classified[2] * 100 / reps);

    /*


                        satisfiable = readData(file, n/step -1, reps, "Satisfiability " + title, "HermiT");
                        seriesHermitSat2.add(n, satisfiable[0]);
                        seriesHermitSatMemory2.add(n, (new BigDecimal(satisfiable[1])).setScale(2, RoundingMode.HALF_DOWN));
                        seriesHermitSatCPU2.add(n, (new BigDecimal(satisfiable[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

                        satisfiable = readData(file, n/step -1, reps, "Satisfiability " + title, "Pellet");
                        seriesPelletSat2.add(n, satisfiable[0]);
                        seriesPelletSatMemory2.add(n, (new BigDecimal(satisfiable[1])).setScale(2, RoundingMode.HALF_DOWN));
                        seriesPelletSatCPU2.add(n, (new BigDecimal(satisfiable[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

                        satisfiable = readData(file, n/step -1, reps, "Satisfiability " + title, "JFact");
                        seriesJFactSat.add(n, satisfiable[0]);
                        seriesJFactSatMemory.add(n, (new BigDecimal(satisfiable[1])).setScale(2, RoundingMode.HALF_DOWN));
                        seriesJFactSatCPU.add(n, (new BigDecimal(satisfiable[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

                        satisfiable = readData(file, n/step -1, reps, "Satisfiability " + title, "ELK");
                        seriesELKSat.add(n, satisfiable[0]);
                        seriesELKSatMemory.add(n, (new BigDecimal(satisfiable[1])).setScale(2, RoundingMode.HALF_DOWN));
                        seriesELKSatCPU.add(n, (new BigDecimal(satisfiable[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

                        classified = readData(file, n/step -1, reps, "Classify " + title, "HermiT");
                        seriesHermitCla.add(n, classified[0]);
                        seriesHermitClaMemory.add(n, (new BigDecimal(classified[1])).setScale(2, RoundingMode.HALF_DOWN));
                        seriesHermitClaCPU.add(n, (new BigDecimal(classified[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

                        classified = readData(file, n/step -1, reps, "Classify " + title, "Pellet");
                        seriesPelletCla.add(n, classified[0]);
                        seriesPelletClaMemory.add(n, (new BigDecimal(classified[1])).setScale(2, RoundingMode.HALF_DOWN));
                        seriesPelletClaCPU.add(n, (new BigDecimal(classified[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

                        classified = readData(file, n/step -1, reps, "Classify " + title, "JFact");
                        seriesJFactCla.add(n, classified[0]);
                        seriesJFactClaMemory.add(n, (new BigDecimal(classified[1])).setScale(2, RoundingMode.HALF_DOWN));
                        seriesJFactClaCPU.add(n, (new BigDecimal(classified[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

                        classified = readData(file, n/step -1, reps, "Classify " + title, "ELK");
                        seriesELKCla.add(n, classified[0]);
                        seriesELKClaMemory.add(n, (new BigDecimal(classified[1])).setScale(2, RoundingMode.HALF_DOWN));
                        seriesELKClaCPU.add(n, (new BigDecimal(classified[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

     */
                        if (ont == 0) {
                            consistent = times.get(ont + " HermiT consistency " + n);
                            seriesHermitCons.add(n, consistent[0] / reps);
                            seriesHermitConsMemory.add(n, consistent[1] / reps);
                            seriesHermitConsCPU.add(n, consistent[2] * 100 / reps);

                            consistent = times.get(ont + " Pellet consistency " + n);
                            seriesPelletCons.add(n, consistent[0] / reps);
                            seriesPelletConsMemory.add(n, consistent[1] / reps);
                            seriesPelletConsCPU.add(n, consistent[2] * 100 / reps);

                            consistent = times.get(ont + " JFact consistency " + n);
                            seriesJFactCons.add(n, consistent[0] / reps);
                            seriesJFactConsMemory.add(n, consistent[1] / reps);
                            seriesJFactConsCPU.add(n, consistent[2] * 100 / reps);

                            consistent = times.get(ont + " ELK consistency " + n);
                            seriesELKCons.add(n, consistent[0] / reps);
                            seriesELKConsMemory.add(n, consistent[1] / reps);
                            seriesELKConsCPU.add(n, consistent[2] * 100 / reps);

                            instanceChecked = times.get(ont + " HermiT instance checking " + n);
                            seriesHermitIC.add(n, instanceChecked[0] / reps);
                            seriesHermitICMemory.add(n, instanceChecked[1] / reps);
                            seriesHermitICCPU.add(n, instanceChecked[2] * 100 / reps);

                            instanceChecked = times.get(ont + " Pellet instance checking " + n);
                            seriesPelletIC.add(n, instanceChecked[0] / reps);
                            seriesPelletICMemory.add(n, instanceChecked[1] / reps);
                            seriesPelletICCPU.add(n, instanceChecked[2] * 100 / reps);

                            instanceChecked = times.get(ont + " JFact instance checking " + n);
                            seriesJFactIC.add(n, instanceChecked[0] / reps);
                            seriesJFactICMemory.add(n, instanceChecked[1] / reps);
                            seriesJFactICCPU.add(n, instanceChecked[2] * 100 / reps);

                            instanceChecked = times.get(ont + " ELK instance checking " + n);
                            seriesELKIC.add(n, instanceChecked[0] / reps);
                            seriesELKICMemory.add(n, instanceChecked[1] / reps);
                            seriesELKICCPU.add(n, instanceChecked[2] * 100 / reps);




    /*





                            consistent = readData(file, n/step -1, reps, "Consistency", "HermiT");
                            seriesHermitCons.add(n, consistent[0]);
                            seriesHermitConsMemory.add(n, (new BigDecimal(consistent[1])).setScale(2, RoundingMode.HALF_DOWN));
                            seriesHermitConsCPU.add(n, (new BigDecimal(consistent[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

                            consistent = readData(file, n/step -1, reps, "Consistency", "Pellet");
                            seriesPelletCons.add(n, consistent[0]);
                            seriesPelletConsMemory.add(n, (new BigDecimal(consistent[1])).setScale(2, RoundingMode.HALF_DOWN));
                            seriesPelletConsCPU.add(n, (new BigDecimal(consistent[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

                            consistent = readData(file, n/step -1, reps, "Consistency", "JFact");
                            seriesJFactCons.add(n, consistent[0]);
                            seriesJFactConsMemory.add(n, (new BigDecimal(consistent[1])).setScale(2, RoundingMode.HALF_DOWN));
                            seriesJFactConsCPU.add(n, (new BigDecimal(consistent[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

                            consistent = readData(file, n/step -1, reps, "Consistency", "ELK");
                            seriesELKCons.add(n, consistent[0]);
                            seriesELKConsMemory.add(n, (new BigDecimal(consistent[1])).setScale(2, RoundingMode.HALF_DOWN));
                            seriesELKConsCPU.add(n, (new BigDecimal(consistent[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

                            instanceChecked = readData(file, n/step -1, reps, "Instance Checking", "HermiT");
                            seriesHermitIC.add(n, instanceChecked[0]);
                            seriesHermitICMemory.add(n, (new BigDecimal(instanceChecked[1])).setScale(2, RoundingMode.HALF_DOWN));
                            seriesHermitICCPU.add(n, (new BigDecimal(instanceChecked[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

                            instanceChecked = readData(file, n/step -1, reps, "Instance Checking", "Pellet");
                            seriesPelletIC.add(n, instanceChecked[0]);
                            seriesPelletICMemory.add(n, (new BigDecimal(instanceChecked[1])).setScale(2, RoundingMode.HALF_DOWN));
                            seriesPelletICCPU.add(n, (new BigDecimal(instanceChecked[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

                            instanceChecked = readData(file, n/step -1, reps, "Instance Checking", "JFact");
                            seriesJFactIC.add(n, instanceChecked[0]);
                            seriesJFactICMemory.add(n, (new BigDecimal(instanceChecked[1])).setScale(2, RoundingMode.HALF_DOWN));
                            seriesJFactICCPU.add(n, (new BigDecimal(instanceChecked[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

                            instanceChecked = readData(file, n/step -1, reps, "Instance Checking", "ELK");
                            seriesELKIC.add(n, instanceChecked[0]);
                            seriesELKICMemory.add(n, (new BigDecimal(instanceChecked[1])).setScale(2, RoundingMode.HALF_DOWN));
                            seriesELKICCPU.add(n, (new BigDecimal(instanceChecked[2] * 100)).setScale(2, RoundingMode.HALF_DOWN));

     */
                        }
                    }
                }
                String title = null;
                switch (ont){
                    case 0:
                        title = "KB";
                        break;
                    case 1:
                        title = "TBOX";
                        break;
                    case 2:
                        title = "ABOX";
                        break;
                }

                if (ont != 2){
                    var datasetSat = new XYSeriesCollection();
                    datasetSat.addSeries(seriesHermitSat);
                    datasetSat.addSeries(seriesPelletSat);
                    datasetSat.addSeries(seriesJFactSat);
                    datasetSat.addSeries(seriesELKSat);
                    var datasetSatMemory = new XYSeriesCollection();
                    datasetSatMemory.addSeries(seriesHermitSatMemory);
                    datasetSatMemory.addSeries(seriesPelletSatMemory);
                    datasetSatMemory.addSeries(seriesJFactSatMemory);
                    datasetSatMemory.addSeries(seriesELKSatMemory);
                    var datasetSatCPU = new XYSeriesCollection();
                    datasetSatCPU.addSeries(seriesHermitSatCPU);
                    datasetSatCPU.addSeries(seriesPelletSatCPU);
                    datasetSatCPU.addSeries(seriesJFactSatCPU);
                    datasetSatCPU.addSeries(seriesELKSatCPU);
                    JFreeChart chartSat = createChart(datasetSat, "Satisfiability " + title, "Time (milliseconds)");
                    ChartUtilities.saveChartAsPNG(new File("Satisfiability" + title + ".png"), chartSat, 450, 400);
                    JFreeChart chartSatMemory = createChart(datasetSatMemory, "Satisfiability Memory " + title, "Memory (%)");
                    ChartUtilities.saveChartAsPNG(new File("SatisfiabilityMemory" + title + ".png"), chartSatMemory, 450, 400);
                    JFreeChart chartSatCPU = createChart(datasetSatCPU, "Satisfiability CPU " + title, "CPU (%)");
                    ChartUtilities.saveChartAsPNG(new File("SatisfiabilityCPU" + title + ".png"), chartSatCPU, 450, 400);




/*


                    var datasetSat2 = new XYSeriesCollection();
                    datasetSat2.addSeries(seriesHermitSat2);
                    datasetSat2.addSeries(seriesPelletSat2);
                    datasetSat2.addSeries(seriesJFactSat2);
                    datasetSat2.addSeries(seriesELKSat2);
                    var datasetSatMemory2 = new XYSeriesCollection();
                    datasetSatMemory2.addSeries(seriesHermitSatMemory2);
                    datasetSatMemory2.addSeries(seriesPelletSatMemory2);
                    datasetSatMemory2.addSeries(seriesJFactSatMemory2);
                    datasetSatMemory2.addSeries(seriesELKSatMemory2);
                    var datasetSatCPU2 = new XYSeriesCollection();
                    datasetSatCPU2.addSeries(seriesHermitSatCPU2);
                    datasetSatCPU2.addSeries(seriesPelletSatCPU2);
                    datasetSatCPU2.addSeries(seriesJFactSatCPU2);
                    datasetSatCPU2.addSeries(seriesELKSatCPU2);
                    JFreeChart chartSat2 = createChart(datasetSat2, "Satisfiability " + title, "Time (milliseconds)");
                    ChartUtilities.saveChartAsPNG(new File("Satisfiability" + title + "2.png"), chartSat2, 450, 400);
                    JFreeChart chartSatMemory2 = createChart(datasetSatMemory2, "Satisfiability Memory " + title, "Memory (%)");
                    ChartUtilities.saveChartAsPNG(new File("SatisfiabilityMemory" + title + "2.png"), chartSatMemory2, 450, 400);
                    JFreeChart chartSatCPU2 = createChart(datasetSatCPU2, "Satisfiability CPU " + title, "CPU (%)");
                    ChartUtilities.saveChartAsPNG(new File("SatisfiabilityCPU" + title + "2.png"), chartSatCPU2, 450, 400);

 */

                    var datasetCla = new XYSeriesCollection();
                    datasetCla.addSeries(seriesHermitCla);
                    datasetCla.addSeries(seriesPelletCla);
                    datasetCla.addSeries(seriesJFactCla);
                    datasetCla.addSeries(seriesELKCla);
                    var datasetClaMemory = new XYSeriesCollection();
                    datasetClaMemory.addSeries(seriesHermitClaMemory);
                    datasetClaMemory.addSeries(seriesPelletClaMemory);
                    datasetClaMemory.addSeries(seriesJFactClaMemory);
                    datasetClaMemory.addSeries(seriesELKClaMemory);
                    var datasetClaCPU = new XYSeriesCollection();
                    datasetClaCPU.addSeries(seriesHermitClaCPU);
                    datasetClaCPU.addSeries(seriesPelletClaCPU);
                    datasetClaCPU.addSeries(seriesJFactClaCPU);
                    datasetClaCPU.addSeries(seriesELKClaCPU);
                    JFreeChart chartCla = createChart(datasetCla, "Classify " + title, "Time (milliseconds)");
                    ChartUtilities.saveChartAsPNG(new File("Classify" + title + ".png"), chartCla, 450, 400);
                    JFreeChart chartClaMemory = createChart(datasetClaMemory, "Classify Memory " + title, "Memory (%)");
                    ChartUtilities.saveChartAsPNG(new File("ClassifyMemory" + title + ".png"), chartClaMemory, 450, 400);
                    JFreeChart chartClaCPU = createChart(datasetClaCPU, "Classify CPU " + title, "CPU (%)");
                    ChartUtilities.saveChartAsPNG(new File("ClassifyCPU" + title + ".png"), chartClaCPU, 450, 400);




/*
                    var datasetCla2 = new XYSeriesCollection();
                    datasetCla2.addSeries(seriesHermitCla2);
                    datasetCla2.addSeries(seriesPelletCla2);
                    datasetCla2.addSeries(seriesJFactCla2);
                    datasetCla2.addSeries(seriesELKCla2);
                    var datasetClaMemory2 = new XYSeriesCollection();
                    datasetClaMemory2.addSeries(seriesHermitClaMemory2);
                    datasetClaMemory2.addSeries(seriesPelletClaMemory2);
                    datasetClaMemory2.addSeries(seriesJFactClaMemory2);
                    datasetClaMemory2.addSeries(seriesELKClaMemory2);
                    var datasetClaCPU2 = new XYSeriesCollection();
                    datasetClaCPU2.addSeries(seriesHermitClaCPU2);
                    datasetClaCPU2.addSeries(seriesPelletClaCPU2);
                    datasetClaCPU2.addSeries(seriesJFactClaCPU2);
                    datasetClaCPU2.addSeries(seriesELKClaCPU2);
                    JFreeChart chartCla2 = createChart(datasetCla2, "Classify " + title, "Time (milliseconds)");
                    ChartUtilities.saveChartAsPNG(new File("Classify" + title + "2.png"), chartCla2, 450, 400);
                    JFreeChart chartClaMemory2 = createChart(datasetClaMemory2, "Classify Memory " + title, "Memory (%)");
                    ChartUtilities.saveChartAsPNG(new File("ClassifyMemory" + title + "2.png"), chartClaMemory2, 450, 400);
                    JFreeChart chartClaCPU2 = createChart(datasetClaCPU2, "Classify CPU " + title, "CPU (%)");
                    ChartUtilities.saveChartAsPNG(new File("ClassifyCPU" + title + "2.png"), chartClaCPU2, 450, 400);

 */
                }

                if (ont == 0){
                    var datasetCons = new XYSeriesCollection();
                    datasetCons.addSeries(seriesHermitCons);
                    datasetCons.addSeries(seriesPelletCons);
                    datasetCons.addSeries(seriesJFactCons);
                    datasetCons.addSeries(seriesELKCons);
                    var datasetConsMemory = new XYSeriesCollection();
                    datasetConsMemory.addSeries(seriesHermitConsMemory);
                    datasetConsMemory.addSeries(seriesPelletConsMemory);
                    datasetConsMemory.addSeries(seriesJFactConsMemory);
                    datasetConsMemory.addSeries(seriesELKConsMemory);
                    var datasetConsCPU = new XYSeriesCollection();
                    datasetConsCPU.addSeries(seriesHermitConsCPU);
                    datasetConsCPU.addSeries(seriesPelletConsCPU);
                    datasetConsCPU.addSeries(seriesJFactConsCPU);
                    datasetConsCPU.addSeries(seriesELKConsCPU);
                    JFreeChart chartCons = createChart(datasetCons, "Consistency " + title, "Time (microseconds)");
                    ChartUtilities.saveChartAsPNG(new File("Consistency" + title + ".png"), chartCons, 450, 400);
                    JFreeChart chartConsMemory = createChart(datasetConsMemory, "Consistency Memory " + title, "Memory (%)");
                    ChartUtilities.saveChartAsPNG(new File("ConsistencyMemory" + title + ".png"), chartConsMemory, 450, 400);
                    JFreeChart chartConsCPU = createChart(datasetConsCPU, "Consistency CPU " + title, "CPU (%)");
                    ChartUtilities.saveChartAsPNG(new File("ConsistencyCPU" + title + ".png"), chartConsCPU, 450, 400);






/*

                    var datasetCons2 = new XYSeriesCollection();
                    datasetCons2.addSeries(seriesHermitCons2);
                    datasetCons2.addSeries(seriesPelletCons2);
                    datasetCons2.addSeries(seriesJFactCons2);
                    datasetCons2.addSeries(seriesELKCons2);
                    var datasetConsMemory2 = new XYSeriesCollection();
                    datasetConsMemory2.addSeries(seriesHermitConsMemory2);
                    datasetConsMemory2.addSeries(seriesPelletConsMemory2);
                    datasetConsMemory2.addSeries(seriesJFactConsMemory2);
                    datasetConsMemory2.addSeries(seriesELKConsMemory2);
                    var datasetConsCPU2 = new XYSeriesCollection();
                    datasetConsCPU2.addSeries(seriesHermitConsCPU2);
                    datasetConsCPU2.addSeries(seriesPelletConsCPU2);
                    datasetConsCPU2.addSeries(seriesJFactConsCPU2);
                    datasetConsCPU2.addSeries(seriesELKConsCPU2);
                    JFreeChart chartCons2 = createChart(datasetCons2, "Consistency " + title, "Time (microseconds)");
                    ChartUtilities.saveChartAsPNG(new File("Consistency" + title + "2.png"), chartCons2, 450, 400);
                    JFreeChart chartConsMemory2 = createChart(datasetConsMemory2, "Consistency Memory " + title, "Memory (%)");
                    ChartUtilities.saveChartAsPNG(new File("ConsistencyMemory" + title + "2.png"), chartConsMemory2, 450, 400);
                    JFreeChart chartConsCPU2 = createChart(datasetConsCPU2, "Consistency CPU " + title, "CPU (%)");
                    ChartUtilities.saveChartAsPNG(new File("ConsistencyCPU" + title + "2.png"), chartConsCPU2, 450, 400);

 */





                    var datasetIC = new XYSeriesCollection();
                    datasetIC.addSeries(seriesHermitIC);
                    datasetIC.addSeries(seriesPelletIC);
                    datasetIC.addSeries(seriesJFactIC);
                    datasetIC.addSeries(seriesELKIC);
                    var datasetICMemory = new XYSeriesCollection();
                    datasetICMemory.addSeries(seriesHermitICMemory);
                    datasetICMemory.addSeries(seriesPelletICMemory);
                    datasetICMemory.addSeries(seriesJFactICMemory);
                    datasetICMemory.addSeries(seriesELKICMemory);
                    var datasetICCPU = new XYSeriesCollection();
                    datasetICCPU.addSeries(seriesHermitICCPU);
                    datasetICCPU.addSeries(seriesPelletICCPU);
                    datasetICCPU.addSeries(seriesJFactICCPU);
                    datasetICCPU.addSeries(seriesELKICCPU);
                    JFreeChart chartIC = createChart(datasetIC, "Instance checking " + title, "Time (milliseconds)");
                    ChartUtilities.saveChartAsPNG(new File("InstanceChecking" + title + ".png"), chartIC, 450, 400);
                    JFreeChart chartICMemory = createChart(datasetICMemory, "Instance checking Memory " + title, "Memory (%)");
                    ChartUtilities.saveChartAsPNG(new File("InstanceCheckingMemory" + title + ".png"), chartICMemory, 450, 400);
                    JFreeChart chartICCPU = createChart(datasetICCPU, "Instance checking CPU " + title, "CPU (%)");
                    ChartUtilities.saveChartAsPNG(new File("InstanceCheckingCPU" + title + ".png"), chartICCPU, 450, 400);

/*
                    var datasetIC2 = new XYSeriesCollection();
                    datasetIC2.addSeries(seriesHermitIC2);
                    datasetIC2.addSeries(seriesPelletIC2);
                    datasetIC2.addSeries(seriesJFactIC2);
                    datasetIC2.addSeries(seriesELKIC2);
                    var datasetICMemory2 = new XYSeriesCollection();
                    datasetICMemory2.addSeries(seriesHermitICMemory2);
                    datasetICMemory2.addSeries(seriesPelletICMemory2);
                    datasetICMemory2.addSeries(seriesJFactICMemory2);
                    datasetICMemory2.addSeries(seriesELKICMemory2);
                    var datasetICCPU2 = new XYSeriesCollection();
                    datasetICCPU2.addSeries(seriesHermitICCPU2);
                    datasetICCPU2.addSeries(seriesPelletICCPU2);
                    datasetICCPU2.addSeries(seriesJFactICCPU2);
                    datasetICCPU2.addSeries(seriesELKICCPU2);
                    JFreeChart chartIC2 = createChart(datasetIC2, "Instance checking " + title, "Time (milliseconds)");
                    ChartUtilities.saveChartAsPNG(new File("InstanceChecking" + title + "2.png"), chartIC2, 450, 400);
                    JFreeChart chartICMemory2 = createChart(datasetICMemory2, "Instance checking Memory " + title, "Memory (%)");
                    ChartUtilities.saveChartAsPNG(new File("InstanceCheckingMemory" + title + "2.png"), chartICMemory2, 450, 400);
                    JFreeChart chartICCPU2 = createChart(datasetICCPU2, "Instance checking CPU " + title, "CPU (%)");
                    ChartUtilities.saveChartAsPNG(new File("InstanceCheckingCPU" + title + "2.png"), chartICCPU2, 450, 400);

 */

                }
            }
        }catch (Exception e){
            e.printStackTrace();
        }

    }
}