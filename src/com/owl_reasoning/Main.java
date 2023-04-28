package com.owl_reasoning;

import com.opencsv.CSVWriter;
import org.jfree.chart.ChartFactory;
import org.jfree.chart.ChartUtilities;
import org.jfree.chart.JFreeChart;
import org.jfree.chart.block.BlockBorder;
import org.jfree.chart.plot.PlotOrientation;
import org.jfree.chart.plot.XYPlot;
import org.jfree.chart.renderer.xy.XYLineAndShapeRenderer;
import org.jfree.chart.title.TextTitle;
import org.jfree.data.xy.XYDataItem;
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
import org.semanticweb.owlapi.formats.OWLXMLDocumentFormat;
import org.semanticweb.owlapi.formats.RDFDocumentFormat;
import org.semanticweb.owlapi.formats.RDFXMLDocumentFormat;
import org.semanticweb.owlapi.io.OWLXMLOntologyFormat;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.*;
import uk.ac.manchester.cs.jfact.JFactFactory;

import java.io.*;
import java.lang.management.ManagementFactory;
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

    public static OWLOntology generateOntology(int n, int m, int rep) throws OWLOntologyCreationException, OWLOntologyStorageException {
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

        /*
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

         */
        File file = new File("ontology" + n + "rep" + rep + ".rdf");
        RDFDocumentFormat format = (RDFDocumentFormat) ontologyManager.getOntologyFormat(o);
        RDFXMLDocumentFormat rdfxmlFormat = new RDFXMLDocumentFormat();
        if (format.isPrefixOWLDocumentFormat()) {
            rdfxmlFormat.copyPrefixesFrom(format.asPrefixOWLDocumentFormat());
        }
        ontologyManager.saveOntology(o, rdfxmlFormat, IRI.create(file.toURI()));
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

    public static String[] isSatisfiable(OWLReasoner reasoner, OWLOntology owlOntology, int n) {
        Stream<OWLClass> classes = owlOntology.classesInSignature();
        List<OWLClass> classesList = classes.toList();
        long tic = System.currentTimeMillis();
        for (int c=0; c<classesList.size(); c++){
            reasoner.isSatisfiable(classesList.get(c));
        }
        long toc = System.currentTimeMillis();
        long executionTime = toc - tic;
        if (owlOntology.equals(ontology)){
            return new String[]{String.valueOf(n), "Satisfiability KB", String.valueOf(executionTime), String.valueOf(100*Runtime.getRuntime().totalMemory()/Runtime.getRuntime().maxMemory()), String.valueOf(getProcessCpuLoad())};
        }
        else
            return new String[]{String.valueOf(n), "Satisfiability TBox", String.valueOf(executionTime), String.valueOf(100*Runtime.getRuntime().totalMemory()/Runtime.getRuntime().maxMemory()), String.valueOf(getProcessCpuLoad())};
    }

    public static String[] classify(OWLReasoner reasoner, OWLOntology owlOntology, int n){
        long tic = System.currentTimeMillis();
        reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
        long toc = System.currentTimeMillis();
        long executionTime = toc - tic;
        if (owlOntology.equals(ontology)){
            return new String[]{String.valueOf(n), "Classify KB", String.valueOf(executionTime), String.valueOf(100*Runtime.getRuntime().totalMemory()/Runtime.getRuntime().maxMemory()), String.valueOf(getProcessCpuLoad())};
        }
        else
            return new String[]{String.valueOf(n), "Classify TBox", String.valueOf(executionTime), String.valueOf(100*Runtime.getRuntime().totalMemory()/Runtime.getRuntime().maxMemory()), String.valueOf(getProcessCpuLoad())};    }

    public static String[] isConsistent(OWLReasoner reasoner, int n){
        long tic = System.nanoTime();
        reasoner.isConsistent();
        long toc = System.nanoTime();
        long executionTime = toc - tic;
        return new String[]{String.valueOf(n), "Consistency KB", String.valueOf(executionTime/100), String.valueOf(100*Runtime.getRuntime().totalMemory()/Runtime.getRuntime().maxMemory()), String.valueOf(getProcessCpuLoad())};
    }

    public static String[] instanceChecking(OWLReasoner reasoner, OWLAxiom axiom, int n){
        long tic = System.currentTimeMillis();
        reasoner.isEntailed(axiom);
        long toc = System.currentTimeMillis();
        long executionTime = toc - tic;
        return new String[]{String.valueOf(n), "Instance Checking KB", String.valueOf(executionTime), String.valueOf(100*Runtime.getRuntime().totalMemory()/Runtime.getRuntime().maxMemory()), String.valueOf(getProcessCpuLoad())};
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


    public static void main(String[] args) {
        try{
            PrintStream dummyStream = new PrintStream(new OutputStream(){
                public void write(int b) {
                    // NO-OP
                }
            });
            System.setOut(dummyStream);

            File fileH = new File("hermit.csv");
            File fileP = new File("pellet.csv");
            File fileJ = new File("jfact.csv");
            File fileE = new File("elk.csv");

            // create FileWriter object with file as parameter
            FileWriter outputfileH = new FileWriter(fileH);
            FileWriter outputfileP = new FileWriter(fileP);
            FileWriter outputfileJ = new FileWriter(fileJ);
            FileWriter outputfileE = new FileWriter(fileE);
            // create CSVWriter object filewriter object as parameter
            CSVWriter writerH = new CSVWriter(outputfileH);
            CSVWriter writerP = new CSVWriter(outputfileP);
            CSVWriter writerJ = new CSVWriter(outputfileJ);
            CSVWriter writerE = new CSVWriter(outputfileE);
            // adding header to csv
            String[] header = { "Classes", "Reasoning Task", "Time(ms)", "Memory(%)", "CPU(%)" };
            writerH.writeNext(header);
            writerP.writeNext(header);
            writerJ.writeNext(header);
            writerE.writeNext(header);

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
            int iterations = 7;
            int step = 5000;
            int reps = 1;

            int m = 1000;

            for (int rep=0; rep<reps; rep++){
                int n = 0;
                for (int i=0; i<iterations; i++){
                    n += step;
                    ontology = generateOntology(n, m, rep);
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
                            writerH.writeNext(isSatisfiable(reasonerH, boxes[ont], n));
                            writerP.writeNext(isSatisfiable(reasonerP, boxes[ont], n));
                            writerJ.writeNext(isSatisfiable(reasonerJ, boxes[ont], n));
                            writerE.writeNext(isSatisfiable(reasonerE, boxes[ont], n));

                            writerH.writeNext(classify(reasonerH, boxes[ont], n));
                            writerP.writeNext(classify(reasonerP, boxes[ont], n));
                            writerJ.writeNext(classify(reasonerJ, boxes[ont], n));
                            writerE.writeNext(classify(reasonerE, boxes[ont], n));
                        }
                        if (ont == 0){
                            writerH.writeNext(isConsistent(reasonerH, n));
                            writerP.writeNext(isConsistent(reasonerP, n));
                            writerJ.writeNext(isConsistent(reasonerJ, n));
                            writerE.writeNext(isConsistent(reasonerE, n));

                            Random rnd = new Random();
                            rnd.setSeed(rep);
                            int A = rnd.nextInt(n);
                            int B = rnd. nextInt(m);
                            OWLClass cls = df.getOWLClass("#Class" + A);
                            OWLNamedIndividual individual = df.getOWLNamedIndividual("#Individual" + B);
                            OWLAxiom axiom =  df.getOWLClassAssertionAxiom(cls, individual);

                            writerH.writeNext(instanceChecking(reasonerH, axiom, n));
                            writerP.writeNext(instanceChecking(reasonerP, axiom, n));
                            writerJ.writeNext(instanceChecking(reasonerJ, axiom, n));
                            writerE.writeNext(instanceChecking(reasonerE, axiom, n));
                        }
                    }
                }
            }
            writerH.close();
            writerP.close();
            writerJ.close();
            writerE.close();
            var seriesHermitCons = new XYSeries("Hermit", false);
            var seriesPelletCons = new XYSeries("Pellet", false);
            var seriesJFactCons = new XYSeries("JFact", false);
            var seriesELKCons = new XYSeries("ELK", false);
            var seriesHermitSat = new XYSeries("Hermit", false);
            var seriesPelletSat = new XYSeries("Pellet", false);
            var seriesJFactSat = new XYSeries("JFact", false);
            var seriesELKSat = new XYSeries("ELK", false);
            var seriesHermitCla = new XYSeries("Hermit", false);
            var seriesPelletCla = new XYSeries("Pellet", false);
            var seriesJFactCla = new XYSeries("JFact", false);
            var seriesELKCla = new XYSeries("ELK", false);
            var seriesHermitSatTB = new XYSeries("Hermit", false);
            var seriesPelletSatTB = new XYSeries("Pellet", false);
            var seriesJFactSatTB = new XYSeries("JFact", false);
            var seriesELKSatTB = new XYSeries("ELK", false);
            var seriesHermitClaTB = new XYSeries("Hermit", false);
            var seriesPelletClaTB = new XYSeries("Pellet", false);
            var seriesJFactClaTB = new XYSeries("JFact", false);
            var seriesELKClaTB = new XYSeries("ELK", false);
            var seriesHermitIC = new XYSeries("Hermit", false);
            var seriesPelletIC = new XYSeries("Pellet", false);
            var seriesJFactIC = new XYSeries("JFact", false);
            var seriesELKIC = new XYSeries("ELK", false);

            var seriesHermitConsMemory = new XYSeries("Hermit", false);
            var seriesPelletConsMemory = new XYSeries("Pellet", false);
            var seriesJFactConsMemory = new XYSeries("JFact", false);
            var seriesELKConsMemory = new XYSeries("ELK", false);
            var seriesHermitSatMemory = new XYSeries("Hermit", false);
            var seriesPelletSatMemory = new XYSeries("Pellet", false);
            var seriesJFactSatMemory = new XYSeries("JFact", false);
            var seriesELKSatMemory = new XYSeries("ELK", false);
            var seriesHermitClaMemory = new XYSeries("Hermit", false);
            var seriesPelletClaMemory = new XYSeries("Pellet", false);
            var seriesJFactClaMemory = new XYSeries("JFact", false);
            var seriesELKClaMemory = new XYSeries("ELK", false);
            var seriesHermitSatMemoryTB = new XYSeries("Hermit", false);
            var seriesPelletSatMemoryTB = new XYSeries("Pellet", false);
            var seriesJFactSatMemoryTB = new XYSeries("JFact", false);
            var seriesELKSatMemoryTB = new XYSeries("ELK", false);
            var seriesHermitClaMemoryTB = new XYSeries("Hermit", false);
            var seriesPelletClaMemoryTB = new XYSeries("Pellet", false);
            var seriesJFactClaMemoryTB = new XYSeries("JFact", false);
            var seriesELKClaMemoryTB = new XYSeries("ELK", false);
            var seriesHermitICMemory = new XYSeries("Hermit", false);
            var seriesPelletICMemory = new XYSeries("Pellet", false);
            var seriesJFactICMemory = new XYSeries("JFact", false);
            var seriesELKICMemory = new XYSeries("ELK", false);

            var seriesHermitConsCPU = new XYSeries("Hermit", false);
            var seriesPelletConsCPU = new XYSeries("Pellet", false);
            var seriesJFactConsCPU = new XYSeries("JFact", false);
            var seriesELKConsCPU = new XYSeries("ELK", false);
            var seriesHermitSatCPU = new XYSeries("Hermit", false);
            var seriesPelletSatCPU = new XYSeries("Pellet", false);
            var seriesJFactSatCPU = new XYSeries("JFact", false);
            var seriesELKSatCPU = new XYSeries("ELK", false);
            var seriesHermitClaCPU = new XYSeries("Hermit", false);
            var seriesPelletClaCPU = new XYSeries("Pellet", false);
            var seriesJFactClaCPU = new XYSeries("JFact", false);
            var seriesELKClaCPU = new XYSeries("ELK", false);
            var seriesHermitSatCPUTB = new XYSeries("Hermit", false);
            var seriesPelletSatCPUTB = new XYSeries("Pellet", false);
            var seriesJFactSatCPUTB = new XYSeries("JFact", false);
            var seriesELKSatCPUTB = new XYSeries("ELK", false);
            var seriesHermitClaCPUTB = new XYSeries("Hermit", false);
            var seriesPelletClaCPUTB = new XYSeries("Pellet", false);
            var seriesJFactClaCPUTB = new XYSeries("JFact", false);
            var seriesELKClaCPUTB = new XYSeries("ELK", false);
            var seriesHermitICCPU = new XYSeries("Hermit", false);
            var seriesPelletICCPU = new XYSeries("Pellet", false);
            var seriesJFactICCPU = new XYSeries("JFact", false);
            var seriesELKICCPU = new XYSeries("ELK", false);

            BufferedReader reader = new BufferedReader(new FileReader("hermit.csv"));
            String line = null;
            int i = 0;
            int n = -1;
            int time = -1;
            int memory = -1;
            double cpu = -1;
            reader.readLine();
            while ((line = reader.readLine()) != null) {
                String[] data = line.split(",");
                int j = 0;
                for(String singleData : data){
                    if (j==0){
                        n = Integer.parseInt(singleData.replaceAll("\"",""));
                    }
                    if (j==2){
                        time = Integer.parseInt(singleData.replaceAll("\"",""));
                    }
                    if (j==3){
                        memory = Integer.parseInt(singleData.replaceAll("\"",""));
                    }
                    if (j==4){
                        cpu = Double.parseDouble(singleData.replaceAll("\"",""));
                    }
                    j++;
                }
                if (i%6 == 0){
                    if (i > 5+6*(iterations-1)){
                        XYDataItem old = seriesHermitSat.remove(0);
                        seriesHermitSat.add(n, time + old.getYValue());
                        old = seriesHermitSatMemory.remove(0);
                        seriesHermitSatMemory.add(n, memory + old.getYValue());
                        old = seriesHermitSatCPU.remove(0);
                        seriesHermitSatCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesHermitSat.add(n, time);
                        seriesHermitSatMemory.add(n, memory);
                        seriesHermitSatCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 1){
                    if (i > 6+6*(iterations-1)){
                        XYDataItem old = seriesHermitCla.remove(0);
                        seriesHermitCla.add(n, time + old.getYValue());
                        old = seriesHermitClaMemory.remove(0);
                        seriesHermitClaMemory.add(n, memory + old.getYValue());
                        old = seriesHermitClaCPU.remove(0);
                        seriesHermitClaCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesHermitCla.add(n, time);
                        seriesHermitClaMemory.add(n, memory);
                        seriesHermitClaCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 2){
                    if (i > 7+6*(iterations-1)){
                        XYDataItem old = seriesHermitCons.remove(0);
                        seriesHermitCons.add(n, time + old.getYValue());
                        old = seriesHermitConsMemory.remove(0);
                        seriesHermitConsMemory.add(n, memory + old.getYValue());
                        old = seriesHermitConsCPU.remove(0);
                        seriesHermitConsCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesHermitCons.add(n, time);
                        seriesHermitConsMemory.add(n, memory);
                        seriesHermitConsCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 3){
                    if (i > 8+6*(iterations-1)){
                        XYDataItem old = seriesHermitIC.remove(0);
                        seriesHermitIC.add(n, time + old.getYValue());
                        old = seriesHermitICMemory.remove(0);
                        seriesHermitICMemory.add(n, memory + old.getYValue());
                        old = seriesHermitICCPU.remove(0);
                        seriesHermitICCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesHermitIC.add(n, time);
                        seriesHermitICMemory.add(n, memory);
                        seriesHermitICCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 4){
                    if (i > 9+6*(iterations-1)){
                        XYDataItem old = seriesHermitSatTB.remove(0);
                        seriesHermitSatTB.add(n, time + old.getYValue());
                        old = seriesHermitSatMemoryTB.remove(0);
                        seriesHermitSatMemoryTB.add(n, memory + old.getYValue());
                        old = seriesHermitSatCPUTB.remove(0);
                        seriesHermitSatCPUTB.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesHermitSatTB.add(n, time);
                        seriesHermitSatMemoryTB.add(n, memory);
                        seriesHermitSatCPUTB.add(n, cpu*100);
                    }
                }
                else{
                    if (i > 10+6*(iterations-1)){
                        XYDataItem old = seriesHermitClaTB.remove(0);
                        seriesHermitClaTB.add(n, time + old.getYValue());
                        old = seriesHermitClaMemoryTB.remove(0);
                        seriesHermitClaMemoryTB.add(n, memory + old.getYValue());
                        old = seriesHermitClaCPUTB.remove(0);
                        seriesHermitClaCPUTB.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesHermitClaTB.add(n, time);
                        seriesHermitClaMemoryTB.add(n, memory);
                        seriesHermitClaCPUTB.add(n, cpu*100);
                    }
                }
                i++;
            }
            reader.close();

            reader = new BufferedReader(new FileReader("pellet.csv"));
            line = null;
            i = 0;
            n = -1;
            time = -1;
            memory = -1;
            cpu = -1;
            reader.readLine();
            while ((line = reader.readLine()) != null) {
                String[] data = line.split(",");
                int j = 0;
                for(String singleData : data){
                    if (j==0){
                        n = Integer.parseInt(singleData.replaceAll("\"",""));
                    }
                    if (j==2){
                        time = Integer.parseInt(singleData.replaceAll("\"",""));
                    }
                    if (j==3){
                        memory = Integer.parseInt(singleData.replaceAll("\"",""));
                    }
                    if (j==4){
                        cpu = Double.parseDouble(singleData.replaceAll("\"",""));
                    }
                    j++;
                }
                if (i%6 == 0){
                    if (i > 5+6*(iterations-1)){
                        XYDataItem old = seriesPelletSat.remove(0);
                        seriesPelletSat.add(n, time + old.getYValue());
                        old = seriesPelletSatMemory.remove(0);
                        seriesPelletSatMemory.add(n, memory + old.getYValue());
                        old = seriesPelletSatCPU.remove(0);
                        seriesPelletSatCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesPelletSat.add(n, time);
                        seriesPelletSatMemory.add(n, memory);
                        seriesPelletSatCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 1){
                    if (i > 6+6*(iterations-1)){
                        XYDataItem old = seriesPelletCla.remove(0);
                        seriesPelletCla.add(n, time + old.getYValue());
                        old = seriesPelletClaMemory.remove(0);
                        seriesPelletClaMemory.add(n, memory + old.getYValue());
                        old = seriesPelletClaCPU.remove(0);
                        seriesPelletClaCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesPelletCla.add(n, time);
                        seriesPelletClaMemory.add(n, memory);
                        seriesPelletClaCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 2){
                    if (i > 7+6*(iterations-1)){
                        XYDataItem old = seriesPelletCons.remove(0);
                        seriesPelletCons.add(n, time + old.getYValue());
                        old = seriesPelletConsMemory.remove(0);
                        seriesPelletConsMemory.add(n, memory + old.getYValue());
                        old = seriesPelletConsCPU.remove(0);
                        seriesPelletConsCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesPelletCons.add(n, time);
                        seriesPelletConsMemory.add(n, memory);
                        seriesPelletConsCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 3){
                    if (i > 8+6*(iterations-1)){
                        XYDataItem old = seriesPelletIC.remove(0);
                        seriesPelletIC.add(n, time + old.getYValue());
                        old = seriesPelletICMemory.remove(0);
                        seriesPelletICMemory.add(n, memory + old.getYValue());
                        old = seriesPelletICCPU.remove(0);
                        seriesPelletICCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesPelletIC.add(n, time);
                        seriesPelletICMemory.add(n, memory);
                        seriesPelletICCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 4){
                    if (i > 9+6*(iterations-1)){
                        XYDataItem old = seriesPelletSatTB.remove(0);
                        seriesPelletSatTB.add(n, time + old.getYValue());
                        old = seriesPelletSatMemoryTB.remove(0);
                        seriesPelletSatMemoryTB.add(n, memory + old.getYValue());
                        old = seriesPelletSatCPUTB.remove(0);
                        seriesPelletSatCPUTB.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesPelletSatTB.add(n, time);
                        seriesPelletSatMemoryTB.add(n, memory);
                        seriesPelletSatCPUTB.add(n, cpu*100);
                    }
                }
                else{
                    if (i > 10+6*(iterations-1)){
                        XYDataItem old = seriesPelletClaTB.remove(0);
                        seriesPelletClaTB.add(n, time + old.getYValue());
                        old = seriesPelletClaMemoryTB.remove(0);
                        seriesPelletClaMemoryTB.add(n, memory + old.getYValue());
                        old = seriesPelletClaCPUTB.remove(0);
                        seriesPelletClaCPUTB.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesPelletClaTB.add(n, time);
                        seriesPelletClaMemoryTB.add(n, memory);
                        seriesPelletClaCPUTB.add(n, cpu*100);
                    }
                }
                i++;
            }
            reader.close();

            reader = new BufferedReader(new FileReader("jfact.csv"));
            line = null;
            i = 0;
            n = -1;
            time = -1;
            memory = -1;
            cpu = -1;
            reader.readLine();
            while ((line = reader.readLine()) != null) {
                String[] data = line.split(",");
                int j = 0;
                for(String singleData : data){
                    if (j==0){
                        n = Integer.parseInt(singleData.replaceAll("\"",""));
                    }
                    if (j==2){
                        time = Integer.parseInt(singleData.replaceAll("\"",""));
                    }
                    if (j==3){
                        memory = Integer.parseInt(singleData.replaceAll("\"",""));
                    }
                    if (j==4){
                        cpu = Double.parseDouble(singleData.replaceAll("\"",""));
                    }
                    j++;
                }
                if (i%6 == 0){
                    if (i > 5+6*(iterations-1)){
                        XYDataItem old = seriesJFactSat.remove(0);
                        seriesJFactSat.add(n, time + old.getYValue());
                        old = seriesJFactSatMemory.remove(0);
                        seriesJFactSatMemory.add(n, memory + old.getYValue());
                        old = seriesJFactSatCPU.remove(0);
                        seriesJFactSatCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesJFactSat.add(n, time);
                        seriesJFactSatMemory.add(n, memory);
                        seriesJFactSatCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 1){
                    if (i > 6+6*(iterations-1)){
                        XYDataItem old = seriesJFactCla.remove(0);
                        seriesJFactCla.add(n, time + old.getYValue());
                        old = seriesJFactClaMemory.remove(0);
                        seriesJFactClaMemory.add(n, memory + old.getYValue());
                        old = seriesJFactClaCPU.remove(0);
                        seriesJFactClaCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesJFactCla.add(n, time);
                        seriesJFactClaMemory.add(n, memory);
                        seriesJFactClaCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 2){
                    if (i > 7+6*(iterations-1)){
                        XYDataItem old = seriesJFactCons.remove(0);
                        seriesJFactCons.add(n, time + old.getYValue());
                        old = seriesJFactConsMemory.remove(0);
                        seriesJFactConsMemory.add(n, memory + old.getYValue());
                        old = seriesJFactConsCPU.remove(0);
                        seriesJFactConsCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesJFactCons.add(n, time);
                        seriesJFactConsMemory.add(n, memory);
                        seriesJFactConsCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 3){
                    if (i > 8+6*(iterations-1)){
                        XYDataItem old = seriesJFactIC.remove(0);
                        seriesJFactIC.add(n, time + old.getYValue());
                        old = seriesJFactICMemory.remove(0);
                        seriesJFactICMemory.add(n, memory + old.getYValue());
                        old = seriesJFactICCPU.remove(0);
                        seriesJFactICCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesJFactIC.add(n, time);
                        seriesJFactICMemory.add(n, memory);
                        seriesJFactICCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 4){
                    if (i > 9+6*(iterations-1)){
                        XYDataItem old = seriesJFactSatTB.remove(0);
                        seriesJFactSatTB.add(n, time + old.getYValue());
                        old = seriesJFactSatMemoryTB.remove(0);
                        seriesJFactSatMemoryTB.add(n, memory + old.getYValue());
                        old = seriesJFactSatCPUTB.remove(0);
                        seriesJFactSatCPUTB.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesJFactSatTB.add(n, time);
                        seriesJFactSatMemoryTB.add(n, memory);
                        seriesJFactSatCPUTB.add(n, cpu*100);
                    }
                }
                else{
                    if (i > 10+6*(iterations-1)){
                        XYDataItem old = seriesJFactClaTB.remove(0);
                        seriesJFactClaTB.add(n, time + old.getYValue());
                        old = seriesJFactClaMemoryTB.remove(0);
                        seriesJFactClaMemoryTB.add(n, memory + old.getYValue());
                        old = seriesJFactClaCPUTB.remove(0);
                        seriesJFactClaCPUTB.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesJFactClaTB.add(n, time);
                        seriesJFactClaMemoryTB.add(n, memory);
                        seriesJFactClaCPUTB.add(n, cpu*100);
                    }
                }
                i++;
            }
            reader.close();

            reader = new BufferedReader(new FileReader("elk.csv"));
            line = null;
            i = 0;
            n = -1;
            time = -1;
            memory = -1;
            cpu = -1;
            reader.readLine();
            while ((line = reader.readLine()) != null) {
                String[] data = line.split(",");
                int j = 0;
                for(String singleData : data){
                    if (j==0){
                        n = Integer.parseInt(singleData.replaceAll("\"",""));
                    }
                    if (j==2){
                        time = Integer.parseInt(singleData.replaceAll("\"",""));
                    }
                    if (j==3){
                        memory = Integer.parseInt(singleData.replaceAll("\"",""));
                    }
                    if (j==4){
                        cpu = Double.parseDouble(singleData.replaceAll("\"",""));
                    }
                    j++;
                }
                if (i%6 == 0){
                    if (i > 5+6*(iterations-1)){
                        XYDataItem old = seriesELKSat.remove(0);
                        seriesELKSat.add(n, time + old.getYValue());
                        old = seriesELKSatMemory.remove(0);
                        seriesELKSatMemory.add(n, memory + old.getYValue());
                        old = seriesELKSatCPU.remove(0);
                        seriesELKSatCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesELKSat.add(n, time);
                        seriesELKSatMemory.add(n, memory);
                        seriesELKSatCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 1){
                    if (i > 6+6*(iterations-1)){
                        XYDataItem old = seriesELKCla.remove(0);
                        seriesELKCla.add(n, time + old.getYValue());
                        old = seriesELKClaMemory.remove(0);
                        seriesELKClaMemory.add(n, memory + old.getYValue());
                        old = seriesELKClaCPU.remove(0);
                        seriesELKClaCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesELKCla.add(n, time);
                        seriesELKClaMemory.add(n, memory);
                        seriesELKClaCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 2){
                    if (i > 7+6*(iterations-1)){
                        XYDataItem old = seriesELKCons.remove(0);
                        seriesELKCons.add(n, time + old.getYValue());
                        old = seriesELKConsMemory.remove(0);
                        seriesELKConsMemory.add(n, memory + old.getYValue());
                        old = seriesELKConsCPU.remove(0);
                        seriesELKConsCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesELKCons.add(n, time);
                        seriesELKConsMemory.add(n, memory);
                        seriesELKConsCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 3){
                    if (i > 8+6*(iterations-1)){
                        XYDataItem old = seriesELKIC.remove(0);
                        seriesELKIC.add(n, time + old.getYValue());
                        old = seriesELKICMemory.remove(0);
                        seriesELKICMemory.add(n, memory + old.getYValue());
                        old = seriesELKICCPU.remove(0);
                        seriesELKICCPU.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesELKIC.add(n, time);
                        seriesELKICMemory.add(n, memory);
                        seriesELKICCPU.add(n, cpu*100);
                    }
                }
                else if (i%6 == 4){
                    if (i > 9+6*(iterations-1)){
                        XYDataItem old = seriesELKSatTB.remove(0);
                        seriesELKSatTB.add(n, time + old.getYValue());
                        old = seriesELKSatMemoryTB.remove(0);
                        seriesELKSatMemoryTB.add(n, memory + old.getYValue());
                        old = seriesELKSatCPUTB.remove(0);
                        seriesELKSatCPUTB.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesELKSatTB.add(n, time);
                        seriesELKSatMemoryTB.add(n, memory);
                        seriesELKSatCPUTB.add(n, cpu*100);
                    }
                }
                else{
                    if (i > 10+6*(iterations-1)){
                        XYDataItem old = seriesELKClaTB.remove(0);
                        seriesELKClaTB.add(n, time + old.getYValue());
                        old = seriesELKClaMemoryTB.remove(0);
                        seriesELKClaMemoryTB.add(n, memory + old.getYValue());
                        old = seriesELKClaCPUTB.remove(0);
                        seriesELKClaCPUTB.add(n, cpu*100 + old.getYValue());
                    }
                    else {
                        seriesELKClaTB.add(n, time);
                        seriesELKClaMemoryTB.add(n, memory);
                        seriesELKClaCPUTB.add(n, cpu*100);
                    }
                }
                i++;
            }
            reader.close();



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
                    JFreeChart chartSat = createChart(datasetSat, "Satisfiability KB", "Time (milliseconds)");
                    ChartUtilities.saveChartAsPNG(new File("SatisfiabilityKB.png"), chartSat, 450, 400);
                    JFreeChart chartSatMemory = createChart(datasetSatMemory, "Satisfiability Memory KB", "Memory (%)");
                    ChartUtilities.saveChartAsPNG(new File("SatisfiabilityMemoryKB.png"), chartSatMemory, 450, 400);
                    JFreeChart chartSatCPU = createChart(datasetSatCPU, "Satisfiability CPU KB", "CPU (%)");
                    ChartUtilities.saveChartAsPNG(new File("SatisfiabilityCPUKB.png"), chartSatCPU, 450, 400);
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
                    JFreeChart chartCla = createChart(datasetCla, "Classify KB", "Time (milliseconds)");
                    ChartUtilities.saveChartAsPNG(new File("ClassifyKB.png"), chartCla, 450, 400);
                    JFreeChart chartClaMemory = createChart(datasetClaMemory, "Classify Memory KB", "Memory (%)");
                    ChartUtilities.saveChartAsPNG(new File("ClassifyMemoryKB.png"), chartClaMemory, 450, 400);
                    JFreeChart chartClaCPU = createChart(datasetClaCPU, "Classify CPU KB", "CPU (%)");
                    ChartUtilities.saveChartAsPNG(new File("ClassifyCPUKB.png"), chartClaCPU, 450, 400);



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
                    JFreeChart chartCons = createChart(datasetCons, "Consistency KB", "Time (microseconds)");
                    ChartUtilities.saveChartAsPNG(new File("ConsistencyKB.png"), chartCons, 450, 400);
                    JFreeChart chartConsMemory = createChart(datasetConsMemory, "Consistency Memory KB", "Memory (%)");
                    ChartUtilities.saveChartAsPNG(new File("ConsistencyMemoryKBpng"), chartConsMemory, 450, 400);
                    JFreeChart chartConsCPU = createChart(datasetConsCPU, "Consistency CPU KB", "CPU (%)");
                    ChartUtilities.saveChartAsPNG(new File("ConsistencyCPUKB.png"), chartConsCPU, 450, 400);
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
                    JFreeChart chartIC = createChart(datasetIC, "Instance checking KB", "Time (milliseconds)");
                    ChartUtilities.saveChartAsPNG(new File("InstanceCheckingKB.png"), chartIC, 450, 400);
                    JFreeChart chartICMemory = createChart(datasetICMemory, "Instance checking Memory KB", "Memory (%)");
                    ChartUtilities.saveChartAsPNG(new File("InstanceCheckingMemoryKB.png"), chartICMemory, 450, 400);
                    JFreeChart chartICCPU = createChart(datasetICCPU, "Instance checking CPU KB", "CPU (%)");
                    ChartUtilities.saveChartAsPNG(new File("InstanceCheckingCPUKB.png"), chartICCPU, 450, 400);




                    var datasetSatTB = new XYSeriesCollection();
                    datasetSatTB.addSeries(seriesHermitSatTB);
                    datasetSatTB.addSeries(seriesPelletSatTB);
                    datasetSatTB.addSeries(seriesJFactSatTB);
                    datasetSatTB.addSeries(seriesELKSatTB);
                    var datasetSatMemoryTB = new XYSeriesCollection();
                    datasetSatMemoryTB.addSeries(seriesHermitSatMemoryTB);
                    datasetSatMemoryTB.addSeries(seriesPelletSatMemoryTB);
                    datasetSatMemoryTB.addSeries(seriesJFactSatMemoryTB);
                    datasetSatMemoryTB.addSeries(seriesELKSatMemoryTB);
                    var datasetSatCPUTB = new XYSeriesCollection();
                    datasetSatCPUTB.addSeries(seriesHermitSatCPUTB);
                    datasetSatCPUTB.addSeries(seriesPelletSatCPUTB);
                    datasetSatCPUTB.addSeries(seriesJFactSatCPUTB);
                    datasetSatCPUTB.addSeries(seriesELKSatCPUTB);
                    JFreeChart chartSatTB = createChart(datasetSatTB, "Satisfiability TBox", "Time (milliseconds)");
                    ChartUtilities.saveChartAsPNG(new File("SatisfiabilityTBox.png"), chartSatTB, 450, 400);
                    JFreeChart chartSatMemoryTB = createChart(datasetSatMemoryTB, "Satisfiability Memory TBox", "Memory (%)");
                    ChartUtilities.saveChartAsPNG(new File("SatisfiabilityMemoryTBox.png"), chartSatMemoryTB, 450, 400);
                    JFreeChart chartSatCPUTB = createChart(datasetSatCPUTB, "Satisfiability CPU TBox", "CPU (%)");
                    ChartUtilities.saveChartAsPNG(new File("SatisfiabilityCPUTB.png"), chartSatCPUTB, 450, 400);
                    var datasetClaTB = new XYSeriesCollection();
                    datasetClaTB.addSeries(seriesHermitClaTB);
                    datasetClaTB.addSeries(seriesPelletClaTB);
                    datasetClaTB.addSeries(seriesJFactClaTB);
                    datasetClaTB.addSeries(seriesELKClaTB);
                    var datasetClaMemoryTB = new XYSeriesCollection();
                    datasetClaMemoryTB.addSeries(seriesHermitClaMemoryTB);
                    datasetClaMemoryTB.addSeries(seriesPelletClaMemoryTB);
                    datasetClaMemoryTB.addSeries(seriesJFactClaMemoryTB);
                    datasetClaMemoryTB.addSeries(seriesELKClaMemoryTB);
                    var datasetClaCPUTB = new XYSeriesCollection();
                    datasetClaCPUTB.addSeries(seriesHermitClaCPUTB);
                    datasetClaCPUTB.addSeries(seriesPelletClaCPUTB);
                    datasetClaCPUTB.addSeries(seriesJFactClaCPUTB);
                    datasetClaCPUTB.addSeries(seriesELKClaCPUTB);
                    JFreeChart chartClaTB = createChart(datasetClaTB, "Classify TBox", "Time (milliseconds)");
                    ChartUtilities.saveChartAsPNG(new File("ClassifyTB.png"), chartClaTB, 450, 400);
                    JFreeChart chartClaMemoryTB = createChart(datasetClaMemoryTB, "Classify Memory TBox", "Memory (%)");
                    ChartUtilities.saveChartAsPNG(new File("ClassifyMemoryTB.png"), chartClaMemoryTB, 450, 400);
                    JFreeChart chartClaCPUTB = createChart(datasetClaCPUTB, "Classify CPU TBox", "CPU (%)");
                    ChartUtilities.saveChartAsPNG(new File("ClassifyCPUTB.png"), chartClaCPUTB, 450, 400);


        }catch (Exception e){
            e.printStackTrace();
        }

    }
}