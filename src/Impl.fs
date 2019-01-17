
(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Impl.fsi: implementazioni degli studenti
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Impl

open Absyn
open Prelude
open System

//tipo utilizzato durante universalSolve, serve a distinguere il caso in cui non trovo un divisore (No) dal caso in cui lo trovo (Un rational)
type errore =  No |Un of rational 

//array con i vari colori 
let raibowArr = [|ConsoleColor.Magenta;ConsoleColor.Blue;ConsoleColor.Green;ConsoleColor.Yellow;ConsoleColor.DarkYellow;ConsoleColor.Red|]
//contatore per calcoare a che punto di rainbowArr ci si trova
let mutable contatore = 0
//funzione utile a stampare il grafico in rainbowMode
let coloraConsole c = 
    let coloreBase = Console.ForegroundColor
    Console.ForegroundColor <- raibowArr.[contatore]
    printf "%c" c
    Console.ForegroundColor <- coloreBase
    contatore <- contatore + 1
    if contatore = 6 then 
        contatore <- 0
    
    


//ho aggiunto il try per evitare il caso in cui l'input sia x.000 . . . (x indica qualsiasi valore) 
let rationalize (x : float) : rational = 
    try
        let numero = x.ToString().Split(',')
        rational ( Int32.Parse (numero.[0]+numero.[1]) , int ( 10.0**( float numero.[1].Length)))
    with 
        e -> rational (int x,1) 

let monomial_degree (m : monomial) : int = 
    let (Monomial (_ , esponente)) = m
    esponente

let monomial_negate (m : monomial) : monomial =
    let (Monomial (coefficeinte , esponente)) = m
    Monomial (coefficeinte*(-1Q),esponente )


// tramite map applico la funzione monomial negate ad ogni elemento della lista 
// mentre con max calcolo il valore massimo 
let polynomial_degree (p : polynomial) : int = 
    let (Polynomial lista) = p
    List.max(List.map (fun x -> monomial_degree x) lista)

// tramite map applico la funzione monomial negate ad ogni elemento della lista  
let polynomial_negate (p : polynomial) : polynomial = 
    let ( Polynomial listaMonomi )= p
    Polynomial (List.map (fun x -> monomial_negate x) listaMonomi)

// sfruttando la struttura di normalized_polynomial calcolo il grado massimo
let normalized_polynomial_degree (np : normalized_polynomial) : int = 
    let (NormalizedPolynomial arrayRazionali)=np
    in arrayRazionali.Length-1

let normalize (p : polynomial) : normalized_polynomial = 
    let maxDegree = polynomial_degree p 
    let TempArr = Array.create (maxDegree+1) rational.Zero
    let (Polynomial (listaDiMonomi))  = p 
    for i=0 to maxDegree do
        let value = List.sum (
                        List.map 
                            (fun x -> match x with (Monomial (c,_))-> c)
                            (List.filter 
                                (fun x -> match x with (Monomial (_,e))-> e = i)
                                listaDiMonomi ))
        TempArr.[i] <- value
    let mutable maxSizeArr = 1
    try 
       maxSizeArr <- 1 + Array.findIndexBack (fun x -> x <> rational.Zero) TempArr 
    with 
        e -> maxSizeArr <- 1
    let res = Array.create maxSizeArr rational.Zero
    Array.Copy (TempArr,res,maxSizeArr)
    NormalizedPolynomial res
    


// tramite map applico una funzione ad ogni elemento della lista per derivarlo
let derive (p : polynomial) : polynomial = 
    let (Polynomial (listaDiMonomi))  = p 
    Polynomial 
        (List.map 
            (fun x ->
                match x with 
                    (Monomial (c,e))-> 
                        if e>0 then 
                            Monomial(c*(rational (e,1)),e-1) 
                        else 
                            Monomial(rational.Zero,0)) 
            listaDiMonomi)

// tramite map applico una funzione ad ogni elemento della lista per integrarlo
let integral (p : polynomial) : polynomial = 
    let (Polynomial (listaDiMonomi))  = p 
    Polynomial 
        (List.map 
            (fun x ->
                match x with 
                    (Monomial (c,e))-> 
                        Monomial(c/(rational (e+1,1)),e+1))
            listaDiMonomi)

// riduco expr ricorsivamente in un polinomio, a seconda di come è costituita deriverò, integrerò oppure ritornerò il polinomio 
let rec reduce (e : expr) : polynomial =
    match e with
        | Poly e -> e                 
        | Derive e -> derive (reduce e)
        | Integral e -> integral ( reduce e )
    

//controllo se l'unico valore che compone l'array è uguale a 0 
let solve0 (np : normalized_polynomial) : bool = 
    match np with 
        (NormalizedPolynomial numeri) -> 
            let numero = numeri.[0]
            numero = rational.Zero

//effettuo il calcolo per trovare il valore di x (-c/a)
let solve1 (np : normalized_polynomial) : rational = 
    match np with 
        (NormalizedPolynomial numeri) -> 
            let numero = numeri.[0]
            let x = numeri.[1]
            (numero*(rational (-1,1)))/x

//salvo come float a e b 
//il delta lo calcolo direttamente con i valori presi dall'array rational per usare rational.Pow
//se il delta è = 0 uso la formula ridotta (senza c) e calcolo x
//se delta > 0 allora calcolo x1 e x2
let solve2 (np : normalized_polynomial) : (float * float option) option = 
    let (NormalizedPolynomial razionaliArray) = np 
    let b = rational.op_Implicit razionaliArray.[1]
    let a = rational.op_Implicit razionaliArray.[2]
    let delta = (rational.Pow (razionaliArray.[1],2)) - ((rational (4,1))*razionaliArray.[2]*razionaliArray.[0]) 
    if delta = rational.Zero then Some (((-1.0) * b )/(2.0*a),None)
    elif delta > rational.Zero then 
        let parziale = sqrt(delta) 
        let x1 = (((-1.0) * b ) + parziale)/(2.0*a)
        let x2 = (((-1.0) * b ) - parziale)/(2.0*a)
        if x1 <> x2 then Some (x1,Some x2) 
        else Some (x1,None)           
    else None

//Universal solve è una fuznione che calcola tutte le soluzioni razionali poiche, per calcolarle non uso i float (poco precisi) ma i rational (molto precisi)
let rec universal_solve (normP:normalized_polynomial) : rational list= 
    let (NormalizedPolynomial norm) = normP 
    if norm.[0] <> rational.Zero then 
        //salvo i 2 valori utili per trovare i possibili zeri del polinomio
        let a0 = if norm.[0] < rational.Zero then -norm.[0]
                 else norm.[0]
        let an = if norm.[norm.Length-1] < rational.Zero then -norm.[norm.Length-1]
                 else norm.[norm.Length-1]
    
        //funzione di ordine sup per trovare i divisori, la funzione che passo specifica se il divisore diventerà numeratore o denominatore
        let rec findDiv numero divisore funzione  = 
            if divisore > numero then []
            else 
                if numero % divisore = 0 then 
                    (funzione divisore) :: findDiv numero (divisore+1) funzione 
                else 
                    findDiv numero (divisore+1) funzione 
        
        //con queste due funzioni combino 2 liste 
        let rec subCombina x divisoriAn funzione= 
            match divisoriAn with
                |[] -> []
                | y :: ys -> funzione x  y :: subCombina x ys funzione

        let rec combina divisoriA0 divisoriAn funzione =
            match divisoriA0 with 
                |[] -> []
                |x :: xs -> subCombina x divisoriAn funzione @ combina xs divisoriAn funzione       

        //tramite dinDiv in cui calcolo tutti i possibili divisori sia del primo valore dell'array che del ultimo 
        //e tramite la funzione che passo specifico se deve essere preso come numeratore o denominatore
        //tramite combina 
        let divA0D = findDiv a0.N 1 (fun x -> rational (x,1)) 
        let divA0N = findDiv a0.D 1 (fun x -> rational (1,x)) 
        let divA0 = combina divA0N divA0D (fun x y -> x*y)

        let divAnD = findDiv an.N 1 (fun x -> rational (x,1)) 
        let divAnN = findDiv an.D 1 (fun x -> rational (1,x)) 
        let divAn = combina divAnN divAnD (fun x y -> x*y)

        let divAll = combina divA0 divAn (fun x y ->Un (x / y))
        
        //funzione che data la lista di 
        let rec trovaZero divLista = 
            match divLista with
                | [] ->  No  //caso in cui non trovo divisori 
                | y :: ys -> 
                    //visto che la lista di divisori è solo positiva calcolo sia +divisore che -divisore  
                    let (Un divisore)= y  
                    let mutable zero = rational.Zero
                    zero <- zero + norm.[0]
                    for i=1 to norm.Length-1 do 
                        if norm.[i] <> rational.Zero then
                            zero <- zero + norm.[i] * divisore ** (i)
                    let mutable zeroNeg = rational.Zero
                    zeroNeg <-zeroNeg + norm.[0]
                    for i=1 to norm.Length-1 do 
                        if norm.[i] <> rational.Zero then
                            zeroNeg <-zeroNeg + norm.[i] * ((-divisore) ** (i))
                    //controllo quale dei due è uguale a 0 (se lo sono entrambi prima passa il positivo poi, alla prossima chiamata il valore negativo)
                    if zero = rational.Zero then Un divisore
                    elif zeroNeg = rational.Zero then Un -divisore 
                    else trovaZero ys

        try 
            match trovaZero divAll with
            | No ->   [] 
            | Un zero ->
                //trovato il valore che divide il polinomio effettuo ruffini per trovare il nuovo polinomio ridotto
                let newNorm = Array.create (norm.Length-1) rational.Zero
                let mutable tempValue = rational.Zero
                for i = (norm.Length-1) downto 0 do 
                    tempValue <- tempValue + norm.[i]  
                    if i-1>=0 then
                        newNorm.[i-1] <- tempValue     
                    tempValue <- tempValue * zero
                //continuo la ricorsione fino ad arrivare al caso in cui il polinomio ridotto sia di grado 1 
                if newNorm.Length > 2 then 
                    zero :: (universal_solve  (NormalizedPolynomial newNorm))
                else 
                    zero :: solve1 (NormalizedPolynomial newNorm) :: []
        with
            //il try è necessario poichè nella funzione trovaZero se vengono inserite funzioni con grado molto alto e/o coefficienti molto elevati è facile 
            //superare il limite di int
            e -> failwith "Valori troppo grandi per una variabile int"         
    else
        let newNorm = Array.create (norm.Length-1) rational.Zero
        for i = (norm.Length-1) downto 0 do 
            if i-1>=0 then
                newNorm.[i-1] <- norm.[i]        
        rational.Zero :: (universal_solve  (NormalizedPolynomial newNorm))       
        


let plot (normP:normalized_polynomial)(scala:float)(precisione:float)(raibowMode:int) : unit =
    printfn "[Plot]\n" 
    let (NormalizedPolynomial tempNorm) = normP 
    let norm = Array.create tempNorm.Length rational.Zero
    //aumento o diminuisco i valori dell'array tramite il valore scala
    //esempio scala = 10  tutti i valori vengono ingranditi e quindi viene effettuato uno zoom del grafico
    for i=0 to tempNorm.Length-1 do 
        norm.[i] <- tempNorm.[i] * rationalize scala
    let height = Console.WindowHeight
    let lenght = Console.WindowWidth-1
    //preparo la matrice con l'asse x e y
    let matrix = Array2D.create height lenght  ' '
    for counterI = 0 to (height-1) do 
        for counterJ = 0 to (lenght-1) do 
            if counterJ = (lenght/2) then matrix.SetValue( '|', counterI, counterJ) 
            if counterI = (height/2) then matrix.SetValue( '-', counterI, counterJ) 
    //max size identifica quanti valori di x possono essere scritti nel grafico senza superare i limiti della matrice
    let maxSizeGrafico = if height>lenght || norm.Length=1 then lenght else height 
    let mutable x_value = 0.0
    let mutable y_value = 0.0
    let mutable skip = 0.0
    let mutable i = 0
    try
        while i < maxSizeGrafico do
            //calcolo il valore di x e di y
            x_value <-  ((( - float maxSizeGrafico / 2.0) + float i) * skip)
            y_value <-     
                let mutable acc = 0.0
                for i = 0 to (norm.Length-1) do
                    acc <- (acc + float (norm.[i].N) * (( x_value) ** float i)) / float norm.[i].D
                acc
            //controllo se i valori possono essere scritti nella matrice 
            if (int x_value < maxSizeGrafico/2 && int x_value > -maxSizeGrafico/2 && int y_value < maxSizeGrafico/2 && int y_value > -maxSizeGrafico/2) 
            then 
                matrix.SetValue( 'o',height-(int y_value+(height/2)), int x_value+(lenght/2)) 
            //alcuni grafici aumentano di valore troppo rapidamente, quindi sarebbe comodo calcolare anche i valori intermedi tra gli interi 
            //tramite il valore di precisione diminuisco il divario tra i punti del grafico 
            //ad esempio con precisione = 0.1 e maxSizeGrafico = 30 vengono calcolati 30 * 10 valori 
            if  skip > 1.0 then 
                i <- i+1
                skip <- 0.0
            else 
                skip <- skip + 1.0 * precisione 
    with
        //Caso in cui per qualche motivo viene inserito un valore fuori dai limiti della matrice
        e -> failwith "Non è possibile creare i grafico con i valori inseriti "
    //sezione in cui viene stampato il grafico (normale o rainbow)
    for counterI = 0 to (height-1) do 
        for counterJ = 0 to (lenght-1) do 
            if raibowMode = 1 then 
                if matrix.[counterI,counterJ] = 'o' then
                    coloraConsole 'o'
                else
                    printf "%c" matrix.[counterI,counterJ]
            else 
                printf "%c" matrix.[counterI,counterJ]
        printfn ""