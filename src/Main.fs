(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Main.fs: console e codice main
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Main

open Microsoft.FSharp.Text.Lexing
open Absyn
open System
open Prelude
open Microsoft.FSharp.Text

// funzioni di logging e printing
//

let hout hd fmt =
    if not <| String.IsNullOrWhiteSpace hd then
        printf "[%s]%s" hd (new String (' ', max 1 (Config.prefix_max_len - String.length hd)))
        stdout.Flush ()
    printfn fmt

let chout col hd fmt =
    let c = Console.ForegroundColor
    Console.ForegroundColor <- col
    Printf.kprintf (fun s -> hout hd "%s" s; Console.ForegroundColor <- c) fmt

let out fmt = hout "" fmt
let cout col fmt = chout col "" fmt

// sono state aggiunte derived, integral, degree
let redux fmt = chout ConsoleColor.Magenta "redux" fmt
let norm fmt = chout ConsoleColor.Yellow "norm" fmt

let derived fmt = chout ConsoleColor.Blue "derive" fmt
let integral fmt = chout ConsoleColor.Cyan "integral" fmt    

let degree fmt = chout ConsoleColor.DarkYellow "degree" fmt
let sol fmt = chout ConsoleColor.Green "sol" fmt
let ident fmt = chout ConsoleColor.Green "ident" fmt    
let error fmt = chout ConsoleColor.Red "error" fmt   

// Variabili aggiuntive
// posizione array -> tipo di output
// [|1; x; x; x; x; x; x|] -> polinomio ridotto
// [|x; 1; x; x; x; x; x|] -> polinomio normalizzato
// [|x; x; 1; x; x; x; x|] -> derivata
// [|x; x; x; 1; x; x; x|] -> integrale
// [|x; x; x; x; 1; x; x|] -> grado polinomio
// [|x; x; x; x; x; 1; x|] -> soluzioni dell'equazione
// [|x; x; x; x; x; x; 1|] -> derivata
let mutable arrayimpostazioni = Array.create 7 1
// Settings del grafico
// precisione serve ad aumentare il numero di punti che compongono il grafico
let mutable precisione = 1.0
// server per effettuare ingrandire o dimunuire la dimensione dei valori (da usare in funzioni con grado >= 2 )
let mutable fattoreScala = 1.0
// Easter egg (funzione plot)
let mutable rainbowMode = 0
//-----------------------------------------------------------------

// interprete dei comandi e delle espressioni
//

let interpreter_loop () =
    while true do
        printf "\n%s" Config.prompt_prefix          // stampa il prompt
        stdout.Flush ()                             // per sicurezza flusha lo stdout per vedere la stampa del prompt senza end-of-line
        let input = Console.ReadLine ()             // leggi l'input scritto dall'utente
        let lexbuf = LexBuffer<_>.FromString input  // crea un lexbuffer sulla stringa di input


        // funzione locale per il pretty-printing degli errori
        let localized_error msg =
            let tabs = new string (' ', Config.prompt_prefix.Length + lexbuf.StartPos.Column)
            let cuts = new string ('^', let n = lexbuf.EndPos.Column - lexbuf.StartPos.Column in if n > 0 then n else 1)
            cout ConsoleColor.Yellow "%s%s\n" tabs cuts
            error "error at %d-%d: %s" lexbuf.StartPos.Column lexbuf.EndPos.Column msg 
        
        // blocco con trapping delle eccezioni
        try
            let line = Parser.line Lexer.tokenize lexbuf    // invoca il parser sul lexbuffer usando il lexer come tokenizzatore
            #if DEBUG
            hout "absyn" "%+A" line
            hout "pretty" "%O" line
            #endif

            // interpreta la linea in base al valore di tipo line prodotto dal parsing
            match line with
            | Cmd "help" ->
                out "%s" Config.help_text

            | Cmd ("quit" | "exit") ->
                out "%s" Config.exit_text
                exit 0

            // TODO: se volete supportare altri comandi, fatelo qui (opzionale)
            // chiedo quali funzioni voglio che vengano mostrate ( e quindi calcolate) e quali no (con controllo dell'input)
            | Cmd ("settings") -> 
                Console.Clear ()
                out "\n Press 1 to allow or 0 to decline"
                let mutable counter = 0
                while counter < (arrayimpostazioni.Length) do 
                    out " Show %s ? (1/0) " Config.impostazioniTesto.[counter]
                    printf " "
                    let value = Int32.Parse( Console.ReadLine ())
                    if value = 0 || value = 1 then 
                        arrayimpostazioni.[counter] <-  value
                    else 
                        out " Write 1 or 0"
                        (counter <- counter - 1 )
                    counter <- counter + 1
                Console.Clear ()
                out " Settings changed"
            //comando per pulire la schermata
            | Cmd ("clear") -> Console.Clear ()
            //comando per modificare i 3 settaggi per stampare il grafico (con controllo dell'input)
            | Cmd ("plot") ->
                Console.Clear ()
                let mutable i = true
                while i do 
                    out "\n Set plot scale "
                    fattoreScala <- parse_float( Console.ReadLine ())
                    if fattoreScala <= 0.0 then 
                        out "Value not reconized "
                    else 
                        i <- false
                i <- true
                while i do 
                    out "\n Set plot precision "
                    precisione <- parse_float( Console.ReadLine ())
                    if precisione <= 0.0 then 
                        out "\n Value not reconized"
                    else 
                        if precisione < 0.0001 && precisione > 0.0 then 
                            out "\n Attenzione per valori inferiori di 0.00001 è possibile un rallentamento nella visualizzazione del grafico \n Accettare (y/n) ?"
                            if Console.ReadLine() = "y" then
                                i <- false
                        else 
                            i <- false
                out "\n Activate rainbowMode ?"
                out " Press 1 to allow "
                rainbowMode <- Int32.Parse( Console.ReadLine ())
                Console.Clear ()

            //-----------------------------------------------------------------
            | Cmd s -> error "unknown command: %s" s    // i comandi non conosciuti cadono in questo caso

            // TODO: aggiungere qui sotto i pattern per i casi Expr ed Equ con relativo codice per, rispettivamente, normalizzare espressioni e risolvere equazioni
            // oltre mostrare il valore di redux, viene mostrata sia la derivata che l'integrale del valore output di redux (simile a studio di funzione)

            | Expr expr -> 
                // sezione generale
                let polinomio = Impl.reduce expr
                let norma = Impl.normalize polinomio
                
                // sezione specifica (controllo fatto da #settings)
                if (arrayimpostazioni.[0]=1) then redux "%O" polinomio
                if (arrayimpostazioni.[1]=1) then norm "%O" norma 
                if (arrayimpostazioni.[2]=1) then derived "%O" (Impl.normalize (Impl.derive polinomio))
                if (arrayimpostazioni.[3]=1) then integral "c + %O" (Impl.normalize (Impl.integral  polinomio)) 
                if (arrayimpostazioni.[4]=1) then degree "%i" (Impl.normalized_polynomial_degree norma) 
                if (arrayimpostazioni.[6]=1) then Impl.plot norma fattoreScala precisione rainbowMode         
                                                         
            | Equ (expr1,expr2) -> 
                // sezione generale
                let polinomioSx = Impl.reduce expr1
                let polinomioDx = Impl.reduce expr2
                let polinomio =  
                    match polinomioSx,Impl.polynomial_negate polinomioDx with               
                        (Polynomial listaMonomi1),(Polynomial listaMonomi2) ->Polynomial (listaMonomi1@listaMonomi2)
                let norma = Impl.normalize polinomio
                let polinomioGrado =  Impl.normalized_polynomial_degree norma
                                    
                // sezione specifica (controllo fatto da #settings)
                if (arrayimpostazioni.[0]=1) then redux "%O = %O" polinomioSx polinomioDx
                if (arrayimpostazioni.[1]=1) then norm "%O = 0" norma 
                if (arrayimpostazioni.[2]=1) then derived "%O" (Impl.normalize (Impl.derive polinomio))
                if (arrayimpostazioni.[3]=1) then integral "c + %O" (Impl.normalize (Impl.integral  polinomio)) 
                if (arrayimpostazioni.[4]=1) then degree "%i" (Impl.normalized_polynomial_degree norma) 
                // Sezione di solve0/1/2/infinito, le soluzioni superiori al secondo grado saranno SOLO razionali (congrue al tipo rational)
                // utilizzo error per segnalare casi con nessuna soluzione
                // utilizzo la variabile soluzioni come accumulatore in cui riporre gli output di tutte le funzioni che usano sol per stampare
                if (arrayimpostazioni.[5]=1) then 
                    let mutable error = false
                    let mutable soluzioni = ""
                    if polinomioGrado = 0 then  ident "%O" (Impl.solve0 norma)
                    else 
                        if polinomioGrado = 1 then 
                            soluzioni <- "x = " + (Impl.solve1 norma).ToString() 
                        elif polinomioGrado = 2 then 
                            match (Impl.solve2 norma) with 
                            | None ->  error <- true 
                            | (Some (x1 , None)) -> soluzioni <- "x = " + x1.ToString()
                            | (Some (x1 , Some x2)) -> soluzioni <- "x1 = " + x1.ToString() + " vel x2 = " + x2.ToString() 
                        elif polinomioGrado > 2  then 
                            let mutable counter = 1 
                            let x  = Impl.universal_solve norma
                            if x <> [] then 
                                for i in x do
                                    soluzioni <-soluzioni + "x" + counter.ToString() + " = " + i.ToString() + " vel "
                                    counter <- counter + 1
                            else 
                                error <- true
                            if soluzioni.Length>4 then
                                soluzioni <- soluzioni.Remove(soluzioni.Length - 4)
                        else soluzioni <- "Grado non supportato"
                        if error then 
                            soluzioni <- "Non esistono soluzioni razionali"
                        sol "%O" soluzioni
                if (arrayimpostazioni.[6]=1) then Impl.plot norma fattoreScala precisione rainbowMode          

            //-----------------------------------------------------------------

            | _ -> raise (NotImplementedException (sprintf "unknown command or expression: %O" line))
                   
        // gestione delle eccezioni
        with LexYacc.ParseErrorContextException ctx ->
                let ctx = ctx :?> Parsing.ParseErrorContext<Parser.token>
                localized_error (sprintf "syntax error%s" (match ctx.CurrentToken with Some t -> sprintf " at token <%O>" t | None -> ""))

           | Lexer.LexerError msg -> localized_error msg 

           | :? NotImplementedException as e -> error "%O" e
        
           | e -> localized_error e.Message


// funzione main: il programma comincia da qui
//

[<EntryPoint>]
let main _ = 
    let code =
        try
            interpreter_loop ()                 // chiama l'interprete
            0                                   // ritorna il codice di errore 0 (nessun errore) al sistema operativo se tutto è andato liscio
        with e -> error "fatal error: %O" e; 1  // in caso di eccezione esce con codice di errore 1
    #if DEBUG
    Console.ReadKey () |> ignore                // aspetta la pressione di un tasto prima di chiudere la finestra del terminare 
    #endif
    code


