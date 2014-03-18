#|
Interrogates a database given the specified query. Returns a list of substitutions.
|#

;; utility functions

#|
Checks if the provided value is a variable
|#
(define (variable? sym)
  (and (symbol? sym) (equal? (string-ref (symbol->string sym) 0) #\?)))

#| functie ce intoarce variabilele dintr-o lista, in membrul al II lea |#
(define getVars
  (λ (L result)
    (if (null? L)
        result
        (if (list? (car L))
            (getVars (cdr L) (append result (getVars (car L) null))) ;daca car L e lista, caut recursiv in interior ei.
            ;else
            (if (variable? (car L))
                (getVars (cdr L) (append result (cons (car L) null))) ;daca e variabila, o bag in lista
                ;else
                (getVars (cdr L) result) ;altfel, trec mai departe
                )))))

(require (lib "trace.ss"))

#| functie ce primeste o lista - de tipul L - si o variabila, var, 
si intoarce o lista cu 2 elem, (var value) daca var exista, null in caz contrar |#
(define getVal
  (λ (L var); result)
    (if (null? L)
        L
        (if (list? (car L))
            (if (not (null? (cdr L)))
                (append (getVal (car L) var) (getVal (cdr L) var)); cauta recursiv si in dreapta listei
                (getVal (car L) var))
            ;else nu e lista
            (if (variable? (car L)) ;daca primul elem e var, si e cea cautata, intorc rezultatul, perechea (?var value)
                (if (equal? (car L) var)
                    ;(cons (car L) result)
                    L
                    null)
                (getVal (cdr L) var)))))); result))))


#| functie ce inlocuieste variabilele din lista Q, cu valoarea variabilelor din lista L |#
(define replaceVars
  (λ (Q L result)
    (if (null? L)
        Q
        (if (null? Q)
            (reverse result)
            ;altfel Q si L nu sunt nule
            (if (variable? (car Q))
                (let ((val (getVal L (car Q))));acum am in (cdr val) valoarea variabilei
                  ;(if (not (null? (cdr Q)))
                  (if (null? val)
                      (replaceVars (cdr Q) L (append (cons (car Q) null) result))
                      (replaceVars (cdr Q) L (append (cdr val) result))))
                ;altfel: (car Q) nu e variabila
                (if (list? (car Q))
                    (replaceVars (cdr Q) L (cons (replaceVars (car Q) L null) result))
                    (replaceVars (cdr Q) L (append (cons (car Q) null) result))))))))


#| functie ce primeste o lista src si una ldb, si face match intre src si dbl (daca se potrivesc, intoarce var legate la val potrivite) |#
(define matchLists
  (λ (src ldb result)
    (if (not (equal? (length src) (length ldb))) 
        #f
        (if (null? src)            
            (reverse result)
            (let* ((var (car src)) (val (car ldb)) (match (list var val)))
              (if (variable? var)
                  (matchLists (cdr src) (cdr ldb) (cons match result));pun in rezultat perechea (var val)   
                  (if (list? var) ;daca var e lista, trec prin ea, si merg mai departe
                      (if (list? val);daca si val e lista
                          ;tratez si cazul in care, aceasta lista e null, tot rezultatul tb sa fie null!!
                          (let ((rz (matchLists var val null)))
                            (if (null? rz)
                                (matchLists (cdr src) (cdr ldb) result)
                                (if (equal? #f rz)
                                    #f
                                    (matchLists (cdr src) (cdr ldb) (append rz result)))))
                          ;(matchLists (cdr src) (cdr ldb) (append (matchLists var val null) result));le prelucrez pe aman2 si merg mai departe
                          ;altfel, not match
                          null)
                      ;daca nu e nici variabila, nici lista, e un cuvant de legatura: am 2 cazuri, fie se potrivesc fie nu
                      (if (equal? var val)
                          (matchLists (cdr src) (cdr ldb)  result);e ok, merg mai departe
                          #f))))))))

#| funct ce intoarce ce contine SEARCH |#
(define takeSearch
  (λ (query)
    (cdar query)))

#| funct ce intoarce ce contine SELECT |#
(define takeSelect
  (λ (query)
    (cdar (cdr query))))

#| functie ce aplica matchLists pe un intreg db, si primeste ca param, un querry si db |#
(define applyMatchLists
  (λ (pattern db)
    (let* ((rezult (map (λ (x)
                   (matchLists pattern x null)) 
                 db))           
           (noMatch? (foldl (λ (x y)
                              (if (equal? x y)
                                  #f
                                  #t)) #f rezult)))
      (if (equal? noMatch? #f)
          #f
          (filter (λ (y)
                    (not (equal? #f y))) 
                  (map (λ (x)
                         (matchLists pattern x null)) 
                       db))))))

#| am o selectie, in oldsel, care vreau sa o adaug la inceputul fiecarui elem din newsel|#
(define extendSelected
  (λ (oldsel newsel pattern db)
    (let ((newBound (applyMatchLists pattern db)))
      ;creez o lista noua, in care adaug fiecare rezultat ob
      ;la vechea selectie, selectia noua, avand atatea elemenete
      ;cata are newsel - practic adaug oldsel in fata fiecarui
      ;element din newsel- . In cazul in care newsel e null, nu s-a
      ;gasit nicio potrivire, deci nu e bine, intorc null
      (if (equal? #f newBound)
          newsel
          (if (null? (car newBound))
              (append newsel (cons oldsel null))
              (append newsel (map (λ (x)
                                    (append oldsel x))
                                  newBound)))))))


(define compute1Querry
  (λ (qr db S)
    (if (equal? (car qr) 'if) ;daca e un predicat
        (if (areBounded? qr S) ;testez daca e un predicat valid
            (ifEval qr S null) ;daca da, il aplic ifEval
            null ;aici nu intra niciodata
            )
            (if (null? S)
                null
                ;acum am un pattern = car search
                ;si S-ul meu cu toate val de pana acuma
                ;pt fiecare car din S, tb sa fac, replaceVars peste pattern
                ;si sa apelez pattern-ul pe tot DB,si imi rezulta un matchList
                (let computeSel ((oldsel S) (newsel null))
                  (let* ((pattern (replaceVars qr (car oldsel) null)) 
                         (newsel2 (extendSelected (car oldsel) newsel pattern db)))                
                    (if (null? (cdr oldsel))
                        newsel2
                        (computeSel (cdr oldsel) newsel2))))))))


(define computeAllQuerries
  (λ (querry db S)
    (if (null? querry)
        S
        (let ((newS (compute1Querry (car querry) db S)))
          (computeAllQuerries (cdr querry) db newS)))))


#| folosesc aceasta functie, ca parametru pentru filter, in functia ce urmeaza -> select |#
(define comparator
  (λ (lst bound)
    (let* ((rez (map (λ (y)
                      (equal? (car bound) y))
                    lst))
           (rez2 (filter (λ (z) 
                            (equal? z #t))
                          rez)))
      (if (null? rez2)
          #f
          #t))))


#| functie ce ia dintr-o lista de solutii, doar variabilele din SELECT |#
(define select
  (λ (choices what selection)
    (if (null? choices)
        selection
        (if (null? what)
            choices
            (let* ((line (car choices))
                  (rez (filter (λ (x) 
                                 (comparator what x))
                               line)))
              (if (null? selection)
                  (select (cdr choices) what (list rez))
                  (select (cdr choices) what (cons rez selection))))))))
                    
      
(define ask
  (λ (db query)
    (let ((search (takeSearch query)) (whatToSelect (takeSelect query)))
      (let* ((choices (computeAllQuerries search db '(()) ))
             (validChoices (validateAllChoices choices)))
        (if (areBounded? whatToSelect validChoices)
            (select validChoices (car whatToSelect) null)
            null;aici nu se ajunge niciodata
            )))))



#| functie care sterge duplicatele |#
(define keepUnique
  (λ (lst result)
    (if (null? lst)
        (reverse result)
        (let iter ((elem (car lst)) (r result))
          (if (null? r)
              (keepUnique (cdr lst) (cons elem result))
              (if (equal? elem (car r))
                  (keepUnique (cdr lst) result)
                  (iter elem (cdr r))))))))

        




#| functie ce evalueaza un predicat, dintr-un query 
   primeste 3 parametri:
   - ifExpr = toata linia if din query
   - S = lista de solutii ce am obtinut-o pana am ajuns la if-ul din query
   - newS = noua lista de solutii, dupa ce am filtrat-o (am pastrat doar ce trecea de if)
|#
(define ifEval
  (λ (ifExpr S newS)
    (if (null? S)
        newS
        (let* ((sel (car S)) (ifStatement (replaceVars ifExpr sel null)))
          (if (eval (cadr ifStatement))
              (if (null? newS)
                  (ifEval ifExpr (cdr S) (list sel))
                  (ifEval ifExpr (cdr S) (cons sel newS)))
              (ifEval ifExpr (cdr S) newS))))))
    
        

#|functie ce verefica daca variabilele sunt legate corect,
  si anume, sa nu exista o variabila, legata la 2 valori, in acelasi timp |#
(define validate1Choice
  (λ (choice result)
    (if (null? choice)
        (if (null? result)
            null
            (reverse result))
        (let iter ((x (car choice)) (y result))
          (if (null? y)
              (validate1Choice (cdr choice) (cons x result))
              ;verific daca var e in result, si daca e, verif daca are
              ;aceeasi valoare cu val din var.
              (if (equal? (car x) (caar y)) ;var1 == var2
                  (if (equal? (cadr x) (cadr (car y))) ;val1 == val2
                      (validate1Choice (cdr choice) result) ;ok, trec peste sa nu am 2 var la fel, result ramane acelasi
                      (validate1Choice null null));nu e bine, am 2 var care sunt legate la valori diferite, tb sa sterg aceasta intrare
                  (iter x (cdr y))))))))

#| functie care valideaza toate alegerile, nu doar una |#
(define validateAllChoices
  (λ (choices)
    (let* ((result1 (map (λ (x)
                           (validate1Choice x null))
                         choices))
           (result2 (filter (λ (y)
                              (not (null? y)))
                            result1)))
      (if (null? result2)
          '(())
          result2))))


#|functie care verifica daca variabilele din if sunt legate.
  daca nu sunt arunca exceptie
  parametrii primiti sunt:
  - ifExpr = expresia if luata din query
  - choices = solutiile pana la momentul respectiv
|#
(define areBounded?
  (λ (ifExpr choices)
    (let ((ifVars (getVars ifExpr null)) (boundedVars (keepUnique (getVars choices null) null)))
      (let iter ((v ifVars))
        (if (null? v)
            #t
            (if (equal? #f (member (car v) boundedVars))
                (error "Unbound variable exception" (car v))
                (iter (cdr v))))))))
