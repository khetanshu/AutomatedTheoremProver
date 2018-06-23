;Program    : Automated Theorem Prover
;Developer  : Khetanshu chauhan

;Coverage   : The program contains the implementation of tell, ask and resolve Interfaces for theorem prover
;*** P.S. To do a QUICK UNIT TESTING of the INTERFACES, simply run : (runTests)

;____________________________ APIs/Interfaces  (below) ______________________________

;@INPUT 
;alist - a list containing propositional statement
;blist - another list containing propositional statement
;@RETURN
;a resolution or #f or CONTRADICTION
(define (resolve alist blist)
  (cond 
        ((null? alist) blist)
        ((null? blist) alist)
        (#t (if (and  (and  (= (length alist) 1)(= (length blist) 1))
                      (equal? (negate (car alist)) (car blist))
                )
                'CONTRADICTION
               (let
                      (
                        (partA (resolve-internal alist blist '() 0) )
                        (partB (resolve-internal blist alist '() 0) )
                      )
                      (cond
                          ((and (equal? partA #f) (equal? partB #f))  #f)
                          ((and (equal? partA alist) (equal? partB blist))  #f)
                          (#t (remove-duplicates
                                      (append 
                                             (if (list? partA) partA '())
                                             (if (list? partB) partB '())
                                      )
                                      '()
                              )
                          )
                      )
                )
        )  
      )
  )
)

;@INPUT 
;clause - a CNF statement that needs to be saved in KB (Knowledge Base)
;@RETURN
;Status OK
(define (tell clause)
  (let*
      (
        (refindClause (removeTrueClauses (convert-to-CNF-for-tell clause))) 
      )
      (begin
        (set! KB (append KB refindClause) )  
        'OK
      )
  )
  
)

;@INPUT 
;clause - a proposition that needs to Resolve
;@RETURN
;if resolved then returns #t otherwise UNKNOWN
(define (ask clause)
  (begin
    (cond
        ((null? clause) ) 
        (#t 
            (let*
              (
                (proposition 
                             (if  (and (list? clause) (not (isOperator (car clause))))
                                  (negate-all clause)
                                  (removeTrueClauses (convert-to-CNF-for-ask clause))
                             )
                )
              )
              (begin
                (set! KB-CURSOR KB)
                (set! KB-CURSOR  (append  KB-CURSOR proposition))
                (kb-resolve)
              )
            )
        )
    )
  )
)

;________________________ Unit Testing Modules  (below) ___________________________

;This is the unit testing procedures - it would test all the interfaces tell, ask and resolve with the written testcase below
(define (runTests)
  (begin
    (display "____________( Testing Resolve Interfaces )_____________")
    (newline)
    (display "FORMAT (statment1 statment1 expectedOutput)")
    (newline)
    (newline)
    (test-resolve  testcasesForResolve)
    (newline)
    (newline)
    (display "____________( Testing Tell and Ask Interfaces )_____________")
    (newline)
    (display "FORMAT ( action{tell/ask} statement expectedOutput)")
    (newline)
    (newline)
    (test-tell-and-ask  testcasesForTellAndAsk)
  )
)  

;These are the testcases for Tell and Ask Interfaces
(define testcasesForTellAndAsk
    '(
        ;FORMAT ( action{tell/ask} statement expectedOutput)
        
        ;Scenario 1:
        ( tell ((NOT a) b) OK )
        ( tell ((NOT b) c) OK )
        ( tell (a) OK )
        ( ask (a) #t )
        (ask (c) #t)
        (ask (d) UNKNOWN)
        
        ;Scenario 2:
        (tell ((NOT A) B)  OK)
        (tell ((NOT B) C) OK)
        (tell (A) OK)
        (ask (C) #t)
        
        (tell (IMPLIES hasDog hasMess) OK)
        (tell (IMPLIES hasMess (NOT clean)) OK)
        (tell hasDog OK) 
        (ask hasDog #t)
        (ask clean UNKNOWN)
        (ask (NOT clean)  #t)
        (ask (IMPLIES hasDog (NOT clean)) #t)
        (ask hasCat UNKNOWN)
        (tell (IMPLIES hasMess hasDog) OK)
        (ask (BICONDITIONAL hasMess hasDog) #t) 
        
        ;Scenario 3:
        (tell (OR x (OR y z)) OK)
        (tell ((NOT x)) OK)
        (tell ((NOT y)) OK)
        (ask  (z) #t)
        
        ;scenario 4:
        (tell (OR P Q) OK)
        (tell (IMPLIES P R) OK)
        (tell (IMPLIES Q R) OK)
        (ask  (R) #t)
        
        ;scenario 5:
        (tell (IMPLIES (IMPLIES P Q) Q) OK)
        (tell (IMPLIES (IMPLIES P P) R) OK)
        (ask (R) #t)
        
        ;scenario 6:
        (tell (IMPLIES A6 B6) OK)
        (tell (IMPLIES B6 C6 ) OK)
        (tell A6 OK)
        (ask (c) #t)
        
        ;scenario 7:
        (tell (OR (AND A7 B7) (OR C7 D7)) OK)
        (tell (NOT (OR C7 D7)) OK)
        (tell ((NOT A7)) OK)
        (ask (B7) #t)
        
        ;scenario 8:
        (tell (IMPLIES A8 (AND B8 C8)) OK)
        (tell (IMPLIES (NOT B8) A8) OK)
        ;(ask (NOT (NOT A8)) #t)
        (ask B8 #t)
        (ask (OR B8 C8) #t)
        (ask (AND B8 (OR B8 C8)) #t)
        (tell D8 OK)
        (ask (AND (AND B8 D8) (OR B8 C8)) #t)
        (ask (AND (OR B8 (NOT A8)) (OR C8 (NOT A8))) #t)
        
        ;scenarios 9:
        (tell (a b c d) OK)
        (ask (a b c) #t)
        (ask d #t)
        
     )
)


;This is the unit testing procedures - it would test all the interfaces tell and ask  with the written testcase above
(define (test-tell-and-ask  testcases)
  (cond
    ((null? testcases) '.)
    (#t
        (let*
          (
            (testcase (car testcases))
            (action (car testcase))
            (clause (cadr testcase))
            (expectedOutput (caddr testcase))
            (result 
                    (cond
                        ((equal? action 'tell) (tell clause))
                        ((equal? action 'ask) (ask clause))
                    )
            )
          )
          (if (equal? result expectedOutput) 
                        (begin (display 
                                        (append '("$*$Passed! Test case:") 
                                                (list testcase)
                                                ; '(" {ActualOutout:") 
                                                ; (if(list? result) (list result)  (list result) )
                                                ; '("}")
                                        )
                                ) 
                                (newline)
                                (test-tell-and-ask  (cdr testcases))
                        )
                        (begin (display 
                                        (append '("<<<***!***>>>> Failed! Test case:") 
                                                (list testcase) 
                                                '(" {ActualOutout:") 
                                                (if(list? result) (list result)  (list result) )
                                                '("}")
                                        )
                                ) 
                                (newline)
                                (test-tell-and-ask (cdr testcases))
                        )
                        
          )
        )
    )
  )
)  

;These are the testcases for resolve Interfaces
(define testcasesForResolve
    '(
        ;FORMAT (statment1 statment1 expectedOutput)
        
        ;HAPPY-PATH scenarios
        ( (a (NOT b) c) (d (NOT f) b) (a c d (NOT f)) )
        ( (a b)  ((NOT b))  (a))
        ( (A (NOT B)) (B) (A) )
        ( (A  B (NOT C) (NOT D)) (C) (A B (NOT D)))
        ( (A (NOT B)) ((NOT A)) ((NOT B)) )
        ( (A B) ((NOT B) C) (A C))
        ( ((NOT A)(NOT B) C)   ((NOT D) B (NOT E))    ((NOT A) C (NOT D) (NOT E))  )
        
        
        ;NO RESOLUTION scenarios
        ( (a b) (c d) #f)
        ( (a b) ((NOT a) (NOT b)) #f )
        ( (a (NOT b)) ((NOT c) (NOT D))  #f  )
        
        
        ;CONTRADICTION scenarios
        ( (a) ((NOT a)) CONTRADICTION)
        ( ((NOT a)) (a) CONTRADICTION)
        ( ((NOT a)) (a)  CONTRADICTION)
        ( (((NOT a) b)) ((NOT ((NOT a) b))) CONTRADICTION)
        ( ((NOT ((NOT a) b))) (((NOT a) b))  CONTRADICTION)
     )
)


;This is the unit testing procedures - it would test all the interfaces resolve  with the written testcase above
(define (test-resolve  testcases)
  (cond
    ((null? testcases) '.)
    (#t
        (let*
          (
            (testcase (car testcases))
            (alist (car testcase))
            (blist (cadr testcase))
            (expectedOutput (caddr testcase))
            (result (resolve alist blist))
          )
          (if (equal? result expectedOutput) 
                        (begin (display 
                                        (append '("Passed! Test case:") 
                                                (list testcase)
                                                ; '(" {ActualOutout:") 
                                                ; (if(list? result) (list result)  (list result) )
                                                ; '("}")
                                        )
                                ) 
                                (newline)
                                (test-resolve (cdr testcases))
                        )
                        (begin (display 
                                        (append '("<*> Failed! Test case:") 
                                                (list testcase) 
                                                '(" {ActualOutout:") 
                                                (if(list? result) (list result)  (list result) )
                                                '("}")
                                        )
                                ) 
                                (newline)
                                (test-resolve (cdr testcases))
                        )
          )
        )
    )
  )
  
)  


;________________________ Tell and Ask internal modules (below) ___________________________

;This is Knowledge base. ONLY statements through 'tell' interfaces would be part of this Knowledge base
(define KB '())

;This is a supporting cursor or a temporary Knowledge which get used when a statement is asked through the 'ask' interface.
;Statements resolved during the resolution would be store in the this cursor not the actual KB
(define KB-CURSOR '())

;return #f iff there firstItem isnt an operator 
(define (isOperator firstItem)
  (cond
    ((equal? firstItem 'NOT) #t)
    ((equal? firstItem 'AND) #t)
    ((equal? firstItem 'OR) #t)
    ((equal? firstItem 'IMPLIES) #t)
    ((equal? firstItem 'BICONDITIONAL) #t)
    (#t #f)
  )
) 

;returns a list of negated literals
(define (negate-all clause)
  (cond
    ((null? clause) '())
    (#t (append (list (list (negate (car clause)))) (negate-all (cdr clause))))
  )  
  
)


;Given a list, like KB, it would remove the resolved clause. 
;For ex: clauses like (a (NOT a)) would be removed from the list as its always TRUE
(define (removeTrueClauses alist)
 (cond
      ((null? alist) '())  
      (#t (append 
              (let
                (
                  (clause (car alist))
                )
                (if (and (= (length clause) 2) (equal? (negate (car clause))  (cadr clause)))
                    '()
                    (list clause)
                )
              )
              (removeTrueClauses (cdr alist))
          )
      )  
   
 ) 
)  

;This procedure would convert a clause in its CNF form
(define (convert-to-CNF-for-ask clause)
  (cond
    ((null? clause) clause)
    ((not(list? clause)) (list (list (negate clause))))
    ((not (= (length clause) 3)) (list (list (negate clause))))
    (#t 
        (let*
          (
            (operator (car clause))
            ; (firstValue (cadr clause))
            ; (secondValue (caddr clause))
          ) 
          (cond
            ((equal? operator 'OR ) (negate-OR clause))
            ((equal? operator 'AND )  (negate-AND clause))
            ((equal? operator 'IMPLIES ) (negate-IMPLIES clause))
            ((equal? operator 'BICONDITIONAL ) (negate-BICONDITIONAL clause))
            (#t clause)
          )
      )
    )
  )
)

;This would return negated value of any OR clause
(define (negate-OR clause)
  (let*
          (
            (operator (car clause))
            (firstValue (cadr clause))
            (secondValue (caddr clause))
          ) 
          (cond
            ((equal? operator 'OR ) (list (list (negate firstValue)) (list (negate secondValue))))
            (#t clause)
          )
      )
)  

;This would return negated value of any AND clause
(define (negate-AND clause)
  (let*
          (
            (operator (car clause))
            (firstValue (cadr clause))
            (secondValue (caddr clause))
          ) 
          (cond
            ((equal? operator 'AND )  (list (list (negate firstValue) (negate secondValue)) ))
            (#t clause)
          )
      )
)

;This would return negated value of any IMPLIES clause
(define (negate-IMPLIES clause)
  (let*
          (
            (operator (car clause))
            (firstValue (cadr clause))
            (secondValue (caddr clause))
          ) 
          (cond
            ((equal? operator 'IMPLIES ) (list (list  firstValue) (list (negate secondValue))))
            (#t clause)
          )
      )
)
;This would return negated value of any BICONDITIONAL clause
(define (negate-BICONDITIONAL clause)
  (let*
          (
            (operator (car clause))
            (firstValue (cadr clause))
            (secondValue (caddr clause))
          ) 
          (cond
            ((equal? operator 'BICONDITIONAL ) (list (list  firstValue secondValue) (list (negate firstValue) (negate secondValue))))
            (#t clause)
          )
      )
)


;This would convert a OR clause in into its CNF form
(define (convert-OR-CNF firstValue secondValue)
  (cond
                    ;***** NORMAL scenarios ******
                    ; a , b
                    ( (and (not (list? firstValue ))   (not(list? secondValue)) )
                         (list (append (list firstValue) (list secondValue)))
                    )
                    ; a , (b)
                    ( (and (not (list? firstValue ))  (and (list? secondValue ) (< (length secondValue) 3)) )
                      (list (append (list firstValue) (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue)))
                    )
                    ; (a) , b
                    ( (and (and (list? firstValue ) (< (length firstValue) 3))  (not(list? secondValue)) )
                         (list (append (if (equal? (car firstValue) 'NOT) (list firstValue) firstValue) (list secondValue) ))
                    )
                    ; (a) , (b) 
                    ( (and 
                           (and (list? firstValue ) (< (length firstValue) 3))  
                           (and (list? secondValue ) (< (length secondValue) 3) ) )
                        (list  (append (if (equal? (car firstValue) 'NOT) (list firstValue) firstValue) 
                               (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue) 
                         ))
                    )
                  
                    ; (OR a b ) , (AND c d) 
                    ( (and 
                           (and (list? firstValue ) (equal? (car firstValue) 'OR) )
                           (and (list? secondValue ) (equal? (car secondValue) 'AND ))) 
                         (list 
                                     (append  (cdr firstValue) (list (cadr secondValue)))
                                     (append  (cdr firstValue) (list (caddr secondValue)))
                         )     
                    )
                    
                    ;***** AND - Any Scenarios ****** 
                    ; (AND a b ) , c 
                    ( (and (and (list? firstValue) (equal? (car firstValue) 'AND)) (not (list? secondValue ))) 
                         (list (append (list  (cadr firstValue)) (list  secondValue))
                               (append (list  (caddr firstValue)) (list  secondValue))
                         )     
                    )
                    ; (AND a b ) , (c) 
                    ( (and (and (list? firstValue) (equal? (car firstValue) 'AND)) 
                           (and (list? secondValue ) (< (length secondValue) 3))) 
                        (list (append (list  (cadr firstValue)) 
                                      (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue))
                               (append (list  (caddr firstValue)) 
                                       (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue))
                         )
                    )
                    
                    ; c, (AND a b )
                    ( (and (and (list? secondValue) (equal? (car secondValue) 'AND)) (not (list? firstValue ))) 
                         (list (append (list  (cadr secondValue)) (list  firstValue))
                               (append (list  (caddr secondValue)) (list  firstValue))
                         )     
                    )
                    ; (c) , (AND a b )
                    ( (and (and (list? secondValue) (equal? (car secondValue) 'AND)) 
                           (and (list? firstValue ) (< (length firstValue) 3))) 
                        (list (append (list  (cadr secondValue)) 
                                      (if (equal? (car firstValue) 'NOT) (list firstValue) firstValue))
                               (append (list  (caddr secondValue)) 
                                       (if (equal? (car firstValue) 'NOT) (list firstValue) firstValue))
                         )
                    )
                    
                    ; (AND a b ) , (OR c d) 
                    ( (and 
                           (and (list? firstValue ) (equal? (car firstValue) 'AND) )
                           (and (list? secondValue ) (equal? (car secondValue) 'OR ))) 
                         (list 
                                     (append  (list (cadr firstValue)) (cdr secondValue) )
                                     (append  (list (caddr firstValue)) (cdr secondValue) )
                         )     
                    )
                  
                    ; (AND a b ) , (AND c d) 
                    ( (and 
                           (and (list? firstValue ) (equal? (car firstValue) 'AND) )
                           (and (list? secondValue ) (equal? (car secondValue) 'AND ))) 
                              (list 
                                     (append  (list (cadr firstValue)) (list (cadr secondValue)))
                                     (append  (list (cadr firstValue)) (list (caddr secondValue)))
                                     (append  (list (caddr firstValue)) (list (cadr secondValue)))
                                     (append  (list (caddr firstValue)) (list (caddr secondValue)))
                         )     
                    )
                  
                     ;***** OR - OR Scenarios ******
                    (#t
                        (list (append 
                                (if (not (list? firstValue )) 
                                          (list firstValue)
                                          (cond
                                              ((< (length firstValue) 3) (list firstValue))
                                              ((equal? (car firstValue) 'OR ) 
                                                      (car (convert-OR-CNF (cadr firstValue) 
                                                                                  (caddr firstValue))))
                                          )        
                                ) 
                                (if (not (list? secondValue )) 
                                          (list secondValue)
                                          (cond
                                              ((< (length secondValue) 3) (list secondValue))
                                              ((equal? (car secondValue) 'OR ) 
                                                      (car (convert-OR-CNF (cadr secondValue) 
                                                                                  (caddr secondValue))))
                                          )        
                                )
                        ))
                    )
                    
                    
                  
  )                
   
)

;This would convert a AND clause in into its CNF form
(define (convert-AND-CNF firstValue secondValue)
  (cond
    
                    ;***** NORMAL scenarios ******
                    ; a , b
                    ( (and (not (list? firstValue ))   (not(list? secondValue)) )
                         (list (list firstValue) (list secondValue))
                    )
                    ; a , (b)
                    ( (and (not (list? firstValue ))  (and (list? secondValue ) (< (length secondValue) 3)) )
                      (list (list firstValue) (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue))
                    )
                    ; (a) , b
                    ( (and (and (list? firstValue ) (< (length firstValue) 3))  (not(list? secondValue)) )
                         (list (if (equal? (car firstValue) 'NOT) (list firstValue) firstValue) (list secondValue) )
                    )
                    ; (a) , (b) 
                    (   (and 
                               (and (list? firstValue) (< (length firstValue) 3))  
                               (and (list? secondValue) (< (length secondValue) 3))
                          ) 
                         (list (if (equal? (car firstValue) 'NOT) (list firstValue) firstValue) 
                               (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue) 
                         )
                    )
                  
                    ;***** OR - Any Scenarios ******  
                    ; (OR a b ) , c 
                    ( (and (and (list? firstValue) (equal? (car firstValue) 'OR)) (not (list? secondValue ))) 
                         (list (append (list  (cadr firstValue)) (list  secondValue))
                               (append (list  (caddr firstValue)) (list  secondValue))
                         )     
                    )
                    ; (OR a b ) , (c) 
                    ( (and (and (list? firstValue) (equal? (car firstValue) 'OR)) 
                           (and (list? secondValue ) (< (length secondValue) 3))) 
                        (list (append (list  (cadr firstValue)) 
                                      (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue))
                               (append (list  (caddr firstValue)) 
                                       (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue))
                         )
                    )
                    
                    ; c, (OR a b )
                    ( (and (and (list? secondValue) (equal? (car secondValue) 'OR)) (not (list? firstValue ))) 
                         (list (append (list  (cadr secondValue)) (list  firstValue))
                               (append (list  (caddr secondValue)) (list  firstValue))
                         )     
                    )
                    ; (c) , (OR a b )
                    ( (and (and (list? secondValue) (equal? (car secondValue) 'OR)) 
                           (and (list? firstValue ) (< (length firstValue) 3))) 
                        (list (append (list  (cadr secondValue)) 
                                      (if (equal? (car firstValue) 'NOT) (list firstValue) firstValue))
                               (append (list  (caddr secondValue)) 
                                       (if (equal? (car firstValue) 'NOT) (list firstValue) firstValue))
                         )
                    )
                  
                  
                    ; (OR a b ) , (OR c d) 
                    ( (and (and (list? firstValue) (equal? (car firstValue) 'OR))
                           (and (list? secondValue) (equal? (car secondValue) 'OR))) 
                        (append 
                              (list (cdr firstValue))
                              (list (cdr secondValue))
                        )
                               
                         
                    )
                    ; (OR a b ) , (AND c d) 
                    ( (and (and (list? firstValue) (equal? (car firstValue) 'OR))
                           (and (list? secondValue) (equal? (car secondValue) 'AND)))
                         (list 
                                     (append  (list (cadr firstValue)) (list (cadr secondValue)))
                                     (append  (list (cadr firstValue)) (list (caddr secondValue)))
                                     (append  (list (caddr firstValue)) (list (cadr secondValue)))
                                     (append  (list (caddr firstValue)) (list (caddr secondValue)))
                         )     
                    )
                    
                    ;***** AND - OR Scenarios ****** 
                    ( (and (and (list? firstValue) (equal? (car firstValue) 'AND))
                           (and (list? secondValue) (equal? (car secondValue) 'OR))) 
                         (list 
                                     (append  (list (cadr firstValue))  (list (cadr secondValue)) )
                                     (append  (list (caddr firstValue)) (list (cadr secondValue)) )
                                     (append  (list (cadr firstValue))  (list (caddr secondValue)) )
                                     (append  (list (caddr firstValue)) (list (caddr secondValue)) )
                         )     
                    )
                    
                    ;***** AND - AND Scenarios ******
                    (#t  (append 
                              (if (not (list? firstValue )) 
                                        (list (list firstValue))
                                        (cond
                                            ((< (length firstValue) 3) (list firstValue))
                                            ((equal? (car firstValue) 'AND ) 
                                                    (convert-AND-CNF (cadr firstValue) (caddr firstValue)))
                                        )        
                              ) 
                              (if (not (list? secondValue )) 
                                        (list (list secondValue))
                                        (cond
                                            ((< (length secondValue) 3) (list secondValue))
                                            ((equal? (car secondValue) 'AND ) 
                                                     (convert-AND-CNF (cadr secondValue) (caddr secondValue)))
                                        )        
                              )
                        )
                  )
  )
)

;This would convert a IMPLIES clause in into its CNF form
(define (convert-IMPLIES-CNF firstValue secondValue)
                 (cond
                    ;***** NORMAL scenarios ******
                    ; a -> b : KB (((NOT a)  b))
                    ( (and (not (list? firstValue ))   (not(list? secondValue)) )
                         (list (append (list (negate firstValue)) (list secondValue)))
                    )
                    ; a -> (b) : KB ( ( (NOT a)  (b)))
                    ( (and (not (list? firstValue ))  (and (list? secondValue ) (< (length secondValue) 3)) ) 
                         (list (append (list (negate firstValue)) 
                                 (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue) 
                         ))
                    )
                    ; (a) -> b : KB ( ( (NOT a)  (b)))
                    ( (and (and (list? firstValue ) (< (length firstValue) 3))  (not(list? secondValue)) )
                         (list (append 
                                 (list (negate firstValue)) 
                                 (list secondValue)
                         ))
                    )
                    ; (a) -> (b) : KB ( ( (NOT a)  (b)))
                    ( (and 
                           (and (list? firstValue) (< (length firstValue) 3))  
                           (and (list? secondValue) (< (length secondValue) 3)) 
                       ) 
                         (list (append (list (negate firstValue)) 
                                (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue) 
                                 
                         ))
                    )
                       
                    ;***** (AND -> Any) scenarios ******* 
                    
                    ; (AND a b ) -> c) : ( (NOT a) (NOT b) c)
                    ( (and 
                           (and (list? firstValue) (equal? (car firstValue) 'AND)) 
                           (not (list? secondValue ))) 
                         (list (append (car (negate-AND firstValue)) (list secondValue)))
                    )
                     ; (AND a b ) -> (c)) : ( (NOT a) (NOT b) c)
                    ( (and 
                           (and (list? firstValue)(equal? (car firstValue) 'AND) )
                           (and (list? secondValue)(< (length secondValue) 3))
                       ) 
                       (list (append (car (negate-AND firstValue))  
                                 (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue)
                         )
                       )
                    )
                    ; c -> (AND a b ) : (((NOT c) a ) ((NOT c) b))
                    ( (and 
                           (not (list? firstValue ))
                           (and (list? secondValue)(equal? (car secondValue) 'AND) )
                           
                       ) 
                        (list (append (list  (cadr secondValue)) 
                                       (list (negate firstValue)) )
                               (append (list  (caddr secondValue)) 
                                       (list (negate firstValue)) )
                         )
                    )
                    
                    ; (c) -> (AND a b ) : (((NOT c) a ) ((NOT c) b))
                    ( (and 
                           (and (list? firstValue)(< (length firstValue) 3))
                           (and (list? secondValue)(equal? (car secondValue) 'AND) )
                           
                       ) 
                        (list (append 
                                      (list (negate firstValue))
                                      (list  (cadr secondValue)) )
                               (append (list (negate firstValue))
                                       (list  (caddr secondValue)) )
                         )
                    )
                  
                  
                    ; (AND a b ) -> (OR c d) : ( ((NOT a) (NOT b) c d) )
                    ( (and 
                           (and (list? firstValue) (equal? (car firstValue) 'AND) )
                           (and (list? secondValue) (equal? (car secondValue) 'OR ))
                      ) 
                         (list (append (car (negate-AND firstValue)) (cdr secondValue)))
                    )
                    ; (AND a b ) -> (AND c d) : ( ((NOT a) (NOT b) c) ((NOT a) (NOT b) d))
                    ( (and 
                           (and (list? firstValue) (equal? (car firstValue) 'AND) )
                           (and (list? secondValue) (equal? (car secondValue) 'AND ))
                      )
                      
                      
                         (list (append (car (negate-AND firstValue)) (list (cadr secondValue)))
                               (append (car (negate-AND firstValue)) (list (caddr secondValue)))
                         )     
                    )
                  
                    ;***** (OR -> Any) scenarios ******* 
                    ; (OR a b ) -> c : ( ((NOT a) c) ((NOT b) d)  )
                    ( (and 
                           (and (list? firstValue) (equal? (car firstValue) 'OR)) 
                           (not (list? secondValue ))) 
                           (list (append (list (negate ( cadr firstValue))) (list  secondValue))
                                 (append (list (negate ( caddr firstValue))) (list  secondValue))
                           )     
                    )
                  
                    ; (OR a b ) -> (c) : ( ((NOT a) c) ((NOT b) c)  )
                    ( (and 
                          (and (list? firstValue)  (equal? (car firstValue) 'OR)) 
                          (and (list? secondValue)  (< (length secondValue) 3))
                      ) 
                         (list (append (list (negate ( cadr firstValue))) 
                                       (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue)
                               )
                               (append (list (negate ( caddr firstValue))) 
                                       (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue)
                               )
                         )
                    )
                    ; c -> (OR a b ) : ( ((NOT c) a b )  )
                    ( (and 
                           (not (list? firstValue ))
                           (and (list? secondValue) (equal? (car secondValue) 'OR)) 
                           ) 
                           (list (append (list  (negate firstValue)) (cdr secondValue)))
                    )
                  
                    ; (c) -> (OR a b ) : ( ((NOT c) a b )  )
                    ( (and 
                          (and (list? firstValue)  (< (length firstValue) 3)) 
                          (and (list? secondValue)  (equal? (car secondValue) 'OR)) 
                          
                      ) 
                         (list (append (list (negate firstValue))
                                       (cdr secondValue)))
                    )
                  
                    ; (OR a b ) -> (OR c d) : ( ((NOT a) c d) ((NOT b) c d) )
                    ( (and 
                           (and (list? firstValue) (equal? (car firstValue) 'OR) )
                           (and (list? secondValue) (equal? (car secondValue) 'OR ))
                      ) 
                        (list (append (list (negate ( cadr firstValue)))  (cdr secondValue))
                               (append (list (negate ( caddr firstValue)))  (cdr secondValue))
                         ) 
                    )
                  
                    ; (OR a b ) -> (AND c d) : ( ((NOT a) (NOT b) c) (c) (d) )
                    ( (and 
                           (and (list? firstValue) (equal? (car firstValue) 'OR) )
                           (and (list? secondValue) (equal? (car secondValue) 'AND ))
                      )
                         (append 
                               (list (list (negate ( cadr firstValue))))
                               (list (list (negate ( caddr firstValue))))
                               (list (list  (cadr secondValue)))
                               (list (list  (caddr secondValue)))
                         )     
                    )
                  
                    ; (IMPLIES a b ) -> c
                    ( (and 
                           (and (list? firstValue) (equal? (car firstValue) 'IMPLIES)) 
                           (not (list? secondValue ))) 
                           (list (append (list ( cadr firstValue)) (list  secondValue))
                                 (append (list (negate ( caddr firstValue))) (list  secondValue))
                           )     
                    )
                  
                    ; (IMPLIES a b ) -> (c) 
                    ( (and 
                          (and (list? firstValue)  (equal? (car firstValue) 'IMPLIES)) 
                          (and (list? secondValue)  (< (length secondValue) 3))
                      ) 
                         (list (append (list  ( cadr firstValue))
                                       (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue)
                               )
                               (append (list (negate ( caddr firstValue))) 
                                       (if (equal? (car secondValue) 'NOT) (list secondValue) secondValue)
                               )
                         )
                    )
                  
                    ; p -> (IMPLIES q r ) 
                    ( (and 
                           (not (list? firstValue ))
                           (and (list? secondValue)(equal? (car secondValue) 'IMPLIES) )
                           
                       ) 
                        (list (append (list (negate firstValue))
                                      (list  (negate (cadr secondValue))) 
                                      (list (caddr secondValue)) )
                         )
                    )
                    
                    ;  (p) -> (IMPLIES q r ) 
                    ( (and 
                           (and (list? firstValue)(< (length firstValue) 3))
                           (and (list? secondValue)(equal? (car secondValue) 'IMPLIES) )
                           
                       ) 
                       (list (append (if (equal? (car firstValue) 'NOT) (list firstValue) firstValue)
                                      (list  (negate (cadr secondValue))) 
                                      (list (caddr secondValue)) )
                       ) 
                    )
                    ;  (IMPLIES a b ) -> (IMPLIES c d ) : ((a (NOT c) d) ((NOT b) (NOT c) d))
                    ( (and 
                           (and (list? firstValue)  (equal? (car firstValue) 'IMPLIES))
                           (and (list? secondValue)(equal? (car secondValue) 'IMPLIES) )
                           
                       ) 
                       (list    
                             (append (list ( cadr firstValue)) (list(negate( cadr secondValue))) (list ( caddr secondValue)))
                             (append (list (negate( caddr firstValue))) (list(negate( cadr secondValue))) (list ( caddr secondValue)))
                       ) 
                     
                    )
                  
                  
                 )
)


;This would convert a BICONDITIONAL clause in into its CNF form
(define (convert-BICONDITIONAL-CNF firstValue secondValue)
  (list 
        (car (convert-IMPLIES-CNF firstValue secondValue))
        (car (convert-IMPLIES-CNF secondValue firstValue ))
  )
)

;This is supportig procedure for TELL interfaces for the convertion of a clause into its CNF form 
(define (convert-to-CNF-for-tell clause)
  ; (begin
  ;     (display "convert-to-CNF-for-tell : clause > ")
  ;     (display clause)
  ;     (newline)
  ; )
  (cond
    ((null? clause) clause)
    ((not(list? clause)) (list (list clause)))
    ((< (length clause) 3)
          (cond
            ((equal? (car clause) 'NOT) 
                        (cond
                              ;(NOT a)
                              ( (not (list? (cadr clause))) (negate (cadr clause)))
                              ;(NOT (NOT a)
                              ((equal? (caadr clause) 'NOT)
                                  (cdadr clause)) 
                              ;(NOT (OR a b)  
                              ((equal? (caadr clause) 'OR)
                                (negate-OR (cadr clause)) )  
                              ;(NOT (AND a b)  
                              ((equal? (caadr clause) 'AND)
                                (negate-AND (cadr clause)) )
                              ;(NOT (IMPLIES a b)  
                              ((equal? (caadr clause) 'IMPLIES)
                                (negate-IMPLIES (cadr clause)) )
                              ;(NOT (BICONDITIONAL a b)  
                              ((equal? (caadr clause) 'BICONDITIONAL)
                                (negate-BICONDITIONAL (cadr clause)) )
                        )
              ) 
              (#t (list clause))  
          )
    )
    (#t (let*
          (
            (operator (car clause))
            (firstValue (cadr clause))
            (secondValue (caddr clause))
          ) 
          (cond
            ((equal? operator 'OR ) (convert-OR-CNF firstValue secondValue))
            ((equal? operator 'AND ) (convert-AND-CNF firstValue secondValue))
            ((equal? operator 'IMPLIES ) (convert-IMPLIES-CNF firstValue secondValue))
            ((equal? operator 'BICONDITIONAL ) (convert-BICONDITIONAL-CNF firstValue secondValue))
            (#t (list clause))
          )
      )
    )
  )
) 

;________________________ resolve's internal modules (below) ___________________________

;This is a supporting procedure for RESOLVE interface, (resolve ..) acts as a wrapper function for this procedure
(define (kb-resolve )
  (begin
    ; (newline)
    ; (display "-------kb-resolve---------")
    ; (newline)
    ; (display "##### KB-CURSOR    :")
    ; (display KB-CURSOR)
    ; (newline)
    (cond
            ((null? KB-CURSOR) 'UNKNOWN )
            (#t 
               
                (let*
                    (
                      (firstProposition (car KB-CURSOR))
                      (remainingKB  (cdr KB-CURSOR))
                      (hasContradiction 
                                        (begin
                                          (set! KB-CURSOR  remainingKB)  
                                          (contradictionPresent firstProposition remainingKB)
                                        )
                                        
                      )
                    )
                    (begin
                      ; (newline)
                      ; (display "Found Contradiction? : ")
                      ; (display hasContradiction)
                      ; (newline)
                      (cond
                        ((equal? hasContradiction #t) #t)
                        (#t (kb-resolve ))
                      )
                    )
                )  
            )
    )
  )
)


;Checks if given propostion contradicts with given KB instance
(define (contradictionPresent firstProposition remainingKB)
      (cond
        ((null? remainingKB) #f)
        (#t   
            (begin
              ; ; (display "Check contradiction @ ")
              ; (display firstProposition)
              ; (display " : remainingKB > ")
              ; (display remainingKB)
              ; ; (display (car remainingKB))
              ; (newline)
              (let*
                  (
                    (resolution (resolve firstProposition (car remainingKB)))
                    (hasContradiction (equal? resolution 'CONTRADICTION))
                    (newProposition  (cond
                                        (hasContradiction '())
                                        ((equal? resolution #f) '())
                                        (#t (list resolution))
                                      )
                    )
                    ; (newProposition (if (equal? resolution #f) '() (list resolution)))
                    (updatedKB  (append (cdr remainingKB)  newProposition))
                  )
                  (if hasContradiction
                    #t 
                    (begin
                      (set! KB-CURSOR  (append KB-CURSOR newProposition))
                      ; (display "KB-CURSOR Update! @: ")
                      ; (display KB-CURSOR)
                      ; (newline)
                      (contradictionPresent firstProposition updatedKB)
                    )
                  )
              )
            )
        )
      )
)





;@INPUT 
;alist - a list containing propositional statement
;blist - another list containing propositional statement
;outputList - temp list to pass the intermediate value to the recursion (default '())
;foundCnt - temp variable to track to the total number of interjection found (default 0)
;@RETURN
;Statement resolution 
(define (resolve-internal alist blist outputList foundCnt)
  ; (begin
  ;   (display alist)
  ;   (display "  ---  ")
  ;   (display outputList)
  ;   (newline)
  ; )
  (cond
    ((> foundCnt 1) #f)
    ((null? alist) (if (null? outputList) #f outputList))
    (#t 
        (let
            (
              (foundResolution (list-contains? (negate (car alist)) blist))
            )
            (if foundResolution
                (resolve-internal (cdr alist) blist outputList (+ foundCnt 1))
                (resolve-internal (cdr alist) blist (append outputList (list (car alist))) foundCnt)
            )
        )
    )
  )
)


;#INPUT
;@value : value that needs to be checked
;@alist : a list
;#RETURNS
; #t of #f depending if value is present in alist
(define (list-contains? value alist)
        (cond
                ((null? alist) #f)
                (#t (if (equal? (car alist) value) #t (list-contains? value (cdr alist))))
        )
)


;#INPUT
;@value : it would be a list or single literal example (NOT a) or a or (a b)
;#RETURNS
;This returns the negated version of the input given
;Example for i/p 
; (NOT a) => a
; a => (NOT a)
; null => null
(define (negate item)
  (let
    (
      (value 
             (cond
               ((not (list? item)) item)
               ((= (length item) 1) (car item))
               (#t item)
             )
      )
    )
    (cond
      ((null? value) value)
      ((not(list? value)) (append '(NOT) (list value)))
      (#t (if (equal? (car value) 'NOT) 
              (cadr value)
              (append '(NOT) (list value))
          )    
      )
    )
  )
)

;This would check if the list is the negated version
;#INPUT
;@alist : a list
;#RETURNS
; if alist = (NOT a ) => #t 
; if alist = (a b) => #f
; if alist = (a (NOT b)) => #f
; (define (is-negatedValue alist)
;   (cond
;     ((null? alist) #f)
;     ((equal? (car alist) 'NOT) #t)
;     (#t #f)
;   )
; )  


;#INPUT
;@alist = a list
;@returnList = empty list '()
;#RETURNS
;Same list without duplicate values
(define (remove-duplicates alist returnList)
  (cond
    ((null? alist) returnList)
    (#t (remove-duplicates
                           (cdr alist)
                           (append  returnList
                                    (if (list-contains? (car alist) returnList)
                                        '()
                                         (list (car alist))
                                    )
                            )
      )
    )
  )
)
