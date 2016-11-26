(* TP 4 : Un petit langage impératif en Coq *)

Require Import List.

(* Les valeurs calculées seront des entiers. *)
Definition value := nat.
(* Les addresses seront implémentées par des entiers. *)
Definition addr := nat.   
(* La mémoire sera représentée par une liste de couples adresse/valeur *)
Definition env := list (addr * value). 

(* Le prédicat (get l a x) signifie que (a,x) ∈ l. 
   Il est axiomatisé par les règles suivantes : 
                                    get l a x
  ────────────────── head  a≠b ──────────────────── tail
  get ((a,x)::l) a x            get ((b,y)::l) a x

*)
Inductive get : env -> addr -> value -> Prop := ...

(* Le prédicat (update l a y l') signifie que l' est obtenu en 
   remplaçant la première occurence de (a,_) dans l' par (a,y). *)
(* 
                                                       update l a x l'
  ──────────────────────────────── head  a≠b ────────────────────────────────── tail
  update ((a,x)::l) a y ((a,y)::l)            update ((b,y)::l) a x ((b,y)::l')

*)
Inductive update : env -> addr -> value -> env -> Prop := ...

(* Les termes arithmétiques du langage sont donnés par
   la grammaire suivante *)
Inductive aexpr : Type :=
   | zero : aexpr
   | var : addr -> aexpr
   | succ : aexpr -> aexpr
   | pred : aexpr -> aexpr. 

(* On a aussi des expressions booleens*)
Inductive bexpr : Type :=
   | blt : aexpr -> aexpr -> bexpr.

(* Les programmes sont donnés par : *)
Inductive prg : Type :=
   | skip : prg
   | seq : prg -> prg -> prg
   | ass : addr -> expr -> prg 
   | ifte : bexpr -> prg -> prg -> prg
   | while : bexpr -> prg -> prg.

Notation "# x" := (var x) (at level 0).
Notation "x << y" := (blt x y) (at level 70).
Notation "A ; B" := (seq A B) (at level 100, right associativity).
Notation "A <- B" := (ass A B) (at level 80, right associativity).


(* Voilà, le seul programme qui nous intéressera. 
 * On cherchera à montrer dans la suite qu'il implémente l'addition
 *)
Definition add :=
     while (zero <<  #0)
       (0 <- pred #0; 
        1 <- succ #1).

(* Sémantique grand pas pour les expressions arithmetiques:
                         get ρ x n              <ρ|t> ⇓ n
  ──────────── zero    ───────────── var   ────────────────── succ
  <ρ|zero> ⇓ 0         <ρ|var x> ⇓ n       <ρ|succ t> ⇓ (S n)

        <ρ|t> ⇓ (S n)              <ρ|t> ⇓ 0
       ────────────── pred_S    ────────────── pred_0
       <ρ|pred t> ⇓ n           <ρ|pred t> ⇓ 0

 *)



Inductive aeval : env -> aexpr -> value -> Prop := ...


(*Sémantique grand pas pour les expressions booleenes.*)
(*
   <ρ|x> ⇓ n   <ρ|y> ⇓ m   n < m 
  ─────────────────────────────── 
         <ρ|x<<y> ⇓ true        


   <ρ|x> ⇓ n   <ρ|y> ⇓ m   m <= n 
  ─────────────────────────────── 
         <ρ|x<<y> ⇓ false        
*)

Inductive beval : env -> bexpr -> bool -> Prop := ...


(* Sémantique grand pas pour les programmes. *)
(* Exercice : écrire sur papier un système de règles 
   pour la sémantique grand pas "execute".

   On se synchronisera au tableau pour l'écriture du prédicat 
   "execute".
*)

Inductive execute : env -> prg -> env -> Prop := ...


(* On va maintenant montrer que add est correcte *)
(* Astuces :
   - Appliquez les constructeurs adéquats pour résoudre les buts. 
   - Quand le système n'arrive pas à inférer l'argument d'une 
     application vous pouvez le lui préciser à l'aide de "with" et de 
     la syntaxe suivante : "apply execute_while_true with x"
   - Certains lemmes de la bibliothèque standard
     pourront vous etre utiles :
*)
Check sym_eq.
Check plus_n_Sm.

Lemma correctness : forall x y, 
    execute ((0,x)::(1,y)::nil) add ((0,0)::(1,x+y)::nil).
...
Qed.

(* On maintenant s'intéresser à une sémantique à petits pas
   en montrer son équivalence avec la sémantique à grands pas
   donnée par execute *)
Reserved Notation "A => B" (at level 80). 

Definition state := (prg * env)%type.
Notation "[ π | p ]" := (π,p).

Inductive ss : state -> state -> Prop :=
  | ss_ass : forall s s' i a x, aeval s a x -> update s i x s' -> [i <- a | s] => [skip | s']
  | ss_seq_skip : forall s c, [skip ; c | s] => [ c | s ] 
  | ss_seq_seq : forall s s' c c' d, [c | s] => [c'|s'] -> [c ; d|s] => [ c' ; d | s']
  | ss_ifte_true : forall s b c d, beval s b true -> [ ifte b c d | s ] => [ c | s ]
  | ss_ifte_false : forall s b c d, beval s b false -> [ ifte b c d | s ] => [ d | s ]
  | ss_while : forall s b c, [ while b c | s ] => [ ifte b (c ; while b c) skip | s ]
where "A => B" := (ss A B). 


(* L'évaluation d'un programme correspond à la clôture 
   réflexive transitive de la sémantique à petit-pas.
   La définir inductivement permet de raisonner 
   dessus plus facilement.
*)

Section Star. 
Variable A : Type. 
Variable R : A -> A -> Prop. 

Inductive star : A -> A -> Prop :=
  | star_refl : forall a, star a a
  | star_R : forall a b c, R a b -> star b c -> star a c. 

Lemma star_trans : forall a b c, star a b -> star b c -> star a c. 
...
Qed.

End Star.

Notation "A =>* B" := (star _ ss A B) (at level 20).

(* On va maintenant montrer l'équivalence entre les deux sémantiques. *)

(* On commence par grands pas -> petits pas. *)
(* Le séquencement ';' est géré de manière différente
   par les deux sémantiques : *)
Check execute_seq.
Check ss_seq_skip.
Check ss_seq_seq.

(* On va montrer que =>* peut traiter ';' de manière similaire
   à execute_seq :
     pour tous p q r e1 e2,
   [p | e1] =>* [q | e2] -> [p ; r | e1] =>* [q ; r | e2]
*)

(* La tactique [induction H] est insuffisante
   pour certains prédicats inductifs dépendants.
   Commencez par décommenter les lignes suivantes
   et essayer de continuer la preuve ...
*)
(*
Goal forall p q r e1 e2,
  [p | e1] =>* [q | e2] -> [p ; r | e1] =>* [q ; r | e2].
intros. induction H.
...
*)
(* Cette difficulté se résoud en renforcant le principe d'induction.
   On utilise pour cela la tactique [assert P].
*)

(* Astuce : la tactique [injection H] permet d'utiliser l'injectivité
     des constructeurs (en particulier du constructeur de paires)
*)

Lemma seq_trans : forall p q r e1 e2,
  [p | e1] =>* [q | e2] -> [p ; r | e1] =>* [q ; r | e2].
assert (H : forall s1 s2, s1 =>* s2 -> forall p q r e1 e2, 
  s1 = [ p | e1 ] -> s2 = [ q | e2 ] -> [ p ; r | e1 ] =>* [ q ; r | e2 ]).
...
Qed.

(* Vous pouvez maintenant montrer que *)
Lemma execute_sse : forall p e1 e2,
  execute e1 p e2 -> [p | e1] =>* [skip | e2].
...
Qed.

(* On va maintenant montrer le sens petits pas -> grands pas *)
(* Question préliminaire : essayez de poursuivre la preuve suivante *)
(*
Goal forall p1 p2 e1 e2,
  [p1 | e1] => [p2 | e2] ->
  forall e3, execute e2 p2 e3 -> execute e1 p1 e3.
intros until 1. induction H.
*)
(* De quelle hypothese d'induction avez-vous besoin ? *)

(* Astuce : Il peut etre pratiquer d'enlever les
   hypotheses inutiles du contexte.
   Pour cela utiliser [clear H]
*)

Lemma ss_execute_aux : forall p1 p2 e1 e2,
  [p1 | e1] => [p2 | e2] ->
  forall e3, execute e2 p2 e3 -> execute e1 p1 e3.
...
Qed.


(* Vous pouvez maintenant conclure. *)
(* Attention a l'hypothese d'induction. *)

Lemma sse_execute : forall p e1 e2,
  [ p | e1 ] =>*  [ skip | e2 ] -> execute e1 p e2.
...
Qed.