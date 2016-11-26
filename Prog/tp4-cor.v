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
Inductive get : env -> addr -> value -> Prop := 
  | get_head : forall l a x, get ((a,x)::l) a x
  | get_tail : forall l a b x y, get l a x -> a<>b -> get ((b,y)::l) a x.

(* Le prédicat (update l a x y l') signifie que l' est obtenu en remplaçant la 
   première occurence de (a,x) dans l' par (a,y). *)
(* 
                                                       update l a x l'
  ──────────────────────────────── head  a≠b ────────────────────────────────── tail
  update ((a,x)::l) a y ((a,y)::l)            update ((b,y)::l) a x ((b,y)::l')

*)
Inductive update : env -> addr -> value -> env -> Prop := 
  | update_head : forall l a x y, update ((a,x)::l) a y ((a,y)::l)
  | update_tail : forall l l' a b x y, update l a x l' -> a<>b -> update ((b,y)::l) a x ((b,y)::l').

(* Les termes arithmétiques du langage sont donnés par la grammaire suivante *)

Inductive aexpr : Type :=
   | zero : aexpr
   | var : addr -> aexpr
   | succ : aexpr -> aexpr
   | pred : aexpr -> aexpr. 


Inductive bexpr : Type :=
   | blt : aexpr -> aexpr -> bexpr.



(* Les programmes sont donnés par : *)
Inductive prg : Type :=
   | skip : prg
   | seq : prg -> prg -> prg
   | ass : addr -> aexpr -> prg 
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

Inductive aeval : env -> aexpr -> value -> Prop :=
  (* Implémentez vous-même le type inductif qui réalise cette sémantique *)
  | aeval_zero : forall e, aeval e zero O
  | aeval_var : forall e x n, get e x n -> aeval e #x n
  | aeval_succ : forall e t n, aeval e t n -> aeval e (succ t) (S n)
  | aeval_pred_S : forall e t n, aeval e t (S n) -> aeval e (pred t) n
  | aeval_pred_0 : forall e t, aeval e t O -> aeval e (pred t) O
.


(*Sémantique grand pas pour les expressions booleenes.*)
(*
   <ρ|x> ⇓ n   <ρ|y> ⇓ m   n < m 
  ─────────────────────────────── 
         <ρ|x<<y> ⇓ true        


   <ρ|x> ⇓ n   <ρ|y> ⇓ m   m <= n 
  ─────────────────────────────── 
         <ρ|x<<y> ⇓ false        
*)

Inductive beval : env -> bexpr -> bool -> Prop := 
  | beval_inf : forall e x y n m, 
      aeval e x n -> aeval e y m -> n < m -> beval e (blt x y) true
  | beval_sup : forall e x y n m, aeval e x n -> aeval e y m -> m <= n -> 
      beval e (blt x y) false.


(* Sémantique grand pas pour les programmes. *)
(* Exercice : écrire sur papier un système de règles 
   pour la sémantique grand pas "execute".

   On se synchronisera au tableau pour l'écriture du prédicat 
   "execute".
*)

Inductive execute : env -> prg -> env -> Prop := 
   | execute_skip : forall rho, execute rho skip rho
   | execute_ass : forall rho rho' t a n,
         aeval rho t n ->
         update rho a n rho' ->
         execute rho (a <- t) rho'
   | execute_seq : forall rho1 rho2 rho3 p q,
         execute rho1 p rho2 ->
         execute rho2 q rho3 ->
         execute rho1 (p;q) rho3
   | execute_ifte_true : forall rho t p1 p2 rho',
         beval rho t true ->
         execute rho p1 rho' ->
         execute rho (ifte t p1 p2) rho'
   | execute_ifte_false : forall rho t p1 p2 rho',
         beval rho t false ->
         execute rho p2 rho' ->
         execute rho (ifte t p1 p2) rho'
   | execute_while_true : forall rho1 rho2 t p, 
         beval rho1 t true ->
         execute rho1 (p; while t p) rho2 ->
         execute rho1 (while t p) rho2
   | execute_while_false : forall rho t p, 
         beval rho t false ->
         execute rho (while t p) rho.


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
induction x; intros ; unfold add.
  apply execute_while_false. apply beval_sup with 0 0. 
  apply aeval_zero. apply aeval_var. apply get_head. trivial.
  apply execute_while_true.
    apply beval_inf  with 0 (S x).
    apply aeval_zero.
    apply aeval_var. apply get_head. auto with arith.
    apply execute_seq with ((0, x) :: (1, S y) :: nil).
      apply execute_seq with ((0, x) :: (1, y) :: nil).
        apply execute_ass with x.
          apply aeval_pred_S. apply aeval_var. apply get_head.
          apply update_head.
        apply execute_ass with (S y).
          apply aeval_succ. apply aeval_var. apply get_tail.
            apply get_head.
            intro H. inversion H.
          apply update_tail.
            apply update_head.
            intro H. inversion H.
      replace (S x + y) with (x + (S y)).
        apply IHx.
Require Import Omega.
omega.
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
intros a b c Hab Hbc. induction Hab.
  apply Hbc.
  apply star_R with b.
    apply H.
    apply IHHab. apply Hbc.
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
 intros s1 s2 H. induction H ; intros ; subst.
    injection H0. intros. subst. apply star_refl.
    destruct b.
    apply star_R with [p0 ; r | e].
      apply ss_seq_seq. assumption.
      apply IHstar.
        reflexivity.
        reflexivity.
intros p q r e1 e2 Hstar.
apply H with [p | e1] [q | e2].
  assumption.
  reflexivity.
  reflexivity.

Qed.

(* Vous pouvez maintenant montrer que *)
Lemma execute_sse : forall p e1 e2,
  execute e1 p e2 -> [p | e1] =>* [skip | e2].
  intros p eq e2 H. induction H.
  apply star_refl.
  apply star_R with [skip | rho'].
    apply ss_ass with n.
      assumption.
      assumption.
    apply star_refl.
  apply star_trans with [q | rho2].
    apply star_trans with [skip ; q | rho2].
      apply seq_trans. assumption.
      apply star_R with [q | rho2].
        apply ss_seq_skip.
        apply star_refl.
    assumption.
  apply star_R with [p1 | rho].
    apply ss_ifte_true.
      assumption.
      assumption.
  apply star_R with [p2 | rho].
    apply ss_ifte_false.
      assumption.
      assumption.
  apply star_R with [ ifte t (p ; while t p) skip | rho1 ].
    apply ss_while.
    apply star_R with [p ; while t p | rho1].
      apply ss_ifte_true. assumption.
      assumption.
  apply star_R with [ ifte t (p ; while t p) skip | rho].
    apply ss_while.
    apply star_R with [skip | rho].
      apply ss_ifte_false. assumption.
      apply star_refl.  
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
assert (forall s1 s2, s1 => s2 -> forall p1 p2 e1 e2, 
  s1 = [ p1 | e1 ] -> s2 = [ p2 | e2 ] ->
  forall e3, execute e2 p2 e3 -> execute e1 p1 e3).
intros s1 s2 H. induction H ; intros ; subst.
  injection H1. injection H2. intros. subst.
    apply execute_ass with x.
      assumption.
      inversion H3. subst. assumption.
  injection H. injection H0. intros. subst.
    apply execute_seq with e2.
      subst. apply execute_skip.
      assumption.
  injection H0. injection H1. intros. subst.
    clear H0 H1. inversion H2. subst.
    apply execute_seq with rho2.
    apply IHss with c' e2.
      reflexivity.
      reflexivity.
      assumption.
    assumption.
  injection H1. injection H0. intros. subst.
  clear H1 H0.
  apply execute_ifte_true.
    assumption.
    subst. assumption.
  injection H0. injection H1. intros. subst.
  apply execute_ifte_false.
    subst. assumption.
    clear H1. injection H0. intros. subst. assumption.
  injection H. injection H0. intros. subst. subst. clear H H0.
    inversion H1 ; subst.
      apply execute_while_true.
        assumption.
        assumption.
    inversion H6. subst.
      apply execute_while_false.
        assumption.
intros p1 p2 e1 e2 Hss e3 Hex.
apply H with [p1 | e1] [p2 | e2] p2 e2.
  assumption.
  reflexivity.
  reflexivity.
  assumption.
Qed.


(* Vous pouvez maintenant conclure. *)
(* Attention a l'hypothese d'induction. *)

Lemma sse_execute : forall p e1 e2,
  [ p | e1 ] =>*  [ skip | e2 ] -> execute e1 p e2.
assert (forall s1 s2, s1 =>* s2 -> forall p e1 e2, 
  s1 = [ p | e1 ] -> s2 = [ skip | e2 ] -> execute e1 p e2).
  intros s1 s2 H. induction H.
    intros. subst. injection H0. intros. subst. apply execute_skip.
    intros. destruct b. subst. apply ss_execute_aux with p0 e.
      assumption.
      apply IHstar.
        reflexivity.
        reflexivity.
  intros p e1 e2 Hp. apply H with [p | e1] [skip | e2].
    assumption.
    reflexivity.
    reflexivity.
Qed.