(***************** 1ere Partie  *********************)

(* Il s'agit de finir les preuves commencées en TP4 sur la sémantique de IMP.
  Vous pouvez soit continuer sur votre fichier pour TP4 soit sur ce fichier.
  Une partie des preuves est fournie.
*)


Require Import List.
Require Import Omega.

Definition value := nat.  (* Les valeurs calculées seront des entiers. *)
Definition addr := nat.   (* Les addresses seront implémentées par des entiers. *)
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
  ────────────────────────── head  a≠b ───────────────────────tail
  update ((a,x)::l) a y ((a,y)::l)            update ((b,y)::l) a x ((b,y)::l')

*)

Inductive update : env -> addr -> value -> env -> Prop := 
  | update_head : forall l a x y, update ((a,x)::l) a y ((a,y)::l)
  | update_tail : forall l l' a b x y, 
      update l a x l' -> a<>b -> update ((b,y)::l) a x ((b,y)::l').

(* Les termes arithmétiques du langage sont donnés par la grammaire suivante *)
Inductive aexpr : Type :=
   | zero : aexpr
   | var : addr -> aexpr
   | succ : aexpr -> aexpr
   | pred : aexpr -> aexpr. 

Inductive bexpr : Type :=
   | blt : aexpr -> aexpr -> bexpr.

(* Les programmes par : *)
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

(* Sémantique grand pas pour les expressions:
                         get ρ x n              <ρ|t> ⇓ n
  ──────────── zero    ───────────── var   ────────────────── succ
  <ρ|zero> ⇓ 0         <ρ|var x> ⇓ n       <ρ|succ t> ⇓ (S n)

        <ρ|t> ⇓ (S n)              <ρ|t> ⇓ 0
       ────────────── pred_S    ────────────── pred_0
       <ρ|pred t> ⇓ n           <ρ|pred t> ⇓ 0

 *)

Inductive aeval : env -> aexpr -> value -> Prop :=
  | eval_zero : forall e, aeval e zero O
  | eval_var : forall e x n, get e x n -> aeval e #x n
  | eval_succ : forall e t n, aeval e t n -> aeval e (succ t) (S n)
  | eval_pred_S : forall e t n, aeval e t (S n) -> aeval e (pred t) n
  | eval_pred_0 : forall e t, aeval e t O -> aeval e (pred t) O.

Inductive beval : env -> bexpr -> bool -> Prop :=
| be_lt1 : forall r e1 e2 v1 v2,
            aeval r e1 v1 -> aeval r e2 v2 ->
            v1 < v2 -> beval r (blt e1 e2) true
| be_lt2 : forall r e1 e2 v1 v2,
            aeval r e1 v1 -> aeval r e2 v2 ->
            v2 <= v1 -> beval r (blt e1 e2) false.


(* Sémantique grand pas pour les programmes. *)
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
   | execute_ifte_true : forall rho t p1 p2 rho' ,
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

Reserved Notation "A =>> B" (at level 80). 

Definition state := (prg * env)%type.
Notation "[ π | p ]" := (π,p).

(* La sémantique à petit-pas : *)
Inductive ss : state -> state -> Prop :=
  | ss_ass : forall s s' i a x, 
      aeval s a x -> update s i x s' -> [i <- a | s] =>> [skip | s']
  | ss_seq_skip : forall s c, [skip ; c | s] =>> [ c | s ] 
  | ss_seq_seq : forall s s' c c' d, 
      [c | s] =>> [c'|s'] -> [c ; d|s] =>> [ c' ; d | s']
  | ss_ifte_true : forall s b c d, 
      beval s b true -> [ ifte b c d | s ] =>> [ c | s ]
  | ss_ifte_false : forall s b c d, 
      beval s b false -> [ ifte b c d | s ] =>> [ d | s ]
  | ss_while : forall s b c, 
      [ while b c | s ] =>> [ ifte b (c ; while b c) skip | s ]
where "A =>> B" := (ss A B). 

(* Pour travailler avec la sémantique à petit-pas, on doit utiliser la clôture 
réflexive transitive de ss. La définir inductivement permet de raisonner 
dessus plus facilement. *)

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

assert (forall s1 s2, s1 =>* s2 -> forall p q r e1 e2, 
  s1 = [ p | e1 ] -> s2 = [ q | e2 ] -> [ p ; r | e1 ] =>* [ q ; r | e2 ]).



(* Vous pouvez maintenant montrer que *)
Lemma execute_sse : forall p e1 e2,
  execute e1 p e2 -> [p | e1] =>* [skip | e2].


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
  [p1 | e1] =>> [p2 | e2] ->
  forall e3, execute e2 p2 e3 -> execute e1 p1 e3.


(* Vous pouvez maintenant conclure. *)
(* Attention a l'hypothese d'induction. *)

Lemma sse_execute : forall p e1 e2,
  [ p | e1 ] =>*  [ skip | e2 ] -> execute e1 p e2.



(************************ 2eme Partie ***************************)

(* Dans cette partie on va s'interesser aux triplets de Hoare. *)

(** ** Assertions *)
(* On formalise les assertion comme des propositions logiques 
  dependantes de l'environnement. *)
Definition assertion := env -> Prop.

(* Une triple de Hoare est un programme [c] avec un pre-condition [P] et une 
 post-condition [Q] et son sens est :
  si le programme [c] est demarre dans un environment qui satisfait la 
  pre-condition [P] et si [c] termine alors l'environment final va satisfaire
  la post-condition [Q].
*)
Definition hoare_triple (P: assertion) (c : prg) (Q: assertion) : Prop :=
  forall e1 e2, execute e1 c e2 -> P e1 -> Q e2.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
    (at level 90, c at next level).


Theorem hoare_post_true : forall (P Q : assertion) c,
  (forall e, Q e) ->
  {{P}} c {{Q}}.


Theorem hoare_pre_false : forall (P Q : assertion) c,
  (forall e, ~(P e)) ->
  {{P}} c {{Q}}.


(* Si pour un programme on a une triple valide, alors un triple ou la 
  pre-condition est plus forte ou la post-condition plus faible va etre valide
  pour le meme programme.

             {{P'}} c {{Q'}}
         P implies P' (in every state)
         Q' implies Q (in every state)
         -----------------------------  (hoare_consequence)
                {{P}} c {{Q}}

              {{P'}} c {{Q}}
         P implies P' (in every state)
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
         Q' implies Q (in every state)
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}

*)

Theorem hoare_consequence : forall (P P' Q Q' : assertion) c,
  (forall e, P e -> P' e) ->
  (forall e, Q' e -> Q e) ->
  {{P'}} c {{Q'}} ->
  {{P}} c {{Q}}.
Admitted.

Theorem hoare_consequence_pre: forall (P P' Q : assertion) c,
  (forall e, P e -> P' e) ->
  {{P'}} c {{Q}} ->
  {{P}} c {{Q}}.
Admitted.

Theorem hoare_consequence_post : forall (P Q Q' : assertion) c,
  (forall e, Q' e -> Q e) ->
  {{P}} c {{Q'}} ->
  {{P}} c {{Q}}.
Admitted.

(* On va maitenant decrire comment se comportent les instructions de notre 
  langage en logique de Hoare.
*)

(********* Skip *)
(** [skip] ne chnage pas l'environement, donc il conserve la pre-condition P

      --------------------  (hoare_skip)
      {{ P }} skip {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Admitted.

(***** Sequencement de 2 instructions *)
(* 

        {{ P }} c1 {{ Q }} 
        {{ Q }} c2 {{ R }}
       ---------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}

*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;c2 {{R}}.
Admitted.

(************* Affectation *)

(* c'est un peu plus complique a ecrire... *)
(* La post-condition Q est verifie dans l'environement obtenu apres 
  l'assignation si Q est verifie dans l'environement initial ou on a mis a jour
  la variable assigne avec la valeur de l'exprssion a assigne. 

*)
Definition asgn_sub x a Q : assertion :=
  fun e =>
  exists n, exists e', (aeval e a n) /\ (update e x n e') /\ Q e'.
(*
    ------------------------------------ (hoare_asgn)
      {{asgn_sub x a n Q}} x <- a {{Q}}
*)


(* Pour la suite, on a besion de lemmes intermediaires *)
Lemma get_eq : 
  forall e x n m, get e x n -> get e x m -> n = m.
Admitted.

Lemma aeval_eq :
  forall e a n1, aeval e a n1 -> forall n2,  aeval e a n2 -> n1 = n2.
Admitted.
(* ca vous rappelle des souvenirs ? *)
(* ... lemma bs_conflu du TP3 ... *)


Lemma update_eq :
  forall e x n e1, update e x n e1 -> 
forall e2, update e x n e2 -> e1 = e2.
Admitted.

Theorem hoare_asgn : forall Q V a,
  {{asgn_sub V a Q }} (V <- a) {{Q}}.
Admitted.

(*
Lemma update_update: 
   forall e1 x1 n1 e2 x2 n2 e3, 
     update e1 x1 n1 e2 -> 
     update e2 x2 n2 e3 ->
     update e1 x1 n1 *)

(************* If then else *)

(*

              {{P /\  beval b true}} c1 {{Q}}
              {{P /\  beval b false}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} ifte b c1 c2 {{Q}} 
*)


Theorem hoare_if : forall P Q b c1 c2,
  {{fun e => P e /\ beval e b true}} c1 {{Q}} ->
  {{fun e => P e /\ beval e b false}} c2 {{Q}} ->
  {{P}} (ifte b c1 c2) {{Q}}.
Admitted.


(************ While *)


(* 


               {{P /\ beval b true}} c {{P}}
        -----------------------------------  [hoare_while]
            {{P}} while b c {{P /\ beval b false}}
*)

Lemma hoare_while : forall P b c,
  {{fun e => P e /\ beval e b true}} c {{P}} ->
  {{P}} while b c {{fun e => P e /\ beval e b false}}.
Admitted.

(*** Exemple.

  On veut montrer : 
 
{{ x est declare dans l'environment }} x <- 0 {{x = 0}}

ou dans notre langage : *)

(* Cette preuve est un peu technique, a cause du choix de formalisation 
   pour les environments et pour [get] et [update]. *)

(* Astuce : on peut raisoner par cas pour 2 entiers naturels n et m suivant 
   si n = m ou n <> m en utilisant la tactique [destruct (eq_nat_dec n m)].
*) 

Example hoare_asgn_example0 : forall x, 
  {{fun e => exists k, get e x k}} (x <- zero) {{fun e => get e x 0}}.
Admitted.

(** On utilise un modèle de correction partiel, cela explique 
    qu'après une boucle qui ne termine jamais toute les post-conditions
    sont vérifiées : *)
Example hoare_infinite :   
    forall P Q, {{P}} while (zero << succ zero) skip {{ Q }}.
Admitted.

Lemma lt_ex: 
  forall a, 0 < a -> exists k, a = (S k).
Admitted.


(* Le dernier exemple est difficile, vous allez avoir besoin des lemmes suivants: *)

Lemma update_exists: 
   forall e x n, get e x n -> forall m, 
        exists e', update e x m e'. 
Admitted.

Lemma update_get : 
  forall e x n e', update e x n e' -> get e' x n.
Admitted.

Lemma get_update_get : 
  forall e x n, get e x n -> 
     forall e' x' n', update e x' n' e' -> 
      x <> x' -> get e' x n.
Admitted.

Example hoare_add : 
  forall a b, {{fun e => get e 0 a /\ get e 1 b}}
              add
              {{fun e => get e 0 0 /\ get e 1 (a+b)}}.
intros.
unfold add.
(** La tactique suivante vous est offerte par vos chargés de TD. *)
eapply hoare_consequence_pre with 
   (fun e => exists x, exists y, get e 0 x /\ get e 1 y /\ x+y=a+b).
Admitted.
