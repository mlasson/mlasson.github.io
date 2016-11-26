(***************** 1ere Partie  *********************)

(* Il s'agit de finir les preuves commencées en TP4 sur la sémantique de IMP.
  Vous pouvez soit continuer sur votre fichier pour TP4 soit sur ce fichier.
  Une partie des preuves est furnie.
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
   | execute_while_true : forall rho1 rho2 rho3 t p, 
         beval rho1 t true ->
         execute rho1 p rho3 ->
         execute rho3 (while t p) rho2 ->
         execute rho1 (while t p) rho2
   | execute_while_false : forall rho t p, 
         beval rho t false ->
         execute rho (while t p) rho.

Reserved Notation "A =>> B" (at level 80). 

Definition state := (prg * env)%type.
Notation "[ π | p ]" := (π,p).

(************************ 2eme Partie ***************************)

(* Dans cette partie on va s'interesser aux triples de Hoare.
*)

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
intros P Q c Hq.
intros e1 e2 Hex Hp.
apply Hq.
Qed.


Theorem hoare_pre_false : forall (P Q : assertion) c,
  (forall e, ~(P e)) ->
  {{P}} c {{Q}}.
intros.
intros e1 e2 Hex Hp.
destruct (H e1).
assumption.
Qed.


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
  {{P'}} c {{Q'}} ->
  (forall e, P e -> P' e) ->
  (forall e, Q' e -> Q e) ->
  {{P}} c {{Q}}.
intros P P' Q Q' c HH Hp Hq.
intros e1 e2 Hex H.
apply Hq.
unfold hoare_triple in HH.
apply HH with e1.
assumption.
apply Hp.
assumption.
Qed.
 

Theorem hoare_consequence_pre: forall (P P' Q : assertion) c,
  {{P'}} c {{Q}} ->
  (forall e, P e -> P' e) ->
  {{P}} c {{Q}}.
intros.
apply hoare_consequence with P' Q.
assumption.
assumption.
intros; assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : assertion) c,
  {{P}} c {{Q'}} ->
  (forall e, Q' e -> Q e) ->
  {{P}} c {{Q}}.
intros.
apply hoare_consequence with P Q'.
assumption.
intros; assumption.
assumption.
Qed.


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
intros P e1 e2 Hex Hp.
inversion Hex; subst.
assumption.
Qed.

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
intros P Q R c1 c2 H1 H2 e1 e2 Hex Hp.
unfold hoare_triple in H1, H2.
inversion Hex; subst.
apply H1 with rho2.
assumption.
apply H2 with e1; assumption.
Qed. 


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

(* Pour la preuve on a besion de 2 lemmes intermediares *)
Lemma aeval_eq :
  forall e a n1, aeval e a n1 -> forall n2,  aeval e a n2 -> n1 = n2.
intros e a n1 H1.
induction H1.
(* zero *)
intros n2 H2.
inversion H2; subst.
reflexivity.
(* var *)
intros n2 H2.
inversion H2.
subst.
induction H.
inversion H3; subst.
reflexivity.
destruct H7; reflexivity.
apply IHget.
constructor.
inversion H3; subst.
destruct H0; reflexivity.
assumption.
inversion H3; subst.
destruct H0; reflexivity.
assumption.
(* succ *)
intros n2 H2.
inversion H2.
subst.
assert (n = n0).
apply IHaeval.
assumption.
rewrite H.
reflexivity.
(* pred s *)
intros n2 H2.
inversion H2; subst.
assert (Heq : S n = S n2).
apply IHaeval.
assumption.
injection Heq.
trivial.
assert (Heq : S n = 0).
apply IHaeval.
assumption.
discriminate Heq.
(* pred 0 *)
intros n2 H2.
inversion H2; subst.
assert (Heq : 0 = S n2).
apply IHaeval.
assumption.
discriminate Heq.
reflexivity.
Qed.


Lemma update_eq :
  forall e x n e1, update e x n e1 -> 
forall e2, update e x n e2 -> e1 = e2.
intros e x n e1 H1.
induction H1.
intros e2 H2.
inversion H2; subst.
reflexivity. 
destruct H7; reflexivity.
intros e2 H2.
inversion H2; subst.
destruct H; trivial.
rewrite IHupdate with l'0; trivial.
Qed.


Theorem hoare_asgn : forall Q V a,
  {{asgn_sub V a Q }} (V <- a) {{Q}}.
unfold hoare_triple.
  intros Q V a e1 e2 HE HQ.
  unfold asgn_sub in HQ.
  destruct HQ as [v [e' [H0 [H1 H2]]]]. 
  inversion HE; subst.
  assert (v = n).
  apply aeval_eq with e1 a; assumption.
  subst.
  clear H0.
  assert (e' = e2).
  apply update_eq with e1 V n; assumption.
  subst;  assumption.  Qed.

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
 intros P Q b c1 c2 H1 H2.
 intros e1 e2 Hex Hp.
 unfold hoare_triple in H1, H2.
inversion Hex; subst.
 apply H1 with e1.
 assumption.
 split; assumption.
apply H2 with e1. 
 assumption.
 split; assumption.

Qed.

(************ While *)


(* 


               {{P /\ beval b true}} c {{P}}
        -----------------------------------  [hoare_while]
            {{P}} while b c {{P /\ beval b false}}
*)

Lemma hoare_while : forall b c P,
  {{fun e => P e /\ beval e b true}} c {{P}} ->
  {{P}} while b c {{fun e => P e /\ beval e b false}}.
 intros b c P Ho.
unfold hoare_triple in Ho |- *.
intros e1 e2 Hex Hp.
remember (while b c) as wcom.
induction Hex; subst; try discriminate Heqwcom.
injection Heqwcom.
intros; subst.
apply IHHex2.
assumption.
apply Ho with rho1.
assumption.
split; assumption.
injection Heqwcom; intros; subst.
split; assumption.
Qed.


(*** Exemple.

  On veut montrer : 
 
{{ x est declare dans l'environment }} x <- 0 {{x = 0}}

ou dans notre langage :
*)

(* Cette preuve est un peu technique, a cause du choix de formalisation pour
  les environments et pour get et update *)
(* Astuce : on peut raisoner par cas pour 2 entiers naturels n et m suivant 
  si n = m ou n <> m en utilisant la tactique [destruct (eq_nat_dec n m).]
*) 

Example hoare_asgn_example0 : forall x, 
  {{fun e => exists k, get e x k}} (x <- zero) {{fun e => get e x 0}}.
intros x.
apply hoare_consequence_pre with 
   (asgn_sub x zero (fun e => get e x 0)) .
apply hoare_asgn.
intros e [n Hn].
unfold asgn_sub.
exists 0.
induction e.
inversion Hn.
destruct a.
destruct (eq_nat_dec a x).
inversion Hn; subst.
exists ([x | 0] :: e).
split.
apply eval_zero.
split.
apply update_head.
apply get_head.
destruct H5; trivial.
inversion Hn; subst.
destruct n0; trivial.
destruct (IHe H4) as [e' [Hae [Hup Hg]] ].
exists ([a | v] :: e').
split.
apply eval_zero.
split.
apply update_tail; assumption.
apply get_tail; assumption.
Qed.


(** On utilise un modèle de correction partiel, cela explique 
    qu'après une boucle qui ne termine jamais toute les post-conditions
    sont vérifiées : *)
Example hoare_infinite :   
    forall P Q, {{P}} while (zero << succ zero) skip {{ Q }}.
intros P Q.
apply hoare_consequence_pre with (fun e => True).
intros; trivial.

apply hoare_consequence_post with 
  (fun e => True /\ beval e (zero << succ zero) false ).

apply hoare_while.
apply hoare_post_true.
intros; trivial.
intros.
destruct H.
inversion H0; subst.
inversion H3; subst.
inversion H5; subst.
inversion H6.
intros; trivial.
Qed.

Lemma lt_ex: 
  forall a, 0 < a -> exists k, a = (S k).
intros a Ha.
destruct a.
destruct (lt_irrefl 0 Ha).
exists a.
reflexivity.
Qed.


(* Le dernier exemple est difficile, vous allez avoir besoin des lemmes suivants: *)

Lemma update_exists: 
   forall e x n, get e x n -> forall m, 
        exists e', update e x m e'. 
intros e x n Hget m.
induction Hget.
exists ([a | m] :: l).
constructor.
destruct IHHget.
exists ([b | y] :: x0).
constructor.
assumption.
assumption.
Qed.



Lemma update_get : 
  forall e x n e', update e x n e' -> get e' x n.
intros e x n e' Hu.
induction Hu.
constructor.
constructor; assumption.
Qed.

Lemma get_update_get : 
  forall e x n, get e x n -> 
     forall e' x' n', update e x' n' e' -> 
      x <> x' -> get e' x n.
intros e x n Hget.
intros.
induction H.
inversion Hget; subst.
destruct H0.
reflexivity.
constructor.
assumption.
assumption.
inversion Hget; subst.
constructor.
constructor.
apply IHupdate.
assumption.
assumption.
assumption.
Qed.


Example hoare_add : 
  forall a b, {{fun e => get e 0 a /\ get e 1 b}}
              add
              {{fun e => get e 0 0 /\ get e 1 (a+b)}}.
intros.
unfold add.
apply hoare_consequence_pre with 
   (fun e => exists x, exists y, get e 0 x /\ get e 1 y /\ x+y=a+b).
apply hoare_consequence_post with 
  (fun e : env =>
      (fun e0 : env =>
       exists x : value,
         exists y : value, get e0 0 x /\ get e0 1 y /\ x + y = a + b) e /\
      beval e (zero << #(0)) false).
apply hoare_while.
intros e1 e2 Hex Hval.
destruct Hval as [[x [y H]] Ht].
destruct H as [H1 [H2 H3]].
inversion Hex; subst.
inversion H5.
inversion H7.
subst.
exists n.
exists n0.
split.
apply get_update_get with rho2 1 n0.
apply update_get with e1.
assumption.
assumption.
omega.
split.
apply update_get with rho2.
assumption.
inversion Ht; subst.
inversion H4; subst.
clear H4.
assert (Heqx : x = S n).
apply aeval_eq with e1 (#(0)).
constructor.
assumption.
inversion H6; subst.
assumption.
assert (Hv2: v2 = 0).
apply aeval_eq with e1 (#(0)); assumption.
rewrite Hv2 in H11.
destruct (lt_irrefl 0 H11).
assert (Heqy: n0 = S y).
apply aeval_eq with rho2 (succ #(1)).
assumption.
constructor.
constructor.
apply get_update_get with e1 0 n.
assumption.
assumption.
omega.
subst.
rewrite <-H3.
omega.
(************)
intros e [[x [y [Hg0 [Hg1 Heq]]]] Hb].
assert (Heqx: x = 0).
inversion Hb; subst.
inversion H1; subst.
assert (v2 = x).
apply aeval_eq with e (#(0)).
assumption.
constructor.
assumption.
rewrite <- H.
unfold value; omega.
subst.
simpl in Heq.
subst; split; assumption.
(***********)
intros e [Ha Hb].
exists a.
exists b.
split.
assumption.
split.
assumption.
reflexivity.
Qed.
