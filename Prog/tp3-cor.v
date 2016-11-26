(* TP n°3 *)
Require Import rel.

(* Durant le reste du TP, on va chercher à étudier la sémantique 
   à petits pas et à grands pas pour le language minimaliste suivant:  *)

Inductive expr : Set :=
  | N : nat -> expr
  | Plus : expr -> expr -> expr
  | Mult : expr -> expr -> expr
  | Minus : expr -> expr -> expr.

Infix "[+]" := Plus (at level 50, left associativity).
Infix "[*]" := Mult (at level 40, left associativity).
Infix "[-]" := Minus(at level 50, left associativity).

Definition example := (N 1) [+] (N 5) [*] (N 4) [-] (N 2).

Reserved Notation "x '-->' y" (at level 60).

(* Implémentez une sémantique à petit pas pour l'évalution 
    de ces expressions à l'aide d'un prédicat inductif. *)
Inductive ss : expr -> expr -> Prop := 
  | ss_plus : forall n m, ((N n) [+] (N m)) --> (N (n + m))
  | ss_mult : forall n m, ((N n) [*] (N m)) --> (N (n * m))
  | ss_minus : forall n m, ((N n) [-] (N m)) --> (N (n - m))
  | ss_left_plus : forall a a' b, a --> a' -> (a [+] b) --> (a' [+] b)
  | ss_left_mult : forall a a' b, a --> a' -> (a [*] b) --> (a' [*] b)
  | ss_left_minus : forall a a' b, a --> a' -> (a [-] b) -->  (a' [-] b)
  | ss_right_plus : forall a b b', b --> b' -> (a [+] b) --> (a [+] b')
  | ss_right_mult : forall a b b', b --> b' -> (a [*] b) --> (a [*] b')
  | ss_right_minus : forall a b b', b --> b' -> (a [-] b) --> (a [-] b')
where "a --> b" := (ss a b).


Definition sse := star expr ss. 

Infix "-->>" := sse (at level 60).

(* Indice :  [replace t₁ with t₂] remplace toute 
    occurrence de t₁ par t₂ et génère le but (t₂=t₁) *)
Lemma ten : example -->> (N 19).
  unfold example.
  eapply star_R.
  eapply ss_left_minus.
  eapply ss_right_plus.
  eapply ss_mult.

  eapply star_R.
  eapply ss_left_minus.
  eapply ss_plus.
  
  eapply star_R.
  eapply ss_minus.
  simpl.
  eapply star_refl.
Qed.


(* Est-ce que votre solution est déterministe ? 
    Est-ce que vous pourriez trouver une version ss' déterministe ? 
    (Exercice à la maison: prouver que ss et ss' définissent la même 
     clôture reflexive-transitive et que ss' est bien déterministe (pas 
     facile)). *)

(* Donnez maintenant une sémantique à grand pas. *)
Inductive bs : expr -> nat -> Prop := 
  | bs_nat : forall n, bs (N n) n
  | bs_plus : forall e₁ e₂ n₁ n₂, bs e₁ n₁ -> bs e₂ n₂ -> bs (e₁ [+] e₂) (n₁ + n₂)
  | bs_mult : forall e₁ e₂ n₁ n₂, bs e₁ n₁ -> bs e₂ n₂ -> bs (e₁ [*] e₂) (n₁ * n₂)
  | bs_minus : forall e₁ e₂ n₁ n₂, bs e₁ n₁ -> bs e₂ n₂ -> bs (e₁ [-] e₂) (n₁ - n₂)
.

(* Vous pouvez utiliser la tactique [rewrite t₁ with t₂]. *)
Lemma dix : bs example 19.
  unfold example.
  replace 19 with (1+5*4-2).
  repeat constructor.
  reflexivity.
Qed.

(* On peut aussi utiliser les points fixe de coq pour 
   évaluer ce language (c'est pas toujours possible, mais là 
   le language est vraiment très simple : *)
Fixpoint eval e := match e with 
  | N n => n 
  | e₁ [+] e₂ => (eval e₁) + (eval e₂)
  | e₁ [*] e₂ => (eval e₁) * (eval e₂)
  | e₁ [-] e₂ => (eval e₁) - (eval e₂) end.

(* Prouver que la sémantique à grand pas est correcte vis-à-vis d'éval. *)
Lemma bs_correct : forall e, bs e (eval e).
  intros e; induction e; simpl; auto using bs_nat, bs_mult, bs_minus, bs_plus.
Qed.

(* En déduire que la sémantique à grands pas est totale. *)
Lemma bs_tot : forall e, exists n, bs e n.
  intros e; exists (eval e).
  apply bs_correct.

Qed.

(* On va commencer par prouver que "grand pas" implique "petit pas". *)
 
(* Tout d'abord deux petits lemmes pour vous aider. *)
Lemma star_ss_plus : forall  a b c, a -->> c ->  (a [+] b) -->> (c [+] b). 
   intros a b c H.
   induction H.
   apply star_refl.
   eapply star_R.
   apply ss_left_plus.
   eassumption.
   assumption.
Qed. 

Lemma star_ss_plus' : forall a b c,  b -->> c -> (a [+] b) -->> (a [+] c). 
   intros a b c H.
   induction H.
   apply star_refl.
   eapply star_R.
   apply ss_right_plus.
   eassumption.
   assumption.
Qed. 

Lemma bs_sse : forall a n, bs a n -> sse a (N n).
 intros n a H.
 induction H.
 apply star_refl.
 eapply star_trans.
  eapply star_ss_plus.
eassumption.
 eapply star_trans.
   eapply star_ss_plus'.
eassumption.
  eapply star_R.
  eapply ss_plus. 
  eapply star_refl.
Admitted. 

(* En déduire que la sémantique à petits pas est totale. *)
Lemma sse_tot : forall e, exists n, sse e (N n).
  intros e. exists (eval e).
  apply bs_sse.
  apply bs_correct.
Qed.

(* Et maintenant on va prouver la réciproque: 
       "Petit pas" implique "grand pas". *)

(* Mais avant tout d'autres lemmes. *)
(* Rappel : [inversion H]  élimine des cas impossibles
    si le type de H est inductif.
    Il peut être pratique de simplifier les hypothèses
    obtenues en utilisant [subst]. *)
Lemma ss_bs_bs: forall a b, ss a b -> forall n, bs b n -> bs a n.
  intros a b H1.
  induction H1; intros k H2; inversion H2; subst; 
  try repeat constructor; auto.    
Qed. 

Lemma  sse_bs_aux : forall a b n, sse a b -> b = N n -> bs a n.
  intros a b n H.
  induction H; intros; subst.
  constructor.
  eapply ss_bs_bs.
  eassumption.
  apply IHstar.
  reflexivity.
Qed. 

Lemma sse_bs : forall a n, sse a (N n) -> bs a n.
  intros a n H.
  eapply sse_bs_aux. 
  eassumption.
  reflexivity.
Qed. 


(* Dans cette dernière partie, on va compiler notre language de 
    départ en notation polonaise inversée et on va prouver 
    que la compilation préserve la sémantique. *)

(* On charge le module [List] de la bibliothèque standard. *)
Require Import List. 

Check (1::2::nil). (** Ça marche comme en caml (sauf que [] est noté nil). *)
Print list. (* Vous pouvez regarder la définition. *)
 
(* On compile vers une liste de cexpr *)
Inductive cexpr : Set :=
  | cN : nat -> cexpr
  | cPlus : cexpr
  | cMult : cexpr
  | cMinus : cexpr.

(* (1 + 2) * (5 - 2) est compilé en la liste [1;2;+;5;2;-;*]. *)

(* Implémentez la fonction de compilation [compile e l] qui 
   compile l'expression [e] et concatène la liste obtenue à [l]. 
   Conseil: il faut voir [l] comme étant "la suite des calculs". *)
Fixpoint compile e l := match e with 
  | N n => (cN n)::l
  | e₁ [+] e₂ => compile e₁ (compile e₂ (cPlus::l))
  | e₁ [*] e₂ => compile e₁ (compile e₂ (cMult::l))
  | e₁ [-] e₂ => compile e₁ (compile e₂ (cMinus::l))
 end.

(* Ce prédicat décrit l'exécution d'une petit machine à pile. 
    Essayez de comprendre comment elle calcule. *)
Inductive exec : list cexpr * list nat -> list cexpr * list nat -> Prop :=
  | exec_nat   : forall n l e, exec ((cN n) ::l,e) (l,n::e)
  | exec_plus  : forall l a b e, exec (cPlus :: l, a :: b :: e) (l,(b+a) :: e)
  | exec_mult  : forall l a b e, exec (cMult :: l, a :: b :: e) (l,(b*a) :: e) 
  | exec_minus : forall l a b e, exec (cMinus :: l, a :: b :: e) (l,(b-a) :: e).

Infix "=>" := exec (at level 40). 

(* On prend sa cloture-reflexive transitive. *)
Notation "a =>> b" := (star _ exec a b) (at level 40).

(* Montrez qu'elle est correcte vis-à-vis de big step: *)
Lemma compilation_correct_aux :
  forall a n, bs a n -> forall l l', (compile a l,l') =>> (l,n :: l').
  intros a n H.
  induction H; simpl; intros.

  eapply star_R. eapply exec_nat. eapply star_refl.
  
  eapply star_trans; [ eapply IHbs1 
                     | eapply star_trans ; 
                         [ eapply IHbs2 
                         | eapply star_R; 
                           [ eapply exec_plus
                           | eapply star_refl]
                     ]   ].
  
  eapply star_trans; [ eapply IHbs1 
                     | eapply star_trans ; 
                         [ eapply IHbs2 
                         | eapply star_R; 
                           [ eapply exec_mult
                           | eapply star_refl]
                     ]   ].

  eapply star_trans; [ eapply IHbs1 
                     | eapply star_trans ; 
                         [ eapply IHbs2 
                         | eapply star_R; 
                           [ eapply exec_minus
                           | eapply star_refl]
                     ]   ].
Qed.
 
(* Voilà ! *)
Lemma compilation_correct : 
  forall a n, bs a n -> (compile a nil,nil) =>> (nil,n :: nil).
  intros. 
  apply compilation_correct_aux.
  assumption.
Qed.


(* Exercices suplémentaires :
    confluence à grands pas et à petits pas. *)
Lemma bs_conflu : forall a n, bs a n -> forall m, bs a m -> n = m.
  intros a n H1.
  induction H1; intros m H2; inversion H2; auto.
Qed.

(* En déduire la confluence de petits pas. *)
(* Indice : [cut P] permet d'utiliser P comme étape intermédiaire *)

Lemma ss_bs_bs2: forall a b, ss a b -> forall n, bs a n -> bs b n.
  intros a b H1.
  induction H1; intros k H2; inversion H2; subst; 
  try repeat constructor; auto;
  inversion_clear H1;
  inversion_clear H4;
  constructor.
Qed. 

Lemma sse_bs_bs2: forall a b, sse a b -> forall n, bs a n -> bs b n.
  intros a b H1.
  induction H1.
  trivial.
  intros.
  apply IHstar.
  eapply ss_bs_bs2.
  eassumption.
  eassumption.
Qed.


Lemma ss_conflu : forall a b b', 
   sse a b -> sse a b' -> exists c, sse b c /\ sse b' c.
   intros a b b' H1 H2. 
   exists (N (eval a)); split.
   
    
   clear H2. 
   apply bs_sse.
   eapply sse_bs_bs2.
   eassumption.
   eapply bs_correct.

   clear H1.
   apply bs_sse.
   eapply sse_bs_bs2.
   eassumption.
   eapply bs_correct.
Qed.


