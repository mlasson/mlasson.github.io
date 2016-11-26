(*  TP n°1 : Introduction à Coq   *)

(* Coq est un langage de programmation fourni avec un interpréteur
   que l'on peut interroger -en autre- pour faire des calculs: *)

Eval compute in 2+2.
Eval compute in 6*8.

(* Toutes les expressions bien formées de Coq ont un type que l'on 
peut demander à l'interpréteur grâce à la commande "Check" : *)

Check 2+2. (* 2+2 a le type "nat" des entiers naturels *)
Check plus. (* l'addition "plus" prends deux entiers en paramètre et retourne 
             un entier. *)
(* Les types sont eux-mêmes des expressions bien formées de Coq, elles 
   ont donc également un type. *)

Check nat-> nat -> nat. (* Set est le type des types de données. *)

(* On peut également demander à Coq de nous donner la définition d'une 
   d'une expression déjà définie; on utilise pour ça la commande "Print". *) 
Print plus.

(* On peut bien sûr définir de nouvelles fonctions *) 
Definition times_two (n : nat) := 2 * n.

(* et on utilise la syntaxique suivante pour faire des définitions 
   récursives: *)

Fixpoint double (n : nat) := match n with 
  | 0 => 0
  | S p => S (S (double p))
 end.

Print double.

(* Sur le même modèle implémentez la fonction [sum: nat -> nat] qui calcule
   la somme des premiers entiers *)

Fixpoint sum (n : nat ) := 
(* ... Complétez ici ... *)

Eval compute in sum 3.

(* En plus des types de données et des programmes, coq permet également 
   de manipuler des formules. À commencer par les égalités : *)
Check 0 = 0. (* "Prop" est le type des formules logiques. *)
Check 0 = 1. (* Les formules fausses sont aussi des expressions valides ! *)

(* Enfin, Coq permet de prouver les formules à l'aide d'un système de 
   "tactiques" de preuves. *)
Lemma zero_equals_zero :
  0 = 0.
reflexivity. (* Comme on le verra plus tard, c'est la tactique qui
                  résout les égalités triviales. *)
Qed.

Lemma two_plus_two_equals_four : 
  2+2 = 4.
simpl. (* Cette tactique nous sera très utile dans la suite, elle
                  sert à effectuer les pas de calcul dans les buts. *)
reflexivity.
Qed.

(* On dispose également de quantificateurs pour fabriquer les formules :*)
Check (forall x y : nat, x+y = y + x). (* Une formule qui nous dit que + est commutatif. *)

(* Il y a tout un tas de tactiques qu'il faudra apprendre à utiliser.
   Voici un exemple de preuve un peu moins triviales. Pouvez-vous 
   retranscrire cette preuve simple en "mathématiques informelles" ? *)

Lemma f_double : 
  forall n, double n = n * 2.
intros n.
induction n.
  simpl.
  reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

(* Les deux tactiques centrales de COQ sont 
     - [intros H] : l'équivalent de "soit H" et de "supposons que..."
                   dans les maths informelles, [intros H] introduit une
                   hypothèse H dans le contexte.
       (notez qu'il est également permis d'invoquer [intros H1 H2 H3]
       à la place de [intros A. intros B. intros C.]  pour faire des 
       intros successifs)
     - [apply H] : permet d'invoquer l'hypothèse nommée H. *)

(* À vous de jouer maintenant ! *)

Lemma trivial1 : forall P:Prop, P -> P.

Qed.

Lemma trivial3: forall P Q R:Prop, (P -> Q -> R) -> (P -> Q) -> P -> R.

Qed.


(* Coq fournit les connecteurs logiques usuels : 
       connecteur ┃ destructeur ┃ constructeur
      ━━━━━━━━━━━━╋━━━━━━━━━━━━━╇━━━━━━━━━━━━━━━━━━━
          P /\ Q  ┃ [destruct]  ┆  [split]
          P \/ Q  ┃ [destruct]  ┆  [left] et [right]
  exists x:nat, P ┃ [destruct]  ┆  [exists t]          
          False   ┃ [destruct]  ┆  aucun 
*)

Lemma conj1: forall P Q:Prop, P /\ Q -> P.

Qed.

Lemma conj2: forall P Q:Prop, P /\ Q -> Q.

Qed.

Lemma conj3: forall P Q:Prop, P -> Q -> P /\ Q.

Qed.

Lemma or1 : forall P Q:Prop, P -> P \/ Q.

Qed.

Lemma or2 : forall P Q:Prop, Q -> P \/ Q.

Qed.

Lemma or3 : forall P Q R:Prop, P \/ Q -> (P -> R) -> (Q -> R) -> R.

Qed.

Lemma ex_falso: forall P:Prop, False -> P.

Qed.

Notation "~ P" := (P -> False).

Lemma not_not : forall P:Prop, P -> ~~P.

Qed.

Lemma morgan1 : forall P Q:Prop, 
  ~P \/ ~Q -> ~(P /\ Q).

Qed.

Lemma morgan2 : forall P Q:Prop, 
  ~P /\ ~Q -> ~(P \/ Q).

Qed.

(* On dispose également d'une égalité entre les termes de 
   coq qui vient avec trois tactiques pour les manipuler: 
      - [reflexivity] : permet de prouver les but de la forme t=t. 
      - [symmetry] : permet de transformer un but t₁ = t₂ en t₂ = t₁.
      - [rewrite H] : si H est une hypothèse de la forme "t₁ = t₂"
        cette tactique remplace dans le but courant les sous-termes
        de la forme t₁ par t₂.
      - [rewrite <-H] : si H est une hypothèse de la forme "t₁ = t₂"
        cette tactique remplace dans le but courant les sous-termes
        de la forme t₂ par t₁.  *)


Lemma eq_trans : forall (x y z:nat), x = y -> y = z -> x = z.

Qed.

(* Arithmétique *)

(* Rappel: on utilise la tactique simpl, pour simplifier les calculs. *)
Lemma zero_plus : forall x:nat, 0 + x = x.

Qed.

Lemma exists_factor : 
  exists n, exists m , n * (m+1) = 36.

Qed.

(* La tactique simpl ne marche par pour prouver la proposition
   suivante. Pourquoi ? *)

Lemma plus_zero : forall x:nat, x + 0 = x.

(* Il va nous faloir démontrer le résultat par récurrence sur la
   forme de x. 
   La tactique [induction x] invoque automatiquement le 
   principe d'induction pour prouver un but par induction sur 
   la variable x. *)

induction x.
(* Il faut ensuite prouver le cas de base et l'hérédité...*) 

Qed.

Lemma plus_assoc : forall a b c, (a + b) + c = a + (b + c).

Qed.

Lemma mult_zero : forall a, a*0 = 0.

Qed.



(* En coq on peut également définition des propositions
   qui dépendent de paramètre. Cela permet de représenter
   d'autres relations que l'égalité *)

Definition lesser_or_equal (n m : nat) := exists k, n+k = m.
Check lesser_or_equal. (* Méditez le types de la relation. *)

Infix "<=" := lesser_or_equal.  (* On déclare "<=" comme étant une notation
                                  cette relation. *)

Lemma lesser_or_equal_refl : 
  forall x, x <= x.

Qed.

Lemma lesser_or_equal_trans : 
  forall x y z, x <= y -> y <= z -> x <= z.

Qed.

(* Pour finir, quelques exercices pour occuper les plus rapides d'entre vous :*)

(* N'hésitez pas à faire des lemmes intermédiaires !*)


Lemma sum_formula: 
  forall n, 2 * (sum n) = n * (n+1).

Qed.

(* Ce n'est pas aussi trivial qu'il n'y paraît. *)
Lemma plus_comm : forall a b, a + b = b + a.

Qed.

Lemma identite : 
  forall a b, (a + b)*(a+b) = a*a + 2*a*b + b*b.

Qed.

(* Écrivez la fonction [power] qui calcule les puissances entières : *)
Fixpoint power a b := 
...

Infix "^" := power.

Lemma power_exp: 
  forall a n m, a^(n + m) = a^n * a^m.

Qed.

Lemma closed:
  forall n a b c, 3 <= n -> a^n + b^n = c^n -> a = c \/ b = c.

Qed.
