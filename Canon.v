(******************************************************************************)
(*                                                                            *)
(*                          CODE OF CANON LAW (1983)                          *)
(*                                                                            *)
(*     Formalizing the 1983 Code of Canon Law: marriage validity,             *)
(*     ordination requirements, excommunication latae sententiae,             *)
(*     tribunal procedures, and sacramental disciplines.                      *)
(*                                                                            *)
(*     Salus animarum suprema lex.                                            *)
(*     (Canon 1752)                                                            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 6, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

(******************************************************************************)
(* SECTION 1: PERSONS IN THE CHURCH                                           *)
(******************************************************************************)

(* Canonical status of a person *)
Inductive CanonicalStatus : Type :=
  | Layperson
  | Deacon
  | Priest
  | Bishop
  | Pope.

(* Baptismal status *)
Inductive BaptismalStatus : Type :=
  | Baptized
  | Unbaptized.

(* A person in canon law *)
Record CanonPerson : Type := mkPerson {
  cp_baptized   : BaptismalStatus;
  cp_status     : CanonicalStatus;
  cp_age        : nat;              (* age in years *)
  cp_male       : bool;             (* biological sex per canonical usage *)
  cp_excommunicated : bool;
  cp_interdicted    : bool;
}.

Definition is_catholic (p : CanonPerson) : bool :=
  match cp_baptized p with
  | Baptized   => true
  | Unbaptized => false
  end.

(******************************************************************************)
(* SECTION 2: MARRIAGE — CANONS 1055-1165                                    *)
(******************************************************************************)

(* Canon 1055: Marriage is an exclusive, permanent covenant between
   a man and a woman ordered to the good of the spouses and procreation. *)

(* Impediments to marriage (Canon 1073-1094) *)
Inductive MarriageImpediment : Type :=
  | AgeTooYoung            (* Canon 1083: male < 16, female < 14 *)
  | PriorBond              (* Canon 1085: prior valid marriage subsists *)
  | Disparity              (* Canon 1086: one party unbaptized *)
  | SacredOrders           (* Canon 1087: in sacred orders *)
  | PublicPerpetualVow     (* Canon 1088: public perpetual vow of chastity *)
  | Abduction              (* Canon 1089 *)
  | Crime                  (* Canon 1090: spouse murder *)
  | Consanguinity          (* Canon 1091 *)
  | Affinity               (* Canon 1092 *)
  | PublicPropriety        (* Canon 1093 *)
  | LegalRelationship.     (* Canon 1094 *)

(* Canon 1057: Marriage arises from the consent of the parties.
   Consent must be free, deliberate, and expressed in canonical form. *)
Record MarriageConsent : Type := mkConsent {
  mc_free       : bool;   (* not coerced *)
  mc_deliberate : bool;   (* not mistaken about the nature of marriage *)
  mc_expressed  : bool;   (* externally manifested in canonical form *)
}.

Definition consent_valid (c : MarriageConsent) : bool :=
  mc_free c && mc_deliberate c && mc_expressed c.

(* Canon 1083: Minimum age for valid marriage *)
Definition age_impediment_check (male : bool) (age : nat) : bool :=
  if male then Nat.ltb age 16 else Nat.ltb age 14.

(* Canon 1086: Disparity of cult — one party not baptized *)
Definition disparity_impediment (p1 p2 : BaptismalStatus) : bool :=
  match p1, p2 with
  | Baptized, Baptized => false
  | _, _               => true
  end.

(* Marriage is valid if consent is valid, no impediments, and both of age *)
Definition marriage_valid
    (p1_male : bool) (p1_age : nat) (p1_bap : BaptismalStatus)
    (p2_male : bool) (p2_age : nat) (p2_bap : BaptismalStatus)
    (consent : MarriageConsent)
    (has_other_impediment : bool) : bool :=
  consent_valid consent &&
  negb (age_impediment_check p1_male p1_age) &&
  negb (age_impediment_check p2_male p2_age) &&
  negb (disparity_impediment p1_bap p2_bap) &&
  negb has_other_impediment.

Theorem invalid_consent_voids_marriage : forall p1m p1a p1b p2m p2a p2b c i,
  consent_valid c = false ->
  marriage_valid p1m p1a p1b p2m p2a p2b c i = false.
Proof.
  intros. unfold marriage_valid. rewrite H. reflexivity.
Qed.

Theorem impediment_voids_marriage : forall p1m p1a p1b p2m p2a p2b c,
  marriage_valid p1m p1a p1b p2m p2a p2b c true = false.
Proof.
  intros. unfold marriage_valid. simpl.
  repeat rewrite andb_false_r. reflexivity.
Qed.

Theorem valid_marriage_requires_consent : forall p1m p1a p1b p2m p2a p2b c i,
  marriage_valid p1m p1a p1b p2m p2a p2b c i = true ->
  consent_valid c = true.
Proof.
  intros p1m p1a p1b p2m p2a p2b c i H.
  unfold marriage_valid in H.
  repeat rewrite andb_true_iff in H. tauto.
Qed.

(******************************************************************************)
(* SECTION 3: HOLY ORDERS — CANONS 1008-1054                                 *)
(******************************************************************************)

(* Canon 1024: Only a baptized male can validly receive sacred ordination. *)
Definition ordination_valid_candidate (p : CanonPerson) : bool :=
  is_catholic p &&
  cp_male p &&
  negb (cp_excommunicated p) &&
  negb (cp_interdicted p).

Theorem unbaptized_cannot_be_ordained : forall p,
  cp_baptized p = Unbaptized ->
  ordination_valid_candidate p = false.
Proof.
  intros p H.
  unfold ordination_valid_candidate, is_catholic. rewrite H. reflexivity.
Qed.

Theorem excommunicated_cannot_be_ordained : forall p,
  cp_excommunicated p = true ->
  ordination_valid_candidate p = false.
Proof.
  intros p H.
  unfold ordination_valid_candidate.
  destruct (is_catholic p); [|reflexivity].
  destruct (cp_male p); [|reflexivity].
  rewrite H. reflexivity.
Qed.

(* Canon 1031: Minimum age for ordination to the diaconate: 25 (transitional) *)
Definition min_age_priesthood  : nat := 25.
Definition min_age_episcopate  : nat := 35.

Definition age_for_orders (status : CanonicalStatus) (age : nat) : bool :=
  match status with
  | Priest => Nat.leb min_age_priesthood age
  | Bishop => Nat.leb min_age_episcopate age
  | Deacon => Nat.leb 23 age   (* permanent diaconate: 35; transitional: 23 *)
  | _      => true
  end.

Lemma priest_needs_25 :
  age_for_orders Priest 24 = false /\
  age_for_orders Priest 25 = true.
Proof. split; reflexivity. Qed.

(******************************************************************************)
(* SECTION 4: EXCOMMUNICATION LATAE SENTENTIAE                               *)
(******************************************************************************)

(* Canon 1364-1399: Offenses that incur automatic excommunication *)
Inductive LataeSententiaeOffense : Type :=
  | Apostasy               (* Canon 1364 *)
  | Heresy                 (* Canon 1364 *)
  | Schism                 (* Canon 1364 *)
  | DesecrationEucharist   (* Canon 1367 *)
  | ViolatingConfessional  (* Canon 1388 §1 *)
  | OrdainingWoman         (* Canon 1379 §2, 2021 *)
  | ProcuringAbortion      (* Canon 1397 §2 *)
  | ConsecrateBishopWithout (* Canon 1382 — both parties *)
  | ViolatingPapalSecret.  (* Canon 1386 *)

(* Canon 1321: A penalty requires imputability — grave offense with dolus or culpa *)
Record Imputability : Type := mkImpute {
  imp_gravely_imputable : bool;   (* full knowledge and deliberate consent *)
  imp_not_minors        : bool;   (* not a minor (< 18) *)
  imp_not_insane        : bool;   (* not lacking reason *)
}.

Definition excommunication_incurred
    (offense : LataeSententiaeOffense)
    (imp : Imputability) : bool :=
  imp_gravely_imputable imp &&
  imp_not_minors        imp &&
  imp_not_insane        imp.

Theorem not_imputable_no_excommunication : forall o imp,
  imp_gravely_imputable imp = false ->
  excommunication_incurred o imp = false.
Proof.
  intros o imp H.
  unfold excommunication_incurred. rewrite H. reflexivity.
Qed.

Theorem minor_no_excommunication : forall o imp,
  imp_not_minors imp = false ->
  excommunication_incurred o imp = false.
Proof.
  intros o imp H.
  unfold excommunication_incurred.
  destruct (imp_gravely_imputable imp); [rewrite H; reflexivity | reflexivity].
Qed.

(******************************************************************************)
(* SECTION 5: SACRAMENTS — GENERAL CONDITIONS                                *)
(******************************************************************************)

(* Canon 840: Sacraments are actions of Christ and the Church.
   Validity requires correct matter, form, minister, and intent. *)

Record SacramentConditions : Type := mkSacrament {
  sc_valid_matter   : bool;
  sc_valid_form     : bool;
  sc_valid_minister : bool;
  sc_minister_intent: bool;   (* intends to do what the Church does *)
}.

Definition sacrament_valid (s : SacramentConditions) : bool :=
  sc_valid_matter    s &&
  sc_valid_form      s &&
  sc_valid_minister  s &&
  sc_minister_intent s.

Theorem sacrament_invalid_without_intent : forall s,
  sc_minister_intent s = false ->
  sacrament_valid s = false.
Proof.
  intros s H.
  unfold sacrament_valid.
  repeat rewrite andb_assoc || idtac.
  rewrite andb_false_r || idtac.
  destruct (sc_valid_matter s); destruct (sc_valid_form s);
    destruct (sc_valid_minister s); rewrite H; reflexivity.
Qed.

Theorem all_conditions_required : forall s,
  sacrament_valid s = true ->
  sc_valid_matter s = true /\
  sc_valid_form s = true /\
  sc_valid_minister s = true /\
  sc_minister_intent s = true.
Proof.
  intros s H.
  unfold sacrament_valid in H.
  repeat rewrite andb_true_iff in H. tauto.
Qed.

(******************************************************************************)
(* SECTION 6: TRIBUNAL PROCEDURE — CANONS 1400-1500                          *)
(******************************************************************************)

(* Canon 1401: The Church has the right to judge its own members in
   spiritual matters and violations of ecclesiastical law. *)

(* Canon 1481-1490: Right to defense — no one may be punished unless
   given the opportunity to defend themselves. *)

Record CanonTrial : Type := mkTrial {
  ct_accused_notified  : bool;   (* accused informed of charges *)
  ct_defense_permitted : bool;   (* opportunity to respond given *)
  ct_judge_impartial   : bool;   (* judge is not the accuser *)
  ct_evidence_reviewed : bool;   (* evidence examined *)
}.

Definition trial_valid (t : CanonTrial) : bool :=
  ct_accused_notified  t &&
  ct_defense_permitted t &&
  ct_judge_impartial   t &&
  ct_evidence_reviewed t.

Theorem trial_requires_notice : forall t,
  ct_accused_notified t = false ->
  trial_valid t = false.
Proof.
  intros t H. unfold trial_valid. rewrite H. reflexivity.
Qed.

Theorem trial_requires_defense : forall t,
  ct_defense_permitted t = false ->
  trial_valid t = false.
Proof.
  intros t H. unfold trial_valid.
  destruct (ct_accused_notified t); [rewrite H; reflexivity | reflexivity].
Qed.

(******************************************************************************)
(* SECTION 7: PARISHES AND PASTORS — CANONS 515-552                          *)
(******************************************************************************)

(* Canon 521: To be appointed pastor, one must be a priest in full communion,
   of good moral standing, and have the requisite pastoral skills. *)

Definition valid_pastor_candidate (p : CanonPerson) : bool :=
  match cp_status p with
  | Priest | Bishop | Pope => true
  | _                      => false
  end &&
  is_catholic p &&
  negb (cp_excommunicated p).

Lemma layperson_cannot_be_pastor : forall p,
  cp_status p = Layperson ->
  valid_pastor_candidate p = false.
Proof.
  intros p H. unfold valid_pastor_candidate. rewrite H. reflexivity.
Qed.

Lemma deacon_cannot_be_pastor : forall p,
  cp_status p = Deacon ->
  valid_pastor_candidate p = false.
Proof.
  intros p H. unfold valid_pastor_candidate. rewrite H. reflexivity.
Qed.

(******************************************************************************)
(* SECTION 8: PENAL LAW — CANON 1311-1399                                    *)
(******************************************************************************)

(* Canon 1311: The Church has the innate and proper right to coerce
   offending members with penal sanctions. *)

Inductive PenalSanction : Type :=
  | Warning
  | Censure        (* censura: excommunication, interdict, suspension *)
  | Expiatory      (* loss of office, prohibition, etc. *)
  | Excommunication_Ferendae  (* imposed by authority *)
  | Interdict_Ferendae
  | Suspension.    (* clerics only *)

(* Canon 1321 §3: Ignorance of the law reduces imputability *)
Inductive ImputableLevel : Type :=
  | FullImputability
  | PartialImputability  (* reduced due to ignorance, passion, etc. *)
  | NoImputability.      (* no penalty *)

Definition penalty_applicable (level : ImputableLevel) : bool :=
  match level with
  | FullImputability    => true
  | PartialImputability => true   (* reduced penalty still applicable *)
  | NoImputability      => false
  end.

Theorem no_imputability_no_penalty : forall level,
  level = NoImputability ->
  penalty_applicable level = false.
Proof.
  intros level H. rewrite H. reflexivity.
Qed.

(******************************************************************************)
(* SECTION 9: HIERARCHICAL AUTHORITY                                          *)
(******************************************************************************)

(* The Church has a hierarchical structure. A bishop has authority over
   priests in his diocese; priests over deacons; all under the Pope. *)

Definition canonical_rank (s : CanonicalStatus) : nat :=
  match s with
  | Layperson => 0
  | Deacon    => 1
  | Priest    => 2
  | Bishop    => 3
  | Pope      => 4
  end.

Theorem pope_highest_rank : forall s,
  canonical_rank s <= canonical_rank Pope.
Proof.
  intros []; simpl; lia.
Qed.

Theorem layperson_lowest_rank : forall s,
  canonical_rank Layperson <= canonical_rank s.
Proof.
  intros []; simpl; lia.
Qed.

Theorem bishop_outranks_priest :
  canonical_rank Priest < canonical_rank Bishop.
Proof. simpl. lia. Qed.

(* Authority requires rank: a lower-ranked minister cannot delegate
   to a higher-ranked one for jurisdiction purposes *)
Definition can_delegate (delegator delegatee : CanonicalStatus) : bool :=
  Nat.leb (canonical_rank delegatee) (canonical_rank delegator).

Lemma priest_cannot_delegate_to_bishop :
  can_delegate Priest Bishop = false.
Proof. reflexivity. Qed.

Lemma bishop_can_delegate_to_priest :
  can_delegate Bishop Priest = true.
Proof. reflexivity. Qed.

(******************************************************************************)
(* SECTION 10: SUMMARY                                                        *)
(******************************************************************************)

(*
  This file formalizes key structures of the 1983 Code of Canon Law.

  Areas covered:
    1. Persons: canonical status (layperson, deacon, priest, bishop, pope),
       baptismal status, excommunication, interdict.
    2. Marriage (cc. 1055-1165): consent validity (free, deliberate, expressed);
       impediments (age, prior bond, disparity of cult, sacred orders, etc.);
       marriage_valid predicate.
    3. Holy Orders (cc. 1008-1054): valid candidate (baptized male, not
       excommunicated); minimum ages (deacon 23, priest 25, bishop 35).
    4. Excommunication latae sententiae (cc. 1364-1399): nine enumerated
       offenses; imputability requirements; minors and the insane exempt.
    5. Sacraments (c. 840): valid matter, form, minister, and intent —
       all four required.
    6. Tribunal procedure (cc. 1400-1500): notice, defense, impartiality,
       evidence — all four required for a valid trial.
    7. Parishes (cc. 515-552): only priests/bishops/popes can be pastors.
    8. Penal law (cc. 1311-1399): no penalty without imputability.
    9. Hierarchical authority: canonical rank ordering; delegation rules.

  Key theorems:
    - invalid_consent_voids_marriage / impediment_voids_marriage
    - unbaptized_cannot_be_ordained / excommunicated_cannot_be_ordained
    - not_imputable_no_excommunication / minor_no_excommunication
    - sacrament_invalid_without_intent
    - trial_requires_notice / trial_requires_defense
    - pope_highest_rank / layperson_lowest_rank
    - priest_cannot_delegate_to_bishop

  All proofs closed; no Admitted lemmas.
*)
