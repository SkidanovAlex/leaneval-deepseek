/-
**The three Bender families satisfy the abstract Bender-action axioms.**

Suzuki's classification of Bender groups starts from the following situation: a finite group `G`
acting faithfully and transitively on a set `Ω` of more than one point, such that *every
involution of `G` fixes exactly one point of `Ω`*.  In the commons this is packaged by
`Commons.GroupTheory.Bender.isBenderAction_coset`: for a strongly embedded subgroup `M` of a
finite group `G`, the natural action of `G` on `G ⧸ M` is a Bender action, and then
`Commons.GroupTheory.Bender.existsUnique_fixedPoint_isPGroup_two` shows that every non-trivial
`2`-subgroup of `G` has a unique fixed point.

In this file we instantiate these abstract results for the three families, so that the models
`PSL(2,2ⁿ)`, `Sz(2^(2n+1))` and `PSU(3,2ⁿ)` are seen to satisfy the hypotheses of Suzuki's
theory.  The fixed-point statement for a Sylow `2`-subgroup is the structural input used to
identify the point stabiliser with the normaliser of a Sylow `2`-subgroup.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSL2Model
import Submission.Work.Models.Port.Sz.StronglyEmbedded
import Submission.Work.Models.Port.Sz.TwoTransitive
import Submission.Work.Models.Port.PSU3.Main
import Submission.Work.Models.Port.PSU3.Sylow
import Submission.Work.Models.Port.PSU3.Simple
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.isBenderAction_coset
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.existsUnique_fixedPoint_isPGroup_two
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.eq_of_smul_eq_self_of_mem_of_isPGroup_two
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.stronglyEmbedded_stabilizer_projectiveSpecialLinearGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs

namespace Submission

/-! ## `PSL(2, 2ⁿ)` -/

theorem pSL2Model_isBenderAction (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : Subgroup (PSL2Model n),
      MulAction.IsPretransitive (PSL2Model n) (PSL2Model n ⧸ M) ∧
        1 < Nat.card (PSL2Model n ⧸ M) ∧ Even (Nat.card (PSL2Model n)) ∧
        ∀ t : PSL2Model n, orderOf t = 2 → ∃! x : PSL2Model n ⧸ M, t • x = x := by
  obtain ⟨M, hM⟩ := PSL2Model_exists_isStronglyEmbedded n hn
  obtain ⟨hne, heven, hodd⟩ := hM
  exact ⟨M, Commons.GroupTheory.Bender.isBenderAction_coset M hne heven hodd⟩

theorem pSL2Model_existsUnique_fixedPoint_isPGroup_two (n : ℕ) (hn : 2 ≤ n)
    (M : Subgroup (PSL2Model n)) (hM : IsStronglyEmbedded M)
    (P : Subgroup (PSL2Model n)) (hP : IsPGroup 2 P) (hPne : P ≠ ⊥) :
    ∃! x : PSL2Model n ⧸ M, ∀ g : P, (g : PSL2Model n) • x = x := by
  obtain ⟨hne, heven, hodd⟩ := hM
  obtain ⟨-, -, hEvenG, hinv⟩ :=
    Commons.GroupTheory.Bender.isBenderAction_coset M hne heven hodd
  exact Commons.GroupTheory.Bender.existsUnique_fixedPoint_isPGroup_two hEvenG hinv P hP hPne

/-! ## `Sz(2^(2n+1))` -/

theorem szModel_isBenderAction (n : ℕ) (hn : 1 ≤ n) :
    MulAction.IsPretransitive (SzModel n) (SzModel n ⧸ Submission.Sz.szBorelS n) ∧
      1 < Nat.card (SzModel n ⧸ Submission.Sz.szBorelS n) ∧
      Even (Nat.card (SzModel n)) ∧
      ∀ t : SzModel n, orderOf t = 2 →
        ∃! x : SzModel n ⧸ Submission.Sz.szBorelS n, t • x = x := by
  obtain ⟨hne, heven, hodd⟩ := Submission.Sz.szBorel_stronglyEmbedded n hn
  exact Commons.GroupTheory.Bender.isBenderAction_coset (Submission.Sz.szBorelS n)
    hne heven hodd

theorem szModel_existsUnique_fixedPoint_isPGroup_two (n : ℕ) (hn : 1 ≤ n)
    (P : Subgroup (SzModel n)) (hP : IsPGroup 2 P) (hPne : P ≠ ⊥) :
    ∃! x : SzModel n ⧸ Submission.Sz.szBorelS n, ∀ g : P, (g : SzModel n) • x = x := by
  obtain ⟨-, -, hEvenG, hinv⟩ := szModel_isBenderAction n hn
  exact Commons.GroupTheory.Bender.existsUnique_fixedPoint_isPGroup_two hEvenG hinv P hP hPne

/-! ## `PSU(3, 2ⁿ)` -/

theorem psu3Model_isBenderAction (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : Subgroup (PSU3Model n),
      MulAction.IsPretransitive (PSU3Model n) (PSU3Model n ⧸ M) ∧
        1 < Nat.card (PSU3Model n ⧸ M) ∧ Even (Nat.card (PSU3Model n)) ∧
        ∀ t : PSU3Model n, orderOf t = 2 → ∃! x : PSU3Model n ⧸ M, t • x = x := by
  obtain ⟨M, hM⟩ := Submission.PSU3.PSU3Model_exists_isStronglyEmbedded n hn
  obtain ⟨hne, heven, hodd⟩ := hM
  exact ⟨M, Commons.GroupTheory.Bender.isBenderAction_coset M hne heven hodd⟩

theorem psu3Model_existsUnique_fixedPoint_isPGroup_two (n : ℕ) (hn : 2 ≤ n)
    (M : Subgroup (PSU3Model n)) (hM : IsStronglyEmbedded M)
    (P : Subgroup (PSU3Model n)) (hP : IsPGroup 2 P) (hPne : P ≠ ⊥) :
    ∃! x : PSU3Model n ⧸ M, ∀ g : P, (g : PSU3Model n) • x = x := by
  obtain ⟨hne, heven, hodd⟩ := hM
  obtain ⟨-, -, hEvenG, hinv⟩ :=
    Commons.GroupTheory.Bender.isBenderAction_coset M hne heven hodd
  exact Commons.GroupTheory.Bender.existsUnique_fixedPoint_isPGroup_two hEvenG hinv P hP hPne


/-! ## The Suzuki condition `[G : B] = |U| + 1`

In each of the three families the number of points of the Bender action is one more than the
order of the Sylow `2`-subgroup `U`; this is the key numerical relation of Suzuki's
classification (it forces the possible degrees `q + 1`, `q² + 1`, `q³ + 1`).  In the general
rank-`1` BN-pair setting it is the content of the commons lemma
`Commons.GroupTheory.Subgroup.index_eq_one_add_card_of_doubleCoset_cover`.
-/

/-- `Sz(2^(2n+1))`: the degree `q² + 1` of the Bender action is `|U| + 1`. -/
theorem szBorelS_index_eq_one_add_card_szTwoGroupS (n : ℕ) :
    (Submission.Sz.szBorelS n).index = 1 + Nat.card ↥(Submission.Sz.szTwoGroupS n) := by
  have h1 : Nat.card (Submission.Sz.SzField n) ^ 2 = 2 ^ (4 * n + 2) := by
    rw [Submission.Sz.card_szField, ← pow_mul]
    congr 1
    ring
  rw [Submission.Sz.card_szBorelS_index, Submission.Sz.card_szTwoGroupS, h1, Nat.add_comm]

/-- `PSU(3,2ⁿ)`: the degree `q³ + 1` of the Bender action is `|U| + 1`. -/
theorem suBS_index_eq_one_add_card_suUS (n : ℕ) (hn : 1 ≤ n) :
    (Submission.PSU3.suBS n).index = 1 + Nat.card ↥(Submission.PSU3.suUS n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : Nat.card ↥(Submission.PSU3.suUS n) = 2 ^ (3 * n) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Submission.PSU3.suU_le_SU3 n)).toEquiv,
      Submission.PSU3.card_suU n hn]
  have h1 : (Submission.PSU3.suBS n).index = 2 ^ (3 * n) + 1 := by
    rw [← Submission.PSU3.normalizer_suUS n hn,
      ← Submission.PSU3.suSylow_coe n hn,
      ← Sylow.card_eq_index_normalizer (Submission.PSU3.suSylow n hn),
      Submission.PSU3.card_sylow2_SU3 n hn]
  rw [h1, h2, Nat.add_comm]

/-- `PSL(2,2ⁿ)`: the degree `q + 1` of the Bender action is `|U| + 1`, where `|U| = 2ⁿ`. -/
theorem pSL2Stabilizer_index_eq_one_add_sylowTwo (n : ℕ) (hn : 1 ≤ n)
    (a : Projectivization (GaloisField 2 n) (Fin 2 → GaloisField 2 n)) :
    (MulAction.stabilizer (PSL2Model n) a).index = 1 + 2 ^ n := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  haveI : MulAction.IsMultiplyPretransitive (PSL2Model n)
      (Projectivization (GaloisField 2 n) (Fin 2 → GaloisField 2 n)) 2 :=
    Commons.GroupTheory.SL2.isMultiplyPretransitive_projectiveSpecialLinearGroup_two
  haveI : MulAction.IsPretransitive (PSL2Model n)
      (Projectivization (GaloisField 2 n) (Fin 2 → GaloisField 2 n)) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hos := Commons.GroupTheory.SL2.natCard_stabilizer_mul_natCard_eq_of_pretransitive
    (G := PSL2Model n) (X := Projectivization (GaloisField 2 n) (Fin 2 → GaloisField 2 n)) a
  rw [Commons.GroupTheory.SL2.natCard_projectivization_fin_two (K := GaloisField 2 n),
    GaloisField.card (p := 2) (n := n) (by omega)] at hos
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer (PSL2Model n) a)
  have hpos : 0 < Nat.card ↥(MulAction.stabilizer (PSL2Model n) a) := Nat.card_pos
  have : Nat.card ↥(MulAction.stabilizer (PSL2Model n) a) *
      (MulAction.stabilizer (PSL2Model n) a).index =
      Nat.card ↥(MulAction.stabilizer (PSL2Model n) a) * (2 ^ n + 1) := by
    rw [hcard, ← hos]
  have hfin : (MulAction.stabilizer (PSL2Model n) a).index = 2 ^ n + 1 :=
    Nat.mul_left_cancel hpos this
  rwa [Nat.add_comm] at hfin


/-! ## The Suzuki `2`-group acts freely off the base point

Once `[G : B] = |U| + 1` is known, the abstract Bender action theory
(`Commons.GroupTheory.Bender.existsUnique_fixedPoint_isPGroup_two`) shows that every non-trivial
element of `U` fixes only the base point; equivalently `U` acts regularly (sharply transitively)
on the remaining `|U|` points.  This is the Frobenius structure of the Borel subgroup used in
Suzuki's classification.
-/

/-- A non-trivial element of `U = O₂(B) ≤ Sz(2^(2n+1))` fixes only the base point of the Bender
action. -/
theorem szTwoGroupS_fixedPoint_eq_one (n : ℕ) (hn : 1 ≤ n)
    (u : ↥(Submission.Sz.szTwoGroupS n)) (hu : u ≠ 1)
    {x : SzModel n ⧸ Submission.Sz.szBorelS n} (hx : (u : SzModel n) • x = x) :
    x = ((1 : SzModel n) : SzModel n ⧸ Submission.Sz.szBorelS n) := by
  obtain ⟨-, -, heven, hinv⟩ := szModel_isBenderAction n hn
  have hUB : Submission.Sz.szTwoGroupS n ≤ Submission.Sz.szBorelS n :=
    Subgroup.subgroupOf_mono (SzModel n) (by rw [Submission.Sz.szBorel]; exact le_sup_left)
  have hu' : (u : SzModel n) ≠ 1 := fun h => hu (Subtype.ext h)
  refine Commons.GroupTheory.Bender.eq_of_smul_eq_self_of_mem_of_isPGroup_two heven hinv
    (Submission.Sz.szTwoGroupS_isPGroup n) ?_ u.2 hu' hx
  intro g
  have hmem : (g : SzModel n) ∈ Submission.Sz.szBorelS n := hUB g.2
  rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
  exact hmem

/-- A non-trivial element of the image `U` of the unipotent radical fixes only the base point of
the Bender action of `PSU(3,2ⁿ)`. -/
theorem psu3U_fixedPoint_eq_one (n : ℕ) (hn : 2 ≤ n)
    (u : ↥(Submission.PSU3.psu3U n)) (hu : u ≠ 1)
    {x : PSU3Model n ⧸ Submission.PSU3.psu3B n} (hx : (u : PSU3Model n) • x = x) :
    x = ((1 : PSU3Model n) : PSU3Model n ⧸ Submission.PSU3.psu3B n) := by
  have hn1 : 1 ≤ n := by omega
  have hM : IsStronglyEmbedded (Submission.PSU3.psu3B n) :=
    Submission.PSU3.psu3B_stronglyEmbedded n hn
  obtain ⟨-, -, heven, hinv⟩ :=
    Commons.GroupTheory.Bender.isBenderAction_coset (Submission.PSU3.psu3B n)
      hM.1 hM.2.1 hM.2.2
  have hu' : (u : PSU3Model n) ≠ 1 := fun h => hu (Subtype.ext h)
  refine Commons.GroupTheory.Bender.eq_of_smul_eq_self_of_mem_of_isPGroup_two heven hinv
    (Submission.PSU3.isPGroup_psu3U n hn1) ?_ u.2 hu' hx
  intro g
  have hmem : (g : PSU3Model n) ∈ Submission.PSU3.psu3B n :=
    Submission.PSU3.psu3U_le_psu3B n g.2
  rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
  exact hmem

/-- `PSL(2,2ⁿ)`: a non-trivial element of a Sylow `2`-subgroup contained in a point stabiliser
fixes only the base point of the Bender action. -/
theorem pSL2SylowTwo_fixedPoint_eq (n : ℕ) (hn : 2 ≤ n)
    (a : Projectivization (GaloisField 2 n) (Fin 2 → GaloisField 2 n))
    (S : Sylow 2 (PSL2Model n))
    (hS : (S : Subgroup (PSL2Model n)) ≤ MulAction.stabilizer (PSL2Model n) a)
    (u : ↥(S : Subgroup (PSL2Model n))) (hu : u ≠ 1)
    {x : PSL2Model n ⧸ MulAction.stabilizer (PSL2Model n) a}
    (hx : (u : PSL2Model n) • x = x) :
    x = ((1 : PSL2Model n) : PSL2Model n ⧸ MulAction.stabilizer (PSL2Model n) a) := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP (GaloisField 2 n) 2 := inferInstance
  have hcard : 2 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card (p := 2) (n := n) (by omega)]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hne, heven, hodd⟩ :=
    Commons.GroupTheory.SL2.stronglyEmbedded_stabilizer_projectiveSpecialLinearGroup
      hchar hcard a
  obtain ⟨-, -, hEvenG, hinv⟩ :=
    Commons.GroupTheory.Bender.isBenderAction_coset (MulAction.stabilizer (PSL2Model n) a)
      hne heven hodd
  have hu' : (u : PSL2Model n) ≠ 1 := fun h => hu (Subtype.ext h)
  refine Commons.GroupTheory.Bender.eq_of_smul_eq_self_of_mem_of_isPGroup_two
    (P := (S : Subgroup (PSL2Model n))) hEvenG hinv S.isPGroup' ?_ u.2 hu' hx
  intro g
  rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
  exact hS g.2

end Submission
