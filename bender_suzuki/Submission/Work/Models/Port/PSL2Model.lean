/-
Verification of the `PSL(2, 2ⁿ)` family of the Bender–Suzuki classification.

`PSL2Model n` is `PSL(2, GF(2ⁿ))`.  We record that, for `n ≥ 2`,

* `PSL2Model n` is simple,
* `PSL2Model n` has a strongly embedded subgroup (the stabilizer of a point of the
  projective line, i.e. a Borel subgroup), and consequently
* `PSL2Model n` satisfies the conclusion `IsSimpleBenderGroup` of the challenge theorem.

The mathematical content lives in the shared commons: simplicity is
`Commons.GroupTheory.SL2.isSimpleGroup_projectiveSpecialLinearGroup` (Iwasawa's criterion)
and strong embeddedness is
`Commons.GroupTheory.SL2.stronglyEmbedded_stabilizer_projectiveSpecialLinearGroup`.
-/
import ChallengeDeps
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.stronglyEmbedded_stabilizer_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.isSimpleGroup_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.exists_sylow_two_elementaryAbelian_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.existsUnique_fixedPoint_involution_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.card_sylow_two_projectiveSpecialLinearGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs

namespace Submission

/-- `PSL(2, 2ⁿ)` is simple for `n ≥ 2`. -/
theorem PSL2Model_isSimpleGroup (n : ℕ) (hn : 2 ≤ n) : IsSimpleGroup (PSL2Model n) := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : 4 ≤ Nat.card (GaloisField 2 n) := by
    have hc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card (p := 2) (n := n) (by omega)
    rw [hc]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact Commons.GroupTheory.SL2.isSimpleGroup_projectiveSpecialLinearGroup hcard

/-- `PSL(2, 2ⁿ)` (`n ≥ 2`) has a strongly embedded subgroup. -/
theorem PSL2Model_exists_isStronglyEmbedded (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : Subgroup (PSL2Model n), IsStronglyEmbedded M := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hchar : CharP (GaloisField 2 n) 2 := inferInstance
  have hcard : 2 ≤ Nat.card (GaloisField 2 n) := by
    have hc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card (p := 2) (n := n) (by omega)
    rw [hc]
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨a⟩ : Nonempty (Projectivization (GaloisField 2 n) (Fin 2 → GaloisField 2 n)) :=
    inferInstance
  exact ⟨MulAction.stabilizer (PSL2Model n) a,
    Commons.GroupTheory.SL2.stronglyEmbedded_stabilizer_projectiveSpecialLinearGroup
      hchar hcard a⟩

/-- The Sylow `2`-subgroups of `PSL(2, 2ⁿ)` are elementary abelian of order `2ⁿ`. -/
theorem PSL2Model_exists_sylow_two_elementaryAbelian (n : ℕ) (hn : n ≠ 0) :
    ∃ S : Sylow 2 (PSL2Model n),
      Nat.card ↥(S : Subgroup (PSL2Model n)) = 2 ^ n ∧
        ∀ x : ↥(S : Subgroup (PSL2Model n)), x ^ 2 = 1 := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hchar : CharP (GaloisField 2 n) 2 := inferInstance
  obtain ⟨S, hS⟩ :=
    Commons.GroupTheory.SL2.exists_sylow_two_elementaryAbelian_projectiveSpecialLinearGroup
      (K := GaloisField 2 n) hchar
  exact ⟨S, hS.1.trans (GaloisField.card (p := 2) (n := n) (by omega)), hS.2⟩

/-- `PSL(2, 2ⁿ)` has exactly `2ⁿ + 1` Sylow `2`-subgroups, one for each point of the
projective line. -/
theorem PSL2Model_card_sylow_two (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Sylow 2 (PSL2Model n)) = 2 ^ n + 1 := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hchar : CharP (GaloisField 2 n) 2 := inferInstance
  rw [Commons.GroupTheory.SL2.card_sylow_two_projectiveSpecialLinearGroup (K := GaloisField 2 n) hchar,
    GaloisField.card (p := 2) (n := n) (by omega)]

/-- In its action on the projective line, every involution of `PSL(2, 2ⁿ)` fixes exactly one
point (the "Bender action" property). -/
theorem PSL2Model_existsUnique_fixedPoint_involution (n : ℕ)
    (a : Projectivization (GaloisField 2 n) (Fin 2 → GaloisField 2 n)) :
    ∀ t : PSL2Model n, orderOf t = 2 →
      ∃! x : Projectivization (GaloisField 2 n) (Fin 2 → GaloisField 2 n), t • x = x := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hchar : CharP (GaloisField 2 n) 2 := inferInstance
  exact Commons.GroupTheory.SL2.existsUnique_fixedPoint_involution_projectiveSpecialLinearGroup
    (K := GaloisField 2 n) hchar a

/-- `PSL(2, 2ⁿ)` satisfies the conclusion of the Bender–Suzuki classification: it is one of
the three families, namely the `PSL(2, q)` family. -/
theorem PSL2Model_isSimpleBenderGroup (n : ℕ) (hn : 2 ≤ n) :
    IsSimpleBenderGroup (PSL2Model n) :=
  IsSimpleBenderGroup.isPSL2 n hn (MulEquiv.refl _)

end Submission
