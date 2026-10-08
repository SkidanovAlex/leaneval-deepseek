/-
**The strongly embedded subgroups of `PSL(2, 2ⁿ)` are the normalizers of Sylow `2`-subgroups.**

The stabilizer of a point of the projective line is a maximal subgroup of `PSL(2,2ⁿ)`
(`Commons.GroupTheory.SL2.isCoatom_stabilizer_projectiveSpecialLinearGroup`) and it is the
normalizer of the unipotent subgroup `U` (`PSL2Stabilizer_eq_normalizer_unipotent`).  Since `U` is
a Sylow `2`-subgroup, and Sylow `2`-subgroups are conjugate, the normalizer of an arbitrary Sylow
`2`-subgroup is a conjugate of a point stabilizer, hence maximal.  The general theorem
`Submission.exists_sylow_normalizer_eq_of_isStronglyEmbedded` then shows that every strongly
embedded subgroup of `PSL(2,2ⁿ)` is the normalizer of a Sylow `2`-subgroup.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.ModelStructure
import Submission.Work.Models.Port.SylowNormalizer
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.isCoatom_map_mulAut_conj
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.isCoatom_stabilizer_projectiveSpecialLinearGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise LinearAlgebra.Projectivization

namespace Submission.PSL2

open Commons.GroupTheory.SL2

/-- The image of the unipotent subgroup of `SL(2,2ⁿ)` in `PSL(2,2ⁿ)`, chosen as a Sylow
`2`-subgroup. -/
noncomputable def pSL2Sylow (n : ℕ) (hn : 1 ≤ n) : Sylow 2 (PSL2Model n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hchar : CharP (GaloisField 2 n) 2 := inferInstance
  have hinj := Commons.GroupTheory.SL2.unipotentPSLHom_injective (K := GaloisField 2 n) hchar
  have hcardU : Nat.card ↥((unipotentPSLHom (GaloisField 2 n)).range) =
      Nat.card (GaloisField 2 n) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      ← Nat.card_congr Multiplicative.ofAdd]
  have hcardK : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card (p := 2) (n := n) (by omega)
  have hq : 0 < Nat.card (GaloisField 2 n) := Nat.card_pos
  refine IsPGroup.toSylow (p := 2)
    (IsPGroup.of_card (show Nat.card ↥((unipotentPSLHom (GaloisField 2 n)).range) = 2 ^ n by
      rw [hcardU, hcardK])) ?_
  have h1 := Subgroup.card_mul_index ((unipotentPSLHom (GaloisField 2 n)).range)
  rw [hcardU, Commons.GroupTheory.SL2.card_projectiveSpecialLinearGroup hchar] at h1
  have hidx : ((unipotentPSLHom (GaloisField 2 n)).range).index =
      Nat.card (GaloisField 2 n) ^ 2 - 1 := by
    refine Nat.mul_left_cancel hq ?_
    exact h1
  rw [hidx, hcardK, ← pow_mul, show n * 2 = 2 * n from by ring]
  exact (Commons.Nat.odd_two_pow_sub_one (2 * n) (by omega)).not_two_dvd_nat

/-- Every normalizer of a Sylow `2`-subgroup of `PSL(2,2ⁿ)` is a conjugate of a point
stabilizer, hence a maximal subgroup. -/
theorem pSL2Sylow_normalizer_isCoatom (n : ℕ) (hn : 2 ≤ n) (T : Sylow 2 (PSL2Model n)) :
    IsCoatom (Subgroup.normalizer (((T : Subgroup (PSL2Model n)) : Set (PSL2Model n)))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : MulAction.IsPretransitive (PSL2Model n) (Sylow 2 (PSL2Model n)) :=
    Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := PSL2Model n)
    (pSL2Sylow n (by omega)) T
  have hcoe : (T : Subgroup (PSL2Model n)) =
      (unipotentPSLHom (GaloisField 2 n)).range.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def]
    rfl
  rw [hcoe, Submission.normalizer_map_mulAut_conj,
    pSL2Stabilizer_eq_normalizer_unipotent n hn]
  exact Commons.GroupTheory.Subgroup.isCoatom_map_mulAut_conj
    (Commons.GroupTheory.SL2.isCoatom_stabilizer_projectiveSpecialLinearGroup
      (pt0 (GaloisField 2 n))) g

/-- **A strongly embedded subgroup of `PSL(2,2ⁿ)` is the normalizer of a Sylow
`2`-subgroup.** -/
theorem pSL2StronglyEmbedded_eq_sylow_normalizer (n : ℕ) (hn : 2 ≤ n)
    (M : Subgroup (PSL2Model n)) (hM : IsStronglyEmbedded M) :
    ∃ T : Sylow 2 (PSL2Model n),
      M = Subgroup.normalizer (((T : Subgroup (PSL2Model n)) : Set (PSL2Model n))) :=
  Submission.exists_sylow_normalizer_eq_of_isStronglyEmbedded M hM.1 hM.2.1 hM.2.2
    (fun T => pSL2Sylow_normalizer_isCoatom n hn T)

end Submission.PSL2
