/-
**Completing the Suzuki set-up for the three families.**

In a rank-`1` BN-pair of characteristic two with Borel `B = U ⋊ T` the Suzuki `2`-group `U`
acts *regularly* on the non-base points of the coset space `G ⧸ B`; equivalently `B` is a
Frobenius group with kernel `U`.  The abstract form of this statement is
`Commons.GroupTheory.GroupAction.exists_smul_eq_of_ne_of_card_eq_one_add`, and here we verify
for all three families of the Bender–Suzuki classification that it applies:

* `PSL(2, 2ⁿ)`: `Sylow 2`-subgroups of `PSL(2,2ⁿ)` have order `2ⁿ` (`card_sylow_two_PSL2Model`)
  and act regularly on the projective line minus a point,
* `PSU(3, 2ⁿ)`: the image `Ū ≤ PSU(3,2ⁿ)` of the unipotent radical has the same order as the
  unipotent radical (`card_psu3U`) and acts regularly on the Bender action off the base point.

Together with `Submission/Sz/SuzukiCondition.lean` (where the same is proved for
`Sz(2^(2n+1))`) this completes the verification of the Suzuki/Frobenius structure for all
three families.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSL2Model
import Submission.Work.Models.Port.BenderAction
import Submission.Work.Models.Port.PSU3.SuzukiCondition
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.card_map_mul_card_inf_ker
import Submission.Work.Models.Port.Commons.GroupTheory.IsPGroup.inf_eq_bot_of_not_dvd_card
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.exists_smul_eq_of_ne_of_card_eq_one_add

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs
open scoped Pointwise LinearAlgebra.Projectivization

namespace Submission

/-! ## `PSL(2, 2ⁿ)` -/

/-- Every Sylow `2`-subgroup of `PSL(2, 2ⁿ)` has order `2ⁿ`. -/
theorem card_sylow_two_PSL2Model (n : ℕ) (hn : n ≠ 0) (S : Sylow 2 (PSL2Model n)) :
    Nat.card ↥(S : Subgroup (PSL2Model n)) = 2 ^ n := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  obtain ⟨S₀, hcard₀, -⟩ := PSL2Model_exists_sylow_two_elementaryAbelian n hn
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := PSL2Model n) S₀ S
  have hcoe : (S : Subgroup (PSL2Model n)) =
      (S₀ : Subgroup (PSL2Model n)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def]; rfl
  rw [hcoe, Subgroup.card_map_of_injective (MulEquiv.injective _), hcard₀]

/-- The Sylow `2`-subgroup of `PSL(2,2ⁿ)` inside a point stabilizer acts regularly on the
projective line with the base point removed (Frobenius structure of the Borel subgroup). -/
theorem pSL2_exists_smul_eq_of_ne (n : ℕ) (hn : 2 ≤ n)
    (a : Projectivization (GaloisField 2 n) (Fin 2 → GaloisField 2 n))
    (S : Sylow 2 (PSL2Model n))
    (hS : (S : Subgroup (PSL2Model n)) ≤ MulAction.stabilizer (PSL2Model n) a)
    {x y : PSL2Model n ⧸ MulAction.stabilizer (PSL2Model n) a}
    (hx : x ≠ ((1 : PSL2Model n) : PSL2Model n ⧸ MulAction.stabilizer (PSL2Model n) a))
    (hy : y ≠ ((1 : PSL2Model n) : PSL2Model n ⧸ MulAction.stabilizer (PSL2Model n) a)) :
    ∃ u : ↥(S : Subgroup (PSL2Model n)), (u : PSL2Model n) • x = y := by
  refine Commons.GroupTheory.GroupAction.exists_smul_eq_of_ne_of_card_eq_one_add
    (U := (S : Subgroup (PSL2Model n)))
    (((1 : PSL2Model n) : PSL2Model n ⧸ MulAction.stabilizer (PSL2Model n) a)) ?_ ?_ ?_ hx hy
  · show (MulAction.stabilizer (PSL2Model n) a).index = Nat.card ↥(S : Subgroup (PSL2Model n)) + 1
    rw [pSL2Stabilizer_index_eq_one_add_sylowTwo n (by omega) a,
      card_sylow_two_PSL2Model n (by omega) S, Nat.add_comm]
  · intro u
    rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
    exact hS u.2
  · intro u hu x hx
    exact pSL2SylowTwo_fixedPoint_eq n hn a S hS u hu hx

/-! ## `PSU(3, 2ⁿ)` -/

/-- The image `Ū` of the unipotent radical in `PSU(3,2ⁿ)` has the same order as the unipotent
radical itself: the projection `SU(3,2ⁿ) → PSU(3,2ⁿ)` is injective on a `2`-group (its kernel
has odd order). -/
theorem card_psu3U (n : ℕ) (hn : 2 ≤ n) :
    Nat.card ↥(Submission.PSU3.psu3U n) = Nat.card ↥(Submission.PSU3.suUS n) := by
  have hn1 : 1 ≤ n := by omega
  have hbot : Submission.PSU3.suUS n ⊓ (Submission.PSU3.psu3Hom n).ker = ⊥ :=
    Commons.GroupTheory.IsPGroup.inf_eq_bot_of_not_dvd_card (p := 2)
      (Submission.PSU3.suUS_isPGroup n hn1)
      (by
        intro h
        exact Nat.not_even_iff_odd.mpr (Submission.PSU3.odd_card_psu3Hom_ker n hn1)
          (even_iff_two_dvd.mpr h))
  have h := Commons.GroupTheory.Subgroup.card_map_mul_card_inf_ker (Submission.PSU3.psu3Hom n)
    (Submission.PSU3.psu3Hom_surjective n) (Submission.PSU3.suUS n)
  rw [hbot, Subgroup.card_bot, mul_one] at h
  show Nat.card ↥(Subgroup.map (Submission.PSU3.psu3Hom n) (Submission.PSU3.suUS n)) =
    Nat.card ↥(Submission.PSU3.suUS n)
  exact h

/-- **The Suzuki condition for `PSU(3,2ⁿ)`**: the degree `q³ + 1` of the Bender action is one
more than the order of the image of the unipotent radical. -/
theorem psu3B_index_eq_one_add_card_psu3U (n : ℕ) (hn : 2 ≤ n) :
    (Submission.PSU3.psu3B n).index = 1 + Nat.card ↥(Submission.PSU3.psu3U n) := by
  have hn1 : 1 ≤ n := by omega
  have hidx : (Submission.PSU3.psu3B n).index = (Submission.PSU3.suBS n).index :=
    (Submission.PSU3.suBS n).index_map_eq (Submission.PSU3.psu3Hom_surjective n)
      (Submission.PSU3.psu3Hom_ker_le_borel n)
  rw [hidx, Submission.PSU3.suBS_index_eq_one_add n hn1, card_psu3U n hn]

/-- The image of the unipotent radical acts regularly on the Bender action of `PSU(3,2ⁿ)` off
the base point. -/
theorem psu3U_exists_smul_eq_of_ne (n : ℕ) (hn : 2 ≤ n)
    {x y : PSU3Model n ⧸ Submission.PSU3.psu3B n}
    (hx : x ≠ ((1 : PSU3Model n) : PSU3Model n ⧸ Submission.PSU3.psu3B n))
    (hy : y ≠ ((1 : PSU3Model n) : PSU3Model n ⧸ Submission.PSU3.psu3B n)) :
    ∃ u : ↥(Submission.PSU3.psu3U n), (u : PSU3Model n) • x = y := by
  refine Commons.GroupTheory.GroupAction.exists_smul_eq_of_ne_of_card_eq_one_add
    (U := Submission.PSU3.psu3U n)
    (((1 : PSU3Model n) : PSU3Model n ⧸ Submission.PSU3.psu3B n)) ?_ ?_ ?_ hx hy
  · show (Submission.PSU3.psu3B n).index = Nat.card ↥(Submission.PSU3.psu3U n) + 1
    rw [psu3B_index_eq_one_add_card_psu3U n hn, Nat.add_comm]
  · intro u
    rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
    exact Submission.PSU3.psu3U_le_psu3B n u.2
  · intro u hu x hx
    exact Submission.psu3U_fixedPoint_eq_one n hn u hu hx

end Submission
