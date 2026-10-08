import Mathlib
import Submission.Work.Frobenius.Fpf.Basic
import Submission.Work.Fitting.fitting_ne_bot
import Submission.Work.Fitting.fitting_eq_iSup_pCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A nontrivial characteristic abelian `p`-subgroup of a finite solvable group

Every finite nontrivial solvable group `K` possesses a nontrivial characteristic subgroup `N`
which is abelian and a `p`-group for some prime `p`.

The construction is the classical one: the Fitting subgroup `F(K)` is nontrivial
(`Work.Fitting.fitting_ne_bot`) and is the product of the `p`-cores
(`Work.Fitting.fitting_eq_iSup_pCore`), so some `p`-core `O_p(K)` is nontrivial.  Being a
characteristic (`Work.Fitting.pCore_characteristic`) `p`-subgroup, its centre is again
characteristic, and it is nontrivial because a nontrivial finite `p`-group has nontrivial centre.
Identifying `Z(O_p(K))` with its image in `K` gives the required `N`.
-/

namespace Work.Frobenius.Fpf

/-- **A8b support.**  A finite nontrivial solvable group has a nontrivial characteristic
abelian `p`-subgroup. -/
theorem exists_characteristic_abelian_pGroup {K : Type*} [Group K] [Finite K] [Nontrivial K] [Group.IsSolvable K] : ∃ (p : ℕ) (N : Subgroup K), p.Prime ∧ N.Characteristic ∧ N ≠ ⊥ ∧ IsMulCommutative ↥N ∧ IsPGroup p ↥N := by
  -- The Fitting subgroup is nontrivial, and it is the supremum of the `p`-cores.
  have hfit : Work.Fitting.fitting K ≠ ⊥ := Work.Fitting.fitting_ne_bot K
  rw [Work.Fitting.fitting_eq_iSup_pCore] at hfit
  -- Hence some `p`-core `O_p(K)` is nontrivial.
  have hex : ∃ p ∈ (Nat.card K).primeFactors, Work.Fitting.pCore p K ≠ ⊥ := by
    by_contra h
    push Not at h
    exact hfit (le_bot_iff.mp (iSup_le fun q => iSup_le fun hq => by rw [h q hq]))
  obtain ⟨p, hp_mem, hp_ne⟩ := hex
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  haveI : Fact p.Prime := ⟨hp⟩
  -- `O_p(K)` is a nontrivial finite `p`-group, characteristic in `K`.
  have hPp : IsPGroup p ↥(Work.Fitting.pCore p K) := Work.Fitting.isPGroup_pCore hp
  haveI : Nontrivial ↥(Work.Fitting.pCore p K) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hp_ne
  -- Its centre is nontrivial (nontrivial finite `p`-group).
  have hcen : Nontrivial ↥(Subgroup.center ↥(Work.Fitting.pCore p K)) :=
    IsPGroup.center_nontrivial hPp
  refine ⟨p, (Subgroup.center ↥(Work.Fitting.pCore p K)).map (Work.Fitting.pCore p K).subtype,
    hp, ?_, ?_, ?_, ?_⟩
  · -- characteristic in `K`: the centre of the characteristic subgroup `O_p(K)`.
    infer_instance
  · -- nontrivial: the (injective) image of the nontrivial centre of `O_p(K)`.
    intro hbot
    have hc : Subgroup.center ↥(Work.Fitting.pCore p K) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hbot
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hcen hc
  · -- abelian: an image of the (abelian) centre.
    infer_instance
  · -- a `p`-group: a subgroup of the `p`-group `O_p(K)`.
    exact hPp.to_le (Subgroup.map_subtype_le _)

end Work.Frobenius.Fpf
