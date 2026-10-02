import Mathlib
import Submission.Work.Projective.CP2Concrete
import Submission.Work.Projective.CP2Duality
import Submission.Work.Projective.cp2_homology_free

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `h ⌣ h` generates `H⁴(ℂP²;ℤ)`, from the value `⟨h ⌣ h, [ℂP²]⟩ = ±1`

This is the `H⁴`-counterpart of `Work.Projective.cp2SelfIntersection_eq_pm_one_of_cupH`, and the
direct companion of `Work.Projective.cp2H_cup_generates_of_good`: instead of deriving the value
`cp2SelfIntersection = ±1` from Poincaré duality (`Good 4 cp2C Set.univ`), we take it as the
hypothesis and conclude the ring statement.

The point that makes this unconditional is `Work.Projective.cp2EvalMap_bijective`: the pairing
with the fundamental class `y ↦ ⟨y, [ℂP²]⟩ : H⁴(ℂP²;ℤ) → ℤ` is a bijection, because `cp2C`
generates `H₄(ℂP²;ℤ)` (`cp2C_span`) and the Kronecker pairing `kronH 4 : H⁴ → (H₄ →ₗ ℤ)` is
bijective (`cfkronH_four_cp2_bijective`, from the freeness of the homology of `ℂP²`).  Since
`cp2EvalMap (h ⌣ h) = ⟨h ⌣ h, [ℂP²]⟩ = cp2SelfIntersection` is `±1`, and `±1` generates `ℤ`, the
class `h ⌣ h` is the image of a generator under the inverse bijection, hence generates
`H⁴(ℂP²;ℤ) ≅ ℤ`.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Projective

open CategoryTheory Limits Work.Cohomology Work.SignatureBordism

noncomputable section

theorem cp2H_cup_generates
    (h : Work.Projective.cp2SelfIntersection = 1 ∨ Work.Projective.cp2SelfIntersection = -1) :
    Submodule.span ℤ {(Work.Cohomology.cupH' ℤ Work.Projective.cp2SSet 2 2
      Work.Projective.cp2H Work.Projective.cp2H)} = ⊤ := by
  -- `1` generates `ℤ`.
  have hsp : Submodule.span ℤ {(1 : ℤ)} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro z
    rw [show z = z • (1 : ℤ) from (mul_one z).symm]
    exact Submodule.smul_mem _ z (Submodule.subset_span (Set.mem_singleton 1))
  -- The pairing with the fundamental class is an isomorphism `H⁴(ℂP²;ℤ) ≅ ℤ`.
  set e : (cochainC ℤ cp2SSet).homology 4 ≃ₗ[ℤ] ℤ :=
    LinearEquiv.ofBijective cp2EvalMap cp2EvalMap_bijective with he
  -- Its inverse carries `1` to a generator, and `-1` to a generator.
  have hgen : Submodule.span ℤ {e.symm (1 : ℤ)} = ⊤ :=
    span_singleton_map_eq_top' (e.symm : ℤ →ₗ[ℤ] (cochainC ℤ cp2SSet).homology 4)
      e.symm.surjective 1 hsp
  have hneg : Submodule.span ℤ {-(e.symm (1 : ℤ))} = ⊤ := by
    rw [span_singleton_eq_top_iff'] at hgen ⊢
    intro z
    obtain ⟨a, ha⟩ := hgen z
    exact ⟨-a, by rw [ha]; simp⟩
  -- `⟨h ⌣ h, [ℂP²]⟩ = cp2SelfIntersection = ±1`.
  have hm : cp2EvalMap (cupH' ℤ cp2SSet 2 2 cp2H cp2H) = 1 ∨
      cp2EvalMap (cupH' ℤ cp2SSet 2 2 cp2H cp2H) = -1 := by
    have hval : cp2EvalMap (cupH' ℤ cp2SSet 2 2 cp2H cp2H) = cp2SelfIntersection :=
      h4_cup_self_eq_selfIntersection
    rw [hval]; exact h
  rcases hm with hm | hm
  · have hx : cupH' ℤ cp2SSet 2 2 cp2H cp2H = e.symm 1 := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact hm
    rw [hx]; exact hgen
  · have hx : cupH' ℤ cp2SSet 2 2 cp2H cp2H = -(e.symm 1) := by
      apply e.injective
      rw [map_neg, e.apply_symm_apply]
      exact hm
    rw [hx]; exact hneg

end

end Work.Projective
