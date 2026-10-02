import Mathlib
import Submission.Work.Kunneth.cp2cp2Model
import Submission.Work.Gen.ChernGeneratorTwo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The hyperplane class of `ℂP²` in the two normalisations

`Work.Projective.cp2H` is the hyperplane class of `ℂP²` obtained from Mayer–Vietoris
(`Work.Projective.CP2Cohomology`), and `Work.Gen.uCoh 2 = c₁(O(1))` is the hyperplane class in the
projectivisation normalisation used by `Work.Gen` (the first Chern class of the dual tautological
line bundle).

Both generate `H²(ℂP²;ℤ) ≅ ℤ` (`Work.Projective.cp2H_span`, `Work.Gen.ChernGeneratorTwo`), so they
differ by a *unit* of `ℤ`, i.e. by a sign:

`Work.Kunneth.uCoh_two_eq_pm_cp2H : uCoh 2 = cp2H ∨ uCoh 2 = -cp2H`.

The sign is invisible in the Künneth-ring model of `ℂP² × ℂP²`, where it enters the nine
intersection numbers of `a², ab, b²` to the fourth power.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [-instance] AddCommGroup.toIntModule

/-- A chosen linear equivalence `H²(ℂP²;ℤ) ≅ ℤ` (`Work.Projective.cpn_cohomology`). -/
noncomputable def cp2CohEquiv : ↥((cochainC ℤ cpX).homology 2) ≃ₗ[ℤ] ℤ :=
  ((Classical.choice (Work.Projective.cpn_cohomology 2 2 :
      Nonempty ((cochainC ℤ cpX).homology 2 ≅ Work.Projective.cpnModel 2 2))) ≪≫
    Classical.choice (Work.Projective.cpnModel_iso_int (⟨even_two, by norm_num⟩ :
      Even 2 ∧ 2 ≤ 2 * 2))).toLinearEquiv

/-- The image of a spanning element under a surjective linear map is a unit of `ℤ`. -/
private lemma isUnit_of_span_singleton_eq_top (f : ↥((cochainC ℤ cpX).homology 2) →ₗ[ℤ] ℤ)
    (hf : Function.Surjective f) (x : ↥((cochainC ℤ cpX).homology 2))
    (hx : Submodule.span ℤ ({x} : Set ↥((cochainC ℤ cpX).homology 2)) = ⊤) :
    IsUnit (f x) := by
  have hL : Submodule.span ℤ ({f x} : Set ℤ) = ⊤ := by
    have h := congrArg (Submodule.map f) hx
    rw [Submodule.map_top, Submodule.map_span] at h
    have h2 : Submodule.span ℤ ({f x} : Set ℤ) = f.range := by simpa using h
    rw [h2, LinearMap.range_eq_top.mpr hf]
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp
    (show (1 : ℤ) ∈ Submodule.span ℤ ({f x} : Set ℤ) by rw [hL]; trivial)
  have hk' : k * f x = 1 := by rw [← smul_eq_mul]; exact hk
  exact isUnit_iff_exists.mpr ⟨k, by rw [mul_comm]; exact hk', hk'⟩

/-- **The hyperplane class is the same in the two normalisations, up to sign.** -/
theorem uCoh_two_eq_pm_cp2H : Work.Gen.uCoh 2 = cpH ∨ Work.Gen.uCoh 2 = -cpH := by
  let L := cp2CohEquiv
  have hcpH : L cpH = 1 ∨ L cpH = -1 :=
    Int.isUnit_iff.mp (isUnit_of_span_singleton_eq_top L L.surjective cpH
      Work.Projective.cp2H_span)
  have hu : L (Work.Gen.uCoh 2) = 1 ∨ L (Work.Gen.uCoh 2) = -1 :=
    Int.isUnit_iff.mp (isUnit_of_span_singleton_eq_top L L.surjective (Work.Gen.uCoh 2)
      Work.Gen.ChernGeneratorTwo)
  rcases hcpH with h | h <;> rcases hu with h' | h'
  · left; exact L.injective (by rw [h, h'])
  · right; refine L.injective ?_; rw [map_neg, h, h']
  · right; refine L.injective ?_; rw [map_neg, h, h']; norm_num
  · left; exact L.injective (by rw [h, h'])

end

end Work.Kunneth
