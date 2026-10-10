import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Submission.Work.CohomologicalShrinking.Functorial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.functorial

open Work.CohomologicalShrinking

/-! ## Compatibility of the induced graded maps with composition

For surjective group homomorphisms `φ : P →* Q` and `ψ : Q →* R` the induced maps on the
graded pieces of the refined `p`-central filtration are compatible with composition, in each
of the three incarnations of the induced map (`refinedMap`, `gradedMapMul`, `gradedMapAdd`,
`gradedMapLin`).  These are the structure maps of the functor that Schmidt–Wingberg's
Proposition 5 makes natural in the operator group; the linear statement
`gradedMapLin_comp` is the one used downstream.
-/

/-- Composition compatibility of the induced maps `refinedTerm p P i j →* refinedTerm p Q i j`. -/
theorem refinedMap_comp (p : ℕ) {P Q R : Type*} [Group P] [Group Q] [Group R]
    (φ : P →* Q) (hφ : Function.Surjective φ)
    (ψ : Q →* R) (hψ : Function.Surjective ψ) (i j : ℕ) :
    (refinedMap p ψ hψ i j).comp (refinedMap p φ hφ i j)
      = refinedMap p (ψ.comp φ) (hψ.comp hφ) i j := by
  ext x
  simp [refinedMap_coe]

/-- Composition compatibility of the induced maps `gradedMapMul` on the graded pieces. -/
theorem gradedMapMul_comp (p : ℕ) {P Q R : Type*} [Group P] [Group Q] [Group R]
    (φ : P →* Q) (hφ : Function.Surjective φ)
    (ψ : Q →* R) (hψ : Function.Surjective ψ) (i j : ℕ) :
    gradedMapMul p (ψ.comp φ) (hψ.comp hφ) i j
      = (gradedMapMul p ψ hψ i j).comp (gradedMapMul p φ hφ i j) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((refinedTerm p P (tauSucc i j).1 (tauSucc i j).2).subgroupOf (refinedTerm p P i j)) x
  rw [gradedMapMul_of, MonoidHom.comp_apply, gradedMapMul_of, gradedMapMul_of]
  congr 1

/-- Composition compatibility of the induced maps `gradedMapAdd` on the graded pieces. -/
theorem gradedMapAdd_comp (p : ℕ) {P Q R : Type*} [Group P] [Group Q] [Group R]
    (φ : P →* Q) (hφ : Function.Surjective φ)
    (ψ : Q →* R) (hψ : Function.Surjective ψ) (i j : ℕ) :
    gradedMapAdd p (ψ.comp φ) (hψ.comp hφ) i j
      = (gradedMapAdd p ψ hψ i j).comp (gradedMapAdd p φ hφ i j) := by
  apply AddMonoidHom.ext
  intro z
  show Additive.ofMul (gradedMapMul p (ψ.comp φ) (hψ.comp hφ) i j (Additive.toMul z))
      = Additive.ofMul (gradedMapMul p ψ hψ i j
          (gradedMapMul p φ hφ i j (Additive.toMul z)))
  rw [gradedMapMul_comp, MonoidHom.comp_apply]

/-- Composition compatibility of the `𝔽_p`-linear maps `gradedMapLin` on the graded pieces. -/
theorem gradedMapLin_comp (p : ℕ) {P Q R : Type*} [Group P] [Group Q] [Group R]
    (φ : P →* Q) (hφ : Function.Surjective φ)
    (ψ : Q →* R) (hψ : Function.Surjective ψ) (i j : ℕ) :
    Work.CohomologicalShrinking.gradedMapLin p (ψ.comp φ) (hψ.comp hφ) i j
      = (Work.CohomologicalShrinking.gradedMapLin p ψ hψ i j).comp
          (Work.CohomologicalShrinking.gradedMapLin p φ hφ i j) := by
  apply LinearMap.ext
  intro z
  show gradedMapAdd p (ψ.comp φ) (hψ.comp hφ) i j z
      = gradedMapAdd p ψ hψ i j (gradedMapAdd p φ hφ i j z)
  rw [gradedMapAdd_comp, AddMonoidHom.comp_apply]

end Work.CohomologicalShrinking.functorial
