import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.geomFiniteDefs

/-!
# Vocabulary shared by the `Work.Mostow.cuspCorr` development

`cuspStab Γ ξ` is the stabiliser of the boundary point `ξ` in `Γ`.  The cusp correspondence
theorem `Work.Mostow.cuspCorr` produces an `f`-equivariant bijection between the parabolic fixed
point sets `parFixSet Γ` and `parFixSet Λ` of two lattices, and this module provides the
definitions (and the elementary lemmas about them) that the chapters of that proof share.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-- The stabiliser in `Γ` of a boundary point `ξ ∈ Sph n`. -/
def cuspStab (hA : POBasic n) (Γ : Subgroup (PO n 1)) (ξ : E n) (hξ : ξ ∈ Sph n) : Subgroup Γ where
  carrier := {γ | bd (γ : PO n 1) ξ = ξ}
  mul_mem' := by
    intro a b ha hb
    show bd ((a : PO n 1) * (b : PO n 1)) ξ = ξ
    rw [hA.bd_mul (a : PO n 1) (b : PO n 1) ξ hξ, hb, ha]
  one_mem' := hA.bd_one ξ hξ
  inv_mem' := by
    intro a ha
    have h1 : bd (((a⁻¹ : Γ) : PO n 1) * ((a : Γ) : PO n 1)) ξ = ξ := by
      rw [show ((a⁻¹ : Γ) : PO n 1) * ((a : Γ) : PO n 1) = 1 from by
            simpa using inv_mul_cancel a, hA.bd_one ξ hξ]
    rw [hA.bd_mul ((a⁻¹ : Γ) : PO n 1) ((a : Γ) : PO n 1) ξ hξ, ha] at h1
    exact h1

lemma mem_cuspStab {hA : POBasic n} {Γ : Subgroup (PO n 1)} {ξ : E n} {hξ : ξ ∈ Sph n} (γ : Γ) :
    γ ∈ cuspStab hA Γ ξ hξ ↔ bd (γ : PO n 1) ξ = ξ := Iff.rfl

/-- `parFixSet Γ` is invariant under `Γ`. -/
theorem parFixSet_smul_mem (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} {γ : Γ} {ξ : E n} (hξ : ξ ∈ parFixSet Γ) :
    bd (γ : PO n 1) ξ ∈ parFixSet Γ := by
  obtain ⟨hξS, δ, hδpar, hδfix⟩ := hξ
  refine ⟨hA.2.2.2.2.2.2.2.1 (γ : PO n 1) ξ hξS, ?_⟩
  refine ⟨⟨(γ : PO n 1) * (δ : PO n 1) * (γ : PO n 1)⁻¹, ?_⟩, ?_, ?_⟩
  · exact mul_mem (mul_mem γ.2 δ.2) (inv_mem γ.2)
  · exact isParabolic_conj hA hI (γ : PO n 1) (δ : PO n 1) hδpar
  · rw [show (((⟨(γ : PO n 1) * (δ : PO n 1) * (γ : PO n 1)⁻¹, _⟩ : Γ) : PO n 1))
        = (γ : PO n 1) * (δ : PO n 1) * (γ : PO n 1)⁻¹ from rfl]
    rw [hA.2.2.2.2.2.2.2.2.2.1 ((γ : PO n 1) * (δ : PO n 1)) ((γ : PO n 1)⁻¹)
          (bd (γ : PO n 1) ξ)
          (hA.2.2.2.2.2.2.2.1 (γ : PO n 1) ξ hξS)]
    have h2 : bd ((γ : PO n 1)⁻¹ * (γ : PO n 1)) ξ = ξ := by
      rw [inv_mul_cancel, hA.2.2.2.2.2.2.2.2.1 ξ hξS]
    rw [hA.2.2.2.2.2.2.2.2.2.1 ((γ : PO n 1)⁻¹) ((γ : PO n 1)) ξ hξS] at h2
    rw [h2, hA.2.2.2.2.2.2.2.2.2.1 (γ : PO n 1) (δ : PO n 1) ξ hξS, hδfix]

end Work.Mostow
