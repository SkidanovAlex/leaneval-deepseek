import Mathlib
import Submission.Work.TangentClasses.Bundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

/-!
# Auxiliary facts about complex vector bundles in the gluing model

* the real dimension of `ℂ^m` is `2m` (`Work.Thom.finrank_real_euclidean_complex`);
* the transition function `coordChange i j x` of a complex gluing datum is bijective on
  `baseSet i ∩ baseSet j` (`Work.Thom.coordChange_bijective`), from the cocycle condition.

These are used by `Work.Thom.isOrientedOver_of_complex` (and its contractible-overlap variant).
-/

open Work.TangentClasses

namespace Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-- The real dimension of `ℂ^m` is `2m`. -/
theorem finrank_real_euclidean_complex (m : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin m)) = 2 * m := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin m)),
    Complex.finrank_real_complex, finrank_euclideanSpace]
  simp

/-- **The `ℂ`-linear gauge is bijective**, from the cocycle condition of the gluing data. -/
theorem coordChange_bijective {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i j : ι) {x : B} (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) :
    Function.Bijective (Z.coordChange i j x).toLinearMap := by
  have hxi : x ∈ Z.baseSet i := hx.1
  have hmem : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ Z.baseSet i := ⟨hx, hxi⟩
  have hmem' : x ∈ Z.baseSet j ∩ Z.baseSet i ∩ Z.baseSet j := ⟨⟨hx.2, hx.1⟩, hx.2⟩
  have h1 : ∀ v, (Z.coordChange j i x) ((Z.coordChange i j x) v) = v := fun v => by
    rw [VectorBundleCore.coordChange_comp Z i j i x hmem v,
      VectorBundleCore.coordChange_self Z i x hxi v]
  have h2 : ∀ v, (Z.coordChange i j x) ((Z.coordChange j i x) v) = v := fun v => by
    rw [VectorBundleCore.coordChange_comp Z j i j x hmem' v,
      VectorBundleCore.coordChange_self Z j x hx.2 v]
  have hbij : Function.Bijective (Z.coordChange i j x) :=
    ⟨fun u v huv => by
       have h := h1 u
       rw [huv] at h
       exact h.symm.trans (h1 v),
     fun w => ⟨(Z.coordChange j i x) w, h2 w⟩⟩
  simpa using hbij

end

end Work.Thom
