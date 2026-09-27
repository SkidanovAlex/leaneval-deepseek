import Mathlib
import Submission.Work.Drive.BoxParityDefs
import Submission.Work.Drive.exists_uniform_local_integralCurve

/-!
# Global integral curves of a compactly supported smooth vector field

`Work.Drive.exists_global_integralCurve`: every smooth, compactly supported vector field
`w : ℝ^{m+1} → ℝ^{m+1}` has global integral curves, i.e. for every `x₀` there is `γ : ℝ → ℝ^{m+1}`
with `γ 0 = x₀` and `γ' t = w (γ t)` for all `t`.

The proof (carried out for a general complete real normed space `E`, and then specialised to
`Amb m = EuclideanSpace ℝ (Fin (m+1))`) combines three inputs.

* A smooth compactly supported field is globally Lipschitz
  (`ContDiff.lipschitzWith_of_hasCompactSupport`) and globally bounded
  (`HasCompactSupport.exists_bound_of_continuous`).
* Picard–Lindelöf with these two *global* constants gives a local solution of uniform radius
  `ε > 0` around *every* initial point (`Work.Drive.exists_uniform_local_integralCurve`).
* The uniform time lemma for the global existence of integral curves
  (`exists_isMIntegralCurve_of_isMIntegralCurveOn`) then turns uniform local existence into a global
  integral curve.  The flat ODE statement is transported into the manifold language of that lemma;
  on the model space `E` the manifold derivative `HasMFDerivAt` and the derivative `HasDerivAt`
  coincide (`hasMFDerivAt_iff_hasFDerivAt`), and a vector field on a vector space is `C¹` in the
  manifold sense iff it is `C¹` in the vector space sense
  (`contMDiff_vectorSpace_iff_contDiff`).
-/

namespace Work.Drive

open scoped ContDiff Manifold NNReal
open Set

noncomputable section

/-- **Global existence of integral curves**, in a general complete real normed space. -/
theorem exists_global_integralCurve_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {w : E → E} (hw : ContDiff ℝ 1 w) (hws : HasCompactSupport w) (x₀ : E) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (w (γ t)) t := by
  -- A `C¹` field with compact support is globally Lipschitz with some constant `K`...
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) hws hw one_ne_zero
  -- ... and globally bounded by some constant `C`.
  obtain ⟨C, hC⟩ := hws.exists_bound_of_continuous hw.continuous
  set C' : NNReal := ⟨max C 0, le_max_right _ _⟩ with hC'
  have hC'' : ∀ x : E, ‖w x‖ ≤ (C' : ℝ) := by
    intro x
    have h := hC x
    rw [hC']
    exact h.trans (le_max_left _ _)
  -- Picard–Lindelöf with these global constants gives a local solution of uniform radius `ε`.
  obtain ⟨ε, hε, hloc⟩ := exists_uniform_local_integralCurve hK hC''
  -- The field, as a section of the tangent bundle of the model space, is `C¹`.
  have hv : CMDiff 1 (fun x : E => (⟨x, w x⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    (contMDiff_vectorSpace_iff_contDiff (V := fun x : E => w x)).mpr hw
  -- Re-read the flat local solutions as manifold integral curves (the model space is the manifold).
  have hloc' : ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧
      IsMIntegralCurveOn (I := 𝓘(ℝ, E)) γ w (Ioo (-ε) ε) := by
    intro x
    obtain ⟨γ, h0, hγ⟩ := hloc x
    exact ⟨γ, h0, fun t ht =>
      (hasDerivWithinAt_iff_hasFDerivWithinAt.mp (hγ t ht)).hasMFDerivWithinAt⟩
  -- The uniform time lemma upgrades uniform local existence to a global integral curve.
  obtain ⟨γ, hγ0, hγ⟩ := exists_isMIntegralCurve_of_isMIntegralCurveOn
    (I := 𝓘(ℝ, E)) (M := E) (v := fun x : E => w x) hv hε hloc' x₀
  -- On the model space the manifold derivative is the ordinary derivative.
  exact ⟨γ, hγ0, fun t => hasMFDerivAt_iff_hasFDerivAt.mp (hγ t)⟩

theorem exists_global_integralCurve {m : ℕ} {w : Work.Drive.Amb m → Work.Drive.Amb m}
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (hws : HasCompactSupport w)
    (x₀ : Work.Drive.Amb m) :
    ∃ γ : ℝ → Work.Drive.Amb m, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (w (γ t)) t :=
  exists_global_integralCurve_aux (hw.of_le (by simp)) hws x₀

end

end Work.Drive
