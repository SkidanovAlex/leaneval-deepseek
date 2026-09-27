import Mathlib

namespace Work.Drive.Whitney

open WithLp

/-- The Euclidean space `ℝ^{k+1}` splits as `ℝ × ℝ^k`, compatibly with `Fin.cons`.

The underlying linear equivalence is `Fin.consLinearEquiv`; it is promoted to a continuous
linear equivalence (all spaces involved are finite-dimensional) and transported across the
`WithLp 2` type synonyms via `EuclideanSpace.equiv`. -/
theorem splitEuclideanSpace (k : ℕ) :
    ∃ e : (ℝ × EuclideanSpace ℝ (Fin k)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k + 1)),
      (∀ (x : ℝ) (v : EuclideanSpace ℝ (Fin k)),
        e (x, v) = WithLp.toLp 2 (Fin.cons x (WithLp.ofLp v))) := by
  refine ⟨(ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (EuclideanSpace.equiv (Fin k) ℝ) |>.trans
    ((Fin.consLinearEquiv ℝ (fun _ : Fin (k+1) => ℝ)).toContinuousLinearEquiv) |>.trans
    (EuclideanSpace.equiv (Fin (k+1)) ℝ).symm, ?_⟩
  intro x v
  simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
    PiLp.coe_continuousLinearEquiv, PiLp.coe_symm_continuousLinearEquiv,
    LinearEquiv.coe_toContinuousLinearEquiv']
  ext i
  simp [Fin.consLinearEquiv_apply, Fin.consEquiv_apply]

end Work.Drive.Whitney
