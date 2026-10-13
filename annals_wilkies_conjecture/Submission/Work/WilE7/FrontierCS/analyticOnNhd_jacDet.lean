/-
  WilE7 / CS-slice, node N1c: the Jacobian determinant `jacDet` of an entire map is entire.

  The entries of the Jacobian are `e ↦ fderiv ℝ g e (Pi.single l 1) a`; each is analytic because
  `fderiv ℝ g` is analytic (for `g` analytic, `AnalyticOnNhd.fderiv`) and the evaluation
  `L ↦ L v` followed by a coordinate projection is a continuous linear map (hence analytic).
  The determinant is the generic determinant polynomial `det (Matrix.mvPolynomialX)`, evaluated
  at the analytic matrix entries (`AnalyticOnNhd.aeval_mvPolynomial`,
  `Matrix.eval_det_mvPolynomialX`).
-/
import Mathlib

namespace Work.WilE7.FrontierCS

open scoped Topology

theorem analyticOnNhd_jacDet {j : ℕ} {g : (Fin j → ℝ) → (Fin j → ℝ)}
    (hg : AnalyticOnNhd ℝ g Set.univ) :
    AnalyticOnNhd ℝ (fun e => (Matrix.of fun (a l : Fin j) => fderiv ℝ g e (Pi.single l 1) a).det)
      Set.univ := by
  have hfd : AnalyticOnNhd ℝ (fun e => fderiv ℝ g e) Set.univ := hg.fderiv
  -- Each entry of the Jacobian is analytic in `e`.
  have hent : ∀ (a l : Fin j),
      AnalyticOnNhd ℝ (fun e => fderiv ℝ g e (Pi.single l 1) a) Set.univ := by
    intro a l
    -- `Φ` is the continuous linear map `L ↦ (L (Pi.single l 1)) a` on `ℝ^j →L[ℝ] ℝ^j`.
    set Φ : ((Fin j → ℝ) →L[ℝ] (Fin j → ℝ)) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj a).comp ((ContinuousLinearMap.apply ℝ (Fin j → ℝ)) (Pi.single l 1))
    have h1 : AnalyticOnNhd ℝ (fun L : (Fin j → ℝ) →L[ℝ] (Fin j → ℝ) => Φ L) Set.univ :=
      Φ.analyticOnNhd Set.univ
    have h2 := h1.comp hfd (fun x _ => trivial)
    simpa [Function.comp_def, Φ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.apply_apply] using h2
  -- Package the entries as a function of `(Fin j × Fin j)`.
  set f : (Fin j → ℝ) → (Fin j × Fin j) → ℝ :=
      fun e p => fderiv ℝ g e (Pi.single p.2 1) p.1 with hfdef
  have hf_an : ∀ p : Fin j × Fin j, AnalyticOnNhd ℝ (f · p) Set.univ := by
    rintro ⟨a, l⟩
    simpa [hfdef] using hent a l
  -- The determinant is a polynomial in the entries.
  have hpoly := AnalyticOnNhd.aeval_mvPolynomial (𝕜 := ℝ) hf_an
      (Matrix.det (Matrix.mvPolynomialX (Fin j) (Fin j) ℝ))
  have heq : (fun x => MvPolynomial.aeval (f x) (Matrix.det (Matrix.mvPolynomialX (Fin j) (Fin j) ℝ)))
      = (fun e => (Matrix.of fun (a l : Fin j) => fderiv ℝ g e (Pi.single l 1) a).det) := by
    funext x
    rw [MvPolynomial.aeval_eq_eval, Matrix.eval_det_mvPolynomialX]
  rwa [heq] at hpoly

end Work.WilE7.FrontierCS
