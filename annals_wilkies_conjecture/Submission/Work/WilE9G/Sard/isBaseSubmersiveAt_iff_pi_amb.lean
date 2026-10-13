import Mathlib
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE5.Strat.flatConormalTools

namespace Work.WilE9G.Sard

open WilkiesDesign WilkiesDesign.E

/-- The differential of the tuple of equations `z' ↦ (a ↦ eaEval S.X.c (S.h a) z')` is the
tuple of the differentials: `fderiv` commutes with the product projection.  This is the only
analytic ingredient of `isBaseSubmersiveAt_iff_pi_amb`. -/
theorem fderiv_pi_eaEval_amb {N : ℕ} (S : Work.WilE9G.AmbStratum N) (z : Fin N → ℝ) :
    fderiv ℝ (fun z' : Fin N → ℝ => fun a : Fin S.j => eaEval S.X.c (S.h a) z') z
      = ContinuousLinearMap.pi (fun a : Fin S.j =>
          fderiv ℝ (fun w : Fin N → ℝ => eaEval S.X.c (S.h a) w) z) := by
  rw [fderiv_pi (fun a =>
    (Work.WilE5.Strat.analyticAt_eaEval S.X.c (S.h a) z).differentiableAt)]

theorem isBaseSubmersiveAt_iff_pi_amb {N n : ℕ} (hn : n ≤ N) (S : Work.WilE9G.AmbStratum N)
    (z : Fin N → ℝ) :
    Work.WilE9G.AmbStratum.IsBaseSubmersiveAt S hn z ↔
      (∀ w : Fin n → ℝ, ∃ v : Fin N → ℝ,
        Work.WilE9G.projBase hn v = w ∧
        fderiv ℝ (fun z' : Fin N → ℝ =>
          (fun a : Fin S.j => WilkiesDesign.E.eaEval S.X.c (S.h a) z')) z v = 0) := by
  have hfd := fderiv_pi_eaEval_amb S z
  constructor
  · intro h w
    obtain ⟨v, hv, hker⟩ := h w
    refine ⟨v, hv, ?_⟩
    rw [hfd]
    funext a
    rw [ContinuousLinearMap.pi_apply]
    exact hker a
  · intro h w
    obtain ⟨v, hv, h0⟩ := h w
    refine ⟨v, hv, fun a => ?_⟩
    have := congrFun h0 a
    rw [hfd, ContinuousLinearMap.pi_apply] at this
    exact this

end Work.WilE9G.Sard
