import Mathlib
import Submission.Work.WilE3.Frame.CutSys
import Submission.Work.WilE3.Frame.eaEvalC_toC

namespace Work.WilE3.Frame

/-- `toC` (viewing a real point as a complex one) is continuous: it is the product over the
coordinates of the inclusions `ℝ → ℂ`. -/
private lemma continuous_toC {k : ℕ} : Continuous (toC (k := k)) := by
  refine continuous_pi (fun i => ?_)
  exact Complex.continuous_ofReal.comp (continuous_apply i)

/-- **From the ball to the real germ.**  Let `Ψ` straighten `{h = 0}` at the real point `x`
(`IsStraightening`), and suppose that the composed function `u ↦ eaEvalC c f (Ψ (u, 0))` vanishes
at every *real* point of the ball of radius `ρ > 0` around `u₀ = uCoord k ι (toC x)`, i.e. at every
`u₀ + w_ℂ` with `w : U k ι → ℝ` and `‖w_ℂ‖ < ρ`.  Then `eaEval c f` vanishes on `{h = 0}` near
`x`.

Indeed, for a real `y` near `x`, conjunct 4 of `IsStraightening` gives
`toC y = Ψ (PhiC c h ι (toC y))`, and if in addition `h y = 0` then
`PhiC c h ι (toC y) = (uCoord k ι (toC y), 0)` (using `eaEvalC_toC` and `eaEval c (h a) y = 0`),
while `uCoord k ι (toC y) = u₀ + w_ℂ` for the real direction `w i = y i.1 - x i.1`.  For `y` close
enough to `x` one has `‖w_ℂ‖ < ρ` (continuity of the norm at `y = x`, where it is `0`), so the
hypothesis gives `eaEvalC c f (toC y) = 0`, and `eaEvalC_toC` transfers this to
`eaEval c f y = 0`.

The continuity of `toC` is available as `Submission.Work.WilE3.Identity.E3_identity_proved_of_multiplicity`
has it privately; it is `continuous_pi` applied to `Complex.continuous_ofReal.comp (continuous_apply i)`. -/
theorem vanish_of_straightening_of_ball_zero {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (h : Fin j → WilkiesDesign.E.EAPoly k r) (ι : Fin j → Fin k)
    (f : WilkiesDesign.E.EAPoly k r) (x : Fin k → ℝ)
    (Ψ : ((Work.WilE3.Frame.U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ))
    (hΨ : Work.WilE3.Frame.IsStraightening c h ι x Ψ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hGz : ∀ w : Work.WilE3.Frame.U k ι → ℝ, ‖(fun i => (w i : ℂ))‖ < ρ →
      Work.WilE3.eaEvalC c f (Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x) +
        (fun i => (w i : ℂ)), 0)) = 0) :
    ∀ᶠ y in nhds x, (∀ a, WilkiesDesign.E.eaEval c (h a) y = 0) →
      WilkiesDesign.E.eaEval c f y = 0 := by
  classical
  -- Conjunct 4 of `IsStraightening`, pulled back along the continuous map `toC`.
  have hev1 : ∀ᶠ y in nhds x, Ψ (PhiC c h ι (toC y)) = toC y :=
    Filter.Tendsto.eventually ((continuous_toC (k := k)).tendsto x) hΨ.2.2.2
  -- The real direction `w l = y l - x l` is small as soon as `y` is close to `x`.
  have hcont : Continuous (fun y : Fin k → ℝ =>
      (fun l : U k ι => ((y l.1 - x l.1 : ℝ) : ℂ))) := by
    refine continuous_pi (fun l => ?_)
    exact Complex.continuous_ofReal.comp ((continuous_apply l.1).sub continuous_const)
  have hzx : (fun l : U k ι => ((x l.1 - x l.1 : ℝ) : ℂ)) = 0 := by
    funext l
    simp
  have h0val :
      (fun y : Fin k → ℝ => ‖(fun l : U k ι => ((y l.1 - x l.1 : ℝ) : ℂ))‖) x = 0 := by
    show ‖(fun l : U k ι => ((x l.1 - x l.1 : ℝ) : ℂ))‖ = 0
    rw [hzx]
    simp
  have hlim : Filter.Tendsto (fun y : Fin k → ℝ =>
      ‖(fun l : U k ι => ((y l.1 - x l.1 : ℝ) : ℂ))‖) (nhds x) (nhds 0) := by
    rw [← h0val]
    exact hcont.norm.tendsto x
  have hev2 : ∀ᶠ y in nhds x, ‖(fun l : U k ι => ((y l.1 - x l.1 : ℝ) : ℂ))‖ < ρ :=
    Filter.Tendsto.eventually hlim (isOpen_Iio.mem_nhds hρ)
  filter_upwards [hev1, hev2] with y h1 h2
  intro hP
  -- If `h y = 0`, the straightened coordinates of `toC y` are the real direction translated to
  -- the base point, with zero in the `h`-slot.
  have hPhi : PhiC c h ι (toC y) =
      (uCoord k ι (toC x) + (fun l => ((y l.1 - x l.1 : ℝ) : ℂ)), 0) := by
    have hunfold : PhiC c h ι (toC y) =
        (uCoord k ι (toC y), fun a => eaEvalC c (h a) (toC y)) := rfl
    rw [hunfold]
    refine Prod.ext ?_ ?_
    · funext l
      show (y l.1 : ℂ) = (x l.1 : ℂ) + ((y l.1 - x l.1 : ℝ) : ℂ)
      push_cast
      ring
    · funext a
      show eaEvalC c (h a) (toC y) = 0
      rw [eaEvalC_toC, hP a]
      simp
  -- Transport the ball hypothesis back to the real point `y`.
  have hfy : eaEvalC c f (toC y) = 0 := by
    rw [← h1, hPhi]
    exact hGz (fun l => y l.1 - x l.1) h2
  rw [eaEvalC_toC] at hfy
  exact Complex.ofReal_eq_zero.mp hfy

end Work.WilE3.Frame
