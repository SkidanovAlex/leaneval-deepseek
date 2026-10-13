import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllExist.SmoothOpenSep
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.mixed_sep_product
import Submission.Work.FTS.PhiStar.ThetaTraces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PhiStar.thetaTraces_orthSource` — θ-traces of the orthogonalised source (R6(4), 2026-10-11)

`orthSource g = g - (15/4)·sin 2θ·F_*(g)(z)`.  On the open quadrant
`D_z^s (orthSource g) = D_z^s g + A(z)·sin 2θ` with `A(z) = D_z^s(-(15/4)F_*(g))(z)`, and
`sin(2θ)^{1-γ}·sin(2θ)² = sin(2θ)^{3-γ} → 0` at both angular ends (`γ = 1 + α/10 ≤ 11/10`).
-/

noncomputable section
open scoped Real Topology
open Filter

namespace Work.FTS.PhiStar

/-- `D_z`-iterates of a radial function do not depend on the angle. -/
theorem DzIter_radial_indep (f : ℝ → ℝ) (n : ℕ) (z θ θ' : ℝ) :
    Work.Spaces.DzIter n (fun z _ => f z) z θ = Work.Spaces.DzIter n (fun z _ => f z) z θ' := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    rw [show (fun z' => Work.Spaces.DzIter n (fun z _ => f z) z' θ)
        = fun z' => Work.Spaces.DzIter n (fun z _ => f z) z' θ' from funext fun z' => ih z']

/-- `sin(2θ)^{1-γ}·sin(2θ)² → 0` along any filter that tends to a zero of `sin 2θ` and on which
`sin 2θ ≥ 0` eventually. -/
theorem sin_rpow_mul_sq_tendsto {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {l : Filter ℝ} {θ₀ : ℝ}
    (hl : l ≤ 𝓝 θ₀) (h0 : Real.sin (2 * θ₀) = 0) (hpos : ∀ᶠ θ in l, 0 ≤ Real.sin (2 * θ)) :
    Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * Real.sin (2 * θ) ^ 2)
      l (𝓝 0) := by
  have hq : 0 < 3 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hsin : Tendsto (fun θ => Real.sin (2 * θ)) l (𝓝 0) := by
    have h1 : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝 θ₀) (𝓝 (Real.sin (2 * θ₀))) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).tendsto θ₀)
    rw [h0] at h1
    exact h1.mono_left hl
  have hc : Tendsto (fun θ => Real.sin (2 * θ) ^ (3 - Work.Spaces.gam α)) l (𝓝 0) := by
    have hr := (Real.continuousAt_rpow_const 0 (3 - Work.Spaces.gam α) (Or.inr hq.le)).tendsto
    rw [Real.zero_rpow hq.ne'] at hr
    exact hr.comp hsin
  refine hc.congr' ?_
  filter_upwards [hpos] with θ hθ
  have hne : (1 - Work.Spaces.gam α) + 2 ≠ 0 := by intro h; linarith
  rw [show (3 - Work.Spaces.gam α) = (1 - Work.Spaces.gam α) + 2 by ring,
    Real.rpow_add' hθ hne, Real.rpow_two]

/-- Transfer of a θ-trace through `n = m + A·sin 2θ`. -/
theorem trace_add_sin {α A : ℝ} {m n : ℝ → ℝ} {l : Filter ℝ}
    (hl : ∀ᶠ θ in l, θ ∈ Set.Ioo 0 (π / 2))
    (heq : ∀ θ, 0 < θ → θ < π / 2 → n θ = m θ + A * Real.sin (2 * θ))
    (hm : Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (m θ) ^ 2) l (𝓝 0))
    (hs : Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * Real.sin (2 * θ) ^ 2)
      l (𝓝 0)) :
    Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (n θ) ^ 2) l (𝓝 0) := by
  have hlim : Tendsto (fun θ => 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (m θ) ^ 2)
      + 2 * A ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * Real.sin (2 * θ) ^ 2))
      l (𝓝 0) := by
    simpa using (hm.const_mul 2).add (hs.const_mul (2 * A ^ 2))
  have hp : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) → 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
    fun θ hθ => Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2])) _
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hl] with θ hθ
    exact mul_nonneg (hp θ hθ) (sq_nonneg _)
  · filter_upwards [hl] with θ hθ
    rw [heq θ hθ.1 hθ.2]
    have hsq : (m θ + A * Real.sin (2 * θ)) ^ 2
        ≤ 2 * (m θ) ^ 2 + 2 * A ^ 2 * Real.sin (2 * θ) ^ 2 := by
      nlinarith [sq_nonneg (m θ - A * Real.sin (2 * θ))]
    calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (m θ + A * Real.sin (2 * θ)) ^ 2
        ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (2 * (m θ) ^ 2 + 2 * A ^ 2 * Real.sin (2 * θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (hp θ hθ)
      _ = 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (m θ) ^ 2)
            + 2 * A ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * Real.sin (2 * θ) ^ 2) := by ring

/-- **R6(4) — the θ-traces of the orthogonalised source.** -/
theorem thetaTraces_orthSource {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hF : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Elliptic.Fstar g) (Set.Ioi 0))
    (h : ThetaTraces α k g) : ThetaTraces α k (Work.Elliptic.orthSource g) := by
  set f : ℝ → ℝ := fun z => (-(15 / 4)) * Work.Elliptic.Fstar g z with hfdef
  have hfsm : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) f (Set.Ioi 0) :=
    fun m => (contDiffOn_const (c := (-(15 / 4) : ℝ))).mul (hF m)
  have hsin : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hSsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z * Real.sin (2 * θ)) :=
    Work.FTS.EllExist.sep_mul_open (g := f) (χ := fun θ : ℝ => Real.sin (2 * θ)) hfsm hsin
  have horth : Work.Elliptic.orthSource g = fun z θ => g z θ + f z * Real.sin (2 * θ) := by
    funext z θ
    simp only [Work.Elliptic.orthSource, hfdef]
    ring
  intro s hs z hz
  have hz0 : 0 < z := hz
  obtain ⟨h0, h1⟩ := h s hs z hz
  set A : ℝ := Work.Spaces.DzIter s (fun z _ => f z) z 0 with hA
  have hmix : ∀ θ, 0 < θ → θ < π / 2 →
      Work.Spaces.mixed s 0 (Work.Elliptic.orthSource g) z θ
        = Work.Spaces.mixed s 0 g z θ + A * Real.sin (2 * θ) := by
    intro θ hθ0 hθ1
    rw [horth, Work.FTS.EllipticEst.SmoothOpen.mixed_add hsm hSsm s 0 z θ hz0 hθ0 hθ1,
      Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.mixed_sep_product s 0 f
        (fun θ => Real.sin (2 * θ)) z θ,
      DzIter_radial_indep f s z θ 0]
    rfl
  have hIoo0 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Set.Ioo 0 (π / 2) :=
    Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by positivity)
  have hIoo1 : ∀ᶠ θ in 𝓝[<] (π / 2), θ ∈ Set.Ioo 0 (π / 2) :=
    Ioo_mem_nhdsLT (show (0 : ℝ) < π / 2 by positivity)
  have hnn : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) → 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  refine ⟨?_, ?_⟩
  · refine trace_add_sin (m := fun θ => Work.Spaces.mixed s 0 g z θ) hIoo0 hmix h0 ?_
    exact sin_rpow_mul_sq_tendsto hα hα1 nhdsWithin_le_nhds (by simp)
      (hIoo0.mono fun θ hθ => hnn θ hθ)
  · refine trace_add_sin (m := fun θ => Work.Spaces.mixed s 0 g z θ) hIoo1 hmix h1 ?_
    exact sin_rpow_mul_sq_tendsto hα hα1 nhdsWithin_le_nhds
      (by rw [show 2 * (π / 2) = π by ring]; exact Real.sin_pi)
      (hIoo1.mono fun θ hθ => hnn θ hθ)

end Work.FTS.PhiStar
