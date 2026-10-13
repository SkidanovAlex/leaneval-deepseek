import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Horizon
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FKJets
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Standing

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RXT0.QlimZLipBox` — the `z`-Lipschitz bound of the angular moments `Qlim` on a box `[a,b]`

The angular moments of the limit profile, `Qlim α g τ k`, are the `z`-jets of the `L₁₂`-profile:
`Qlim · (k+1) z / z` is the `z`-derivative of `Qlim · k` (`FKDeriv.Qlim_hasDerivAt_1/2`).  Hence
each `Qlim · k` (`k ≤ 2`) is Lipschitz on every box `[a,b]` with `0 < a`, uniformly in `τ ∈ [0,S]`:

    |Qlim α g τ k z - Qlim α g τ k z'| ≤ C · |z - z'|.

The proof is by the uniform-in-`n` mean value theorem on the approximants `Qapp α gn τ n k` — whose
`z`-derivative is `Qapp · (k+1) x / x`, bounded by `3(π/2)C_B / a` uniformly, since the slot
bound `Ftau_slot_le3` (uniform on the horizon, `Horizon.ftau_slot_bound`) controls the moments up
to order `3` — and then passing to the limit `n → ∞` with `FKJets.Qapp_tendsto`.

`sorry`-free; rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT0

open Work.FTS.Galerkin (Fn Fam slice)

set_option maxHeartbeats 800000

theorem QlimZLipBox {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∀ a b : ℝ, 0 < a → a ≤ b → ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k ≤ 2 →
      ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z ∈ Set.Icc a b, ∀ z' ∈ Set.Icc a b,
        |Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim α g τ k z
          - Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim α g τ k z'| ≤ C * |z - z'| := by
  intro S hS a b ha hab
  obtain ⟨gn, B, L, hC, hLip, hjet0, -⟩ := hA S hS
  -- the two uniform slot bounds on the horizon `[0,S]`
  obtain ⟨Cw, hCw0, hblock⟩ :=
    Work.FTS_RegExport.RXT.Sys.L12FKaux.approx_slot_bound (α := α) (C₀ := C₀) hα hα13
      (T := S) hS (fun n τ hτ => (hC n τ hτ).1) (fun n τ hτ => (hC n τ hτ).2.1)
  obtain ⟨CB, hCB0, hsl⟩ :=
    Work.FTS_RegExport.RXT.Sys.L12FKaux.ftau_slot_bound (α := α) (B := B) hα hα13
      (fun n τ hτ => (hC n τ hτ).1) (fun n τ hτ => (hC n τ hτ).2.2)
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the profiles are `C⁴` on the open quadrant
  have hCD : ∀ (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) S → ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0 := by
    intro τ hτ n
    have hstar := Work.FTS_RegExport.RXT.Sys.L12FKaux.Fstar_contDiffOn hβ hβ1 4
    have hsl' : ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
        Work.FTS.EllipticEst.Q0 := (hC n τ hτ).1.reg.forall 4
    have heq : Function.uncurry (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (gn n) τ)
        = fun x : ℝ × ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) x.1 x.2
          + slice (gn n) τ x.1 x.2 := by
      funext x
      rfl
    rw [heq]
    exact hstar.add hsl'
  -- pointwise jet convergence of the approximants
  have hjet : ∀ (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) S → ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ)) := by
    intro τ hτ k hk z θ hQd
    simpa only [Work.Spaces.mixed_zero_right] using hjet0 τ hτ k 0 (by omega) z θ hQd
  have hCBnn : 0 ≤ 3 * (Real.pi / 2) * CB := by positivity
  refine ⟨3 * (Real.pi / 2) * CB / a, div_nonneg hCBnn ha.le, ?_⟩
  intro k hk τ hτ z hz z' hz'
  have hza : 0 < z := lt_of_lt_of_le ha hz.1
  have hza' : 0 < z' := lt_of_lt_of_le ha hz'.1
  -- the approximant moments converge to the limit moment, at both points
  have hlimz : Filter.Tendsto (fun n => Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp α gn τ n k z)
      Filter.atTop (𝓝 (Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim α g τ k z)) :=
    Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp_tendsto (α := α) hα hα13 hCw0 hCB0
      (fun n => (hC n τ hτ).1.reg.forall 4)
      (fun n k' hk' y θ hy h0 h1 => hblock n τ hτ k' hk' y θ hy h0 h1)
      (hCD τ hτ)
      (fun n k' hk' y θ hy h0 h1 => hsl τ hτ n k' hk' y θ hy h0 h1)
      (hjet τ hτ) hk hza
  have hlimz' : Filter.Tendsto (fun n => Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp α gn τ n k z')
      Filter.atTop (𝓝 (Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim α g τ k z')) :=
    Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp_tendsto (α := α) hα hα13 hCw0 hCB0
      (fun n => (hC n τ hτ).1.reg.forall 4)
      (fun n k' hk' y θ hy h0 h1 => hblock n τ hτ k' hk' y θ hy h0 h1)
      (hCD τ hτ)
      (fun n k' hk' y θ hy h0 h1 => hsl τ hτ n k' hk' y θ hy h0 h1)
      (hjet τ hτ) hk hza'
  refine le_of_tendsto ((hlimz.sub hlimz').abs) (Filter.Eventually.of_forall fun n => ?_)
  -- the uniform-in-`n` mean value theorem on `[a,b]`
  have hder : ∀ x ∈ Set.Icc a b, HasDerivAt (Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp α gn τ n k)
      (Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp α gn τ n (k + 1) x / x) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    exact Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp_hasDerivAt (α := α) hα hα13 hCB0
      (hCD τ hτ)
      (fun m k' hk' y θ hy h0 h1 => hsl τ hτ m k' hk' y θ hy h0 h1) n hk hx0
  have hbnd : ∀ x ∈ Set.Icc a b,
      ‖deriv (Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp α gn τ n k) x‖
        ≤ 3 * (Real.pi / 2) * CB / a := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hdx := hder x hx
    rw [hdx.deriv, Real.norm_eq_abs, abs_div, abs_of_pos hx0]
    refine div_le_div₀ hCBnn ?_ ha hx.1
    exact Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp_bound (α := α) hα hα13 hCB0
      (hCD τ hτ)
      (fun m k' hk' y θ hy h0 h1 => hsl τ hτ m k' hk' y θ hy h0 h1) n (by omega) hx0
  have hMV := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp α gn τ n k) (s := Set.Icc a b)
    (x := z') (y := z) (C := 3 * (Real.pi / 2) * CB / a)
    (fun x hx => (hder x hx).differentiableAt) hbnd (convex_Icc a b) hz' hz
  simpa using hMV

end Work.FTS_RegExport.RXT0
