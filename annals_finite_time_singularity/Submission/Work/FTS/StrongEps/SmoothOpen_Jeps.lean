/-
Copyright: work module for the Elgindi finite-time singularity project.

# `SmoothOpen_Jeps` — `J_ε` preserves `C^∞` on the open quadrant

`Jeps ρ ε f` is the log-coordinate mollifier of `Submission/Work/FTS/StrongEps/Basic.lean`:

`Jeps ρ ε f z θ = ∫ p, ε⁻¹^2 ρ (ε⁻¹ • p) * f (z e^{-p₁}) (arctan (tan θ e^{-p₂}))`

on the open quadrant `Q0 = (0,∞) × (0,π/2)` and `0` outside it.  The target of this file is

`SmoothOpen_Jeps : (∀ n, ContDiffOn ℝ n (uncurry f) Q0) → ∀ n, ContDiffOn ℝ n (uncurry (Jeps ρ ε f)) Q0`

for a *merely continuous* mollifier kernel `ρ ∈ IsMollKernel ρ` (continuous, supported in the
closed unit ball, nonnegative, mass `1`).  Note that `IsMollKernel ρ` does **not** assume that `ρ`
is smooth, so the derivatives cannot be pushed onto the kernel (that is the hypothesis
`IsSmoothKernel ρ` of the sibling statement `Jeps_contDiffOn`); instead they are pushed onto the
profile `f`, which is smooth by hypothesis.

## The argument

In the log coordinates `(s,ζ) = (log z, log tan θ)` the substitution `z ↦ z e^{-p₁}`,
`θ ↦ arctan (tan θ e^{-p₂})` is the translation `(s,ζ) ↦ (s,ζ) - p` (`Basic.logPull_shift`), so

`Jeps ρ ε f z θ = (Jker ρ ε ⋆ logPull f) (log z, log tan θ)`   (`Jeps_eq_conv`)

where `Jker ρ ε` is the rescaled kernel (compactly supported and continuous, by `IsMollKernel`)
and `logPull f (s,ζ) = f (e^s) (arctan e^ζ)` is `C^n` because `(e^s, arctan e^ζ) ∈ Q0` always.

The one analytic ingredient is therefore

`contDiff_convolution_of_continuous_hasCompactSupport`: the convolution of a compactly supported
*continuous* kernel `K` with a `C^n` function `g` is `C^n`.  (Mathlib's
`HasCompactSupport.contDiff_convolution_right` wants the compactly supported factor to be smooth;
here instead the smooth factor is cut off locally: near a point `x₀` the convolution only sees the
values of `g` on the compact set `x₀ - tsupport K`, on which a `ContDiffBump` may be inserted, and
the convolution of a compactly supported `C^n` function with a locally integrable one is `C^n`
again.)

Composing with the `C^∞` log-coordinate map `(z,θ) ↦ (log z, log tan θ)` on `Q0` and rewriting
with `Jeps_eq_conv` concludes the proof.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Convolution
open MeasureTheory Set Filter
open Work.FTS.EllipticEst (Q0 mem_Q0)

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-! ## The kernel `Jker ρ ε` of a merely continuous mollifier -/

/-- `Jker ρ ε` is continuous as soon as `ρ` is. -/
theorem continuous_Jker (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) (ε : ℝ) :
    Continuous (Jker ρ ε) :=
  continuous_const.mul (hρ.cont.comp (continuous_id.const_smul (ε⁻¹)))

/-- `Jker ρ ε` is compactly supported (its support is contained in the square of half-side `|ε|`,
because `ρ` is supported in the closed unit ball).  The variant of `hasCompactSupport_Jker`
(`Jeps_contDiffOn.lean`) for a merely continuous kernel. -/
theorem hasCompactSupport_Jker_moll (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) : HasCompactSupport (Jker ρ ε) := by
  refine HasCompactSupport.intro (K := Set.Icc (-|ε|) |ε| ×ˢ Set.Icc (-|ε|) |ε|)
    (isCompact_Icc.prod isCompact_Icc) ?_
  rintro ⟨x1, x2⟩ hx
  have hx' : ¬(-|ε| ≤ x1 ∧ x1 ≤ |ε|) ∨ ¬(-|ε| ≤ x2 ∧ x2 ≤ |ε|) := by
    simpa only [Set.mem_prod, Set.mem_Icc, not_and_or] using hx
  have aux : ∀ y : ℝ, ¬(-|ε| ≤ y ∧ y ≤ |ε|) → |ε| < |y| := by
    intro y hy
    rw [not_and_or, not_le, not_le] at hy
    rcases hy with h | h
    · have hy0 : y < 0 := by linarith [abs_nonneg ε, h]
      have : |y| = -y := abs_of_neg hy0
      linarith
    · have hy0 : 0 < y := by linarith [abs_nonneg ε, h]
      have : |y| = y := abs_of_nonneg hy0.le
      linarith
  have hbig : |ε| < |x1| ∨ |ε| < |x2| := by
    rcases hx' with h | h
    · exact Or.inl (aux x1 h)
    · exact Or.inr (aux x2 h)
  have habs_aux : ∀ y : ℝ, |ε| < |y| → (1 : ℝ) < (ε⁻¹ * y) ^ 2 := by
    intro y hy
    have h1 : (1 : ℝ) < |ε⁻¹ * y| := by
      rw [abs_mul, abs_inv, abs_of_pos hε, ← inv_mul_cancel₀ (ne_of_gt hε)]
      simpa [abs_of_pos hε] using mul_lt_mul_of_pos_left hy (inv_pos.mpr hε)
    have h2 : ((1 : ℝ)) ^ 2 < (ε⁻¹ * y) ^ 2 := by
      rw [sq_lt_sq]
      simpa using h1
    simpa using h2
  have hρ0 : ρ (ε⁻¹ • (x1, x2)) = 0 := by
    by_contra hne
    have hle := hρ.support _ hne
    simp only [Prod.smul_mk, smul_eq_mul] at hle
    have hsum : (1 : ℝ) < (ε⁻¹ * x1) ^ 2 + (ε⁻¹ * x2) ^ 2 := by
      rcases hbig with h | h
      · nlinarith [habs_aux x1 h, sq_nonneg (ε⁻¹ * x2)]
      · nlinarith [habs_aux x2 h, sq_nonneg (ε⁻¹ * x1)]
    exact absurd hle (not_le.mpr hsum)
  simp only [Jker, hρ0, mul_zero]

/-! ## Convolution with a compactly supported continuous kernel -/

/-- **Convolution with a compactly supported continuous kernel preserves `C^n`.**

The kernel `K` is only assumed continuous; the derivatives are pushed onto the `C^n` factor `g`.
Since `g` need not be compactly supported, one localises: near a fixed point `x₀` the convolution
only evaluates `g` on the compact set `x₀ - tsupport K`, where a smooth bump function equal to `1`
may be inserted. -/
theorem contDiff_convolution_of_continuous_hasCompactSupport {K g : ℝ × ℝ → ℝ} (n : ℕ)
    (hKc : Continuous K) (hK : HasCompactSupport K) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ × ℝ)
  let r : ℝ := |R| + 1
  have hrdef : r = |R| + 1 := rfl
  have hRr : tsupport K ⊆ Metric.closedBall (0 : ℝ × ℝ) r := by
    refine hR.trans (Metric.closedBall_subset_closedBall ?_)
    rw [hrdef]
    linarith [le_abs_self R]
  let ψ : ContDiffBump x₀ := ⟨r + 1, r + 2, by rw [hrdef]; positivity, by rw [hrdef]; norm_num⟩
  have hψrIn : ψ.rIn = r + 1 := rfl
  have hev : (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)
      =ᶠ[𝓝 x₀] (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun x : ℝ × ℝ => ψ x * g x)) := by
    show ∀ᶠ x in 𝓝 x₀, (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x
      = (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun x : ℝ × ℝ => ψ x * g x)) x
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨Metric.ball x₀ 1, Metric.ball_mem_nhds _ zero_lt_one, fun x hx => ?_⟩
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change K y * g (x - y) = K y * (ψ (x - y) * g (x - y))
    by_cases hy : K y = 0
    · rw [hy, zero_mul, zero_mul]
    · have hyts : y ∈ tsupport K := subset_closure (Function.mem_support.mpr hy)
      have hyr : ‖y‖ ≤ r := by
        have h := Metric.mem_closedBall.mp (hRr hyts)
        simpa only [dist_eq_norm, sub_zero] using h
      have hx1 : dist x x₀ < 1 := Metric.mem_ball.mp hx
      have hlt : dist (x - y) x₀ < ψ.rIn := by
        have h1 : dist (x - y) (x₀ - y) = dist x x₀ := by
          rw [dist_eq_norm, dist_eq_norm]
          congr 1
          abel
        have h2 : dist (x₀ - y) x₀ = ‖y‖ := by
          rw [dist_eq_norm]
          have h3 : (x₀ - y) - x₀ = -y := by abel
          rw [h3, norm_neg]
        have h4 : dist (x - y) x₀ < r + 1 := by
          calc dist (x - y) x₀
              ≤ dist (x - y) (x₀ - y) + dist (x₀ - y) x₀ := dist_triangle _ _ _
            _ = dist x x₀ + ‖y‖ := by rw [h1, h2]
            _ < 1 + r := by linarith
            _ = r + 1 := by ring
        rwa [hψrIn]
      have hpsi : ψ (x - y) = 1 :=
        ψ.one_of_mem_closedBall (Metric.ball_subset_closedBall hlt)
      rw [hpsi, one_mul]
  have hψg_cs : HasCompactSupport (fun x : ℝ × ℝ => ψ x * g x) :=
    ψ.hasCompactSupport.mul_right (f' := g)
  have hψg_diff : ContDiff ℝ n (fun x : ℝ × ℝ => ψ x * g x) :=
    (ContDiffBump.contDiff ψ).mul hg
  have hglob : ContDiff ℝ n (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun x : ℝ × ℝ => ψ x * g x)) :=
    HasCompactSupport.contDiff_convolution_right _ hψg_cs hKc.locallyIntegrable hψg_diff
  exact ((contDiff_iff_contDiffAt.mp hglob) x₀).congr_of_eventuallyEq hev

/-! ## The target -/

theorem SmoothOpen_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε f))
      Work.FTS.EllipticEst.Q0 := by
  intro n
  -- `logPull f` is `C^n`, because `(e^s, arctan e^ζ)` always lies in `Q0`
  have hlog : ContDiff ℝ n (logPull f) := by
    have hφ : ContDiff ℝ n
        (fun s : ℝ × ℝ => (Real.exp s.1, Real.arctan (Real.exp s.2))) :=
      (Real.contDiff_exp.comp contDiff_fst).prodMk
        (Real.contDiff_arctan.comp (Real.contDiff_exp.comp contDiff_snd))
    have hmem : ∀ s : ℝ × ℝ, (Real.exp s.1, Real.arctan (Real.exp s.2)) ∈ Q0 := fun s =>
      mem_Q0.mpr ⟨Real.exp_pos _, Real.arctan_pos.mpr (Real.exp_pos s.2),
        Real.arctan_lt_pi_div_two _⟩
    have h := (hf n).comp_contDiff hφ hmem
    have hfun : ((Function.uncurry f)
        ∘ (fun s : ℝ × ℝ => (Real.exp s.1, Real.arctan (Real.exp s.2)))) = logPull f := rfl
    rwa [hfun] at h
  -- the convolution with the kernel `Jker ρ ε` is `C^n`
  have hconv : ContDiff ℝ n
      (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull f) :=
    contDiff_convolution_of_continuous_hasCompactSupport n (continuous_Jker ρ hρ ε)
      (hasCompactSupport_Jker_moll ρ hρ hε) hlog
  -- compose with the log-coordinate map, which is `C^∞` on `Q0`
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull f)
          (sOf p.1, zetaOf p.2))
      Work.FTS.EllipticEst.Q0 := by
    have h := hconv.comp_contDiffOn (contDiffOn_logMap n)
    simpa only [Function.comp_def, Quad, Work.FTS.EllipticEst.Q0] using h
  -- and rewrite `Jeps` as the convolution in the log coordinates
  exact hcomp.congr (fun p hp => Jeps_eq_conv ρ ε f hp.1 hp.2)

end Work.FTS.StrongEps
