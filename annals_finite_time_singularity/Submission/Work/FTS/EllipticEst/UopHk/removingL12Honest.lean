import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.RegQ
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `removingL12Honest`

Target (Elgindi, Annals **194** (2021), §'Elliptic Regularity Estimates', Theorem
`RemovingL12`, tex 1034) in the *interior* class `EllHypQ` of `Submission/Work/FTS/EllipticEst/RegQ.lean`:

  `α² |z²∂_zzΨ|_{ℋ^k} + |∂_θθ(Ψ - (1/(4α)) sin 2θ · L₁₂(F))|_{ℋ^k} ≤ C |F|_{ℋ^k}`.

## The route, and the structural facts about the class proved here

* `sliceTendsto_zero_left` / `sliceTendsto_zero_right`: **a datum of `RegQ α k f` (i.e. of
  `BdryTraces`) has vanishing slice limits at both angular endpoints, for `α > 0`.**  This is
  the structural difference between the interior class `RegQ` and the trace-free classes
  (`EllHypT`, `TT.EllWeakPos`): `BdryTraces` demands
  `sin(2θ)^{1-γ} f(z,θ)² → 0` as `θ → 0⁺`, and `1 - γ = -α/10 < 0` makes the prefactor
  `sin(2θ)^{1-γ} ≥ 1` near the endpoint, so `f(z,θ)² ≤ sin(2θ)^{1-γ} f(z,θ)² → 0`.
  Equivalently the `θ = 0` **limit** of every slice vanishes (the counterexample of
  `Submission/Work/FTS/EllipticEst/Cores/honestFstarFacts.lean` — which refutes the corresponding
  smoothness statement for the trace-free class `EllHypT` — therefore does *not* lie in
  `EllHypQ`).

* `mixed_tendsto_zero_left`: the same for every mixed derivative `D_z^bD_θ^a f` for which the
  class carries the traces (`RegQ α k (mixed b a f)`).

These are the boundary inputs the straightening `Ψ ↦ Ψ + Gsing α F · sin 2θ` needs in order to
upgrade a datum of `EllHypQ` to one of the weak class `TT.EllWeakPos` (where the a-priori
`ℋ^k` estimate `prop:Hk` is stated).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.UopHk

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Vanishing of the slice limits at the angular endpoints -/

/-- **The slice limit at `θ = 0⁺` vanishes for a datum of the interior class.**

`BdryTraces` gives `sin(2θ)^{1-γ} f(z,θ)² → 0` along `𝓝[>] 0`; since `γ = 1 + α/10 > 1` for
`α > 0`, the prefactor satisfies `sin(2θ)^{1-γ} ≥ 1` for `θ ∈ (0,π/2)`, so
`f(z,θ)² ≤ sin(2θ)^{1-γ} f(z,θ)² → 0`. -/
theorem regQ_sliceTendsto_zero_left {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (hα : 0 < α)
    (h : Work.FTS.Nonlin.RegQ α k f) (z : ℝ) (hz : 0 < z) :
    Tendsto (fun θ => f z θ) (𝓝[>] 0) (𝓝 0) := by
  have hB : Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (f z θ) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    have h1 := (h.2.2 0 0 (Nat.zero_le k)).2 z hz
    simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero] using h1.1
  have hgam : (1 : ℝ) - Work.Spaces.gam α < 0 := by
    rw [show Work.Spaces.gam α = 1 + α / 10 from rfl]; linarith
  have hev : ∀ᶠ θ in 𝓝[>] (0:ℝ), θ ∈ Set.Ioo 0 (π / 2) := by
    refine inter_mem self_mem_nhdsWithin ?_
    exact (Filter.le_def.mp nhdsWithin_le_nhds) (Set.Iio (π / 2))
      (Iio_mem_nhds (by linarith [Real.pi_pos] : (0:ℝ) < π / 2))
  have hsq : Tendsto (fun θ => f z θ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun θ => sq_nonneg _) ?_ hB
    filter_upwards [hev] with θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hle : 1 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hs (Real.sin_le_one (2 * θ)) (le_of_lt hgam)
      simpa using h
    nlinarith [sq_nonneg (f z θ)]
  have hroot : Tendsto (fun θ => |f z θ|) (𝓝[>] 0) (𝓝 0) := by
    have h := hsq.sqrt
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using h
  exact (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa using hroot)

/-- **The slice limit at `θ = (π/2)⁻` vanishes for a datum of the interior class.**  Same proof
as `sliceTendsto_zero_left`, using the second conjunct of `BdryTraces` at `(a,b) = (0,0)`. -/
theorem regQ_sliceTendsto_zero_right {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (hα : 0 < α)
    (h : Work.FTS.Nonlin.RegQ α k f) (z : ℝ) (hz : 0 < z) :
    Tendsto (fun θ => f z θ) (𝓝[<] (π / 2)) (𝓝 0) := by
  have hB : Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (f z θ) ^ 2)
      (𝓝[<] (π / 2)) (𝓝 0) := by
    have h1 := (h.2.2 0 0 (Nat.zero_le k)).2 z hz
    simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero] using h1.2
  have hgam : (1 : ℝ) - Work.Spaces.gam α < 0 := by
    rw [show Work.Spaces.gam α = 1 + α / 10 from rfl]; linarith
  have hev : ∀ᶠ θ in 𝓝[<] (π / 2), θ ∈ Set.Ioo 0 (π / 2) := by
    refine inter_mem ?_ self_mem_nhdsWithin
    exact (Filter.le_def.mp nhdsWithin_le_nhds) (Set.Ioi (0:ℝ))
      (Ioi_mem_nhds (by linarith [Real.pi_pos] : (0:ℝ) < π / 2))
  have hsq : Tendsto (fun θ => f z θ ^ 2) (𝓝[<] (π / 2)) (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun θ => sq_nonneg _) ?_ hB
    filter_upwards [hev] with θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hle : 1 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hs (Real.sin_le_one (2 * θ)) (le_of_lt hgam)
      simpa using h
    nlinarith [sq_nonneg (f z θ)]
  have hroot : Tendsto (fun θ => |f z θ|) (𝓝[<] (π / 2)) (𝓝 0) := by
    have h := hsq.sqrt
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using h
  exact (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa using hroot)

/-- **Every mixed derivative whose traces the class carries vanishes at `θ = 0⁺`.** -/
theorem mixed_tendsto_zero_left {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (b a : ℕ) (hα : 0 < α)
    (h : Work.FTS.Nonlin.RegQ α k (Work.Spaces.mixed b a f))
    (z : ℝ) (hz : 0 < z) :
    Tendsto (fun θ => Work.Spaces.mixed b a f z θ) (𝓝[>] 0) (𝓝 0) :=
  regQ_sliceTendsto_zero_left hα h z hz

/-! ## The consequences for a datum of `EllHypQ` -/

/-- A datum of `EllHypQ α k F Ψ` has vanishing slice limit at `θ = 0⁺` (this is the control of
the `θ = 0` trace which the trace-free class `EllHypT` lacks). -/
theorem EllHypQ.sliceTendsto_zero_left {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHypQ α k F Ψ) (z : ℝ) (hz : 0 < z) :
    Tendsto (fun θ => Ψ z θ) (𝓝[>] 0) (𝓝 0) :=
  regQ_sliceTendsto_zero_left hα h.regPsi z hz

/-- The same at `θ = (π/2)⁻`. -/
theorem EllHypQ.sliceTendsto_zero_right {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHypQ α k F Ψ) (z : ℝ) (hz : 0 < z) :
    Tendsto (fun θ => Ψ z θ) (𝓝[<] (π / 2)) (𝓝 0) :=
  regQ_sliceTendsto_zero_right hα h.regPsi z hz

end Work.FTS.EllipticEst.UopHk

namespace Work.FTS.EllipticEst.UopHk

theorem removingL12Honest : ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.EllHypQ α k F Ψ →
      Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
      α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  sorry

end Work.FTS.EllipticEst.UopHk
