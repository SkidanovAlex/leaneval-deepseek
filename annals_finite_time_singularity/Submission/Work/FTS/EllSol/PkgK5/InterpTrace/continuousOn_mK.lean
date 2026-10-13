/-
# `PkgK5.InterpTrace.continuousOn_mK` — continuity in `θ` of the cut-off `m_k`-type integrals

All four integrals in the statement have the shape

  `θ ↦ ∫ z in cA k..cB k, χ k z * w z ^ 2 * G z θ`

with `G` a product of at most two of the jointly smooth open-quadrant functions `ψ`, `∂_θψ`,
`∂_θ²ψ`.  Since the window `[cA k, cB k]` is a compact sub-interval of `(0,∞)` and `θ` ranges in
the *open* interval `(0, π/2)`, the integrand is jointly continuous on a compact neighbourhood of
`[cA k, cB k] × {θ₀}`; continuity of the parameter integral is then the standard dominated
convergence statement `intervalIntegral.continuousWithinAt_of_dominated_interval`, with a constant
dominating function (the integrand is bounded on the compact rectangle).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllSol.PkgK5.InterpTraceCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.InterpTrace

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The generic parameter-continuity lemma -/

/-- **Continuity in the parameter of an interval integral.**  If `F` is jointly continuous on the
open quadrant and `0 < a`, `a ≤ b`, then `θ ↦ ∫ z in a..b, F z θ` is continuous (within the open
interval `(0,π/2)`) at every interior point `θ₀`. -/
theorem continuousWithinAt_intervalIntegral_of_continuousOn
    {F : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousWithinAt (fun θ => ∫ z in a..b, F z θ) (Set.Ioo 0 (π / 2)) θ₀ := by
  -- a symmetric inner interval around `θ₀` contained in `(0,π/2)`
  set δ : ℝ := min θ₀ (π / 2 - θ₀) / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    have : 0 < min θ₀ (π / 2 - θ₀) := lt_min hθ₀.1 (by linarith [hθ₀.2])
    linarith
  have hδ₁ : 2 * δ ≤ θ₀ := by
    rw [hδdef]; have := min_le_left θ₀ (π / 2 - θ₀); linarith
  have hδ₂ : 2 * δ ≤ π / 2 - θ₀ := by
    rw [hδdef]; have := min_le_right θ₀ (π / 2 - θ₀); linarith
  have hsub : Set.Icc (θ₀ - δ) (θ₀ + δ) ⊆ Set.Ioo 0 (π / 2) := by
    intro θ hθ
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hθ
    exact ⟨by linarith, by linarith⟩
  -- the compact rectangle
  set B : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc (θ₀ - δ) (θ₀ + δ) with hBdef
  have hBsub : B ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
    have hp1' : a ≤ p.1 := (Set.mem_Icc.mp hp1).1
    exact Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr (lt_of_lt_of_le ha hp1'), hsub hp2⟩
  have hFB : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) B := hF.mono hBsub
  have hcomp : IsCompact B := isCompact_Icc.prod isCompact_Icc
  -- a uniform bound for the integrand on the rectangle
  set M : ℝ := sSup ((fun p : ℝ × ℝ => |F p.1 p.2|) '' B) with hMdef
  have hbdd : BddAbove ((fun p : ℝ × ℝ => |F p.1 p.2|) '' B) :=
    hcomp.bddAbove_image hFB.abs
  have hM : ∀ p ∈ B, |F p.1 p.2| ≤ M := fun p hp => le_csSup hbdd ⟨p, hp, rfl⟩
  -- the neighbourhood of `θ₀` on which both the bound and the measurability hold
  have hnbhd : ∀ᶠ θ in 𝓝[Set.Ioo 0 (π / 2)] θ₀, θ ∈ Set.Ioo (θ₀ - δ) (θ₀ + δ) :=
    Filter.mem_of_superset
      (nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩))
      (fun θ hθ => hθ)
  have hmemIcc : ∀ θ ∈ Set.Ioo (θ₀ - δ) (θ₀ + δ), θ ∈ Set.Icc (θ₀ - δ) (θ₀ + δ) :=
    fun θ hθ => Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hF_meas : ∀ᶠ θ in 𝓝[Set.Ioo 0 (π / 2)] θ₀,
      AEStronglyMeasurable (fun z => F z θ) (volume.restrict (Ι a b)) := by
    refine hnbhd.mono fun θ hθ => ?_
    rw [Set.uIoc_of_le hab]
    have hslice : ContinuousOn (fun z : ℝ => F z θ) (Set.Ioc a b) :=
      hFB.comp' (continuousOn_id.prodMk continuousOn_const)
        (fun z hz => Set.mem_prod.mpr
          ⟨Set.mem_Icc.mpr ⟨le_of_lt hz.1, hz.2⟩, hmemIcc θ hθ⟩)
    exact hslice.aestronglyMeasurable measurableSet_Ioc
  have h_bound : ∀ᶠ θ in 𝓝[Set.Ioo 0 (π / 2)] θ₀,
      ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Ι a b → ‖F z θ‖ ≤ M := by
    refine hnbhd.mono fun θ hθ => ?_
    refine Filter.Eventually.of_forall fun z hz => ?_
    rw [Set.uIoc_of_le hab] at hz
    rw [Real.norm_eq_abs]
    exact hM (z, θ) (Set.mem_prod.mpr
      ⟨Set.mem_Icc.mpr ⟨le_of_lt hz.1, hz.2⟩, hmemIcc θ hθ⟩)
  have h_cont : ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Ι a b →
      ContinuousWithinAt (fun θ => F z θ) (Set.Ioo 0 (π / 2)) θ₀ := by
    refine Filter.Eventually.of_forall fun z hz => ?_
    rw [Set.uIoc_of_le hab] at hz
    have hzpos : 0 < z := lt_of_lt_of_le ha (le_of_lt hz.1)
    have hmem : (z, θ₀) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) :=
      Set.mem_prod.mpr ⟨hzpos, hθ₀⟩
    have hcontAt : ContinuousAt (fun p : ℝ × ℝ => F p.1 p.2) (z, θ₀) :=
      hF.continuousAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem)
    have : ContinuousAt (fun θ => F z θ) θ₀ :=
      hcontAt.comp (f := fun θ : ℝ => (z, θ)) (by fun_prop)
    exact this.continuousWithinAt
  exact intervalIntegral.continuousWithinAt_of_dominated_interval hF_meas h_bound
    intervalIntegrable_const h_cont

/-! ## The weighted cut-off factor `χ k z * w z ^ 2` -/

theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hw : ContinuousOn (Work.Spaces.w) (Set.Ioi 0) := by
    have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
    rw [h]
    exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  exact hw.pow 2

theorem continuousOn_cutweight {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K)
    (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => χ k p.1 * (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hχc : ContinuousOn (χ k) (Set.Ioi 0) := (hχ.sm k).continuousOn
  have hχQ : ContinuousOn (fun p : ℝ × ℝ => χ k p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hχc.comp' continuousOn_fst (fun p hp => (Set.mem_prod.mp hp).1)
  have hwQ : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    continuousOn_w_sq.comp' continuousOn_fst (fun p hp => (Set.mem_prod.mp hp).1)
  exact hχQ.mul hwQ

/-! ## The main statement -/

theorem continuousOn_mK {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K)
    (k : ℕ) {ψ : ℝ → ℝ → ℝ} (hψ : Work.FTS.EllipticEst.SmoothOpen ψ) :
    ContinuousOn (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
    ContinuousOn (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ * Work.Spaces.pth ψ z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
    ContinuousOn (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * (Work.Spaces.pth ψ z θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
    ContinuousOn (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ * Work.Spaces.pthIter 2 ψ z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  set Q : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) with hQdef
  have ha : 0 < Work.FTS.EllSol.PkgK5.cA k := Work.FTS.EllSol.PkgK5.cA_pos k
  have hab : Work.FTS.EllSol.PkgK5.cA k ≤ Work.FTS.EllSol.PkgK5.cB k :=
    Work.FTS.EllSol.PkgK5.cA_le_cB k
  -- the weighted cut-off factor
  have hχw : ContinuousOn (fun p : ℝ × ℝ => χ k p.1 * (Work.Spaces.w p.1) ^ 2) Q :=
    continuousOn_cutweight hχ k
  -- the smooth factors
  have hψQ : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) Q := hψ.continuousOn
  have hψpthQ : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth ψ p.1 p.2) Q :=
    hψ.pth.continuousOn
  have hψ2Q : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 ψ p.1 p.2) Q := by
    have h : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 ψ) := by
      have := hψ.pth.pth
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using this
    exact h.continuousOn
  -- the four joint-continuity facts, in the exact shapes appearing in the statement
  have J1 : ContinuousOn (fun p : ℝ × ℝ =>
      χ k p.1 * (Work.Spaces.w p.1) ^ 2 * ψ p.1 p.2 ^ 2) Q :=
    hχw.mul (hψQ.pow 2)
  have J2 : ContinuousOn (fun p : ℝ × ℝ =>
      χ k p.1 * (Work.Spaces.w p.1) ^ 2 * ψ p.1 p.2 * Work.Spaces.pth ψ p.1 p.2) Q :=
    (hχw.mul hψQ).mul hψpthQ
  have J3 : ContinuousOn (fun p : ℝ × ℝ =>
      χ k p.1 * (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.pth ψ p.1 p.2) ^ 2) Q :=
    hχw.mul (hψpthQ.pow 2)
  have J4 : ContinuousOn (fun p : ℝ × ℝ =>
      χ k p.1 * (Work.Spaces.w p.1) ^ 2 * ψ p.1 p.2 * Work.Spaces.pthIter 2 ψ p.1 p.2) Q :=
    (hχw.mul hψQ).mul hψ2Q
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun θ₀ hθ₀ =>
      continuousWithinAt_intervalIntegral_of_continuousOn ha hab J1 hθ₀
  · exact fun θ₀ hθ₀ =>
      continuousWithinAt_intervalIntegral_of_continuousOn ha hab J2 hθ₀
  · exact fun θ₀ hθ₀ =>
      continuousWithinAt_intervalIntegral_of_continuousOn ha hab J3 hθ₀
  · exact fun θ₀ hθ₀ =>
      continuousWithinAt_intervalIntegral_of_continuousOn ha hab J4 hθ₀

end Work.FTS.EllSol.PkgK5.InterpTrace
