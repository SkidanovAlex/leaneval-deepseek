/-
# `mK_hasDerivAt` — differentiation under the `z`-integral of the cut-off mass `m_k`

`m_k(θ) = ∫_{cA k}^{cB k} χ_k(z) w(z)² ψ(z,θ)² dz` is `C¹` in `θ` with

`m_k'(θ) = 2 ∫_{cA k}^{cB k} χ_k(z) w(z)² ψ(z,θ) ∂_θψ(z,θ) dz`.

The proof is the parametric-integral theorem
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`: the integrand is only
supported on the compact window `[cA k, cB k] ⊂ (0,∞)`, and on a compact box
`[cA k, cB k] × [θ₀-ε, θ₀+ε] ⊂ (0,∞) × (0,π/2)` the `θ`-derivative
`χ_k w² · 2 ψ ∂_θψ` is continuous (hence bounded), which supplies the dominating function
(the constant bound `C`).  The pointwise angular derivative uses
`SmoothOpen.curry_θ` (smoothness of the `θ`-slice at positive `z`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.EllSol.PkgK5.InterpTraceCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.InterpTrace

set_option maxHeartbeats 800000

theorem mK_hasDerivAt {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {ψ : ℝ → ℝ → ℝ}
    (hψ : Work.FTS.EllipticEst.SmoothOpen ψ)
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2)
      (2 * ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ₀ * Work.Spaces.pth ψ z θ₀) θ₀ := by
  let a : ℝ := Work.FTS.EllSol.PkgK5.cA k
  let b : ℝ := Work.FTS.EllSol.PkgK5.cB k
  change HasDerivAt (fun θ => ∫ z in a..b, χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2)
      (2 * ∫ z in a..b, χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ₀ * Work.Spaces.pth ψ z θ₀) θ₀
  have ha : 0 < a := Work.FTS.EllSol.PkgK5.cA_pos k
  have hab : a ≤ b := Work.FTS.EllSol.PkgK5.cA_le_cB k
  -- a small symmetric neighbourhood `s` of `θ₀` inside `(0,π/2)`
  let ε : ℝ := min (θ₀ / 2) ((Real.pi / 2 - θ₀) / 2)
  have hεpos : 0 < ε := lt_min (by linarith [hθ₀.1]) (by linarith [hθ₀.2, Real.pi_pos])
  have hεle1 : ε ≤ θ₀ / 2 := min_le_left _ _
  have hεle2 : ε ≤ (Real.pi / 2 - θ₀) / 2 := min_le_right _ _
  have hθ₀mε : 0 < θ₀ - ε := by linarith
  have hθ₀pε : θ₀ + ε < Real.pi / 2 := by linarith
  let s : Set ℝ := Set.Icc (θ₀ - ε) (θ₀ + ε)
  have hs : s ∈ 𝓝 θ₀ := Icc_mem_nhds (by linarith) (by linarith)
  have hθ₀s : θ₀ ∈ s := ⟨by linarith, by linarith⟩
  have hs_sub : s ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have huIcc_sub : Set.uIcc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro z hz
    rcases Set.mem_uIcc.mp hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact lt_of_lt_of_le ha h1
    · exact lt_of_lt_of_le ha (le_trans hab h1)
  have hKQ0 : Set.uIcc a b ×ˢ s ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro ⟨z, x⟩ ⟨hz, hx⟩
    exact ⟨huIcc_sub hz, hs_sub hx⟩
  -- the compact box on which the derivative integrand is bounded
  have hK : IsCompact (Set.uIcc a b ×ˢ s) := isCompact_uIcc.prod isCompact_Icc
  have hwc : ContinuousOn Work.Spaces.w (Set.Ioi (0:ℝ)) := by
    have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
    rw [h]
    exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
      ((continuous_id.pow 2).continuousOn) (fun z hz => by
        simp only [Set.mem_Ioi] at hz
        positivity)
  have hχK : ContinuousOn (fun p : ℝ × ℝ => χ k p.1) (Set.uIcc a b ×ˢ s) :=
    ((hχ.sm k).continuousOn).comp continuousOn_fst (fun p hp => huIcc_sub hp.1)
  have hwK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) (Set.uIcc a b ×ˢ s) :=
    hwc.comp continuousOn_fst (fun p hp => huIcc_sub hp.1)
  have hψK : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) (Set.uIcc a b ×ˢ s) :=
    hψ.continuousOn.mono hKQ0
  have hpthK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth ψ p.1 p.2) (Set.uIcc a b ×ˢ s) :=
    (hψ.pth).continuousOn.mono hKQ0
  have hG : ContinuousOn (fun p : ℝ × ℝ =>
      χ k p.1 * (Work.Spaces.w p.1) ^ 2 * (2 * ψ p.1 p.2 * Work.Spaces.pth ψ p.1 p.2))
      (Set.uIcc a b ×ˢ s) :=
    (hχK.mul (hwK.pow 2)).mul ((continuousOn_const.mul hψK).mul hpthK)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG
  -- the parametric family and its formal `θ`-derivative
  let F : ℝ → ℝ → ℝ := fun θ z => χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2
  let F' : ℝ → ℝ → ℝ := fun θ z =>
    χ k z * (Work.Spaces.w z) ^ 2 * (2 * ψ z θ * Work.Spaces.pth ψ z θ)
  have hslice_cont : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      ContinuousOn (fun z => F x z) (Set.uIcc a b) := by
    intro x hx
    show ContinuousOn (fun z => χ k z * (Work.Spaces.w z) ^ 2 * ψ z x ^ 2) (Set.uIcc a b)
    have hχ1 : ContinuousOn (χ k) (Set.uIcc a b) := ((hχ.sm k).continuousOn).mono huIcc_sub
    have hw1 : ContinuousOn Work.Spaces.w (Set.uIcc a b) := hwc.mono huIcc_sub
    have hψx : ContinuousOn (fun z => ψ z x) (Set.uIcc a b) :=
      ((hψ.curry_z hx).continuousOn).mono huIcc_sub
    exact (hχ1.mul (hw1.pow 2)).mul (hψx.pow 2)
  have hF_meas : ∀ᶠ x in 𝓝 θ₀,
      AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc a b)) := by
    filter_upwards [hs] with x hx
    exact ((hslice_cont x (hs_sub hx)).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  have hF_int : IntervalIntegrable (F θ₀) volume a b :=
    (hslice_cont θ₀ hθ₀).intervalIntegrable
  have hpthθ₀ : ContinuousOn (fun z => Work.Spaces.pth ψ z θ₀) (Set.uIcc a b) :=
    ((hψ.pth).curry_z hθ₀).continuousOn.mono huIcc_sub
  have hF'_meas : AEStronglyMeasurable (F' θ₀) (volume.restrict (Set.uIoc a b)) := by
    have hχ1 : ContinuousOn (χ k) (Set.uIcc a b) := ((hχ.sm k).continuousOn).mono huIcc_sub
    have hw1 : ContinuousOn Work.Spaces.w (Set.uIcc a b) := hwc.mono huIcc_sub
    have hψθ₀ : ContinuousOn (fun z => ψ z θ₀) (Set.uIcc a b) :=
      ((hψ.curry_z hθ₀).continuousOn).mono huIcc_sub
    have hcont : ContinuousOn (fun z => F' θ₀ z) (Set.uIcc a b) := by
      show ContinuousOn (fun z => χ k z * (Work.Spaces.w z) ^ 2 *
        (2 * ψ z θ₀ * Work.Spaces.pth ψ z θ₀)) (Set.uIcc a b)
      exact (hχ1.mul (hw1.pow 2)).mul ((continuousOn_const.mul hψθ₀).mul hpthθ₀)
    exact (hcont.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Set.uIoc a b →
      ∀ x ∈ s, ‖F' x z‖ ≤ (fun _ : ℝ => C) z := by
    refine Filter.Eventually.of_forall fun z hz x hx => ?_
    have hzK : z ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hz
    have h := hC (z, x) ⟨hzK, hx⟩
    simpa [F'] using h
  have h_diff : ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Set.uIoc a b →
      ∀ x ∈ s, HasDerivAt (fun x => F x z) (F' x z) x := by
    refine Filter.Eventually.of_forall fun z hz x hx => ?_
    have hzpos : 0 < z := huIcc_sub (Set.uIoc_subset_uIcc hz)
    have hxIoo : x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := hs_sub hx
    have hd : HasDerivAt (fun θ => ψ z θ) (Work.Spaces.pth ψ z x) x := by
      have hcda : ContDiffAt ℝ Work.Stability.smoothOrder (fun θ => ψ z θ) x :=
        (hψ.curry_θ hzpos).contDiffAt (isOpen_Ioo.mem_nhds hxIoo)
      simpa only [Work.Spaces.pth] using
        (hcda.differentiableAt (by simp [Work.Stability.smoothOrder])).hasDerivAt
    have h1 : HasDerivAt (fun θ => ψ z θ ^ 2) (2 * ψ z x * Work.Spaces.pth ψ z x) x := by
      have hp : HasDerivAt ((fun θ => ψ z θ) ^ 2)
          (↑2 * ψ z x ^ (2 - 1) * Work.Spaces.pth ψ z x) x := hd.pow 2
      have heq : (fun θ => ψ z θ ^ 2) = ((fun θ => ψ z θ) ^ 2) := by
        funext θ; simp
      rw [heq]
      convert hp using 1
      ring
    have h2 : HasDerivAt (fun θ => (χ k z * (Work.Spaces.w z) ^ 2) * ψ z θ ^ 2)
        ((χ k z * (Work.Spaces.w z) ^ 2) * (2 * ψ z x * Work.Spaces.pth ψ z x)) x :=
      h1.const_mul (χ k z * (Work.Spaces.w z) ^ 2)
    show HasDerivAt (fun θ => χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2)
        (χ k z * (Work.Spaces.w z) ^ 2 * (2 * ψ z x * Work.Spaces.pth ψ z x)) x
    exact h2
  obtain ⟨-, hmain⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (F := F) (F' := F') (bound := fun _ : ℝ => C)
    (x₀ := θ₀) (s := s)
    hs hF_meas hF_int hF'_meas h_bound (intervalIntegrable_const (c := C)) h_diff
  have hInt : (∫ z in a..b, F' θ₀ z)
      = 2 * ∫ z in a..b, χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ₀ * Work.Spaces.pth ψ z θ₀ := by
    have h2 : (2:ℝ) * ∫ z in a..b,
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ₀ * Work.Spaces.pth ψ z θ₀
        = ∫ z in a..b,
            2 * (χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ₀ * Work.Spaces.pth ψ z θ₀) :=
      (intervalIntegral.integral_const_mul (μ := volume) (2:ℝ)
        (fun z => χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ₀ * Work.Spaces.pth ψ z θ₀)).symm
    rw [h2]
    refine intervalIntegral.integral_congr fun z hz => ?_
    simp only [F']
    ring
  rw [hInt] at hmain
  exact hmain

end Work.FTS.EllSol.PkgK5.InterpTrace
