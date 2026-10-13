import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Honesty.derivWithinEndpointBounds
import Submission.Work.FTS.PhiStar.Honesty.GWeightBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open scoped Real Topology
open MeasureTheory Filter

/-- **`Lzero1` is bounded on the open interval, for a `C²` slice vanishing at both ends.**

`Lzero1 v = -v'' + (tan θ · v)' - 6v` (defined in `Submission/Work/FTS/EllipticEst/StraightDefs.lean`).
For `v` of class `C²` (within) the closed interval `[0, π/2]` with `v 0 = v (π/2) = 0`, the two
singular pieces `v/cos²θ` and `tan θ · v'` of `Lzero1 v` cancel: `Lzero1 v` is *bounded* on
`(0, π/2)`.  (Consumers need exactly this to know that `(Lzero1 v)² cos θ` is integrable on `Iθ`
and that `Lzero1 v` is an honest, non-junk Bochner integrand; without the vanishing at the
endpoints it is false, e.g. `v ≡ 1` gives `Lzero1 v θ = 1/cos²θ`.)

*Route (for the prover).*  Let `s := Set.Icc 0 (Real.pi/2)`, `u₁ := derivWithin v s`,
`u₂ := derivWithin u₁ s`.  `ContDiffOn.derivWithin` (twice, with `uniqueDiffOn_Icc`) gives `u₂`
continuous on the compact `s`, hence `∃ B, ∀ θ ∈ s, |u₂ θ| ≤ B`; and on `Ioo 0 (π/2)` one has
`deriv v = u₁` and `deriv (deriv v) = u₂` (`derivWithin_of_mem_nhds`, since `s ∈ 𝓝 θ`).
Put `a := u₁ (π/2)`.  From the FTC on `[θ, π/2]` inside `Ioo` (`u₁` is differentiable on the open
interval with derivative `u₂`, and `u₁` is continuous on `Icc`), `|u₁ θ - a| ≤ B (π/2 - θ)`; a second
FTC gives `|v θ + a cos θ| ≤ (B/2 + |a|/6) cos²θ` (using `|cos θ - (π/2 - θ)| ≤ (π/2 - θ)³/6` and
`(π/2 - θ) ≤ (π/2) cos θ`, which is `Real.mul_le_sin` for `s = π/2 - θ`).  With
`G := v + sin θ cos θ v'`, one has `sec²θ v θ + tan θ v'θ = G/cos²θ` and the elementary
`G = sin θ cos θ (u₁ θ - a) + (v θ + a cos θ) - a cos³θ/(1 + sin θ)` (using `1 - sin θ = cos²θ/(1 + sin θ)`),
so `|G| ≤ (B + B/2 + |a|/6 + |a|) cos²θ` and `|sec²θ v θ + tan θ v'θ|` is bounded.  Finally
`v` is bounded on `Icc` (`hv.continuousOn` + compactness), so
`Lzero1 v = -u₂ + G/cos² - 6v` is bounded on `Ioo`.  (The mean value inequality
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` on the convex set `Icc` is an alternative
to the first FTC.) -/
theorem lzero1_bdd_on_Ioo {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2)))
    (h0 : v 0 = 0) (h1 : v (Real.pi / 2) = 0) :
    ∃ M : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.Lzero1 v θ| ≤ M := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  let s : Set ℝ := Set.Icc 0 (Real.pi / 2)
  let u₁ : ℝ → ℝ := derivWithin v s
  let u₂ : ℝ → ℝ := derivWithin u₁ s
  have hu1 : ContDiffOn ℝ 1 u₁ s :=
    hv.derivWithin (uniqueDiffOn_Icc hpi) (m := 1) (by norm_num)
  have hu2 : ContDiffOn ℝ 0 u₂ s :=
    hu1.derivWithin (uniqueDiffOn_Icc hpi) (m := 0) (by norm_num)
  have hu1diff : DifferentiableOn ℝ u₁ s := hu1.differentiableOn (by norm_num)
  have hu2cont : ContinuousOn u₂ s := hu2.continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hu2cont
  have hB' : ∀ x ∈ s, |u₂ x| ≤ B := fun x hx => by
    simpa only [Real.norm_eq_abs] using hB x hx
  have hs0 : (0 : ℝ) ∈ s := by simp only [s]; exact ⟨le_rfl, hpi.le⟩
  have hs1 : Real.pi / 2 ∈ s := by simp only [s]; exact ⟨hpi.le, le_rfl⟩
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB' 0 hs0)
  let a₀ : ℝ := u₁ (Real.pi / 2)
  obtain ⟨hend1, hend2⟩ :=
    derivWithinEndpointBounds (f := v) (a := 0) (b := Real.pi / 2) (B := B) hpi hv hB'
  refine ⟨B + (B * Real.pi ^ 2 / 8 + |a₀| * Real.pi ^ 3 / 12 + B * (Real.pi / 2))
      + 6 * ((B / 2) * (Real.pi / 2) ^ 2 + |a₀| * (Real.pi / 2)), ?_⟩
  intro θ hθ
  have hθs : θ ∈ s := ⟨hθ.1.le, hθ.2.le⟩
  have hnhds : s ∈ 𝓝 θ := Icc_mem_nhds hθ.1 hθ.2
  have hcpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hc2pos : 0 < Real.cos θ ^ 2 := pow_pos hcpos 2
  have hfirst : |u₁ θ - a₀| ≤ B * (Real.pi / 2 - θ) := hend1 θ hθ
  have hsecond : |v θ + a₀ * (Real.pi / 2 - θ)| ≤ B / 2 * (Real.pi / 2 - θ) ^ 2 := by
    have h := hend2 θ hθ
    rw [h1, sub_zero] at h
    exact h
  have hG := GWeightBound (v := v) (dv := u₁) (a := a₀) (B := B) hB0 hθ.1 hθ.2 hsecond hfirst
  -- identification of the two derivatives of `v` on the open interval
  have hdv : deriv v θ = u₁ θ := (derivWithin_of_mem_nhds hnhds).symm
  have hddv : deriv (fun t => deriv v t) θ = u₂ θ := by
    have hEv : deriv v =ᶠ[𝓝 θ] u₁ := by
      obtain ⟨t, hts, htopen, hθt⟩ := mem_nhds_iff.mp hnhds
      filter_upwards [htopen.mem_nhds hθt] with x hx
      exact (derivWithin_of_mem_nhds (mem_of_superset (htopen.mem_nhds hx) hts)).symm
    exact (hEv.deriv_eq).trans (derivWithin_of_mem_nhds hnhds).symm
  have htan : deriv (fun t => Real.tan t * v t) θ
      = v θ / Real.cos θ ^ 2 + Real.tan θ * u₁ θ := by
    have hvderiv : HasDerivAt v (u₁ θ) θ :=
      (((hv.differentiableOn (by norm_num)) θ hθs).hasDerivWithinAt).hasDerivAt hnhds
    have h := (Real.hasDerivAt_tan hcpos.ne').mul hvderiv
    change deriv (Real.tan * v) θ = v θ / Real.cos θ ^ 2 + Real.tan θ * u₁ θ
    rw [h.deriv]
    ring
  have hLz : Work.FTS.EllipticEst.Lzero1 v θ
      = -u₂ θ + (v θ + Real.sin θ * Real.cos θ * u₁ θ) / Real.cos θ ^ 2 - 6 * v θ := by
    have htanid : Real.tan θ * u₁ θ
        = (Real.sin θ * Real.cos θ * u₁ θ) / Real.cos θ ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
    simp only [Work.FTS.EllipticEst.Lzero1]
    rw [show deriv (fun t => deriv v t) θ = u₂ θ from hddv, htan, htanid, ← add_div]
  -- auxiliary estimates
  have hcenter : |(v θ + Real.sin θ * Real.cos θ * u₁ θ) / Real.cos θ ^ 2|
      ≤ B * Real.pi ^ 2 / 8 + |a₀| * Real.pi ^ 3 / 12 + B * (Real.pi / 2) := by
    rw [abs_div, abs_of_pos hc2pos, div_le_iff₀ hc2pos]
    exact hG
  have hvbound : |v θ| ≤ (B / 2) * (Real.pi / 2) ^ 2 + |a₀| * (Real.pi / 2) := by
    have hδ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have hδle : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith [hθ.1]
    have hsq : (Real.pi / 2 - θ) ^ 2 ≤ (Real.pi / 2) ^ 2 := by nlinarith
    calc |v θ| = |(v θ + a₀ * (Real.pi / 2 - θ)) - a₀ * (Real.pi / 2 - θ)| := by
          congr 1; ring
      _ ≤ |v θ + a₀ * (Real.pi / 2 - θ)| + |a₀ * (Real.pi / 2 - θ)| := by
          simpa using abs_sub_le (v θ + a₀ * (Real.pi / 2 - θ)) 0 (a₀ * (Real.pi / 2 - θ))
      _ ≤ (B / 2) * (Real.pi / 2 - θ) ^ 2 + |a₀| * (Real.pi / 2 - θ) := by
          have h2 : |a₀ * (Real.pi / 2 - θ)| = |a₀| * (Real.pi / 2 - θ) := by
            rw [abs_mul, abs_of_nonneg hδ0]
          rw [h2]
          exact add_le_add hsecond le_rfl
      _ ≤ (B / 2) * (Real.pi / 2) ^ 2 + |a₀| * (Real.pi / 2) := by
          have h1' : (B / 2) * (Real.pi / 2 - θ) ^ 2 ≤ (B / 2) * (Real.pi / 2) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by linarith)
          have h2' : |a₀| * (Real.pi / 2 - θ) ≤ |a₀| * (Real.pi / 2) :=
            mul_le_mul_of_nonneg_left hδle (abs_nonneg _)
          linarith
  have htri : |Work.FTS.EllipticEst.Lzero1 v θ|
      ≤ |u₂ θ| + |(v θ + Real.sin θ * Real.cos θ * u₁ θ) / Real.cos θ ^ 2| + 6 * |v θ| := by
    have h6 : |6 * v θ| = 6 * |v θ| := by rw [abs_mul]; norm_num
    have hab : |(-u₂ θ) + (v θ + Real.sin θ * Real.cos θ * u₁ θ) / Real.cos θ ^ 2|
        ≤ |u₂ θ| + |(v θ + Real.sin θ * Real.cos θ * u₁ θ) / Real.cos θ ^ 2| := by
      have h := abs_add_le (-u₂ θ) ((v θ + Real.sin θ * Real.cos θ * u₁ θ) / Real.cos θ ^ 2)
      rwa [abs_neg] at h
    calc |Work.FTS.EllipticEst.Lzero1 v θ|
        = |(-u₂ θ + (v θ + Real.sin θ * Real.cos θ * u₁ θ) / Real.cos θ ^ 2) - 6 * v θ| := by
          rw [hLz]
      _ ≤ |(-u₂ θ + (v θ + Real.sin θ * Real.cos θ * u₁ θ) / Real.cos θ ^ 2) - 0|
            + |0 - 6 * v θ| := abs_sub_le _ _ _
      _ = |(-u₂ θ) + (v θ + Real.sin θ * Real.cos θ * u₁ θ) / Real.cos θ ^ 2|
            + |6 * v θ| := by
          rw [sub_zero, zero_sub, abs_neg]
      _ = |(-u₂ θ) + (v θ + Real.sin θ * Real.cos θ * u₁ θ) / Real.cos θ ^ 2|
            + 6 * |v θ| := by rw [h6]
      _ ≤ |u₂ θ| + |(v θ + Real.sin θ * Real.cos θ * u₁ θ) / Real.cos θ ^ 2| + 6 * |v θ| := by
          linarith [hab]
  calc |Work.FTS.EllipticEst.Lzero1 v θ|
      ≤ |u₂ θ| + |(v θ + Real.sin θ * Real.cos θ * u₁ θ) / Real.cos θ ^ 2| + 6 * |v θ| := htri
    _ ≤ B + (B * Real.pi ^ 2 / 8 + |a₀| * Real.pi ^ 3 / 12 + B * (Real.pi / 2))
          + 6 * ((B / 2) * (Real.pi / 2) ^ 2 + |a₀| * (Real.pi / 2)) := by
        linarith [hB' θ hθs, hcenter, hvbound]

end Work.FTS.PhiStar.Honesty
