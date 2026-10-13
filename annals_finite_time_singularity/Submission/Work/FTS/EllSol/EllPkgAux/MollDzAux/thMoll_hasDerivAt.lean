import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDzAux

open scoped Real Topology
open MeasureTheory Set Filter

/-- `sKer ε` is smooth, hence its derivative `sKerd ε` is continuous. -/
theorem continuous_sKerd (ε : ℝ) : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd ε) := by
  have h : ContDiff ℝ 1 (Work.FTS.EllSol.PkgK5.K5c.sKer ε) :=
    Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)
  simpa [Work.FTS.EllSol.EllPkgAux.sKerd] using h.continuous_deriv_one

/-- The derivative kernel `sKerd ε = (sKer ε)'` vanishes outside the support `[-ε, ε]` of
`sKer ε`. -/
theorem sKerd_eq_zero_of_lt_abs {ε t : ℝ} (hε : 0 < ε) (ht : ε < |t|) :
    Work.FTS.EllSol.EllPkgAux.sKerd ε t = 0 := by
  have hev : Work.FTS.EllSol.PkgK5.K5c.sKer ε =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    show ∀ᶠ y in 𝓝 t, Work.FTS.EllSol.PkgK5.K5c.sKer ε y = 0
    rw [Metric.eventually_nhds_iff]
    refine ⟨(|t| - ε) / 2, by linarith, ?_⟩
    intro y hy
    have h1 : |y - t| < (|t| - ε) / 2 := by simpa [Real.dist_eq] using hy
    have h2 : ε < |y| := by
      have h3 : |t| ≤ |y| + |y - t| := by
        simpa [abs_sub_comm] using abs_sub_le y 0 (y - t)
      linarith
    exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε (le_of_lt h2)
  rw [Work.FTS.EllSol.EllPkgAux.sKerd, hev.deriv_eq, deriv_const]

theorem thMoll_hasDerivAt {Q : ℝ → ℝ} (hQ : ContinuousOn Q (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    {ε M θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hM : ∀ x : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd ε x| ≤ M)
    (hθ : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4)) :
    HasDerivAt (fun θ' : ℝ => ∫ s : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s) * Q s)
      (∫ s : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) * Q s) θ := by
  obtain ⟨hθ1, hθ2⟩ := hθ
  -- The interval `[a, b]` on which everything happens.
  set a : ℝ := θ - 5 / 8 with ha
  set b : ℝ := θ + 5 / 8 with hb
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have ha1 : -1 < a := by rw [ha]; linarith
  have hb1 : b < Real.pi / 2 + 1 := by rw [hb]; linarith
  have hsubIoc : Set.Ioc a b ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsubuIoc : Set.uIoc a b ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
    rw [uIoc_of_le hab]; exact hsubIoc
  have hsubIcc : Set.Icc a b ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hQ_Icc : ContinuousOn Q (Set.Icc a b) := hQ.mono hsubIcc
  have hQ_uIoc : ContinuousOn Q (Set.uIoc a b) := hQ.mono hsubuIoc
  have hsm : Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer ε) :=
    (Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).continuous
  have hder : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd ε) := continuous_sKerd ε
  -- The main differentiation under the integral sign, on the fixed interval `[a, b]`.
  have key : HasDerivAt
      (fun x : ℝ => ∫ t in a..b, Work.FTS.EllSol.PkgK5.K5c.sKer ε (x - t) * Q t)
      (∫ t in a..b, Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - t) * Q t) θ := by
    have hF_int : IntervalIntegrable
        (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - t) * Q t) volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab]
      have h1 : ContinuousOn (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - t))
          (Set.Icc a b) :=
        (hsm.comp (continuous_const.sub continuous_id)).continuousOn
      exact h1.mul hQ_Icc
    have hF'_meas : AEStronglyMeasurable
        (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - t) * Q t)
        (volume.restrict (Set.uIoc a b)) :=
      (((hder.comp (continuous_const.sub continuous_id)).continuousOn).mul hQ_uIoc).aestronglyMeasurable
        measurableSet_uIoc
    have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → ∀ x ∈ Set.Ioo (θ - 1 / 8) (θ + 1 / 8),
        ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (x - t) * Q t‖ ≤ M * |Q t| := by
      refine Eventually.of_forall fun t _ x _ => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM (x - t)) (abs_nonneg _)
    have hbound_int : IntervalIntegrable (fun t : ℝ => M * |Q t|) volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab]
      exact hQ_Icc.abs.const_mul M
    have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → ∀ x ∈ Set.Ioo (θ - 1 / 8) (θ + 1 / 8),
        HasDerivAt (fun y : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (y - t) * Q t)
          (Work.FTS.EllSol.EllPkgAux.sKerd ε (x - t) * Q t) x := by
      refine Eventually.of_forall fun t _ x _ => ?_
      have hderiv : HasDerivAt (Work.FTS.EllSol.PkgK5.K5c.sKer ε)
          (deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) (x - t)) (x - t) :=
        (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one) (x - t)).hasDerivAt
      have hcomp : HasDerivAt (fun y : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (y - t))
          (deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) (x - t)) x := by
        have := hderiv.comp x ((hasDerivAt_id x).sub_const t)
        simpa [Function.comp_def] using this
      have := hcomp.mul_const (Q t)
      simpa [Work.FTS.EllSol.EllPkgAux.sKerd] using this
    have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := a) (b := b)
      (bound := fun t : ℝ => M * |Q t|)
      (F := fun x t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (x - t) * Q t)
      (F' := fun x t : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (x - t) * Q t)
      (x₀ := θ) (s := Set.Ioo (θ - 1 / 8) (θ + 1 / 8))
      (Ioo_mem_nhds (by linarith) (by linarith))
      (by
        refine Eventually.of_forall fun x => ?_
        exact (((hsm.comp (continuous_const.sub continuous_id)).continuousOn).mul hQ_uIoc).aestronglyMeasurable
          measurableSet_uIoc)
      hF_int hF'_meas hbound hbound_int hdiff
    exact hmain.2
  -- Transfer the function to the integral over `ℝ` …
  have hcong1 : (fun θ' : ℝ => ∫ s : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s) * Q s)
      =ᶠ[𝓝 θ] (fun θ' : ℝ => ∫ s in a..b, Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s) * Q s) := by
    filter_upwards [Ioo_mem_nhds (show θ - 1 / 8 < θ by linarith)
      (show θ < θ + 1 / 8 by linarith)] with θ' hθ'
    have hzero : ∀ s : ℝ, s ∉ Set.Ioc a b →
        Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s) * Q s = 0 := by
      intro s hs
      have hs' : s ≤ a ∨ b < s := by
        by_cases h : s ≤ a
        · exact Or.inl h
        · exact Or.inr (by
            by_contra hb'
            exact hs ⟨not_le.mp h, not_lt.mp hb'⟩)
      rcases hs' with h | h
      · have hle : ε ≤ |θ' - s| := by
          have h2 : (1 / 2 : ℝ) < θ' - s := by linarith [h, hθ'.1, ha]
          have h3 : θ' - s ≤ |θ' - s| := le_abs_self _
          linarith
        rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε0 hle, zero_mul]
      · have hle : ε ≤ |θ' - s| := by
          have h2 : (1 / 2 : ℝ) < s - θ' := by linarith [h, hθ'.2, hb]
          have h3 : s - θ' ≤ |θ' - s| := by rw [abs_sub_comm]; exact le_abs_self _
          linarith
        rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε0 hle, zero_mul]
    rw [intervalIntegral.integral_of_le hab]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  -- … and the value of the derivative.
  have hcong2 : (∫ s in a..b, Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) * Q s)
      = ∫ s : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) * Q s := by
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
    have hs' : s ≤ a ∨ b < s := by
      by_cases h : s ≤ a
      · exact Or.inl h
      · exact Or.inr (by
          by_contra hb'
          exact hs ⟨not_le.mp h, not_lt.mp hb'⟩)
    rcases hs' with h | h
    · have h1 : ε < θ - s := by linarith [h, ha, hε1]
      have h2 : ε < |θ - s| := lt_of_lt_of_le h1 (le_abs_self _)
      rw [sKerd_eq_zero_of_lt_abs hε0 h2, zero_mul]
    · have h1 : ε < s - θ := by linarith [h, hb, hε1]
      have h2 : ε < |θ - s| := by
        have h3 : s - θ ≤ |θ - s| := by rw [abs_sub_comm]; exact le_abs_self _
        linarith
      rw [sKerd_eq_zero_of_lt_abs hε0 h2, zero_mul]
  have hfin : HasDerivAt (fun θ' : ℝ => ∫ s : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s) * Q s)
      (∫ s in a..b, Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) * Q s) θ :=
    (hcong1.hasDerivAt_iff).mpr key
  rwa [hcong2] at hfin

end Work.FTS.EllSol.EllPkgAux.MollDzAux
