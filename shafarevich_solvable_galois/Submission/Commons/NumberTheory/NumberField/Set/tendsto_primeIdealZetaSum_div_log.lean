import Mathlib.Analysis.Asymptotics.TVS
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Submission.Commons.NumberTheory.NumberField.Set.isBigO_primeIdealZetaSum_sub_log
import Submission.Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_univ_nhdsGT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Set

open Filter IsDedekindDomain Topology Set Asymptotics
open scoped BigOperators

/-- `log (1/(s-1)) → +∞` as `s → 1⁺`. -/
private lemma tendsto_log_one_div_sub_one_nhdsGT :
    Filter.Tendsto (fun s : ℝ => Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
  have h1a : Filter.Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
    ((continuous_id.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds).sub_const 1
  have h1b : Filter.Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using h1a
  have h1 : Filter.Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h1b, by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_Ioi] at hs ⊢
      linarith⟩
  have h2 : Filter.Tendsto (fun s : ℝ => (s - 1)⁻¹) (𝓝[>] (1 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp h1
  have h3 : Filter.Tendsto (fun s : ℝ => Real.log ((s - 1)⁻¹)) (𝓝[>] (1 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp h2
  refine h3.congr' ?_
  filter_upwards with s
  rw [one_div]

/-- If `f - g` is bounded and `g → +∞`, then `(f - g)/g → 0`. -/
private lemma tendsto_sub_div_self_of_isBigO_one {f g : ℝ → ℝ}
    (h : (fun s : ℝ => f s - g s) =O[𝓝[>] (1 : ℝ)] (fun _ => (1 : ℝ)))
    (hg : Filter.Tendsto g (𝓝[>] (1 : ℝ)) atTop) :
    Filter.Tendsto (fun s : ℝ => (f s - g s) / g s) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨c, hc⟩ := h.bound
  have hcb : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ‖f s - g s‖ ≤ max c 0 := by
    filter_upwards [hc] with s hs
    calc ‖f s - g s‖ ≤ c * ‖(1 : ℝ)‖ := hs
      _ = c := by simp
      _ ≤ max c 0 := le_max_left c 0
  have hginv : Filter.Tendsto (fun s : ℝ => max c 0 * (g s)⁻¹) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have h0 := hg.inv_tendsto_atTop.const_mul (max c 0)
    simpa using h0
  refine squeeze_zero' ?_ ?_ hginv
  · filter_upwards with s
    exact norm_nonneg _
  · filter_upwards [hcb, hg.eventually (eventually_gt_atTop (0 : ℝ))] with s hbs hpos
    have hbs' : |f s - g s| ≤ max c 0 := by rwa [Real.norm_eq_abs] at hbs
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos]
    exact le_trans (div_le_div_of_nonneg_right hbs' (le_of_lt hpos))
      (le_of_eq (div_eq_mul_inv _ _))

theorem tendsto_primeIdealZetaSum_div_log {K : Type*} [Field K] [NumberField K]
    {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {δ : ℝ}
    (hS : NumberField.Set.HasDirichletDensity S δ) :
    Filter.Tendsto (fun s : ℝ => NumberField.Set.primeIdealZetaSum S s / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 δ) := by
  have hAB : Filter.Tendsto (fun s : ℝ =>
      NumberField.Set.primeIdealZetaSum S s /
        NumberField.Set.primeIdealZetaSum
          (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)
      (𝓝[>] (1 : ℝ)) (𝓝 δ) := hS
  have hBL : (fun s : ℝ =>
      NumberField.Set.primeIdealZetaSum
          (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s
        - Real.log (1 / (s - 1))) =O[𝓝[>] (1 : ℝ)] (fun _ : ℝ => (1 : ℝ)) :=
    isBigO_primeIdealZetaSum_sub_log K
  have hBtop : Filter.Tendsto (fun s : ℝ =>
      NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)
      (𝓝[>] (1 : ℝ)) atTop := tendsto_primeIdealZetaSum_univ_nhdsGT K
  have hLtop : Filter.Tendsto (fun s : ℝ => Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop :=
    tendsto_log_one_div_sub_one_nhdsGT
  have hquot : Filter.Tendsto (fun s : ℝ =>
      NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s
      / Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    have hstep := tendsto_sub_div_self_of_isBigO_one hBL hLtop
    have h1 : Filter.Tendsto (fun s : ℝ =>
        (NumberField.Set.primeIdealZetaSum
            (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s
          - Real.log (1 / (s - 1))) / Real.log (1 / (s - 1)) + 1)
        (𝓝[>] (1 : ℝ)) (𝓝 1) := by
      have := hstep.add (tendsto_const_nhds (x := (1 : ℝ)) (f := 𝓝[>] (1 : ℝ)))
      simpa using this
    refine h1.congr' ?_
    filter_upwards [hLtop.eventually (eventually_ne_atTop 0)] with s hne
    field_simp
    ring
  have hmul : Filter.Tendsto (fun s : ℝ =>
      (NumberField.Set.primeIdealZetaSum S s /
          NumberField.Set.primeIdealZetaSum
            (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)
        * (NumberField.Set.primeIdealZetaSum
            (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s
          / Real.log (1 / (s - 1))))
      (𝓝[>] (1 : ℝ)) (𝓝 δ) := by
    have := hAB.mul hquot
    simpa using this
  refine hmul.congr' ?_
  filter_upwards [hBtop.eventually (eventually_gt_atTop (0 : ℝ))] with s hpos
  have hBne : NumberField.Set.primeIdealZetaSum
      (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s ≠ 0 :=
    ne_of_gt hpos
  field_simp

end Commons.NumberTheory.NumberField.Set
