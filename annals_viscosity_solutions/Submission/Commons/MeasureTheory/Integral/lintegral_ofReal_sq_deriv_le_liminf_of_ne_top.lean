import Mathlib
import Submission.Commons.MeasureTheory.Integral.lintegral_sliding_differenceQuotient_le_of_finiteDimensional
import Submission.Commons.Analysis.Calculus.absolutelyContinuousOnInterval_and_deriv_bound_of_differenceQuotient

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Commons.MeasureTheory.Integral

open Commons.Analysis.Calculus

/-- Auxiliary statement: the sliding difference-quotient `L²` estimate passes to the limit along a
uniformly convergent sequence of absolutely continuous curves. -/
lemma lintegral_sliding_differenceQuotient_le_liminf {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : ℕ → ℝ → E} {g : ℝ → E} {τ : ℝ} (hτ : 0 ≤ τ)
    (hconv : TendstoUniformlyOn F g atTop (Set.Icc 0 τ))
    (hAC : ∀ n, AbsolutelyContinuousOnInterval (F n) 0 τ)
    {s : ℝ} (hs0 : 0 < s) (hst : s < τ) :
    ∫⁻ t in Set.Ioc 0 (τ - s), ENNReal.ofReal (‖s⁻¹ • (g (t + s) - g t)‖ ^ 2)
      ≤ Filter.liminf (fun n => ∫⁻ t in Set.Ioc 0 τ,
          ENNReal.ofReal (‖deriv (F n) t‖ ^ 2)) atTop := by
  have hbound : ∀ n, ∫⁻ t in Set.Ioc 0 (τ - s),
        ENNReal.ofReal (‖s⁻¹ • (F n (t + s) - F n t)‖ ^ 2)
      ≤ ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv (F n) t‖ ^ 2) := by
    intro n
    exact lintegral_sliding_differenceQuotient_le_of_finiteDimensional hτ hs0 (by linarith) (hAC n)
  have hmeas : ∀ n, AEMeasurable
      (fun t : ℝ => ENNReal.ofReal (‖s⁻¹ • (F n (t + s) - F n t)‖ ^ 2))
      (volume.restrict (Set.Ioc 0 (τ - s))) := by
    intro n
    have hFn : ContinuousOn (F n) (Set.Icc 0 τ) := by
      have h := (hAC n).continuousOn
      rwa [uIcc_of_le hτ] at h
    have hmaps : MapsTo (fun t : ℝ => t + s) (Set.Ioc 0 (τ - s)) (Set.Icc 0 τ) := by
      intro t ht
      rw [mem_Ioc] at ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hmaps' : MapsTo (fun t : ℝ => t) (Set.Ioc 0 (τ - s)) (Set.Icc 0 τ) := by
      intro t ht
      rw [mem_Ioc] at ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hc1 : ContinuousOn (fun t : ℝ => F n (t + s)) (Set.Ioc 0 (τ - s)) :=
      hFn.comp (continuous_id.add continuous_const).continuousOn hmaps
    have hc2 : ContinuousOn (fun t : ℝ => F n t) (Set.Ioc 0 (τ - s)) :=
      hFn.comp continuousOn_id hmaps'
    have hc3 : ContinuousOn (fun t : ℝ => s⁻¹ • (F n (t + s) - F n t)) (Set.Ioc 0 (τ - s)) :=
      (hc1.sub hc2).const_smul s⁻¹
    have hc4 : ContinuousOn (fun t : ℝ => ‖s⁻¹ • (F n (t + s) - F n t)‖ ^ 2)
        (Set.Ioc 0 (τ - s)) :=
      (hc3.norm).pow 2
    exact (ENNReal.continuous_ofReal.comp_continuousOn hc4).aemeasurable measurableSet_Ioc
  have hliminf_eq : ∀ t ∈ Set.Ioc 0 (τ - s),
      Filter.liminf (fun n => ENNReal.ofReal (‖s⁻¹ • (F n (t + s) - F n t)‖ ^ 2)) atTop
        = ENNReal.ofReal (‖s⁻¹ • (g (t + s) - g t)‖ ^ 2) := by
    intro t ht
    rw [mem_Ioc] at ht
    have htI : t ∈ Set.Icc 0 τ := ⟨le_of_lt ht.1, by linarith [ht.2]⟩
    have htsI : t + s ∈ Set.Icc 0 τ := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h1 : Tendsto (fun n => F n (t + s)) atTop (𝓝 (g (t + s))) := hconv.tendsto_at htsI
    have h2 : Tendsto (fun n => F n t) atTop (𝓝 (g t)) := hconv.tendsto_at htI
    have h3 := (h1.sub h2).const_smul s⁻¹
    have hcont : Continuous fun x : E => ENNReal.ofReal (‖x‖ ^ 2) :=
      ENNReal.continuous_ofReal.comp (continuous_norm.pow 2)
    exact ((hcont.tendsto (s⁻¹ • (g (t + s) - g t))).comp h3).liminf_eq
  have hfatou := lintegral_liminf_le' (μ := volume.restrict (Set.Ioc 0 (τ - s)))
    (f := fun n t => ENNReal.ofReal (‖s⁻¹ • (F n (t + s) - F n t)‖ ^ 2)) (u := atTop) hmeas
  calc ∫⁻ t in Set.Ioc 0 (τ - s), ENNReal.ofReal (‖s⁻¹ • (g (t + s) - g t)‖ ^ 2)
      = ∫⁻ t in Set.Ioc 0 (τ - s),
          Filter.liminf (fun n => ENNReal.ofReal
            (‖s⁻¹ • (F n (t + s) - F n t)‖ ^ 2)) atTop :=
        (setLIntegral_congr_fun measurableSet_Ioc hliminf_eq).symm
    _ ≤ Filter.liminf (fun n => ∫⁻ t in Set.Ioc 0 (τ - s),
          ENNReal.ofReal (‖s⁻¹ • (F n (t + s) - F n t)‖ ^ 2)) atTop := hfatou
    _ ≤ Filter.liminf (fun n => ∫⁻ t in Set.Ioc 0 τ,
          ENNReal.ofReal (‖deriv (F n) t‖ ^ 2)) atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall hbound)

/-- **Lower semicontinuity of the Dirichlet energy under uniform convergence (finite-liminf
case).**  This is the *correct* form of
`Commons.MeasureTheory.Integral.lintegral_ofReal_sq_deriv_le_liminf`: the extra hypothesis that
the `liminf` of the energies is finite is necessary, because the first conclusion (absolute
continuity of the limit) is false in general without it (take the standard piecewise-linear
approximations of the Cantor function: they converge uniformly, are absolutely continuous, and
their energies `∫⁻ ofReal ‖deriv‖²` equal `(3/2)^n`, so the liminf is `⊤`, while the Cantor
function is not absolutely continuous).

Route: for each `s ∈ Ioo 0 (b - a)`, the sliding Jensen bound
`lintegral_sliding_differenceQuotient_le_of_finiteDimensional` applied to each `F n`, together
with Fatou's lemma `MeasureTheory.lintegral_liminf_le'` and the pointwise convergence
`F n t → g t`, `F n (t+s) → g (t+s)` (`TendstoUniformlyOn.tendsto_at`) give
`∫⁻ t in Ioc 0 (b - s), ofReal (‖s⁻¹ • (g (t+s) - g t)‖²) ≤ L`, where `L` is the liminf.
If `L ≠ ⊤`, set `M := sqrt L.toReal`; then `ENNReal.ofReal (M^2) = L`, and
`absolutelyContinuousOnInterval_and_deriv_bound_of_differenceQuotient` (with `a := 0`,
`b := τ`, `M := M`) yields both conclusions.  When the energies are uniformly bounded by
`ENNReal.ofReal C` the hypothesis `hfin` follows since `liminf ≤ … ≠ ⊤`. -/
theorem lintegral_ofReal_sq_deriv_le_liminf_of_ne_top {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : ℕ → ℝ → E} {g : ℝ → E} {τ : ℝ} (hτ : 0 ≤ τ)
    (hg : ContinuousOn g (Set.Icc 0 τ))
    (hconv : TendstoUniformlyOn F g atTop (Set.Icc 0 τ))
    (hAC : ∀ n, AbsolutelyContinuousOnInterval (F n) 0 τ)
    (hfin : Filter.liminf (fun n =>
        ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv (F n) t‖ ^ 2)) atTop ≠ ⊤) :
    AbsolutelyContinuousOnInterval g 0 τ ∧
      ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv g t‖ ^ 2)
        ≤ Filter.liminf (fun n => ∫⁻ t in Set.Ioc 0 τ,
            ENNReal.ofReal (‖deriv (F n) t‖ ^ 2)) atTop := by
  set L := Filter.liminf (fun n => ∫⁻ t in Set.Ioc 0 τ,
      ENNReal.ofReal (‖deriv (F n) t‖ ^ 2)) atTop with hL
  set M := Real.sqrt L.toReal with hM
  have hMnonneg : 0 ≤ M := Real.sqrt_nonneg _
  have hMsq : M ^ 2 = L.toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have hLM : ENNReal.ofReal (M ^ 2) = L := by
    rw [hMsq, ENNReal.ofReal_toReal hfin]
  obtain ⟨hac, hbd⟩ :=
    absolutelyContinuousOnInterval_and_deriv_bound_of_differenceQuotient hτ hMnonneg hg
      (fun s hs => by
        have hs' : s ∈ Set.Ioo (0:ℝ) τ := ⟨hs.1, by linarith [hs.2]⟩
        rw [hLM]
        exact lintegral_sliding_differenceQuotient_le_liminf hτ hconv hAC hs'.1 hs'.2)
  exact ⟨hac, hLM ▸ hbd⟩

end Commons.MeasureTheory.Integral
