import Mathlib
import Submission.Work.BourgainPlan.Maximal.dyadicMaximal

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

/-! ## Auxiliary lemmas for `ae_le_dyMax`

The dyadic maximal function dominates `f` almost everywhere.  The proof is the Lebesgue
differentiation theorem along the shrinking dyadic cells containing `x`: for a.e. `x` the
average of `f` over the dyadic cell `dyCell n (dyIdx n x)` converges to `f x` as `n → -∞`.
-/

/-- `2 ^ n → 0` as `n → -∞` (integer powers). -/
lemma tendsto_two_zpow_atBot_zero : Tendsto (fun n : ℤ => (2:ℝ)^n) atBot (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.HasBasis.eventually_iff (Filter.atBot_basis (α := ℤ))]
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (show ((2:ℝ))⁻¹ < 1 by norm_num)
  refine ⟨-(m : ℤ), trivial, fun n hn => ?_⟩
  have hn' : n ≤ -(m:ℤ) := hn
  rw [Real.dist_eq, sub_zero]
  have hpos : (0:ℝ) < (2:ℝ)^n := zpow_pos (by norm_num) n
  rw [abs_of_pos hpos]
  calc (2:ℝ)^n ≤ (2:ℝ)^(-(m:ℤ)) := zpow_le_zpow_right₀ (by norm_num) hn'
    _ = ((2:ℝ)⁻¹)^m := by rw [zpow_neg, zpow_natCast, inv_pow]
    _ < ε := hm

/-- The left endpoint `dyIdx n x * 2 ^ n` of the dyadic cell of level `n` containing `x`
converges to `x` as `n → -∞`. -/
lemma tendsto_dyIdx_mul_atBot (x : ℝ) :
    Tendsto (fun n : ℤ => (dyIdx n x : ℝ) * (2:ℝ)^n) atBot (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.HasBasis.eventually_iff (Filter.atBot_basis (α := ℤ))]
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (show ((2:ℝ))⁻¹ < 1 by norm_num)
  refine ⟨-(m : ℤ), trivial, fun n hn => ?_⟩
  have hn' : n ≤ -(m:ℤ) := hn
  rw [Real.dist_eq]
  have hmem := dyIdx_mem n x
  have hax : (dyIdx n x : ℝ) * (2:ℝ)^n ≤ x := hmem.1
  rw [abs_of_nonpos (by linarith : (dyIdx n x : ℝ) * (2:ℝ)^n - x ≤ 0), neg_sub]
  have hlt : x - (dyIdx n x : ℝ) * (2:ℝ)^n < (2:ℝ)^n := by
    have h2 := hmem.2
    have h3 := dyCell_len n (dyIdx n x)
    linarith
  calc x - (dyIdx n x : ℝ) * (2:ℝ)^n < (2:ℝ)^n := hlt
    _ ≤ (2:ℝ)^(-(m:ℤ)) := zpow_le_zpow_right₀ (by norm_num) hn'
    _ = ((2:ℝ)⁻¹)^m := by rw [zpow_neg, zpow_natCast, inv_pow]
    _ < ε := hm

/-- If `F` has derivative `c` at `x` and `a i ≤ x ≤ b i` with `a i, b i → x`, then the mean
value `(F (b i) - F (a i)) / (b i - a i)` tends to `c`. -/
lemma tendsto_average_of_hasDerivAt {F : ℝ → ℝ} {c x : ℝ} (hF : HasDerivAt F c x)
    {ι : Type*} {l : Filter ι} {a b : ι → ℝ} (ha : Tendsto a l (𝓝 x)) (hb : Tendsto b l (𝓝 x))
    (hax : ∀ᶠ i in l, a i ≤ x) (hxb : ∀ᶠ i in l, x ≤ b i) (hlt : ∀ᶠ i in l, a i < b i) :
    Tendsto (fun i => (F (b i) - F (a i)) / (b i - a i)) l (𝓝 c) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hlittle := Asymptotics.isLittleO_iff.mp hF.isLittleO hε2
  filter_upwards [hb.eventually hlittle, ha.eventually hlittle, hax, hxb, hlt] with i hbi hai hai' hbi' hlti
  rw [Real.dist_eq]
  have hdpos : 0 < b i - a i := by linarith
  have hdne : b i - a i ≠ 0 := ne_of_gt hdpos
  have hA : |F (b i) - F x - (b i - x) * c| ≤ ε / 2 * (b i - x) := by
    have h := hbi
    rw [smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ b i - x)] at h
    exact h
  have hB : |F (a i) - F x - (a i - x) * c| ≤ ε / 2 * (x - a i) := by
    have h := hai
    rw [smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos (by linarith : a i - x ≤ 0),
      neg_sub] at h
    exact h
  have hnum : |F (b i) - F (a i) - (b i - a i) * c| ≤ ε / 2 * (b i - a i) := by
    have key : F (b i) - F (a i) - (b i - a i) * c
        = (F (b i) - F x - (b i - x) * c) - (F (a i) - F x - (a i - x) * c) := by ring
    rw [key]
    have hsub : |(F (b i) - F x - (b i - x) * c) - (F (a i) - F x - (a i - x) * c)|
        ≤ |F (b i) - F x - (b i - x) * c| + |F (a i) - F x - (a i - x) * c| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (F (b i) - F x - (b i - x) * c) 0
        (F (a i) - F x - (a i - x) * c)
    linarith
  have heq : (F (b i) - F (a i)) / (b i - a i) - c
      = (F (b i) - F (a i) - (b i - a i) * c) / (b i - a i) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hdpos, div_lt_iff₀ hdpos]
  exact lt_of_le_of_lt hnum (mul_lt_mul_of_pos_right (by linarith : ε / 2 < ε) hdpos)

/-- A set integral over `Ico u v` is the interval integral over `u..v`. -/
lemma integral_Ico_eq_intervalIntegral {f : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v) :
    ∫ y in Set.Ico u v, f y = ∫ y in u..v, f y := by
  rw [intervalIntegral.integral_of_le huv, MeasureTheory.integral_Ico_eq_integral_Ioc]

theorem ae_le_dyMax (f : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f MeasureTheory.volume)
    (hfnn : 0 ≤ f) :
    ∀ᵐ x ∂MeasureTheory.volume,
      ENNReal.ofReal (f x) ≤ Work.BourgainPlan.Maximal.dyMax (fun y => ENNReal.ofReal (f y)) x := by
  set F : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, f s with hFdef
  have hInt : ∀ u v : ℝ, IntervalIntegrable f volume u v := fun u v =>
    intervalIntegrable_iff.mpr ((hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hderiv : ∀ᵐ x ∂volume, HasDerivAt F (f x) x := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral (f := f) hf] with x hx
    exact hx 0
  filter_upwards [hderiv] with x hd
  set A : ℤ → ℝ := fun n => (dyIdx n x : ℝ) * (2:ℝ)^n with hA
  set B : ℤ → ℝ := fun n => ((dyIdx n x : ℝ) + 1) * (2:ℝ)^n with hB
  have ha : Tendsto A atBot (𝓝 x) := by rw [hA]; exact tendsto_dyIdx_mul_atBot x
  have hb : Tendsto B atBot (𝓝 x) := by
    have h := Tendsto.add ha tendsto_two_zpow_atBot_zero
    simpa [hB, hA, add_mul, add_zero] using h
  have hax : ∀ᶠ n in atBot, A n ≤ x := by
    rw [hA]; exact Filter.Eventually.of_forall fun n => (dyIdx_mem n x).1
  have hxb : ∀ᶠ n in atBot, x ≤ B n := by
    rw [hB]; exact Filter.Eventually.of_forall fun n => (dyIdx_mem n x).2.le
  have hlt : ∀ᶠ n in atBot, A n < B n := by
    rw [hA, hB]
    exact Filter.Eventually.of_forall fun n => by
      have h := dyCell_len n (dyIdx n x)
      linarith [zpow_two_pos n]
  have hT := tendsto_average_of_hasDerivAt hd ha hb hax hxb hlt
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεR : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
  obtain ⟨n, hn⟩ :=
    (hT.eventually (Ioi_mem_nhds (show f x - (ε:ℝ)/2 < f x by linarith))).exists
  have hAn : A n = (dyIdx n x : ℝ) * (2:ℝ)^n := by simp [hA]
  have hBn : B n = ((dyIdx n x : ℝ) + 1) * (2:ℝ)^n := by simp [hB]
  have hlen : B n - A n = (2:ℝ)^n := by rw [hAn, hBn]; exact dyCell_len n (dyIdx n x)
  have hnlt : A n < B n := by linarith [hlen, zpow_two_pos n]
  have hFint : F (B n) - F (A n) = ∫ y in (A n)..(B n), f y := by
    simp only [hFdef]
    exact intervalIntegral.integral_interval_sub_left (hInt 0 (B n)) (hInt 0 (A n))
  have hIco : ∫ y in (A n)..(B n), f y = ∫ y in dyCell n (dyIdx n x), f y := by
    rw [← integral_Ico_eq_intervalIntegral (u := A n) (v := B n) hnlt.le, hAn, hBn]
    rfl
  have hTval : (F (B n) - F (A n)) / (B n - A n)
      = ((2:ℝ)^n)⁻¹ * ∫ y in dyCell n (dyIdx n x), f y := by
    rw [hFint, hIco, hlen, div_eq_inv_mul]
  have hcell_int : IntegrableOn f (dyCell n (dyIdx n x)) volume := by
    refine (hf.integrableOn_isCompact (isCompact_Icc (a := (dyIdx n x : ℝ) * (2:ℝ)^n)
      (b := ((dyIdx n x : ℝ) + 1) * (2:ℝ)^n))).mono_set ?_
    intro y hy
    exact ⟨hy.1, hy.2.le⟩
  have hlin : ∫⁻ y in dyCell n (dyIdx n x), ENNReal.ofReal (f y)
      = ENNReal.ofReal (∫ y in dyCell n (dyIdx n x), f y) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := volume.restrict (dyCell n (dyIdx n x))) hcell_int
      (Filter.Eventually.of_forall hfnn)]
  have hofreal : ENNReal.ofReal (((2:ℝ)^n)⁻¹ * ∫ y in dyCell n (dyIdx n x), f y)
      = ENNReal.ofReal (((2:ℝ)^n)⁻¹) * ∫⁻ y in dyCell n (dyIdx n x), ENNReal.ofReal (f y) := by
    rw [ENNReal.ofReal_mul (by positivity), hlin]
  have hstep1 : ENNReal.ofReal (f x - (ε:ℝ)/2)
      ≤ ENNReal.ofReal ((F (B n) - F (A n)) / (B n - A n)) :=
    ENNReal.ofReal_le_ofReal hn.le
  have hstep2 : ENNReal.ofReal ((F (B n) - F (A n)) / (B n - A n))
      ≤ dyMax (fun y => ENNReal.ofReal (f y)) x := by
    rw [hTval, hofreal, dyMax]
    exact le_iSup_of_le n (le_iSup_of_le (dyIdx n x) (le_iSup_of_le (dyIdx_mem n x) le_rfl))
  have hsplit : ENNReal.ofReal (f x) ≤ ENNReal.ofReal (f x - (ε:ℝ)/2) + (ε : ℝ≥0∞) := by
    have h1 := ENNReal.ofReal_add_le (p := f x - (ε:ℝ)/2) (q := (ε:ℝ)/2)
    rw [sub_add_cancel] at h1
    refine h1.trans (add_le_add le_rfl ?_)
    rw [← ENNReal.ofReal_coe_nnreal (p := ε)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc ENNReal.ofReal (f x)
      ≤ ENNReal.ofReal (f x - (ε:ℝ)/2) + (ε : ℝ≥0∞) := hsplit
    _ ≤ ENNReal.ofReal ((F (B n) - F (A n)) / (B n - A n)) + (ε : ℝ≥0∞) :=
        add_le_add hstep1 le_rfl
    _ ≤ dyMax (fun y => ENNReal.ofReal (f y)) x + (ε : ℝ≥0∞) := add_le_add hstep2 le_rfl

end Work.BourgainPlan.Maximal
