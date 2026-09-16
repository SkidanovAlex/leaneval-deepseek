import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Countable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory

namespace Commons.MeasureTheory.Integral

noncomputable section

/-! ## Helper definitions -/

/-- Insert a value at coordinate `i` of a function defined on the other coordinates. -/
private def marginalExtendAt {k : ℕ} (i : Fin k) (x : ℝ)
    (t' : {j : Fin k // j ≠ i} → ℝ) : Fin k → ℝ :=
  fun j => if h : j = i then x else t' ⟨j, h⟩

private lemma marginalExtendAt_self {k : ℕ} (i : Fin k) (x : ℝ)
    (t' : {j : Fin k // j ≠ i} → ℝ) : marginalExtendAt i x t' i = x := by
  simp [marginalExtendAt]

/-- Indicator of the closed orthant, as a product of one-dimensional indicators. -/
private def marginalOrthInd {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∏ i, (Set.Ici (0:ℝ)).indicator (fun _ => (1:ℝ)) (x i)

private lemma marginalOrthInd_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ marginalOrthInd x :=
  Finset.prod_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _

private lemma marginalOrthInd_le_one {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    marginalOrthInd x ≤ 1 := by
  refine Finset.prod_le_one₀ (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (fun i _ => ?_)
  by_cases h : x i ∈ Set.Ici (0:ℝ)
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

private lemma marginalOrthInd_eq_zero_of_lt {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (h : ∃ i, x i < 0) : marginalOrthInd x = 0 := by
  obtain ⟨i, hi⟩ := h
  rw [marginalOrthInd]
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (Set.indicator_of_notMem (by rw [Set.mem_Ici]; exact not_le.mpr hi) _)

private lemma measurable_marginalOrthInd {ι : Type*} [Fintype ι] :
    Measurable (fun t : ι → ℝ => marginalOrthInd t) :=
  Finset.measurable_prod _ fun l _ =>
    (measurable_const.indicator measurableSet_Ici).comp (measurable_pi_apply l)

/-- The box `∏ [0,B]` in a finite-dimensional real space. -/
private def marginalBox {ι : Type*} [Fintype ι] (B : ℝ) : Set (ι → ℝ) :=
  Set.univ.pi fun _ => Set.Icc (0:ℝ) B

private lemma measurableSet_marginalBox {ι : Type*} [Fintype ι] (B : ℝ) :
    MeasurableSet (marginalBox (ι := ι) B) :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc

private lemma volume_marginalBox {ι : Type*} [Fintype ι] {B : ℝ} (hB : 0 ≤ B) :
    (volume : Measure (ι → ℝ)) (marginalBox B)
      = ENNReal.ofReal (B ^ Fintype.card ι) := by
  rw [marginalBox, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  have h1 : (∏ _i : ι, (volume : Measure ℝ) (Set.Icc (0:ℝ) B))
      = ∏ _i : ι, ENNReal.ofReal B :=
    Finset.prod_congr rfl fun _ _ => by rw [Real.volume_Icc]; congr 1; ring
  rw [h1, Finset.prod_const, Finset.card_univ]
  exact (ENNReal.ofReal_pow hB (Fintype.card ι)).symm

private lemma card_subtype_ne {k : ℕ} (i : Fin k) :
    Fintype.card {l : Fin k // l ≠ i} = k - 1 := by
  have h1 : Fintype.card {l : Fin k // ¬ (l ≠ i)}
      = Fintype.card (Fin k) - Fintype.card {l : Fin k // l ≠ i} :=
    Fintype.card_subtype_compl (fun l : Fin k => l ≠ i)
  rw [Fintype.card_fin] at h1
  have h2 : Fintype.card {l : Fin k // ¬ (l ≠ i)} = 1 := by
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun l : Fin k => not_ne_iff))]
    exact Fintype.card_subtype_eq i
  omega

/-- A function vanishing beyond `B` has the same halfline integral as over `(0,B]`. -/
private lemma setIntegral_Ioi_eq_Ioc_of_gt_eq_zero {g : ℝ → ℝ} {B : ℝ}
    (hg : ∀ x : ℝ, B < x → g x = 0) :
    (∫ x in Set.Ioi (0:ℝ), g x) = ∫ x in Set.Ioc (0:ℝ) B, g x := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Set.Ioi (0:ℝ)
  · rw [Set.indicator_of_mem hx]
    by_cases hxB : x ∈ Set.Ioc (0:ℝ) B
    · rw [Set.indicator_of_mem hxB]
    · rw [Set.indicator_of_notMem hxB]
      have hlt : B < x := by
        rw [Set.mem_Ioc, not_and_or] at hxB
        rcases hxB with h | h
        · exact absurd hx h
        · exact lt_of_not_ge h
      exact hg x hlt
  · rw [Set.indicator_of_notMem hx]
    have hx' : x ∉ Set.Ioc (0:ℝ) B :=
      fun h => hx (Set.mem_Ioi.mpr (Set.mem_Ioc.mp h).1)
    rw [Set.indicator_of_notMem hx']

/-! ## The abstract error estimate -/

/-- Abstract `L¹` error estimate for a squared marginal against the orthant indicator:
two (measurable) functions bounded by `a`, `b`, differing by at most `δ`, both vanishing
outside the box `[0,B]^ι`, have squared-orthant-indicator set integrals differing by at
most `δ (a+b) B^{card ι}`. -/
private theorem setIntegral_sq_orthant_error_le {ι : Type*} [Fintype ι]
    {u v : (ι → ℝ) → ℝ} {a b δ B : ℝ}
    (hB0 : 0 ≤ B) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hδ0 : 0 ≤ δ)
    (hu : ∀ t, |u t| ≤ a) (hv : ∀ t, |v t| ≤ b) (huv : ∀ t, |u t - v t| ≤ δ)
    (hu0 : ∀ t, (∃ i, B < t i) → u t = 0)
    (hv0 : ∀ t, (∃ i, B < t i) → v t = 0)
    (hum : Measurable u) (hvm : Measurable v)
    {S : Set (ι → ℝ)} (_hS : MeasurableSet S) :
    |(∫ t in S, (u t) ^ 2 * marginalOrthInd t)
      - (∫ t in S, (v t) ^ 2 * marginalOrthInd t)|
      ≤ δ * (a + b) * B ^ (Fintype.card ι) := by
  classical
  have hK0 : 0 ≤ δ * (a + b) := mul_nonneg hδ0 (add_nonneg ha0 hb0)
  have hsqu : ∀ t, |(u t) ^ 2 - (v t) ^ 2| ≤ δ * (a + b) := by
    intro t
    have h1 : (u t) ^ 2 - (v t) ^ 2 = (u t - v t) * (u t + v t) := by ring
    rw [h1, abs_mul]
    have h2 : |u t + v t| ≤ a + b := by
      calc |u t + v t| ≤ |u t| + |v t| := abs_add_le _ _
        _ ≤ a + b := add_le_add (hu t) (hv t)
    exact mul_le_mul (huv t) h2 (abs_nonneg _) hδ0
  have hx_out : ∀ t : ι → ℝ, t ∉ marginalBox B → ∃ i : ι, t i < 0 ∨ B < t i := by
    intro t ht
    by_contra hc
    push Not at hc
    exact ht (Set.mem_univ_pi.mpr fun i => Set.mem_Icc.mpr ⟨(hc i).1, (hc i).2⟩)
  have hpt : ∀ t : ι → ℝ,
      ‖(u t) ^ 2 * marginalOrthInd t - (v t) ^ 2 * marginalOrthInd t‖
        ≤ (δ * (a + b)) * (marginalBox B).indicator (fun _ => (1:ℝ)) t := by
    intro t
    by_cases ht : t ∈ marginalBox B
    · rw [Set.indicator_of_mem ht, mul_one]
      have h1 : (u t) ^ 2 * marginalOrthInd t - (v t) ^ 2 * marginalOrthInd t
          = ((u t) ^ 2 - (v t) ^ 2) * marginalOrthInd t := by ring
      rw [h1, Real.norm_eq_abs, abs_mul, abs_of_nonneg (marginalOrthInd_nonneg t)]
      refine le_trans (mul_le_mul_of_nonneg_right (hsqu t) (marginalOrthInd_nonneg t)) ?_
      simpa using mul_le_mul_of_nonneg_left (marginalOrthInd_le_one t) hK0
    · rw [Set.indicator_of_notMem ht, mul_zero]
      obtain ⟨i, hi⟩ := hx_out t ht
      rcases hi with hi | hi
      · rw [marginalOrthInd_eq_zero_of_lt t ⟨i, hi⟩]
        rw [show (u t) ^ 2 * 0 - (v t) ^ 2 * 0 = 0 from by ring, norm_zero]
      · rw [hu0 t ⟨i, hi⟩, hv0 t ⟨i, hi⟩]
        rw [show (0:ℝ) ^ 2 * marginalOrthInd t - (0:ℝ) ^ 2 * marginalOrthInd t = 0 from by
          ring, norm_zero]
  have hCu : ∀ t : ι → ℝ, ‖(u t) ^ 2 * marginalOrthInd t‖
      ≤ max 1 (a ^ 2) * (marginalBox B).indicator (fun _ => (1:ℝ)) t := by
    intro t
    by_cases ht : t ∈ marginalBox B
    · rw [Set.indicator_of_mem ht, mul_one, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg _), abs_of_nonneg (marginalOrthInd_nonneg t)]
      have h2 : (u t) ^ 2 ≤ a ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hu t) 2
      refine le_trans (mul_le_mul_of_nonneg_right h2 (marginalOrthInd_nonneg t)) ?_
      refine le_trans (mul_le_mul_of_nonneg_left (marginalOrthInd_le_one t) (pow_nonneg ha0 2)) ?_
      rw [mul_one]
      rcases le_total (a ^ 2) 1 with h | h
      · exact le_trans h (le_max_left _ _)
      · exact le_max_right _ _
    · rw [Set.indicator_of_notMem ht, mul_zero]
      obtain ⟨i, hi⟩ := hx_out t ht
      rcases hi with hi | hi
      · rw [marginalOrthInd_eq_zero_of_lt t ⟨i, hi⟩]
        rw [show (u t) ^ 2 * 0 = 0 from by ring, norm_zero]
      · rw [hu0 t ⟨i, hi⟩]
        rw [show (0:ℝ) ^ 2 * marginalOrthInd t = 0 from by ring, norm_zero]
  have hCv : ∀ t : ι → ℝ, ‖(v t) ^ 2 * marginalOrthInd t‖
      ≤ max 1 (b ^ 2) * (marginalBox B).indicator (fun _ => (1:ℝ)) t := by
    intro t
    by_cases ht : t ∈ marginalBox B
    · rw [Set.indicator_of_mem ht, mul_one, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg _), abs_of_nonneg (marginalOrthInd_nonneg t)]
      have h2 : (v t) ^ 2 ≤ b ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hv t) 2
      refine le_trans (mul_le_mul_of_nonneg_right h2 (marginalOrthInd_nonneg t)) ?_
      refine le_trans (mul_le_mul_of_nonneg_left (marginalOrthInd_le_one t) (pow_nonneg hb0 2)) ?_
      rw [mul_one]
      rcases le_total (b ^ 2) 1 with h | h
      · exact le_trans h (le_max_left _ _)
      · exact le_max_right _ _
    · rw [Set.indicator_of_notMem ht, mul_zero]
      obtain ⟨i, hi⟩ := hx_out t ht
      rcases hi with hi | hi
      · rw [marginalOrthInd_eq_zero_of_lt t ⟨i, hi⟩]
        rw [show (v t) ^ 2 * 0 = 0 from by ring, norm_zero]
      · rw [hv0 t ⟨i, hi⟩]
        rw [show (0:ℝ) ^ 2 * marginalOrthInd t = 0 from by ring, norm_zero]
  have hvolM : (volume : Measure (ι → ℝ)) (marginalBox B) ≠ ⊤ := by
    rw [volume_marginalBox hB0]; exact ENNReal.ofReal_ne_top
  have hIind : Integrable ((marginalBox B).indicator (fun _ => (1:ℝ)))
      (volume : Measure (ι → ℝ)) := by
    rw [MeasureTheory.integrable_indicator_iff (measurableSet_marginalBox (ι := ι) B)]
    refine IntegrableOn.of_bound ?_ aestronglyMeasurable_const 1
      (Filter.Eventually.of_forall fun x => by simp)
    rw [lt_top_iff_ne_top]; exact hvolM
  have hIindS : Integrable ((marginalBox B).indicator (fun _ => (1:ℝ)))
      (volume.restrict S) := hIind.restrict
  have hdomS : IntegrableOn
      (fun t => (δ * (a + b)) * (marginalBox B).indicator (fun _ => (1:ℝ)) t)
      S volume := hIindS.const_mul _
  have hIf : IntegrableOn (fun t => (u t) ^ 2 * marginalOrthInd t) S volume :=
    Integrable.mono' (hIindS.const_mul (max 1 (a ^ 2)))
      (((hum.pow_const 2).mul (measurable_marginalOrthInd (ι := ι))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hCu t)
  have hIg : IntegrableOn (fun t => (v t) ^ 2 * marginalOrthInd t) S volume :=
    Integrable.mono' (hIindS.const_mul (max 1 (b ^ 2)))
      (((hvm.pow_const 2).mul (measurable_marginalOrthInd (ι := ι))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hCv t)
  have hstep1 : |(∫ t in S, (u t) ^ 2 * marginalOrthInd t)
      - (∫ t in S, (v t) ^ 2 * marginalOrthInd t)|
      ≤ ∫ t in S, ‖(u t) ^ 2 * marginalOrthInd t - (v t) ^ 2 * marginalOrthInd t‖ := by
    rw [← MeasureTheory.integral_sub hIf hIg]
    simpa only [Real.norm_eq_abs] using
      (abs_integral_le_integral_abs (μ := volume.restrict S)
        (f := fun t : ι → ℝ => (u t) ^ 2 * marginalOrthInd t - (v t) ^ 2 * marginalOrthInd t))
  refine le_trans hstep1 ?_
  refine le_trans (MeasureTheory.setIntegral_mono_of_nonneg
    (f := fun t : ι → ℝ => ‖(u t) ^ 2 * marginalOrthInd t - (v t) ^ 2 * marginalOrthInd t‖)
    (g := fun t : ι → ℝ => (δ * (a + b)) * (marginalBox B).indicator (fun _ => (1:ℝ)) t)
    (fun t _ => norm_nonneg _) (fun t _ => hpt t) hdomS) ?_
  calc ∫ t in S, (δ * (a + b)) * (marginalBox B).indicator (fun _ => (1:ℝ)) t
      = (δ * (a + b)) * ∫ t in S, (marginalBox B).indicator (fun _ => (1:ℝ)) t := by
        rw [MeasureTheory.integral_const_mul]
    _ = (δ * (a + b)) * (volume (S ∩ marginalBox B)).toReal := by
        rw [MeasureTheory.setIntegral_indicator (measurableSet_marginalBox (ι := ι) B),
          MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
        rfl
    _ ≤ (δ * (a + b)) * B ^ Fintype.card ι := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        calc (volume (S ∩ marginalBox B)).toReal
            ≤ (volume (marginalBox B)).toReal :=
              ENNReal.toReal_mono hvolM (measure_mono Set.inter_subset_right)
          _ = B ^ Fintype.card ι := by
              rw [volume_marginalBox hB0, ENNReal.toReal_ofReal (pow_nonneg hB0 _)]

/-- Continuity of the insertion map, in `(t, x)`. -/
private lemma continuous_marginalExtendAt_pair {k : ℕ} (i₀ : Fin k) :
    Continuous (fun p : ({l : Fin k // l ≠ i₀} → ℝ) × ℝ =>
      marginalExtendAt i₀ p.2 p.1) := by
  refine continuous_pi fun l => ?_
  by_cases hl : l = i₀
  · have h : Continuous (fun p : ({l : Fin k // l ≠ i₀} → ℝ) × ℝ => p.2) := continuous_snd
    simpa only [marginalExtendAt, dif_pos hl] using h
  · have h : Continuous (fun p : ({l : Fin k // l ≠ i₀} → ℝ) × ℝ => p.1 ⟨l, hl⟩) :=
      (continuous_apply (⟨l, hl⟩ : {l : Fin k // l ≠ i₀})).comp continuous_fst
    simpa only [marginalExtendAt, dif_neg hl] using h


/-- **Marginal set error bound.**  If `Gtf` is an `el`-perturbation of the bounded, supported
function `F`, then the squared marginal of `Gtf` (against the orthant indicator of the remaining
coordinates) differs from that of `F` by at most `el * Bg * (2*CF*Bg + el*Bg) * Bg^(k-1)` on any
measurable set `S` of the marginal coordinates. -/
theorem marginal_set_error_le {k : ℕ} {F Gtf : (Fin k → ℝ) → ℝ} {CF R Bg el : ℝ}
    (hCF0 : 0 ≤ CF) (hCF : ∀ s : Fin k → ℝ, |F s| ≤ CF)
    (hBg0 : 0 ≤ Bg) (hRB : R ≤ Bg) (hel : 0 ≤ el)
    (hFcoord : ∀ s : Fin k → ℝ, (∃ i, R < s i) → F s = 0)
    (hGcoord : ∀ s : Fin k → ℝ, (∃ i, Bg < s i) → Gtf s = 0)
    (happrox : ∀ s : Fin k → ℝ, |Gtf s - F s| ≤ el)
    (hGtfc : Continuous Gtf) (hFc : Continuous F) (i₀ : Fin k)
    {S : Set ({l : Fin k // l ≠ i₀} → ℝ)} (hS : MeasurableSet S) :
    |(∫ t in S,
        (∫ x in Set.Ioi (0:ℝ),
            Gtf (fun j => if h : j = i₀ then x else t ⟨j, h⟩)) ^ 2 *
          (∏ l : {l : Fin k // l ≠ i₀},
            (Set.Ici (0:ℝ)).indicator (fun _ => (1:ℝ)) (t l)))
      - ∫ t in S,
        (∫ x in Set.Ioi (0:ℝ),
            F (fun j => if h : j = i₀ then x else t ⟨j, h⟩)) ^ 2 *
          (∏ l : {l : Fin k // l ≠ i₀},
            (Set.Ici (0:ℝ)).indicator (fun _ => (1:ℝ)) (t l))|
      ≤ el * Bg * (2 * CF * Bg + el * Bg) * Bg ^ (k - 1) := by
  classical
  change |(∫ t in S, (∫ x in Set.Ioi (0:ℝ), Gtf (marginalExtendAt i₀ x t)) ^ 2 *
          marginalOrthInd t)
      - ∫ t in S, (∫ x in Set.Ioi (0:ℝ), F (marginalExtendAt i₀ x t)) ^ 2 *
          marginalOrthInd t|
      ≤ el * Bg * (2 * CF * Bg + el * Bg) * Bg ^ (k - 1)
  -- uniform bound on `Gtf`
  have hGb : ∀ s : Fin k → ℝ, |Gtf s| ≤ CF + el := by
    intro s
    calc |Gtf s| = |F s + (Gtf s - F s)| := by ring_nf
      _ ≤ |F s| + |Gtf s - F s| := abs_add_le _ _
      _ ≤ CF + el := add_le_add (hCF s) (happrox s)
  -- continuity of the parametrised integrands
  have hcontG : Continuous (fun p : ({l : Fin k // l ≠ i₀} → ℝ) × ℝ =>
      Gtf (marginalExtendAt i₀ p.2 p.1)) :=
    hGtfc.comp (continuous_marginalExtendAt_pair i₀)
  have hcontF : Continuous (fun p : ({l : Fin k // l ≠ i₀} → ℝ) × ℝ =>
      F (marginalExtendAt i₀ p.2 p.1)) :=
    hFc.comp (continuous_marginalExtendAt_pair i₀)
  have hvolIoc : volume (Set.Ioc (0:ℝ) Bg) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hcI : ∀ c : ℝ, 0 ≤ c → IntegrableOn (fun _ : ℝ => c) (Set.Ioc (0:ℝ) Bg) volume :=
    fun c hc => IntegrableOn.of_bound hvolIoc aestronglyMeasurable_const c
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg hc])
  -- halfline integrals are integrals over `(0, Bg]`
  have hIocG : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      (∫ x in Set.Ioi (0:ℝ), Gtf (marginalExtendAt i₀ x t))
        = ∫ x in Set.Ioc (0:ℝ) Bg, Gtf (marginalExtendAt i₀ x t) := by
    intro t
    refine setIntegral_Ioi_eq_Ioc_of_gt_eq_zero (fun x hx => ?_)
    exact hGcoord _ ⟨i₀, by rw [marginalExtendAt_self]; exact hx⟩
  have hIocF : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      (∫ x in Set.Ioi (0:ℝ), F (marginalExtendAt i₀ x t))
        = ∫ x in Set.Ioc (0:ℝ) Bg, F (marginalExtendAt i₀ x t) := by
    intro t
    refine setIntegral_Ioi_eq_Ioc_of_gt_eq_zero (fun x hx => ?_)
    exact hFcoord _ ⟨i₀, by rw [marginalExtendAt_self]; exact lt_of_le_of_lt hRB hx⟩
  -- slice integrability
  have hGi : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      IntegrableOn (fun x : ℝ => Gtf (marginalExtendAt i₀ x t)) (Set.Ioc (0:ℝ) Bg) volume := by
    intro t
    exact IntegrableOn.of_bound hvolIoc
      ((hcontG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (CF + el) (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hGb _)
  have hFi : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      IntegrableOn (fun x : ℝ => F (marginalExtendAt i₀ x t)) (Set.Ioc (0:ℝ) Bg) volume := by
    intro t
    exact IntegrableOn.of_bound hvolIoc
      ((hcontF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      CF (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hCF _)
  -- bounds on the slice integrals
  have hbdG : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      |∫ x in Set.Ioc (0:ℝ) Bg, Gtf (marginalExtendAt i₀ x t)| ≤ (CF + el) * Bg := by
    intro t
    calc |∫ x in Set.Ioc (0:ℝ) Bg, Gtf (marginalExtendAt i₀ x t)|
        ≤ ∫ x in Set.Ioc (0:ℝ) Bg, |Gtf (marginalExtendAt i₀ x t)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x in Set.Ioc (0:ℝ) Bg, (CF + el) :=
          setIntegral_mono_of_nonneg (fun x _ => abs_nonneg _) (fun x _ => hGb _)
            (hcI _ (by linarith))
      _ = (CF + el) * Bg := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul]
          show (volume (Set.Ioc (0:ℝ) Bg)).toReal * (CF + el) = (CF + el) * Bg
          rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ Bg - 0)]
          ring
  have hbdF : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      |∫ x in Set.Ioc (0:ℝ) Bg, F (marginalExtendAt i₀ x t)| ≤ CF * Bg := by
    intro t
    calc |∫ x in Set.Ioc (0:ℝ) Bg, F (marginalExtendAt i₀ x t)|
        ≤ ∫ x in Set.Ioc (0:ℝ) Bg, |F (marginalExtendAt i₀ x t)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x in Set.Ioc (0:ℝ) Bg, CF :=
          setIntegral_mono_of_nonneg (fun x _ => abs_nonneg _) (fun x _ => hCF _)
            (hcI _ hCF0)
      _ = CF * Bg := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul]
          show (volume (Set.Ioc (0:ℝ) Bg)).toReal * CF = CF * Bg
          rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ Bg - 0)]
          ring
  -- the hypothesis bounds for the abstract estimate
  have hu : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      |∫ x in Set.Ioi (0:ℝ), Gtf (marginalExtendAt i₀ x t)| ≤ (CF + el) * Bg := by
    intro t
    rw [hIocG t]; exact hbdG t
  have hv : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      |∫ x in Set.Ioi (0:ℝ), F (marginalExtendAt i₀ x t)| ≤ CF * Bg := by
    intro t
    rw [hIocF t]; exact hbdF t
  have huv : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      |(∫ x in Set.Ioi (0:ℝ), Gtf (marginalExtendAt i₀ x t))
        - (∫ x in Set.Ioi (0:ℝ), F (marginalExtendAt i₀ x t))| ≤ el * Bg := by
    intro t
    rw [hIocG t, hIocF t]
    have heq : (∫ x in Set.Ioc (0:ℝ) Bg, Gtf (marginalExtendAt i₀ x t))
        - (∫ x in Set.Ioc (0:ℝ) Bg, F (marginalExtendAt i₀ x t))
        = ∫ x in Set.Ioc (0:ℝ) Bg,
            (Gtf (marginalExtendAt i₀ x t) - F (marginalExtendAt i₀ x t)) :=
      (MeasureTheory.integral_sub (hGi t) (hFi t)).symm
    rw [heq]
    calc |∫ x in Set.Ioc (0:ℝ) Bg,
            (Gtf (marginalExtendAt i₀ x t) - F (marginalExtendAt i₀ x t))|
        ≤ ∫ x in Set.Ioc (0:ℝ) Bg,
            |Gtf (marginalExtendAt i₀ x t) - F (marginalExtendAt i₀ x t)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x in Set.Ioc (0:ℝ) Bg, el :=
          setIntegral_mono_of_nonneg (fun x _ => abs_nonneg _) (fun x _ => happrox _)
            (hcI _ hel)
      _ = el * Bg := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul]
          show (volume (Set.Ioc (0:ℝ) Bg)).toReal * el = el * Bg
          rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ Bg - 0)]
          ring
  -- vanishing of the marginal integrals outside the box
  have hU0 : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      (∃ i : {l : Fin k // l ≠ i₀}, Bg < t i) →
      (∫ x in Set.Ioi (0:ℝ), Gtf (marginalExtendAt i₀ x t)) = 0 := by
    intro t ht
    obtain ⟨i, hi⟩ := ht
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x _ => ?_
    refine hGcoord _ ⟨i.1, ?_⟩
    have hself : marginalExtendAt i₀ x t i.1 = t i := by
      simp only [marginalExtendAt, dif_neg i.2]
    rw [hself]; exact hi
  have hV0 : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      (∃ i : {l : Fin k // l ≠ i₀}, Bg < t i) →
      (∫ x in Set.Ioi (0:ℝ), F (marginalExtendAt i₀ x t)) = 0 := by
    intro t ht
    obtain ⟨i, hi⟩ := ht
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x _ => ?_
    refine hFcoord _ ⟨i.1, ?_⟩
    have hself : marginalExtendAt i₀ x t i.1 = t i := by
      simp only [marginalExtendAt, dif_neg i.2]
    rw [hself]; exact lt_of_le_of_lt hRB hi
  -- continuity of the marginal integrals
  have hUcont : Continuous (fun t : {l : Fin k // l ≠ i₀} → ℝ =>
      ∫ x in Set.Ioi (0:ℝ), Gtf (marginalExtendAt i₀ x t)) := by
    rw [show (fun t : {l : Fin k // l ≠ i₀} → ℝ =>
            ∫ x in Set.Ioi (0:ℝ), Gtf (marginalExtendAt i₀ x t))
          = fun t => ∫ x in Set.Ioc (0:ℝ) Bg, Gtf (marginalExtendAt i₀ x t) from by
            funext t; exact hIocG t]
    rw [show (fun t : {l : Fin k // l ≠ i₀} → ℝ =>
            ∫ x in Set.Ioc (0:ℝ) Bg, Gtf (marginalExtendAt i₀ x t))
          = fun t => ∫ x in (0:ℝ)..Bg, Gtf (marginalExtendAt i₀ x t) from by
            funext t; exact (intervalIntegral.integral_of_le hBg0).symm]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcontG 0 Bg
  have hVcont : Continuous (fun t : {l : Fin k // l ≠ i₀} → ℝ =>
      ∫ x in Set.Ioi (0:ℝ), F (marginalExtendAt i₀ x t)) := by
    rw [show (fun t : {l : Fin k // l ≠ i₀} → ℝ =>
            ∫ x in Set.Ioi (0:ℝ), F (marginalExtendAt i₀ x t))
          = fun t => ∫ x in Set.Ioc (0:ℝ) Bg, F (marginalExtendAt i₀ x t) from by
            funext t; exact hIocF t]
    rw [show (fun t : {l : Fin k // l ≠ i₀} → ℝ =>
            ∫ x in Set.Ioc (0:ℝ) Bg, F (marginalExtendAt i₀ x t))
          = fun t => ∫ x in (0:ℝ)..Bg, F (marginalExtendAt i₀ x t) from by
            funext t; exact (intervalIntegral.integral_of_le hBg0).symm]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcontF 0 Bg
  -- apply the abstract estimate
  refine le_trans (setIntegral_sq_orthant_error_le
    (ι := {l : Fin k // l ≠ i₀})
    (u := fun t => ∫ x in Set.Ioi (0:ℝ), Gtf (marginalExtendAt i₀ x t))
    (v := fun t => ∫ x in Set.Ioi (0:ℝ), F (marginalExtendAt i₀ x t))
    (a := (CF + el) * Bg) (b := CF * Bg) (δ := el * Bg) (B := Bg) (S := S)
    hBg0 (mul_nonneg (by linarith : (0:ℝ) ≤ CF + el) hBg0)
    (mul_nonneg hCF0 hBg0) (mul_nonneg hel hBg0)
    hu hv huv hU0 hV0 hUcont.measurable hVcont.measurable hS) ?_
  rw [card_subtype_ne i₀,
    show el * Bg * ((CF + el) * Bg + CF * Bg) * Bg ^ (k - 1)
      = el * Bg * (2 * CF * Bg + el * Bg) * Bg ^ (k - 1) from by ring]


end

end Commons.MeasureTheory.Integral