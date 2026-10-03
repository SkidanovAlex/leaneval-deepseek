import Mathlib
import Submission.Port.Aesm

/-!
# Marcinkiewicz-type interpolation between weak `(1,1)` and strong `(q,q)`

This file proves `Work.Analysis.Probability.interpolation_weak_one_strong_real`, the
interpolation step used in Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional
bilinear polynomial averages* (Annals 195 (2022)): a nonnegative, a.e. subadditive operator which
is weak `(1,1)` and strong `(q,q)` with `2 < q` is strong `(p,p)` for every `1 < p < q`, with the
explicit constant `(p (2 A₀/(p-1) + 2^q A₁^q/(q-p)))^(1/p)`.

The proof is the classical truncation argument: for each level `t > 0` split
`f = f 1_{|f|>t} + f 1_{|f|≤t}` and apply the weak `(1,1)` bound to the first piece (Markov at
level `t/2`) and the strong `(q,q)` bound to the second (Markov at level `t/2`), then integrate
the resulting pointwise bound against `p t^{p-1} dt` using the layer cake formula and two
one-dimensional tail computations.
-/

namespace Work.Analysis.Probability

open MeasureTheory
open scoped ENNReal

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

/-! ## `σ`-finiteness of `μ` restricted to the support of an `L^p` function -/

lemma sfinite_restrict_of_lintegral_lt_top {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {F : α → ℝ} (hF : Measurable F) (hFnn : 0 ≤ F) {p : ℝ} (hp : 0 < p)
    (hfin : ∫⁻ ω, ENNReal.ofReal (F ω) ^ p ∂μ ≠ ⊤) :
    MeasureTheory.SFinite (μ.restrict {ω | F ω ≠ 0}) := by
  have hd_meas : Measurable (fun ω => ENNReal.ofReal (F ω) ^ p) := hF.ennreal_ofReal.pow_const p
  have hkey : ∀ n : ℕ, μ {ω | 1 ≤ ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (F ω) ^ p} < ⊤ := by
    intro n
    refine lt_of_le_of_lt (MeasureTheory.meas_le_lintegral₀ (μ := μ)
      (f := fun ω => ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (F ω) ^ p)
      ((hd_meas.const_mul _).aemeasurable) (fun ω hω => hω)) ?_
    rw [MeasureTheory.lintegral_const_mul _ hd_meas]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (lt_top_iff_ne_top.mpr hfin)
  haveI : MeasureTheory.SigmaFinite (μ.restrict {ω | F ω ≠ 0}) := by
    refine ⟨⟨{
      set := fun n => {ω | F ω ≠ 0} ∩ {ω | 1 ≤ ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (F ω) ^ p}
        ∪ {ω | F ω = 0}
      set_mem := fun _ => trivial
      finite := fun n => ?_
      spanning := ?_ }⟩⟩
    · have hmeas : MeasurableSet ({ω | F ω ≠ 0} ∩
          {ω | 1 ≤ ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (F ω) ^ p} ∪ {ω | F ω = 0}) :=
        ((hF (measurableSet_singleton 0)).compl.inter
          (measurableSet_le measurable_const (hd_meas.const_mul _))).union
          (hF (measurableSet_singleton 0))
      rw [MeasureTheory.Measure.restrict_apply hmeas]
      refine lt_of_le_of_lt (measure_mono ?_) (hkey n)
      rintro ω ⟨h1, h2⟩
      rcases h1 with ⟨hA, hB⟩ | hC
      · exact hB
      · exact absurd hC (by simpa using h2)
    · rw [Set.eq_univ_iff_forall]
      intro ω
      rw [Set.mem_iUnion]
      by_cases h : F ω = 0
      · exact ⟨0, Or.inr h⟩
      · have hpos : 0 < F ω := lt_of_le_of_ne (hFnn ω) (Ne.symm h)
        have hp' : (0:ℝ) < (F ω) ^ p := Real.rpow_pos_of_pos hpos p
        obtain ⟨N, hN⟩ := exists_nat_gt (((F ω) ^ p)⁻¹)
        refine ⟨N, Or.inl ⟨h, ?_⟩⟩
        have hN' : 1 ≤ (N : ℝ) * (F ω) ^ p :=
          (inv_le_iff_one_le_mul₀ hp').mp (le_of_lt hN)
        have hb : 1 ≤ ((N + 1 : ℕ) : ℝ) * (F ω) ^ p := by
          have hle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
          nlinarith [Real.rpow_nonneg (le_of_lt hpos) p]
        calc (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) := (ENNReal.ofReal_one).symm
          _ ≤ ENNReal.ofReal (((N + 1 : ℕ) : ℝ) * (F ω) ^ p) := ENNReal.ofReal_le_ofReal hb
          _ = ((N + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (F ω) ^ p := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
                ENNReal.ofReal_rpow_of_nonneg (hFnn ω) hp.le]
  exact inferInstance

/-! ## One-dimensional power integrals -/

lemma lintegral_Ioi_rpow_neg {a c : ℝ} (ha : a < -1) (hc : 0 < c) :
    ∫⁻ t in Set.Ioi c, ENNReal.ofReal (t ^ a) ∂MeasureTheory.volume
      = ENNReal.ofReal (c ^ (a + 1) / (-(a + 1))) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (μ := MeasureTheory.volume.restrict (Set.Ioi c))
      (integrableOn_Ioi_rpow_of_lt ha hc) ?_]
  · rw [integral_Ioi_rpow_of_lt ha hc]
    congr 1
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (le_of_lt (lt_trans hc ht)) a

lemma lintegral_Ici_rpow_of_lt {a c : ℝ} (ha : a < -1) (hc : 0 < c) :
    ∫⁻ t in Set.Ici c, ENNReal.ofReal (t ^ a) ∂MeasureTheory.volume
      = ENNReal.ofReal (c ^ (a + 1) / (-(a + 1))) := by
  have hae : Set.Ici c =ᵐ[MeasureTheory.volume] Set.Ioi c := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · refine MeasureTheory.measure_mono_null (t := {c}) ?_ Real.volume_singleton
      intro t ht
      simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_Ioi] at ht
      exact le_antisymm (not_lt.mp ht.2) ht.1
    · rw [Set.sdiff_eq_empty.mpr (fun t ht => Set.mem_Ici.mpr ht.le), MeasureTheory.measure_empty]
  rw [show (∫⁻ t in Set.Ici c, ENNReal.ofReal (t ^ a) ∂MeasureTheory.volume)
      = ∫⁻ t in Set.Ioi c, ENNReal.ofReal (t ^ a) ∂MeasureTheory.volume from by
    rw [MeasureTheory.Measure.restrict_congr_set hae]]
  exact lintegral_Ioi_rpow_neg ha hc

lemma lower_tail_one_dim {p q c : ℝ} (hp : 0 < p) (hpq : p < q) (hc : 0 ≤ c) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal c ^ q * ENNReal.ofReal t ^ (p - 1 - q)
        * (if c ≤ t then 1 else 0) ∂MeasureTheory.volume
      = ENNReal.ofReal (c ^ p / (q - p)) := by
  have hqp : 0 < q - p := by linarith
  have ha : p - 1 - q < -1 := by linarith
  have hq0 : 0 < q := by linarith
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · subst hc0
    rw [show (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal 0 ^ q * ENNReal.ofReal t ^ (p-1-q)
        * (if (0:ℝ) ≤ t then 1 else 0) ∂MeasureTheory.volume) = 0 from ?_]
    · rw [Real.zero_rpow (ne_of_gt hp), zero_div, ENNReal.ofReal_zero]
    · refine MeasureTheory.lintegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards with t
      rw [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hq0]
      simp
  · have hmeas : Measurable (fun t : ℝ =>
        ENNReal.ofReal t ^ (p - 1 - q) * (if c ≤ t then 1 else 0)) :=
      ((measurable_id.ennreal_ofReal).pow_const _).mul
        (Measurable.ite (measurableSet_Ici) measurable_const measurable_const)
    have h1 : (∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal t ^ (p - 1 - q) * (if c ≤ t then 1 else 0) ∂MeasureTheory.volume)
        = ∫⁻ t in Set.Ici c, ENNReal.ofReal t ^ (p - 1 - q) ∂MeasureTheory.volume := by
      rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi]
      rw [show (∫⁻ t, (Set.Ioi (0:ℝ)).indicator (fun t => ENNReal.ofReal t ^ (p-1-q)
            * (if c ≤ t then 1 else 0)) t ∂MeasureTheory.volume)
          = ∫⁻ t, (Set.Ici c).indicator (fun t => ENNReal.ofReal t ^ (p-1-q)) t ∂MeasureTheory.volume from
          lintegral_congr (fun t => ?_)]
      · rw [MeasureTheory.lintegral_indicator measurableSet_Ici]
      · by_cases h : c ≤ t
        · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr (lt_of_lt_of_le hcpos h)), if_pos h, mul_one,
            Set.indicator_of_mem (Set.mem_Ici.mpr h)]
        · by_cases h0 : t ∈ Set.Ioi (0:ℝ)
          · rw [Set.indicator_of_mem h0, if_neg h, mul_zero,
              Set.indicator_of_notMem (fun hh => h (Set.mem_Ici.mp hh))]
          · rw [Set.indicator_of_notMem h0,
              Set.indicator_of_notMem (fun hh => h (Set.mem_Ici.mp hh))]
    have h2 : (∫⁻ t in Set.Ici c, ENNReal.ofReal t ^ (p - 1 - q) ∂MeasureTheory.volume)
        = ENNReal.ofReal (c ^ (p - q) / (q - p)) := by
      rw [show (∫⁻ t in Set.Ici c, ENNReal.ofReal t ^ (p - 1 - q) ∂MeasureTheory.volume)
          = ∫⁻ t in Set.Ici c, ENNReal.ofReal (t ^ (p - 1 - q)) ∂MeasureTheory.volume from ?_]
      · rw [lintegral_Ici_rpow_of_lt ha hcpos]
        congr 1
        rw [show (p - 1 - q) + 1 = p - q by ring]
        rw [div_eq_div_iff (by linarith) (by linarith)]
        ring
      · refine lintegral_congr_ae ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with t ht
        exact ENNReal.ofReal_rpow_of_pos (lt_of_lt_of_le hcpos (Set.mem_Ici.mp ht))
    calc ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal c ^ q * ENNReal.ofReal t ^ (p - 1 - q)
            * (if c ≤ t then 1 else 0) ∂MeasureTheory.volume
        = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal c ^ q
            * (ENNReal.ofReal t ^ (p - 1 - q) * (if c ≤ t then 1 else 0)) ∂MeasureTheory.volume :=
          lintegral_congr (fun t => by rw [mul_assoc])
      _ = ENNReal.ofReal c ^ q * (∫⁻ t in Set.Ioi (0 : ℝ),
            ENNReal.ofReal t ^ (p - 1 - q) * (if c ≤ t then 1 else 0) ∂MeasureTheory.volume) :=
          MeasureTheory.lintegral_const_mul _ hmeas
      _ = ENNReal.ofReal c ^ q * (∫⁻ t in Set.Ici c, ENNReal.ofReal t ^ (p - 1 - q) ∂MeasureTheory.volume) := by
          rw [h1]
      _ = ENNReal.ofReal c ^ q * ENNReal.ofReal (c ^ (p - q) / (q - p)) := by rw [h2]
      _ = ENNReal.ofReal (c ^ p / (q - p)) := by
          rw [ENNReal.ofReal_rpow_of_pos hcpos, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ c ^ q)]
          congr 1
          rw [div_eq_mul_inv, ← mul_assoc, ← Real.rpow_add' hc (by linarith : q + (p - q) ≠ 0)]
          ring_nf

/-! ## The lower tail (`t`-form) via Tonelli -/

/-- The lower-tail layer cake identity: if `∫ |f|^p < ∞` then
`∫_0^∞ (∫_{|f|≤t} |f|^q) t^{p-1-q} dt = (q-p)^{-1} ∫ |f|^p`.
The hypothesis is needed because `μ` is not assumed σ-finite. -/
theorem lower_tail_lintegral_rpow_t {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) (f : α → ℝ) (hf : Measurable f)
    (hfin : ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂μ ≠ ⊤) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
        (∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ)
          * ENNReal.ofReal (t ^ (p - 1 - q)) ∂MeasureTheory.volume
      = ENNReal.ofReal (1 / (q - p)) * ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂μ := by
  have hqp : 0 < q - p := by linarith
  have hq0 : 0 < q := by linarith
  have hfin' : ∫⁻ ω, ENNReal.ofReal (|f ω|) ^ p ∂μ ≠ ⊤ := by
    rw [show (∫⁻ ω, ENNReal.ofReal (|f ω|) ^ p ∂μ) = ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂μ from
      lintegral_congr (fun ω => ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le)]
    exact hfin
  haveI : MeasureTheory.SFinite (μ.restrict {ω | |f ω| ≠ 0}) :=
    sfinite_restrict_of_lintegral_lt_top hf.abs (fun ω => abs_nonneg _) hp hfin'
  set Ψ : ℝ → α → ENNReal := fun t ω =>
    ENNReal.ofReal (|f ω|) ^ q * ENNReal.ofReal t ^ (p - 1 - q) * (if |f ω| ≤ t then 1 else 0) with hΨ
  have hAf : MeasurableSet {ω : α | |f ω| ≠ 0} := by
    have h1 : {ω : α | |f ω| ≠ 0} = {ω | f ω ≠ 0} := by
      ext ω; simp only [Set.mem_setOf_eq, ne_eq, abs_eq_zero]
    rw [h1]
    exact (hf (measurableSet_singleton 0)).compl
  have hΨm : AEMeasurable (Function.uncurry Ψ)
      (((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (μ.restrict {ω | |f ω| ≠ 0}))) := by
    rw [hΨ]
    refine AEMeasurable.mul (AEMeasurable.mul ?_ ?_) ?_
    · exact ((hf.abs.ennreal_ofReal).comp measurable_snd).pow_const q |>.aemeasurable
    · exact ((measurable_fst.ennreal_ofReal).pow_const (p - 1 - q)).aemeasurable
    · exact (Measurable.ite (measurableSet_le (hf.abs.comp measurable_snd) measurable_fst)
        measurable_const measurable_const).aemeasurable
  have hswap := MeasureTheory.lintegral_lintegral_swap
    (μ := MeasureTheory.volume.restrict (Set.Ioi 0)) (ν := μ.restrict {ω | |f ω| ≠ 0})
    (f := Ψ) hΨm
  have hLHS : (∫⁻ t in Set.Ioi (0 : ℝ),
        (∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ)
          * ENNReal.ofReal (t ^ (p - 1 - q)) ∂MeasureTheory.volume)
      = ∫⁻ t in Set.Ioi (0 : ℝ), (∫⁻ ω in {ω | |f ω| ≠ 0}, Ψ t ω ∂μ)
          ∂MeasureTheory.volume := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hgm : Measurable (fun ω => ENNReal.ofReal (|f ω|) ^ q * (if |f ω| ≤ t then 1 else 0)) :=
      ((hf.abs.ennreal_ofReal).pow_const q).mul
        (Measurable.ite (measurableSet_le hf.abs measurable_const) measurable_const measurable_const)
    have hstep : (∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ)
        = ∫⁻ ω in {ω | |f ω| ≠ 0},
            ENNReal.ofReal (|f ω|) ^ q * (if |f ω| ≤ t then 1 else 0) ∂μ := by
      rw [show (∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ)
          = ∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω|) ^ q ∂μ from
          lintegral_congr (fun ω => (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le).symm)]
      rw [← MeasureTheory.lintegral_indicator (measurableSet_le hf.abs measurable_const),
        ← MeasureTheory.lintegral_indicator hAf]
      refine lintegral_congr (fun ω => ?_)
      by_cases h1 : |f ω| ≤ t
      · rw [Set.indicator_of_mem (show ω ∈ {ω | |f ω| ≤ t} from h1)]
        by_cases h0 : |f ω| = 0
        · rw [h0, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hq0,
            Set.indicator_of_notMem (show ω ∉ {ω | |f ω| ≠ 0} from by simpa using h0)]
        · rw [Set.indicator_of_mem (show ω ∈ {ω | |f ω| ≠ 0} from by simpa using h0),
            if_pos h1, mul_one]
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | |f ω| ≤ t} from h1),
          Set.indicator_of_mem (show ω ∈ {ω | |f ω| ≠ 0} from by
            simp only [Set.mem_setOf_eq, ne_eq]
            exact fun hh => h1 (by rw [hh]; exact ht0.le)),
          if_neg h1, mul_zero]
    have hfin2 : ∀ ω, Ψ t ω
        = (ENNReal.ofReal (|f ω|) ^ q * (if |f ω| ≤ t then 1 else 0))
            * ENNReal.ofReal t ^ (p - 1 - q) := fun ω => by rw [hΨ]; ring
    rw [hstep, ← ENNReal.ofReal_rpow_of_pos ht0, ← MeasureTheory.lintegral_mul_const _ hgm]
    refine lintegral_congr (fun ω => ?_)
    rw [hfin2 ω]
  have hRHS : (∫⁻ ω in {ω | |f ω| ≠ 0},
        ∫⁻ t in Set.Ioi (0 : ℝ), Ψ t ω ∂MeasureTheory.volume ∂μ)
      = ENNReal.ofReal (1 / (q - p)) * ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂μ := by
    have hinner : ∀ ω, (∫⁻ t in Set.Ioi (0 : ℝ), Ψ t ω ∂MeasureTheory.volume)
        = ENNReal.ofReal (|f ω| ^ p / (q - p)) := by
      intro ω
      rw [hΨ]
      exact lower_tail_one_dim hp hpq (abs_nonneg _)
    have hrestrict : (∫⁻ ω in {ω | |f ω| ≠ 0}, ENNReal.ofReal (|f ω| ^ p / (q - p)) ∂μ)
        = ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p / (q - p)) ∂μ := by
      rw [← MeasureTheory.lintegral_indicator hAf]
      refine lintegral_congr (fun ω => ?_)
      by_cases h0 : |f ω| = 0
      · rw [h0, Real.zero_rpow (ne_of_gt hp), zero_div, ENNReal.ofReal_zero,
          Set.indicator_of_notMem (show ω ∉ {ω | |f ω| ≠ 0} from by simpa using h0)]
      · rw [Set.indicator_of_mem (show ω ∈ {ω | |f ω| ≠ 0} from by simpa using h0)]
    calc (∫⁻ ω in {ω | |f ω| ≠ 0}, ∫⁻ t in Set.Ioi (0 : ℝ), Ψ t ω ∂MeasureTheory.volume ∂μ)
        = ∫⁻ ω in {ω | |f ω| ≠ 0}, ENNReal.ofReal (|f ω| ^ p / (q - p)) ∂μ :=
          lintegral_congr (fun ω => hinner ω)
      _ = ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p / (q - p)) ∂μ := hrestrict
      _ = ENNReal.ofReal (1 / (q - p)) * ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂μ := by
          rw [show (∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂μ)
              = ∫⁻ ω, ENNReal.ofReal (|f ω|) ^ p ∂μ from
              lintegral_congr (fun ω => (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le).symm)]
          rw [show (∫⁻ ω, ENNReal.ofReal (|f ω| ^ p / (q - p)) ∂μ)
              = ∫⁻ ω, ENNReal.ofReal (1 / (q - p)) * ENNReal.ofReal (|f ω|) ^ p ∂μ from
              lintegral_congr (fun ω => ?_)]
          · rw [MeasureTheory.lintegral_const_mul _ ((hf.abs.ennreal_ofReal).pow_const p)]
          · rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]
            rw [show (|f ω| ^ p / (q - p)) = (1 / (q - p)) * |f ω| ^ p by
              rw [div_eq_mul_inv, one_div, mul_comm]]
            rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1 / (q - p))]
  rw [← hLHS] at hswap
  rw [hRHS] at hswap
  exact hswap

/-! ## The upper tail identity -/

/-- The upper-tail layer cake identity: for `1 < p`,
`∫_0^∞ (∫_{t<|f|} |f|) t^{p-2} dt = (p-1)^{-1} ∫ |f|^p`. -/
theorem upper_tail_lintegral_rpow {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {p : ℝ} (hp : 1 < p) (f : α → ℝ) (hf : Measurable f) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
        (∫⁻ ω in {ω | t < |f ω|}, ENNReal.ofReal |f ω| ∂μ)
          * ENNReal.ofReal (t ^ (p - 2)) ∂MeasureTheory.volume
      = ENNReal.ofReal (1 / (p - 1)) * ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂μ := by
  have hp1 : (0:ℝ) < p - 1 := by linarith
  set g : α → ℝ := fun ω => |f ω| with hg
  have hgm : Measurable g := hf.abs
  have hgnn : 0 ≤ g := fun ω => abs_nonneg (f ω)
  have hd_meas : Measurable (fun ω => ENNReal.ofReal (g ω)) := hgm.ennreal_ofReal
  set ν := μ.withDensity (fun ω => ENNReal.ofReal (g ω)) with hν
  have hkey := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul (μ := ν)
      (ae_of_all _ hgnn) hgm.aemeasurable hp1
  have hL : ∫⁻ ω, ENNReal.ofReal (g ω ^ (p - 1)) ∂ν = ∫⁻ ω, ENNReal.ofReal (g ω ^ p) ∂μ := by
    have hrw : (fun ω => ENNReal.ofReal (g ω ^ (p-1))) = fun ω => ENNReal.ofReal (g ω) ^ (p-1) := by
      funext ω; exact (ENNReal.ofReal_rpow_of_nonneg (hgnn ω) hp1.le).symm
    rw [hrw, MeasureTheory.lintegral_withDensity_eq_lintegral_mul μ hd_meas
      (hd_meas.pow_const (p - 1))]
    refine lintegral_congr (fun ω => ?_)
    rw [Pi.mul_apply, ENNReal.ofReal_rpow_of_nonneg (hgnn ω) hp1.le,
      ← ENNReal.ofReal_mul (hgnn ω)]
    congr 1
    nth_rewrite 1 [← Real.rpow_one (g ω)]
    rw [← Real.rpow_add' (hgnn ω) (by linarith : (1:ℝ) + (p-1) ≠ 0)]
    ring_nf
  have hR : ∫⁻ t in Set.Ioi (0:ℝ), ν {a | t < g a} * ENNReal.ofReal (t ^ (p - 1 - 1))
      = ∫⁻ t in Set.Ioi (0:ℝ),
          (∫⁻ ω in {ω | t < g ω}, ENNReal.ofReal (g ω) ∂μ) * ENNReal.ofReal (t ^ (p - 2)) := by
    refine lintegral_congr (fun t => ?_)
    rw [MeasureTheory.withDensity_apply _ (measurableSet_lt measurable_const hgm)]
    congr 2
    ring_nf
  rw [hL, hR] at hkey
  rw [hkey, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1/(p-1)),
    one_div_mul_cancel (ne_of_gt hp1), ENNReal.ofReal_one, one_mul]

/-! ## From a pointwise estimate to an `L^p` estimate -/

/-- Taking `1/p`-th powers of an `L^p` bound. -/
theorem eLpNorm_le_of_lintegral_enorm_rpow_le {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {g h : α → ℝ} {p K : ℝ} (hp : 0 < p) (hK : 0 ≤ K)
    (hbound : ∫⁻ ω, enorm (g ω) ^ p ∂μ ≤ ENNReal.ofReal K * ∫⁻ ω, enorm (h ω) ^ p ∂μ)
    (hg : MeasureTheory.AEStronglyMeasurable g μ := by pw_aesm)
    (hh : MeasureTheory.AEStronglyMeasurable h μ := by pw_aesm) :
    MeasureTheory.eLpNorm g (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (K ^ (1 / p)) * MeasureTheory.eLpNorm h (ENNReal.ofReal p) μ := by
  have hp0 : (0:ℝ) < 1 / p := by positivity
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hg) (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top (f := g),
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hh) (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top (f := h)]
  simp only [ENNReal.toReal_ofReal hp.le]
  by_cases hBtop : (∫⁻ ω, enorm (h ω) ^ p ∂μ) = ⊤
  · rw [hBtop, ENNReal.top_rpow_of_pos hp0]
    by_cases hK0 : K = 0
    · have hA0 : (∫⁻ ω, enorm (g ω) ^ p ∂μ) ≤ 0 := by
        have hh := hbound
        rw [hK0] at hh
        simpa using hh
      have hAeq : (∫⁻ ω, enorm (g ω) ^ p ∂μ) = 0 := le_bot_iff.mp hA0
      rw [hAeq, hK0, ENNReal.zero_rpow_of_pos hp0, Real.zero_rpow (ne_of_gt hp0)]
      simp
    · have hCne : ENNReal.ofReal (K ^ (1 / p)) ≠ 0 := by
        rw [ENNReal.ofReal_ne_zero_iff]
        exact Real.rpow_pos_of_pos (lt_of_le_of_ne hK (Ne.symm hK0)) _
      rw [ENNReal.mul_top hCne]
      exact le_top
  · have hpow : ENNReal.ofReal (K ^ (1 / p)) ^ p = ENNReal.ofReal K := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hK (1/p)) hp.le]
      congr 1
      rw [← Real.rpow_mul hK (1 / p) p, one_div_mul_cancel (ne_of_gt hp), Real.rpow_one]
    have hkey : ENNReal.ofReal (K ^ (1 / p)) * (∫⁻ ω, enorm (h ω) ^ p ∂μ) ^ (1 / p)
        = (ENNReal.ofReal (K ^ (1/p)) ^ p * ∫⁻ ω, enorm (h ω) ^ p ∂μ) ^ (1 / p) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
        mul_one_div_cancel (ne_of_gt hp), ENNReal.rpow_one]
    rw [hkey, ENNReal.rpow_le_rpow_iff hp0, hpow]
    exact hbound

/-! ## The pointwise-in-`t` bound -/

/-- For each level `t > 0`, the weak `(1,1)` estimate applied to `f 1_{|f|>t}` and the strong
`(q,q)` estimate applied to `f 1_{|f|≤t}` (via Markov's inequality) give the pointwise bound. -/
theorem weak_type_one_strong_pointwise_bound {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (T : (α → ℝ) → α → ℝ) (hTnn : ∀ f, 0 ≤ T f) (hTmeas : ∀ f, Measurable (T f))
    (hsub : ∀ f g : α → ℝ, T (f + g) ≤ᵐ[μ] T f + T g)
    {A0 A1 q : ℝ} (hA0 : 0 < A0) (hA1 : 0 < A1) (hq : 2 < q)
    (hweak : ∀ f : α → ℝ, Measurable f → MeasureTheory.Integrable f μ → ∀ t : ℝ, 0 < t →
      μ {ω | t < T f ω} ≤ ENNReal.ofReal (A0 / t) * MeasureTheory.eLpNorm f 1 μ)
    (hstrong : ∀ f : α → ℝ, Measurable f → MeasureTheory.Integrable f μ →
      MeasureTheory.eLpNorm (T f) (ENNReal.ofReal q) μ
        ≤ ENNReal.ofReal A1 * MeasureTheory.eLpNorm f (ENNReal.ofReal q) μ)
    (f : α → ℝ) (hf : Measurable f) (hfint : MeasureTheory.Integrable f μ) {t : ℝ} (ht : 0 < t) :
    μ {ω | t < T f ω} ≤
      ENNReal.ofReal (2 * A0 / t) * (∫⁻ ω in {ω | t < |f ω|}, ENNReal.ofReal |f ω| ∂μ)
        + ENNReal.ofReal (2 ^ q * A1 ^ q / t ^ q) *
            (∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ) := by
  have hq0 : 0 < q := by linarith
  have ht2 : 0 < t/2 := by linarith
  have hq_ne0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq0
  have hq_netop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  set f₁ : α → ℝ := fun ω => if t < |f ω| then f ω else 0 with hf₁
  set f₂ : α → ℝ := fun ω => if |f ω| ≤ t then f ω else 0 with hf₂
  have hf₁app : ∀ ω, f₁ ω = if t < |f ω| then f ω else 0 := fun ω => by rw [hf₁]
  have hf₂app : ∀ ω, f₂ ω = if |f ω| ≤ t then f ω else 0 := fun ω => by rw [hf₂]
  have hf₁m : Measurable f₁ := by
    rw [hf₁]
    exact Measurable.ite (measurableSet_lt measurable_const hf.abs) hf measurable_const
  have hf₂m : Measurable f₂ := by
    rw [hf₂]
    exact Measurable.ite (measurableSet_le hf.abs measurable_const) hf measurable_const
  have hf₁le : ∀ ω, |f₁ ω| ≤ |f ω| := by
    intro ω
    rw [hf₁app ω]
    by_cases h : t < |f ω|
    · rw [if_pos h]
    · rw [if_neg h]; simp
  have hf₂le : ∀ ω, |f₂ ω| ≤ |f ω| := by
    intro ω
    rw [hf₂app ω]
    by_cases h : |f ω| ≤ t
    · rw [if_pos h]
    · rw [if_neg h]; simp
  have hf₁i : MeasureTheory.Integrable f₁ μ :=
    hfint.abs.mono' hf₁m.aestronglyMeasurable (ae_of_all _ (fun ω => by simpa [Real.norm_eq_abs] using hf₁le ω))
  have hf₂i : MeasureTheory.Integrable f₂ μ :=
    hfint.abs.mono' hf₂m.aestronglyMeasurable (ae_of_all _ (fun ω => by simpa [Real.norm_eq_abs] using hf₂le ω))
  have hsum : f₁ + f₂ = f := by
    funext ω
    by_cases hle : |f ω| ≤ t
    · have hlt : ¬ (t < |f ω|) := not_lt.mpr hle
      rw [Pi.add_apply, hf₁app ω, hf₂app ω, if_neg hlt, if_pos hle, zero_add]
    · have hlt : t < |f ω| := not_le.mp hle
      rw [Pi.add_apply, hf₁app ω, hf₂app ω, if_pos hlt, if_neg hle, add_zero]
  have hsub' : T f ≤ᵐ[μ] T f₁ + T f₂ := by
    have h := hsub f₁ f₂
    rwa [hsum] at h
  have hnull : μ {ω | ¬ (T f ω ≤ T f₁ ω + T f₂ ω)} = 0 := MeasureTheory.ae_iff.mp hsub'
  have hsub2 : {ω | t < T f ω} ⊆ ({ω | t/2 < T f₁ ω} ∪ {ω | t/2 < T f₂ ω})
      ∪ {ω | ¬ (T f ω ≤ T f₁ ω + T f₂ ω)} := by
    intro ω hω
    change t < T f ω at hω
    by_cases hle : T f ω ≤ T f₁ ω + T f₂ ω
    · left
      by_contra hcon
      rw [Set.mem_union, not_or] at hcon
      obtain ⟨h1, h2⟩ := hcon
      have h1' : T f₁ ω ≤ t/2 := not_lt.mp (by simpa using h1)
      have h2' : T f₂ ω ≤ t/2 := not_lt.mp (by simpa using h2)
      linarith
    · right
      exact hle
  have hmeasure : μ {ω | t < T f ω} ≤ μ {ω | t/2 < T f₁ ω} + μ {ω | t/2 < T f₂ ω} := by
    calc μ {ω | t < T f ω}
        ≤ μ (({ω | t/2 < T f₁ ω} ∪ {ω | t/2 < T f₂ ω}) ∪ {ω | ¬ (T f ω ≤ T f₁ ω + T f₂ ω)}) :=
          measure_mono hsub2
      _ ≤ μ ({ω | t/2 < T f₁ ω} ∪ {ω | t/2 < T f₂ ω}) + μ {ω | ¬ (T f ω ≤ T f₁ ω + T f₂ ω)} :=
          MeasureTheory.measure_union_le _ _
      _ = μ ({ω | t/2 < T f₁ ω} ∪ {ω | t/2 < T f₂ ω}) := by rw [hnull, add_zero]
      _ ≤ μ {ω | t/2 < T f₁ ω} + μ {ω | t/2 < T f₂ ω} := MeasureTheory.measure_union_le _ _
  have hE₁ : MeasureTheory.eLpNorm f₁ 1 μ = ∫⁻ ω in {ω | t < |f ω|}, ENNReal.ofReal |f ω| ∂μ := by
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
    simp only [Real.enorm_eq_ofReal_abs]
    rw [← MeasureTheory.lintegral_indicator (measurableSet_lt measurable_const hf.abs)]
    refine lintegral_congr (fun ω => ?_)
    by_cases h : t < |f ω|
    · rw [hf₁app ω, if_pos h, Set.indicator_of_mem (show ω ∈ {ω | t < |f ω|} from h)]
    · rw [hf₁app ω, if_neg h, Set.indicator_of_notMem (show ω ∉ {ω | t < |f ω|} from h),
        abs_zero, ENNReal.ofReal_zero]
  have hA : μ {ω | t/2 < T f₁ ω} ≤ ENNReal.ofReal (2 * A0 / t) *
      (∫⁻ ω in {ω | t < |f ω|}, ENNReal.ofReal |f ω| ∂μ) := by
    have h := hweak f₁ hf₁m hf₁i (t/2) ht2
    rw [hE₁] at h
    have hconst : ENNReal.ofReal (A0 / (t/2)) = ENNReal.ofReal (2 * A0 / t) := by
      have h1 : A0 / (t/2) = 2 * A0 / t := by field_simp
      rw [h1]
    rw [hconst] at h
    exact h
  have hE₂ : MeasureTheory.eLpNorm f₂ (ENNReal.ofReal q) μ ^ q
      = ∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq_ne0 hq_netop (f := f₂)]
    simp only [ENNReal.toReal_ofReal hq0.le]
    rw [← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hq0), ENNReal.rpow_one]
    rw [← MeasureTheory.lintegral_indicator (measurableSet_le hf.abs measurable_const)]
    refine lintegral_congr (fun ω => ?_)
    by_cases h : |f ω| ≤ t
    · rw [hf₂app ω, if_pos h, Set.indicator_of_mem (show ω ∈ {ω | |f ω| ≤ t} from h)]
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le]
    · rw [hf₂app ω, if_neg h, Set.indicator_of_notMem (show ω ∉ {ω | |f ω| ≤ t} from h)]
      rw [Real.enorm_eq_ofReal_abs, abs_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hq0]
  have hB : μ {ω | t/2 < T f₂ ω} ≤ ENNReal.ofReal (2 ^ q * A1 ^ q / t ^ q) *
      (∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ) := by
    have hstr := hstrong f₂ hf₂m hf₂i
    have hmarkov := MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm (μ := μ)
      (p := ENNReal.ofReal q) (f := T f₂) hq_ne0 hq_netop
      (ε := ENNReal.ofReal (t/2)) (by positivity) (fun hh => absurd hh ENNReal.ofReal_ne_top)
    simp only [ENNReal.toReal_ofReal hq0.le] at hmarkov
    have hsub'' : {ω | t/2 < T f₂ ω} ⊆ {x | ENNReal.ofReal (t/2) ≤ ‖T f₂ x‖ₑ} := by
      intro ω hω
      change t/2 < T f₂ ω at hω
      rw [Set.mem_setOf_eq, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hTnn f₂ ω)]
      exact ENNReal.ofReal_le_ofReal hω.le
    have hstep : (ENNReal.ofReal (t/2))⁻¹ ^ q = ENNReal.ofReal ((2/t)^q) := by
      have h1 : (t/2)⁻¹ = 2/t := by rw [inv_div]
      rw [← ENNReal.ofReal_inv_of_pos ht2, h1,
        ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ 2/t) hq0.le]
    have hmul : (ENNReal.ofReal A1 * MeasureTheory.eLpNorm f₂ (ENNReal.ofReal q) μ) ^ q
        = ENNReal.ofReal (A1^q) * MeasureTheory.eLpNorm f₂ (ENNReal.ofReal q) μ ^ q := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ENNReal.ofReal_rpow_of_nonneg hA1.le hq0.le]
    have hmid : (ENNReal.ofReal (t/2))⁻¹ ^ q * MeasureTheory.eLpNorm (T f₂) (ENNReal.ofReal q) μ ^ q
        ≤ (ENNReal.ofReal (t/2))⁻¹ ^ q
          * (ENNReal.ofReal A1 * MeasureTheory.eLpNorm f₂ (ENNReal.ofReal q) μ) ^ q := by
      refine mul_le_mul_right ?_ _
      exact ENNReal.rpow_le_rpow hstr hq0.le
    have hfinal : (ENNReal.ofReal (t/2))⁻¹ ^ q
          * (ENNReal.ofReal A1 * MeasureTheory.eLpNorm f₂ (ENNReal.ofReal q) μ) ^ q
        = ENNReal.ofReal (2^q * A1^q / t^q) * (∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ) := by
      rw [hstep, hmul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2/t)^q), hE₂,
        show (2/t)^q * A1^q = 2^q * A1^q / t^q by
          rw [Real.div_rpow (by norm_num) (le_of_lt ht)]; ring]
    exact ((measure_mono hsub'').trans hmarkov).trans (hmid.trans hfinal.le)
  exact hmeasure.trans (add_le_add hA hB)

/-! ## The interpolation theorem -/

theorem interpolation_weak_one_strong_real {q : ℝ} (hq : 2 < q) :
    ∀ {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
      (T : (α → ℝ) → α → ℝ) (hTnn : ∀ f, 0 ≤ T f) (hTmeas : ∀ f, Measurable (T f))
      (hsub : ∀ f g : α → ℝ, T (f + g) ≤ᵐ[μ] T f + T g)
      {A0 A1 p : ℝ} (hA0 : 0 < A0) (hA1 : 0 < A1) (hp1 : 1 < p) (hpq : p < q)
      (hweak : ∀ f : α → ℝ, Measurable f → MeasureTheory.Integrable f μ → ∀ t : ℝ, 0 < t →
        μ {ω | t < T f ω} ≤ ENNReal.ofReal (A0 / t) * MeasureTheory.eLpNorm f 1 μ)
      (hstrong : ∀ f : α → ℝ, Measurable f → MeasureTheory.Integrable f μ →
        MeasureTheory.eLpNorm (T f) (ENNReal.ofReal q) μ
          ≤ ENNReal.ofReal A1 * MeasureTheory.eLpNorm f (ENNReal.ofReal q) μ),
      ∀ f : α → ℝ, Measurable f → MeasureTheory.MemLp f (ENNReal.ofReal p) μ →
        MeasureTheory.Integrable f μ →
        MeasureTheory.eLpNorm (T f) (ENNReal.ofReal p) μ
          ≤ ENNReal.ofReal ((p * (2 * A0 / (p - 1) + 2 ^ q * A1 ^ q / (q - p))) ^ (1 / p))
            * MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ := by
  intro α _ μ T hTnn hTmeas hsub A0 A1 p hA0 hA1 hp1 hpq hweak hstrong f hf hfLp hfint
  have hp0 : (0:ℝ) < p := by linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hp1' : (0:ℝ) < p - 1 := by linarith
  have hqp : (0:ℝ) < q - p := by linarith
  have hfin : ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂μ ≠ ⊤ := by
    have h1 : (∫⁻ ω, ENNReal.ofReal (|f ω|) ^ p ∂μ) < ⊤ := by
      rw [show (∫⁻ ω, ENNReal.ofReal (|f ω|) ^ p ∂μ) = ∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ from
        lintegral_congr (fun ω => by rw [Real.enorm_eq_ofReal_abs])]
      rw [show (∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ)
          = ∫⁻ ω, ‖f ω‖ₑ ^ (ENNReal.ofReal p).toReal ∂μ from by
        rw [ENNReal.toReal_ofReal hp0.le]]
      rw [← MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (hf := by pw_aesm)
        (p := ENNReal.ofReal p) (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top]
      exact hfLp.eLpNorm_lt_top
    rw [show (∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂μ) = ∫⁻ ω, ENNReal.ofReal (|f ω|) ^ p ∂μ from
      lintegral_congr (fun ω => (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le).symm)]
    exact ne_of_lt h1
  have hXmono : Antitone (fun t : ℝ => ∫⁻ ω in {ω | t < |f ω|}, ENNReal.ofReal |f ω| ∂μ) := by
    intro s t hst
    exact MeasureTheory.lintegral_mono_set (fun ω hω => lt_of_le_of_lt hst hω)
  have hYmono : Monotone (fun t : ℝ => ∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ) := by
    intro s t hst
    exact MeasureTheory.lintegral_mono_set (fun ω hω => le_trans hω hst)
  have hpoint : ∀ t : ℝ, 0 < t →
      μ {ω | t < T f ω} * ENNReal.ofReal t ^ (p - 1)
        ≤ ENNReal.ofReal (2 * A0) * ((∫⁻ ω in {ω | t < |f ω|}, ENNReal.ofReal |f ω| ∂μ)
              * ENNReal.ofReal t ^ (p - 2))
          + ENNReal.ofReal (2 ^ q * A1 ^ q)
              * ((∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ)
                  * ENNReal.ofReal t ^ (p - 1 - q)) := by
    intro t ht
    have hPBt := weak_type_one_strong_pointwise_bound T hTnn hTmeas hsub hA0 hA1 hq hweak hstrong f hf hfint ht
    have h1 := mul_le_mul_left hPBt (ENNReal.ofReal t ^ (p - 1))
    refine h1.trans (le_of_eq ?_)
    rw [add_mul]
    congr 1
    · have e1 : ENNReal.ofReal (2 * A0 / t) * ENNReal.ofReal t ^ (p - 1)
          = ENNReal.ofReal (2 * A0) * ENNReal.ofReal t ^ (p - 2) := by
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * A0),
          ENNReal.ofReal_inv_of_pos ht]
        rw [mul_assoc, ← ENNReal.rpow_neg_one,
          ← ENNReal.rpow_add (-1) (p - 1) (ENNReal.ofReal_ne_zero_iff.mpr ht) ENNReal.ofReal_ne_top,
          show (-1:ℝ) + (p - 1) = p - 2 by ring]
      rw [show ENNReal.ofReal (2 * A0 / t) * (∫⁻ ω in {ω | t < |f ω|}, ENNReal.ofReal |f ω| ∂μ)
            * ENNReal.ofReal t ^ (p - 1)
          = (ENNReal.ofReal (2 * A0 / t) * ENNReal.ofReal t ^ (p - 1))
            * (∫⁻ ω in {ω | t < |f ω|}, ENNReal.ofReal |f ω| ∂μ) by ring,
        e1]
      ring
    · have e2 : ENNReal.ofReal (2 ^ q * A1 ^ q / t ^ q) * ENNReal.ofReal t ^ (p - 1)
          = ENNReal.ofReal (2 ^ q * A1 ^ q) * ENNReal.ofReal t ^ (p - 1 - q) := by
        rw [ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos ht q),
          ← ENNReal.ofReal_rpow_of_pos ht, div_eq_mul_inv, mul_assoc,
          ← ENNReal.rpow_neg (ENNReal.ofReal t) q,
          ← ENNReal.rpow_add (-q) (p - 1) (ENNReal.ofReal_ne_zero_iff.mpr ht) ENNReal.ofReal_ne_top,
          show (-q:ℝ) + (p - 1) = p - 1 - q by ring]
      rw [show ENNReal.ofReal (2 ^ q * A1 ^ q / t ^ q)
            * (∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ)
            * ENNReal.ofReal t ^ (p - 1)
          = (ENNReal.ofReal (2 ^ q * A1 ^ q / t ^ q) * ENNReal.ofReal t ^ (p - 1))
            * (∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ) by ring,
        e2]
      ring
  set J := ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂μ with hJ
  set I1 := ∫⁻ t in Set.Ioi (0:ℝ),
    (∫⁻ ω in {ω | t < |f ω|}, ENNReal.ofReal |f ω| ∂μ) * ENNReal.ofReal t ^ (p - 2) ∂MeasureTheory.volume with hI1
  set I2 := ∫⁻ t in Set.Ioi (0:ℝ),
    (∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ) * ENNReal.ofReal t ^ (p - 1 - q) ∂MeasureTheory.volume with hI2
  have hBmeas : Measurable (fun t : ℝ => ENNReal.ofReal (2 ^ q * A1 ^ q)
      * ((∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ)
          * ENNReal.ofReal t ^ (p - 1 - q))) :=
    measurable_const.mul (hYmono.measurable.mul (measurable_id.ennreal_ofReal.pow_const _))
  have h2 : (∫⁻ t in Set.Ioi (0:ℝ), μ {a | t < T f a} * ENNReal.ofReal (t ^ (p - 1)) ∂MeasureTheory.volume)
      ≤ ENNReal.ofReal (2 * A0) * I1 + ENNReal.ofReal (2 ^ q * A1 ^ q) * I2 := by
    calc (∫⁻ t in Set.Ioi (0:ℝ), μ {a | t < T f a} * ENNReal.ofReal (t ^ (p - 1)) ∂MeasureTheory.volume)
        = ∫⁻ t in Set.Ioi (0:ℝ), μ {a | t < T f a} * ENNReal.ofReal t ^ (p - 1) ∂MeasureTheory.volume := by
          refine lintegral_congr_ae ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
          rw [ENNReal.ofReal_rpow_of_pos ht]
      _ ≤ ∫⁻ t in Set.Ioi (0:ℝ), (ENNReal.ofReal (2 * A0)
              * ((∫⁻ ω in {ω | t < |f ω|}, ENNReal.ofReal |f ω| ∂μ) * ENNReal.ofReal t ^ (p - 2))
            + ENNReal.ofReal (2 ^ q * A1 ^ q)
              * ((∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ)
                  * ENNReal.ofReal t ^ (p - 1 - q))) ∂MeasureTheory.volume := by
          refine lintegral_mono_ae ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
          exact hpoint t ht
      _ = ENNReal.ofReal (2 * A0) * I1 + ENNReal.ofReal (2 ^ q * A1 ^ q) * I2 := by
          rw [MeasureTheory.lintegral_add_right _ hBmeas,
            MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hT1' : I1 = ENNReal.ofReal (1 / (p - 1)) * J := by
    rw [hI1]
    rw [show (∫⁻ t in Set.Ioi (0:ℝ),
          (∫⁻ ω in {ω | t < |f ω|}, ENNReal.ofReal |f ω| ∂μ) * ENNReal.ofReal t ^ (p - 2) ∂MeasureTheory.volume)
        = ∫⁻ t in Set.Ioi (0:ℝ),
          (∫⁻ ω in {ω | t < |f ω|}, ENNReal.ofReal |f ω| ∂μ) * ENNReal.ofReal (t ^ (p - 2)) ∂MeasureTheory.volume from by
        refine lintegral_congr_ae ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
        rw [ENNReal.ofReal_rpow_of_pos ht]]
    exact upper_tail_lintegral_rpow hp1 f hf
  have hT2' : I2 = ENNReal.ofReal (1 / (q - p)) * J := by
    rw [hI2]
    rw [show (∫⁻ t in Set.Ioi (0:ℝ),
          (∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ) * ENNReal.ofReal t ^ (p - 1 - q) ∂MeasureTheory.volume)
        = ∫⁻ t in Set.Ioi (0:ℝ),
          (∫⁻ ω in {ω | |f ω| ≤ t}, ENNReal.ofReal (|f ω| ^ q) ∂μ) * ENNReal.ofReal (t ^ (p - 1 - q)) ∂MeasureTheory.volume from by
        refine lintegral_congr_ae ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
        rw [ENNReal.ofReal_rpow_of_pos ht]]
    exact lower_tail_lintegral_rpow_t hp0 hpq f hf hfin
  have harith : ENNReal.ofReal p * (ENNReal.ofReal (2 * A0) * (ENNReal.ofReal (1 / (p - 1)) * J)
        + ENNReal.ofReal (2 ^ q * A1 ^ q) * (ENNReal.ofReal (1 / (q - p)) * J))
      = ENNReal.ofReal (p * (2 * A0 / (p - 1) + 2 ^ q * A1 ^ q / (q - p))) * J := by
    have h1 : ENNReal.ofReal (2 * A0 * (1 / (p - 1))) = ENNReal.ofReal (2 * A0 / (p - 1)) := by
      congr 1
      ring
    have h2 : ENNReal.ofReal (2 ^ q * A1 ^ q * (1 / (q - p)))
        = ENNReal.ofReal (2 ^ q * A1 ^ q / (q - p)) := by
      congr 1
      ring
    have hA' : ENNReal.ofReal (2 * A0) * (ENNReal.ofReal (1 / (p - 1)) * J)
        = ENNReal.ofReal (2 * A0 / (p - 1)) * J := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * A0), h1]
    have hB' : ENNReal.ofReal (2 ^ q * A1 ^ q) * (ENNReal.ofReal (1 / (q - p)) * J)
        = ENNReal.ofReal (2 ^ q * A1 ^ q / (q - p)) * J := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 ^ q * A1 ^ q), h2]
    rw [hA', hB', ← add_mul,
      ← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 2 * A0 / (p - 1))
        (by positivity : (0:ℝ) ≤ 2 ^ q * A1 ^ q / (q - p)),
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ p)]
  have hmain : ∫⁻ ω, ENNReal.ofReal ((T f ω) ^ p) ∂μ
      ≤ ENNReal.ofReal (p * (2 * A0 / (p - 1) + 2 ^ q * A1 ^ q / (q - p))) * J := by
    rw [MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul (μ := μ) (f := T f)
      (ae_of_all _ (hTnn f)) (hTmeas f).aemeasurable hp0]
    rw [hT1', hT2'] at h2
    exact (mul_le_mul_right h2 _).trans (le_of_eq harith)
  have hK : (0:ℝ) ≤ p * (2 * A0 / (p - 1) + 2 ^ q * A1 ^ q / (q - p)) := by positivity
  have hen : (∫⁻ ω, ‖T f ω‖ₑ ^ p ∂μ) ≤ ENNReal.ofReal (p * (2 * A0 / (p - 1) + 2 ^ q * A1 ^ q / (q - p)))
      * (∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ) := by
    rw [show (∫⁻ ω, ‖T f ω‖ₑ ^ p ∂μ) = ∫⁻ ω, ENNReal.ofReal ((T f ω) ^ p) ∂μ from
      lintegral_congr (fun ω => by rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hTnn f ω),
        ENNReal.ofReal_rpow_of_nonneg (hTnn f ω) hp0.le])]
    rw [show (∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ) = ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂μ from
      lintegral_congr (fun ω => by rw [Real.enorm_eq_ofReal_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le])]
    rw [← hJ]
    exact hmain
  exact eLpNorm_le_of_lintegral_enorm_rpow_le hp0 hK hen

end Work.Analysis.Probability
