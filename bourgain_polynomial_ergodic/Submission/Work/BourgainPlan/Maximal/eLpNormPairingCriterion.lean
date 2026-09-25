import Mathlib
import Submission.Commons.Analysis.Integral.integrable_of_bound_of_support_subset
import Submission.Commons.Analysis.InnerProductSpace.inner_smul_rpow_smul_self
import Submission.Commons.Analysis.InnerProductSpace.norm_smul_rpow_smul_self

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal

/-- A function which is a.e. strongly measurable, bounded and supported on a set of finite
measure belongs to every `L^r`. -/
private lemma memLp_of_bound_of_support_subset {f : ℝ → ℂ} (r : ENNReal) {S : Set ℝ} {C : ℝ}
    (hS : MeasurableSet S) (hSfin : volume S ≠ ⊤) (hsm : AEStronglyMeasurable f volume)
    (hb : ∀ x, ‖f x‖ ≤ C) (hsupp : ∀ x, x ∉ S → f x = 0) : MemLp f r volume := by
  haveI : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hSfin⟩
  have hfs : f = S.indicator f := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hsupp x hx]
  rw [hfs, memLp_indicator_iff_restrict hS]
  exact MemLp.of_bound (hsm.mono_measure Measure.restrict_le_self) C (Filter.Eventually.of_forall hb)

/-- `‖z‖ₑ = ofReal ‖z‖` for a real number `z ≥ 0`. -/
private lemma enorm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : enorm ((r : ℂ)) = ENNReal.ofReal r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

/-- Taking a positive power commutes with a supremum in `ℝ≥0∞`.  Local copy to avoid
importing `Commons.Analysis.MeasureTheory.iSup_rpow_eq` (which would clash with other modules). -/
private lemma iSup_rpow_eq' {ι : Type*} (a : ι → ℝ≥0∞) {q : ℝ} (hq : 0 < q) :
    (⨆ i, a i) ^ q = ⨆ i, (a i) ^ q := by
  have h := (ENNReal.orderIsoRpow q hq).map_iSup a
  rw [ENNReal.orderIsoRpow_apply] at h
  exact h

/-- Monotone convergence for the `L^p` seminorm, for a monotone sequence of *measurable*
`ℝ≥0∞`-valued functions.  Local copy of
`Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone`, re-proved here (via
`lintegral_iSup`) so that this module does not depend on that one. -/
private lemma eLpNorm_iSup_of_monotone_meas {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {P : ENNReal} (hP0 : P ≠ 0) (hPtop : P ≠ ⊤) {u : ℕ → α → ℝ≥0∞}
    (hu : ∀ n, Measurable (u n)) (hmono : Monotone u) :
    MeasureTheory.eLpNorm (fun x => ⨆ n, u n x) P μ = ⨆ n, MeasureTheory.eLpNorm (u n) P μ := by
  have hq_pos : 0 < P.toReal := ENNReal.toReal_pos hP0 hPtop
  have hInt : ∫⁻ x, ‖(⨆ n, u n x)‖ₑ ^ P.toReal ∂μ
      = ⨆ n, ∫⁻ x, ‖u n x‖ₑ ^ P.toReal ∂μ := by
    have hcongr : (fun x => ‖(⨆ n, u n x)‖ₑ ^ P.toReal)
        = fun x => ⨆ n, ‖u n x‖ₑ ^ P.toReal := by
      funext x
      simp only [enorm_eq_self]
      exact iSup_rpow_eq' _ hq_pos
    rw [hcongr]
    refine lintegral_iSup ?_ ?_
    · intro n
      exact ENNReal.continuous_rpow_const.measurable.comp (hu n)
    · intro n m hnm x
      exact ENNReal.rpow_le_rpow (by simpa only [enorm_eq_self] using hmono hnm x) hq_pos.le
  calc MeasureTheory.eLpNorm (fun x => ⨆ n, u n x) P μ
      = (∫⁻ x, ‖(⨆ n, u n x)‖ₑ ^ P.toReal ∂μ) ^ (1 / P.toReal) :=
        MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop
          (Measurable.iSup hu).aestronglyMeasurable
    _ = (⨆ n, ∫⁻ x, ‖u n x‖ₑ ^ P.toReal ∂μ) ^ (1 / P.toReal) := by rw [hInt]
    _ = ⨆ n, (∫⁻ x, ‖u n x‖ₑ ^ P.toReal ∂μ) ^ (1 / P.toReal) :=
        iSup_rpow_eq' _ (one_div_pos.mpr hq_pos)
    _ = ⨆ n, MeasureTheory.eLpNorm (u n) P μ := by
        refine iSup_congr fun n => ?_
        rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop (hu n).aestronglyMeasurable]

/-- Riesz duality criterion, with no boundedness or MemLp hypothesis on h: if 1 < p, h is a.e.
strongly measurable and finite E satisfies the pairing bound against every test function in
L^2 ∩ L^q (q = p/(p-1)), then eLpNorm h (ofReal p) ≤ E.

This is the statement of Work.BourgainPlan.Maximal.eLpNorm_le_of_pairing_bound_memLp in
Submission/Work/BourgainPlan/Maximal/eLpNorm_le_of_pairing_bound_memLp.lean with its unused MemLp
hypothesis dropped, re-proved in a fresh module because that module imports
Submission.Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone_aemeasurable, which redeclares
Commons.Analysis.MeasureTheory.iSup_rpow_eq and therefore cannot be imported here.

Suggested proof: copy that file's proof body verbatim (the extremal truncated test function
F n = {s n}.indicator (fun y => (norm (h' y) ^ (p - 2)) smul h' y), with
s n = {x | norm (h' x) ≤ n+1} ∩ {x | 1/(n+1) ≤ norm (h' x)} ∩ Icc (-n) n).  The three private
helper lemmas used there (memLp_of_bound_of_support_subset, enorm_ofReal_of_nonneg) can be copied or
replaced by the importable Commons modules
Submission.Commons.Analysis.Integral.integrable_of_bound_of_support_subset,
Submission.Commons.Analysis.Lp.ofReal_integral_norm_rpow_eq_lintegral_enorm_rpow,
Submission.Commons.Analysis.InnerProductSpace.inner_smul_rpow_smul_self and
Submission.Commons.Analysis.InnerProductSpace.norm_smul_rpow_smul_self (all of which build fine
alongside the rest of this workspace).  Only the final monotone-convergence step must be replaced:
instead of Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone_aemeasurable, show
(eLpNorm h' (ofReal p))^p = (iSup n, eLpNorm (G n) (ofReal p))^p, where G n = {s n}.indicator h',
by combining (i) (eLpNorm f (ofReal p))^p = ∫⁻ x, ‖f x‖^p (from
eLpNorm_eq_lintegral_rpow_enorm_toReal plus ENNReal.rpow_mul), (ii) the pointwise identity
‖h' x‖^p = ⨆ n, ‖G n x‖^p, (iii) Mathlib's MeasureTheory.lintegral_iSup' (needs only AEMeasurable of
each summand and pointwise monotonicity), and (iv) the order-isomorphism
ENNReal.orderIsoRpow p (0 < p) to move the power out of the supremum.  Then use
ENNReal.rpow_le_rpow_iff (or rpow_left_injective) to conclude eLpNorm h' (ofReal p) ≤ E from the
already-established bound ofReal ((∫ A n)^(1/p)) ≤ E for every n. -/
theorem eLpNormPairingCriterion (h : ℝ → ℂ) {p : ℝ} (hp : 1 < p)
    (hsm : MeasureTheory.AEStronglyMeasurable h (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (E : ENNReal) (hE : E ≠ ⊤)
    (hpair : ∀ g : ℝ → ℂ,
      MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      MeasureTheory.MemLp g (ENNReal.ofReal (p / (p - 1))) (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      enorm (∫ x : ℝ, inner ℂ (h x) (g x))
        ≤ E * MeasureTheory.eLpNorm g (ENNReal.ofReal (p / (p - 1))) (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    MeasureTheory.eLpNorm h (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ) ≤ E := by
  classical
  obtain ⟨h', h'm, hh'⟩ := hsm
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hp1_pos : 0 < p - 1 := by linarith
  have hp1_ne : p - 1 ≠ 0 := hp1_pos.ne'
  have hq_pos : 0 < p / (p - 1) := div_pos hp_pos hp1_pos
  have hq_ne : p / (p - 1) ≠ 0 := hq_pos.ne'
  have hP0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp_pos).ne'
  have hPtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hQ0 : ENNReal.ofReal (p / (p - 1)) ≠ 0 := (ENNReal.ofReal_pos.mpr hq_pos).ne'
  have hQtop : ENNReal.ofReal (p / (p - 1)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqinv_pos : 0 < 1 / (p / (p - 1)) := one_div_pos.mpr hq_pos
  have h1q : (1 : ℝ) - 1 / (p / (p - 1)) = 1 / p := by
    field_simp
    ring
  have hmulq : (p - 1) * (p / (p - 1)) = p := by
    rw [← mul_div_assoc, mul_comm (p - 1) p, mul_div_cancel_right₀ p hp1_ne]
  -- ### the truncation sets
  set s : ℕ → Set ℝ := fun n =>
    {x : ℝ | ‖h' x‖ ≤ (n : ℝ) + 1} ∩ {x : ℝ | 1 / ((n : ℝ) + 1) ≤ ‖h' x‖}
      ∩ Set.Icc (-(n : ℝ)) (n : ℝ) with hs_def
  have hs_meas : ∀ n, MeasurableSet (s n) := by
    intro n
    show MeasurableSet ({x : ℝ | ‖h' x‖ ≤ (n : ℝ) + 1} ∩ {x : ℝ | 1 / ((n : ℝ) + 1) ≤ ‖h' x‖}
      ∩ Set.Icc (-(n : ℝ)) (n : ℝ))
    exact ((measurableSet_le h'm.norm.measurable measurable_const).inter
      (measurableSet_le measurable_const h'm.norm.measurable)).inter measurableSet_Icc
  have hs_ub : ∀ n x, x ∈ s n → ‖h' x‖ ≤ (n : ℝ) + 1 := by
    intro n x hx
    have := hx
    simp only [hs_def, Set.mem_inter_iff, Set.mem_ofPred_eq] at this
    exact this.1.1
  have hs_lb : ∀ n x, x ∈ s n → 1 / ((n : ℝ) + 1) ≤ ‖h' x‖ := by
    intro n x hx
    have := hx
    simp only [hs_def, Set.mem_inter_iff, Set.mem_ofPred_eq] at this
    exact this.1.2
  have hs_Icc : ∀ n x, x ∈ s n → x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) := by
    intro n x hx
    have := hx
    simp only [hs_def, Set.mem_inter_iff, Set.mem_ofPred_eq] at this
    exact this.2
  have hs_fin : ∀ n, volume (s n) ≠ ⊤ := by
    intro n
    refine ne_top_of_le_ne_top ?_ (measure_mono (hs_Icc n))
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hs_mono : Monotone s := by
    intro m n hmn x hx
    have hmn' : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
    have h1 := hs_ub m x hx
    have h2 := hs_lb m x hx
    have h3 := hs_Icc m x hx
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · show ‖h' x‖ ≤ (n : ℝ) + 1
      linarith
    · show 1 / ((n : ℝ) + 1) ≤ ‖h' x‖
      have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    · show -(n : ℝ) ≤ x
      linarith [h3.1]
    · show x ≤ (n : ℝ)
      linarith [h3.2]
  -- ### the truncations
  set A : ℕ → ℝ → ℝ := fun n => (s n).indicator (fun x => ‖h' x‖ ^ p) with hA_def
  set G : ℕ → ℝ → ℂ := fun n => (s n).indicator h' with hG_def
  set F : ℕ → ℝ → ℂ :=
    fun n => (s n).indicator (fun y => (‖h' y‖ ^ (p - 2)) • h' y) with hF_def
  have hA_of_mem : ∀ n x, x ∈ s n → A n x = ‖h' x‖ ^ p := by
    intro n x hx
    show (s n).indicator (fun x => ‖h' x‖ ^ p) x = ‖h' x‖ ^ p
    exact Set.indicator_of_mem hx _
  have hA_of_notMem : ∀ n x, x ∉ s n → A n x = 0 := by
    intro n x hx
    show (s n).indicator (fun x => ‖h' x‖ ^ p) x = 0
    exact Set.indicator_of_notMem hx _
  have hG_of_mem : ∀ n x, x ∈ s n → G n x = h' x := by
    intro n x hx
    show (s n).indicator h' x = h' x
    exact Set.indicator_of_mem hx _
  have hG_of_notMem : ∀ n x, x ∉ s n → G n x = 0 := by
    intro n x hx
    show (s n).indicator h' x = 0
    exact Set.indicator_of_notMem hx _
  have hF_of_mem : ∀ n x, x ∈ s n → F n x = (‖h' x‖ ^ (p - 2)) • h' x := by
    intro n x hx
    show (s n).indicator (fun y => (‖h' y‖ ^ (p - 2)) • h' y) x = (‖h' x‖ ^ (p - 2)) • h' x
    exact Set.indicator_of_mem hx _
  have hF_of_notMem : ∀ n x, x ∉ s n → F n x = 0 := by
    intro n x hx
    show (s n).indicator (fun y => (‖h' y‖ ^ (p - 2)) • h' y) x = 0
    exact Set.indicator_of_notMem hx _
  have hA_nn : ∀ n x, 0 ≤ A n x := by
    intro n x
    by_cases hx : x ∈ s n
    · rw [hA_of_mem n x hx]
      exact Real.rpow_nonneg (norm_nonneg _) p
    · rw [hA_of_notMem n x hx]
  have hA_int : ∀ n, Integrable (A n) := by
    intro n
    refine Commons.Analysis.Integral.integrable_of_bound_of_support_subset (C := ((n : ℝ) + 1) ^ p)
      (hs_meas n) (hs_fin n) ?_ ?_ ?_
    · show AEStronglyMeasurable ((s n).indicator (fun x => ‖h' x‖ ^ p)) volume
      exact (((by fun_prop : Measurable fun t : ℝ => t ^ p).comp h'm.norm.measurable).aestronglyMeasurable).indicator (hs_meas n)
    · intro x
      by_cases hx : x ∈ s n
      · rw [hA_of_mem n x hx, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
        exact Real.rpow_le_rpow (norm_nonneg _) (hs_ub n x hx) hp_pos.le
      · rw [hA_of_notMem n x hx, norm_zero]
        exact Real.rpow_nonneg (by positivity) p
    · intro x hx
      exact hA_of_notMem n x hx
  have hF_sm : ∀ n, AEStronglyMeasurable (F n) volume := by
    intro n
    have hinner : AEStronglyMeasurable (fun y : ℝ => (‖h' y‖ ^ (p - 2)) • h' y) volume := by
      have h1 : AEMeasurable (fun y : ℝ => ‖h' y‖ ^ (p - 2)) volume :=
        ((by fun_prop : Measurable fun t : ℝ => t ^ (p - 2))).comp_aemeasurable
          h'm.norm.measurable.aemeasurable
      exact h1.aestronglyMeasurable.smul h'm.aestronglyMeasurable
    show AEStronglyMeasurable ((s n).indicator (fun y => (‖h' y‖ ^ (p - 2)) • h' y)) volume
    exact hinner.indicator (hs_meas n)
  have hG_meas : ∀ n, Measurable (G n) := fun n => h'm.measurable.indicator (hs_meas n)
  have hF_norm_mem : ∀ n x, x ∈ s n → ‖F n x‖ = ‖h' x‖ ^ (p - 1) := by
    intro n x hx
    rw [hF_of_mem n x hx]
    have h := Commons.Analysis.InnerProductSpace.norm_smul_rpow_smul_self (h' x) (p := p) (c := 1) hp zero_le_one
    simpa using h
  have hF_le : ∀ n, ∀ x, ‖F n x‖ ≤ ((n : ℝ) + 1) ^ (p - 1) := by
    intro n x
    by_cases hx : x ∈ s n
    · rw [hF_norm_mem n x hx]
      exact Real.rpow_le_rpow (norm_nonneg _) (hs_ub n x hx) hp1_pos.le
    · rw [hF_of_notMem n x hx, norm_zero]
      exact Real.rpow_nonneg (by positivity) (p - 1)
  have hF_supp : ∀ n, ∀ x, x ∉ s n → F n x = 0 := fun n x hx => hF_of_notMem n x hx
  -- ### the pairing identities
  have hF_inner : ∀ n x, inner ℂ (h' x) (F n x) = ((A n x : ℝ) : ℂ) := by
    intro n x
    by_cases hx : x ∈ s n
    · rw [hF_of_mem n x hx, hA_of_mem n x hx]
      have h := Commons.Analysis.InnerProductSpace.inner_smul_rpow_smul_self (h' x) (p := p) (c := 1) hp
      simpa using h
    · rw [hF_of_notMem n x hx, hA_of_notMem n x hx, inner_zero_right, Complex.ofReal_zero]
  have hpairval : ∀ n, ∫ x, inner ℂ (h' x) (F n x) = (((∫ x, A n x) : ℝ) : ℂ) := by
    intro n
    calc ∫ x, inner ℂ (h' x) (F n x) = ∫ x, (((A n x : ℝ)) : ℂ) := by
          apply integral_congr_ae
          filter_upwards with x
          exact hF_inner n x
      _ = (((∫ x, A n x) : ℝ) : ℂ) := integral_ofReal
  have hpair_eq : ∀ n, ∫ x, inner ℂ (h x) (F n x) = ∫ x, inner ℂ (h' x) (F n x) := by
    intro n
    apply integral_congr_ae
    filter_upwards [hh'] with x hx
    rw [hx]
  -- ### the three norm identities
  have hGpow : ∀ n x, ‖G n x‖ ^ p = A n x := by
    intro n x
    by_cases hx : x ∈ s n
    · rw [hG_of_mem n x hx, hA_of_mem n x hx]
    · rw [hG_of_notMem n x hx, hA_of_notMem n x hx, norm_zero, Real.zero_rpow hp_ne]
  have hFpow : ∀ n x, ‖F n x‖ ^ (p / (p - 1)) = A n x := by
    intro n x
    by_cases hx : x ∈ s n
    · rw [hF_norm_mem n x hx, hA_of_mem n x hx, ← Real.rpow_mul (norm_nonneg _) (p - 1) (p / (p - 1)),
          hmulq]
    · rw [hF_of_notMem n x hx, hA_of_notMem n x hx, norm_zero, Real.zero_rpow hq_ne]
  have hLp : ∀ n, eLpNorm (G n) (ENNReal.ofReal p) volume
      = ENNReal.ofReal ((∫ x, A n x) ^ (1 / p)) := by
    intro n
    have hpt : ∀ x, ‖G n x‖ₑ ^ p = ENNReal.ofReal (A n x) := by
      intro x
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (G n x)) hp_pos.le, hGpow n x]
    rw [eLpNorm_eq_eLpNorm' hP0 hPtop (hG_meas n).aestronglyMeasurable, ENNReal.toReal_ofReal hp_pos.le,
      show eLpNorm' (G n) p volume = (∫⁻ x, ‖G n x‖ₑ ^ p) ^ (1 / p) from rfl,
      lintegral_congr hpt,
      ← ofReal_integral_eq_lintegral_ofReal (hA_int n) (Filter.Eventually.of_forall (hA_nn n)),
      ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (hA_nn n))
        (by rw [one_div_nonneg]; exact hp_pos.le)]
  have hLq : ∀ n, eLpNorm (F n) (ENNReal.ofReal (p / (p - 1))) volume
      = ENNReal.ofReal ((∫ x, A n x) ^ (1 / (p / (p - 1)))) := by
    intro n
    have hpt : ∀ x, ‖F n x‖ₑ ^ (p / (p - 1)) = ENNReal.ofReal (A n x) := by
      intro x
      rw [← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (F n x)) hq_pos.le, hFpow n x]
    rw [eLpNorm_eq_eLpNorm' hQ0 hQtop (hF_sm n), ENNReal.toReal_ofReal hq_pos.le,
      show eLpNorm' (F n) (p / (p - 1)) volume
        = (∫⁻ x, ‖F n x‖ₑ ^ (p / (p - 1))) ^ (1 / (p / (p - 1))) from rfl,
      lintegral_congr hpt,
      ← ofReal_integral_eq_lintegral_ofReal (hA_int n) (Filter.Eventually.of_forall (hA_nn n)),
      ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (hA_nn n)) (le_of_lt hqinv_pos)]
  -- ### the pairing bound
  have hkey : ∀ n, ENNReal.ofReal (∫ x, A n x)
      ≤ E * ENNReal.ofReal ((∫ x, A n x) ^ (1 / (p / (p - 1)))) := by
    intro n
    have hmem2 : MemLp (F n) 2 volume :=
      memLp_of_bound_of_support_subset 2 (hs_meas n) (hs_fin n) (hF_sm n) (hF_le n) (hF_supp n)
    have hmemq : MemLp (F n) (ENNReal.ofReal (p / (p - 1))) volume :=
      memLp_of_bound_of_support_subset _ (hs_meas n) (hs_fin n) (hF_sm n) (hF_le n) (hF_supp n)
    have h1 := hpair (F n) hmem2 hmemq
    rw [hLq n] at h1
    calc ENNReal.ofReal (∫ x, A n x)
        = enorm (∫ x, inner ℂ (h' x) (F n x)) := by
          rw [hpairval n]
          exact (enorm_ofReal_of_nonneg (integral_nonneg (hA_nn n))).symm
      _ = enorm (∫ x, inner ℂ (h x) (F n x)) := by rw [hpair_eq n]
      _ ≤ E * ENNReal.ofReal ((∫ x, A n x) ^ (1 / (p / (p - 1)))) := h1
  -- ### the arithmetic
  have harith : ∀ n, ENNReal.ofReal ((∫ x, A n x) ^ (1 / p)) ≤ E := by
    intro n
    have ha0 : 0 ≤ ∫ x, A n x := integral_nonneg (hA_nn n)
    have h1 : ∫ x, A n x ≤ E.toReal * (∫ x, A n x) ^ (1 / (p / (p - 1))) := by
      have h2 : ENNReal.ofReal (∫ x, A n x)
          ≤ ENNReal.ofReal (E.toReal * (∫ x, A n x) ^ (1 / (p / (p - 1)))) := by
        calc ENNReal.ofReal (∫ x, A n x)
            ≤ E * ENNReal.ofReal ((∫ x, A n x) ^ (1 / (p / (p - 1)))) := hkey n
          _ = ENNReal.ofReal E.toReal * ENNReal.ofReal ((∫ x, A n x) ^ (1 / (p / (p - 1)))) := by
              rw [ENNReal.ofReal_toReal hE]
          _ = ENNReal.ofReal (E.toReal * (∫ x, A n x) ^ (1 / (p / (p - 1)))) := by
              rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      exact (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg ha0 _))).mp h2
    have h3 : (∫ x, A n x) ^ (1 / p) ≤ E.toReal := by
      rcases eq_or_lt_of_le ha0 with h0 | hpos
      · rw [← h0, Real.zero_rpow (by positivity : (1 : ℝ) / p ≠ 0)]
        exact ENNReal.toReal_nonneg
      · have hqpow : 0 < (∫ x, A n x) ^ (1 / (p / (p - 1))) := Real.rpow_pos_of_pos hpos _
        have h4 : (∫ x, A n x) / (∫ x, A n x) ^ (1 / (p / (p - 1))) ≤ E.toReal :=
          (div_le_iff₀ hqpow).mpr h1
        have hrw : (∫ x, A n x) ^ (1 / p)
            = (∫ x, A n x) / (∫ x, A n x) ^ (1 / (p / (p - 1))) := by
          rw [← h1q, Real.rpow_sub hpos 1 (1 / (p / (p - 1))), Real.rpow_one]
        rw [hrw]
        exact h4
    calc ENNReal.ofReal ((∫ x, A n x) ^ (1 / p)) ≤ ENNReal.ofReal E.toReal :=
          ENNReal.ofReal_le_ofReal h3
      _ = E := ENNReal.ofReal_toReal hE
  -- ### monotone convergence
  have hu : ∀ n, Measurable (fun x => ‖G n x‖ₑ) := fun n => (hG_meas n).enorm
  have hmono_u : Monotone (fun n => fun x => ‖G n x‖ₑ) := by
    intro m n hmn x
    show ‖(s m).indicator h' x‖ₑ ≤ ‖(s n).indicator h' x‖ₑ
    exact enorm_indicator_le_of_subset (hs_mono hmn) h' x
  have hsup_pt : ∀ x, (⨆ n, ‖G n x‖ₑ) = ‖h' x‖ₑ := by
    intro x
    refine le_antisymm (iSup_le fun n => ?_) ?_
    · show ‖(s n).indicator h' x‖ₑ ≤ ‖h' x‖ₑ
      exact enorm_indicator_le_enorm_self h' x
    · by_cases hx0 : h' x = 0
      · rw [hx0, enorm_zero]
        exact bot_le
      · have hr : 0 < ‖h' x‖ := norm_pos_iff.mpr hx0
        obtain ⟨n, hn1, hn2, hn3⟩ :
            ∃ n : ℕ, |x| ≤ (n : ℝ) ∧ 1 / ‖h' x‖ ≤ (n : ℝ) ∧ ‖h' x‖ ≤ (n : ℝ) := by
          refine ⟨⌈max (max |x| (1 / ‖h' x‖)) ‖h' x‖⌉₊, ?_, ?_, ?_⟩
          · exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (Nat.le_ceil _))
          · exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (Nat.le_ceil _))
          · exact le_trans (le_max_right _ _) (Nat.le_ceil _)
        have hmem : x ∈ s n := by
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · show ‖h' x‖ ≤ (n : ℝ) + 1
            linarith
          · show 1 / ((n : ℝ) + 1) ≤ ‖h' x‖
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
            have h1 : 1 ≤ ‖h' x‖ * n := by
              have h := mul_le_mul_of_nonneg_left hn2 (le_of_lt hr)
              rw [mul_one_div, div_self hr.ne'] at h
              exact h
            nlinarith [hr]
          · show x ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
            exact abs_le.mp hn1
        calc ‖h' x‖ₑ = ‖(s n).indicator h' x‖ₑ := by rw [Set.indicator_of_mem hmem]
          _ ≤ ⨆ m, ‖(s m).indicator h' x‖ₑ :=
            le_iSup (fun m => ‖(s m).indicator h' x‖ₑ) n
  have hmain : eLpNorm h' (ENNReal.ofReal p) volume
      = ⨆ n, eLpNorm (G n) (ENNReal.ofReal p) volume := by
    have key := eLpNorm_iSup_of_monotone_meas (μ := volume) (P := ENNReal.ofReal p)
      hP0 hPtop hu hmono_u
    have hleft : eLpNorm (fun x => ‖h' x‖ₑ) (ENNReal.ofReal p) volume
        = eLpNorm h' (ENNReal.ofReal p) volume :=
      eLpNorm_congr_enorm_ae h'm.measurable.enorm.aestronglyMeasurable h'm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by rw [enorm_eq_self])
    have hright : (⨆ n, eLpNorm (fun x => ‖G n x‖ₑ) (ENNReal.ofReal p) volume)
        = ⨆ n, eLpNorm (G n) (ENNReal.ofReal p) volume :=
      iSup_congr fun n => eLpNorm_congr_enorm_ae (hG_meas n).enorm.aestronglyMeasurable
        (hG_meas n).aestronglyMeasurable (Filter.Eventually.of_forall fun x => by rw [enorm_eq_self])
    rw [show (fun x => ⨆ n, ‖G n x‖ₑ) = fun x => ‖h' x‖ₑ from funext hsup_pt, hleft, hright] at key
    exact key
  rw [eLpNorm_congr_ae hh']
  rw [hmain]
  exact iSup_le fun n => by rw [hLp n]; exact harith n

end Work.BourgainPlan.Maximal
