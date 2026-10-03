import Mathlib
import Submission.Commons.Analysis.CalderonZygmund.calderon_zygmund_decomposition_1d_banach
import Submission.Commons.Analysis.CalderonZygmund.cz_bad_part_interval_lintegral
import Submission.Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal

namespace Commons.Analysis.CalderonZygmund

open _root_.MeasureTheory Filter Set
open scoped ENNReal

set_option autoImplicit false

noncomputable section

/-- The convolution operator with kernel `K`: `x ↦ ∫ y, K (x - y) • f y`. -/
def czConv {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (K : ℝ → ℂ) (f : ℝ → H) : ℝ → H :=
  fun x => ∫ y, K (x - y) • f y

/-- The convolution is a.e.-strongly-measurable. -/
lemma aestronglyMeasurable_czConv {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] {K : ℝ → ℂ} (hK : AEStronglyMeasurable K volume)
    {u : ℝ → H} (hu : AEStronglyMeasurable u volume) :
    AEStronglyMeasurable (czConv K u) volume := by
  have hK' : StronglyMeasurable (hK.mk K) := hK.stronglyMeasurable_mk
  have hu' : StronglyMeasurable (hu.mk u) := hu.stronglyMeasurable_mk
  have hjoint : StronglyMeasurable (fun p : ℝ × ℝ => (hK.mk K) (p.1 - p.2) • (hu.mk u) p.2) :=
    (hK'.comp_measurable (measurable_fst.sub measurable_snd)).smul
      (hu'.comp_measurable measurable_snd)
  have hjoint2 : StronglyMeasurable
      (fun x : ℝ => ∫ y : ℝ, (hK.mk K) (x - y) • (hu.mk u) y) :=
    hjoint.integral_prod_right'
  have hmp : MeasurePreserving (fun y : ℝ => -y) volume volume :=
    ⟨measurable_neg, Measure.map_neg_eq_self volume⟩
  refine hjoint2.aestronglyMeasurable.congr ?_
  filter_upwards with x
  refine integral_congr_ae ?_
  have hKshift : (fun y : ℝ => (hK.mk K) (x - y)) =ᵐ[volume] (fun y : ℝ => K (x - y)) := by
    have hcomp : MeasurePreserving (fun y : ℝ => x + (-y)) volume volume :=
      (measurePreserving_add_left volume x).comp hmp
    have hcomp' : MeasurePreserving (fun y : ℝ => x - y) volume volume := by
      simpa [sub_eq_add_neg] using hcomp
    have hh := hcomp'.quasiMeasurePreserving.ae_eq_comp hK.ae_eq_mk
    filter_upwards [hh] with y hy
    simpa using hy.symm
  filter_upwards [hKshift, hu.ae_eq_mk] with y hy1 hy2
  rw [← hy2]
  exact congrArg (fun c : ℂ => c • u y) hy1

/-- A bounded kernel times an integrable function is integrable. -/
lemma integrable_kernel_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {K : ℝ → ℂ} (hKmeas : Measurable K) {B : ℝ} (hB : ∀ z, ‖K z‖ ≤ B)
    {u : ℝ → H} (hu : Integrable u) (x : ℝ) :
    Integrable (fun y => K (x - y) • u y) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (K 0)) (hB 0)
  have hmeask : AEStronglyMeasurable (fun y : ℝ => K (x - y)) volume :=
    (hKmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  refine (hu.norm.const_mul B).mono' (hmeask.smul hu.aestronglyMeasurable) ?_
  filter_upwards with y
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hB (x - y)) (norm_nonneg _)

/-- `czConv` is additive in the second argument (as a Bochner integral). -/
lemma czConv_add {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {K : ℝ → ℂ} (hKmeas : Measurable K) {B : ℝ} (hB : ∀ z, ‖K z‖ ≤ B)
    {u v : ℝ → H} (hu : Integrable u) (hv : Integrable v) (x : ℝ) :
    czConv K (u + v) x = czConv K u x + czConv K v x := by
  rw [czConv, czConv, czConv]
  have h1 : (fun y => K (x - y) • (u + v) y) = fun y => K (x - y) • u y + K (x - y) • v y := by
    funext y; rw [Pi.add_apply, smul_add]
  rw [h1, integral_add (integrable_kernel_smul hKmeas hB hu x)
    (integrable_kernel_smul hKmeas hB hv x)]

/-- A family of vectors supported on pairwise disjoint intervals is summable at every point. -/
lemma summable_of_disjoint_support {H : Type*} [NormedAddCommGroup H]
    {A c : ℕ → ℝ} {b : ℕ → ℝ → H}
    (hdisj : ∀ j k, j ≠ k → Disjoint (Ioo (A j) (c j)) (Ioo (A k) (c k)))
    (hb_supp : ∀ j x, x ∉ Ioo (A j) (c j) → b j x = 0) (y : ℝ) :
    Summable (fun j => b j y) := by
  by_cases h : ∃ j, b j y ≠ 0
  · obtain ⟨j0, hj0⟩ := h
    have hy0 : y ∈ Ioo (A j0) (c j0) := by
      by_contra hy; exact hj0 (hb_supp j0 y hy)
    refine summable_of_ne_finset_zero (s := {j0}) ?_
    intro j hj
    rw [Finset.mem_singleton] at hj
    by_contra hb
    have hyj : y ∈ Ioo (A j) (c j) := by
      by_contra hy; exact hb (hb_supp j y hy)
    exact (Set.disjoint_left.mp (hdisj j j0 hj) hyj) hy0
  · simp only [not_exists, not_ne_iff] at h
    refine summable_of_ne_finset_zero (s := ∅) ?_
    simp [h]

/-- A helper: `‖x‖ₑ = ENNReal.ofReal ‖x‖`. -/
lemma enorm_eq_ofReal_norm' {H : Type*} [SeminormedAddGroup H] (x : H) :
    ‖x‖ₑ = ENNReal.ofReal ‖x‖ := (ofReal_norm x).symm

theorem cz_weak_type_one_measurable_bounded {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (K : ℝ → ℂ) (A2 Ak B : ℝ) (hA2 : 0 < A2) (hAk : 0 ≤ Ak)
    (hB : ∀ z : ℝ, ‖K z‖ ≤ B)
    (hKmeas : Measurable K)
    (hker : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
      ∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal Ak)
    (hstrong : ∀ f : ℝ → H, MeasureTheory.Integrable f →
      MeasureTheory.eLpNorm (fun x : ℝ => ∫ y : ℝ, K (x - y) • f y) 2 MeasureTheory.volume
        ≤ ENNReal.ofReal A2 * MeasureTheory.eLpNorm f 2 MeasureTheory.volume)
    (f : ℝ → H) (hf : MeasureTheory.Integrable f) (α : ℝ) (hα : 0 < α) :
    MeasureTheory.volume {x : ℝ | α < ‖∫ y : ℝ, K (x - y) • f y‖}
      ≤ ENNReal.ofReal ((24 * A2 ^ 2 + 4 * Ak + 100) / α)
        * MeasureTheory.eLpNorm f 1 MeasureTheory.volume := by
  classical
  have hKsm : AEStronglyMeasurable K volume := hKmeas.aestronglyMeasurable
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (K 0)) (hB 0)
  obtain ⟨A, c, g, b, hAc, hdisj, hlow, hhigh, hbdef, hgout, hgin, hfaeb, hgaeb, hIv, hfgb⟩ :=
    calderon_zygmund_decomposition_1d_banach f hf α hα
  set L : ℕ → ℝ := fun j => c j - A j with hLdef
  set mass : ℕ → ℝ := fun j => ∫ t in (A j)..(c j), ‖f t‖ with hmassdef
  set cen : ℕ → ℝ := fun j => (A j + c j) / 2 with hcendef
  set mean : ℕ → H := fun j => (L j)⁻¹ • (∫ t in (A j)..(c j), f t) with hmeandef
  set hh : ℝ → H := fun x => f x - g x with hhhdef
  set M : ℝ := ∫ x, ‖f x‖ with hMdef
  set Vset : Set ℝ := ⋃ j, Metric.ball (cen j) (50 * L j) with hVdef
  have hMnn : 0 ≤ M := by rw [hMdef]; exact integral_nonneg (fun x => norm_nonneg _)
  have hLnn : ∀ j, 0 ≤ L j := fun j => by rw [hLdef]; exact sub_nonneg.mpr (hAc j)
  have hlow' : ∀ j, α * L j ≤ mass j := fun j => by
    rw [hLdef, hmassdef]; exact hlow j
  have hhigh' : ∀ j, mass j ≤ 2 * α * L j := fun j => by
    rw [hLdef, hmassdef]; exact hhigh j
  have hmass_nonneg : ∀ j, 0 ≤ mass j := fun j => by
    rw [hmassdef]
    exact intervalIntegral.integral_nonneg (hAc j) (fun t _ => norm_nonneg _)
  have hmass_one : ∀ j, mass j = ∫ x in Set.Ioo (A j) (c j), ‖f x‖ := fun j => by
    rw [hmassdef]
    change (∫ t in (A j)..(c j), ‖f t‖) = ∫ x in Set.Ioo (A j) (c j), ‖f x‖
    rw [intervalIntegral.integral_of_le (hAc j), MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hmass_U : ∑' j, mass j = ∫ x in ⋃ j, Set.Ioo (A j) (c j), ‖f x‖ := by
    rw [MeasureTheory.integral_iUnion (fun j => measurableSet_Ioo)
      (fun j k hjk => hdisj j k hjk) hf.norm.integrableOn]
    exact tsum_congr (fun j => hmass_one j)
  have hmass_sum : ∑' j, mass j ≤ M := by
    rw [hmass_U, hMdef]
    exact setIntegral_le_integral hf.norm (ae_of_all _ (fun x => norm_nonneg _))
  have hsumm_mass : Summable mass := by
    have hHS : HasSum (fun j => ∫ x in Set.Ioo (A j) (c j), ‖f x‖)
        (∫ x in ⋃ j, Set.Ioo (A j) (c j), ‖f x‖) :=
      hasSum_integral_iUnion (fun j => measurableSet_Ioo) (fun j k hjk => hdisj j k hjk)
        hf.norm.integrableOn
    rw [show mass = fun j => ∫ x in Set.Ioo (A j) (c j), ‖f x‖ from
      funext (fun j => hmass_one j)]
    exact hHS.summable
  have hUmeas : MeasurableSet (⋃ j, Set.Ioo (A j) (c j)) :=
    MeasurableSet.iUnion (fun j => measurableSet_Ioo)
  have hVmeas : MeasurableSet Vset := by
    rw [hVdef]; exact MeasurableSet.iUnion (fun j => measurableSet_ball)
  -- mean facts
  have hmean_eq : ∀ j, L j • mean j = ∫ x in Set.Ioo (A j) (c j), f x := fun j => by
    by_cases hL0 : L j = 0
    · have hcA : c j = A j := by rw [hLdef] at hL0; linarith
      have hIe : Set.Ioo (A j) (c j) = ∅ := by rw [hcA]; exact Set.Ioo_self (A j)
      rw [hIe, hL0]; simp
    · rw [hmeandef]
      simp only [hLdef]
      rw [smul_inv_smul₀ hL0]
      show (∫ t in (A j)..(c j), f t) = ∫ x in Set.Ioo (A j) (c j), f x
      rw [intervalIntegral.integral_of_le (hAc j), MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hmeaneq : ∀ j, mean j = (c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t) := fun _ => rfl
  have hmean_le : ∀ j, ‖mean j‖ * L j ≤ mass j := fun j => by
    have h2 : L j * ‖mean j‖ ≤ mass j := by
      have h1 : ‖L j • mean j‖ ≤ ∫ x in Set.Ioo (A j) (c j), ‖f x‖ := by
        rw [hmean_eq j]
        exact norm_integral_le_integral_norm _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hLnn j), ← hmass_one j] at h1
      exact h1
    calc ‖mean j‖ * L j = L j * ‖mean j‖ := mul_comm _ _
      _ ≤ mass j := h2
  -- b facts
  have hb_supp : ∀ j x, x ∉ Set.Ioo (A j) (c j) → b j x = 0 := fun j x hx => by
    rw [hbdef j x, if_neg hx]
  have hb_summ : ∀ y, Summable (fun j => b j y) :=
    fun y => summable_of_disjoint_support hdisj hb_supp y
  have hImeas_fin : ∀ j, volume (Set.Ioo (A j) (c j)) < ∞ := fun j => by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hb_eq : ∀ j x, x ∈ Set.Ioo (A j) (c j) → b j x = f x - mean j := fun j x hx => by
    rw [hbdef j x, if_pos hx, ← hmeaneq j]
  have hb_int : ∀ j, Integrable (b j) := fun j => by
    have hbeq : b j = (Set.Ioo (A j) (c j)).indicator (fun x => f x - mean j) := by
      funext x
      by_cases hx : x ∈ Set.Ioo (A j) (c j)
      · rw [hb_eq j x hx, Set.indicator_of_mem hx]
      · rw [hb_supp j x hx, Set.indicator_of_notMem hx]
    rw [hbeq]
    have hon : IntegrableOn (fun x => f x - mean j) (Set.Ioo (A j) (c j)) volume :=
      (hf.integrableOn).sub (integrableOn_const (C := mean j) (hImeas_fin j).ne enorm_ne_top)
    exact (integrable_indicator_iff measurableSet_Ioo).mpr hon
  have hb_mean : ∀ j, ∫ x in Set.Ioo (A j) (c j), b j x = 0 := fun j => by
    rw [setIntegral_congr_fun measurableSet_Ioo (fun x hx => hb_eq j x hx)]
    rw [integral_sub hf.integrableOn
      (integrableOn_const (C := mean j) (hImeas_fin j).ne enorm_ne_top)]
    have h1 : ∫ x in Set.Ioo (A j) (c j), f x = L j • mean j := (hmean_eq j).symm
    have h2 : ∫ x in Set.Ioo (A j) (c j), mean j = L j • mean j := by
      rw [setIntegral_const, Measure.real_def, Real.volume_Ioo,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (hAc j))]
    rw [h1, h2, sub_self]
  -- bound on sum of L1 norms of b j
  have hb_L1 : ∀ j, ∫ x, ‖b j x‖ ≤ 2 * mass j := fun j => by
    have hsupp : ∀ x, x ∉ Set.Ioo (A j) (c j) → ‖b j x‖ = 0 := fun x hx => by
      rw [hb_supp j x hx, norm_zero]
    have h0 : ∫ x, ‖b j x‖ = ∫ x in Set.Ioo (A j) (c j), ‖b j x‖ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
    rw [h0]
    have hpt : ∀ x, ‖b j x‖ ≤ ‖f x‖ + ‖mean j‖ := fun x => by
      by_cases hx : x ∈ Set.Ioo (A j) (c j)
      · rw [hb_eq j x hx]; exact norm_sub_le _ _
      · rw [hb_supp j x hx, norm_zero]; positivity
    have hbdd : ∫ x in Set.Ioo (A j) (c j), ‖b j x‖
        ≤ ∫ x in Set.Ioo (A j) (c j), (‖f x‖ + ‖mean j‖) := by
      apply integral_mono (hb_int j).norm.integrableOn
        ((hf.norm.integrableOn).add (integrableOn_const (C := ‖mean j‖) (hImeas_fin j).ne enorm_ne_top))
      intro x
      exact hpt x
    have hIc : (∫ x in Set.Ioo (A j) (c j), ‖mean j‖) = ‖mean j‖ * L j := by
      rw [setIntegral_const, Measure.real_def, Real.volume_Ioo,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (hAc j))]
      simp only [hLdef, smul_eq_mul, mul_comm]
    have hsplit : (∫ x in Set.Ioo (A j) (c j), (‖f x‖ + ‖mean j‖)) = mass j + ‖mean j‖ * L j := by
      rw [integral_add (hf.norm.integrableOn)
        (integrableOn_const (C := ‖mean j‖) (hImeas_fin j).ne enorm_ne_top), hmass_one j, hIc]
    calc ∫ x in Set.Ioo (A j) (c j), ‖b j x‖
        ≤ ∫ x in Set.Ioo (A j) (c j), (‖f x‖ + ‖mean j‖) := hbdd
      _ = mass j + ‖mean j‖ * L j := hsplit
      _ ≤ mass j + mass j := by linarith [hmean_le j]
      _ = 2 * mass j := by ring
  have hbLs : Summable (fun j => ∫ x, ‖b j x‖) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg (fun x => norm_nonneg _))
      (fun j => hb_L1 j) (hsumm_mass.mul_left 2)
  have hb_norm_sum : ∑' j, ∫⁻ x, ‖b j x‖ₑ ≤ ENNReal.ofReal (2 * M) := by
    have heq : ∑' j, ∫⁻ x, ‖b j x‖ₑ = ENNReal.ofReal (∑' j, ∫ x, ‖b j x‖) := by
      have h1 : ∑' j, ∫⁻ x, ‖b j x‖ₑ = ∑' j, ENNReal.ofReal (∫ x, ‖b j x‖) :=
        tsum_congr (fun j => (ofReal_integral_norm_eq_lintegral_enorm (hb_int j)).symm)
      rw [h1, ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (fun x => norm_nonneg _)) hbLs]
    rw [heq]
    apply ENNReal.ofReal_le_ofReal
    have h2 : ∑' j, ∫ x, ‖b j x‖ ≤ ∑' j, 2 * mass j :=
      Summable.tsum_le_tsum (fun j => hb_L1 j) hbLs (hsumm_mass.mul_left 2)
    rw [tsum_mul_left] at h2
    calc ∑' j, ∫ x, ‖b j x‖ ≤ 2 * ∑' j, mass j := h2
      _ ≤ 2 * M := by linarith [hmass_sum]
  -- g integrable and lintegral bound
  have hI_lin : ∀ j, ∫⁻ x in Set.Ioo (A j) (c j), ‖g x‖ₑ ≤ ENNReal.ofReal (mass j) := fun j => by
    have hcongr : ∫⁻ x in Set.Ioo (A j) (c j), ‖g x‖ₑ
        = ∫⁻ x in Set.Ioo (A j) (c j), ‖mean j‖ₑ :=
      setLIntegral_congr_fun measurableSet_Ioo (fun x hx => by rw [hgin j x hx, ← hmeaneq j])
    calc ∫⁻ x in Set.Ioo (A j) (c j), ‖g x‖ₑ
        = ∫⁻ x in Set.Ioo (A j) (c j), ‖mean j‖ₑ := hcongr
      _ = ‖mean j‖ₑ * volume (Set.Ioo (A j) (c j)) := setLIntegral_const _ _
      _ = ENNReal.ofReal ‖mean j‖ * ENNReal.ofReal (c j - A j) := by
            rw [Real.volume_Ioo, enorm_eq_ofReal_norm']
      _ = ENNReal.ofReal (‖mean j‖ * (c j - A j)) := (ENNReal.ofReal_mul (norm_nonneg _)).symm
      _ ≤ ENNReal.ofReal (mass j) := ENNReal.ofReal_le_ofReal (hmean_le j)
  have hg_le : ∫⁻ x, ‖g x‖ₑ ≤ ENNReal.ofReal (2 * M) := by
    rw [← lintegral_add_compl (fun x => ‖g x‖ₑ) hUmeas]
    have hA : ∫⁻ x in ⋃ j, Set.Ioo (A j) (c j), ‖g x‖ₑ ≤ ENNReal.ofReal M := by
      rw [lintegral_iUnion (fun j => measurableSet_Ioo) (fun j k hjk => hdisj j k hjk)]
      calc (∑' j, ∫⁻ x in Set.Ioo (A j) (c j), ‖g x‖ₑ) ≤ ∑' j, ENNReal.ofReal (mass j) :=
            ENNReal.tsum_le_tsum (fun j => hI_lin j)
        _ = ENNReal.ofReal (∑' j, mass j) :=
            (ENNReal.ofReal_tsum_of_nonneg hmass_nonneg hsumm_mass).symm
        _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal hmass_sum
    have hB : ∫⁻ x in (⋃ j, Set.Ioo (A j) (c j))ᶜ, ‖g x‖ₑ ≤ ENNReal.ofReal M := by
      have hcongr : ∫⁻ x in (⋃ j, Set.Ioo (A j) (c j))ᶜ, ‖g x‖ₑ
          = ∫⁻ x in (⋃ j, Set.Ioo (A j) (c j))ᶜ, ‖f x‖ₑ :=
        setLIntegral_congr_fun hUmeas.compl (fun x hx => by rw [hgout x hx])
      rw [hcongr]
      calc ∫⁻ x in (⋃ j, Set.Ioo (A j) (c j))ᶜ, ‖f x‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ :=
            setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal M := by rw [← ofReal_integral_norm_eq_lintegral_enorm hf, hMdef]
    calc (∫⁻ x in ⋃ j, Set.Ioo (A j) (c j), ‖g x‖ₑ)
          + ∫⁻ x in (⋃ j, Set.Ioo (A j) (c j))ᶜ, ‖g x‖ₑ
        ≤ ENNReal.ofReal M + ENNReal.ofReal M := add_le_add hA hB
      _ = ENNReal.ofReal (2 * M) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  have hg_sm : AEStronglyMeasurable g volume := by
    have hsp : Summable (fun j => b j) := Pi.summable.mpr hb_summ
    have htsum_sm : AEStronglyMeasurable (fun x => ∑' j, b j x) volume :=
      AEStronglyMeasurable.tsum (fun j => (hb_int j).aestronglyMeasurable)
    refine (hf.aestronglyMeasurable.sub htsum_sm).congr ?_
    filter_upwards [hfgb] with x hx
    simp only [Pi.sub_apply]
    rw [hx, add_sub_cancel_right]
  have hgint : Integrable g := ⟨hg_sm, by
    rw [hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt hg_le ENNReal.ofReal_lt_top⟩
  have hg_norm2 : ∫ x, ‖g x‖ ≤ 2 * M := by
    have h := hg_le
    rw [← ofReal_integral_norm_eq_lintegral_enorm hgint] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : (0:ℝ) ≤ 2 * M)).mp h
  have hhint : Integrable hh := by rw [hhhdef]; exact hf.sub hgint
  -- good part
  have hg_sq_int : Integrable (fun x => ‖g x‖ ^ 2) := by
    have hbd : Integrable (fun x => 2 * α * ‖g x‖) := hgint.norm.const_mul (2 * α)
    refine hbd.mono' ?_ ?_
    · refine (hgint.aestronglyMeasurable.norm.pow 2).congr ?_
      filter_upwards with x
      simp only [Pi.pow_apply]
    · filter_upwards [hgaeb] with x hx
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith [norm_nonneg (g x)]
  have hgL2 : (eLpNorm g 2 volume) ^ (2:ℝ) ≤ ENNReal.ofReal (4 * α * M) := by
    have h1 : (eLpNorm g 2 volume) ^ (2:ℝ) = ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) := by
      have hh2 := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (μ := volume) (p := (2:ℝ≥0∞))
        (by norm_num) (by norm_num) g hg_sm
      simpa only [ENNReal.toReal_ofNat] using hh2
    rw [h1]
    have hpt : ∀ x, ‖g x‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖g x‖ ^ 2) := fun x => by
      rw [enorm_eq_ofReal_norm',
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2), Real.rpow_ofNat]
    rw [show (fun x => ‖g x‖ₑ ^ (2:ℝ)) = fun x => ENNReal.ofReal (‖g x‖ ^ 2) from funext hpt]
    rw [← ofReal_integral_eq_lintegral_ofReal hg_sq_int (ae_of_all _ (fun x => by positivity))]
    apply ENNReal.ofReal_le_ofReal
    have h2 : ∫ x, ‖g x‖ ^ 2 ≤ ∫ x, 2 * α * ‖g x‖ := by
      apply integral_mono_ae hg_sq_int (hgint.norm.const_mul (2 * α))
      filter_upwards [hgaeb] with x hx
      nlinarith [norm_nonneg (g x)]
    rw [MeasureTheory.integral_const_mul] at h2
    calc ∫ x, ‖g x‖ ^ 2 ≤ 2 * α * ∫ x, ‖g x‖ := h2
      _ ≤ 2 * α * (2 * M) := by gcongr
      _ = 4 * α * M := by ring
  have hgood : volume {x : ℝ | ENNReal.ofReal (α / 2) < ‖czConv K g x‖ₑ}
      ≤ ENNReal.ofReal (16 * A2 ^ 2 * M / α) := by
    have hc0 : ENNReal.ofReal (α / 2) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
    have hcheb := meas_ge_le_mul_pow_eLpNorm_enorm (μ := volume) (p := (2:ℝ≥0∞))
      (by norm_num) (by norm_num) (f := czConv K g) hc0
      (fun h => absurd h ENNReal.ofReal_ne_top)
    have hcg2 : (eLpNorm (czConv K g) 2 volume) ^ (2:ℝ)
        ≤ ENNReal.ofReal (A2 ^ 2 * (4 * α * M)) := by
      have h1 : (eLpNorm (czConv K g) 2 volume) ^ (2:ℝ)
          ≤ (ENNReal.ofReal A2 * eLpNorm g 2 volume) ^ (2:ℝ) :=
        ENNReal.rpow_le_rpow (hstrong g hgint) (by norm_num)
      calc (eLpNorm (czConv K g) 2 volume) ^ (2:ℝ)
          ≤ (ENNReal.ofReal A2 * eLpNorm g 2 volume) ^ (2:ℝ) := h1
        _ = ENNReal.ofReal A2 ^ (2:ℝ) * (eLpNorm g 2 volume) ^ (2:ℝ) :=
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
        _ = ENNReal.ofReal (A2 ^ 2) * (eLpNorm g 2 volume) ^ (2:ℝ) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt hA2) (by norm_num : (0:ℝ) ≤ 2),
              Real.rpow_ofNat]
        _ ≤ ENNReal.ofReal (A2 ^ 2) * ENNReal.ofReal (4 * α * M) := by gcongr
        _ = ENNReal.ofReal (A2 ^ 2 * (4 * α * M)) :=
            (ENNReal.ofReal_mul (by positivity)).symm
    have hinv : (ENNReal.ofReal (α / 2))⁻¹ ^ (2:ℝ) = ENNReal.ofReal ((α / 2)⁻¹ ^ 2) := by
      rw [← ENNReal.ofReal_inv_of_pos (by linarith : (0:ℝ) < α / 2),
        ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr (by linarith : (0:ℝ) ≤ α / 2))
          (by norm_num : (0:ℝ) ≤ 2), Real.rpow_ofNat]
    calc volume {x : ℝ | ENNReal.ofReal (α / 2) < ‖czConv K g x‖ₑ}
        ≤ volume {x : ℝ | ENNReal.ofReal (α / 2) ≤ ‖czConv K g x‖ₑ} :=
          measure_mono (fun x hx => by
            simp only [Set.mem_ofPred_eq] at hx ⊢
            exact le_of_lt hx)
      _ ≤ (ENNReal.ofReal (α / 2))⁻¹ ^ (2:ℝ) * (eLpNorm (czConv K g) 2 volume) ^ (2:ℝ) := by
          simpa only [ENNReal.toReal_ofNat] using hcheb
      _ = ENNReal.ofReal ((α / 2)⁻¹ ^ 2) * (eLpNorm (czConv K g) 2 volume) ^ (2:ℝ) := by
          rw [hinv]
      _ ≤ ENNReal.ofReal ((α / 2)⁻¹ ^ 2) * ENNReal.ofReal (A2 ^ 2 * (4 * α * M)) := by gcongr
      _ = ENNReal.ofReal (16 * A2 ^ 2 * M / α) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show ((α / 2)⁻¹ ^ 2 * (A2 ^ 2 * (4 * α * M))) = 16 * A2 ^ 2 * M / α by
            field_simp; ring]
  -- bad part
  have hh_eq_ae : hh =ᵐ[volume] fun y => ∑' j, b j y := by
    filter_upwards [hfgb] with y hy
    simp only [hhhdef]
    rw [hy, add_sub_cancel_left]
  have hpoint : ∀ x, czConv K f x = czConv K g x + ∑' j, czConv K (b j) x := by
    intro x
    have hgf : g + hh = f := by
      funext y; simp only [Pi.add_apply, hhhdef]; abel
    have h1 : czConv K f x = czConv K g x + czConv K hh x := by
      rw [← hgf, czConv_add hKmeas hB hgint hhint x]
    have h2 : czConv K hh x = ∑' j, czConv K (b j) x := by
      rw [czConv]
      have hcongr : (∫ y, K (x - y) • hh y) = ∫ y, ∑' j, K (x - y) • b j y := by
        apply integral_congr_ae
        filter_upwards [hh_eq_ae] with y hy
        rw [hy, ← Summable.tsum_const_smul (K (x - y)) (hb_summ y)]
      have hfin : (∑' j, ∫⁻ y, ‖K (x - y) • b j y‖ₑ) ≠ ∞ := by
        have hbd : ∀ j, ∫⁻ y, ‖K (x - y) • b j y‖ₑ ≤ ENNReal.ofReal B * ∫⁻ y, ‖b j y‖ₑ := fun j => by
          rw [← lintegral_const_mul' (ENNReal.ofReal B) (fun y => ‖b j y‖ₑ) ENNReal.ofReal_ne_top]
          apply lintegral_mono
          intro y
          simp only [enorm_smul]
          rw [enorm_eq_ofReal_norm']
          gcongr
          exact hB (x - y)
        refine (calc (∑' j, ∫⁻ y, ‖K (x - y) • b j y‖ₑ)
            ≤ ∑' j, ENNReal.ofReal B * ∫⁻ y, ‖b j y‖ₑ := ENNReal.tsum_le_tsum hbd
          _ = ENNReal.ofReal B * ∑' j, ∫⁻ y, ‖b j y‖ₑ := ENNReal.tsum_mul_left
          _ ≤ ENNReal.ofReal B * ENNReal.ofReal (2 * M) := by gcongr
          _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
      rw [hcongr]
      have hsum := integral_tsum (f := fun j y => K (x - y) • b j y)
        (fun j => ((hKmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).smul
          (hb_int j).aestronglyMeasurable) hfin
      simpa only [czConv] using hsum
    rw [h1, h2]
  have hterm : ∀ j, ∫⁻ x in Vsetᶜ, ‖czConv K (b j) x‖ₑ ≤ ENNReal.ofReal Ak * ∫⁻ x, ‖b j x‖ₑ := fun j => by
    have hbad := cz_bad_part_interval_lintegral K Ak hAk hKsm hker (A j) (c j) (hAc j) (b j)
      (hb_int j) (hb_supp j) (hb_mean j)
    have hset : Vsetᶜ ⊆ {x : ℝ | 50 * (c j - A j) ≤ |x - (A j + c j) / 2|} := by
      intro x hx
      have hx' : 50 * L j ≤ |x - cen j| := by
        have h1 := hx
        simp only [hVdef, Set.mem_compl_iff, Set.mem_iUnion, not_exists] at h1
        have h2 := h1 j
        simpa only [Metric.mem_ball, not_lt, Real.dist_eq] using h2
      simpa only [hcendef, hLdef, Set.mem_ofPred_eq] using hx'
    calc ∫⁻ x in Vsetᶜ, ‖czConv K (b j) x‖ₑ
        ≤ ∫⁻ x in {x : ℝ | 50 * (c j - A j) ≤ |x - (A j + c j) / 2|},
            ‖czConv K (b j) x‖ₑ := lintegral_mono_set hset
      _ ≤ ENNReal.ofReal Ak * ∫⁻ x, ‖b j x‖ₑ := hbad
  have hbad_lin : ∫⁻ x in Vsetᶜ, (∑' j, ‖czConv K (b j) x‖ₑ) ≤ ENNReal.ofReal (2 * Ak * M) := by
    have hstep : ∫⁻ x in Vsetᶜ, (∑' j, ‖czConv K (b j) x‖ₑ)
        = ∑' j, ∫⁻ x in Vsetᶜ, ‖czConv K (b j) x‖ₑ := by
      refine lintegral_tsum (μ := volume.restrict Vsetᶜ) ?_
      intro j
      exact ((aestronglyMeasurable_czConv hKsm (hb_int j).aestronglyMeasurable).enorm).restrict
    rw [hstep]
    calc ∑' j, ∫⁻ x in Vsetᶜ, ‖czConv K (b j) x‖ₑ
        ≤ ∑' j, ENNReal.ofReal Ak * ∫⁻ x, ‖b j x‖ₑ := ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal Ak * ∑' j, ∫⁻ x, ‖b j x‖ₑ := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal Ak * ENNReal.ofReal (2 * M) := by gcongr
      _ = ENNReal.ofReal (2 * Ak * M) := by
          rw [← ENNReal.ofReal_mul hAk]; congr 1; ring
  have hbad : volume {x : ℝ | x ∉ Vset ∧ ENNReal.ofReal (α / 2) < ∑' j, ‖czConv K (b j) x‖ₑ}
      ≤ ENNReal.ofReal (4 * Ak * M / α) := by
    set Bf : ℝ → ℝ≥0∞ := Vsetᶜ.indicator (fun x => ∑' j, ‖czConv K (b j) x‖ₑ) with hBfdef
    have hBf_meas : AEMeasurable Bf volume := by
      rw [hBfdef]
      exact AEMeasurable.indicator (AEMeasurable.tsum (fun j =>
        ((aestronglyMeasurable_czConv hKsm (hb_int j).aestronglyMeasurable).enorm)))
        hVmeas.compl
    have hε0 : ENNReal.ofReal (α / 2) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
    have hεt : ENNReal.ofReal (α / 2) ≠ ∞ := ENNReal.ofReal_ne_top
    have hkey := meas_ge_le_lintegral_div hBf_meas hε0 hεt
    have hset : {x : ℝ | x ∉ Vset ∧ ENNReal.ofReal (α / 2) < ∑' j, ‖czConv K (b j) x‖ₑ}
        ⊆ {x : ℝ | ENNReal.ofReal (α / 2) ≤ Bf x} := by
      intro x hx
      have hmem : x ∈ Vsetᶜ := hx.1
      have hval : Bf x = ∑' j, ‖czConv K (b j) x‖ₑ := by
        rw [hBfdef, Set.indicator_of_mem hmem]
      show ENNReal.ofReal (α / 2) ≤ Bf x
      rw [hval]
      exact le_of_lt hx.2
    have hlint : ∫⁻ x, Bf x = ∫⁻ x in Vsetᶜ, ∑' j, ‖czConv K (b j) x‖ₑ := by
      rw [hBfdef, lintegral_indicator hVmeas.compl]
    calc volume {x : ℝ | x ∉ Vset ∧ ENNReal.ofReal (α / 2) < ∑' j, ‖czConv K (b j) x‖ₑ}
        ≤ volume {x : ℝ | ENNReal.ofReal (α / 2) ≤ Bf x} := measure_mono hset
      _ ≤ (∫⁻ x, Bf x) / ENNReal.ofReal (α / 2) := hkey
      _ = (∫⁻ x in Vsetᶜ, ∑' j, ‖czConv K (b j) x‖ₑ) / ENNReal.ofReal (α / 2) := by rw [hlint]
      _ ≤ ENNReal.ofReal (2 * Ak * M) / ENNReal.ofReal (α / 2) :=
          ENNReal.div_le_div_right hbad_lin _
      _ = ENNReal.ofReal (4 * Ak * M / α) := by
          rw [← ENNReal.ofReal_div_of_pos (by linarith : (0:ℝ) < α / 2)]
          congr 1
          field_simp
          ring
  have hV_meas : volume Vset ≤ ENNReal.ofReal (100 * M / α) := by
    have hLle : ∀ j, L j ≤ mass j / α := fun j => by
      rw [le_div_iff₀ hα]; linarith [hlow' j]
    have hsummL : Summable L := Summable.of_nonneg_of_le hLnn hLle (hsumm_mass.div_const α)
    have htsumL : ∑' j, L j ≤ M / α := by
      calc ∑' j, L j ≤ ∑' j, mass j / α := Summable.tsum_le_tsum hLle hsummL (hsumm_mass.div_const α)
        _ = (∑' j, mass j) / α := tsum_div_const
        _ ≤ M / α := div_le_div_of_nonneg_right hmass_sum (le_of_lt hα)
    calc volume Vset ≤ ∑' j, volume (Metric.ball (cen j) (50 * L j)) := by
          rw [hVdef]; exact measure_iUnion_le _
      _ = ∑' j, ENNReal.ofReal (100 * L j) := by
          apply tsum_congr; intro j
          rw [Real.volume_ball]; congr 1; ring
      _ = ENNReal.ofReal (100 * (∑' j, L j)) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (by norm_num) (hLnn j))
            (hsummL.mul_left 100), tsum_mul_left]
      _ ≤ ENNReal.ofReal (100 * (M / α)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left htsumL (by norm_num))
      _ = ENNReal.ofReal (100 * M / α) := by ring_nf
  -- assembly
  have hsubset : {x : ℝ | α < ‖czConv K f x‖} ⊆ Vset ∪
      ({x : ℝ | ENNReal.ofReal (α / 2) < ‖czConv K g x‖ₑ} ∪
       {x : ℝ | x ∉ Vset ∧ ENNReal.ofReal (α / 2) < ∑' j, ‖czConv K (b j) x‖ₑ}) := by
    intro x hx
    by_cases hxV : x ∈ Vset
    · exact Or.inl hxV
    · refine Or.inr ?_
      by_cases hg : ENNReal.ofReal (α / 2) < ‖czConv K g x‖ₑ
      · exact Or.inl hg
      · refine Or.inr ⟨hxV, ?_⟩
        by_contra hc
        push Not at hg hc
        have hxα : ENNReal.ofReal α < ‖czConv K f x‖ₑ := by
          rw [enorm_eq_ofReal_norm']
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hα)).mpr hx
        rw [hpoint x] at hxα
        have h2 : ‖czConv K g x + ∑' j, czConv K (b j) x‖ₑ
            ≤ ‖czConv K g x‖ₑ + ∑' j, ‖czConv K (b j) x‖ₑ :=
          (enorm_add_le _ _).trans (add_le_add le_rfl enorm_tsum_le_tsum_enorm)
        have h4 : ENNReal.ofReal (α / 2) + ENNReal.ofReal (α / 2) = ENNReal.ofReal α := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
        have h3 : ‖czConv K g x‖ₑ + ∑' j, ‖czConv K (b j) x‖ₑ ≤ ENNReal.ofReal α := by
          rw [← h4]; exact add_le_add hg hc
        exact absurd (hxα.trans_le (h2.trans h3)) (lt_irrefl _)
  have hfin : volume {x : ℝ | α < ‖czConv K f x‖}
      ≤ ENNReal.ofReal ((24 * A2 ^ 2 + 4 * Ak + 100) / α) * ENNReal.ofReal M := by
    calc volume {x : ℝ | α < ‖czConv K f x‖}
        ≤ volume (Vset ∪ ({x : ℝ | ENNReal.ofReal (α / 2) < ‖czConv K g x‖ₑ} ∪
              {x : ℝ | x ∉ Vset ∧ ENNReal.ofReal (α / 2) < ∑' j, ‖czConv K (b j) x‖ₑ})) :=
          measure_mono hsubset
      _ ≤ volume Vset + volume ({x : ℝ | ENNReal.ofReal (α / 2) < ‖czConv K g x‖ₑ} ∪
              {x : ℝ | x ∉ Vset ∧ ENNReal.ofReal (α / 2) < ∑' j, ‖czConv K (b j) x‖ₑ}) :=
          measure_union_le _ _
      _ ≤ volume Vset + (volume {x : ℝ | ENNReal.ofReal (α / 2) < ‖czConv K g x‖ₑ}
            + volume {x : ℝ | x ∉ Vset ∧ ENNReal.ofReal (α / 2) < ∑' j, ‖czConv K (b j) x‖ₑ}) :=
          add_le_add le_rfl (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (100 * M / α) + (ENNReal.ofReal (16 * A2 ^ 2 * M / α)
            + ENNReal.ofReal (4 * Ak * M / α)) := add_le_add hV_meas (add_le_add hgood hbad)
      _ = ENNReal.ofReal ((100 * M + 16 * A2 ^ 2 * M + 4 * Ak * M) / α) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (((24 * A2 ^ 2 + 4 * Ak + 100) * M) / α) := by
          apply ENNReal.ofReal_le_ofReal
          rw [div_le_div_iff_of_pos_right hα]
          nlinarith [hMnn, hAk, sq_nonneg A2]
      _ = ENNReal.ofReal ((24 * A2 ^ 2 + 4 * Ak + 100) / α) * ENNReal.ofReal M := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have he1 : eLpNorm f 1 volume = ENNReal.ofReal M := by
    rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hf, hMdef]
  calc volume {x : ℝ | α < ‖czConv K f x‖}
      ≤ ENNReal.ofReal ((24 * A2 ^ 2 + 4 * Ak + 100) / α) * ENNReal.ofReal M := hfin
    _ = ENNReal.ofReal ((24 * A2 ^ 2 + 4 * Ak + 100) / α) * eLpNorm f 1 volume := by rw [he1]

end

end Commons.Analysis.CalderonZygmund
