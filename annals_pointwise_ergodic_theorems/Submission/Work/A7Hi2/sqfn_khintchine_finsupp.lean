import Mathlib
import Submission.Work.A7Hi2.RealScaleDefs
import Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert
import Submission.Work.A7Hi2.tsum_bSign_conv
import Submission.Work.A7Hi2.eLpNorm_iSup_le
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.A7Hi2

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

/-- The convolution sum `n ↦ ∑'_y k l y * g (n - y)`. -/
private noncomputable def convSum (k : ℕ → ℤ → ℂ) (g : ℤ → ℂ) (l : ℕ) (n : ℤ) : ℂ :=
  ∑' y : ℤ, k l y * g (n - y)

/-- The sign sequence on `ℕ` determined by a sign pattern on `Fin N`. -/
private def signSeq (N : ℕ) (e : Fin N → Bool) : ℕ → Bool :=
  fun l => if h : l < N then e ⟨l, h⟩ else false

private lemma signSeq_apply {N : ℕ} (e : Fin N → Bool) (i : Fin N) :
    signSeq N e i = e i := by
  show (if h : i < N then e ⟨i, h⟩ else false) = e i
  rw [dif_pos i.2]

private lemma bSign_signSeq {N : ℕ} (e : Fin N → Bool) (i : Fin N) :
    Work.KMTAreas.ADev.bSign (signSeq N e) i = if e i then (1:ℂ) else -1 := by
  simp only [Work.KMTAreas.ADev.bSign, signSeq_apply e i]

private lemma measurable_ennreal_rpow_const (c : ℝ) :
    Measurable (fun x : ENNReal => x ^ c) :=
  measurable_pow.comp (measurable_id.prodMk measurable_const)

/-- Supremum commutes with `rpow` on `ℝ≥0∞` for a positive exponent. -/
private lemma iSup_rpow_ennreal {ι : Type*} (f : ι → ENNReal) {c : ℝ} (hc : 0 < c) :
    (⨆ i, f i) ^ c = ⨆ i, f i ^ c := by
  refine le_antisymm ?_ (iSup_le fun i => ENNReal.rpow_le_rpow (le_iSup f i) hc.le)
  have hle : (⨆ i, f i) ≤ (⨆ i, f i ^ c) ^ c⁻¹ := by
    refine iSup_le fun i => ?_
    have h := ENNReal.rpow_le_rpow (le_iSup (fun i => f i ^ c) i) (inv_nonneg.mpr hc.le)
    rwa [ENNReal.rpow_rpow_inv hc.ne'] at h
  calc (⨆ i, f i) ^ c ≤ ((⨆ i, f i ^ c) ^ c⁻¹) ^ c := ENNReal.rpow_le_rpow hle hc.le
    _ = (⨆ i, f i ^ c) ^ (c⁻¹ * c) := (ENNReal.rpow_mul _ _ _).symm
    _ = (⨆ i, f i ^ c) ^ (1 : ℝ) := by rw [inv_mul_cancel₀ hc.ne']
    _ = ⨆ i, f i ^ c := ENNReal.rpow_one _

/-- From the `p`-th root form of Khintchine's lower bound: the `p`-th power bound. -/
private lemma rpow_le_of_mul_le {c D A p : ℝ} (hc : 0 < c) (hp : 0 < p)
    (hD : 0 ≤ D) (hA : 0 ≤ A) (h : c * D ≤ A ^ (1/p)) :
    D ^ p ≤ (c⁻¹) ^ p * A := by
  have h1 : (c * D) ^ p ≤ A := by
    calc (c * D) ^ p ≤ (A ^ (1/p)) ^ p := Real.rpow_le_rpow (by positivity) h hp.le
      _ = A ^ ((1/p) * p) := (Real.rpow_mul hA (1/p) p).symm
      _ = A ^ (1:ℝ) := by rw [one_div, inv_mul_cancel₀ hp.ne']
      _ = A := Real.rpow_one A
  have h2 : c ^ p * D ^ p ≤ A := by
    rw [← Real.mul_rpow hc.le hD]; exact h1
  have h3 : (c ^ p)⁻¹ * (c ^ p * D ^ p) = D ^ p := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hc p)), one_mul]
  have h4 : D ^ p ≤ (c ^ p)⁻¹ * A := by
    have h5 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (Real.rpow_nonneg hc.le p))
    rwa [h3] at h5
  rwa [← Real.inv_rpow hc.le p] at h4

/-- The `ℝ≥0∞` square function of a finite block, raised to the `p`-th power, is
`ENNReal.ofReal` of the corresponding real quantity. -/
private lemma enorm_range_sum_rpow (N : ℕ) (z : ℕ → ℂ) {p : ℝ} (hp : 0 ≤ p) :
    ((∑ l ∈ Finset.range N, ‖z l‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) ^ p
      = ENNReal.ofReal ((∑ l ∈ Finset.range N, ‖z l‖ ^ 2) ^ (p/2)) := by
  have h1 : (∑ l ∈ Finset.range N, ‖z l‖ₑ ^ (2:ℝ))
      = ENNReal.ofReal (∑ l ∈ Finset.range N, ‖z l‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => by positivity)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ENNReal.rpow_two, show ‖z l‖ₑ = ENNReal.ofReal ‖z l‖ from (ofReal_norm (z l)).symm,
      ← ENNReal.ofReal_pow (norm_nonneg (z l)) 2]
  rw [h1, ← ENNReal.rpow_mul,
    ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun l _ => by positivity)
      (show (0:ℝ) ≤ (1:ℝ)/2 * p from mul_nonneg (by norm_num) hp),
    show (1:ℝ)/2 * p = p/2 by ring]

/-- The average of the `p`-th powers over all sign patterns, as an `ℝ≥0∞` quantity. -/
private lemma ofReal_avg_eq (N : ℕ) (z : (Fin N → Bool) → ℂ) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal ((∑ e : Fin N → Bool, ‖z e‖ ^ p) / (2:ℝ)^N)
      = (1/2 : ENNReal)^N * ∑ e : Fin N → Bool, ‖z e‖ₑ ^ p := by
  have htwo : ENNReal.ofReal (2:ℝ) = 2 := ENNReal.ofReal_natCast 2
  have hhalf : ENNReal.ofReal ((2:ℝ)⁻¹) = (1/2 : ENNReal) := by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2), htwo, one_div]
  have hsum : (∑ e : Fin N → Bool, ENNReal.ofReal (‖z e‖ ^ p))
      = ∑ e : Fin N → Bool, ‖z e‖ₑ ^ p := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← ofReal_norm (z e), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (z e)) hp]
  rw [div_eq_mul_inv, ← inv_pow,
    ENNReal.ofReal_mul (Finset.sum_nonneg fun e _ => Real.rpow_nonneg (norm_nonneg (z e)) p),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹) N, hhalf,
    ENNReal.ofReal_sum_of_nonneg (fun e _ => Real.rpow_nonneg (norm_nonneg (z e)) p), hsum,
    mul_comm]

/-- `eLpNorm`, raised to the `p`-th power, is the `p`-th power integral of the `enorm`. -/
private lemma eLpNorm_ofReal_rpow_eq {ε : Type*} [ENorm ε] [TopologicalSpace ε] {p : ℝ} (hp : 0 < p) (f : ℤ → ε) :
    (MeasureTheory.eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ)) ^ p
      = ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂(Measure.count : Measure ℤ) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal hp.le]
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]

/-- The sum of a constant over all sign patterns. -/
private lemma sum_const_card (N : ℕ) (A : ENNReal) :
    (∑ _e : Fin N → Bool, A) = ((2^N : ℕ) : ENNReal) * A := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    nsmul_eq_mul]

/-- `(1/2)^N * 2^N = 1` in `ℝ≥0∞`. -/
private lemma half_pow_mul_two_pow (N : ℕ) :
    (1/2 : ENNReal)^N * ((2^N : ℕ) : ENNReal) = 1 := by
  have h2 : ((2^N : ℕ) : ENNReal) = (2:ENNReal)^N := by
    rw [Nat.cast_pow]; simp
  have h3 : (1/2 : ENNReal) * 2 = 1 := by
    rw [one_div]
    exact ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr (by norm_num : (2:ℝ≥0) ≠ 0))
      ENNReal.coe_ne_top
  rw [h2, ← mul_pow, h3, one_pow]

/-- The sum of a constant over all sign patterns, weighted by `(1/2)^N`. -/
private lemma half_pow_mul_sum_const (N : ℕ) (A : ENNReal) :
    (1/2 : ENNReal)^N * (∑ _e : Fin N → Bool, A) = A := by
  rw [sum_const_card, ← mul_assoc, half_pow_mul_two_pow, one_mul]

theorem sqfn_khintchine_finsupp (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ → ℤ → ℂ) (C' : ℝ), 0 < C' →
      (∀ (F : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ),
        (∃ t : Finset ℤ, ∀ x : ℤ, x ∉ t → g x = 0) →
        MeasureTheory.eLpNorm
            (fun n : ℤ => ∑' y : ℤ, (∑ l ∈ F, Work.KMTAreas.ADev.bSign ω l * k l y) * g (n - y))
            (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
          ≤ ENNReal.ofReal C' * MeasureTheory.eLpNorm g (ENNReal.ofReal p)
              (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) →
      ∀ g : ℤ → ℂ, (∃ t : Finset ℤ, ∀ x : ℤ, x ∉ t → g x = 0) →
        MeasureTheory.eLpNorm
            (fun n : ℤ => (∑' l : ℕ, ‖∑' y : ℤ, k l y * g (n - y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
            (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
          ≤ ENNReal.ofReal (C * C') * MeasureTheory.eLpNorm g (ENNReal.ofReal p)
              (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  obtain ⟨c, _Ck, hc, _hCk, hkh⟩ := Commons.Analysis.Walsh.exists_khintchine_hilbert p hp.le
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro k C' hC' hhyp g hg
  obtain ⟨t, ht⟩ := hg
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  change MeasureTheory.eLpNorm
      (fun n : ℤ => (∑' l : ℕ, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2))
      (ENNReal.ofReal p) (Measure.count : Measure ℤ)
    ≤ ENNReal.ofReal (c⁻¹ * C') * MeasureTheory.eLpNorm g (ENNReal.ofReal p)
        (Measure.count : Measure ℤ)
  -- the bound coming from the linearisation hypothesis
  have hkey : ∀ (F : Finset ℕ) (ω : ℕ → Bool),
      MeasureTheory.eLpNorm (fun n : ℤ => ∑ l ∈ F, Work.KMTAreas.ADev.bSign ω l * convSum k g l n)
          (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal C' * MeasureTheory.eLpNorm g (ENNReal.ofReal p)
            (Measure.count : Measure ℤ) := by
    intro F ω
    have h := hhyp F ω g ⟨t, ht⟩
    have hfun : (fun n : ℤ => ∑ l ∈ F, Work.KMTAreas.ADev.bSign ω l * convSum k g l n)
        = (fun n : ℤ =>
            ∑' y : ℤ, (∑ l ∈ F, Work.KMTAreas.ADev.bSign ω l * k l y) * g (n - y)) := by
      funext n
      exact (tsum_bSign_conv ht k F ω n).symm
    rw [hfun]
    exact h
  -- the finite-block bound
  have hfin : ∀ N : ℕ,
      MeasureTheory.eLpNorm
          (fun n : ℤ => (∑ l ∈ Finset.range N, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2))
          (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal c⁻¹ * (ENNReal.ofReal C' *
            MeasureTheory.eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ)) := by
    intro N
    let Z : (Fin N → Bool) → ℤ → ℂ := fun e n =>
      ∑ l ∈ Finset.range N, Work.KMTAreas.ADev.bSign (signSeq N e) l * convSum k g l n
    -- pointwise Khintchine
    have hkhint : ∀ n : ℤ,
        c * (∑ l ∈ Finset.range N, ‖convSum k g l n‖ ^ 2) ^ ((1:ℝ)/2)
          ≤ ((∑ e : Fin N → Bool, ‖Z e n‖ ^ p) / (2:ℝ)^N) ^ ((1:ℝ)/p) := by
      intro n
      have hb : ∀ e : Fin N → Bool,
          (∑ i : Fin N, (if e i then (1:ℂ) else -1) • convSum k g i n) = Z e n := by
        intro e
        show (∑ i : Fin N, (if e i then (1:ℂ) else -1) • convSum k g i n)
          = ∑ l ∈ Finset.range N,
              Work.KMTAreas.ADev.bSign (signSeq N e) l * convSum k g l n
        rw [show (∑ i : Fin N, (if e i then (1:ℂ) else -1) • convSum k g i n)
              = ∑ i : Fin N, Work.KMTAreas.ADev.bSign (signSeq N e) i * convSum k g i n from
            Finset.sum_congr rfl (fun i _ => by rw [bSign_signSeq e i, smul_eq_mul])]
        rw [Fin.sum_univ_eq_sum_range
          (fun l => Work.KMTAreas.ADev.bSign (signSeq N e) l * convSum k g l n) N]
      have h := (hkh N (fun i : Fin N => convSum k g i n)).1
      have h2 : (∑ e : Fin N → Bool,
            ‖∑ i : Fin N, (if e i then (1:ℂ) else -1) • convSum k g i n‖ ^ p)
          = ∑ e : Fin N → Bool, ‖Z e n‖ ^ p := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hb e]
      rw [Fin.sum_univ_eq_sum_range (fun l => ‖convSum k g l n‖ ^ 2) N, h2] at h
      exact h
    -- the pointwise ℝ≥0∞ inequality
    have hpt : ∀ n : ℤ,
        ((∑ l ∈ Finset.range N, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) ^ p
          ≤ (ENNReal.ofReal c⁻¹)^p * ((1/2 : ENNReal)^N *
              ∑ e : Fin N → Bool, ‖Z e n‖ₑ ^ p) := by
      intro n
      have hDp : ((∑ l ∈ Finset.range N, ‖convSum k g l n‖ ^ 2) ^ ((1:ℝ)/2)) ^ p
          ≤ (c⁻¹)^p * ((∑ e : Fin N → Bool, ‖Z e n‖ ^ p) / (2:ℝ)^N) := by
        refine rpow_le_of_mul_le hc hp0 ?_ ?_ ?_
        · exact Real.rpow_nonneg (Finset.sum_nonneg fun l _ => by positivity) _
        · exact div_nonneg (Finset.sum_nonneg fun e _ => Real.rpow_nonneg (norm_nonneg _) p)
            (by positivity)
        · exact hkhint n
      calc ((∑ l ∈ Finset.range N, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) ^ p
          = ENNReal.ofReal (((∑ l ∈ Finset.range N, ‖convSum k g l n‖ ^ 2) ^
                ((1:ℝ)/2)) ^ p) := by
            rw [enorm_range_sum_rpow N (fun l => convSum k g l n) hp0.le]
            congr 1
            rw [← Real.rpow_mul (Finset.sum_nonneg fun l _ => by positivity),
              show (1:ℝ)/2 * p = p/2 by ring]
        _ ≤ ENNReal.ofReal ((c⁻¹)^p * ((∑ e : Fin N → Bool, ‖Z e n‖ ^ p) / (2:ℝ)^N)) :=
            ENNReal.ofReal_le_ofReal hDp
        _ = (ENNReal.ofReal c⁻¹)^p * ((1/2 : ENNReal)^N *
              ∑ e : Fin N → Bool, ‖Z e n‖ₑ ^ p) := by
            rw [ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hc.le) p),
              ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hc.le) hp0.le,
              ofReal_avg_eq N (fun e => Z e n) hp0.le]
    have hmeasB : ∀ e : Fin N → Bool, Measurable (fun n : ℤ => ‖Z e n‖ₑ ^ p) :=
      fun e => measurable_of_countable _
    have hint : (∫⁻ n : ℤ,
          ((∑ l ∈ Finset.range N, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) ^ p
          ∂(Measure.count : Measure ℤ))
        ≤ (ENNReal.ofReal c⁻¹)^p * ((1/2 : ENNReal)^N *
            ∑ e : Fin N → Bool, (ENNReal.ofReal C' *
              MeasureTheory.eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ))^p) := by
      have h1 : (∫⁻ n : ℤ,
            ((∑ l ∈ Finset.range N, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) ^ p
            ∂(Measure.count : Measure ℤ))
          ≤ ∫⁻ n : ℤ, (ENNReal.ofReal c⁻¹)^p * ((1/2 : ENNReal)^N *
              ∑ e : Fin N → Bool, ‖Z e n‖ₑ ^ p) ∂(Measure.count : Measure ℤ) :=
        lintegral_mono fun n => hpt n
      have hsumle : (∑ e : Fin N → Bool,
            ∫⁻ n : ℤ, ‖Z e n‖ₑ ^ p ∂(Measure.count : Measure ℤ))
          ≤ ∑ e : Fin N → Bool, (ENNReal.ofReal C' *
              MeasureTheory.eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ))^p :=
        Finset.sum_le_sum fun e _ => by
          rw [← eLpNorm_ofReal_rpow_eq (f := fun n => Z e n) hp0]
          exact ENNReal.rpow_le_rpow (hkey (Finset.range N) (signSeq N e)) hp0.le
      calc (∫⁻ n : ℤ,
              ((∑ l ∈ Finset.range N, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) ^ p
              ∂(Measure.count : Measure ℤ))
          ≤ ∫⁻ n : ℤ, (ENNReal.ofReal c⁻¹)^p * ((1/2 : ENNReal)^N *
              ∑ e : Fin N → Bool, ‖Z e n‖ₑ ^ p) ∂(Measure.count : Measure ℤ) := h1
        _ = (ENNReal.ofReal c⁻¹)^p * ((1/2 : ENNReal)^N *
              ∑ e : Fin N → Bool, ∫⁻ n : ℤ, ‖Z e n‖ₑ ^ p ∂(Measure.count : Measure ℤ)) := by
            rw [lintegral_const_mul _ (measurable_of_countable _),
              lintegral_const_mul _ (measurable_of_countable _),
              lintegral_finsetSum Finset.univ (fun e _ => hmeasB e)]
        _ ≤ (ENNReal.ofReal c⁻¹)^p * ((1/2 : ENNReal)^N *
              ∑ e : Fin N → Bool, (ENNReal.ofReal C' *
                MeasureTheory.eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ))^p) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumle zero_le) zero_le
    have hmain : (MeasureTheory.eLpNorm
          (fun n : ℤ => (∑ l ∈ Finset.range N, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2))
          (ENNReal.ofReal p) (Measure.count : Measure ℤ))^p
        ≤ (ENNReal.ofReal c⁻¹ * (ENNReal.ofReal C' *
            MeasureTheory.eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ)))^p := by
      rw [eLpNorm_ofReal_rpow_eq hp0]
      simp only [enorm_eq_self]
      calc ∫⁻ n : ℤ,
            ((∑ l ∈ Finset.range N, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) ^ p
            ∂(Measure.count : Measure ℤ)
          ≤ (ENNReal.ofReal c⁻¹)^p * ((1/2 : ENNReal)^N *
              ∑ e : Fin N → Bool, (ENNReal.ofReal C' *
                MeasureTheory.eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ))^p) := hint
        _ = (ENNReal.ofReal c⁻¹)^p * (ENNReal.ofReal C' *
                MeasureTheory.eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ))^p := by
            rw [half_pow_mul_sum_const N ((ENNReal.ofReal C' *
                MeasureTheory.eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ))^p)]
        _ = ((ENNReal.ofReal c⁻¹) * (ENNReal.ofReal C' *
                MeasureTheory.eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ)))^p :=
            (ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal c⁻¹) (ENNReal.ofReal C' *
                MeasureTheory.eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ))
              hp0.le).symm
    exact (ENNReal.rpow_le_rpow_iff hp0).mp hmain
  -- the sup over the block length
  have hS : (fun n : ℤ => (∑' l : ℕ, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2))
      = fun n : ℤ => ⨆ N : ℕ,
          (∑ l ∈ Finset.range N, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
    funext n
    rw [← iSup_rpow_ennreal
      (fun N : ℕ => ∑ l ∈ Finset.range N, ‖convSum k g l n‖ₑ ^ (2:ℝ))
      (by norm_num : (0:ℝ) < 1/2)]
    congr 1
    exact ENNReal.tsum_eq_iSup_sum' (fun N : ℕ => Finset.range N) fun s =>
      ⟨s.sum (fun x => x) + 1, fun l hl => by
        have hle : l ≤ s.sum (fun x => x) :=
          Finset.single_le_sum (fun j _ => Nat.zero_le j) hl
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)⟩
  have hmono : Monotone (fun N : ℕ => fun n : ℤ =>
      (∑ l ∈ Finset.range N, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) := by
    intro N M hNM n
    refine ENNReal.rpow_le_rpow
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNM) ?_)
      (by norm_num)
    intro l _ _; exact zero_le
  have hbound : (⨆ N : ℕ, MeasureTheory.eLpNorm
        (fun n : ℤ => (∑ l ∈ Finset.range N, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2))
        (ENNReal.ofReal p) (Measure.count : Measure ℤ))
      ≤ ENNReal.ofReal c⁻¹ * (ENNReal.ofReal C' *
          MeasureTheory.eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ)) :=
    iSup_le hfin
  calc MeasureTheory.eLpNorm
        (fun n : ℤ => (∑' l : ℕ, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2))
        (ENNReal.ofReal p) (Measure.count : Measure ℤ)
      = MeasureTheory.eLpNorm
          (fun n : ℤ => ⨆ N : ℕ,
            (∑ l ∈ Finset.range N, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2))
          (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by rw [hS]
    _ ≤ ⨆ N : ℕ, MeasureTheory.eLpNorm
          (fun n : ℤ => (∑ l ∈ Finset.range N, ‖convSum k g l n‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2))
          (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
        eLpNorm_iSup_le hp0 hmono (fun N => measurable_of_countable _)
    _ ≤ ENNReal.ofReal c⁻¹ * (ENNReal.ofReal C' *
          MeasureTheory.eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ)) := hbound
    _ = ENNReal.ofReal (c⁻¹ * C') * MeasureTheory.eLpNorm g (ENNReal.ofReal p)
          (Measure.count : Measure ℤ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]

end Work.A7Hi2
