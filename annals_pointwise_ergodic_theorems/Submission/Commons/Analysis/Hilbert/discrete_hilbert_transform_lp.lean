import Mathlib
import Submission.Commons.Analysis.DiscreteCZ.discrete_convolution_weak_type_one
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable
import Submission.Commons.MeasureTheory.Function.eLpNorm_count
import Submission.Commons.Analysis.Lp.eLpNorm_le_of_pairing_bound
import Submission.Commons.Analysis.Integral.holder_complex_finset
import Submission.Commons.Analysis.Hilbert.tsum_int_ofReal_natAbs_inv_sq_le
import Submission.Commons.Analysis.InfiniteSum.tendsto_sum_Icc_tsum
import Submission.Port.Aesm

open MeasureTheory Measure Filter
open scoped ENNReal BigOperators NNReal

set_option maxHeartbeats 1000000

namespace Commons.Analysis.Hilbert

noncomputable section

/-- The Hilbert kernel `1/z` (with the principal value convention `1/0 = 0`). -/
def hkern (z : ℤ) : ℂ := ((z : ℤ) : ℂ)⁻¹

/-- The discrete Hilbert transform on `ℤ`. -/
def hH (f : ℤ → ℂ) : ℤ → ℂ := fun n => ∑' m : ℤ, hkern (n - m) * f m

lemma hH_apply (f : ℤ → ℂ) (n : ℤ) :
    hH f n = ∑' m : ℤ, ((n - m : ℤ) : ℂ)⁻¹ * f m := by
  simp only [hH, hkern]

/-! ### Converting between `eLpNorm` on `ℤ` and `ℓᵖ`-sums -/

/-- `eLpNorm` on `ℤ` with the counting measure, in terms of the `ℓᵖ` sum. -/
theorem eLpNorm_count_rpow (u : ℤ → ℂ) {p : ℝ} (hp : 0 < p) :
    eLpNorm u (ENNReal.ofReal p) (Measure.count : Measure ℤ)
      = (∑' n : ℤ, ‖u n‖ₑ ^ p) ^ (1 / p) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
        (p := ENNReal.ofReal p) (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
    MeasureTheory.lintegral_count]
  rw [ENNReal.toReal_ofReal hp.le]

/-- For `p ≥ 0` and `p`-summable `u`, the `enorm`-`p`-power sum is the `ofReal` of the
`p`-power sum. -/
theorem lintegral_enorm_rpow_eq_ofReal_tsum (u : ℤ → ℂ) {p : ℝ} (hp : 0 ≤ p)
    (h : Summable (fun n : ℤ => ‖u n‖ ^ p)) :
    (∑' n : ℤ, ‖u n‖ₑ ^ p) = ENNReal.ofReal (∑' n : ℤ, ‖u n‖ ^ p) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun n => Real.rpow_nonneg (norm_nonneg (u n)) p) h]
  apply tsum_congr; intro n
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (u n)) hp, ofReal_norm]

/-- `eLpNorm` of a `p`-summable family. -/
theorem eLpNorm_count_eq_ofReal (u : ℤ → ℂ) {p : ℝ} (hp : 0 < p)
    (h : Summable (fun n : ℤ => ‖u n‖ ^ p)) :
    eLpNorm u (ENNReal.ofReal p) (Measure.count : Measure ℤ)
      = ENNReal.ofReal ((∑' n : ℤ, ‖u n‖ ^ p) ^ (1 / p)) := by
  rw [eLpNorm_count_rpow u hp, lintegral_enorm_rpow_eq_ofReal_tsum u hp.le h,
    ENNReal.ofReal_rpow_of_nonneg
      (tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg (u n)) p)) (by positivity)]

/-- A non-negative series of reals has finite `ofReal`-sum iff it is summable. -/
theorem tsum_ofReal_ne_top_iff_summable {f : ℤ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    (∑' n, ENNReal.ofReal (f n)) ≠ ⊤ ↔ Summable f := by
  constructor
  · intro h
    have hg : (∑' n, ((NNReal.mk (f n) (hf n)) : ℝ≥0∞)) ≠ ⊤ := by
      rw [show (∑' n, ((NNReal.mk (f n) (hf n)) : ℝ≥0∞)) = ∑' n, ENNReal.ofReal (f n) from
        tsum_congr (fun n => (ENNReal.ofReal_eq_coe_nnreal (hf n)).symm)]
      exact h
    have h2 := (ENNReal.tsum_coe_ne_top_iff_summable_coe).mp hg
    simpa using h2
  · intro h
    exact h.tsum_ofReal_ne_top

/-- A non-negative series of reals has finite `ofReal`-sum iff it is summable. -/
theorem tsum_ofReal_lt_top_iff_summable {f : ℤ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    (∑' n, ENNReal.ofReal (f n)) < ⊤ ↔ Summable f := by
  rw [lt_top_iff_ne_top]
  exact tsum_ofReal_ne_top_iff_summable hf

/-- Finiteness of the `eLpNorm` on `ℤ` with the counting measure is `ℓᵖ`-summability. -/
theorem eLpNorm_count_lt_top_iff (u : ℤ → ℂ) {p : ℝ} (hp : 0 < p) :
    eLpNorm u (ENNReal.ofReal p) (Measure.count : Measure ℤ) < ⊤
      ↔ Summable (fun n : ℤ => ‖u n‖ ^ p) := by
  have hcoe : (∑' n : ℤ, ‖u n‖ₑ ^ p) = ∑' n : ℤ, ENNReal.ofReal (‖u n‖ ^ p) := by
    apply tsum_congr; intro n
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (u n)) hp.le, ofReal_norm]
  rw [eLpNorm_count_rpow u hp, hcoe,
    ENNReal.rpow_lt_top_iff_of_pos (show (0:ℝ) < 1/p by positivity),
    tsum_ofReal_lt_top_iff_summable (fun n => Real.rpow_nonneg (norm_nonneg (u n)) p)]


/-! ### The `ℓ²` bound in `eLpNorm` form -/

lemma summable_norm_sq_of_summable {f : ℤ → ℂ} (hf : Summable f) :
    Summable (fun n => ‖f n‖ ^ 2) := by
  refine Summable.of_norm_bounded_eventually hf.norm ?_
  have hlim : ∀ᶠ n : ℤ in cofinite, ‖f n‖ < 1 :=
    (hf.tendsto_cofinite_zero.norm).eventually
      (eventually_lt_nhds (show ‖(0 : ℂ)‖ < 1 by norm_num))
  filter_upwards [hlim] with n hn
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg (f n)]

/-- `x ^ (2 : ℝ) = x ^ (2 : ℕ)`. -/
lemma rpow_two_eq_pow_two (x : ℝ) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

/-! ### The size bound and the weak-type `(1,1)` bound -/

lemma hkern_norm_le_one (z : ℤ) : ‖hkern z‖ ≤ 1 := by
  rw [hkern]
  by_cases hz : z = 0
  · simp [hz]
  · rw [norm_inv, Complex.norm_intCast]
    rw [inv_le_one₀]
    · rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz
    · rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz

lemma hkern_antisym (n m : ℤ) : hkern (m - n) = - hkern (n - m) := by
  rw [hkern, hkern]
  have h : ((m - n : ℤ) : ℂ) = - ((n - m : ℤ) : ℂ) := by push_cast; ring
  rw [h, inv_neg]


/-! ### Marcinkiewicz interpolation: the `ℓᵖ` bound for `1 < p < 2` -/

/-- Additivity of the discrete Hilbert transform on `ℓ¹`. -/
theorem hH_add {f g : ℤ → ℂ} (hf : Summable (fun n : ℤ => ‖f n‖))
    (hg : Summable (fun n : ℤ => ‖g n‖)) : hH (f + g) = hH f + hH g := by
  funext x
  have hsumf : Summable (fun m : ℤ => hkern (x - m) * f m) :=
    Summable.of_norm_bounded hf (fun m => by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hkern_norm_le_one _))
  have hsumg : Summable (fun m : ℤ => hkern (x - m) * g m) :=
    Summable.of_norm_bounded hg (fun m => by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hkern_norm_le_one _))
  simp only [hH, Pi.add_apply]
  rw [show (∑' m : ℤ, hkern (x - m) * (f m + g m))
        = ∑' m : ℤ, (hkern (x - m) * f m + hkern (x - m) * g m) from
      tsum_congr (fun m => by ring)]
  exact Summable.tsum_add hsumf hsumg

/-! ### A Fatou/liminf principle for `eLpNorm` on `ℤ` -/

/-- Lower semicontinuity of `eLpNorm` under pointwise limits, on `ℤ` with the counting measure. -/
theorem eLpNorm_le_liminf_of_tendsto {p : ℝ} (hp : 0 < p) {u : ℕ → ℤ → ℂ} {U : ℤ → ℂ}
    (h : ∀ x : ℤ, Tendsto (fun N => u N x) atTop (nhds (U x))) :
    eLpNorm U (ENNReal.ofReal p) (Measure.count : Measure ℤ)
      ≤ Filter.liminf (fun N => eLpNorm (u N) (ENNReal.ofReal p)
          (Measure.count : Measure ℤ)) atTop := by
  have hpne0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hpnetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcongr : (fun N => eLpNorm' (u N) p (Measure.count : Measure ℤ))
      = (fun N => eLpNorm (u N) (ENNReal.ofReal p) (Measure.count : Measure ℤ)) := by
    funext N; rw [eLpNorm_eq_eLpNorm' (hf := by pw_aesm) hpne0 hpnetop, ENNReal.toReal_ofReal hp.le]
  have hmain : eLpNorm' U p (Measure.count : Measure ℤ)
      ≤ Filter.liminf (fun N => eLpNorm' (u N) p (Measure.count : Measure ℤ)) atTop :=
    MeasureTheory.Lp.eLpNorm'_lim_le_liminf_eLpNorm' hp
      (fun n => (measurable_of_countable (u n)).aestronglyMeasurable) (Eventually.of_forall h)
  rw [eLpNorm_eq_eLpNorm' (hf := by pw_aesm) hpne0 hpnetop, ENNReal.toReal_ofReal hp.le, ← hcongr]
  exact hmain


/-! ### Extending an `ℓᵖ` bound from finitely supported functions to all of `ℓᵖ` -/

lemma integrable_of_finsupp {f : ℤ → ℂ} (hf : ∃ s : Finset ℤ, ∀ n, n ∉ s → f n = 0) :
    Integrable f (Measure.count : Measure ℤ) := by
  obtain ⟨s, hs⟩ := hf
  exact integrable_count_iff.mpr (summable_of_ne_finset_zero (fun n hn => by rw [hs n hn, norm_zero]))

/-! ### Preparations for the duality argument -/

lemma star_hkern (z : ℤ) : star (hkern z) = hkern z := by
  rw [hkern, star_inv₀]
  congr 1
  exact map_intCast (starRingEnd ℂ) z

lemma hH_eq_sum_of_finsupp {f : ℤ → ℂ} {s : Finset ℤ} (hs : ∀ n, n ∉ s → f n = 0) (n : ℤ) :
    hH f n = ∑ m ∈ s, hkern (n - m) * f m := by
  rw [hH, tsum_eq_sum (s := s) (fun m hm => by rw [hs m hm, mul_zero])]

/-- The finite-sum pairing (antisymmetry) identity for the Hilbert kernel. -/
lemma hilbert_pairing {s t : Finset ℤ} {f g : ℤ → ℂ} (hf : ∀ n, n ∉ t → f n = 0)
    (hg : ∀ n, n ∉ s → g n = 0) :
    (∑ n ∈ s, (∑ m ∈ t, hkern (n - m) * f m) * star (g n))
      = - ∑ m ∈ t, f m * star (∑ n ∈ s, hkern (m - n) * g n) := by
  have hpair : ∀ m : ℤ, (∑ n ∈ s, hkern (n - m) * star (g n))
      = - star (∑ n ∈ s, hkern (m - n) * g n) := by
    intro m
    rw [star_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro n _
    rw [star_mul, star_hkern, hkern_antisym m n]
    ring
  have hswap : (∑ n ∈ s, (∑ m ∈ t, hkern (n - m) * f m) * star (g n))
      = ∑ m ∈ t, f m * ∑ n ∈ s, hkern (n - m) * star (g n) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    ring
  rw [hswap]
  rw [show (∑ m ∈ t, f m * ∑ n ∈ s, hkern (n - m) * star (g n))
        = ∑ m ∈ t, -(f m * star (∑ n ∈ s, hkern (m - n) * g n)) from by
      apply Finset.sum_congr rfl; intro m _
      rw [hpair m, mul_neg]]
  rw [Finset.sum_neg_distrib]

/-- The pairing identity for the discrete Hilbert transform on finitely supported functions. -/
lemma hilbert_pairing_hH {s t : Finset ℤ} {f g : ℤ → ℂ} (hf : ∀ n, n ∉ t → f n = 0)
    (hg : ∀ n, n ∉ s → g n = 0) :
    (∑ n ∈ s, hH f n * star (g n)) = - ∑ m ∈ t, f m * star (hH g m) := by
  have h1 : (∑ n ∈ s, hH f n * star (g n))
      = ∑ n ∈ s, (∑ m ∈ t, hkern (n - m) * f m) * star (g n) :=
    Finset.sum_congr rfl (fun n _ => by rw [hH_eq_sum_of_finsupp hf n])
  have h2 : (∑ m ∈ t, f m * star (hH g m))
      = ∑ m ∈ t, f m * star (∑ n ∈ s, hkern (m - n) * g n) :=
    Finset.sum_congr rfl (fun m _ => by rw [hH_eq_sum_of_finsupp hg m])
  rw [h1, h2]
  exact hilbert_pairing hf hg

/-! ### Converting between the `eLpNorm` and the `ℓᵖ`-sum form -/

lemma tsum_rpow_le_of_eLpNorm_le {q X : ℝ} (hq : 0 < q) (hX : 0 ≤ X) {u : ℤ → ℂ}
    (h : eLpNorm u (ENNReal.ofReal q) (Measure.count : Measure ℤ) ≤ ENNReal.ofReal X) :
    Summable (fun n : ℤ => ‖u n‖ ^ q) ∧ (∑' n : ℤ, ‖u n‖ ^ q) ^ (1 / q) ≤ X := by
  have h1 : (∑' n : ℤ, ‖u n‖ₑ ^ q) ^ (1 / q) ≤ ENNReal.ofReal X := by
    rw [← eLpNorm_count_rpow u hq]; exact h
  have hcoe : (∑' n : ℤ, ‖u n‖ₑ ^ q) = ∑' n : ℤ, ENNReal.ofReal (‖u n‖ ^ q) :=
    tsum_congr (fun n => by
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (u n)) hq.le, ofReal_norm])
  have h2 : (∑' n : ℤ, ENNReal.ofReal (‖u n‖ ^ q)) < ⊤ := by
    have ha : (∑' n : ℤ, ‖u n‖ₑ ^ q) ^ (1 / q) < ⊤ :=
      lt_of_le_of_lt h1 (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
    have hb : (∑' n : ℤ, ‖u n‖ₑ ^ q) < ⊤ :=
      (ENNReal.rpow_lt_top_iff_of_pos (show (0:ℝ) < 1 / q by positivity)).mp ha
    rwa [hcoe] at hb
  have hsum : Summable (fun n : ℤ => ‖u n‖ ^ q) :=
    (tsum_ofReal_lt_top_iff_summable (fun n => Real.rpow_nonneg (norm_nonneg (u n)) q)).mp h2
  refine ⟨hsum, ?_⟩
  have h4 : ENNReal.ofReal ((∑' n : ℤ, ‖u n‖ ^ q) ^ (1 / q)) ≤ ENNReal.ofReal X := by
    rw [← ENNReal.ofReal_rpow_of_nonneg
        (tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg (u n)) q)) (by positivity),
      ← lintegral_enorm_rpow_eq_ofReal_tsum u hq.le hsum]
    exact h1
  exact (ENNReal.ofReal_le_ofReal_iff hX).mp h4

lemma eLpNorm_le_ofReal_of_tsum_rpow_le {q X : ℝ} (hq : 0 < q) {u : ℤ → ℂ}
    (hu : Summable (fun n : ℤ => ‖u n‖ ^ q)) (h : (∑' n : ℤ, ‖u n‖ ^ q) ^ (1 / q) ≤ X) :
    eLpNorm u (ENNReal.ofReal q) (Measure.count : Measure ℤ) ≤ ENNReal.ofReal X := by
  rw [eLpNorm_count_rpow u hq, lintegral_enorm_rpow_eq_ofReal_tsum u hq.le hu,
    ENNReal.ofReal_rpow_of_nonneg
      (tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg (u n)) q)) (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

lemma integral_count_eq_tsum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℤ → E} (hf : Integrable f (Measure.count : Measure ℤ)) :
    ∫ x : ℤ, f x ∂(Measure.count : Measure ℤ) = ∑' x : ℤ, f x := by
  rw [MeasureTheory.integral_countable hf]
  apply tsum_congr; intro x
  rw [MeasureTheory.Measure.real, MeasureTheory.Measure.count_singleton]
  simp


/-! ### The duality argument: the `ℓᵖ` bound for `p > 2` -/

lemma exists_finset_subset_Icc (s : Finset ℤ) :
    ∃ N : ℕ, s ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  refine ⟨s.sum (fun z : ℤ => z.natAbs), fun z hz => ?_⟩
  rw [Finset.mem_Icc]
  have h1 : (z.natAbs : ℤ) ≤ ((s.sum (fun z : ℤ => z.natAbs) : ℕ) : ℤ) := by
    exact_mod_cast Finset.single_le_sum (fun i _ => Nat.zero_le _) hz
  rw [← Int.abs_eq_natAbs] at h1
  exact abs_le.mp h1

lemma rpow_inv_self {x p : ℝ} (hx : 0 ≤ x) (hp : p ≠ 0) : (x ^ (1 / p)) ^ p = x := by
  rw [← Real.rpow_mul hx (1 / p) p, show (1 / p) * p = 1 by field_simp, Real.rpow_one]

/-- The `ℓᵖ` bound for the discrete Hilbert transform, `p > 2`, for finitely supported
functions, by duality against the `ℓ^{p'}` bound. -/
theorem hilbert_large_of_small {p : ℝ} (hp : 2 < p)
    {Cq : ℝ} (hCq : 0 < Cq)
    (hsmall : ∀ g : ℤ → ℂ,
      eLpNorm (hH g) (ENNReal.ofReal (p / (p - 1))) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal Cq * eLpNorm g (ENNReal.ofReal (p / (p - 1)))
            (Measure.count : Measure ℤ)) :
    ∀ f : ℤ → ℂ, (∃ s : Finset ℤ, ∀ n, n ∉ s → f n = 0) →
      eLpNorm (hH f) (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal Cq * eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
  intro f hfs
  obtain ⟨F, hF⟩ := hfs
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  set q : ℝ := p / (p - 1) with hq
  have hq1 : 1 < q := by
    rw [hq, one_lt_div (by linarith)]; linarith
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    exact ⟨hp1, by rw [hq]; field_simp; ring⟩
  have hfsum : Summable (fun n : ℤ => ‖f n‖ ^ p) := by
    refine summable_of_hasFiniteSupport ((Finset.finite_toSet F).subset ?_)
    intro n hn
    by_contra hc
    rw [Function.mem_support] at hn
    exact hn (by rw [hF n hc, norm_zero, Real.zero_rpow hp0.ne'])
  set Nf : ℝ := (∑' n : ℤ, ‖f n‖ ^ p) ^ (1 / p) with hNf
  have hNfnn : 0 ≤ Nf := Real.rpow_nonneg (tsum_nonneg fun n => Real.rpow_nonneg (norm_nonneg _) _) _
  have hef : eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) = ENNReal.ofReal Nf :=
    eLpNorm_count_eq_ofReal f hp0 hfsum
  set B : ℝ := ∑ m ∈ F, ‖f m‖ with hB
  have hBnn : 0 ≤ B := Finset.sum_nonneg (fun m _ => norm_nonneg _)
  have hNfF : (∑ m ∈ F, ‖f m‖ ^ p) ^ (1 / p) ≤ Nf := by
    rw [hNf]
    exact Real.rpow_le_rpow (Finset.sum_nonneg (fun m _ => Real.rpow_nonneg (norm_nonneg _) _))
      (Summable.sum_le_tsum F (fun n _ => Real.rpow_nonneg (norm_nonneg _) _) hfsum)
      (by positivity)
  have key : ∀ N : ℕ,
      (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖hH f n‖ ^ p) ^ (1 / p) ≤ Cq * Nf := by
    intro N
    set Sfin : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hSfin
    set hS : ℤ → ℂ := fun n => if n ∈ Sfin then hH f n else 0 with hhS
    have hsuppS : ∀ n : ℤ, n ∉ (Sfin : Set ℤ) → hS n = 0 := by
      intro n hn
      change (if n ∈ Sfin then hH f n else 0) = 0
      rw [if_neg (by simpa using hn)]
    have hbdd : ∀ n : ℤ, ‖hS n‖ ≤ B := by
      intro n
      change ‖(if n ∈ Sfin then hH f n else 0)‖ ≤ B
      by_cases hn : n ∈ Sfin
      · rw [if_pos hn]
        calc ‖hH f n‖ = ‖∑ m ∈ F, hkern (n - m) * f m‖ := by rw [hH_eq_sum_of_finsupp hF n]
          _ ≤ ∑ m ∈ F, ‖hkern (n - m) * f m‖ := norm_sum_le _ _
          _ ≤ ∑ m ∈ F, ‖f m‖ := Finset.sum_le_sum (fun m _ => by
                rw [norm_mul]
                exact mul_le_of_le_one_left (norm_nonneg _) (hkern_norm_le_one _))
          _ = B := rfl
      · rw [if_neg hn, norm_zero]; exact hBnn
    have hSmeas : MeasurableSet (Sfin : Set ℤ) :=
      (Set.countable_univ.mono (Set.subset_univ _)).measurableSet
    have hSfin_ne_top : Measure.count (Sfin : Set ℤ) ≠ ⊤ := by
      rw [Measure.count_apply_finset]; exact ENNReal.natCast_ne_top _
    obtain ⟨g, hgint, hgsupp, hgLq, hpair⟩ :=
      Commons.Analysis.Lp.exists_dual_pairing_of_finite_support hS hp1
        (le_trans (norm_nonneg _) (hbdd 0))
        (measurable_of_countable hS).aestronglyMeasurable hbdd
        (Sfin : Set ℤ) hSmeas hSfin_ne_top hsuppS
    have hgsum_q : Summable (fun n : ℤ => ‖hH g n‖ ^ q) ∧
        (∑' n : ℤ, ‖hH g n‖ ^ q) ^ (1 / q) ≤ Cq := by
      have heq : eLpNorm g (ENNReal.ofReal q) (Measure.count : Measure ℤ) ≤ 1 := by
        rw [hq]; exact hgLq
      have h1 : eLpNorm (hH g) (ENNReal.ofReal q) (Measure.count : Measure ℤ)
          ≤ ENNReal.ofReal Cq := by
        calc eLpNorm (hH g) (ENNReal.ofReal q) (Measure.count : Measure ℤ)
            ≤ ENNReal.ofReal Cq * eLpNorm g (ENNReal.ofReal q) (Measure.count : Measure ℤ) := by
              rw [hq]; exact hsmall g
          _ ≤ ENNReal.ofReal Cq * 1 := by gcongr
          _ = ENNReal.ofReal Cq := mul_one _
      exact tsum_rpow_le_of_eLpNorm_le hq0 hCq.le h1
    have hgfs : ∀ n : ℤ, n ∉ Sfin → g n = 0 := fun n hn => hgsupp n (by simpa using hn)
    have hint_int : Integrable (fun x : ℤ => inner ℂ (hS x) (g x)) Measure.count :=
      integrable_of_finsupp ⟨Sfin, fun n hn => by rw [hgfs n hn]; simp⟩
    have hint : ‖∫ x : ℤ, inner ℂ (hS x) (g x) ∂Measure.count‖
        = ‖∑ m ∈ F, f m * star (hH g m)‖ := by
      rw [integral_count_eq_tsum hint_int]
      have h1 : ∑' x : ℤ, inner ℂ (hS x) (g x) = ∑' x : ℤ, g x * star (hS x) :=
        tsum_congr (fun x => RCLike.inner_apply _ _)
      rw [h1]
      have h2 : ∑' x : ℤ, g x * star (hS x) = ∑ x ∈ Sfin, g x * star (hS x) := by
        apply tsum_eq_sum
        intro x hx
        rw [hgfs x hx, zero_mul]
      rw [h2]
      have h3 : star (∑ x ∈ Sfin, hS x * star (g x)) = ∑ x ∈ Sfin, g x * star (hS x) := by
        rw [star_sum]
        apply Finset.sum_congr rfl; intro x _
        rw [star_mul, star_star]
      rw [← h3, norm_star]
      have h4 : (∑ x ∈ Sfin, hS x * star (g x)) = ∑ x ∈ Sfin, hH f x * star (g x) := by
        apply Finset.sum_congr rfl; intro x hx
        change (if x ∈ Sfin then hH f x else 0) * star (g x) = hH f x * star (g x)
        rw [if_pos hx]
      rw [h4, hilbert_pairing_hH hF hgfs, norm_neg]
    have hholder : ‖∑ m ∈ F, f m * star (hH g m)‖
        ≤ Nf * (∑' n : ℤ, ‖hH g n‖ ^ q) ^ (1 / q) := by
      have h1 : ‖∑ m ∈ F, f m * star (hH g m)‖
          = ‖∑ m ∈ F, star (f m) * hH g m‖ := by
        rw [← norm_star, star_sum]
        congr 1
        apply Finset.sum_congr rfl; intro m _
        rw [star_mul, star_star]
        ring
      rw [h1]
      refine (Commons.Analysis.Integral.holder_complex_finset F (fun m => star (f m))
        (fun m => hH g m) hpq).trans ?_
      have hs1 : (∑ m ∈ F, ‖star (f m)‖ ^ p) = ∑ m ∈ F, ‖f m‖ ^ p :=
        Finset.sum_congr rfl (fun m _ => by rw [norm_star])
      have hs2 : (∑ m ∈ F, ‖hH g m‖ ^ q) ≤ ∑' n : ℤ, ‖hH g n‖ ^ q :=
        Summable.sum_le_tsum F (fun n _ => Real.rpow_nonneg (norm_nonneg _) _) hgsum_q.1
      rw [hs1]
      exact mul_le_mul hNfF
        (Real.rpow_le_rpow
          (Finset.sum_nonneg (fun m _ => Real.rpow_nonneg (norm_nonneg _) _)) hs2 (by positivity))
        (Real.rpow_nonneg
          (Finset.sum_nonneg (fun m _ => Real.rpow_nonneg (norm_nonneg _) _)) _) hNfnn
    have hbd : ‖∑ m ∈ F, f m * star (hH g m)‖ ≤ Cq * Nf := by
      calc ‖∑ m ∈ F, f m * star (hH g m)‖
          ≤ Nf * (∑' n : ℤ, ‖hH g n‖ ^ q) ^ (1 / q) := hholder
        _ ≤ Nf * Cq := mul_le_mul_of_nonneg_left hgsum_q.2 hNfnn
        _ = Cq * Nf := by ring
    have hfin : eLpNorm hS (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal (Cq * Nf) :=
      le_trans hpair (by
        rw [← ofReal_norm, hint]
        exact ENNReal.ofReal_le_ofReal hbd)
    have h2 := (tsum_rpow_le_of_eLpNorm_le hp0 (mul_nonneg hCq.le hNfnn) hfin).2
    rw [show (∑' n : ℤ, ‖hS n‖ ^ p) = ∑ n ∈ Sfin, ‖hH f n‖ ^ p from by
      rw [tsum_eq_sum (s := Sfin) (fun n hn => by
        rw [show hS n = 0 from by
          change (if n ∈ Sfin then hH f n else 0) = 0
          rw [if_neg (by simpa using hn)], norm_zero, Real.zero_rpow hp0.ne'])]
      apply Finset.sum_congr rfl; intro n hn
      change ‖(if n ∈ Sfin then hH f n else 0)‖ ^ p = ‖hH f n‖ ^ p
      rw [if_pos hn]] at h2
    exact h2
  have key2 : ∀ s : Finset ℤ, ∑ n ∈ s, ‖hH f n‖ ^ p ≤ (Cq * Nf) ^ p := by
    intro s
    obtain ⟨N, hN⟩ := exists_finset_subset_Icc s
    have h1 : (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖hH f n‖ ^ p) ≤ (Cq * Nf) ^ p := by
      have h2 := key N
      have h3 := Real.rpow_le_rpow (Real.rpow_nonneg
          (Finset.sum_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) _)) _) h2 (le_of_lt hp0)
      rwa [rpow_inv_self (Finset.sum_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) _))
        hp0.ne'] at h3
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hN
      (fun _ _ _ => Real.rpow_nonneg (norm_nonneg _) _)) h1
  have hsumH : Summable (fun n : ℤ => ‖hH f n‖ ^ p) :=
    summable_of_sum_le (fun n => Real.rpow_nonneg (norm_nonneg _) _) key2
  have hle : (∑' n : ℤ, ‖hH f n‖ ^ p) ^ (1 / p) ≤ Cq * Nf := by
    have h1 : (∑' n : ℤ, ‖hH f n‖ ^ p) ≤ (Cq * Nf) ^ p :=
      Real.tsum_le_of_sum_le (fun n => Real.rpow_nonneg (norm_nonneg _) _) key2
    calc (∑' n : ℤ, ‖hH f n‖ ^ p) ^ (1 / p)
        ≤ ((Cq * Nf) ^ p) ^ (1 / p) :=
          Real.rpow_le_rpow (tsum_nonneg fun n => Real.rpow_nonneg (norm_nonneg _) _) h1
            (by positivity)
      _ = Cq * Nf := by
          rw [← Real.rpow_mul (mul_nonneg hCq.le hNfnn) p (1 / p),
            show p * (1 / p) = 1 by field_simp, Real.rpow_one]
  rw [hef, ← ENNReal.ofReal_mul hCq.le]
  exact eLpNorm_le_ofReal_of_tsum_rpow_le hp0 hsumH hle


/-! ### Converting an `eLpNorm` bound into the `ℓᵖ`-sum bound -/

lemma hilbert_of_eLpNorm_bound {p : ℝ} (hp : 0 < p) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ f : ℤ → ℂ, eLpNorm (hH f) (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ)) :
    ∀ f : ℤ → ℂ, Summable (fun n : ℤ => ‖f n‖ ^ p) →
      Summable (fun n : ℤ => ‖hH f n‖ ^ p) ∧
      (∑' n : ℤ, ‖hH f n‖ ^ p) ^ (1 / p) ≤ C * (∑' n : ℤ, ‖f n‖ ^ p) ^ (1 / p) := by
  intro f hf
  have hNf : eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ)
      = ENNReal.ofReal ((∑' n : ℤ, ‖f n‖ ^ p) ^ (1 / p)) :=
    eLpNorm_count_eq_ofReal f hp hf
  have h1 : eLpNorm (hH f) (ENNReal.ofReal p) (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (C * (∑' n : ℤ, ‖f n‖ ^ p) ^ (1 / p)) := by
    calc eLpNorm (hH f) (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) := hbound f
      _ = ENNReal.ofReal C * ENNReal.ofReal ((∑' n : ℤ, ‖f n‖ ^ p) ^ (1 / p)) := by rw [hNf]
      _ = ENNReal.ofReal (C * (∑' n : ℤ, ‖f n‖ ^ p) ^ (1 / p)) :=
          (ENNReal.ofReal_mul hC).symm
  exact tsum_rpow_le_of_eLpNorm_le hp
    (mul_nonneg hC (Real.rpow_nonneg
      (tsum_nonneg fun n => Real.rpow_nonneg (norm_nonneg _) _) _)) h1

end

end Commons.Analysis.Hilbert
