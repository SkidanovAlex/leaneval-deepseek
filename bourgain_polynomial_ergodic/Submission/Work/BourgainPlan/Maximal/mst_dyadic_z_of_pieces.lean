import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.subtwo_of_dyadic_z
import Submission.Work.BourgainPlan.Maximal.mst_minor_per_n
import Submission.Work.BourgainPlan.Maximal.eLpNorm_varRhoAll_le_geometric
import Submission.Work.BourgainPlan.Maximal.minor_arc_lp_bound
import Submission.Work.BourgainPlan.IonescuWainger.opArc_strata_incl_excl
import Submission.Work.BourgainPlan.Maximal.opMul_sub

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped ENNReal BigOperators

open Work.BourgainPlan.IonescuWainger

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-! ## Elementary endgame lemmas for the `eLpNorm` assembly

The `eLpNorm` of a `ℝ≥0∞`-valued function is `(∫⁻ ‖f‖ₑ^p)^{1/p}`, and for such functions the
exponential and the integral are freely interchangeable.  We record the two conversions used, the
countable Minkowski inequality for such functions, and the two sup/sum splitting lemmas. -/

/-- `eLpNorm` raised to the exponent is the defining `lintegral`, for `ℝ≥0∞`-valued functions. -/
theorem eLpNorm_ennreal_rpow_eq (p : ℝ) (hp : 0 < p) (F : ℤ → ENNReal) :
    (eLpNorm F (ENNReal.ofReal p) Measure.count) ^ p
      = ∫⁻ m : ℤ, F m ^ p ∂Measure.count := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete,
    ENNReal.toReal_ofReal hp.le]
  simp only [enorm_eq_self]
  rw [← ENNReal.rpow_mul, show (1 / p) * p = 1 by field_simp, ENNReal.rpow_one]

/-- Monotonicity of `eLpNorm` for `ℝ≥0∞`-valued functions, in the pointwise form. -/
theorem eLpNorm_mono_ennreal {q : ℝ≥0∞} {f g : ℤ → ENNReal} (h : f ≤ g) :
    eLpNorm f q Measure.count ≤ eLpNorm g q Measure.count :=
  eLpNorm_mono_enorm AEStronglyMeasurable.of_discrete
    (fun x => by simpa only [enorm_eq_self] using h x)

/-- **Countable Minkowski** for `ℝ≥0∞`-valued functions on `ℤ`: the `ℓᵖ` norm of a pointwise `tsum`
is at most the `tsum` of the `ℓᵖ` norms. -/
theorem eLpNorm_tsum_le_tsum_eLpNorm' {p : ℝ} (hp : 1 ≤ p) (f : ℕ → ℤ → ENNReal) :
    eLpNorm (fun m : ℤ => ∑' n : ℕ, f n m) (ENNReal.ofReal p) Measure.count
      ≤ ∑' n : ℕ, eLpNorm (f n) (ENNReal.ofReal p) Measure.count :=
  eLpNorm_tsum_le_tsum_eLpNorm (ENNReal.one_le_ofReal.mpr hp) ENNReal.ofReal_ne_top
    (fun n => measurable_of_int _)

/-- **Minkowski for a finite pointwise sum** of `ℝ≥0∞`-valued functions on `ℤ`. -/
theorem eLpNorm_finset_sum_le' {ι : Type*} {p : ℝ} (hp : 1 ≤ p) (s : Finset ι)
    (f : ι → ℤ → ENNReal) :
    eLpNorm (∑ i ∈ s, f i) (ENNReal.ofReal p) Measure.count
      ≤ ∑ i ∈ s, eLpNorm (f i) (ENNReal.ofReal p) Measure.count :=
  eLpNorm_sum_le (ENNReal.one_le_ofReal.mpr hp)

/-- **The `sup` over a scale family is dominated by the `tsum` of the norms.** -/
theorem eLpNorm_iSup_le_tsum {p : ℝ} (hp : 1 ≤ p) (f : ℕ → ℤ → ENNReal) :
    eLpNorm (fun m : ℤ => ⨆ n : ℕ, f n m) (ENNReal.ofReal p) Measure.count
      ≤ ∑' n : ℕ, eLpNorm (f n) (ENNReal.ofReal p) Measure.count := by
  refine (eLpNorm_mono_ennreal (fun m => ?_)).trans (eLpNorm_tsum_le_tsum_eLpNorm' hp f)
  exact iSup_le fun n => ENNReal.le_tsum (f := fun n => f n m) n

/-- **Splitting the `sup` at the threshold `K₀`.**  The supremum over all scales is dominated by the
finite head `k < K₀` (kept as the sum of the norms, since only the small-scale contraction is
available) plus the supremum over the tail `k = n + K₀`. -/
theorem eLpNorm_iSup_le_sum_range_add_iSup {p : ℝ} (hp : 1 ≤ p) (K₀ : ℕ) (f : ℕ → ℤ → ENNReal) :
    eLpNorm (fun m : ℤ => ⨆ k : ℕ, f k m) (ENNReal.ofReal p) Measure.count
      ≤ (∑ k ∈ Finset.range K₀, eLpNorm (f k) (ENNReal.ofReal p) Measure.count)
        + eLpNorm (fun m : ℤ => ⨆ n : ℕ, f (n + K₀) m) (ENNReal.ofReal p) Measure.count := by
  have hp1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hpt : (fun m : ℤ => ⨆ k : ℕ, f k m)
      ≤ (∑ k ∈ Finset.range K₀, f k) + (fun m : ℤ => ⨆ n : ℕ, f (n + K₀) m) := by
    intro m
    simp only [Pi.add_apply, Finset.sum_apply]
    refine iSup_le fun k => ?_
    rcases lt_or_ge k K₀ with hk | hk
    · refine le_trans (Finset.single_le_sum (f := fun i => f i m) (fun i _ => bot_le)
          (Finset.mem_range.mpr hk)) ?_
      exact le_self_add
    · obtain ⟨n, rfl⟩ : ∃ n, k = n + K₀ := ⟨k - K₀, (Nat.sub_add_cancel hk).symm⟩
      exact le_trans (le_iSup (fun n : ℕ => f (n + K₀) m) n) le_add_self
  calc eLpNorm (fun m : ℤ => ⨆ k : ℕ, f k m) (ENNReal.ofReal p) Measure.count
      ≤ eLpNorm ((∑ k ∈ Finset.range K₀, f k)
          + (fun m : ℤ => ⨆ n : ℕ, f (n + K₀) m)) (ENNReal.ofReal p) Measure.count :=
        eLpNorm_mono_ennreal hpt
    _ ≤ eLpNorm (∑ k ∈ Finset.range K₀, f k) (ENNReal.ofReal p) Measure.count
          + eLpNorm (fun m : ℤ => ⨆ n : ℕ, f (n + K₀) m) (ENNReal.ofReal p) Measure.count :=
        eLpNorm_add_le hp1e
    _ ≤ (∑ k ∈ Finset.range K₀, eLpNorm (f k) (ENNReal.ofReal p) Measure.count)
          + eLpNorm (fun m : ℤ => ⨆ n : ℕ, f (n + K₀) m) (ENNReal.ofReal p) Measure.count :=
        add_le_add (eLpNorm_finset_sum_le' hp (Finset.range K₀) f) le_rfl

/-- **The tail `sup` of the level sums is dominated by the `tsum` of the level sups.** -/
theorem eLpNorm_iSup_sum_range_le_tsum_iSup {p : ℝ} (hp : 1 ≤ p) (K₀ : ℕ)
    (c : ℕ → ℕ → ℤ → ENNReal) :
    eLpNorm (fun m : ℤ => ⨆ n : ℕ, ∑ s ∈ Finset.range (n + K₀), c (n + K₀) s m)
        (ENNReal.ofReal p) Measure.count
      ≤ ∑' s : ℕ, eLpNorm (fun m : ℤ => ⨆ k : ℕ, ⨆ (_ : s < k), c k s m)
        (ENNReal.ofReal p) Measure.count := by
  have hp1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hpt : (fun m : ℤ => ⨆ n : ℕ, ∑ s ∈ Finset.range (n + K₀), c (n + K₀) s m)
      ≤ (fun m : ℤ => ∑' s : ℕ, (⨆ k : ℕ, ⨆ (_ : s < k), c k s m)) := by
    intro m
    simp only
    refine iSup_le fun n => ?_
    refine le_trans (Finset.sum_le_sum (fun s hs => ?_)) (ENNReal.sum_le_tsum _)
    have hs' : s < n + K₀ := Finset.mem_range.mp hs
    exact le_trans (le_iSup (fun _ : s < n + K₀ => c (n + K₀) s m) hs')
      (le_iSup (fun k : ℕ => ⨆ (_ : s < k), c k s m) (n + K₀))
  calc eLpNorm (fun m : ℤ => ⨆ n : ℕ, ∑ s ∈ Finset.range (n + K₀), c (n + K₀) s m)
        (ENNReal.ofReal p) Measure.count
      ≤ eLpNorm (fun m : ℤ => ∑' s : ℕ, (⨆ k : ℕ, ⨆ (_ : s < k), c k s m))
          (ENNReal.ofReal p) Measure.count := eLpNorm_mono_ennreal hpt
    _ ≤ ∑' s : ℕ, eLpNorm (fun m : ℤ => ⨆ k : ℕ, ⨆ (_ : s < k), c k s m)
          (ENNReal.ofReal p) Measure.count :=
        eLpNorm_tsum_le_tsum_eLpNorm' hp _

/-- Summability of `n ↦ ((n:ℝ) + m + 1)^{-2}` (a shifted `p`-series with `p = 2`). -/
theorem summable_shift_inv_sq (m : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + m + 1) ^ (-2 : ℝ)) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := by
    have h := (Real.summable_nat_rpow_inv (p := 2)).mpr (by norm_num : (1 : ℝ) < 2)
    refine h.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two, inv_eq_one_div]
  have hshift := (summable_nat_add_iff (m + 1)).mpr hbase
  refine hshift.congr fun n => ?_
  push_cast
  ring_nf

/-- Summability of the geometric-exponential sum `n ↦ 2^{-(c((n:ℝ)+m))}` for `c > 0`. -/
theorem summable_two_rpow_neg (c : ℝ) (hc : 0 < c) (m : ℕ) :
    Summable (fun n : ℕ => (2 : ℝ) ^ (-(c * ((n : ℝ) + m)))) := by
  have hr1 : (2 : ℝ) ^ (-c) < 1 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hc)
  have hgeo : Summable (fun n : ℕ => ((2 : ℝ) ^ (-c)) ^ n) :=
    summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _) hr1
  have h1 : Summable (fun n : ℕ => (2 : ℝ) ^ (-(c * (m : ℝ))) * ((2 : ℝ) ^ (-c)) ^ n) :=
    hgeo.mul_left _
  refine h1.congr fun n => ?_
  rw [show -(c * ((n : ℝ) + m)) = -(c * (m : ℝ)) + (-c) * (n : ℝ) by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

/-- The coefficient `((2:ℝ)^k)^{-1}` viewed in `ℂ` is the inverse of the natural number `2^k`. -/
theorem coeff_eq (k : ℕ) : ((((2 : ℝ) ^ k)⁻¹ : ℝ) : ℂ) = ((2 ^ k : ℕ) : ℂ)⁻¹ := by
  rw [Complex.ofReal_inv, Complex.ofReal_pow, Nat.cast_pow]
  norm_num

/-- The raw form of the dyadic average is `discAvgZC` at `N = 2^k`. -/
theorem raw_eq (P : Polynomial ℤ) (k : ℕ) (g : ℤ → ℂ) (m : ℤ) :
    ((2 : ℝ) ^ k)⁻¹ * ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))
      = discAvgZC P (2 ^ k) g m := by
  unfold discAvgZC
  congr 1
  rw [coeff_eq k]

/-- `‖a + b + c + d‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ + ‖d‖ₑ`. -/
theorem enorm_add_four (a b c d : ℂ) :
    ‖a + b + c + d‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ + ‖d‖ₑ := by
  calc ‖a + b + c + d‖ₑ ≤ ‖a + b + c‖ₑ + ‖d‖ₑ := enorm_add_le _ _
    _ ≤ (‖a + b‖ₑ + ‖c‖ₑ) + ‖d‖ₑ := add_le_add (enorm_add_le _ _) le_rfl
    _ ≤ ((‖a‖ₑ + ‖b‖ₑ) + ‖c‖ₑ) + ‖d‖ₑ :=
        add_le_add (add_le_add (enorm_add_le _ _) le_rfl) le_rfl
    _ = ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ + ‖d‖ₑ := rfl

/-- **The decomposition of the dyadic average** at a single scale `k`: the minor-arc operator, the
first major-arc error, the second major-arc error, and the level pieces `s < k`. -/
theorem mst_discAvgZC_decomp (P : Polynomial ℤ) (l : ℕ) {χ : ℝ} (η : ℝ → ℂ) (k : ℕ)
    (hηk : MemLp (mstEta P.natDegree χ η k) ⊤ haarT)
    (hνmlk : MemLp (mstNu P l P.natDegree χ η k) ⊤ haarT)
    (hνsmlk : ∀ s : ℕ, MemLp (mstNuS P l P.natDegree χ η k s) ⊤ haarT)
    (g : ℤ →₀ ℂ) :
    discAvgZC P (2 ^ k) (⇑g)
      = mstMinorOp P l P.natDegree χ η k hηk (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)
        + opMul (mstMajErr1Cls P l P.natDegree χ η k hηk hνmlk) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)
        + opMul (mstMajErr2Cls P l P.natDegree χ η k hνmlk hνsmlk) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)
        + ∑ s ∈ Finset.range k, opMul (mstNuSCls P l P.natDegree χ η k s (hνsmlk s)) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) := by
  have hA : discAvgZC P (2 ^ k) (⇑g)
      = mstMinorOp P l P.natDegree χ η k hηk (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)
        + opMul (mstProjCls P l P.natDegree χ η k hηk) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) := by
    rw [mstMinorOp_eq, discAvgZC_opArc_eq_opMul_smul]
    unfold mstProjCls
    abel
  rw [hA]
  have hsplit1 : mstProjCls P l P.natDegree χ η k hηk
      = mstNuCls P l P.natDegree χ η k hνmlk
        + mstMajErr1Cls P l P.natDegree χ η k hηk hνmlk := by
    unfold mstMajErr1Cls; abel
  rw [hsplit1, opMul_add]
  have hsplit2 : mstNuCls P l P.natDegree χ η k hνmlk
      = mstNuSumCls P l P.natDegree χ η k hνsmlk
        + mstMajErr2Cls P l P.natDegree χ η k hνmlk hνsmlk := by
    unfold mstMajErr2Cls; abel
  rw [hsplit2, opMul_add]
  rw [mstNuSumCls]
  rw [show (∑ s ∈ Finset.range k, (hνsmlk s).toLp (mstNuS P l P.natDegree χ η k s))
      = ∑ s ∈ Finset.range k,
          (1 : ℂ) • (hνsmlk s).toLp (mstNuS P l P.natDegree χ η k s) by simp]
  rw [opMul_finset_sum]
  simp only [one_smul, mstNuSCls]
  abel


/-- MST §6 (Mirek-Stein-Trojan, arXiv:1512.07518, §4, final assembly): the dyadic `ℤ`-form `DyadicZStatement P p` for every `p ∈ (1,2)`, from the four families of per-scale estimates, for a fixed parameter set `(l, χ, η)` and threshold `K₀`.  This is the last step before `subtwo_of_dyadic_z`.

The four hypotheses (all in `eLpNorm`-form at the exponent `p`, for finitely supported `g : ℤ →₀ ℂ`):
* `hminor`: the minor-arc per-scale bound (§4.1, output of `mst_minor_per_n`) with gain `(k+1)^{−2}` for `k ≥ K₀`;
* `herr1`: the first major-arc error `m_{2^k}Ξ_k − ν_{2^k}` with gain `2^{−c₁k}` (§4.2 eq. (73));
* `herr2`: the second major-arc error `ν_{2^k} − Σ_{s<k}ν^s_{2^k}` with gain `2^{−c₂k}` (§4.2 eq. (80));
* `hlevel`: the level estimate (L) = eq. (81), the supremum over the levels `k > s`, with gain `(s+1)^{−2}`.

Route: for `k ≥ K₀` the pointwise identity `discAvgZC P (2^k) g = mstMinorOp k g + opMul (mstMajErr1Cls k) g + opMul (mstMajErr2Cls k) g + Σ_{s<k} opMul (mstNuSCls k s) g` holds (`mstMinorOp_eq`, `discAvgZC_opArc_eq_opMul_smul`, the definitions of the error classes, additivity of `opMul` in the class); hence `sup_k‖A_{2^k}g‖` is dominated by the finite small-scale sum plus the four series, whose `ℓᵖ` norms are the hypotheses and the geometric series `Σ_k(k+1)^{−2}`, `Σ_k 2^{−ck}`, `Σ_s(s+1)^{−2}`; the small-scale part is bounded by the `ℓᵖ` contraction of the averages (`discAvgZC_lp_contraction`).  Minkowski for `eLpNorm` at `p ≥ 1` plus the `eLpNorm`/`∫⁻‖·‖ₑ^p` conversions finish. -/
theorem mst_dyadic_z_of_pieces (P : Polynomial ℤ) (hP : Submission.BourgainPlan.NonnegOnNat P)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (hη : ∀ n : ℕ, MeasureTheory.MemLp (mstEta P.natDegree χ η n) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hνml : ∀ n : ℕ, MeasureTheory.MemLp (mstNu P l P.natDegree χ η n) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp (mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (K₀ : ℕ) (Cminor : ℝ) (hCminor : 0 < Cminor)
    (hminor : ∀ k : ℕ, K₀ ≤ k → ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => mstMinorOp P l P.natDegree χ η k (hη k) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m)
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Cminor * ((k : ℝ) + 1) ^ (-2 : ℝ))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count)
    (C₁ c₁ : ℝ) (hC₁ : 0 < C₁) (hc₁ : 0 < c₁)
    (herr1 : ∀ k : ℕ, K₀ ≤ k → ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
          (mstMajErr1Cls P l P.natDegree χ η k (hη k) (hνml k)) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C₁ * (2 : ℝ) ^ (-(c₁ * (k : ℝ))))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count)
    (C₂ c₂ : ℝ) (hC₂ : 0 < C₂) (hc₂ : 0 < c₂)
    (herr2 : ∀ k : ℕ, K₀ ≤ k → ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
          (mstMajErr2Cls P l P.natDegree χ η k (hνml k) (hνsml k)) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C₂ * (2 : ℝ) ^ (-(c₂ * (k : ℝ))))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count)
    (C₃ : ℝ) (hC₃ : 0 < C₃)
    (hlevel : ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ (k : ℕ) (_ : s < k),
          ‖Work.BourgainPlan.IonescuWainger.opMul
            (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C₃ * ((s : ℝ) + 1) ^ (-2 : ℝ))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count) :
    DyadicZStatement P p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  set q : ℝ≥0∞ := ENNReal.ofReal p with hqdef
  have hq1 : 1 ≤ q := by rw [hqdef]; exact ENNReal.one_le_ofReal.mpr hp1.le
  have hs0 : Summable (fun n : ℕ => ((n : ℝ) + K₀ + 1) ^ (-2 : ℝ)) := summable_shift_inv_sq K₀
  have hs1 : Summable (fun n : ℕ => (2 : ℝ) ^ (-(c₁ * ((n : ℝ) + K₀)))) :=
    summable_two_rpow_neg c₁ hc₁ K₀
  have hs2 : Summable (fun n : ℕ => (2 : ℝ) ^ (-(c₂ * ((n : ℝ) + K₀)))) :=
    summable_two_rpow_neg c₂ hc₂ K₀
  have hs3 : Summable (fun s : ℕ => ((s : ℝ) + 1) ^ (-2 : ℝ)) := by
    simpa using summable_shift_inv_sq 0
  set S₀ : ℝ := ∑' n : ℕ, ((n : ℝ) + K₀ + 1) ^ (-2 : ℝ) with hS₀
  set S₁ : ℝ := ∑' n : ℕ, (2 : ℝ) ^ (-(c₁ * ((n : ℝ) + K₀))) with hS₁
  set S₂ : ℝ := ∑' n : ℕ, (2 : ℝ) ^ (-(c₂ * ((n : ℝ) + K₀))) with hS₂
  set S₃ : ℝ := ∑' s : ℕ, ((s : ℝ) + 1) ^ (-2 : ℝ) with hS₃
  have hS₀nn : 0 ≤ S₀ := by
    rw [hS₀]; exact tsum_nonneg (fun n => Real.rpow_nonneg (by positivity) _)
  have hS₁nn : 0 ≤ S₁ := by
    rw [hS₁]; exact tsum_nonneg (fun n => Real.rpow_nonneg (by norm_num) _)
  have hS₂nn : 0 ≤ S₂ := by
    rw [hS₂]; exact tsum_nonneg (fun n => Real.rpow_nonneg (by norm_num) _)
  have hS₃nn : 0 ≤ S₃ := by
    rw [hS₃]; exact tsum_nonneg (fun n => Real.rpow_nonneg (by positivity) _)
  have hCS0 : 0 ≤ Cminor * S₀ := mul_nonneg hCminor.le hS₀nn
  have hCS1 : 0 ≤ C₁ * S₁ := mul_nonneg hC₁.le hS₁nn
  have hCS2 : 0 ≤ C₂ * S₂ := mul_nonneg hC₂.le hS₂nn
  have hCS3 : 0 ≤ C₃ * S₃ := mul_nonneg hC₃.le hS₃nn
  set C : ℝ := (K₀ : ℝ) + Cminor * S₀ + C₁ * S₁ + C₂ * S₂ + C₃ * S₃ with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]; linarith [hCS0, hCS1, hCS2, hCS3]
  refine ⟨C, hCnn, ?_⟩
  intro g hg
  obtain ⟨s, hs⟩ := hg
  have hfin : (Function.support g).Finite := by
    refine (s.finite_toSet).subset ?_
    intro n hn
    by_contra hns
    exact hn (hs n hns)
  set g₀ : ℤ →₀ ℂ := Finsupp.ofSupportFinite g hfin with hg₀
  have hg₀coe : (⇑g₀ : ℤ → ℂ) = g := by rw [hg₀]; exact Finsupp.ofSupportFinite_coe
  set A : ℕ → ℤ → ENNReal := fun k m => ‖discAvgZC P (2 ^ k) (⇑g₀) m‖ₑ with hAdef
  set B : ℕ → ℤ → ENNReal := fun k m =>
    ‖mstMinorOp P l P.natDegree χ η k (hη k) (⇑g₀)
      (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g₀) m‖ₑ with hBdef
  set E1 : ℕ → ℤ → ENNReal := fun k m =>
    ‖opMul (mstMajErr1Cls P l P.natDegree χ η k (hη k) (hνml k)) (⇑g₀)
      (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g₀) m‖ₑ with hE1def
  set E2 : ℕ → ℤ → ENNReal := fun k m =>
    ‖opMul (mstMajErr2Cls P l P.natDegree χ η k (hνml k) (hνsml k)) (⇑g₀)
      (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g₀) m‖ₑ with hE2def
  set SS : ℕ → ℤ → ENNReal := fun k m =>
    ∑ s ∈ Finset.range k, ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g₀)
      (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g₀) m‖ₑ with hSSdef
  set LL : ℕ → ℤ → ENNReal := fun s m =>
    ⨆ (k : ℕ) (_ : s < k), ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g₀)
      (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g₀) m‖ₑ with hLLdef
  set X : ENNReal := eLpNorm (⇑g₀) q Measure.count with hXdef
  have hA_le : ∀ k : ℕ, eLpNorm (A k) q Measure.count ≤ X := by
    intro k
    simp only [hAdef, hXdef]
    rw [eLpNorm_enorm _ AEStronglyMeasurable.of_discrete]
    exact eLpNorm_discAvgZC_le P (2 ^ k) hp1.le (⇑g₀)
  have hsmall : (∑ k ∈ Finset.range K₀, eLpNorm (A k) q Measure.count)
      ≤ ENNReal.ofReal (K₀ : ℝ) * X := by
    calc ∑ k ∈ Finset.range K₀, eLpNorm (A k) q Measure.count
        ≤ ∑ _k ∈ Finset.range K₀, X := Finset.sum_le_sum (fun k _ => hA_le k)
      _ = (K₀ : ℝ≥0∞) * X := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ENNReal.ofReal (K₀ : ℝ) * X := by rw [ENNReal.ofReal_natCast]
  have hdec : ∀ n : ℕ, ∀ m : ℤ,
      A (n + K₀) m ≤ B (n + K₀) m + E1 (n + K₀) m + E2 (n + K₀) m + SS (n + K₀) m := by
    intro n m
    have hdc := mst_discAvgZC_decomp P l η (n + K₀) (hη (n + K₀)) (hνml (n + K₀))
      (hνsml (n + K₀)) g₀
    simp only [hAdef, hBdef, hE1def, hE2def, hSSdef]
    rw [congrFun hdc m]
    simp only [Pi.add_apply, Finset.sum_apply]
    refine le_trans (enorm_add_four _ _ _ _) ?_
    refine add_le_add (add_le_add (add_le_add le_rfl le_rfl) le_rfl) ?_
    exact enorm_sum_le _ _
  have hstep2 : (fun m : ℤ => ⨆ n : ℕ, A (n + K₀) m)
      ≤ (fun m : ℤ => ⨆ n : ℕ, B (n + K₀) m) + (fun m : ℤ => ⨆ n : ℕ, E1 (n + K₀) m)
        + (fun m : ℤ => ⨆ n : ℕ, E2 (n + K₀) m) + (fun m : ℤ => ⨆ n : ℕ, SS (n + K₀) m) := by
    intro m
    simp only [Pi.add_apply]
    refine iSup_le fun n => ?_
    refine le_trans (hdec n m) ?_
    exact add_le_add (add_le_add (add_le_add (le_iSup (fun n : ℕ => B (n + K₀) m) n)
      (le_iSup (fun n : ℕ => E1 (n + K₀) m) n))
      (le_iSup (fun n : ℕ => E2 (n + K₀) m) n)) (le_iSup (fun n : ℕ => SS (n + K₀) m) n)
  have hB_le : eLpNorm (fun m : ℤ => ⨆ n : ℕ, B (n + K₀) m) q Measure.count
      ≤ ENNReal.ofReal (Cminor * S₀) * X := by
    refine (eLpNorm_iSup_le_tsum (p := p) hp1.le (fun n => B (n + K₀))).trans ?_
    have hbd : ∀ n : ℕ, eLpNorm (B (n + K₀)) q Measure.count
        ≤ ENNReal.ofReal (Cminor * ((n : ℝ) + K₀ + 1) ^ (-2 : ℝ)) * X := by
      intro n
      have hb := hminor (n + K₀) (Nat.le_add_left K₀ n) g₀
      have hcast : (((n + K₀ : ℕ) : ℝ) + 1) = (n : ℝ) + K₀ + 1 := by push_cast; ring
      simp only [hBdef, hXdef]
      rw [eLpNorm_enorm _ AEStronglyMeasurable.of_discrete]
      refine le_trans hb ?_
      rw [hcast]
    calc ∑' n : ℕ, eLpNorm (B (n + K₀)) q Measure.count
        ≤ ∑' n : ℕ, ENNReal.ofReal (Cminor * ((n : ℝ) + K₀ + 1) ^ (-2 : ℝ)) * X :=
          ENNReal.tsum_le_tsum hbd
      _ = (∑' n : ℕ, ENNReal.ofReal (Cminor * ((n : ℝ) + K₀ + 1) ^ (-2 : ℝ))) * X :=
          ENNReal.tsum_mul_right
      _ = ENNReal.ofReal (Cminor * S₀) * X := by
          congr 1
          rw [hS₀, ← tsum_mul_left,
            ENNReal.ofReal_tsum_of_nonneg
              (fun n => mul_nonneg hCminor.le (Real.rpow_nonneg (by positivity) _))
              (hs0.mul_left Cminor)]
  have hE1_le : eLpNorm (fun m : ℤ => ⨆ n : ℕ, E1 (n + K₀) m) q Measure.count
      ≤ ENNReal.ofReal (C₁ * S₁) * X := by
    refine (eLpNorm_iSup_le_tsum (p := p) hp1.le (fun n => E1 (n + K₀))).trans ?_
    have hbd : ∀ n : ℕ, eLpNorm (E1 (n + K₀)) q Measure.count
        ≤ ENNReal.ofReal (C₁ * (2 : ℝ) ^ (-(c₁ * ((n : ℝ) + K₀)))) * X := by
      intro n
      have hb := herr1 (n + K₀) (Nat.le_add_left K₀ n) g₀
      have hcast : (((n + K₀ : ℕ) : ℝ)) = (n : ℝ) + K₀ := by push_cast; ring
      simp only [hE1def, hXdef]
      rw [eLpNorm_enorm _ AEStronglyMeasurable.of_discrete]
      refine le_trans hb ?_
      rw [hcast]
    calc ∑' n : ℕ, eLpNorm (E1 (n + K₀)) q Measure.count
        ≤ ∑' n : ℕ, ENNReal.ofReal (C₁ * (2 : ℝ) ^ (-(c₁ * ((n : ℝ) + K₀)))) * X :=
          ENNReal.tsum_le_tsum hbd
      _ = (∑' n : ℕ, ENNReal.ofReal (C₁ * (2 : ℝ) ^ (-(c₁ * ((n : ℝ) + K₀))))) * X :=
          ENNReal.tsum_mul_right
      _ = ENNReal.ofReal (C₁ * S₁) * X := by
          congr 1
          rw [hS₁, ← tsum_mul_left,
            ENNReal.ofReal_tsum_of_nonneg
              (fun n => mul_nonneg hC₁.le (Real.rpow_nonneg (by norm_num) _))
              (hs1.mul_left C₁)]
  have hE2_le : eLpNorm (fun m : ℤ => ⨆ n : ℕ, E2 (n + K₀) m) q Measure.count
      ≤ ENNReal.ofReal (C₂ * S₂) * X := by
    refine (eLpNorm_iSup_le_tsum (p := p) hp1.le (fun n => E2 (n + K₀))).trans ?_
    have hbd : ∀ n : ℕ, eLpNorm (E2 (n + K₀)) q Measure.count
        ≤ ENNReal.ofReal (C₂ * (2 : ℝ) ^ (-(c₂ * ((n : ℝ) + K₀)))) * X := by
      intro n
      have hb := herr2 (n + K₀) (Nat.le_add_left K₀ n) g₀
      have hcast : (((n + K₀ : ℕ) : ℝ)) = (n : ℝ) + K₀ := by push_cast; ring
      simp only [hE2def, hXdef]
      rw [eLpNorm_enorm _ AEStronglyMeasurable.of_discrete]
      refine le_trans hb ?_
      rw [hcast]
    calc ∑' n : ℕ, eLpNorm (E2 (n + K₀)) q Measure.count
        ≤ ∑' n : ℕ, ENNReal.ofReal (C₂ * (2 : ℝ) ^ (-(c₂ * ((n : ℝ) + K₀)))) * X :=
          ENNReal.tsum_le_tsum hbd
      _ = (∑' n : ℕ, ENNReal.ofReal (C₂ * (2 : ℝ) ^ (-(c₂ * ((n : ℝ) + K₀))))) * X :=
          ENNReal.tsum_mul_right
      _ = ENNReal.ofReal (C₂ * S₂) * X := by
          congr 1
          rw [hS₂, ← tsum_mul_left,
            ENNReal.ofReal_tsum_of_nonneg
              (fun n => mul_nonneg hC₂.le (Real.rpow_nonneg (by norm_num) _))
              (hs2.mul_left C₂)]
  have hSS_le : eLpNorm (fun m : ℤ => ⨆ n : ℕ, SS (n + K₀) m) q Measure.count
      ≤ ∑' s : ℕ, eLpNorm (LL s) q Measure.count := by
    have h := eLpNorm_iSup_sum_range_le_tsum_iSup (p := p) hp1.le K₀
      (fun k s m => ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g₀)
        (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g₀) m‖ₑ)
    simpa only [hSSdef, hLLdef] using h
  have hlev_le : (∑' s : ℕ, eLpNorm (LL s) q Measure.count) ≤ ENNReal.ofReal (C₃ * S₃) * X := by
    have hbd : ∀ s : ℕ, eLpNorm (LL s) q Measure.count
        ≤ ENNReal.ofReal (C₃ * ((s : ℝ) + 1) ^ (-2 : ℝ)) * X := by
      intro s
      have hb := hlevel s g₀
      simp only [hLLdef, hXdef]
      exact hb
    calc ∑' s : ℕ, eLpNorm (LL s) q Measure.count
        ≤ ∑' s : ℕ, ENNReal.ofReal (C₃ * ((s : ℝ) + 1) ^ (-2 : ℝ)) * X :=
          ENNReal.tsum_le_tsum hbd
      _ = (∑' s : ℕ, ENNReal.ofReal (C₃ * ((s : ℝ) + 1) ^ (-2 : ℝ))) * X :=
          ENNReal.tsum_mul_right
      _ = ENNReal.ofReal (C₃ * S₃) * X := by
          congr 1
          rw [hS₃, ← tsum_mul_left,
            ENNReal.ofReal_tsum_of_nonneg
              (fun s => mul_nonneg hC₃.le (Real.rpow_nonneg (by positivity) _))
              (hs3.mul_left C₃)]
  have hofsum : ENNReal.ofReal (Cminor * S₀) + ENNReal.ofReal (C₁ * S₁)
        + ENNReal.ofReal (C₂ * S₂) + ENNReal.ofReal (C₃ * S₃)
      = ENNReal.ofReal (Cminor * S₀ + C₁ * S₁ + C₂ * S₂ + C₃ * S₃) := by
    rw [← ENNReal.ofReal_add hCS0 hCS1,
      ← ENNReal.ofReal_add (add_nonneg hCS0 hCS1) hCS2,
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg hCS0 hCS1) hCS2) hCS3]
  have hlarge : eLpNorm (fun m : ℤ => ⨆ n : ℕ, A (n + K₀) m) q Measure.count
      ≤ ENNReal.ofReal (Cminor * S₀ + C₁ * S₁ + C₂ * S₂ + C₃ * S₃) * X := by
    calc eLpNorm (fun m : ℤ => ⨆ n : ℕ, A (n + K₀) m) q Measure.count
        ≤ eLpNorm ((fun m : ℤ => ⨆ n : ℕ, B (n + K₀) m)
            + (fun m : ℤ => ⨆ n : ℕ, E1 (n + K₀) m)
            + (fun m : ℤ => ⨆ n : ℕ, E2 (n + K₀) m)
            + (fun m : ℤ => ⨆ n : ℕ, SS (n + K₀) m)) q Measure.count :=
          eLpNorm_mono_ennreal hstep2
      _ ≤ eLpNorm (fun m : ℤ => ⨆ n : ℕ, B (n + K₀) m) q Measure.count
            + eLpNorm (fun m : ℤ => ⨆ n : ℕ, E1 (n + K₀) m) q Measure.count
            + eLpNorm (fun m : ℤ => ⨆ n : ℕ, E2 (n + K₀) m) q Measure.count
            + eLpNorm (fun m : ℤ => ⨆ n : ℕ, SS (n + K₀) m) q Measure.count := by
          refine le_trans (eLpNorm_add_le hq1) ?_
          refine le_trans (add_le_add (eLpNorm_add_le hq1) le_rfl) ?_
          refine le_trans (add_le_add (add_le_add (eLpNorm_add_le hq1) le_rfl) le_rfl) ?_
          rfl
      _ ≤ ENNReal.ofReal (Cminor * S₀) * X + ENNReal.ofReal (C₁ * S₁) * X
            + ENNReal.ofReal (C₂ * S₂) * X + ENNReal.ofReal (C₃ * S₃) * X :=
          add_le_add (add_le_add (add_le_add hB_le hE1_le) hE2_le) (hSS_le.trans hlev_le)
      _ = ENNReal.ofReal (Cminor * S₀ + C₁ * S₁ + C₂ * S₂ + C₃ * S₃) * X := by
          rw [← add_mul, ← add_mul, ← add_mul, hofsum]
  have hmain : eLpNorm (fun m : ℤ => ⨆ k : ℕ, A k m) q Measure.count ≤ ENNReal.ofReal C * X := by
    calc eLpNorm (fun m : ℤ => ⨆ k : ℕ, A k m) q Measure.count
        ≤ (∑ k ∈ Finset.range K₀, eLpNorm (A k) q Measure.count)
          + eLpNorm (fun m : ℤ => ⨆ n : ℕ, A (n + K₀) m) q Measure.count :=
          eLpNorm_iSup_le_sum_range_add_iSup (p := p) hp1.le K₀ A
      _ ≤ ENNReal.ofReal (K₀ : ℝ) * X
          + ENNReal.ofReal (Cminor * S₀ + C₁ * S₁ + C₂ * S₂ + C₃ * S₃) * X :=
          add_le_add hsmall hlarge
      _ = ENNReal.ofReal C * X := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by linarith [hCS0, hCS1, hCS2, hCS3])]
          have harg : (K₀ : ℝ) + (Cminor * S₀ + C₁ * S₁ + C₂ * S₂ + C₃ * S₃) = C := by
            rw [hCdef]; ring
          rw [harg]
  have hXeq : X = eLpNorm (fun m : ℤ => g m) q Measure.count := by
    rw [hXdef, hg₀coe]
  have hAeq : (fun m : ℤ => ⨆ k : ℕ, A k m)
      = (fun m : ℤ => ⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹
          * ∑ i ∈ Finset.range (2 ^ k), ⇑g₀ (m + P.eval (i : ℤ))‖ₑ) := by
    funext m
    refine iSup_congr (fun k => ?_)
    simp only [hAdef]
    rw [← raw_eq P k (⇑g₀) m]
  have hraw : (fun m : ℤ => ⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹
        * ∑ i ∈ Finset.range (2 ^ k), ⇑g₀ (m + P.eval (i : ℤ))‖ₑ)
      = (fun m : ℤ => ⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹
          * ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))‖ₑ) := by
    rw [hg₀coe]
  rw [hAeq, hXeq] at hmain
  rw [hraw] at hmain
  rw [← eLpNorm_ennreal_rpow_eq p hp0
        (fun m : ℤ => ⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹
          * ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))‖ₑ),
      ← eLpNorm_ennreal_rpow_eq p hp0 (fun m : ℤ => ‖g m‖ₑ)]
  rw [eLpNorm_enorm _ AEStronglyMeasurable.of_discrete]
  calc (eLpNorm (fun m : ℤ => ⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹
          * ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))‖ₑ) q Measure.count) ^ p
      ≤ (ENNReal.ofReal C * eLpNorm g q Measure.count) ^ p :=
        ENNReal.rpow_le_rpow hmain hp0.le
    _ = ENNReal.ofReal (C ^ p) * (eLpNorm g q Measure.count) ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.ofReal_rpow_of_nonneg hCnn hp0.le]

end

end Work.BourgainPlan.Maximal
