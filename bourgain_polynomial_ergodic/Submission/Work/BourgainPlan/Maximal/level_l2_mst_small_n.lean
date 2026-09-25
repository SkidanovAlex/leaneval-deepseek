import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_decay_sharp
import Submission.Work.BourgainPlan.Maximal.polyProfile_sub_one_le
import Submission.Work.BourgainPlan.Maximal.mstRademacherMenshov
import Submission.Work.BourgainPlan.Maximal.sigmaN_separated
import Submission.Work.BourgainPlan.Maximal.opMul_l2_bound
import Submission.Work.BourgainPlan.Maximal.rmELpNormSupLe
import Submission.Work.BourgainPlan.Maximal.eLpNorm_two_opMul_le
import Submission.Work.BourgainPlan.Maximal.memLp_scaled_bump
import Submission.Work.BourgainPlan.IonescuWainger.opArc_l2
import Submission.Work.IonescuWainger.memLp_count_two_iff
import Submission.Work.BourgainPlan.Maximal.polyProfile_lacunary_sum_le
import Submission.Work.BourgainPlan.Maximal.sum_tsum_norm_sq_opMul_le
import Submission.Work.BourgainPlan.Maximal.sum_block_sq_le
import Submission.Work.BourgainPlan.Maximal.mstEta_arcSum_le

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section


/-- The square of an `L²`-`eLpNorm` is the integral of the squared pointwise norm. -/
lemma eLpNorm_two_sq {ε : Type*} [TopologicalSpace ε] [ENorm ε] (g : ℤ → ε) :
    (MeasureTheory.eLpNorm g (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ 2
      = ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0:ℝ) < 2))) ENNReal.ofReal_ne_top
    AEStronglyMeasurable.of_discrete]
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2), one_div]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  rw [show (2 : ℝ)⁻¹ * ((2 : ℕ) : ℝ) = 1 from by norm_num, ENNReal.rpow_one]

/-- `x ^ (2 : ℝ) = x ^ 2` for real `x`. -/
lemma rpow_two_nat (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [Real.rpow_two, pow_two]

/-- `ℓ²`-membership in the Pi-type sense (`_root_.Memℓp`) is square-summability. -/
lemma summable_norm_sq_of_memℓp {f : ℤ → ℂ} (hf : Memℓp f 2) :
    Summable (fun m : ℤ => ‖f m‖ ^ 2) := by
  have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp hf
  simpa [Real.rpow_two] using h

/-- From a `lintegral` bound for the `q`-th powers to a bound on the `L^q`-norms, the
`ℝ≥0∞`-valued version (with a `ℂ`-valued majorant). -/
lemma eLpNorm_le_of_lintegral_rpow_le_enn {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    {u : ℤ → ℝ≥0∞} {v : ℤ → ℂ}
    (h : ∫⁻ m : ℤ, u m ^ q ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ q) * ∫⁻ m : ℤ, ‖v m‖ₑ ^ q ∂MeasureTheory.Measure.count) :
    MeasureTheory.eLpNorm u (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C
        * MeasureTheory.eLpNorm v (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  have hqne : ENNReal.ofReal q ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hq)
  have hL : (MeasureTheory.eLpNorm u (ENNReal.ofReal q) MeasureTheory.Measure.count) ^ q
      = ∫⁻ m : ℤ, u m ^ q ∂MeasureTheory.Measure.count := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hqne ENNReal.ofReal_ne_top
      AEStronglyMeasurable.of_discrete]
    simp only [enorm_eq_self]
    rw [ENNReal.toReal_ofReal hq.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne',
      ENNReal.rpow_one]
  have hR : (MeasureTheory.eLpNorm v (ENNReal.ofReal q) MeasureTheory.Measure.count) ^ q
      = ∫⁻ m : ℤ, ‖v m‖ₑ ^ q ∂MeasureTheory.Measure.count := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hqne ENNReal.ofReal_ne_top
      AEStronglyMeasurable.of_discrete]
    rw [ENNReal.toReal_ofReal hq.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne',
      ENNReal.rpow_one]
  rw [← hL, ← hR] at h
  rw [← ENNReal.ofReal_rpow_of_nonneg hC hq.le,
    ← ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal C)
      (MeasureTheory.eLpNorm v (ENNReal.ofReal q) MeasureTheory.Measure.count) hq.le] at h
  exact (ENNReal.rpow_le_rpow_iff hq).mp h

/-- The `q = 2` case, with the constant written as a natural square (so that it can be fed by
`sum_tsum_norm_sq_opMul_le`). -/
lemma eLpNorm_le_of_lintegral_sq_le {μ : ℝ} (hμ : 0 ≤ μ) {u : ℤ → ℝ≥0∞} {v : ℤ → ℂ}
    (h : ∫⁻ m : ℤ, u m ^ (2 : ℝ) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (μ ^ 2) * ∫⁻ m : ℤ, ‖v m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) :
    MeasureTheory.eLpNorm u (ENNReal.ofReal 2) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal μ
        * MeasureTheory.eLpNorm v (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
  refine eLpNorm_le_of_lintegral_rpow_le_enn (q := 2) (C := μ) (by norm_num) hμ ?_
  simpa only [rpow_two_nat μ] using h

/-- The elementary `ℝ≥0∞` arithmetic of the level estimate: `μr + 2(κ+1)μr ≤ 3(κ+1)μ r`. -/
lemma ofReal_level_arith (μ r : ℝ) (hμ : 0 ≤ μ) (hr : 0 ≤ r) (κ : ℕ) :
    ENNReal.ofReal μ * ENNReal.ofReal r
      + ENNReal.ofReal 2 * (ENNReal.ofReal ((κ:ℝ)+1) * (ENNReal.ofReal μ * ENNReal.ofReal r))
    ≤ ENNReal.ofReal (3 * ((κ:ℝ)+1) * μ) * ENNReal.ofReal r := by
  rw [← ENNReal.ofReal_mul hμ, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (κ:ℝ)+1),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ← ENNReal.ofReal_add (mul_nonneg hμ hr) (by positivity),
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 3 * ((κ:ℝ)+1) * μ)]
  apply ENNReal.ofReal_le_ofReal
  have hle : (1:ℝ) + 2 * ((κ:ℝ)+1) ≤ 3 * ((κ:ℝ)+1) := by
    have : (0:ℝ) ≤ (κ:ℝ) := Nat.cast_nonneg κ
    linarith
  have hmr : 0 ≤ μ * r := mul_nonneg hμ hr
  have h1 : μ * r + 2 * ((κ+1) * (μ*r)) = (μ*r) * (1 + 2 * ((κ:ℝ)+1)) := by ring
  have h2 : 3 * ((κ:ℝ)+1) * μ * r = (μ*r) * (3 * ((κ:ℝ)+1)) := by ring
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left hle hmr

/-- **The abstract Rademacher–Menshov level bound.** -/
theorem level_l2_of_symbol_bounds {κ : ℕ}
    (S : ℕ → MeasureTheory.Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) {μ : ℝ} (hμ : 0 ≤ μ)
    (h0 : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ‖(S 0 : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ≤ μ)
    (hΔ : ∀ i : ℕ, i ≤ κ → ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ∑ m' ∈ Finset.range (2 ^ (κ - i)),
        ‖(((S ((m' + 1) * 2 ^ i) - S (m' * 2 ^ i)) : MeasureTheory.Lp ℂ ⊤
            (AddCircle.haarAddCircle (T := 1))) : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2
        ≤ μ ^ 2)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    MeasureTheory.eLpNorm (fun m : ℤ => ⨆ n ∈ Finset.range (2 ^ κ + 1),
        ‖Work.BourgainPlan.IonescuWainger.opMul (S n) f hf m‖ₑ)
        (ENNReal.ofReal 2) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (3 * ((κ : ℝ) + 1) * μ)
        * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
  classical
  have hlev : ∀ i : ℕ, i ≤ κ →
      MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal
          (Real.sqrt (∑ m' ∈ Finset.range (2 ^ (κ - i)),
            ‖opMul ((S ((m' + 1) * 2 ^ i) - S (m' * 2 ^ i))) f hf m‖ ^ 2)))
        (ENNReal.ofReal 2) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal μ
        * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
    intro i hi
    refine eLpNorm_le_of_lintegral_sq_le hμ ?_
    have hsumm : ∀ m' : ℕ, Summable (fun m : ℤ =>
        ‖opMul ((S ((m' + 1) * 2 ^ i) - S (m' * 2 ^ i))) f hf m‖ ^ 2) :=
      fun m' => summable_norm_sq_of_memℓp (opMul_memℓp _ f hf)
    have hfs : Summable (fun m : ℤ => ‖f m‖ ^ 2) := summable_norm_sq_of_memℓp hf
    have hpt : ∀ m : ℤ, ENNReal.ofReal (Real.sqrt (∑ m' ∈ Finset.range (2 ^ (κ - i)),
            ‖opMul ((S ((m' + 1) * 2 ^ i) - S (m' * 2 ^ i))) f hf m‖ ^ 2)) ^ (2 : ℝ)
        = ∑ m' ∈ Finset.range (2 ^ (κ - i)),
            ENNReal.ofReal (‖opMul ((S ((m' + 1) * 2 ^ i) - S (m' * 2 ^ i))) f hf m‖ ^ 2) := by
      intro m
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_two, Real.sq_sqrt (Finset.sum_nonneg fun m' _ => sq_nonneg _),
        ENNReal.ofReal_sum_of_nonneg (fun m' _ => sq_nonneg _)]
    have hbudget : (∑ m' ∈ Finset.range (2 ^ (κ - i)), ∑' m : ℤ,
          ‖opMul ((S ((m' + 1) * 2 ^ i) - S (m' * 2 ^ i))) f hf m‖ ^ 2)
        ≤ μ ^ 2 * ∑' m : ℤ, ‖f m‖ ^ 2 :=
      sum_tsum_norm_sq_opMul_le (Finset.range (2 ^ (κ - i)))
        (fun m' => (S ((m' + 1) * 2 ^ i) - S (m' * 2 ^ i))) (B := μ) hμ (hΔ i hi) f hf
    have hfsum : (∫⁻ m : ℤ, ‖f m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
        = ENNReal.ofReal (∑' m : ℤ, ‖f m‖ ^ 2) := by
      rw [MeasureTheory.lintegral_count,
        ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg _) hfs]
      refine tsum_congr fun m => ?_
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_two]
    have hfinal : ENNReal.ofReal (μ ^ 2) * ∫⁻ m : ℤ, ‖f m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count
        = ENNReal.ofReal (μ ^ 2 * ∑' m : ℤ, ‖f m‖ ^ 2) := by
      rw [hfsum, ← ENNReal.ofReal_mul (sq_nonneg μ)]
    calc ∫⁻ m : ℤ, ENNReal.ofReal (Real.sqrt (∑ m' ∈ Finset.range (2 ^ (κ - i)),
              ‖opMul ((S ((m' + 1) * 2 ^ i) - S (m' * 2 ^ i))) f hf m‖ ^ 2)) ^ (2 : ℝ)
            ∂MeasureTheory.Measure.count
        = ∑ m' ∈ Finset.range (2 ^ (κ - i)), ∑' m : ℤ, ENNReal.ofReal
            (‖opMul ((S ((m' + 1) * 2 ^ i) - S (m' * 2 ^ i))) f hf m‖ ^ 2) := by
          rw [lintegral_congr hpt, lintegral_finsetSum _
            (fun m' _ => Measurable.of_discrete)]
          exact Finset.sum_congr rfl fun m' _ => MeasureTheory.lintegral_count _
      _ = ENNReal.ofReal (∑ m' ∈ Finset.range (2 ^ (κ - i)), ∑' m : ℤ,
            ‖opMul ((S ((m' + 1) * 2 ^ i) - S (m' * 2 ^ i))) f hf m‖ ^ 2) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun m' _ => tsum_nonneg fun m => sq_nonneg _)]
          exact Finset.sum_congr rfl fun m' _ =>
            (ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg _) (hsumm m')).symm
      _ ≤ ENNReal.ofReal (μ ^ 2 * ∑' m : ℤ, ‖f m‖ ^ 2) := ENNReal.ofReal_le_ofReal hbudget
      _ ≤ ENNReal.ofReal (μ ^ 2) * ∫⁻ m : ℤ, ‖f m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count :=
          le_of_eq hfinal.symm
  have ht : ∀ j : ℕ, AEMeasurable (fun m : ℤ =>
      ENNReal.ofReal (‖opMul (S j) f hf m‖)) MeasureTheory.Measure.count :=
    fun j => (Measurable.of_discrete (f := fun m : ℤ =>
      ENNReal.ofReal (‖opMul (S j) f hf m‖))).aemeasurable
  have hrm := rmELpNormSupLe (μ := MeasureTheory.Measure.count) κ (p := 2) (by norm_num)
      (fun j m => ‖opMul (S j) f hf m‖) ht (fun j m => norm_nonneg _)
  simp only [ofReal_norm] at hrm
  have h0term : MeasureTheory.eLpNorm (fun m : ℤ => ‖opMul (S 0) f hf m‖ₑ)
        (ENNReal.ofReal 2) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal μ * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count :=
    by rw [MeasureTheory.eLpNorm_enorm _ AEStronglyMeasurable.of_discrete]
       exact eLpNorm_two_opMul_le (Φ := S 0) hf hμ h0
  have hlevterms : ∀ i ∈ Finset.range (κ + 1),
      MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal
          (rmLevel κ i (fun j => ‖opMul (S j) f hf x‖)))
        (ENNReal.ofReal 2) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal μ
        * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
    intro i hi
    have hiκ : i ≤ κ := by have := Finset.mem_range.mp hi; omega
    refine le_trans (eLpNorm_mono_enorm AEStronglyMeasurable.of_discrete (fun x => ?_)) (hlev i hiκ)
    rw [enorm_eq_self, enorm_eq_self]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [rmLevel]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun m' _ => ?_)
    have hsub : opMul (S ((m' + 1) * 2 ^ i)) f hf - opMul (S (m' * 2 ^ i)) f hf
        = opMul ((S ((m' + 1) * 2 ^ i) - S (m' * 2 ^ i))) f hf :=
      opMul_sub _ _ f hf
    rw [Real.norm_eq_abs]
    refine le_trans (pow_le_pow_left₀ (abs_nonneg _) (abs_norm_sub_norm_le _ _) 2) ?_
    rw [← Pi.sub_apply, congrFun hsub x]
  have hsum : (∑ i ∈ Finset.range (κ + 1), MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal
        (rmLevel κ i (fun j => ‖opMul (S j) f hf x‖)))
        (ENNReal.ofReal 2) MeasureTheory.Measure.count)
      ≤ ((κ + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal μ
            * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count) := by
    calc _ ≤ ∑ _i ∈ Finset.range (κ + 1), (ENNReal.ofReal μ
            * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count) :=
          Finset.sum_le_sum hlevterms
      _ = ((κ + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal μ
            * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hK : ((κ + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((κ : ℝ) + 1) := by
    rw [← ENNReal.ofReal_natCast]; norm_num
  rw [hK] at hsum
  have hef : MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count
      = ENNReal.ofReal ‖ftLp f hf‖ := eLpNorm_count_ftLp hf
  refine le_trans hrm ?_
  refine le_trans (add_le_add h0term (mul_le_mul_right hsum (ENNReal.ofReal 2))) ?_
  rw [hef]
  exact ofReal_level_arith μ ‖ftLp f hf‖ hμ (norm_nonneg _) κ

/-- **The small-scale half of MST Theorem 2** (arXiv:1512.07518, §4.3, the estimate for `sup_{0 ≤ n ≤ 2^κ}`): for the level-`s` major-arc model, the `ℓ²` norm of the maximal function over the dyadic scales `n ≤ 2^κ` is bounded by `C (κ+1) G0 (s+1)^{−δl} ‖f‖_{ℓ²}` — the `(κ+1)` being the number of Rademacher–Menshov levels and the `(s+1)^{−δl}` the Gauss-sum decay on the level's arcs. Route: `rm_le_sum_levels` at `s := κ` for the phase sequence `n ↦ F⁻¹(ν^s_{2^n} f̂)`; each RM level is the square function `(Σ_j ‖F⁻¹((Σ_{m ∈ I_j^i}(ν^s_{2^{m+1}} − ν^s_{2^m})) f̂)‖²)^{1/2}` with `I_j^i = [j 2^i, (j+1) 2^i)`, and its blocks are handled by Plancherel (`tsum_norm_sq_opMul_eq_integral`), the telescoping identity `Σ_{m∈I_j^i}(Φ_{2^{m+1}} − Φ_{2^m}) = Φ_{2^{(j+1)2^i}} − Φ_{2^{j2^i}}` followed by the pointwise bound `|Δ_m(ξ)| ≲ min(|2^{md}ξ|, |2^{md}ξ|^{−1/d})` (from `polyProfile_sub_one_le` for the small regime and `polyProfile_decay_sharp` for the large one), whose sum over `m` is `≲ 1` uniformly — no `2^i` loss, because the block sums are summed *before* squaring: `Σ_j (Σ_{m∈I_j}|Δ_m|)² ≤ (Σ_m |Δ_m|)²`; the disjointness of the bump supports `η_s(· − β)`, `β ∈ (mstU l (s+1)) \ (mstU l s)`, comes from `sigmaN_separated` and gives `Σ_β η_s(ξ − β)² ≤ 1`. -/
theorem level_l2_mst_small_n (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (l : ℕ) (hl : 1 ≤ l) (χ : ℝ) (hχ : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η) (hη1 : η 0 = 1)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s κ : ℕ) (G : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      (G0 : ℝ), 0 ≤ G0 →
      (∀ β ∈ (Work.BourgainPlan.Maximal.mstU l (s + 1)) \ (Work.BourgainPlan.Maximal.mstU l s),
        ‖G β‖ ≤ G0 * ((s : ℝ) + 1) ^ (-(δ * l))) →
      ∀ (hS : ∀ n : ℕ, MeasureTheory.Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))),
      (∀ n : ℕ, ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
        (hS n : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ
          = Work.BourgainPlan.Maximal.mstModelFn G (Work.BourgainPlan.Maximal.mstProf P (2 ^ n))
              (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s)
              ((Work.BourgainPlan.Maximal.mstU l (s + 1))
                \ (Work.BourgainPlan.Maximal.mstU l s)) ξ) →
      ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        ∫⁻ m : ℤ,
            (⨆ n ∈ Finset.range (2 ^ κ + 1),
              ‖Work.BourgainPlan.IonescuWainger.opMul (hS n) f hf m‖ₑ) ^ (2 : ℝ)
            ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal
              ((C * ((κ : ℝ) + 1) * G0 * ((s : ℝ) + 1) ^ (-(δ * l))) ^ 2)
            * ∫⁻ m : ℤ, ‖f m‖ₑ ^ 2 ∂MeasureTheory.Measure.count := by
  -- the two analytic inputs
  obtain ⟨Cdec, hCdecpos, hCdec⟩ := polyProfile_lacunary_sum_le P hd
  have hχd : χ < (P.natDegree : ℝ) := by
    have h2 : (2:ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨M, hMpos, hM⟩ := mstEta_arcSum_le l hl P.natDegree (by omega) χ hχ hχd η
    hηc.continuous hηsup
  refine ⟨3 * M * max 1 Cdec, by positivity, ?_⟩
  intro s κ G G0 hG0 hG hS hSeq f hf
  classical
  -- the level model and its parameters
  set E : Finset Work.BourgainPlan.IonescuWainger.Circle :=
    (mstU l (s + 1)) \ (mstU l s) with hEdef
  set ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ := mstEta P.natDegree χ η s with hψdef
  set ν : ℕ → Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
    fun n => mstModelFn G (mstProf P (2 ^ n)) ψ E with hνdef
  set μ : ℝ := G0 * ((s : ℝ) + 1) ^ (-(δ * l)) * (M * max 1 Cdec) with hμdef
  have hg0 : 0 ≤ G0 * ((s : ℝ) + 1) ^ (-(δ * l)) :=
    mul_nonneg hG0 (Real.rpow_nonneg (by positivity) _)
  have hμ0 : 0 ≤ μ := by
    rw [hμdef]
    exact mul_nonneg hg0 (le_of_lt (mul_pos hMpos (lt_of_lt_of_le one_pos (le_max_left _ _))))
  -- ## (A) the pointwise bound of the zeroth level
  have hν0 : ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, ‖ν 0 ξ‖ ≤ μ := by
    intro ξ
    have hpt : ν 0 ξ = ∑ β ∈ E, G β * (mstProf P 1 (ξ - β) * ψ (ξ - β)) := by
      simp only [hνdef, mstModelFn_apply, pow_zero]
    rw [hpt]
    calc ‖∑ β ∈ E, G β * (mstProf P 1 (ξ - β) * ψ (ξ - β))‖
        ≤ ∑ β ∈ E, ‖G β * (mstProf P 1 (ξ - β) * ψ (ξ - β))‖ := norm_sum_le _ _
      _ ≤ ∑ β ∈ E, (G0 * ((s : ℝ) + 1) ^ (-(δ * l))) * ‖ψ (ξ - β)‖ := by
          refine Finset.sum_le_sum fun β hβ => ?_
          rw [norm_mul, norm_mul]
          calc ‖G β‖ * (‖mstProf P 1 (ξ - β)‖ * ‖ψ (ξ - β)‖)
              ≤ (G0 * ((s : ℝ) + 1) ^ (-(δ * l))) * (1 * ‖ψ (ξ - β)‖) := by
                refine mul_le_mul (hG β hβ) ?_ (by positivity) hg0
                exact mul_le_mul_of_nonneg_right (norm_polyProfile_le_one P 1 _) (norm_nonneg _)
            _ = (G0 * ((s : ℝ) + 1) ^ (-(δ * l))) * ‖ψ (ξ - β)‖ := by ring
      _ = (G0 * ((s : ℝ) + 1) ^ (-(δ * l))) * ∑ β ∈ E, ‖ψ (ξ - β)‖ := by
          rw [Finset.mul_sum]
      _ ≤ (G0 * ((s : ℝ) + 1) ^ (-(δ * l))) * M := mul_le_mul_of_nonneg_left (hM s ξ) hg0
      _ ≤ μ := by
          rw [hμdef]
          exact mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_right hMpos.le (le_max_left _ _)) hg0
  -- ## (B) the pointwise dyadic increment bound
  have hνinc : ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, ∀ i : ℕ, i ≤ κ →
      ∑ m' ∈ Finset.range (2 ^ (κ - i)), ‖ν ((m' + 1) * 2 ^ i) ξ - ν (m' * 2 ^ i) ξ‖ ^ 2
        ≤ μ ^ 2 := by
    intro ξ i hi
    set D : ℕ → ℝ := fun k => ∑ β ∈ E, ‖ψ (ξ - β)‖ *
      ‖polyProfile P (2 ^ (k + 1)) (iwRep (ξ - β)) - polyProfile P (2 ^ k) (iwRep (ξ - β))‖
      with hDdef
    have hDnn : ∀ k, 0 ≤ D k := fun k =>
      Finset.sum_nonneg fun β _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    -- the telescoping identity for the profile
    have htel : ∀ (n n' : ℕ) (ζ : Work.BourgainPlan.IonescuWainger.Circle), n ≤ n' →
        mstProf P (2 ^ n') ζ - mstProf P (2 ^ n) ζ
          = ∑ k ∈ Finset.Ico n n', (mstProf P (2 ^ (k + 1)) ζ - mstProf P (2 ^ k) ζ) := by
      intro n n' ζ hnn
      rw [← Finset.sum_Ico_sub (fun k => mstProf P (2 ^ k) ζ) hnn]
    -- the increment of the model, dominated by the `D`-sum over the block
    have hblock : ∀ n n' : ℕ, n ≤ n' → ‖ν n' ξ - ν n ξ‖
        ≤ (G0 * ((s : ℝ) + 1) ^ (-(δ * l))) * ∑ k ∈ Finset.Ico n n', D k := by
      intro n n' hnn
      have hpt : ν n' ξ - ν n ξ
          = ∑ β ∈ E, G β * ((∑ k ∈ Finset.Ico n n',
              (mstProf P (2 ^ (k + 1)) (ξ - β) - mstProf P (2 ^ k) (ξ - β))) * ψ (ξ - β)) := by
        simp only [hνdef, mstModelFn_apply]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [← htel n n' (ξ - β) hnn]
        ring
      rw [hpt]
      calc ‖∑ β ∈ E, G β * ((∑ k ∈ Finset.Ico n n',
              (mstProf P (2 ^ (k + 1)) (ξ - β) - mstProf P (2 ^ k) (ξ - β))) * ψ (ξ - β))‖
          ≤ ∑ β ∈ E, ‖G β * ((∑ k ∈ Finset.Ico n n',
              (mstProf P (2 ^ (k + 1)) (ξ - β) - mstProf P (2 ^ k) (ξ - β))) * ψ (ξ - β))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ β ∈ E, (G0 * ((s : ℝ) + 1) ^ (-(δ * l))) * ((∑ k ∈ Finset.Ico n n',
              ‖mstProf P (2 ^ (k + 1)) (ξ - β) - mstProf P (2 ^ k) (ξ - β)‖) * ‖ψ (ξ - β)‖) := by
            refine Finset.sum_le_sum fun β hβ => ?_
            calc ‖G β * ((∑ k ∈ Finset.Ico n n',
                    (mstProf P (2 ^ (k + 1)) (ξ - β) - mstProf P (2 ^ k) (ξ - β))) * ψ (ξ - β))‖
                = ‖G β‖ * ‖(∑ k ∈ Finset.Ico n n',
                    (mstProf P (2 ^ (k + 1)) (ξ - β) - mstProf P (2 ^ k) (ξ - β))) * ψ (ξ - β)‖ := by
                  rw [norm_mul]
              _ ≤ (G0 * ((s : ℝ) + 1) ^ (-(δ * l))) * ((∑ k ∈ Finset.Ico n n',
                    ‖mstProf P (2 ^ (k + 1)) (ξ - β) - mstProf P (2 ^ k) (ξ - β)‖)
                      * ‖ψ (ξ - β)‖) := by
                  refine mul_le_mul (hG β hβ) ?_ (norm_nonneg _) hg0
                  rw [norm_mul]
                  exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)
        _ = (G0 * ((s : ℝ) + 1) ^ (-(δ * l))) * ∑ k ∈ Finset.Ico n n', D k := by
            have hcommon : (∑ β ∈ E, (G0 * ((s : ℝ) + 1) ^ (-(δ * l))) *
                  ((∑ k ∈ Finset.Ico n n', ‖mstProf P (2 ^ (k + 1)) (ξ - β)
                      - mstProf P (2 ^ k) (ξ - β)‖) * ‖ψ (ξ - β)‖))
                = ∑ k ∈ Finset.Ico n n', ∑ β ∈ E, (G0 * ((s : ℝ) + 1) ^ (-(δ * l))) *
                    (‖mstProf P (2 ^ (k + 1)) (ξ - β) - mstProf P (2 ^ k) (ξ - β)‖
                      * ‖ψ (ξ - β)‖) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun β _ => ?_
              rw [Finset.sum_mul, Finset.mul_sum]
            rw [hcommon]
            rw [hDdef, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun β _ => ?_
            simp only [mstProf_apply]
            ring
    -- the total budget of the increments
    have hDsum : ∀ N : ℕ, ∑ k ∈ Finset.range N, D k ≤ M * Cdec := by
      intro N
      rw [hDdef, Finset.sum_comm]
      calc ∑ β ∈ E, ∑ k ∈ Finset.range N, ‖ψ (ξ - β)‖ *
              ‖polyProfile P (2 ^ (k + 1)) (iwRep (ξ - β)) - polyProfile P (2 ^ k) (iwRep (ξ - β))‖
          = ∑ β ∈ E, ‖ψ (ξ - β)‖ * (∑ k ∈ Finset.range N,
              ‖polyProfile P (2 ^ (k + 1)) (iwRep (ξ - β))
                - polyProfile P (2 ^ k) (iwRep (ξ - β))‖) := by
            refine Finset.sum_congr rfl fun β _ => ?_
            rw [Finset.mul_sum]
        _ ≤ ∑ β ∈ E, ‖ψ (ξ - β)‖ * Cdec :=
            Finset.sum_le_sum fun β _ =>
              mul_le_mul_of_nonneg_left (hCdec (iwRep (ξ - β)) (abs_iwRep_le _) N) (norm_nonneg _)
        _ = Cdec * ∑ β ∈ E, ‖ψ (ξ - β)‖ := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun β _ => by ring
        _ ≤ Cdec * M := mul_le_mul_of_nonneg_left (hM s ξ) hCdecpos.le
        _ = M * Cdec := by ring
    -- assemble over the dyadic blocks
    set g : ℝ := G0 * ((s : ℝ) + 1) ^ (-(δ * l)) with hgdef
    have hpow : 2 ^ (κ - i) * 2 ^ i = 2 ^ κ := by
      rw [← pow_add]; congr 1; omega
    have hblockle : ∀ m' : ℕ, ‖ν ((m' + 1) * 2 ^ i) ξ - ν (m' * 2 ^ i) ξ‖
        ≤ g * ∑ k ∈ Finset.range (2 ^ i), D (m' * 2 ^ i + k) := by
      intro m'
      have h := hblock (m' * 2 ^ i) ((m' + 1) * 2 ^ i)
        (Nat.mul_le_mul_right _ (Nat.le_succ m'))
      rw [Finset.sum_Ico_eq_sum_range] at h
      have hidx : (m' + 1) * 2 ^ i - m' * 2 ^ i = 2 ^ i := by
        have : (m' + 1) * 2 ^ i = 2 ^ i + m' * 2 ^ i := by
          rw [Nat.add_mul, one_mul, add_comm]
        rw [this, Nat.add_sub_cancel]
      rwa [hidx] at h
    calc ∑ m' ∈ Finset.range (2 ^ (κ - i)), ‖ν ((m' + 1) * 2 ^ i) ξ - ν (m' * 2 ^ i) ξ‖ ^ 2
        ≤ ∑ m' ∈ Finset.range (2 ^ (κ - i)),
            (g * ∑ k ∈ Finset.range (2 ^ i), D (m' * 2 ^ i + k)) ^ 2 :=
          Finset.sum_le_sum fun m' _ =>
            pow_le_pow_left₀ (norm_nonneg _) (hblockle m') 2
      _ = g ^ 2 * ∑ m' ∈ Finset.range (2 ^ (κ - i)),
            (∑ k ∈ Finset.range (2 ^ i), D (m' * 2 ^ i + k)) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m' _ => ?_
          rw [mul_pow]
      _ ≤ g ^ 2 * (∑ k ∈ Finset.range (2 ^ κ), D k) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg g)
          rw [← hpow]
          exact sum_block_sq_le D hDnn (2 ^ (κ - i)) (2 ^ i)
      _ ≤ g ^ 2 * (M * Cdec) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => hDnn k) (hDsum (2 ^ κ)) 2) (sq_nonneg g)
      _ ≤ g ^ 2 * (M * max 1 Cdec) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg g)
          exact pow_le_pow_left₀ (mul_nonneg hMpos.le hCdecpos.le)
            (mul_le_mul_of_nonneg_left (le_max_right 1 Cdec) hMpos.le) 2
      _ = μ ^ 2 := by
          rw [hgdef, hμdef]; ring
  -- ## (C) the a.e. transfer to the `L^∞` classes
  have hcoe : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ∀ n ∈ Finset.range (2 ^ κ + 1), (hS n : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ
        = ν n ξ :=
    (Finset.eventually_all (Finset.range (2 ^ κ + 1))).mpr fun n _ => hSeq n
  have h0 : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ‖(hS 0 : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ≤ μ := by
    filter_upwards [hcoe] with ξ hξ
    rw [hξ 0 (Finset.mem_range.mpr (by positivity))]
    exact hν0 ξ
  have hΔ : ∀ i : ℕ, i ≤ κ → ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ∑ m' ∈ Finset.range (2 ^ (κ - i)),
        ‖(((hS ((m' + 1) * 2 ^ i) - hS (m' * 2 ^ i)) : MeasureTheory.Lp ℂ ⊤
            (AddCircle.haarAddCircle (T := 1))) : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2
        ≤ μ ^ 2 := by
    intro i hi
    have hsub : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
        ∀ m' ∈ Finset.range (2 ^ (κ - i)),
          (((hS ((m' + 1) * 2 ^ i) - hS (m' * 2 ^ i)) : MeasureTheory.Lp ℂ ⊤
              (AddCircle.haarAddCircle (T := 1))) : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ
            = (hS ((m' + 1) * 2 ^ i) : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ
              - (hS (m' * 2 ^ i) : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ :=
      (Finset.eventually_all (Finset.range (2 ^ (κ - i)))).mpr fun m' _ => Lp.coeFn_sub _ _
    filter_upwards [hcoe, hsub] with ξ hξ hξsub
    have hm1 : ∀ m' ∈ Finset.range (2 ^ (κ - i)), (m' + 1) * 2 ^ i ∈ Finset.range (2 ^ κ + 1) := by
      intro m' hm'
      rw [Finset.mem_range] at hm' ⊢
      have h2 : m' + 1 ≤ 2 ^ (κ - i) := by omega
      calc (m' + 1) * 2 ^ i ≤ 2 ^ (κ - i) * 2 ^ i := Nat.mul_le_mul_right _ h2
        _ = 2 ^ κ := by rw [← pow_add]; congr 1; omega
        _ < 2 ^ κ + 1 := Nat.lt_succ_self _
    have hm0 : ∀ m' ∈ Finset.range (2 ^ (κ - i)), m' * 2 ^ i ∈ Finset.range (2 ^ κ + 1) := by
      intro m' hm'
      rw [Finset.mem_range] at hm' ⊢
      have h2 : m' ≤ 2 ^ (κ - i) := by omega
      calc m' * 2 ^ i ≤ 2 ^ (κ - i) * 2 ^ i := Nat.mul_le_mul_right _ h2
        _ = 2 ^ κ := by rw [← pow_add]; congr 1; omega
        _ < 2 ^ κ + 1 := Nat.lt_succ_self _
    calc ∑ m' ∈ Finset.range (2 ^ (κ - i)),
          ‖(((hS ((m' + 1) * 2 ^ i) - hS (m' * 2 ^ i)) : MeasureTheory.Lp ℂ ⊤
              (AddCircle.haarAddCircle (T := 1))) : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2
        = ∑ m' ∈ Finset.range (2 ^ (κ - i)),
          ‖(hS ((m' + 1) * 2 ^ i) : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ
            - (hS (m' * 2 ^ i) : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2 :=
          Finset.sum_congr rfl fun m' hm' => by rw [hξsub m' hm']
      _ = ∑ m' ∈ Finset.range (2 ^ (κ - i)),
          ‖ν ((m' + 1) * 2 ^ i) ξ - ν (m' * 2 ^ i) ξ‖ ^ 2 :=
          Finset.sum_congr rfl fun m' hm' => by rw [hξ _ (hm1 m' hm'), hξ _ (hm0 m' hm')]
      _ ≤ μ ^ 2 := hνinc ξ i hi
  -- ## (D) the abstract level bound and the conversion to the `lintegral` shape
  have hmain := level_l2_of_symbol_bounds (κ := κ) hS hμ0 h0 hΔ f hf
  have hsq : (MeasureTheory.eLpNorm (fun m : ℤ => ⨆ n ∈ Finset.range (2 ^ κ + 1),
        ‖opMul (hS n) f hf m‖ₑ) (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ 2
      = ∫⁻ m : ℤ, (⨆ n ∈ Finset.range (2 ^ κ + 1), ‖opMul (hS n) f hf m‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count := by
    rw [eLpNorm_two_sq]
    exact lintegral_congr fun m => by rw [enorm_eq_self]
  have hXY : 3 * ((κ : ℝ) + 1) * μ
      = 3 * M * max 1 Cdec * ((κ : ℝ) + 1) * G0 * ((s : ℝ) + 1) ^ (-(δ * l)) := by
    rw [hμdef]; ring
  have hstep : (MeasureTheory.eLpNorm (fun m : ℤ => ⨆ n ∈ Finset.range (2 ^ κ + 1),
        ‖opMul (hS n) f hf m‖ₑ) (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ 2
      ≤ ENNReal.ofReal
          ((3 * M * max 1 Cdec * ((κ : ℝ) + 1) * G0 * ((s : ℝ) + 1) ^ (-(δ * l))) ^ 2)
          * ∫⁻ m : ℤ, ‖f m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
    calc (MeasureTheory.eLpNorm (fun m : ℤ => ⨆ n ∈ Finset.range (2 ^ κ + 1),
          ‖opMul (hS n) f hf m‖ₑ) (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ 2
        ≤ (ENNReal.ofReal (3 * ((κ : ℝ) + 1) * μ)
            * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hmain 2
      _ = ENNReal.ofReal ((3 * ((κ : ℝ) + 1) * μ) ^ 2)
            * ∫⁻ m : ℤ, ‖f m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
          rw [mul_pow, ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 3 * ((κ:ℝ)+1) * μ),
            ← eLpNorm_two_sq f]
      _ = ENNReal.ofReal
            ((3 * M * max 1 Cdec * ((κ : ℝ) + 1) * G0 * ((s : ℝ) + 1) ^ (-(δ * l))) ^ 2)
            * ∫⁻ m : ℤ, ‖f m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
          rw [hXY]
  rw [← hsq]
  simpa using hstep

end

end Work.BourgainPlan.Maximal
