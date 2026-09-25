import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.discAvgZC_multiplier_z
import Submission.Work.BourgainPlan.Maximal.minor_arc_lp
import Submission.Work.BourgainPlan.IonescuWainger.OpArcLinear
import Submission.Work.BourgainPlan.IonescuWainger.opMul_mul
import Submission.Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
import Submission.Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal

/-!
# Pulling the frozen density weight out of a maximal supremum

This file proves `Work.Maximal.mst_lrs_frozen_sup`: the `ℓ^r`-norm (`r ≥ 1`) of the maximal
function `sup_{k ∈ K} |Op_{μ • Π_k} g|` of the *frozen* density-weighted symbols `μ • Π_k`
(`μ = khatZMult P J`) is bounded by the maximal function of the weight-free symbols `Π_k`.

The analytic content is entirely local and does not use any property of the symbols `Π_k`:

* the density average `discAvgZC P J h m = J⁻¹ Σ_{i<J} h (m + P(i))` is a convex combination of
  the shifts `h (· + P(i))`, so `sup_k |M_J h_k (m)| ≤ J⁻¹ Σ_i sup_k |h_k (m + P(i))|`
  (`mst_lrs_discAvg_iSup_le`);
* the counting measure on `ℤ` is translation invariant, so the `ℓ^r`-norms of the shifted maximal
  functions `m ↦ sup_k |h_k (m + P(i))|` are all equal (`lrs_eLpNorm_count_add_const`), and
  Minkowski's inequality (the triangle inequality for `eLpNorm`, `r ≥ 1`) bounds the norm of the
  finite sum by the sum of the norms (`eLpNorm_finset_sum_le_ennreal`).

The identification `Op_{μ • Π_k} g = M_J (Op_{Π_k} g)` is `opMul_mul` + `opMul_khatZMult_eq_discAvgZC`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))
local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-! ## Translation invariance of the counting measure on `ℤ` -/

/-- Translation invariance of the counting integral on `ℤ`. -/
lemma lrs_lintegral_count_add_const (f : ℤ → ℝ≥0∞) (c : ℤ) :
    ∫⁻ m : ℤ, f (m + c) ∂MeasureTheory.Measure.count
      = ∫⁻ m : ℤ, f m ∂MeasureTheory.Measure.count := by
  rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
  exact Equiv.tsum_eq (Equiv.addRight c) f

/-- Translation invariance of the `ℒ^q`-seminorm (`q` a real exponent) for the counting measure. -/
lemma lrs_eLpNorm'_count_add_const (f : ℤ → ℝ≥0∞) (q : ℝ) (c : ℤ) :
    MeasureTheory.eLpNorm' (fun m : ℤ => f (m + c)) q MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm' f q MeasureTheory.Measure.count := by
  simp only [MeasureTheory.eLpNorm', enorm_eq_self]
  congr 1
  exact lrs_lintegral_count_add_const (fun m => f m ^ q) c

/-- Translation invariance of the `eLpNorm` (`q` an `ℝ≥0∞`-exponent, `q ≠ 0, ⊤`). -/
lemma lrs_eLpNorm_count_add_const (f : ℤ → ℝ≥0∞) {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ⊤)
    (c : ℤ) :
    MeasureTheory.eLpNorm (fun m : ℤ => f (m + c)) q MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm f q MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_eLpNorm' hq0 hqt (measurable_of_countable _).aestronglyMeasurable,
    MeasureTheory.eLpNorm_eq_eLpNorm' hq0 hqt (measurable_of_countable _).aestronglyMeasurable]
  exact lrs_eLpNorm'_count_add_const f q.toReal c

/-! ## The pointwise bound for a single density average -/

/-- **The norm bound for the discrete average**: `‖M_J h m‖ ≤ J⁻¹ Σ_{i<J} ‖h (m + P(i))‖`. -/
lemma mst_lrs_enorm_discAvgZC_le (P : Polynomial ℤ) (J : ℕ) (h : ℤ → ℂ) (m : ℤ) :
    ‖Work.BourgainPlan.Maximal.discAvgZC P J h m‖ₑ ≤ ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹)
      * ∑ i ∈ Finset.range J, ‖h (m + P.eval (i : ℤ))‖ₑ := by
  have hstep : ‖Work.BourgainPlan.Maximal.discAvgZC P J h m‖ ≤ ((J : ℕ) : ℝ)⁻¹
      * ∑ i ∈ Finset.range J, ‖h (m + P.eval (i : ℤ))‖ := by
    rw [Work.BourgainPlan.Maximal.discAvgZC]
    calc ‖((J : ℂ)⁻¹) * ∑ i ∈ Finset.range J, h (m + P.eval (i : ℤ))‖
        ≤ ‖((J : ℂ)⁻¹)‖ * ‖∑ i ∈ Finset.range J, h (m + P.eval (i : ℤ))‖ := norm_mul_le _ _
      _ = ((J : ℕ) : ℝ)⁻¹ * ‖∑ i ∈ Finset.range J, h (m + P.eval (i : ℤ))‖ := by
          rw [norm_inv, Complex.norm_natCast, inv_eq_one_div]
      _ ≤ ((J : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range J, ‖h (m + P.eval (i : ℤ))‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
  refine le_trans (le_of_eq (ofReal_norm _).symm) ?_
  refine le_trans (ENNReal.ofReal_le_ofReal hstep) (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]
  simp only [ofReal_norm]

/-! ## The maximal density average is an `ℓ^r`-contraction, uniformly in the family -/

/-- **The density average `M_J` is a contraction on the maximal function.**  For `J ≥ 1` and every
exponent `p ≥ 1`, the `eLpNorm` of `sup_{k ∈ K} |M_J h_k|` is bounded by that of
`sup_{k ∈ K} |h_k|`: `M_J` is a convex combination of the translations `· + P(i)`, the counting
measure is translation invariant, and Minkowski's inequality bounds the norm of the finite sum. -/
lemma mst_lrs_discAvg_iSup_le (P : Polynomial ℤ) (J : ℕ) (hJ : 0 < J) (K : Finset ℕ)
    (T : ℕ → ℤ → ℂ) {p : ℝ} (hp : 1 ≤ p) :
    MeasureTheory.eLpNorm (fun m : ℤ =>
        ⨆ k ∈ K, ‖Work.BourgainPlan.Maximal.discAvgZC P J (T k) m‖ₑ)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun m : ℤ => ⨆ k ∈ K, ‖T k m‖ₑ)
        (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  set U : ℤ → ℝ≥0∞ := fun m => ⨆ k ∈ K, ‖T k m‖ₑ with hU
  have hppos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hppos
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc : ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpoint : ∀ m, (⨆ k ∈ K, ‖Work.BourgainPlan.Maximal.discAvgZC P J (T k) m‖ₑ)
      ≤ ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹)
        * ∑ i ∈ Finset.range J, U (m + P.eval (i : ℤ)) := by
    intro m
    refine iSup₂_le (fun k _ => ?_)
    refine (mst_lrs_enorm_discAvgZC_le P J (T k) m).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Finset.sum_le_sum
      (fun i _ => le_iSup₂ (f := fun k _ => ‖T k (m + P.eval (i : ℤ))‖ₑ) k ‹k ∈ K›)
  have hpoint' : ∀ m : ℤ,
      ‖(⨆ k ∈ K, ‖Work.BourgainPlan.Maximal.discAvgZC P J (T k) m‖ₑ)‖ₑ
        ≤ ‖ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹)
            * ∑ i ∈ Finset.range J, U (m + P.eval (i : ℤ))‖ₑ := by
    intro m
    rw [enorm_eq_self, enorm_eq_self]
    exact hpoint m
  have h1 : MeasureTheory.eLpNorm (fun m : ℤ =>
        ⨆ k ∈ K, ‖Work.BourgainPlan.Maximal.discAvgZC P J (T k) m‖ₑ)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹) * MeasureTheory.eLpNorm
          (fun m : ℤ => ∑ i ∈ Finset.range J, U (m + P.eval (i : ℤ)))
          (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    refine (eLpNorm_mono_enorm (measurable_of_countable _).aestronglyMeasurable hpoint').trans
      (le_of_eq ?_)
    exact Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal hc hp0 hpt
  have h2 : MeasureTheory.eLpNorm (fun m : ℤ => ∑ i ∈ Finset.range J, U (m + P.eval (i : ℤ)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ∑ i ∈ Finset.range J, MeasureTheory.eLpNorm
          (fun m : ℤ => U (m + P.eval (i : ℤ))) (ENNReal.ofReal p)
          MeasureTheory.Measure.count :=
    Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal
      (ENNReal.one_le_ofReal.mpr hp) (fun i _ => (measurable_of_countable _).aemeasurable)
  have h3 : ∀ i : ℕ, MeasureTheory.eLpNorm (fun m : ℤ => U (m + P.eval (i : ℤ)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm U (ENNReal.ofReal p) MeasureTheory.Measure.count := fun i =>
    lrs_eLpNorm_count_add_const U hp0 hpt (P.eval (i : ℤ))
  have hsum : (∑ i ∈ Finset.range J, MeasureTheory.eLpNorm
        (fun m : ℤ => U (m + P.eval (i : ℤ))) (ENNReal.ofReal p) MeasureTheory.Measure.count)
      = (J : ℝ≥0∞) * MeasureTheory.eLpNorm U (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    rw [Finset.sum_congr rfl (fun i _ => h3 i), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have harith : ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹) * (J : ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    rw [show (((J : ℕ) : ℝ)⁻¹ * (J : ℝ)) = 1 by
      rw [inv_mul_cancel₀ (by exact_mod_cast hJ.ne')]]
    simp
  calc MeasureTheory.eLpNorm (fun m : ℤ =>
          ⨆ k ∈ K, ‖Work.BourgainPlan.Maximal.discAvgZC P J (T k) m‖ₑ)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹) * MeasureTheory.eLpNorm
          (fun m : ℤ => ∑ i ∈ Finset.range J, U (m + P.eval (i : ℤ)))
          (ENNReal.ofReal p) MeasureTheory.Measure.count := h1
    _ ≤ ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹) *
          ((J : ℝ≥0∞) * MeasureTheory.eLpNorm U (ENNReal.ofReal p)
            MeasureTheory.Measure.count) :=
        mul_le_mul_of_nonneg_left (h2.trans (le_of_eq hsum)) bot_le
    _ = MeasureTheory.eLpNorm U (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        rw [← mul_assoc, harith, one_mul]

/-! ## The frozen weight may be pulled out of the supremum -/

/-- **The frozen weight may be pulled out of the supremum.**  With `μ = khatZMult P J` — the `L^∞`-class of the Fourier transform of the polynomial density kernel `k(j) = J⁻¹·#{i < J : P i = j}` (a probability measure with nonnegative weights, `opMul_khatZMult_eq_discAvgZC`) — the pointwise supremum over any finite set `K` of scale indices of the multiplier with symbol `μ • Π_k` is dominated in `ℓ^r`, `r ≥ 1`, by the same supremum for the weight-free symbols `Π_k`.  (The density average is the convex combination `discAvgZC P J h m = J⁻¹ Σ_{i<J} h (m + P i)` of the shifts of `h`, so `sup_k |(μ * h_k)(m)| ≤ J⁻¹ Σ_i sup_k |h_k (m + P i)|`, and the `ℓ^r`-norms of the shifted sequences agree by translation invariance of the counting measure together with Minkowski's inequality.)  Note `opMul (μ • Π_k) = opMul μ (opMul Π_k g)` by `opMul_mul`, and `opMul (khatZMult P J)` is `discAvgZC P J` by `opMul_khatZMult_eq_discAvgZC`. -/
theorem mst_lrs_frozen_sup
    (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (J : ℕ)
    (hpi : ∀ (N s : ℕ), MeasureTheory.MemLp
      (fun ζ : Work.BourgainPlan.IonescuWainger.Circle =>
        star (Work.BourgainPlan.Maximal.mstProf P N ζ) *
          Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    {r : ℝ} (hr : 1 ≤ r) (s : ℕ) (K : Finset ℕ) (g : ℤ →₀ ℂ) :
    MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k ∈ K,
        ‖Work.BourgainPlan.IonescuWainger.opMul
          (Work.BourgainPlan.Maximal.khatZMult P J •
            Work.BourgainPlan.IonescuWainger.arcSymbolLp
              (fun ζ : Work.BourgainPlan.IonescuWainger.Circle =>
                star (Work.BourgainPlan.Maximal.mstProf P (2 ^ k) ζ) *
                  Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ)
              (hpi (2 ^ k) s)
              (Work.BourgainPlan.Maximal.mstLevel l (s + 1) \
                Work.BourgainPlan.Maximal.mstLevel l s))
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
        (ENNReal.ofReal r) (MeasureTheory.Measure.count)
      ≤ MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k ∈ K,
        ‖Work.BourgainPlan.IonescuWainger.opMul
          (Work.BourgainPlan.IonescuWainger.arcSymbolLp
            (fun ζ : Work.BourgainPlan.IonescuWainger.Circle =>
              star (Work.BourgainPlan.Maximal.mstProf P (2 ^ k) ζ) *
                Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ)
            (hpi (2 ^ k) s)
            (Work.BourgainPlan.Maximal.mstLevel l (s + 1) \
              Work.BourgainPlan.Maximal.mstLevel l s))
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
        (ENNReal.ofReal r) (MeasureTheory.Measure.count) := by
  -- abbreviate the arc symbols and the level set
  set E : Finset Circ := Work.BourgainPlan.Maximal.mstLevel l (s + 1) \
    Work.BourgainPlan.Maximal.mstLevel l s with hE
  set Phi : ℕ → Lp ℂ ⊤ haarT := fun k =>
    arcSymbolLp (fun ζ : Circ => star (Work.BourgainPlan.Maximal.mstProf P (2 ^ k) ζ) *
      Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ) (hpi (2 ^ k) s) E with hPhi
  -- the frozen multiplier is the density average of the weight-free multiplier
  have hkey : ∀ k : ℕ, opMul (Work.BourgainPlan.Maximal.khatZMult P J • Phi k) (⇑g)
      (memℓp_finsupp g)
        = Work.BourgainPlan.Maximal.discAvgZC P J
            (opMul (Phi k) (⇑g) (memℓp_finsupp g)) := by
    intro k
    rw [← opMul_mul (Work.BourgainPlan.Maximal.khatZMult P J) (Phi k) (⇑g)
      (memℓp_finsupp g)]
    exact Work.BourgainPlan.Maximal.opMul_khatZMult_eq_discAvgZC P J
      (opMul (Phi k) (⇑g) (memℓp_finsupp g))
      (opMul_memℓp (Phi k) (⇑g) (memℓp_finsupp g))
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ
  · -- `J = 0`: the density average vanishes identically
    subst hJ0
    have hL : (fun m : ℤ => (⨆ k ∈ K, ‖opMul (Work.BourgainPlan.Maximal.khatZMult P 0 • Phi k)
          (⇑g) (memℓp_finsupp g) m‖ₑ)) = fun _ => 0 := by
      funext m
      refine le_antisymm ?_ bot_le
      refine iSup₂_le fun k _ => ?_
      rw [hkey k]
      simp [Work.BourgainPlan.Maximal.discAvgZC]
    rw [hL]
    simp
  · -- `J ≥ 1`: the maximal density average is an `ℓ^r`-contraction
    have hpoint : (fun m : ℤ => (⨆ k ∈ K, ‖opMul
          (Work.BourgainPlan.Maximal.khatZMult P J • Phi k) (⇑g) (memℓp_finsupp g) m‖ₑ))
        = (fun m : ℤ => (⨆ k ∈ K, ‖Work.BourgainPlan.Maximal.discAvgZC P J
            (opMul (Phi k) (⇑g) (memℓp_finsupp g)) m‖ₑ)) := by
      funext m
      exact iSup_congr fun k => iSup_congr fun _ => by rw [hkey k]
    rw [hpoint]
    exact mst_lrs_discAvg_iSup_le P J hJ K
      (fun k : ℕ => fun m : ℤ => opMul (Phi k) (⇑g) (memℓp_finsupp g) m) hr

end

end Work.Maximal
