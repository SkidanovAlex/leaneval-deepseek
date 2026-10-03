/-
# The small-scale (paper §7) estimate of the low case of area A6

This module proves `Work.KMTPlan.A6.LcSmall`: the small-scale half of the low case
`k₁ = 0 ∨ k₂ = 0` of Krause--Mirek--Tao's Theorem `varp` at `(p₁,p₂,p) = (2,2,1)`.

The concrete clamped columns `colSmall` are compared with the §6 model tuple `lowModel`, and the
two pieces are estimated by

* `lowSmallModelApprox` (paper §6, Proposition `mod-approx` composed with the functional calculus
  `bn-ident`), whose single-scale error `2^{O(2^{ρL})} N^{-1}` is summed over the admissible
  lacunary scales by `lowSmallErrSum` and `eLpNorm_variationalNorm_le_of_termwise_low`;
* `lowSmallModelVar` (paper §7 for the model tuple);
* `lowSmallBoundedL` (the crude bound for the `Λ`-dependently finitely many bounded quadruples
  `lcL ≤ B`, where the main regime may fail);
* the arithmetic lemmas `mainRegimeOfHeightScale`, `scale_ge_of_heightScale`,
  `modelWeightInvLeGain`, `lacunarySumInv`, and the new `lowSmallWindowCondsStrict`, which supplies the
  threshold `B₀` beyond which the two §6 window conditions of the model `lowModel` are automatic
  on `lowSmallSet`.

**The §6 window.**  `lowModel` uses the *narrow* window `m_* = η_{≤-2u} ⊗ η_{≤-2du}`,
`u = uScale ρ (lcL l₁ l₂ k₁ k₂)`, exactly as `Work.KMTAreas.A7.modelTuple`; the earlier wide
window `mStarF 0` made both `lowSmallModelApprox` and `lowSmallModelVar` *false* (the arithmetic
frequencies are then not resolved and the model's torus symbol is inflated by `≍ 4^l`).  The two
conditions on the window — it contains the frequency support of the bumps, and it is finer than
the spacing `2^{-l}` of the arithmetic frequencies — are the extra hypotheses of
`lowSmallModelApprox` (and the second one of `lowSmallModelVar`); see
`NOTES_A6_lowModel_WINDOW_FIX.md` and `NOTES_lowSmallModelApprox.md`, Finding 2.

The new material in this file is the assembly: the pointwise splitting
`colSmall = lowModel + (colSmall - lowModel)`, the subadditivity of the variational norm in
`ℓ¹(ℤ)`, the termwise summation of the approximation error, the absorption of the two constants
into a single one, and the case split in `lcL l₁ l₂ k₁ k₂`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.modelWeightInvLeGain
import Submission.Work.KMTPlan.A6.mainRegimeOfHeightScale
import Submission.Work.KMTPlan.A6.lowSmallErrSum
import Submission.Work.KMTPlan.A6.lowSmallModelVar
import Submission.Work.KMTPlan.A6.lowSmallBoundedL
import Submission.Work.KMTPlan.A6.lowSmallModelApprox
import Submission.Work.KMTPlan.A6.lowSmallWindowCondsStrict
import Submission.Port.Aesm

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.Analysis.EndVar

/-! ## Elementary bookkeeping -/

/-- **Subadditivity of the variational norm, integrated in `ℓ¹(ℤ)`.** -/
lemma eLpNorm_variationalNorm_add_le_low (r : ℝ≥0) (hr : 1 ≤ r) (u v : ℕ → ℤ → ℂ) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n => u n x + v n x)) 1 Measure.count
      ≤ eLpNorm (fun x : ℤ => variationalNorm r (fun n => u n x)) 1 Measure.count
        + eLpNorm (fun x : ℤ => variationalNorm r (fun n => v n x)) 1 Measure.count := by
  refine (eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ => variationalNorm r (fun n => u n x + v n x))
    (g := fun x : ℤ => variationalNorm r (fun n => u n x) + variationalNorm r (fun n => v n x))
    (fun x => ?_)).trans ?_
  · rw [enorm_eq_self, enorm_eq_self]
    exact variationalNorm_add_le hr (fun n => u n x) (fun n => v n x)
  · have h1 : AEStronglyMeasurable (fun x : ℤ => variationalNorm r (fun n => u n x))
        Measure.count := (measurable_of_countable _).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x : ℤ => variationalNorm r (fun n => v n x))
        Measure.count := (measurable_of_countable _).aestronglyMeasurable
    exact eLpNorm_add_le (show (1 : ℝ≥0∞) ≤ 1 from le_rfl)

/-- **The `ℓ¹` norm of an error family supported on a set of scales.** -/
lemma eLpNorm_variationalNorm_le_of_termwise_low {r : ℝ≥0} (hr : 1 ≤ r) {P : ℕ → Prop}
    [DecidablePred P] {u : ℕ → ℤ → ℂ} {w C : ℝ} {E : ℝ≥0∞} {N : ℕ → ℝ}
    (hzero : ∀ n, ¬ P n → u n = 0)
    (hbd : ∀ n, P n →
      eLpNorm (fun x : ℤ => u n x) 1 Measure.count
        ≤ ENNReal.ofReal w * ENNReal.ofReal ((N n)⁻¹) * E)
    (hsum : (∑' n : ℕ, if P n then ENNReal.ofReal ((N n)⁻¹) else 0) ≤ ENNReal.ofReal C) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n => u n x)) 1 Measure.count
      ≤ 3 * (ENNReal.ofReal w * ENNReal.ofReal C * E) := by
  refine (eLpNorm_variationalNorm_one_le_tsum hr u).trans ?_
  have hstep1 : (∑' n : ℕ, eLpNorm (fun x : ℤ => u n x) 1 Measure.count)
      ≤ ∑' n : ℕ, (if P n then ENNReal.ofReal w * ENNReal.ofReal ((N n)⁻¹) * E else 0) := by
    refine ENNReal.tsum_le_tsum (fun n => ?_)
    by_cases hn : P n
    · rw [if_pos hn]; exact hbd n hn
    · rw [if_neg hn, hzero n hn]; simp
  refine (mul_le_mul_right hstep1 3).trans ?_
  have hstep2 : (∑' n : ℕ, (if P n then ENNReal.ofReal w * ENNReal.ofReal ((N n)⁻¹) * E else 0))
      = ENNReal.ofReal w * (∑' n : ℕ, if P n then ENNReal.ofReal ((N n)⁻¹) * E else 0) := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr (fun n => by by_cases hn : P n <;> simp [hn, mul_assoc])
  have hstep3 : (∑' n : ℕ, if P n then ENNReal.ofReal ((N n)⁻¹) * E else 0)
      = (∑' n : ℕ, if P n then ENNReal.ofReal ((N n)⁻¹) else 0) * E := by
    rw [← ENNReal.tsum_mul_right]
    exact tsum_congr (fun n => by by_cases hn : P n <;> simp [hn])
  have hmain : (∑' n : ℕ,
        (if P n then ENNReal.ofReal w * ENNReal.ofReal ((N n)⁻¹) * E else 0))
      ≤ ENNReal.ofReal w * ENNReal.ofReal C * E := by
    rw [hstep2, hstep3]
    refine (mul_le_mul' le_rfl (mul_le_mul_left hsum E)).trans ?_
    rw [mul_assoc]
  exact (mul_le_mul_right hmain 3).trans le_rfl

/-- `lcWeight` in terms of the scale `lcL`. -/
lemma lcWeight_eq_lcL (c : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    lcWeight c l₁ l₂ k₁ k₂ = (2 : ℝ) ^ (-(c * (lcL l₁ l₂ k₁ k₂ : ℝ))) := by
  have h : (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ) = (lcL l₁ l₂ k₁ k₂ : ℝ) := by
    have h2 := congrArg (fun (z : ℤ) => (z : ℝ)) (lcL_eq l₁ l₂ k₁ k₂)
    simp only [Int.cast_natCast] at h2
    exact h2.symm
  simp only [lcWeight, h]

/-- `modelWeight` depends only on the scale `lcL`. -/
lemma modelWeight_eq_lcL (A ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂
      = Work.KMTAreas.A7.modelWeight A ρ (lcL l₁ l₂ k₁ k₂) (lcL l₁ l₂ k₁ k₂)
          (lcL l₁ l₂ k₁ k₂) (lcL l₁ l₂ k₁ k₂) := by
  have h : (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ) = (lcL l₁ l₂ k₁ k₂ : ℝ) := by
    have h2 := congrArg (fun (z : ℤ) => (z : ℝ)) (lcL_eq l₁ l₂ k₁ k₂)
    simp only [Int.cast_natCast] at h2
    exact h2.symm
  have h4 : (lmax (lcL l₁ l₂ k₁ k₂) (lcL l₁ l₂ k₁ k₂) (lcL l₁ l₂ k₁ k₂ : ℤ)
      (lcL l₁ l₂ k₁ k₂ : ℤ) : ℝ) = (lcL l₁ l₂ k₁ k₂ : ℝ) := by
    simp [lmax]
  simp only [Work.KMTAreas.A7.modelWeight, Work.KMTAreas.A7.lmaxR, h, h4]

/-- `Real.toNNReal` and `ENNReal.ofReal` agree (as `ℝ≥0∞`-valued quantities). -/
lemma coe_toNNReal_eq_ofReal {x : ℝ} (hx : 0 ≤ x) :
    ((Real.toNNReal x : NNReal) : ENNReal) = ENNReal.ofReal x := by
  rw [ENNReal.ofReal_eq_coe_nnreal hx, Real.toNNReal_of_nonneg hx]

/-- `lcWeight c l₁ l₂ k₁ k₂ > 0` for `c > 0`. -/
lemma lcWeight_pos (c : ℝ) (hc : 0 < c) (l₁ l₂ k₁ k₂ : ℕ) :
    0 < lcWeight c l₁ l₂ k₁ k₂ := by
  rw [lcWeight_eq_lcL]
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- The scales `⌊a n⌋` as real numbers. -/
def scaleSeq (a : ℕ → NNReal) : ℕ → ℝ := fun n => ((Nat.floor (a n) : ℕ) : ℝ)

/-- `variationalNorm r 0 = 0` for `r ≥ 1`. -/
lemma variationalNorm_zero_local {r : ℝ≥0} (hr : 1 ≤ r) :
    variationalNorm r (0 : ℕ → ℂ) = 0 := by
  have h := variationalNorm_smul (r := r) hr (0 : ℂ) (0 : ℕ → ℂ)
  simpa using h

/-- A sum of the shape `A + 3q + B` with `q > 0` is positive. -/
lemma coe_sum_ne_zero (A B : NNReal) {q : NNReal} (hq : 0 < q) :
    ((A + 3 * q + B : NNReal) : ENNReal) ≠ 0 := by
  intro hzero
  have h0 : (A + 3 * q + B : NNReal) = 0 := ENNReal.coe_eq_zero.mp hzero
  have h1 : A + 3 * q = 0 :=
    ((add_eq_zero_iff_of_nonneg (zero_le : (0 : NNReal) ≤ A + 3 * q)
      (zero_le : (0 : NNReal) ≤ B)).mp h0).1
  have h2 : 3 * q = 0 :=
    ((add_eq_zero_iff_of_nonneg (zero_le : (0 : NNReal) ≤ A)
      (zero_le : (0 : NNReal) ≤ 3 * q)).mp h1).2
  have h3 : q = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  rw [h3] at hq
  exact lt_irrefl _ hq

/-- A function on `ℤ` whose `ℓ²`-norm vanishes is identically zero. -/
lemma eq_zero_of_eLpNorm_eq_zero {f : ℤ → ℂ} (h : eLpNorm f 2 Measure.count = 0) :
    f = 0 := by
  have hae : f =ᵐ[Measure.count] 0 :=
    (MeasureTheory.eLpNorm_eq_zero_iff
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp h
  have hcount : Measure.count {x : ℤ | f x ≠ 0} = 0 := MeasureTheory.ae_iff.mp hae
  funext x
  by_contra hx
  have hle : (1 : ℝ≥0∞) ≤ Measure.count {x : ℤ | f x ≠ 0} := by
    have hsub : ({x} : Set ℤ) ⊆ {x : ℤ | f x ≠ 0} := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      simpa [hy] using hx
    have h1 : Measure.count ({x} : Set ℤ) ≤ Measure.count {x : ℤ | f x ≠ 0} :=
      MeasureTheory.measure_mono hsub
    rw [MeasureTheory.Measure.count_apply (measurableSet_singleton x)] at h1
    simpa using h1
  rw [hcount] at hle
  exact absurd hle (by norm_num)

/-- The clamped columns built from the zero function vanish (first variable). -/
lemma colSmall_zero_left (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ n : ℕ) :
    colSmall ρ P C₀ a (0 : ℤ → ℂ) g l₁ l₂ k₁ k₂ n = 0 := by
  funext x
  rw [colSmall_apply]
  split_ifs with h
  · have h0 := congrFun (congrFun
      (Work.KMTContract.varpCol_kmt_zero_left ρ P P.natDegree C₀ a l₁ l₂ k₁ k₂ g) n) x
    simpa using h0
  · rfl

/-- The clamped columns built from the zero function vanish (second variable). -/
lemma colSmall_zero_right (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (f : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ n : ℕ) :
    colSmall ρ P C₀ a f (0 : ℤ → ℂ) l₁ l₂ k₁ k₂ n = 0 := by
  funext x
  rw [colSmall_apply]
  split_ifs with h
  · have h0 := congrFun (congrFun
      (Work.KMTContract.varpCol_kmt_zero_right ρ P P.natDegree C₀ a l₁ l₂ k₁ k₂ f) n) x
    simpa using h0
  · rfl

/-- The `ℓ¹(ℤ;V^r)` norm of the clamped columns vanishes with the first function. -/
lemma eLpNorm_varNorm_colSmall_zero_left (r : ℝ≥0) (hr : 1 ≤ r) (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ)
    (a : ℕ → NNReal) (g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    eLpNorm (fun x : ℤ => variationalNorm r
      (fun n : ℕ => colSmall ρ P C₀ a (0 : ℤ → ℂ) g l₁ l₂ k₁ k₂ n x))
      1 Measure.count = 0 := by
  rw [show (fun x : ℤ => variationalNorm r
        (fun n : ℕ => colSmall ρ P C₀ a (0 : ℤ → ℂ) g l₁ l₂ k₁ k₂ n x)) = 0 from by
    funext x
    have hz : (fun n : ℕ => colSmall ρ P C₀ a (0 : ℤ → ℂ) g l₁ l₂ k₁ k₂ n x) = 0 := by
      funext n
      exact congrFun (colSmall_zero_left ρ P C₀ a g l₁ l₂ k₁ k₂ n) x
    rw [hz, variationalNorm_zero_local hr]
    simp]
  simp

/-- The `ℓ¹(ℤ;V^r)` norm of the clamped columns vanishes with the second function. -/
lemma eLpNorm_varNorm_colSmall_zero_right (r : ℝ≥0) (hr : 1 ≤ r) (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ)
    (a : ℕ → NNReal) (f : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    eLpNorm (fun x : ℤ => variationalNorm r
      (fun n : ℕ => colSmall ρ P C₀ a f (0 : ℤ → ℂ) l₁ l₂ k₁ k₂ n x))
      1 Measure.count = 0 := by
  rw [show (fun x : ℤ => variationalNorm r
        (fun n : ℕ => colSmall ρ P C₀ a f (0 : ℤ → ℂ) l₁ l₂ k₁ k₂ n x)) = 0 from by
    funext x
    have hz : (fun n : ℕ => colSmall ρ P C₀ a f (0 : ℤ → ℂ) l₁ l₂ k₁ k₂ n x) = 0 := by
      funext n
      exact congrFun (colSmall_zero_right ρ P C₀ a f l₁ l₂ k₁ k₂ n) x
    rw [hz, variationalNorm_zero_local hr]
    simp]
  simp

/-! ## The assembly -/

theorem lowSmallScaled_of_approx
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hApprox : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ A : ℝ, 0 ≤ A ∧
      ∀ (Λ : NNReal) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) (f g : ℤ → ℂ),
        (k₁ = 0 ∨ k₂ = 0) → MemLp f 2 Measure.count → MemLp g 2 Measure.count →
        1 < Λ → Lacunary Λ a → (∀ m, 1 ≤ a m) →
        lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
        Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n)) →
        max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) + 1
            ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat →
        lcL l₁ l₂ k₁ k₂ ≤ 2 * Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) →
        eLpNorm (fun x : ℤ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count
          ≤ ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂)
              * ENNReal.ofReal ((((Nat.floor (a n) : ℕ) : ℝ))⁻¹)
              * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count)
    (hWin : ∀ (ρ : ℝ), 0 < ρ → ρ * (C₀ : ℝ) ≤ 1 / 8 →
      ∃ B₀ : ℕ, ∀ (l₁ l₂ k₁ k₂ N : ℕ),
        Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N →
        B₀ ≤ lcL l₁ l₂ k₁ k₂ →
        (max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) + 1
            ≤ (Work.Analysis.EndVar.logN N).toNat) ∧
          lcL l₁ l₂ k₁ k₂ ≤ 2 * Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)) :
    LcSmall P r C₀ := by
  intro _
  obtain ⟨c, hc, ρ₀, hρ₀, hmodel⟩ := lowSmallModelVar P hd r hr hA1 hI C₀ hC₀
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  refine ⟨c, hc, min ρ₀ (min (1 / (8 * (C₀ : ℝ))) 1),
    lt_min hρ₀ (lt_min (by positivity) one_pos), ?_⟩
  intro ρ hρ hρle
  have hρρ₀ : ρ ≤ ρ₀ := le_trans hρle (min_le_left _ _)
  have hρle1 : ρ ≤ 1 := le_trans hρle (le_trans (min_le_right _ _) (min_le_right _ _))
  have hρ8C₀ : ρ * (8 * (C₀ : ℝ)) ≤ 1 := by
    have h : ρ ≤ 1 / (8 * (C₀ : ℝ)) :=
      le_trans hρle (le_trans (min_le_right _ _) (min_le_left _ _))
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (C₀ : ℝ))] at h
    linarith
  have hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 4 := by nlinarith [hρ8C₀]
  have h2ρC₀ : 2 * ρ * (C₀ : ℝ) ≤ 1 / 4 := by nlinarith [hρ8C₀]
  obtain ⟨A, hA, happrox⟩ := hApprox ρ hρ hρle1
  obtain ⟨C₂, hC₂⟩ := hmodel ρ hρ hρρ₀
  obtain ⟨B₁, hB₁⟩ := mainRegimeOfHeightScale ρ hρ C₀ hC₀ hρC₀
  obtain ⟨B₂, hB₂⟩ := modelWeightInvLeGain A c ρ hA hc hρ (C₀ : ℝ)
    (by exact_mod_cast hC₀) h2ρC₀
  obtain ⟨B₀, hWinB⟩ := hWin ρ hρ (by nlinarith [hρ8C₀])
  set B : ℕ := max (max (max B₁ B₂) B₀) (2 * C₀ + 1) with hBdef
  obtain ⟨Cb, hCb⟩ := lowSmallBoundedL P hd r hr hA1 hI ρ hρ hρle1 C₀ hC₀ B
  refine ⟨fun Λ => C₂ Λ + 3 * Real.toNNReal (2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)))
      + Cb Λ * Real.toNNReal ((2 : ℝ) ^ (c * (B : ℝ))), ?_⟩
  change ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → (k₁ = 0 ∨ k₂ = 0) →
      eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
        ≤ ((C₂ Λ + 3 * Real.toNNReal (2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)))
            + Cb Λ * Real.toNNReal ((2 : ℝ) ^ (c * (B : ℝ))) : NNReal) : ENNReal)
          * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hcase
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hratio : (0 : ℝ) < (Λ : ℝ) / ((Λ : ℝ) - 1) := div_pos (by positivity) (by linarith)
  have hqR : (0 : ℝ) < 2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)) := mul_pos (by norm_num) hratio
  have hq0le : (0 : ℝ) ≤ 2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)) := le_of_lt hqR
  set q : NNReal := Real.toNNReal (2 * ((Λ : ℝ) / ((Λ : ℝ) - 1))) with hqdef
  set K : NNReal := Real.toNNReal ((2 : ℝ) ^ (c * (B : ℝ))) with hKdef
  have hqNN : (0 : NNReal) < q := by
    rw [hqdef]; exact Real.toNNReal_pos.mpr hqR
  have hKposR : (0 : ℝ) < (2 : ℝ) ^ (c * (B : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hKENN : (K : ENNReal) = ENNReal.ofReal ((2 : ℝ) ^ (c * (B : ℝ))) := by
    rw [hKdef]; exact coe_toNNReal_eq_ofReal hKposR.le
  have hwne : ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (lcWeight_pos c hc l₁ l₂ k₁ k₂))
  have hCne : ((C₂ Λ + 3 * q + Cb Λ * K : NNReal) : ENNReal) ≠ 0 :=
    coe_sum_ne_zero (C₂ Λ) (Cb Λ * K) hqNN
  have hB₁B : B₁ ≤ B := by
    rw [hBdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hB₂B : B₂ ≤ B := by
    rw [hBdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hB₀B : B₀ ≤ B := by
    rw [hBdef]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have h2C₀B : 2 * C₀ + 1 ≤ B := by rw [hBdef]; exact le_max_right _ _
  by_cases hf : MemLp f 2 Measure.count
  · by_cases hg : MemLp g 2 Measure.count
    · by_cases hLs : lcL l₁ l₂ k₁ k₂ ≤ B
      · -- ===================== the crude bound =====================
        have hK1 : (1 : ENNReal) ≤ (K : ENNReal)
            * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂) := by
          rw [hKENN, lcWeight_eq_lcL, ← ENNReal.ofReal_mul hKposR.le,
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) from (Real.rpow_zero 2).symm]
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have hLB : ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast hLs
          nlinarith [hc, hLB]
        have hCb_le : (Cb Λ : ENNReal) ≤ ((C₂ Λ + 3 * q + Cb Λ * K : NNReal) : ENNReal)
            * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂) := by
          have hA' : (Cb Λ : ENNReal) * 1 ≤ (Cb Λ : ENNReal) * ((K : ENNReal)
              * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂)) := mul_le_mul' le_rfl hK1
          rw [mul_one] at hA'
          refine hA'.trans ?_
          have h4 : (Cb Λ : ENNReal) * ((K : ENNReal) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂))
              = ((Cb Λ : ENNReal) * (K : ENNReal))
                  * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂) := (mul_assoc _ _ _).symm
          rw [h4, ← ENNReal.coe_mul]
          refine mul_le_mul' ?_ le_rfl
          rw [ENNReal.coe_add]
          exact le_add_of_nonneg_left
            (a := ((Cb Λ * K : NNReal) : ENNReal))
            (b := ((C₂ Λ + 3 * q : NNReal) : ENNReal)) zero_le
        exact (hCb a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hcase hf hg hLs).trans
          (mul_le_mul' (mul_le_mul' hCb_le le_rfl) le_rfl)
      · -- ===================== the model split =====================
        push Not at hLs
        have hB₁L : B₁ ≤ lcL l₁ l₂ k₁ k₂ := le_trans hB₁B (le_of_lt hLs)
        have hB₂L : B₂ ≤ lcL l₁ l₂ k₁ k₂ := le_trans hB₂B (le_of_lt hLs)
        have h2C₀L : 2 * C₀ ≤ lcL l₁ l₂ k₁ k₂ := by
          have h := lt_of_le_of_lt h2C₀B hLs
          omega
        have hmainReg : ∀ n, lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
            Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n)) := fun n hn =>
          hB₁ l₁ l₂ k₁ k₂ (Nat.floor (a n)) hn.1 hB₁L
        have hcond : ∀ n, lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
            heightScale C₀ (Nat.floor (a n)) ≥ lcL l₁ l₂ k₁ k₂ := by
          intro n hn
          obtain ⟨h1, h2, h3, h4⟩ := inIndexSet_iff_le.mp hn.1
          rw [lcL]
          exact max_le (max_le h1 h2) (max_le h3 h4)
        by_cases hex : ∃ n, lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
        · obtain ⟨n₀, hn₀⟩ := hex
          have hB₀L : B₀ ≤ lcL l₁ l₂ k₁ k₂ := le_trans hB₀B (le_of_lt hLs)
          have hcollapse : lcL l₁ l₂ k₁ k₂
              ≤ 2 * Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) :=
            (hWinB l₁ l₂ k₁ k₂ (Nat.floor (a n₀)) hn₀.1 hB₀L).2
          set t : ℝ := (2 : ℝ) ^ (-(2 : ℝ) ^ (((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ) / (C₀ : ℝ) - 2)) with htdef
          set Cc : ℝ := 2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)) * t with hCcdef
          have hmod := hC₂ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hcase hf hg hcollapse
          have hsum : (∑' n : ℕ, if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n then
                ENNReal.ofReal ((scaleSeq a n)⁻¹) else 0) ≤ ENNReal.ofReal Cc := by
            rw [hCcdef, ENNReal.ofReal_mul hq0le]
            have h := lowSmallErrSum C₀ hC₀ Λ hΛ a ha ha1
              (fun n => lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n) (lcL l₁ l₂ k₁ k₂) h2C₀L hcond
            simpa only [scaleSeq, htdef] using h
          have herr : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
                (colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                  - lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))) 1 Measure.count
              ≤ 3 * (ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂)
                  * ENNReal.ofReal Cc
                  * (eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count)) := by
            refine eLpNorm_variationalNorm_le_of_termwise_low hr1
              (P := fun n => lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n)
              (u := fun n x => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
              (w := Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂)
              (N := scaleSeq a)
              (E := eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count)
              (C := Cc) ?_ ?_ ?_
            · intro n hn
              funext x
              rw [colSmall_eq_zero_of_not ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hn,
                lowModel_eq_zero_of_not ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hn]
              simp
            · intro n hn
              have h := happrox Λ a l₁ l₂ k₁ k₂ n f g hcase hf hg hΛ ha ha1 hn (hmainReg n hn)
                (hWinB l₁ l₂ k₁ k₂ (Nat.floor (a n)) hn.1 hB₀L).1 hcollapse
              simpa only [scaleSeq, mul_assoc] using h
            · exact hsum
          have hreal : Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂
                * (2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)) * t)
              ≤ 2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)) * lcWeight c l₁ l₂ k₁ k₂ := by
            have hmt : Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂ * t
                ≤ lcWeight c l₁ l₂ k₁ k₂ := by
              rw [htdef, modelWeight_eq_lcL A ρ l₁ l₂ k₁ k₂, lcWeight_eq_lcL, mul_comm]
              exact hB₂ (lcL l₁ l₂ k₁ k₂) hB₂L
            calc Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂
                  * (2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)) * t)
                = 2 * ((Λ : ℝ) / ((Λ : ℝ) - 1))
                  * (Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂ * t) := by ring
              _ ≤ 2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)) * lcWeight c l₁ l₂ k₁ k₂ :=
                  mul_le_mul_of_nonneg_left hmt hq0le
          have hmw : (0 : ℝ) ≤ Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂ :=
            Work.KMTAreas.A7.modelWeight_nonneg A ρ hA l₁ l₂ k₁ k₂
          have hfac : ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂)
                * ENNReal.ofReal Cc
              ≤ ENNReal.ofReal (2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)))
                * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂) := by
            rw [hCcdef, ← ENNReal.ofReal_mul hmw, ← ENNReal.ofReal_mul hq0le]
            exact ENNReal.ofReal_le_ofReal hreal
          have h3q : ((3 * q : NNReal) : ENNReal)
              = 3 * ENNReal.ofReal (2 * ((Λ : ℝ) / ((Λ : ℝ) - 1))) := by
            rw [ENNReal.coe_mul, hqdef, coe_toNNReal_eq_ofReal hq0le, ENNReal.coe_ofNat]
          have herr' : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
                (colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                  - lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))) 1 Measure.count
              ≤ ((3 * q : NNReal) : ENNReal) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂)
                  * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
            refine herr.trans ?_
            have hstep1 : 3 * (ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂)
                  * ENNReal.ofReal Cc
                  * (eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count))
                ≤ 3 * (ENNReal.ofReal (2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)))
                    * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂)
                    * (eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count)) :=
              mul_le_mul' le_rfl (mul_le_mul' hfac le_rfl)
            have hstep2 : 3 * (ENNReal.ofReal (2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)))
                  * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂)
                  * (eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count))
                = ((3 * q : NNReal) : ENNReal) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂)
                  * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
              rw [h3q]; ring
            exact hstep1.trans (le_of_eq hstep2)
          have hcomb : ((C₂ Λ : ENNReal) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂)
                * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count)
              + (((3 * q : NNReal) : ENNReal) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂)
                * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count)
              = (((C₂ Λ + 3 * q : NNReal) : ENNReal) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂)
                * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count) := by
            rw [ENNReal.coe_add, add_mul, add_mul, add_mul]
          have hfinal : (((C₂ Λ + 3 * q : NNReal) : ENNReal)
                * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂)
                * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count)
              ≤ (((C₂ Λ + 3 * q + Cb Λ * K : NNReal) : ENNReal)
                * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂)
                * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count) := by
            refine mul_le_mul' (mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl) le_rfl
            exact ENNReal.coe_le_coe.mpr
              (le_add_of_nonneg_right (zero_le : (0 : NNReal) ≤ Cb Λ * K))
          have hsplit_fun : (fun x : ℤ => variationalNorm r
                (fun n : ℕ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              = (fun x : ℤ => variationalNorm r (fun n : ℕ =>
                  (lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    + (colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                      - lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)))) := by
            funext x
            congr 1
            funext n
            ring
          rw [hsplit_fun]
          refine (eLpNorm_variationalNorm_add_le_low r hr1
            (fun n x => lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            (fun n x => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
              - lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)).trans ?_
          refine (add_le_add hmod herr').trans ?_
          rw [hcomb]
          exact hfinal
        · push Not at hex
          have hzero : (fun x : ℤ => variationalNorm r
              (fun n : ℕ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) = 0 := by
            funext x
            have hz : (fun n : ℕ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
              funext n
              rw [colSmall_eq_zero_of_not ρ P C₀ a f g l₁ l₂ k₁ k₂ n x (hex n)]
              simp
            rw [hz, variationalNorm_zero_local hr1]
            simp
          rw [hzero]
          simp
    · -- ===================== `g ∉ ℓ²` =====================
      have hGtop : eLpNorm g 2 Measure.count = ⊤ := by
        by_contra hne
        exact hg (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hne))
      by_cases hF0 : eLpNorm f 2 Measure.count = 0
      · have hfz : f = 0 := eq_zero_of_eLpNorm_eq_zero hF0
        have hLHS0 : eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count = 0 := by
          rw [show (fun x : ℤ => variationalNorm r
                (fun n : ℕ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              = (fun x : ℤ => variationalNorm r
                (fun n : ℕ => colSmall ρ P C₀ a (0 : ℤ → ℂ) g l₁ l₂ k₁ k₂ n x)) from by
            funext x; rw [hfz]]
          exact eLpNorm_varNorm_colSmall_zero_left r hr1 ρ P C₀ a g l₁ l₂ k₁ k₂
        exact hLHS0.le.trans (zero_le : (0 : ENNReal) ≤ _)
      · rw [hGtop, ENNReal.mul_top (mul_ne_zero (mul_ne_zero hCne hwne) hF0)]
        exact le_top
  · -- ===================== `f ∉ ℓ²` =====================
    have hFtop : eLpNorm f 2 Measure.count = ⊤ := by
      by_contra hne
      exact hf (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hne))
    by_cases hG0 : eLpNorm g 2 Measure.count = 0
    · have hgz : g = 0 := eq_zero_of_eLpNorm_eq_zero hG0
      have hLHS0 : eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count = 0 := by
        rw [show (fun x : ℤ => variationalNorm r
              (fun n : ℕ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
            = (fun x : ℤ => variationalNorm r
              (fun n : ℕ => colSmall ρ P C₀ a f (0 : ℤ → ℂ) l₁ l₂ k₁ k₂ n x)) from by
          funext x; rw [hgz]]
        exact eLpNorm_varNorm_colSmall_zero_right r hr1 ρ P C₀ a f l₁ l₂ k₁ k₂
      exact hLHS0.le.trans (zero_le : (0 : ENNReal) ≤ _)
    · rw [hFtop, ENNReal.mul_top (mul_ne_zero hCne hwne), ENNReal.top_mul hG0]
      exact le_top


open MeasureTheory Polynomial Finset Filter Topology in
open scoped ENNReal NNReal BigOperators in
/-- **`Work.KMTPlan.A6.LcSmall`**, the small-scale half of the low case of area A6. -/
theorem lowSmallScaled (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : ℝ≥0) (hr : 2 < r)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    Work.KMTPlan.A6.LcSmall P r C₀ :=
  lowSmallScaled_of_approx P hd r hr hA1 hI C₀ hC₀
    (fun ρ hρ hρ1 => lowSmallModelApprox P hd ρ hρ hρ1 C₀ hC₀)
    (fun ρ hρ hρC => lowSmallWindowCondsStrict ρ hρ C₀ hC₀ hρC)

end

end Work.KMTPlan.A6
