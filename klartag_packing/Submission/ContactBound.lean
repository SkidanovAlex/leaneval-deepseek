import Mathlib
import Submission.Good
import Submission.Moment

/-!
# The contact estimate

For the exploration process run with the *integer* lattice `Λ = ℤ^d` (see
`Submission/PLAN_V8.md` §R2), the number of violated candidates is bounded as

    ∑_{k<K} E |violSet R BoxL A_k| ≤ K · E |violSet R BoxL A_K| ,

because a vector that is violated at some time stays violated forever: its quadratic form is
FROZEN by the constraint projection (`Submission/Rescale.quadFormV_frozen`).  This file records
the corresponding Finset monotonicity.

The remaining ingredient is the per-vector tail bound

    P(∃ k ≤ K : quadFormV A_k y ≤ 1) ≤ 8 exp(-(a₀ - 1/‖y‖²)² / (2 T)) ,   T = K ε²

which follows from `GenProc.maximal_tail_incr` applied to `W = tensorV y / ‖y‖²`, and the
elementary fact that for `y ∈ ℤ^d` the exponent is `≳ 1/(8 log d)` when `‖y‖ = 1` and
`≳ d²/(128 log d)` otherwise.
-/

namespace Submission.ContactBound

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.GenProc
open Submission.Contact
open Submission.Rescale
open Submission.OpNorm

noncomputable section

variable {d m : ℕ}

/-- The cardinality of the violated set depends on the state only through the violation
pattern. -/
def cardOf (BoxL : Fin m → Vec d) (χ : Fin m → Bool) : ℝ :=
  ((Finset.univ.filter (fun i : Fin m => χ i = true)).image BoxL).card

lemma card_violSet_eq_cardOf (R : ℝ) (BoxL : Fin m → Vec d) (A : MatV d) :
    ((violSet R BoxL A).card : ℝ) = cardOf BoxL (patt R BoxL A) := by
  have h : (Finset.univ.filter (fun i : Fin m => patt R BoxL A i = true)).image BoxL
      = violSet R BoxL A := by
    ext y
    simp only [violSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, patt,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases hh : ‖BoxL i‖ ≤ R ∧ quadFormV A (BoxL i) ≤ 1
      · exact ⟨i, hh, rfl⟩
      · simp [hh] at hi
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, by simp [hi], rfl⟩
  rw [cardOf, h]

lemma measurable_card_violSet (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ) :
    Measurable fun ω : Fin K → MatV d × MatV d =>
      ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω K)).card : ℝ) := by
  have h : (fun ω : Fin K → MatV d × MatV d =>
        ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω K)).card : ℝ))
      = (cardOf BoxL) ∘ (fun ω => patt R BoxL (proc (projL R BoxL) a₀ ε K ω K)) := by
    funext ω
    exact card_violSet_eq_cardOf R BoxL _
  rw [h]
  exact (measurable_of_finite _).comp
    ((measurable_patt R BoxL).comp
      (measurable_proc (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K)
        (measurable_projL R BoxL) K))

lemma integrable_card_violSet (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ) :
    Integrable (fun ω : Fin K → MatV d × MatV d =>
      ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω K)).card : ℝ)) (sampleLaw d K) := by
  refine MeasureTheory.Integrable.mono'
    (f := fun ω : Fin K → MatV d × MatV d =>
      ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω K)).card : ℝ))
    (g := fun _ : Fin K → MatV d × MatV d => (m : ℝ)) ?_ ?_ ?_
  · exact MeasureTheory.integrable_const _
  · exact (measurable_card_violSet R BoxL a₀ ε K).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    refine Nat.cast_le.mpr ?_
    calc (violSet R BoxL (proc (projL R BoxL) a₀ ε K ω K)).card
        ≤ (Finset.univ.filter (fun i : Fin m =>
            ‖BoxL i‖ ≤ R ∧ quadFormV (proc (projL R BoxL) a₀ ε K ω K) (BoxL i) ≤ 1)).card :=
          Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
      _ = m := by rw [Finset.card_univ, Fintype.card_fin]

/-- Once violated, always violated: the violated set is monotone in time. -/
lemma violSet_mono (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ)
    (ω : Fin K → MatV d × MatV d) {k : ℕ} (hk : k ≤ K) :
    violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)
      ⊆ violSet R BoxL (proc (projL R BoxL) a₀ ε K ω K) :=
  fun _x hx => (quadFormV_frozen R ε a₀ K BoxL ω hk le_rfl hx).1

/-- Cardinality form of the monotonicity. -/
lemma card_violSet_mono (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ)
    (ω : Fin K → MatV d × MatV d) {k : ℕ} (hk : k ≤ K) :
    (violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card
      ≤ (violSet R BoxL (proc (projL R BoxL) a₀ ε K ω K)).card :=
  Finset.card_le_card (violSet_mono R BoxL a₀ ε K ω hk)

/-- The sum of the cardinalities is dominated by `K` times the last one. -/
lemma sum_card_violSet_le (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range K, ∫ ω : Fin K → MatV d × MatV d,
        ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K))
      ≤ (K : ℝ) * ∫ ω : Fin K → MatV d × MatV d,
          ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω K)).card : ℝ) ∂(sampleLaw d K) := by
  calc (∑ k ∈ Finset.range K, ∫ ω : Fin K → MatV d × MatV d,
        ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K))
      ≤ ∑ _k ∈ Finset.range K, ∫ ω : Fin K → MatV d × MatV d,
          ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω K)).card : ℝ) ∂(sampleLaw d K) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkK : k ≤ K := Nat.le_of_lt (Finset.mem_range.mp hk)
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg _)
          (integrable_card_violSet R BoxL a₀ ε K) (Filter.Eventually.of_forall fun ω => ?_)
        exact Nat.cast_le.mpr (card_violSet_mono R BoxL a₀ ε K ω hkK)
    _ = (K : ℝ) * ∫ ω : Fin K → MatV d × MatV d,
          ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω K)).card : ℝ) ∂(sampleLaw d K) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Per-vector contact probability.**  For a fixed nonzero vector `y` with `a₀‖y‖² ≥ 1`,
the probability that `y` ever falls inside the ellipsoid `{x : quadFormV A_k x ≤ 1}` is at most
the Gaussian upper tail of `(a₀ - 1/‖y‖²)/√T`, `T = Kε²`. -/
theorem measureReal_quadFormV_le (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ)
    {y : Vec d} (hy : y ≠ 0) (hε : 0 ≤ ε) (ha₀ : 1 ≤ a₀ * ‖y‖ ^ 2) :
    (sampleLaw d K).real {ω : Fin K → MatV d × MatV d |
        ∃ k ≤ K, quadFormV (proc (projL R BoxL) a₀ ε K ω k - a₀ • oneV d) y
          ≤ 1 - a₀ * ‖y‖ ^ 2}
      ≤ 8 * Real.exp (-((a₀ - 1 / ‖y‖ ^ 2) ^ 2) / (2 * (K : ℝ) * ε ^ 2)) := by
  set W : MatV d := (‖y‖ ^ 2)⁻¹ • tensorV y with hWdef
  have hyn : (‖y‖ ^ 2) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
  have hW : ‖W‖ ≤ 1 := by
    rw [hWdef, norm_smul, Real.norm_of_nonneg (by positivity), norm_tensorV,
      inv_mul_cancel₀ hyn]
  have hrnn : 0 ≤ (a₀ * ‖y‖ ^ 2 - 1) / ‖y‖ ^ 2 :=
    div_nonneg (by linarith) (by positivity)
  have hsub : {ω : Fin K → MatV d × MatV d |
        ∃ k ≤ K, quadFormV (proc (projL R BoxL) a₀ ε K ω k - a₀ • oneV d) y
          ≤ 1 - a₀ * ‖y‖ ^ 2}
      ⊆ {ω : Fin K → MatV d × MatV d | ∃ k ≤ K,
          (a₀ * ‖y‖ ^ 2 - 1) / ‖y‖ ^ 2 ≤ |∑ j ∈ Finset.univ.filter
            (fun j : Fin K => (j : ℕ) < k),
            ε * inner ℝ (incrAt (projL R BoxL) a₀ ε K ω j) W|} := by
    rintro ω ⟨k, hk, hle⟩
    refine ⟨k, hk, ?_⟩
    have hsum := quadFormV_state_sub (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K) hk ω y
    rw [hsum] at hle
    have hkey : (a₀ * ‖y‖ ^ 2 - 1) ≤ -(∑ j ∈ Finset.univ.filter
        (fun j : Fin K => (j : ℕ) < k),
          ε * inner ℝ (incrAt (projL R BoxL) a₀ ε K ω j) (tensorV y)) := by linarith
    have hneg := hkey.trans (neg_le_abs _)
    have hscale : (∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
        ε * inner ℝ (incrAt (projL R BoxL) a₀ ε K ω j) W)
        = (‖y‖ ^ 2)⁻¹ * ∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
            ε * inner ℝ (incrAt (projL R BoxL) a₀ ε K ω j) (tensorV y) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hWdef, real_inner_smul_right]
      ring
    have habs : |∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
        ε * inner ℝ (incrAt (projL R BoxL) a₀ ε K ω j) W|
        = (‖y‖ ^ 2)⁻¹ * |∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
            ε * inner ℝ (incrAt (projL R BoxL) a₀ ε K ω j) (tensorV y)| := by
      rw [hscale, abs_mul, abs_of_nonneg (by positivity)]
    rw [habs, show (a₀ * ‖y‖ ^ 2 - 1) / ‖y‖ ^ 2
        = (‖y‖ ^ 2)⁻¹ * (a₀ * ‖y‖ ^ 2 - 1) from by rw [div_eq_inv_mul, mul_comm]]
    exact mul_le_mul_of_nonneg_left hneg (by positivity)
  refine le_trans (MeasureTheory.measureReal_mono hsub (MeasureTheory.measure_ne_top _ _)) ?_
  have hmain := maximal_tail_incr (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K)
    (measurable_projL R BoxL) (fun A => good_projL R BoxL A) W hW hε hrnn
  refine le_trans hmain ?_
  have hexp : ((a₀ * ‖y‖ ^ 2 - 1) / ‖y‖ ^ 2) ^ 2 = (a₀ - 1 / ‖y‖ ^ 2) ^ 2 := by
    congr 1
    field_simp
  rw [hexp]

end

end Submission.ContactBound
