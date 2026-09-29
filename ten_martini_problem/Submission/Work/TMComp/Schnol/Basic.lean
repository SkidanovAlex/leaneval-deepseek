import Mathlib
import Submission.Work.TMComp.Schnol.Defs

/-!
# Component C15 (`P_Schnol`): elementary lemmas

Self-adjointness of the almost Mathieu operator (from its coordinate formula), the
pigeonhole step of the finite-volume argument, and the orthonormal-basis facts used to
diagonalise the Dirichlet truncation.
-/

open scoped ENNReal
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Schnol

/-! ## 1. Summability of products of square-summable sequences -/

theorem summable_sq_of_memℓp (u : EllTwo) : Summable fun n : ℤ => ‖u n‖ ^ 2 := by
  have h := (lp.memℓp u).summable (p := 2) (by norm_num)
  simpa using h

theorem summable_sq_shift (u : EllTwo) (k : ℤ) : Summable fun n : ℤ => ‖u (n + k)‖ ^ 2 :=
  (Equiv.summable_iff (Equiv.addRight k)).2 (summable_sq_of_memℓp u)

theorem summable_sq_sub (u : EllTwo) (k : ℤ) : Summable fun n : ℤ => ‖u (n - k)‖ ^ 2 := by
  simpa only [sub_eq_add_neg] using summable_sq_shift u (-k)

theorem summable_mul_of_summable_sq (f g : ℤ → ℂ)
    (hf : Summable fun n => ‖f n‖ ^ 2) (hg : Summable fun n => ‖g n‖ ^ 2) :
    Summable fun n => f n * g n := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((hf.add hg).mul_left (1 / 2))
  rw [norm_mul]
  nlinarith [sq_nonneg (‖f n‖ - ‖g n‖)]

/-! ## 2. Self-adjointness of the almost Mathieu operator -/

theorem selfAdjointAMO (α lam θ : ℝ) {H : EllTwo →L[ℂ] EllTwo}
    (hH : IsAlmostMathieuOperator α lam θ H) : IsSelfAdjoint H := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  set c : ℤ → ℂ := fun n => ((2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α)) : ℝ) : ℂ)
    with hcdef
  have hc : ∀ n : ℤ, starRingEnd ℂ (c n) = c n := fun n => by
    rw [hcdef]; exact Complex.conj_ofReal _
  have hHu : ∀ n : ℤ, (H u) n = u (n + 1) + u (n - 1) + c n * u n := by
    intro n
    rw [hH u n]
    congr 1
    rw [hcdef]
    push_cast
    ring
  have hHv : ∀ n : ℤ, (H v) n = v (n + 1) + v (n - 1) + c n * v n := by
    intro n
    rw [hH v n]
    congr 1
    rw [hcdef]
    push_cast
    ring
  have key1 : ∀ n : ℤ, inner ℂ ((H u) n) (v n)
      = starRingEnd ℂ (u (n + 1)) * v n + starRingEnd ℂ (u (n - 1)) * v n
        + starRingEnd ℂ (u n) * (c n * v n) := by
    intro n
    simp only [hHu n, RCLike.inner_apply', map_add, map_mul, hc n]
    ring
  have key2 : ∀ n : ℤ, inner ℂ (u n) ((H v) n)
      = starRingEnd ℂ (u n) * v (n + 1) + starRingEnd ℂ (u n) * v (n - 1)
        + starRingEnd ℂ (u n) * (c n * v n) := by
    intro n
    simp only [hHv n, RCLike.inner_apply', mul_add, mul_add]
  have hu2 : Summable fun n : ℤ => ‖u n‖ ^ 2 := summable_sq_of_memℓp u
  have hv2 : Summable fun n : ℤ => ‖v n‖ ^ 2 := summable_sq_of_memℓp v
  have hush1 : Summable fun n : ℤ => ‖starRingEnd ℂ (u (n + 1))‖ ^ 2 := by
    simpa using summable_sq_shift u 1
  have hushm1 : Summable fun n : ℤ => ‖starRingEnd ℂ (u (n - 1))‖ ^ 2 := by
    simpa using summable_sq_sub u 1
  have hv1 : Summable fun n : ℤ => ‖v (n + 1)‖ ^ 2 := summable_sq_shift v 1
  have hvm1 : Summable fun n : ℤ => ‖v (n - 1)‖ ^ 2 := summable_sq_sub v 1
  have hc_bound : ∀ n : ℤ, ‖c n‖ ≤ 2 * |lam| := by
    intro n
    rw [hcdef, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))| ≤ 1 := Real.abs_cos_le_one _
    calc |2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))|
        = 2 * |lam| * |Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))| := by
          rw [abs_mul, abs_mul]; norm_num
      _ ≤ 2 * |lam| * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * |lam| := by ring
  have hcv2 : Summable fun n : ℤ => ‖c n * v n‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hv2.mul_left ((2 * |lam|) ^ 2))
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hc_bound n) 2) (by positivity)
  have hsumA : Summable fun n : ℤ => starRingEnd ℂ (u (n + 1)) * v n :=
    summable_mul_of_summable_sq _ _ hush1 hv2
  have hsumB : Summable fun n : ℤ => starRingEnd ℂ (u (n - 1)) * v n :=
    summable_mul_of_summable_sq _ _ hushm1 hv2
  have hsumC : Summable fun n : ℤ => starRingEnd ℂ (u n) * (c n * v n) :=
    summable_mul_of_summable_sq _ _ (by simpa using hu2) hcv2
  have hsumA' : Summable fun n : ℤ => starRingEnd ℂ (u n) * v (n + 1) :=
    summable_mul_of_summable_sq _ _ (by simpa using hu2) hv1
  have hsumB' : Summable fun n : ℤ => starRingEnd ℂ (u n) * v (n - 1) :=
    summable_mul_of_summable_sq _ _ (by simpa using hu2) hvm1
  have hA'B : (∑' n : ℤ, starRingEnd ℂ (u n) * v (n + 1))
      = ∑' b : ℤ, starRingEnd ℂ (u (b - 1)) * v b := by
    have h := Equiv.tsum_eq (Equiv.addRight (1 : ℤ))
      (fun b : ℤ => starRingEnd ℂ (u (b - 1)) * v b)
    simpa using h
  have hB'A : (∑' n : ℤ, starRingEnd ℂ (u n) * v (n - 1))
      = ∑' b : ℤ, starRingEnd ℂ (u (b + 1)) * v b := by
    have h := Equiv.tsum_eq (Equiv.addRight (-1 : ℤ))
      (fun b : ℤ => starRingEnd ℂ (u (b + 1)) * v b)
    simpa [sub_eq_add_neg, Equiv.coe_addRight] using h
  have lhs_e : (∑' n : ℤ, (starRingEnd ℂ (u (n + 1)) * v n + starRingEnd ℂ (u (n - 1)) * v n
        + starRingEnd ℂ (u n) * (c n * v n)))
      = (∑' n : ℤ, starRingEnd ℂ (u (n + 1)) * v n)
        + (∑' n : ℤ, starRingEnd ℂ (u (n - 1)) * v n)
        + (∑' n : ℤ, starRingEnd ℂ (u n) * (c n * v n)) := by
    rw [Summable.tsum_add (hsumA.add hsumB) hsumC, Summable.tsum_add hsumA hsumB]
  have rhs_e : (∑' n : ℤ, (starRingEnd ℂ (u n) * v (n + 1) + starRingEnd ℂ (u n) * v (n - 1)
        + starRingEnd ℂ (u n) * (c n * v n)))
      = (∑' n : ℤ, starRingEnd ℂ (u n) * v (n + 1))
        + (∑' n : ℤ, starRingEnd ℂ (u n) * v (n - 1))
        + (∑' n : ℤ, starRingEnd ℂ (u n) * (c n * v n)) := by
    rw [Summable.tsum_add (hsumA'.add hsumB') hsumC, Summable.tsum_add hsumA' hsumB']
  have hEE' : (∑' n : ℤ, (starRingEnd ℂ (u (n + 1)) * v n + starRingEnd ℂ (u (n - 1)) * v n
        + starRingEnd ℂ (u n) * (c n * v n)))
      = (∑' n : ℤ, (starRingEnd ℂ (u n) * v (n + 1) + starRingEnd ℂ (u n) * v (n - 1)
        + starRingEnd ℂ (u n) * (c n * v n))) := by
    rw [lhs_e, rhs_e, hA'B, hB'A]
    ring
  exact ((lp.inner_eq_tsum (H u) v).trans (tsum_congr (fun n => key1 n))).trans
    (hEE'.trans ((tsum_congr (fun n => key2 n)).symm.trans (lp.inner_eq_tsum u (H v)).symm))

/-! ## 3. The pigeonhole step -/

theorem pigeonhole {n : ℕ} (a b : Fin n → ℝ) (G : Finset (Fin n)) {c : ℝ} (hc : 0 < c)
    (h1 : 3 / 4 ≤ ∑ j ∈ G, a j) (h2 : c * (∑ j, b j) ≤ 1 / 2)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    ∃ j ∈ G, c * b j ≤ a j ∧ 0 < a j := by
  by_contra hcon
  have hle : ∀ j ∈ G, a j ≤ c * b j := by
    intro j hj
    by_cases h0 : a j ≤ 0
    · have := ha j; have := hb j; nlinarith
    · have hnot : ¬ (c * b j ≤ a j) := fun hh => hcon ⟨j, hj, hh, not_le.mp h0⟩
      linarith [not_le.mp hnot]
  have hsum_le : (∑ j ∈ G, a j) ≤ c * ∑ j ∈ G, b j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hle
  have hsumG : (∑ j ∈ G, b j) ≤ ∑ j, b j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G) (fun j _ _ => hb j)
  have hcb : c * (∑ j ∈ G, b j) ≤ c * (∑ j, b j) :=
    mul_le_mul_of_nonneg_left hsumG hc.le
  linarith [h1, hsum_le, hcb, h2]

/-! ## 4. Orthonormal basis facts -/

theorem onbFacts {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (x : EuclideanSpace ℂ (Fin n)) :
    (∑ j, ‖inner ℂ (b j) x‖ ^ 2 = ‖x‖ ^ 2) ∧
    (∀ m : Fin n, ∑ j, ‖(b j).ofLp m‖ ^ 2 = 1) ∧
    (x = ∑ j, inner ℂ (b j) x • b j) := by
  refine ⟨OrthonormalBasis.sum_sq_norm_inner_right b x, ?_, (b.sum_repr' x).symm⟩
  intro m
  have h := OrthonormalBasis.sum_sq_norm_inner_right b (EuclideanSpace.single m (1 : ℂ))
  have h1 : ‖EuclideanSpace.single m (1 : ℂ)‖ ^ 2 = 1 := by
    rw [PiLp.norm_single]
    simp
  rw [h1] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.inner_single_right]
  simp

end Work.TMComp.Schnol
