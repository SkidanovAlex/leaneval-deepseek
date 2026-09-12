import Mathlib
import Submission.Commons.Analysis.MeasureTheory.odd_degree_homogeneous_sphere_integral_zero
import Submission.Commons.Analysis.MeasureTheory.homogeneous_even_sphere_integral_eq_const_laplacian_pow

noncomputable section
open scoped BigOperators

namespace Commons.Analysis.MeasureTheory

private lemma lapOp_zero {n : ℕ} :
    (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (0 : MvPolynomial (Fin n) ℝ))) = 0 := by
  simp

private lemma lapIter_eval_zero {n : ℕ} {P : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hr : 1 ≤ r)
    (h : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0) :
    MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
      ((fun Q : MvPolynomial (Fin n) ℝ =>
          ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q))^[r] P) = 0 := by
  let lapOp : MvPolynomial (Fin n) ℝ → MvPolynomial (Fin n) ℝ :=
    fun Q => ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)
  have hlap : lapOp P = 0 := h
  have hzero : (lapOp^[r]) P = 0 := by
    induction r with
    | zero => omega
    | succ r ih =>
        by_cases h0 : r = 0
        · subst r
          simpa [Function.iterate_one, lapOp] using hlap
        · have hr' : 1 ≤ r := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0)
          rw [Function.iterate_succ_apply']
          rw [ih hr']
          exact lapOp_zero
  change MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (lapOp^[r] P) = 0
  rw [hzero]
  simp

theorem harmonic_sphere_integral_zero
    {n : ℕ} {k : ℕ} [Nonempty (Fin n)] (hk : k ≠ 0)
    (P : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hlapP : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0) :
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P
      ∂MeasureTheory.volume.toSphere) = 0 := by
  have hnpos : 0 < n := by
    have hc : 0 < Fintype.card (Fin n) := Fintype.card_pos_iff.mpr ‹Nonempty (Fin n)›
    simpa using hc
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | hkodd
  · have hk2 : k = 2 * m := by
      rw [hm, two_mul]
    have hmpos : 0 < m := by omega
    have hPeven : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m) := by
      simpa [hk2] using hP
    obtain ⟨c, hc⟩ := homogeneous_even_sphere_integral_eq_const_laplacian_pow
      (n := n) (m := m) hnpos
    have hint := hc P hPeven
    have hzero : MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
        ((fun Q : MvPolynomial (Fin n) ℝ =>
            ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q))^[m] P) = 0 :=
      lapIter_eval_zero hmpos hlapP
    calc
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P
        ∂MeasureTheory.volume.toSphere)
          = c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
              ((fun Q : MvPolynomial (Fin n) ℝ =>
                  ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q))^[m] P) := hint
      _ = c * 0 := by rw [hzero]
      _ = 0 := by ring
  · exact odd_degree_homogeneous_sphere_integral_zero hkodd P hP

end Commons.Analysis.MeasureTheory
