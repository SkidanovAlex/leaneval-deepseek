import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Submission.Commons.Algebra.MvPolynomial.pderiv_mem_homogeneousSubmodule

open MvPolynomial
open scoped BigOperators

namespace Commons.Algebra.MvPolynomial

noncomputable section

private abbrev P (n : ℕ) := MvPolynomial (Fin n) ℝ

private noncomputable def lap (n : ℕ) : P n → P n :=
  fun X => ∑ i : Fin n, pderiv i (pderiv i X)

private lemma pderiv_comm {n : ℕ} (i j : Fin n) (p : P n) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv]
  by_cases hij : i = j
  · subst hij
    ring
  · have hc : coeff ((m + Finsupp.single i 1) + Finsupp.single j 1) p =
        coeff ((m + Finsupp.single j 1) + Finsupp.single i 1) p := by
      congr 1
      rw [add_assoc, add_assoc]
      congr 1
      rw [add_comm (Finsupp.single i 1) (Finsupp.single j 1)]
    have h1i : (m + Finsupp.single i 1 : Fin n →₀ ℕ) j = m j := by
      simp [Finsupp.add_apply, hij]
    have h2i : (m + Finsupp.single j 1 : Fin n →₀ ℕ) i = m i := by
      simp [Finsupp.add_apply, Ne.symm hij]
    rw [hc, h1i, h2i]
    ring

private lemma lap_add {n : ℕ} (x y : P n) : lap n (x + y) = lap n x + lap n y := by
  unfold lap
  simp only [map_add]
  rw [Finset.sum_add_distrib]

private lemma lap_smul {n : ℕ} (a : ℝ) (x : P n) : lap n (a • x) = a • lap n x := by
  unfold lap
  simp
  rw [← Finset.smul_sum]

private lemma lap_pderiv {n : ℕ} (i : Fin n) (f : P n) :
    lap n (pderiv i f) = pderiv i (lap n f) := by
  unfold lap
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    pderiv j (pderiv j (pderiv i f)) = pderiv j (pderiv i (pderiv j f)) := by
      rw [pderiv_comm j i f]
    _ = pderiv i (pderiv j (pderiv j f)) := by
      exact (pderiv_comm i j (pderiv j f)).symm

private lemma pderiv2_mul {n : ℕ} (i : Fin n) (f g : P n) :
    pderiv i (pderiv i (f * g)) =
      pderiv i (pderiv i f) * g
        + (2 : ℝ) • (pderiv i f * pderiv i g)
        + f * pderiv i (pderiv i g) := by
  rw [MvPolynomial.pderiv_mul]
  rw [map_add]
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul]
  rw [two_smul ℝ (pderiv i f * pderiv i g)]
  ring

private lemma lap_mul {n : ℕ} (f g : P n) :
    lap n (f * g) =
      lap n f * g
        + (2 : ℝ) • (∑ i : Fin n, pderiv i f * pderiv i g)
        + f * lap n g := by
  unfold lap
  trans ∑ i : Fin n,
    (pderiv i (pderiv i f) * g
      + (2 : ℝ) • (pderiv i f * pderiv i g)
      + f * pderiv i (pderiv i g))
  · apply Finset.sum_congr rfl
    intro i hi
    exact pderiv2_mul i f g
  · rw [Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
    rw [← Finset.sum_mul]
    rw [← Finset.smul_sum]
    rw [← Finset.mul_sum]

private lemma lap_mul_of_harmonic {n : ℕ} (f g : P n) (hf : lap n f = 0) (hg : lap n g = 0) :
    lap n (f * g) = (2 : ℝ) • (∑ i : Fin n, pderiv i f * pderiv i g) := by
  rw [lap_mul, hf, hg]
  simp

private lemma lap_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → P n) :
    lap n (∑ i ∈ s, f i) = ∑ i ∈ s, lap n (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [lap]
  · intro a s' has' ih
    simp [has', Finset.sum_insert, lap_add, ih]

/-- `B n f g t` is the sum over all `t`-tuples of partial-derivative multi-indices of
the product of the corresponding derivatives of `f` and `g`. -/
private noncomputable def B (n : ℕ) (f g : P n) : ℕ → P n
  | 0 => f * g
  | t + 1 => ∑ i : Fin n, B n (pderiv i f) (pderiv i g) t

private lemma B_zero_left {n : ℕ} (t : ℕ) : ∀ g : P n, B n 0 g t = 0 := by
  induction t with
  | zero => intro g; simp [B]
  | succ t ih =>
      intro g
      simp [B]
      apply Finset.sum_eq_zero
      intro i hi
      exact ih (pderiv i g)

private lemma B_symm {n : ℕ} (t : ℕ) : ∀ (f g : P n), B n f g t = B n g f t := by
  induction t with
  | zero => intro f g; simp [B, mul_comm]
  | succ t ih =>
      intro f g
      change ∑ i : Fin n, B n (pderiv i f) (pderiv i g) t =
        ∑ i : Fin n, B n (pderiv i g) (pderiv i f) t
      apply Finset.sum_congr rfl
      intro i hi
      exact ih (pderiv i f) (pderiv i g)

private lemma pderiv_eq_zero_of_mem_homogeneous_zero {n : ℕ} (i : Fin n) (p : P n)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ 0) :
    pderiv i p = 0 := by
  have h' : p ∈ (1 : Submodule ℝ (P n)) := by
    simpa [MvPolynomial.homogeneousSubmodule_zero] using hp
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp h'
  rw [← hy]
  simpa using (MvPolynomial.pderiv_C (R := ℝ) (σ := Fin n) (a := y) (i := i))

/-- If `f` is homogeneous of degree `k < t`, then every term of `B n f g t`
contains a `t`-fold derivative of `f`, which vanishes. -/
private lemma B_eq_zero_of_mem_homogeneous {n : ℕ} (t : ℕ) : ∀ (f g : P n) {k : ℕ},
    k < t → f ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k → B n f g t = 0 := by
  induction t with
  | zero =>
      intro f g k hk
      omega
  | succ t ih =>
      intro f g k hk hf
      cases k with
      | zero =>
          simp [B]
          apply Finset.sum_eq_zero
          intro i hi
          have hder : pderiv i f = 0 := pderiv_eq_zero_of_mem_homogeneous_zero i f hf
          rw [hder]
          exact B_zero_left t (pderiv i g)
      | succ k =>
          simp [B]
          apply Finset.sum_eq_zero
          intro i hi
          have hder : pderiv i f ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
            simpa [Nat.add_sub_cancel] using
              (pderiv_mem_homogeneousSubmodule (n := n) (i := i) (k := k + 1) hf)
          exact ih (pderiv i f) (pderiv i g) (by omega : k < t) hder

/-- For harmonic `f g`, the Laplacian of `B n f g t` is `2 • B n f g (t+1)`. -/
private lemma lap_B (n : ℕ) (t : ℕ) : ∀ (f g : P n), lap n f = 0 → lap n g = 0 →
    lap n (B n f g t) = (2 : ℝ) • B n f g (t + 1) := by
  induction t with
  | zero =>
      intro f g hf hg
      change lap n (f * g) = (2 : ℝ) • B n f g (0 + 1)
      rw [lap_mul_of_harmonic f g hf hg]
      simp [B]
  | succ t ih =>
      intro f g hf hg
      change lap n (∑ i : Fin n, B n (pderiv i f) (pderiv i g) t) =
        (2 : ℝ) • B n f g (t + 1 + 1)
      rw [show B n f g (t + 1 + 1) = ∑ i : Fin n, B n (pderiv i f) (pderiv i g) (t + 1) by rfl]
      have hlin : lap n (∑ i : Fin n, B n (pderiv i f) (pderiv i g) t) =
          ∑ i : Fin n, lap n (B n (pderiv i f) (pderiv i g) t) := by
        simpa using (lap_sum (Finset.univ : Finset (Fin n))
          (fun i : Fin n => B n (pderiv i f) (pderiv i g) t))
      rw [hlin]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hDf : lap n (pderiv i f) = 0 := by
        rw [lap_pderiv, hf]
        simp
      have hDg : lap n (pderiv i g) = 0 := by
        rw [lap_pderiv, hg]
        simp
      exact ih (pderiv i f) (pderiv i g) hDf hDg

/-- Leibniz-type formula for the iterated Laplacian of a product of two harmonic
polynomials: `lap^[t] (f * g) = 2^t • B n f g t`. -/
private lemma iterate_lap_mul (n : ℕ) (t : ℕ) : ∀ (f g : P n), lap n f = 0 → lap n g = 0 →
    (lap n)^[t] (f * g) = (2 : ℝ) ^ t • B n f g t := by
  induction t with
  | zero =>
      intro f g hf hg
      simp [B]
  | succ t ih =>
      intro f g hf hg
      rw [Function.iterate_succ_apply']
      rw [ih f g hf hg]
      rw [lap_smul]
      rw [lap_B n t f g hf hg]
      rw [smul_smul]
      rw [pow_succ]

theorem lapIter_mul_eq_zero_of_harmonic
    {n : ℕ} {m k l : ℕ} (P Q : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hQ : Q ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ l)
    (hlapP : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0)
    (hlapQ : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) = 0)
    (hdeg : k + l = 2 * m) (hkl : k ≠ l) :
    ((fun X : MvPolynomial (Fin n) ℝ =>
        ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i X))^[m]) (P * Q) = 0 := by
  classical
  have hlapP' : lap n P = 0 := by simpa [lap] using hlapP
  have hlapQ' : lap n Q = 0 := by simpa [lap] using hlapQ
  have hmain : (lap n)^[m] (P * Q) = (2 : ℝ) ^ m • B n P Q m :=
    iterate_lap_mul n m P Q hlapP' hlapQ'
  change (lap n)^[m] (P * Q) = 0
  by_cases hkm : k < m
  · have hB : B n P Q m = 0 := B_eq_zero_of_mem_homogeneous m P Q hkm hP
    rw [hmain, hB]
    simp
  · have hlm : l < m := by omega
    have hB' : B n Q P m = 0 := B_eq_zero_of_mem_homogeneous m Q P hlm hQ
    have hB : B n P Q m = 0 := by
      rw [B_symm m P Q]
      exact hB'
    rw [hmain, hB]
    simp

end

end Commons.Algebra.MvPolynomial