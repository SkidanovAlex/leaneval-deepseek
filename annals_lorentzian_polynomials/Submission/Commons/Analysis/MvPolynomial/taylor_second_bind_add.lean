import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

namespace Commons.Analysis.MvPolynomial

set_option autoImplicit false

open scoped BigOperators

noncomputable section

/-! ## Homogeneous components and products with a variable -/

/-- Removing one unit from the `i`-coordinate of a nonzero exponent lowers the degree by 1. -/
private lemma finsupp_deg_sub_single {σ : Type*} (m : σ →₀ ℕ) (i : σ) (hi : i ∈ m.support) :
    (m - Finsupp.single i 1).degree = m.degree - 1 := by
  have hcancel : m - Finsupp.single i 1 + Finsupp.single i 1 = m :=
    Finsupp.sub_add_single_one_cancel (by simpa [Finsupp.mem_support_iff] using hi)
  have hdeg : m.degree = (m - Finsupp.single i 1).degree + 1 := by
    rw [← hcancel]
    rw [map_add]
    simp
  omega

/-- Multiplying a polynomial by a single variable raises each homogeneous component
by one. -/
private lemma homogeneousComponent_mul_X (n : ℕ) (q : MvPolynomial (Fin n) ℝ) (k : ℕ) (i : Fin n) :
    MvPolynomial.homogeneousComponent (k + 1) (q * MvPolynomial.X i) =
      MvPolynomial.homogeneousComponent k q * MvPolynomial.X i := by
  ext m
  by_cases hi : i ∈ m.support
  · have hd : (m - Finsupp.single i 1).degree = m.degree - 1 := finsupp_deg_sub_single m i hi
    rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_mul_X', if_pos hi]
    rw [MvPolynomial.coeff_mul_X', if_pos hi, MvPolynomial.coeff_homogeneousComponent]
    by_cases h1 : m.degree = k + 1
    · have h2 : (m - Finsupp.single i 1).degree = k := by omega
      simp [h1, h2]
    · have h2 : ¬ (m - Finsupp.single i 1).degree = k := by
        intro hk
        have hge : 1 ≤ m.degree := by
          have hmi : 0 < m i := Nat.pos_of_ne_zero (by simpa [Finsupp.mem_support_iff] using hi)
          exact le_trans (Nat.succ_le_of_lt hmi) (Finsupp.le_degree i m)
        omega
      simp [h1, h2]
  · simp [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_mul_X', hi]

/-- The degree-zero homogeneous component of `q * X i` vanishes. -/
private lemma homogeneousComponent_zero_mul_X (n : ℕ) (q : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    MvPolynomial.homogeneousComponent 0 (q * MvPolynomial.X i) = 0 := by
  ext m
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_mul_X']
  by_cases hm : m.degree = 0
  · have mz : m = 0 := (Finsupp.degree_eq_zero_iff m).mp hm
    subst m
    simp
  · simp [hm]

/-- Constants have zero `k`-th homogeneous component for `k ≠ 0`. -/
private lemma homogeneousComponent_C_of_pos (n : ℕ) (r : ℝ) {k : ℕ} (hk : k ≠ 0) :
    MvPolynomial.homogeneousComponent k (MvPolynomial.C r : MvPolynomial (Fin n) ℝ) = 0 := by
  apply MvPolynomial.homogeneousComponent_eq_zero'
  intro d hd hdeg
  have hd0 : d = 0 := by
    by_contra hd0
    have hz : MvPolynomial.coeff d (MvPolynomial.C r : MvPolynomial (Fin n) ℝ) = 0 := by
      rw [MvPolynomial.coeff_C]
      exact if_neg (fun h : 0 = d => hd0 h.symm)
    exact (MvPolynomial.mem_support_iff.mp hd) hz
  rw [hd0] at hdeg
  simp at hdeg
  exact hk hdeg.symm

/-! ## Taylor components of the shifted polynomial -/

/-- the shift `X_i ↦ X_i + w_i` -/
private abbrev shift (n : ℕ) (w : Fin n → ℝ) : Fin n → MvPolynomial (Fin n) ℝ :=
  fun i => MvPolynomial.X i + MvPolynomial.C (w i)

private lemma shift_mul_X (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    MvPolynomial.bind₁ (shift n w) (p * MvPolynomial.X i)
      = MvPolynomial.bind₁ (shift n w) p * (MvPolynomial.X i + MvPolynomial.C (w i)) := by
  rw [map_mul, MvPolynomial.bind₁_X_right]

private lemma hc_shift_mul_X (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (k : ℕ) (i : Fin n) :
    MvPolynomial.homogeneousComponent (k + 1)
        (MvPolynomial.bind₁ (shift n w) p * MvPolynomial.X i) =
      MvPolynomial.homogeneousComponent k
        (MvPolynomial.bind₁ (shift n w) p) * MvPolynomial.X i := by
  exact homogeneousComponent_mul_X n (MvPolynomial.bind₁ (shift n w) p) k i

private lemma hc0_shift_mul_X (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    MvPolynomial.homogeneousComponent 0
        (MvPolynomial.bind₁ (shift n w) (p * MvPolynomial.X i)) =
      MvPolynomial.C (w i) * MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) p) := by
  calc
    MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) (p * MvPolynomial.X i))
        = MvPolynomial.homogeneousComponent 0
            (MvPolynomial.bind₁ (shift n w) p * (MvPolynomial.X i + MvPolynomial.C (w i))) := by
            rw [shift_mul_X]
    _ = MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) p * MvPolynomial.X i)
          + MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) p * MvPolynomial.C (w i)) := by
          rw [mul_add]
          simp [map_add]
    _ = 0 + MvPolynomial.homogeneousComponent 0 (MvPolynomial.C (w i) * MvPolynomial.bind₁ (shift n w) p) := by
          rw [homogeneousComponent_zero_mul_X n (MvPolynomial.bind₁ (shift n w) p) i]
          congr 1
          rw [mul_comm]
    _ = MvPolynomial.C (w i) * MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) p) := by
          rw [zero_add]
          rw [MvPolynomial.homogeneousComponent_C_mul]

private lemma hc1_shift_mul_X (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    MvPolynomial.homogeneousComponent 1
        (MvPolynomial.bind₁ (shift n w) (p * MvPolynomial.X i)) =
      MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) p) * MvPolynomial.X i
        + MvPolynomial.C (w i) * MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) p) := by
  calc
    MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) (p * MvPolynomial.X i))
        = MvPolynomial.homogeneousComponent 1
            (MvPolynomial.bind₁ (shift n w) p * (MvPolynomial.X i + MvPolynomial.C (w i))) := by
            rw [shift_mul_X]
    _ = MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) p * MvPolynomial.X i)
          + MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) p * MvPolynomial.C (w i)) := by
          rw [mul_add]
          simp [map_add]
    _ = MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) p) * MvPolynomial.X i
          + MvPolynomial.homogeneousComponent 1 (MvPolynomial.C (w i) * MvPolynomial.bind₁ (shift n w) p) := by
          rw [hc_shift_mul_X n w p 0 i]
          congr 1
          rw [mul_comm]
    _ = MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) p) * MvPolynomial.X i
          + MvPolynomial.C (w i) * MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) p) := by
          rw [MvPolynomial.homogeneousComponent_C_mul]

private lemma hc2_shift_mul_X (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    MvPolynomial.homogeneousComponent 2
        (MvPolynomial.bind₁ (shift n w) (p * MvPolynomial.X i)) =
      MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) p) * MvPolynomial.X i
        + MvPolynomial.C (w i) * MvPolynomial.homogeneousComponent 2 (MvPolynomial.bind₁ (shift n w) p) := by
  calc
    MvPolynomial.homogeneousComponent 2 (MvPolynomial.bind₁ (shift n w) (p * MvPolynomial.X i))
        = MvPolynomial.homogeneousComponent 2
            (MvPolynomial.bind₁ (shift n w) p * (MvPolynomial.X i + MvPolynomial.C (w i))) := by
            rw [shift_mul_X]
    _ = MvPolynomial.homogeneousComponent 2 (MvPolynomial.bind₁ (shift n w) p * MvPolynomial.X i)
          + MvPolynomial.homogeneousComponent 2 (MvPolynomial.bind₁ (shift n w) p * MvPolynomial.C (w i)) := by
          rw [mul_add]
          simp [map_add]
    _ = MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) p) * MvPolynomial.X i
          + MvPolynomial.homogeneousComponent 2 (MvPolynomial.C (w i) * MvPolynomial.bind₁ (shift n w) p) := by
          rw [hc_shift_mul_X n w p 1 i]
          congr 1
          rw [mul_comm]
    _ = MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) p) * MvPolynomial.X i
          + MvPolynomial.C (w i) * MvPolynomial.homogeneousComponent 2 (MvPolynomial.bind₁ (shift n w) p) := by
          rw [MvPolynomial.homogeneousComponent_C_mul]

/-! ## The three explicit Taylor components -/

/-- degree-zero Taylor component: `g ↦ g(w)` -/
private abbrev T0 (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (MvPolynomial.eval w p)

/-- degree-one Taylor component: `g ↦ ∑ a (∂a g)(w) Xa` -/
private abbrev T1 (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p)) * MvPolynomial.X a

/-- degree-two Taylor component: `g ↦ (1/2) ∑ a b (∂a∂b g)(w) Xa Xb` -/
private abbrev T2 (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (1 / 2 : ℝ) *
    (∑ a : Fin n, ∑ b : Fin n,
      MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p))) *
        MvPolynomial.X a * MvPolynomial.X b)

/-! ### constant behaviour -/

private lemma T0_C (n : ℕ) (w : Fin n → ℝ) (r : ℝ) : T0 n w (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [T0]

private lemma T1_C (n : ℕ) (w : Fin n → ℝ) (r : ℝ) : T1 n w (MvPolynomial.C r) = 0 := by
  unfold T1
  rw [Finset.sum_eq_zero]
  intro a ha
  simp

private lemma T2_C (n : ℕ) (w : Fin n → ℝ) (r : ℝ) : T2 n w (MvPolynomial.C r) = 0 := by
  unfold T2
  rw [show (∑ a : Fin n, ∑ b : Fin n,
        MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b (MvPolynomial.C r))))
          * MvPolynomial.X a * MvPolynomial.X b) = 0 by
      rw [Finset.sum_eq_zero]
      intro a ha
      rw [Finset.sum_eq_zero]
      intro b hb
      simp]
  simp

/-! ### additivity -/

private lemma T0_add (n : ℕ) (w : Fin n → ℝ) (p q : MvPolynomial (Fin n) ℝ) :
    T0 n w (p + q) = T0 n w p + T0 n w q := by
  simp [T0, map_add]

private lemma T1_add (n : ℕ) (w : Fin n → ℝ) (p q : MvPolynomial (Fin n) ℝ) :
    T1 n w (p + q) = T1 n w p + T1 n w q := by
  unfold T1
  calc
    (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (p + q))) * MvPolynomial.X a)
        = ∑ a : Fin n, (MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p))
            + MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a q))) * MvPolynomial.X a := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [map_add]
            rw [map_add]
            rw [map_add]
    _ = (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p)) * MvPolynomial.X a)
          + (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a q)) * MvPolynomial.X a) := by
          simp only [add_mul, Finset.sum_add_distrib]

private lemma T2_add (n : ℕ) (w : Fin n → ℝ) (p q : MvPolynomial (Fin n) ℝ) :
    T2 n w (p + q) = T2 n w p + T2 n w q := by
  unfold T2
  calc
    MvPolynomial.C (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n,
        MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b (p + q)))) * MvPolynomial.X a * MvPolynomial.X b)
      = MvPolynomial.C (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n,
          (MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p)))
            + MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b q))))
            * MvPolynomial.X a * MvPolynomial.X b) := by
          congr 1
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          rw [map_add]
          rw [map_add]
          rw [map_add]
          rw [map_add]
    _ = MvPolynomial.C (1 / 2 : ℝ) *
          ((∑ a : Fin n, ∑ b : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p))) * MvPolynomial.X a * MvPolynomial.X b)
          + (∑ a : Fin n, ∑ b : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b q))) * MvPolynomial.X a * MvPolynomial.X b)) := by
          congr 1
          simp only [add_mul, Finset.sum_add_distrib]
    _ = MvPolynomial.C (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p))) * MvPolynomial.X a * MvPolynomial.X b)
        + MvPolynomial.C (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b q))) * MvPolynomial.X a * MvPolynomial.X b) := by
          rw [mul_add]

/-! ### product with a variable -/

private lemma T0_mul_X (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    T0 n w (p * MvPolynomial.X i) = MvPolynomial.C (w i) * T0 n w p := by
  unfold T0
  rw [map_mul]
  simp
  rw [mul_comm]

private lemma R1S1 (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p * MvPolynomial.X i)) * MvPolynomial.X a)
      = MvPolynomial.C (w i) * (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p)) * MvPolynomial.X a) := by
  calc
    (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p * MvPolynomial.X i)) * MvPolynomial.X a)
        = ∑ a : Fin n, MvPolynomial.C (w i) * (MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p)) * MvPolynomial.X a) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [map_mul]
            simp
            ring
    _ = MvPolynomial.C (w i) * (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p)) * MvPolynomial.X a) := by
            rw [Finset.mul_sum]

private lemma R1S2 (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (p * MvPolynomial.pderiv a (MvPolynomial.X i))) * MvPolynomial.X a)
      = MvPolynomial.C (MvPolynomial.eval w p) * MvPolynomial.X i := by
  rw [Finset.sum_eq_single i]
  · rw [MvPolynomial.pderiv_X_self]
    simp
  · intro b hb hbi
    rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hbi)]
    simp
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

private lemma T1_mul_X (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    T1 n w (p * MvPolynomial.X i) = T0 n w p * MvPolynomial.X i + MvPolynomial.C (w i) * T1 n w p := by
  unfold T1 T0
  calc
    (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (p * MvPolynomial.X i))) * MvPolynomial.X a)
      = ∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p * MvPolynomial.X i + p * MvPolynomial.pderiv a (MvPolynomial.X i))) * MvPolynomial.X a := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [MvPolynomial.pderiv_mul]
    _ = ∑ a : Fin n, (MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p * MvPolynomial.X i))
            + MvPolynomial.C (MvPolynomial.eval w (p * MvPolynomial.pderiv a (MvPolynomial.X i)))) * MvPolynomial.X a := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [map_add]
          rw [map_add]
    _ = (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p * MvPolynomial.X i)) * MvPolynomial.X a)
          + (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (p * MvPolynomial.pderiv a (MvPolynomial.X i))) * MvPolynomial.X a) := by
          simp only [add_mul, Finset.sum_add_distrib]
    _ = MvPolynomial.C (w i) * (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p)) * MvPolynomial.X a)
          + MvPolynomial.C (MvPolynomial.eval w p) * MvPolynomial.X i := by
          rw [R1S1 n w p i, R1S2 n w p i]
    _ = MvPolynomial.C (MvPolynomial.eval w p) * MvPolynomial.X i + MvPolynomial.C (w i) * T1 n w p := by
          rw [add_comm]

/-- second derivative of `p * X_i` splits into three terms -/
private lemma pair_expand (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (a b i : Fin n) :
    MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b (p * MvPolynomial.X i))))
        * MvPolynomial.X a * MvPolynomial.X b
      = MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p) * MvPolynomial.X i))
            * MvPolynomial.X a * MvPolynomial.X b
        + MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv b p * MvPolynomial.pderiv a (MvPolynomial.X i)))
            * MvPolynomial.X a * MvPolynomial.X b
        + MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p * MvPolynomial.pderiv b (MvPolynomial.X i)))
            * MvPolynomial.X a * MvPolynomial.X b := by
  have h1 : MvPolynomial.pderiv a (MvPolynomial.pderiv b (p * MvPolynomial.X i))
      = MvPolynomial.pderiv a (MvPolynomial.pderiv b p) * MvPolynomial.X i
        + MvPolynomial.pderiv b p * MvPolynomial.pderiv a (MvPolynomial.X i)
        + MvPolynomial.pderiv a p * MvPolynomial.pderiv b (MvPolynomial.X i) := by
    have hX : MvPolynomial.pderiv a (MvPolynomial.pderiv b (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)) = 0 := by
      by_cases h : b = i
      · subst b
        rw [MvPolynomial.pderiv_X_self]
        rw [MvPolynomial.pderiv_one]
      · have hne : i ≠ b := Ne.symm h
        rw [MvPolynomial.pderiv_X_of_ne hne]
        simp
    rw [MvPolynomial.pderiv_mul]
    rw [map_add]
    rw [MvPolynomial.pderiv_mul]
    rw [MvPolynomial.pderiv_mul]
    rw [hX]
    rw [mul_zero]
    rw [add_zero]
  rw [h1]
  simp [map_add, add_mul]

private lemma S1_factor (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n,
      MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p) * MvPolynomial.X i))
        * MvPolynomial.X a * MvPolynomial.X b)
      = MvPolynomial.C (w i) *
          (∑ a : Fin n, ∑ b : Fin n,
            MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p)))
              * MvPolynomial.X a * MvPolynomial.X b) := by
  calc
    (∑ a : Fin n, ∑ b : Fin n,
      MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p) * MvPolynomial.X i))
        * MvPolynomial.X a * MvPolynomial.X b)
      = ∑ a : Fin n, ∑ b : Fin n,
          MvPolynomial.C (w i) *
            (MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p)))
              * MvPolynomial.X a * MvPolynomial.X b) := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          rw [map_mul]
          simp
          ring
    _ = MvPolynomial.C (w i) *
          (∑ a : Fin n, ∑ b : Fin n,
            MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p)))
              * MvPolynomial.X a * MvPolynomial.X b) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]

private lemma S2_collapse (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n,
      MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv b p * MvPolynomial.pderiv a (MvPolynomial.X i)))
        * MvPolynomial.X a * MvPolynomial.X b)
      = MvPolynomial.X i * (∑ b : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv b p)) * MvPolynomial.X b) := by
  rw [Finset.sum_eq_single i]
  · rw [MvPolynomial.pderiv_X_self]
    calc
      (∑ b : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv b p * (1 : MvPolynomial (Fin n) ℝ))) * MvPolynomial.X i * MvPolynomial.X b)
          = ∑ b : Fin n, MvPolynomial.X i * (MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv b p)) * MvPolynomial.X b) := by
              apply Finset.sum_congr rfl
              intro b hb
              simp
              ring
      _ = MvPolynomial.X i * (∑ b : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv b p)) * MvPolynomial.X b) := by
              rw [Finset.mul_sum]
  · intro b hb hbi
    rw [Finset.sum_eq_zero]
    intro c hc
    rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hbi)]
    simp
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

private lemma S3_collapse (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n,
      MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p * MvPolynomial.pderiv b (MvPolynomial.X i)))
        * MvPolynomial.X a * MvPolynomial.X b)
      = (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p)) * MvPolynomial.X a) * MvPolynomial.X i := by
  calc
    (∑ a : Fin n, ∑ b : Fin n,
      MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p * MvPolynomial.pderiv b (MvPolynomial.X i)))
        * MvPolynomial.X a * MvPolynomial.X b)
      = ∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p)) * MvPolynomial.X a * MvPolynomial.X i := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_eq_single i]
          · rw [MvPolynomial.pderiv_X_self]
            simp
          · intro c hc hci
            rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hci)]
            simp
          · intro hi
            exact False.elim (hi (Finset.mem_univ i))
    _ = (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p)) * MvPolynomial.X a) * MvPolynomial.X i := by
          rw [Finset.sum_mul]

/-- collecting the two half-weight contributions from the cross terms -/
private lemma half_combine (n : ℕ) (w : Fin n → ℝ) (i : Fin n) (U V : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.C (1 / 2 : ℝ) * (MvPolynomial.C (w i) * U + (MvPolynomial.X i * V + V * MvPolynomial.X i))
      = MvPolynomial.C (w i) * (MvPolynomial.C (1 / 2 : ℝ) * U) + V * MvPolynomial.X i := by
  have hh : MvPolynomial.C (1 / 2 : ℝ) + MvPolynomial.C (1 / 2 : ℝ) = (1 : MvPolynomial (Fin n) ℝ) := by
    rw [← map_add (MvPolynomial.C : ℝ →+* MvPolynomial (Fin n) ℝ)]
    norm_num
  calc
    MvPolynomial.C (1 / 2 : ℝ) * (MvPolynomial.C (w i) * U + (MvPolynomial.X i * V + V * MvPolynomial.X i))
        = MvPolynomial.C (1 / 2 : ℝ) * (MvPolynomial.C (w i) * U) + MvPolynomial.C (1 / 2 : ℝ) * (MvPolynomial.X i * V + V * MvPolynomial.X i) := by
            rw [mul_add]
    _ = MvPolynomial.C (w i) * (MvPolynomial.C (1 / 2 : ℝ) * U)
          + (MvPolynomial.C (1 / 2 : ℝ) * (V * MvPolynomial.X i) + MvPolynomial.C (1 / 2 : ℝ) * (V * MvPolynomial.X i)) := by
          rw [show MvPolynomial.C (1 / 2 : ℝ) * (MvPolynomial.C (w i) * U)
                = MvPolynomial.C (w i) * (MvPolynomial.C (1 / 2 : ℝ) * U) by ring]
          rw [mul_add]
          rw [mul_comm (MvPolynomial.X i) V]
    _ = MvPolynomial.C (w i) * (MvPolynomial.C (1 / 2 : ℝ) * U) + V * MvPolynomial.X i := by
          rw [← add_mul]
          rw [hh]
          simp

private lemma T2_mul_X (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    T2 n w (p * MvPolynomial.X i) = T1 n w p * MvPolynomial.X i + MvPolynomial.C (w i) * T2 n w p := by
  calc
    T2 n w (p * MvPolynomial.X i)
      = MvPolynomial.C (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n,
          MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b (p * MvPolynomial.X i))))
            * MvPolynomial.X a * MvPolynomial.X b) := by rfl
    _ = MvPolynomial.C (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n,
          (MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p) * MvPolynomial.X i))
              * MvPolynomial.X a * MvPolynomial.X b
            + MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv b p * MvPolynomial.pderiv a (MvPolynomial.X i)))
              * MvPolynomial.X a * MvPolynomial.X b
            + MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p * MvPolynomial.pderiv b (MvPolynomial.X i)))
              * MvPolynomial.X a * MvPolynomial.X b)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          exact pair_expand n w p a b i
    _ = MvPolynomial.C (1 / 2 : ℝ) *
          ((∑ a : Fin n, ∑ b : Fin n,
            MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p) * MvPolynomial.X i))
              * MvPolynomial.X a * MvPolynomial.X b)
          + ((∑ a : Fin n, ∑ b : Fin n,
            MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv b p * MvPolynomial.pderiv a (MvPolynomial.X i)))
              * MvPolynomial.X a * MvPolynomial.X b)
            + (∑ a : Fin n, ∑ b : Fin n,
            MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p * MvPolynomial.pderiv b (MvPolynomial.X i)))
              * MvPolynomial.X a * MvPolynomial.X b))) := by
          congr 1
          simp only [Finset.sum_add_distrib]
          rw [add_assoc]
    _ = MvPolynomial.C (1 / 2 : ℝ) *
          (MvPolynomial.C (w i) *
            (∑ a : Fin n, ∑ b : Fin n,
              MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p)))
                * MvPolynomial.X a * MvPolynomial.X b)
          + (MvPolynomial.X i *
              (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p)) * MvPolynomial.X a)
            + (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p)) * MvPolynomial.X a) * MvPolynomial.X i)) := by
          rw [S1_factor n w p i, S2_collapse n w p i, S3_collapse n w p i]
    _ = MvPolynomial.C (w i) *
          (MvPolynomial.C (1 / 2 : ℝ) *
            (∑ a : Fin n, ∑ b : Fin n,
              MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p)))
                * MvPolynomial.X a * MvPolynomial.X b))
        + (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p)) * MvPolynomial.X a) * MvPolynomial.X i := by
          exact half_combine n w i
            (∑ a : Fin n, ∑ b : Fin n,
              MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p)))
                * MvPolynomial.X a * MvPolynomial.X b)
            (∑ a : Fin n, MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a p)) * MvPolynomial.X a)
    _ = MvPolynomial.C (w i) * T2 n w p + T1 n w p * MvPolynomial.X i := by
          rfl
    _ = T1 n w p * MvPolynomial.X i + MvPolynomial.C (w i) * T2 n w p := by
          rw [add_comm]

/-! ## Induction: the shifted polynomial has the stated Taylor components -/

private theorem taylor_components (n : ℕ) (g : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ) :
    MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) g) = T0 n w g ∧
    MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) g) = T1 n w g ∧
    MvPolynomial.homogeneousComponent 2 (MvPolynomial.bind₁ (shift n w) g) = T2 n w g := by
  induction g using MvPolynomial.induction_on with
  | C r =>
      constructor
      · calc
          MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) (MvPolynomial.C r))
              = MvPolynomial.homogeneousComponent 0 (MvPolynomial.C r : MvPolynomial (Fin n) ℝ) := by
                rw [MvPolynomial.bind₁_C_right]
          _ = MvPolynomial.C r := by
                rw [MvPolynomial.homogeneousComponent_zero]
                simp
          _ = T0 n w (MvPolynomial.C r) := (T0_C n w r).symm
      · constructor
        · calc
            MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) (MvPolynomial.C r))
                = MvPolynomial.homogeneousComponent 1 (MvPolynomial.C r : MvPolynomial (Fin n) ℝ) := by
                  rw [MvPolynomial.bind₁_C_right]
            _ = 0 := homogeneousComponent_C_of_pos n r (by norm_num)
            _ = T1 n w (MvPolynomial.C r) := (T1_C n w r).symm
        · calc
            MvPolynomial.homogeneousComponent 2 (MvPolynomial.bind₁ (shift n w) (MvPolynomial.C r))
                = MvPolynomial.homogeneousComponent 2 (MvPolynomial.C r : MvPolynomial (Fin n) ℝ) := by
                  rw [MvPolynomial.bind₁_C_right]
            _ = 0 := homogeneousComponent_C_of_pos n r (by norm_num)
            _ = T2 n w (MvPolynomial.C r) := (T2_C n w r).symm
  | add p q hp hq =>
      rcases hp with ⟨hp0, hp1, hp2⟩
      rcases hq with ⟨hq0, hq1, hq2⟩
      constructor
      · calc
          MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) (p + q))
              = MvPolynomial.homogeneousComponent 0
                  (MvPolynomial.bind₁ (shift n w) p + MvPolynomial.bind₁ (shift n w) q) := by
                rw [map_add]
          _ = MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) p)
              + MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) q) := by
                rw [map_add]
          _ = T0 n w p + T0 n w q := by rw [hp0, hq0]
          _ = T0 n w (p + q) := (T0_add n w p q).symm
      · constructor
        · calc
            MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) (p + q))
                = MvPolynomial.homogeneousComponent 1
                    (MvPolynomial.bind₁ (shift n w) p + MvPolynomial.bind₁ (shift n w) q) := by
                  rw [map_add]
            _ = MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) p)
                + MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) q) := by
                  rw [map_add]
            _ = T1 n w p + T1 n w q := by rw [hp1, hq1]
            _ = T1 n w (p + q) := (T1_add n w p q).symm
        · calc
            MvPolynomial.homogeneousComponent 2 (MvPolynomial.bind₁ (shift n w) (p + q))
                = MvPolynomial.homogeneousComponent 2
                    (MvPolynomial.bind₁ (shift n w) p + MvPolynomial.bind₁ (shift n w) q) := by
                  rw [map_add]
            _ = MvPolynomial.homogeneousComponent 2 (MvPolynomial.bind₁ (shift n w) p)
                + MvPolynomial.homogeneousComponent 2 (MvPolynomial.bind₁ (shift n w) q) := by
                  rw [map_add]
            _ = T2 n w p + T2 n w q := by rw [hp2, hq2]
            _ = T2 n w (p + q) := (T2_add n w p q).symm
  | mul_X p i hp =>
      rcases hp with ⟨hp0, hp1, hp2⟩
      constructor
      · calc
          MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) (p * MvPolynomial.X i))
              = MvPolynomial.C (w i) * MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) p) :=
                hc0_shift_mul_X n w p i
          _ = MvPolynomial.C (w i) * T0 n w p := by rw [hp0]
          _ = T0 n w (p * MvPolynomial.X i) := (T0_mul_X n w p i).symm
      · constructor
        · calc
            MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) (p * MvPolynomial.X i))
                = MvPolynomial.homogeneousComponent 0 (MvPolynomial.bind₁ (shift n w) p) * MvPolynomial.X i
                    + MvPolynomial.C (w i) * MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) p) :=
                  hc1_shift_mul_X n w p i
            _ = T0 n w p * MvPolynomial.X i + MvPolynomial.C (w i) * T1 n w p := by rw [hp0, hp1]
            _ = T1 n w (p * MvPolynomial.X i) := (T1_mul_X n w p i).symm
        · calc
            MvPolynomial.homogeneousComponent 2 (MvPolynomial.bind₁ (shift n w) (p * MvPolynomial.X i))
                = MvPolynomial.homogeneousComponent 1 (MvPolynomial.bind₁ (shift n w) p) * MvPolynomial.X i
                    + MvPolynomial.C (w i) * MvPolynomial.homogeneousComponent 2 (MvPolynomial.bind₁ (shift n w) p) :=
                  hc2_shift_mul_X n w p i
            _ = T1 n w p * MvPolynomial.X i + MvPolynomial.C (w i) * T2 n w p := by rw [hp1, hp2]
            _ = T2 n w (p * MvPolynomial.X i) := (T2_mul_X n w p i).symm

/-- Second-order Taylor expansion: substituting `X_i + w_i` for each variable `X_i` and
taking the degree-2 homogeneous component gives `(1/2) * sum_ab (d^2 g / dX_a dX_b)(w) X_a X_b`,
where the second derivative is evaluated at `w` (a finite Taylor expansion, valid over `ℝ`). -/
theorem taylor_second_bind_add (n : ℕ) (g : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ) :
    MvPolynomial.homogeneousComponent 2
        (MvPolynomial.bind₁ (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C (w i)) g) =
      MvPolynomial.C (1 / 2 : ℝ) *
        (∑ a : Fin n, ∑ b : Fin n,
          MvPolynomial.C (MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b g))) *
            MvPolynomial.X a * MvPolynomial.X b) := by
  simpa [shift, T2] using (taylor_components n g w).2.2

end

end Commons.Analysis.MvPolynomial