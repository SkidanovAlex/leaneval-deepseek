import Submission.CDT.EulerIndicial
import Submission.CDT.ElimOperatorC

/-!
# The degree and leading coefficient of the Frobenius cascade numerator

For a polynomial `q` of degree `3` and a polynomial `p` of positive degree, the
recursive numerator `dnum p q j` of the `j`-th derivative of `p/q` satisfies

`natDegree (dnum p q j) = p.natDegree + 2j`,
`leadingCoeff (dnum p q j) = (leadingCoeff q)^j · (N)_j · leadingCoeff p`,

where `N = p.natDegree − 3` is the order of vanishing of `p/q` at infinity and
`(N)_j` is the falling factorial.  The hypothesis is that `N − k ≠ 0` for all
`k < j` (the "non-resonant" case); this is what makes the leading terms of the
cascade add up.

This is the input to the Frobenius analysis of the eliminated operator at
infinity: it computes the leading behaviour of the cleared equation `∑_j A_j
b₃^{(j)} = Δ₁⁴R` at `∞`.
-/

open Classical

noncomputable section
namespace Submission.CDT

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

lemma fallFact_cast_ne_zero {N : ℤ} {j : ℕ} (h : ∀ k : ℕ, k < j → N - (k : ℤ) ≠ 0) :
    ((fallFact N j : ℤ) : K) ≠ 0 := by
  have hz : (fallFact N j : ℤ) ≠ 0 := by
    rw [fallFact, Finset.prod_ne_zero_iff]
    intro i hi
    exact h i (Finset.mem_range.mp hi)
  exact_mod_cast hz

lemma derivative_natDegree_of_natDegree_eq_three (q : Polynomial K) (hq : q.natDegree = 3) :
    q.derivative.natDegree = 2 ∧ q.derivative.leadingCoeff = 3 * q.leadingCoeff := by
  have hq0 : q ≠ 0 := fun h => by rw [h] at hq; simp at hq
  have hc : q.derivative.coeff 2 = 3 * q.leadingCoeff := by
    rw [Polynomial.coeff_derivative]
    rw [show (2 + 1 : ℕ) = 3 from rfl, show q.coeff 3 = q.leadingCoeff from by
      rw [Polynomial.leadingCoeff, hq]]
    ring
  have hne : q.derivative.coeff 2 ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (by norm_num) (Polynomial.leadingCoeff_ne_zero.mpr hq0)
  have hle : q.derivative.natDegree ≤ 2 := by
    have := Polynomial.natDegree_derivative_le q
    omega
  have hge : 2 ≤ q.derivative.natDegree := le_natDegree_of_ne_zero hne
  refine ⟨by omega, ?_⟩
  rw [Polynomial.leadingCoeff, show q.derivative.natDegree = 2 from by omega, hc]

theorem dnum_natDegree_leadingCoeff (p q : Polynomial K) (hq : q.natDegree = 3)
    (hp : p.natDegree ≠ 0) (j : ℕ)
    (hN : ∀ k : ℕ, k < j → ((p.natDegree : ℤ) - 3 - (k : ℤ)) ≠ 0) :
    (dnum p q j).natDegree = p.natDegree + 2 * j ∧
    (dnum p q j).leadingCoeff
      = q.leadingCoeff ^ j * ((fallFact ((p.natDegree : ℤ) - 3) j : ℤ) : K) * p.leadingCoeff := by
  have lcC_ne_zero : ∀ j : ℕ, (Polynomial.C (((j : ℕ) + 1 : ℕ) : K) : Polynomial K) ≠ 0 :=
    fun j => Polynomial.C_ne_zero.mpr (by exact_mod_cast (Nat.succ_ne_zero j))
  have hq0 : q ≠ 0 := fun h => by rw [h] at hq; simp at hq
  have hqlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
  have hp0 : p ≠ 0 := fun h => hp (by rw [h]; simp)
  have hplc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  obtain ⟨hq'deg, hq'lc⟩ := derivative_natDegree_of_natDegree_eq_three q hq
  have hq'0 : q.derivative ≠ 0 := fun h => by rw [h] at hq'deg; simp at hq'deg
  have aux : ∀ j : ℕ, (∀ k : ℕ, k < j → ((p.natDegree : ℤ) - 3 - (k : ℤ)) ≠ 0) →
      (dnum p q j).natDegree = p.natDegree + 2 * j ∧
      (dnum p q j).leadingCoeff
        = q.leadingCoeff ^ j * ((fallFact ((p.natDegree : ℤ) - 3) j : ℤ) : K) * p.leadingCoeff := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨by simp [dnum], ?_⟩
      simp [dnum, fallFact_zero]
    | succ j ih =>
      intro hN'
      have hNj : ((p.natDegree : ℤ) - 3 - (j : ℤ)) ≠ 0 := hN' j (by omega)
      obtain ⟨hdeg, hlc⟩ := ih (fun k hk => hN' k (by omega))
      set c := dnum p q j with hc
      have hcdeg : c.natDegree = p.natDegree + 2 * j := hdeg
      have hclc : c.leadingCoeff
          = q.leadingCoeff ^ j * ((fallFact ((p.natDegree : ℤ) - 3) j : ℤ) : K) * p.leadingCoeff := hlc
      have hfj : ((fallFact ((p.natDegree : ℤ) - 3) j : ℤ) : K) ≠ 0 :=
        fallFact_cast_ne_zero (fun k hk => hN' k (by omega))
      have hc0 : c ≠ 0 := by
        rw [← Polynomial.leadingCoeff_ne_zero, hclc]
        exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hqlc) hfj) hplc
      have hclcne : c.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hc0
      have hc1 : 1 ≤ c.natDegree := by rw [hcdeg]; omega
      have hcN0 : c.natDegree ≠ 0 := by omega
      -- derivative of `c`
      have hc'deg : c.derivative.natDegree = c.natDegree - 1 := by
        refine le_antisymm (Polynomial.natDegree_derivative_le c) ?_
        have hcast : ((c.natDegree - 1 : ℕ) : K) + 1 = (c.natDegree : K) := by
          have h := Nat.cast_sub (R := K) hc1 (n := c.natDegree) (m := 1)
          rw [h, Nat.cast_one]
          ring
        have hcoeff : c.derivative.coeff (c.natDegree - 1) = (c.natDegree : K) * c.leadingCoeff := by
          rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hc1]
          rw [show ((c.natDegree - 1 : ℕ) : K) + 1 = (c.natDegree : K) from hcast]
          simp only [Polynomial.leadingCoeff]
          ring
        refine le_natDegree_of_ne_zero ?_
        rw [hcoeff]
        exact mul_ne_zero (by exact_mod_cast hcN0) hclcne
      have hc'lc : c.derivative.leadingCoeff = (c.natDegree : K) * c.leadingCoeff := by
        rw [Polynomial.leadingCoeff_derivative]
        ring
      have hc'0 : c.derivative ≠ 0 := by
        rw [← Polynomial.leadingCoeff_ne_zero, hc'lc]
        exact mul_ne_zero (by exact_mod_cast hcN0) hclcne
      -- the coefficient of `y^(c.natDegree+2)` in `dnum p q (j+1)`
      have hkey : (dnum p q (j + 1)).coeff (c.natDegree + 2)
          = (((c.natDegree : K) - (((j : ℕ) + 1 : ℕ) : K) * 3)) * c.leadingCoeff * q.leadingCoeff := by
        have hAcoeff : (c.derivative * q).coeff (c.natDegree + 2)
            = c.derivative.leadingCoeff * q.leadingCoeff := by
          rw [show c.natDegree + 2 = c.derivative.natDegree + q.natDegree from by
            rw [hc'deg, hq]; omega]
          exact Polynomial.coeff_mul_degree_add_degree _ _
        have hCdeg : (Polynomial.C (((j : ℕ) + 1 : ℕ) : K) : Polynomial K).natDegree = 0 :=
          Polynomial.natDegree_C _
        have hBcoeff : ((Polynomial.C (((j : ℕ) + 1 : ℕ) : K) : Polynomial K) * (c * q.derivative)).coeff
            (c.natDegree + 2)
            = (((j : ℕ) + 1 : ℕ) : K) * (c.leadingCoeff * q.derivative.leadingCoeff) := by
          rw [show c.natDegree + 2
              = (Polynomial.C (((j : ℕ) + 1 : ℕ) : K) : Polynomial K).natDegree
                + (c * q.derivative).natDegree from by
            rw [hCdeg, Polynomial.natDegree_mul hc0 hq'0, hcdeg, hq'deg]; omega]
          rw [Polynomial.coeff_mul_degree_add_degree, Polynomial.leadingCoeff_C,
            Polynomial.leadingCoeff_mul]
        rw [dnum_succ, Polynomial.coeff_sub, hAcoeff, hBcoeff, hc'lc, hq'lc]
        ring
      have hkeyne : (dnum p q (j + 1)).coeff (c.natDegree + 2) ≠ 0 := by
        rw [hkey]
        have hcast2 : (c.natDegree : K) - (((j : ℕ) + 1 : ℕ) : K) * 3
            = (((p.natDegree : ℤ) - 3 - (j : ℤ) : ℤ) : K) := by
          rw [show (c.natDegree : K) = (((p.natDegree : ℤ) + 2 * (j : ℤ) : ℤ) : K) from by
            rw [hcdeg]; push_cast; ring]
          push_cast
          ring
        rw [hcast2]
        exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hNj) hclcne) hqlc
      have hsubdeg : (dnum p q (j + 1)).natDegree = c.natDegree + 2 := by
        refine le_antisymm ?_ (le_natDegree_of_ne_zero hkeyne)
        have h1 : (dnum p q (j + 1)).natDegree
            ≤ max (c.derivative * q).natDegree
              ((Polynomial.C (((j : ℕ) + 1 : ℕ) : K) : Polynomial K) * (c * q.derivative)).natDegree := by
          rw [dnum_succ]
          exact Polynomial.natDegree_sub_le _ _
        have h2 : (c.derivative * q).natDegree = c.natDegree + 2 := by
          rw [Polynomial.natDegree_mul hc'0 hq0, hc'deg, hq]; omega
        have h3 : ((Polynomial.C (((j : ℕ) + 1 : ℕ) : K) : Polynomial K) * (c * q.derivative)).natDegree
            = c.natDegree + 2 := by
          rw [Polynomial.natDegree_mul (lcC_ne_zero j) (mul_ne_zero hc0 hq'0),
            Polynomial.natDegree_C, zero_add, Polynomial.natDegree_mul hc0 hq'0, hcdeg, hq'deg]
        rw [h2, h3, max_self] at h1
        exact h1
      refine ⟨by rw [hsubdeg, hcdeg]; ring, ?_⟩
      rw [Polynomial.leadingCoeff, hsubdeg, hkey]
      rw [show (c.natDegree : K) - (((j : ℕ) + 1 : ℕ) : K) * 3
          = (((p.natDegree : ℤ) - 3 - (j : ℤ) : ℤ) : K) from by
        rw [show (c.natDegree : K) = (((p.natDegree : ℤ) + 2 * (j : ℤ) : ℤ) : K) from by
          rw [hcdeg]; push_cast; ring]
        push_cast
        ring]
      rw [hclc, fallFact_succ]
      push_cast
      ring

  exact aux j hN

end Submission.CDT
