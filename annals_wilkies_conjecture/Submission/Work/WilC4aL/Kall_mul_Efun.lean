/-
  annals_wilkies_conjecture, area C4aL (`C4a_lift`): the cleared equation identity.

  `Kall σ D z * Efun cc σ P z = Ppart cc σ D P z`: multiplying the (non-entire) slice
  equation by the clearing factor `Kall` (one factor `(z j) ^ D` per inverted coordinate)
  removes every occurrence of `(z j)⁻¹` and yields the entire equation `Ppart`.

  The two hypotheses are exactly what makes this work: `hD` bounds the exponents of every
  monomial of `P` by `D` on the inverted coordinates (so that `D - d x` is a genuine
  natural number), and `hz` makes the inverted coordinates nonzero (so that
  `z ^ D * (z⁻¹) ^ d = z ^ (D - d)`).
-/
import Mathlib
import Submission.Work.WilC4aL.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilC4aL
open WilkiesDesign WilkiesDesign.CG.C4a
open scoped BigOperators

variable {k m : ℕ}

/-! ## 1. Elementary ingredients -/

/-- `z ^ D * (z⁻¹) ^ n = z ^ (D - n)`: clearing the inverses. -/
theorem pow_mul_inv_pow {z : ℝ} (hz : z ≠ 0) {n D : ℕ} (hn : n ≤ D) :
    z ^ (D - n) = z ^ D * (z⁻¹) ^ n := by
  conv_rhs => rw [← Nat.sub_add_cancel hn]
  rw [pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ hz, one_pow, mul_one]

/-- A product over the support of a `ℕ`-valued finsupp is the product over all coordinates. -/
theorem finsupp_prod_nat {α : Type*} [Fintype α] (d : α →₀ ℕ) (g : α → ℝ) :
    d.prod (fun x e => g x ^ e) = ∏ x, g x ^ d x := by
  rw [Finsupp.prod_of_support_subset d (Finset.subset_univ d.support) (fun x e => g x ^ e)
    (fun x _ => by simp)]

/-! ## 2. The factors of `Kall` -/

theorem Kx_inl_big (σ : Fin (m + 2) → VC) (D : ℕ) (z : Fin (m + 2) → ℝ)
    (i : Fin (k + 2 + m)) (h : bigSum σ (Sum.inl i) = true) :
    Kx σ D z (Sum.inl i) = (z (coordOf i)) ^ D := by
  simp only [Kx, Sum.elim_inl, h, ite_true]

theorem Kx_inl_not_big (σ : Fin (m + 2) → VC) (D : ℕ) (z : Fin (m + 2) → ℝ)
    (i : Fin (k + 2 + m)) (h : bigSum σ (Sum.inl i) = false) :
    Kx σ D z (Sum.inl i) = 1 := by
  simp only [Kx, h, Bool.false_eq_true, ite_false]

theorem Kx_inr (σ : Fin (m + 2) → VC) (D : ℕ) (z : Fin (m + 2) → ℝ)
    (i : Fin (k + 2 + m)) : Kx σ D z (Sum.inr i) = 1 := by
  simp only [Kx, bigSum_inr, Bool.false_eq_true, ite_false]

/-! ## 3. The identity, one variable at a time -/

/-- For every variable of the two blocks, the cleared value raised to the reversed exponent
is the corresponding factor of `Kall` times the substituted value raised to the original
exponent.  This is where `hD` and `hz` are used. -/
theorem pervar (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (D : ℕ)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) (z : Fin (m + 2) → ℝ)
    (hD : ∀ d ∈ P.support, ∀ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
      bigSum σ x = true → d x ≤ D)
    (hz : ∀ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
      bigSum σ x = true → z (Sum.elim coordOf coordOf x) ≠ 0)
    {d : Fin (k + 2 + m) ⊕ Fin (k + 2 + m) →₀ ℕ} (hd : d ∈ P.support)
    (x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) :
    (Sum.elim (fun i => valC cc σ i z) (fun i => rvE cc σ i z) x) ^ (ddMon σ D d x) =
      Kx σ D z x * (Sum.elim (fun i => valE cc σ i z) (fun i => rvE cc σ i z) x) ^ (d x) := by
  rcases x with i | i
  · simp only [Sum.elim_inl]
    by_cases hb : bigSum σ (Sum.inl i) = true
    · rw [valC_eq_val_of_big cc σ i hb z, valE_eq_inv_of_big cc σ i hb z,
        ddMon_apply_of_big σ D d hb, Kx_inl_big σ D z i hb]
      exact pow_mul_inv_pow (hz (Sum.inl i) hb) (hD d hd (Sum.inl i) hb)
    · have hbf : bigSum σ (Sum.inl i) = false := by
        cases hh : bigSum σ (Sum.inl i) <;> simp_all
      rw [valC_eq_valE_of_not_big cc σ i hbf z, ddMon_apply_of_not_big σ D d hbf,
        Kx_inl_not_big σ D z i hbf, one_mul]
  · simp only [Sum.elim_inr]
    rw [ddMon_apply_of_not_big σ D d (bigSum_inr σ i), Kx_inr σ D z i, one_mul]

/-! ## 4. The identity for a single monomial -/

/-- `Kall` times the substituted monomial equals the cleared monomial. -/
theorem Kall_mul_prod (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (D : ℕ)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) (z : Fin (m + 2) → ℝ)
    (hD : ∀ d ∈ P.support, ∀ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
      bigSum σ x = true → d x ≤ D)
    (hz : ∀ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
      bigSum σ x = true → z (Sum.elim coordOf coordOf x) ≠ 0)
    {d : Fin (k + 2 + m) ⊕ Fin (k + 2 + m) →₀ ℕ} (hd : d ∈ P.support) :
    Kall (k := k) σ D z * (∏ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
        (Sum.elim (fun i => valE cc σ i z) (fun i => rvE cc σ i z) x) ^ (d x)) =
      ∏ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
        (Sum.elim (fun i => valC cc σ i z) (fun i => rvE cc σ i z) x) ^ (ddMon σ D d x) := by
  simp only [Kall]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun x _ => (pervar cc σ D P z hD hz hd x).symm)

/-! ## 5. `Efun` and `Ppart` as sums over the support -/

theorem Efun_eq_sum (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) (z : Fin (m + 2) → ℝ) :
    Efun cc σ P z = ∑ d ∈ P.support, P.coeff d *
      ∏ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
        (Sum.elim (fun i => valE cc σ i z) (fun i => rvE cc σ i z) x) ^ (d x) := by
  rw [Efun]
  exact MvPolynomial.eval_eq' _ P

theorem Ppart_eq_sum (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (D : ℕ)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) (z : Fin (m + 2) → ℝ) :
    Ppart cc σ D P z = ∑ d ∈ P.support, P.coeff d *
      ∏ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
        (Sum.elim (fun i => valC cc σ i z) (fun i => rvE cc σ i z) x) ^ (ddMon σ D d x) := by
  rw [Ppart, clePoly, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [MvPolynomial.eval_monomial]
  congr 1
  exact finsupp_prod_nat (ddMon σ D d)
    (Sum.elim (fun i => valC cc σ i z) (fun i => rvE cc σ i z))

/-! ## 6. The cleared equation identity -/

theorem Kall_mul_Efun {k m : ℕ} (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (D : ℕ)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) (z : Fin (m + 2) → ℝ)
    (hD : ∀ d ∈ P.support, ∀ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
      bigSum σ x = true → d x ≤ D)
    (hz : ∀ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
      bigSum σ x = true →
        z (Sum.elim (coordOf (k := k) (m := m)) (coordOf (k := k) (m := m)) x) ≠ 0) :
    Kall (k := k) σ D z * Efun cc σ P z = Ppart cc σ D P z := by
  rw [Efun_eq_sum cc σ P z, Ppart_eq_sum cc σ D P z, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  calc Kall (k := k) σ D z * (P.coeff d * ∏ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
          (Sum.elim (fun i => valE cc σ i z) (fun i => rvE cc σ i z) x) ^ (d x))
      = P.coeff d * (Kall (k := k) σ D z * ∏ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
          (Sum.elim (fun i => valE cc σ i z) (fun i => rvE cc σ i z) x) ^ (d x)) := by
        ring
    _ = P.coeff d * ∏ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
          (Sum.elim (fun i => valC cc σ i z) (fun i => rvE cc σ i z) x) ^ (ddMon σ D d x) := by
        rw [Kall_mul_prod cc σ D P z hD hz hd]

end Work.WilC4aL
