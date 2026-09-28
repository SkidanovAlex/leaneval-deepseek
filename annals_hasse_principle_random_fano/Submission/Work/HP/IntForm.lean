import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Psi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Integral and modular bookkeeping for `formEval`

Lemmas relating `formEval d n a x` over `ℤ`, over `ZMod W`, and under scaling of `x`,
and the size bound `‖ν(x)‖ ≤ √N · R^d` for `‖x‖ ≤ R`.
-/

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Finset
open scoped BigOperators

namespace Work.HP

/-! ## Homogeneity in the integer scalar -/

/-- `ν` is homogeneous of degree `d`, over any commutative semiring. -/
theorem veronese_const_mul' {R : Type*} [CommSemiring R] {d n : ℕ} (T : R)
    (u : Fin (n + 1) → R) :
    veronese d n (fun i => T * u i) = fun μ => T ^ d * veronese d n u μ := by
  funext μ
  simp only [veronese]
  have h : ∏ i, (T * u i) ^ ((μ.1 i : ℕ)) =
      ∏ i, (T ^ ((μ.1 i : ℕ)) * u i ^ ((μ.1 i : ℕ))) :=
    Finset.prod_congr rfl fun i _ => by rw [mul_pow]
  rw [h, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have h2 : (∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), ((μ.1 i : ℕ))) = d := by
    simpa using μ.2
  rw [h2]

/-- `formEval` is homogeneous of degree `d` in `x` over `ℤ`. -/
theorem formEval_const_mul {d n : ℕ} (a : Mon d n → ℤ) (k : ℤ) (x : Fin (n + 1) → ℤ) :
    formEval d n a (fun i => k * x i) = k ^ d * formEval d n a x := by
  simp only [formEval]
  rw [veronese_const_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => by ring

/-! ## Reduction modulo `W` -/

/-- Reduction of `formEval` modulo `W` commutes with reducing the point. -/
theorem formEval_intCast_zmod {d n : ℕ} (a : Mon d n → ℤ) (W : ℕ) (x : Fin (n + 1) → ℤ) :
    ((formEval d n a x : ℤ) : ZMod W) = formEval d n a (fun i => (x i : ZMod W)) := by
  simp only [formEval, veronese]
  push_cast
  rfl

/-- `f_a(x) ≡ 0 mod W` iff the reduction of `x` is a zero of the reduced form. -/
theorem formEval_dvd_iff {d n : ℕ} (a : Mon d n → ℤ) (W : ℕ) (x : Fin (n + 1) → ℤ) :
    ((W : ℤ) ∣ formEval d n a x) ↔ formEval d n a (fun i => (x i : ZMod W)) = 0 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, formEval_intCast_zmod]

/-- If `x ≡ y` coordinatewise modulo `W` then `f_a(x) ≡ f_a(y)` modulo `W`. -/
theorem formEval_congr_mod {d n : ℕ} (a : Mon d n → ℤ) (W : ℕ) (x y : Fin (n + 1) → ℤ)
    (h : ∀ i, (W : ℤ) ∣ x i - y i) : (W : ℤ) ∣ formEval d n a x - formEval d n a y := by
  have hxy : (fun i => (x i : ZMod W)) = fun i => (y i : ZMod W) := by
    funext i
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    obtain ⟨c, hc⟩ := h i
    exact ⟨-c, by rw [show y i - x i = -(x i - y i) by ring, hc]; ring⟩
  have hcast : ((formEval d n a x - formEval d n a y : ℤ) : ZMod W) = 0 := by
    push_cast
    rw [formEval_intCast_zmod, formEval_intCast_zmod, hxy, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ W).mp hcast

/-! ## Size bounds for the Veronese image -/

/-- A coordinate of `x` is bounded by `rNorm x`. -/
theorem abs_le_rNorm {n : ℕ} (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : |x i| ≤ rNorm x := by
  have h : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  calc |x i| = Real.sqrt ((x i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, (x j) ^ 2) := Real.sqrt_le_sqrt h
    _ = rNorm x := rfl

/-- `‖ν(x)‖ ≤ √N · R^d` for `‖x‖ ≤ R`. -/
theorem rNorm_veronese_le {d n : ℕ} {x : Fin (n + 1) → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hx : rNorm x ≤ R) :
    rNorm (veronese d n x) ≤ Real.sqrt (NN d n : ℝ) * R ^ d := by
  have hx' : ∀ i, |x i| ≤ R := fun i => le_trans (abs_le_rNorm x i) hx
  have hterm : ∀ μ : Mon d n, (veronese d n x μ) ^ 2 ≤ R ^ (2 * d) := by
    intro μ
    have h1 : |veronese d n x μ| ≤ R ^ d := by
      rw [veronese]
      calc |∏ i, x i ^ ((μ.1 i : ℕ))| = ∏ i, |x i| ^ ((μ.1 i : ℕ)) := by
            rw [Finset.abs_prod]
            exact Finset.prod_congr rfl fun i _ => abs_pow _ _
        _ ≤ ∏ i : Fin (n + 1), R ^ ((μ.1 i : ℕ)) := by
            gcongr with i
            exact hx' i
        _ = R ^ d := by
            rw [Finset.prod_pow_eq_pow_sum]
            have h2 : (∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), ((μ.1 i : ℕ))) = d := by
              simpa using μ.2
            rw [h2]
    rw [← sq_abs]
    calc |veronese d n x μ| ^ 2 ≤ (R ^ d) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = R ^ (2 * d) := by rw [← pow_mul]; ring_nf
  calc rNorm (veronese d n x)
      = Real.sqrt (∑ μ : Mon d n, (veronese d n x μ) ^ 2) := rfl
    _ ≤ Real.sqrt (∑ _μ : Mon d n, R ^ (2 * d)) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => hterm μ)
    _ = Real.sqrt ((NN d n : ℝ) * R ^ (2 * d)) := by
          congr 1
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NN]
    _ = Real.sqrt (NN d n : ℝ) * R ^ d := by
          rw [Real.sqrt_mul (by positivity)]
          congr 1
          rw [show R ^ (2 * d) = (R ^ d) ^ 2 from by rw [← pow_mul]; ring_nf]
          exact Real.sqrt_sq (pow_nonneg hR d)

end Work.HP
