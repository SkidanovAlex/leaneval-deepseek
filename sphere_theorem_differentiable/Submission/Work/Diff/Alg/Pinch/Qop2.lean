import Mathlib
import Submission.Diff.Alg
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.Pinch.Qop

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Symmetric/skew decomposition and the shear identity

Companion module to `Work.Diff.Alg.Pinch.Qop`.  Every pair-indexed vector `X : Fin n × Fin n → ℂ`
splits as `symPart X + skewPart X` (symmetric + skew part with respect to the coordinate swap), and
the operator `Rop R` of an algebraic curvature tensor kills the symmetric part while mapping the
skew part to the skew part.  The shear identity `adF Y (wedgeF ζ η) = wedgeF (matVec Y ζ) η +
wedgeF ζ (matVec Y η)` (for skew `Y`) identifies the tangent directions of the `ad`-orbit of a
decomposable bivector with the directions used by `secondVariation`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-- Symmetric part of a pair-indexed vector (fixed under the coordinate swap). -/
noncomputable def symPart (X : Fin n × Fin n → ℂ) : Fin n × Fin n → ℂ :=
  fun p => (X p + X (p.2, p.1)) / 2

/-- Skew part of a pair-indexed vector (negated by the coordinate swap). -/
noncomputable def skewPart (X : Fin n × Fin n → ℂ) : Fin n × Fin n → ℂ :=
  fun p => (X p - X (p.2, p.1)) / 2

/-- Matrix-vector product with a pair-indexed vector, as a vector. -/
noncomputable def matVec (Z : Fin n × Fin n → ℂ) (ζ : Fin n → ℂ) : Fin n → ℂ :=
  fun i => ∑ j : Fin n, Z (i, j) * ζ j

/-! ## Elementary swap lemmas -/

@[simp] theorem swapF_apply (X : Fin n × Fin n → ℂ) (p : Fin n × Fin n) : swapF X p = X (p.2, p.1) := rfl

@[simp] theorem swapF_swapF (X : Fin n × Fin n → ℂ) : swapF (swapF X) = X := by
  funext p; simp [swapF]

theorem swapF_add (X Y : Fin n × Fin n → ℂ) : swapF (X + Y) = swapF X + swapF Y := by
  funext p; simp [swapF]

theorem swapF_sub (X Y : Fin n × Fin n → ℂ) : swapF (X - Y) = swapF X - swapF Y := by
  funext p; simp [swapF]

theorem swapF_neg (X : Fin n × Fin n → ℂ) : swapF (-X) = - swapF X := by
  funext p; simp [swapF]

theorem swapF_smul (c : ℂ) (X : Fin n × Fin n → ℂ) : swapF (c • X) = c • swapF X := by
  funext p; simp [swapF]

theorem symPart_add_skewPart (X : Fin n × Fin n → ℂ) : symPart X + skewPart X = X := by
  funext p; simp only [symPart, skewPart, Pi.add_apply]; ring

theorem swapF_symPart (X : Fin n × Fin n → ℂ) : swapF (symPart X) = symPart X := by
  funext p; simp only [symPart, swapF_apply]; ring

theorem swapF_skewPart (X : Fin n × Fin n → ℂ) : swapF (skewPart X) = - skewPart X := by
  funext p; simp only [skewPart, swapF_apply, Pi.neg_apply]; ring

@[simp] theorem swapF_wedgeF (ζ η : Fin n → ℂ) : swapF (wedgeF ζ η) = - wedgeF ζ η := by
  funext p; simp only [wedgeF, swapF_apply, Pi.neg_apply]; ring

theorem wedgeF_add₁ (ζ ζ' η : Fin n → ℂ) : wedgeF (ζ + ζ') η = wedgeF ζ η + wedgeF ζ' η := by
  funext p; simp only [wedgeF, Pi.add_apply]; ring

theorem wedgeF_add₂ (ζ η η' : Fin n → ℂ) : wedgeF ζ (η + η') = wedgeF ζ η + wedgeF ζ η' := by
  funext p; simp only [wedgeF, Pi.add_apply]; ring

theorem wedgeF_smul₁ (c : ℂ) (ζ η : Fin n → ℂ) : wedgeF (c • ζ) η = c • wedgeF ζ η := by
  funext p; simp only [wedgeF, Pi.smul_apply, smul_eq_mul]; ring

theorem wedgeF_smul₂ (c : ℂ) (ζ η : Fin n → ℂ) : wedgeF ζ (c • η) = c • wedgeF ζ η := by
  funext p; simp only [wedgeF, Pi.smul_apply, smul_eq_mul]; ring

theorem matVec_add (Z Z' : Fin n × Fin n → ℂ) (ζ : Fin n → ℂ) :
    matVec (Z + Z') ζ = matVec Z ζ + matVec Z' ζ := by
  funext i; simp only [matVec, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem matVec_smul (c : ℂ) (Z : Fin n × Fin n → ℂ) (ζ : Fin n → ℂ) :
    matVec (c • Z) ζ = c • matVec Z ζ := by
  funext i; simp only [matVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _; ring

theorem matVec_neg (Z : Fin n × Fin n → ℂ) (ζ : Fin n → ℂ) : matVec (-Z) ζ = - matVec Z ζ := by
  funext i; simp only [matVec, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-! ## Linearity of `adF` and `Rop` -/

theorem adF_add (X Z W : Fin n × Fin n → ℂ) : adF X (Z + W) = adF X Z + adF X W := by
  funext p
  simp only [adF, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

theorem adF_neg (X Z : Fin n × Fin n → ℂ) : adF X (-Z) = - adF X Z := by
  funext p; simp only [adF, Pi.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]; ring

theorem adF_smul (c : ℂ) (X Z : Fin n × Fin n → ℂ) : adF X (c • Z) = c • adF X Z := by
  funext p
  simp only [adF, Pi.smul_apply, smul_eq_mul]
  rw [mul_sub]
  congr 1
  · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring

theorem Rop_add (R : Curv4 n) (X Y : Fin n × Fin n → ℂ) : Rop R (X + Y) = Rop R X + Rop R Y :=
  Matrix.mulVec_add (Rm R) X Y

theorem Rop_neg (R : Curv4 n) (X : Fin n × Fin n → ℂ) : Rop R (-X) = - Rop R X :=
  Matrix.mulVec_neg X (Rm R)

theorem Rop_smul (R : Curv4 n) (c : ℂ) (X : Fin n × Fin n → ℂ) :
    Rop R (c • X) = c • Rop R X :=
  Matrix.mulVec_smul (Rm R) c X

/-! ## `Rop` maps everything into the skew part and kills the symmetric part -/

/-- `Rop R X` is always skew. -/
theorem swapF_Rop (R : Curv4 n) (hR : IsAlgCurv R) (X : Fin n × Fin n → ℂ) :
    swapF (Rop R X) = - Rop R X := by
  funext p
  simp only [swapF, Rop, Rm, Matrix.mulVec, dotProduct, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro q _
  rw [hR.1 p.1 p.2 q.1 q.2]
  push_cast
  ring

/-- Intertwining of `Rop R` with the coordinate swap (up to sign). -/
theorem Rop_swapF (R : Curv4 n) (hR : IsAlgCurv R) (X : Fin n × Fin n → ℂ) :
    Rop R (swapF X) = - Rop R X := by
  funext p
  simp only [Rop, Rm, swapF, Matrix.mulVec, dotProduct, Pi.neg_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro a _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro b _
  rw [Work.Diff.Alg.Q2P.IsAlgCurv_antisym₃₄ hR p.1 p.2 b a]
  push_cast
  ring

/-- `Rop R` kills symmetric vectors. -/
theorem Rop_symPart (R : Curv4 n) (hR : IsAlgCurv R) (X : Fin n × Fin n → ℂ) :
    Rop R (symPart X) = 0 := by
  have h : symPart X = ((2 : ℂ)⁻¹) • (X + swapF X) := by
    funext p
    simp only [symPart, swapF_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, Rop_smul, Rop_add, Rop_swapF R hR X, add_neg_cancel, smul_zero]

/-- The Hermitian pairing of a symmetric and a skew vector vanishes. -/
theorem dotProduct_sym_skew {Z W : Fin n × Fin n → ℂ} (hZ : swapF Z = Z) (hW : swapF W = -W) :
    (star Z) ⬝ᵥ W = 0 := by
  have hZ' : ∀ p : Fin n × Fin n, Z (p.2, p.1) = Z p := by
    intro p; have := congrFun hZ p; simpa [swapF] using this
  have hW' : ∀ p : Fin n × Fin n, W (p.2, p.1) = - W p := by
    intro p; have := congrFun hW p; simpa [swapF] using this
  rw [dotProduct]
  refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
  · intro a _
    show (star Z) a * W a + (star Z) (a.2, a.1) * W (a.2, a.1) = 0
    have h1 : (star Z) (a.2, a.1) = (star Z) a := by
      simp only [Pi.star_apply]
      rw [hZ' a]
    rw [h1, hW' a]
    ring
  · intro a _ hf h
    apply hf
    have hW0 : W a = 0 := by
      have h2 := hW' a
      rw [show (a.2, a.1) = a from h] at h2
      have h3 : (2 : ℂ) * W a = 0 := by rw [two_mul]; nth_rewrite 2 [h2]; ring
      exact (mul_eq_zero.mp h3).resolve_left two_ne_zero
    simp [hW0]
  · intro a _; exact Finset.mem_univ _
  · intro a _; exact Prod.swap_swap a

/-! ## The shear identity -/

/-- Intertwining of `adF` with the coordinate swap for skew `X`. -/
theorem adF_swap_of_skew {X : Fin n × Fin n → ℂ} (hX : swapF X = -X) (Z : Fin n × Fin n → ℂ) :
    swapF (adF X Z) = adF X (swapF Z) := by
  have hX' : ∀ a b : Fin n, X (b, a) = - X (a, b) := by
    intro a b; have := congrFun hX (a, b); simpa [swapF] using this
  funext p
  simp only [adF, swapF_apply]
  have hA1 : (∑ k : Fin n, X (p.2, k) * Z (k, p.1))
      = - ∑ k : Fin n, Z (k, p.1) * X (k, p.2) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro k _
    rw [hX' k p.2]; ring
  have hA2 : (∑ k : Fin n, Z (p.2, k) * X (k, p.1))
      = - ∑ k : Fin n, X (p.1, k) * Z (p.2, k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro k _
    rw [hX' p.1 k]; ring
  rw [hA1, hA2]; ring

/-- The shear identity: for skew `Y` the commutator with `Y` of a decomposable bivector is the
sum of the two "shear" directions. -/
theorem adF_shear {Y : Fin n × Fin n → ℂ} (hY : swapF Y = -Y) (ζ η : Fin n → ℂ) :
    adF Y (wedgeF ζ η) = wedgeF (matVec Y ζ) η + wedgeF ζ (matVec Y η) := by
  have hY' : ∀ a b : Fin n, Y (b, a) = - Y (a, b) := by
    intro a b; have := congrFun hY (a, b); simpa [swapF] using this
  funext p
  simp only [adF, wedgeF, matVec, Pi.add_apply]
  have hA : (∑ k : Fin n, Y (p.1, k) * (ζ k * η p.2 - ζ p.2 * η k))
      = (∑ k : Fin n, Y (p.1, k) * ζ k) * η p.2
        - (∑ k : Fin n, Y (p.1, k) * η k) * ζ p.2 := by
    have h1 : (∑ k : Fin n, Y (p.1, k) * (ζ k * η p.2 - ζ p.2 * η k))
        = (∑ k : Fin n, (Y (p.1, k) * ζ k) * η p.2)
          - (∑ k : Fin n, (Y (p.1, k) * η k) * ζ p.2) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [h1, Finset.sum_mul, Finset.sum_mul]
  have hB : (∑ k : Fin n, (ζ p.1 * η k - ζ k * η p.1) * Y (k, p.2))
      = η p.1 * (∑ k : Fin n, Y (p.2, k) * ζ k)
        - ζ p.1 * (∑ k : Fin n, Y (p.2, k) * η k) := by
    have h1 : (∑ k : Fin n, (ζ p.1 * η k - ζ k * η p.1) * Y (k, p.2))
        = (∑ k : Fin n, η p.1 * (Y (p.2, k) * ζ k))
          - (∑ k : Fin n, ζ p.1 * (Y (p.2, k) * η k)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k _
      rw [hY' p.2 k]; ring
    rw [h1, Finset.mul_sum, Finset.mul_sum]
  rw [hA, hB]; ring

/-- `Rop R` commutes with entrywise conjugation (the array `R` is real). -/
theorem Rop_bar (R : Curv4 n) (X : Fin n × Fin n → ℂ) : Rop R (bar X) = bar (Rop R X) := by
  funext p
  simp only [Rop, Rm, bar, Matrix.mulVec, dotProduct]
  rw [star_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [star_mul, star_ofReal']
  ring

end Work.Diff.Alg.Pinch
