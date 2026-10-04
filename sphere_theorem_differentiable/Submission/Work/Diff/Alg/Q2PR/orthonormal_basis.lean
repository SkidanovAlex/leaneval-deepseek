import Mathlib
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# An orthonormal basis adapted to two complex vectors

`Work.Diff.Alg.Q2PR.orthonormal_basis`: given two complex vectors `z w : Fin n → ℂ` which are
`ℂ`-linearly independent, one can normalise `z` to a unit vector `e1`, subtract from `w` its
component along `e1`, and normalise the remainder to a second unit vector `e2` orthogonal to `e1`.
In coordinates, `z = c1 • e1` and `w = c2 • e2 + c3 • e1` with `c1, c2 ≠ 0`.

The relevant pairing is the Hermitian form `cHerm z w = ∑ i, z i * star (w i)` of
`Submission.Work.Diff.Alg.q2p_defs` (linear in the first variable, conjugate linear in the
second).  We collect here its elementary sesquilinearity, its conjugate symmetry and the
positive-definiteness of the associated squared norm `cNSq x = ∑ i, Complex.normSq (x i)`.
-/

namespace Work.Diff.Alg.Q2PR

open Work.Diff.Alg.Q2P Finset

noncomputable section

variable {n : ℕ}

/-- The squared Euclidean norm `∑ᵢ ‖xᵢ‖²` of a complex vector, as a real number. -/
def cNSq (x : Fin n → ℂ) : ℝ := ∑ i, Complex.normSq (x i)

/-- `cHerm x x` is the (real, nonnegative) squared norm of `x`. -/
lemma cHerm_self (x : Fin n → ℂ) : cHerm x x = (cNSq x : ℂ) := by
  rw [cNSq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl; intro i _
  exact Complex.mul_conj (x i)

lemma cHerm_add₁ (x y w : Fin n → ℂ) : cHerm (x + y) w = cHerm x w + cHerm y w := by
  simp only [cHerm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma cHerm_add₂ (x y z : Fin n → ℂ) : cHerm x (y + z) = cHerm x y + cHerm x z := by
  simp only [cHerm, Pi.add_apply, star_add, mul_add, Finset.sum_add_distrib]

lemma cHerm_smul₁ (c : ℂ) (x w : Fin n → ℂ) : cHerm (c • x) w = c * cHerm x w := by
  simp only [cHerm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

lemma cHerm_smul₂ (c : ℂ) (x w : Fin n → ℂ) : cHerm x (c • w) = star c * cHerm x w := by
  simp only [cHerm, Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

lemma cHerm_conj_symm (x y : Fin n → ℂ) : cHerm x y = star (cHerm y x) := by
  simp only [cHerm, star_sum]
  apply Finset.sum_congr rfl; intro _ _
  rw [star_mul, star_star]

lemma cHerm_sub₁ (x y w : Fin n → ℂ) : cHerm (x - y) w = cHerm x w - cHerm y w := by
  simp only [cHerm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma cHerm_sub₂ (x y z : Fin n → ℂ) : cHerm x (y - z) = cHerm x y - cHerm x z := by
  simp only [cHerm, Pi.sub_apply, star_sub, mul_sub, Finset.sum_sub_distrib]

lemma cNSq_nonneg (x : Fin n → ℂ) : 0 ≤ cNSq x :=
  Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (x i))

lemma cNSq_eq_zero {x : Fin n → ℂ} : cNSq x = 0 ↔ x = 0 := by
  rw [cNSq, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (x i))]
  constructor
  · intro h; funext i; exact Complex.normSq_eq_zero.mp (h i (Finset.mem_univ i))
  · intro h _ _; rw [h]; simp

theorem orthonormal_basis {n : ℕ} (z w : Fin n → ℂ)
    (hind : ∀ a b : ℂ, (∀ i, a * z i + b * w i = 0) → a = 0 ∧ b = 0) :
    ∃ (e1 e2 : Fin n → ℂ) (c1 c2 c3 : ℂ),
      c1 ≠ 0 ∧ c2 ≠ 0 ∧
      Work.Diff.Alg.Q2P.cHerm e1 e1 = 1 ∧ Work.Diff.Alg.Q2P.cHerm e2 e2 = 1 ∧
      Work.Diff.Alg.Q2P.cHerm e1 e2 = 0 ∧ Work.Diff.Alg.Q2P.cHerm e2 e1 = 0 ∧
      z = c1 • e1 ∧ w = c2 • e2 + c3 • e1 := by
  -- `z ≠ 0`, hence `‖z‖² > 0`; normalise `z` to `e1 = c1⁻¹ • z` with `c1 = √‖z‖²`.
  have hz0 : z ≠ 0 := by
    intro h
    exact one_ne_zero (hind 1 0 (fun i => by simp [h])).1
  have hSne : cNSq z ≠ 0 := fun h => hz0 (cNSq_eq_zero.mp h)
  have hSpos : 0 < cNSq z := lt_of_le_of_ne (cNSq_nonneg z) (Ne.symm hSne)
  set c1 : ℂ := (Real.sqrt (cNSq z) : ℂ) with hc1
  have hc1ne : c1 ≠ 0 := by
    rw [hc1]; simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr hSpos)
  have hc1sq : c1 * c1 = (cNSq z : ℂ) := by
    rw [hc1, ← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hSpos)]
  have hc1star : star c1 = c1 := by rw [hc1]; simp
  set e1 : Fin n → ℂ := c1⁻¹ • z with he1
  have he1self : cHerm e1 e1 = 1 := by
    rw [he1, cHerm_smul₁, cHerm_smul₂, cHerm_self]
    rw [show star (c1⁻¹) = c1⁻¹ from by rw [star_inv₀, hc1star]]
    have h2 : c1⁻¹ * c1 = 1 := inv_mul_cancel₀ hc1ne
    calc c1⁻¹ * (c1⁻¹ * (cNSq z : ℂ)) = (c1⁻¹ * c1) * (c1⁻¹ * c1) := by
          rw [← hc1sq]; ring
      _ = 1 := by rw [h2, mul_one]
  -- Remove from `w` its `cHerm`-component along `e1`; the remainder `r` is non-zero by `hind`.
  set c3 : ℂ := cHerm w e1 with hc3
  set r : Fin n → ℂ := w - c3 • e1 with hr
  have he1r : cHerm e1 r = 0 := by
    rw [hr, cHerm_sub₂, cHerm_smul₂, he1self, mul_one, hc3, ← cHerm_conj_symm e1 w]
    ring
  have hre1 : cHerm r e1 = 0 := by
    rw [hr, cHerm_sub₁, cHerm_smul₁, he1self, mul_one, hc3]
    ring
  have hr0 : r ≠ 0 := by
    intro hr0
    have hw : w = (c3 * c1⁻¹) • z := by
      have h1 : w = c3 • e1 := by
        have : w - c3 • e1 = 0 := by rw [← hr]; exact hr0
        exact sub_eq_zero.mp this
      rw [h1, he1, smul_smul]
    have hc := (hind (-(c3 * c1⁻¹)) 1 (fun i => by
      simp only [hw, Pi.smul_apply, smul_eq_mul]; ring)).2
    exact one_ne_zero hc
  -- Normalise the remainder to `e2`.
  have hTne : cNSq r ≠ 0 := fun h => hr0 (cNSq_eq_zero.mp h)
  have hTpos : 0 < cNSq r := lt_of_le_of_ne (cNSq_nonneg r) (Ne.symm hTne)
  set c2 : ℂ := (Real.sqrt (cNSq r) : ℂ) with hc2
  have hc2ne : c2 ≠ 0 := by
    rw [hc2]; simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr hTpos)
  have hc2sq : c2 * c2 = (cNSq r : ℂ) := by
    rw [hc2, ← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hTpos)]
  have hc2star : star c2 = c2 := by rw [hc2]; simp
  set e2 : Fin n → ℂ := c2⁻¹ • r with he2
  have he2self : cHerm e2 e2 = 1 := by
    rw [he2, cHerm_smul₁, cHerm_smul₂, cHerm_self]
    rw [show star (c2⁻¹) = c2⁻¹ from by rw [star_inv₀, hc2star]]
    have h2 : c2⁻¹ * c2 = 1 := inv_mul_cancel₀ hc2ne
    calc c2⁻¹ * (c2⁻¹ * (cNSq r : ℂ)) = (c2⁻¹ * c2) * (c2⁻¹ * c2) := by
          rw [← hc2sq]; ring
      _ = 1 := by rw [h2, mul_one]
  refine ⟨e1, e2, c1, c2, c3, hc1ne, hc2ne, he1self, he2self, ?_, ?_, ?_, ?_⟩
  · rw [he2, cHerm_smul₂, he1r, mul_zero]
  · rw [he2, cHerm_smul₁, hre1, mul_zero]
  · rw [he1, smul_smul, mul_inv_cancel₀ hc1ne, one_smul]
  · rw [he2, smul_smul, mul_inv_cancel₀ hc2ne, one_smul]
    rw [hr, sub_add_cancel]

end

end Work.Diff.Alg.Q2PR
