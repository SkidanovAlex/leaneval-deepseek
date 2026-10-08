import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open scoped commutatorElement

namespace Work.Higman.H8

/-- In an abelian subgroup four elements can be reordered: `a * b * c * d = c * d * b * a`. -/
theorem mul_four_reorder {P : Type} [Group P] {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {a b c d : P} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) :
    a * b * c * d = c * d * b * a := by
  calc a * b * c * d = (a * b) * (c * d) := by group
    _ = (c * d) * (a * b) := hAab (a * b) (A.mul_mem ha hb) (c * d) (A.mul_mem hc hd)
    _ = c * d * b * a := by rw [hAab a ha b hb]; group

/-- Squaring a product of four elements of an abelian subgroup. -/
theorem sq_four_of_mem {P : Type} [Group P] {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {a b c d : P} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) :
    (a * b * c * d) ^ 2 = a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 := by
  have h1 : Commute (a * b) (c * d) := hAab (a * b) (A.mul_mem ha hb) (c * d) (A.mul_mem hc hd)
  have h2 : Commute a b := hAab a ha b hb
  have h3 : Commute c d := hAab c hc d hd
  calc (a * b * c * d) ^ 2 = ((a * b) * (c * d)) ^ 2 := by group
    _ = (a * b) ^ 2 * (c * d) ^ 2 := h1.mul_pow 2
    _ = (a ^ 2 * b ^ 2) * (c ^ 2 * d ^ 2) := by rw [h2.mul_pow 2, h3.mul_pow 2]
    _ = a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 := by group

theorem pow4_mul {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (x y : P) : (x * y) ^ 4 = x ^ 4 * y ^ 4 * (x * y * x⁻¹ * y⁻¹) ^ 2 := by
  -- `A` is a `ξ`-invariant abelian normal subgroup.
  have hAnorm : A.Normal := by
    rw [← hGs]
    exact Subgroup.commutator_normal ⊤ ⊤
  have hA : Work.Higman.IsXiAbelNormal h A := ⟨hAnorm, hAxi, hAab⟩
  -- Unipotence: `⁅u, a⁆ ∈ A ^ 2` for `u : P`, `a ∈ A`.
  have huni : ∀ u : P, ∀ a ∈ A, ⁅u, a⁆ ∈ Work.Higman.powSub A 2 :=
    Work.Higman.commutator_mem_powSub_two h hA
  -- `A ^ 2 = Ω₁(P)` is elementary abelian.
  have hZs : ∀ z ∈ Work.Higman.powSub A 2, z ^ 2 = 1 := by
    intro z hz
    rw [htop] at hz
    exact h.omega1_sq_eq_one hz
  -- The relevant element `c = ⁅y, x⁆` and companions.
  set c : P := ⁅y, x⁆ with hc
  have hcA : c ∈ A := by
    rw [hc, ← hGs]
    exact Subgroup.commutator_mem_commutator trivial trivial
  have hyx : y * x = c * (x * y) := by
    rw [hc, commutatorElement_def]; group
  have hxconj : x * c * x⁻¹ = ⁅x, c⁆ * c := by
    rw [commutatorElement_def]; group
  have hxcA : ⁅x, c⁆ ∈ A := by
    rw [commutatorElement_def]
    exact A.mul_mem (hAnorm.conj_mem c hcA x) (A.inv_mem hcA)
  have hxcZ : ⁅x, c⁆ ∈ Work.Higman.powSub A 2 := huni x c hcA
  -- Step 1: the square of a product.
  have key1 : (x * y) ^ 2 = x ^ 2 * y ^ 2 * c * ⁅x, c⁆ := by
    calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
      _ = x * (c * (x * y)) * y := by rw [hyx]
      _ = (x * c * x⁻¹) * x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]; group
      _ = (⁅x, c⁆ * c) * x ^ 2 * y ^ 2 := by rw [hxconj]
      _ = x ^ 2 * y ^ 2 * c * ⁅x, c⁆ := mul_four_reorder hAab hxcA hcA (hsq x) (hsq y)
  -- Step 2: the fourth power of a product.
  have key2 : (x * y) ^ 4 = (x ^ 2) ^ 2 * (y ^ 2) ^ 2 * c ^ 2 * ⁅x, c⁆ ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, key1]
    exact sq_four_of_mem hAab (hsq x) (hsq y) hcA hxcA
  have hx4 : (x ^ 2) ^ 2 = x ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
  have hy4 : (y ^ 2) ^ 2 = y ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
  -- `c ^ 4 = 1`.
  have hc4 : c ^ 4 = 1 := by
    have hmem : c ^ 2 ∈ Work.Higman.omega1 P := by
      rw [← htop]
      exact Work.Higman.pow_mem_powSub (n := 2) hcA
    have h' : c ^ (2 * 2) = 1 := by
      rw [pow_mul]
      exact h.omega1_sq_eq_one hmem
    rw [show (2 : ℕ) * 2 = 4 by norm_num] at h'
    exact h'
  -- `c ^ 2 = ⁅x, y⁆ ^ 2`.
  have hc2 : c ^ 2 = ⁅x, y⁆ ^ 2 := by
    have h2 : c ^ 2 * c ^ 2 = 1 := by
      have hpow : c ^ 2 * c ^ 2 = c ^ 4 := by rw [← pow_add]
      rw [hpow, hc4]
    have h1 : (c ^ 2)⁻¹ = c ^ 2 := inv_eq_of_mul_eq_one_right h2
    have hcinv : c⁻¹ = ⁅x, y⁆ := by rw [hc, commutatorElement_inv]
    calc c ^ 2 = (c ^ 2)⁻¹ := h1.symm
      _ = (c⁻¹) ^ 2 := by rw [← inv_pow]
      _ = ⁅x, y⁆ ^ 2 := by rw [hcinv]
  have hD2 : ⁅x, c⁆ ^ 2 = 1 := hZs ⁅x, c⁆ hxcZ
  calc (x * y) ^ 4 = (x ^ 2) ^ 2 * (y ^ 2) ^ 2 * c ^ 2 * ⁅x, c⁆ ^ 2 := key2
    _ = x ^ 4 * y ^ 4 * c ^ 2 * ⁅x, c⁆ ^ 2 := by rw [hx4, hy4]
    _ = x ^ 4 * y ^ 4 * ⁅x, y⁆ ^ 2 * ⁅x, c⁆ ^ 2 := by rw [hc2]
    _ = x ^ 4 * y ^ 4 * ⁅x, y⁆ ^ 2 * 1 := by rw [hD2]
    _ = x ^ 4 * y ^ 4 * (x * y * x⁻¹ * y⁻¹) ^ 2 := by
        rw [commutatorElement_def, mul_one]

end Work.Higman.H8
