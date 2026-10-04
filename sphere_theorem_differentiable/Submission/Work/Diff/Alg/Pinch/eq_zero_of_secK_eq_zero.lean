import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# An algebraic curvature tensor with all sectional curvatures zero is zero

If `R` is an algebraic curvature tensor (`IsAlgCurv`, i.e. antisymmetric in the first pair,
symmetric under exchanging the two pairs, first Bianchi) and every sectional curvature
`secK R u v = R4 R u v u v` vanishes, then `R = 0`.

The proof is the classical "sectional curvature determines the curvature tensor" argument,
done here in the form needed for the Böhm–Wilking pinching-set construction:

* Evaluating at the basis vectors `E a` reduces `secK` to the components
  `R4 R (E a) (E b) (E c) (E d) = R a b c d`, so the hypothesis reads `R a b a b = 0`.
* Polarising in one argument gives the *vanishing* of the mixed components
  `R a b a d = 0` (first = third index) and `R a b c b = 0` (second = fourth index).
* Polarising in both arguments gives `R a b c d = - R a d c b`, whence, using the pair symmetry
  `R a b c d = - R c b a d`, the tensor is *cyclic* in its first three indices.
* The first Bianchi identity then forces `3 * R a b c d = 0`, hence `R a b c d = 0`.
-/

open Finset
open Submission.Diff.Alg (Curv4 IsAlgCurv R4 secK)

namespace Work.Diff.Alg.Pinch

variable {n : ℕ}

/-- The standard basis vector `e_a` of `ℝⁿ`, as an element of `Fin n → ℝ`. -/
private noncomputable def E (a : Fin n) : Fin n → ℝ := Pi.single a 1

/-- `R4` is additive in its first argument. -/
private lemma R4_add₁ (R : Curv4 n) (a1 a2 b c d : Fin n → ℝ) :
    R4 R (a1 + a2) b c d = R4 R a1 b c d + R4 R a2 b c d := by
  simp only [R4, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- `R4` is additive in its second argument. -/
private lemma R4_add₂ (R : Curv4 n) (a b1 b2 c d : Fin n → ℝ) :
    R4 R a (b1 + b2) c d = R4 R a b1 c d + R4 R a b2 c d := by
  simp only [R4, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- `R4` is additive in its third argument. -/
private lemma R4_add₃ (R : Curv4 n) (a b c1 c2 d : Fin n → ℝ) :
    R4 R a b (c1 + c2) d = R4 R a b c1 d + R4 R a b c2 d := by
  simp only [R4, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- `R4` is additive in its fourth argument. -/
private lemma R4_add₄ (R : Curv4 n) (a b c d1 d2 : Fin n → ℝ) :
    R4 R a b c (d1 + d2) = R4 R a b c d1 + R4 R a b c d2 := by
  simp only [R4, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- `R4` evaluated on the basis vectors is the corresponding component. -/
private lemma R4_basis (R : Curv4 n) (a b c d : Fin n) :
    R4 R (E a) (E b) (E c) (E d) = R a b c d := by
  simp only [R4]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single c]
      · rw [Finset.sum_eq_single d]
        · simp [E]
        · intro l _ hl; simp only [E, Pi.single_eq_of_ne hl, mul_zero]
        · intro h; exact absurd (Finset.mem_univ d) h
      · intro k _ hk; simp only [E, Pi.single_eq_of_ne hk, mul_zero]; simp
      · intro h; exact absurd (Finset.mem_univ c) h
    · intro j _ hj; simp only [E, Pi.single_eq_of_ne hj, mul_zero]; simp
    · intro h; exact absurd (Finset.mem_univ b) h
  · intro i _ hi; simp only [E, Pi.single_eq_of_ne hi, mul_zero]; simp
  · intro h; exact absurd (Finset.mem_univ a) h

theorem eq_zero_of_secK_eq_zero (n : ℕ) {R : Submission.Diff.Alg.Curv4 n}
    (h : Submission.Diff.Alg.IsAlgCurv R)
    (h0 : ∀ u v : Fin n → ℝ, Submission.Diff.Alg.secK R u v = 0) : R = 0 := by
  -- diagonal components
  have hdiag : ∀ a b : Fin n, R a b a b = 0 := by
    intro a b
    have hh := h0 (E a) (E b)
    simpa only [secK, R4_basis] using hh
  -- components with first index = third index
  have h13 : ∀ a b d : Fin n, R a b a d = 0 := by
    intro a b d
    have hh := h0 (E a) (E b + E d)
    simp only [secK, R4_add₂, R4_add₄, R4_basis] at hh
    have h1 := hdiag a b
    have h2 := hdiag a d
    have h3 := h.2.1 a b a d
    linarith
  -- components with second index = fourth index
  have h24 : ∀ a b c : Fin n, R a b c b = 0 := by
    intro a b c
    have hh := h0 (E a + E c) (E b)
    simp only [secK, R4_add₁, R4_add₃, R4_basis] at hh
    have h1 := hdiag a b
    have h2 := hdiag c b
    have h3 := h.2.1 c b a b
    linarith
  -- polarisation in both arguments: `R a b c d = - R a d c b`
  have hD : ∀ a b c d : Fin n, R a b c d = -R a d c b := by
    intro a b c d
    have hh := h0 (E a + E c) (E b + E d)
    simp only [secK, R4_add₁, R4_add₂, R4_add₃, R4_add₄, R4_basis] at hh
    have h1 := hdiag a b; have h2 := hdiag a d
    have h3 := hdiag c b; have h4 := hdiag c d
    have h5 := h13 a b d; have h6 := h13 a d b
    have h7 := h13 c b d; have h8 := h13 c d b
    have h9 := h24 a b c; have h10 := h24 a d c
    have h11 := h24 c b a; have h12 := h24 c d a
    have h14 := h.2.1 a b c d
    have h15 := h.2.1 a d c b
    linarith
  -- the tensor is antisymmetric under exchanging the first and third argument
  have hC : ∀ a b c d : Fin n, R a b c d = -R c b a d := by
    intro a b c d
    have h1 := hD a d c b
    have h2 := h.2.1 a d c b
    linarith
  -- the tensor is cyclic in its first three arguments
  have hcyc : ∀ a b c d : Fin n, R a b c d = R b c a d := by
    intro a b c d
    have h1 := hC a b c d
    have h2 := h.1 b c a d
    linarith
  have hcyc2 : ∀ a b c d : Fin n, R a b c d = R c a b d := by
    intro a b c d
    have h1 := hcyc a b c d
    have h2 := hcyc b c a d
    linarith
  -- first Bianchi identity + cyclicity force the component to vanish
  funext a b c d
  change R a b c d = 0
  have h1 := h.2.2 a b c d
  have h2 := hcyc a b c d
  have h3 := hcyc2 a b c d
  linarith

end Work.Diff.Alg.Pinch
