import Mathlib

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Plancherel's identity for the discrete Fourier transform on `ZMod N`

`Work.Peluse.U2Inv.u2inv_dft_plancherel` is the `L²`-isometry (Plancherel) property of the
discrete Fourier transform `ZMod.dft` on the cyclic group `ZMod N` with the counting measure:

`∑_ξ ‖𝓕 F ξ‖² = N · ∑_x ‖F x‖²`.

The proof is the standard explicit one: expand `𝓕 F ξ` and `conj (𝓕 F ξ)`, exchange the order of
summation, and evaluate the resulting additive-character sum with the orthogonality relation
`∑_ξ χ(ξ · b) = N` if `b = 0` and `0` otherwise (`AddChar.sum_mulShift`, primitivity of
`ZMod.stdAddChar`).  The diagonal case `G = F` of the sesquilinear Parseval identity is what is
needed; it is proved here as the auxiliary lemma `dft_parseval`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.U2Inv

noncomputable section

section Plancherel

variable {N : ℕ} [NeZero N]

/-- The standard additive character takes conjugate values at opposite points:
`conj (χ x) = χ (-x)`. -/
private lemma star_stdAddChar (x : ZMod N) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have h1 : star (ZMod.stdAddChar x) = (ZMod.stdAddChar x)⁻¹ := by
    rw [ZMod.stdAddChar_apply, Complex.star_def]
    exact (Circle.coe_inv_eq_conj (ZMod.toCircle x)).symm
  rw [h1, ← AddChar.map_neg_eq_inv]

/-- The conjugate of the discrete Fourier transform, expanded as a character-weighted sum. -/
private lemma dft_star (G : ZMod N → ℂ) (ξ : ZMod N) :
    star (ZMod.dft G ξ) = ∑ k : ZMod N, ZMod.stdAddChar (k * ξ) * star (G k) := by
  rw [ZMod.dft_apply]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_eq_mul, star_mul]
  rw [star_stdAddChar]
  ring_nf

/-- Orthogonality of the standard additive character: the sum over `ξ` of `χ (b * ξ)` vanishes
unless `b = 0`, in which case it is `N`. -/
private lemma char_sum (b : ZMod N) :
    (∑ ξ : ZMod N, ZMod.stdAddChar (b * ξ)) = if b = 0 then (N : ℂ) else 0 := by
  rw [show (∑ ξ : ZMod N, ZMod.stdAddChar (b * ξ))
        = ∑ ξ : ZMod N, ZMod.stdAddChar (ξ * b) by
      apply Finset.sum_congr rfl; intro ξ _; rw [mul_comm]]
  rw [AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar N)]
  by_cases hb : b = 0
  · rw [if_pos hb, if_pos hb, ZMod.card]
  · rw [if_neg hb, if_neg hb]; simp

/-- Parseval's identity in sesquilinear form: the discrete Fourier transform is (up to the
factor `N`) an isometry for the hermitian form `(F, G) ↦ ∑_x F x * conj (G x)`. -/
private lemma dft_parseval (F G : ZMod N → ℂ) :
    (∑ ξ : ZMod N, ZMod.dft F ξ * star (ZMod.dft G ξ))
      = (N : ℂ) * ∑ x : ZMod N, F x * star (G x) := by
  classical
  have step1 : ∀ ξ : ZMod N, ZMod.dft F ξ * star (ZMod.dft G ξ)
      = ∑ j : ZMod N, ∑ k : ZMod N,
          ZMod.stdAddChar ((k - j) * ξ) * (F j * star (G k)) := by
    intro ξ
    rw [ZMod.dft_apply, dft_star, Finset.sum_mul_sum]
    simp only [smul_eq_mul]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    have hchar : ZMod.stdAddChar (-(j * ξ)) * ZMod.stdAddChar (k * ξ)
        = ZMod.stdAddChar ((k - j) * ξ) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [← hchar]
    ring
  rw [Finset.sum_congr rfl (fun ξ _ => step1 ξ)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
  have hinner : ∀ j k : ZMod N,
      (∑ ξ : ZMod N, ZMod.stdAddChar ((k - j) * ξ) * (F j * star (G k)))
      = (if k - j = 0 then (N : ℂ) else 0) * (F j * star (G k)) := by
    intro j k
    rw [← Finset.sum_mul, char_sum]
  rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => hinner _ _))]
  rw [show (∑ j : ZMod N, ∑ k : ZMod N,
        (if k - j = 0 then (N : ℂ) else 0) * (F j * star (G k)))
      = ∑ j : ZMod N, (N : ℂ) * (F j * star (G j)) from by
    apply Finset.sum_congr rfl; intro j _
    have hk : (∑ k : ZMod N, (if k - j = 0 then (N : ℂ) else 0) * (F j * star (G k)))
        = ∑ k : ZMod N, (if k = j then (N : ℂ) * (F j * star (G k)) else 0) := by
      apply Finset.sum_congr rfl; intro k _
      by_cases h : k = j
      · rw [if_pos (sub_eq_zero.mpr h), if_pos h]
      · rw [if_neg (fun hc => h (sub_eq_zero.mp hc)), if_neg h, zero_mul]
    rw [hk, Finset.sum_ite_eq' Finset.univ j (fun k => (N : ℂ) * (F j * star (G k)))]
    simp]
  rw [Finset.mul_sum]

/-- The real part of `z * conj z` is the square of the norm of `z`. -/
private lemma re_mul_star (z : ℂ) : (z * star z).re = ‖z‖ ^ 2 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end Plancherel

theorem u2inv_dft_plancherel (N : ℕ) [NeZero N] (F : ZMod N → ℂ) :
    (∑ ξ : ZMod N, ‖ZMod.dft F ξ‖ ^ 2) = (N : ℝ) * ∑ x : ZMod N, ‖F x‖ ^ 2 := by
  have h := dft_parseval F F
  have hre := congrArg Complex.re h
  rw [Complex.re_sum] at hre
  simp only [re_mul_star] at hre
  have hrhs : ((N : ℂ) * ∑ x : ZMod N, F x * star (F x)).re
      = (N : ℝ) * ∑ x : ZMod N, ‖F x‖ ^ 2 := by
    have hcast : (N : ℂ) = ((N : ℝ) : ℂ) := (Complex.ofReal_natCast N).symm
    rw [hcast, Complex.re_ofReal_mul, Complex.re_sum]
    apply congrArg ((N : ℝ) * ·)
    apply Finset.sum_congr rfl
    intro x _
    exact re_mul_star (F x)
  rw [← hrhs]
  exact hre

end

end Work.Peluse.U2Inv
