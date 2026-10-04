import Mathlib
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `|det|²`-invariance of the complex isotropic curvature: the algebraic core of `q2p_transform`

This module proves `Work.Diff.Alg.q2p_transform`: for an algebraic curvature tensor `R` the complex
isotropic curvature (the real form `EFunC R z w = R(ζ, η, ζ̄, η̄)` with `ζ = Re z + i Im z` and
`η = Re w + i Im w`) transforms under a `ℂ`-linear change of basis
`(ζ, η) ↦ (a ζ + b η, c ζ + d η)` by the factor `|ad − bc|²`.

The route is the classical one: extend `R4` to a `ℂ`-multilinear form
`cR4 R a b c d = ∑ Rᵢⱼₖₗ aᵢ bⱼ cₖ dₗ`.  Then
* `Re (cR4 R ζ η ζ̄ η̄) = EFunC R ζ η` (the standard real expression of the isotropic curvature),
* `cR4` is `ℂ`-multilinear and alternating in the first and in the last pair, so that on the span of
  the vectors involved the two-dimensional determinant rule applies, giving the scalar
  `(ad − bc)·overline(ad − bc) = |ad − bc|²` on the surviving term.
-/

namespace Work.Diff.Alg

open Finset Submission.Diff.Alg
open Work.Diff.Alg.Q2P

variable {n : ℕ}

/-! ## The complexified curvature tensor -/

/-- `ℂ`-multilinear extension of `R4`: `cR4 R a b c d = ∑ᵢⱼₖₗ Rᵢⱼₖₗ aᵢ bⱼ cₖ dₗ`. -/
noncomputable def cR4 (R : Curv4 n) (a b c d : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, (R i j k l : ℂ) * a i * b j * c k * d l

/-- The real vector `a` regarded as a complex vector. -/
abbrev ofR (a : Fin n → ℝ) : Fin n → ℂ := fun i => (a i : ℂ)

/-! ## Reordering a four-fold sum (complex valued) -/

theorem sum4_swap12C {A : Type*} [AddCommMonoid A] (F : Fin n → Fin n → Fin n → Fin n → A) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F j i k l := by
  rw [Finset.sum_comm]

theorem sum4_swap34C {A : Type*} [AddCommMonoid A] (F : Fin n → Fin n → Fin n → Fin n → A) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F i j l k := by
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]

/-! ## Multilinearity of `cR4` -/

theorem cR4_add₁ (R : Curv4 n) (a a' b c d : Fin n → ℂ) :
    cR4 R (a + a') b c d = cR4 R a b c d + cR4 R a' b c d := by
  simp only [cR4, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem cR4_add₂ (R : Curv4 n) (a b b' c d : Fin n → ℂ) :
    cR4 R a (b + b') c d = cR4 R a b c d + cR4 R a b' c d := by
  simp only [cR4, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem cR4_add₃ (R : Curv4 n) (a b c c' d : Fin n → ℂ) :
    cR4 R a b (c + c') d = cR4 R a b c d + cR4 R a b c' d := by
  simp only [cR4, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem cR4_add₄ (R : Curv4 n) (a b c d d' : Fin n → ℂ) :
    cR4 R a b c (d + d') = cR4 R a b c d + cR4 R a b c d' := by
  simp only [cR4, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem cR4_smul₁ (R : Curv4 n) (t : ℂ) (a b c d : Fin n → ℂ) :
    cR4 R (t • a) b c d = t * cR4 R a b c d := by
  simp only [cR4, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]; simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

theorem cR4_smul₂ (R : Curv4 n) (t : ℂ) (a b c d : Fin n → ℂ) :
    cR4 R a (t • b) c d = t * cR4 R a b c d := by
  simp only [cR4, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]; simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

theorem cR4_smul₃ (R : Curv4 n) (t : ℂ) (a b c d : Fin n → ℂ) :
    cR4 R a b (t • c) d = t * cR4 R a b c d := by
  simp only [cR4, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]; simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

theorem cR4_smul₄ (R : Curv4 n) (t : ℂ) (a b c d : Fin n → ℂ) :
    cR4 R a b c (t • d) = t * cR4 R a b c d := by
  simp only [cR4, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]; simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

/-! ## Alternation of `cR4` in the two pairs -/

theorem cR4_antisym₁₂ (R : Curv4 n) (hR : IsAlgCurv R) (x y z w : Fin n → ℂ) :
    cR4 R y x z w = - cR4 R x y z w := by
  calc cR4 R y x z w = ∑ i, ∑ j, ∑ k, ∑ l, (R i j k l : ℂ) * y i * x j * z k * w l := rfl
    _ = ∑ i, ∑ j, ∑ k, ∑ l, (R j i k l : ℂ) * y j * x i * z k * w l := sum4_swap12C _
    _ = ∑ i, ∑ j, ∑ k, ∑ l, -((R i j k l : ℂ) * x i * y j * z k * w l) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        rw [hR.1 i j k l]; push_cast; ring
    _ = - cR4 R x y z w := by simp only [cR4, Finset.sum_neg_distrib]

theorem cR4_antisym₃₄ (R : Curv4 n) (hR : IsAlgCurv R) (x y z w : Fin n → ℂ) :
    cR4 R x y w z = - cR4 R x y z w := by
  calc cR4 R x y w z = ∑ i, ∑ j, ∑ k, ∑ l, (R i j k l : ℂ) * x i * y j * w k * z l := rfl
    _ = ∑ i, ∑ j, ∑ k, ∑ l, (R i j l k : ℂ) * x i * y j * w l * z k := sum4_swap34C _
    _ = ∑ i, ∑ j, ∑ k, ∑ l, -((R i j k l : ℂ) * x i * y j * z k * w l) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        rw [IsAlgCurv_antisym₃₄ hR i j k l]; push_cast; ring
    _ = - cR4 R x y z w := by simp only [cR4, Finset.sum_neg_distrib]

theorem cR4_self₁ (R : Curv4 n) (hR : IsAlgCurv R) (x z w : Fin n → ℂ) :
    cR4 R x x z w = 0 := by
  have h := cR4_antisym₁₂ R hR x x z w
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp h)

theorem cR4_self₂ (R : Curv4 n) (hR : IsAlgCurv R) (x y z : Fin n → ℂ) :
    cR4 R x y z z = 0 := by
  have h := cR4_antisym₃₄ R hR x y z z
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp h)

/-- On real vectors `cR4` is `R4` with real scalars. -/
theorem cR4_ofR (R : Curv4 n) (a b c d : Fin n → ℝ) :
    cR4 R (ofR a) (ofR b) (ofR c) (ofR d) = (R4 R a b c d : ℂ) := by
  simp only [cR4, R4, ofR]
  push_cast
  rfl

/-! ## Full expansion of `cR4` on four two-term combinations -/

theorem cR4_expand (R : Curv4 n) (a1 a2 b1 b2 c1 c2 d1 d2 : ℂ)
    (p1 p2 p3 p4 q1 q2 q3 q4 : Fin n → ℂ) :
    cR4 R (a1•p1 + a2•q1) (b1•p2 + b2•q2) (c1•p3 + c2•q3) (d1•p4 + d2•q4)
    = a1*b1*c1*d1 * cR4 R p1 p2 p3 p4 + a1*b1*c1*d2 * cR4 R p1 p2 p3 q4
    + a1*b1*c2*d1 * cR4 R p1 p2 q3 p4 + a1*b1*c2*d2 * cR4 R p1 p2 q3 q4
    + a1*b2*c1*d1 * cR4 R p1 q2 p3 p4 + a1*b2*c1*d2 * cR4 R p1 q2 p3 q4
    + a1*b2*c2*d1 * cR4 R p1 q2 q3 p4 + a1*b2*c2*d2 * cR4 R p1 q2 q3 q4
    + a2*b1*c1*d1 * cR4 R q1 p2 p3 p4 + a2*b1*c1*d2 * cR4 R q1 p2 p3 q4
    + a2*b1*c2*d1 * cR4 R q1 p2 q3 p4 + a2*b1*c2*d2 * cR4 R q1 p2 q3 q4
    + a2*b2*c1*d1 * cR4 R q1 q2 p3 p4 + a2*b2*c1*d2 * cR4 R q1 q2 p3 q4
    + a2*b2*c2*d1 * cR4 R q1 q2 q3 p4 + a2*b2*c2*d2 * cR4 R q1 q2 q3 q4 := by
  simp only [cR4_add₁, cR4_smul₁, cR4_add₂, cR4_smul₂, cR4_add₃, cR4_smul₃, cR4_add₄, cR4_smul₄]
  ring

/-! ## The algebraic Bianchi identity for `R4` -/

theorem sum3_add_eq {ι : Type*} [Fintype ι] (f g h : ι → ℝ) :
    (∑ i, f i) + (∑ i, g i) + (∑ i, h i) = ∑ i, (f i + g i + h i) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

theorem R4_cycle₁ (R : Curv4 n) (x y z w : Fin n → ℝ) :
    R4 R y z x w = ∑ i, ∑ j, ∑ k, ∑ l, R j k i l * x i * y j * z k * w l := by
  calc R4 R y z x w = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * y i * z j * x k * w l := rfl
    _ = ∑ i, ∑ j, ∑ k, ∑ l, R j k i l * y j * z k * x i * w l := sum4_cycle _
    _ = ∑ i, ∑ j, ∑ k, ∑ l, R j k i l * x i * y j * z k * w l := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        ring

theorem R4_cycle₂ (R : Curv4 n) (x y z w : Fin n → ℝ) :
    R4 R z x y w = ∑ i, ∑ j, ∑ k, ∑ l, R k i j l * x i * y j * z k * w l := by
  calc R4 R z x y w = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * z i * x j * y k * w l := rfl
    _ = ∑ i, ∑ j, ∑ k, ∑ l, R k i j l * z k * x i * y j * w l := sum4_cycle2 _
    _ = ∑ i, ∑ j, ∑ k, ∑ l, R k i j l * x i * y j * z k * w l := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        ring

/-- Cyclic-form Bianchi identity: `R4 x y z w + R4 y z x w + R4 z x y w = 0`. -/
theorem R4_bianchi (n : ℕ) (R : Curv4 n) (hR : IsAlgCurv R) (x y z w : Fin n → ℝ) :
    R4 R x y z w + R4 R y z x w + R4 R z x y w = 0 := by
  have h1 : R4 R x y z w = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * x i * y j * z k * w l := rfl
  have hz : ∀ i j k l : Fin n,
      R i j k l * x i * y j * z k * w l + R j k i l * x i * y j * z k * w l
        + R k i j l * x i * y j * z k * w l = 0 := by
    intro i j k l
    calc R i j k l * x i * y j * z k * w l + R j k i l * x i * y j * z k * w l
          + R k i j l * x i * y j * z k * w l
        = (R i j k l + R j k i l + R k i j l) * (x i * y j * z k * w l) := by ring
      _ = 0 := by rw [hR.2.2 i j k l, zero_mul]
  rw [h1, R4_cycle₁ R x y z w, R4_cycle₂ R x y z w]
  rw [sum3_add_eq]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [sum3_add_eq]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [sum3_add_eq]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [sum3_add_eq]
  exact Finset.sum_eq_zero (fun l _ => hz i j k l)

/-! ## The real isotropic-curvature expression from the eight surviving terms -/

/-- The real part of `cR4 R ζ η ζ̄ η̄` collapses (via the pair symmetries and Bianchi) to `EFun`. -/
theorem eight_to_EFun (R : Curv4 n) (hR : IsAlgCurv R) (x y z w : Fin n → ℝ) :
    R4 R x z x z + R4 R x w x w + R4 R y z y z + R4 R y w y w
      - R4 R x z y w + R4 R x w y z + R4 R y z x w - R4 R y w x z
      = EFun R x y z w := by
  have h1 : R4 R x z y w = R4 R x y z w + R4 R y z x w := by
    have hb := R4_bianchi n R hR z x y w
    have ha := R4_antisym₁₂ R hR z x y w
    linarith
  have h2 : R4 R y w x z = R4 R x y z w + R4 R y z x w := by
    rw [show R4 R y w x z = R4 R x z y w from (R4_pair_symm R hR y w x z).symm, h1]
  have h3 : R4 R x w y z = R4 R y z x w := (R4_pair_symm R hR x w y z).symm
  rw [h1, h2, h3, EFun]
  ring

/-! ## `Re (cR4 R ζ η ζ̄ η̄) = EFunC R ζ η` -/

theorem cR4_re_special (R : Curv4 n) (hR : IsAlgCurv R) (x y z w : Fin n → ℝ) :
    (cR4 R ((1:ℂ) • ofR x + Complex.I • ofR y) ((1:ℂ) • ofR z + Complex.I • ofR w)
        ((1:ℂ) • ofR x + (-Complex.I) • ofR y)
        ((1:ℂ) • ofR z + (-Complex.I) • ofR w)).re = EFun R x y z w := by
  rw [cR4_expand R 1 Complex.I 1 Complex.I 1 (-Complex.I) 1 (-Complex.I)
        (ofR x) (ofR z) (ofR x) (ofR z) (ofR y) (ofR w) (ofR y) (ofR w)]
  simp only [cR4_ofR]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
  ring_nf
  linarith [eight_to_EFun R hR x y z w]

theorem ofR_cRe_cIm (ζ : Fin n → ℂ) :
    ζ = (1:ℂ) • ofR (cRe ζ) + Complex.I • ofR (cIm ζ) := by
  ext i
  simp only [ofR, cRe, cIm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
  rw [mul_comm Complex.I]
  exact (Complex.re_add_im (ζ i)).symm

theorem star_ofR_cRe_cIm (ζ : Fin n → ℂ) :
    star ζ = (1:ℂ) • ofR (cRe ζ) + (-Complex.I) • ofR (cIm ζ) := by
  ext i
  simp only [ofR, cRe, cIm, Pi.add_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, one_mul]
  conv_lhs => rw [Complex.star_def, ← Complex.re_add_im (ζ i), map_add, map_mul]
  simp only [Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The complex isotropic curvature is the real part of `cR4 R ζ η ζ̄ η̄`. -/
theorem cR4_re (R : Curv4 n) (hR : IsAlgCurv R) (ζ η : Fin n → ℂ) :
    (cR4 R ζ η (star ζ) (star η)).re = EFunC R ζ η := by
  have key := cR4_re_special R hR (cRe ζ) (cIm ζ) (cRe η) (cIm η)
  rw [← star_ofR_cRe_cIm ζ, ← star_ofR_cRe_cIm η] at key
  rw [← ofR_cRe_cIm ζ, ← ofR_cRe_cIm η] at key
  exact key

/-! ## The determinant factor -/

theorem coeff_normSq (a b c d : ℂ) :
    a * d * star a * star d - a * d * star b * star c - b * c * star a * star d
      + b * c * star b * star c = (Complex.normSq (a * d - b * c) : ℂ) := by
  have h : (a * d - b * c) * star (a * d - b * c) = (Complex.normSq (a * d - b * c) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  rw [← h, Complex.star_def, map_sub, map_mul, map_mul]
  ring

/-! ## The transformation identity for `cR4` -/

theorem comb_eq_smul_add (a b : ℂ) (z w : Fin n → ℂ) : comb a b z w = a • z + b • w := rfl

theorem star_comb (a b : ℂ) (z w : Fin n → ℂ) :
    star (comb a b z w) = (star a) • (star z) + (star b) • (star w) := by
  ext i
  simp only [comb, Pi.add_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul,
    Complex.star_def, map_add, map_mul]

/-- The `GL₂(ℂ)` transformation law for the complexified curvature tensor. -/
theorem cR4_comb (R : Curv4 n) (hR : IsAlgCurv R) (z w : Fin n → ℂ) (a b c d : ℂ) :
    cR4 R (comb a b z w) (comb c d z w) (star (comb a b z w)) (star (comb c d z w))
      = (Complex.normSq (a * d - b * c) : ℂ) * cR4 R z w (star z) (star w) := by
  rw [star_comb a b z w, star_comb c d z w,
      comb_eq_smul_add a b z w, comb_eq_smul_add c d z w,
      cR4_expand R a b c d (star a) (star b) (star c) (star d)
        z z (star z) (star z) w w (star w) (star w)]
  simp only [cR4_self₁ R hR, cR4_self₂ R hR, mul_zero, zero_mul, add_zero, zero_add]
  rw [cR4_antisym₃₄ R hR z w (star z) (star w), cR4_antisym₁₂ R hR z w (star z) (star w),
      cR4_antisym₁₂ R hR z w (star w) (star z), cR4_antisym₃₄ R hR z w (star z) (star w)]
  rw [← coeff_normSq a b c d]
  ring

/-! ## The target -/

theorem q2p_transform {n : ℕ} (R : Submission.Diff.Alg.Curv4 n) (hR : Submission.Diff.Alg.IsAlgCurv R)
    (z w : Fin n → ℂ) (a b c d : ℂ) :
    Work.Diff.Alg.Q2P.EFunC R (Work.Diff.Alg.Q2P.comb a b z w)
      (Work.Diff.Alg.Q2P.comb c d z w)
      = Complex.normSq (a * d - b * c) * Work.Diff.Alg.Q2P.EFunC R z w := by
  have hZ := cR4_re R hR (comb a b z w) (comb c d z w)
  have hexp := cR4_comb R hR z w a b c d
  have hzw := cR4_re R hR z w
  rw [← hZ, hexp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hzw]

end Work.Diff.Alg
