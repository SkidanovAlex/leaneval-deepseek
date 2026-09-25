/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `(0,1)`-form of a map which is antilinear for a perturbed complex structure

Let `V = ℂⁿ = Fin n → ℂ` (as a real vector space), `L : V →L[ℝ] ℂ` real-linear and
`B : V →L[ℝ] V` real-linear.  The main hypothesis of the auxiliary estimate
`Work.NN.Final.antilinear_sub_stdForm_bound` is that `L` is `Jstd + B`-antilinear:
`L ((Jstd + B) w) = -I * L w` for all `w`, i.e. `L (I • w + B w) = -I * L w`.

This module sets up the objects attached to such a pair `(L, B)`:

* `lambdaOf L B = L ∘ B` is `ℂ`-linear;
* `psiOf L B = L - (i/2) λ` is `ℂ`-antilinear;
* `avec L B k = i * λ (e_k)`, `bvec L B k = 2 * ψ (e_k)`, `hvec = avec + bvec`,
  `cvec k = L (e_k) = (avec k + bvec k)/2`;
* the complex-linear map `SOf L B` with `SOf x = B x` for real `x` and the complex-linear
  map `DOf L B` with `DOf x = -i B (i x)` for real `x` (so that `B (x + i y) = S x + i D y`).
-/

import Mathlib
import Submission.Work.NN.Final.Defs

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

open Work.NN.Core

noncomputable section

variable {n : ℕ}

/-! ## Definitions -/

/-- `λ = L ∘ B` for `L` real-linear `ℂ`-valued and `B` real-linear on `ℂⁿ`. -/
def lamOf (L : Cn n →L[ℝ] ℂ) (B : Cn n →L[ℝ] Cn n) : Cn n → ℂ := fun w => L (B w)

/-- `ψ = L - (i/2) λ`, the `ℂ`-antilinear part of `L`. -/
def psiOf (L : Cn n →L[ℝ] ℂ) (B : Cn n →L[ℝ] Cn n) : Cn n → ℂ :=
  fun w => L w - (Complex.I / 2) * lamOf L B w

/-- The coefficients `a_k = i * λ (e_k)` of the `ℂ`-linear part of `L`. -/
def avec (L : Cn n →L[ℝ] ℂ) (B : Cn n →L[ℝ] Cn n) : Fin n → ℂ :=
  fun k => Complex.I * lamOf L B (Pi.single k 1)

/-- The coefficients `b_k = 2 * ψ (e_k)`. -/
def bvec (L : Cn n →L[ℝ] ℂ) (B : Cn n →L[ℝ] Cn n) : Fin n → ℂ :=
  fun k => 2 * psiOf L B (Pi.single k 1)

/-- `h = a + b`. -/
def hvec (L : Cn n →L[ℝ] ℂ) (B : Cn n →L[ℝ] Cn n) : Fin n → ℂ :=
  fun k => avec L B k + bvec L B k

/-- The `ℂ`-linear map `S` such that `B (x + i y) = S x + i D y` for real `x, y`. -/
def SOf (B : Cn n →L[ℝ] Cn n) : Cn n → Cn n :=
  fun w => B (fun k => ((w k).re : ℂ)) + Complex.I • B (fun k => ((w k).im : ℂ))

/-- The `ℂ`-linear map `D` such that `B (x + i y) = S x + i D y` for real `x, y`. -/
def DOf (B : Cn n →L[ℝ] Cn n) : Cn n → Cn n :=
  fun w => B (fun k => ((w k).im : ℂ))
    - Complex.I • B (fun k => ((Complex.I * (w k).re : ℂ)))

/-- The real matrix `X = Re S`. -/
def XOf (B : Cn n →L[ℝ] Cn n) : Cn n → Cn n :=
  fun w => fun k => (((SOf B) w k).re : ℂ)

/-- The real matrix `U = Im S`. -/
def UOf (B : Cn n →L[ℝ] Cn n) : Cn n → Cn n :=
  fun w => fun k => (((SOf B) w k).im : ℂ)

/-- The real matrix `V = Re D`. -/
def VOf (B : Cn n →L[ℝ] Cn n) : Cn n → Cn n :=
  fun w => fun k => (((DOf B) w k).re : ℂ)

/-- The real matrix `Y = Im D`. -/
def YOf (B : Cn n →L[ℝ] Cn n) : Cn n → Cn n :=
  fun w => fun k => (((DOf B) w k).im : ℂ)


/-! ## Elementary lemmas -/

section Basic

variable {L : Cn n →L[ℝ] ℂ} {B : Cn n →L[ℝ] Cn n}

lemma lamOf_add (v w : Cn n) : lamOf L B (v + w) = lamOf L B v + lamOf L B w := by
  simp [lamOf, map_add]

lemma lamOf_smul (c : ℝ) (v : Cn n) : lamOf L B (c • v) = c * lamOf L B v := by
  simp [lamOf]

/-- `λ = L ∘ B` is `ℂ`-linear, provided `L` is `Jstd + B`-antilinear. -/
lemma lamOf_I (hc : ∀ w, L (Complex.I • w + B w) = -Complex.I * L w) (w : Cn n) :
    lamOf L B (Complex.I • w) = Complex.I * lamOf L B w := by
  have h1 : L (Complex.I • w) = -Complex.I * L w - L (B w) := by
    have h : L (Complex.I • w) + L (B w) = -Complex.I * L w := by
      rw [← map_add]; exact hc w
    linear_combination h
  have h2 : L (Complex.I • (Complex.I • w)) + L (B (Complex.I • w))
      = -Complex.I * L (Complex.I • w) := by
    rw [← map_add]; exact hc (Complex.I • w)
  have hII : Complex.I • (Complex.I • w) = -w := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [hII, map_neg] at h2
  have h3 : -Complex.I * (-Complex.I * L w - L (B w))
      = -L w + Complex.I * L (B w) := by
    ring_nf
    rw [show Complex.I ^ 2 = -1 by rw [pow_two, Complex.I_mul_I]]
    ring
  rw [h1, h3] at h2
  simp only [lamOf]
  linear_combination h2

/-- `ψ` is `ℂ`-antilinear on the distinguished real complex structure. -/
lemma psiOf_I (hc : ∀ w, L (Complex.I • w + B w) = -Complex.I * L w) (w : Cn n) :
    psiOf L B (Complex.I • w) = -Complex.I * psiOf L B w := by
  have h : L (Complex.I • w) + L (B w) = -Complex.I * L w := by
    rw [← map_add]; exact hc w
  have h1 : L (Complex.I • w) = -Complex.I * L w - lamOf L B w := by
    rw [eq_sub_iff_add_eq, show lamOf L B w = L (B w) from rfl]
    exact h
  have h2 : lamOf L B (Complex.I • w) = Complex.I * lamOf L B w := lamOf_I hc w
  simp only [psiOf, h1, h2]
  ring_nf
  rw [show Complex.I ^ 2 = -1 by rw [pow_two, Complex.I_mul_I]]
  ring

lemma psiOf_add (v w : Cn n) : psiOf L B (v + w) = psiOf L B v + psiOf L B w := by
  simp only [psiOf, lamOf_add, map_add]
  ring

lemma psiOf_real_smul (r : ℝ) (v : Cn n) : psiOf L B (r • v) = (r : ℂ) * psiOf L B v := by
  simp only [psiOf, lamOf_smul, map_smul, Complex.real_smul]
  ring

/-- Decomposition of the `ℂ`-action into the `ℝ`-action. -/
lemma complex_smul_decomp (c : ℂ) (w : Cn n) :
    c • w = (c.re : ℝ) • w + (c.im : ℝ) • (Complex.I • w) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- The component of a sum of `Pi.single`s. -/
lemma sum_smul_single_apply (w : Cn n) (k : Fin n) :
    (∑ i, w i • (Pi.single i (1 : ℂ) : Cn n)) k = w k := by
  rw [Finset.sum_apply, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb)]
    simp
  · intro h; exact absurd (Finset.mem_univ k) h

/-- `λ` is `ℂ`-linear for complex scalars. -/
lemma lamOf_complex_smul (hc : ∀ w, L (Complex.I • w + B w) = -Complex.I * L w)
    (c : ℂ) (w : Cn n) : lamOf L B (c • w) = c * lamOf L B w := by
  rw [complex_smul_decomp c w, lamOf_add, lamOf_smul, lamOf_smul, lamOf_I hc]
  push_cast
  conv_rhs => rw [← Complex.re_add_im c]
  ring

/-- `ψ` is `ℂ`-antilinear for complex scalars. -/
lemma psiOf_complex_smul (hc : ∀ w, L (Complex.I • w + B w) = -Complex.I * L w)
    (c : ℂ) (w : Cn n) : psiOf L B (c • w) = star c * psiOf L B w := by
  rw [complex_smul_decomp c w, psiOf_add, psiOf_real_smul, psiOf_real_smul, psiOf_I hc]
  push_cast
  conv_rhs => rw [← Complex.re_add_im c]
  simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.star_def]
  ring

lemma smul_single_one (i : Fin n) (c : ℂ) :
    (Pi.single i c : Cn n) = c • (Pi.single i (1 : ℂ) : Cn n) := by
  ext k
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

lemma lamOf_sum {ι : Type*} (s : Finset ι) (f : ι → Cn n) :
    lamOf L B (∑ i ∈ s, f i) = ∑ i ∈ s, lamOf L B (f i) := by
  simp only [lamOf]
  rw [map_sum, map_sum]

lemma psiOf_sum {ι : Type*} (s : Finset ι) (f : ι → Cn n) :
    psiOf L B (∑ i ∈ s, f i) = ∑ i ∈ s, psiOf L B (f i) := by
  simp only [psiOf, lamOf]
  rw [map_sum, map_sum, map_sum, Finset.mul_sum, Finset.sum_sub_distrib]

/-- The representation of `L` by its `λ`- and `ψ`-coefficients. -/
lemma L_decomp (hc : ∀ w, L (Complex.I • w + B w) = -Complex.I * L w) (w : Cn n) :
    L w = (Complex.I / 2) * (∑ k, lamOf L B (Pi.single k 1) * w k)
      + ∑ k, psiOf L B (Pi.single k 1) * star (w k) := by
  have hw : w = ∑ k, w k • (Pi.single k (1 : ℂ) : Cn n) := by
    conv_lhs => rw [← Finset.univ_sum_single w]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact smul_single_one k (w k)
  have hlam : lamOf L B (∑ k, w k • (Pi.single k (1 : ℂ) : Cn n))
      = ∑ k, w k * lamOf L B (Pi.single k 1) := by
    rw [lamOf_sum Finset.univ]
    exact Finset.sum_congr rfl fun k _ => lamOf_complex_smul hc _ _
  have hpsi : psiOf L B (∑ k, w k • (Pi.single k (1 : ℂ) : Cn n))
      = ∑ k, star (w k) * psiOf L B (Pi.single k 1) := by
    rw [psiOf_sum Finset.univ]
    exact Finset.sum_congr rfl fun k _ => psiOf_complex_smul hc _ _
  have hmain : L w = (Complex.I / 2) * lamOf L B w + psiOf L B w := by
    simp only [psiOf]; ring
  rw [hmain, hw, hlam, hpsi]
  simp only [sum_smul_single_apply]
  rw [Finset.mul_sum (s := Finset.univ)
    (f := fun k : Fin n => lamOf L B (Pi.single k 1) * w k)]
  rw [Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => by ring
  · exact Finset.sum_congr rfl fun k _ => by ring
/-- The value of `L` at a basis vector, in terms of `a` and `b`. -/
lemma cvec_eq (hc : ∀ w, L (Complex.I • w + B w) = -Complex.I * L w) (k : Fin n) :
    L (Pi.single k (1 : ℂ)) = (avec L B k + bvec L B k) / 2 := by
  have h := L_decomp (L := L) (B := B) hc (Pi.single k (1 : ℂ))
  rw [h]
  have h1 : (∑ j, lamOf L B (Pi.single j 1) * (Pi.single k (1:ℂ) : Cn n) j)
      = lamOf L B (Pi.single k 1) := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; rw [Pi.single_apply, if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  have h2 : (∑ j, psiOf L B (Pi.single j 1) * star ((Pi.single k (1:ℂ) : Cn n) j))
      = psiOf L B (Pi.single k 1) := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; rw [Pi.single_apply, if_neg hb, star_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [h1, h2]
  simp only [avec, bvec, lamOf]
  ring

/-- The `(0,1)`-form defect: `L w` minus the standard form with coefficients `L (e_k)`. -/
lemma stdForm_sub (hc : ∀ w, L (Complex.I • w + B w) = -Complex.I * L w) (w : Cn n) :
    L w - ∑ k, ((avec L B k + bvec L B k) / 2) * star (w k)
      = Complex.I * ∑ k, avec L B k * ((w k).im : ℂ) := by
  rw [L_decomp hc w]
  have hsplit : (∑ k, ((avec L B k + bvec L B k) / 2) * star (w k))
      = (∑ k, (Complex.I / 2) * lamOf L B (Pi.single k 1) * star (w k))
        + ∑ k, psiOf L B (Pi.single k 1) * star (w k) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [avec, bvec]
    ring
  rw [hsplit]
  have h1 : (Complex.I / 2) * (∑ k, lamOf L B (Pi.single k 1) * w k)
        + (∑ k, psiOf L B (Pi.single k 1) * star (w k))
        - ((∑ k, (Complex.I / 2) * lamOf L B (Pi.single k 1) * star (w k))
          + ∑ k, psiOf L B (Pi.single k 1) * star (w k))
      = (Complex.I / 2) * (∑ k, lamOf L B (Pi.single k 1) * w k)
        - (∑ k, (Complex.I / 2) * lamOf L B (Pi.single k 1) * star (w k)) := by
    ring
  rw [h1]
  have hkey : ∀ k : Fin n, (Complex.I / 2) * lamOf L B (Pi.single k 1) * w k
      - (Complex.I / 2) * lamOf L B (Pi.single k 1) * star (w k)
      = Complex.I * avec L B k * ((w k).im : ℂ) := by
    intro k
    have hw : (w k : ℂ) - star (w k) = 2 * Complex.I * ((w k).im : ℂ) := by
      apply Complex.ext <;>
        simp [Complex.star_def, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
          <;> ring
    have h2 : (Complex.I / 2) * lamOf L B (Pi.single k 1) * ((w k : ℂ) - star (w k))
        = (Complex.I / 2) * lamOf L B (Pi.single k 1) * w k
          - (Complex.I / 2) * lamOf L B (Pi.single k 1) * star (w k) := by ring
    rw [← h2, hw, avec]
    ring
  rw [Finset.mul_sum (s := Finset.univ)
    (f := fun k : Fin n => lamOf L B (Pi.single k 1) * w k)]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum (s := Finset.univ)
    (f := fun k : Fin n => avec L B k * ((w k).im : ℂ))]
  exact Finset.sum_congr rfl fun k _ => by linear_combination hkey k

/-- Cauchy–Schwarz bound for the defect. -/
lemma norm_stdForm_sub (hc : ∀ w, L (Complex.I • w + B w) = -Complex.I * L w) (w : Cn n) :
    ‖L w - ∑ k, ((avec L B k + bvec L B k) / 2) * star (w k)‖
      ≤ (∑ k, ‖avec L B k‖) * ‖w‖ := by
  rw [stdForm_sub hc w]
  have hsum : ‖∑ k, avec L B k * ((w k).im : ℂ)‖ ≤ ∑ k, ‖avec L B k‖ * ‖w‖ := by
    calc ‖∑ k, avec L B k * ((w k).im : ℂ)‖
        ≤ ∑ k, ‖avec L B k * ((w k).im : ℂ)‖ := norm_sum_le _ _
      _ = ∑ k, ‖avec L B k‖ * |(w k).im| := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, show ‖((((w k).im : ℝ)) : ℂ)‖ = |(w k).im| from by
            rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]]
      _ ≤ ∑ k, ‖avec L B k‖ * ‖w‖ := by
          refine Finset.sum_le_sum fun k _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          calc |(w k).im| ≤ ‖w k‖ := Complex.abs_im_le_norm _
            _ ≤ ‖w‖ := norm_le_pi_norm w k
  rw [norm_mul, Complex.norm_I, one_mul]
  calc ‖∑ k, avec L B k * ((w k).im : ℂ)‖ ≤ ∑ k, ‖avec L B k‖ * ‖w‖ := hsum
    _ = (∑ k, ‖avec L B k‖) * ‖w‖ := by rw [Finset.sum_mul]

end Basic

end

end Work.NN.Final
