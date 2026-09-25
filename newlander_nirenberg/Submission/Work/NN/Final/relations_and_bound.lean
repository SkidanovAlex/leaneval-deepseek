/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The core estimate relating the coefficients `a` and `h`

Let `V = ℂⁿ` (as a real vector space), `L : V →L[ℝ] ℂ` real-linear and `B : V →L[ℝ] V` real-linear
with `L` antilinear for the perturbed structure `I + B`:

  `L (I • w + B w) = -I * L w`  for all `w`.

Write `a k = avec L B k = I * L (B e_k)` for the coefficients of the `ℂ`-linear part `λ = L ∘ B`
of `L`, and `h k = hvec L B k = a k + b k` where `b k = 2 ψ(e_k)`.  Note `h k = 2 * L (e_k)`.

**Main result** (`relations_and_bound`): if `‖B‖ ≤ ε ≤ 1` then `∑ k, ‖a k‖ ≤ 6 ε ∑ k, ‖h k‖`.

## Structure of the proof

* Expanding `L` and `B` in the real basis `e_l = Pi.single l 1`, `I • e_l` gives, for every `l`,
  two complex relations (`rel_one`, `rel_two`); adding `-I` times the second to the first yields
  the linear system (`rel_comb`)

    `2 a_l + ∑ k, (im ((B e_l) k) - I * im ((B (I • e_l)) k)) * a_k
        = ∑ k, (I/2 * conj ((B e_l) k) + 1/2 * conj ((B (I • e_l)) k)) * h_k.`

* The coefficient matrix on the left and the matrix on the right both have rows bounded by `‖B‖`:
  the first is the "phase bound" `phase_bound` (a real-linear functional `φ` of norm at most one
  is applied to the coordinates of `B` on the complexified torus), the second follows from the
  elementary bounds `row_M_bound`, `row_N_bound`.
* Taking `ℓ¹` norms in the system and applying the row bounds gives
  `2 ∑ ‖a‖ ≤ 2 ‖B‖ ∑ ‖h‖ + ‖B‖ ∑ ‖a‖`, hence `∑ ‖a‖ ≤ 2 ‖B‖ ∑ ‖h‖ ≤ 6 ε ∑ ‖h‖`.
-/

import Mathlib
import Submission.Work.NN.Final.antilinear_defs

set_option maxHeartbeats 20000000
namespace Work.NN.Final

open Work.NN.Final Work.NN.Core

noncomputable section

variable {n : ℕ}

/-- The expansion of `z` in the real basis `e_l = Pi.single l 1`, `I • e_l`. -/
lemma self_expand (z : Cn n) :
    z = (∑ l : Fin n, ((z l).re : ℝ) • (Pi.single l (1 : ℂ) : Cn n))
      + ∑ l : Fin n, ((z l).im : ℝ) • (Complex.I • (Pi.single l (1 : ℂ) : Cn n)) := by
  have h1 : ∀ k : Fin n,
      (∑ l : Fin n, ((z l).re : ℝ) • (Pi.single l (1 : ℂ) : Cn n)) k = (z k).re := by
    intro k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · rw [Pi.smul_apply]; simp
    · intro b _ hb; rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  have h2 : ∀ k : Fin n,
      (∑ l : Fin n, ((z l).im : ℝ) • (Complex.I • (Pi.single l (1 : ℂ) : Cn n))) k
        = (z k).im • (Complex.I : ℂ) := by
    intro k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · rw [Pi.smul_apply, Pi.smul_apply]; simp
    · intro b _ hb
      rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero, smul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  ext k
  rw [Pi.add_apply, h1 k, h2 k, Complex.real_smul]
  exact (Complex.re_add_im (z k)).symm

/-- Expansion of `L z` in the real basis. -/
lemma L_expand (L : Cn n →L[ℝ] ℂ) (z : Cn n) :
    L z = ∑ l : Fin n, (((z l).re : ℂ) * L (Pi.single l (1 : ℂ))
        + ((z l).im : ℂ) * L (Complex.I • (Pi.single l (1 : ℂ)))) := by
  conv_lhs => rw [self_expand z]
  rw [map_add, map_sum, map_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- Expansion of `(B z) k` in the real basis. -/
lemma B_coord (B : Cn n →L[ℝ] Cn n) (z : Cn n) (k : Fin n) :
    (B z) k = ∑ l : Fin n, (((z l).re : ℂ) * ((B (Pi.single l (1 : ℂ))) k)
        + ((z l).im : ℂ) * ((B (Complex.I • (Pi.single l (1 : ℂ)))) k)) := by
  conv_lhs => rw [self_expand z]
  rw [map_add, map_sum, map_sum, Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, Complex.real_smul, Complex.real_smul]

/-- Norm of a complex number of the form `a - I * b` with `a b : ℝ`. -/
lemma norm_sub_I (a b : ℝ) : ‖(a : ℂ) - Complex.I * (b : ℂ)‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  have h : ‖(a : ℂ) - Complex.I * (b : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- Norm of a complex number of the form `a + I * b` with `a b : ℝ`. -/
lemma norm_add_I (a b : ℝ) : ‖(a : ℂ) + Complex.I * (b : ℂ)‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  have h : ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- **The phase bound.**  For a real-linear functional `φ` on `ℂ` (of norm at most one), the
`ℓ¹`-norm of the complex numbers `φ((B e_l) k) - I * φ((B (I • e_l)) k)` is at most `‖B‖`. -/
lemma phase_bound (φ : ℂ →ₗ[ℝ] ℝ) (hφ : ∀ z, ‖φ z‖ ≤ ‖z‖) (B : Cn n →L[ℝ] Cn n)
    (k : Fin n) :
    (∑ l : Fin n, ‖((φ ((B (Pi.single l (1 : ℂ))) k) : ℂ)
        - Complex.I * ((φ ((B (Complex.I • (Pi.single l (1 : ℂ)))) k)) : ℂ))‖) ≤ ‖B‖ := by
  classical
  let m : Fin n → ℝ := fun l => φ ((B (Pi.single l (1 : ℂ))) k)
  let m' : Fin n → ℝ := fun l => φ ((B (Complex.I • (Pi.single l (1 : ℂ)))) k)
  let c : Fin n → ℝ := fun l => ‖((m l : ℂ) - Complex.I * (m' l : ℂ))‖
  have hcsq : ∀ l, c l ^ 2 = m l ^ 2 + m' l ^ 2 := by
    intro l
    rw [show c l = ‖((m l : ℂ) - Complex.I * (m' l : ℂ))‖ from rfl, norm_sub_I,
      Real.sq_sqrt (by positivity)]
  let z : Cn n := fun l => ((m l / c l : ℝ) : ℂ) + Complex.I * ((m' l / c l : ℝ) : ℂ)
  have hzre : ∀ l, (z l).re = m l / c l := by intro l; simp [z]
  have hzim : ∀ l, (z l).im = m' l / c l := by intro l; simp [z]
  have hzl : ∀ l, ‖z l‖ ≤ 1 := by
    intro l
    have hz2 : ‖z l‖ ^ 2 = (m l / c l) ^ 2 + (m' l / c l) ^ 2 := by
      rw [show z l = ((m l / c l : ℝ) : ℂ) + Complex.I * ((m' l / c l : ℝ) : ℂ) from rfl,
        norm_add_I, Real.sq_sqrt (by positivity)]
    rcases eq_or_ne (c l) 0 with h0 | h0
    · have hz0 : z l = 0 := by
        rw [show z l = ((m l / c l : ℝ) : ℂ) + Complex.I * ((m' l / c l : ℝ) : ℂ) from rfl,
          h0]; simp
      rw [hz0]; norm_num
    · have h4 : (m l / c l) ^ 2 + (m' l / c l) ^ 2 = (m l ^ 2 + m' l ^ 2) / c l ^ 2 := by
        field_simp
      have h3 : ‖z l‖ ^ 2 = 1 := by
        rw [hz2, h4, ← hcsq l]
        exact div_self (pow_ne_zero 2 h0)
      nlinarith [norm_nonneg (z l)]
  have hzle : ‖z‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    exact hzl
  have hval : ∀ l, (z l).re * m l + (z l).im * m' l = c l := by
    intro l
    rw [hzre l, hzim l]
    rcases eq_or_ne (c l) 0 with h0 | h0
    · have hs : m l ^ 2 + m' l ^ 2 = 0 := by
        rw [← hcsq l, h0]; norm_num
      have hm0 : m l = 0 := by nlinarith [sq_nonneg (m l), sq_nonneg (m' l)]
      have hm'0 : m' l = 0 := by nlinarith [sq_nonneg (m l), sq_nonneg (m' l)]
      rw [hm0, hm'0, h0]; norm_num
    · have hc2 := hcsq l
      field_simp
      nlinarith [hc2]
  have hkey : φ ((B z) k) = ∑ l : Fin n, ((z l).re * m l + (z l).im * m' l) := by
    rw [B_coord B z k, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_add]
    congr 1
    · rw [← Complex.real_smul, map_smul, smul_eq_mul]
    · rw [← Complex.real_smul, map_smul, smul_eq_mul]
  have hsum : φ ((B z) k) = ∑ l : Fin n, c l := by
    rw [hkey]
    exact Finset.sum_congr rfl fun l _ => hval l
  change (∑ l : Fin n, c l) ≤ ‖B‖
  calc (∑ l : Fin n, c l) = φ ((B z) k) := hsum.symm
    _ ≤ ‖φ ((B z) k)‖ := le_abs_self _
    _ ≤ ‖(B z) k‖ := hφ _
    _ ≤ ‖B z‖ := norm_le_pi_norm _ _
    _ ≤ ‖B‖ * ‖z‖ := B.le_opNorm z
    _ ≤ ‖B‖ * 1 := by gcongr
    _ = ‖B‖ := mul_one _

/-! ## The values of `L` on the basis and on the perturbed basis -/

variable (L : Cn n →L[ℝ] ℂ) (B : Cn n →L[ℝ] Cn n)

/-- `hvec L B k = 2 * L (e k)`. -/
lemma hvec_eq (k : Fin n) : hvec L B k = 2 * L (Pi.single k (1 : ℂ)) := by
  simp only [hvec, avec, bvec, psiOf, lamOf]
  ring

/-- `L (e k) = hvec L B k / 2`. -/
lemma L_single (k : Fin n) : L (Pi.single k (1 : ℂ)) = hvec L B k / 2 := by
  rw [hvec_eq L B k]; ring

/-- `L (B (e k)) = -I * avec L B k`. -/
lemma L_B_single (k : Fin n) : L (B (Pi.single k (1 : ℂ))) = -Complex.I * avec L B k := by
  have h : avec L B k = Complex.I * L (B (Pi.single k (1 : ℂ))) := rfl
  rw [h, neg_mul, ← mul_assoc, Complex.I_mul_I]; ring

/-- The value of `L` on `I • e_k`. -/
lemma L_I_single (hc : ∀ w : Cn n, L (Complex.I • w + B w) = -Complex.I * L w) (k : Fin n) :
    L (Complex.I • Pi.single k (1 : ℂ)) = Complex.I * (avec L B k - hvec L B k / 2) := by
  have h := hc (Pi.single k (1 : ℂ))
  rw [map_add] at h
  have h2 : L (Complex.I • Pi.single k (1 : ℂ))
      = -Complex.I * L (Pi.single k (1 : ℂ)) - L (B (Pi.single k (1 : ℂ))) := by
    rw [eq_sub_iff_add_eq]; exact h
  rw [h2, L_B_single, L_single]
  ring

/-- The value of `L` on `B (I • e_k)`. -/
lemma L_B_I_single (hc : ∀ w : Cn n, L (Complex.I • w + B w) = -Complex.I * L w) (k : Fin n) :
    L (B (Complex.I • Pi.single k (1 : ℂ))) = avec L B k := by
  have h := hc (Complex.I • Pi.single k (1 : ℂ))
  rw [map_add] at h
  have hII : Complex.I • (Complex.I • Pi.single k (1 : ℂ)) = -(Pi.single k (1 : ℂ) : Cn n) := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [hII, map_neg] at h
  have h2 : L (B (Complex.I • Pi.single k (1 : ℂ)))
      = L (Pi.single k (1 : ℂ)) - Complex.I * L (Complex.I • Pi.single k (1 : ℂ)) := by
    rw [eq_sub_iff_add_eq]; linear_combination h
  rw [h2, L_I_single L B hc, L_single]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma star_eq (z : ℂ) : star z = (z.re : ℂ) - Complex.I * (z.im : ℂ) := by
  apply Complex.ext <;>
    simp [Complex.star_def, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]

/-! ## The two relations -/

/-- The first relation between the coefficients `a` and `h`. -/
lemma rel_one (hc : ∀ w : Cn n, L (Complex.I • w + B w) = -Complex.I * L w) (l : Fin n) :
    avec L B l + ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
      = (Complex.I / 2) * ∑ k : Fin n, hvec L B k * star ((B (Pi.single l (1 : ℂ))) k) := by
  have hexp : -Complex.I * avec L B l
      = ∑ k : Fin n, ((((B (Pi.single l (1 : ℂ))) k).re : ℂ) * (hvec L B k / 2)
          + (((B (Pi.single l (1 : ℂ))) k).im : ℂ)
              * (Complex.I * (avec L B k - hvec L B k / 2))) := by
    rw [← L_B_single L B l, L_expand L (B (Pi.single l (1 : ℂ)))]
    exact Finset.sum_congr rfl fun k _ => by rw [L_single, L_I_single L B hc]
  have e1a : ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).re : ℂ) * (hvec L B k / 2)
      = (1 / 2) * ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e1b : ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).im : ℂ)
          * (Complex.I * (avec L B k - hvec L B k / 2))
      = Complex.I * ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
        - (Complex.I / 2) * ∑ k : Fin n,
            (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k := by
    rw [show (∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).im : ℂ)
            * (Complex.I * (avec L B k - hvec L B k / 2)))
        = ∑ k : Fin n, (Complex.I * ((((B (Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k)
            - (Complex.I / 2) * ((((B (Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k)) from
        Finset.sum_congr rfl fun k _ => by ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have e1 : ∑ k : Fin n, ((((B (Pi.single l (1 : ℂ))) k).re : ℂ) * (hvec L B k / 2)
          + (((B (Pi.single l (1 : ℂ))) k).im : ℂ)
              * (Complex.I * (avec L B k - hvec L B k / 2)))
      = (1 / 2) * ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k
        + (Complex.I * ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
          - (Complex.I / 2) * ∑ k : Fin n,
              (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k) := by
    rw [Finset.sum_add_distrib, e1a, e1b]
  have hstar : (Complex.I / 2) * ∑ k : Fin n, hvec L B k * star ((B (Pi.single l (1 : ℂ))) k)
      = (Complex.I / 2) * ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k
        + (1 / 2) * ∑ k : Fin n,
            (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k := by
    have e : ∑ k : Fin n, hvec L B k * star ((B (Pi.single l (1 : ℂ))) k)
        = ∑ k : Fin n, ((((B (Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k
            - Complex.I * ((((B (Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [star_eq]
      ring
    rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
    linear_combination (-(1 / 2) * (∑ k : Fin n,
        (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k)) * Complex.I_mul_I
  rw [hstar]
  have hI : Complex.I * Complex.I + 1 = 0 := by rw [Complex.I_mul_I]; ring
  have key : avec L B l
      = (Complex.I / 2) * ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k
        - ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
        + (1 / 2) * ∑ k : Fin n,
            (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k := by
    have h := congrArg (fun x => Complex.I * x) (hexp.trans e1)
    have h' : Complex.I * (-Complex.I * avec L B l)
        = Complex.I * ((1 / 2) * (∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k)
            + (Complex.I * ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
              - (Complex.I / 2) * ∑ k : Fin n,
                  (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k)) := h
    rw [show Complex.I * (-Complex.I * avec L B l) = avec L B l by
          ring_nf; rw [Complex.I_sq]; ring,
        show Complex.I * ((1 / 2) * (∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k)
            + (Complex.I * ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
              - (Complex.I / 2) * ∑ k : Fin n,
                  (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k))
            = (Complex.I / 2) * ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k
              - ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
              + (1 / 2) * ∑ k : Fin n,
                  (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k by
          ring_nf; rw [Complex.I_sq]; ring] at h'
    exact h'
  rw [key]; ring

/-- The second relation between the coefficients `a` and `h`. -/
lemma rel_two (hc : ∀ w : Cn n, L (Complex.I • w + B w) = -Complex.I * L w) (l : Fin n) :
    ∑ k : Fin n, (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
        + Complex.I * avec L B l
      = (Complex.I / 2) * ∑ k : Fin n,
          hvec L B k * star ((B (Complex.I • Pi.single l (1 : ℂ))) k) := by
  have hexp : avec L B l
      = ∑ k : Fin n, ((((B (Complex.I • Pi.single l (1 : ℂ))) k).re : ℂ) * (hvec L B k / 2)
          + (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)
              * (Complex.I * (avec L B k - hvec L B k / 2))) := by
    have h0 : avec L B l = L (B (Complex.I • Pi.single l (1 : ℂ))) :=
      (L_B_I_single L B hc l).symm
    have h1 := L_expand L (B (Complex.I • Pi.single l (1 : ℂ)))
    rw [h0, h1]
    exact Finset.sum_congr rfl fun k _ => by rw [L_single, L_I_single L B hc]
  have e1a : ∑ k : Fin n, (((B (Complex.I • Pi.single l (1 : ℂ))) k).re : ℂ) * (hvec L B k / 2)
      = (1 / 2) * ∑ k : Fin n,
          (((B (Complex.I • Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e1b : ∑ k : Fin n, (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)
          * (Complex.I * (avec L B k - hvec L B k / 2))
      = Complex.I * ∑ k : Fin n,
            (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
        - (Complex.I / 2) * ∑ k : Fin n,
            (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k := by
    rw [show (∑ k : Fin n, (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)
            * (Complex.I * (avec L B k - hvec L B k / 2)))
        = ∑ k : Fin n, (Complex.I * ((((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)
              * avec L B k)
            - (Complex.I / 2) * ((((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)
              * hvec L B k)) from
        Finset.sum_congr rfl fun k _ => by ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have e1 : ∑ k : Fin n, ((((B (Complex.I • Pi.single l (1 : ℂ))) k).re : ℂ) * (hvec L B k / 2)
          + (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)
              * (Complex.I * (avec L B k - hvec L B k / 2)))
      = (1 / 2) * ∑ k : Fin n, (((B (Complex.I • Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k
        + (Complex.I * ∑ k : Fin n,
              (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
          - (Complex.I / 2) * ∑ k : Fin n,
              (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k) := by
    rw [Finset.sum_add_distrib, e1a, e1b]
  have hstar : (Complex.I / 2) * ∑ k : Fin n,
        hvec L B k * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)
      = (Complex.I / 2) * ∑ k : Fin n,
            (((B (Complex.I • Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k
        + (1 / 2) * ∑ k : Fin n,
            (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k := by
    have e : ∑ k : Fin n, hvec L B k * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)
        = ∑ k : Fin n, ((((B (Complex.I • Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k
            - Complex.I * ((((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [star_eq]
      ring
    rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
    linear_combination (-(1 / 2) * (∑ k : Fin n,
        (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k)) * Complex.I_mul_I
  rw [hstar]
  have key : Complex.I * avec L B l
      = (Complex.I / 2) * ∑ k : Fin n,
            (((B (Complex.I • Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k
        - ∑ k : Fin n, (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
        + (1 / 2) * ∑ k : Fin n,
            (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k := by
    have h := congrArg (fun x => Complex.I * x) (hexp.trans e1)
    have h' : Complex.I * avec L B l
        = Complex.I * ((1 / 2) * (∑ k : Fin n,
              (((B (Complex.I • Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k)
            + (Complex.I * ∑ k : Fin n,
                (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
              - (Complex.I / 2) * ∑ k : Fin n,
                  (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k)) := h
    rw [show Complex.I * ((1 / 2) * (∑ k : Fin n,
              (((B (Complex.I • Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k)
            + (Complex.I * ∑ k : Fin n,
                (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
              - (Complex.I / 2) * ∑ k : Fin n,
                  (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k))
            = (Complex.I / 2) * ∑ k : Fin n,
                (((B (Complex.I • Pi.single l (1 : ℂ))) k).re : ℂ) * hvec L B k
              - ∑ k : Fin n, (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
              + (1 / 2) * ∑ k : Fin n,
                  (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * hvec L B k by
          ring_nf; rw [Complex.I_sq]; ring] at h'
    exact h'
  rw [key]; ring

/-- The combined relation: a linear system for `a` in terms of `h`. -/
lemma rel_comb (hc : ∀ w : Cn n, L (Complex.I • w + B w) = -Complex.I * L w) (l : Fin n) :
    2 * avec L B l
      + ∑ k : Fin n, ((((B (Pi.single l (1 : ℂ))) k).im : ℂ)
          - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)) * avec L B k
      = (Complex.I / 2) * ∑ k : Fin n, hvec L B k * star ((B (Pi.single l (1 : ℂ))) k)
        + (1 / 2) * ∑ k : Fin n,
            hvec L B k * star ((B (Complex.I • Pi.single l (1 : ℂ))) k) := by
  have h1 := rel_one L B hc l
  have h2 := rel_two L B hc l
  have hL : ∑ k : Fin n, ((((B (Pi.single l (1 : ℂ))) k).im : ℂ)
          - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)) * avec L B k
      = (∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k)
        - Complex.I * ∑ k : Fin n,
            (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k := by
    rw [show (∑ k : Fin n, ((((B (Pi.single l (1 : ℂ))) k).im : ℂ)
            - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)) * avec L B k)
        = ∑ k : Fin n, ((((B (Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
            - Complex.I * ((((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k)) from
        Finset.sum_congr rfl fun k _ => by ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hL]
  have h2' : Complex.I * (∑ k : Fin n,
          (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k
          + Complex.I * avec L B l)
      = Complex.I * ((Complex.I / 2) * ∑ k : Fin n,
          hvec L B k * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)) := by rw [h2]
  have hkey : (avec L B l + ∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k)
        - Complex.I * ((∑ k : Fin n,
              (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k)
            + Complex.I * avec L B l)
      = ((Complex.I / 2) * ∑ k : Fin n, hvec L B k * star ((B (Pi.single l (1 : ℂ))) k))
        - Complex.I * ((Complex.I / 2) * ∑ k : Fin n,
            hvec L B k * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)) := by
    rw [h1, h2']
  have key : 2 * avec L B l
        + ((∑ k : Fin n, (((B (Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k)
            - Complex.I * ∑ k : Fin n,
                (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ) * avec L B k)
      = (Complex.I / 2) * ∑ k : Fin n, hvec L B k * star ((B (Pi.single l (1 : ℂ))) k)
        + (1 / 2) * ∑ k : Fin n,
            hvec L B k * star ((B (Complex.I • Pi.single l (1 : ℂ))) k) := by
    have h' := hkey
    ring_nf at h'
    rw [Complex.I_sq] at h'
    linear_combination h'
  rw [key]

/-! ## Row bounds -/

/-- The imaginary-part row bound. -/
lemma row_im_bound (B : Cn n →L[ℝ] Cn n) (k : Fin n) :
    (∑ l : Fin n, ‖(((B (Pi.single l (1 : ℂ))) k).im : ℂ)
        - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)‖) ≤ ‖B‖ := by
  have h := phase_bound Complex.imLm (fun z => Complex.abs_im_le_norm z) B k
  simpa using h

/-- The real-part row bound. -/
lemma row_re_bound (B : Cn n →L[ℝ] Cn n) (k : Fin n) :
    (∑ l : Fin n, ‖(((B (Pi.single l (1 : ℂ))) k).re : ℂ)
        - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).re : ℂ)‖) ≤ ‖B‖ := by
  have h := phase_bound Complex.reLm (fun z => Complex.abs_re_le_norm z) B k
  simpa using h

/-- A pointwise inequality comparing the size of a complex number with the sizes of the
`re`/`im` combinations appearing in the relations. -/
lemma norm_parts_le (a b c d : ℝ) :
    ‖(a : ℂ) + (b : ℂ) * Complex.I‖
      ≤ ‖(a : ℂ) - Complex.I * (c : ℂ)‖ + ‖(b : ℂ) - Complex.I * (d : ℂ)‖ := by
  rw [mul_comm, norm_add_I, norm_sub_I, norm_sub_I]
  have h1 : |a| ≤ Real.sqrt (a ^ 2 + c ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg c])
  have h2 : |b| ≤ Real.sqrt (b ^ 2 + d ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg d])
  have h3 : Real.sqrt (a ^ 2 + b ^ 2) ≤ |a| + |b| := by
    calc Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt ((|a| + |b|) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b])
      _ = |a| + |b| := Real.sqrt_sq (by positivity)
  linarith [h1, h2, h3]

/-- Variant of `norm_parts_le` where the size of the second vector is compared. -/
lemma norm_parts_le' (a b c d : ℝ) :
    ‖(c : ℂ) + (d : ℂ) * Complex.I‖
      ≤ ‖(a : ℂ) - Complex.I * (c : ℂ)‖ + ‖(b : ℂ) - Complex.I * (d : ℂ)‖ := by
  rw [mul_comm, norm_add_I, norm_sub_I, norm_sub_I]
  have h1 : |c| ≤ Real.sqrt (a ^ 2 + c ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a])
  have h2 : |d| ≤ Real.sqrt (b ^ 2 + d ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])
  have h3 : Real.sqrt (c ^ 2 + d ^ 2) ≤ |c| + |d| := by
    calc Real.sqrt (c ^ 2 + d ^ 2) ≤ Real.sqrt ((|c| + |d|) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_abs c, sq_abs d, abs_nonneg c, abs_nonneg d])
      _ = |c| + |d| := Real.sqrt_sq (by positivity)
  linarith [h1, h2, h3]

/-- Row bound for the part of `B` along `e_l`. -/
lemma row_M_bound (B : Cn n →L[ℝ] Cn n) (k : Fin n) :
    (∑ l : Fin n, ‖(B (Pi.single l (1 : ℂ))) k‖) ≤ 2 * ‖B‖ := by
  have h1 : (∑ l : Fin n, ‖(B (Pi.single l (1 : ℂ))) k‖)
      ≤ ∑ l : Fin n, (‖(((B (Pi.single l (1 : ℂ))) k).re : ℂ)
            - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).re : ℂ)‖
          + ‖(((B (Pi.single l (1 : ℂ))) k).im : ℂ)
            - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)‖) := by
    refine Finset.sum_le_sum fun l _ => ?_
    have hp := norm_parts_le (((B (Pi.single l (1 : ℂ))) k).re)
      (((B (Pi.single l (1 : ℂ))) k).im)
      (((B (Complex.I • Pi.single l (1 : ℂ))) k).re)
      (((B (Complex.I • Pi.single l (1 : ℂ))) k).im)
    have hz := Complex.re_add_im ((B (Pi.single l (1 : ℂ))) k)
    rw [hz] at hp
    exact hp
  rw [Finset.sum_add_distrib] at h1
  linarith [h1, row_re_bound B k, row_im_bound B k]

/-- Row bound for the part of `B` along `I • e_l`. -/
lemma row_N_bound (B : Cn n →L[ℝ] Cn n) (k : Fin n) :
    (∑ l : Fin n, ‖(B (Complex.I • Pi.single l (1 : ℂ))) k‖) ≤ 2 * ‖B‖ := by
  have h1 : (∑ l : Fin n, ‖(B (Complex.I • Pi.single l (1 : ℂ))) k‖)
      ≤ ∑ l : Fin n, (‖(((B (Pi.single l (1 : ℂ))) k).re : ℂ)
            - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).re : ℂ)‖
          + ‖(((B (Pi.single l (1 : ℂ))) k).im : ℂ)
            - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)‖) := by
    refine Finset.sum_le_sum fun l _ => ?_
    have hp := norm_parts_le' (((B (Pi.single l (1 : ℂ))) k).re)
      (((B (Pi.single l (1 : ℂ))) k).im)
      (((B (Complex.I • Pi.single l (1 : ℂ))) k).re)
      (((B (Complex.I • Pi.single l (1 : ℂ))) k).im)
    have hz := Complex.re_add_im ((B (Complex.I • Pi.single l (1 : ℂ))) k)
    rw [hz] at hp
    exact hp
  rw [Finset.sum_add_distrib] at h1
  linarith [h1, row_re_bound B k, row_im_bound B k]

/-- Row bound for the coefficient vector multiplying `hvec`. -/
lemma row_Bp_bound (B : Cn n →L[ℝ] Cn n) (k : Fin n) :
    (∑ l : Fin n, ‖(Complex.I / 2) * star ((B (Pi.single l (1 : ℂ))) k)
        + (1 / 2) * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)‖) ≤ 2 * ‖B‖ := by
  have key : ∀ l : Fin n, ‖(Complex.I / 2) * star ((B (Pi.single l (1 : ℂ))) k)
        + (1 / 2) * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)‖
      ≤ (1 / 2) * ‖(B (Pi.single l (1 : ℂ))) k‖
        + (1 / 2) * ‖(B (Complex.I • Pi.single l (1 : ℂ))) k‖ := by
    intro l
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, norm_star, norm_star]
    simp
  have h1 : (∑ l : Fin n, ‖(Complex.I / 2) * star ((B (Pi.single l (1 : ℂ))) k)
        + (1 / 2) * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)‖)
      ≤ ∑ l : Fin n, ((1 / 2) * ‖(B (Pi.single l (1 : ℂ))) k‖
          + (1 / 2) * ‖(B (Complex.I • Pi.single l (1 : ℂ))) k‖) :=
    Finset.sum_le_sum fun l _ => key l
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
  linarith [h1, row_M_bound B k, row_N_bound B k]

/-- **The core estimate.**  Let `B : ℂⁿ →L[ℝ] ℂⁿ` with `‖B‖ ≤ ε ≤ 1` and let `L : ℂⁿ →L[ℝ] ℂ`
be `(I + B)`-antilinear.  Then the coefficients `a k = avec L B k` of the `ℂ`-linear part
`λ = L ∘ B` of `L` and the vector `hvec L B` satisfy `∑ ‖avec L B k‖ ≤ 6 ε ∑ ‖hvec L B k‖`. -/
theorem relations_and_bound {n : ℕ} (L : Cn n →L[ℝ] ℂ) (B : Cn n →L[ℝ] Cn n) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hB : ‖B‖ ≤ ε)
    (hc : ∀ w : Cn n, L (Complex.I • w + B w) = -Complex.I * L w) :
    (∑ k : Fin n, ‖avec L B k‖) ≤ 6 * ε * ∑ k : Fin n, ‖hvec L B k‖ := by
  classical
  have hsys : ∀ l : Fin n, 2 * avec L B l
      = (∑ k : Fin n, ((Complex.I / 2) * star ((B (Pi.single l (1 : ℂ))) k)
            + (1 / 2) * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)) * hvec L B k)
        - ∑ k : Fin n, ((((B (Pi.single l (1 : ℂ))) k).im : ℂ)
            - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)) * avec L B k := by
    intro l
    have h := rel_comb L B hc l
    have hBsum : (∑ k : Fin n, ((Complex.I / 2) * star ((B (Pi.single l (1 : ℂ))) k)
          + (1 / 2) * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)) * hvec L B k)
        = (Complex.I / 2) * ∑ k : Fin n, hvec L B k * star ((B (Pi.single l (1 : ℂ))) k)
          + (1 / 2) * ∑ k : Fin n,
              hvec L B k * star ((B (Complex.I • Pi.single l (1 : ℂ))) k) := by
      rw [show (∑ k : Fin n, ((Complex.I / 2) * star ((B (Pi.single l (1 : ℂ))) k)
            + (1 / 2) * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)) * hvec L B k)
          = ∑ k : Fin n, ((Complex.I / 2) * (hvec L B k * star ((B (Pi.single l (1 : ℂ))) k))
            + (1 / 2) * (hvec L B k * star ((B (Complex.I • Pi.single l (1 : ℂ))) k))) from
          Finset.sum_congr rfl fun k _ => by ring]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hBsum]
    linear_combination h
  have hnorm : ∀ l : Fin n, ‖2 * avec L B l‖
      ≤ (∑ k : Fin n, ‖(Complex.I / 2) * star ((B (Pi.single l (1 : ℂ))) k)
            + (1 / 2) * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)‖ * ‖hvec L B k‖)
        + ∑ k : Fin n, ‖(((B (Pi.single l (1 : ℂ))) k).im : ℂ)
            - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)‖
            * ‖avec L B k‖ := by
    intro l
    rw [hsys l]
    have h0 := norm_sub_le
      (∑ k : Fin n, ((Complex.I / 2) * star ((B (Pi.single l (1 : ℂ))) k)
            + (1 / 2) * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)) * hvec L B k)
      (∑ k : Fin n, ((((B (Pi.single l (1 : ℂ))) k).im : ℂ)
            - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)) * avec L B k)
    have h1 : ‖∑ k : Fin n, ((Complex.I / 2) * star ((B (Pi.single l (1 : ℂ))) k)
            + (1 / 2) * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)) * hvec L B k‖
        ≤ ∑ k : Fin n, ‖(Complex.I / 2) * star ((B (Pi.single l (1 : ℂ))) k)
            + (1 / 2) * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)‖ * ‖hvec L B k‖ :=
      le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    have h2 : ‖∑ k : Fin n, ((((B (Pi.single l (1 : ℂ))) k).im : ℂ)
            - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)) * avec L B k‖
        ≤ ∑ k : Fin n, ‖(((B (Pi.single l (1 : ℂ))) k).im : ℂ)
            - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)‖
            * ‖avec L B k‖ :=
      le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    linarith [h0, h1, h2]
  have hsumB : (∑ l : Fin n, ∑ k : Fin n,
        ‖(Complex.I / 2) * star ((B (Pi.single l (1 : ℂ))) k)
          + (1 / 2) * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)‖ * ‖hvec L B k‖)
      ≤ (2 * ‖B‖) * ∑ k : Fin n, ‖hvec L B k‖ := by
    rw [Finset.sum_comm]
    have h2 : ∀ k : Fin n, (∑ l : Fin n, ‖(Complex.I / 2) * star ((B (Pi.single l (1 : ℂ))) k)
          + (1 / 2) * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)‖ * ‖hvec L B k‖)
        ≤ (2 * ‖B‖) * ‖hvec L B k‖ := by
      intro k
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (row_Bp_bound B k) (norm_nonneg _)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => h2 k
  have hsumA : (∑ l : Fin n, ∑ k : Fin n,
        ‖(((B (Pi.single l (1 : ℂ))) k).im : ℂ)
          - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)‖ * ‖avec L B k‖)
      ≤ ‖B‖ * ∑ k : Fin n, ‖avec L B k‖ := by
    rw [Finset.sum_comm]
    have h2 : ∀ k : Fin n, (∑ l : Fin n, ‖(((B (Pi.single l (1 : ℂ))) k).im : ℂ)
          - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)‖ * ‖avec L B k‖)
        ≤ ‖B‖ * ‖avec L B k‖ := by
      intro k
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (row_im_bound B k) (norm_nonneg _)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => h2 k
  have hmain : 2 * (∑ k : Fin n, ‖avec L B k‖)
      ≤ (2 * ‖B‖) * (∑ k : Fin n, ‖hvec L B k‖) + ‖B‖ * (∑ k : Fin n, ‖avec L B k‖) := by
    have hstep : 2 * (∑ k : Fin n, ‖avec L B k‖) = ∑ l : Fin n, ‖2 * avec L B l‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [norm_mul, Complex.norm_ofNat]
    rw [hstep]
    have h4 : (∑ l : Fin n, ‖2 * avec L B l‖)
        ≤ ∑ l : Fin n, ((∑ k : Fin n, ‖(Complex.I / 2) * star ((B (Pi.single l (1 : ℂ))) k)
              + (1 / 2) * star ((B (Complex.I • Pi.single l (1 : ℂ))) k)‖ * ‖hvec L B k‖)
          + ∑ k : Fin n, ‖(((B (Pi.single l (1 : ℂ))) k).im : ℂ)
              - Complex.I * (((B (Complex.I • Pi.single l (1 : ℂ))) k).im : ℂ)‖
              * ‖avec L B k‖) := Finset.sum_le_sum fun l _ => hnorm l
    rw [Finset.sum_add_distrib] at h4
    linarith [h4, hsumB, hsumA]
  have hS : 0 ≤ ∑ k : Fin n, ‖avec L B k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hT : 0 ≤ ∑ k : Fin n, ‖hvec L B k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB1 : ‖B‖ ≤ 1 := le_trans hB hε1
  have hgoal : (∑ k : Fin n, ‖avec L B k‖)
      ≤ 2 * ‖B‖ * (∑ k : Fin n, ‖hvec L B k‖) := by
    nlinarith [hmain, hS, hT, hB1, norm_nonneg B]
  calc (∑ k : Fin n, ‖avec L B k‖) ≤ 2 * ‖B‖ * (∑ k : Fin n, ‖hvec L B k‖) := hgoal
    _ ≤ 2 * ε * (∑ k : Fin n, ‖hvec L B k‖) := by
        have := mul_le_mul_of_nonneg_right hB hT; nlinarith [this]
    _ ≤ 6 * ε * (∑ k : Fin n, ‖hvec L B k‖) := by
        have := mul_le_mul_of_nonneg_right hε0 hT; nlinarith [this]

end

end Work.NN.Final
