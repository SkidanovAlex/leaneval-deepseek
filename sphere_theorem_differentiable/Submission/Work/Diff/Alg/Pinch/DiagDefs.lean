import Mathlib
import Submission.Work.Diff.Alg.Pinch.DtensorDefs
import Submission.Work.Diff.Alg.Pinch.EFun_knProd_diag

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The diagonal-Ric form of the Böhm–Wilking tensor `D_{a,b}(S)`

The target `Work.Diff.Alg.Pinch.EFun_Dtensor_pos_diag` treats the case where the Ricci tensor of
`S` is *diagonal*: `ric S i j = 0` for `i ≠ j`.  In that case every tensor appearing in the
Böhm–Wilking difference tensor

`Dtensor n b S = c₀ • (Ric₀ ∧ Ric₀) + 2a • (Ric ∧ Ric) + 2b² • (Ric₀² ∧ id) + c₃ |Ric₀|² • (id ∧ id)`

is a `knProd` of two *diagonal* tensors, so the computation of
`Work.Diff.Alg.Pinch.EFun_knProd_diag`

`EFun (knProd (diag u) (diag v)) x y z w = ∑ᵢⱼ uᵢ vⱼ |ζᵢηⱼ − ζⱼηᵢ|²`

expands `EFun (Dtensor n b S)` into a double sum

`EFun (Dtensor n b S) x y z w = ∑ᵢⱼ Wt n b S i j * Zf x y z w i j`

whose *pair weights* `Wt n b S i j` (the "`d_ij`" of Böhm–Wilking Corollary 2.3) were computed by
Böhm–Wilking: with `m = Ric₀(S)` the traceless Ricci tensor and `a = ccA n b`, `p = ccP n b`,

`Wt n b S i j = ((n-2)b² - 2(a-b)) mᵢ mⱼ + 2a (λ̄+mᵢ)(λ̄+mⱼ) + b²(mᵢ² + mⱼ²) + bwC n b · |m|²`,

`λ̄` being the mean of the Ricci eigenvalues and `bwC n b` a nonnegative constant in the range
`2 ≤ n`, `0 < b ≤ 1/2` (the Böhm–Wilking rewrite of the fourth coefficient).

The point of this module is to fix that notation once, so that the two independent halves of the
proof — the *computation* of `EFun (Dtensor n b S)` (`EFun_Dtensor_diag`) and the *strict
positivity* of the weights `Wt n b S i j` (Böhm–Wilking Corollary 2.3 / the first step of Lemma
3.4, `Dtensor_weight_pos`) — can be stated and proved separately.

## Conventions

* `Zf x y z w i j = |ζᵢηⱼ − ζⱼηᵢ|²` for `ζ = x + iy`, `η = z + iw`; it is symmetric in `i, j` and
  nonnegative.
* `bwC n b = (2 + 2(n-2)b) b²(1-2b) / (n (1 + 2(n-1)a) (1 + (n-2)b²))` with `a = ccA n b`; this is
  the Böhm–Wilking rewrite of the coefficient `c₃` of `Dtensor`, and it is `≥ 0` for
  `2 ≤ n`, `0 < b ≤ 1/2`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg
open Work.Diff.Alg.Q2P (EFun)

variable {n : ℕ}

/-! ## The pair form `Zf` -/

/-- `Zf x y z w i j = |ζᵢ ηⱼ − ζⱼ ηᵢ|²`, the squared modulus of the `(i,j)` minor of the
decomposable complex `2`-form `ω = ζ ∧ η`, `ζ = x + iy`, `η = z + iw`. -/
noncomputable def Zf (x y z w : Fin n → ℝ) (i j : Fin n) : ℝ :=
  Complex.normSq (((x i : ℂ) + (y i : ℂ) * Complex.I) * ((z j : ℂ) + (w j : ℂ) * Complex.I)
    - ((x j : ℂ) + (y j : ℂ) * Complex.I) * ((z i : ℂ) + (w i : ℂ) * Complex.I))

/-- `Zf` is symmetric in its two indices. -/
theorem Zf_symm (x y z w : Fin n → ℝ) (i j : Fin n) : Zf x y z w i j = Zf x y z w j i := by
  rw [Zf, Zf]
  have h : ((x j : ℂ) + (y j : ℂ) * Complex.I) * ((z i : ℂ) + (w i : ℂ) * Complex.I)
      - ((x i : ℂ) + (y i : ℂ) * Complex.I) * ((z j : ℂ) + (w j : ℂ) * Complex.I)
      = - (((x i : ℂ) + (y i : ℂ) * Complex.I) * ((z j : ℂ) + (w j : ℂ) * Complex.I)
      - ((x j : ℂ) + (y j : ℂ) * Complex.I) * ((z i : ℂ) + (w i : ℂ) * Complex.I)) := by
    ring
  rw [h, Complex.normSq_neg]

/-- `Zf` is nonnegative. -/
theorem Zf_nonneg (x y z w : Fin n → ℝ) (i j : Fin n) : 0 ≤ Zf x y z w i j :=
  Complex.normSq_nonneg _

/-! ## Linearity of `EFun` in the tensor -/

/-- `R4` is additive in the tensor. -/
theorem R4_tensor_add (R S : Curv4 n) (a b c d : Fin n → ℝ) :
    R4 (R + S) a b c d = R4 R a b c d + R4 S a b c d := by
  simp only [R4, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- `R4` is homogeneous in the tensor. -/
theorem R4_tensor_smul (t : ℝ) (R : Curv4 n) (a b c d : Fin n → ℝ) :
    R4 (t • R) a b c d = t * R4 R a b c d := by
  simp only [R4, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro l _
  ring

/-- `EFun` is additive in the tensor. -/
theorem EFun_add_lin (R S : Curv4 n) (x y z w : Fin n → ℝ) :
    EFun (R + S) x y z w = EFun R x y z w + EFun S x y z w := by
  simp only [EFun, R4_tensor_add]
  ring

/-- `EFun` is homogeneous in the tensor. -/
theorem EFun_smul_lin (t : ℝ) (R : Curv4 n) (x y z w : Fin n → ℝ) :
    EFun (t • R) x y z w = t * EFun R x y z w := by
  simp only [EFun, R4_tensor_smul]
  ring

/-! ## `EFun (Iso n)` as half the total mass of `Zf` -/

/-- `knProd (id2 n) (id2 n) = 2 • Iso n`. -/
theorem knProd_id2_id2_eq_two_smul (n : ℕ) : knProd (id2 n) (id2 n) = (2 : ℝ) • Iso n := by
  funext i j k l
  simp only [knProd, id2, Iso, Pi.smul_apply, smul_eq_mul]
  ring

/-- The isotropic curvature of the round sphere is half the total mass of the pair forms:
`EFun (Iso n) x y z w = ½ ∑ᵢⱼ |ζᵢηⱼ − ζⱼηᵢ|²`. -/
theorem EFun_Iso_eq_half_sum_Zf (n : ℕ) (x y z w : Fin n → ℝ) :
    EFun (Iso n) x y z w = (1 / 2) * ∑ i, ∑ j, Zf x y z w i j := by
  have h1 : EFun (knProd (id2 n) (id2 n)) x y z w = ∑ i, ∑ j, Zf x y z w i j := by
    rw [show id2 n = (fun i j : Fin n => if i = j then (1 : ℝ) else 0) from rfl,
      EFun_knProd_diag n (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) x y z w]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    simp only [one_mul, Zf]
  have h2 : EFun (knProd (id2 n) (id2 n)) x y z w = 2 * EFun (Iso n) x y z w := by
    rw [knProd_id2_id2_eq_two_smul n, EFun_smul_lin]
  rw [h2] at h1
  linarith [h1]

/-! ## The Böhm–Wilking weight `bwC` and the pair weight `Wt` -/

/-- The Böhm–Wilking coefficient of the `id ∧ id` term, in its rewritten (manifestly nonnegative)
form.  It is the same number as the coefficient of `knProd (id2 n) (id2 n)` in `Dtensor n b S`
divided by `n` (see `dtensorCoeff_eq_bwC`). -/
noncomputable def bwC (n : ℕ) (b : ℝ) : ℝ :=
  (2 + 2 * ((n : ℝ) - 2) * b) * b ^ 2 * (1 - 2 * b)
    / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * ccA n b) * (1 + ((n : ℝ) - 2) * b ^ 2))

/-- The Böhm–Wilking pair weight `Wt n b S i j` (the `d_ij` of Böhm–Wilking Corollary 2.3): for
`m = Ric₀(S)`, `λ̄ = scal(S)/n` and `a = ccA n b`,

`Wt n b S i j = ((n-2)b² - 2(a-b)) mᵢmⱼ + 2a (λ̄+mᵢ)(λ̄+mⱼ) + b²(mᵢ²+mⱼ²) + bwC n b · |m|²`. -/
noncomputable def Wt (n : ℕ) (b : ℝ) (S : Curv4 n) (i j : Fin n) : ℝ :=
  (((n : ℝ) - 2) * b ^ 2 - 2 * (ccA n b - b)) * ric0 S i i * ric0 S j j
    + 2 * ccA n b * (scalAlg S / (n : ℝ) + ric0 S i i) * (scalAlg S / (n : ℝ) + ric0 S j j)
    + b ^ 2 * ((ric0 S i i) ^ 2 + (ric0 S j j) ^ 2)
    + bwC n b * (∑ k, (ric0 S k k) ^ 2)

/-- `bwC` is nonnegative in the Böhm–Wilking range `2 ≤ n`, `0 < b ≤ 1/2`. -/
theorem bwC_nonneg {n : ℕ} (hn2 : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    0 ≤ bwC n b := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have ha : 0 < ccA n b := ccA_pos hn1 hb hb'
  have hQ : (0 : ℝ) < 1 + ((n : ℝ) - 2) * b ^ 2 := by nlinarith [sq_nonneg b]
  have hnum1 : (0 : ℝ) ≤ 2 + 2 * ((n : ℝ) - 2) * b := by nlinarith
  have hden : (0 : ℝ) < (n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * ccA n b) * (1 + ((n : ℝ) - 2) * b ^ 2) := by
    have h1 : 0 < 1 + 2 * ((n : ℝ) - 1) * ccA n b := by nlinarith
    positivity
  rw [bwC]
  apply div_nonneg
  · have : (0 : ℝ) ≤ 1 - 2 * b := by linarith
    positivity
  · linarith

/-- `ccP n b ≥ 0` in the Böhm–Wilking range `2 ≤ n`. -/
theorem ccP_nonneg_diag {n : ℕ} (hn2 : 2 ≤ n) (b : ℝ) : 0 ≤ ccP n b := by
  have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hb2 : (0 : ℝ) ≤ ((n : ℝ) - 2) * b ^ 2 :=
    mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 2) (sq_nonneg b)
  have hQ : (0 : ℝ) < 1 + ((n : ℝ) - 2) * b ^ 2 := by linarith
  have h : 1 / (1 + ((n : ℝ) - 2) * b ^ 2) ≤ 1 := by
    rw [div_le_one hQ]
    linarith
  rw [ccP]
  linarith

/-- `1 - ccP n b > 0` (the pinching parameter `p = ccP n b` is `< 1`). -/
theorem one_sub_ccP_pos {n : ℕ} (hn2 : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    0 < 1 - ccP n b := by
  have h := ccP_lt_one (by omega : 1 ≤ n) hb hb'
  linarith

/-- The `b`-dependence of `ccA`: `ccA n b - b = (n-2) b² (1-2b) / (2 (1 + (n-2)b²))`. -/
theorem ccA_sub_b {n : ℕ} (hn2 : 2 ≤ n) (b : ℝ) :
    ccA n b - b = ((n : ℝ) - 2) * b ^ 2 * (1 - 2 * b) / (2 * (1 + ((n : ℝ) - 2) * b ^ 2)) := by
  have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hQ : (1 : ℝ) + ((n : ℝ) - 2) * b ^ 2 ≠ 0 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 2) (sq_nonneg b)]
  have hden : (2 : ℝ) * (1 + ((n : ℝ) - 2) * b ^ 2) ≠ 0 := mul_ne_zero two_ne_zero hQ
  rw [ccA, eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden]
  ring

/-- The auxiliary polynomial identity behind `dtensorCoeff_eq_bwC`:
`n(1+(n-2)b²) - (n-2)(1-2b+nb²) = 2 + 2(n-2)b`. -/
theorem npoly_sub {n : ℕ} (b : ℝ) :
    (n : ℝ) * (1 + ((n : ℝ) - 2) * b ^ 2) - ((n : ℝ) - 2) * (1 - 2 * b + (n : ℝ) * b ^ 2)
      = 2 + 2 * ((n : ℝ) - 2) * b := by
  ring

/-- The fourth coefficient of `Dtensor n b S` (the one multiplying `|Ric₀|² • id ∧ id`) equals
`bwC n b`, divided by the `n` of the normalization.  This is the Böhm–Wilking rewrite
`n b²(1-2b) - 2(a-b)(1-2b+nb²) = (1-2b) b² (2 + 2(n-2)b)/(1+(n-2)b²)`. -/
theorem dtensorCoeff_eq_bwC {n : ℕ} (hn2 : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    ((n : ℝ) * b ^ 2 * (1 - 2 * b) - 2 * (ccA n b - b) * (1 - 2 * b + (n : ℝ) * b ^ 2))
        / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * ccA n b)) = bwC n b := by
  have hn1 : 1 ≤ n := by omega
  have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have ha : 0 < ccA n b := ccA_pos hn1 hb hb'
  have hD : (n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * ccA n b) ≠ 0 := by
    have h1 : 0 < 1 + 2 * ((n : ℝ) - 1) * ccA n b := by nlinarith
    have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    positivity
  have hQ : (1 : ℝ) + ((n : ℝ) - 2) * b ^ 2 ≠ 0 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 2) (sq_nonneg b)]
  have hDQ : (n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * ccA n b) * (1 + ((n : ℝ) - 2) * b ^ 2) ≠ 0 :=
    mul_ne_zero hD hQ
  rw [bwC, eq_div_iff hDQ, ← mul_assoc, div_mul_cancel₀ _ hD]
  have hsub : 2 * (ccA n b - b) * (1 - 2 * b + (n : ℝ) * b ^ 2) * (1 + ((n : ℝ) - 2) * b ^ 2)
      = ((n : ℝ) - 2) * b ^ 2 * (1 - 2 * b) * (1 - 2 * b + (n : ℝ) * b ^ 2) := by
    rw [ccA_sub_b hn2]
    field_simp
  linear_combination (b ^ 2 * (1 - 2 * b)) * npoly_sub (n := n) b - hsub

end Work.Diff.Alg.Pinch
