import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseRowsFS.RowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.Theta` — the Gaussian lattice summation (Poisson/theta) step

The FS §11 lattice row compares the box-mode sum `Σ_j Ŵ₁(k_j)²/‖k_j‖²` with the continuum
integral; the classical route replaces the sharp lattice weights `1/‖k_j‖²` by the heat-kernel
layer cake `1/‖k_j‖² = ∫_0^∞ e^{-t‖k_j‖²}dt` and then uses the **Poisson/theta identity** for the
Gaussian-damped lattice sums with the box modes `k_j = (2π/ℓ)·ℤ³`.

This module provides that identity, in the form in which it is consumed:

* `pi3_prod_tsum` — a sum over `Fin 3 → ℤ` of a product of per-coordinate summands factors as
  the product of the one-dimensional sums (the `ℤ`-analogue of
  `Commons.Analysis.Fourier.tsum_fin3_prod`);
* `theta1_cos` — the one-dimensional theta transformation in the form
  `Σ_n e^{-(z+ℓn)²/4t} = (2√(πt)/ℓ) Σ_n e^{-t(2πn/ℓ)²} cos(2πnz/ℓ)`
  (`Commons.Analysis.Fourier.theta_shift_real` with `a = ℓ²/4t`, `c = z/ℓ`);
* `theta1_sin_zero` — the companion sine sum vanishes;
* `theta3_images` and `theta3` — the three-dimensional identity, in the image form and in the
  heat-kernel form `Σ_j e^{-t‖k_j‖²}cos⟨k_j,z⟩ = ℓ³ Σ_m Kt t (z + ℓ•vecZ m)`.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseRowsFS

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. Factoring a sum over `Fin 3 → ℤ` -/

/-- The bijection `(Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ` sending `k` to `(k 0, k 1, k 2)`. -/
def fin3IntEquivProd : (Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ where
  toFun k := (k 0, k 1, k 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv := by
    intro k
    funext i
    fin_cases i <;> simp
  right_inv := by
    rintro ⟨a, b, c⟩
    simp

/-- A product of three independent absolutely summable complex series over `ℤ`, re-indexed by
`Fin 3 → ℤ`, equals the product of the one-dimensional sums. -/
theorem pi3_prod_tsum (g : Fin 3 → ℤ → ℂ) (hg : ∀ i, Summable (g i)) :
    (∑' j : Fin 3 → ℤ, ∏ i, g i (j i)) = ∏ i, ∑' n : ℤ, g i n := by
  have hF : ∀ i, Summable fun n : ℤ => ‖g i n‖ := fun i => (hg i).norm
  have h01 : Summable fun q : ℤ × ℤ => ‖g 1 q.1 * g 2 q.2‖ := Summable.mul_norm (hF 1) (hF 2)
  have hinner : (∑' m : ℤ, g 1 m) * (∑' m : ℤ, g 2 m)
      = ∑' q : ℤ × ℤ, g 1 q.1 * g 2 q.2 :=
    tsum_mul_tsum_of_summable_norm (hF 1) (hF 2)
  have hmain : (∑' m : ℤ, g 0 m) * (∑' q : ℤ × ℤ, g 1 q.1 * g 2 q.2)
      = ∑' p : ℤ × ℤ × ℤ, g 0 p.1 * (g 1 p.2.1 * g 2 p.2.2) :=
    tsum_mul_tsum_of_summable_norm (hF 0) h01
  rw [show (∏ i : Fin 3, ∑' m : ℤ, g i m)
      = (∑' m : ℤ, g 0 m) * (∑' m : ℤ, g 1 m) * (∑' m : ℤ, g 2 m) by
    rw [Fin.prod_univ_three]]
  rw [← Equiv.tsum_eq fin3IntEquivProd.symm (fun j : Fin 3 → ℤ => ∏ i : Fin 3, g i (j i))]
  rw [show (∑' p : ℤ × ℤ × ℤ, ∏ i : Fin 3, g i ((fin3IntEquivProd.symm p) i))
      = ∑' p : ℤ × ℤ × ℤ, g 0 p.1 * (g 1 p.2.1 * g 2 p.2.2) by
    apply tsum_congr
    intro p
    obtain ⟨a, b, c⟩ := p
    simp only [fin3IntEquivProd, Equiv.coe_fn_symm_mk]
    rw [Fin.prod_univ_three]
    simp [mul_assoc]]
  rw [← hmain, ← hinner]
  ring

/-- A product of three independent absolutely summable real series over `ℤ`, re-indexed by
`Fin 3 → ℤ`, equals the product of the one-dimensional sums. -/
theorem pi3_prod_tsum_real (g : Fin 3 → ℤ → ℝ) (hg : ∀ i, Summable (g i)) :
    (∑' j : Fin 3 → ℤ, ∏ i, g i (j i)) = ∏ i, ∑' n : ℤ, g i n := by
  have hF : ∀ i, Summable fun n : ℤ => ‖g i n‖ := fun i => (hg i).norm
  have h01 : Summable fun q : ℤ × ℤ => ‖g 1 q.1 * g 2 q.2‖ := Summable.mul_norm (hF 1) (hF 2)
  have hinner : (∑' m : ℤ, g 1 m) * (∑' m : ℤ, g 2 m)
      = ∑' q : ℤ × ℤ, g 1 q.1 * g 2 q.2 :=
    tsum_mul_tsum_of_summable_norm (hF 1) (hF 2)
  have hmain : (∑' m : ℤ, g 0 m) * (∑' q : ℤ × ℤ, g 1 q.1 * g 2 q.2)
      = ∑' p : ℤ × ℤ × ℤ, g 0 p.1 * (g 1 p.2.1 * g 2 p.2.2) :=
    tsum_mul_tsum_of_summable_norm (hF 0) h01
  rw [show (∏ i : Fin 3, ∑' m : ℤ, g i m)
      = (∑' m : ℤ, g 0 m) * (∑' m : ℤ, g 1 m) * (∑' m : ℤ, g 2 m) by
    rw [Fin.prod_univ_three]]
  rw [← Equiv.tsum_eq fin3IntEquivProd.symm (fun j : Fin 3 → ℤ => ∏ i : Fin 3, g i (j i))]
  rw [show (∑' p : ℤ × ℤ × ℤ, ∏ i : Fin 3, g i ((fin3IntEquivProd.symm p) i))
      = ∑' p : ℤ × ℤ × ℤ, g 0 p.1 * (g 1 p.2.1 * g 2 p.2.2) by
    apply tsum_congr
    intro p
    obtain ⟨a, b, c⟩ := p
    simp only [fin3IntEquivProd, Equiv.coe_fn_symm_mk]
    rw [Fin.prod_univ_three]
    simp [mul_assoc]]
  rw [← hmain, ← hinner]
  ring

/-! ## 2. The one-dimensional theta identities -/

/-- **The one-dimensional theta/Poisson identity** in the orientation used below:
`Σ_{n∈ℤ} e^{-(z+ℓn)²/(4t)} = (2√(πt)/ℓ)·Σ_{n∈ℤ} e^{-t(2πn/ℓ)²} cos(2πnz/ℓ)` for `ℓ, t > 0`.

This is `Commons.Analysis.Fourier.theta_shift_real` at `a = ℓ²/(4t)`, `c = z/ℓ`. -/
theorem theta1_cos {ℓ : ℝ} (hℓ : 0 < ℓ) {t : ℝ} (ht : 0 < t) (z : ℝ) :
    (∑' n : ℤ, Real.exp (-((z + ℓ * (n : ℝ)) ^ 2 / (4 * t))))
      = (2 * Real.sqrt (Real.pi * t) / ℓ)
        * ∑' n : ℤ, Real.exp (-(t * ((2 * Real.pi / ℓ) * (n : ℝ)) ^ 2))
            * Real.cos (((2 * Real.pi / ℓ) * (n : ℝ)) * z) := by
  have ha : 0 < ℓ ^ 2 / (4 * t) := by positivity
  have h := Commons.Analysis.Fourier.theta_shift_real (a := ℓ ^ 2 / (4 * t)) (c := z / ℓ) ha
  have hL : (∑' n : ℤ, Real.exp (-((ℓ ^ 2 / (4 * t)) * ((n : ℝ) + z / ℓ) ^ 2)))
      = ∑' n : ℤ, Real.exp (-((z + ℓ * (n : ℝ)) ^ 2 / (4 * t))) := by
    apply tsum_congr
    intro n
    rw [show -((ℓ ^ 2 / (4 * t)) * ((n : ℝ) + z / ℓ) ^ 2)
        = -((z + ℓ * (n : ℝ)) ^ 2 / (4 * t)) by field_simp; ring]
  have hsqrt : Real.sqrt (Real.pi / (ℓ ^ 2 / (4 * t))) = 2 * Real.sqrt (Real.pi * t) / ℓ := by
    rw [show Real.pi / (ℓ ^ 2 / (4 * t)) = 4 * Real.pi * t / ℓ ^ 2 by field_simp]
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 4 * Real.pi * t), Real.sqrt_sq hℓ.le]
    rw [show Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt (Real.pi * t) by
      rw [show (4 * Real.pi * t : ℝ) = (2 * Real.sqrt (Real.pi * t)) ^ 2 by
        rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.pi * t)]; ring,
        Real.sqrt_sq (by positivity)]]
  have hsum : (∑' n : ℤ, Real.exp (-((Real.pi * (n : ℝ)) ^ 2) / (ℓ ^ 2 / (4 * t)))
        * Real.cos (2 * Real.pi * (n : ℝ) * (z / ℓ)))
      = ∑' n : ℤ, Real.exp (-(t * ((2 * Real.pi / ℓ) * (n : ℝ)) ^ 2))
            * Real.cos (((2 * Real.pi / ℓ) * (n : ℝ)) * z) := by
    apply tsum_congr
    intro n
    rw [show -((Real.pi * (n : ℝ)) ^ 2) / (ℓ ^ 2 / (4 * t))
          = -(t * ((2 * Real.pi / ℓ) * (n : ℝ)) ^ 2) by field_simp; ring,
      show 2 * Real.pi * (n : ℝ) * (z / ℓ) = ((2 * Real.pi / ℓ) * (n : ℝ)) * z by ring]
  have hR : (Real.sqrt (Real.pi / (ℓ ^ 2 / (4 * t))))
        * (∑' n : ℤ, Real.exp (-((Real.pi * (n : ℝ)) ^ 2) / (ℓ ^ 2 / (4 * t)))
            * Real.cos (2 * Real.pi * (n : ℝ) * (z / ℓ)))
      = (2 * Real.sqrt (Real.pi * t) / ℓ)
        * ∑' n : ℤ, Real.exp (-(t * ((2 * Real.pi / ℓ) * (n : ℝ)) ^ 2))
            * Real.cos (((2 * Real.pi / ℓ) * (n : ℝ)) * z) := by
    rw [hsqrt, hsum]
  rw [hL, hR] at h
  exact h

/-- The companion **sine sum vanishes**: `Σ_{n∈ℤ} e^{-a n²} sin (b n) = 0` for `a > 0`
(the summand is odd in `n`). -/
theorem theta1_sin_zero {a b : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, Real.exp (-(a * (n : ℝ) ^ 2)) * Real.sin (b * (n : ℝ))) = 0 := by
  set f : ℤ → ℝ := fun n => Real.exp (-(a * (n : ℝ) ^ 2)) * Real.sin (b * (n : ℝ)) with hf
  have h := Equiv.tsum_eq (Equiv.neg ℤ) f
  simp only [Equiv.neg_apply] at h
  have hpt : ∀ n : ℤ, f (-n) = -f n := by
    intro n
    simp only [hf, Int.cast_neg, neg_sq]
    rw [mul_neg, Real.sin_neg]
    ring
  rw [tsum_congr hpt, tsum_neg] at h
  linarith [h]

/-! ## 3. The three-dimensional theta identity -/

section Theta3

variable {ℓ t : ℝ}

/-- The coordinates of `z + ℓ • vecZ m`. -/
lemma ofLp_add_smul_vecZ (z : ℝ³) (m : Fin 3 → ℤ) (i : Fin 3) :
    (z + ℓ • vecZ m).ofLp i = z.ofLp i + ℓ * (m i : ℝ) := by
  rw [WithLp.ofLp_add, WithLp.ofLp_smul]
  simp [vecZ, Pi.add_apply, Pi.smul_apply]

lemma norm_sq_add_smul_vecZ (z : ℝ³) (m : Fin 3 → ℤ) :
    ‖z + ℓ • vecZ m‖ ^ 2 = ∑ i, (z.ofLp i + ℓ * (m i : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, ofLp_add_smul_vecZ]

lemma inner_smul_vecZ (z : ℝ³) (j : Fin 3 → ℤ) :
    inner ℝ ((2 * Real.pi / ℓ) • vecZ j) z
      = ∑ i, (2 * Real.pi / ℓ) * (j i : ℝ) * z.ofLp i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [WithLp.ofLp_smul, WithLp.ofLp_toLp, Pi.smul_apply, RCLike.inner_apply]
  simp [vecZ]
  ring

lemma norm_sq_smul_vecZ (j : Fin 3 → ℤ) :
    ‖(2 * Real.pi / ℓ) • vecZ j‖ ^ 2 = ∑ i, ((2 * Real.pi / ℓ) * (j i : ℝ)) ^ 2 := by
  rw [norm_smul, mul_pow, norm_vecZ_sq, Real.norm_eq_abs, sq_abs]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A product of per-coordinate summable **nonnegative** real series over `ℤ`, re-indexed by
`Fin 3 → ℤ`, is summable. -/
lemma summable_pi3_prod_of_nonneg {F : Fin 3 → ℤ → ℝ} (hF : ∀ i n, 0 ≤ F i n)
    (hS : ∀ i, Summable (F i)) :
    Summable fun j : Fin 3 → ℤ => ∏ i, F i (j i) := by
  rw [← Equiv.summable_iff (fin3IntEquivProd.symm)]
  change Summable fun p : ℤ × ℤ × ℤ => ∏ i, F i ((fin3IntEquivProd.symm p) i)
  have heq : (fun p : ℤ × ℤ × ℤ => ∏ i, F i ((fin3IntEquivProd.symm p) i))
      = fun p : ℤ × ℤ × ℤ => F 0 p.1 * (F 1 p.2.1 * F 2 p.2.2) := by
    funext p
    obtain ⟨a, b, c⟩ := p
    simp only [fin3IntEquivProd, Equiv.coe_fn_symm_mk]
    rw [Fin.prod_univ_three]
    simp [mul_assoc]
  rw [heq]
  have h12 : Summable fun q : ℤ × ℤ => F 1 q.1 * F 2 q.2 := by
    refine (summable_prod_of_nonneg (fun q => mul_nonneg (hF 1 q.1) (hF 2 q.2))).mpr ⟨?_, ?_⟩
    · intro a
      exact (hS 2).mul_left (F 1 a)
    · have h1 : (fun a : ℤ => ∑' b : ℤ, F 1 a * F 2 b)
          = fun a : ℤ => F 1 a * ∑' b : ℤ, F 2 b := by
        funext a
        rw [tsum_mul_left]
      rw [h1]
      exact (hS 1).mul_right _
  refine (summable_prod_of_nonneg (fun p : ℤ × ℤ × ℤ =>
    mul_nonneg (hF 0 p.1) (mul_nonneg (hF 1 p.2.1) (hF 2 p.2.2)))).mpr ⟨?_, ?_⟩
  · intro a
    exact h12.mul_left (F 0 a)
  · have h1 : (fun a : ℤ => ∑' q : ℤ × ℤ, F 0 a * (F 1 q.1 * F 2 q.2))
        = fun a : ℤ => F 0 a * ∑' q : ℤ × ℤ, F 1 q.1 * F 2 q.2 := by
      funext a
      rw [tsum_mul_left]
    rw [h1]
    exact (hS 0).mul_right _

/-- The one-dimensional Gaussian sum over the shifted image points, in the form used for the
three-dimensional identity: `Π_i Σ_n e^{-(z_i+ℓn)²/4t} = Σ_{m∈ℤ³} e^{-‖z+ℓm‖²/4t}`. -/
lemma prod_image_sum (hℓ : 0 < ℓ) (ht : 0 < t) (z : ℝ³) :
    (∏ i : Fin 3, ∑' n : ℤ, Real.exp (-((z.ofLp i + ℓ * (n : ℝ)) ^ 2 / (4 * t))))
      = ∑' m : Fin 3 → ℤ, Real.exp (-(‖z + ℓ • vecZ m‖ ^ 2 / (4 * t))) := by
  have hsumm : ∀ i : Fin 3, Summable fun n : ℤ =>
      Real.exp (-((z.ofLp i + ℓ * (n : ℝ)) ^ 2 / (4 * t))) := by
    intro i
    have hbase : Summable fun n : ℤ => Real.exp (-(ℓ ^ 2 / (8 * t) * (n : ℝ) ^ 2)) := by
      have h := Commons.Analysis.Fourier.summable_exp_neg_mul_sq_int (c := ℓ ^ 2 / (8 * t))
        (by positivity)
      refine h.congr (fun n => ?_)
      congr 1
      ring
    refine Summable.of_norm_bounded (g := fun n : ℤ =>
      Real.exp (z.ofLp i ^ 2 / (2 * t)) * Real.exp (-(ℓ ^ 2 / (8 * t) * (n : ℝ) ^ 2)))
      (hbase.mul_left _) fun n => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hkey : ℓ ^ 2 * (n : ℝ) ^ 2 / 2 - z.ofLp i ^ 2 ≤ (z.ofLp i + ℓ * (n : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (ℓ * (n : ℝ) + 2 * z.ofLp i)]
    have h4t : (0 : ℝ) < 4 * t := by positivity
    have hL : (4 * t) * -((z.ofLp i + ℓ * (n : ℝ)) ^ 2 / (4 * t))
        = -((z.ofLp i + ℓ * (n : ℝ)) ^ 2) := by
      field_simp
    have hmul : (4 * t) * (z.ofLp i ^ 2 / (2 * t) + -(ℓ ^ 2 / (8 * t) * (n : ℝ) ^ 2))
        = 2 * z.ofLp i ^ 2 - ℓ ^ 2 * (n : ℝ) ^ 2 / 2 := by
      field_simp
      ring
    refine le_of_mul_le_mul_left ?_ h4t
    rw [hL, hmul]
    nlinarith [hkey]
  rw [← pi3_prod_tsum_real
    (fun i n => Real.exp (-((z.ofLp i + ℓ * (n : ℝ)) ^ 2 / (4 * t)))) hsumm]
  apply tsum_congr
  intro m
  rw [← Real.exp_sum, norm_sq_add_smul_vecZ]
  congr 1
  rw [Finset.sum_neg_distrib, ← Finset.sum_div]
/-- The elementary trigonometric identity behind the three-dimensional theta identity:
`cos (a₀+a₁+a₂) = cos a₀ cos a₁ cos a₂ - sin a₀ sin a₁ cos a₂ - sin a₀ cos a₁ sin a₂
   - cos a₀ sin a₁ sin a₂`. -/
lemma cos_three (a₀ a₁ a₂ : ℝ) :
    Real.cos (a₀ + a₁ + a₂) = Real.cos a₀ * Real.cos a₁ * Real.cos a₂
      - Real.sin a₀ * Real.sin a₁ * Real.cos a₂
      - Real.sin a₀ * Real.cos a₁ * Real.sin a₂
      - Real.cos a₀ * Real.sin a₁ * Real.sin a₂ := by
  rw [Real.cos_add, Real.cos_add, Real.sin_add]
  ring

/-- The per-coordinate cosine factor `e^{-t(2πn/ℓ)²}cos((2πn/ℓ)z_i)` of the box-lattice theta
summand. -/
def Fac (ℓ t : ℝ) (z : ℝ³) (i : Fin 3) (n : ℤ) : ℝ :=
  Real.exp (-(t * ((2 * Real.pi / ℓ) * (n : ℝ)) ^ 2))
    * Real.cos (((2 * Real.pi / ℓ) * (n : ℝ)) * z.ofLp i)

/-- The per-coordinate sine companion of `Fac`. -/
def FacS (ℓ t : ℝ) (z : ℝ³) (i : Fin 3) (n : ℤ) : ℝ :=
  Real.exp (-(t * ((2 * Real.pi / ℓ) * (n : ℝ)) ^ 2))
    * Real.sin (((2 * Real.pi / ℓ) * (n : ℝ)) * z.ofLp i)

lemma abs_Fac_le (ℓ t : ℝ) (z : ℝ³) (i : Fin 3) (n : ℤ) :
    |Fac ℓ t z i n| ≤ Real.exp (-(t * (2 * Real.pi / ℓ) ^ 2 * (n : ℝ) ^ 2)) := by
  rw [Fac, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine le_trans (mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)) ?_
  exact le_of_eq (by congr 1; ring)

lemma abs_FacS_le (ℓ t : ℝ) (z : ℝ³) (i : Fin 3) (n : ℤ) :
    |FacS ℓ t z i n| ≤ Real.exp (-(t * (2 * Real.pi / ℓ) ^ 2 * (n : ℝ) ^ 2)) := by
  rw [FacS, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine le_trans (mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _)) ?_
  exact le_of_eq (by congr 1; ring)

lemma summable_fac_gauss {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) :
    Summable fun n : ℤ => Real.exp (-(t * (2 * Real.pi / ℓ) ^ 2 * (n : ℝ) ^ 2)) := by
  have h2 : (0 : ℝ) < 2 * Real.pi / ℓ := by positivity
  have h := Commons.Analysis.Fourier.summable_exp_neg_mul_sq_int
    (c := t * (2 * Real.pi / ℓ) ^ 2) (mul_pos ht (pow_pos h2 2))
  refine h.congr (fun n => ?_)
  congr 1
  ring

lemma summable_Fac {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) (z : ℝ³) (i : Fin 3) :
    Summable (Fac ℓ t z i) := by
  refine Summable.of_norm_bounded (summable_fac_gauss hℓ ht) fun n => ?_
  rw [Real.norm_eq_abs]
  exact abs_Fac_le ℓ t z i n

lemma summable_FacS {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) (z : ℝ³) (i : Fin 3) :
    Summable (FacS ℓ t z i) := by
  refine Summable.of_norm_bounded (summable_fac_gauss hℓ ht) fun n => ?_
  rw [Real.norm_eq_abs]
  exact abs_FacS_le ℓ t z i n

lemma FacS_tsum_zero {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) (z : ℝ³) (i : Fin 3) :
    (∑' n : ℤ, FacS ℓ t z i n) = 0 := by
  have h2 : (0 : ℝ) < 2 * Real.pi / ℓ := by positivity
  simp only [FacS]
  have h := theta1_sin_zero (a := t * (2 * Real.pi / ℓ) ^ 2)
    (b := (2 * Real.pi / ℓ) * z.ofLp i) (mul_pos ht (pow_pos h2 2))
  simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using h

lemma Fac_tsum {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) (z : ℝ³) (i : Fin 3) :
    (∑' n : ℤ, Fac ℓ t z i n)
      = (ℓ / (2 * Real.sqrt (Real.pi * t)))
        * ∑' n : ℤ, Real.exp (-((z.ofLp i + ℓ * (n : ℝ)) ^ 2 / (4 * t))) := by
  have h := theta1_cos hℓ ht (z.ofLp i)
  have hCpos : 0 < 2 * Real.sqrt (Real.pi * t) / ℓ := by positivity
  have hCinv : ℓ / (2 * Real.sqrt (Real.pi * t)) = 1 / (2 * Real.sqrt (Real.pi * t) / ℓ) := by
    field_simp
  simp only [Fac]
  rw [hCinv, h, ← mul_assoc, one_div_mul_cancel (ne_of_gt hCpos), one_mul]

/-- The pointwise expansion of the box-lattice theta summand: `e^{-t‖k_j‖²}cos⟨k_j,z⟩` is the
product of the three cosine factors minus the three "two-sine" terms of `cos_three`. -/
lemma theta3_pointwise (ℓ t : ℝ) (z : ℝ³) (j : Fin 3 → ℤ) :
    Real.exp (-(t * ‖(2 * Real.pi / ℓ) • vecZ j‖ ^ 2))
        * Real.cos (inner ℝ ((2 * Real.pi / ℓ) • vecZ j) z)
      = ∏ i, Fac ℓ t z i (j i)
        - (FacS ℓ t z 0 (j 0) * FacS ℓ t z 1 (j 1) * Fac ℓ t z 2 (j 2)
            + FacS ℓ t z 0 (j 0) * Fac ℓ t z 1 (j 1) * FacS ℓ t z 2 (j 2)
            + Fac ℓ t z 0 (j 0) * FacS ℓ t z 1 (j 1) * FacS ℓ t z 2 (j 2)) := by
  set a₀ : ℝ := (2 * Real.pi / ℓ) * (j 0 : ℝ) * z.ofLp 0 with ha₀
  set a₁ : ℝ := (2 * Real.pi / ℓ) * (j 1 : ℝ) * z.ofLp 1 with ha₁
  set a₂ : ℝ := (2 * Real.pi / ℓ) * (j 2 : ℝ) * z.ofLp 2 with ha₂
  have hinner : inner ℝ ((2 * Real.pi / ℓ) • vecZ j) z = a₀ + a₁ + a₂ := by
    rw [inner_smul_vecZ, Fin.sum_univ_three, ha₀, ha₁, ha₂]
  have hnorm : ‖(2 * Real.pi / ℓ) • vecZ j‖ ^ 2
      = ((2 * Real.pi / ℓ) * (j 0 : ℝ)) ^ 2 + ((2 * Real.pi / ℓ) * (j 1 : ℝ)) ^ 2
        + ((2 * Real.pi / ℓ) * (j 2 : ℝ)) ^ 2 := by
    rw [norm_sq_smul_vecZ, Fin.sum_univ_three]
  have hexp : Real.exp (-(t * (((2 * Real.pi / ℓ) * (j 0 : ℝ)) ^ 2
          + ((2 * Real.pi / ℓ) * (j 1 : ℝ)) ^ 2 + ((2 * Real.pi / ℓ) * (j 2 : ℝ)) ^ 2)))
      = Real.exp (-(t * ((2 * Real.pi / ℓ) * (j 0 : ℝ)) ^ 2))
        * Real.exp (-(t * ((2 * Real.pi / ℓ) * (j 1 : ℝ)) ^ 2))
        * Real.exp (-(t * ((2 * Real.pi / ℓ) * (j 2 : ℝ)) ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have htrig := cos_three a₀ a₁ a₂
  simp only [Fac, FacS, Fin.prod_univ_three]
  rw [hinner, hnorm, hexp, htrig, ha₀, ha₁, ha₂]
  ring

/-- The sum over `Fin 3 → ℤ` of a product of per-coordinate factors is the product of the
one-dimensional sums. -/
lemma prod_sum_factors (g : Fin 3 → ℤ → ℝ) (hg : ∀ i, Summable (g i)) :
    (∑' j : Fin 3 → ℤ, g 0 (j 0) * g 1 (j 1) * g 2 (j 2))
      = (∑' n : ℤ, g 0 n) * (∑' n : ℤ, g 1 n) * (∑' n : ℤ, g 2 n) := by
  have h := pi3_prod_tsum_real g hg
  have h2 : (∑' j : Fin 3 → ℤ, ∏ i, g i (j i))
      = ∑' j : Fin 3 → ℤ, g 0 (j 0) * g 1 (j 1) * g 2 (j 2) := by
    apply tsum_congr
    intro j
    rw [Fin.prod_univ_three]
  rw [h2] at h
  rw [h, Fin.prod_univ_three]

set_option maxHeartbeats 1000000 in
lemma summable_prod_factors {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) (g : Fin 3 → ℤ → ℝ)
    (hg : ∀ i n, |g i n| ≤ Real.exp (-(t * (2 * Real.pi / ℓ) ^ 2 * (n : ℝ) ^ 2))) :
    Summable fun j : Fin 3 → ℤ => g 0 (j 0) * g 1 (j 1) * g 2 (j 2) := by
  have hG : Summable fun j : Fin 3 → ℤ =>
      ∏ i, Real.exp (-(t * (2 * Real.pi / ℓ) ^ 2 * (j i : ℝ) ^ 2)) :=
    summable_pi3_prod_of_nonneg
      (F := fun i (n : ℤ) => Real.exp (-(t * (2 * Real.pi / ℓ) ^ 2 * (n : ℝ) ^ 2)))
      (fun i n => (Real.exp_pos _).le) (fun _ => summable_fac_gauss hℓ ht)
  have hprod : ∀ j : Fin 3 → ℤ,
      (∏ i : Fin 3, Real.exp (-(t * (2 * Real.pi / ℓ) ^ 2 * (j i : ℝ) ^ 2)))
      = Real.exp (-(t * (2 * Real.pi / ℓ) ^ 2 * (j 0 : ℝ) ^ 2))
        * (Real.exp (-(t * (2 * Real.pi / ℓ) ^ 2 * (j 1 : ℝ) ^ 2))
          * Real.exp (-(t * (2 * Real.pi / ℓ) ^ 2 * (j 2 : ℝ) ^ 2))) := by
    intro j
    rw [Fin.prod_univ_three]
    ring
  refine Summable.of_norm_bounded (hG.congr hprod) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, mul_assoc]
  exact mul_le_mul (hg 0 (j 0))
    (mul_le_mul (hg 1 (j 1)) (hg 2 (j 2)) (abs_nonneg _) (Real.exp_pos _).le)
    (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le

/-- **The three-dimensional theta/Poisson identity, image form**: for `ℓ, t > 0` and
`z : ℝ³`,

    `Σ_{m∈ℤ³} e^{-‖z + ℓm‖²/4t} = (2√(πt)/ℓ)³ Σ_{j∈ℤ³} e^{-t‖(2π/ℓ)j‖²} cos⟨(2π/ℓ)j, z⟩`,

the sums running over the dual lattice `ℤ³` and the box lattice `(2π/ℓ)ℤ³`.  It is the
three-fold product of the one-dimensional theta transformations `theta1_cos`; the three
"two-sine" terms of the expansion `cos_three` of `cos (a₀+a₁+a₂)` factor into the vanishing
one-dimensional sine sums `theta1_sin_zero`. -/
theorem theta3_images (hℓ : 0 < ℓ) (ht : 0 < t) (z : ℝ³) :
    (∑' m : Fin 3 → ℤ, Real.exp (-(‖z + ℓ • vecZ m‖ ^ 2 / (4 * t))))
      = (2 * Real.sqrt (Real.pi * t) / ℓ) ^ 3
        * ∑' j : Fin 3 → ℤ, Real.exp (-(t * ‖(2 * Real.pi / ℓ) • vecZ j‖ ^ 2))
            * Real.cos (inner ℝ ((2 * Real.pi / ℓ) • vecZ j) z) := by
  have hFsum : ∀ i : Fin 3, Summable (Fac ℓ t z i) := fun i => summable_Fac hℓ ht z i
  have hSsum : ∀ i : Fin 3, Summable (FacS ℓ t z i) := fun i => summable_FacS hℓ ht z i
  -- summability of the four pieces
  have hmajor : ∀ i n, |Fac ℓ t z i n| ≤
      Real.exp (-(t * (2 * Real.pi / ℓ) ^ 2 * (n : ℝ) ^ 2)) := fun i n => abs_Fac_le ℓ t z i n
  have hmajorS : ∀ i n, |FacS ℓ t z i n| ≤
      Real.exp (-(t * (2 * Real.pi / ℓ) ^ 2 * (n : ℝ) ^ 2)) := fun i n => abs_FacS_le ℓ t z i n
  have hprodsum : Summable fun j : Fin 3 → ℤ => ∏ i, Fac ℓ t z i (j i) := by
    have h := summable_prod_factors hℓ ht (fun i (n : ℤ) => Fac ℓ t z i n) hmajor
    refine h.congr (fun j => ?_)
    rw [Fin.prod_univ_three]
  have hpair1 : Summable fun j : Fin 3 → ℤ =>
      FacS ℓ t z 0 (j 0) * FacS ℓ t z 1 (j 1) * Fac ℓ t z 2 (j 2) :=
    summable_prod_factors hℓ ht (fun i n => ![FacS ℓ t z 0, FacS ℓ t z 1, Fac ℓ t z 2] i n)
      (by
        intro i n
        fin_cases i
        · exact abs_FacS_le ℓ t z 0 n
        · exact abs_FacS_le ℓ t z 1 n
        · exact abs_Fac_le ℓ t z 2 n)
  have hpair2 : Summable fun j : Fin 3 → ℤ =>
      FacS ℓ t z 0 (j 0) * Fac ℓ t z 1 (j 1) * FacS ℓ t z 2 (j 2) :=
    summable_prod_factors hℓ ht (fun i n => ![FacS ℓ t z 0, Fac ℓ t z 1, FacS ℓ t z 2] i n)
      (by
        intro i n
        fin_cases i
        · exact abs_FacS_le ℓ t z 0 n
        · exact abs_Fac_le ℓ t z 1 n
        · exact abs_FacS_le ℓ t z 2 n)
  have hpair3 : Summable fun j : Fin 3 → ℤ =>
      Fac ℓ t z 0 (j 0) * FacS ℓ t z 1 (j 1) * FacS ℓ t z 2 (j 2) :=
    summable_prod_factors hℓ ht (fun i n => ![Fac ℓ t z 0, FacS ℓ t z 1, FacS ℓ t z 2] i n)
      (by
        intro i n
        fin_cases i
        · exact abs_Fac_le ℓ t z 0 n
        · exact abs_FacS_le ℓ t z 1 n
        · exact abs_FacS_le ℓ t z 2 n)
  -- the pair sums vanish
  have hzero1 : (∑' j : Fin 3 → ℤ,
      FacS ℓ t z 0 (j 0) * FacS ℓ t z 1 (j 1) * Fac ℓ t z 2 (j 2)) = 0 := by
    have h1 := prod_sum_factors (fun i n => ![FacS ℓ t z 0, FacS ℓ t z 1, Fac ℓ t z 2] i n)
      (by intro i; fin_cases i <;> simp [hSsum, hFsum])
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h1 ⊢
    rw [h1]
    simp [FacS_tsum_zero hℓ ht z]
  have hzero2 : (∑' j : Fin 3 → ℤ,
      FacS ℓ t z 0 (j 0) * Fac ℓ t z 1 (j 1) * FacS ℓ t z 2 (j 2)) = 0 := by
    have h1 := prod_sum_factors (fun i n => ![FacS ℓ t z 0, Fac ℓ t z 1, FacS ℓ t z 2] i n)
      (by intro i; fin_cases i <;> simp [hSsum, hFsum])
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h1 ⊢
    rw [h1]
    simp [FacS_tsum_zero hℓ ht z]
  have hzero3 : (∑' j : Fin 3 → ℤ,
      Fac ℓ t z 0 (j 0) * FacS ℓ t z 1 (j 1) * FacS ℓ t z 2 (j 2)) = 0 := by
    have h1 := prod_sum_factors (fun i n => ![Fac ℓ t z 0, FacS ℓ t z 1, FacS ℓ t z 2] i n)
      (by intro i; fin_cases i <;> simp [hSsum, hFsum])
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h1 ⊢
    rw [h1]
    simp [FacS_tsum_zero hℓ ht z]
  -- the cosine sum
  have hcos : (∑' j : Fin 3 → ℤ, Real.exp (-(t * ‖(2 * Real.pi / ℓ) • vecZ j‖ ^ 2))
      * Real.cos (inner ℝ ((2 * Real.pi / ℓ) • vecZ j) z))
      = (ℓ / (2 * Real.sqrt (Real.pi * t))) ^ 3
        * ∑' m : Fin 3 → ℤ, Real.exp (-(‖z + ℓ • vecZ m‖ ^ 2 / (4 * t))) := by
    rw [tsum_congr (fun j => theta3_pointwise ℓ t z j)]
    rw [Summable.tsum_sub hprodsum ((hpair1.add hpair2).add hpair3),
      Summable.tsum_add (hpair1.add hpair2) hpair3, Summable.tsum_add hpair1 hpair2]
    rw [hzero1, hzero2, hzero3]
    simp only [add_zero, sub_zero]
    rw [show (∑' j : Fin 3 → ℤ, ∏ i, Fac ℓ t z i (j i))
        = ∑' j : Fin 3 → ℤ, Fac ℓ t z 0 (j 0) * Fac ℓ t z 1 (j 1) * Fac ℓ t z 2 (j 2) from
      tsum_congr (fun j => Fin.prod_univ_three _)]
    rw [prod_sum_factors (Fac ℓ t z) hFsum,
      Fac_tsum hℓ ht z 0, Fac_tsum hℓ ht z 1, Fac_tsum hℓ ht z 2]
    have h3 : (ℓ / (2 * Real.sqrt (Real.pi * t))
          * ∑' n : ℤ, Real.exp (-((z.ofLp 0 + ℓ * (n : ℝ)) ^ 2 / (4 * t))))
        * (ℓ / (2 * Real.sqrt (Real.pi * t))
          * ∑' n : ℤ, Real.exp (-((z.ofLp 1 + ℓ * (n : ℝ)) ^ 2 / (4 * t))))
        * (ℓ / (2 * Real.sqrt (Real.pi * t))
          * ∑' n : ℤ, Real.exp (-((z.ofLp 2 + ℓ * (n : ℝ)) ^ 2 / (4 * t))))
        = (ℓ / (2 * Real.sqrt (Real.pi * t))) ^ 3
          * ∏ i : Fin 3,
              ∑' n : ℤ, Real.exp (-((z.ofLp i + ℓ * (n : ℝ)) ^ 2 / (4 * t))) := by
      rw [Fin.prod_univ_three]
      ring
    rw [h3, ← prod_image_sum hℓ ht z]
  -- conclude by multiplying by the constant `C`
  have hkey : (2 * Real.sqrt (Real.pi * t) / ℓ) ^ 3
      * (ℓ / (2 * Real.sqrt (Real.pi * t))) ^ 3 = 1 := by
    rw [← mul_pow]
    have : 2 * Real.sqrt (Real.pi * t) / ℓ * (ℓ / (2 * Real.sqrt (Real.pi * t))) = 1 := by
      field_simp
    rw [this, one_pow]
  rw [hcos, ← mul_assoc, hkey, one_mul]

end Theta3

end Work.BoseRowsFS
