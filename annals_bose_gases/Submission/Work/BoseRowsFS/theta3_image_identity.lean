import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseRowsFS.KernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.theta3_image_identity`

The three-dimensional Gaussian lattice (Poisson/theta) identity, in the form used by the
FS §11 lattice row:  for `ℓ, s > 0` and `z : ℝ³`,

    Σ_{m∈ℤ³} e^{-‖z + ℓm‖²/4s} = (2√(πs)/ℓ)³ Σ_{j∈ℤ³} e^{-s‖(2π/ℓ)j‖²} cos⟨(2π/ℓ)j, z⟩,

the sums running over the dual lattice `ℤ³` and the box lattice `(2π/ℓ)ℤ³`.

It is the three-fold product of the one-dimensional theta transformations
`Commons.Analysis.Fourier.theta_shift_real`; the three "two-sine" terms of the expansion
`cos (a₀+a₁+a₂) = cos a₀ cos a₁ cos a₂ - …` factor into vanishing one-dimensional sine sums.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseRowsFS

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## 1. Factoring a sum over `Fin 3 → ℤ` -/

/-- The bijection `(Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ` sending `k` to `(k 0, k 1, k 2)`. -/
private def fin3IntEquivProd : (Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ where
  toFun k := (k 0, k 1, k 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv := by
    intro k
    funext i
    fin_cases i <;> simp
  right_inv := by
    rintro ⟨a, b, c⟩
    simp

/-- A product of three independent absolutely summable real series over `ℤ`, re-indexed by
`Fin 3 → ℤ`, equals the product of the one-dimensional sums. -/
private theorem pi3_prod_tsum_real (g : Fin 3 → ℤ → ℝ) (hg : ∀ i, Summable (g i)) :
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

/-- A product of three independent summable real series over `ℤ`, re-indexed by `Fin 3 → ℤ`,
equals the product of the one-dimensional sums. -/
private theorem prod_sum_factors (g : Fin 3 → ℤ → ℝ) (hg : ∀ i, Summable (g i)) :
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

/-! ## 2. The one-dimensional theta identities -/

/-- **The one-dimensional theta/Poisson identity**:
`Σ_{n∈ℤ} e^{-(z+ℓn)²/(4t)} = (2√(πt)/ℓ)·Σ_{n∈ℤ} e^{-t(2πn/ℓ)²} cos(2πnz/ℓ)` for `ℓ, t > 0`. -/
private theorem theta1_cos {ℓ : ℝ} (hℓ : 0 < ℓ) {t : ℝ} (ht : 0 < t) (z : ℝ) :
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
private theorem theta1_sin_zero {a b : ℝ} (ha : 0 < a) :
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

/-! ## 3. The per-coordinate factors of the box-lattice theta sum -/

/-- The Gaussian weight `e^{-s(2πn/ℓ)²}`. -/
private def gauss (ℓ s : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-(s * (2 * Real.pi / ℓ) ^ 2 * (n : ℝ) ^ 2))

/-- The per-coordinate cosine factor `e^{-s(2πn/ℓ)²}cos((2πn/ℓ)z_i)`. -/
private def cosFac (ℓ s : ℝ) (z : ℝ³) (i : Fin 3) (n : ℤ) : ℝ :=
  Real.exp (-(s * ((2 * Real.pi / ℓ) * (n : ℝ)) ^ 2))
    * Real.cos (((2 * Real.pi / ℓ) * (n : ℝ)) * z.ofLp i)

/-- The per-coordinate sine companion of `cosFac`. -/
private def sinFac (ℓ s : ℝ) (z : ℝ³) (i : Fin 3) (n : ℤ) : ℝ :=
  Real.exp (-(s * ((2 * Real.pi / ℓ) * (n : ℝ)) ^ 2))
    * Real.sin (((2 * Real.pi / ℓ) * (n : ℝ)) * z.ofLp i)

private lemma abs_cosFac_le (ℓ s : ℝ) (z : ℝ³) (i : Fin 3) (n : ℤ) :
    |cosFac ℓ s z i n| ≤ gauss ℓ s n := by
  unfold cosFac gauss
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine le_trans (mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)) ?_
  exact le_of_eq (by congr 1; ring)

private lemma abs_sinFac_le (ℓ s : ℝ) (z : ℝ³) (i : Fin 3) (n : ℤ) :
    |sinFac ℓ s z i n| ≤ gauss ℓ s n := by
  unfold sinFac gauss
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine le_trans (mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _)) ?_
  exact le_of_eq (by congr 1; ring)

private lemma summable_gauss {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) :
    Summable (gauss ℓ s) := by
  have h2 : (0 : ℝ) < 2 * Real.pi / ℓ := by positivity
  have h := Commons.Analysis.Fourier.summable_exp_neg_mul_sq_int
    (c := s * (2 * Real.pi / ℓ) ^ 2) (mul_pos hs (pow_pos h2 2))
  refine h.congr (fun n => ?_)
  unfold gauss
  congr 1
  ring

private lemma summable_cosFac {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (z : ℝ³) (i : Fin 3) :
    Summable (cosFac ℓ s z i) :=
  Summable.of_norm_bounded (summable_gauss hℓ hs) fun n => by
    rw [Real.norm_eq_abs]; exact abs_cosFac_le ℓ s z i n

private lemma summable_sinFac {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (z : ℝ³) (i : Fin 3) :
    Summable (sinFac ℓ s z i) :=
  Summable.of_norm_bounded (summable_gauss hℓ hs) fun n => by
    rw [Real.norm_eq_abs]; exact abs_sinFac_le ℓ s z i n

private lemma sinFac_tsum_zero {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (z : ℝ³) (i : Fin 3) :
    (∑' n : ℤ, sinFac ℓ s z i n) = 0 := by
  simp only [sinFac]
  have h := theta1_sin_zero (a := s * (2 * Real.pi / ℓ) ^ 2)
    (b := (2 * Real.pi / ℓ) * z.ofLp i) (by positivity)
  simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using h

private lemma cosFac_tsum {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (z : ℝ³) (i : Fin 3) :
    (∑' n : ℤ, cosFac ℓ s z i n)
      = (ℓ / (2 * Real.sqrt (Real.pi * s)))
        * ∑' n : ℤ, Real.exp (-((z.ofLp i + ℓ * (n : ℝ)) ^ 2 / (4 * s))) := by
  have h := theta1_cos hℓ hs (z.ofLp i)
  have hCpos : 0 < 2 * Real.sqrt (Real.pi * s) / ℓ := by positivity
  have hCinv : ℓ / (2 * Real.sqrt (Real.pi * s)) = 1 / (2 * Real.sqrt (Real.pi * s) / ℓ) := by
    field_simp
  simp only [cosFac]
  rw [hCinv, h, ← mul_assoc, one_div_mul_cancel (ne_of_gt hCpos), one_mul]

/-! ## 4. Coordinates, norms, inner products -/

private lemma ofLp_add_smul_vecZ {ℓ : ℝ} (z : ℝ³) (m : Fin 3 → ℤ) (i : Fin 3) :
    (z + ℓ • vecZ m).ofLp i = z.ofLp i + ℓ * (m i : ℝ) := by
  rw [WithLp.ofLp_add, WithLp.ofLp_smul]
  simp [vecZ, Pi.add_apply, Pi.smul_apply]

private lemma norm_sq_add_smul_vecZ {ℓ : ℝ} (z : ℝ³) (m : Fin 3 → ℤ) :
    ‖z + ℓ • vecZ m‖ ^ 2 = ∑ i, (z.ofLp i + ℓ * (m i : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, ofLp_add_smul_vecZ]

private lemma inner_smul_vecZ {ℓ : ℝ} (z : ℝ³) (j : Fin 3 → ℤ) :
    inner ℝ ((2 * Real.pi / ℓ) • vecZ j) z
      = ∑ i, (2 * Real.pi / ℓ) * (j i : ℝ) * z.ofLp i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [WithLp.ofLp_smul, WithLp.ofLp_toLp, Pi.smul_apply, RCLike.inner_apply]
  simp [vecZ]
  ring

private lemma norm_sq_smul_vecZ {ℓ : ℝ} (j : Fin 3 → ℤ) :
    ‖(2 * Real.pi / ℓ) • vecZ j‖ ^ 2 = ∑ i, ((2 * Real.pi / ℓ) * (j i : ℝ)) ^ 2 := by
  rw [norm_smul, mul_pow, norm_vecZ_sq, Real.norm_eq_abs, sq_abs]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A product of per-coordinate summable **nonnegative** real series over `ℤ`, re-indexed by
`Fin 3 → ℤ`, is summable. -/
private lemma summable_pi3_prod_of_nonneg {F : Fin 3 → ℤ → ℝ} (hF : ∀ i n, 0 ≤ F i n)
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

/-- `Π_i Σ_n e^{-(z_i+ℓn)²/4t} = Σ_{m∈ℤ³} e^{-‖z+ℓm‖²/4t}`. -/
private lemma prod_image_sum {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) (z : ℝ³) :
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

/-! ## 5. The trigonometric expansion of the three-dimensional summand -/

/-- `cos (a₀+a₁+a₂) = cos a₀ cos a₁ cos a₂ - sin a₀ sin a₁ cos a₂ - sin a₀ cos a₁ sin a₂
   - cos a₀ sin a₁ sin a₂`. -/
private lemma cos_three (a₀ a₁ a₂ : ℝ) :
    Real.cos (a₀ + a₁ + a₂) = Real.cos a₀ * Real.cos a₁ * Real.cos a₂
      - Real.sin a₀ * Real.sin a₁ * Real.cos a₂
      - Real.sin a₀ * Real.cos a₁ * Real.sin a₂
      - Real.cos a₀ * Real.sin a₁ * Real.sin a₂ := by
  rw [Real.cos_add, Real.cos_add, Real.sin_add]
  ring

/-- **The pointwise expansion** of the box-lattice theta summand: `e^{-s‖k_j‖²}cos⟨k_j,z⟩`
is the product of the three cosine factors minus the three "two-sine" terms. -/
private lemma theta3_pointwise (ℓ s : ℝ) (z : ℝ³) (j : Fin 3 → ℤ) :
    Real.exp (-(s * ‖(2 * Real.pi / ℓ) • vecZ j‖ ^ 2))
        * Real.cos (inner ℝ ((2 * Real.pi / ℓ) • vecZ j) z)
      = (∏ i, cosFac ℓ s z i (j i))
        - (sinFac ℓ s z 0 (j 0) * sinFac ℓ s z 1 (j 1) * cosFac ℓ s z 2 (j 2)
          + (sinFac ℓ s z 0 (j 0) * cosFac ℓ s z 1 (j 1) * sinFac ℓ s z 2 (j 2)
            + cosFac ℓ s z 0 (j 0) * sinFac ℓ s z 1 (j 1) * sinFac ℓ s z 2 (j 2))) := by
  set a₀ : ℝ := (2 * Real.pi / ℓ) * (j 0 : ℝ) * z.ofLp 0 with ha₀
  set a₁ : ℝ := (2 * Real.pi / ℓ) * (j 1 : ℝ) * z.ofLp 1 with ha₁
  set a₂ : ℝ := (2 * Real.pi / ℓ) * (j 2 : ℝ) * z.ofLp 2 with ha₂
  have hinner : inner ℝ ((2 * Real.pi / ℓ) • vecZ j) z = a₀ + a₁ + a₂ := by
    rw [inner_smul_vecZ, Fin.sum_univ_three, ha₀, ha₁, ha₂]
  have hnorm : ‖(2 * Real.pi / ℓ) • vecZ j‖ ^ 2
      = ((2 * Real.pi / ℓ) * (j 0 : ℝ)) ^ 2 + ((2 * Real.pi / ℓ) * (j 1 : ℝ)) ^ 2
        + ((2 * Real.pi / ℓ) * (j 2 : ℝ)) ^ 2 := by
    rw [norm_sq_smul_vecZ, Fin.sum_univ_three]
  have hexp : Real.exp (-(s * (((2 * Real.pi / ℓ) * (j 0 : ℝ)) ^ 2
          + ((2 * Real.pi / ℓ) * (j 1 : ℝ)) ^ 2 + ((2 * Real.pi / ℓ) * (j 2 : ℝ)) ^ 2)))
      = Real.exp (-(s * ((2 * Real.pi / ℓ) * (j 0 : ℝ)) ^ 2))
        * Real.exp (-(s * ((2 * Real.pi / ℓ) * (j 1 : ℝ)) ^ 2))
        * Real.exp (-(s * ((2 * Real.pi / ℓ) * (j 2 : ℝ)) ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have htrig := cos_three a₀ a₁ a₂
  simp only [cosFac, sinFac, Fin.prod_univ_three]
  rw [hinner, hnorm, hexp, htrig, ha₀, ha₁, ha₂]
  ring

/-! ## 6. Summability of the four pieces -/

/-- The triple product of Gaussian weights is summable. -/
private lemma summable_gauss_triple {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) :
    Summable fun j : Fin 3 → ℤ => gauss ℓ s (j 0) * gauss ℓ s (j 1) * gauss ℓ s (j 2) := by
  have h1 : Summable fun j : Fin 3 → ℤ => ∏ i, gauss ℓ s (j i) :=
    summable_pi3_prod_of_nonneg (fun i n => (Real.exp_pos _).le)
      (fun i => summable_gauss hℓ hs)
  have h2 : (fun j : Fin 3 → ℤ => ∏ i, gauss ℓ s (j i))
      = fun j : Fin 3 → ℤ => gauss ℓ s (j 0) * gauss ℓ s (j 1) * gauss ℓ s (j 2) := by
    funext j
    rw [Fin.prod_univ_three]
  rwa [h2] at h1

/-- A product of three real sequences dominated by the Gaussian weight is summable. -/
private lemma summable_triple {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (g0 g1 g2 : ℤ → ℝ)
    (h0 : ∀ n, |g0 n| ≤ gauss ℓ s n) (h1 : ∀ n, |g1 n| ≤ gauss ℓ s n)
    (h2 : ∀ n, |g2 n| ≤ gauss ℓ s n) :
    Summable fun j : Fin 3 → ℤ => g0 (j 0) * g1 (j 1) * g2 (j 2) := by
  refine Summable.of_norm_bounded (summable_gauss_triple hℓ hs) fun j => ?_
  have hb : ‖g0 (j 0) * g1 (j 1) * g2 (j 2)‖ = |g0 (j 0)| * |g1 (j 1)| * |g2 (j 2)| := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
  rw [hb]
  exact mul_le_mul (mul_le_mul (h0 _) (h1 _) (abs_nonneg _) (le_of_lt (Real.exp_pos _)))
    (h2 _) (abs_nonneg _) (mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _)))

/-! ## 7. The three-dimensional theta identity -/

theorem theta3_image_identity {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s)
    (z : EuclideanSpace ℝ (Fin 3)) :
    (∑' m : Fin 3 → ℤ, Real.exp (-(‖z + ℓ • Work.BoseRowsFS.vecZ m‖ ^ 2 / (4 * s))))
      = (2 * Real.sqrt (Real.pi * s) / ℓ) ^ 3
        * ∑' j : Fin 3 → ℤ, Real.exp (-(s * ‖(2 * Real.pi / ℓ) • Work.BoseRowsFS.vecZ j‖ ^ 2))
            * Real.cos (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseRowsFS.vecZ j) z) := by
  have hFsum : ∀ i : Fin 3, Summable (cosFac ℓ s z i) := fun i => summable_cosFac hℓ hs z i
  have hSsum : ∀ i : Fin 3, Summable (sinFac ℓ s z i) := fun i => summable_sinFac hℓ hs z i
  -- summability of the four pieces
  have hprodsum : Summable fun j : Fin 3 → ℤ => ∏ i, cosFac ℓ s z i (j i) :=
    (summable_triple hℓ hs (cosFac ℓ s z 0) (cosFac ℓ s z 1) (cosFac ℓ s z 2)
      (fun n => abs_cosFac_le ℓ s z 0 n) (fun n => abs_cosFac_le ℓ s z 1 n)
      (fun n => abs_cosFac_le ℓ s z 2 n)).congr (fun j => by rw [Fin.prod_univ_three])
  have hpair1 : Summable fun j : Fin 3 → ℤ =>
      sinFac ℓ s z 0 (j 0) * sinFac ℓ s z 1 (j 1) * cosFac ℓ s z 2 (j 2) :=
    summable_triple hℓ hs (sinFac ℓ s z 0) (sinFac ℓ s z 1) (cosFac ℓ s z 2)
      (fun n => abs_sinFac_le ℓ s z 0 n) (fun n => abs_sinFac_le ℓ s z 1 n)
      (fun n => abs_cosFac_le ℓ s z 2 n)
  have hpair2 : Summable fun j : Fin 3 → ℤ =>
      sinFac ℓ s z 0 (j 0) * cosFac ℓ s z 1 (j 1) * sinFac ℓ s z 2 (j 2) :=
    summable_triple hℓ hs (sinFac ℓ s z 0) (cosFac ℓ s z 1) (sinFac ℓ s z 2)
      (fun n => abs_sinFac_le ℓ s z 0 n) (fun n => abs_cosFac_le ℓ s z 1 n)
      (fun n => abs_sinFac_le ℓ s z 2 n)
  have hpair3 : Summable fun j : Fin 3 → ℤ =>
      cosFac ℓ s z 0 (j 0) * sinFac ℓ s z 1 (j 1) * sinFac ℓ s z 2 (j 2) :=
    summable_triple hℓ hs (cosFac ℓ s z 0) (sinFac ℓ s z 1) (sinFac ℓ s z 2)
      (fun n => abs_cosFac_le ℓ s z 0 n) (fun n => abs_sinFac_le ℓ s z 1 n)
      (fun n => abs_sinFac_le ℓ s z 2 n)
  have hpair23 : Summable fun j : Fin 3 → ℤ =>
      (sinFac ℓ s z 0 (j 0) * cosFac ℓ s z 1 (j 1) * sinFac ℓ s z 2 (j 2)
        + cosFac ℓ s z 0 (j 0) * sinFac ℓ s z 1 (j 1) * sinFac ℓ s z 2 (j 2)) :=
    hpair2.add hpair3
  have hcorr : Summable fun j : Fin 3 → ℤ =>
      (sinFac ℓ s z 0 (j 0) * sinFac ℓ s z 1 (j 1) * cosFac ℓ s z 2 (j 2)
        + (sinFac ℓ s z 0 (j 0) * cosFac ℓ s z 1 (j 1) * sinFac ℓ s z 2 (j 2)
          + cosFac ℓ s z 0 (j 0) * sinFac ℓ s z 1 (j 1) * sinFac ℓ s z 2 (j 2))) :=
    hpair1.add hpair23
  -- the three "two-sine" sums vanish
  have hzero1 : (∑' j : Fin 3 → ℤ,
      sinFac ℓ s z 0 (j 0) * sinFac ℓ s z 1 (j 1) * cosFac ℓ s z 2 (j 2)) = 0 := by
    have h1 := prod_sum_factors (fun i n => ![sinFac ℓ s z 0, sinFac ℓ s z 1, cosFac ℓ s z 2] i n)
      (by intro i; fin_cases i <;> simp [hSsum, hFsum])
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h1 ⊢
    rw [h1, sinFac_tsum_zero hℓ hs z 0]
    ring
  have hzero2 : (∑' j : Fin 3 → ℤ,
      sinFac ℓ s z 0 (j 0) * cosFac ℓ s z 1 (j 1) * sinFac ℓ s z 2 (j 2)) = 0 := by
    have h1 := prod_sum_factors (fun i n => ![sinFac ℓ s z 0, cosFac ℓ s z 1, sinFac ℓ s z 2] i n)
      (by intro i; fin_cases i <;> simp [hSsum, hFsum])
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h1 ⊢
    rw [h1, sinFac_tsum_zero hℓ hs z 0]
    ring
  have hzero3 : (∑' j : Fin 3 → ℤ,
      cosFac ℓ s z 0 (j 0) * sinFac ℓ s z 1 (j 1) * sinFac ℓ s z 2 (j 2)) = 0 := by
    have h1 := prod_sum_factors (fun i n => ![cosFac ℓ s z 0, sinFac ℓ s z 1, sinFac ℓ s z 2] i n)
      (by intro i; fin_cases i <;> simp [hSsum, hFsum])
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h1 ⊢
    rw [h1, sinFac_tsum_zero hℓ hs z 1]
    ring
  -- the cosine sum, split against the vanishing correction
  have hcos : (∑' j : Fin 3 → ℤ, Real.exp (-(s * ‖(2 * Real.pi / ℓ) • vecZ j‖ ^ 2))
        * Real.cos (inner ℝ ((2 * Real.pi / ℓ) • vecZ j) z))
      = (ℓ / (2 * Real.sqrt (Real.pi * s))) ^ 3
        * ∑' m : Fin 3 → ℤ, Real.exp (-(‖z + ℓ • vecZ m‖ ^ 2 / (4 * s))) := by
    rw [tsum_congr (fun j => theta3_pointwise ℓ s z j),
      Summable.tsum_sub hprodsum hcorr,
      Summable.tsum_add hpair1 hpair23,
      Summable.tsum_add hpair2 hpair3,
      hzero1, hzero2, hzero3, add_zero, add_zero, sub_zero,
      pi3_prod_tsum_real (cosFac ℓ s z) hFsum, Fin.prod_univ_three,
      cosFac_tsum hℓ hs z 0, cosFac_tsum hℓ hs z 1, cosFac_tsum hℓ hs z 2,
      ← prod_image_sum hℓ hs z, Fin.prod_univ_three]
    ring
  -- conclude by multiplying by the constant
  have hCD : (2 * Real.sqrt (Real.pi * s) / ℓ) * (ℓ / (2 * Real.sqrt (Real.pi * s))) = 1 := by
    have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
    have hs0 : 2 * Real.sqrt (Real.pi * s) ≠ 0 := by
      have : 0 < Real.sqrt (Real.pi * s) := Real.sqrt_pos.mpr (by positivity)
      positivity
    field_simp
  rw [hcos, ← mul_assoc, ← mul_pow, hCD, one_pow, one_mul]

end Work.BoseRowsFS
