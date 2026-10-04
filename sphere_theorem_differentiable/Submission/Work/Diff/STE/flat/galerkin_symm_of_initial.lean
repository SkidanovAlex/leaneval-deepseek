/-
# Symmetry of the Galerkin coefficients is preserved by the truncated flow

This file proves `Work.Diff.STE.flat.galerkin_symm_of_initial`: a family of Fourier coefficients
`c` solving the *truncated* (Galerkin) DeTurck ODE on the box `box n N`, with a symmetric initial
datum `c₀`, stays symmetric for all times in `[0, T)`.

## The argument

Write `a t := ofCoeff (c t) (hsupp t)` for the box-supported coefficient family of `c t`, and

* `antiCoeff (a t) k i j = a t k i j - a t k j i` (the antisymmetric part of the coefficients),
* `antiSum (a t) = Σ_{k,i,j} ‖antiCoeff (a t) k i j‖`,
* `antiEnergy (a t) = Σ_{k,i,j} ‖antiCoeff (a t) k i j‖²`.

The energy `E t := antiEnergy (a t)` is differentiable, `E ≥ 0`, `E 0 = 0` (the initial datum is
symmetric), and one shows `E' t ≤ C · E t` with a constant `C` depending only on the truncation
order `N`, the dimension `n`, the ellipticity constant `lam` and the size of the jet of `a` on the
time interval.  Grönwall's lemma (`eq_zero_of_deriv_le`) then gives `E ≡ 0`, whence all the
coefficients `a t k` are symmetric.

The key estimate is the *pointwise* bound

`‖Φ (x, jet a) i j - Φ (x, jet a) j i‖ ≤ K · antiSum a`

for `x` in the unit cube.  It comes from the DeTurck shape `Φ (A,L,B) = secOpFlat A B + N (x,A,L)`:

* the second-jet part is `Σ_{cd} ((reMat A)⁻¹) c d (B c d i j - B c d j i)`, and in the explicit
  finite-sum picture `B c d i j - B c d j i` is a linear combination of the antisymmetric parts of
  the coefficients, with weights bounded by `(2πN)²`; the inverse-metric entries are bounded by the
  ellipticity constant (`quadForm_inv_entry_le`);
* the lower-order part is the antisymmetrisation of `N`, bounded by the mean-value/Lipschitz
  estimate `nDiff_bound_quadForm` applied at the second jet `0`, together with the symmetry of `N`
  at symmetric value/1-jet pairs (which is `hsym` read at the jet `(symmMat A, symmMat L, 0)`).
-/

import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.GalerkinDefs
import Submission.Work.Diff.STE.flat.GalerkinJet
import Submission.Work.Diff.STE.flat.GalerkinSmooth
import Submission.Work.Diff.STE.flat.galerkin_ode_existence
import Submission.Work.Diff.STE.flat.torus_uniqueness
import Submission.Work.Diff.STE.flat.norm_fourierCoeff_sub_le
import Submission.Work.Diff.STE.flat.galerkin.nDiff_bound_quadForm
import Submission.Work.Diff.STE.flat.galerkin.coeff_box_sum_bound
import Submission.Work.Diff.STE.flat.galerkin.inv_entry_le_of_quadForm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

set_option maxHeartbeats 4000000

open Work.Diff.STE Work.Diff.STE.Flat
open Work.Diff.STE.Flat.Galerkin
  (Coeff toCoeff ofCoeff toCoeff_ofCoeff valExp valExp_eq_seriesFunM linExp secExp jetExp dExp d2Exp
    closedCube rhsExp)
open scoped BigOperators Topology Matrix
open MeasureTheory

set_option maxHeartbeats 2000000

noncomputable section

variable {n : ℕ}

/-! ## General summation helpers -/

/-- A double sum of a constant. -/
lemma sum2_le_card_mul {ι κ : Type*} [Fintype ι] [Fintype κ] {f : ι → κ → ℝ} {C : ℝ}
    (h : ∀ i j, f i j ≤ C) :
    (∑ i, ∑ j, f i j) ≤ ((Fintype.card ι * Fintype.card κ : ℕ) : ℝ) * C := by
  calc (∑ i, ∑ j, f i j) ≤ ∑ i, ∑ j, C :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = ((Fintype.card ι * Fintype.card κ : ℕ) : ℝ) * C := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring

/-- A triple sum of a constant. -/
lemma sum3_le_card_mul {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    {f : ι → κ → μ → ℝ} {C : ℝ} (h : ∀ i j k, f i j k ≤ C) :
    (∑ i, ∑ j, ∑ k, f i j k) ≤ ((Fintype.card ι * Fintype.card κ * Fintype.card μ : ℕ) : ℝ) * C := by
  calc (∑ i, ∑ j, ∑ k, f i j k) ≤ ∑ i, ∑ j, ∑ k, C :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => h i j k
    _ = ((Fintype.card ι * Fintype.card κ * Fintype.card μ : ℕ) : ℝ) * C := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring

/-- A constant factor is pulled out of a triple sum. -/
lemma sum3_const_mul {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (c : ℝ) (f : ι → κ → μ → ℝ) :
    (∑ i, ∑ j, ∑ k, c * f i j k) = c * (∑ i, ∑ j, ∑ k, f i j k) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum Finset.univ (fun k => f i j k) c).symm

/-- A constant factor is pulled out of a double sum. -/
lemma sum_sum_const_mul' {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ℝ) (X : ι → κ → ℝ) :
    (∑ i, ∑ j, c * X i j) = c * (∑ i, ∑ j, X i j) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    (Finset.mul_sum Finset.univ (fun j => X i j) c).symm

/-- The norm of a real number viewed as a complex number. -/
lemma norm_ofReal_C (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq_abs]
    ring
  calc ‖(r : ℂ)‖ = Real.sqrt (‖(r : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (|r| ^ 2) := by rw [h]
    _ = |r| := Real.sqrt_sq (abs_nonneg r)

/-! ## The antisymmetric part of a box-supported coefficient family -/

/-- The antisymmetric part (in the two matrix indices) of a box-supported coefficient family. -/
def antiCoeff {n N : ℕ} (a : Coeff n N) : Coeff n N := fun k i j => a k i j - a k j i

@[simp] lemma antiCoeff_apply {n N : ℕ} (a : Coeff n N) (k : box n N) (i j : Fin n) :
    antiCoeff a k i j = a k i j - a k j i := rfl

/-- The total size (sum of the norms) of the antisymmetric part of a coefficient family. -/
def antiSum {n N : ℕ} (a : Coeff n N) : ℝ := ∑ k, ∑ i, ∑ j, ‖antiCoeff a k i j‖

/-- The `ℓ²` energy of the antisymmetric part of a coefficient family. -/
def antiEnergy {n N : ℕ} (a : Coeff n N) : ℝ := ∑ k, ∑ i, ∑ j, ‖antiCoeff a k i j‖ ^ 2

/-- The total size (sum of the norms of the coefficients) of a coefficient family. -/
def fullSum {n N : ℕ} (a : Coeff n N) : ℝ := ∑ k, ∑ i, ∑ j, ‖a k i j‖

lemma antiSum_nonneg {n N : ℕ} (a : Coeff n N) : 0 ≤ antiSum a :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    norm_nonneg _

lemma antiEnergy_nonneg {n N : ℕ} (a : Coeff n N) : 0 ≤ antiEnergy a :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    sq_nonneg _

lemma antiSum_eq_sum_prod {n N : ℕ} (a : Coeff n N) :
    antiSum a = ∑ p : box n N × Fin n × Fin n, ‖antiCoeff a p.1 p.2.1 p.2.2‖ := by
  rw [antiSum]
  rw [show (∑ k : box n N, ∑ i : Fin n, ∑ j : Fin n, ‖antiCoeff a k i j‖)
      = ∑ k : box n N, ∑ q : Fin n × Fin n, ‖antiCoeff a k q.1 q.2‖ from
        Finset.sum_congr rfl (fun k _ =>
          (Fintype.sum_prod_type (f := fun q : Fin n × Fin n => ‖antiCoeff a k q.1 q.2‖)).symm)]
  exact (Fintype.sum_prod_type
    (f := fun p : box n N × (Fin n × Fin n) => ‖antiCoeff a p.1 p.2.1 p.2.2‖)).symm

lemma antiEnergy_eq_sum_prod {n N : ℕ} (a : Coeff n N) :
    antiEnergy a = ∑ p : box n N × Fin n × Fin n, ‖antiCoeff a p.1 p.2.1 p.2.2‖ ^ 2 := by
  rw [antiEnergy]
  rw [show (∑ k : box n N, ∑ i : Fin n, ∑ j : Fin n, ‖antiCoeff a k i j‖ ^ 2)
      = ∑ k : box n N, ∑ q : Fin n × Fin n, ‖antiCoeff a k q.1 q.2‖ ^ 2 from
        Finset.sum_congr rfl (fun k _ =>
          (Fintype.sum_prod_type (f := fun q : Fin n × Fin n => ‖antiCoeff a k q.1 q.2‖ ^ 2)).symm)]
  exact (Fintype.sum_prod_type
    (f := fun p : box n N × (Fin n × Fin n) => ‖antiCoeff a p.1 p.2.1 p.2.2‖ ^ 2)).symm

/-- Cauchy–Schwarz for the antisymmetric sums: the `ℓ¹` size is controlled by the `ℓ²` energy. -/
lemma antiSum_sq_le {n N : ℕ} (a : Coeff n N) :
    antiSum a ^ 2 ≤ ((Fintype.card (box n N) * n * n : ℕ) : ℝ) * antiEnergy a := by
  rw [antiSum_eq_sum_prod, antiEnergy_eq_sum_prod]
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun p : box n N × Fin n × Fin n => ‖antiCoeff a p.1 p.2.1 p.2.2‖)
  have hcard : ((Finset.univ : Finset (box n N × Fin n × Fin n)).card : ℝ)
      = ((Fintype.card (box n N) * n * n : ℕ) : ℝ) := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_coe]
    push_cast
    ring
  rwa [hcard] at h

/-! ## Bounds for the explicit jet -/

lemma box_abs_le {n N : ℕ} (m : box n N) (c : Fin n) : |(m.1 c : ℤ)| ≤ (N : ℤ) := by
  have hm : m.1 ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(N : ℤ)) N) := m.2
  have h := (Fintype.mem_piFinset.mp hm) c
  rw [Finset.mem_Icc] at h
  exact abs_le.mpr ⟨h.1, h.2⟩

lemma norm_dExp_le {n N : ℕ} (m : box n N) (c : Fin n) (x : Fin n → ℝ) :
    ‖dExp m.1 c x‖ ≤ 2 * Real.pi * (N : ℝ) := by
  have hmc : |(((m.1 c : ℤ)) : ℝ)| ≤ (N : ℝ) := by
    have := box_abs_le m c
    exact_mod_cast this
  have hnorm : ‖2 * Real.pi * Complex.I * ((m.1 c : ℤ) : ℂ)‖
      = 2 * Real.pi * |((m.1 c : ℤ) : ℝ)| := by
    rw [show 2 * Real.pi * Complex.I * ((m.1 c : ℤ) : ℂ)
        = (((2 * Real.pi * ((m.1 c : ℤ) : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [norm_mul, Complex.norm_I, mul_one, norm_ofReal_C]
    rw [abs_mul, abs_mul, abs_of_nonneg Real.pi_pos.le,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc ‖dExp m.1 c x‖
      = ‖(2 * Real.pi * Complex.I * ((m.1 c : ℤ) : ℂ)) * fourierExp m.1 x‖ := rfl
    _ = ‖2 * Real.pi * Complex.I * ((m.1 c : ℤ) : ℂ)‖ * ‖fourierExp m.1 x‖ := norm_mul _ _
    _ = 2 * Real.pi * |((m.1 c : ℤ) : ℝ)| := by rw [hnorm, tpd_norm_fourierExp, mul_one]
    _ ≤ 2 * Real.pi * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hmc (by positivity)

lemma norm_d2Exp_le {n N : ℕ} (m : box n N) (d c : Fin n) (x : Fin n → ℝ) :
    ‖d2Exp m.1 d c x‖ ≤ (2 * Real.pi * (N : ℝ)) ^ 2 := by
  have hnorm : ‖2 * Real.pi * Complex.I * ((m.1 d : ℤ) : ℂ)‖
      = 2 * Real.pi * |((m.1 d : ℤ) : ℝ)| := by
    rw [show 2 * Real.pi * Complex.I * ((m.1 d : ℤ) : ℂ)
        = (((2 * Real.pi * ((m.1 d : ℤ) : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [norm_mul, Complex.norm_I, mul_one, norm_ofReal_C]
    rw [abs_mul, abs_mul, abs_of_nonneg Real.pi_pos.le,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hmd : |(((m.1 d : ℤ)) : ℝ)| ≤ (N : ℝ) := by
    have := box_abs_le m d
    exact_mod_cast this
  have h1 : ‖d2Exp m.1 d c x‖
      = ‖2 * Real.pi * Complex.I * ((m.1 d : ℤ) : ℂ)‖ * ‖dExp m.1 c x‖ := by
    rw [show d2Exp m.1 d c x = (2 * Real.pi * Complex.I * ((m.1 d : ℤ) : ℂ)) * dExp m.1 c x
      from rfl, norm_mul]
  have hQ : 0 ≤ 2 * Real.pi * (N : ℝ) := by positivity
  have hfac : ‖2 * Real.pi * Complex.I * ((m.1 d : ℤ) : ℂ)‖ ≤ 2 * Real.pi * (N : ℝ) := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hmd (by positivity)
  calc ‖d2Exp m.1 d c x‖
      = ‖2 * Real.pi * Complex.I * ((m.1 d : ℤ) : ℂ)‖ * ‖dExp m.1 c x‖ := h1
    _ ≤ (2 * Real.pi * (N : ℝ)) * (2 * Real.pi * (N : ℝ)) :=
        mul_le_mul hfac (norm_dExp_le m c x) (norm_nonneg _) hQ
    _ = (2 * Real.pi * (N : ℝ)) ^ 2 := by ring

lemma valExp_norm_le {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) (i j : Fin n) :
    ‖valExp a x i j‖ ≤ fullSum a := by
  calc ‖valExp a x i j‖ = ‖∑ m : box n N, a m i j * fourierExp m.1 x‖ := rfl
    _ ≤ ∑ m : box n N, ‖a m i j * fourierExp m.1 x‖ := norm_sum_le _ _
    _ = ∑ m : box n N, ‖a m i j‖ := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [norm_mul, tpd_norm_fourierExp, mul_one]
    _ ≤ ∑ m : box n N, ∑ i' : Fin n, ∑ j' : Fin n, ‖a m i' j'‖ := by
        refine Finset.sum_le_sum fun m _ => ?_
        exact (single_le_sum_univ (f := fun j' : Fin n => ‖a m i j'‖)
            (fun j' => norm_nonneg _) j).trans
          (single_le_sum_univ (f := fun i' : Fin n => ∑ j' : Fin n, ‖a m i' j'‖)
            (fun i' => Finset.sum_nonneg fun j' _ => norm_nonneg _) i)
    _ = fullSum a := rfl

lemma linExp_norm_le {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) (c : Fin n) (i j : Fin n) :
    ‖linExp a x c i j‖ ≤ (2 * Real.pi * (N : ℝ)) * fullSum a := by
  have hQ : 0 ≤ 2 * Real.pi * (N : ℝ) := by positivity
  calc ‖linExp a x c i j‖ = ‖∑ m : box n N, a m i j * dExp m.1 c x‖ := rfl
    _ ≤ ∑ m : box n N, ‖a m i j * dExp m.1 c x‖ := norm_sum_le _ _
    _ ≤ ∑ m : box n N, ‖a m i j‖ * (2 * Real.pi * (N : ℝ)) := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_dExp_le m c x) (norm_nonneg _)
    _ = (2 * Real.pi * (N : ℝ)) * ∑ m : box n N, ‖a m i j‖ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ (2 * Real.pi * (N : ℝ)) * ∑ m : box n N, ∑ i' : Fin n, ∑ j' : Fin n, ‖a m i' j'‖ := by
        refine mul_le_mul_of_nonneg_left ?_ hQ
        refine Finset.sum_le_sum fun m _ => ?_
        exact (single_le_sum_univ (f := fun j' : Fin n => ‖a m i j'‖)
            (fun j' => norm_nonneg _) j).trans
          (single_le_sum_univ (f := fun i' : Fin n => ∑ j' : Fin n, ‖a m i' j'‖)
            (fun i' => Finset.sum_nonneg fun j' _ => norm_nonneg _) i)
    _ = (2 * Real.pi * (N : ℝ)) * fullSum a := rfl

lemma secExp_norm_le {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) (c d : Fin n) (i j : Fin n) :
    ‖secExp a x c d i j‖ ≤ (2 * Real.pi * (N : ℝ)) ^ 2 * fullSum a := by
  have hQ : 0 ≤ (2 * Real.pi * (N : ℝ)) ^ 2 := by positivity
  calc ‖secExp a x c d i j‖ = ‖∑ m : box n N, a m i j * d2Exp m.1 d c x‖ := rfl
    _ ≤ ∑ m : box n N, ‖a m i j * d2Exp m.1 d c x‖ := norm_sum_le _ _
    _ ≤ ∑ m : box n N, ‖a m i j‖ * (2 * Real.pi * (N : ℝ)) ^ 2 := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_d2Exp_le m d c x) (norm_nonneg _)
    _ = (2 * Real.pi * (N : ℝ)) ^ 2 * ∑ m : box n N, ‖a m i j‖ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ (2 * Real.pi * (N : ℝ)) ^ 2 * ∑ m : box n N, ∑ i' : Fin n, ∑ j' : Fin n, ‖a m i' j'‖ := by
        refine mul_le_mul_of_nonneg_left ?_ hQ
        refine Finset.sum_le_sum fun m _ => ?_
        exact (single_le_sum_univ (f := fun j' : Fin n => ‖a m i j'‖)
            (fun j' => norm_nonneg _) j).trans
          (single_le_sum_univ (f := fun i' : Fin n => ∑ j' : Fin n, ‖a m i' j'‖)
            (fun i' => Finset.sum_nonneg fun j' _ => norm_nonneg _) i)
    _ = (2 * Real.pi * (N : ℝ)) ^ 2 * fullSum a := rfl

lemma valExp_sub_swap_le' {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) (i j : Fin n) :
    ‖valExp a x i j - valExp a x j i‖ ≤ ∑ m : box n N, ‖a m i j - a m j i‖ := by
  have hval : valExp a x i j - valExp a x j i
      = ∑ m : box n N, (a m i j - a m j i) * fourierExp m.1 x := by
    rw [show valExp a x i j = ∑ m : box n N, a m i j * fourierExp m.1 x from rfl,
      show valExp a x j i = ∑ m : box n N, a m j i * fourierExp m.1 x from rfl,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hval]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, tpd_norm_fourierExp, mul_one]

lemma linExp_sub_swap_le' {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) (c : Fin n) (i j : Fin n) :
    ‖linExp a x c i j - linExp a x c j i‖ ≤
      (2 * Real.pi * (N : ℝ)) * (∑ m : box n N, ‖a m i j - a m j i‖) := by
  have hval : linExp a x c i j - linExp a x c j i
      = ∑ m : box n N, (a m i j - a m j i) * dExp m.1 c x := by
    rw [show linExp a x c i j = ∑ m : box n N, a m i j * dExp m.1 c x from rfl,
      show linExp a x c j i = ∑ m : box n N, a m j i * dExp m.1 c x from rfl,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hval]
  calc ‖∑ m : box n N, (a m i j - a m j i) * dExp m.1 c x‖
      ≤ ∑ m : box n N, ‖a m i j - a m j i‖ * (2 * Real.pi * (N : ℝ)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_dExp_le m c x) (norm_nonneg _)
    _ = (2 * Real.pi * (N : ℝ)) * ∑ m : box n N, ‖a m i j - a m j i‖ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring

lemma secExp_sub_swap_le' {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) (c d : Fin n) (i j : Fin n) :
    ‖secExp a x c d i j - secExp a x c d j i‖ ≤
      (2 * Real.pi * (N : ℝ)) ^ 2 * (∑ m : box n N, ‖a m i j - a m j i‖) := by
  have hval : secExp a x c d i j - secExp a x c d j i
      = ∑ m : box n N, (a m i j - a m j i) * d2Exp m.1 d c x := by
    rw [show secExp a x c d i j = ∑ m : box n N, a m i j * d2Exp m.1 d c x from rfl,
      show secExp a x c d j i = ∑ m : box n N, a m j i * d2Exp m.1 d c x from rfl,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hval]
  calc ‖∑ m : box n N, (a m i j - a m j i) * d2Exp m.1 d c x‖
      ≤ ∑ m : box n N, ‖a m i j - a m j i‖ * (2 * Real.pi * (N : ℝ)) ^ 2 := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_d2Exp_le m d c x) (norm_nonneg _)
    _ = (2 * Real.pi * (N : ℝ)) ^ 2 * ∑ m : box n N, ‖a m i j - a m j i‖ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring

/-- The inner sums are bounded by `antiSum`. -/
lemma box_sum_anti_le {n N : ℕ} (a : Coeff n N) (i j : Fin n) :
    (∑ m : box n N, ‖a m i j - a m j i‖) ≤ antiSum a := by
  rw [antiSum]
  refine Finset.sum_le_sum fun m _ => ?_
  exact (single_le_sum_univ (f := fun j' : Fin n => ‖a m i j' - a m j' i‖)
      (fun j' => norm_nonneg _) j).trans
    (single_le_sum_univ (f := fun i' : Fin n => ∑ j' : Fin n, ‖a m i' j' - a m j' i'‖)
      (fun i' => Finset.sum_nonneg fun j' _ => norm_nonneg _) i)

lemma valExp_sub_swap_le {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) (i j : Fin n) :
    ‖valExp a x i j - valExp a x j i‖ ≤ antiSum a :=
  (valExp_sub_swap_le' a x i j).trans (box_sum_anti_le a i j)

lemma linExp_sub_swap_le {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) (c : Fin n) (i j : Fin n) :
    ‖linExp a x c i j - linExp a x c j i‖ ≤ (2 * Real.pi * (N : ℝ)) * antiSum a := by
  refine (linExp_sub_swap_le' a x c i j).trans ?_
  exact mul_le_mul_of_nonneg_left (box_sum_anti_le a i j) (by positivity)

lemma secExp_sub_swap_le {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) (c d : Fin n) (i j : Fin n) :
    ‖secExp a x c d i j - secExp a x c d j i‖ ≤ (2 * Real.pi * (N : ℝ)) ^ 2 * antiSum a := by
  refine (secExp_sub_swap_le' a x c d i j).trans ?_
  exact mul_le_mul_of_nonneg_left (box_sum_anti_le a i j) (by positivity)

/-! ## Symmetrisation of a complex matrix -/

/-- The symmetrisation `(A + Aᵀ)/2` of a complex matrix. -/
def symmMat {n : ℕ} (A : MatC n) : MatC n := fun i j => (A i j + A j i) / 2

@[simp] lemma symmMat_apply {n : ℕ} (A : MatC n) (i j : Fin n) :
    symmMat A i j = (A i j + A j i) / 2 := rfl

lemma symmMat_symm {n : ℕ} (A : MatC n) : ∀ i j, symmMat A i j = symmMat A j i := by
  intro i j
  simp only [symmMat_apply]
  ring

lemma reMat_symmMat {n : ℕ} (A : MatC n) (i j : Fin n) :
    reMat (symmMat A) i j = (reMat A i j + reMat A j i) / 2 := by
  simp only [symmMat_apply, reMat_apply, Complex.div_ofNat_re, Complex.add_re]

/-- The quadratic form of the symmetrised matrix. -/
lemma sum_quadForm_symm {n : ℕ} (S : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    (∑ i, ∑ j, ((S i j + S j i) / 2) * ξ i * ξ j)
      = (∑ i, ∑ j, S i j * ξ i * ξ j) := by
  have hswap : (∑ i, ∑ j, S j i * ξ i * ξ j) = ∑ i, ∑ j, S i j * ξ i * ξ j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hpt1 : ∀ i j : Fin n, ((S i j + S j i) / 2) * ξ i * ξ j
      = (1 / 2 : ℝ) * ((S i j + S j i) * ξ i * ξ j) := fun i j => by ring
  have hpull : (∑ i, ∑ j, ((S i j + S j i) / 2) * ξ i * ξ j)
      = (1 / 2 : ℝ) * (∑ i, ∑ j, (S i j + S j i) * ξ i * ξ j) := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt1 i j))]
    exact sum_sum_const_mul' (1 / 2) _
  have hpt2 : ∀ i j : Fin n, (S i j + S j i) * ξ i * ξ j
      = S i j * ξ i * ξ j + S j i * ξ i * ξ j := fun i j => by ring
  have hdist : (∑ i, ∑ j, (S i j + S j i) * ξ i * ξ j)
      = (∑ i, ∑ j, S i j * ξ i * ξ j) + (∑ i, ∑ j, S j i * ξ i * ξ j) := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt2 i j))]
    have hinner : ∀ i : Fin n, (∑ j, (S i j * ξ i * ξ j + S j i * ξ i * ξ j))
        = (∑ j, S i j * ξ i * ξ j) + (∑ j, S j i * ξ i * ξ j) :=
      fun i => Finset.sum_add_distrib
    rw [Finset.sum_congr rfl (fun i _ => hinner i)]
    exact Finset.sum_add_distrib
  rw [hpull, hdist, hswap]
  ring

/-- The quadratic form only sees the symmetric part: it is unchanged by symmetrisation. -/
lemma sum_reMat_symmMat {n : ℕ} (A : MatC n) (ξ : Fin n → ℝ) :
    (∑ i, ∑ j, reMat (symmMat A) i j * ξ i * ξ j)
      = (∑ i, ∑ j, reMat A i j * ξ i * ξ j) := by
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
    rw [reMat_symmMat]))]
  exact sum_quadForm_symm (reMat A) ξ

/-- The sum of the entry norms of `A - symmMat A` is controlled by the antisymmetric part. -/
lemma sum_norm_sub_symmMat_le {n : ℕ} (A : MatC n) :
    (∑ i, ∑ j, ‖(A - symmMat A) i j‖) ≤ ∑ i, ∑ j, ‖A i j - A j i‖ := by
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have heq : (A - symmMat A) i j = (A i j - A j i) / 2 := by
    simp only [Pi.sub_apply, symmMat_apply]
    ring
  rw [heq, norm_div]
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [h2]
  linarith [norm_nonneg (A i j - A j i)]

lemma norm_sub_symmMat_le {n : ℕ} (A : MatC n) :
    ‖A - symmMat A‖ ≤ ∑ i, ∑ j, ‖A i j - A j i‖ :=
  (norm_le_sum_norm_matC _).trans (sum_norm_sub_symmMat_le A)

lemma norm_sub_symmMat_function_le {n : ℕ} (L : Fin n → MatC n) :
    ‖L - (fun c => symmMat (L c))‖ ≤ ∑ c, ∑ i, ∑ j, ‖L c i j - L c j i‖ :=
  (norm_le_sum_norm_pi_matC _).trans (Finset.sum_le_sum fun c _ =>
    sum_norm_sub_symmMat_le (L c))

/-! ## The pointwise bound on the antisymmetrised nonlinearity -/

/-- The `i j`-entry of `Φ (·, jetExp a ·)` is continuous on the closed cube, as long as the
metric matrix is nondegenerate there. -/
lemma continuousOn_phi_jetExp_entry {n N : ℕ}
    (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ
      (Set.univ ×ˢ {w : Jet n | (reMat w.1).det ≠ 0}))
    (a : Coeff n N)
    (hdet : ∀ x ∈ closedCube n, (reMat (valExp a x)).det ≠ 0)
    (i j : Fin n) :
    ContinuousOn (fun x : Fin n → ℝ => Φ (x, jetExp a x) i j) (closedCube n) := by
  have hjet : Continuous (fun x : Fin n → ℝ => jetExp a x) :=
    (Work.Diff.STE.Flat.Galerkin.contDiff_jetExp_fixed a).continuous
  have hpair : Continuous (fun x : Fin n → ℝ => (x, jetExp a x)) :=
    Continuous.prodMk continuous_id hjet
  have hmaps : Set.MapsTo (fun x : Fin n → ℝ => (x, jetExp a x)) (closedCube n)
      (Set.univ ×ˢ {w : Jet n | (reMat w.1).det ≠ 0}) := fun x hx => ⟨trivial, hdet x hx⟩
  have hcomp : ContinuousOn (fun x : Fin n → ℝ => Φ (x, jetExp a x)) (closedCube n) := by
    have h := hΦ.continuousOn.comp hpair.continuousOn hmaps
    simpa [Function.comp_def] using h
  have hproj : Continuous fun M : MatC n => M i j :=
    (continuous_apply j).comp (continuous_apply i)
  exact hproj.comp_continuousOn hcomp

/-- **The pointwise bound on the antisymmetrised DeTurck nonlinearity.**

`Φ` has the DeTurck shape `Φ (A,L,B) = secOpFlat A B + N (x,A,L)` near nondegenerate `A`, and is
symmetric on symmetric jets.  Then the antisymmetrisation of `Φ` at the jet of the explicit
trigonometric polynomial `a` is controlled by the antisymmetric part of the coefficients. -/
theorem antiPhi_bound {n N : ℕ} (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (hsym : ∀ (x : Fin n → ℝ) (A : MatC n) (L : Fin n → MatC n)
        (B : Fin n → Fin n → MatC n),
      (∀ i j, A i j = A j i) → (∀ c i j, L c i j = L c j i) →
      (∀ c d i j, B c d i j = B c d j i) → (∀ c d, B c d = B d c) →
      ∀ i j, Φ (x, (A, L, B)) i j = Φ (x, (A, L, B)) j i)
    (Nfun : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) → MatC n)
    (hNdec : ∀ (x : Fin n → ℝ) (A : MatC n) (L : Fin n → MatC n)
        (B : Fin n → Fin n → MatC n),
      (reMat A).det ≠ 0 → Φ (x, (A, L, B)) = secOpFlat A B + Nfun (x, (A, L)))
    {Cn lam M : ℝ} (hlam : 0 < lam) (hMnn : 0 ≤ M) (hMlam : lam⁻¹ ≤ M) (hCn : 0 ≤ Cn)
    (hC : ∀ (x : Fin n → ℝ), (∀ i, x i ∈ Set.Icc (0:ℝ) 1) → ∀ (J₁ J₂ : Jet n),
      (∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, reMat J₁.1 i j * ξ i * ξ j) →
      (∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, reMat J₂.1 i j * ξ i * ξ j) →
      (∀ i j, ‖J₁.1 i j‖ ≤ M) → (∀ i j, ‖J₂.1 i j‖ ≤ M) →
      (∀ i j, ‖((reMat J₁.1)⁻¹) i j‖ ≤ M) → (∀ i j, ‖((reMat J₂.1)⁻¹) i j‖ ≤ M) →
      (∀ c i j, ‖J₁.2.1 c i j‖ ≤ M) → (∀ c i j, ‖J₂.2.1 c i j‖ ≤ M) →
      (∀ c d i j, ‖J₁.2.2 c d i j‖ ≤ M) → (∀ c d i j, ‖J₂.2.2 c d i j‖ ≤ M) →
      ‖Φ (x, J₁) - Φ (x, J₂) - secOpFlat J₁.1 (J₁.2.2 - J₂.2.2)‖
        ≤ Cn * (‖J₁.1 - J₂.1‖ + ‖J₁.2.1 - J₂.2.1‖))
    (a : Coeff n N) (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0:ℝ) 1)
    (hell : ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤
      ∑ i, ∑ j, reMat (valExp a x) i j * ξ i * ξ j)
    (hAb : ∀ i j, ‖valExp a x i j‖ ≤ M) (hLb : ∀ c i j, ‖linExp a x c i j‖ ≤ M)
    (hBb : ∀ c d i j, ‖secExp a x c d i j‖ ≤ M) (i j : Fin n) :
    ‖Φ (x, jetExp a x) i j - Φ (x, jetExp a x) j i‖
      ≤ ((n : ℝ) ^ 2 * M * (2 * Real.pi * (N : ℝ)) ^ 2
          + 2 * Cn * ((n : ℝ) ^ 2 * (1 + (n : ℝ) * (2 * Real.pi * (N : ℝ))))) * antiSum a := by
  set A : MatC n := valExp a x with hAset
  set L : Fin n → MatC n := linExp a x with hLset
  set B : Fin n → Fin n → MatC n := secExp a x with hBset
  have hjet : jetExp a x = (A, L, B) := rfl
  have hdet : (reMat A).det ≠ 0 := det_ne_zero_of_quadratic hlam hell
  -- the symmetrised value / first jet
  set As : MatC n := symmMat A with hAsset
  set Ls : Fin n → MatC n := fun c => symmMat (L c) with hLsset
  have hAs_sym : ∀ i j, As i j = As j i := by
    intro i j; rw [hAsset]; exact symmMat_symm A i j
  have hLs_sym : ∀ c i j, Ls c i j = Ls c j i := by
    intro c i j; rw [hLsset]; exact symmMat_symm (L c) i j
  have hellAs : ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤
      ∑ i, ∑ j, reMat As i j * ξ i * ξ j := by
    intro ξ
    rw [hAsset, sum_reMat_symmMat]
    exact hell ξ
  have hAs_det : (reMat As).det ≠ 0 := det_ne_zero_of_quadratic hlam hellAs
  -- `secOpFlat` vanishes at the zero second jet
  have hseczero : ∀ C : MatC n, secOpFlat C (0 : Fin n → Fin n → MatC n) = 0 := by
    intro C
    funext i' j'
    simp only [secOpFlat, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  -- the lower order term is symmetric at the symmetrised pair
  have hNsym : Nfun (x, (As, Ls)) i j = Nfun (x, (As, Ls)) j i := by
    have h0ij : ∀ c d i' j', (0 : Fin n → Fin n → MatC n) c d i' j'
        = (0 : Fin n → Fin n → MatC n) c d j' i' := fun c d i' j' => rfl
    have h0cd : ∀ c d, (0 : Fin n → Fin n → MatC n) c d
        = (0 : Fin n → Fin n → MatC n) d c := fun c d => rfl
    have h := hsym x As Ls 0 hAs_sym hLs_sym h0ij h0cd i j
    have h1 : Φ (x, (As, Ls, 0))
        = secOpFlat As (0 : Fin n → Fin n → MatC n) + Nfun (x, (As, Ls)) :=
      hNdec x As Ls 0 hAs_det
    rw [h1, hseczero As, zero_add] at h
    exact h
  -- the second-jet (principal) part
  have hT1 : ‖secOpFlat A B i j - secOpFlat A B j i‖
      ≤ (n : ℝ) ^ 2 * M * (2 * Real.pi * (N : ℝ)) ^ 2 * antiSum a := by
    have hrepr : secOpFlat A B i j - secOpFlat A B j i
        = ∑ c, ∑ d, (((reMat A)⁻¹) c d : ℂ) * (B c d i j - B c d j i) := by
      simp only [secOpFlat, Pi.sub_apply]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun d _ => by ring
    have hIA : ∀ c d, ‖(((reMat A)⁻¹) c d : ℂ)‖ ≤ M := by
      intro c d
      rw [norm_ofReal_C]
      exact (Work.Diff.STE.flat.galerkin.inv_entry_le_of_quadForm (reMat A) hlam hell c d).trans
        hMlam
    calc ‖secOpFlat A B i j - secOpFlat A B j i‖
        = ‖∑ c, ∑ d, (((reMat A)⁻¹) c d : ℂ) * (B c d i j - B c d j i)‖ := by rw [hrepr]
      _ ≤ ∑ c, ∑ d, ‖(((reMat A)⁻¹) c d : ℂ) * (B c d i j - B c d j i)‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
          exact norm_sum_le _ _
      _ ≤ ∑ c, ∑ d, M * ((2 * Real.pi * (N : ℝ)) ^ 2 * antiSum a) := by
          refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => ?_
          rw [norm_mul]
          exact mul_le_mul (hIA c d) (by rw [hBset]; exact secExp_sub_swap_le a x c d i j)
            (norm_nonneg _) hMnn
      _ = (n : ℝ) ^ 2 * M * (2 * Real.pi * (N : ℝ)) ^ 2 * antiSum a := by
          rw [sum_sum_const]; ring
  -- the entries of the symmetrised pair are bounded
  have hAsb : ∀ i' j', ‖As i' j'‖ ≤ M := by
    intro i' j'
    rw [hAsset, symmMat_apply, norm_div]
    have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    rw [h2]
    calc ‖A i' j' + A j' i'‖ / 2 ≤ (‖A i' j'‖ + ‖A j' i'‖) / 2 :=
          div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
      _ ≤ (M + M) / 2 :=
          div_le_div_of_nonneg_right (add_le_add (hAb i' j') (hAb j' i')) (by norm_num)
      _ = M := by ring
  have hLsb : ∀ c i' j', ‖Ls c i' j'‖ ≤ M := by
    intro c i' j'
    show ‖symmMat (L c) i' j'‖ ≤ M
    rw [symmMat_apply, norm_div]
    have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    rw [h2]
    calc ‖L c i' j' + L c j' i'‖ / 2 ≤ (‖L c i' j'‖ + ‖L c j' i'‖) / 2 :=
          div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
      _ ≤ (M + M) / 2 :=
          div_le_div_of_nonneg_right (add_le_add (hLb c i' j') (hLb c j' i')) (by norm_num)
      _ = M := by ring
  have hIAs : ∀ i' j', ‖((reMat As)⁻¹) i' j'‖ ≤ M := by
    intro i' j'
    exact (Work.Diff.STE.flat.galerkin.inv_entry_le_of_quadForm (reMat As) hlam hellAs i' j').trans
      hMlam
  have h0b : ∀ c d i' j', ‖(0 : Fin n → Fin n → MatC n) c d i' j'‖ ≤ M := by
    intro c d i' j'; simpa using hMnn
  have hnd : ‖Nfun (x, (A, L)) - Nfun (x, (As, Ls))‖
      ≤ Cn * (‖A - As‖ + ‖L - Ls‖) := by
    have h := hC x hx (A, L, 0) (As, Ls, 0) hell hellAs hAb hAsb
      (fun i' j' =>
        (Work.Diff.STE.flat.galerkin.inv_entry_le_of_quadForm (reMat A) hlam hell i' j').trans
          hMlam)
      hIAs hLb hLsb h0b h0b
    have e1 : Φ (x, (A, L, 0)) = Nfun (x, (A, L)) := by
      rw [hNdec x A L 0 hdet, hseczero A, zero_add]
    have e2 : Φ (x, (As, Ls, 0)) = Nfun (x, (As, Ls)) := by
      rw [hNdec x As Ls 0 hAs_det, hseczero As, zero_add]
    rw [e1, e2] at h
    rw [sub_self, hseczero A, sub_zero] at h
    exact h
  have hdistA : ‖A - As‖ ≤ (n : ℝ) ^ 2 * antiSum a := by
    have h1 : ‖A - As‖ ≤ ∑ i', ∑ j', ‖A i' j' - A j' i'‖ := by
      rw [hAsset]; exact norm_sub_symmMat_le A
    have h2 : (∑ i', ∑ j', ‖A i' j' - A j' i'‖) ≤
        ((Fintype.card (Fin n) * Fintype.card (Fin n) : ℕ) : ℝ) * antiSum a := by
      refine sum2_le_card_mul fun i' j' => ?_
      rw [hAset]
      exact valExp_sub_swap_le a x i' j'
    have hcard : ((Fintype.card (Fin n) * Fintype.card (Fin n) : ℕ) : ℝ) = (n : ℝ) ^ 2 := by
      simp only [Fintype.card_fin, Nat.cast_mul]
      ring
    rw [hcard] at h2
    exact h1.trans h2
  have hdistL : ‖L - Ls‖ ≤ (n : ℝ) ^ 3 * (2 * Real.pi * (N : ℝ)) * antiSum a := by
    have h1 : ‖L - Ls‖ ≤ ∑ c, ∑ i', ∑ j', ‖L c i' j' - L c j' i'‖ := by
      rw [hLsset]; exact norm_sub_symmMat_function_le L
    have h2 : (∑ c, ∑ i', ∑ j', ‖L c i' j' - L c j' i'‖) ≤
        ((Fintype.card (Fin n) * Fintype.card (Fin n) * Fintype.card (Fin n) : ℕ) : ℝ)
          * ((2 * Real.pi * (N : ℝ)) * antiSum a) := by
      refine sum3_le_card_mul fun c i' j' => ?_
      rw [hLset]
      exact linExp_sub_swap_le a x c i' j'
    have hcard : ((Fintype.card (Fin n) * Fintype.card (Fin n) * Fintype.card (Fin n) : ℕ) : ℝ)
        = (n : ℝ) ^ 3 := by
      simp [Fintype.card_fin]
      ring
    rw [hcard] at h2
    exact h1.trans (h2.trans (le_of_eq (by ring)))
  have hT2 : ‖Nfun (x, (A, L)) i j - Nfun (x, (A, L)) j i‖
      ≤ 2 * Cn * ((n : ℝ) ^ 2 * (1 + (n : ℝ) * (2 * Real.pi * (N : ℝ)))) * antiSum a := by
    have heq : Nfun (x, (A, L)) i j - Nfun (x, (A, L)) j i
        = (Nfun (x, (A, L)) - Nfun (x, (As, Ls))) i j
          - (Nfun (x, (A, L)) - Nfun (x, (As, Ls))) j i := by
      simp only [Pi.sub_apply]
      rw [hNsym]
      ring
    have h12 : ‖(Nfun (x, (A, L)) - Nfun (x, (As, Ls))) i j
        - (Nfun (x, (A, L)) - Nfun (x, (As, Ls))) j i‖
        ≤ 2 * (Cn * (‖A - As‖ + ‖L - Ls‖)) := by
      calc ‖(Nfun (x, (A, L)) - Nfun (x, (As, Ls))) i j
            - (Nfun (x, (A, L)) - Nfun (x, (As, Ls))) j i‖
          ≤ ‖(Nfun (x, (A, L)) - Nfun (x, (As, Ls))) i j‖
            + ‖(Nfun (x, (A, L)) - Nfun (x, (As, Ls))) j i‖ := norm_sub_le _ _
        _ ≤ ‖Nfun (x, (A, L)) - Nfun (x, (As, Ls))‖
            + ‖Nfun (x, (A, L)) - Nfun (x, (As, Ls))‖ :=
            add_le_add (norm_entry_le_norm_matC _ i j) (norm_entry_le_norm_matC _ j i)
        _ ≤ Cn * (‖A - As‖ + ‖L - Ls‖) + Cn * (‖A - As‖ + ‖L - Ls‖) := by
            linarith [hnd]
        _ = 2 * (Cn * (‖A - As‖ + ‖L - Ls‖)) := by ring
    rw [heq]
    refine h12.trans ?_
    have hsum : ‖A - As‖ + ‖L - Ls‖ ≤
        (n : ℝ) ^ 2 * antiSum a
          + (n : ℝ) ^ 3 * (2 * Real.pi * (N : ℝ)) * antiSum a := add_le_add hdistA hdistL
    have hfac : (n : ℝ) ^ 2 * antiSum a
          + (n : ℝ) ^ 3 * (2 * Real.pi * (N : ℝ)) * antiSum a
        = (n : ℝ) ^ 2 * (1 + (n : ℝ) * (2 * Real.pi * (N : ℝ))) * antiSum a := by ring
    calc 2 * (Cn * (‖A - As‖ + ‖L - Ls‖))
        ≤ 2 * (Cn * ((n : ℝ) ^ 2 * (1 + (n : ℝ) * (2 * Real.pi * (N : ℝ))) * antiSum a)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCn) (by norm_num)
          rwa [hfac] at hsum
      _ = 2 * Cn * ((n : ℝ) ^ 2 * (1 + (n : ℝ) * (2 * Real.pi * (N : ℝ)))) * antiSum a := by ring
  -- combine
  have hdec : Φ (x, jetExp a x) = secOpFlat A B + Nfun (x, (A, L)) := by
    rw [hjet]
    exact hNdec x A L B hdet
  have hsplit : Φ (x, jetExp a x) i j - Φ (x, jetExp a x) j i
      = (secOpFlat A B i j - secOpFlat A B j i)
        + (Nfun (x, (A, L)) i j - Nfun (x, (A, L)) j i) := by
    rw [hdec]
    simp only [Pi.add_apply]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add hT1 hT2).trans (le_of_eq ?_)
  ring

theorem galerkin_symm_of_initial {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (hsym : ∀ (x : Fin n → ℝ) (A : Work.Diff.STE.Flat.MatC n)
        (L : Fin n → Work.Diff.STE.Flat.MatC n)
        (B : Fin n → Fin n → Work.Diff.STE.Flat.MatC n),
      (∀ i j, A i j = A j i) → (∀ c i j, L c i j = L c j i) →
      (∀ c d i j, B c d i j = B c d j i) → (∀ c d, B c d = B d c) →
      ∀ i j, Φ (x, (A, L, B)) i j = Φ (x, (A, L, B)) j i)
    (N : ℕ) (c₀ : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hc₀ : ∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c₀ k' = 0)
    (hsym₀ : ∀ (k' : Fin n → ℤ) (i j : Fin n), c₀ k' i j = c₀ k' j i)
    (T : ℝ) (hT : 0 < T) (lam : ℝ) (hlam : 0 < lam)
    (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hc0 : c 0 = c₀)
    (hode : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
      HasDerivAt (fun s => c s k' i j)
        (Work.Diff.STE.fourierCoeff (fun x =>
          Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) k') t)
    (hsupp : ∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0)
    (hell : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
        Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c t) x) i j * v i * v j) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : Fin n → ℝ) (i j : Fin n),
      Work.Diff.STE.Flat.seriesFunM (c t) x i j = Work.Diff.STE.Flat.seriesFunM (c t) x j i := by
  intro t₀ ht₀ x i₀ j₀
  have hshape' := hshape
  obtain ⟨hΦsm, Nfun, _hNsm, hNdec, _hNper⟩ := hshape
  -- the box-supported coefficient family of `c`
  let a : ℝ → Coeff n N := fun t => ofCoeff (c t) (hsupp t)
  have haCoeff : ∀ t, toCoeff (a t) = c t := fun t => toCoeff_ofCoeff (c t) (hsupp t)
  -- the Galerkin ODE in box-supported form
  have hode' : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ k : box n N, ∀ i j : Fin n,
      HasDerivAt (fun s : ℝ => a s k i j)
        (Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k i j) t := by
    intro t ht k i j
    have h := hode t ht k.1 k.2 i j
    have hrhs : Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k i j
        = fourierCoeff (fun x => Φ (x, jetM (seriesFunM (c t)) x) i j) k.1 := by
      simp only [Work.Diff.STE.Flat.Galerkin.rhs]
      rw [haCoeff t]
    have hfun : (fun s : ℝ => a s k i j) = fun s : ℝ => c s k.1 i j := rfl
    rw [hfun, hrhs]
    exact h
  have hrhsExp : ∀ t : ℝ, ∀ k : box n N, ∀ i j : Fin n,
      Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k i j
        = fourierCoeff (fun x => Φ (x, jetExp (a t) x) i j) k.1 := by
    intro t k i j
    rw [Work.Diff.STE.flat.rhs_eq_rhsExp]
    rfl
  -- the comparison time and the a priori bound for the jet
  set tstar : ℝ := (t₀ + T) / 2 with htstardef
  have htstarT : tstar < T := by rw [htstardef]; linarith [ht₀.2]
  have ht₀tstar : t₀ ∈ Set.Icc (0:ℝ) tstar :=
    ⟨ht₀.1, by rw [htstardef]; linarith [ht₀.2]⟩
  have hdiff : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ k ∈ box n N, ∀ i j : Fin n,
      DifferentiableAt ℝ (fun s : ℝ => c s k i j) t :=
    fun t ht k hk i j => (hode t ht k hk i j).differentiableAt
  obtain ⟨B, hB0, hB⟩ := Work.Diff.STE.flat.galerkin.coeff_box_sum_bound htstarT c hdiff
  set Q : ℝ := 2 * Real.pi * (N : ℝ) with hQdef
  have hQ0 : 0 ≤ Q := by rw [hQdef]; positivity
  set M : ℝ := max B (max (Q * B) (max (Q ^ 2 * B) (max lam⁻¹ 1))) with hMdef
  have hBle : B ≤ M := le_max_left _ _
  have hQBle : Q * B ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hQ2Ble : Q ^ 2 * B ≤ M :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hlamM : lam⁻¹ ≤ M :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  have h1M : 1 ≤ M :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hM0 : 0 ≤ M := le_trans hB0 hBle
  have hfull : ∀ t ∈ Set.Icc (0:ℝ) tstar, fullSum (a t) ≤ B := by
    intro t ht
    have h := hB t ht
    have hcongr : fullSum (a t) = ∑ k : box n N, ∑ i, ∑ j, ‖c t k.1 i j‖ := rfl
    rw [hcongr]
    exact h
  have hjetVal : ∀ t ∈ Set.Icc (0:ℝ) tstar, ∀ x : Fin n → ℝ, ∀ i j : Fin n,
      ‖valExp (a t) x i j‖ ≤ M :=
    fun t ht x i j => (valExp_norm_le (a t) x i j).trans ((hfull t ht).trans hBle)
  have hjetLin : ∀ t ∈ Set.Icc (0:ℝ) tstar, ∀ x : Fin n → ℝ, ∀ c i j : Fin n,
      ‖linExp (a t) x c i j‖ ≤ M :=
    fun t ht x c i j => (linExp_norm_le (a t) x c i j).trans
      ((mul_le_mul_of_nonneg_left (hfull t ht) hQ0).trans hQBle)
  have hjetSec : ∀ t ∈ Set.Icc (0:ℝ) tstar, ∀ x : Fin n → ℝ, ∀ c d i j : Fin n,
      ‖secExp (a t) x c d i j‖ ≤ M :=
    fun t ht x c d i j => (secExp_norm_le (a t) x c d i j).trans
      ((mul_le_mul_of_nonneg_left (hfull t ht) (by positivity)).trans hQ2Ble)
  -- the Lipschitz constant of the nonlinearity
  obtain ⟨Cn, hCn0, hCbound⟩ :=
    Work.Diff.STE.flat.galerkin.nDiff_bound_quadForm hn Φ hshape' lam hlam M hM0
  set K : ℝ := (n : ℝ) ^ 2 * M * (2 * Real.pi * (N : ℝ)) ^ 2
      + 2 * Cn * ((n : ℝ) ^ 2 * (1 + (n : ℝ) * (2 * Real.pi * (N : ℝ)))) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have h1 : 0 ≤ (n : ℝ) ^ 2 * M * (2 * Real.pi * (N : ℝ)) ^ 2 := by positivity
    have h2 : 0 ≤ 2 * Cn * ((n : ℝ) ^ 2 * (1 + (n : ℝ) * (2 * Real.pi * (N : ℝ)))) := by
      have : 0 ≤ (1 + (n : ℝ) * (2 * Real.pi * (N : ℝ))) := by positivity
      positivity
    linarith
  -- the pointwise bound on the antisymmetrised nonlinearity
  have hpoint : ∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ x ∈ unitCube (ι := Fin n),
      ∀ k : box n N, ∀ i j : Fin n,
      ‖Φ (x, jetExp (a t) x) i j - Φ (x, jetExp (a t) x) j i‖ ≤ K * antiSum (a t) := by
    intro t ht x hx k i j
    have htT : t ∈ Set.Ico (0:ℝ) T := ⟨ht.1, lt_of_lt_of_le ht.2 (le_of_lt htstarT)⟩
    have htIcc : t ∈ Set.Icc (0:ℝ) tstar := ⟨ht.1, le_of_lt ht.2⟩
    have hxIcc : ∀ i, x i ∈ Set.Icc (0:ℝ) 1 := fun i =>
      unitCube_subset_closedCube n hx i trivial
    refine antiPhi_bound Φ hsym Nfun hNdec hlam hM0 hlamM hCn0 hCbound (a t) x hxIcc ?_ ?_ ?_ ?_ i j
    · intro ξ
      have h := hell t htT x ξ
      rw [valExp_eq_seriesFunM (a t) x, haCoeff t]
      exact h
    · exact hjetVal t htIcc x
    · exact hjetLin t htIcc x
    · exact hjetSec t htIcc x
  -- transfer to the Fourier coefficients
  have hcoeff : ∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ k : box n N, ∀ i j : Fin n,
      ‖Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k i j
        - Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k j i‖ ≤ K * antiSum (a t) := by
    intro t ht k i j
    have htT : t ∈ Set.Ico (0:ℝ) T := ⟨ht.1, lt_of_lt_of_le ht.2 (le_of_lt htstarT)⟩
    have hdet : ∀ x ∈ closedCube n, (reMat (valExp (a t) x)).det ≠ 0 := by
      intro x _hx
      refine det_ne_zero_of_quadratic hlam ?_
      intro ξ
      have h := hell t htT x ξ
      rw [valExp_eq_seriesFunM (a t) x, haCoeff t]
      exact h
    rw [hrhsExp t k i j, hrhsExp t k j i]
    refine norm_fourierCoeff_sub_le (continuousOn_phi_jetExp_entry Φ hΦsm (a t) hdet i j)
      (continuousOn_phi_jetExp_entry Φ hΦsm (a t) hdet j i)
      (mul_nonneg hK0 (antiSum_nonneg _)) ?_ k.1
    intro x hx
    exact hpoint t ht x hx k i j
  -- the energy
  set Efun : ℝ → ℝ := fun t => antiEnergy (a t) with hEdef
  set Ed : ℝ → ℝ := fun t => ∑ k : box n N, ∑ i, ∑ j,
      2 * ((Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k i j
        - Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k j i)
        * star (a t k i j - a t k j i)).re with hEddef
  have hderivAt : ∀ t ∈ Set.Icc (0:ℝ) tstar, HasDerivAt Efun (Ed t) t := by
    intro t ht
    have htT : t ∈ Set.Ico (0:ℝ) T := ⟨ht.1, lt_of_le_of_lt ht.2 htstarT⟩
    rw [show Efun = fun s : ℝ => ∑ k : box n N, ∑ i : Fin n, ∑ j : Fin n,
        ‖a s k i j - a s k j i‖ ^ 2 from by
      funext s; simp only [hEdef, antiEnergy, antiCoeff_apply]]
    rw [show Ed t = ∑ k : box n N, ∑ i : Fin n, ∑ j : Fin n,
        2 * ((Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k i j
          - Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k j i)
          * star (a t k i j - a t k j i)).re from by
      simp only [hEddef]]
    have h1 : (∑ k : box n N, ∑ i : Fin n, ∑ j : Fin n,
        fun s : ℝ => ‖a s k i j - a s k j i‖ ^ 2)
        = fun s : ℝ => ∑ k : box n N, ∑ i : Fin n, ∑ j : Fin n,
          ‖a s k i j - a s k j i‖ ^ 2 := by
      funext s; simp only [Finset.sum_apply]
    rw [← h1]
    refine HasDerivAt.sum (u := Finset.univ) fun k _ => ?_
    refine HasDerivAt.sum (u := Finset.univ) fun i _ => ?_
    refine HasDerivAt.sum (u := Finset.univ) fun j _ => ?_
    exact hasDerivAt_normsq ((hode' t htT k i j).sub (hode' t htT k j i))
  have hcontE : ContinuousOn Efun (Set.Icc (0:ℝ) tstar) := fun t ht =>
    ((hderivAt t ht).continuousAt).continuousWithinAt
  have hderivE : ∀ t ∈ Set.Ioo (0:ℝ) tstar,
      HasDerivWithinAt Efun (Ed t) (Set.Ioo (0:ℝ) tstar) t := fun t ht =>
    (hderivAt t (show t ∈ Set.Icc (0:ℝ) tstar from ⟨le_of_lt ht.1, le_of_lt ht.2⟩)).hasDerivWithinAt
  have hineqE : ∀ t ∈ Set.Ioo (0:ℝ) tstar,
      Ed t ≤ (2 * K * ((Fintype.card (box n N) * n * n : ℕ) : ℝ)) * Efun t := by
    intro t ht
    have htIco : t ∈ Set.Ico (0:ℝ) tstar := ⟨le_of_lt ht.1, ht.2⟩
    have hterm : ∀ (k : box n N) (i j : Fin n),
        2 * ((Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k i j
          - Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k j i)
          * star (a t k i j - a t k j i)).re
        ≤ 2 * (K * antiSum (a t)) * ‖antiCoeff (a t) k i j‖ := by
      intro k i j
      have h1 : ((Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k i j
            - Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k j i)
            * star (a t k i j - a t k j i)).re
          ≤ ‖Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k i j
              - Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k j i‖
            * ‖a t k i j - a t k j i‖ := by
        calc _ ≤ ‖(Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k i j
                - Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k j i)
                * star (a t k i j - a t k j i)‖ := Complex.re_le_norm _
          _ = ‖Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k i j
                - Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k j i‖
              * ‖star (a t k i j - a t k j i)‖ := norm_mul _ _
          _ = ‖Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k i j
                - Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k j i‖
              * ‖a t k i j - a t k j i‖ := by rw [norm_star]
      calc 2 * ((Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k i j
            - Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k j i)
            * star (a t k i j - a t k j i)).re
          ≤ 2 * (‖Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k i j
                - Work.Diff.STE.Flat.Galerkin.rhs Φ (a t) k j i‖
              * ‖a t k i j - a t k j i‖) := by linarith
        _ ≤ 2 * ((K * antiSum (a t)) * ‖a t k i j - a t k j i‖) := by
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hcoeff t htIco k i j) (norm_nonneg _)) (by norm_num)
        _ = 2 * (K * antiSum (a t)) * ‖antiCoeff (a t) k i j‖ := by
            rw [antiCoeff_apply]; ring
    have hsum : Ed t ≤ ∑ k : box n N, ∑ i, ∑ j,
        2 * (K * antiSum (a t)) * ‖antiCoeff (a t) k i j‖ :=
      Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hterm k i j
    have hpull : (∑ k : box n N, ∑ i : Fin n, ∑ j : Fin n,
        2 * (K * antiSum (a t)) * ‖antiCoeff (a t) k i j‖)
        = 2 * (K * antiSum (a t)) * antiSum (a t) := by
      rw [antiSum]
      exact sum3_const_mul _ _
    calc Ed t ≤ ∑ k : box n N, ∑ i, ∑ j,
          2 * (K * antiSum (a t)) * ‖antiCoeff (a t) k i j‖ := hsum
      _ = 2 * (K * antiSum (a t)) * antiSum (a t) := hpull
      _ = 2 * K * (antiSum (a t)) ^ 2 := by ring
      _ ≤ 2 * K * (((Fintype.card (box n N) * n * n : ℕ) : ℝ) * Efun t) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simpa [hEdef] using antiSum_sq_le (a t)
      _ = (2 * K * ((Fintype.card (box n N) * n * n : ℕ) : ℝ)) * Efun t := by ring
  have hE0 : Efun 0 = 0 := by
    simp only [hEdef, antiEnergy, antiCoeff_apply]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun j _ => ?_
    have hsym0 : a 0 k i j = a 0 k j i := by
      have h1 : a 0 k i j = c 0 k.1 i j := rfl
      have h2 : a 0 k j i = c 0 k.1 j i := rfl
      rw [h1, h2, hc0]
      exact hsym₀ k.1 i j
    rw [hsym0]
    simp
  have hEnn : ∀ t ∈ Set.Icc (0:ℝ) tstar, 0 ≤ Efun t := fun t _ => antiEnergy_nonneg _
  have hEz := eq_zero_of_deriv_le hcontE hderivE hineqE hEnn hE0
  -- conclusion
  have hEzero : Efun t₀ = 0 := hEz t₀ ht₀tstar
  have hcoeff0 : (∑ k : box n N, ∑ i, ∑ j,
      ‖a t₀ k i j - a t₀ k j i‖ ^ 2) = 0 := by
    simpa [hEdef, antiEnergy, antiCoeff_apply] using hEzero
  have hallzero : ∀ k : box n N, ∀ i j : Fin n, a t₀ k i j = a t₀ k j i := by
    intro k i j
    have hle : ‖a t₀ k i j - a t₀ k j i‖ ^ 2 ≤ 0 := by
      have hA : ‖a t₀ k i j - a t₀ k j i‖ ^ 2
          ≤ ∑ i', ∑ j', ‖a t₀ k i' j' - a t₀ k j' i'‖ ^ 2 :=
        (single_le_sum_univ (f := fun j' : Fin n => ‖a t₀ k i j' - a t₀ k j' i‖ ^ 2)
          (fun j' => sq_nonneg _) j).trans
        (single_le_sum_univ
          (f := fun i' : Fin n => ∑ j' : Fin n, ‖a t₀ k i' j' - a t₀ k j' i'‖ ^ 2)
          (fun i' => Finset.sum_nonneg fun j' _ => sq_nonneg _) i)
      have hB : (∑ i', ∑ j', ‖a t₀ k i' j' - a t₀ k j' i'‖ ^ 2) ≤ 0 :=
        (single_le_sum_univ (f := fun k' : box n N =>
            ∑ i', ∑ j', ‖a t₀ k' i' j' - a t₀ k' j' i'‖ ^ 2)
          (fun k' => Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j' _ =>
            sq_nonneg _) k).trans (le_of_eq hcoeff0)
      exact hA.trans hB
    have hzero : ‖a t₀ k i j - a t₀ k j i‖ ^ 2 = 0 :=
      le_antisymm hle (sq_nonneg _)
    have hzero' : ‖a t₀ k i j - a t₀ k j i‖ = 0 := sq_eq_zero_iff.mp hzero
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero')
  have hcoeffeq : ∀ k : Fin n → ℤ, c t₀ k i₀ j₀ = c t₀ k j₀ i₀ := by
    intro k
    by_cases hk : k ∈ box n N
    · exact hallzero ⟨k, hk⟩ i₀ j₀
    · rw [hsupp t₀ k hk]
      simp
  have hfun : (fun k => c t₀ k i₀ j₀) = fun k => c t₀ k j₀ i₀ := funext hcoeffeq
  simp only [seriesFunM_apply]
  rw [hfun]

end

end Work.Diff.STE.flat
