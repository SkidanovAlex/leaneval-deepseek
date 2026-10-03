/-
# Auxiliary identities for the fibre form of the §6 model kernel (Area A7)

This module collects the two analytic/algebraic inputs of `Work.KMTAreas.A7.hiKmodN_fibre`:

* `tsum_cw_fourier_eq_integral_aux` — the master one-variable identity
  `∑_j cw m j · e(-jη) · cw f (a-j) = ∫_y f(y) e(-ay) · periodize m (y - η) dy`
  (Poisson summation on the circle plus one interchange of series and integral);
* `kernComp_arith_factor_aux` — the two-variable rearrangement of `kernComp` for arithmetic
  kernels into the diagonal "fibre" form used by the §6 model approximation.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.cw_tsum_fourier
import Submission.Work.KMTAreas.A7.ModelApproxHiDefs

set_option autoImplicit false
set_option maxHeartbeats 32000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- `fourier (T := 1) n` at a real point is the character `e(n·)`. -/
private lemma fourier_coe_eq_ee' (n : ℤ) (y : ℝ) :
    fourier (T := 1) n ((y : ℝ) : Circ) = Work.KMTAreas.A7.ee ((n : ℝ) * y) := by
  rw [fourier_coe_apply, Work.KMTAreas.A7.ee]
  congr 1
  push_cast
  ring

/-- `fourier (T := 1) (-n)` at a real point is the character `e(-n·)`. -/
private lemma fourier_coe_eq_ee_neg' (n : ℤ) (y : ℝ) :
    fourier (T := 1) (-n) ((y : ℝ) : Circ) = Work.KMTAreas.A7.ee (-(n : ℝ) * y) := by
  rw [fourier_coe_eq_ee']
  congr 1
  push_cast
  ring

/-- `fourier (T := 1) n` at `-x` is `fourier (T := 1) (-n)` at `x`. -/
private lemma fourier_neg_apply' (n : ℤ) (x : Circ) :
    fourier (T := 1) n (-x) = fourier (T := 1) (-n) x := by
  rw [fourier_apply, fourier_apply]
  congr 1
  rw [smul_neg, neg_zsmul]

/-- The character `fourier (T := 1) n` is additive in its argument. -/
lemma fourier_add_arg' (n : ℤ) (x y : Circ) :
    fourier (T := 1) n (x + y) = fourier (T := 1) n x * fourier (T := 1) n y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- The character `fourier (T := 1) n` has modulus one. -/
private lemma norm_fourier_eq_one (n : ℤ) (x : Circ) : ‖fourier (T := 1) n x‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- The character `fourier (T := 1) n` has modulus one at real points. -/
private lemma norm_fourier_coe_eq_one (n : ℤ) (y : ℝ) :
    ‖fourier (T := 1) n ((y : ℝ) : Circ)‖ = 1 :=
  norm_fourier_eq_one n _

/-- The character `y ↦ ee (c * y)` is continuous. -/
private lemma continuous_ee_const_mul' (c : ℝ) : Continuous (fun y : ℝ => Work.KMTAreas.A7.ee (c * y)) := by
  unfold Work.KMTAreas.A7.ee
  fun_prop

/-- The `cw`-coefficient as an integral against the characters `fourier (T := 1) (-n)`. -/
private lemma cw_eq_integral_fourier' {f : ℝ → ℂ} (k : ℤ) :
    Work.KMTAreas.A7.cw f k
      = ∫ y : ℝ, f y * fourier (T := 1) (-k) ((y : ℝ) : Circ) := by
  rw [Work.KMTAreas.A7.cw]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  change f y * Work.KMTAreas.A7.ee (-(k : ℝ) * y)
      = f y * fourier (T := 1) (-k) ((y : ℝ) : Circ)
  rw [fourier_coe_eq_ee_neg']

/-- **The master one-variable identity.**  For `m` of class `C²` with compact support and `f`
integrable,
`∑_j cw m j · e(-jη) · cw f (a-j) = ∫_y f(y) e(-ay) · periodize m (y - η) dy`.
This is Poisson summation (`cw_tsum_fourier`) applied to the inner sum after one interchange of
the series in `j` with the integral over `y` (`integral_tsum_of_summable_integral_norm`). -/
theorem tsum_cw_fourier_eq_integral_aux {m f : ℝ → ℂ} (hm : ContDiff ℝ 2 m)
    (hcs : HasCompactSupport m) (hf : MeasureTheory.Integrable f)
    (η : Circ) (a : ℤ) :
    (∑' j : ℤ, Work.KMTAreas.A7.cw m j * fourier (T := 1) (-j) η
        * Work.KMTAreas.A7.cw f (a - j))
      = ∫ y : ℝ, f y * fourier (T := 1) (-a) ((y : ℝ) : Circ)
          * Work.Analysis.IonescuWainger.periodize m
              (((y : ℝ) : Circ) - η) := by
  classical
  set F : ℤ → ℝ → ℂ := fun j y => Work.KMTAreas.A7.cw m j
      * fourier (T := 1) (-j) η
      * (f y * fourier (T := 1) (-(a - j)) ((y : ℝ) : Circ)) with hFdef
  have hgmeas : ∀ j : ℤ, AEStronglyMeasurable
      (fun y : ℝ => fourier (T := 1) (-(a - j)) ((y : ℝ) : Circ)) volume := by
    intro j
    have h : (fun y : ℝ => fourier (T := 1) (-(a - j)) ((y : ℝ) : Circ))
        = fun y : ℝ => Work.KMTAreas.A7.ee ((((-(a - j)) : ℤ) : ℝ) * y) := by
      funext y
      rw [fourier_coe_eq_ee']
    rw [h]
    exact (continuous_ee_const_mul' _).aestronglyMeasurable
  have hint : ∀ j : ℤ, MeasureTheory.Integrable (F j) := by
    intro j
    have h1 : MeasureTheory.Integrable
        (fun y : ℝ => f y * fourier (T := 1) (-(a - j)) ((y : ℝ) : Circ)) :=
      hf.mul_bdd (hgmeas j)
        (Filter.Eventually.of_forall (fun y => le_of_eq (norm_fourier_eq_one _ _)))
    have h2 : MeasureTheory.Integrable (fun y : ℝ => (Work.KMTAreas.A7.cw m j
        * fourier (T := 1) (-j) η)
        * (f y * fourier (T := 1) (-(a - j)) ((y : ℝ) : Circ))) := h1.const_mul _
    rwa [hFdef]
  have hsum : Summable fun j : ℤ => ∫ y, ‖F j y‖ := by
    have hbase : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖ :=
      summable_cw_of_contDiff_hasCompactSupport hm hcs
    have hpt : ∀ j : ℤ, ∫ y, ‖F j y‖ = ‖Work.KMTAreas.A7.cw m j‖ * ∫ y, ‖f y‖ := by
      intro j
      have h1 : (fun y : ℝ => ‖F j y‖)
          = fun y : ℝ => ‖Work.KMTAreas.A7.cw m j‖ * ‖f y‖ := by
        funext y
        simp only [hFdef, norm_mul, norm_fourier_eq_one, mul_one]
      rw [h1, MeasureTheory.integral_const_mul]
    simp only [hpt]
    exact hbase.mul_right _
  have hcw : ∀ j : ℤ, Work.KMTAreas.A7.cw f (a - j)
      = ∫ y : ℝ, f y * fourier (T := 1) (-(a - j)) ((y : ℝ) : Circ) :=
    fun j => cw_eq_integral_fourier' (a - j)
  have hFint : ∀ j : ℤ, ∫ y, F j y
      = (Work.KMTAreas.A7.cw m j * fourier (T := 1) (-j) η)
        * ∫ y : ℝ, f y * fourier (T := 1) (-(a - j)) ((y : ℝ) : Circ) := by
    intro j
    have hsplit : (fun y : ℝ => Work.KMTAreas.A7.cw m j * fourier (T := 1) (-j) η
          * (f y * fourier (T := 1) (-(a - j)) ((y : ℝ) : Circ)))
        = fun y : ℝ => (Work.KMTAreas.A7.cw m j * fourier (T := 1) (-j) η)
            * (f y * fourier (T := 1) (-(a - j)) ((y : ℝ) : Circ)) := rfl
    rw [hFdef, hsplit, MeasureTheory.integral_const_mul]
  simp only [hcw, ← hFint]
  rw [MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  have hterm : ∀ j : ℤ, F j y = Work.KMTAreas.A7.cw m j
      * fourier (T := 1) j (((y : ℝ) : Circ) - η)
      * (f y * fourier (T := 1) (-a) ((y : ℝ) : Circ)) := by
    intro j
    have hfa : fourier (T := 1) (-(a - j)) ((y : ℝ) : Circ)
        = fourier (T := 1) (-a) ((y : ℝ) : Circ)
          * fourier (T := 1) j ((y : ℝ) : Circ) := by
      rw [show (-(a - j) : ℤ) = (-a) + j by omega, fourier_add]
    have hcomb : fourier (T := 1) (-j) η * fourier (T := 1) j ((y : ℝ) : Circ)
        = fourier (T := 1) j (((y : ℝ) : Circ) - η) := by
      rw [sub_eq_add_neg, fourier_add_arg', fourier_neg_apply']
      ring
    simp only [hFdef]
    rw [hfa]
    rw [show Work.KMTAreas.A7.cw m j * fourier (T := 1) (-j) η
          * (f y * (fourier (T := 1) (-a) ((y : ℝ) : Circ)
              * fourier (T := 1) j ((y : ℝ) : Circ)))
        = Work.KMTAreas.A7.cw m j
            * (fourier (T := 1) (-j) η * fourier (T := 1) j ((y : ℝ) : Circ))
            * (f y * fourier (T := 1) (-a) ((y : ℝ) : Circ)) from by ring]
    rw [hcomb]
  simp only [hterm]
  rw [show (∑' j : ℤ, Work.KMTAreas.A7.cw m j
        * fourier (T := 1) j (((y : ℝ) : Circ) - η)
        * (f y * fourier (T := 1) (-a) ((y : ℝ) : Circ)))
      = (∑' j : ℤ, Work.KMTAreas.A7.cw m j
          * fourier (T := 1) j (((y : ℝ) : Circ) - η))
        * (f y * fourier (T := 1) (-a) ((y : ℝ) : Circ)) from tsum_mul_right]
  rw [cw_tsum_fourier hm hcs (((y : ℝ) : Circ) - η)]
  ring


/-! ## The `cw`-summability of a shifted sequence -/

/-- Shifting the index does not affect absolute summability of `cw`. -/
private lemma summable_cw_sub {f : ℝ → ℂ} (h : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw f j‖)
    (a : ℤ) : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw f (a - j)‖ := by
  have h2 : (fun j : ℤ => ‖Work.KMTAreas.A7.cw f (a - j)‖)
      = (fun j : ℤ => ‖Work.KMTAreas.A7.cw f j‖) ∘ (Equiv.subLeft a) := by
    funext j
    simp [Function.comp_def, Equiv.subLeft_apply]
  rw [h2]
  exact (Equiv.summable_iff (Equiv.subLeft a)).mpr h

/-- The character sums over `A₁` are bounded by the cardinality. -/
private lemma norm_finset_fourier_le {A : Finset Circ} (j : ℤ) :
    ‖∑ α ∈ A, fourier (T := 1) (-j) α‖ ≤ (A.card : ℝ) := by
  calc ‖∑ α ∈ A, fourier (T := 1) (-j) α‖ ≤ ∑ α ∈ A, ‖fourier (T := 1) (-j) α‖ :=
        norm_sum_le _ _
    _ = ∑ _α ∈ A, (1 : ℝ) := Finset.sum_congr rfl (fun α _ => norm_fourier_eq_one _ _)
    _ = (A.card : ℝ) := by simp

/-- **The distribution of the finite frequency sums.** -/
private lemma dist_arith {A₁ A₂ : Finset Circ} (W : Circ → Circ → ℂ)
    (m₁ m₂ f g : ℝ → ℂ) (α β : Circ) (a b : ℤ) (j₁ j₂ : ℤ) :
    W α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β
        * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂
      * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j₁)) α₁) * Work.KMTAreas.A7.cw f (a - j₁))
      * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j₂)) β₁) * Work.KMTAreas.A7.cw g (b - j₂))
    = ∑ q ∈ A₁.product A₂,
        (W α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β
            * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂)
          * (fourier (T := 1) (-(a - j₁)) q.1 * Work.KMTAreas.A7.cw f (a - j₁))
          * (fourier (T := 1) (-(b - j₂)) q.2 * Work.KMTAreas.A7.cw g (b - j₂)) := by
  rw [Finset.product_eq_sprod, Finset.sum_product]
  rw [Finset.sum_mul, Finset.sum_mul]
  have hA := Finset.mul_sum A₁ (fun α₁ : Circ =>
      fourier (T := 1) (-(a - j₁)) α₁ * Work.KMTAreas.A7.cw f (a - j₁))
      (W α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β
        * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂)
  rw [hA, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun α₁ _ => ?_)
  rw [Finset.mul_sum]

/-- The iterated `tsum` of a product family factorises. -/
private lemma tsum_prod_fact (A B : ℤ → ℂ) :
    (∑' j₁ : ℤ, ∑' j₂ : ℤ, A j₁ * B j₂) = (∑' j₁, A j₁) * (∑' j₂, B j₂) := by
  have h : (∑' j₁ : ℤ, ∑' j₂ : ℤ, A j₁ * B j₂)
      = ∑' j₁ : ℤ, A j₁ * (∑' j₂ : ℤ, B j₂) := by
    refine tsum_congr (fun j₁ => ?_)
    rw [tsum_mul_left]
  rw [h, tsum_mul_right]

/-- The elementary character identity of the one-variable computation. -/
private lemma one_var_ident (W' : ℂ) (α α₁ : Circ) (m f : ℝ → ℂ) (a : ℤ) (j : ℤ) :
    (W' * fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw m j)
        * (fourier (T := 1) (-(a - j)) α₁ * Work.KMTAreas.A7.cw f (a - j))
      = W' * fourier (T := 1) (-a) α₁
          * (Work.KMTAreas.A7.cw m j * fourier (T := 1) (-j) (α - α₁)
              * Work.KMTAreas.A7.cw f (a - j)) := by
  have h1 : fourier (T := 1) (-(a - j)) α₁
      = fourier (T := 1) (-a) α₁ * fourier (T := 1) j α₁ := by
    rw [show (-(a - j) : ℤ) = (-a) + j by omega, fourier_add]
  have h2 : fourier (T := 1) (-j) α * fourier (T := 1) j α₁
      = fourier (T := 1) (-j) (α - α₁) := by
    rw [show α - α₁ = α + (-α₁) by abel, fourier_add_arg', fourier_neg_apply']
    simp only [neg_neg]
  rw [h1]
  rw [show W' * fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw m j
        * (fourier (T := 1) (-a) α₁ * fourier (T := 1) j α₁ * Work.KMTAreas.A7.cw f (a - j))
      = W' * fourier (T := 1) (-a) α₁ * ((fourier (T := 1) (-j) α * fourier (T := 1) j α₁)
          * (Work.KMTAreas.A7.cw m j * Work.KMTAreas.A7.cw f (a - j))) from by ring]
  rw [h2]
  ring

/-- **The one-variable computation.**  Pulling the finite sum of the convolution kernel out of the
series and using `fourier_add`. -/
private lemma tsum_one_var {A : Finset Circ} (W' : ℂ) (α : Circ) (m f : ℝ → ℂ) (a : ℤ)
    (hm : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖)
    (hf : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw f j‖) :
    (∑' j : ℤ, W' * fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw m j
        * ((∑ α₁ ∈ A, fourier (T := 1) (-(a - j)) α₁) * Work.KMTAreas.A7.cw f (a - j)))
      = W' * ∑ α₁ ∈ A, fourier (T := 1) (-a) α₁
          * (∑' j : ℤ, Work.KMTAreas.A7.cw m j * fourier (T := 1) (-j) (α - α₁)
              * Work.KMTAreas.A7.cw f (a - j)) := by
  have hstep : ∀ j : ℤ, W' * fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw m j
        * ((∑ α₁ ∈ A, fourier (T := 1) (-(a - j)) α₁) * Work.KMTAreas.A7.cw f (a - j))
      = ∑ α₁ ∈ A, (W' * fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw m j)
          * (fourier (T := 1) (-(a - j)) α₁ * Work.KMTAreas.A7.cw f (a - j)) := by
    intro j
    rw [Finset.sum_mul]
    rw [Finset.mul_sum]
  simp only [hstep]
  rw [Summable.tsum_finsetSum (fun α₁ hα₁ => ?_)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun α₁ hα₁ => ?_)
    refine Eq.trans (tsum_congr (fun j => one_var_ident W' α α₁ m f a j)) ?_
    rw [show (∑' j : ℤ, W' * fourier (T := 1) (-a) α₁
          * (Work.KMTAreas.A7.cw m j * fourier (T := 1) (-j) (α - α₁)
              * Work.KMTAreas.A7.cw f (a - j)))
        = W' * fourier (T := 1) (-a) α₁
          * (∑' j : ℤ, Work.KMTAreas.A7.cw m j * fourier (T := 1) (-j) (α - α₁)
              * Work.KMTAreas.A7.cw f (a - j)) from tsum_mul_left]
    ring
  · refine Summable.of_norm_bounded
      (g := fun j : ℤ => (‖W'‖ + 1) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖)
        * ‖Work.KMTAreas.A7.cw f (a - j)‖)
      (Summable.mul_left _ (summable_cw_sub hf a)) (fun j => ?_)
    calc ‖(W' * fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw m j)
            * (fourier (T := 1) (-(a - j)) α₁ * Work.KMTAreas.A7.cw f (a - j))‖
        = ‖W'‖ * ‖Work.KMTAreas.A7.cw m j‖ * ‖Work.KMTAreas.A7.cw f (a - j)‖ := by
          simp only [norm_mul, norm_fourier_eq_one, mul_one, one_mul]
      _ ≤ (‖W'‖ + 1) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖)
            * ‖Work.KMTAreas.A7.cw f (a - j)‖ := by
          have h1 : ‖Work.KMTAreas.A7.cw m j‖ ≤ ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ := by
            simpa using hm.sum_le_tsum ({j} : Finset ℤ) (fun _ _ => norm_nonneg _)
          have hS : (0 : ℝ) ≤ ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ :=
            tsum_nonneg (fun _ => norm_nonneg _)
          have h0 : (0 : ℝ) ≤ ‖W'‖ := norm_nonneg _
          have hB : (0 : ℝ) ≤ ‖Work.KMTAreas.A7.cw f (a - j)‖ := norm_nonneg _
          calc ‖W'‖ * ‖Work.KMTAreas.A7.cw m j‖ * ‖Work.KMTAreas.A7.cw f (a - j)‖
              ≤ ‖W'‖ * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖)
                  * ‖Work.KMTAreas.A7.cw f (a - j)‖ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h0) hB
            _ ≤ (‖W'‖ + 1) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖)
                  * ‖Work.KMTAreas.A7.cw f (a - j)‖ := by
                refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hS) hB
                linarith

/-- The one-variable computation in the *single spike* form. -/
private lemma tsum_one_var_single (W' : ℂ) (α α₁ : Circ) (m f : ℝ → ℂ) (a : ℤ) :
    (∑' j : ℤ, W' * fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw m j
        * (fourier (T := 1) (-(a - j)) α₁ * Work.KMTAreas.A7.cw f (a - j)))
      = W' * fourier (T := 1) (-a) α₁
          * (∑' j : ℤ, Work.KMTAreas.A7.cw m j * fourier (T := 1) (-j) (α - α₁)
              * Work.KMTAreas.A7.cw f (a - j)) := by
  have h : (∑' j : ℤ, W' * fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw m j
        * (fourier (T := 1) (-(a - j)) α₁ * Work.KMTAreas.A7.cw f (a - j)))
      = ∑' j : ℤ, W' * fourier (T := 1) (-a) α₁
          * (Work.KMTAreas.A7.cw m j * fourier (T := 1) (-j) (α - α₁)
              * Work.KMTAreas.A7.cw f (a - j)) :=
    tsum_congr (fun j => one_var_ident W' α α₁ m f a j)
  rw [h, tsum_mul_left]

/-- **The one-term computation of the two-variable sum.** -/
private theorem double_tsum_single {A₁ A₂ : Finset Circ} (W : Circ → Circ → ℂ)
    (m₁ m₂ f g : ℝ → ℂ) (α β : Circ) (a b : ℤ)
    (hm₁ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖)
    (hm₂ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖)
    (hf : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw f j‖)
    (hg : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw g j‖) :
    (∑' j₁ : ℤ, ∑' j₂ : ℤ,
        W α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β
          * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂
          * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j₁)) α₁) * Work.KMTAreas.A7.cw f (a - j₁))
          * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j₂)) β₁) * Work.KMTAreas.A7.cw g (b - j₂)))
      = W α β * ∑ α₁ ∈ A₁, ∑ β₁ ∈ A₂,
          fourier (T := 1) (-a) α₁ * fourier (T := 1) (-b) β₁
          * (∑' j : ℤ, Work.KMTAreas.A7.cw m₁ j * fourier (T := 1) (-j) (α - α₁)
              * Work.KMTAreas.A7.cw f (a - j))
          * (∑' j : ℤ, Work.KMTAreas.A7.cw m₂ j * fourier (T := 1) (-j) (β - β₁)
              * Work.KMTAreas.A7.cw g (b - j)) := by
  classical
  have hfac : ∀ (q : Circ × Circ) (j₁ j₂ : ℤ),
      (W α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β
          * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂)
        * (fourier (T := 1) (-(a - j₁)) q.1 * Work.KMTAreas.A7.cw f (a - j₁))
        * (fourier (T := 1) (-(b - j₂)) q.2 * Work.KMTAreas.A7.cw g (b - j₂))
      = (W α β * fourier (T := 1) (-j₁) α * Work.KMTAreas.A7.cw m₁ j₁
            * (fourier (T := 1) (-(a - j₁)) q.1 * Work.KMTAreas.A7.cw f (a - j₁)))
        * (fourier (T := 1) (-j₂) β * Work.KMTAreas.A7.cw m₂ j₂
            * (fourier (T := 1) (-(b - j₂)) q.2 * Work.KMTAreas.A7.cw g (b - j₂))) := by
    intro q j₁ j₂
    ring
  simp only [dist_arith, hfac]
  -- summability of the two factor sequences
  have hAA : ∀ q : Circ × Circ, Summable fun j : ℤ =>
      W α β * fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw m₁ j
        * (fourier (T := 1) (-(a - j)) q.1 * Work.KMTAreas.A7.cw f (a - j)) := by
    intro q
    refine Summable.of_norm_bounded
      (g := fun j : ℤ => (‖W α β‖ + 1) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m₁ j‖)
        * ‖Work.KMTAreas.A7.cw f (a - j)‖) (Summable.mul_left _ (summable_cw_sub hf a))
      (fun j => ?_)
    calc ‖W α β * fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw m₁ j
            * (fourier (T := 1) (-(a - j)) q.1 * Work.KMTAreas.A7.cw f (a - j))‖
        = ‖W α β‖ * ‖Work.KMTAreas.A7.cw m₁ j‖ * ‖Work.KMTAreas.A7.cw f (a - j)‖ := by
          simp only [norm_mul, norm_fourier_eq_one, mul_one, one_mul]
      _ ≤ (‖W α β‖ + 1) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m₁ j‖)
            * ‖Work.KMTAreas.A7.cw f (a - j)‖ := by
          have h1 : ‖Work.KMTAreas.A7.cw m₁ j‖ ≤ ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m₁ j‖ := by
            simpa using hm₁.sum_le_tsum ({j} : Finset ℤ) (fun _ _ => norm_nonneg _)
          have hS : (0 : ℝ) ≤ ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m₁ j‖ :=
            tsum_nonneg (fun _ => norm_nonneg _)
          have h0 : (0 : ℝ) ≤ ‖W α β‖ := norm_nonneg _
          have hB : (0 : ℝ) ≤ ‖Work.KMTAreas.A7.cw f (a - j)‖ := norm_nonneg _
          calc ‖W α β‖ * ‖Work.KMTAreas.A7.cw m₁ j‖ * ‖Work.KMTAreas.A7.cw f (a - j)‖
              ≤ ‖W α β‖ * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m₁ j‖)
                  * ‖Work.KMTAreas.A7.cw f (a - j)‖ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h0) hB
            _ ≤ (‖W α β‖ + 1) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m₁ j‖)
                  * ‖Work.KMTAreas.A7.cw f (a - j)‖ := by
                refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hS) hB
                linarith
  have hBB : ∀ q : Circ × Circ, Summable fun j : ℤ =>
      fourier (T := 1) (-j) β * Work.KMTAreas.A7.cw m₂ j
        * (fourier (T := 1) (-(b - j)) q.2 * Work.KMTAreas.A7.cw g (b - j)) := by
    intro q
    refine Summable.of_norm_bounded
      (g := fun j : ℤ => (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m₂ j‖)
        * ‖Work.KMTAreas.A7.cw g (b - j)‖) (Summable.mul_left _ (summable_cw_sub hg b))
      (fun j => ?_)
    calc ‖fourier (T := 1) (-j) β * Work.KMTAreas.A7.cw m₂ j
            * (fourier (T := 1) (-(b - j)) q.2 * Work.KMTAreas.A7.cw g (b - j))‖
        = ‖Work.KMTAreas.A7.cw m₂ j‖ * ‖Work.KMTAreas.A7.cw g (b - j)‖ := by
          simp only [norm_mul, norm_fourier_eq_one, mul_one, one_mul]
      _ ≤ (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m₂ j‖) * ‖Work.KMTAreas.A7.cw g (b - j)‖ := by
          have h1 : ‖Work.KMTAreas.A7.cw m₂ j‖ ≤ ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m₂ j‖ := by
            simpa using hm₂.sum_le_tsum ({j} : Finset ℤ) (fun _ _ => norm_nonneg _)
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hM2 : ∀ q ∈ A₁.product A₂, ∀ j₁ : ℤ, Summable fun j₂ : ℤ =>
      (W α β * fourier (T := 1) (-j₁) α * Work.KMTAreas.A7.cw m₁ j₁
          * (fourier (T := 1) (-(a - j₁)) q.1 * Work.KMTAreas.A7.cw f (a - j₁)))
        * (fourier (T := 1) (-j₂) β * Work.KMTAreas.A7.cw m₂ j₂
            * (fourier (T := 1) (-(b - j₂)) q.2 * Work.KMTAreas.A7.cw g (b - j₂))) := by
    intro q hq j₁
    exact (hBB q).mul_left _
  have hM1 : ∀ q ∈ A₁.product A₂, Summable fun j₁ : ℤ => ∑' j₂ : ℤ,
      (W α β * fourier (T := 1) (-j₁) α * Work.KMTAreas.A7.cw m₁ j₁
          * (fourier (T := 1) (-(a - j₁)) q.1 * Work.KMTAreas.A7.cw f (a - j₁)))
        * (fourier (T := 1) (-j₂) β * Work.KMTAreas.A7.cw m₂ j₂
            * (fourier (T := 1) (-(b - j₂)) q.2 * Work.KMTAreas.A7.cw g (b - j₂))) := by
    intro q hq
    have hC : (fun j₁ : ℤ => ∑' j₂ : ℤ,
        (W α β * fourier (T := 1) (-j₁) α * Work.KMTAreas.A7.cw m₁ j₁
            * (fourier (T := 1) (-(a - j₁)) q.1 * Work.KMTAreas.A7.cw f (a - j₁)))
          * (fourier (T := 1) (-j₂) β * Work.KMTAreas.A7.cw m₂ j₂
              * (fourier (T := 1) (-(b - j₂)) q.2 * Work.KMTAreas.A7.cw g (b - j₂))))
        = fun j₁ : ℤ => (W α β * fourier (T := 1) (-j₁) α * Work.KMTAreas.A7.cw m₁ j₁
            * (fourier (T := 1) (-(a - j₁)) q.1 * Work.KMTAreas.A7.cw f (a - j₁)))
          * (∑' j₂ : ℤ, fourier (T := 1) (-j₂) β * Work.KMTAreas.A7.cw m₂ j₂
              * (fourier (T := 1) (-(b - j₂)) q.2 * Work.KMTAreas.A7.cw g (b - j₂))) := by
      funext j₁
      exact tsum_mul_left
    rw [hC]
    exact (hAA q).mul_right _
  have hinner : ∀ j₁ : ℤ, (∑' j₂ : ℤ, ∑ q ∈ A₁.product A₂,
        (W α β * fourier (T := 1) (-j₁) α * Work.KMTAreas.A7.cw m₁ j₁
            * (fourier (T := 1) (-(a - j₁)) q.1 * Work.KMTAreas.A7.cw f (a - j₁)))
          * (fourier (T := 1) (-j₂) β * Work.KMTAreas.A7.cw m₂ j₂
              * (fourier (T := 1) (-(b - j₂)) q.2 * Work.KMTAreas.A7.cw g (b - j₂))))
      = ∑ q ∈ A₁.product A₂, ∑' j₂ : ℤ,
        (W α β * fourier (T := 1) (-j₁) α * Work.KMTAreas.A7.cw m₁ j₁
            * (fourier (T := 1) (-(a - j₁)) q.1 * Work.KMTAreas.A7.cw f (a - j₁)))
          * (fourier (T := 1) (-j₂) β * Work.KMTAreas.A7.cw m₂ j₂
              * (fourier (T := 1) (-(b - j₂)) q.2 * Work.KMTAreas.A7.cw g (b - j₂))) := by
    intro j₁
    exact Summable.tsum_finsetSum (fun q hq => hM2 q hq j₁)
  simp only [hinner]
  rw [Summable.tsum_finsetSum (fun q hq => hM1 q hq)]
  -- the per-`q` computation
  rw [show (∑ q ∈ A₁.product A₂, ∑' j₁ : ℤ, ∑' j₂ : ℤ,
        (W α β * fourier (T := 1) (-j₁) α * Work.KMTAreas.A7.cw m₁ j₁
            * (fourier (T := 1) (-(a - j₁)) q.1 * Work.KMTAreas.A7.cw f (a - j₁)))
          * (fourier (T := 1) (-j₂) β * Work.KMTAreas.A7.cw m₂ j₂
              * (fourier (T := 1) (-(b - j₂)) q.2 * Work.KMTAreas.A7.cw g (b - j₂))))
      = ∑ q ∈ A₁.product A₂, W α β * (fourier (T := 1) (-a) q.1 * fourier (T := 1) (-b) q.2
          * (∑' j : ℤ, Work.KMTAreas.A7.cw m₁ j * fourier (T := 1) (-j) (α - q.1)
              * Work.KMTAreas.A7.cw f (a - j))
          * (∑' j : ℤ, Work.KMTAreas.A7.cw m₂ j * fourier (T := 1) (-j) (β - q.2)
              * Work.KMTAreas.A7.cw g (b - j))) from by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [tsum_prod_fact]
    rw [tsum_one_var_single (W α β) α q.1 m₁ f a]
    have hbb : (∑' j : ℤ, fourier (T := 1) (-j) β * Work.KMTAreas.A7.cw m₂ j
          * (fourier (T := 1) (-(b - j)) q.2 * Work.KMTAreas.A7.cw g (b - j)))
        = fourier (T := 1) (-b) q.2
          * (∑' j : ℤ, Work.KMTAreas.A7.cw m₂ j * fourier (T := 1) (-j) (β - q.2)
              * Work.KMTAreas.A7.cw g (b - j)) := by
      simpa only [one_mul] using tsum_one_var_single (1 : ℂ) β q.2 m₂ g b
    rw [hbb]
    ring]
  rw [← Finset.mul_sum]
  rw [Finset.product_eq_sprod, Finset.sum_product]

/-- The boundedness of one "half-kernel times `cw`" factor of the arithmetic kernel. -/
private lemma summable_ker_factor {A : Finset Circ} (W' : ℂ) (α : Circ) (m f : ℝ → ℂ) (a : ℤ)
    (hm : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖)
    (hf : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw f j‖) :
    Summable fun j : ℤ => W' * fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw m j
        * ((∑ α₁ ∈ A, fourier (T := 1) (-(a - j)) α₁) * Work.KMTAreas.A7.cw f (a - j)) := by
  refine Summable.of_norm_bounded
    (g := fun j : ℤ => (‖W'‖ + 1) * (A.card : ℝ) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖)
      * ‖Work.KMTAreas.A7.cw f (a - j)‖) (Summable.mul_left _ (summable_cw_sub hf a))
    (fun j => ?_)
  have hA : ‖∑ α₁ ∈ A, fourier (T := 1) (-(a - j)) α₁‖ ≤ (A.card : ℝ) :=
    norm_finset_fourier_le _
  have h1 : ‖Work.KMTAreas.A7.cw m j‖ ≤ ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ := by
    simpa using hm.sum_le_tsum ({j} : Finset ℤ) (fun _ _ => norm_nonneg _)
  have h0 : (0 : ℝ) ≤ ‖W'‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖Work.KMTAreas.A7.cw f (a - j)‖ := norm_nonneg _
  have h3 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ := tsum_nonneg (fun _ => norm_nonneg _)
  have h5 : (0 : ℝ) ≤ ‖Work.KMTAreas.A7.cw m j‖ := norm_nonneg _
  have h6 : (0 : ℝ) ≤ ‖∑ α₁ ∈ A, fourier (T := 1) (-(a - j)) α₁‖ := norm_nonneg _
  calc ‖W' * fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw m j
          * ((∑ α₁ ∈ A, fourier (T := 1) (-(a - j)) α₁) * Work.KMTAreas.A7.cw f (a - j))‖
      = ‖W'‖ * ‖Work.KMTAreas.A7.cw m j‖
          * ‖∑ α₁ ∈ A, fourier (T := 1) (-(a - j)) α₁‖ * ‖Work.KMTAreas.A7.cw f (a - j)‖ := by
        simp only [norm_mul, norm_fourier_eq_one, mul_one, one_mul]
        ring
    _ ≤ (‖W'‖ + 1) * (A.card : ℝ) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖)
          * ‖Work.KMTAreas.A7.cw f (a - j)‖ := by
        have hAB : ‖W'‖ * ‖Work.KMTAreas.A7.cw m j‖
            ≤ (‖W'‖ + 1) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖) := by
          calc ‖W'‖ * ‖Work.KMTAreas.A7.cw m j‖
              ≤ ‖W'‖ * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖) :=
                mul_le_mul_of_nonneg_left h1 h0
            _ ≤ (‖W'‖ + 1) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖) :=
                mul_le_mul_of_nonneg_right (by linarith) h4
        calc ‖W'‖ * ‖Work.KMTAreas.A7.cw m j‖
              * ‖∑ α₁ ∈ A, fourier (T := 1) (-(a - j)) α₁‖ * ‖Work.KMTAreas.A7.cw f (a - j)‖
            ≤ ((‖W'‖ + 1) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖))
                * (A.card : ℝ) * ‖Work.KMTAreas.A7.cw f (a - j)‖ := by
              gcongr
          _ = (‖W'‖ + 1) * (A.card : ℝ) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖)
                * ‖Work.KMTAreas.A7.cw f (a - j)‖ := by ring

/-- **The two-variable factorisation of `kernComp` for arithmetic kernels.** -/
theorem kernComp_arith_factor_aux {A₁ A₂ : Finset Circ}
    (W : Circ → Circ → ℂ) (m₁ m₂ f g : ℝ → ℂ) (a b : ℤ)
    (hs₁ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖)
    (hs₂ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖)
    (hf : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw f j‖)
    (hg : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw g j‖) :
    Work.KMTAreas.A7.kernComp
        (fun j₁ j₂ => (∑ α ∈ A₁, ∑ β ∈ A₂,
              W α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β)
            * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂)
        (fun j => (∑ α ∈ A₁, fourier (T := 1) (-j) α) * Work.KMTAreas.A7.cw f j)
        (fun j => (∑ β ∈ A₂, fourier (T := 1) (-j) β) * Work.KMTAreas.A7.cw g j) a b
      = ∑ α ∈ A₁, ∑ β ∈ A₂, W α β *
          ∑ α₁ ∈ A₁, ∑ β₁ ∈ A₂,
            fourier (T := 1) (-a) α₁ * fourier (T := 1) (-b) β₁
            * (∑' j : ℤ, Work.KMTAreas.A7.cw m₁ j * fourier (T := 1) (-j) (α - α₁)
                * Work.KMTAreas.A7.cw f (a - j))
            * (∑' j : ℤ, Work.KMTAreas.A7.cw m₂ j * fourier (T := 1) (-j) (β - β₁)
                * Work.KMTAreas.A7.cw g (b - j)) := by
  classical
  have hK : ∀ j₁ j₂ : ℤ,
      (∑ α ∈ A₁, ∑ β ∈ A₂, W α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β)
        * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂
      = ∑ p ∈ A₁.product A₂, W p.1 p.2 * fourier (T := 1) (-j₁) p.1
          * fourier (T := 1) (-j₂) p.2 * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂ := by
    intro j₁ j₂
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp only [Finset.sum_mul]
  rw [Work.KMTAreas.A7.kernComp_eq_iter]
  have hexp : (∑' j₁ : ℤ, ∑' j₂ : ℤ,
        (∑ α ∈ A₁, ∑ β ∈ A₂, W α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β)
          * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂
          * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j₁)) α₁) * Work.KMTAreas.A7.cw f (a - j₁))
          * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j₂)) β₁) * Work.KMTAreas.A7.cw g (b - j₂)))
      = ∑' j₁ : ℤ, ∑' j₂ : ℤ, ∑ p ∈ A₁.product A₂,
          (W p.1 p.2 * fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
              * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂)
            * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j₁)) α₁) * Work.KMTAreas.A7.cw f (a - j₁))
            * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j₂)) β₁) * Work.KMTAreas.A7.cw g (b - j₂)) := by
    refine tsum_congr (fun j₁ => tsum_congr (fun j₂ => ?_))
    rw [hK, Finset.sum_mul, Finset.sum_mul]
  rw [hexp]
  -- summability of the `j₂`-sum for each `p` and each `j₁`
  have hH2 : ∀ p ∈ A₁.product A₂, ∀ j₁ : ℤ, Summable fun j₂ : ℤ =>
      (W p.1 p.2 * fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
          * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂)
        * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j₁)) α₁) * Work.KMTAreas.A7.cw f (a - j₁))
        * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j₂)) β₁) * Work.KMTAreas.A7.cw g (b - j₂)) := by
    intro p hp j₁
    have hY : Summable fun j₂ : ℤ => fourier (T := 1) (-j₂) p.2 * Work.KMTAreas.A7.cw m₂ j₂
        * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j₂)) β₁) * Work.KMTAreas.A7.cw g (b - j₂)) :=
      (summable_ker_factor (A := A₂) 1 p.2 m₂ g b hs₂ hg).congr (fun j₂ => by ring)
    refine (hY.mul_left (W p.1 p.2 * fourier (T := 1) (-j₁) p.1 * Work.KMTAreas.A7.cw m₁ j₁
      * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j₁)) α₁) * Work.KMTAreas.A7.cw f (a - j₁)))).congr
      (fun j₂ => ?_)
    ring
  have hH1 : ∀ p ∈ A₁.product A₂, Summable fun j₁ : ℤ => ∑' j₂ : ℤ,
      (W p.1 p.2 * fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
          * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂)
        * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j₁)) α₁) * Work.KMTAreas.A7.cw f (a - j₁))
        * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j₂)) β₁) * Work.KMTAreas.A7.cw g (b - j₂)) := by
    intro p hp
    have hX : Summable fun j : ℤ => W p.1 p.2 * fourier (T := 1) (-j) p.1
        * Work.KMTAreas.A7.cw m₁ j
        * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j)) α₁) * Work.KMTAreas.A7.cw f (a - j)) :=
      summable_ker_factor (W p.1 p.2) p.1 m₁ f a hs₁ hf
    have hY : Summable fun j : ℤ => fourier (T := 1) (-j) p.2 * Work.KMTAreas.A7.cw m₂ j
        * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j)) β₁) * Work.KMTAreas.A7.cw g (b - j)) :=
      (summable_ker_factor (A := A₂) 1 p.2 m₂ g b hs₂ hg).congr (fun j₂ => by ring)
    have hC : (fun j₁ : ℤ => ∑' j₂ : ℤ,
        (W p.1 p.2 * fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
            * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂)
          * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j₁)) α₁) * Work.KMTAreas.A7.cw f (a - j₁))
          * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j₂)) β₁) * Work.KMTAreas.A7.cw g (b - j₂)))
        = fun j₁ : ℤ => (W p.1 p.2 * fourier (T := 1) (-j₁) p.1 * Work.KMTAreas.A7.cw m₁ j₁
            * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j₁)) α₁) * Work.KMTAreas.A7.cw f (a - j₁)))
          * (∑' j₂ : ℤ, fourier (T := 1) (-j₂) p.2 * Work.KMTAreas.A7.cw m₂ j₂
              * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j₂)) β₁) * Work.KMTAreas.A7.cw g (b - j₂))) := by
      funext j₁
      have hterm : (fun j₂ : ℤ =>
          (W p.1 p.2 * fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
              * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂)
            * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j₁)) α₁) * Work.KMTAreas.A7.cw f (a - j₁))
            * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j₂)) β₁) * Work.KMTAreas.A7.cw g (b - j₂)))
          = fun j₂ : ℤ => (W p.1 p.2 * fourier (T := 1) (-j₁) p.1 * Work.KMTAreas.A7.cw m₁ j₁
              * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j₁)) α₁) * Work.KMTAreas.A7.cw f (a - j₁)))
            * (fourier (T := 1) (-j₂) p.2 * Work.KMTAreas.A7.cw m₂ j₂
              * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j₂)) β₁) * Work.KMTAreas.A7.cw g (b - j₂))) := by
        funext j₂
        ring
      rw [hterm, tsum_mul_left]
    rw [hC]
    exact hX.mul_right _
  have hinner : ∀ j₁ : ℤ, (∑' j₂ : ℤ, ∑ p ∈ A₁.product A₂,
        (W p.1 p.2 * fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
            * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂)
          * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j₁)) α₁) * Work.KMTAreas.A7.cw f (a - j₁))
          * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j₂)) β₁) * Work.KMTAreas.A7.cw g (b - j₂)))
      = ∑ p ∈ A₁.product A₂, ∑' j₂ : ℤ,
        (W p.1 p.2 * fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
            * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂)
          * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j₁)) α₁) * Work.KMTAreas.A7.cw f (a - j₁))
          * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j₂)) β₁) * Work.KMTAreas.A7.cw g (b - j₂)) := by
    intro j₁
    exact Summable.tsum_finsetSum (fun p hp => hH2 p hp j₁)
  simp only [hinner]
  rw [Summable.tsum_finsetSum (fun p hp => hH1 p hp)]
  rw [show (∑ p ∈ A₁.product A₂, ∑' j₁ : ℤ, ∑' j₂ : ℤ,
        (W p.1 p.2 * fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
            * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂)
          * ((∑ α₁ ∈ A₁, fourier (T := 1) (-(a - j₁)) α₁) * Work.KMTAreas.A7.cw f (a - j₁))
          * ((∑ β₁ ∈ A₂, fourier (T := 1) (-(b - j₂)) β₁) * Work.KMTAreas.A7.cw g (b - j₂)))
      = ∑ p ∈ A₁.product A₂, W p.1 p.2 * ∑ α₁ ∈ A₁, ∑ β₁ ∈ A₂,
          fourier (T := 1) (-a) α₁ * fourier (T := 1) (-b) β₁
          * (∑' j : ℤ, Work.KMTAreas.A7.cw m₁ j * fourier (T := 1) (-j) (p.1 - α₁)
              * Work.KMTAreas.A7.cw f (a - j))
          * (∑' j : ℤ, Work.KMTAreas.A7.cw m₂ j * fourier (T := 1) (-j) (p.2 - β₁)
              * Work.KMTAreas.A7.cw g (b - j)) from
    Finset.sum_congr rfl (fun p hp =>
      double_tsum_single W m₁ m₂ f g p.1 p.2 a b hs₁ hs₂ hf hg)]
  rw [Finset.product_eq_sprod, Finset.sum_product]

end

end Work.KMTAreas.A7
