import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseKinLoc.Momentum.chFT_eq_ofReal
import Submission.Work.BoseKinLoc.Momentum.cubFT_prod
import Submission.Work.BoseKinLoc.Momentum.hFT_bounds
import Submission.Work.BoseKinLoc.Momentum.hasDerivAt_hFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Derivative facts about the unit-cube Fourier symbol `cubFT`

The symbol `cubFT q = ∫_{acube 1} cos ⟪q,x⟫ dx` factorises as `∏ i, hFT (q i)`
(`cubFT_eq_prod_of`, `chFT_eq_ofReal`), so it is a product of one-dimensional
differentiable factors and its Fréchet derivative is given by the product rule:

    `fderiv ℝ cubFT q h = ∑ i, (-(mFT (q i)) * ∏ j ≠ i, hFT (q j)) * h i`.

The three facts recorded in `cubFT_deriv_facts` are:

* this coordinate formula for the full derivative;
* the momentum bound `|fderiv ℝ cubFT q (kcStdBasis i)| ≤ ∏ j, 2 / max 1 |q j|`
  obtained from `|hFT t| ≤ 2/max 1 |t|` and `|mFT t| ≤ 2/max 1 |t|`;
* the fundamental theorem of calculus along the segment `t ↦ w - t v`, i.e.
  `cubFT (w - v) - cubFT w = ∫_0^1 fderiv ℝ cubFT (w - t • v) (-v) dt`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false

/-! ## Coordinates of the standard basis and the one-dimensional factors -/

/-- Coordinates of the standard basis vector: `(kcStdBasis i) j = δ_{ij}`. -/
lemma kcStdBasis_apply_coord (i j : Fin 3) :
    (kcStdBasis i : ℝ³) j = if j = i then (1 : ℝ) else 0 := by
  rw [Submission.BoseGases.kcStdBasis, EuclideanSpace.single_apply]

/-- `inner ℝ (kcStdBasis i) q = q i`. -/
lemma inner_kcStdBasis (i : Fin 3) (q : ℝ³) :
    inner ℝ (kcStdBasis i) q = q i := by
  rw [Submission.BoseGases.kcStdBasis, EuclideanSpace.inner_single_left]
  simp

/-- `hFT` is continuous (it is differentiable everywhere, `hasDerivAt_hFT`). -/
lemma continuous_hFT : Continuous hFT :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_hFT t).continuousAt

/-- `mFT` is continuous: it is a parametric integral over the compact interval `[-1/2,1/2]`. -/
lemma continuous_mFT : Continuous mFT := by
  have h := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun (t s : ℝ) => s * Real.sin (t * s)) (by fun_prop)
    (s := Set.Icc (-(1/2)) (1/2)) isCompact_Icc
  exact h

lemma continuous_coord (i : Fin 3) : Continuous (fun q : ℝ³ => q i) := by fun_prop

lemma continuous_hFT_coord (i : Fin 3) : Continuous (fun q : ℝ³ => hFT (q i)) :=
  continuous_hFT.comp (continuous_coord i)

lemma continuous_mFT_coord (i : Fin 3) : Continuous (fun q : ℝ³ => mFT (q i)) :=
  continuous_mFT.comp (continuous_coord i)

/-! ## The derivative of `cubFT` -/

/-- The Fréchet derivative of `cubFT` at `q`, in the form produced by the product rule. -/
def cubFTderiv (q : ℝ³) : ℝ³ →L[ℝ] ℝ :=
  ∑ i : Fin 3, (∏ j ∈ Finset.univ.erase i, hFT (q j)) •
    ((-(mFT (q i))) • innerSL ℝ (kcStdBasis i))

/-- The one-dimensional factors `hFT` and `mFT` have derivative `hFT' = -mFT`, hence the
coordinate factors `q ↦ hFT (q j)` have Fréchet derivative `-(mFT (q j)) • innerSL ℝ (kcStdBasis j)`. -/
lemma hasFDerivAt_hFT_coord (q : ℝ³) (j : Fin 3) :
    HasFDerivAt (fun x : ℝ³ => hFT (x j))
      ((-(mFT (q j))) • innerSL ℝ (kcStdBasis j)) q := by
  have h1 : HasFDerivAt (innerSL ℝ (kcStdBasis j)) (innerSL ℝ (kcStdBasis j)) q :=
    (innerSL ℝ (kcStdBasis j)).hasFDerivAt
  have h3 : HasFDerivAt (hFT ∘ (innerSL ℝ (kcStdBasis j)))
      ((-(mFT (inner ℝ (kcStdBasis j) q))) • innerSL ℝ (kcStdBasis j)) q :=
    (hasDerivAt_hFT (inner ℝ (kcStdBasis j) q)).comp_hasFDerivAt q h1
  rw [inner_kcStdBasis j q] at h3
  have h4 : (fun x : ℝ³ => hFT (x j)) = (hFT ∘ (innerSL ℝ (kcStdBasis j))) := by
    funext x
    simp [Function.comp, innerSL_apply_apply, inner_kcStdBasis]
  rwa [h4]

/-- **The product rule for `cubFT`**: the derivative of `∏ j, hFT (q j)` at `q`. -/
lemma hasFDerivAt_cubFT (q : ℝ³) : HasFDerivAt cubFT (cubFTderiv q) q := by
  have h := HasFDerivAt.finsetProd (u := Finset.univ) (g := fun j (x : ℝ³) => hFT (x j))
    (g' := fun j => (-(mFT (q j))) • innerSL ℝ (kcStdBasis j))
    (fun j _ => hasFDerivAt_hFT_coord q j)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  show cubFT x = ∏ i ∈ Finset.univ, hFT (x i)
  rw [cubFT_eq_prod_of chFT_eq_ofReal]

/-- **The full derivative of `cubFT`.** -/
lemma fderiv_cubFT_apply (q h : ℝ³) :
    fderiv ℝ cubFT q h =
      ∑ i : Fin 3, (-(mFT (q i)) * ∏ j ∈ Finset.univ.erase i, hFT (q j)) * h i := by
  rw [(hasFDerivAt_cubFT q).fderiv]
  rw [cubFTderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, inner_kcStdBasis, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The coordinate derivative of `cubFT`.** -/
lemma fderiv_cubFT_basis (q : ℝ³) (i : Fin 3) :
    fderiv ℝ cubFT q (kcStdBasis i) = -(mFT (q i)) * ∏ j ∈ Finset.univ.erase i, hFT (q j) := by
  rw [fderiv_cubFT_apply]
  rw [Finset.sum_eq_single i]
  · rw [kcStdBasis_apply_coord, if_pos rfl, mul_one]
  · intro b _ hb
    rw [kcStdBasis_apply_coord, if_neg hb, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ## The momentum bound -/

lemma two_div_max_nonneg (t : ℝ) : 0 ≤ 2 / max 1 |t| :=
  div_nonneg (by norm_num) (le_trans zero_le_one (le_max_left _ _))

/-- `|hFT t| ≤ 2 / max 1 |t|`. -/
lemma hFT_abs_le_two_div_max (t : ℝ) : |hFT t| ≤ 2 / max 1 |t| := by
  rcases le_or_gt |t| 1 with h | h
  · rw [max_eq_left h, div_one]
    linarith [hFT_abs_le_one t]
  · rw [max_eq_right (le_of_lt h), le_div_iff₀ (lt_trans zero_lt_one h)]
    calc |hFT t| * |t| = |hFT t * t| := (abs_mul _ _).symm
      _ = |t * hFT t| := by rw [mul_comm]
      _ ≤ 2 := hFT_mul_abs_le t

/-- `|mFT t| ≤ 2 / max 1 |t|`. -/
lemma mFT_abs_le_two_div_max (t : ℝ) : |mFT t| ≤ 2 / max 1 |t| := by
  rcases le_or_gt |t| 1 with h | h
  · rw [max_eq_left h, div_one]
    linarith [mFT_abs_le_half t]
  · rw [max_eq_right (le_of_lt h), le_div_iff₀ (lt_trans zero_lt_one h)]
    calc |mFT t| * |t| = |mFT t * t| := (abs_mul _ _).symm
      _ = |t * mFT t| := by rw [mul_comm]
      _ ≤ 2 := mFT_mul_abs_le t

/-- **The momentum bound for the coordinate derivative of `cubFT`.** -/
lemma fderiv_cubFT_basis_abs_le (q : ℝ³) (i : Fin 3) :
    |fderiv ℝ cubFT q (kcStdBasis i)| ≤ ∏ j : Fin 3, 2 / max 1 |q j| := by
  rw [fderiv_cubFT_basis, abs_mul, abs_neg, Finset.abs_prod]
  calc |mFT (q i)| * ∏ j ∈ Finset.univ.erase i, |hFT (q j)|
      ≤ (2 / max 1 |q i|) * ∏ j ∈ Finset.univ.erase i, (2 / max 1 |q j|) :=
        mul_le_mul (mFT_abs_le_two_div_max (q i))
          (Finset.prod_le_prod₀ (fun j _ => abs_nonneg _)
            (fun j _ => hFT_abs_le_two_div_max (q j)))
          (Finset.prod_nonneg fun j _ => abs_nonneg _) (two_div_max_nonneg (q i))
    _ = ∏ j : Fin 3, 2 / max 1 |q j| := by
        rw [mul_comm, Finset.prod_erase_mul Finset.univ
          (fun j : Fin 3 => 2 / max 1 |q j|) (Finset.mem_univ i)]

/-! ## Continuity and the fundamental theorem of calculus -/

/-- `q ↦ fderiv ℝ cubFT q h` is continuous for fixed `h`. -/
lemma continuous_fderiv_cubFT_apply (h : ℝ³) : Continuous (fun q : ℝ³ => fderiv ℝ cubFT q h) := by
  have heq : (fun q : ℝ³ => fderiv ℝ cubFT q h) =
      fun q : ℝ³ => ∑ i : Fin 3,
        (-(mFT (q i)) * ∏ j ∈ Finset.univ.erase i, hFT (q j)) * h i := by
    funext q
    rw [fderiv_cubFT_apply]
  rw [heq]
  refine continuous_finsetSum Finset.univ fun i _ => ?_
  refine Continuous.mul (Continuous.mul (continuous_neg.comp (continuous_mFT_coord i)) ?_)
    continuous_const
  exact continuous_finsetProd (Finset.univ.erase i) fun j _ => continuous_hFT_coord j

/-- Continuity of the derivative along the segment `t ↦ w - t v`. -/
lemma continuous_fderiv_cubFT_along (w v : ℝ³) :
    Continuous (fun t : ℝ => fderiv ℝ cubFT (w - t • v) (-v)) :=
  (continuous_fderiv_cubFT_apply (-v)).comp (by fun_prop)

/-- **Fundamental theorem of calculus for `cubFT`** along the segment `t ↦ w - t v`. -/
lemma cubFT_sub_eq_integral_fderiv (w v : ℝ³) :
    cubFT (w - v) - cubFT w = ∫ t in (0 : ℝ)..1, fderiv ℝ cubFT (w - t • v) (-v) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => cubFT (w - t • v))
      (fderiv ℝ cubFT (w - t • v) (-v)) t := by
    intro t
    have hcurve : HasDerivAt (fun t : ℝ => w - t • v) (-v) t := by
      have h1 : HasDerivAt (fun t : ℝ => t • v) v t := by
        simpa using (hasDerivAt_id t).smul_const v
      simpa using h1.const_sub w
    have hd := HasFDerivAt.comp_hasDerivAt t
      ((hasFDerivAt_cubFT (w - t • v)).differentiableAt.hasFDerivAt) hcurve
    exact hd
  have hint : IntervalIntegrable (fun t : ℝ => fderiv ℝ cubFT (w - t • v) (-v)) volume 0 1 :=
    (continuous_fderiv_cubFT_along w v).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := 1) (f := fun t : ℝ => cubFT (w - t • v))
    (f' := fun t : ℝ => fderiv ℝ cubFT (w - t • v) (-v)) (fun t _ => hderiv t) hint
  rw [h]
  simp

theorem cubFT_deriv_facts :
    (∀ q h : EuclideanSpace ℝ (Fin 3),
        fderiv ℝ cubFT q h =
          ∑ i : Fin 3,
            (-(mFT (q i)) * ∏ j ∈ Finset.univ.erase i, hFT (q j)) * h i) ∧
    (∀ q : EuclideanSpace ℝ (Fin 3), ∀ i : Fin 3,
        |fderiv ℝ cubFT q (Submission.BoseGases.kcStdBasis i)|
          ≤ ∏ j : Fin 3, 2 / max 1 |q j|) ∧
    (∀ w v : EuclideanSpace ℝ (Fin 3),
        cubFT (w - v) - cubFT w =
          ∫ t in (0:ℝ)..1, fderiv ℝ cubFT (w - t • v) (-v)) :=
  ⟨fderiv_cubFT_apply, fderiv_cubFT_basis_abs_le, cubFT_sub_eq_integral_fderiv⟩

end Work.BoseKinLoc.Momentum
