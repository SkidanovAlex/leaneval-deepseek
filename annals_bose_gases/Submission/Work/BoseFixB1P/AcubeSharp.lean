import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1P.FDerivBoxScale
import Submission.Work.ESYStage.neuMode_integral_zero
import Submission.Work.SmallBoxA0.boxNeumann3_deriv_parseval
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sharp mean-free Poincaré inequality on the centred cube

`Work.BoseFixB1P.acubeSharp`: for `a > 0` and a smooth `u` with `∫_{acube a} u = 0`,

    `π²/a² · ∫_{acube a} u² ≤ ∑_k ∫_{acube a} (∂_k u)²`.

The constant is sharp (first non-zero Neumann eigenvalue of the cube of side `a`).  The proof
combines the two Parseval identities of the corpus:
`Work.SmallBoxModeParseval.acube_parseval_boxNeumann3` (L²-norm of `u` against the Neumann cosine
basis) and the mixed-basis `HasSum` Parseval `Work.SmallBoxA0.acube_parseval_mixed` applied to the
partial derivatives, together with the integration by parts
`Work.SmallBoxA0.acube_mode_deriv_ibp_sine`.  The comparison is termwise; summability is taken
from the `HasSum` statements (`ℝ`-valued `tsum` identities alone do not provide it).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators Real
open Submission.BoseGases
open Work.SmallBoxA0

namespace Work.BoseFixB1P

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The product Neumann mode evaluated at `cgEuc3.symm x` agrees with its evaluation at `x`. -/
lemma boxNeumann3_cgEuc3_symm (a : ℝ) (k : Fin 3 → ℕ) (x : E3) :
    boxNeumann3 a k (cgEuc3.symm x) = boxNeumann3 a k x := rfl

/-- The cosine coefficient may be written with either witness of the coordinate picture. -/
lemma boxCoeff_eq (a : ℝ) (u : E3 → ℝ) (k : Fin 3 → ℕ) :
    (∫ x in acube a, u x * boxNeumann3 a k x)
      = ∫ x in acube a, u x * boxNeumann3 a k (cgEuc3.symm x) :=
  setIntegral_congr_fun (acube_measurable a) (fun x _ => by rw [boxNeumann3_cgEuc3_symm])

/-- **Identification of the mixed-basis Parseval summand** with `((k m)π/a)²` times the coefficient
series of the cosine basis. -/
lemma mixedSummand_eq {a : ℝ} (ha : 0 < a) {u : E3 → ℝ} (hu : ContDiff ℝ 2 u)
    (m : Fin 3) (k : Fin 3 → ℕ) :
    (∫ x in acube a, fderiv ℝ u x (kcStdBasis m)
        * ∏ i : Fin 3, mixedMode a (decide (i = m)) (k i) (x i)) ^ 2
      / (∏ i : Fin 3, mixedWgt a (decide (i = m)) (k i))
      = ((k m : ℝ) * π / a) ^ 2
        * ((∫ x in acube a, u x * boxNeumann3 a k (cgEuc3.symm x)) ^ 2
            / ∏ j : Fin 3, (if k j = 0 then a else a / 2)) := by
  have hbf : (∫ x in acube a, u x * boxNeumann3 a k x)
      = ∫ x in acube a, u x * boxNeumann3 a k (cgEuc3.symm x) := by
    refine setIntegral_congr_fun (acube_measurable a) (fun x _ => ?_)
    rw [boxNeumann3_cgEuc3_symm]
  have hibp : (∫ x in acube a, fderiv ℝ u x (kcStdBasis m)
      * ∏ i : Fin 3, mixedMode a (decide (i = m)) (k i) (x i))
      = -(((k m : ℝ) * π / a))
        * (∫ x in acube a, u x * boxNeumann3 a k (cgEuc3.symm x)) := by
    rw [setIntegral_congr_fun (acube_measurable a)
      (fun x _ => by rw [Work.SmallBoxA0.prod_mixed_split (s := a) m k x])]
    rw [Work.SmallBoxA0.acube_mode_deriv_ibp_sine ha m k hu, hbf]
  rw [hibp]
  by_cases hkm : k m = 0
  · have hz : ((k m : ℝ) * π / a) = 0 := by rw [hkm]; simp
    rw [hz]
    simp
  · have h1 : (∏ i ∈ Finset.univ.erase m, mixedWgt a (decide (i = m)) (k i))
        = ∏ i ∈ Finset.univ.erase m, (if k i = 0 then a else a / 2) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hne : i ≠ m := Finset.ne_of_mem_erase hi
      have hdec : decide (i = m) = false := by simp [hne]
      rw [hdec, Work.SmallBoxA0.mixedWgt_false]
      rfl
    have h2 : mixedWgt a (decide (m = m)) (k m) = (if k m = 0 then a else a / 2) := by
      have hdec : decide (m = m) = true := by simp
      rw [hdec, Work.SmallBoxA0.mixedWgt_true, if_neg hkm]
    rw [← Finset.prod_erase_mul Finset.univ
          (f := fun i => mixedWgt a (decide (i = m)) (k i)) (Finset.mem_univ m),
      ← Finset.prod_erase_mul Finset.univ
          (f := fun j => (if k j = 0 then a else a / 2)) (Finset.mem_univ m), h1, h2]
    ring

/-- **The sharp mean-free Poincaré inequality on the cube `acube a`.** -/
theorem acubeSharp {a : ℝ} (ha : 0 < a) {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : ContDiff ℝ (⊤ : ENat) u)
    (hmean : (∫ x in acube a, u x) = 0) :
    Real.pi ^ 2 / a ^ 2 * (∫ x in acube a, (u x) ^ 2)
      ≤ ∑ k : Fin 3, ∫ x in acube a,
          (fderiv ℝ u x (kcStdBasis k)) ^ 2 := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hcont : Continuous (fun y : Fin 3 → ℝ => u (cgEuc3 y)) :=
    hu.continuous.comp (contDiff_cgEuc3 (n := (⊤ : ENat))).continuous
  have hcont_m : ∀ m : Fin 3, Continuous (fun x : E3 => fderiv ℝ u x (kcStdBasis m)) :=
    fun m => (hu2.continuous_fderiv (by norm_num)).clm_apply continuous_const
  set b : (Fin 3 → ℕ) → ℝ := fun k => ∫ x in acube a, u x * boxNeumann3 a k (cgEuc3.symm x)
    with hb
  set W : (Fin 3 → ℕ) → ℝ := fun k => ∏ j : Fin 3, (if k j = 0 then a else a / 2) with hW
  set f : (Fin 3 → ℕ) → ℝ := fun k => (b k) ^ 2 / W k with hf
  set lam : (Fin 3 → ℕ) → ℝ := fun k => ∑ m : Fin 3, ((k m : ℝ) * π / a) ^ 2 with hlam
  have hWpos : ∀ k, 0 < W k := by
    intro k
    rw [hW]
    refine Finset.prod_pos (fun j _ => ?_)
    by_cases hj : k j = 0
    · rw [if_pos hj]; exact ha
    · rw [if_neg hj]; positivity
  have hf0 : ∀ k, 0 ≤ f k := fun k => div_nonneg (sq_nonneg _) (le_of_lt (hWpos k))
  -- the L² Parseval identity
  have hpar : (∫ x in acube a, (u x) ^ 2) = ∑' k, f k := by
    rw [Submission.BoseGases.acube_parseval_boxNeumann3 ha hcont]
  -- the Dirichlet-form Parseval identity (tsum form, from the corpus)
  have hderiv : (∫ x in acube a, ∑ m : Fin 3, (fderiv ℝ u x (kcStdBasis m)) ^ 2)
      = ∑' k, lam k * f k := by
    rw [Work.SmallBoxA0.boxNeumann3_deriv_parseval ha hu2]
    refine tsum_congr (fun k => ?_)
    rw [boxCoeff_eq]
    have hWne : W k ≠ 0 := ne_of_gt (hWpos k)
    have hw : (∏ m : Fin 3, (if k m = 0 then (1 : ℝ) / a else 2 / a)) = (W k)⁻¹ := by
      rw [hW, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl (fun j _ => by
        by_cases hj : k j = 0
        · rw [if_pos hj, if_pos hj, one_div]
        · rw [if_neg hj, if_neg hj, inv_div])
    rw [hw, hlam, hf]
    ring
  -- the value of the partial sums
  have hint : (∫ x in acube a, ∑ m : Fin 3, (fderiv ℝ u x (kcStdBasis m)) ^ 2)
      = ∑ m : Fin 3, ∫ x in acube a, (fderiv ℝ u x (kcStdBasis m)) ^ 2 := by
    rw [MeasureTheory.integral_finsetSum]
    intro m _
    exact ((hcont_m m).pow 2).continuousOn.integrableOn_compact (acube_compact ha)
  -- summability of the `λ · f` family, from the mixed-basis `HasSum` Parsvals
  have hsum_m : ∀ m : Fin 3, Summable (fun k : Fin 3 → ℕ => ((k m : ℝ) * π / a) ^ 2 * f k) := by
    intro m
    have hh := (Work.SmallBoxA0.acube_parseval_mixed ha (fun i => decide (i = m))
      (hcont_m m)).summable
    refine hh.congr (fun k => ?_)
    rw [mixedSummand_eq ha hu2 m k, hf, hb, hW]
  have hsum_g : Summable (fun k : Fin 3 → ℕ => lam k * f k) := by
    have h : Summable (fun k : Fin 3 → ℕ => ∑ m : Fin 3, ((k m : ℝ) * π / a) ^ 2 * f k) :=
      summable_sum (fun m _ => hsum_m m)
    refine h.congr (fun k => ?_)
    rw [hlam, Finset.sum_mul]
  -- the termwise comparison
  have hpnt : ∀ k : Fin 3 → ℕ, Real.pi ^ 2 / a ^ 2 * f k ≤ lam k * f k := by
    intro k
    by_cases hk : k = 0
    · have hb0 : b k = 0 := by
        rw [hb, hk]
        have hpt : ∀ x : E3, boxNeumann3 a 0 (cgEuc3.symm x) = 1 := fun x => by
          rw [boxNeumann3_cgEuc3_symm, Work.ESYStage.boxNeumann3_zero_eq_one]
        simp only [hpt, mul_one]
        exact hmean
      rw [hf]
      simp [hb0]
    · obtain ⟨m, hm⟩ : ∃ m : Fin 3, k m ≠ 0 := by
        by_contra h
        exact hk (funext (fun j => not_not.mp (not_exists.mp h j)))
      have hkm1 : (1 : ℝ) ≤ (k m : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
      have hπa : 0 ≤ π / a := le_of_lt (div_pos Real.pi_pos ha)
      have h1 : π / a ≤ (k m : ℝ) * (π / a) := by nlinarith [hπa, hkm1]
      have h2 : (π / a) ^ 2 ≤ ((k m : ℝ) * (π / a)) ^ 2 := by nlinarith [h1, hπa]
      have h3 : Real.pi ^ 2 / a ^ 2 ≤ lam k := by
        rw [hlam]
        calc Real.pi ^ 2 / a ^ 2 = (π / a) ^ 2 := by rw [div_pow]
          _ ≤ ((k m : ℝ) * (π / a)) ^ 2 := h2
          _ = ((k m : ℝ) * π / a) ^ 2 := by ring
          _ ≤ ∑ i : Fin 3, ((k i : ℝ) * π / a) ^ 2 :=
              Finset.single_le_sum (f := fun i : Fin 3 => ((k i : ℝ) * π / a) ^ 2)
                (fun i _ => sq_nonneg _) (Finset.mem_univ m)
      have hfk := hf0 k
      nlinarith [h3, hfk]
  have hsum_f : Summable (fun k : Fin 3 → ℕ => Real.pi ^ 2 / a ^ 2 * f k) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (by positivity) (hf0 k)) hpnt hsum_g
  calc Real.pi ^ 2 / a ^ 2 * (∫ x in acube a, (u x) ^ 2)
      = Real.pi ^ 2 / a ^ 2 * ∑' k, f k := by rw [hpar]
    _ = ∑' k, Real.pi ^ 2 / a ^ 2 * f k := (tsum_mul_left).symm
    _ ≤ ∑' k, lam k * f k := Summable.tsum_le_tsum hpnt hsum_f hsum_g
    _ = ∫ x in acube a, ∑ m : Fin 3, (fderiv ℝ u x (kcStdBasis m)) ^ 2 := hderiv.symm
    _ = ∑ m : Fin 3, ∫ x in acube a, (fderiv ℝ u x (kcStdBasis m)) ^ 2 := hint

end Work.BoseFixB1P
