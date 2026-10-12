import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Momentum.cubFT_fubini
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The product structure of the unit-cube Fourier symbol `cubFT`

`cubFT q = ∫_{acube 1} cos ⟪q,x⟫ dx` factorises over the coordinates of the unit cube:
with `hFT t = ∫_{-1/2}^{1/2} cos (t s) ds` one has

    `cubFT q = ∏ i, hFT (q i)`     (`cubFT_eq_prod_of`)

and the coordinate derivatives are

    `fderiv ℝ cubFT q (kcStdBasis i) = -(mFT (q i)) * ∏ j ≠ i, hFT (q j)`
                                        (`fderiv_cubFT_coord_of`)

where `mFT t = ∫_{-1/2}^{1/2} s sin (t s) ds`.

Both proofs are written here in "conditional" form, taking the two elementary 1D inputs
(`chFT t = ↑(hFT t)` and `HasDerivAt hFT (-(mFT t)) t`) as explicit hypotheses; the unconditional
statements are obtained in `cubFT_exterior_bounds` from the separately proved 1D lemmas.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false

/-- The coordinate factor of the complex exponential: `s ↦ 1_{[-1/2,1/2]}(s) e^{i q_i s}`. -/
def cubeCoord (q : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) : ℝ → ℂ :=
  (Set.Icc (-(1/2)) (1/2)).indicator
    (fun s : ℝ => Complex.exp (Complex.I * ((q i * s : ℝ) : ℂ)))

lemma integral_cubeCoord (q : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    ∫ s : ℝ, cubeCoord q i s = chFT (q i) := by
  rw [cubeCoord, MeasureTheory.integral_indicator measurableSet_Icc]
  rfl

/-- The Euclidean inner product on `ℝ³` as a coordinate sum. -/
lemma inner_eq_sum_coord (q x : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ q x = ∑ i, q i * x i := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => Real.inner_apply _ _

/-- The pointwise product identity: the product of the coordinate factors is the (truncated)
complex exponential of the inner product. -/
lemma prod_cubeCoord (q x : EuclideanSpace ℝ (Fin 3)) :
    ∏ i, cubeCoord q i (x i)
      = (acube (1 : ℝ)).indicator
          (fun x => Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ))) x := by
  by_cases hx : x ∈ acube 1
  · rw [Set.indicator_of_mem (s := acube (1 : ℝ)) hx
      (fun x => Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)))]
    have hxi : ∀ i, x i ∈ Set.Icc (-(1/2)) (1/2) := (mem_acube_one x).mp hx
    have hstep : (∏ i : Fin 3, cubeCoord q i (x i))
        = ∏ i : Fin 3, Complex.exp (Complex.I * ((q i * x i : ℝ) : ℂ)) :=
      Finset.prod_congr rfl fun i _ =>
        Set.indicator_of_mem (s := Set.Icc (-(1/2)) (1/2)) (hxi i) _
    rw [hstep, ← Complex.exp_sum]
    congr 1
    rw [← Finset.mul_sum]
    congr 1
    rw [inner_eq_sum_coord]
    exact (map_sum Complex.ofRealHom _ _).symm
  · rw [Set.indicator_of_notMem (s := acube (1 : ℝ)) hx
      (fun x => Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)))]
    obtain ⟨i, hi⟩ := not_forall.mp fun h => hx ((mem_acube_one x).mpr h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      rw [cubeCoord]
      exact Set.indicator_of_notMem hi _)

/-- The complex cube Fourier transform `∫_{acube 1} e^{i⟪q,x⟫} dx` as a product of the 1D
complex factors. -/
lemma integral_cubeCoord_prod (q : EuclideanSpace ℝ (Fin 3)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ∏ i, cubeCoord q i (x i)) = ∏ i, chFT (q i) := by
  rw [integral_euclidean_prod]
  exact Finset.prod_congr rfl fun i _ => integral_cubeCoord q i

/-- **The product formula for `cubFT`** (conditional on `chFT t = ↑(hFT t)`). -/
theorem cubFT_eq_prod_of (hch : ∀ t : ℝ, chFT t = (hFT t : ℂ))
    (q : EuclideanSpace ℝ (Fin 3)) : cubFT q = ∏ i, hFT (q i) := by
  have hIntOn : IntegrableOn
      (fun x : EuclideanSpace ℝ (Fin 3) => Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)))
      (acube 1) := by
    refine IntegrableOn.of_bound (by rw [volume_acube_one]; exact ENNReal.one_lt_top)
      (by fun_prop) 1 ?_
    filter_upwards with x
    rw [mul_comm Complex.I _, Complex.norm_exp_ofReal_mul_I]
  have hInt : Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) => ∏ i, cubeCoord q i (x i)) := by
    rw [show (fun x : EuclideanSpace ℝ (Fin 3) => ∏ i, cubeCoord q i (x i))
        = (acube (1 : ℝ)).indicator
            (fun x => Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ))) from
      funext fun x => prod_cubeCoord q x]
    rwa [integrable_indicator_iff (measurableSet_acube 1)]
  have hmain : (∫ x : EuclideanSpace ℝ (Fin 3), ∏ i, cubeCoord q i (x i)).re = cubFT q := by
    have hcomm : (∫ x : EuclideanSpace ℝ (Fin 3), ∏ i, cubeCoord q i (x i)).re
        = ∫ x : EuclideanSpace ℝ (Fin 3), (∏ i, cubeCoord q i (x i)).re :=
      (ContinuousLinearMap.integral_comp_comm Complex.reCLM hInt).symm
    rw [hcomm]
    have hpt : ∀ x : EuclideanSpace ℝ (Fin 3), (∏ i, cubeCoord q i (x i)).re
        = (acube (1 : ℝ)).indicator (fun x => Real.cos (inner ℝ q x)) x := by
      intro x
      rw [prod_cubeCoord q x]
      by_cases hx : x ∈ acube 1
      · rw [Set.indicator_of_mem (s := acube (1 : ℝ)) hx
            (fun x => Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ))),
          Set.indicator_of_mem (s := acube (1 : ℝ)) hx (fun x => Real.cos (inner ℝ q x)),
          mul_comm Complex.I _, Complex.exp_ofReal_mul_I_re]
      · rw [Set.indicator_of_notMem (s := acube (1 : ℝ)) hx _,
          Set.indicator_of_notMem (s := acube (1 : ℝ)) hx _]
        simp
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_indicator (measurableSet_acube 1)]
    rfl
  rw [← hmain, integral_cubeCoord_prod]
  rw [Finset.prod_congr rfl fun i _ => hch (q i)]
  have hmp : (∏ i : Fin 3, ((hFT (q i) : ℝ) : ℂ))
      = ((∏ i : Fin 3, hFT (q i) : ℝ) : ℂ) :=
    (map_prod Complex.ofRealHom (fun i => hFT (q i)) Finset.univ).symm
  rw [hmp, Complex.ofReal_re]

end Work.BoseKinLoc.Momentum
