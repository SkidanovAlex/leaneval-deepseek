import Submission.FUP.Dbar2Calc
import Submission.Commons.Topology.CompactSupport.hasCompactSupport_pi
import Submission.Commons.Measure.EuclideanSpace.integral_fderiv_mul_weighted_eq_neg_nocompact

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# `∂̄`-closed smooth `(0,1)`-forms are weakly `∂̄₂`-closed, and two integration-by-parts lemmas
without compact support on the first factor

The main result of this module is

  `dbarWeak2_of_dbarClosed` : `DbarClosed η → DbarWeak2 φ (liftForm η) 0`

for a smooth `(0,1)`-form `η` (NO compact-support hypothesis), which is precisely the hypothesis
`hv0` of `Submission.FUP.exists_L2_solution_of_dbar` (Hörmander's `L²` existence theorem for
`∂̄`).  The compactly supported case was proved earlier in
`Submission.FUP.dbarWeak2_of_dbarClosed_of_hasCompactSupport`; the general case is obtained from
the weighted integration-by-parts identity for `∂̄₂`, which is applied with the *test form* as the
compactly supported factor.

To make this work we need the two integration-by-parts identities without a compact-support
hypothesis on the FIRST factor:

* `integral_partialZ_mul_weighted_eq_neg_nocompact` — the `∂_j`-version, obtained by linearity
  from the commons lemma
  `Commons.Measure.EuclideanSpace.integral_fderiv_mul_weighted_eq_neg_nocompact` (which requires
  compact support only of the second factor), using
  `partialZ j F z = (D_{e_j}F − i D_{i e_j}F)/2`;
* `integral_inner_dbar2_eq_nocompact` — the `(0,1) → (0,2)` version, with only the `(0,2)`-form
  compactly supported.
-/

namespace Submission.FUP

variable {d : ℕ}


noncomputable section
theorem integral_partialZ_mul_weighted_eq_neg_nocompact {d : ℕ} {F G ψ : (Fin d → ℂ) → ℂ}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) (hψ : ContDiff ℝ 1 ψ)
    (hsG : HasCompactSupport G) (j : Fin d) :
    (∫ z, partialZ j F z * G z * Complex.exp (-(ψ z)))
      = - (∫ z, F z * partialZ j G z * Complex.exp (-(ψ z)))
        + (∫ z, F z * G z * partialZ j ψ z * Complex.exp (-(ψ z))) := by
  have hψe : Continuous (fun z : (Fin d → ℂ) => Complex.exp (-(ψ z))) :=
    Complex.continuous_exp.comp hψ.continuous.neg
  have hF1 : Continuous (fun z : (Fin d → ℂ) => fderiv ℝ F z (Pi.single j (1 : ℂ))) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hF2 : Continuous (fun z : (Fin d → ℂ) => fderiv ℝ F z (Pi.single j Complex.I)) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hG1 : Continuous (fun z : (Fin d → ℂ) => fderiv ℝ G z (Pi.single j (1 : ℂ))) :=
    (hG.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hG2 : Continuous (fun z : (Fin d → ℂ) => fderiv ℝ G z (Pi.single j Complex.I)) :=
    (hG.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hψ1 : Continuous (fun z : (Fin d → ℂ) => fderiv ℝ ψ z (Pi.single j (1 : ℂ))) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hψ2 : Continuous (fun z : (Fin d → ℂ) => fderiv ℝ ψ z (Pi.single j Complex.I)) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have iE1 : Integrable (fun z : (Fin d → ℂ) =>
      fderiv ℝ F z (Pi.single j (1 : ℂ)) * G z * Complex.exp (-(ψ z))) :=
    ((hF1.mul hG.continuous).mul hψe).integrable_of_hasCompactSupport
      ((hsG.mul_left (f := fun z => fderiv ℝ F z (Pi.single j (1 : ℂ)))).mul_right
        (f' := fun z => Complex.exp (-(ψ z))))
  have iE2 : Integrable (fun z : (Fin d → ℂ) =>
      fderiv ℝ F z (Pi.single j Complex.I) * G z * Complex.exp (-(ψ z))) :=
    ((hF2.mul hG.continuous).mul hψe).integrable_of_hasCompactSupport
      ((hsG.mul_left (f := fun z => fderiv ℝ F z (Pi.single j Complex.I))).mul_right
        (f' := fun z => Complex.exp (-(ψ z))))
  have iA1 : Integrable (fun z : (Fin d → ℂ) =>
      F z * fderiv ℝ G z (Pi.single j (1 : ℂ)) * Complex.exp (-(ψ z))) :=
    ((hF.continuous.mul hG1).mul hψe).integrable_of_hasCompactSupport
      (((hsG.fderiv_apply ℝ (Pi.single j (1 : ℂ))).mul_left (f := F)).mul_right
        (f' := fun z => Complex.exp (-(ψ z))))
  have iA2 : Integrable (fun z : (Fin d → ℂ) =>
      F z * fderiv ℝ G z (Pi.single j Complex.I) * Complex.exp (-(ψ z))) :=
    ((hF.continuous.mul hG2).mul hψe).integrable_of_hasCompactSupport
      (((hsG.fderiv_apply ℝ (Pi.single j Complex.I)).mul_left (f := F)).mul_right
        (f' := fun z => Complex.exp (-(ψ z))))
  have iB1' : Integrable (fun z : (Fin d → ℂ) =>
      (F z * fderiv ℝ ψ z (Pi.single j (1 : ℂ))) * G z * Complex.exp (-(ψ z))) :=
    (((hF.continuous.mul hψ1).mul hG.continuous).mul hψe).integrable_of_hasCompactSupport
      ((hsG.mul_left (f := fun z => F z * fderiv ℝ ψ z (Pi.single j (1 : ℂ)))).mul_right
        (f' := fun z => Complex.exp (-(ψ z))))
  have iB1 : Integrable (fun z : (Fin d → ℂ) => F z * G z * fderiv ℝ ψ z (Pi.single j (1 : ℂ))
      * Complex.exp (-(ψ z))) :=
    iB1'.congr (Filter.Eventually.of_forall fun z => by ring)
  have iB2' : Integrable (fun z : (Fin d → ℂ) =>
      (F z * fderiv ℝ ψ z (Pi.single j Complex.I)) * G z * Complex.exp (-(ψ z))) :=
    (((hF.continuous.mul hψ2).mul hG.continuous).mul hψe).integrable_of_hasCompactSupport
      ((hsG.mul_left (f := fun z => F z * fderiv ℝ ψ z (Pi.single j Complex.I))).mul_right
        (f' := fun z => Complex.exp (-(ψ z))))
  have iB2 : Integrable (fun z : (Fin d → ℂ) => F z * G z * fderiv ℝ ψ z (Pi.single j Complex.I)
      * Complex.exp (-(ψ z))) :=
    iB2'.congr (Filter.Eventually.of_forall fun z => by ring)
  have hE : (∫ z, partialZ j F z * G z * Complex.exp (-(ψ z)))
      = (∫ z, fderiv ℝ F z (Pi.single j (1 : ℂ)) * G z * Complex.exp (-(ψ z))) / 2
        - Complex.I * ((∫ z, fderiv ℝ F z (Pi.single j Complex.I) * G z
            * Complex.exp (-(ψ z))) / 2) := by
    rw [show (fun z : (Fin d → ℂ) => partialZ j F z * G z * Complex.exp (-(ψ z)))
        = fun z => (fderiv ℝ F z (Pi.single j (1 : ℂ)) * G z * Complex.exp (-(ψ z))
            - Complex.I * (fderiv ℝ F z (Pi.single j Complex.I) * G z
              * Complex.exp (-(ψ z)))) / 2 from by
      funext z; rw [partialZ]; ring]
    rw [integral_div, integral_sub iE1 (iE2.const_mul Complex.I), integral_const_mul]
    ring
  have hA : (∫ z, F z * partialZ j G z * Complex.exp (-(ψ z)))
      = (∫ z, F z * fderiv ℝ G z (Pi.single j (1 : ℂ)) * Complex.exp (-(ψ z))) / 2
        - Complex.I * ((∫ z, F z * fderiv ℝ G z (Pi.single j Complex.I)
            * Complex.exp (-(ψ z))) / 2) := by
    rw [show (fun z : (Fin d → ℂ) => F z * partialZ j G z * Complex.exp (-(ψ z)))
        = fun z => (F z * fderiv ℝ G z (Pi.single j (1 : ℂ)) * Complex.exp (-(ψ z))
            - Complex.I * (F z * fderiv ℝ G z (Pi.single j Complex.I)
              * Complex.exp (-(ψ z)))) / 2 from by
      funext z; rw [partialZ]; ring]
    rw [integral_div, integral_sub iA1 (iA2.const_mul Complex.I), integral_const_mul]
    ring
  have hB : (∫ z, F z * G z * partialZ j ψ z * Complex.exp (-(ψ z)))
      = (∫ z, F z * G z * fderiv ℝ ψ z (Pi.single j (1 : ℂ)) * Complex.exp (-(ψ z))) / 2
        - Complex.I * ((∫ z, F z * G z * fderiv ℝ ψ z (Pi.single j Complex.I)
            * Complex.exp (-(ψ z))) / 2) := by
    rw [show (fun z : (Fin d → ℂ) => F z * G z * partialZ j ψ z * Complex.exp (-(ψ z)))
        = fun z => (F z * G z * fderiv ℝ ψ z (Pi.single j (1 : ℂ)) * Complex.exp (-(ψ z))
            - Complex.I * (F z * G z * fderiv ℝ ψ z (Pi.single j Complex.I)
              * Complex.exp (-(ψ z)))) / 2 from by
      funext z; rw [partialZ]; ring]
    rw [integral_div, integral_sub iB1 (iB2.const_mul Complex.I), integral_const_mul]
    ring
  have h1 := Commons.Measure.EuclideanSpace.integral_fderiv_mul_weighted_eq_neg_nocompact (F := F) (G := G) (φ := ψ) hF hG hψ hsG (Pi.single j (1 : ℂ))
  have h2 := Commons.Measure.EuclideanSpace.integral_fderiv_mul_weighted_eq_neg_nocompact (F := F) (G := G) (φ := ψ) hF hG hψ hsG (Pi.single j Complex.I)
  rw [hE, hA, hB, h1, h2]
  ring
/-- **Weighted integration by parts for `∂̄₂`, without compact support on the first factor.** -/
theorem integral_inner_dbar2_eq_nocompact {Y : FormDu d → (Fin d → ℂ)}
    {Θ : FormDu d → (Fin d × Fin d → ℂ)} {φ : FormDu d → ℝ}
    (hY : ∀ j, ContDiff ℝ 1 (fun z => Y z j))
    (hΘ : ∀ i, ContDiff ℝ 1 (fun z => Θ z i))
    (hφ : ContDiff ℝ 1 φ)
    (hsΘ : ∀ i, HasCompactSupport (fun z => Θ z i)) :
    (∫ z, (∑ j, ∑ k, (partialZ k (fun w => Y w j) z - partialZ j (fun w => Y w k) z)
        * Θ z (j, k)) * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)
      = ∫ z, (∑ j, Y z j * dbarAdjoint2 φ Θ z j)
          * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume := by
  have hΦ : ContDiff ℝ 1 (fun z : FormDu d => ((φ z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφ
  have hΔc : ∀ j k, Continuous (fun z : FormDu d => Θ z (j, k) - Θ z (k, j)) :=
    fun j k => (hΘ (j, k)).continuous.sub (hΘ (k, j)).continuous
  have hΔs : ∀ j k, HasCompactSupport (fun z : FormDu d => Θ z (j, k) - Θ z (k, j)) :=
    fun j k => (hsΘ (j, k)).sub (hsΘ (k, j))
  have hIntP : ∀ j k : Fin d, Integrable (fun z => partialZ k (fun w => Y w j) z
      * (Θ z (j, k) - Θ z (k, j)) * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
    intro j k
    exact integrable_mul_cexp_neg hΦ.continuous
      ((continuous_partialZ (hY j) k).mul (hΔc j k))
      ((hΔs j k).mul_left (f := fun z => partialZ k (fun w => Y w j) z))
  have hIntA : ∀ j k : Fin d, Integrable (fun z => Y z j
      * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
      * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
    intro j k
    exact integrable_mul_cexp_neg hΦ.continuous
      ((hY j).continuous.mul (continuous_partialZ ((hΘ (j, k)).sub (hΘ (k, j))) k))
      ((hasCompactSupport_partialZ (hΔs j k) k).mul_left (f := fun z => Y z j))
  have hIntB : ∀ j k : Fin d, Integrable (fun z => Y z j * (Θ z (j, k) - Θ z (k, j))
      * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
      * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
    intro j k
    exact integrable_mul_cexp_neg hΦ.continuous
      (((hY j).continuous.mul (hΔc j k)).mul (continuous_partialZ hΦ k))
      (((hΔs j k).mul_left (f := fun z => Y z j)).mul_right
        (f' := fun z => partialZ k (fun w => ((φ w : ℝ) : ℂ)) z))
  have hip : ∀ j k : Fin d, (∫ z, partialZ k (fun w => Y w j) z * (Θ z (j, k) - Θ z (k, j))
        * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)
      = - (∫ z, Y z j * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
            * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)
        + (∫ z, Y z j * (Θ z (j, k) - Θ z (k, j)) * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
            * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume) := by
    intro j k
    exact integral_partialZ_mul_weighted_eq_neg_nocompact (hY j) ((hΘ (j, k)).sub (hΘ (k, j)))
      hΦ (hΔs j k) k
  have hIntj : ∀ j : Fin d, Integrable (fun z => (∑ k : Fin d, partialZ k (fun w => Y w j) z
      * (Θ z (j, k) - Θ z (k, j))) * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
    intro j
    rw [show (fun z : FormDu d => (∑ k : Fin d, partialZ k (fun w => Y w j) z
        * (Θ z (j, k) - Θ z (k, j))) * Complex.exp (-(((φ z : ℝ) : ℂ))))
        = fun z => ∑ k : Fin d, partialZ k (fun w => Y w j) z
            * (Θ z (j, k) - Θ z (k, j)) * Complex.exp (-(((φ z : ℝ) : ℂ))) from by
      funext z; rw [Finset.sum_mul]]
    exact integrable_finsetSum Finset.univ (fun k _ => hIntP j k)
  have hIntFA : ∀ j : Fin d, Integrable (fun z => ∑ k : Fin d, Y z j
      * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
      * Complex.exp (-(((φ z : ℝ) : ℂ)))) := fun j =>
    integrable_finsetSum Finset.univ (fun k _ => hIntA j k)
  have hIntFB : ∀ j : Fin d, Integrable (fun z => ∑ k : Fin d, Y z j
      * (Θ z (j, k) - Θ z (k, j)) * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
      * Complex.exp (-(((φ z : ℝ) : ℂ)))) := fun j =>
    integrable_finsetSum Finset.univ (fun k _ => hIntB j k)
  have hInt2j : ∀ j : Fin d, Integrable (fun z => Y z j * dbarAdjoint2 φ Θ z j
      * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
    intro j
    have hsadj : HasCompactSupport (fun z : FormDu d => dbarAdjoint2 φ Θ z j) :=
      hasCompactSupport_comp j
        (hasCompactSupport_dbarAdjoint2 (φ := φ)
          (Commons.Topology.CompactSupport.hasCompactSupport_pi (F := Θ) hsΘ))
    exact integrable_mul_cexp_neg hΦ.continuous
      ((hY j).continuous.mul ((continuous_apply j).comp (continuous_dbarAdjoint2 hΘ hΦ)))
      (hsadj.mul_left (f := fun z => Y z j))
  have hpt : ∀ j : Fin d, ∀ z : FormDu d,
      - (∑ k : Fin d, Y z j * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
          * Complex.exp (-(((φ z : ℝ) : ℂ))))
        + (∑ k : Fin d, Y z j * (Θ z (j, k) - Θ z (k, j))
          * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
          * Complex.exp (-(((φ z : ℝ) : ℂ))))
      = Y z j * dbarAdjoint2 φ Θ z j * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
    intro j z
    have hY' : Y z j * dbarAdjoint2 φ Θ z j
        = -(∑ k : Fin d, Y z j * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z)
          + (∑ k : Fin d, Y z j * (Θ z (j, k) - Θ z (k, j))
              * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z) := by
      rw [dbarAdjoint2, mul_neg, Finset.mul_sum]
      rw [show (∑ k : Fin d, Y z j * (partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
            - (Θ z (j, k) - Θ z (k, j)) * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z))
          = (∑ k : Fin d, Y z j * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z)
            - (∑ k : Fin d, Y z j * (Θ z (j, k) - Θ z (k, j))
                * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z) from by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring]
      rw [neg_sub]
      ring
    have hEfac : (-(∑ k : Fin d, Y z j * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z)
          + (∑ k : Fin d, Y z j * (Θ z (j, k) - Θ z (k, j))
              * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z)) * Complex.exp (-(((φ z : ℝ) : ℂ)))
        = -(∑ k : Fin d, Y z j * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
              * Complex.exp (-(((φ z : ℝ) : ℂ))))
          + (∑ k : Fin d, Y z j * (Θ z (j, k) - Θ z (k, j))
              * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
              * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
      rw [add_mul, neg_mul, Finset.sum_mul, Finset.sum_mul]
    rw [hY', hEfac]
  calc (∫ z, (∑ j, ∑ k, (partialZ k (fun w => Y w j) z - partialZ j (fun w => Y w k) z)
          * Θ z (j, k)) * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)
      = ∫ z, ∑ j : Fin d, (∑ k, partialZ k (fun w => Y w j) z
          * (Θ z (j, k) - Θ z (k, j))) * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [sum_dbar2_rearrange, Finset.sum_mul]
    _ = ∑ j : Fin d, ∫ z, (∑ k, partialZ k (fun w => Y w j) z
          * (Θ z (j, k) - Θ z (k, j))) * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume :=
        integral_finsetSum Finset.univ (fun j _ => hIntj j)
    _ = ∑ j : Fin d, ∑ k : Fin d, ∫ z, partialZ k (fun w => Y w j) z
          * (Θ z (j, k) - Θ z (k, j)) * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [show (fun z : FormDu d => (∑ k, partialZ k (fun w => Y w j) z
            * (Θ z (j, k) - Θ z (k, j))) * Complex.exp (-(((φ z : ℝ) : ℂ))))
            = fun z => ∑ k : Fin d, partialZ k (fun w => Y w j) z
                * (Θ z (j, k) - Θ z (k, j)) * Complex.exp (-(((φ z : ℝ) : ℂ))) from by
          funext z; rw [Finset.sum_mul]]
        exact integral_finsetSum Finset.univ (fun k _ => hIntP j k)
    _ = ∑ j : Fin d, ∑ k : Fin d, (-(∫ z, Y z j
            * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
            * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)
          + (∫ z, Y z j * (Θ z (j, k) - Θ z (k, j))
            * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
            * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)) := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => hip j k))
    _ = ∑ j : Fin d, (-(∫ z, ∑ k : Fin d, Y z j
            * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
            * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)
          + (∫ z, ∑ k : Fin d, Y z j * (Θ z (j, k) - Θ z (k, j))
            * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
            * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
          ← integral_finsetSum Finset.univ (fun k _ => hIntA j k),
          ← integral_finsetSum Finset.univ (fun k _ => hIntB j k)]
    _ = ∑ j : Fin d, ∫ z, Y z j * dbarAdjoint2 φ Θ z j
          * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← sub_eq_neg_add, ← integral_sub (hIntFB j) (hIntFA j)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [Pi.mul_apply]
        rw [sub_eq_neg_add]
        exact hpt j z
    _ = ∫ z, (∑ j : Fin d, Y z j * dbarAdjoint2 φ Θ z j)
          * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume := by
        rw [← integral_finsetSum Finset.univ (fun j _ => hInt2j j)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [Pi.mul_apply, Finset.sum_mul]

/-- `1 ≤ ∞` for the `ContDiff` order. -/
private lemma hle1' : (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top

/-- **A smooth `∂̄`-closed `(0,1)`-form is weakly `∂̄₂`-closed.**  No compact support hypothesis. -/
theorem dbarWeak2_of_dbarClosed {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {η : FormDu d → (Fin d → ℂ)} (hη : ∀ j, ContDiff ℝ ∞ (fun z => η z j))
    (hηm : MemLp (liftForm η) 2 (wtMeasure φ)) (hclosed : DbarClosed η) :
    DbarWeak2 φ (hηm.toLp (liftForm η)) 0 := by
  intro Ψ h1 h2 hΨ hθ
  have hΘ2 : ∀ i, ContDiff ℝ 1 (fun z => toFormFun2 Ψ z i) :=
    fun i => (contDiff_toFormFun2 h1 i).of_le hle1'
  have hsΘ : ∀ i, HasCompactSupport (fun z => toFormFun2 Ψ z i) := fun i =>
    (hasCompactSupport_toFormFun2 h2).comp_left
      (g := fun v : Fin d × Fin d → ℂ => v i) (by simp)
  have hY1 : ∀ j, ContDiff ℝ 1 (fun z => star (η z j)) := fun j =>
    (Complex.conjCLE.contDiff).comp ((hη j).of_le hle1')
  rw [inner_zero_right]
  have hB : inner ℂ (hθ.toLp (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ)))) (hηm.toLp (liftForm η))
      = ∫ z, (∑ j, η z j * star (dbarAdjoint2 φ (toFormFun2 Ψ) z j))
          * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
    rw [MeasureTheory.L2.inner_def]
    have hae : (fun z => inner ℂ ((hθ.toLp (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ)))
            : FormDu d → FormSpace d) z)
          ((hηm.toLp (liftForm η) : FormDu d → FormSpace d) z))
        =ᵐ[wtMeasure φ] (fun z => inner ℂ (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ)) z)
          (liftForm η z)) := by
      filter_upwards [MemLp.coeFn_toLp hθ, MemLp.coeFn_toLp hηm] with z hz1 hz2
      rw [hz1, hz2]
    refine (integral_congr_ae hae).trans ?_
    · rw [integral_wtMeasure hφ.continuous]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      change Real.exp (-(φ z)) • inner ℂ (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ)) z) (liftForm η z)
        = (∑ j, η z j * star (dbarAdjoint2 φ (toFormFun2 Ψ) z j))
          * Complex.exp (-(((φ z : ℝ) : ℂ)))
      rw [PiLp.inner_apply]
      simp only [liftForm_apply, RCLike.inner_apply, starRingEnd_apply, Complex.real_smul,
        Complex.ofReal_exp, Complex.ofReal_neg]
      ring
  rw [hB]
  have hstar : star (∫ z, (∑ j, η z j * star (dbarAdjoint2 φ (toFormFun2 Ψ) z j))
        * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)
      = ∫ z, (∑ j, star (η z j) * dbarAdjoint2 φ (toFormFun2 Ψ) z j)
          * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume := by
    rw [integral_star_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    calc star ((∑ j, η z j * star (dbarAdjoint2 φ (toFormFun2 Ψ) z j))
          * Complex.exp (-(((φ z : ℝ) : ℂ))))
        = star (Complex.exp (-(((φ z : ℝ) : ℂ))))
            * star (∑ j, η z j * star (dbarAdjoint2 φ (toFormFun2 Ψ) z j)) := star_mul _ _
      _ = Complex.exp (-(((φ z : ℝ) : ℂ)))
            * (∑ j, star (η z j * star (dbarAdjoint2 φ (toFormFun2 Ψ) z j))) := by
          rw [star_cexp_neg, star_sum]
      _ = Complex.exp (-(((φ z : ℝ) : ℂ)))
            * (∑ j, star (η z j) * dbarAdjoint2 φ (toFormFun2 Ψ) z j) := by
          rw [show (∑ j, star (η z j * star (dbarAdjoint2 φ (toFormFun2 Ψ) z j)))
              = ∑ j, star (η z j) * dbarAdjoint2 φ (toFormFun2 Ψ) z j from ?_]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [star_mul, star_star]
          ring
      _ = (∑ j, star (η z j) * dbarAdjoint2 φ (toFormFun2 Ψ) z j)
            * Complex.exp (-(((φ z : ℝ) : ℂ))) := by ring
  have hL : (∫ z, (∑ j, ∑ k, (partialZ k (fun w => star (η w j)) z
        - partialZ j (fun w => star (η w k)) z) * toFormFun2 Ψ z (j, k))
        * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume) = 0 := by
    have hpt : (fun z => (∑ j, ∑ k, (partialZ k (fun w => star (η w j)) z
          - partialZ j (fun w => star (η w k)) z) * toFormFun2 Ψ z (j, k))
          * Complex.exp (-(((φ z : ℝ) : ℂ)))) = fun _ => (0 : ℂ) := by
      funext z
      have hcl : ∀ j k : Fin d,
          partialZbar k (fun w => η w j) z - partialZbar j (fun w => η w k) z = 0 :=
        fun j k => congrFun (congrFun (congrFun hclosed z) j) k
      rw [Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun k _ => ?_)), zero_mul]
      rw [← star_partialZbar, ← star_partialZbar, ← star_sub, hcl j k, star_zero, zero_mul]
    rw [hpt]
    simp
  have hibp : (∫ z, (∑ j, star (η z j) * dbarAdjoint2 φ (toFormFun2 Ψ) z j)
        * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume) = 0 := by
    rw [← integral_inner_dbar2_eq_nocompact (Y := fun z j => star (η z j)) (Θ := toFormFun2 Ψ)
      hY1 hΘ2 hφ hsΘ]
    exact hL
  exact star_injective (by rw [hstar, hibp, star_zero])


end

end Submission.FUP
