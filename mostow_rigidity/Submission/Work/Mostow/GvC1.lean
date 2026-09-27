import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.NatMeasure
import Submission.Work.Mostow.visualBasic
import Submission.Work.Mostow.poissonBaseLowerBound
import Submission.Work.Mostow.PfunBoundSph
import Submission.Work.Mostow.BCGBlocksContinuous
import Submission.Work.Mostow.HasFDerivProdSmul

/-!
# `GvC1`: regularity of the BCG gradient field `Gv` and its Fréchet derivative `DGv`

`Gv n φ x y = ∫ ξ, pfun n x ξ • gradB n (φ ξ) y ∂(sigma n)` is the `y`-gradient of the
barycentre functional `Phi n φ x ·` of the pushed-forward visual measure, and `DGv n φ x y` is
the integral of its (formal) joint derivative with respect to `(x,y)`.

The main results of this file are

* `hasFDerivAt_Gv` : at every point `p = (x,y)` the map `p ↦ Gv n φ p.1 p.2` has Fréchet
  derivative `DGv n φ p.1 p.2`;
* `continuous_DGv` : the map `p ↦ DGv n φ p.1 p.2` is continuous;

and together they give `GvC1`, the `C¹`-regularity statement.

Both are proved by differentiating/integrating under the integral sign against the finite
measure `sigma n` (which is carried by the sphere): the parametric differentiation lemma
`hasFDerivAt_integral_of_dominated_of_fderiv_le` and the parametric continuity lemma
`continuousOn_of_dominated`.  The only measure-theoretic inputs are that `sigma n (Sph n)ᶜ = 0`
(so `Sph n` is the effective domain of integration) and that `φ` is a.e. measurable for
`sigma n` (a consequence of the continuity of `φ` on the sphere).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ## The two integrands -/

/-- The `ξ`-integrand of `Gv n φ p`. -/
private def Wv (n : ℕ) (φ : E n → E n) (p : E n × E n) (ξ : E n) : E n :=
  pfun n p.1 ξ • gradB n (φ ξ) p.2

/-- The `ξ`-integrand of `DGv n φ p`. -/
private def DWv (n : ℕ) (φ : E n → E n) (p : E n × E n) (ξ : E n) : (E n × E n) →L[ℝ] E n :=
  ((dpfun n p.1 ξ).smulRight (gradB n (φ ξ) p.2)) ∘L
      ContinuousLinearMap.fst ℝ (E n) (E n) +
    (pfun n p.1 ξ • hessB n (φ ξ) p.2) ∘L
      ContinuousLinearMap.snd ℝ (E n) (E n)

/-! ## `sigma n`: finiteness and support -/

/-- `sigma n` is a finite measure (it is `(sphM n univ)⁻¹ • sphM n` and `sphM n` is finite). -/
private theorem sigma_finite (n : ℕ) : IsFiniteMeasure (sigma n) := by
  rw [isFiniteMeasure_iff, sigma_eq_smul_sphM, Measure.smul_apply, smul_eq_mul]
  refine lt_of_le_of_lt ?_ ENNReal.one_lt_top
  have hle : (sphM n Set.univ)⁻¹ * sphM n Set.univ ≤ 1 := by
    by_cases h : sphM n Set.univ = 0
    · rw [h]; simp
    · rw [ENNReal.inv_mul_cancel h (sphM_univ_ne_top n)]
  exact hle

/-- `sigma n` is carried by the unit sphere. -/
private lemma ae_mem_Sph (n : ℕ) : ∀ᵐ ξ ∂(sigma n), ξ ∈ Sph n := by
  rw [MeasureTheory.ae_iff]
  simpa [Set.compl_def] using sigma_compl_sphere n

/-- A function whose restriction to the sphere is continuous is a.e. strongly measurable for
`sigma n` (which is carried by the sphere). -/
private lemma aes_of_continuous_subtype (n : ℕ) {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] {f : E n → X}
    (hf : Continuous fun η : ↥(Sph n) => f η) : AEStronglyMeasurable f (sigma n) := by
  rw [← Measure.restrict_eq_self_of_ae_mem (ae_mem_Sph n)]
  exact ((continuousOn_iff_continuous_domRestrict).mpr hf).aestronglyMeasurable_of_isCompact
    (isCompact_sphere (0 : E n) 1) Metric.isClosed_sphere.measurableSet

/-! ## Continuity of the building blocks in the sphere variable -/

private lemma continuous_pfun_subtype (n : ℕ) (x : E n) :
    Continuous (fun η : ↥(Sph n) => pfun n x η) := by
  rw [show (fun η : ↥(Sph n) => pfun n x η)
      = fun η : ↥(Sph n) => (tpart x - inner ℝ x (η : E n)) ^ (-((n : ℝ) - 1)) from rfl]
  exact Continuous.rpow_const
    (continuous_const.sub (continuous_const.inner continuous_subtype_val))
    (fun η => Or.inl (ne_of_gt (busemann_arg_pos η.1 η.2 x)))

private lemma continuous_dpfun_subtype (n : ℕ) (x : E n) :
    Continuous (fun η : ↥(Sph n) => dpfun n x η) := by
  rw [show (fun η : ↥(Sph n) => dpfun n x η)
      = fun η : ↥(Sph n) =>
          (-((n : ℝ) - 1) * (tpart x - inner ℝ x (η : E n)) ^ (-((n : ℝ) - 1) - 1)) •
            ((tpart x)⁻¹ • innerSL ℝ x - innerSL ℝ (η : E n)) from rfl]
  have hs : Continuous (fun η : ↥(Sph n) =>
      -((n : ℝ) - 1) * (tpart x - inner ℝ x (η : E n)) ^ (-((n : ℝ) - 1) - 1)) :=
    continuous_const.mul (Continuous.rpow_const
      (continuous_const.sub (continuous_const.inner continuous_subtype_val))
      (fun η => Or.inl (ne_of_gt (busemann_arg_pos η.1 η.2 x))))
  have hv : Continuous (fun η : ↥(Sph n) =>
      (tpart x)⁻¹ • innerSL ℝ x - innerSL ℝ (η : E n)) :=
    continuous_const.sub ((innerSL ℝ).continuous.comp continuous_subtype_val)
  exact hs.smul hv

private lemma continuous_gradB_subtype (n : ℕ) (y : E n) :
    Continuous (fun η : ↥(Sph n) => gradB n η y) := by
  rw [show (fun η : ↥(Sph n) => gradB n η y)
      = fun η : ↥(Sph n) =>
          (tpart y - inner ℝ y (η : E n))⁻¹ • ((tpart y)⁻¹ • y - (η : E n)) from rfl]
  exact ((continuous_const.sub (continuous_const.inner continuous_subtype_val)).inv₀
    (fun η => ne_of_gt (busemann_arg_pos η.1 η.2 y))).smul
    (continuous_const.sub continuous_subtype_val)

private lemma continuous_hessB_subtype (n : ℕ) (y : E n) :
    Continuous (fun η : ↥(Sph n) => hessB n η y) := by
  rw [show (fun η : ↥(Sph n) => hessB n η y)
      = fun η : ↥(Sph n) =>
          (tpart y - inner ℝ y (η : E n))⁻¹ •
              ((tpart y)⁻¹ • (1 : E n →L[ℝ] E n) -
                ((tpart y) ^ 3)⁻¹ • (innerSL ℝ y).smulRight y) -
            (innerSL ℝ (gradB n η y)).smulRight (gradB n η y) from rfl]
  have hinner : Continuous (fun η : ↥(Sph n) =>
      (tpart y)⁻¹ • (1 : E n →L[ℝ] E n) -
        ((tpart y) ^ 3)⁻¹ • (innerSL ℝ y).smulRight y) :=
    continuous_const.sub continuous_const
  have hfirst : Continuous (fun η : ↥(Sph n) =>
      (tpart y - inner ℝ y (η : E n))⁻¹ •
        ((tpart y)⁻¹ • (1 : E n →L[ℝ] E n) -
          ((tpart y) ^ 3)⁻¹ • (innerSL ℝ y).smulRight y)) :=
    ((continuous_const.sub (continuous_const.inner continuous_subtype_val)).inv₀
      (fun η => ne_of_gt (busemann_arg_pos η.1 η.2 y))).smul hinner
  have hlast : Continuous (fun η : ↥(Sph n) =>
      (innerSL ℝ (gradB n η y)).smulRight (gradB n η y)) :=
    (continuous_innerSL_smulRight n).comp (continuous_gradB_subtype n y)
  exact hfirst.sub hlast

private lemma continuous_phi_subtype (n : ℕ) (φ : E n → E n) (hcont : ContinuousOn φ (Sph n)) :
    Continuous (fun η : ↥(Sph n) => φ η) :=
  (continuousOn_iff_continuous_domRestrict).mp hcont

private lemma continuous_gradB_phi_subtype (n : ℕ) (φ : E n → E n)
    (hbij : Set.BijOn φ (Sph n) (Sph n)) (hcont : ContinuousOn φ (Sph n)) (y : E n) :
    Continuous (fun η : ↥(Sph n) => gradB n (φ η) y) := by
  have hphi : Continuous (fun η : ↥(Sph n) => φ η) := continuous_phi_subtype n φ hcont
  rw [show (fun η : ↥(Sph n) => gradB n (φ η) y)
      = fun η : ↥(Sph n) =>
          (tpart y - inner ℝ y (φ η))⁻¹ • ((tpart y)⁻¹ • y - φ η) from rfl]
  exact ((continuous_const.sub (continuous_const.inner hphi)).inv₀
    (fun η => ne_of_gt (busemann_arg_pos (φ η) (hbij.1 η.2) y))).smul
    (continuous_const.sub hphi)

private lemma continuous_hessB_phi_subtype (n : ℕ) (φ : E n → E n)
    (hbij : Set.BijOn φ (Sph n) (Sph n)) (hcont : ContinuousOn φ (Sph n)) (y : E n) :
    Continuous (fun η : ↥(Sph n) => hessB n (φ η) y) := by
  have hphi : Continuous (fun η : ↥(Sph n) => φ η) := continuous_phi_subtype n φ hcont
  rw [show (fun η : ↥(Sph n) => hessB n (φ η) y)
      = fun η : ↥(Sph n) =>
          (tpart y - inner ℝ y (φ η))⁻¹ •
              ((tpart y)⁻¹ • (1 : E n →L[ℝ] E n) -
                ((tpart y) ^ 3)⁻¹ • (innerSL ℝ y).smulRight y) -
            (innerSL ℝ (gradB n (φ η) y)).smulRight (gradB n (φ η) y) from rfl]
  have hinner : Continuous (fun η : ↥(Sph n) =>
      (tpart y)⁻¹ • (1 : E n →L[ℝ] E n) -
        ((tpart y) ^ 3)⁻¹ • (innerSL ℝ y).smulRight y) :=
    continuous_const.sub continuous_const
  have hfirst : Continuous (fun η : ↥(Sph n) =>
      (tpart y - inner ℝ y (φ η))⁻¹ •
        ((tpart y)⁻¹ • (1 : E n →L[ℝ] E n) -
          ((tpart y) ^ 3)⁻¹ • (innerSL ℝ y).smulRight y)) :=
    ((continuous_const.sub (continuous_const.inner hphi)).inv₀
      (fun η => ne_of_gt (busemann_arg_pos (φ η) (hbij.1 η.2) y))).smul hinner
  have hlast : Continuous (fun η : ↥(Sph n) =>
      (innerSL ℝ (gradB n (φ η) y)).smulRight (gradB n (φ η) y)) :=
    (continuous_innerSL_smulRight n).comp
      (continuous_gradB_phi_subtype n φ hbij hcont y)
  exact hfirst.sub hlast

/-! ## Continuity in the point variable, for `ξ` on the sphere -/

private lemma continuous_pfun_prod (n : ℕ) (ξ : E n) (hξ : ξ ∈ Sph n) :
    Continuous (fun p : E n × E n => pfun n p.1 ξ) := by
  rw [show (fun p : E n × E n => pfun n p.1 ξ)
      = fun p : E n × E n => (tpart p.1 - inner ℝ p.1 ξ) ^ (-((n : ℝ) - 1)) from rfl]
  exact Continuous.rpow_const
    ((continuous_tpart.comp continuous_fst).sub (continuous_fst.inner continuous_const))
    (fun p => Or.inl (ne_of_gt (busemann_arg_pos ξ hξ p.1)))

private lemma continuous_dpfun_prod (n : ℕ) (ξ : E n) (hξ : ξ ∈ Sph n) :
    Continuous (fun p : E n × E n => dpfun n p.1 ξ) := by
  rw [show (fun p : E n × E n => dpfun n p.1 ξ)
      = fun p : E n × E n =>
          (-((n : ℝ) - 1) * (tpart p.1 - inner ℝ p.1 ξ) ^ (-((n : ℝ) - 1) - 1)) •
            ((tpart p.1)⁻¹ • innerSL ℝ p.1 - innerSL ℝ ξ) from rfl]
  have hs : Continuous (fun p : E n × E n =>
      -((n : ℝ) - 1) * (tpart p.1 - inner ℝ p.1 ξ) ^ (-((n : ℝ) - 1) - 1)) :=
    continuous_const.mul (Continuous.rpow_const
      ((continuous_tpart.comp continuous_fst).sub (continuous_fst.inner continuous_const))
      (fun p => Or.inl (ne_of_gt (busemann_arg_pos ξ hξ p.1))))
  have hv : Continuous (fun p : E n × E n =>
      (tpart p.1)⁻¹ • innerSL ℝ p.1 - innerSL ℝ ξ) :=
    (((continuous_tpart.comp continuous_fst).inv₀
      (fun p => (tpart_pos p.1).ne')).smul ((innerSL ℝ).continuous.comp continuous_fst)).sub
      continuous_const
  exact hs.smul hv

private lemma continuous_gradB_prod (n : ℕ) (φ : E n → E n) (hbij : Set.BijOn φ (Sph n) (Sph n))
    (hd2 : ∀ (ξ : E n), ξ ∈ Sph n →
      ∀ y : E n, HasFDerivAt (fun y => gradB n ξ y) (hessB n ξ y) y)
    (ξ : E n) (hξ : ξ ∈ Sph n) :
    Continuous (fun p : E n × E n => gradB n (φ ξ) p.2) :=
  (continuous_iff_continuousAt.mpr
    (fun y => (hd2 (φ ξ) (hbij.1 hξ) y).continuousAt)).comp continuous_snd

private lemma continuous_hessB_prod (n : ℕ) (φ : E n → E n) (hbij : Set.BijOn φ (Sph n) (Sph n))
    (hd2 : ∀ (ξ : E n), ξ ∈ Sph n →
      ∀ y : E n, HasFDerivAt (fun y => gradB n ξ y) (hessB n ξ y) y)
    (ξ : E n) (hξ : ξ ∈ Sph n) :
    Continuous (fun p : E n × E n => hessB n (φ ξ) p.2) := by
  have hgrad : Continuous (fun y : E n => gradB n (φ ξ) y) :=
    continuous_iff_continuousAt.mpr (fun y => (hd2 (φ ξ) (hbij.1 hξ) y).continuousAt)
  rw [show (fun p : E n × E n => hessB n (φ ξ) p.2)
      = fun p : E n × E n =>
          (tpart p.2 - inner ℝ p.2 (φ ξ))⁻¹ •
              ((tpart p.2)⁻¹ • (1 : E n →L[ℝ] E n) -
                ((tpart p.2) ^ 3)⁻¹ • (innerSL ℝ p.2).smulRight p.2) -
            (innerSL ℝ (gradB n (φ ξ) p.2)).smulRight (gradB n (φ ξ) p.2) from rfl]
  have hbase : Continuous (fun p : E n × E n => tpart p.2 - inner ℝ p.2 (φ ξ)) :=
    (continuous_tpart.comp continuous_snd).sub (continuous_snd.inner continuous_const)
  have hinner : Continuous (fun p : E n × E n =>
      (tpart p.2)⁻¹ • (1 : E n →L[ℝ] E n) -
        ((tpart p.2) ^ 3)⁻¹ • (innerSL ℝ p.2).smulRight p.2) :=
    (((continuous_tpart.comp continuous_snd).inv₀
        (fun p => (tpart_pos p.2).ne')).smul
        (continuous_const : Continuous (fun _ : E n × E n => (1 : E n →L[ℝ] E n)))).sub
      ((((continuous_tpart.comp continuous_snd).pow 3).inv₀
        (fun p => pow_ne_zero 3 (tpart_pos p.2).ne')).smul
        ((continuous_innerSL_smulRight n).comp continuous_snd))
  have hfirst : Continuous (fun p : E n × E n =>
      (tpart p.2 - inner ℝ p.2 (φ ξ))⁻¹ •
        ((tpart p.2)⁻¹ • (1 : E n →L[ℝ] E n) -
          ((tpart p.2) ^ 3)⁻¹ • (innerSL ℝ p.2).smulRight p.2)) :=
    (hbase.inv₀ (fun p => ne_of_gt (busemann_arg_pos (φ ξ) (hbij.1 hξ) p.2))).smul hinner
  have hlast : Continuous (fun p : E n × E n =>
      (innerSL ℝ (gradB n (φ ξ) p.2)).smulRight (gradB n (φ ξ) p.2)) :=
    (continuous_innerSL_smulRight n).comp (hgrad.comp continuous_snd)
  exact hfirst.sub hlast

private lemma continuous_Wv_subtype (n : ℕ) (φ : E n → E n)
    (hbij : Set.BijOn φ (Sph n) (Sph n)) (hcont : ContinuousOn φ (Sph n))
    (p : E n × E n) :
    Continuous (fun η : ↥(Sph n) => Wv n φ p η) :=
  (continuous_fst.smul continuous_snd : Continuous fun q : ℝ × E n => q.1 • q.2).comp
    ((continuous_pfun_subtype n p.1).prodMk (continuous_gradB_phi_subtype n φ hbij hcont p.2))

private lemma aes_Wv (n : ℕ) (φ : E n → E n) (hbij : Set.BijOn φ (Sph n) (Sph n))
    (hcont : ContinuousOn φ (Sph n)) (p : E n × E n) :
    AEStronglyMeasurable (fun ξ : E n => Wv n φ p ξ) (sigma n) :=
  aes_of_continuous_subtype n (continuous_Wv_subtype n φ hbij hcont p)

private lemma continuous_DWv_subtype (n : ℕ) (φ : E n → E n)
    (hbij : Set.BijOn φ (Sph n) (Sph n)) (hcont : ContinuousOn φ (Sph n))
    (p : E n × E n) :
    Continuous (fun η : ↥(Sph n) => DWv n φ p η) := by
  have hsm : Continuous fun q : (E n →L[ℝ] ℝ) × E n => q.1.smulRight q.2 :=
    (ContinuousLinearMap.smulRightL ℝ (E n) (E n)).continuous₂
  have hsmc : Continuous fun q : ℝ × (E n →L[ℝ] E n) => q.1 • q.2 :=
    continuous_fst.smul continuous_snd
  have hcomp : Continuous fun L : E n →L[ℝ] E n =>
      L ∘L ContinuousLinearMap.fst ℝ (E n) (E n) := by fun_prop
  have hcomp' : Continuous fun L : E n →L[ℝ] E n =>
      L ∘L ContinuousLinearMap.snd ℝ (E n) (E n) := by fun_prop
  have h1 : Continuous fun η : ↥(Sph n) =>
      ((dpfun n p.1 η).smulRight (gradB n (φ η) p.2)) ∘L
        ContinuousLinearMap.fst ℝ (E n) (E n) :=
    hcomp.comp (hsm.comp ((continuous_dpfun_subtype n p.1).prodMk
      (continuous_gradB_phi_subtype n φ hbij hcont p.2)))
  have h2 : Continuous fun η : ↥(Sph n) =>
      (pfun n p.1 η • hessB n (φ η) p.2) ∘L
        ContinuousLinearMap.snd ℝ (E n) (E n) :=
    hcomp'.comp (hsmc.comp ((continuous_pfun_subtype n p.1).prodMk
      (continuous_hessB_phi_subtype n φ hbij hcont p.2)))
  exact h1.add h2

private lemma aes_DWv (n : ℕ) (φ : E n → E n) (hbij : Set.BijOn φ (Sph n) (Sph n))
    (hcont : ContinuousOn φ (Sph n)) (p : E n × E n) :
    AEStronglyMeasurable (fun ξ : E n => DWv n φ p ξ) (sigma n) :=
  aes_of_continuous_subtype n (continuous_DWv_subtype n φ hbij hcont p)

private lemma continuous_DWv_prod (n : ℕ) (φ : E n → E n) (hbij : Set.BijOn φ (Sph n) (Sph n))
    (hd2 : ∀ (ξ : E n), ξ ∈ Sph n →
      ∀ y : E n, HasFDerivAt (fun y => gradB n ξ y) (hessB n ξ y) y)
    (ξ : E n) (hξ : ξ ∈ Sph n) :
    Continuous (fun p : E n × E n => DWv n φ p ξ) := by
  have hsm : Continuous fun q : (E n →L[ℝ] ℝ) × E n => q.1.smulRight q.2 :=
    (ContinuousLinearMap.smulRightL ℝ (E n) (E n)).continuous₂
  have hsmc : Continuous fun q : ℝ × (E n →L[ℝ] E n) => q.1 • q.2 :=
    continuous_fst.smul continuous_snd
  have hcomp : Continuous fun L : E n →L[ℝ] E n =>
      L ∘L ContinuousLinearMap.fst ℝ (E n) (E n) := by fun_prop
  have hcomp' : Continuous fun L : E n →L[ℝ] E n =>
      L ∘L ContinuousLinearMap.snd ℝ (E n) (E n) := by fun_prop
  have h1 : Continuous fun p : E n × E n =>
      ((dpfun n p.1 ξ).smulRight (gradB n (φ ξ) p.2)) ∘L
        ContinuousLinearMap.fst ℝ (E n) (E n) :=
    hcomp.comp (hsm.comp ((continuous_dpfun_prod n ξ hξ).prodMk
      (continuous_gradB_prod n φ hbij hd2 ξ hξ)))
  have h2 : Continuous fun p : E n × E n =>
      (pfun n p.1 ξ • hessB n (φ ξ) p.2) ∘L
        ContinuousLinearMap.snd ℝ (E n) (E n) :=
    hcomp'.comp (hsmc.comp ((continuous_pfun_prod n ξ hξ).prodMk
      (continuous_hessB_prod n φ hbij hd2 ξ hξ)))
  exact h1.add h2

/-! ## Norm bounds for the integrands -/

private lemma norm_comp_fst_le (n : ℕ) (L : E n →L[ℝ] E n) :
    ‖L ∘L ContinuousLinearMap.fst ℝ (E n) (E n)‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) fun x => ?_
  rw [ContinuousLinearMap.comp_apply]
  show ‖L x.1‖ ≤ ‖L‖ * ‖x‖
  calc ‖L x.1‖ ≤ ‖L‖ * ‖x.1‖ := L.le_opNorm x.1
    _ ≤ ‖L‖ * ‖x‖ := by gcongr; exact norm_fst_le x

private lemma norm_comp_snd_le (n : ℕ) (L : E n →L[ℝ] E n) :
    ‖L ∘L ContinuousLinearMap.snd ℝ (E n) (E n)‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) fun x => ?_
  rw [ContinuousLinearMap.comp_apply]
  show ‖L x.2‖ ≤ ‖L‖ * ‖x‖
  calc ‖L x.2‖ ≤ ‖L‖ * ‖x.2‖ := L.le_opNorm x.2
    _ ≤ ‖L‖ * ‖x‖ := by gcongr; exact norm_snd_le x

private lemma norm_Wv_le (n : ℕ) (φ : E n → E n) (p : E n × E n) (ξ : E n) {Cg Cf : ℝ}
    (hg : ‖gradB n (φ ξ) p.2‖ ≤ Cg) (hf : |pfun n p.1 ξ| ≤ Cf) :
    ‖Wv n φ p ξ‖ ≤ Cf * Cg := by
  have hf0 : 0 ≤ Cf := le_trans (abs_nonneg _) hf
  have hg0 : 0 ≤ Cg := le_trans (norm_nonneg _) hg
  calc ‖Wv n φ p ξ‖ = |pfun n p.1 ξ| * ‖gradB n (φ ξ) p.2‖ := by
        simp only [Wv, norm_smul, Real.norm_eq_abs]
    _ ≤ Cf * Cg := mul_le_mul hf hg (norm_nonneg _) hf0

private lemma norm_DWv_le (n : ℕ) (φ : E n → E n) (p : E n × E n) (ξ : E n) {Cp Cf Cg Ch : ℝ}
    (hCp : ‖dpfun n p.1 ξ‖ ≤ Cp) (hf : |pfun n p.1 ξ| ≤ Cf)
    (hCg : ‖gradB n (φ ξ) p.2‖ ≤ Cg) (hCh : ‖hessB n (φ ξ) p.2‖ ≤ Ch) :
    ‖DWv n φ p ξ‖ ≤ Cp * Cg + Cf * Ch := by
  have hCp0 : 0 ≤ Cp := le_trans (norm_nonneg _) hCp
  have hf0 : 0 ≤ Cf := le_trans (abs_nonneg _) hf
  have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg _) hCg
  have hCh0 : 0 ≤ Ch := le_trans (norm_nonneg _) hCh
  have hsplit : DWv n φ p ξ =
      ((dpfun n p.1 ξ).smulRight (gradB n (φ ξ) p.2)) ∘L
          ContinuousLinearMap.fst ℝ (E n) (E n) +
        (pfun n p.1 ξ • hessB n (φ ξ) p.2) ∘L
          ContinuousLinearMap.snd ℝ (E n) (E n) := rfl
  rw [hsplit]
  calc ‖((dpfun n p.1 ξ).smulRight (gradB n (φ ξ) p.2)) ∘L
            ContinuousLinearMap.fst ℝ (E n) (E n) +
          (pfun n p.1 ξ • hessB n (φ ξ) p.2) ∘L
            ContinuousLinearMap.snd ℝ (E n) (E n)‖
      ≤ ‖((dpfun n p.1 ξ).smulRight (gradB n (φ ξ) p.2)) ∘L
            ContinuousLinearMap.fst ℝ (E n) (E n)‖ +
          ‖(pfun n p.1 ξ • hessB n (φ ξ) p.2) ∘L
            ContinuousLinearMap.snd ℝ (E n) (E n)‖ := norm_add_le _ _
    _ ≤ ‖(dpfun n p.1 ξ).smulRight (gradB n (φ ξ) p.2)‖ +
          ‖pfun n p.1 ξ • hessB n (φ ξ) p.2‖ :=
        add_le_add (norm_comp_fst_le n _) (norm_comp_snd_le n _)
    _ = ‖dpfun n p.1 ξ‖ * ‖gradB n (φ ξ) p.2‖ + |pfun n p.1 ξ| * ‖hessB n (φ ξ) p.2‖ := by
        rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
    _ ≤ Cp * Cg + Cf * Ch :=
        add_le_add (mul_le_mul hCp hCg (norm_nonneg _) hCp0) (mul_le_mul hf hCh (norm_nonneg _) hf0)

/-! ## Differentiation under the integral sign -/

private theorem hasFDerivAt_Gv (n : ℕ) (φ : E n → E n)
    (hbij : Set.BijOn φ (Sph n) (Sph n)) (hcont : ContinuousOn φ (Sph n))
    (hd2 : ∀ (ξ : E n), ξ ∈ Sph n →
      ∀ y : E n, HasFDerivAt (fun y => gradB n ξ y) (hessB n ξ y) y)
    (hp1 : ∀ (ξ : E n), ξ ∈ Sph n →
      ∀ x : E n, HasFDerivAt (fun x => pfun n x ξ) (dpfun n x ξ) x)
    (hg : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ (ξ : E n), ξ ∈ Sph n →
      ∀ y : E n, ‖y‖ ≤ R → ‖gradB n ξ y‖ ≤ C)
    (hh : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ (ξ : E n), ξ ∈ Sph n →
      ∀ y : E n, ‖y‖ ≤ R → ‖hessB n ξ y‖ ≤ C)
    (hp : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ (ξ : E n), ξ ∈ Sph n →
      ∀ x : E n, ‖x‖ ≤ R → ‖dpfun n x ξ‖ ≤ C)
    (p₀ : E n × E n) :
    HasFDerivAt (fun p : E n × E n => Gv n φ p.1 p.2) (DGv n φ p₀.1 p₀.2) p₀ := by
  haveI : IsFiniteMeasure (sigma n) := sigma_finite n
  obtain ⟨Cg, hCg⟩ := hg (‖p₀‖ + 1) (by positivity)
  obtain ⟨Ch, hCh⟩ := hh (‖p₀‖ + 1) (by positivity)
  obtain ⟨Cp, hCp⟩ := hp (‖p₀‖ + 1) (by positivity)
  obtain ⟨Cf, _hCf0, hCf⟩ := PfunBoundSph n (‖p₀‖ + 1)
  have hball : ∀ p ∈ Metric.closedBall p₀ 1, ‖p‖ ≤ ‖p₀‖ + 1 := by
    intro p hp
    rw [Metric.mem_closedBall, dist_eq_norm] at hp
    have h1 : ‖p‖ ≤ ‖p - p₀‖ + ‖p₀‖ := by
      have h2 := norm_add_le (p - p₀) p₀
      rwa [sub_add_cancel] at h2
    linarith
  have h1ball : ∀ p ∈ Metric.closedBall p₀ 1, ‖p.1‖ ≤ ‖p₀‖ + 1 :=
    fun p hp => le_trans (norm_fst_le p) (hball p hp)
  have h2ball : ∀ p ∈ Metric.closedBall p₀ 1, ‖p.2‖ ≤ ‖p₀‖ + 1 :=
    fun p hp => le_trans (norm_snd_le p) (hball p hp)
  have boundW : ∀ (ξ : E n), ξ ∈ Sph n → ∀ p ∈ Metric.closedBall p₀ 1,
      ‖Wv n φ p ξ‖ ≤ Cf * |Cg| := by
    intro ξ hξ p hp
    exact norm_Wv_le n φ p ξ
      (le_trans (hCg (φ ξ) (hbij.1 hξ) p.2 (h2ball p hp)) (le_abs_self Cg))
      (hCf p.1 (h1ball p hp) ξ hξ)
  have boundD : ∀ (ξ : E n), ξ ∈ Sph n → ∀ p ∈ Metric.closedBall p₀ 1,
      ‖DWv n φ p ξ‖ ≤ |Cp| * |Cg| + Cf * |Ch| := by
    intro ξ hξ p hp
    exact norm_DWv_le n φ p ξ
      (le_trans (hCp ξ hξ p.1 (h1ball p hp)) (le_abs_self Cp))
      (hCf p.1 (h1ball p hp) ξ hξ)
      (le_trans (hCg (φ ξ) (hbij.1 hξ) p.2 (h2ball p hp)) (le_abs_self Cg))
      (le_trans (hCh (φ ξ) (hbij.1 hξ) p.2 (h2ball p hp)) (le_abs_self Ch))
  have key : HasFDerivAt (fun p : E n × E n => ∫ ξ, Wv n φ p ξ ∂(sigma n))
      (∫ ξ, DWv n φ p₀ ξ ∂(sigma n)) p₀ := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := sigma n) (F := fun p ξ => Wv n φ p ξ) (F' := fun p ξ => DWv n φ p ξ)
      (bound := fun _ : E n => |Cp| * |Cg| + Cf * |Ch|) (s := Metric.closedBall p₀ 1)
      (Metric.closedBall_mem_nhds p₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards with p
      exact aes_Wv n φ hbij hcont p
    · refine Integrable.of_bound (aes_Wv n φ hbij hcont p₀) (Cf * |Cg|) ?_
      filter_upwards [ae_mem_Sph n] with ξ hξ
      exact boundW ξ hξ p₀ (Metric.mem_closedBall_self (by norm_num))
    · exact aes_DWv n φ hbij hcont p₀
    · filter_upwards [ae_mem_Sph n] with ξ hξ p hp
      exact boundD ξ hξ p hp
    · exact integrable_const _
    · filter_upwards [ae_mem_Sph n] with ξ hξ p hp
      have hφξ : φ ξ ∈ Sph n := hbij.1 hξ
      exact HasFDerivProdSmul n (hp1 ξ hξ p.1) (hd2 (φ ξ) hφξ p.2)
  show HasFDerivAt (fun p : E n × E n => ∫ ξ, Wv n φ p ξ ∂(sigma n))
      (∫ ξ, DWv n φ p₀ ξ ∂(sigma n)) p₀
  exact key

/-! ## Continuity of the derivative -/

private theorem continuous_DGv (n : ℕ) (φ : E n → E n)
    (hbij : Set.BijOn φ (Sph n) (Sph n)) (hcont : ContinuousOn φ (Sph n))
    (hd2 : ∀ (ξ : E n), ξ ∈ Sph n →
      ∀ y : E n, HasFDerivAt (fun y => gradB n ξ y) (hessB n ξ y) y)
    (hp1 : ∀ (ξ : E n), ξ ∈ Sph n →
      ∀ x : E n, HasFDerivAt (fun x => pfun n x ξ) (dpfun n x ξ) x)
    (hg : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ (ξ : E n), ξ ∈ Sph n →
      ∀ y : E n, ‖y‖ ≤ R → ‖gradB n ξ y‖ ≤ C)
    (hh : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ (ξ : E n), ξ ∈ Sph n →
      ∀ y : E n, ‖y‖ ≤ R → ‖hessB n ξ y‖ ≤ C)
    (hp : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ (ξ : E n), ξ ∈ Sph n →
      ∀ x : E n, ‖x‖ ≤ R → ‖dpfun n x ξ‖ ≤ C) :
    Continuous fun p : E n × E n => DGv n φ p.1 p.2 := by
  haveI : IsFiniteMeasure (sigma n) := sigma_finite n
  apply continuous_iff_continuousAt.mpr
  intro p₀
  obtain ⟨Cg, hCg⟩ := hg (‖p₀‖ + 1) (by positivity)
  obtain ⟨Ch, hCh⟩ := hh (‖p₀‖ + 1) (by positivity)
  obtain ⟨Cp, hCp⟩ := hp (‖p₀‖ + 1) (by positivity)
  obtain ⟨Cf, _hCf0, hCf⟩ := PfunBoundSph n (‖p₀‖ + 1)
  have hball : ∀ p ∈ Metric.closedBall p₀ 1, ‖p‖ ≤ ‖p₀‖ + 1 := by
    intro p hp
    rw [Metric.mem_closedBall, dist_eq_norm] at hp
    have h1 : ‖p‖ ≤ ‖p - p₀‖ + ‖p₀‖ := by
      have h2 := norm_add_le (p - p₀) p₀
      rwa [sub_add_cancel] at h2
    linarith
  have h1ball : ∀ p ∈ Metric.closedBall p₀ 1, ‖p.1‖ ≤ ‖p₀‖ + 1 :=
    fun p hp => le_trans (norm_fst_le p) (hball p hp)
  have h2ball : ∀ p ∈ Metric.closedBall p₀ 1, ‖p.2‖ ≤ ‖p₀‖ + 1 :=
    fun p hp => le_trans (norm_snd_le p) (hball p hp)
  have boundD : ∀ (ξ : E n), ξ ∈ Sph n → ∀ p ∈ Metric.closedBall p₀ 1,
      ‖DWv n φ p ξ‖ ≤ |Cp| * |Cg| + Cf * |Ch| := by
    intro ξ hξ p hp
    exact norm_DWv_le n φ p ξ
      (le_trans (hCp ξ hξ p.1 (h1ball p hp)) (le_abs_self Cp))
      (hCf p.1 (h1ball p hp) ξ hξ)
      (le_trans (hCg (φ ξ) (hbij.1 hξ) p.2 (h2ball p hp)) (le_abs_self Cg))
      (le_trans (hCh (φ ξ) (hbij.1 hξ) p.2 (h2ball p hp)) (le_abs_self Ch))
  have hcontOn : ContinuousOn (fun p : E n × E n => ∫ ξ, DWv n φ p ξ ∂(sigma n))
      (Metric.closedBall p₀ 1) := by
    refine continuousOn_of_dominated
      (μ := sigma n) (F := fun p ξ => DWv n φ p ξ)
      (bound := fun _ : E n => |Cp| * |Cg| + Cf * |Ch|) (s := Metric.closedBall p₀ 1) ?_ ?_ ?_ ?_
    · intro p hp
      exact aes_DWv n φ hbij hcont p
    · intro p hp
      filter_upwards [ae_mem_Sph n] with ξ hξ
      exact boundD ξ hξ p hp
    · exact integrable_const _
    · filter_upwards [ae_mem_Sph n] with ξ hξ
      exact (continuous_DWv_prod n φ hbij hd2 ξ hξ).continuousOn
  exact hcontOn.continuousAt (Metric.closedBall_mem_nhds p₀ one_pos)

/-! ## The requested lemma -/

theorem GvC1 (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hcont : ContinuousOn φ (Submission.Mostow.Sph n))
    (hd1 : ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ y : Submission.Mostow.E n,
        HasFDerivAt (fun y => Submission.Mostow.busemann ξ y)
          (innerSL ℝ (Work.Mostow.gradB n ξ y)) y)
    (hd2 : ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ y : Submission.Mostow.E n, HasFDerivAt (fun y => Work.Mostow.gradB n ξ y)
        (Work.Mostow.hessB n ξ y) y)
    (hp1 : ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ x : Submission.Mostow.E n,
        HasFDerivAt (fun x => Work.Mostow.pfun n x ξ) (Work.Mostow.dpfun n x ξ) x)
    (hg : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ y : Submission.Mostow.E n, ‖y‖ ≤ R → ‖Work.Mostow.gradB n ξ y‖ ≤ C)
    (hh : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ y : Submission.Mostow.E n, ‖y‖ ≤ R → ‖Work.Mostow.hessB n ξ y‖ ≤ C)
    (hp : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ x : Submission.Mostow.E n, ‖x‖ ≤ R → ‖Work.Mostow.dpfun n x ξ‖ ≤ C) :
    ContDiff ℝ 1 (fun p : Submission.Mostow.E n × Submission.Mostow.E n =>
        Work.Mostow.Gv n φ p.1 p.2) ∧
    (∀ p : Submission.Mostow.E n × Submission.Mostow.E n,
      fderiv ℝ (fun q : Submission.Mostow.E n × Submission.Mostow.E n =>
        Work.Mostow.Gv n φ q.1 q.2) p = Work.Mostow.DGv n φ p.1 p.2) := by
  have hder : ∀ p : E n × E n,
      HasFDerivAt (fun q : E n × E n => Gv n φ q.1 q.2) (DGv n φ p.1 p.2) p :=
    fun p => hasFDerivAt_Gv n φ hbij hcont hd2 hp1 hg hh hp p
  refine ⟨contDiff_one_iff_hasFDerivAt.mpr
    ⟨fun p => DGv n φ p.1 p.2, continuous_DGv n φ hbij hcont hd2 hp1 hg hh hp, hder⟩, ?_⟩
  intro p
  exact (hder p).fderiv

end

end Work.Mostow
