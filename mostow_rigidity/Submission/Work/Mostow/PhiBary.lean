import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.NatMeasure
import Submission.Work.Mostow.BaryBase

/-!
# `Phi` is the barycentre functional of the pushed-forward visual measure (area N2/N3)

The BCG natural map is `F x = bar ((visual n x).map φ)`, the (unique) minimiser of the barycentre
functional

  `baryFun ((visual n x).map φ) y = ∫ z, busemann z y ∂((visual n x).map φ)`.

`NatMapJac.lean` and `NatMapSurj.lean` compute with the same functional written against the
normalised surface measure `sigma n`,

  `Phi n φ x y = ∫ ξ, pfun n x ξ * busemann (φ ξ) y ∂(sigma n)`,

using the explicit Poisson kernel `pfun n x ξ`.  This file proves the two definitions agree.

The proof is two measure-theoretic steps, each independent of the other:
* pushing forward commutes with integration (`MeasureTheory.integral_map`), so
  `∫ z, busemann z y ∂((visual n x).map φ) = ∫ ξ, busemann (φ ξ) y ∂(visual n x)`;
* `visual n x` is `sigma n` weighted by its density `exp (-(n-1) β_ξ x)`, which on the sphere is
  exactly `pfun n x ξ`, so `∫ ξ, busemann (φ ξ) y ∂(visual n x)` is
  `∫ ξ, pfun n x ξ * busemann (φ ξ) y ∂(sigma n)`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- On the boundary sphere the Poisson kernel is the exponential of the Busemann function:
`(tpart x - ⟪x,ξ⟫)^{-(n-1)} = exp (-(n-1) * β_ξ x)`. -/
lemma pfun_eq_exp_busemann {n : ℕ} (x ξ : E n) (hξ : ξ ∈ Sph n) :
    pfun n x ξ = Real.exp (-((n : ℝ) - 1) * busemann ξ x) := by
  have hpos := busemann_arg_pos ξ hξ x
  rw [pfun, busemann, Real.rpow_def_of_pos hpos]
  congr 1
  ring

/-- Integration against the visual measure `visual n x` is integration against `sigma n` with the
Poisson kernel inserted.  (The two densities defining `visual n x` and `pfun n x ·` agree
`sigma n`-almost everywhere, since `sigma n` is carried by the unit sphere.) -/
lemma visual_integral_eq_sigma {n : ℕ} (hV : VisualProp n) (x : E n) (g : E n → ℝ) :
    ∫ ξ, g ξ ∂(visual n x) = ∫ ξ, pfun n x ξ * g ξ ∂(sigma n) := by
  have hb : Measurable (fun ξ : E n => busemann ξ x) := measurable_busemann x
  have hmeas_dens : Measurable
      (fun ξ : E n => ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * busemann ξ x))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (measurable_const.mul hb))
  have hlt : ∀ᵐ ξ ∂(sigma n),
      ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * busemann ξ x)) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  -- `sigma n` is carried by the sphere, because `visual n 0 = sigma n`
  have hsupp : sigma n (Sph n)ᶜ = 0 := by
    have h0 : visual n (0 : E n) = sigma n := by simp [visual, busemann, tpart]
    rw [← h0]
    exact (hV 0).2.1
  have hdens : ∀ᵐ ξ ∂(sigma n),
      (ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * busemann ξ x))).toReal • g ξ
        = pfun n x ξ * g ξ := by
    filter_upwards [show ∀ᵐ ξ ∂(sigma n), ξ ∈ Sph n from by
      rw [ae_iff]
      simpa only [Set.compl_def] using hsupp] with ξ hξ
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, pfun_eq_exp_busemann x ξ hξ, smul_eq_mul]
  change ∫ ξ, g ξ ∂(sigma n).withDensity
      (fun ξ => ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * busemann ξ x)))
    = ∫ ξ, pfun n x ξ * g ξ ∂(sigma n)
  rw [integral_withDensity_eq_integral_toReal_smul hmeas_dens hlt]
  exact integral_congr_ae hdens

theorem PhiBary (n : ℕ) (hV : Submission.Mostow.VisualProp n)
    (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hcont : ContinuousOn φ (Submission.Mostow.Sph n)) :
    ∀ x y : Submission.Mostow.E n,
      Work.Mostow.Phi n φ x y = Submission.Mostow.baryFun ((Submission.Mostow.visual n x).map φ) y := by
  intro x y
  -- `φ` is measurable for `visual n x` (continuous on the sphere, where `visual n x` lives)
  have hae : AEMeasurable φ (visual n x) :=
    aemeasurable_of_continuousOn_of_compl_eq_zero (0 : E n)
      Metric.isClosed_sphere.measurableSet hcont (hV x).2.1
  -- pushforward commutes with integration
  have hmap : ∫ z, busemann z y ∂((visual n x).map φ)
      = ∫ ξ, busemann (φ ξ) y ∂(visual n x) :=
    integral_map hae (measurable_busemann y).aestronglyMeasurable
  calc Phi n φ x y
      = ∫ ξ, pfun n x ξ * busemann (φ ξ) y ∂(sigma n) := rfl
    _ = ∫ ξ, busemann (φ ξ) y ∂(visual n x) := (visual_integral_eq_sigma hV x _).symm
    _ = ∫ z, busemann z y ∂((visual n x).map φ) := hmap.symm
    _ = baryFun ((visual n x).map φ) y := rfl

end

end Work.Mostow
