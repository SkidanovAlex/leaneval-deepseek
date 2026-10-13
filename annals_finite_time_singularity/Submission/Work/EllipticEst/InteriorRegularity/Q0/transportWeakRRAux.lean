/-
Work module for `annals_finite_time_singularity`: the assembly of the transport of the real weak
formulation of `bslOp α Ψ = F` on the open quadrant `Q0` to the transported (complex) weak
formulation `StripWeakRR (VRR α Ψ) (GRR α F)`.

A complex test function `ψ` of the half-strip is split into its real and imaginary parts
(`reFun ψ`, `imFun ψ`), which are *real* test functions of the half-strip, of smoothness,
compact support and topological support inherited from `ψ`; the real transport lemma
`transport_real` is applied to each of them and the two complex identities are reassembled with
`integral_add`, `integral_const_mul` and `integral_complex_ofReal`.

The pull-back of a real test function of the half-strip to a test function of the quadrant is
taken as a *hypothesis* (`hpull`, an instance of which is `Q0.pullbackExists`), so that this
module does not depend on the construction of the cut-off.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRTransport
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRTransport2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The real and imaginary parts of a complex test function -/

/-- The real part of a complex-valued function of two variables. -/
def reFun (ψ : ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ := fun σ θ => (ψ σ θ).re

/-- The imaginary part of a complex-valued function of two variables. -/
def imFun (ψ : ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ := fun σ θ => (ψ σ θ).im

theorem uncurry_reFun (ψ : ℝ → ℝ → ℂ) :
    Function.uncurry (reFun ψ) = fun p : ℝ × ℝ => (Function.uncurry ψ p).re := rfl

theorem uncurry_imFun (ψ : ℝ → ℝ → ℂ) :
    Function.uncurry (imFun ψ) = fun p : ℝ × ℝ => (Function.uncurry ψ p).im := rfl

theorem contDiff_uncurry_reFun {ψ : ℝ → ℝ → ℂ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ)) :
    ∀ n : ℕ, ContDiff ℝ n (Function.uncurry (reFun ψ)) := by
  intro n
  rw [uncurry_reFun]
  exact Complex.reCLM.contDiff.comp (hψ n)

theorem contDiff_uncurry_imFun {ψ : ℝ → ℝ → ℂ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ)) :
    ∀ n : ℕ, ContDiff ℝ n (Function.uncurry (imFun ψ)) := by
  intro n
  rw [uncurry_imFun]
  exact Complex.imCLM.contDiff.comp (hψ n)

theorem hasCompactSupport_uncurry_reFun {ψ : ℝ → ℝ → ℂ}
    (hψc : HasCompactSupport (Function.uncurry ψ)) :
    HasCompactSupport (Function.uncurry (reFun ψ)) := by
  rw [uncurry_reFun]
  exact hψc.comp_left (g := Complex.re) (by simp)

theorem hasCompactSupport_uncurry_imFun {ψ : ℝ → ℝ → ℂ}
    (hψc : HasCompactSupport (Function.uncurry ψ)) :
    HasCompactSupport (Function.uncurry (imFun ψ)) := by
  rw [uncurry_imFun]
  exact hψc.comp_left (g := Complex.im) (by simp)

theorem tsupport_uncurry_reFun_subset (ψ : ℝ → ℝ → ℂ) :
    tsupport (Function.uncurry (reFun ψ)) ⊆ tsupport (Function.uncurry ψ) := by
  have hs : Function.support (fun p : ℝ × ℝ => (Function.uncurry ψ p).re)
      ⊆ Function.support (Function.uncurry ψ) := by
    intro p hp
    have hp' : (Function.uncurry ψ p).re ≠ 0 := hp
    intro h0
    exact hp' (by simp [h0])
  rw [uncurry_reFun]
  exact closure_mono hs

theorem tsupport_uncurry_imFun_subset (ψ : ℝ → ℝ → ℂ) :
    tsupport (Function.uncurry (imFun ψ)) ⊆ tsupport (Function.uncurry ψ) := by
  have hs : Function.support (fun p : ℝ × ℝ => (Function.uncurry ψ p).im)
      ⊆ Function.support (Function.uncurry ψ) := by
    intro p hp
    have hp' : (Function.uncurry ψ p).im ≠ 0 := hp
    intro h0
    exact hp' (by simp [h0])
  rw [uncurry_imFun]
  exact closure_mono hs

/-! ## The pointwise complex identities -/

/-- `VRR · kopD` splits into its real and imaginary parts. -/
theorem VRR_mul_kopD_eq {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ → ℂ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ)) (σ θ : ℝ) :
    (VRR α Ψ σ θ : ℂ) * kopD ψ σ θ
      = ((VRR α Ψ σ θ * kopDr (reFun ψ) σ θ : ℝ) : ℂ)
        + Complex.I * ((VRR α Ψ σ θ * kopDr (imFun ψ) σ θ : ℝ) : ℂ) := by
  have hre : (kopD ψ σ θ).re = kopDr (reFun ψ) σ θ := kopD_re hψ σ θ
  have him : (kopD ψ σ θ).im = kopDr (imFun ψ) σ θ := kopD_im hψ σ θ
  conv_lhs => rw [← Complex.re_add_im (kopD ψ σ θ)]
  rw [hre, him]
  simp only [Complex.ofReal_mul]
  ring

/-- `GRR · ψ` splits into its real and imaginary parts. -/
theorem GRR_mul_test_eq {α : ℝ} {F : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ → ℂ} (σ θ : ℝ) :
    (GRR α F σ θ : ℂ) * ψ σ θ
      = ((GRR α F σ θ * reFun ψ σ θ : ℝ) : ℂ)
        + Complex.I * ((GRR α F σ θ * imFun ψ σ θ : ℝ) : ℂ) := by
  have hre : (ψ σ θ).re = reFun ψ σ θ := rfl
  have him : (ψ σ θ).im = imFun ψ σ θ := rfl
  conv_lhs => rw [← Complex.re_add_im (ψ σ θ)]
  rw [hre, him]
  simp only [Complex.ofReal_mul]
  ring

/-! ## The complex integrals -/

/-- The left-hand side of the transported weak formulation, split into real and imaginary
parts. -/
theorem integral_VRR_kopD {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {ψ : ℝ → ℝ → ℂ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (hψc : HasCompactSupport (Function.uncurry ψ))
    (hψs : tsupport (Function.uncurry ψ) ⊆ stripRR) :
    (∫ q : ℝ × ℝ, (VRR α Ψ q.1 q.2 : ℂ) * kopD ψ q.1 q.2)
      = ((∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr (reFun ψ) q.1 q.2 : ℝ) : ℂ)
        + Complex.I * ((∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr (imFun ψ) q.1 q.2 : ℝ) : ℂ) := by
  have hr : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr (reFun ψ) q.1 q.2) :=
    integrable_VRR_kopDr hα hΨ (contDiff_uncurry_reFun hψ)
      (hasCompactSupport_uncurry_reFun hψc) (subset_trans (tsupport_uncurry_reFun_subset ψ) hψs)
  have hi : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr (imFun ψ) q.1 q.2) :=
    integrable_VRR_kopDr hα hΨ (contDiff_uncurry_imFun hψ)
      (hasCompactSupport_uncurry_imFun hψc) (subset_trans (tsupport_uncurry_imFun_subset ψ) hψs)
  have hrC : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => ((VRR α Ψ q.1 q.2 * kopDr (reFun ψ) q.1 q.2 : ℝ) : ℂ)) :=
    hr.ofReal
  have hiC : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => Complex.I * ((VRR α Ψ q.1 q.2 * kopDr (imFun ψ) q.1 q.2 : ℝ) : ℂ)) :=
    hi.ofReal.const_mul Complex.I
  have hpt : (fun q : ℝ × ℝ => (VRR α Ψ q.1 q.2 : ℂ) * kopD ψ q.1 q.2)
      = fun q : ℝ × ℝ => ((VRR α Ψ q.1 q.2 * kopDr (reFun ψ) q.1 q.2 : ℝ) : ℂ)
          + Complex.I * ((VRR α Ψ q.1 q.2 * kopDr (imFun ψ) q.1 q.2 : ℝ) : ℂ) :=
    funext fun q => VRR_mul_kopD_eq hψ q.1 q.2
  rw [hpt, MeasureTheory.integral_add hrC hiC, integral_complex_ofReal,
    MeasureTheory.integral_const_mul Complex.I
      (fun q : ℝ × ℝ => ((VRR α Ψ q.1 q.2 * kopDr (imFun ψ) q.1 q.2 : ℝ) : ℂ)),
    integral_complex_ofReal]
  try rfl

/-- The right-hand side of the transported weak formulation, split into real and imaginary
parts. -/
theorem integral_GRR_test {α : ℝ} {F : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ → ℂ}
    (hr : MeasureTheory.Integrable (fun q : ℝ × ℝ => GRR α F q.1 q.2 * reFun ψ q.1 q.2))
    (hi : MeasureTheory.Integrable (fun q : ℝ × ℝ => GRR α F q.1 q.2 * imFun ψ q.1 q.2)) :
    (∫ q : ℝ × ℝ, (GRR α F q.1 q.2 : ℂ) * ψ q.1 q.2)
      = ((∫ q : ℝ × ℝ, GRR α F q.1 q.2 * reFun ψ q.1 q.2 : ℝ) : ℂ)
        + Complex.I * ((∫ q : ℝ × ℝ, GRR α F q.1 q.2 * imFun ψ q.1 q.2 : ℝ) : ℂ) := by
  have hrC : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => ((GRR α F q.1 q.2 * reFun ψ q.1 q.2 : ℝ) : ℂ)) :=
    hr.ofReal
  have hiC : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => Complex.I * ((GRR α F q.1 q.2 * imFun ψ q.1 q.2 : ℝ) : ℂ)) :=
    hi.ofReal.const_mul Complex.I
  have hpt : (fun q : ℝ × ℝ => (GRR α F q.1 q.2 : ℂ) * ψ q.1 q.2)
      = fun q : ℝ × ℝ => ((GRR α F q.1 q.2 * reFun ψ q.1 q.2 : ℝ) : ℂ)
          + Complex.I * ((GRR α F q.1 q.2 * imFun ψ q.1 q.2 : ℝ) : ℂ) :=
    funext fun q => GRR_mul_test_eq q.1 q.2
  rw [hpt, MeasureTheory.integral_add hrC hiC, integral_complex_ofReal,
    MeasureTheory.integral_const_mul Complex.I
      (fun q : ℝ × ℝ => ((GRR α F q.1 q.2 * imFun ψ q.1 q.2 : ℝ) : ℂ)),
    integral_complex_ofReal]
  try rfl

/-- The real part of an integrable complex integrand is integrable (in the `F · reFun`-form). -/
theorem integrable_re_of_complex {F : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ → ℂ}
    (h : MeasureTheory.Integrable (fun q : ℝ × ℝ => (F q.1 q.2 : ℂ) * ψ q.1 q.2)) :
    MeasureTheory.Integrable (fun q : ℝ × ℝ => F q.1 q.2 * reFun ψ q.1 q.2) := by
  have h1 : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => ((F q.1 q.2 : ℂ) * ψ q.1 q.2).re) := h.re
  refine h1.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [reFun, RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- The imaginary part of an integrable complex integrand is integrable. -/
theorem integrable_im_of_complex {F : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ → ℂ}
    (h : MeasureTheory.Integrable (fun q : ℝ × ℝ => (F q.1 q.2 : ℂ) * ψ q.1 q.2)) :
    MeasureTheory.Integrable (fun q : ℝ × ℝ => F q.1 q.2 * imFun ψ q.1 q.2) := by
  have h1 : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => ((F q.1 q.2 : ℂ) * ψ q.1 q.2).im) := h.im
  refine h1.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [imFun, RCLike.im_to_complex, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]

/-! ## The assembly -/

theorem transportWeakRR_of_pullback {α : ℝ} (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0,
          Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = ∫ p in Work.FTS.EllipticEst.Q0,
            F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
    (hpull : ∀ ψ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ)) →
      HasCompactSupport (Function.uncurry ψ) →
      tsupport (Function.uncurry ψ) ⊆ stripRR →
      ∃ φ : ℝ → ℝ → ℝ,
        (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) ∧
        HasCompactSupport (Function.uncurry φ) ∧
        tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 ∧
        (∀ z θ : ℝ, 0 < z → φ z θ = ψ ((1 / α) * Real.log z) θ) ∧
        (∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
          Work.Elliptic.bslOp α φ z θ = kopDr ψ ((1 / α) * Real.log z) θ)) :
    StripWeakRR (fun σ θ => (VRR α Ψ σ θ : ℂ)) (fun σ θ => (GRR α F σ θ : ℂ)) := by
  intro ψ hψ hψc hψs
  have hweak' : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0, Lint α Ψ φ p)
        = ∫ p in Work.FTS.EllipticEst.Q0, Gint α F φ p := by
    intro φ h1 h2 h3
    simpa only [Lint, Gint] using hweak φ h1 h2 h3
  have hψr := contDiff_uncurry_reFun hψ
  have hψi := contDiff_uncurry_imFun hψ
  have hψrc := hasCompactSupport_uncurry_reFun hψc
  have hψic := hasCompactSupport_uncurry_imFun hψc
  have hψrs : tsupport (Function.uncurry (reFun ψ)) ⊆ stripRR :=
    subset_trans (tsupport_uncurry_reFun_subset ψ) hψs
  have hψis : tsupport (Function.uncurry (imFun ψ)) ⊆ stripRR :=
    subset_trans (tsupport_uncurry_imFun_subset ψ) hψs
  obtain ⟨φr, hφrsm, hφrc, hφrQ, hφrval, hφrbsl⟩ := hpull (reFun ψ) hψr hψrc hψrs
  obtain ⟨φi, hφism, hφic, hφiQ, hφival, hφibsl⟩ := hpull (imFun ψ) hψi hψic hψis
  have hTr : (∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr (reFun ψ) q.1 q.2)
      = ∫ q : ℝ × ℝ, GRR α F q.1 q.2 * reFun ψ q.1 q.2 :=
    transport_real hα hΨ hweak' hψr hψrc hψrs hφrsm hφrc hφrQ hφrval hφrbsl
  have hTi : (∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr (imFun ψ) q.1 q.2)
      = ∫ q : ℝ × ℝ, GRR α F q.1 q.2 * imFun ψ q.1 q.2 :=
    transport_real hα hΨ hweak' hψi hψic hψis hφism hφic hφiQ hφival hφibsl
  rw [integral_VRR_kopD hα hΨ hψ hψc hψs, hTr, hTi]
  by_cases hnd : Nondeg α Ψ
  · have hr : MeasureTheory.Integrable
        (fun q : ℝ × ℝ => GRR α F q.1 q.2 * reFun ψ q.1 q.2) :=
      (integrable_GRR_iff hα hφrval hφrQ).mpr
        (integrableOn_Gint_of_nondeg hα hΨ hweak' hnd hψr hψrc hψrs
          hφrsm hφrc hφrQ hφrval hφrbsl)
    have hi : MeasureTheory.Integrable
        (fun q : ℝ × ℝ => GRR α F q.1 q.2 * imFun ψ q.1 q.2) :=
      (integrable_GRR_iff hα hφival hφiQ).mpr
        (integrableOn_Gint_of_nondeg hα hΨ hweak' hnd hψi hψic hψis
          hφism hφic hφiQ hφival hφibsl)
    rw [integral_GRR_test hr hi]
  · have hzr : (∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr (reFun ψ) q.1 q.2) = 0 :=
      VRR_kopDr_eq_zero_of_not_nondeg hα hΨ hnd hψr hψrc hψrs hφrsm hφrc hφrQ hφrval hφrbsl
    have hzi : (∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr (imFun ψ) q.1 q.2) = 0 :=
      VRR_kopDr_eq_zero_of_not_nondeg hα hΨ hnd hψi hψic hψis hφism hφic hφiQ hφival hφibsl
    have hzr' : (∫ q : ℝ × ℝ, GRR α F q.1 q.2 * reFun ψ q.1 q.2) = 0 := by
      rw [← hTr]; exact hzr
    have hzi' : (∫ q : ℝ × ℝ, GRR α F q.1 q.2 * imFun ψ q.1 q.2) = 0 := by
      rw [← hTi]; exact hzi
    rw [hzr', hzi', Complex.ofReal_zero, mul_zero, add_zero]
    by_cases hint : MeasureTheory.Integrable
        (fun q : ℝ × ℝ => (GRR α F q.1 q.2 : ℂ) * ψ q.1 q.2)
    · rw [integral_GRR_test (integrable_re_of_complex hint) (integrable_im_of_complex hint),
        hzr', hzi', Complex.ofReal_zero, mul_zero, add_zero]
    · rw [MeasureTheory.integral_undef hint]

end Work.EllipticEst.InteriorRegularity.Q0
