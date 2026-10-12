import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.memLp_top_modes` — the one-particle vectors are bounded a.e.

The companion of `Work.BoseBoxFock.memLp_modes` (which gives `L²`): the same three
families of one-particle vectors of the box model at the corpus box data
`Work.BoseK15.corpusBox` are `MemLp · ⊤`, i.e. bounded almost everywhere:

* `θ = 1_Λ` is the indicator of a measurable set of finite measure, hence bounded
  (`memLp_indicator_const`);
* `e^{isx} θ` is bounded by `1` on the compact box (`HasCompactSupport.memLp_of_bound`);
* `e^{ikx} χ_Λ` is continuous with compact support, hence bounded
  (`Continuous.memLp_of_hasCompactSupport`);
* `qVec ℓ k = e^{ikx}χ_Λ − χ̂(kℓ)·θ` is a difference of two `MemLp ⊤` functions.

The proofs are the same as in `memLp_modes`, with the exponent `2` replaced by `⊤`;
only `θ` needs the finiteness of the measure of the box, the other two are compactly
supported.  All the invoked library lemmas are stated for an arbitrary exponent, so
`⊤` goes through verbatim.
-/

namespace Work.BoseBoxFock

open MeasureTheory

/-- `θ = 1_Λ` is bounded: it is the indicator of a measurable set of finite volume. -/
private lemma memLp_top_thetaFun (B : Work.BoseB4.BoxData) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    MemLp (B.thetaFun ℓ) ⊤
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  classical
  have hne : volume (B.boxL ℓ) ≠ ⊤ := by
    rw [Work.BoseB4.BoxData.volume_boxL _ hℓ]
    exact ENNReal.ofReal_ne_top
  have h : MemLp ((B.boxL ℓ).indicator (fun _ => (1 : ℂ))) ⊤
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    memLp_indicator_const ⊤ (B.boxL_measurableSet ℓ) (1 : ℂ) (Or.inr hne)
  refine MemLp.ae_eq (g := B.thetaFun ℓ) ?_ h
  filter_upwards with x
  simp [Work.BoseB4.BoxData.thetaFun_apply, Set.indicator_apply]

/-- The oscillating phase `e^{i⟨s,·⟩}` is continuous. -/
private lemma continuous_cexp_inner (s : EuclideanSpace ℝ (Fin 3)) :
    Continuous fun x : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (Complex.I * ((inner ℝ s x : ℝ) : ℂ)) :=
  Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)))

/-- `e^{ikx}χ_Λ` is continuous with compact support (its support lies in the
compact box `Λ(ℓ)`), hence bounded a.e. -/
private lemma memLp_top_modeVec (B : Work.BoseB4.BoxData) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (k : EuclideanSpace ℝ (Fin 3)) :
    MemLp (B.modeVec ℓ k) ⊤
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  have hcont : Continuous (B.modeVec ℓ k) :=
    (continuous_cexp_inner k).mul (Complex.continuous_ofReal.comp (B.chiLam_cont ℓ))
  have hsupp : Function.support (B.modeVec ℓ k) ⊆ B.boxL ℓ := by
    intro x hx
    exact B.chiLam_supp hℓ (fun h0 => hx (by
      rw [Work.BoseB4.BoxData.modeVec_apply, h0, Complex.ofReal_zero, mul_zero]))
  have hcs : HasCompactSupport (B.modeVec ℓ k) :=
    (B.boxL_compact ℓ).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal hsupp (B.boxL_compact ℓ).isClosed)
  exact hcont.memLp_of_hasCompactSupport hcs

/-- `e^{isx}θ` is bounded by `1` and supported in the compact box `Λ(ℓ)`, hence
bounded a.e. -/
private lemma memLp_top_thetaExp (B : Work.BoseB4.BoxData) (ℓ : ℝ) (_hℓ : 0 < ℓ)
    (s : EuclideanSpace ℝ (Fin 3)) :
    MemLp (B.thetaExp ℓ s) ⊤
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  classical
  have hmeasθ : Measurable (B.thetaFun ℓ) := by
    convert (measurable_const.indicator (B.boxL_measurableSet ℓ) :
      Measurable ((B.boxL ℓ).indicator (fun _ => (1 : ℂ)))) using 1
    funext x
    simp [Work.BoseB4.BoxData.thetaFun_apply, Set.indicator_apply]
  have hmeas : AEStronglyMeasurable (B.thetaExp ℓ s) volume :=
    ((continuous_cexp_inner s).measurable.mul hmeasθ).aestronglyMeasurable
  have hbdd : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
      ‖B.thetaExp ℓ s x‖ ≤ 1 := by
    filter_upwards with x
    rw [Work.BoseB4.BoxData.thetaExp_apply]
    calc ‖Complex.exp (Complex.I * ((inner ℝ s x : ℝ) : ℂ)) * B.thetaFun ℓ x‖
        = ‖Complex.exp (Complex.I * ((inner ℝ s x : ℝ) : ℂ))‖ * ‖B.thetaFun ℓ x‖ :=
          norm_mul _ _
      _ = 1 * ‖B.thetaFun ℓ x‖ := by simp [Complex.norm_exp, Complex.mul_re]
      _ ≤ 1 := by
          rw [one_mul, Work.BoseB4.BoxData.thetaFun_apply]
          split_ifs <;> simp
  have hsupp : Function.support (B.thetaExp ℓ s) ⊆ B.boxL ℓ := by
    intro x hx
    by_contra hxin
    exact hx (by
      rw [Work.BoseB4.BoxData.thetaExp_apply, Work.BoseB4.BoxData.thetaFun_apply,
        if_neg hxin, mul_zero])
  have hcs : HasCompactSupport (B.thetaExp ℓ s) :=
    (B.boxL_compact ℓ).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal hsupp (B.boxL_compact ℓ).isClosed)
  exact hcs.memLp_of_bound hmeas 1 hbdd

/-- `qVec ℓ k = e^{ikx}χ_Λ − χ̂(kℓ)·θ` is bounded a.e., as a difference of two
bounded a.e. functions. -/
private lemma memLp_top_qVec (B : Work.BoseB4.BoxData) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (k : EuclideanSpace ℝ (Fin 3)) :
    MemLp (B.qVec ℓ k) ⊤
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  have h := (memLp_top_modeVec B ℓ hℓ k).sub
    ((memLp_top_thetaFun B ℓ hℓ).const_mul (((B.hatChi (ℓ • k) : ℝ) : ℂ)))
  refine MemLp.ae_eq (g := B.qVec ℓ k) ?_ h
  filter_upwards with x
  simp [Work.BoseB4.BoxData.qVec_apply]

theorem memLp_top_modes (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (∀ k : EuclideanSpace ℝ (Fin 3), MeasureTheory.MemLp (Work.BoseK15.corpusBox.qVec ℓ k) ⊤
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) ∧
    (∀ s : EuclideanSpace ℝ (Fin 3), MeasureTheory.MemLp (Work.BoseK15.corpusBox.thetaExp ℓ s) ⊤
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) ∧
    MeasureTheory.MemLp (Work.BoseK15.corpusBox.thetaFun ℓ) ⊤
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  exact ⟨fun k => memLp_top_qVec _ ℓ hℓ k,
    fun s => memLp_top_thetaExp _ ℓ hℓ s,
    memLp_top_thetaFun _ ℓ hℓ⟩

end Work.BoseBoxFock
