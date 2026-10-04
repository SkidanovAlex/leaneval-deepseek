import Mathlib
import Submission.Work.OddBound.indexTransfer.Infra
import Submission.Work.OddBound.longHomotopy.integrableOn_curveSpeed_of_contMDiffOn_one
import Submission.Work.OddBound.polygonValue.curveSpeedEqOfAffineLength
import Submission.Work.OddBound.longHomotopy.curveLength_toolkit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cauchy–Schwarz for the interval integral of the Riemannian speed

For a curve `γ` of class `C¹` on `[0,S]` and `0 ≤ a ≤ b ≤ S`, the Cauchy–Schwarz inequality
(equivalently, Jensen's inequality for the convex function `x ↦ x²`) for the Riemannian speed
`curveSpeed γ` reads

`(∫_a^b curveSpeed γ)² ≤ (b - a) * ∫_a^b (curveSpeed γ)²`.

Since `curveSpeed γ` is defined through the *unrestricted* derivative `mfderiv`, whose junk value
`0` may occur at the two endpoints of `[0,S]`, the proof compares `curveSpeed γ` with the
continuous "within-interval" speed

`g t = √⟪(mfderivWithin 𝓘(ℝ) I γ (Icc 0 S) t) 1, (mfderivWithin 𝓘(ℝ) I γ (Icc 0 S) t) 1⟫`

(as in `curveLength_toolkit`).  The two functions agree on `Ioo 0 S`, hence on every `Ioo a b`,
and interval integrals only see `Ioo a b`, so both integrals may be replaced by the corresponding
integrals of `g`; the inequality for `g` is the elementary Cauchy–Schwarz inequality for the
integral of a continuous function.
-/

namespace Work.OddBound.indexTransfer

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle MeasureTheory

set_option linter.unusedVariables false in
/-- **Cauchy–Schwarz for the integral over `[a,b]`.**  For an interval-integrable `f` whose square
is interval-integrable, `(∫_a^b f)² ≤ (b - a) ∫_a^b f²`.

Proof: `0 ≤ ∫_a^b (f - t)² = ∫_a^b f² - 2 t ∫_a^b f + t² (b - a)` for every `t`; choosing
`t = (∫_a^b f)/(b - a)` (the case `a = b` being trivial) and multiplying by `b - a > 0` gives the
claim. -/
private theorem sq_intervalIntegral_le_of_integrable {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hf2 : IntervalIntegrable (fun s : ℝ => f s ^ 2) MeasureTheory.volume a b) :
    (∫ s in a..b, f s)^2 ≤ (b - a) * ∫ s in a..b, (f s)^2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    simp [intervalIntegral.integral_same]
  · have hD : 0 < b - a := sub_pos.mpr h
    set c : ℝ := ∫ s in a..b, f s with hc
    obtain ⟨t, ht⟩ : ∃ t : ℝ, (b - a) * t = c := ⟨c / (b - a), by field_simp⟩
    have hI2 : IntervalIntegrable (fun s : ℝ => f s ^ 2) MeasureTheory.volume a b := hf2
    have hItf : IntervalIntegrable (fun s : ℝ => (2 * t) * f s) MeasureTheory.volume a b :=
      hf.const_mul (2 * t)
    have hItt : IntervalIntegrable (fun s : ℝ => t * t) MeasureTheory.volume a b :=
      intervalIntegrable_const
    have e0 : ∫ s in a..b, (f s - t) ^ 2 = ∫ s in a..b, f s ^ 2 - 2 * t * f s + t * t :=
      intervalIntegral.integral_congr_Ioo_of_le hab (fun s _ => by ring)
    have key : ∫ s in a..b, (f s - t) ^ 2
        = (∫ s in a..b, f s ^ 2) - (2 * t) * c + (b - a) * (t * t) := by
      rw [e0]
      rw [intervalIntegral.integral_add (hI2.sub hItf) hItt]
      rw [intervalIntegral.integral_sub hI2 hItf]
      rw [intervalIntegral.integral_const_mul (2 * t) f]
      rw [intervalIntegral.integral_const, smul_eq_mul]
    have hnn : 0 ≤ (∫ s in a..b, f s ^ 2) - (2 * t) * c + (b - a) * (t * t) :=
      key ▸ intervalIntegral.integral_nonneg_of_forall hab (fun u => sq_nonneg (f u - t))
    have hmul := mul_nonneg (le_of_lt hD) hnn
    have hexp : (b - a) * ((∫ s in a..b, f s ^ 2) - (2 * t) * c + (b - a) * (t * t))
        = (b - a) * (∫ s in a..b, f s ^ 2) - c ^ 2 := by
      calc (b - a) * ((∫ s in a..b, f s ^ 2) - (2 * t) * c + (b - a) * (t * t))
          = (b - a) * (∫ s in a..b, f s ^ 2) - 2 * ((b - a) * t) * c
              + ((b - a) * t) * ((b - a) * t) := by ring
        _ = (b - a) * (∫ s in a..b, f s ^ 2) - 2 * c * c + c * c := by rw [ht]
        _ = (b - a) * (∫ s in a..b, f s ^ 2) - c ^ 2 := by ring
    have := hexp ▸ hmul
    linarith

set_option linter.unusedVariables false in
/-- **Cauchy–Schwarz for a function continuous on `[a,b]`.** -/
private theorem sq_intervalIntegral_le_of_continuousOn {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    (∫ s in a..b, g s)^2 ≤ (b - a) * ∫ s in a..b, (g s)^2 := by
  have hg2 : ContinuousOn (fun s : ℝ => g s ^ 2) (Set.Icc a b) := hg.pow 2
  have h1 : IntervalIntegrable g MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      ((hg.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)
  have h2 : IntervalIntegrable (fun s : ℝ => g s ^ 2) MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      ((hg2.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)
  exact sq_intervalIntegral_le_of_integrable hab h1 h2

theorem sq_intervalIntegral_curveSpeed_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {γ : ℝ → M} {S : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc (0 : ℝ) S))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ S) :
    (∫ s in a..b, Submission.Length.curveSpeed (I := I) γ s)^2
      ≤ (b - a) * ∫ s in a..b, (Submission.Length.curveSpeed (I := I) γ s)^2 := by
  rcases lt_or_ge (0 : ℝ) S with hS | hS
  · -- Main case `0 < S`: compare with the continuous "within-interval" speed.
    haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) := by
      obtain ⟨Φ, hΦsm, hΦ⟩ :=
        (inferInstance : IsContMDiffRiemannianBundle I ∞ E
          (fun x : M ↦ TangentSpace I x)).exists_contMDiff
      exact ⟨Φ, hΦsm.continuous, hΦ⟩
    set s : Set ℝ := Set.Icc (0 : ℝ) S with hsdef
    have hs_umd : UniqueMDiff[s] := UniqueDiffOn.uniqueMDiffOn (uniqueDiffOn_Icc hS)
    -- The tangent map of `γ` within `[0,S]` is continuous.
    have htan : ContinuousOn (tangentMapWithin 𝓘(ℝ) I γ s) (Bundle.TotalSpace.proj ⁻¹' s) :=
      hγ.continuousOn_tangentMapWithin le_rfl hs_umd
    -- The constant unit section of the tangent bundle of the model space `ℝ`.
    have hκ : ContinuousOn (fun t : ℝ => (Bundle.TotalSpace.mk' ℝ t (1 : TangentSpace 𝓘(ℝ) t) :
        TangentBundle 𝓘(ℝ) ℝ)) s :=
      ((contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (n := ∞) (E := ℝ)
        (V := fun t : ℝ => (1 : TangentSpace 𝓘(ℝ) t))).mpr contDiff_const).continuous.continuousOn
    have hcomp : ContinuousOn (fun t : ℝ =>
        (⟨γ t, (mfderivWithin 𝓘(ℝ) I γ s t) (1 : ℝ)⟩ : TangentBundle I M)) s :=
      htan.comp hκ (fun t ht => by simpa using ht)
    -- The "within-interval" speed.
    set g : ℝ → ℝ := fun t => Real.sqrt
      (inner ℝ ((mfderivWithin 𝓘(ℝ) I γ s t) (1 : ℝ))
        ((mfderivWithin 𝓘(ℝ) I γ s t) (1 : ℝ))) with hgdef
    have hgcont : ContinuousOn g s := (ContinuousOn.inner_bundle (b := γ) hcomp hcomp).sqrt
    -- It agrees with `curveSpeed γ` on the interior of `[0,S]`.
    have hgspeed : ∀ t ∈ Set.Ioo (0 : ℝ) S, g t = Submission.Length.curveSpeed (I := I) γ t := by
      intro t ht
      have hmem : s ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
      show Real.sqrt (inner ℝ ((mfderivWithin 𝓘(ℝ) I γ s t) (1 : ℝ))
        ((mfderivWithin 𝓘(ℝ) I γ s t) (1 : ℝ))) = Submission.Length.curveSpeed (I := I) γ t
      rw [mfderivWithin_of_mem_nhds hmem, Submission.Length.curveSpeed_def,
        Submission.Geodesic.curveVelocity_apply]
    have hsub : Set.Icc a b ⊆ s := Set.Icc_subset_Icc ha hb
    -- Both integrals only see `Ioo a b`, where the two functions agree.
    have e1 : ∫ t in a..b, Submission.Length.curveSpeed (I := I) γ t = ∫ t in a..b, g t :=
      intervalIntegral.integral_congr_Ioo_of_le hab
        (fun t ht => (hgspeed t (Set.Ioo_subset_Ioo ha hb ht)).symm)
    have e2 : ∫ t in a..b, (Submission.Length.curveSpeed (I := I) γ t) ^ 2
        = ∫ t in a..b, (g t) ^ 2 :=
      intervalIntegral.integral_congr_Ioo_of_le hab
        (fun t ht => by rw [hgspeed t (Set.Ioo_subset_Ioo ha hb ht)])
    calc (∫ t in a..b, Submission.Length.curveSpeed (I := I) γ t) ^ 2
        = (∫ t in a..b, g t) ^ 2 := by rw [e1]
      _ ≤ (b - a) * ∫ t in a..b, (g t) ^ 2 :=
          sq_intervalIntegral_le_of_continuousOn hab (hgcont.mono hsub)
      _ = (b - a) * ∫ t in a..b, (Submission.Length.curveSpeed (I := I) γ t) ^ 2 := by rw [e2]
  · -- Degenerate case `S ≤ 0`: the hypotheses force `a = b = 0`.
    have ha0 : a = 0 := le_antisymm (le_trans hab (le_trans hb hS)) ha
    have hb0 : b = 0 := le_antisymm (le_trans hb hS) (le_trans ha hab)
    subst ha0
    subst hb0
    simp [intervalIntegral.integral_same]

end Work.OddBound.indexTransfer
