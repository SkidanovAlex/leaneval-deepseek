import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.horoUnimodular
import Submission.Work.EKLRelCross.propor_of_same_character
import Submission.Work.EKLRelCross.continuous_lintegral_comp_mul

/-!
# `Work.EKLRelCross.rightQuasiInv`

Let `U ≤ SL₃(ℝ)` be an admissible (horospherical) subgroup in the sense of
`Work.EKLContract.IsHoro`, and let `σ` be a non-zero Radon measure on `SL₃(ℝ)` which is carried
by `U` and is quasi-invariant under *left* translations by elements of `U`, with a cocycle
`χ : U → (0,∞)` (`σ.map (fun g => u * g) = χ u • σ`).  Then `σ` is also quasi-invariant under
*right* translations by elements of `U`.

The proof has three ingredients.

* The cocycle `χ` is multiplicative, hence a character `U → ℝ_{>0}`.
* `χ` is continuous:  `χ w · ∫⁻ F ∂σ = ∫⁻ x, F (w * x) ∂σ` and the right hand side is a
  continuous function of `w` (dominated convergence).
* Twisting `σ` by `χ` produces an exactly left-invariant Radon measure; two Radon measures with
  the same character are proportional (`Work.EKLRelCross.propor_of_same_character`).

Since `g ↦ g * u` commutes with left translations, the right translate of `σ` is again a
`χ`-quasi-invariant Radon measure carried by `U`, and the proportionality lemma finishes.
-/

namespace Work.EKLRelCross

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-- Two scalar multiples of a measure which agree on a set of non-zero finite measure have equal
scalars. -/
private lemma eq_of_smul_eq_smul_of_ne {ν : MeasureTheory.Measure Work.EKLContract.SL3}
    {A : Set Work.EKLContract.SL3} (hA0 : ν A ≠ 0) (hAt : ν A ≠ ⊤) {c₁ c₂ : ENNReal}
    (h : c₁ • ν = c₂ • ν) : c₁ = c₂ := by
  have h' := congrArg (fun (m : MeasureTheory.Measure Work.EKLContract.SL3) => m A) h
  simp only [MeasureTheory.Measure.smul_apply, smul_eq_mul] at h'
  exact (ENNReal.mul_left_inj hA0 hAt).mp h'

theorem rightQuasiInv (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U)
    (σ : MeasureTheory.Measure Work.EKLContract.SL3) (hrad : MeasureTheory.IsFiniteMeasureOnCompacts σ)
    (hcar : σ (U : Set Work.EKLContract.SL3)ᶜ = 0) (hne : σ ≠ 0)
    (hlq : ∀ u ∈ U, ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ σ.map (fun g => u * g) = c • σ) :
    ∀ u ∈ U, ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ σ.map (fun g => g * u) = c • σ := by
  classical
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts σ := hrad
  -- ## The cocycle
  let χ : ↥U → ENNReal := fun w => Classical.choose (hlq w.1 w.2)
  have hχspec : ∀ w : ↥U, σ.map (fun g => w.1 * g) = χ w • σ :=
    fun w => (Classical.choose_spec (hlq w.1 w.2)).2.2
  have hχ0 : ∀ w : ↥U, χ w ≠ 0 := fun w => (Classical.choose_spec (hlq w.1 w.2)).1
  have hχt : ∀ w : ↥U, χ w ≠ ⊤ := fun w => (Classical.choose_spec (hlq w.1 w.2)).2.1
  -- a compact set of positive finite measure
  obtain ⟨K, hKc, hKnz⟩ := MeasureTheory.Measure.InnerRegular.exists_isCompact_not_null.mpr hne
  have hKtop : σ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
  -- ## The cocycle is multiplicative
  have hχm : ∀ v w : ↥U, χ (v * w) = χ v * χ w := by
    intro v w
    have h1 : σ.map (fun g => (v * w).1 * g) = χ (v * w) • σ := hχspec (v * w)
    have h2 : σ.map (fun g => (v * w).1 * g) = (χ v * χ w) • σ := by
      have hcomp : (fun g : Work.EKLContract.SL3 => (v * w).1 * g)
          = (fun g : Work.EKLContract.SL3 => v.1 * g)
              ∘ (fun g : Work.EKLContract.SL3 => w.1 * g) :=
        funext fun g => mul_assoc v.1 w.1 g
      rw [hcomp, ← Measure.map_map (measurable_const_mul v.1) (measurable_const_mul w.1),
        hχspec w, Measure.map_smul, hχspec v, smul_smul, mul_comm] <;> try fun_prop
    exact eq_of_smul_eq_smul_of_ne hKnz hKtop (h1.symm.trans h2)
  -- ## A bounded continuous bump function
  obtain ⟨f, hfK, -, hfc, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hKc isClosed_empty (by simp)
  let F : Work.EKLContract.SL3 → ENNReal := fun x => ENNReal.ofReal (f x)
  have hFc : Continuous F := ENNReal.continuous_ofReal.comp f.continuous
  have hF1 : ∀ x, F x ≤ 1 := fun x => ENNReal.ofReal_le_one.mpr (hf01 x).2
  have hsupp : Function.support F = Function.support (⇑f) := by
    ext x
    simp only [Function.mem_support, ne_eq, F]
    rw [ENNReal.ofReal_eq_zero, not_le]
    exact ⟨fun h => ne_of_gt h, fun h => lt_of_le_of_ne (hf01 x).1 (Ne.symm h)⟩
  have hFs : HasCompactSupport F := by
    have h : tsupport F = tsupport (⇑f) := by rw [tsupport, tsupport, hsupp]
    show IsCompact (tsupport F)
    rw [h]; exact hfc
  have hkey : ∀ w : ↥U, ∫⁻ x, F (w.1 * x) ∂σ = χ w * (∫⁻ x, F x ∂σ) := by
    intro w
    rw [← MeasureTheory.lintegral_map hFc.measurable (measurable_const_mul w.1), hχspec w,
      MeasureTheory.lintegral_smul_measure, smul_eq_mul]
  have hBpos : 0 < ∫⁻ x, F x ∂σ := by
    have hle : ∀ x, K.indicator (fun _ => (1 : ENNReal)) x ≤ F x := by
      intro x
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]
        simp only [F, hfK hx, ENNReal.ofReal_one, Pi.one_apply]
        exact le_refl 1
      · rw [Set.indicator_of_notMem hx]; exact zero_le
    calc (0 : ENNReal) < σ K := pos_iff_ne_zero.mpr hKnz
      _ = ∫⁻ x, K.indicator (fun _ => (1 : ENNReal)) x ∂σ :=
            (MeasureTheory.lintegral_indicator_one hKmeas).symm
      _ ≤ ∫⁻ x, F x ∂σ := MeasureTheory.lintegral_mono hle
  have hBtop : ∫⁻ x, F x ∂σ ≠ ⊤ := by
    have hle : ∀ x, F x ≤ (tsupport F).indicator (fun _ => (1 : ENNReal)) x := by
      intro x
      by_cases hx : x ∈ tsupport F
      · rw [Set.indicator_of_mem hx]; exact hF1 x
      · rw [Set.indicator_of_notMem hx]
        have hz : F x = 0 := by
          by_contra hcon
          have hmem : x ∈ Function.support F := Function.mem_support.mpr hcon
          exact hx (subset_tsupport F hmem)
        rw [hz]
    have h1 : ∫⁻ x, F x ∂σ ≤ σ (tsupport F) :=
      calc ∫⁻ x, F x ∂σ ≤ ∫⁻ x, (tsupport F).indicator (fun _ => (1 : ENNReal)) x ∂σ :=
            MeasureTheory.lintegral_mono hle
        _ = σ (tsupport F) :=
            MeasureTheory.lintegral_indicator_one (isClosed_tsupport F).measurableSet
    exact ne_of_lt (lt_of_le_of_lt h1 hFs.isCompact.measure_lt_top)
  -- ## Continuity of `χ`
  have hχcont : Continuous χ := by
    have hG : Continuous (fun w : Work.EKLContract.SL3 => ∫⁻ x, F (w * x) ∂σ) :=
      continuous_lintegral_comp_mul σ hrad F hFc hF1 hFs
    have hkey' : χ = fun w : ↥U => (∫⁻ x, F (w.1 * x) ∂σ) * (∫⁻ x, F x ∂σ)⁻¹ := by
      funext w
      rw [hkey w, mul_assoc, ENNReal.mul_inv_cancel hBpos.ne' hBtop, mul_one]
    rw [hkey']
    exact (ENNReal.continuous_mul_const (ENNReal.inv_ne_top.mpr hBpos.ne')).comp
      (hG.comp continuous_subtype_val)
  -- ## Transfer to the subgroup
  have hUc : IsClosed (U : Set Work.EKLContract.SL3) := hU.1
  have hUmeas : MeasurableSet (U : Set Work.EKLContract.SL3) := hUc.measurableSet
  have hmval : Measurable (Subtype.val : ↥U → Work.EKLContract.SL3) :=
    continuous_subtype_val.measurable
  haveI : LocallyCompactSpace ↥U := hUc.locallyCompactSpace
  haveI : SecondCountableTopology ↥U :=
    TopologicalSpace.Subtype.secondCountableTopology (U : Set Work.EKLContract.SL3)
  let ν : MeasureTheory.Measure ↥U := MeasureTheory.Measure.comap (Subtype.val) σ
  have hνmap : ν.map (Subtype.val) = σ := by
    have h := (MeasurableEmbedding.subtype_coe hUmeas).map_comap σ
    rw [Subtype.range_coe] at h
    have h2 : σ.restrict (U : Set Work.EKLContract.SL3) = σ := by
      apply MeasureTheory.Measure.restrict_eq_self_of_ae_mem
      rw [ae_iff]
      convert hcar using 2
      all_goals (ext x; simp)
    exact h.trans h2
  haveI hνfin : MeasureTheory.IsFiniteMeasureOnCompacts ν :=
    IsFiniteMeasureOnCompacts.comap' σ continuous_subtype_val
      (MeasurableEmbedding.subtype_coe hUmeas)
  have hνne : ν ≠ 0 := by
    intro h0
    apply hne
    rw [← hνmap, h0, Measure.map_zero]
  have hνq : ∀ w : ↥U, ν.map (fun x => w * x) = χ w • ν := by
    intro w
    refine (MeasurableEmbedding.map_injective (MeasurableEmbedding.subtype_coe hUmeas)) ?_
    have hstep : Measure.map (Subtype.val) (Measure.map (fun x : ↥U => w * x) ν)
        = Measure.map (fun g : Work.EKLContract.SL3 => w.1 * g)
            (Measure.map (Subtype.val) ν) := by
      rw [Measure.map_map hmval (measurable_const_mul w)]
      rw [show (Subtype.val ∘ fun x : ↥U => w * x)
            = (fun g : Work.EKLContract.SL3 => w.1 * g) ∘
              (Subtype.val : ↥U → Work.EKLContract.SL3) from rfl]
      rw [← Measure.map_map (measurable_const_mul w.1) hmval]
    have hgoal : Measure.map (Subtype.val) (χ w • ν)
        = Measure.map (fun g : Work.EKLContract.SL3 => w.1 * g)
            (Measure.map (Subtype.val) ν) := by
      rw [Measure.map_smul, hνmap, hχspec w] <;> try fun_prop
    exact hstep.trans hgoal.symm
  -- ## Conclude
  have hmain : ∀ u : ↥U, ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ σ.map (fun g => g * u.1) = c • σ := by
    intro u
    haveI hνufin : MeasureTheory.IsFiniteMeasureOnCompacts (ν.map (fun x : ↥U => x * u)) := by
      have h := MeasureTheory.Measure.IsFiniteMeasureOnCompacts.map ν (Homeomorph.mulRight u)
      simpa using h
    have hνune : ν.map (fun x : ↥U => x * u) ≠ 0 := by
      intro h0
      exact hνne ((MeasureTheory.Measure.map_eq_zero_iff (μ := ν)
        (f := fun x : ↥U => x * u) (measurable_mul_const u).aemeasurable).mp h0)
    have hνuq : ∀ w : ↥U, (ν.map (fun x : ↥U => x * u)).map (fun x => w * x)
        = χ w • (ν.map (fun x : ↥U => x * u)) := by
      intro w
      have hcomm : (fun x : ↥U => w * x) ∘ (fun x : ↥U => x * u)
          = (fun x : ↥U => x * u) ∘ (fun x : ↥U => w * x) := by
        funext x; simp only [Function.comp_apply]; rw [mul_assoc]
      rw [Measure.map_map (measurable_const_mul w) (measurable_mul_const u), hcomm,
        ← Measure.map_map (measurable_mul_const u) (measurable_const_mul w), hνq w,
        Measure.map_smul] <;> try fun_prop
    obtain ⟨c, hc0, hct, hc⟩ :=
      propor_of_same_character χ hχcont hχ0 hχt hχm ν (ν.map (fun x : ↥U => x * u))
        hνfin hνufin hνne hνune hνq hνuq
    have hc' : ν.map (fun x : ↥U => x * u) = c⁻¹ • ν := by
      conv_rhs => rw [hc]
      rw [smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]
    have hσmap : σ.map (fun g : Work.EKLContract.SL3 => g * u.1)
        = (ν.map (fun x : ↥U => x * u)).map (Subtype.val) := by
      rw [← hνmap, Measure.map_map (measurable_mul_const u.1) hmval,
        Measure.map_map hmval (measurable_mul_const u)]
      congr 1
    exact ⟨c⁻¹, ENNReal.inv_ne_zero.mpr hct, ENNReal.inv_ne_top.mpr hc0, by
      rw [hσmap, hc', Measure.map_smul, hνmap] <;> try fun_prop⟩
  intro u hu
  exact hmain ⟨u, hu⟩

end Work.EKLRelCross
