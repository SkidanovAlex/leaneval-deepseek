import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.HaarSetup
import Submission.Work.EKLC6Core.haar_subgroup_pushforward
import Submission.Work.EKLC6Core.haar_conj_scaling
import Submission.Work.EKLC6Core.box_conjBox_subset
import Submission.Work.EKLC6Core.measurable_growthFun
import Submission.Work.EKLRelCross.horoUnimodular

/-!
# Haar measure on `U⁻(t)`: right translation invariance and conjugation scaling `≥ 1`

`Work.EKLC6Core.Uminus t` is the stable horospherical subgroup of `aDiag t`.  This module
provides a Radon measure `mU` on `SL₃(ℝ)` carried by `Uminus t`, positive on non-empty relatively
open subsets, finite on compacta, invariant under *right* translation by elements of `Uminus t`,
and scaled by a constant `c ≥ 1` under conjugation by `aDiag (-t)` (i.e. by `aDiag t⁻¹`, the
*expanding* direction of `Uminus t`).

`mU` is the push-forward of Haar measure along the inclusion `Uminus t ↪ SL₃(ℝ)`.

* The scaling relation under `conjBy (-t)` is Haar measure uniqueness applied to the
  automorphism `conjBy (-t)` of `Uminus t` (`Work.EKLC6Core.haar_conj_scaling`).
* `c ≥ 1` is proved without any computation of the scaling constant: the exponential factor of
  conjugation by `aDiag t` is `≤ 1` in every direction of `Uminus t`, so `B₁^U` is trapped by
  its own image under `conjBy (-t)` (`Work.EKLC6Core.box_conjBox_subset`); the scaling relation
  applied to `B₁^U` (which has positive, finite mass) therefore forces `c ≥ 1`.
* Right translation invariance is the unimodularity of the nilpotent group `Uminus t`: Haar
  measure is invariant under right translation by any element contracted by a flow of
  automorphisms (`Work.EKLRelCross.haar_map_mul_right_eq_self_of_tendsto_aut`).
-/

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open Work.EKLContract

theorem haar_uminus_data_right_scaling_ge_one (t : Fin 3 → ℝ) :
    ∃ (mU : MeasureTheory.Measure Work.EKLContract.SL3) (c : ENNReal),
      1 ≤ c ∧ c ≠ ⊤ ∧
      mU ((Work.EKLC6Core.Uminus t : Set Work.EKLContract.SL3))ᶜ = 0 ∧
      (∀ s : Set Work.EKLContract.SL3,
        (∃ o : Set Work.EKLContract.SL3, IsOpen o ∧
          s = o ∩ (Work.EKLC6Core.Uminus t : Set Work.EKLContract.SL3)) →
        s.Nonempty → 0 < mU s) ∧
      (∀ K : Set Work.EKLContract.SL3, IsCompact K → mU K ≠ ⊤) ∧
      (∀ u ∈ Work.EKLC6Core.Uminus t, ∀ s : Set Work.EKLContract.SL3,
        s ⊆ (Work.EKLC6Core.Uminus t : Set Work.EKLContract.SL3) → MeasurableSet s →
        mU ((fun g : Work.EKLContract.SL3 => g * u) '' s) = mU s) ∧
      (∀ s : Set Work.EKLContract.SL3,
        s ⊆ (Work.EKLC6Core.Uminus t : Set Work.EKLContract.SL3) → MeasurableSet s →
        mU (Work.EKLC6Core.conjBy (-t) s) = c * mU s) := by
  classical
  set U : Subgroup SL3 := Uminus t with hUdef
  have hHoro : IsHoro U := (uminus_isHoro t).1
  have hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (𝓝 1) :=
    (uminus_isHoro t).2
  have hUc : IsClosed (U : Set SL3) := hHoro.1
  haveI hLC3 : LocallyCompactSpace SL3 := SL3_locallyCompactSpace
  haveI hSC3 : SecondCountableTopology SL3 := SL3_secondCountableTopology
  haveI hLCU : LocallyCompactSpace ↥U := subgroup_locallyCompactSpace hUc
  haveI hSCU : SecondCountableTopology ↥U := subgroup_secondCountableTopology hUc
  haveI hBorU : BorelSpace ↥U := inferInstance
  let μ : Measure ↥U := Measure.haar
  haveI hHaar : μ.IsHaarMeasure := inferInstance
  -- `aDiag (-t)` normalises `Uminus t` in both directions
  have hneg : aDiag (-t) = (aDiag t)⁻¹ := (aDiag_inv_eq_neg t).symm
  have hinv : (aDiag (-t))⁻¹ = aDiag t := by rw [aDiag_inv_eq_neg, neg_neg]
  have hn : ∀ u ∈ U, aDiag (-t) * u * (aDiag (-t))⁻¹ ∈ U := fun u hu => hHoro.2.1 (-t) u hu
  have hn' : ∀ u ∈ U, (aDiag (-t))⁻¹ * u * aDiag (-t) ∈ U := by
    intro u hu
    rw [hinv, hneg]
    exact hHoro.2.1 t u hu
  -- #### the conjugation scaling for `conjBy (-t)`, and the Haar measure data
  obtain ⟨c, hc0, hct, hscale⟩ := haar_conj_scaling hUc (aDiag (-t)) hn hn' μ
  obtain ⟨hcar, hleft, hposOpen, hcomp⟩ := haar_subgroup_pushforward hUc μ
  -- #### positivity on relatively open subsets, in the form used by the statement
  have hpos' : ∀ s : Set SL3, (∃ o : Set SL3, IsOpen o ∧ s = o ∩ ↑U) →
      s.Nonempty → 0 < (μ.map (Subtype.val : ↥U → SL3)) s := by
    rintro s ⟨o, ho, rfl⟩ hsne
    have hemb : MeasurableEmbedding (Subtype.val : ↥U → SL3) :=
      MeasurableEmbedding.subtype_coe hUc.measurableSet
    rw [hemb.map_apply]
    have hpre : (Subtype.val : ↥U → SL3) ⁻¹' (o ∩ (U : Set SL3))
        = (Subtype.val : ↥U → SL3) ⁻¹' o := by ext x; simp
    rw [hpre]
    refine IsOpen.measure_pos μ (ho.preimage continuous_subtype_val) ?_
    obtain ⟨x, hx⟩ := hsne
    exact ⟨⟨x, hx.2⟩, hx.1⟩
  -- #### the flow of automorphisms `conj (aDiag t)^n` of `U`, contracting everything to `1`
  have hpow : ∀ n : ℕ, aDiag t ^ n = aDiag (fun k => (n : ℝ) * t k) :=
    fun n => Work.EKLContract.Lemmas.horoUij_aDiag_pow t n
  have hmem : ∀ n, ∀ u ∈ U, aDiag t ^ n * u * (aDiag t ^ n)⁻¹ ∈ U := by
    intro n u hu
    rw [hpow n]
    exact hHoro.2.1 (fun k => (n : ℝ) * t k) u hu
  have hmem' : ∀ n, ∀ u ∈ U, (aDiag t ^ n)⁻¹ * u * aDiag t ^ n ∈ U := by
    intro n u hu
    simpa only [hpow n, aDiag_inv_eq_neg, neg_neg] using
      hHoro.2.1 (-(fun k => (n : ℝ) * t k)) u hu
  let φ : ℕ → ↥U ≃ₜ* ↥U := fun n => conjContinuousMulEquiv U (aDiag t ^ n) (hmem n) (hmem' n)
  have hcoeφ : ∀ (n : ℕ) (v : ↥U),
      ((φ n v : ↥U) : SL3) = aDiag t ^ n * (v : SL3) * (aDiag t ^ n)⁻¹ := by
    intro n v
    show ((conjMulEquiv U (aDiag t ^ n) (hmem n) (hmem' n)) v : SL3)
      = aDiag t ^ n * (v : SL3) * (aDiag t ^ n)⁻¹
    rw [conjMulEquiv_apply]
  have hφtend : ∀ v : ↥U, Tendsto (fun n => φ n v) atTop (𝓝 1) := by
    intro v
    rw [tendsto_subtype_rng]
    have hfun : (fun n => ((φ n v : ↥U) : SL3)) =
        fun n => aDiag t ^ n * (v : SL3) * (aDiag t ^ n)⁻¹ := funext (fun n => hcoeφ n v)
    rw [hfun]
    simpa using hcontr v.1 v.2
  -- #### right translation invariance
  have hright_meas : ∀ u ∈ U, (μ.map (Subtype.val : ↥U → SL3)).map (fun g : SL3 => g * u)
      = μ.map (Subtype.val : ↥U → SL3) := by
    intro u hu
    rw [Measure.map_map (by fun_prop : Measurable (fun g : SL3 => g * u))
      continuous_subtype_val.measurable]
    rw [show (fun g : SL3 => g * u) ∘ (Subtype.val : ↥U → SL3)
        = (Subtype.val : ↥U → SL3) ∘ (fun x : ↥U => x * (⟨u, hu⟩ : ↥U)) from by
      funext x; rfl]
    rw [← Measure.map_map continuous_subtype_val.measurable
      (by fun_prop : Measurable (fun x : ↥U => x * (⟨u, hu⟩ : ↥U)))]
    rw [Work.EKLRelCross.haar_map_mul_right_eq_self_of_tendsto_aut μ (⟨u, hu⟩ : ↥U) φ
      (hφtend ⟨u, hu⟩)]
  have hright : ∀ u ∈ U, ∀ s : Set SL3, s ⊆ ↑U → MeasurableSet s →
      (μ.map (Subtype.val : ↥U → SL3)) ((fun g : SL3 => g * u) '' s)
        = (μ.map (Subtype.val : ↥U → SL3)) s := by
    intro u hu s _hsU hsm
    have h1 : (fun g : SL3 => g * u) '' s = (fun g : SL3 => g * u⁻¹) ⁻¹' s := by
      ext g; constructor
      · rintro ⟨h, hh, rfl⟩; show (h * u) * u⁻¹ ∈ s; rwa [mul_assoc, mul_inv_cancel, mul_one]
      · intro hg; exact ⟨g * u⁻¹, hg, by simp [mul_assoc]⟩
    rw [h1, ← Measure.map_apply (by fun_prop : Measurable (fun g : SL3 => g * u⁻¹)) hsm]
    rw [hright_meas u⁻¹ (U.inv_mem hu)]
  -- #### `c ≥ 1`, from the trapping `B₁^U ⊆ conjBy (-t) (B₁^U)`
  have hboxsub : (Box1 U : Set SL3) ⊆ conjBy (-t) (Box1 U) := by
    have h := (box_conjBox_subset hHoro hcontr).2
    simpa [conjBox] using h
  have hboxm : MeasurableSet (Box1 U : Set SL3) := (isClosed_box1 hHoro).measurableSet
  have hbcompress : (μ.map (Subtype.val : ↥U → SL3)) (Box1 U) ≤
      c * (μ.map (Subtype.val : ↥U → SL3)) (Box1 U) := by
    calc (μ.map (Subtype.val : ↥U → SL3)) (Box1 U)
        ≤ (μ.map (Subtype.val : ↥U → SL3)) (conjBy (-t) (Box1 U)) := measure_mono hboxsub
      _ = c * (μ.map (Subtype.val : ↥U → SL3)) (Box1 U) :=
          hscale (Box1 U) (fun g hg => hg.1) hboxm
  have hposBox : 0 < (μ.map (Subtype.val : ↥U → SL3)) (Box1 U) := by
    have hOp : IsOpen {g : SL3 | ∀ i j : Fin 3,
        |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 1} := by
      rw [show {g : SL3 | ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 1}
          = ⋂ i : Fin 3, ⋂ j : Fin 3,
              {g : SL3 | |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 1} by ext g; simp]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        isOpen_lt (by fun_prop) continuous_const
    have hne : ({g : SL3 | ∀ i j : Fin 3,
          |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 1}
        ∩ (U : Set SL3)).Nonempty := by
      refine ⟨1, ?_, U.one_mem⟩
      intro i j
      rcases eq_or_ne i j with h | h
      · subst h
        rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq]
        norm_num
      · rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne h, sub_self, abs_zero]
        norm_num
    have hsub : ({g : SL3 | ∀ i j : Fin 3,
          |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 1}
        ∩ (U : Set SL3)) ⊆ Box1 U := by
      intro g hg
      exact ⟨hg.2, fun i j => le_of_lt (hg.1 i j)⟩
    exact lt_of_lt_of_le (hpos' _ ⟨_, hOp, rfl⟩ hne) (measure_mono hsub)
  have hfinBox : (μ.map (Subtype.val : ↥U → SL3)) (Box1 U) ≠ ⊤ :=
    hcomp (Box1 U) (isCompact_box1 hHoro)
  have hc1 : 1 ≤ c := by
    have h := (ENNReal.div_le_iff_le_mul (Or.inr hct) (Or.inl hfinBox)).mpr hbcompress
    rwa [ENNReal.div_self hposBox.ne' hfinBox] at h
  exact ⟨_, c, hc1, hct, hcar, hpos', hcomp, hright, hscale⟩

end

end Work.EKLC6Core
