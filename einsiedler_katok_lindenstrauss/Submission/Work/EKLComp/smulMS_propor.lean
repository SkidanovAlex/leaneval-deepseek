import Mathlib
import Submission.Work.EKLC7.SmulMS
import Submission.Work.EKLC7.isPlaqueAlgebra_smulMS
import Submission.Work.EKLC7.restrict_smulSt
import Submission.Work.EKLRelCross.condExp_comap_aDiag
import Submission.Work.EKLComp.LeafAux
import Submission.Work.EKLC6Core.shape_mass_pos
import Submission.Work.EKLRelCross.restrict_eq_of_pushforward_relation

/-!
# `Work.EKLComp.smulMS_propor`

Proportionality of a system of leafwise measures under the translation `x ↦ u • x` with `u ∈ U`,
on the shape of a plaque algebra: for `μ ↾ Z`-a.e. `x` with `x, u • x` in the conull domain of
the leafwise system,

`((ν (u • x)).map (g ↦ u⁻¹ * g * u)) ↾ shape m U x = c • (ν x) ↾ shape m U x`.

The proof compares the `condexp` field of `IsLeafwise` at `(Z, m)` and at the *translated* plaque
algebra `(smulSt u Z, smulMS u m)` (transported by `Work.EKLC7.isPlaqueAlgebra_smulMS`), using
the naturality of the conditional expectation along the measure preserving map `y ↦ u⁻¹ • y`
(`Work.EKLRelCross.condExp_comap_of_measurePreserving`, which uses `IsUInvariant μ U`).  The two
integrals are matched by the change of variables `ξ = u g u⁻¹`, which pulls the leafwise measure
`ν (u • x)` back to the conjugated measure `(ν (u • x)).map (g ↦ u⁻¹ * g * u)` on `shape m U x`.
Testing the resulting identity on the countable π-system `Work.EKLComp.piBasis` (which generates
the Borel σ-algebra of `X₃`) gives the proportionality of the two push-forwards along the orbit
map `g ↦ u • (g • x)`; that map is the composition of the left translation `g ↦ u * g` (a
homeomorphism) with the orbit map `g ↦ g • x`, which is injective on `U` because `x` has trivial
stabiliser in `U` (`Work.EKLRelCross.map_smul_injective_of_free`), so the translation can be
cancelled.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace Work.EKLComp

open Work.EKLContract

/-- The set integral of the indicator of `B` along a measurable map `ψ` is the mass of `B` for
the push-forward of `ρ ↾ W` under `ψ`. -/
theorem setIntegral_indicator_eq_map_apply {ψ : SL3 → X3} (hψ : Measurable ψ) (ρ : Measure SL3)
    {W : Set SL3} {B : Set X3} (hW : MeasurableSet W) (hB : MeasurableSet B) :
    (∫ g in W, (B.indicator fun _ => (1 : ℝ)) (ψ g) ∂ρ)
      = ((ρ.restrict W).map ψ B).toReal := by
  classical
  have hpre : MeasurableSet (ψ ⁻¹' B) := hB.preimage hψ
  have hfun : (fun g : SL3 => (B.indicator fun _ => (1 : ℝ)) (ψ g))
      = (ψ ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
    funext g
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : ψ g ∈ B <;> simp [h]
  rw [hfun, MeasureTheory.setIntegral_indicator hpre, MeasureTheory.setIntegral_const,
    smul_eq_mul, mul_one, MeasureTheory.measureReal_def]
  rw [Measure.map_apply hψ hB, Measure.restrict_apply' hW, Set.inter_comm]

theorem smulMS_propor (h2 : Work.EKLContract.P_X3) {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (U : Subgroup Work.EKLContract.SL3)
    (hU : Work.EKLContract.IsHoro U) (hinv : Work.EKLContract.IsUInvariant μ U)
    {u : Work.EKLContract.SL3} (hu : u ∈ U)
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hfree : ∀ᵐ x ∂μ, ∀ w ∈ U, w • x = x → w = 1)
    {Z : Set Work.EKLContract.X3} {m : MeasurableSpace Work.EKLContract.X3}
    (hpa : Work.EKLContract.IsPlaqueAlgebra U Z m) :
    ∀ᵐ x ∂(μ.restrict Z), x ∈ X' → u • x ∈ X' →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ((ν (u • x)).map (fun g : Work.EKLContract.SL3 => u⁻¹ * g * u)).restrict
            (Work.EKLContract.shape m U x)
          = c • (ν x).restrict (Work.EKLContract.shape m U x) := by
  classical
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  set Z' : Set X3 := Work.EKLC7.smulSt u Z with hZ'def
  have hZmeas : MeasurableSet Z := hpa.1 Z hpa.2.2.1
  have hmle : m ≤ borel X3 := hpa.1
  have hpla' : IsPlaqueAlgebra U Z' (Work.EKLC7.smulMS u m) := by
    rw [hZ'def]
    exact Work.EKLC7.isPlaqueAlgebra_smulMS hu hpa
  have hZ'meas : MeasurableSet Z' := by
    have h : Z' = (fun y : X3 => u⁻¹ • y) ⁻¹' Z := by
      rw [hZ'def]
      ext y
      rw [Work.EKLC7.smulSt_mem, Set.mem_preimage]
    rw [h]
    exact hZmeas.preimage (continuous_const_smul u⁻¹).measurable
  have huxZ' : ∀ x : X3, x ∈ Z → u • x ∈ Z' := by
    intro x hx
    rw [hZ'def, Work.EKLC7.smulSt]
    exact ⟨x, hx, rfl⟩
  -- measurability of the conjugation, translation and orbit maps
  have hΦmeas : Measurable (fun g : SL3 => u * g * u⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hΨmeas : Measurable (fun g : SL3 => u⁻¹ * g * u) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hLmeas : Measurable (fun g : SL3 => u * g) :=
    (continuous_const.mul continuous_id).measurable
  have hLinvmeas : Measurable (fun g : SL3 => u⁻¹ * g) :=
    (continuous_const.mul continuous_id).measurable
  have hφmeas : ∀ y : X3, Measurable (fun g : SL3 => g • y) :=
    fun y => (continuous_id.smul continuous_const).measurable
  -- the key a.e. identity, on the indicators of the countable π-system
  have hkey : ∀ᵐ x ∂μ, ∀ B ∈ piBasis, x ∈ Z →
      (∫ a in shape m U x, (B.indicator fun _ => (1 : ℝ)) (u • (a • x)) ∂(ν x))
          / ((ν x) (shape m U x)).toReal
        = (∫ ξ in shape (Work.EKLC7.smulMS u m) U (u • x),
              (B.indicator fun _ => (1 : ℝ)) (ξ • (u • x)) ∂(ν (u • x)))
          / ((ν (u • x)) (shape (Work.EKLC7.smulMS u m) U (u • x))).toReal := by
    rw [eventually_countable_ball countable_piBasis]
    intro B hB
    have hBmeas : MeasurableSet B := measurableSet_of_mem_piBasis hB
    have hFmeas : Measurable (B.indicator fun _ => (1 : ℝ)) :=
      Measurable.indicator measurable_const hBmeas
    have hFbdd : ∃ C, ∀ y, |(B.indicator fun _ => (1 : ℝ)) y| ≤ C :=
      ⟨1, fun y => by rw [Set.indicator_apply]; split <;> simp⟩
    have hgmeas : Measurable ((B.indicator fun _ => (1 : ℝ)) ∘ (fun z : X3 => u • z)) :=
      hFmeas.comp (continuous_const_smul u).measurable
    have hgbdd : ∃ C, ∀ y, |((B.indicator fun _ => (1 : ℝ)) ∘ (fun z : X3 => u • z)) y| ≤ C :=
      ⟨1, fun y => by rw [Function.comp_apply, Set.indicator_apply]; split <;> simp⟩
    -- the `condexp` field at `(Z, m)`
    have hc1 : ∀ᵐ z ∂(μ.restrict Z),
        condExp m (μ.restrict Z) ((B.indicator fun _ => (1 : ℝ)) ∘ (fun z : X3 => u • z)) z
          = (∫ a in shape m U z,
                ((B.indicator fun _ => (1 : ℝ)) ∘ (fun z : X3 => u • z)) (a • z) ∂(ν z))
              / ((ν z) (shape m U z)).toReal :=
      hL.condexp Z m hpa _ hgmeas hgbdd
    have h1 : ∀ᵐ x ∂μ, x ∈ Z →
        condExp m (μ.restrict Z) ((B.indicator fun _ => (1 : ℝ)) ∘ (fun z : X3 => u • z)) x
          = (∫ a in shape m U x, (B.indicator fun _ => (1 : ℝ)) (u • (a • x)) ∂(ν x))
              / ((ν x) (shape m U x)).toReal := by
      filter_upwards [(ae_restrict_iff' hZmeas).mp hc1] with x hx hxZ
      simpa only [Function.comp_apply] using hx hxZ
    -- the `condexp` field at the translated plaque algebra, at the point `u • x`
    have hc2 : ∀ᵐ y ∂(μ.restrict Z'), condExp (Work.EKLC7.smulMS u m) (μ.restrict Z')
        (B.indicator fun _ => (1 : ℝ)) y
          = (∫ ξ in shape (Work.EKLC7.smulMS u m) U y,
                (B.indicator fun _ => (1 : ℝ)) (ξ • y) ∂(ν y))
              / ((ν y) (shape (Work.EKLC7.smulMS u m) U y)).toReal :=
      hL.condexp Z' (Work.EKLC7.smulMS u m) hpla' _ hFmeas hFbdd
    have h2 : ∀ᵐ x ∂μ, x ∈ Z →
        condExp (Work.EKLC7.smulMS u m) (μ.restrict Z')
            (B.indicator fun _ => (1 : ℝ)) (u • x)
          = (∫ ξ in shape (Work.EKLC7.smulMS u m) U (u • x),
                (B.indicator fun _ => (1 : ℝ)) (ξ • (u • x)) ∂(ν (u • x)))
              / ((ν (u • x)) (shape (Work.EKLC7.smulMS u m) U (u • x))).toReal := by
      have h := (ae_restrict_iff' hZ'meas).mp hc2
      have h' := (hinv u hu).quasiMeasurePreserving.ae h
      filter_upwards [h'] with x hx hxZ
      exact hx (huxZ' x hxZ)
    -- naturality of the conditional expectation along `y ↦ u⁻¹ • y`
    have hnat : ∀ᵐ y ∂(μ.restrict Z'),
        condExp (Work.EKLC7.smulMS u m) (μ.restrict Z')
            (B.indicator fun _ => (1 : ℝ)) y
          = condExp m (μ.restrict Z)
              ((B.indicator fun _ => (1 : ℝ)) ∘ (fun z : X3 => u • z)) (u⁻¹ • y) := by
      have h := Work.EKLRelCross.condExp_comap_of_measurePreserving
        Work.EKLContract.instMeasurableSpaceX3 (fun y : X3 => u⁻¹ • y) μ
        (hinv u⁻¹ (U.inv_mem hu)) m hmle hpa.2.2.1 hgmeas hgbdd
      have hpreZ : (fun y : X3 => u⁻¹ • y) ⁻¹' Z = Z' := by
        rw [hZ'def]
        ext y
        rw [Work.EKLC7.smulSt_mem, Set.mem_preimage]
      have hcomap : MeasurableSpace.comap (fun y : X3 => u⁻¹ • y) m
          = Work.EKLC7.smulMS u m := rfl
      have hcomp : ((B.indicator fun _ => (1 : ℝ)) ∘ (fun z : X3 => u • z))
          ∘ (fun y : X3 => u⁻¹ • y) = (B.indicator fun _ => (1 : ℝ)) := by
        funext y
        simp only [Function.comp_apply, smul_inv_smul]
      rw [hpreZ, hcomap, hcomp] at h
      exact h
    have hnatμ : ∀ᵐ x ∂μ, x ∈ Z →
        condExp (Work.EKLC7.smulMS u m) (μ.restrict Z')
            (B.indicator fun _ => (1 : ℝ)) (u • x)
          = condExp m (μ.restrict Z)
              ((B.indicator fun _ => (1 : ℝ)) ∘ (fun z : X3 => u • z)) x := by
      have h := (ae_restrict_iff' hZ'meas).mp hnat
      have h' := (hinv u hu).quasiMeasurePreserving.ae h
      filter_upwards [h'] with x hx hxZ
      have hx' := hx (huxZ' x hxZ)
      simpa using hx'
    filter_upwards [h1, h2, hnatμ] with x h1x h2x h3x hxZ
    exact (h1x hxZ).symm.trans ((h3x hxZ).symm.trans (h2x hxZ))
  -- main part
  have hmain : ∀ᵐ x ∂μ, x ∈ Z →
      (x ∈ X' → u • x ∈ X' →
        ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
          ((ν (u • x)).map (fun g : SL3 => u⁻¹ * g * u)).restrict (shape m U x)
            = c • (ν x).restrict (shape m U x)) := by
    filter_upwards [hkey, hfree] with x hxkey hxfree hxZ hxX huxX
    set S₀ : Set SL3 := shape m U x with hS₀
    set St : Set SL3 := shape (Work.EKLC7.smulMS u m) U (u • x) with hSt
    set A : Measure SL3 := (ν (u • x)).map (fun g : SL3 => u⁻¹ * g * u) with hA
    set ψ : SL3 → X3 := fun g => u • (g • x) with hψ
    have hψmeas : Measurable ψ := by
      rw [hψ]
      exact (continuous_const_smul u).measurable.comp (hφmeas x)
    set ρ : Measure SL3 := A.restrict S₀ with hρ
    set ρ' : Measure SL3 := (ν x).restrict S₀ with hρ'
    -- measurability of the two shapes
    have hS₀meas : MeasurableSet S₀ := by
      obtain ⟨O, hO, hOsh⟩ := (hpa.2.2.2 x hxZ).2.2.1
      rw [hS₀, hOsh]
      exact hO.measurableSet.inter hU.1.measurableSet
    have hStmeas : MeasurableSet St := by
      obtain ⟨O, hO, hOsh⟩ := (hpla'.2.2.2 (u • x) (huxZ' x hxZ)).2.2.1
      rw [hSt, hOsh]
      exact hO.measurableSet.inter hU.1.measurableSet
    -- masses
    have hmass₀ : 0 < ν x S₀ ∧ ν x S₀ < ⊤ := by
      have h := Work.EKLC6Core.shape_mass_pos (A := m) (Z := Z) hL hpa hxX hxZ
      simpa only [← hS₀] using h
    have hmass₁ : 0 < ν (u • x) St ∧ ν (u • x) St < ⊤ := by
      have h := Work.EKLC6Core.shape_mass_pos (A := Work.EKLC7.smulMS u m) (Z := Z') hL hpla'
        huxX (huxZ' x hxZ)
      simpa only [← hSt] using h
    -- the conjugation change of variables
    have hAΦ : A.map (fun g : SL3 => u * g * u⁻¹) = ν (u • x) := by
      rw [hA, Measure.map_map hΦmeas hΨmeas]
      have hcomp : (fun g : SL3 => u * g * u⁻¹) ∘ (fun g : SL3 => u⁻¹ * g * u) = id := by
        funext g
        show u * (u⁻¹ * g * u) * u⁻¹ = g
        group
      rw [hcomp, Measure.map_id]
    have hpreΦ : (fun g : SL3 => u * g * u⁻¹) ⁻¹' St = S₀ := by
      have hconj : St = (fun g : SL3 => u * g * u⁻¹) '' S₀ := by
        rw [hSt, hS₀]
        exact Work.EKLC7.shape_smulMS_conj (U := U) (u := u) hu m x
      rw [hconj]
      ext g
      constructor
      · intro hg
        rw [Set.mem_preimage] at hg
        rw [Set.mem_image] at hg
        obtain ⟨w, hw, hwg⟩ := hg
        have h2 : g = w := by
          have h3 := congrArg (fun t : SL3 => u⁻¹ * t * u) hwg
          have h4 : u⁻¹ * (u * g * u⁻¹) * u = g := by group
          have h5 : u⁻¹ * (u * w * u⁻¹) * u = w := by group
          rw [h4, h5] at h3
          exact h3.symm
        rw [h2]
        exact hw
      · intro hg
        rw [Set.mem_preimage, Set.mem_image]
        exact ⟨g, hg, rfl⟩
    have hASt : A S₀ = ν (u • x) St := by
      have h1 : A S₀ = (A.map (fun g : SL3 => u * g * u⁻¹)) St := by
        rw [Measure.map_apply hΦmeas hStmeas, hpreΦ]
      rw [h1, hAΦ]
    -- the substitution identity
    have hsubst : ∀ B : Set X3, MeasurableSet B →
        (∫ ξ in St, (B.indicator fun _ => (1 : ℝ)) (ξ • (u • x)) ∂(ν (u • x)))
          = ∫ g in S₀, (B.indicator fun _ => (1 : ℝ)) (u • (g • x)) ∂A := by
      intro B hB
      have hFmeas : Measurable (fun ξ : SL3 => (B.indicator fun _ => (1 : ℝ)) (ξ • (u • x))) :=
        (measurable_const.indicator hB).comp
          ((continuous_id.smul continuous_const).measurable)
      have h := MeasureTheory.setIntegral_map (μ := A)
        (g := fun g : SL3 => u * g * u⁻¹)
        (f := fun ξ : SL3 => (B.indicator fun _ => (1 : ℝ)) (ξ • (u • x))) hStmeas
        hFmeas.aestronglyMeasurable hΦmeas.aemeasurable
      rw [hAΦ, hpreΦ] at h
      rw [h]
      refine MeasureTheory.setIntegral_congr_fun hS₀meas (fun g _ => ?_)
      show (B.indicator fun _ => (1 : ℝ)) ((u * g * u⁻¹) • (u • x))
        = (B.indicator fun _ => (1 : ℝ)) (u • (g • x))
      have harg : (u * g * u⁻¹) • (u • x) = u • (g • x) := by
        rw [mul_smul, mul_smul]
        congr 1
        rw [inv_smul_smul]
      rw [harg]
    -- proportionality of the push-forwards on the π-system
    set θ : ENNReal := ν (u • x) St / ν x S₀ with hθ
    have hθ0 : θ ≠ 0 := (ENNReal.div_ne_zero).mpr ⟨ne_of_gt hmass₁.1, ne_of_lt hmass₀.2⟩
    have hθT : θ ≠ ⊤ := ENNReal.div_ne_top (ne_of_lt hmass₁.2) (ne_of_gt hmass₀.1)
    have hprop : ∀ B ∈ piBasis, (ρ.map ψ) B = θ * (ρ'.map ψ) B := by
      intro B hB
      have hBmeas : MeasurableSet B := measurableSet_of_mem_piBasis hB
      have hk := hxkey B hB hxZ
      simp only [← hS₀, ← hSt] at hk
      have hL1 : (∫ a in S₀, (B.indicator fun _ => (1 : ℝ)) (u • (a • x)) ∂(ν x))
          = ((ρ'.map ψ) B).toReal := by
        rw [setIntegral_indicator_eq_map_apply hψmeas (ν x) hS₀meas hBmeas, ← hρ']
      have hR : (∫ ξ in St, (B.indicator fun _ => (1 : ℝ)) (ξ • (u • x)) ∂(ν (u • x)))
          = ((ρ.map ψ) B).toReal := by
        rw [hsubst B hBmeas, setIntegral_indicator_eq_map_apply hψmeas A hS₀meas hBmeas, ← hρ]
      rw [hL1, hR] at hk
      have hr0 : (ν x S₀).toReal ≠ 0 := by
        simp only [ENNReal.toReal_ne_zero]
        exact ⟨ne_of_gt hmass₀.1, ne_of_lt hmass₀.2⟩
      have hr1 : (ν (u • x) St).toReal ≠ 0 := by
        simp only [ENNReal.toReal_ne_zero]
        exact ⟨ne_of_gt hmass₁.1, ne_of_lt hmass₁.2⟩
      have hcross : ((ρ'.map ψ) B).toReal * (ν (u • x) St).toReal
          = ((ρ.map ψ) B).toReal * (ν x S₀).toReal :=
        (div_eq_div_iff hr0 hr1).mp hk
      have hB1 : (ρ.map ψ) B ≤ ν (u • x) St := by
        rw [hρ, Measure.map_apply hψmeas hBmeas, Measure.restrict_apply' hS₀meas]
        calc A ((fun g : SL3 => u • (g • x)) ⁻¹' B ∩ S₀)
            ≤ A S₀ := measure_mono Set.inter_subset_right
          _ = ν (u • x) St := hASt
      have hB2 : (ρ'.map ψ) B ≤ ν x S₀ := by
        rw [hρ', Measure.map_apply hψmeas hBmeas, Measure.restrict_apply' hS₀meas]
        exact measure_mono Set.inter_subset_right
      have hf1 : (ρ.map ψ) B ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hB1 hmass₁.2)
      have hf2 : (ρ'.map ψ) B ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hB2 hmass₀.2)
      have hprod : (((ρ'.map ψ) B) * (ν (u • x) St)).toReal
          = (((ρ.map ψ) B) * (ν x S₀)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
        exact hcross
      have ha : ((ρ'.map ψ) B) * (ν (u • x) St) ≠ ⊤ :=
        ENNReal.mul_ne_top hf2 (ne_of_lt hmass₁.2)
      have hb : ((ρ.map ψ) B) * (ν x S₀) ≠ ⊤ := ENNReal.mul_ne_top hf1 (ne_of_lt hmass₀.2)
      have hENN : ((ρ'.map ψ) B) * (ν (u • x) St) = ((ρ.map ψ) B) * (ν x S₀) := by
        rcases (ENNReal.toReal_eq_toReal_iff _ _).mp hprod with h | h | h
        · exact h
        · exact absurd h.2 hb
        · exact absurd h.1 ha
      calc (ρ.map ψ) B = (ρ.map ψ) B * (ν x S₀) * (ν x S₀)⁻¹ := by
            rw [mul_assoc, ENNReal.mul_inv_cancel (ne_of_gt hmass₀.1) (ne_of_lt hmass₀.2),
              mul_one]
        _ = ((ρ'.map ψ) B * (ν (u • x) St)) * (ν x S₀)⁻¹ := by rw [hENN]
        _ = θ * (ρ'.map ψ) B := by
            rw [hθ, ENNReal.div_eq_inv_mul]
            ring
    have hpusheq : ρ.map ψ = θ • (ρ'.map ψ) := by
      haveI : IsFiniteMeasure (ρ.map ψ) := ⟨by
        rw [Measure.map_apply hψmeas MeasurableSet.univ, Set.preimage_univ, hρ,
          Measure.restrict_apply' hS₀meas, Set.univ_inter, hASt]
        exact hmass₁.2⟩
      refine ext_of_piBasis (fun B hB => ?_) ?_
      · rw [Measure.smul_apply, smul_eq_mul]
        exact hprop B hB
      · rw [Measure.smul_apply, smul_eq_mul]
        have h1 : (ρ.map ψ) Set.univ = ν (u • x) St := by
          rw [Measure.map_apply hψmeas MeasurableSet.univ, Set.preimage_univ, hρ,
            Measure.restrict_apply' hS₀meas, Set.univ_inter, hASt]
        have h2 : (ρ'.map ψ) Set.univ = ν x S₀ := by
          rw [Measure.map_apply hψmeas MeasurableSet.univ, Set.preimage_univ, hρ',
            Measure.restrict_apply' hS₀meas, Set.univ_inter]
        rw [h1, h2, hθ]
        exact (ENNReal.div_mul_cancel (ne_of_gt hmass₀.1) (ne_of_lt hmass₀.2)).symm
    -- the push-forward identity along the orbit map
    have hstabil : ∀ w ∈ U, w • x = x → w = 1 := fun w hw hfix => hxfree w hw hfix
    have hmapψ (τ : Measure SL3) :
        (τ.map (fun g : SL3 => u * g)).map (fun g : SL3 => g • x) = τ.map ψ := by
      rw [hψ, Measure.map_map (hφmeas x) hLmeas]
      congr 1
      funext g
      simp only [Function.comp_apply, mul_smul]
    have hcarA : A (U : Set SL3)ᶜ = 0 := by
      rw [hA, Measure.map_apply hΨmeas hU.1.measurableSet.compl]
      have hpre : (fun g : SL3 => u⁻¹ * g * u) ⁻¹' (U : Set SL3)ᶜ = (U : Set SL3)ᶜ := by
        ext g
        rw [Set.mem_preimage, Set.mem_compl_iff, Set.mem_compl_iff]
        constructor
        · intro hg hgU
          exact hg (U.mul_mem (U.mul_mem (U.inv_mem hu) hgU) hu)
        · intro hg hmem
          have h2 : u * (u⁻¹ * g * u) * u⁻¹ ∈ U := U.mul_mem (U.mul_mem hu hmem) (U.inv_mem hu)
          exact hg (by rwa [show u * (u⁻¹ * g * u) * u⁻¹ = g from by group] at h2)
      rw [hpre]
      exact hL.carried (u • x) huxX
    have hcar1 : (ρ.map (fun g : SL3 => u * g)) (U : Set SL3)ᶜ = 0 := by
      rw [hρ, Measure.map_apply hLmeas hU.1.measurableSet.compl,
        Measure.restrict_apply' hS₀meas]
      refine measure_mono_null ?_ hcarA
      intro g hg
      exact fun hgU => hg.1 (U.mul_mem hu hgU)
    have hcar2 : (θ • (ρ'.map (fun g : SL3 => u * g))) (U : Set SL3)ᶜ = 0 := by
      rw [Measure.smul_apply, hρ',
        Measure.map_apply hLmeas hU.1.measurableSet.compl,
        Measure.restrict_apply' hS₀meas]
      refine mul_eq_zero_of_right _ (measure_mono_null ?_ (hL.carried x hxX))
      intro g hg
      exact fun hgU => hg.1 (U.mul_mem hu hgU)
    have hμ₁μ₂ : ρ.map (fun g : SL3 => u * g) = θ • (ρ'.map (fun g : SL3 => u * g)) := by
      have haux : (ρ.map (fun g : SL3 => u * g)).map (fun g : SL3 => g • x)
          = (θ • (ρ'.map (fun g : SL3 => u * g))).map (fun g : SL3 => g • x) := by
        rw [hmapψ ρ, Measure.map_smul, hmapψ ρ'] <;> try fun_prop
        exact hpusheq
      exact Work.EKLRelCross.map_smul_injective_of_free U hU.1 x hstabil hcar1 hcar2 haux
    -- cancel the left translation
    refine ⟨θ, hθ0, hθT, ?_⟩
    have hcomp : (fun g : SL3 => u⁻¹ * g) ∘ (fun g : SL3 => u * g) = id := by
      funext g
      show u⁻¹ * (u * g) = g
      group
    have hcancel : ρ = θ • ρ' := by
      calc ρ = ρ.map id := (Measure.map_id).symm
        _ = ρ.map ((fun g : SL3 => u⁻¹ * g) ∘ (fun g : SL3 => u * g)) := by rw [hcomp]
        _ = (ρ.map (fun g : SL3 => u * g)).map (fun g : SL3 => u⁻¹ * g) :=
              (Measure.map_map hLinvmeas hLmeas).symm
        _ = (θ • (ρ'.map (fun g : SL3 => u * g))).map (fun g : SL3 => u⁻¹ * g) := by
              rw [hμ₁μ₂]
        _ = θ • ((ρ'.map (fun g : SL3 => u * g)).map (fun g : SL3 => u⁻¹ * g)) :=
              Measure.map_smul _ hLinvmeas.aemeasurable
        _ = θ • (ρ'.map ((fun g : SL3 => u⁻¹ * g) ∘ (fun g : SL3 => u * g))) := by
              rw [Measure.map_map hLinvmeas hLmeas]
        _ = θ • (ρ'.map id) := by rw [hcomp]
        _ = θ • ρ' := by rw [Measure.map_id]
    simpa only [hρ, hρ', hA, hS₀] using hcancel
  exact (ae_restrict_iff' hZmeas).mpr hmain

end Work.EKLComp
