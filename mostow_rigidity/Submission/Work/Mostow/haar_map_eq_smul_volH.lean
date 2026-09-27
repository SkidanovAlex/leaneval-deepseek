import Mathlib
import Submission.Work.Mostow.HaarSetup
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.HaarBoost
import Submission.Work.Mostow.VolDefs
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.Ksub_compact
import Submission.Work.Mostow.prod_map_triangular
import Submission.Work.Mostow.exists_probability_haar_Ksub
import Submission.Work.Mostow.volH_measure_facts
import Submission.Work.Mostow.theta_measure_facts

/-!
# The Haar measure of `PO n 1` pushes forward to hyperbolic volume

`Measure.map (fun g : PO n 1 => g • 0) volume` is, up to a positive finite scalar, the hyperbolic
volume `volH n`:  the orbit map `π g = g • 0` identifies `PO n 1` with the principal `Ksub`-bundle
over `ℍⁿ`, and the pushforward of Haar measure along it is an invariant Radon measure on `ℍⁿ`,
hence a multiple of `volH n`.

The proof: for a *continuous section* `s` of `π` (the hyperbolic boost `boost u`) and the
probability Haar measure `τ` on the compact stabiliser `Ksub n hA`, the parametrisation
`Θ (u,k) = s u * k` is a bijection `ℍⁿ × Ksub ≅ PO n 1`.  Hence
`ρ := (volH n × τ) ∘ Θ ⁻¹` is a left-invariant Radon measure on `PO n 1` (left translations act by
the skew product `(u,k) ↦ (g • u, psi g u * k)`, which preserves the product measure), i.e. a Haar
measure; by uniqueness of Haar measure `ρ = c • volume` with `0 < c < ⊤`, and pushing `ρ` forward
along `π` (which is `Prod.fst` transported by `Θ`) gives `volH n = c • π_* volume`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

noncomputable section

variable {n : ℕ}

/-- For `c : ℝ≥0`, the two scalar actions on measures agree. -/
theorem smul_coe_eq_smul {α : Type*} [MeasurableSpace α] (c : NNReal) (μ : Measure α) :
    c • μ = (c : ENNReal) • μ := by
  ext s _
  rw [Measure.smul_apply, Measure.smul_apply]
  rfl

/-- A continuous section of the orbit map `g ↦ g • 0`, given by the hyperbolic boost. -/
theorem exists_continuous_section (n : ℕ) (hA : POActionProp n) :
    ∃ s : E n → PO n 1, Continuous s ∧ ∀ u : E n, s u • (0 : E n) = u :=
  ⟨fun u => ((boost u : O1 n) : PO n 1), continuous_boost n, fun u => boost_smul_zero hA u⟩

/-- The pushed-forward measure `(volH n × τ) ∘ Θ ⁻¹` is a left Haar measure on `PO n 1`. -/
theorem isMulLeftInvariant_theta_aux (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (s : E n → PO n 1) (hs : ∀ u : E n, s u • (0 : E n) = u) (hsc : Continuous s)
    (hvol : SigmaFinite (volH n))
    (τ : Measure ↥(Ksub n hA)) [Measure.IsMulLeftInvariant τ] [SigmaFinite τ] :
    Measure.IsMulLeftInvariant (Measure.map (Theta n hA s) ((volH n).prod τ)) := by
  haveI := hvol
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hMP, -⟩ := hI
  refine ⟨fun g => ?_⟩
  have hΘm : Measurable (Theta n hA s) := (continuous_Theta n hA s hsc).measurable
  have hgm : Measurable fun h : PO n 1 => g * h := (continuous_const.mul continuous_id).measurable
  have hact : Measurable fun u : E n => g • u :=
    (hA.2.2.2.2.2.2.1.comp (continuous_const.prodMk continuous_id)).measurable
  have hΦm : Measurable fun p : E n × ↥(Ksub n hA) => (g • p.1, psi n hA s hs g p.1 * p.2) :=
    (continuous_Phi n hA s hs hsc g).measurable
  rw [Measure.map_map hgm hΘm]
  have hcomp : ((fun h : PO n 1 => g * h) ∘ Theta n hA s) =
      Theta n hA s ∘ fun p : E n × ↥(Ksub n hA) =>
        (g • p.1, psi n hA s hs g p.1 * p.2) := by
    funext p
    obtain ⟨u, k⟩ := p
    exact Theta_mul n hA s hs g u k
  rw [hcomp, ← Measure.map_map hΘm hΦm]
  rw [prod_map_triangular (X := E n) (K := ↥(Ksub n hA)) (volH n) τ
      (fun u : E n => g • u) hact (hMP g).map_eq (fun u => psi n hA s hs g u)
      (continuous_psi n hA s hs hsc g).measurable]

/-- Pushing `(volH n).prod τ` forward along `Theta` and then along the orbit map gives
`τ univ • volH n`. -/
theorem map_orbit_map_Theta (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1)
    (hs : ∀ u : E n, s u • (0 : E n) = u) (hsc : Continuous s)
    (τ : Measure ↥(Ksub n hA)) [SigmaFinite τ] :
    Measure.map (fun g : PO n 1 => g • (0 : E n))
        (Measure.map (Theta n hA s) ((volH n).prod τ)) = τ Set.univ • volH n := by
  have hπ : Measurable fun g : PO n 1 => g • (0 : E n) :=
    (hA.2.2.2.2.2.2.1.comp (continuous_id.prodMk continuous_const)).measurable
  rw [Measure.map_map hπ (continuous_Theta n hA s hsc).measurable]
  have hcomp : (fun p : E n × ↥(Ksub n hA) => Theta n hA s p • (0 : E n)) = Prod.fst := by
    funext p
    obtain ⟨u, k⟩ := p
    exact Theta_fst n hA s hs u k
  change Measure.map (fun p : E n × ↥(Ksub n hA) => Theta n hA s p • (0 : E n))
      ((volH n).prod τ) = τ Set.univ • volH n
  rw [hcomp, Measure.map_fst_prod]

theorem haar_map_eq_smul_volH (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) :
    IsCompact (Work.Mostow.Ksub n hA : Set (LeanEval.Geometry.MostowRigidity.PO n 1)) ∧
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        MeasureTheory.Measure.map (fun g : LeanEval.Geometry.MostowRigidity.PO n 1 =>
            g • (0 : Submission.Mostow.E n))
            (MeasureTheory.MeasureSpace.volume :
              MeasureTheory.Measure (LeanEval.Geometry.MostowRigidity.PO n 1)) =
          c • Submission.Mostow.volH n := by
  refine ⟨Ksub_compact n hA, ?_⟩
  -- a continuous section of the orbit map and a probability Haar measure on `Ksub`
  obtain ⟨s, hsc, hs⟩ := exists_continuous_section n hA
  obtain ⟨τ, hτprob, hτhaar⟩ := exists_probability_haar_Ksub n hA (Ksub_compact n hA)
  haveI : IsProbabilityMeasure τ := hτprob
  haveI : Measure.IsHaarMeasure τ := hτhaar
  -- measure-theoretic properties of `volH`
  obtain ⟨hvolK, hvolS, hvolP⟩ := volH_measure_facts n
  haveI : IsFiniteMeasureOnCompacts (volH n) := hvolK
  haveI : SigmaFinite (volH n) := hvolS
  haveI : Measure.IsOpenPosMeasure (volH n) := hvolP
  -- `ρ := (volH n × τ) ∘ Θ ⁻¹` is a Haar measure on `PO n 1`
  haveI hρinv : Measure.IsMulLeftInvariant (Measure.map (Theta n hA s) ((volH n).prod τ)) :=
    isMulLeftInvariant_theta_aux n hA hI s hs hsc hvolS τ
  obtain ⟨hρfin, hρopen⟩ := theta_measure_facts n hA s hs hsc hvolS hvolK τ
  haveI : IsFiniteMeasureOnCompacts (Measure.map (Theta n hA s) ((volH n).prod τ)) := hρfin
  haveI : Measure.IsOpenPosMeasure (Measure.map (Theta n hA s) ((volH n).prod τ)) := hρopen
  haveI hρhaar : Measure.IsHaarMeasure (Measure.map (Theta n hA s) ((volH n).prod τ)) :=
    Measure.IsHaarMeasure.mk
  haveI hvolhaar : Measure.IsHaarMeasure (volume : Measure (PO n 1)) :=
    (show Measure.IsHaarMeasure (Measure.haar : Measure (PO n 1)) from inferInstance)
  -- uniqueness of Haar measure: `ρ` is a scalar multiple of `volume`
  have huniq : Measure.map (Theta n hA s) ((volH n).prod τ) =
      (Measure.haarScalarFactor (Measure.map (Theta n hA s) ((volH n).prod τ))
        (volume : Measure (PO n 1))) • (volume : Measure (PO n 1)) :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have hcpos : 0 < Measure.haarScalarFactor (Measure.map (Theta n hA s) ((volH n).prod τ))
      (volume : Measure (PO n 1)) :=
    Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  set c : ENNReal := (Measure.haarScalarFactor (Measure.map (Theta n hA s) ((volH n).prod τ))
      (volume : Measure (PO n 1)) : ENNReal) with hc_def
  have hc0 : c ≠ 0 := by
    rw [hc_def]
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt hcpos)
  have hcT : c ≠ ⊤ := by
    rw [hc_def]
    exact ENNReal.coe_ne_top
  have hρc : Measure.map (Theta n hA s) ((volH n).prod τ) = c • (volume : Measure (PO n 1)) := by
    rw [huniq, hc_def]
    exact smul_coe_eq_smul (Measure.haarScalarFactor (Measure.map (Theta n hA s) ((volH n).prod τ))
      (volume : Measure (PO n 1))) (volume : Measure (PO n 1))
  -- push both sides forward along the orbit map
  have hπ : AEMeasurable (fun g : PO n 1 => g • (0 : E n)) (volume : Measure (PO n 1)) :=
    (hA.2.2.2.2.2.2.1.comp (continuous_id.prodMk continuous_const)).measurable.aemeasurable
  have hpush1 : Measure.map (fun g : PO n 1 => g • (0 : E n))
        (Measure.map (Theta n hA s) ((volH n).prod τ)) =
      c • Measure.map (fun g : PO n 1 => g • (0 : E n)) (volume : Measure (PO n 1)) := by
    conv_lhs => rw [hρc]
    exact Measure.map_smul c hπ
  have hpush2 : Measure.map (fun g : PO n 1 => g • (0 : E n))
        (Measure.map (Theta n hA s) ((volH n).prod τ)) = volH n := by
    rw [map_orbit_map_Theta n hA s hs hsc τ, measure_univ, one_smul]
  have hmain : volH n = c • Measure.map (fun g : PO n 1 => g • (0 : E n))
      (volume : Measure (PO n 1)) := by
    rw [← hpush2]
    exact hpush1
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.mpr hcT, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  calc Measure.map (fun g : PO n 1 => g • (0 : E n)) (volume : Measure (PO n 1))
      = (c⁻¹ * c) • Measure.map (fun g : PO n 1 => g • (0 : E n))
          (volume : Measure (PO n 1)) := by
        rw [ENNReal.inv_mul_cancel hc0 hcT, one_smul]
    _ = c⁻¹ • (c • Measure.map (fun g : PO n 1 => g • (0 : E n))
          (volume : Measure (PO n 1))) := by
        rw [smul_smul]
    _ = c⁻¹ • volH n := by
        rw [← hmain]

end

end Work.Mostow
