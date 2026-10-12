import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1Aux.integrable_qLHSBIntegrand_real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1Aux

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

-- Generalisation of `Work.UBBInputs8.A.integrable_qLHSBIntegrand_box` to a SINGLE scale `L`
-- (`hL : 0 < L` instead of `∀ L ≥ 1`), a FREE chemical potential `μ` (instead of `dens N L`) and
-- a REAL scale `d` (instead of `{d : ℕ}` with `(d : ℝ)`), with the box-restricted product measure
-- `volume.prod (volume.restrict (abox N L))` and only `Continuous Φ`.
--
-- Route: (a) re-do the full-measure core `Work.UBBInputs2.integrable_qLHSBIntegrand`
-- verbatim with `hR' := hR`, `hRχ := hRχ` in place of `hdR L hL`, `hdRχ L hL`, real `d`, free `μ`
-- (its body uses the regime hypotheses only at `L`, and `μ` only as a scalar) -- this is the
-- delegated lemma `Work.BoseFixB1Aux.integrable_qLHSBIntegrand_real`;
-- (b) transplant to the box measure as in `Work.UBBInputs8.A.integrable_qLHSBIntegrand_box`:
-- Urysohn bump `f = 1` on the compact `abox N L` with compact support, apply (a) to `Φ * f`,
-- push along `volume.prod (volume.restrict (abox N L)) ≤ volume.prod volume` and use the a.e.
-- agreement of `Φ*f` and `Φ` on `univ ×ˢ abox N L`.
theorem integrable_qLHSBIntegrand_box_singleL {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {R0 μ d : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv1 : MeasureTheory.MemLp v 1) (M : ℕ) (hM : 1 ≤ M) (hd : 0 < d)
    {L : ℝ} (hL : 0 < L) (hR : R0 ≤ L * d / 16) (hRχ : R0 ≤ L * Submission.BoseGases.chiR0)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
      Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Φ p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N L))) := by
  have hLpos : 0 < L := hL
  -- the analysis box is compact, so it carries a compactly supported continuous bump
  have hK : IsCompact (Submission.BoseGases.abox N L) :=
    Submission.BoseGases.abox_compact N hLpos
  obtain ⟨f, hf1, -, hfcs, -⟩ := exists_continuous_one_zero_of_isCompact
    (s := Submission.BoseGases.abox N L) (t := (∅ : Set (Submission.BoseGases.X N)))
    hK isClosed_empty (Set.disjoint_empty _)
  -- transplant: `Φ' := Φ * f` is continuous with compact support and agrees with `Φ` on the box
  have hΦc' : Continuous (fun x : Submission.BoseGases.X N => Φ x * f x) := hΦc.mul f.continuous
  have hΦs' : HasCompactSupport (fun x : Submission.BoseGases.X N => Φ x * f x) :=
    HasCompactSupport.mul_left hfcs
  have hmain := Work.BoseFixB1Aux.integrable_qLHSBIntegrand_real (v := v) (h := h) (μ := μ)
    (d := d) (R0 := R0) hv_supp hR0 hv1 M hM hd hL hR hRχ
    (Φ := fun x => Φ x * f x) hΦc' hΦs'
  -- restrict the product measure
  have hle : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N L))
      ≤ (MeasureTheory.volume :
          MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N)) := by
    rw [show (MeasureTheory.volume :
          MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N))
        = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
            (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)) from rfl]
    exact MeasureTheory.Measure.prod_mono le_rfl MeasureTheory.Measure.restrict_le_self
  have hres : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        Work.SmallBoxSliding.qLHSBIntegrand h M L d μ (fun x => Φ x * f x) p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N L))) := hmain.mono_measure hle
  refine hres.congr ?_
  -- the box-restricted product measure lives on `univ ×ˢ abox N L`
  have hmem : ∀ᵐ p ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N L))),
      p.2 ∈ Submission.BoseGases.abox N L := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
      (p := fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        p.2 ∈ Submission.BoseGases.abox N L)
      ((Submission.BoseGases.abox_measurable N L).preimage measurable_snd)]
    filter_upwards with q
    exact MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable N L)
  filter_upwards [hmem] with p hp
  simp only [Work.SmallBoxSliding.qLHSBIntegrand]
  rw [hf1 hp]
  simp only [Pi.one_apply, mul_one]

end Work.BoseFixB1Aux
