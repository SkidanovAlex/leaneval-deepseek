import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

/-- **`L¹`-ness over the box of the localised pair kernel times a bounded slot factor.**
`Submission.BoseGases.wLoc ℓ (g0 v h) 0` is
`χ_Λ(x_i)·wScaled ℓ (g0 v h)(x_i − x_j)·χ_Λ(x_j)`, so the substance is
`IntegrableOn (fun x => |wScaled ℓ (g0 v h) (x i − x j)|) (abox n ℓ)` -- available as
`Submission.BoseGases.integrableOn_abs_sub_abox` from
`Submission.Work.SmallBoxBogWS1Bound.wScaled_g0_integrable` -- multiplied by the bounded
measurable factor `χ_Λ(x_i)χ_Λ(x_j)ψ x` (`Submission.BoseGases.abs_chiScale_le_chiSup`),
i.e. `Integrable.bdd_mul`.  The one subtlety is that only `Integrable` (hence only a.e.-measurable)
`wScaled` is available, so the pullback `x ↦ wScaled ℓ (g0 v h) (x i − x j)` has to be handled as
in the proved `Submission/Work/BoseFixB3/Conv/abox_peel_pair.lean` (`integrableOn_sub_coord_abox` +
`abox_ae_pair_of_ae`, via `Submission.BoseGases.abox_null_preimage_pair`).  Do NOT import any module
that is not fully proved (in particular not
`Submission/Work/BoseFixB3/Conv/integrableOn_sub_coord.lean`, which is an unproved statement of the
general fact).

(Implemented instead through the *proved* `Submission.BoseGases.integrableOn_bounded_mul_wPair_sub_abox`
of `Submission/WordInteg.lean`, which packages exactly the bounded-factor times windowed-pair-kernel
box integrability, including the a.e.-measurability of the `L¹`-only pullback `x ↦ wScaled … (xᵢ − xⱼ)`;
the localisation `chiU ℓ 0 = chiScale ℓ` rewrites `wLoc` into `wPair` pointwise.)  NOTE for the file: the checker has no `open MeasureTheory`, so write
`MeasureTheory.IntegrableOn` and `MeasureTheory.volume` (or add `open MeasureTheory` above the
statement). -/
theorem integrableOn_pairKernel_lowSlot {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hRℓ : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0)
    {ψ : Submission.BoseGases.X n → ℝ} (hψm : Measurable ψ) {D : ℝ} (hD : 0 ≤ D)
    (hψb : ∀ x, |ψ x| ≤ D) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.wLoc (Work.BoseBoxFock.ellH v μ) (Submission.BoseGases.g0 v h) 0
        (x i) (x j) * ψ x)
      (Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) MeasureTheory.volume := by
  -- `g₀ = v(1−ω)` is `L¹` and vanishes outside `ball 0 R` (`ScatKernelChosen`).
  have hg0 : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ →
      Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  -- `wLoc ℓ (g₀) 0 (xᵢ) (xⱼ) = wPair ℓ (g₀) (xᵢ) (xⱼ)` pointwise, so the claim is the
  -- bounded-factor box integrability of the windowed pair kernel (`Submission.WordInteg`),
  -- which already absorbs the a.e.-measurability of the `L¹`-only kernel `wScaled`.
  have key : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => ψ x *
        Submission.BoseGases.wPair (Work.BoseBoxFock.ellH v μ)
          (Submission.BoseGases.g0 v h) (x i) (x j))
      (Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) MeasureTheory.volume :=
    Submission.BoseGases.integrableOn_bounded_mul_wPair_sub_abox
      (N := n) (R := R) (ℓ := Work.BoseBoxFock.ellH v μ) hℓ hg0 hsupp hRℓ i j hij
      hψm.aestronglyMeasurable hD (Filter.Eventually.of_forall hψb)
  refine key.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [Submission.BoseGases.wLoc, Submission.BoseGases.wPair,
    Submission.BoseGases.chiU, Submission.BoseGases.chiScale, sub_zero]
  ring

end Work.BoseBoxFock.PCFU
