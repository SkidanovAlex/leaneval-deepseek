import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.aeGradTraceAe
import Submission.Work.FTS.EllipticEst.AngAWeak.GradTraceAux
import Submission.Work.FTS.EllipticEst.H2W.AeProof.gradTraceAeUnw
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeColl/aeGradTraceRateUnw` — the a.e. trace and endpoint rate of `z ∂_z u`, *unweighted*

The target

```
theorem aeGradTraceRateUnw : ∃ C > 0, ∀ α u G, AeData α u G →
    (∀ᵐ z ∂(volume.restrict (Ioi 0)), IntegrableOn ((z ∂_z∂_θu)² σ) Iθ) →
    IntegrableOn (z ↦ ∫_θ (z ∂_z∂_θu(z,θ))² σ(θ)) Iz →
    ∀ᵐ z ∂(volume.restrict (Ioi 0)),
      (z ∂_z u(z,·) → 0 at 0⁺) ∧ (z ∂_z u(z,·) → 0 at (π/2)⁻) ∧
      (∀ θ ∈ (0,π/2), (z∂_zu(z,θ))² ≤ C θ^{1+η} ∫_{0<θ'<θ} (z∂_z∂_θu(z,θ'))²σ(θ')) ∧
      (∀ θ ∈ (0,π/2), (z∂_zu(z,θ))² ≤ C (π/2-θ)^{1+η} ∫_{θ<θ'<π/2} (z∂_z∂_θu(z,θ'))²σ(θ'))
```

is the single a.e. statement that `AeColl.i1PaperWeakMixed` consumes: the *two* mixed honesties
(a.e. slicewise, and the *unweighted* outer `z`-integral — no radial weight `w²`) give, for
almost every `z > 0`, the vanishing of the two endpoint traces of the slice of `U = z ∂_z u`
**and** the two sharp endpoint rates with one constant `C` uniform in `α`, `u`, `G`, `z`, `θ`.

## Proof

Two independent halves, each already in the tree:

* the two traces: `Work.FTS.EllipticEst.H2W.AeProof.gradTraceAeUnw` — the unweighted replay of
  `AngAWeak.aeGradTraceAe` (its `boundU`-domination needs only the *local* `z`-integrability of
  the slice energy, which here is the hypothesis itself);
* the two rates: the universal boundary-rate lemma
  `Work.EllipticEst.Core.sliceBoundaryLimit` (`K = 2` outright) applied to the slice
  `θ ↦ z ∂_z u(z,θ)`, whose endpoint constants are identified with `0` by the trace statement,
  whose weighted derivative square is `V²σ` by Clairaut (`AeI1Fts.slice_deriv_eq`), and whose
  energy is finite at a.e. `z` by the a.e.-slicewise honesty.  This is the argument of
  `H2W/slot20A_pieces/aeGradRate`, with the two `ℋ⁰`-honesties replaced by the (weaker)
  a.e. ones.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeColl

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "σ" => Work.FTS.EllipticEst.AngSecond.sig

/-- `AngAWeak`'s angular weight `sEta` is `σ = sin(2θ)^{-η}`. -/
theorem sEta_eq_sig_ae (θ : ℝ) : Work.FTS.EllipticEst.sEta θ = σ θ := rfl

/-- `Core`'s angular weight `thEta` is `σ = sin(2θ)^{-η}`. -/
theorem thEta_eq_sig_ae (θ : ℝ) : Work.FTS.EllipticEst.thEta θ = σ θ := rfl

theorem aeGradTraceRateUnw : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
      (∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        (z * Work.Spaces.pz u z θ) ^ 2 ≤ C * θ ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo 0 θ, (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
              * Work.FTS.EllipticEst.AngSecond.sig t)) ∧
      (∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        (z * Work.Spaces.pz u z θ) ^ 2 ≤ C * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo θ (Real.pi / 2),
              (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
                * Work.FTS.EllipticEst.AngSecond.sig t)) := by
  -- the universal constant of the boundary-rate lemma, taken once and for all
  obtain ⟨K, hKpos, hKL⟩ := Work.EllipticEst.Core.sliceBoundaryLimit
  refine ⟨K, hKpos, ?_⟩
  intro α u G hAe hae hint
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (Work.FTS.EllipticEst.H2W.Ae.AeData.smooth hAe)
  -- the two endpoint traces, from the *unweighted* hypothesis (already in the tree)
  have htr := Work.FTS.EllipticEst.H2W.AeProof.gradTraceAeUnw α u G hAe hae hint
  filter_upwards [htr, MeasureTheory.ae_restrict_mem measurableSet_Ioi, hae]
    with z hztr hzmem hzE
  have hzpos : 0 < z := hzmem
  -- the slice `θ ↦ z ∂_z u(z,θ)` is `C¹` on the open interval, with derivative `V u z ·`
  have hcont1 : ContDiffOn ℝ 1 (fun θ => z * Work.Spaces.pz u z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.AeI1Fts.contDiffOn_slice_U_one hS hzpos
  have hderiv : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      deriv (fun θ' => z * Work.Spaces.pz u z θ') t
        = z * Work.Spaces.pz (Work.Spaces.pth u) z t :=
    fun t ht => Work.FTS.EllipticEst.AeI1Fts.slice_deriv_eq hS hzpos ht
  -- its weighted derivative square is `(V u)²σ`, integrable at this `z` by hypothesis
  have hsig : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => z * Work.Spaces.pz u z θ') θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hzE.mono_set Set.Ioo_subset_Icc_self)
      (fun θ hθ => ?_) measurableSet_Ioo
    rw [hderiv θ hθ]
    simp only [Work.FTS.EllipticEst.AngSecond.sig, Work.FTS.EllipticEst.thEta]
  obtain ⟨⟨c, hc, hb⟩, ⟨c', hc', hb'⟩⟩ :=
    hKL (fun θ => z * Work.Spaces.pz u z θ) hcont1 hsig
  refine ⟨hztr.1, hztr.2, ?_, ?_⟩
  · intro θ hθ
    have hc0 : c = 0 := tendsto_nhds_unique hc hztr.1
    have hmain := hb θ hθ
    rw [hc0, sub_zero] at hmain
    have hset : (∫ θ' in Set.Ioo 0 θ,
          (deriv (fun θ' => z * Work.Spaces.pz u z θ') θ') ^ 2
            * Work.FTS.EllipticEst.thEta θ')
        = ∫ θ' in Set.Ioo 0 θ,
            (z * Work.Spaces.pz (Work.Spaces.pth u) z θ') ^ 2 * σ θ' := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ' hθ' => ?_)
      rw [hderiv θ' ⟨hθ'.1, lt_trans hθ'.2 hθ.2⟩]
      simp only [Work.FTS.EllipticEst.thEta, Work.FTS.EllipticEst.AngSecond.sig]
    rw [hset] at hmain
    exact hmain
  · intro θ hθ
    have hc0 : c' = 0 := tendsto_nhds_unique hc' hztr.2
    have hmain := hb' θ hθ
    rw [hc0, sub_zero] at hmain
    have hset : (∫ θ' in Set.Ioo θ (Real.pi / 2),
          (deriv (fun θ' => z * Work.Spaces.pz u z θ') θ') ^ 2
            * Work.FTS.EllipticEst.thEta θ')
        = ∫ θ' in Set.Ioo θ (Real.pi / 2),
            (z * Work.Spaces.pz (Work.Spaces.pth u) z θ') ^ 2 * σ θ' := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ' hθ' => ?_)
      rw [hderiv θ' ⟨lt_trans hθ.1 hθ'.1, hθ'.2⟩]
      simp only [Work.FTS.EllipticEst.thEta, Work.FTS.EllipticEst.AngSecond.sig]
    rw [hset] at hmain
    exact hmain

end Work.FTS.EllipticEst.AeColl
