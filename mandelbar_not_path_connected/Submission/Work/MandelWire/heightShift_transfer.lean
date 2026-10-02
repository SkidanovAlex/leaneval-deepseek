/-
# `Work.MandelWire.heightShift_transfer`

The *pinned* form of the height-shift theorem: not merely does every real number occur as the
critical Écalle height of some root-parabolic parameter (`Work.FQC.heightShift`), but the
deformation carries the given root-parabolic datum `d` onto the new one along an **explicit**
homeomorphism `θ = principal (muQC d fl P t)`, which

* conjugates `Tantibar c` to `Tantibar c₂`,
* is normalised as `θ z = z + O(1/‖z‖)` at infinity,
* fixes `0`,

and the transported parabolic point is the image `θ d.z₁` of the original one.

The proof is the assembly of `Work.FQC.heightShift` replayed with
`Work.MandelWire.transfer_parabolic_spec` (pinning the transported `z₁`) in place of
`Work.FQC.transfer_parabolic`, the conjugating homeomorphism being the principal Beltrami
solution itself.
-/
import Mathlib
import Submission.Work.MandelWire.Deps
import Submission.Work.MandelWire.transfer_parabolic_spec

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MandelWire

open LeanEval.ComplexAnalysis

theorem heightShift_transfer {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl)
    (hphase : Work.FQC.saw ((fl.φa (Work.FQC.phasePoint d fl)).re) = 1 / 2)
    (hsimple : ∀ t : ℝ, Work.FQC.SimpleTransfer d fl hpetal.Pg t)
    (hU : Work.FQC.FatouUnique) (h : ℝ) :
    ∃ c₂ : ℂ, ∃ θ : ℂ ≃ₜ ℂ,
      (∀ z : ℂ, θ (LeanEval.ComplexAnalysis.Tantibar c z) = LeanEval.ComplexAnalysis.Tantibar c₂ (θ z)) ∧
      (∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖) ∧ θ 0 = 0 ∧
      ∃ d₂ : Work.EL.RootParabolic c₂, d₂.z₁ = θ d.z₁ ∧ Work.FQC.critHeight d₂ = h := by
  set t : ℝ := 2 * (h - Work.FQC.critHeightAt d (Work.FQC.EcalleData.ofFlower d fl)) with ht
  obtain ⟨c₂, hconj⟩ := Work.FQC.conj_is_tricorn_pg d fl hpetal t
  have hμ : Work.MRMT.Found.Admissible (Work.FQC.muQC d fl hpetal.Pg t) :=
    Work.FQC.muQC_admissible_pg d fl hpetal t
  have h0 : (Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t)) 0 = 0 :=
    Work.FQC.zero_of_conj (Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t)).bijective hconj
  have hdecay : ∃ C R : ℝ, ∀ z : ℂ,
      R ≤ ‖z‖ → ‖(Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t)) z - z‖ ≤ C / ‖z‖ :=
    Work.MRMT.Found.principal_decay hμ
  have hs : iteratedDeriv 2 (Work.EL.F c₂)
      ((Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t)) d.z₁) ≠ 0 :=
    hsimple t c₂ (Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t)) rfl hconj
  obtain ⟨d₂, hd₂⟩ := Work.MandelWire.transfer_parabolic_spec d _ hconj hdecay h0 hs
  have hphase' : Work.FQC.saw (fl.φa
      ((Work.EL.F c)^[Work.FQC.nEnter (Work.FQC.EcalleData.ofFlower d fl)] c)).re = 1 / 2 := hphase
  obtain ⟨E₂, hE₂⟩ := Work.FQC.height_after_pg d fl hpetal t d₂ hconj h0 hphase'
  refine ⟨c₂, Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t), hconj, hdecay, h0, d₂, hd₂, ?_⟩
  have hA := hU.eq d₂ (Work.FQC.EcalleData.canonical d₂) E₂
  have hB : Work.FQC.critHeight d = Work.FQC.critHeightAt d (Work.FQC.EcalleData.ofFlower d fl) :=
    hU.eq d (Work.FQC.EcalleData.canonical d) (Work.FQC.EcalleData.ofFlower d fl)
  calc Work.FQC.critHeight d₂ = Work.FQC.critHeightAt d₂ E₂ := hA
    _ = Work.FQC.critHeightAt d (Work.FQC.EcalleData.ofFlower d fl) + t / 2 := hE₂
    _ = Work.FQC.critHeight d + t / 2 := by rw [← hB]
    _ = h := by rw [ht, hB]; ring

end Work.MandelWire
