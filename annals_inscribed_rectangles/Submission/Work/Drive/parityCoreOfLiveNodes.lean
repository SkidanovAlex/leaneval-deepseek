import Mathlib
import Submission.Work.Drive.hn2OffHalfLive
import Submission.Work.Drive.hn2_half_derivation
import Submission.Work.Drive.parityCoreOfSideGermPlaneChart
import Submission.Work.Drive.parityCore_translate
import Submission.Work.Drive.exists_wrapData_translate
import Submission.Work.Drive.exists_planeChart_capSectionDisjoint
import Submission.Work.Drive.exists_chartPert
import Submission.Work.Drive.chartLevelBound
import Submission.Work.Drive.chartIsSmooth
import Submission.Work.Drive.hdense_sideGerm
import Submission.Work.Drive.SheetScheme.isSmoothEmbedding_radialGraph

/-!
# `ParityCore γ` from the **live** `hn2` node and `hdense`

`Work.Drive.parityCore_of_germInputs` (`Drive/parityCore_of_germInputs.lean`) wires the wall
`Work.Drive.ParityCore γ` to the *historical* `hn2` node `Work.Drive.hn2_sideGerm_off_half` (whose
producer route runs through `refTripleAt_producer`).  The `hn2` lane has since re-proved the same node
under a fresh name along a shorter chain:

> `Work.Drive.hn2_off_half` (proved) ← `Work.Drive.hn2_refCount` ← `Work.Drive.hn2_refCountExists`
> (proved),

so the wall should be wired to **that** chain (`Work.Drive.hn2_off_half_live` in
`Drive/hn2OffHalfLive.lean` is that same derivation with the *proved* counting datum
`Work.Drive.hn2_refCountExists` substituted, so that the historical hole file `hn2_refCount.lean` is
not needed either).  This file does the rewiring, in one module:

* `Work.Drive.hn2_full_of_off_half_live` — the full antisymmetry (`hn2_sideGerm_of_off_half`'s
  conclusion) from the *live* off-`1/2` statement `Work.Drive.hn2_off_half`, the openness of `Zc γ`
  and the `1/2`-case `Work.Drive.antisym_of_antisym_off_half` (the inscribed-square theorem);
* **`Work.Drive.parityCore_of_liveNodes`** — `UmlaufProp → IsSmoothEmbedding γ → ParityCore γ`,
  verbatim the body of `parityCore_of_germInputs` with the `hn2` input taken from the live chain.

The remaining holes of the closure of this module are therefore exactly the *live* obligations
(`Work.Drive.hn2_refCount` and `Work.Drive.hdense_sideGerm`), and none of the historical `hn2` node
files (`hn2_sideGerm_off_half`, `hn2_sideGerm_reference`) is needed.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The full antisymmetry of the germ side value from the live off-`1/2` statement.** -/
theorem hn2_full_of_off_half_live {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγsm : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (c : ℝ)
    (hΞ : ChartPert Q m Ξ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q)) :
    ∀ u v : UnitAddCircle, v - u ∈ Zc γ →
      sideGerm Ξ Q c (v - u) + sideGerm Ξ Q c (u - v) = 1 := by
  have hγinj : Function.Injective γ := hγsm.isEmbedding.injective
  have hopen : IsOpen (Zc γ) := isOpen_Zc γ hγsm
  refine antisym_of_antisym_off_half Ξ Q c hγne hγinj hQ hΞ hc hcbot hopen ?_
  intro u hu hne
  have h := hn2_off_half_live (γ := γ) (hγne := hγne) hγsm hQ Ξ c hΞ hc hcbot hdisjZc 0 u
    (by simpa using hu) (by simpa using hne)
  simpa using h

/-- **`ParityCore γ` from the live `hn2` chain and `hdense`.**  The body is that of
`Work.Drive.parityCore_of_germInputs`, with the antisymmetry supplied by
`Work.Drive.hn2_full_of_off_half_live` (whose off-`1/2` input is the live node
`Work.Drive.hn2_off_half`). -/
theorem parityCore_of_liveNodes (hU : Submission.Drive.UmlaufProp) (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) : ParityCore γ := by
  obtain ⟨c₀, hne, hW⟩ := exists_wrapData_translate γ hγ
  have hsm : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ (fun x : Circle => γ x + c₀) :=
    SheetScheme.isSmoothEmbedding_add_const γ hγ c₀
  have hinj : Function.Injective (fun x : Circle => γ x + c₀) := hsm.isEmbedding.injective
  obtain ⟨Q, hQ, hdisjZc⟩ :=
    exists_planeChart_chartDisk_disjoint_capSection hU (fun x : Circle => γ x + c₀) hsm hne hW
  obtain ⟨m, Ξ, hΞ⟩ := exists_chartPert Q
  obtain ⟨c, hc, hcbot⟩ := exists_level_lt_chartDisk
    (continuous_of_isPlaneChart (fun x : Circle => γ x + c₀) hne Q hQ)
  have hn2 := hn2_full_of_off_half_live (γ := fun x : Circle => γ x + c₀) (hγne := hne) hsm hQ
    Ξ c hΞ hc hcbot hdisjZc
  have hdense := hdense_sideGerm (γ := fun x : Circle => γ x + c₀) (hγne := hne) hinj hQ Ξ c hΞ hc
    hcbot hdisjZc
  have hcore : ParityCore (fun x : Circle => γ x + c₀) :=
    parityCore_of_sideGerm_planeChart hsm Ξ Q c hne hinj hQ hΞ hc hcbot hn2 hdense
  exact (parityCore_translate γ c₀).mp hcore

end

end Work.Drive
