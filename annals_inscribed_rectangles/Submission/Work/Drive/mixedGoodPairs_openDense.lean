import Mathlib
import Submission.Work.Drive.goodPairTwoCharts_isOpen
import Submission.Work.Drive.goodPairTwoCharts_exists_near
import Submission.Work.Drive.refTripleGeneric
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.norm_blkSpan

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology
attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-! ## The block bookkeeping of `ℝ¹²` -/

/-- **A move concentrated in one block.**  Adding `blkSpan i σ` to `t` changes the block `i` by `σ`
and leaves the two other blocks unchanged. -/
private lemma blk_add_blkSpan (t : EuclideanSpace ℝ (Fin 12)) (i j : Fin 3)
    (σ : EuclideanSpace ℝ (Fin 4)) :
    blk j (t + blkSpan i σ) = blk j t + (if j = i then σ else 0) := by
  rw [map_add]
  by_cases h : j = i
  · subst h; rw [blk_blkSpan, if_pos rfl]
  · rw [blk_blkSpan_of_ne h, if_neg h, add_zero]

/-! ## The two pair-level genericity statements, in the shape of the mixed pairs

The pair-level results of the lane are stated for a loop chart of the form `chartPert p ∘ Q₁` (with
`Q₁` an arbitrary smooth chart) and a chain chart of the form `rotCapping w ∘ chartPert q ∘ Q₂`.  The
mixed pairs of the reference triple are `(chartPert p ∘ rotCapping u ∘ Q, chartPert q ∘ Q₂)`, i.e. the
rotation sits on the *first* slot and there is none on the second: they are the above with
`Q₁ := rotCapping u ∘ Q` and `w := 0`, using that a rotated smooth chart is smooth
(`Work.Drive.contMDiff_rotCapping_const`) and that `rotCapping 0 = id`
(`Work.Drive.rotCapping_zero`). -/

/-- **Openness of the good configurations of a mixed pair** in the two perturbation parameters: the
loop slot is the chart perturbation of the *rotated* base chart `rotCapping u ∘ Q`, the chain slot the
chart perturbation of `Q₂`. -/
private lemma mixedPair_isOpen {Q Q₂ : ℂ → CappingSpace} (hQ : IsSmoothChart Q)
    (hQ₂ : IsSmoothChart Q₂) (u : UnitAddCircle) (c₂ : ℝ) :
    IsOpen {p : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
      GoodPair (fun z : ℂ => chartPert p.1 (rotCapping u (Q z)))
        (fun z : ℂ => chartPert p.2 (Q₂ z)) c₂} := by
  have hQ₁ : IsSmoothChart (fun z : ℂ => rotCapping u (Q z)) :=
    (contMDiff_rotCapping_const u).comp hQ
  have h := goodPairTwoCharts_isOpen (Q₁ := fun z : ℂ => rotCapping u (Q z)) (Q₂ := Q₂)
    hQ₁ hQ₂ c₂ 0
  simpa only [rotCapping_zero, id_eq] using h

/-- **Density of the good configurations of a mixed pair** at every base point, in the *shift* form:
the loop slot of the mixed pair is `chartPert (s₁ + p) ∘ rotCapping u ∘ Q` with `p` arbitrarily
small, the chain slot is `chartPert s₂ ∘ Q₂` at the fixed parameter `s₂`. -/
private lemma mixedPair_exists_near {Q Q₂ : ℂ → CappingSpace} (hQ : IsSmoothChart Q)
    (hQ₂ : IsSmoothChart Q₂) (u : UnitAddCircle) (c₂ : ℝ)
    (s₁ s₂ : EuclideanSpace ℝ (Fin 4)) :
    ∀ ε : ℝ, 0 < ε → ∃ p : EuclideanSpace ℝ (Fin 4), ‖p‖ < ε ∧
      GoodPair (fun z : ℂ => chartPert (s₁ + p) (rotCapping u (Q z)))
        (fun z : ℂ => chartPert s₂ (Q₂ z)) c₂ := by
  have hQ₁ : IsSmoothChart (fun z : ℂ => rotCapping u (Q z)) :=
    (contMDiff_rotCapping_const u).comp hQ
  intro ε hε
  obtain ⟨p, hp, hgood⟩ := goodPairTwoCharts_exists_near (Q₁ := fun z : ℂ => rotCapping u (Q z))
    (Q₂ := Q₂) hQ₁ hQ₂ c₂ 0 s₁ s₂ ε hε
  exact ⟨p, hp, by simpa only [rotCapping_zero, id_eq] using hgood⟩

/-- **The two mixed pairs of the `hn2` reference triple are good on an open dense set of parameters.**
The reference-triple producer needs, in addition to the sweeps' `Meet3Hyp`, the goodness of the two
pairs `(block 0, reference block)` and `(block 1, reference block)`, i.e. of
`(chartPert (blk 0 t) ∘ rotCapping u ∘ Q, chartPert (blk 2 t) ∘ Q₂)` and its `v`-analogue.  These are
open and dense-at-every-point in `t : 𝔼¹²`: openness is the preimage of the open pair-set
(`Work.Drive.goodPairTwoCharts_isOpen`) under the continuous linear map `t ↦ (blk 0 t, blk 2 t)`;
density follows from the *shift* form (`Work.Drive.goodPairTwoCharts_exists_near`) using the two
projections `blk 0`, `blk 2` (`Work.Drive.blkSpan`, `Work.Drive.blk_blkSpan_of_ne`,
`Work.Drive.norm_blkSpan`), exactly as `Work.Drive.refTripleGeneric` does for the configuration pairs
(shift `blk 0` and `blk 1` independently by `blkSpan`, keeping `blk 2` fixed).  These two sets are to be
added to the open dense set `A` of the Sard step `Work.Drive.exists_meet3Hyp_opens` of the producer, so
that the mixed factors `(F1)` are available at `t` in their box form. -/
theorem mixedGoodPairs_openDense {Q Q₂ : ℂ → Work.Drive.CappingSpace}
    (hQ : Work.Drive.IsSmoothChart Q) (hQ₂ : Work.Drive.IsSmoothChart Q₂)
    (u v : UnitAddCircle) (c₂ : ℝ) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
        Work.Drive.GoodPair (fun z : ℂ => Work.Drive.chartPert (Work.Drive.blk 0 t)
            (Work.Drive.rotCapping u (Q z)))
          (fun z : ℂ => Work.Drive.chartPert (Work.Drive.blk 2 t) (Q₂ z)) c₂ ∧
        Work.Drive.GoodPair (fun z : ℂ => Work.Drive.chartPert (Work.Drive.blk 1 t)
            (Work.Drive.rotCapping v (Q z)))
          (fun z : ℂ => Work.Drive.chartPert (Work.Drive.blk 2 t) (Q₂ z)) c₂} ∧
      (∀ s : EuclideanSpace ℝ (Fin 12), ∀ δ : ℝ, 0 < δ →
        ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - s‖ < δ ∧
          Work.Drive.GoodPair (fun z : ℂ => Work.Drive.chartPert (Work.Drive.blk 0 t)
              (Work.Drive.rotCapping u (Q z)))
            (fun z : ℂ => Work.Drive.chartPert (Work.Drive.blk 2 t) (Q₂ z)) c₂ ∧
          Work.Drive.GoodPair (fun z : ℂ => Work.Drive.chartPert (Work.Drive.blk 1 t)
              (Work.Drive.rotCapping v (Q z)))
            (fun z : ℂ => Work.Drive.chartPert (Work.Drive.blk 2 t) (Q₂ z)) c₂) := by
  refine ⟨?_, ?_⟩
  · -- ### openness: the preimages of the two open pair-sets under `t ↦ (blk k t, blk 2 t)`
    have hA : IsOpen {t : EuclideanSpace ℝ (Fin 12) |
        GoodPair (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z)))
          (fun z : ℂ => chartPert (blk 2 t) (Q₂ z)) c₂} := by
      have hp := (mixedPair_isOpen hQ hQ₂ u c₂).preimage
        ((blk 0).continuous.prodMk (blk 2).continuous)
      convert hp using 1
      ext t
      rfl
    have hB : IsOpen {t : EuclideanSpace ℝ (Fin 12) |
        GoodPair (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z)))
          (fun z : ℂ => chartPert (blk 2 t) (Q₂ z)) c₂} := by
      have hp := (mixedPair_isOpen hQ hQ₂ v c₂).preimage
        ((blk 1).continuous.prodMk (blk 2).continuous)
      convert hp using 1
      ext t
      rfl
    exact hA.inter hB
  · -- ### density at every point: shift block `0`, then block `1`, keeping block `2` fixed
    intro s δ hδ
    have h4 : 0 < δ / 4 := by linarith
    -- the first mixed pair, at the block parameters of `s`
    obtain ⟨p, hp, hgp⟩ := mixedPair_exists_near hQ hQ₂ u c₂ (blk 0 s) (blk 2 s) (δ / 4) h4
    let t₁ : EuclideanSpace ℝ (Fin 12) := s + blkSpan 0 p
    have ht₁_0 : blk 0 t₁ = blk 0 s + p := by
      show blk 0 (s + blkSpan 0 p) = blk 0 s + p
      rw [blk_add_blkSpan, if_pos rfl]
    have ht₁_2 : blk 2 t₁ = blk 2 s := by
      show blk 2 (s + blkSpan 0 p) = blk 2 s
      rw [blk_add_blkSpan, if_neg (by decide : ¬ ((2 : Fin 3) = 0)), add_zero]
    have hP₀ : GoodPair (fun z : ℂ => chartPert (blk 0 t₁) (rotCapping u (Q z)))
        (fun z : ℂ => chartPert (blk 2 t₁) (Q₂ z)) c₂ := by
      rw [ht₁_0, ht₁_2]
      exact hgp
    -- the second mixed pair, moved only in block `1`
    obtain ⟨p', hp', hgp'⟩ := mixedPair_exists_near hQ hQ₂ v c₂ (blk 1 t₁) (blk 2 t₁) (δ / 4) h4
    let t : EuclideanSpace ℝ (Fin 12) := t₁ + blkSpan 1 p'
    have ht_0 : blk 0 t = blk 0 t₁ := by
      show blk 0 (t₁ + blkSpan 1 p') = blk 0 t₁
      rw [blk_add_blkSpan, if_neg (by decide : ¬ ((0 : Fin 3) = 1)), add_zero]
    have ht_1 : blk 1 t = blk 1 t₁ + p' := by
      show blk 1 (t₁ + blkSpan 1 p') = blk 1 t₁ + p'
      rw [blk_add_blkSpan, if_pos rfl]
    have ht_2 : blk 2 t = blk 2 t₁ := by
      show blk 2 (t₁ + blkSpan 1 p') = blk 2 t₁
      rw [blk_add_blkSpan, if_neg (by decide : ¬ ((2 : Fin 3) = 1)), add_zero]
    refine ⟨t, ?_, ?_, ?_⟩
    · -- the move is concentrated in two blocks, so its norm is at most `‖p‖ + ‖p'‖ < δ`
      have hsub : t - s = blkSpan 0 p + blkSpan 1 p' := by
        show (s + blkSpan 0 p) + blkSpan 1 p' - s = blkSpan 0 p + blkSpan 1 p'
        abel
      rw [hsub]
      calc ‖blkSpan 0 p + blkSpan 1 p'‖ ≤ ‖blkSpan 0 p‖ + ‖blkSpan 1 p'‖ := norm_add_le _ _
        _ = ‖p‖ + ‖p'‖ := by rw [norm_blkSpan, norm_blkSpan]
        _ < δ / 4 + δ / 4 := by linarith
        _ < δ := by linarith
    · rw [ht_0, ht_2]
      exact hP₀
    · rw [ht_1, ht_2]
      exact hgp'

end

end Work.Drive
