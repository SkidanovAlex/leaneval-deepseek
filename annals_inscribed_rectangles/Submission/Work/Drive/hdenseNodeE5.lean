import Mathlib
import Submission.Work.Drive.hdenseNodeVocab
import Submission.Work.Drive.hdenseNodeGerm
import Submission.Work.Drive.hdenseNodeE3
import Submission.Work.Drive.hdenseDesignData
import Submission.Work.Drive.sideGerm_indep
import Submission.Work.Drive.hdenseBlockT6

/-!
# The (E5) wiring of the `hdense` node: the node from the design's parameter, at every triple

The node `Work.Drive.hdense_sideGerm` is the identity `E ≡ 1` on the open set of collision-free triples
(equivalently: on a dense set of *good* triples, `Work.Drive.hdense_sideGerm_of_dense_identity`,
`hdenseDesignData.lean`).  This module performs the last step of the lead's `NOTES_LEAD_hdense.md`
(§4–§5, the "(E5)" of the design): given the one-parameter design data

> `hE4 : ∀ a c' ∈ Zc, ∀ ε' > 0, ∃ t, ‖t‖ < ε' ∧ DesignTripleAtN Q c ![c/2,c/3,c/4] ![0,a,a+c'] t ∧
>        BlockT6AtN Q c ![c/2,c/3,c/4] ![0,a,a+c'] t`

(the producer `Work.Drive.exists_designTripleAtN_blockT6AtN`, the only remaining obligation of the lane),
the node's conclusion for the *given* chart perturbation `Ξ` follows:

* `exists_germDataAtN` (proved) supplies the germ data `ε`;
* `hdense_identity_of_designTripleAtN` (proved) gives the identity for the **concrete** perturbation
  `fun s p => chartPert s p` at the parameter `t`;
* `sideGerm_indep` (proved) transfers the six germ values from `chartPert` to `Ξ` at the six angles
  `{a, a + c', -a, c', -(a + c'), -c'}` (all in `Zc γ`);
* `hdense_sideGerm_of_dense_identity` (proved) finishes with `subset_closure` on the good set
  `{q | q.1, q.2, q.1 + q.2 ∈ Zc γ}`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- The design's truncation levels `![c/2, c/3, c/4]` are positive and below `c`. -/
private lemma designCblk_pos {c : ℝ} (hc : 0 < c) :
    ∀ k : Fin 3, 0 < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k := by
  intro k
  fin_cases k <;> simp <;> linarith

/-- The design's truncation levels are below `c`. -/
private lemma designCblk_lt {c : ℝ} (hc : 0 < c) :
    ∀ k : Fin 3, (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k < c := by
  intro k
  fin_cases k <;> simp <;> linarith

/-- The three angles `![0, a, a + c']` have all their pairwise differences in `Zc γ`. -/
private lemma designAngles_hu {γ : Circle → ℝ × ℝ} {a c' : UnitAddCircle}
    (ha : a ∈ Zc γ) (hc' : c' ∈ Zc γ) (hac : a + c' ∈ Zc γ) :
    ∀ k j : Fin 3, k ≠ j →
      (![0, a, a + c'] : Fin 3 → UnitAddCircle) j
        - (![0, a, a + c'] : Fin 3 → UnitAddCircle) k ∈ Zc γ := by
  intro k j hkj
  fin_cases k <;> fin_cases j
  · exact absurd rfl hkj
  · simpa using ha
  · simpa using hac
  · simpa using neg_mem_Zc ha
  · exact absurd rfl hkj
  · simpa using hc'
  · simpa using neg_mem_Zc hac
  · simpa using neg_mem_Zc hc'
  · exact absurd rfl hkj

/-- **(E5) of the `hdense` design**: the node's conclusion from the one-parameter design data
`DesignTripleAtN`/`BlockT6AtN` at every triple. -/
theorem hdense_sideGerm_of_E4 {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q) {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace) (c : ℝ)
    (hΞ : Work.Drive.ChartPert Q m Ξ) (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (hE4 : ∀ (a c' : UnitAddCircle), a ∈ Work.Drive.Zc γ → c' ∈ Work.Drive.Zc γ →
      a + c' ∈ Work.Drive.Zc γ →
      ∀ ε' : ℝ, 0 < ε' →
        ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
          Work.Drive.DesignTripleAtN Q c (![c / 2, c / 3, c / 4] : Fin 3 → ℝ)
            (![0, a, a + c'] : Fin 3 → UnitAddCircle) t ∧
          Work.Drive.BlockT6AtN Q c (![c / 2, c / 3, c / 4] : Fin 3 → ℝ)
            (![0, a, a + c'] : Fin 3 → UnitAddCircle) t) :
    ∀ a c' : UnitAddCircle, a ∈ Work.Drive.Zc γ → c' ∈ Work.Drive.Zc γ →
      a + c' ∈ Work.Drive.Zc γ →
      (a, c') ∈ closure {q : UnitAddCircle × UnitAddCircle |
        q.1 ∈ Work.Drive.Zc γ ∧ q.2 ∈ Work.Drive.Zc γ ∧ q.1 + q.2 ∈ Work.Drive.Zc γ ∧
          Work.Drive.sideGerm Ξ Q c q.1 * Work.Drive.sideGerm Ξ Q c (q.1 + q.2)
            + Work.Drive.sideGerm Ξ Q c (-q.1) * Work.Drive.sideGerm Ξ Q c q.2
            + Work.Drive.sideGerm Ξ Q c (-(q.1 + q.2)) * Work.Drive.sideGerm Ξ Q c (-q.2) = 1} := by
  have hΞc : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  refine hdense_sideGerm_of_dense_identity hγinj hQ Ξ c hΞ hc hcbot
    {q : UnitAddCircle × UnitAddCircle |
      q.1 ∈ Work.Drive.Zc γ ∧ q.2 ∈ Work.Drive.Zc γ ∧ q.1 + q.2 ∈ Work.Drive.Zc γ} ?_ ?_
  · intro a c' ha hc' hac
    exact subset_closure ⟨⟨ha, hc', hac⟩, ⟨ha, hc', hac⟩⟩
  · rintro ⟨a, c'⟩ ⟨ha, hc', hac⟩ - - -
    simp only [Prod.fst, Prod.snd] at ha hc' hac ⊢
    -- the germ data at this triple
    obtain ⟨ε, hε, hGerm⟩ := exists_germDataAtN (γ := γ) (hγne := hγne) hγinj hQ c hc hcbot
      ![c / 2, c / 3, c / 4] (designCblk_pos hc) (designCblk_lt hc)
      ![0, a, a + c'] (designAngles_hu ha hc' hac)
    -- the level band of the concrete perturbation
    obtain ⟨εl, hεl, hlvl⟩ :=
      exists_eps_level_lt_pertChart hQ (fun s p => chartPert s p) hΞc c hcbot
    -- the design's parameter, and the identity for the concrete perturbation
    obtain ⟨t, ht, hdes, hblk⟩ := hE4 a c' ha hc' hac (min ε εl) (lt_min hε hεl)
    have hident := hdense_identity_of_designTripleAtN (γ := γ) (hγne := hγne) hγinj hQ hc hcbot
      ha hc' hac hε hGerm
      (fun ε' hε' _ => hE4 a c' ha hc' hac ε' hε')
    -- transfer the six germ values from `chartPert` to `Ξ`
    have h1 : sideGerm Ξ Q c a = sideGerm (fun s p => chartPert s p) Q c a :=
      sideGerm_indep hγinj hQ Ξ (fun s p => chartPert s p) c hΞ hΞc hc hcbot a ha
    have h2 : sideGerm Ξ Q c (a + c') = sideGerm (fun s p => chartPert s p) Q c (a + c') :=
      sideGerm_indep hγinj hQ Ξ (fun s p => chartPert s p) c hΞ hΞc hc hcbot (a + c') hac
    have h3 : sideGerm Ξ Q c (-a) = sideGerm (fun s p => chartPert s p) Q c (-a) :=
      sideGerm_indep hγinj hQ Ξ (fun s p => chartPert s p) c hΞ hΞc hc hcbot (-a) (neg_mem_Zc ha)
    have h4 : sideGerm Ξ Q c c' = sideGerm (fun s p => chartPert s p) Q c c' :=
      sideGerm_indep hγinj hQ Ξ (fun s p => chartPert s p) c hΞ hΞc hc hcbot c' hc'
    have h5 : sideGerm Ξ Q c (-(a + c')) = sideGerm (fun s p => chartPert s p) Q c (-(a + c')) :=
      sideGerm_indep hγinj hQ Ξ (fun s p => chartPert s p) c hΞ hΞc hc hcbot (-(a + c'))
        (neg_mem_Zc hac)
    have h6 : sideGerm Ξ Q c (-c') = sideGerm (fun s p => chartPert s p) Q c (-c') :=
      sideGerm_indep hγinj hQ Ξ (fun s p => chartPert s p) c hΞ hΞc hc hcbot (-c') (neg_mem_Zc hc')
    rw [h1, h2, h3, h4, h5, h6]
    exact hident

end

end Work.Drive
