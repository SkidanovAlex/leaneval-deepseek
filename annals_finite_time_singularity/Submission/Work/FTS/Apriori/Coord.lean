/-
# Slices of a locally uniformly convergent family (`ConvLocUnif` → the open quadrant)

`ConvLocUnif G g` is locally uniform convergence on the closed slab of the self-similar variables;
the lower-semicontinuity lemma `HkNorm_le_of_tendstoLocUnif` is stated on compact subsets of the
*open* quadrant.  This module records the (elementary) passage between the two.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori

open Work.FTS.Galerkin (Fam slice ConvLocUnif Slab)

set_option autoImplicit false

/-- **Slices of a locally uniformly convergent family converge locally uniformly on the open
quadrant**: `ConvLocUnif` restricted to the compact subset `K × {τ}` of the slab. -/
theorem convLocUnif_slice {G : ℕ → Fam} {g : Fam} (h : ConvLocUnif G g) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.Construction.Qd →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G n p.1 p.2 τ) (fun p => g p.1 p.2 τ)
        Filter.atTop K := by
  intro K hK hKsub
  set K' : Set (ℝ × ℝ × ℝ) := Set.image (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2, q.2))
    (K ×ˢ ({τ} : Set ℝ)) with hK'def
  have hcont : Continuous (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2, q.2)) := by
    have h1 : Continuous (fun q : (ℝ × ℝ) × ℝ => q.1.1) := continuous_fst.comp continuous_fst
    have h2 : Continuous (fun q : (ℝ × ℝ) × ℝ => q.1.2) := continuous_snd.comp continuous_fst
    have h3 : Continuous (fun q : (ℝ × ℝ) × ℝ => q.2) := continuous_snd
    exact h1.prodMk (h2.prodMk h3)
  have hK' : IsCompact K' := by
    rw [hK'def]
    exact (hK.prod isCompact_singleton).image hcont
  have hsub : K' ⊆ Slab := by
    rintro p ⟨⟨⟨z, θ⟩, s⟩, hq, rfl⟩
    obtain ⟨hqK, hqτ⟩ := hq
    rw [Set.mem_singleton_iff] at hqτ
    obtain ⟨hz0, hθ0, hθ1⟩ := hKsub hqK
    have hs : s = τ := hqτ
    show z ∈ Work.Spaces.Iz ∧ θ ∈ Work.Spaces.Iθ ∧ 0 ≤ s
    exact ⟨Set.mem_Ici.mpr (le_of_lt hz0),
      Set.mem_Icc.mpr ⟨le_of_lt hθ0, le_of_lt hθ1⟩, by rw [hs]; exact hτ⟩
  have h' := h K' hK' hsub
  rw [Metric.tendstoUniformlyOn_iff] at h' ⊢
  intro ε hε
  filter_upwards [h' ε hε] with n hn
  intro q hq
  refine hn (q.1, q.2, τ) ?_
  refine ⟨((q.1, q.2), τ), ?_, rfl⟩
  exact ⟨hq, rfl⟩

end Work.FTS.Apriori
