import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Basic.exists_graphPoint_close
import Submission.Work.BoseSym.Perm.graphPoint_permTest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The symmetrisation average preserves the energy space

`symAvgAmb N p` is the average `(N!)⁻¹ • ∑_σ permAmb N σ p` of the permutation
orbit of `p` in the ambient space `Amb N = L²(Conf N) × ∏_j L²(Conf N)`.  We
show that it lies in the energy space `Hsub N L` whenever `p` does.

Two ingredients.  First, the permutation action is continuous on the ambient
space: `permLp N σ` is an isometry (`Lp.isometry_compMeasurePreserving`), so
its composition with the product projections is continuous, and `permAmb N σ`
is the product of those compositions.  Second, `Hsub N L` is the closure of
the range of the graph point map (`Hsub_eq_closure`), and the permutation
action permutes that range with itself (`graphPoint_permTest`); hence it maps
the closure into itself.  Finally a finite sum of members of the submodule
`Hsub N L`, and a scalar multiple of it, are again members.
-/

namespace Work.BoseSym.Perm

open MeasureTheory Filter

/-- The particle permutation acts continuously on `L²`. -/
private lemma continuous_permLp {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Continuous (permLp N σ) :=
  (Lp.isometry_compMeasurePreserving (p := 2) (measurePreserving_tauPerm N σ)).continuous

/-- The particle permutation acts continuously on the ambient space. -/
private lemma continuous_permAmb {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Continuous (permAmb N σ) := by
  have hσ : Continuous (permLp N σ) := continuous_permLp σ
  have h1 : Continuous fun p : Amb N => permLp N σ p.1 := hσ.comp continuous_fst
  have h2 : Continuous fun p : Amb N =>
      fun j : GIdx N => permLp N σ (p.2 (σ.symm j.1, j.2)) :=
    continuous_pi fun j => hσ.comp ((continuous_apply (σ.symm j.1, j.2)).comp continuous_snd)
  change Continuous fun p : Amb N =>
    (permLp N σ p.1, fun j : GIdx N => permLp N σ (p.2 (σ.symm j.1, j.2)))
  exact h1.prodMk h2

/-- The permutation action preserves the energy space: it is continuous and
permutes the generating set `range (graphPoint N L)` with itself. -/
private theorem permAmb_mem_Hsub_aux {N : ℕ} {L : ℝ} (σ : Equiv.Perm (Fin N)) {p : Amb N}
    (hp : p ∈ Hsub N L) : permAmb N σ p ∈ Hsub N L := by
  have hpc : p ∈ closure (Set.range (graphPoint N L)) := by
    rw [← Work.BoseSym.Basic.Hsub_eq_closure N L]
    exact hp
  have hclosed : IsClosed (Hsub N L : Set (Amb N)) :=
    Submodule.isClosed_topologicalClosure (Submodule.span ℝ (Set.range (graphPoint N L)))
  have hsub : permAmb N σ '' Set.range (graphPoint N L) ⊆ (Hsub N L : Set (Amb N)) := by
    rintro _ ⟨F, hF, rfl⟩
    obtain ⟨G, rfl⟩ := hF
    rw [graphPoint_permTest σ G]
    exact Submodule.le_topologicalClosure (Submodule.span ℝ (Set.range (graphPoint N L)))
      (Submodule.subset_span ⟨permTest N L σ G, rfl⟩)
  have hcl : closure (permAmb N σ '' Set.range (graphPoint N L)) ⊆ (Hsub N L : Set (Amb N)) :=
    hclosed.closure_subset_iff.mpr hsub
  have him : permAmb N σ p ∈ permAmb N σ '' closure (Set.range (graphPoint N L)) :=
    Set.mem_image_of_mem _ hpc
  exact hcl (image_closure_subset_closure_image (continuous_permAmb σ) him)

theorem symAvgAmb_mem_Hsub {N : ℕ} {L : ℝ} {p : Amb N} (hp : p ∈ Hsub N L) :
    symAvgAmb N p ∈ Hsub N L := by
  have hsum : (∑ σ : Equiv.Perm (Fin N), permAmb N σ p) ∈ Hsub N L :=
    Submodule.sum_mem _ fun σ _ => permAmb_mem_Hsub_aux σ hp
  simp only [symAvgAmb]
  exact Submodule.smul_mem _ _ hsum

end Work.BoseSym.Perm
