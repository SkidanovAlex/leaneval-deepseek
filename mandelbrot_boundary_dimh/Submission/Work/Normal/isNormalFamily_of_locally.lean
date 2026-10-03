import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.exists_subseq_with_local_limits
import Submission.Work.Normal.local_limits_of_cover

/-!
# Normality is a local property

If a family of functions `Fam : Set (ℂ → ℂ)` is normal on a neighbourhood of every point of an
open preconnected set `U`, then it is normal on all of `U`.

The proof has three steps.

* `exists_normal_cover` : since `ℂ` is second countable, hence hereditarily Lindelöf, the
  neighbourhoods supplied by the hypothesis can be thinned to a countable cover
  `U = ⋃ n, G n` by *nonempty* open normal sets.
* `exists_subseq_with_local_limits` : a nested-subsequence diagonal shows that a single
  subsequence `v ∘ φ` of an arbitrary sequence `v` in `Fam` converges locally uniformly (or
  diverges locally uniformly to `∞`) on every `G n` separately.  (This is where the countability
  of the cover is used.)
* `local_limits_of_cover` : preconnectedness of `U` forces the type of the convergence to be the
  same on every member of the cover, and the local limits then glue to a limit on `U`.
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology

/-- **A countable cover by normal open sets.**  If every point of an open set `U` has a normal
neighbourhood, then `U` is the union of a sequence of nonempty open normal sets (all contained in
`U`). -/
lemma exists_normal_cover {Fam : Set (ℂ → ℂ)} {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hloc : ∀ z ∈ U, ∃ V : Set ℂ, z ∈ V ∧ IsOpen V ∧ IsNormalFamily Fam V) :
    ∃ G : ℕ → Set ℂ, (∀ n, IsOpen (G n)) ∧ (∀ n, (G n).Nonempty) ∧
      (∀ n, IsNormalFamily Fam (G n)) ∧ U = ⋃ n, G n := by
  classical
  -- A normal neighbourhood of each point `x` of `U`, intersected with `U` so that it stays
  -- inside `U`.
  let W : U → Set ℂ := fun x => (Classical.choose (hloc x.1 x.2)) ∩ U
  have hWopen : ∀ x : U, IsOpen (W x) := fun x =>
    (Classical.choose_spec (hloc x.1 x.2)).2.1.inter hU
  have hWne : ∀ x : U, (W x).Nonempty := fun x =>
    ⟨x.1, (Classical.choose_spec (hloc x.1 x.2)).1, x.2⟩
  have hWnorm : ∀ x : U, IsNormalFamily Fam (W x) := fun x =>
    (Classical.choose_spec (hloc x.1 x.2)).2.2.mono Set.inter_subset_left
  have hWU : ∀ x : U, W x ⊆ U := fun _ => Set.inter_subset_right
  have hcoverU : U ⊆ ⋃ x : U, W x := fun z hz =>
    Set.mem_iUnion.2 ⟨⟨z, hz⟩, (Classical.choose_spec (hloc z hz)).1, hz⟩
  -- Lindelöf: extract a countable subcover.
  obtain ⟨f, hf⟩ := @IsLindelof.indexed_countable_subcover ℂ _ U U
    ⟨hUne.choose, hUne.choose_spec⟩
    (HereditarilyLindelofSpace.isLindelof U) W hWopen hcoverU
  refine ⟨fun n => W (f n), fun n => hWopen (f n), fun n => hWne (f n),
    fun n => hWnorm (f n), ?_⟩
  exact Set.Subset.antisymm hf (Set.iUnion_subset fun n => hWU (f n))

theorem isNormalFamily_of_locally {Fam : Set (ℂ → ℂ)} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hloc : ∀ z ∈ U, ∃ V : Set ℂ, z ∈ V ∧ IsOpen V ∧ IsNormalFamily Fam V) :
    IsNormalFamily Fam U := by
  intro u hu
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · -- The empty set is trivially normal: `TendstoLocallyUniformlyAtTop` is vacuous there.
    exact ⟨id, strictMono_id, Or.inr (fun K hK _ _ =>
      ⟨0, fun n _ z hz => absurd (hK hz) (Set.notMem_empty z)⟩)⟩
  · obtain ⟨G, hGopen, hGne, hGnorm, hcover⟩ := exists_normal_cover hU hUne hloc
    obtain ⟨φ, hφ, hlim⟩ := exists_subseq_with_local_limits hu hGnorm
    exact ⟨φ, hφ, local_limits_of_cover hUc hGopen hGne hcover hlim⟩

end Work.Normal
