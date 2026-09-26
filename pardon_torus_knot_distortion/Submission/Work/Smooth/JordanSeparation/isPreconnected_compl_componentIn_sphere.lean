import Mathlib
import Submission.Work.JordanSeparation.onePoint_locallyConnected

/-!
# The complement of a complementary domain of a continuum in the Riemann sphere

`Work.Smooth.JordanSeparation.isPreconnected_compl_componentIn_sphere`: if `K` is a non-empty
closed preconnected subset of the Riemann sphere `OnePoint ℂ` (a *continuum*) and `x ∉ K`, then
the complement of the connected component of `Kᶜ` containing `x` is preconnected.

The proof is the classical one.  Write `C = connectedComponentIn Kᶜ x`.  A point of `Cᶜ` either
lies in `K`, or in another component `D` of `Kᶜ`.  In the second case `D ∪ K` is preconnected:
`K` is preconnected, `closure D = D ∪ frontier D` is preconnected, and `frontier D` is a non-empty
subset of `K` (the frontier of a component of the open set `Kᶜ` cannot meet `Kᶜ`, by
`closure (connectedComponentIn Kᶜ v) ∩ Kᶜ = connectedComponentIn Kᶜ v`; it is non-empty because
`D` is a proper non-empty clopen set otherwise, contradicting connectedness of the sphere).  So
the whole of `Cᶜ = K ∪ ⋃_{D ≠ C} D` lies in a single component of `Cᶜ`, namely the one through
any point of `K`; hence `Cᶜ = connectedComponentIn Cᶜ y` is preconnected.
-/

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

/-- **A component of a set `F` meets `F` exactly in its own closure.** -/
theorem closure_inter_connectedComponentIn_eq {α : Type*} [TopologicalSpace α] {F : Set α}
    {v : α} (hv : v ∈ F) :
    closure (connectedComponentIn F v) ∩ F = connectedComponentIn F v := by
  apply Subset.antisymm
  · rintro z ⟨hzcl, hzF⟩
    by_contra hzV
    have hins : IsPreconnected (insert z (connectedComponentIn F v)) :=
      IsPreconnected.subset_closure isPreconnected_connectedComponentIn
        (subset_insert z _) (insert_subset hzcl subset_closure)
    have hsub : insert z (connectedComponentIn F v) ⊆ F :=
      insert_subset hzF (connectedComponentIn_subset F v)
    exact hzV (hins.subset_connectedComponentIn (Or.inr (mem_connectedComponentIn hv)) hsub
      (Or.inl rfl))
  · intro z hz
    exact ⟨subset_closure hz, connectedComponentIn_subset F v hz⟩

/-- **The frontier of a component of the complement of a closed set lies in that set.**

If `K` is closed and `v ∈ Kᶜ`, then every point of the frontier of `connectedComponentIn Kᶜ v`
lies in `K`: that frontier is contained in `closure (connectedComponentIn Kᶜ v)`, while a point of
`Kᶜ` lying in this closure already lies in the component
(`closure_inter_connectedComponentIn_eq`), whereas the frontier of the *open* component avoids
the component itself. -/
theorem frontier_connectedComponentIn_subset_of_isClosed {α : Type*} [TopologicalSpace α]
    [LocallyConnectedSpace α] {K : Set α} (hK : IsClosed K) {v : α} (hv : v ∈ Kᶜ) :
    frontier (connectedComponentIn Kᶜ v) ⊆ K := by
  intro z hz
  by_contra hzK
  have hDopen : IsOpen (connectedComponentIn Kᶜ v) := hK.isOpen_compl.connectedComponentIn
  rw [hDopen.frontier_eq] at hz
  have hzKc : z ∈ Kᶜ := hzK
  have hmem : z ∈ closure (connectedComponentIn Kᶜ v) ∩ Kᶜ := ⟨hz.1, hzKc⟩
  rw [closure_inter_connectedComponentIn_eq hv] at hmem
  exact hz.2 hmem

/-- **In a connected space, a proper non-empty open set has non-empty frontier.**

Otherwise `closure D = D`, so `D` would be clopen, and in a connected space a clopen set is
empty or the whole space. -/
theorem nonempty_frontier_of_isOpen_ne_univ {α : Type*} [TopologicalSpace α] [ConnectedSpace α]
    {D : Set α} (hDopen : IsOpen D) (hDne : D.Nonempty) (hDproper : D ≠ univ) :
    (frontier D).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hcl : closure D = D := by
    rw [closure_eq_self_union_frontier, h, Set.union_empty]
  have hDclosed : IsClosed D := hcl ▸ isClosed_closure
  have hsep : univ ⊆ D ∪ Dᶜ := fun z _ => by
    rcases em (z ∈ D) with hz | hz
    · exact Or.inl hz
    · exact Or.inr hz
  rcases isPreconnected_univ.subset_or_subset hDopen hDclosed.isOpen_compl disjoint_compl_right
    hsep with h1 | h1
  · exact hDproper (Set.eq_univ_of_univ_subset h1)
  · exact hDne.ne_empty (Set.eq_empty_iff_forall_notMem.mpr fun z hz => (h1 (Set.mem_univ z)) hz)

/-- **The complement of a complementary domain of a continuum in the Riemann sphere is
preconnected.** -/
theorem isPreconnected_compl_componentIn_sphere {K : Set (OnePoint ℂ)} (hK : IsClosed K)
    (hKne : K.Nonempty) (hKp : IsPreconnected K) {x : OnePoint ℂ} (hx : x ∉ K) :
    IsPreconnected ((connectedComponentIn Kᶜ x)ᶜ) := by
  classical
  set C : Set (OnePoint ℂ) := connectedComponentIn Kᶜ x with hCdef
  have hxKc : x ∈ Kᶜ := hx
  have hxC : x ∈ C := hCdef ▸ mem_connectedComponentIn hxKc
  have hCsub : C ⊆ Kᶜ := hCdef ▸ connectedComponentIn_subset Kᶜ x
  have hKC : K ⊆ Cᶜ := fun z hz hzC => hCsub hzC hz
  obtain ⟨y, hyK⟩ := hKne
  -- Every point of `Cᶜ` lies in the component of `Cᶜ` through the fixed point `y ∈ K`.
  have hkey : ∀ d ∈ Cᶜ, d ∈ connectedComponentIn Cᶜ y := by
    intro d hd
    by_cases hdK : d ∈ K
    · exact hKp.subset_connectedComponentIn (x := y) hyK hKC hdK
    · have hdKc : d ∈ Kᶜ := hdK
      set D : Set (OnePoint ℂ) := connectedComponentIn Kᶜ d with hDdef
      have hdD : d ∈ D := hDdef ▸ mem_connectedComponentIn hdKc
      have hDne : D.Nonempty := ⟨d, hdD⟩
      have hDsub : D ⊆ Kᶜ := hDdef ▸ connectedComponentIn_subset Kᶜ d
      have hDopen : IsOpen D := by
        rw [hDdef]; exact hK.isOpen_compl.connectedComponentIn
      have hDpre : IsPreconnected D := hDdef ▸ isPreconnected_connectedComponentIn
      have hDproper : D ≠ Set.univ := by
        intro h
        have hyD : y ∈ D := by rw [h]; exact Set.mem_univ y
        exact hDsub hyD hyK
      have hDcd : D ⊆ Cᶜ := by
        intro z hzD hzC
        have h1 : connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ z :=
          connectedComponentIn_eq hzC
        have h2 : connectedComponentIn Kᶜ d = connectedComponentIn Kᶜ z :=
          connectedComponentIn_eq hzD
        have hCD : C = D := by rw [hCdef, hDdef, h1.trans h2.symm]
        exact hd (hCD ▸ hdD)
      have hfr_sub : frontier D ⊆ K := frontier_connectedComponentIn_subset_of_isClosed hK hdKc
      have hfr_ne : (frontier D).Nonempty :=
        nonempty_frontier_of_isOpen_ne_univ hDopen hDne hDproper
      -- `K ∪ D` is preconnected: glue `K` to `closure D = D ∪ frontier D` along `frontier D ⊆ K`.
      have hpre : IsPreconnected (K ∪ D) := by
        obtain ⟨z, hz⟩ := hfr_ne
        have hzK : z ∈ K := hfr_sub hz
        have hzcl : z ∈ closure D := frontier_subset_closure hz
        have hpre' : IsPreconnected (K ∪ closure D) :=
          IsPreconnected.union' ⟨z, hzK, hzcl⟩ hKp hDpre.closure
        have heq : K ∪ closure D = K ∪ D := by
          rw [closure_eq_self_union_frontier, ← Set.union_assoc]
          exact Set.union_eq_left.mpr (fun z hz => Or.inl (hfr_sub hz))
        rwa [heq] at hpre'
      exact hpre.subset_connectedComponentIn (x := y) (Or.inl hyK) (Set.union_subset hKC hDcd)
        (Or.inr hdD)
  have hCeq : Cᶜ = connectedComponentIn Cᶜ y :=
    Subset.antisymm hkey (connectedComponentIn_subset Cᶜ y)
  rw [hCeq]
  exact isPreconnected_connectedComponentIn

end

end Work.Smooth.JordanSeparation
