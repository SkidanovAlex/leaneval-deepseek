import Mathlib
import Submission.Work.WilC2.CutDefs

/-!
  Area C2 (WilC2): finiteness of the cut-endpoint sets `maxSet X`, `supSet X` of a set `X`
  which is a *finite* union of order-convex (ord-connected) subsets.

  The whole content is elementary order theory.  If `X = ⋃₀ s` with `s` a finset all of whose
  members are ord-connected, then:

  * every point of `maxSet X` is the **maximum of a member of `s`**: if `x ∈ maxSet X`, then
    `x ∈ I` for some `I ∈ s`, and `I` is ord-connected inside `X`, hence lies in the component
    of `x`, whose maximum is `x`; so `x = max I`.  A member has at most one maximum, so
    `maxSet X` is contained in a finite union of singletons.
  * every point of `supSet X` is the **least upper bound of a member of `s`**: the members of
    `s` lying strictly below `x` form a nonempty finite family, and if none of them had `x` as
    its least upper bound then the maximum of a strict upper bound below `x` for each of them
    would be a strict upper bound below `x` for all of `X ∩ (-∞,x)`, contradicting that `x` is
    the supremum of that set.  Again each member has a unique least upper bound.

  Both sets are therefore contained in a finite union of at most `|s|` singletons.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilC2

variable {M : Type*} [LinearOrder M]

/-- Every point of `X` which is the maximum of its component is the maximum of one of the
convex pieces: `maxSet X ⊆ ⋃ I ∈ s, {maxima of I}`. -/
theorem maxSet_subset_maxima {X : Set M} {s : Finset (Set M)}
    (hord : ∀ I ∈ s, I.OrdConnected) (hcov : X = ⋃₀ (s : Set (Set M))) :
    maxSet X ⊆ ⋃ I ∈ (s : Set (Set M)), {x | x ∈ I ∧ ∀ y ∈ I, y ≤ x} := by
  intro x hx
  obtain ⟨hxX, hxmax⟩ := hx
  rw [hcov] at hxX
  obtain ⟨I, hIs, hxI⟩ := Set.mem_sUnion.mp hxX
  have hIs' : I ∈ s := hIs
  have hIX : I ⊆ X := by rw [hcov]; exact Set.subset_sUnion_of_mem hIs
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨I, hIs, hxI, fun y hyI => not_lt.mp fun hlt => by
    obtain ⟨z, hxz, hzy, hzX⟩ := hxmax y (hIX hyI) hlt
    exact hzX (hIX (hord I hIs' |>.out hxI hyI ⟨le_of_lt hxz, le_of_lt hzy⟩))⟩

/-- Every point of `supSet X` is the least upper bound of one of the convex pieces:
`supSet X ⊆ ⋃ I ∈ s, {least upper bounds of I}`. -/
theorem supSet_subset_lubs {X : Set M} {s : Finset (Set M)}
    (hord : ∀ I ∈ s, I.OrdConnected) (hcov : X = ⋃₀ (s : Set (Set M))) :
    supSet X ⊆ ⋃ I ∈ (s : Set (Set M)), {x | IsLUB I x} := by
  intro x hx
  obtain ⟨hxnotX, hy0, hcond⟩ := hx
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  by_contra hcon
  push Not at hcon
  -- the members of `s` lying strictly below `x`
  let J : Finset (Set M) := s.filter (fun I => ∀ y ∈ I, y < x)
  have hJmem : ∀ I, I ∈ J ↔ I ∈ s ∧ ∀ y ∈ I, y < x := fun I => Finset.mem_filter
  have hJne : J.Nonempty := by
    obtain ⟨y0, hy0X, hy0x⟩ := hy0
    rw [hcov] at hy0X
    obtain ⟨I, hIs, hy0I⟩ := Set.mem_sUnion.mp hy0X
    have hIX : I ⊆ X := by rw [hcov]; exact Set.subset_sUnion_of_mem hIs
    refine ⟨I, (hJmem I).mpr ⟨hIs, fun w hwI => ?_⟩⟩
    exact not_le.mp fun hxw => by
      rcases eq_or_lt_of_le hxw with h | h
      · exact hxnotX (hIX (h ▸ hwI))
      · exact hxnotX (hIX (hord I hIs |>.out hy0I hwI ⟨le_of_lt hy0x, le_of_lt h⟩))
  -- a strict upper bound below `x` for each member of `J`
  have hbdd : ∀ I ∈ J, ∃ u, u < x ∧ ∀ y ∈ I, y ≤ u := by
    intro I hI
    obtain ⟨hIs, hIlt⟩ := (hJmem I).mp hI
    have hIupper : ∀ y ∈ I, y ≤ x := fun y hy => le_of_lt (hIlt y hy)
    by_contra h
    refine hcon I hIs ⟨hIupper, fun u hu => ?_⟩
    exact not_lt.mp fun hux => h ⟨u, hux, hu⟩
  let g : Set M → M :=
    fun I => if h : ∃ u, u < x ∧ ∀ y ∈ I, y ≤ u then Classical.choose h else x
  have hg : ∀ I ∈ J, g I < x ∧ ∀ y ∈ I, y ≤ g I := by
    intro I hI
    have : g I = Classical.choose (hbdd I hI) := by
      simp only [g, dite_eq_left (hbdd I hI)]
    rw [this]
    exact Classical.choose_spec (hbdd I hI)
  -- the maximum of these strict upper bounds is itself one
  let u := (J.image g).max' (hJne.image g)
  have hu_lt : u < x := by
    obtain ⟨I, hIJ, hIg⟩ := Finset.mem_image.mp (Finset.max'_mem (J.image g) (hJne.image g))
    dsimp only [u]
    rw [← hIg]
    exact (hg I hIJ).1
  have hu_ub : ∀ I ∈ J, ∀ y ∈ I, y ≤ u := by
    intro I hIJ y hyI
    calc y ≤ g I := (hg I hIJ).2 y hyI
      _ ≤ u := Finset.le_max' _ _ (Finset.mem_image.mpr ⟨I, hIJ, rfl⟩)
  -- it bounds all of `X ∩ (-∞,x)` strictly below `x`, contradicting the sup property
  obtain ⟨y, hyX, huy, hyx⟩ := hcond u hu_lt
  rw [hcov] at hyX
  obtain ⟨I0, hI0s, hyI0⟩ := Set.mem_sUnion.mp hyX
  have hI0X : I0 ⊆ X := by rw [hcov]; exact Set.subset_sUnion_of_mem hI0s
  have hI0J : I0 ∈ J := by
    refine (hJmem I0).mpr ⟨hI0s, fun w hwI0 => ?_⟩
    exact not_le.mp fun hxw => by
      rcases eq_or_lt_of_le hxw with h | h
      · exact hxnotX (hI0X (h ▸ hwI0))
      · exact hxnotX (hI0X (hord I0 hI0s |>.out hyI0 hwI0 ⟨le_of_lt hyx, le_of_lt h⟩))
  exact not_le.mpr huy (hu_ub I0 hI0J y hyI0)

/-- The maxima of a finite family of subsets form a finite set. -/
theorem finite_iUnion_maxima (s : Finset (Set M)) :
    (⋃ I ∈ (s : Set (Set M)), {x | x ∈ I ∧ ∀ y ∈ I, y ≤ x}).Finite :=
  Set.Finite.biUnion s.finite_toSet (fun _ _ =>
    Set.Subsingleton.finite (fun _ ha _ hb => le_antisymm (hb.2 _ ha.1) (ha.2 _ hb.1)))

/-- The least upper bounds of a finite family of subsets form a finite set. -/
theorem finite_iUnion_lubs (s : Finset (Set M)) :
    (⋃ I ∈ (s : Set (Set M)), {x | IsLUB I x}).Finite :=
  Set.Finite.biUnion s.finite_toSet (fun _ _ =>
    Set.Subsingleton.finite (fun _ ha _ hb => IsLUB.unique ha hb))

/-- A set which is a finite union of order-convex pieces has only finitely many
"component endpoints": its points that are the maximum of their component and the outside
points that are the supremum of a component. -/
theorem finite_maxSet_supSet {M : Type} [LinearOrder M] {X : Set M} {s : Finset (Set M)}
    (hord : ∀ I ∈ s, I.OrdConnected) (hcov : X = ⋃₀ (s : Set (Set M))) :
    (Work.WilC2.maxSet X).Finite ∧ (Work.WilC2.supSet X).Finite :=
  ⟨Set.Finite.subset (finite_iUnion_maxima s) (maxSet_subset_maxima hord hcov),
   Set.Finite.subset (finite_iUnion_lubs s) (supSet_subset_lubs hord hcov)⟩

end Work.WilC2
