import Mathlib.Topology.Connected.PathConnected

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter

namespace Commons.Topology.PathConnected

/-- **Generic engine.** Let `s : Set X` be connected. If every point of `s`
has an open path-connected neighbourhood which is contained in `s`, then `s`
is path-connected.

Proof sketch (classical): fix `x₀ ∈ s` and let `Q` be its path component
inside `s`.  Each point of `Q` carries an open path-connected neighbourhood
`U ⊆ s`, and `U ⊆ Q` (paths in `U` join its points to the point of `Q`), so
`Q` is open.  If `y ∈ s ∩ closure Q`, an open path-connected `U ∋ y` with
`U ⊆ s` cannot avoid `Q` (as `y ∈ closure Q`), so some `z ∈ U ∩ Q`; then
`z` joins to both `y` (inside `U ⊆ s`) and `x₀`, forcing `y ∈ Q`.  Hence
`closure Q ∩ s ⊆ Q`, and the preconnected set `s` cannot leave the open set
`Q` (`IsPreconnected.subset_of_closure_inter_subset`), so `Q = s`. -/
theorem isPathConnected_of_isConnected_of_open_pathConnected_nhds {X : Type*}
    [TopologicalSpace X] {s : Set X} (hs : IsConnected s)
    (hloc : ∀ x : X, x ∈ s → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧ U ⊆ s) :
    IsPathConnected s := by
  classical
  rcases hs.nonempty with ⟨x₀, hx₀s⟩
  refine ⟨x₀, hx₀s, ?_⟩
  let Q : Set X := {y | JoinedIn s x₀ y}
  have hQsub : Q ⊆ s := by
    intro y hy
    exact (JoinedIn.mem hy).2
  have hx₀Q : x₀ ∈ Q := by
    dsimp [Q]
    exact JoinedIn.refl hx₀s
  -- (a) Q is open in X: every point of Q carries an open neighbourhood U ⊆ Q
  have hQopen : IsOpen Q := by
    rw [isOpen_iff_mem_nhds]
    intro y hyQ
    have hys : y ∈ s := hQsub hyQ
    rcases hloc y hys with ⟨U, hUopen, hyU, hUpath, hUsub⟩
    refine mem_of_superset (hUopen.mem_nhds hyU) ?_
    intro z hzU
    dsimp [Q]
    exact JoinedIn.trans hyQ (JoinedIn.mono (hUpath.joinedIn y hyU z hzU) hUsub)
  -- (b) s ⊆ Q
  have hsQ : s ⊆ Q := by
    -- any point of s in the closure of Q must lie in Q, so the connected
    -- set s cannot leave Q (IsPreconnected.subset_of_closure_inter_subset)
    apply hs.isPreconnected.subset_of_closure_inter_subset hQopen
    · exact ⟨x₀, hx₀s, hx₀Q⟩
    · intro y hy
      rcases hy with ⟨hycl, hys⟩
      by_contra hyQn
      rcases hloc y hys with ⟨U, hUopen, hyU, hUpath, hUsub⟩
      have hUQempty : U ∩ Q = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro z hz
        have hjz : JoinedIn s x₀ z := by simpa [Q] using hz.2
        have hjy : JoinedIn s x₀ y :=
          JoinedIn.trans hjz (JoinedIn.mono (hUpath.joinedIn z hz.1 y hyU) hUsub)
        exact hyQn (by simpa [Q] using hjy)
      have hne : (U ∩ Q).Nonempty := (mem_closure_iff.1 hycl) U hUopen hyU
      exact (Set.not_nonempty_iff_eq_empty.mpr hUQempty) hne
  intro y hys
  exact (by simpa [Q] using hsQ hys)

end Commons.Topology.PathConnected