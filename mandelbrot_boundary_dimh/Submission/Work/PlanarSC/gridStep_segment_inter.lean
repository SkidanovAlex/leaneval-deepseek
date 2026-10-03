import Mathlib
import Submission.Work.PlanarSC.GridWalk

namespace Work.PlanarSC

/-- A `IsUnitStep e` has distinct endpoints. -/
private lemma isUnitStep_ne' {e : (ℤ × ℤ) × (ℤ × ℤ)} (h : IsUnitStep e) : e.1 ≠ e.2 := by
  rintro he
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : e.1.2 = e.2.2 := by rw [he]
    omega
  · have : e.1.1 = e.2.1 := by rw [he]
    omega

/-- **Canonical form of a unit segment.**  A unit segment is, as a set, one of the two unit grid
segments at level `n`: a vertical piece `{z | z.re = a/2^n, b/2^n ≤ z.im ≤ (b+1)/2^n}` or the
horizontal piece `{z | z.im = b/2^n, a/2^n ≤ z.re ≤ (a+1)/2^n}`.  The lemma records, for the
chosen canonical parameters, the underlying pair of lattice points, the segment, and the pair of
endpoints. -/
private lemma unitSeg_canon {n : ℕ} {u v : ℤ × ℤ} (h : IsUnitSeg u v) :
    (∃ a b : ℤ, ({u, v} : Set (ℤ × ℤ)) = {(a, b), (a, b + 1)} ∧
        segment ℝ (lpt n u) (lpt n v) =
          segment ℝ (Commons.Topology.Plane.gcorner n a b)
            (Commons.Topology.Plane.gcorner n a (b + 1)) ∧
        ({lpt n u, lpt n v} : Set ℂ) =
          ({Commons.Topology.Plane.gcorner n a b,
            Commons.Topology.Plane.gcorner n a (b + 1)} : Set ℂ)) ∨
    (∃ a b : ℤ, ({u, v} : Set (ℤ × ℤ)) = {(a, b), (a + 1, b)} ∧
        segment ℝ (lpt n u) (lpt n v) =
          segment ℝ (Commons.Topology.Plane.gcorner n a b)
            (Commons.Topology.Plane.gcorner n (a + 1) b) ∧
        ({lpt n u, lpt n v} : Set ℂ) =
          ({Commons.Topology.Plane.gcorner n a b,
            Commons.Topology.Plane.gcorner n (a + 1) b} : Set ℂ)) := by
  rcases h with hh | hh
  · rcases hh with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine Or.inl ⟨u.1, u.2, ?_, ?_, ?_⟩
      · have hv : v = (u.1, u.2 + 1) := Prod.ext e1.symm e2.symm
        rw [hv]
      · have hv : v = (u.1, u.2 + 1) := Prod.ext e1.symm e2.symm
        rw [hv]; rfl
      · have hv : v = (u.1, u.2 + 1) := Prod.ext e1.symm e2.symm
        rw [hv]; rfl
    · refine Or.inr ⟨u.1, u.2, ?_, ?_, ?_⟩
      · have hv : v = (u.1 + 1, u.2) := Prod.ext e2.symm e1.symm
        rw [hv]
      · have hv : v = (u.1 + 1, u.2) := Prod.ext e2.symm e1.symm
        rw [hv]; rfl
      · have hv : v = (u.1 + 1, u.2) := Prod.ext e2.symm e1.symm
        rw [hv]; rfl
  · rcases hh with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine Or.inl ⟨v.1, v.2, ?_, ?_, ?_⟩
      · have hu : u = (v.1, v.2 + 1) := Prod.ext e1.symm e2.symm
        rw [hu]; exact Set.pair_comm _ _
      · have hu : u = (v.1, v.2 + 1) := Prod.ext e1.symm e2.symm
        rw [hu]; exact segment_symm ℝ _ _
      · have hu : u = (v.1, v.2 + 1) := Prod.ext e1.symm e2.symm
        rw [hu]; exact Set.pair_comm _ _
    · refine Or.inr ⟨v.1, v.2, ?_, ?_, ?_⟩
      · have hu : u = (v.1 + 1, v.2) := Prod.ext e2.symm e1.symm
        rw [hu]; exact Set.pair_comm _ _
      · have hu : u = (v.1 + 1, v.2) := Prod.ext e2.symm e1.symm
        rw [hu]; exact segment_symm ℝ _ _
      · have hu : u = (v.1 + 1, v.2) := Prod.ext e2.symm e1.symm
        rw [hu]; exact Set.pair_comm _ _

/-- Two unit segments with the same pair of endpoints are the same ordered pair of endpoints, up to
reversal.  Equivalently, the set of endpoints determines the ordered pair up to swapping. -/
private lemma unitSeg_endpoints_agree {u v u' v' : ℤ × ℤ} (h1 : IsUnitSeg u v)
    (h2 : IsUnitSeg u' v') (hset : ({u, v} : Set (ℤ × ℤ)) = {u', v'}) :
    (u, v) = (u', v') ∨ (u, v) = (v', u') := by
  have hu' : u' = u ∨ u' = v := by
    have hmem : u' ∈ ({u, v} : Set (ℤ × ℤ)) := by
      rw [hset]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hv' : v' = u ∨ v' = v := by
    have hmem : v' ∈ ({u, v} : Set (ℤ × ℤ)) := by
      rw [hset]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hu'v' : u' ≠ v' := by
    rcases h2 with hh | hh
    · exact isUnitStep_ne' hh
    · exact (isUnitStep_ne' hh).symm
  rcases hu' with h | h <;> rcases hv' with h' | h'
  · exact absurd (h.trans h'.symm) hu'v'
  · subst h; subst h'; exact Or.inl rfl
  · subst h; subst h'; exact Or.inr rfl
  · exact absurd (h.trans h'.symm) hu'v'

/-- Two unit segments of the level-`n` dyadic grid that are not the same set meet only in their
common endpoints.

Context (all in this workspace):
* `lpt n u = Commons.Topology.Plane.gcorner n u.1 u.2` (`Submission/Work/PlanarSC/GridWalk.lean`);
* `IsUnitSeg u v := IsUnitStep (u,v) ∨ IsUnitStep (v,u)`, where
  `Commons.Topology.Plane.IsUnitStep e := (e.1.1 = e.2.1 ∧ e.1.2 + 1 = e.2.2) ∨ (e.1.2 = e.2.2 ∧ e.1.1 + 1 = e.2.1)`
  (`Submission/Work/PlanarSC/jordan_criterion_simplyConnected.lean`). `IsUnitStep.ne` gives that a
  unit step has distinct endpoints, so both segments are nondegenerate. `hne1 ∧ hne2` says exactly
  that the two segments are different sets.

Useful existing ingredients in
`Submission/Lib/Unif2/Commons/Topology/Plane/exists_homotopyEquiv_subgraph_oneDimCW_of_dyadic_subcomplex.lean`
(namespace `Commons.Topology.Plane`): `gcorner_inj`, `mem_vSeg`, `mem_hSeg` (membership in a
vertical resp. horizontal unit grid segment as a conjunction of inequalities on `.re`/`.im`), and
the four pairwise intersection lemmas `gridSeg_vSeg_inter_vSeg`, `gridSeg_vSeg_inter_hSeg`,
`gridSeg_hSeg_inter_hSeg`, `gridSeg_hSeg_inter_vSeg`. A direct coordinate proof from
`mem_vSeg`/`mem_hSeg` is equally fine. Please name any helper lemma `private`. -/
theorem gridStep_segment_inter {n : ℕ} {u v u' v' : ℤ × ℤ}
    (h1 : IsUnitSeg u v) (h2 : IsUnitSeg u' v')
    (hne1 : (u, v) ≠ (u', v')) (hne2 : (u, v) ≠ (v', u')) :
    segment ℝ (lpt n u) (lpt n v) ∩ segment ℝ (lpt n u') (lpt n v') ⊆
      ({lpt n u, lpt n v} : Set ℂ) ∩ ({lpt n u', lpt n v'} : Set ℂ) := by
  rcases unitSeg_canon h1 with ⟨a, b, hp1, hs1, he1⟩ | ⟨a, b, hp1, hs1, he1⟩
  <;> rcases unitSeg_canon h2 with ⟨a', b', hp2, hs2, he2⟩ | ⟨a', b', hp2, hs2, he2⟩
  · rw [hs1, hs2, he1, he2]
    have hne : (a, b) ≠ (a', b') := by
      rintro hEq
      rw [Prod.mk.injEq] at hEq
      obtain ⟨rfl, rfl⟩ := hEq
      have hset : ({u, v} : Set (ℤ × ℤ)) = {u', v'} := by rw [hp1, hp2]
      rcases unitSeg_endpoints_agree h1 h2 hset with h | h
      · exact hne1 h
      · exact hne2 h
    exact Commons.Topology.Plane.gridSeg_vSeg_inter_vSeg (n := n) (a := a) (b := b)
      (a' := a') (b' := b') hne
  · rw [hs1, hs2, he1, he2]
    exact Commons.Topology.Plane.gridSeg_vSeg_inter_hSeg (n := n) (a := a) (b := b)
      (a' := a') (b' := b')
  · rw [hs1, hs2, he1, he2]
    exact Commons.Topology.Plane.gridSeg_hSeg_inter_vSeg (n := n) (a := a) (b := b)
      (a' := a') (b' := b')
  · rw [hs1, hs2, he1, he2]
    have hne : (a, b) ≠ (a', b') := by
      rintro hEq
      rw [Prod.mk.injEq] at hEq
      obtain ⟨rfl, rfl⟩ := hEq
      have hset : ({u, v} : Set (ℤ × ℤ)) = {u', v'} := by rw [hp1, hp2]
      rcases unitSeg_endpoints_agree h1 h2 hset with h | h
      · exact hne1 h
      · exact hne2 h
    exact Commons.Topology.Plane.gridSeg_hSeg_inter_hSeg (n := n) (a := a) (b := b)
      (a' := a') (b' := b') hne

end Work.PlanarSC
