import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.Torsion.ModelGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The chart pieces of the Thom space over an arbitrary cover of the Grassmannian

**This is the corrected route to item 3** (`Work.ThomBordism.Grassmann.ThomSpaceConnected`).

For an arbitrary indexed family `U : ι → Set (OG k m)` of open subsets of the oriented Grassmannian
we consider the open subsets of the Thom space `T = Th γ = OnePoint (TotalSpace γ)`

`pieceCover k m (U i) = far 1 ∪ π⁻¹ (U i)`,   `π = proj`,   `far 1 = {fibN > 1} ∪ {∞}`.

They are open, and for a finite family they satisfy

`⋂ i ∈ S, pieceCover k m (U i) = pieceCover k m (⋂ i ∈ S, U i)`

(the family is a *filter base* of "escape" neighbourhoods of `∞`), so every finite intersection is
again a chart piece over the intersection `⋂ i ∈ S, U i`.

The point of using an **arbitrary** cover, rather than the cover by the chart cells `baseSet S`, is
that a chart piece `far 1 ∪ π⁻¹ W` is `(k-1)`-connected **only when `W` is highly connected** — the
`W⁺`-compactification of `W` enters the homotopy type.  For `W = baseSet S ≅ ℝ^{km}` this holds, but
for the intersections `baseSet S ∩ baseSet S'` it does not.  The correct input is therefore a
*finitely indexed good cover* of `G̃r_k(ℝ^{k+m})` subordinate to the chart cells (existence:
`Work.ThomBordism.Grassmann.Torsion.goodCoverSubordinate`), whose finite intersections are
contractible; see `GoodCover/Main.lean`.
-/

open scoped Topology
open Work.TangentClasses

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-- **A piece of the Thom space over an open subset of the Grassmannian**: the point at infinity,
the far region `{fibN > 1}`, and the part of the total space lying over `U`. -/
def pieceCover (k m : ℕ) (U : Set (OG k m)) : Set (TautologicalThomSpace k m) :=
  Torsion.far k m 1 ∪ OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' U)

/-- The point at infinity lies in every piece. -/
theorem infty_mem_pieceCover (k m : ℕ) (U : Set (OG k m)) :
    OnePoint.infty ∈ pieceCover k m U :=
  Or.inl (Torsion.infty_mem_far k m 1)

/-- A point of the total space whose projection lies in `U` lies in the piece. -/
theorem some_mem_pieceCover (k m : ℕ) {U : Set (OG k m)}
    {p : (tautologicalBundle k m).TotalSpace} (hp : p.proj ∈ U) :
    (OnePoint.some p : TautologicalThomSpace k m) ∈ pieceCover k m U :=
  Or.inr ⟨p, hp, rfl⟩

/-- The piece over `U` is contained in the piece over `V` for `U ⊆ V`. -/
theorem pieceCover_mono (k m : ℕ) {U V : Set (OG k m)} (h : U ⊆ V) :
    pieceCover k m U ⊆ pieceCover k m V :=
  Set.union_subset_union_right _ (Set.image_mono (Set.preimage_mono h))

/-- The piece over the whole Grassmannian is the whole Thom space. -/
theorem pieceCover_univ (k m : ℕ) : pieceCover k m (Set.univ : Set (OG k m)) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  rcases x with _ | p
  · exact infty_mem_pieceCover k m Set.univ
  · exact some_mem_pieceCover k m (Set.mem_univ p.proj)

/-- **The piece is open**: `far 1` is open and `π⁻¹ U` is open, the latter being carried by the
open embedding `OnePoint.some`. -/
theorem isOpen_pieceCover (k m : ℕ) {U : Set (OG k m)} (hU : IsOpen U) :
    IsOpen (pieceCover k m U) := by
  have hfar : IsOpen (Torsion.far k m 1) := Torsion.isOpen_far_one k m
  have himg : IsOpen (OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' U)) :=
    OnePoint.isOpenEmbedding_coe.isOpenMap _
      ((Work.TangentClasses.RealBundle.continuous_proj _).isOpen_preimage _ hU)
  exact hfar.union himg

/-- **The finite intersections of the pieces are the pieces over the intersections.** -/
theorem iInter_pieceCover (k m : ℕ) {ι : Type} (U : ι → Set (OG k m)) (S : Finset ι) :
    (⋂ i ∈ S, pieceCover k m (U i)) = pieceCover k m (⋂ i ∈ S, U i) := by
  ext x
  constructor
  · intro hx
    by_cases h : x ∈ Torsion.far k m 1
    · exact Or.inl h
    · refine Or.inr ?_
      have hx' : ∀ i ∈ S, x ∈ pieceCover k m (U i) := Set.mem_iInter₂.mp hx
      have hE : ∃ p : (tautologicalBundle k m).TotalSpace, OnePoint.some p = x := by
        rcases x with _ | p
        · exact absurd (Torsion.infty_mem_far k m 1) h
        · exact ⟨p, rfl⟩
      obtain ⟨p, rfl⟩ := hE
      refine ⟨p, ?_, rfl⟩
      rw [Set.mem_preimage]
      refine Set.mem_iInter₂.mpr fun i hi => ?_
      rcases hx' i hi with h' | h'
      · exact absurd h' h
      · obtain ⟨q, hq, hqp⟩ := h'
        rw [Set.mem_preimage] at hq
        rwa [Option.some.inj hqp] at hq
  · intro hx
    rcases hx with h | ⟨p, hp, rfl⟩
    · exact Set.mem_iInter₂.mpr fun i _ => Or.inl h
    · rw [Set.mem_preimage] at hp
      refine Set.mem_iInter₂.mpr fun i hi => some_mem_pieceCover k m ?_
      exact Set.mem_iInter₂.mp hp i hi

/-- **Every finite intersection of the pieces is nonempty** (it contains `∞`). -/
theorem nonempty_iInter_pieceCover (k m : ℕ) {ι : Type} (U : ι → Set (OG k m))
    (S : Finset ι) : (⋂ i ∈ S, pieceCover k m (U i)).Nonempty :=
  ⟨OnePoint.infty, Set.mem_iInter₂.mpr fun i _ => infty_mem_pieceCover k m (U i)⟩

/-- **The pieces cover the Thom space** as soon as the `U i` cover the Grassmannian. -/
theorem iUnion_pieceCover (k m : ℕ) {ι : Type} [Nonempty ι] (U : ι → Set (OG k m))
    (h : (⋃ i, U i) = Set.univ) : (⋃ i, pieceCover k m (U i)) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  rcases x with _ | p
  · exact Set.mem_iUnion.mpr ⟨Classical.arbitrary ι, infty_mem_pieceCover k m (U _)⟩
  · have hp : p.proj ∈ ⋃ i, U i := by rw [h]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    exact Set.mem_iUnion.mpr ⟨i, some_mem_pieceCover k m hi⟩

/-- The same, in the `Finset`-indexed form used by `finsetCoveredConnected`. -/
theorem iUnion_univ_pieceCover (k m m' : ℕ) [Nonempty (Fin m')] (U : Fin m' → Set (OG k m))
    (h : (⋃ i, U i) = Set.univ) :
    (⋃ i ∈ (Finset.univ : Finset (Fin m')), pieceCover k m (U i)) = Set.univ := by
  rw [show (⋃ i ∈ (Finset.univ : Finset (Fin m')), pieceCover k m (U i))
      = (⋃ i, pieceCover k m (U i)) from by ext x; simp]
  exact iUnion_pieceCover k m U h

end

end Work.ThomBordism.Grassmann
