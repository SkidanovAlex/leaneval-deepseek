import Submission.Work.InnermostDisk.Reduction

/-!
# The cut-and-paste step on its own, and the induction that finishes it

Pardon's second innermost argument is a *single* cut-and-paste: an inessential curve `γ ⊆ D ∩ F`
innermost in the disc `D` bounds a disc `D_γ ⊆ D` whose interior misses `F`, as well as a disc
`E ⊆ F`; pushing `D_γ` through the embedded sphere `D_γ ∪ E` removes the intersection `γ` and
reduces the number of intersection curves.  Iterating, all intersections disappear.

This file isolates the single step as the predicate `RemovesOneCurve` and *proves* that it
implies the full cleaning step `CleansDiscs` (Pardon's "Proceeding in this way, we may eliminate
all the intersections of `D` with `F`"):

* `boundsDiskInComplement_of_isEmpty` — the trivial case (base of the induction): if the interior
  of the innermost disc meets `F` in no curve at all, then its boundary is already a compressing
  loop;
* `cleansDiscs_of_removesOneCurve` — the induction: a strictly decreasing sequence of numbers of
  intersection curves must reach `0`.

The point of the decomposition is that `RemovesOneCurve` is *one* cut-and-paste, not the whole
process; it is the form in which Pardon's "it is easy to see that we can modify `D` so as to
eliminate this intersection" is actually proved.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

namespace Work.InnermostDisk

noncomputable section

variable {P : ParamTorus}

/-- **The base case of the cut-and-paste induction.**  If the interior of the disc of an
innermost datum meets `F` in no curve (the index type is empty), then the boundary `α` already
bounds an embedded disc whose interior is disjoint from `F`. -/
theorem boundsDiskInComplement_of_isEmpty (S : Set R3) (D : InnermostDisc P S)
    (h : IsEmpty D.ι) : BoundsDiskInComplement P D.α := by
  refine ⟨D.e, D.inj, D.boundary, fun z hz hmem => ?_⟩
  obtain ⟨i, -⟩ := D.covers z hz hmem
  exact h.false i

/-- **A single cut-and-paste step.**  Any innermost disc with at least one inessential
intersection curve can be replaced (keeping its boundary curve `α`) by an innermost disc whose
number of intersection curves is strictly smaller.

This is the geometric heart of Pardon's second innermost argument. -/
def RemovesOneCurve (P : ParamTorus) : Prop :=
  ∀ (S : Set R3) (D : InnermostDisc P S), 0 < Fintype.card D.ι →
    ∃ (S' : Set R3) (D' : InnermostDisc P S'),
      D'.α = D.α ∧ Fintype.card D'.ι < Fintype.card D.ι

/-- **The cut-and-paste step, iterated.**  A single cut-and-paste operation implies the full
cleaning of an innermost disc: iterating it strictly decreases the number of intersection curves,
which must therefore reach zero, and then `boundsDiskInComplement_of_isEmpty` applies. -/
theorem cleansDiscs_of_removesOneCurve (h : RemovesOneCurve P) : CleansDiscs P := by
  have key : ∀ n : ℕ, ∀ (S : Set R3) (D : InnermostDisc P S), Fintype.card D.ι = n →
      BoundsDiskInComplement P D.α := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S D hn
      rcases Nat.eq_zero_or_pos (Fintype.card D.ι) with h0 | hpos
      · have hI : IsEmpty D.ι := Fintype.card_eq_zero_iff.mp h0
        exact boundsDiskInComplement_of_isEmpty S D hI
      · obtain ⟨S', D', hα, hlt⟩ := h S D hpos
        rw [← hα]
        exact ih (Fintype.card D'.ι) (by omega) S' D' rfl
  exact fun S D => key (Fintype.card D.ι) S D rfl

/-- The single cut-and-paste step for one fixed sphere `S` (the local form of
`RemovesOneCurve`).  The replacement disc is allowed to leave `S`, which is why the local form is
quantified over all spheres when used in the iteration. -/
def RemovesOneCurveOn (P : ParamTorus) (S : Set R3) : Prop :=
  ∀ D : InnermostDisc P S, 0 < Fintype.card D.ι →
    ∃ (S' : Set R3) (D' : InnermostDisc P S'),
      D'.α = D.α ∧ Fintype.card D'.ι < Fintype.card D.ι

/-- The global cut-and-paste step gives the local one at every sphere. -/
theorem RemovesOneCurveOn.of_removesOneCurve {P : ParamTorus} {S : Set R3}
    (h : RemovesOneCurve P) : RemovesOneCurveOn P S :=
  fun D hD => h S D hD

/-- Conversely, the local step at every sphere is the global step. -/
theorem removesOneCurve_of_forall_removesOneCurveOn {P : ParamTorus}
    (h : ∀ S : Set R3, RemovesOneCurveOn P S) : RemovesOneCurve P :=
  fun S D hD => h S D hD

/-- **Pardon's Lemma from the local cut-and-paste step at every sphere.** -/
theorem mustbeinessential_of_removesOneCurveOn_all (P : ParamTorus) (β : ClosedCurve P)
    (S : Set R3) (hRem : ∀ S' : Set R3, RemovesOneCurveOn P S')
    (hIn : InnermostDiscInput P S)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_of_inputs P β S hIn
    (cleansDiscs_of_removesOneCurve (removesOneCurve_of_forall_removesOneCurveOn hRem)) hSβ

/-! ## Pardon's lemma from the single cut-and-paste step -/

/-- **Pardon's Lemma 4.2 from the single cut-and-paste step.** -/
theorem mustbeinessential_of_removesOneCurve (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (hRem : RemovesOneCurve P) (hIn : InnermostDiscInput P S)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_of_inputs P β S hIn (cleansDiscs_of_removesOneCurve hRem) hSβ

/-- **Pardon's Lemma 4.2 with abstract `I`, from the single cut-and-paste step.** -/
theorem mustbeinessential_core_of_removesOneCurve (P : ParamTorus) (β : ClosedCurve P)
    (S : Set R3) (I : ℕ∞)
    (hI : ∀ α : ClosedCurve P, IsSimple P α → IsEssential P α → BoundsDiskInComplement P α →
      I ≤ Set.encard (Set.range α.γ ∩ Set.range β.γ))
    (hRem : RemovesOneCurve P) (hIn : InnermostDiscInput P S)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < I) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_core_of_inputs P β S I hI hIn (cleansDiscs_of_removesOneCurve hRem) hSβ

end

end Work.InnermostDisk
