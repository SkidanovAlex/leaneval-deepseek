/-
  Area E7 / `CoreLT_succ`, the vertical row: **the attainment dichotomy from the
  no-frontier-witness hypothesis**.

  Setting (see `NOTES_S53_span_pieces_and_levels.md` §2): `T` is a *span piece* — an absolute
  `Good` stratum with `T.j = m` and maximal `projTop`-tangential rank `n+1` (so `projTop` is a
  local diffeomorphism on `T`) — `C` is a base cell, and `ℓ : ℝⁿ → ℝ` is a level function.

  `attainment_open` (proved) says the attainment set
  `AttainSet T C ℓ = {x ∈ C | ∃ z ∈ T.X.set, projTop (absPt z) = Fin.snoc x (ℓ x)}`
  is *open* in `C` (the level graph is attained on a neighbourhood of every point where it is
  attained, because `projTop` maps a neighbourhood of the witness diffeomorphically).

  `eventually_not_attain_of_no_witness` (proved) says: if there is no *frontier witness* — no
  `p ∈ closure (absSet T) \ absSet T` lying over the graph of `ℓ` — then the non-attainment is
  open in `C` too.

  Combining the two with the preconnectedness of `C` gives the **attainment dichotomy**: on a
  preconnected `C`, either the level is attained everywhere or nowhere.  This is precisely the
  `hdich` input of the PROVED `cells_compat_span_piece_of_dichotomy`, so it closes the vertical row
  in every case where the no-frontier-witness hypothesis holds.

  The remaining case of the vertical row is the one where frontier witnesses *do* exist: then
  `exists_sheet_eq_of_witness` shows `ℓ` is identically a frontier sheet level over `C`, and the
  remaining mathematical input (`NOTES_S53` §6ter, case (FL)) is that such a level is *never
  attained* on a span piece over `C`.  `attain_dichotomy_of_cases` packages the two cases so that
  the assembly only has to supply one of them per level.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.AttainmentBasic
import Submission.Work.WilE7.CoreStep.attainment_open

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E

/-- The attainment set, viewed as a subset of the subtype `C`. -/
def AttainSub {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ)) (ℓ : (Fin n → ℝ) → ℝ) : Set ↥C :=
  {y | AttainAt T ℓ (y : Fin n → ℝ)}

/-- `AttainSub` unfolded. -/
theorem mem_AttainSub {n m : ℕ} {T : WilkiesDesign.E.Stratum 0 (n + (m + 1))}
    {C : Set (Fin n → ℝ)} {ℓ : (Fin n → ℝ) → ℝ} {y : ↥C} :
    y ∈ AttainSub T C ℓ ↔ AttainAt T ℓ (y : Fin n → ℝ) :=
  Iff.rfl

/-- **The attainment set is open in `C`.**  This is `attainment_open` re-packaged in the subtype. -/
theorem isOpen_attainSub {n m : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (hT : T.Good) (hj : T.j = m)
    (hrank : ∀ z ∈ T.X.set, Module.finrank ℝ
      ((LinearMap.ker (Work.WilE7.MainDesign.jac T z)).map
        ((Work.WilE7.CoreStep.projTopLin n m).comp
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1))))) = n + 1)
    (C : Set (Fin n → ℝ)) (ℓ : (Fin n → ℝ) → ℝ) (hℓ : ContinuousOn ℓ C) :
    IsOpen (AttainSub T C ℓ) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨U, hU, hUsub⟩ :=
    attainment_open T hT hj hrank C ℓ hℓ y.2 (by rwa [mem_AttainSub] at hy)
  rw [nhds_subtype]
  exact Filter.mem_comap.mpr ⟨U, hU, fun z hz => hUsub (z : Fin n → ℝ) ⟨z.2, hz⟩⟩

/-- **The attainment set is closed in `C`** whenever there is no frontier witness. -/
theorem isClosed_attainSub {n m : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ)) (ℓ : (Fin n → ℝ) → ℝ) (hℓ : ContinuousOn ℓ C)
    (hno : ∀ x ∈ C, ∀ p ∈ closure (Work.WilE7.MainDesign.absSet T),
      Work.WilE7.CoreStep.projTop n m p = Fin.snoc x (ℓ x) →
        p ∈ Work.WilE7.MainDesign.absSet T) :
    IsClosed (AttainSub T C ℓ) := by
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hy' : ¬ AttainAt T ℓ (y : Fin n → ℝ) := hy
  have h1 : {x : Fin n → ℝ | ¬ AttainAt T ℓ x} ∈ 𝓝[C] (y : Fin n → ℝ) :=
    eventually_not_attain_of_no_witness T C ℓ hℓ hno (y : Fin n → ℝ) y.2 hy'
  obtain ⟨t, ht, htsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h1
  rw [nhds_subtype]
  exact Filter.mem_comap.mpr ⟨t, ht, fun z hz => htsub ⟨hz, z.2⟩⟩

/-- **The attainment dichotomy from the absence of frontier witnesses.**  On a preconnected base
`C`, a level is either attained at every point of `C` or at none. -/
theorem attain_dichotomy_of_no_witness {n m : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (hT : T.Good) (hj : T.j = m)
    (hrank : ∀ z ∈ T.X.set, Module.finrank ℝ
      ((LinearMap.ker (Work.WilE7.MainDesign.jac T z)).map
        ((Work.WilE7.CoreStep.projTopLin n m).comp
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1))))) = n + 1)
    (C : Set (Fin n → ℝ)) (hCpc : IsPreconnected C)
    (ℓ : (Fin n → ℝ) → ℝ) (hℓ : ContinuousOn ℓ C)
    (hno : ∀ x ∈ C, ∀ p ∈ closure (Work.WilE7.MainDesign.absSet T),
      Work.WilE7.CoreStep.projTop n m p = Fin.snoc x (ℓ x) →
        p ∈ Work.WilE7.MainDesign.absSet T) :
    (∀ x ∈ C, AttainAt T ℓ x) ∨ (∀ x ∈ C, ¬ AttainAt T ℓ x) := by
  have hopen : IsOpen (AttainSub T C ℓ) := isOpen_attainSub T hT hj hrank C ℓ hℓ
  have hclosed : IsClosed (AttainSub T C ℓ) := isClosed_attainSub T C ℓ hℓ hno
  have huniv : IsPreconnected (Set.univ : Set ↥C) :=
    (Subtype.preconnectedSpace hCpc).isPreconnected_univ
  rcases huniv.subset_or_subset hopen hclosed.isOpen_compl disjoint_compl_right
      (fun z _ => (Classical.em (z ∈ AttainSub T C ℓ)).elim Or.inl
        (fun h => Or.inr (by simpa using h))) with h | h
  · left
    intro x hx
    exact h (Set.mem_univ (⟨x, hx⟩ : ↥C))
  · right
    intro x hx
    exact h (Set.mem_univ (⟨x, hx⟩ : ↥C))

/-- **The attainment dichotomy from the two cases.**  Either the level has no frontier witness
(the previous lemma applies), or it is a level which is known never to be attained (the case (FL)
of `NOTES_S53` §6ter, delivered by the classification `exists_sheet_eq_of_witness` plus the
frontier-sheet input).  This is the per-level input the `CoreLT_succ` assembly must supply. -/
theorem attain_dichotomy_of_cases {n m : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (hT : T.Good) (hj : T.j = m)
    (hrank : ∀ z ∈ T.X.set, Module.finrank ℝ
      ((LinearMap.ker (Work.WilE7.MainDesign.jac T z)).map
        ((Work.WilE7.CoreStep.projTopLin n m).comp
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1))))) = n + 1)
    (C : Set (Fin n → ℝ)) (hCpc : IsPreconnected C)
    (ℓ : (Fin n → ℝ) → ℝ) (hℓ : ContinuousOn ℓ C)
    (hcase : (∀ x ∈ C, ∀ p ∈ closure (Work.WilE7.MainDesign.absSet T),
        Work.WilE7.CoreStep.projTop n m p = Fin.snoc x (ℓ x) →
          p ∈ Work.WilE7.MainDesign.absSet T) ∨
      (∀ x ∈ C, ¬ AttainAt T ℓ x)) :
    (∀ x ∈ C, AttainAt T ℓ x) ∨ (∀ x ∈ C, ¬ AttainAt T ℓ x) := by
  rcases hcase with hno | hnever
  · exact attain_dichotomy_of_no_witness T hT hj hrank C hCpc ℓ hℓ hno
  · exact Or.inr hnever

/-- **Sign constancy on a preconnected set.**  A continuous function on a preconnected set which
never vanishes has constant sign.  This is the "index-free" half of the analysis of the frontier
row of `CoreLT_succ`: for the level family of a base cell, any two level functions are either equal
or everywhere unequal (`hdich`), so their difference has constant sign on the preconnected cell.

The application (see `NOTES_S54`): if the endpoint-value function `b` of a branch of a span piece
`T` over `C` is a level function of the family and `b(x) > ℓ(x)` on a nonempty part of `C`, then
`b > ℓ` on *all* of `C`; so `b(x₀) = ℓ(x₀)` at a switch point `x₀` forces `b ≡ ℓ`, contradicting
`b(x) > ℓ(x)`. -/
theorem sign_const_of_preconnected {α : Type*} [TopologicalSpace α] {C : Set α}
    (hC : IsPreconnected C) {f : α → ℝ} (hf : ContinuousOn f C)
    (h0 : ∀ x ∈ C, f x ≠ 0) :
    (∀ x ∈ C, 0 < f x) ∨ (∀ x ∈ C, f x < 0) := by
  have hcont : Continuous fun y : ↥C => f (y : α) :=
    continuousOn_iff_continuous_restrict.mp hf
  have hpos : IsOpen {y : ↥C | 0 < f (y : α)} := isOpen_lt continuous_const hcont
  have hneg : IsOpen {y : ↥C | f (y : α) < 0} := isOpen_lt hcont continuous_const
  have hdisj : Disjoint {y : ↥C | 0 < f (y : α)} {y : ↥C | f (y : α) < 0} :=
    Set.disjoint_left.mpr fun y hy hy' =>
      (lt_asymm (show (0:ℝ) < f (y : α) from hy)) (show f (y : α) < 0 from hy')
  have hcover : (Set.univ : Set ↥C) ⊆
      {y : ↥C | 0 < f (y : α)} ∪ {y : ↥C | f (y : α) < 0} := by
    intro y _
    rcases lt_trichotomy (f (y : α)) 0 with h | h | h
    · exact Or.inr h
    · exact absurd h (h0 _ y.2)
    · exact Or.inl h
  have huniv : IsPreconnected (Set.univ : Set ↥C) :=
    (Subtype.preconnectedSpace hC).isPreconnected_univ
  rcases huniv.subset_or_subset hpos hneg hdisj hcover with h | h
  · left; intro x hx; exact h (Set.mem_univ (⟨x, hx⟩ : ↥C))
  · right; intro x hx; exact h (Set.mem_univ (⟨x, hx⟩ : ↥C))

end Work.WilE7.CoreStep
