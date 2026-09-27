import Mathlib
import Submission.Work.EQ.UnivCover.Defs
import Submission.Work.EQ.UnivCover.Sheet
import Submission.Work.EQ.UnivCover.Topology
import Submission.Work.EQ.UnivCover.Cover

/-!
# Second countability of the universal cover

If `X` is second countable, carries a disc-like neighbourhood basis `HasDiscBasis X`, and the
homotopy classes of paths from the base point `x₀` to every point of `X` form a countable set, then
the universal cover `UC x₀` (topologised by its sheets) is second countable.

The proof produces an explicit countable family of open sets which is a basis of `UC x₀`: the
sheets over the members of a countable disc-like cover, intersected with the preimages of the sets
of a countable basis of `X`.  The key ingredient is that the projection restricted to a sheet over
a disc-like set is an open map.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
open _root_.Topology
open scoped Topology
open Work.EQ.UnivCover

namespace Work.EQ.UnivCover

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

/-- **Symmetry of sheet membership.**  If `e'` lies in the sheet of `e` over `V`, then `e` lies in
the sheet of `e'` over `V`. -/
theorem UC.mem_sheet_of_mem_sheet {V : Set X} {e e' : UC x₀} (h : e' ∈ UC.sheet e V) :
    e ∈ UC.sheet e' V := by
  obtain ⟨-, δ, hδ, hcls⟩ := UC.mem_sheet_iff.mp h
  refine UC.mem_sheet_iff.mpr ⟨?_, δ.symm, fun t => ?_, ?_⟩
  · have := hδ 0; simpa using this
  · rw [Path.symm_apply]; exact hδ _
  · rw [hcls, Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl]

/-- A sheet over a set not containing the base point of the sheet is empty. -/
theorem UC.sheet_eq_empty_of_not_mem {V : Set X} {e : UC x₀} (h : e.pt ∉ V) :
    UC.sheet e V = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro e' he'
  obtain ⟨-, δ, hδ, -⟩ := UC.mem_sheet_iff.mp he'
  exact h (by rw [← δ.source]; exact hδ 0)

/-- **A sheet over a disc-like set is open**, with no condition on the base point of the sheet: if
the base point does not lie in the disc-like set the sheet is empty. -/
theorem UC.isOpen_sheet_of_isDiscLike (hB : HasDiscBasis X) {V : Set X} (hV : IsDiscLike V)
    (e : UC x₀) : IsOpen (UC.sheet e V) := by
  by_cases h : e.pt ∈ V
  · exact UC_isOpen_sheet hB hV h
  · rw [UC.sheet_eq_empty_of_not_mem h]; exact isOpen_empty

/-- **The projection is open on a sheet.**  For a disc-like set `V` and an open set `O` of the
cover, the projection of `O ∩ sheet e V` is open in `X`.  (The map `UC.proj` restricted to a sheet
over `V` is a homeomorphism onto `V`, and this is the openness half of that statement.) -/
theorem UC.isOpen_proj_image_sheet (hB : HasDiscBasis X) {V : Set X} (hV : IsDiscLike V)
    (e : UC x₀) {O : Set (UC x₀)} (hO : IsOpen O) :
    IsOpen (UC.proj '' (O ∩ UC.sheet e V)) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨e_y, ⟨he_yO, he_yS⟩, rfl⟩
  obtain ⟨t, ht_basis, he_y_t, ht_O⟩ :=
    (UC_isTopologicalBasis_basis hB).mem_nhds_iff.mp (hO.mem_nhds he_yO)
  obtain ⟨e₂, V₂, hV₂, he₂V₂, rfl⟩ := ht_basis
  obtain ⟨W, hW, hyW, hWV⟩ := hB e_y.pt (V ∩ V₂) (hV.isOpen.inter hV₂.isOpen)
    (Set.mem_inter he_yS.1 he_y_t.1)
  refine Filter.mem_of_superset (hW.isOpen.mem_nhds hyW) ?_
  intro z hz
  obtain ⟨x, hx, hxpt⟩ := UC_sheet_exists hW hyW hz
  have hxV : x ∈ UC.sheet e V := UC_sheet_trans he_yS hx (fun a ha => (hWV ha).1)
  have hxV₂ : x ∈ UC.sheet e₂ V₂ := UC_sheet_trans he_y_t hx (fun a ha => (hWV ha).2)
  exact ⟨x, ⟨ht_O hxV₂, hxV⟩, hxpt⟩

/-- **The universal cover is second countable.** -/
theorem UC_secondCountableTopology {X : Type*} [TopologicalSpace X] [T2Space X]
    [PathConnectedSpace X] [SecondCountableTopology X] {x₀ : X} (hB : HasDiscBasis X)
    {U : ℕ → Set X} (hU : DiscCover U) (hc : ∀ x : X, Countable (Path.Homotopic.Quotient x₀ x)) :
    SecondCountableTopology (UC x₀) := by
  classical
  -- A countable basis of `X`.
  obtain ⟨W, hW⟩ := TopologicalSpace.exists_seq_basis X
  -- A chosen point of each member of the disc-like cover (falling back to `x₀` when empty).
  let y : ℕ → X := fun n => if h : (U n).Nonempty then h.choose else x₀
  have hy : ∀ n, (U n).Nonempty → y n ∈ U n := by
    intro n h
    simp only [y]
    rw [dite_eq_left h]
    exact h.choose_spec
  -- The candidate countable family of open sets: sheets over the members of the disc-like cover,
  -- cut down by the preimages of the members of the countable basis of `X`.
  let P : (Σ n : ℕ, Path.Homotopic.Quotient x₀ (y n) × ℕ) → Set (UC x₀) :=
    fun i => UC.sheet ⟨y i.1, i.2.1⟩ (U i.1) ∩ UC.proj ⁻¹' (W i.2.2)
  haveI : Countable (Σ n : ℕ, Path.Homotopic.Quotient x₀ (y n) × ℕ) := by
    haveI : ∀ n, Countable (Path.Homotopic.Quotient x₀ (y n)) := fun n => hc (y n)
    infer_instance
  have hbasis : TopologicalSpace.IsTopologicalBasis (Set.range P) := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · -- every member of the family is open
      rintro s ⟨i, rfl⟩
      dsimp only [P]
      exact (UC.isOpen_sheet_of_isDiscLike hB (hU.1 i.1) ⟨y i.1, i.2.1⟩).inter
        ((hW.isOpen (Set.mem_range_self i.2.2)).preimage (UC_continuous_proj hB))
    · -- every neighbourhood of a point contains a member of the family
      intro a u hau hu
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (by rw [hU.2]; exact Set.mem_univ a.pt)
      have hne : (U n).Nonempty := ⟨a.pt, hn⟩
      have hyn : y n ∈ U n := hy n hne
      -- the projection of `u` on the sheet of `a` over `U n` is an open neighbourhood of `a.pt`
      have hpr_open : IsOpen (UC.proj '' (u ∩ UC.sheet a (U n))) :=
        UC.isOpen_proj_image_sheet hB (hU.1 n) a hu
      have ha_pr : a.pt ∈ UC.proj '' (u ∩ UC.sheet a (U n)) :=
        ⟨a, ⟨hau, UC.self_mem_sheet hn⟩, rfl⟩
      obtain ⟨t, ht, hapt_t, ht_sub⟩ := hW.mem_nhds_iff.mp (hpr_open.mem_nhds ha_pr)
      obtain ⟨k, rfl⟩ := ht
      -- the point of the cover over `y n` in the sheet of `a`, as an element of the index set
      obtain ⟨δ, hδ⟩ := (hU.1 n).path_connected hn hyn
      let q : Path.Homotopic.Quotient x₀ (y n) := a.cls.trans (Path.Homotopic.Quotient.mk δ)
      have hqS : (⟨y n, q⟩ : UC x₀) ∈ UC.sheet a (U n) := ⟨hyn, δ, hδ, rfl⟩
      refine ⟨P ⟨n, q, k⟩, ⟨⟨n, q, k⟩, rfl⟩, ?_, ?_⟩
      · dsimp only [P]
        exact ⟨UC.mem_sheet_of_mem_sheet hqS, hapt_t⟩
      · intro z hz
        dsimp only [P] at hz
        obtain ⟨hzS, hzk⟩ := hz
        obtain ⟨z', ⟨hz'u, hz'S⟩, hz'pt⟩ := ht_sub hzk
        have hzS' : z ∈ UC.sheet a (U n) := UC_sheet_trans hqS hzS subset_rfl
        have hzpt' : z.pt = z'.pt := hz'pt.symm
        have hzz' : z = z' := (UC_sheet_unique (hU.1 n)).1 hzS' hz'S hzpt'
        rw [hzz']; exact hz'u
  exact hbasis.secondCountableTopology (Set.countable_range P)

end Work.EQ.UnivCover
