import Mathlib
import Submission.Work.PlanarSC.BO.Defs
import Submission.Work.PlanarSC.BO.Geometry
import Submission.Work.PlanarSC.BO.graph_connected
import Submission.Work.PlanarSC.BO.graph_acyclic
import Submission.Work.PlanarSC.BO.preconn_peel
import Submission.Work.PlanarSC.exists_leaf_of_connected_acyclic

/-!
# A connected Jordan-free step family admits a building order

`Work.HornSC.CellBoundaryJordan.BO.hasStepOrder_of_no_jordan`: if the union of the closed unit
segments of a nonempty finite family `A` of unit lattice steps is preconnected and contains no
Jordan curve, then `A` admits a building order (`HasStepOrder A`).

The proof is by strong induction on `A.card`: by the graph-theoretic leaf theorem
(`Work.PlanarSC.exists_leaf_of_connected_acyclic`) applied to the graph `(stepVerts A, StepAdj A)`
(connected by `graph_connected`, acyclic by `graph_acyclic`) there is a vertex `v` with a unique
neighbour `v₀`; the step `e` realising it meets the union of the remaining steps in exactly the
point `lpt v₀`, so `e` may be placed last and the induction hypothesis applies to `A.erase e`.
-/

open Set

namespace Work.HornSC.CellBoundaryJordan.BO

noncomputable section

/-! ## Bookkeeping for the unions -/

theorem iUnion_lt_eq_biUnion_range {k : ℕ} (P : ℕ → Set ℂ) :
    (⋃ j, ⋃ (_ : j < k), P j) = ⋃ j ∈ Finset.range k, P j := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_biUnion, Finset.mem_range]

theorem iUnion_range_eq_of_onto {N : ℕ} {g : ℕ → (ℤ × ℤ) × (ℤ × ℤ)}
    {B : Finset ((ℤ × ℤ) × (ℤ × ℤ))} (h : ∀ e, e ∈ B ↔ ∃ k, k < N ∧ g k = e)
    (P : (ℤ × ℤ) × (ℤ × ℤ) → Set ℂ) :
    (⋃ k ∈ Finset.range N, P (g k)) = ⋃ e ∈ B, P e := by
  ext z
  simp only [Set.mem_iUnion, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, hz⟩
    exact ⟨g k, (h (g k)).mpr ⟨k, hk, rfl⟩, hz⟩
  · rintro ⟨e, he, hz⟩
    obtain ⟨k, hk, rfl⟩ := (h e).mp he
    exact ⟨k, hk, hz⟩

theorem iUnion_eq_insert_erase {A : Finset ((ℤ × ℤ) × (ℤ × ℤ))} {e : (ℤ × ℤ) × (ℤ × ℤ)}
    (he : e ∈ A) :
    (⋃ g ∈ A, stepSeg g) = stepSeg e ∪ ⋃ g ∈ A.erase e, stepSeg g := by
  conv_lhs => rw [← Finset.insert_erase he]
  ext z
  simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_insert, Set.mem_union, exists_prop]
  constructor
  · rintro ⟨g, hg | hg, hz⟩
    · exact Or.inl (hg ▸ hz)
    · exact Or.inr ⟨g, hg, hz⟩
  · rintro (hz | ⟨g, hg, hz⟩)
    · exact ⟨e, Or.inl rfl, hz⟩
    · exact ⟨g, Or.inr hg, hz⟩

theorem erase_iUnion_subset (A : Finset ((ℤ × ℤ) × (ℤ × ℤ))) (e : (ℤ × ℤ) × (ℤ × ℤ)) :
    (⋃ g ∈ A.erase e, stepSeg g) ⊆ ⋃ g ∈ A, stepSeg g := by
  intro z hz
  obtain ⟨g, hg, hz⟩ := Set.mem_iUnion₂.mp hz
  exact Set.mem_iUnion₂.mpr ⟨g, Finset.mem_of_mem_erase hg, hz⟩

/-! ## The induction -/

theorem hasStepOrder_of_no_jordan (A : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (hunit : ∀ e ∈ A, IsUnitStep e) (hne : A.Nonempty)
    (hconn : IsPreconnected (⋃ e ∈ A, stepSeg e))
    (hno : ¬ ∃ γ : C(Circle, ℂ), Function.Injective γ ∧ Set.range γ ⊆ ⋃ e ∈ A, stepSeg e) :
    HasStepOrder A := by
  classical
  have key : ∀ n : ℕ, ∀ A : Finset ((ℤ × ℤ) × (ℤ × ℤ)), A.card = n →
      (∀ e ∈ A, IsUnitStep e) → A.Nonempty →
      IsPreconnected (⋃ e ∈ A, stepSeg e) →
      (¬ ∃ γ : C(Circle, ℂ), Function.Injective γ ∧ Set.range γ ⊆ ⋃ e ∈ A, stepSeg e) →
      HasStepOrder A := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro A hcard hunit hne hconn hno
      rcases lt_or_ge A.card 2 with hlt | hge
      · -- `A` is a single step
        have hpos0 : 0 < A.card := Finset.card_pos.mpr hne
        obtain ⟨e₀, he₀⟩ := Finset.card_eq_one.mp (by omega : A.card = 1)
        subst he₀
        refine ⟨1, fun _ => e₀, by norm_num, ?_, ?_⟩
        · intro e
          constructor
          · intro h
            rw [Finset.mem_singleton] at h
            exact ⟨0, by norm_num, h.symm⟩
          · rintro ⟨k, hk, hke⟩
            rw [Finset.mem_singleton]
            exact hke.symm
        · intro k hk hk1
          omega
      · -- at least two steps
        have hcardA : 2 ≤ A.card := hge
        have hpos : 1 ≤ A.card := Finset.card_pos.mpr hne
        obtain ⟨e, heA⟩ := hne
        -- `stepVerts A` has at least two elements
        have hT2 : 2 ≤ (stepVerts A).card := by
          have hsub : ({e.1, e.2} : Finset (ℤ × ℤ)) ⊆ stepVerts A := by
            intro x hx
            rcases Finset.mem_insert.mp hx with hx | hx
            · rw [hx]; exact stepVerts_mem_fst heA
            · rw [Finset.mem_singleton.mp hx]; exact stepVerts_mem_snd heA
          calc 2 = ({e.1, e.2} : Finset (ℤ × ℤ)).card :=
                (Finset.card_pair (isStep_ne (hunit e heA))).symm
            _ ≤ (stepVerts A).card := Finset.card_le_card hsub
        -- the leaf vertex of the graph
        obtain ⟨v, -, v₀, -, hadj, huniq⟩ :=
          Work.PlanarSC.exists_leaf_of_connected_acyclic (stepVerts A) (StepAdj A)
            (fun a b h => stepAdj_symm h)
            (fun a h => stepAdj_ne hunit h rfl)
            (fun a b => Work.PlanarSC.BO.graph_connected A hunit hconn a b)
            (fun m c hm hinj hadj' => Work.PlanarSC.BO.graph_acyclic A hunit hno m c hm hinj hadj')
            hT2
        obtain ⟨el, helA, helcase⟩ := hadj
        -- the endpoints of `el` are exactly `v` and `v₀`
        have hends : ({el.1, el.2} : Finset (ℤ × ℤ)) = {v, v₀} := by
          rcases helcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]
          · rw [h1, h2, Finset.pair_comm]
        -- every neighbour of `v` is `v₀`
        have hval : ∀ y, StepAdj A v y → y = v₀ :=
          fun y hy => huniq y (stepVerts_of_stepAdj hy).2 hy
        -- `el` meets the rest only at `v₀`
        have hsubset : stepSeg el ∩ (⋃ g ∈ A.erase el, stepSeg g) ⊆ {lpt v₀} := by
          rintro z ⟨hz1, hz2⟩
          obtain ⟨g, hg, hz2⟩ := Set.mem_iUnion₂.mp hz2
          have hgA : g ∈ A := Finset.mem_of_mem_erase hg
          have hgne : g ≠ el := Finset.ne_of_mem_erase hg
          obtain ⟨hze, hzg⟩ := unitStep_seg_inter_subset (hunit el helA) (hunit g hgA)
            (fun hh => hgne hh.symm) ⟨hz1, hz2⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hze hzg
          have hzt : z = lpt v ∨ z = lpt v₀ := by
            rcases hze with hze | hze
            · have hm : el.1 ∈ ({el.1, el.2} : Finset (ℤ × ℤ)) := by simp
              rw [hends] at hm
              rcases Finset.mem_insert.mp hm with h1 | h1
              · exact Or.inl (by rw [hze, h1])
              · exact Or.inr (by rw [hze, Finset.mem_singleton.mp h1])
            · have hm : el.2 ∈ ({el.1, el.2} : Finset (ℤ × ℤ)) := by simp
              rw [hends] at hm
              rcases Finset.mem_insert.mp hm with h1 | h1
              · exact Or.inl (by rw [hze, h1])
              · exact Or.inr (by rw [hze, Finset.mem_singleton.mp h1])
          rcases hzt with hz | hz
          · -- `z = lpt v` would give another edge at `v`
            exfalso
            have hv_g : v = g.1 ∨ v = g.2 := by
              have hzg' : lpt v ∈ ({lpt g.1, lpt g.2} : Set ℂ) := hz ▸ hzg
              simpa using hzg'
            have hgends : ({g.1, g.2} : Finset (ℤ × ℤ)) = {v, v₀} := by
              rcases hv_g with h1 | h1
              · have h2 : g.2 = v₀ := hval g.2 ⟨g, hgA, Or.inl ⟨h1.symm, rfl⟩⟩
                rw [h1.symm, h2]
              · have h2 : g.1 = v₀ := hval g.1 ⟨g, hgA, Or.inr ⟨rfl, h1.symm⟩⟩
                rw [h2, h1.symm, Finset.pair_comm]
            exact hgne (eq_of_unitStep_same_ends (hunit g hgA) (hunit el helA)
              (by rw [hgends, hends]))
          · exact hz
        -- the intersection is nonempty, by preconnectedness
        have herase : (A.erase el).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hc
          have h1 : (A.erase el).card = 0 := by rw [hc]; rfl
          rw [Finset.card_erase_of_mem helA] at h1
          omega
        have hnonempty : (stepSeg el ∩ (⋃ g ∈ A.erase el, stepSeg g)).Nonempty := by
          by_contra hempty
          rw [Set.not_nonempty_iff_eq_empty] at hempty
          have hcover : (⋃ g ∈ A, stepSeg g) = stepSeg el ∪ ⋃ g ∈ A.erase el, stepSeg g :=
            iUnion_eq_insert_erase helA
          have hsep := (isPreconnected_iff_subset_of_disjoint_closed.mp hconn)
            (stepSeg el) (⋃ g ∈ A.erase el, stepSeg g) (stepSeg_isClosed el)
            (isClosed_biUnion_stepSeg _) (le_of_eq hcover)
            (by rw [hcover, ← Set.inter_assoc, Set.union_inter_cancel_left, hempty])
          rcases hsep with hsub | hsub
          · obtain ⟨g, hg⟩ := herase
            obtain ⟨z, hz⟩ := stepSeg_nonempty g
            have hzv : z ∈ ⋃ g ∈ A.erase el, stepSeg g := Set.mem_iUnion₂.mpr ⟨g, hg, hz⟩
            have hzu : z ∈ stepSeg el := hsub (hcover ▸ Set.mem_union_right _ hzv)
            have hmem : z ∈ stepSeg el ∩ (⋃ g ∈ A.erase el, stepSeg g) := ⟨hzu, hzv⟩
            rw [hempty] at hmem
            exact hmem
          · obtain ⟨z, hz⟩ := stepSeg_nonempty el
            have hzu : z ∈ ⋃ g ∈ A, stepSeg g := Set.mem_iUnion₂.mpr ⟨el, helA, hz⟩
            have hzv : z ∈ ⋃ g ∈ A.erase el, stepSeg g := hsub (hcover ▸ hzu)
            have hmem : z ∈ stepSeg el ∩ (⋃ g ∈ A.erase el, stepSeg g) := ⟨hz, hzv⟩
            rw [hempty] at hmem
            exact hmem
        have hmeet : stepSeg el ∩ (⋃ g ∈ A.erase el, stepSeg g) = {lpt v₀} := by
          refine Set.Subset.antisymm hsubset ?_
          rintro z hz
          obtain ⟨y, hyS⟩ := hnonempty
          have hy : y = lpt v₀ := hsubset hyS
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact hy ▸ hyS
        -- the induction hypothesis for the smaller family
        have hunit' : ∀ g ∈ A.erase el, IsUnitStep g :=
          fun g hg => hunit g (Finset.mem_of_mem_erase hg)
        have hno' : ¬ ∃ γ : C(Circle, ℂ), Function.Injective γ ∧
            Set.range γ ⊆ ⋃ g ∈ A.erase el, stepSeg g := by
          rintro ⟨γ, hinj, hrange⟩
          exact hno ⟨γ, hinj, fun z hz => erase_iUnion_subset A el (hrange hz)⟩
        have hconn' : IsPreconnected (⋃ g ∈ A.erase el, stepSeg g) :=
          Work.PlanarSC.BO.preconn_peel (stepSeg_isClosed el) (isClosed_biUnion_stepSeg _)
            (iUnion_eq_insert_erase helA) hconn hmeet
        have hlt' : (A.erase el).card < n := by
          rw [Finset.card_erase_of_mem helA, hcard]
          omega
        obtain ⟨N', g, hN', honto', hint'⟩ :=
          ih (A.erase el).card hlt' (A.erase el) rfl hunit' herase hconn' hno'
        -- assemble
        set F : ℕ → (ℤ × ℤ) × (ℤ × ℤ) := fun k => if k < N' then g k else el with hF
        refine ⟨N' + 1, F, by omega, ?_, ?_⟩
        · intro e'
          simp only [hF]
          constructor
          · intro he'
            by_cases h : e' = el
            · subst h
              refine ⟨N', by omega, ?_⟩
              simp
            · have hmem : e' ∈ A.erase el := Finset.mem_erase.mpr ⟨h, he'⟩
              obtain ⟨k, hk, hfk⟩ := (honto' e').mp hmem
              exact ⟨k, by omega, by simp [hk, hfk]⟩
          · rintro ⟨k, hk, hfk⟩
            by_cases h : k < N'
            · have hgk : g k = e' := by simpa [h] using hfk
              exact Finset.mem_of_mem_erase ((honto' e').mpr ⟨k, h, hgk⟩)
            · have hel : el = e' := by simpa [h] using hfk
              rw [← hel]
              exact helA
        · intro k hk hkN
          simp only [hF]
          by_cases h : k < N'
          · have hcongr : (⋃ j, ⋃ (_ : j < k), stepSeg (if j < N' then g j else el)) =
                ⋃ j, ⋃ (_ : j < k), stepSeg (g j) := by
              refine Set.iUnion_congr fun j => Set.iUnion_congr fun hj => ?_
              rw [if_pos (lt_trans hj h)]
            rw [if_pos h, hcongr]
            exact hint' k hk h
          · have hk' : k = N' := by omega
            have hcongr : (⋃ j, ⋃ (_ : j < k), stepSeg (if j < N' then g j else el)) =
                ⋃ j ∈ Finset.range N', stepSeg (g j) := by
              rw [iUnion_lt_eq_biUnion_range, hk']
              ext z
              simp only [Set.mem_iUnion, Finset.mem_range]
              constructor
              · rintro ⟨j, hj, hz⟩
                exact ⟨j, hj, by rwa [if_pos hj] at hz⟩
              · rintro ⟨j, hj, hz⟩
                exact ⟨j, hj, by rw [if_pos hj]; exact hz⟩
            rw [if_neg h, hcongr, iUnion_range_eq_of_onto honto' stepSeg, hmeet]
            exact ⟨v₀, rfl⟩
  exact key A.card A rfl hunit hne hconn hno

end

end Work.HornSC.CellBoundaryJordan.BO
