import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.SheetLocalDefs
import Submission.Work.WilE7.DimAPI.SheetP_localHomeo
import Submission.Work.WilE7.DimAPI.SheetP_closedMap
import Submission.Work.WilE7.DimAPI.CoveringSections

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.DimAPI
open WilkiesDesign WilkiesDesign.E

theorem sheets_of_localGraph {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) (C : Set (Fin p → ℝ))
    (hCell : WilkiesDesign.IsCell p C) (hCsub : C ⊆ WilkiesDesign.E.projFirst p q '' X)
    (hbdd : Bornology.IsBounded X)
    (hfin : ∀ x ∈ C, (WilkiesDesign.E.fiber X x).Finite)
    (hclosed : ∀ z ∈ closure X, WilkiesDesign.E.projFirst p q z ∈ C → z ∈ X)
    (hgraph : ∀ z ∈ X, WilkiesDesign.E.projFirst p q z ∈ C →
      ∃ V ∈ nhds z, ∃ U ∈ nhds (WilkiesDesign.E.projFirst p q z), ∃ g : (Fin p → ℝ) → (Fin q → ℝ),
        ContinuousOn g (C ∩ U) ∧ (∀ x ∈ C ∩ U, Fin.append x (g x) ∈ X ∩ V) ∧
        ∀ w ∈ X ∩ V, WilkiesDesign.E.projFirst p q w ∈ C → WilkiesDesign.E.projFirst p q w ∈ U ∧
          g (WilkiesDesign.E.projFirst p q w) = WilkiesDesign.E.projSnd p q w) :
    ∃ (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ)),
      (∀ j, ContinuousOn (s j) C) ∧
      (∀ x ∈ C, Function.Injective fun j : Fin k => s j x) ∧
      (∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X) ∧
      (∀ x ∈ C, (WilkiesDesign.E.fiber X x).ncard = k) ∧
      (∀ z ∈ X, WilkiesDesign.E.projFirst p q z ∈ C →
        ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p q z) = WilkiesDesign.E.projSnd p q z) := by
  -- the cell `C` is contractible: a base point `c₀` and a contraction `K` of `C` onto it
  obtain ⟨c₀, K, hc₀, hKcont, hK0, hK1, hKmem⟩ := Work.WilE7.isCellContractible hCell
  -- the sheet projection is a covering map
  have hcov : IsCoveringMap (SheetP X C) := by
    rw [isCoveringMap_iff_isCoveringMapOn_univ]
    refine (SheetP_closedMap X C hbdd hclosed).isCoveringMapOn_of_isLocalHomeomorphOn
      (fun x _ => SheetP_fiber_finite hfin x) ?_
    simpa using (SheetP_localHomeo X C hgraph :
      IsLocalHomeomorphOn (SheetP X C) Set.univ)
  -- the contraction, as a continuous map `C × unitInterval → C`
  obtain ⟨K', hK'cont, hK'0, hK'1⟩ := hasContraction_subtype (C := C) hc₀ hKcont hK0 hK1 hKmem
  -- the fibre over the contraction centre, enumerated by `Fin k`
  have hfib : ((SheetP X C) ⁻¹' {⟨c₀, hc₀⟩}).Finite := SheetP_fiber_finite hfin ⟨c₀, hc₀⟩
  haveI : Finite ((SheetP X C) ⁻¹' {⟨c₀, hc₀⟩}) := hfib
  haveI : Fintype ((SheetP X C) ⁻¹' {⟨c₀, hc₀⟩}) := Fintype.ofFinite _
  have hcardFib : Fintype.card ((SheetP X C) ⁻¹' {⟨c₀, hc₀⟩}) = (fiber X c₀).ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact SheetP_fiber_ncard (X := X) (C := C) ⟨c₀, hc₀⟩
  let e : Fin (fiber X c₀).ncard ≃ ((SheetP X C) ⁻¹' {⟨c₀, hc₀⟩}) :=
    (finCongr hcardFib).symm.trans (Fintype.equivFin _).symm
  -- sections of the covering map, indexed by the fibre over `c₀`
  obtain ⟨s, hscont, hsp, hsinj, hssurj⟩ := CoveringSections hcov K' hK'cont hK'0 hK'1 _ e
  -- the sheets, as maps `C → ℝ^q` (with a junk value off `C`)
  let G : Fin (fiber X c₀).ncard → (Fin p → ℝ) → (Fin q → ℝ) :=
    fun j x => if hx : x ∈ C then projSnd p q (s j ⟨x, hx⟩).1 else 0
  have hGval : ∀ (j : Fin (fiber X c₀).ncard) (x : Fin p → ℝ) (hx : x ∈ C),
      G j x = projSnd p q (s j ⟨x, hx⟩).1 := fun j x hx => by
    simp only [G, dite_eq_left hx]
  -- the sheets are pointwise distinct
  have hInj : ∀ x ∈ C, Function.Injective fun j : Fin (fiber X c₀).ncard => G j x := by
    intro x hx j j' hjj
    have h1 : projSnd p q (s j ⟨x, hx⟩).1 = projSnd p q (s j' ⟨x, hx⟩).1 := by
      rw [← hGval j x hx, ← hGval j' x hx]
      exact hjj
    exact hsinj ⟨x, hx⟩
      (SheetP_fiber_injOn X C ⟨x, hx⟩ (hsp j ⟨x, hx⟩) (hsp j' ⟨x, hx⟩) h1)
  -- the sheets solve `X`
  have hMem : ∀ (j : Fin (fiber X c₀).ncard) (x : Fin p → ℝ) (hx : x ∈ C),
      Fin.append x (G j x) ∈ X := by
    intro j x hx
    have hfirst : projFirst p q (s j ⟨x, hx⟩).1 = x := congrArg Subtype.val (hsp j ⟨x, hx⟩)
    have h2 : Fin.append x (G j x) = (s j ⟨x, hx⟩).1 := by
      calc Fin.append x (G j x)
          = Fin.append (projFirst p q (s j ⟨x, hx⟩).1) (projSnd p q (s j ⟨x, hx⟩).1) := by
            congr 1
            · exact hfirst.symm
            · exact hGval j x hx
        _ = (s j ⟨x, hx⟩).1 := append_projFirst_projSnd (s j ⟨x, hx⟩).1
    rw [h2]
    exact (s j ⟨x, hx⟩).2.1
  -- the fibre over `x` is exactly the set of the `k` sheet values
  have hRange : ∀ x ∈ C, fiber X x = Set.range (fun j : Fin (fiber X c₀).ncard => G j x) := by
    intro x hx
    ext y
    constructor
    · intro hy
      have hy' : Fin.append x y ∈ X := hy
      have hCy : projFirst p q (Fin.append x y) ∈ C := by
        rw [projFirst_append]; exact hx
      obtain ⟨j, hj⟩ := hssurj ⟨x, hx⟩
        ⟨Fin.append x y, mem_SheetTot.mpr ⟨hy', hCy⟩⟩
        (by
          refine Subtype.ext ?_
          rw [SheetP_val, projFirst_append])
      refine ⟨j, ?_⟩
      show G j x = y
      rw [hGval j x hx]
      exact (congrArg (fun w : SheetT X C => projSnd p q w.1) hj).trans (projSnd_append x y)
    · rintro ⟨j, rfl⟩
      exact hMem j x hx
  refine ⟨(fiber X c₀).ncard, G, ?_, hInj, hMem, ?_, ?_⟩
  · intro j
    have hcont : Continuous fun x : C => projSnd p q (s j x).1 :=
      continuous_pi fun i => (continuous_apply (Fin.natAdd p i)).comp
        (continuous_subtype_val.comp (hscont j))
    rw [continuousOn_iff_continuous_domRestrict]
    exact hcont.congr fun x => (hGval j x.1 x.2).symm
  · intro x hx
    rw [hRange x hx, Set.ncard_range_of_injective (hInj x hx)]
    simp
  · intro z hz hzC
    obtain ⟨j, hj⟩ := hssurj ⟨projFirst p q z, hzC⟩ ⟨z, hz, hzC⟩ rfl
    refine ⟨j, ?_⟩
    rw [hGval j (projFirst p q z) hzC]
    exact congrArg (fun w : SheetT X C => projSnd p q w.1) hj

end Work.WilE7.DimAPI
