/-
  WilE7 (`Work.WilE7.sheetAssembly`): the sheet lemma of the BV sharp cell decomposition.

  Over a cell `C` of the base, the points of a `Good` stratum `S` with `S.j = q` whose base
  projection lies in `C` are covered by the graphs of at most `Q` continuous maps `C → ℝ^q`,
  which are pointwise distinct.

  The proof: the sheet domain `SheetSpace S C` is the total space of a covering map over `C`
  (`Work.WilE7.sheetCoveringMap`, from the local patch lemma on the one hand and the
  clustering of the fibres at the frontier on the other), while `C` is contractible
  (`Work.WilE7.isCellContractible`).  Lifting the contraction homotopy through the covering map
  (`Work.WilE7.sheetSections`) produces, from the `m` points of one fibre, `m` continuous
  sections which are pointwise a bijection onto each fibre; `m` is bounded by `Q` because the
  fibres of the sheet space are the fibres of the stratum.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.stratGraph
import Submission.Work.WilE7.sheetDomain_open
import Submission.Work.WilE7.sheetDomain_closedIn
import Submission.Work.WilE7.isCell_localPreconnected
import Submission.Work.WilE7.cells
import Submission.Work.WilE7.sheetCount_le_fibre
import Submission.Work.WilE7.SheetDefs
import Submission.Work.WilE7.fiberCluster
import Submission.Work.WilE7.isCellContractible
import Submission.Work.WilE7.sheetCoveringMap
import Submission.Work.WilE7.sheetSections

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-- The number of sheets over `x` is the cardinality of the stratum's fibre over `x`. -/
theorem ncard_fibre_eq {p q : ℕ} {S : Stratum p q} {C : Set (Fin p → ℝ)} (x : C) :
    Nat.card (SheetProj (S := S) (C := C) ⁻¹' {x}) = (fiber S.X.set x.1).ncard := by
  have hinj : Set.InjOn (projSnd p q) (SheetSpace S C ∩ {w | projFirst p q w = x.1}) := by
    intro a ha b hb hab
    have ha2 : projFirst p q a = x.1 := ha.2
    have hb2 : projFirst p q b = x.1 := hb.2
    rw [← append_proj a, ← append_proj b, ha2, hb2, hab]
  rw [Nat.card_coe_set_eq,
    ← Set.ncard_image_of_injective (f := Subtype.val) (SheetProj (S := S) (C := C) ⁻¹' {x})
      Subtype.val_injective,
    sheetFiber_val_image,
    ← Set.InjOn.ncard_image (f := projSnd p q)
      (s := SheetSpace S C ∩ {w | projFirst p q w = x.1}) hinj,
    sheetFiber_image]

theorem sheetAssembly
    {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good) (hj : S.j = q)
    (C : Set (Fin p → ℝ)) (hC : WilkiesDesign.IsCell p C)
    (Forbidden : Set (Fin (p + q) → ℝ))
    (hForb : ∀ w ∈ Forbidden, WilkiesDesign.E.projFirst p q w ∉ C)
    (hFr : closure S.X.set \ S.X.set ⊆ Forbidden)
    (hloc : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p q z ∈ C →
      ∀ᶠ z' in nhds z,
        (∀ a : Fin S.j, WilkiesDesign.E.eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set)
    (hCsub : C ⊆ Set.image (WilkiesDesign.E.projFirst p q) S.X.set)
    (hfin : ∀ x : Fin p → ℝ, (WilkiesDesign.E.fiber S.X.set x).Finite)
    (Q : ℕ) (hQ : ∀ x : Fin p → ℝ, (WilkiesDesign.E.fiber S.X.set x).ncard ≤ Q) :
    ∃ (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ)),
      k ≤ Q ∧
      (∀ j, ContinuousOn (s j) C) ∧
      (∀ x ∈ C, Function.Injective fun j : Fin k => s j x) ∧
      (∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set) ∧
      (∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p q z ∈ C →
        ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p q z) = WilkiesDesign.E.projSnd p q z) := by
  classical
  by_cases hCe : C = ∅
  · subst hCe
    refine ⟨0, fun j => j.elim0, Nat.zero_le Q, ?_, ?_, ?_, ?_⟩
    · intro j; exact j.elim0
    · intro x hx; exact absurd hx (Set.notMem_empty x)
    · intro j x hx; exact absurd hx (Set.notMem_empty x)
    · intro z hz hzC; exact absurd hzC (Set.notMem_empty (projFirst p q z))
  · obtain ⟨c₀, K, hc₀, hKcont, hK0, hK1, hKmem⟩ := isCellContractible (n := p) (A := C) hC
    have hcov : IsCoveringMap (SheetProj (S := S) (C := C)) :=
      sheetCoveringMap S hGood hj C Forbidden hForb hFr hloc hCsub hfin
    haveI hfinfib : Finite (SheetProj (S := S) (C := C) ⁻¹' {⟨c₀, hc₀⟩}) :=
      sheetFiber_finite (S := S) (C := C) hfin ⟨c₀, hc₀⟩
    haveI : Fintype (SheetProj (S := S) (C := C) ⁻¹' {⟨c₀, hc₀⟩}) := Fintype.ofFinite _
    let m : ℕ := Fintype.card (SheetProj (S := S) (C := C) ⁻¹' {⟨c₀, hc₀⟩})
    have hmcard : m = (fiber S.X.set c₀).ncard := by
      show Fintype.card (SheetProj (S := S) (C := C) ⁻¹' {⟨c₀, hc₀⟩}) = (fiber S.X.set c₀).ncard
      rw [← Nat.card_eq_fintype_card]
      exact ncard_fibre_eq (S := S) (C := C) ⟨c₀, hc₀⟩
    let e : Fin m ≃ (SheetProj (S := S) (C := C) ⁻¹' {⟨c₀, hc₀⟩}) :=
      (Fintype.equivFin (SheetProj (S := S) (C := C) ⁻¹' {⟨c₀, hc₀⟩})).symm
    obtain ⟨s, hcont, hproj, hinj, hsurj⟩ :=
      sheetSections S C hcov hc₀ K hKcont hK0 hK1 hKmem m e
    let G : Fin m → (Fin p → ℝ) → (Fin q → ℝ) :=
      fun j x => if hx : x ∈ C then projSnd p q (s j ⟨x, hx⟩).1 else 0
    have hG : ∀ (j : Fin m) (x : Fin p → ℝ) (hx : x ∈ C),
        G j x = projSnd p q (s j ⟨x, hx⟩).1 := fun j x hx => by simp only [G, dif_pos hx]
    have hpi : ∀ (j : Fin m) (x : Fin p → ℝ) (hx : x ∈ C),
        projFirst p q (s j ⟨x, hx⟩).1 = x := by
      intro j x hx
      have h := congrArg Subtype.val (hproj j ⟨x, hx⟩)
      simpa only [SheetProj_val] using h
    refine ⟨m, G, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmcard]; exact hQ c₀
    · intro j
      have hg : Continuous fun x : C => projSnd p q (s j x).1 :=
        continuous_pi fun i =>
          (continuous_apply (Fin.natAdd p i)).comp (continuous_subtype_val.comp (hcont j))
      rw [continuousOn_iff_continuous_domRestrict]
      refine hg.congr ?_
      intro x
      simp only [Set.restrict_apply, G, dif_pos x.2]
    · intro x hx
      have hfun : Function.Injective fun j : Fin m => s j ⟨x, hx⟩ := hinj ⟨x, hx⟩
      intro j j' hjj
      refine hfun (Subtype.ext ?_)
      have hjj' : G j x = G j' x := hjj
      have h1 : projSnd p q (s j ⟨x, hx⟩).1 = projSnd p q (s j' ⟨x, hx⟩).1 := by
        rw [hG j x hx, hG j' x hx] at hjj'
        exact hjj'
      calc (s j ⟨x, hx⟩).1
          = Fin.append (projFirst p q (s j ⟨x, hx⟩).1) (projSnd p q (s j ⟨x, hx⟩).1) :=
            (sheetE_append_proj _).symm
        _ = Fin.append x (projSnd p q (s j' ⟨x, hx⟩).1) := by rw [hpi j x hx, h1]
        _ = Fin.append (projFirst p q (s j' ⟨x, hx⟩).1) (projSnd p q (s j' ⟨x, hx⟩).1) := by
              rw [hpi j' x hx]
        _ = (s j' ⟨x, hx⟩).1 := sheetE_append_proj _
    · intro j x hx
      have h4 : Fin.append x (projSnd p q (s j ⟨x, hx⟩).1)
          = Fin.append (projFirst p q (s j ⟨x, hx⟩).1) (projSnd p q (s j ⟨x, hx⟩).1) := by
        rw [hpi j x hx]
      have h2 : Fin.append x (G j x) = (s j ⟨x, hx⟩).1 := by
        rw [hG j x hx, h4, sheetE_append_proj]
      rw [h2]
      exact (s j ⟨x, hx⟩).2.1
    · intro z hz hzC
      have hw : SheetProj (S := S) (C := C) ⟨z, hz, hzC⟩ = ⟨projFirst p q z, hzC⟩ := rfl
      obtain ⟨j, hj⟩ := hsurj ⟨projFirst p q z, hzC⟩ ⟨z, hz, hzC⟩ hw
      refine ⟨j, ?_⟩
      rw [hG j (projFirst p q z) hzC, hj]

end Work.WilE7
