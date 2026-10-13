import Mathlib
import Submission.Work.WilE7.DimAPI.SheetLocalDefs

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.DimAPI
open WilkiesDesign WilkiesDesign.E

theorem SheetP_localHomeo {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) (C : Set (Fin p → ℝ))
    (hgraph : ∀ z ∈ X, WilkiesDesign.E.projFirst p q z ∈ C →
      ∃ V ∈ nhds z, ∃ U ∈ nhds (WilkiesDesign.E.projFirst p q z), ∃ g : (Fin p → ℝ) → (Fin q → ℝ),
        ContinuousOn g (C ∩ U) ∧ (∀ x ∈ C ∩ U, Fin.append x (g x) ∈ X ∩ V) ∧
        ∀ w ∈ X ∩ V, WilkiesDesign.E.projFirst p q w ∈ C → WilkiesDesign.E.projFirst p q w ∈ U ∧
          g (WilkiesDesign.E.projFirst p q w) = WilkiesDesign.E.projSnd p q w) :
    IsLocalHomeomorphOn (Work.WilE7.DimAPI.SheetP X C) Set.univ := by
  classical
  refine IsLocalHomeomorphOn.mk _ _ fun w₀ _ => ?_
  obtain ⟨V, hV, U, hU, g, hgcont, hggraph, hguniq⟩ := hgraph w₀.1 w₀.2.1 w₀.2.2
  have hz₀Vi : w₀.1 ∈ interior V := mem_interior_iff_mem_nhds.mpr hV
  have hx₀Ui : projFirst p q w₀.1 ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  have hViV : interior V ⊆ V := interior_subset
  have hUiU : interior U ⊆ U := interior_subset
  -- the local graph map over the base
  set Φ : (Fin p → ℝ) → (Fin (p + q) → ℝ) := fun x => Fin.append x (g x) with hΦdef
  have hgcont₀ : ContinuousOn g (C ∩ interior U) :=
    hgcont.mono fun x hx => ⟨hx.1, hUiU hx.2⟩
  have hΦcont₀ : ContinuousOn Φ (C ∩ interior U) := by
    rw [hΦdef]; exact continuousOn_append hgcont₀
  have hΦ₀ : Φ (projFirst p q w₀.1) = w₀.1 := by
    have h := (hguniq w₀.1 ⟨w₀.2.1, hViV hz₀Vi⟩ w₀.2.2).2
    show Fin.append (projFirst p q w₀.1) (g (projFirst p q w₀.1)) = w₀.1
    rw [h, append_projFirst_projSnd]
  -- shrink the base so that the graph over it lies in the *interior* of `V`
  have hev : ∀ᶠ x in 𝓝[C ∩ interior U] (projFirst p q w₀.1), Φ x ∈ interior V :=
    (hΦcont₀.continuousWithinAt ⟨w₀.2.2, hx₀Ui⟩).eventually
      (by rw [hΦ₀]; exact isOpen_interior.mem_nhds hz₀Vi)
  obtain ⟨O, hOopen, hx₀O, hOsub⟩ := mem_nhdsWithin.mp hev
  set U₁ : Set (Fin p → ℝ) := O ∩ interior U with hU₁def
  have hU₁open : IsOpen U₁ := by rw [hU₁def]; exact hOopen.inter isOpen_interior
  have hx₀U₁ : projFirst p q w₀.1 ∈ U₁ := by rw [hU₁def]; exact ⟨hx₀O, hx₀Ui⟩
  have hU₁U : U₁ ⊆ U := by
    intro x hx; rw [hU₁def] at hx; exact hUiU hx.2
  have hΦU₁ : ∀ x ∈ C ∩ U₁, Φ x ∈ interior V := by
    intro x hx
    rw [hU₁def] at hx
    exact hOsub ⟨hx.2.1, hx.1, hx.2.2⟩
  have hΦcont : ContinuousOn Φ (C ∩ U₁) :=
    hΦcont₀.mono fun x hx => by rw [hU₁def] at hx; exact ⟨hx.1, hx.2.2⟩
  -- the graph point is in the total space
  have hΦTot : ∀ x ∈ C ∩ U₁, Φ x ∈ SheetTot X C := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact (hggraph x ⟨hx.1, hU₁U hx.2⟩).1
    · show projFirst p q (Fin.append x (g x)) ∈ C
      rw [projFirst_append]; exact hx.1
  -- source and target of the local homeomorphism
  set tgt : Set C := {x : C | x.1 ∈ U₁} with htgtdef
  set src : Set (SheetT X C) :=
    {w : SheetT X C | projFirst p q w.1 ∈ U₁ ∧ w.1 ∈ interior V} with hsrcdef
  have htgt_open : IsOpen tgt := by
    rw [htgtdef]; exact hU₁open.preimage continuous_subtype_val
  have hsrc_open : IsOpen src := by
    rw [hsrcdef]
    exact (htgt_open.preimage (SheetP_continuous X C)).inter
      (isOpen_interior.preimage continuous_subtype_val)
  have hw₀src : w₀ ∈ src := ⟨hx₀U₁, hz₀Vi⟩
  -- the partial inverse: the graph of `g` over the target
  set invF : C → SheetT X C := fun x =>
    if h : x ∈ tgt then (⟨Φ x.1, hΦTot x.1 ⟨x.2, h⟩⟩ : SheetT X C) else w₀ with hinvFdef
  have hinvF_of_mem : ∀ x (hx : x ∈ tgt), invF x = ⟨Φ x.1, hΦTot x.1 ⟨x.2, hx⟩⟩ := by
    intro x hx
    rw [hinvFdef]
    exact dite_eq_left hx
  -- the projection maps the source onto the target
  have hms : ∀ x ∈ src, SheetP X C x ∈ tgt := by
    intro x hx
    show (SheetP X C x).1 ∈ U₁
    rw [SheetP_val]
    exact hx.1
  -- the inverse lands in the source
  have hmt : ∀ x ∈ tgt, invF x ∈ src := by
    intro x hx
    rw [hinvF_of_mem x hx]
    refine ⟨?_, ?_⟩
    · show projFirst p q (Fin.append x.1 (g x.1)) ∈ U₁
      rw [projFirst_append]; exact hx
    · exact hΦU₁ x.1 ⟨x.2, hx⟩
  -- the projection is injective on the source (uniqueness of the graph)
  have hleft : ∀ x ∈ src, invF (SheetP X C x) = x := by
    intro x hx
    have hSx : SheetP X C x ∈ tgt := hms x hx
    rw [hinvF_of_mem (SheetP X C x) hSx]
    have h1 : g (projFirst p q x.1) = projSnd p q x.1 :=
      (hguniq x.1 ⟨x.2.1, hViV hx.2⟩ x.2.2).2
    refine Subtype.ext ?_
    show Fin.append (projFirst p q x.1) (g (projFirst p q x.1)) = x.1
    rw [h1, append_projFirst_projSnd]
  have hright : ∀ x ∈ tgt, SheetP X C (invF x) = x := by
    intro x hx
    rw [hinvF_of_mem x hx]
    refine Subtype.ext ?_
    show projFirst p q (Fin.append x.1 (g x.1)) = x.1
    rw [projFirst_append]
  have hcont_inv : ContinuousOn invF tgt := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : tgt.domRestrict invF =
        (fun x : tgt => (⟨Φ x.1.1, hΦTot x.1.1 ⟨x.1.2, x.2⟩⟩ : SheetT X C)) := by
      funext x
      rw [Set.domRestrict_apply, hinvFdef]
      exact dite_eq_left x.2
    rw [heq]
    refine Continuous.subtype_mk ?_ ?_
    · exact hΦcont.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
        (fun x => ⟨x.1.2, x.2⟩)
  refine ⟨{ toFun := SheetP X C
            invFun := invF
            source := src
            target := tgt
            map_source' := hms
            map_target' := hmt
            left_inv' := hleft
            right_inv' := hright
            continuousOn_toFun := (SheetP_continuous X C).continuousOn
            continuousOn_invFun := hcont_inv
            open_source := hsrc_open
            open_target := htgt_open }, hw₀src, fun y _ => rfl⟩

end Work.WilE7.DimAPI
