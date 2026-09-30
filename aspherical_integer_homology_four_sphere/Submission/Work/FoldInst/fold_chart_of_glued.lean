import Mathlib
import Submission.Work.FoldInst.Basic
import Submission.Work.Fold.FoldChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.FoldInst

open Set

/-- On the subtype `S` of a set, the `Φ`-image of the trace of a set `V ⊆ S` is the `Φ`-image
of `V` itself. -/
private lemma image_subtypeVal_preimage {Y : Type*} {S V : Set Y} (hV : V ⊆ S) (F : Y → E4) :
    (fun p : S => F p.1) '' {p : S | p.1 ∈ V} = F '' V := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, hp, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hV hy⟩, hy, rfl⟩

theorem fold_chart_of_glued {Y : Type*} [TopologicalSpace Y] {c : ℕ} (hc : c ≤ 4)
    (U : Work.Fold.Sign c → Set Y) (Φ : Y → E4)
    (hopen : IsOpen (⋃ r, U r))
    (hcont : ContinuousOn Φ (⋃ r, U r))
    (horth : ∀ r ⦃p⦄, p ∈ U r → Φ p ∈ Work.Fold.orthant r)
    (hinj : Set.InjOn Φ (⋃ r, U r))
    (himage : ∀ r, Φ '' U r = Work.Fold.reflVec r '' (Φ '' U (Work.Fold.oneSign c)))
    (htarget_open : Work.Fold.IsRelOpen (Work.Fold.posOrthant c) (Φ '' U (Work.Fold.oneSign c)))
    (inv : Work.Fold.Sign c → E4 → Y)
    (inv_mem : ∀ r ⦃x⦄, x ∈ Φ '' U r → inv r x ∈ U r)
    (inv_apply : ∀ r ⦃x⦄, x ∈ Φ '' U r → Φ (inv r x) = x)
    (inv_cont : ∀ r, ContinuousOn (inv r) (Φ '' U r)) :
    ∃ Ψ : OpenPartialHomeomorph Y E4, Ψ.source = ⋃ r, U r ∧
      Ψ.target = Work.Fold.foldMap c hc ⁻¹' (Φ '' U (Work.Fold.oneSign c)) ∧
      ∀ p ∈ Ψ.source, Ψ p = Φ p := by
  classical
  set S : Set Y := ⋃ r, U r with hS
  have hUS : ∀ r, U r ⊆ S := fun r => subset_iUnion U r
  have hcontS : Continuous (fun p : S => Φ p.1) := by
    have hcontS' : ContinuousOn Φ S := by rw [hS]; exact hcont
    exact continuousOn_iff_continuous_domRestrict.mp hcontS'
  by_cases hne : S.Nonempty
  · -- the source is nonempty: build the fold gluing datum on the subtype `S`
    obtain ⟨s₀, hs₀⟩ := hne
    -- the local inverses on the subtype
    let inv' : Work.Fold.Sign c → E4 → S := fun r x =>
      if h : x ∈ Φ '' U r then ⟨inv r x, Set.mem_iUnion.mpr ⟨r, inv_mem r h⟩⟩ else ⟨s₀, hs₀⟩
    have hinv'_eq : ∀ (r : Work.Fold.Sign c) ⦃x : E4⦄ (hx : x ∈ Φ '' U r),
        inv' r x = (⟨inv r x, Set.mem_iUnion.mpr ⟨r, inv_mem r hx⟩⟩ : S) :=
      fun r x hx => dite_eq_left hx
    have hinv'_val : ∀ (r : Work.Fold.Sign c) ⦃x : E4⦄ (hx : x ∈ Φ '' U r),
        (inv' r x).1 = inv r x := by
      intro r x hx
      rw [hinv'_eq r hx]
    -- the pieces of the gluing, as subobjects of `S`
    let Cinv : Work.Fold.Sign c → Set S := fun r => {p : S | Φ p.1 ∈ Work.Fold.orthant r}
    let Uinv : Work.Fold.Sign c → Set S := fun r => {p : S | p.1 ∈ U r}
    let ψinv : Work.Fold.Sign c → S → E4 := fun _ p => Φ p.1
    let D : Work.Fold.FoldGlue S c :=
      { C := Cinv
        U := Uinv
        ψ := ψinv
        hU_subset := fun r p hp => horth r hp
        hC_closed := fun r => (Work.Fold.isClosed_orthant r).preimage hcontS
        hψ_cont := fun r => hcontS.continuousOn
        hψ_orth := fun r p hp => hp
        hsource_open := by
          have hUuniv : (⋃ r, Uinv r) = univ := by
            ext p
            refine ⟨fun _ => trivial, fun _ => ?_⟩
            have hp' : p.1 ∈ ⋃ r, U r := by rw [← hS]; exact p.2
            obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hp'
            exact Set.mem_iUnion.mpr ⟨r, hr⟩
          rw [hUuniv]
          exact isOpen_univ
        hagree := fun r s p hp hq => rfl
        hcross := fun r s p q hp hq h =>
          Subtype.ext (hinj (mem_iUnion.mpr ⟨r, hp⟩) (mem_iUnion.mpr ⟨s, hq⟩) h)
        himage := fun r => by
          show (fun p : S => Φ p.1) '' {p : S | p.1 ∈ U r}
            = Work.Fold.reflVec r '' ((fun p : S => Φ p.1) '' {p : S | p.1 ∈ U (Work.Fold.oneSign c)})
          rw [image_subtypeVal_preimage (hUS r) Φ,
            image_subtypeVal_preimage (hUS (Work.Fold.oneSign c)) Φ]
          exact himage r
        htarget_open := by
          show Work.Fold.IsRelOpen (Work.Fold.posOrthant c)
            ((fun p : S => Φ p.1) '' {p : S | p.1 ∈ U (Work.Fold.oneSign c)})
          rw [image_subtypeVal_preimage (hUS (Work.Fold.oneSign c)) Φ]
          exact htarget_open
        inv := inv'
        inv_mem := fun r x hx => by
          obtain ⟨p, hp, hpx⟩ := hx
          have hxim : x ∈ Φ '' U r := ⟨p.1, hp, hpx⟩
          show (inv' r x).1 ∈ U r
          rw [hinv'_val r hxim]
          exact inv_mem r hxim
        inv_apply := fun r x hx => by
          obtain ⟨p, hp, hpx⟩ := hx
          have hxim : x ∈ Φ '' U r := ⟨p.1, hp, hpx⟩
          show Φ (inv' r x).1 = x
          rw [hinv'_val r hxim]
          exact inv_apply r hxim
        inv_cont := fun r => by
          have hT : ψinv r '' Uinv r = Φ '' U r := image_subtypeVal_preimage (hUS r) Φ
          rw [hT]
          have hg : Continuous (fun x : ↥(Φ '' U r) =>
              (⟨inv r x.1, Set.mem_iUnion.mpr ⟨r, inv_mem r x.2⟩⟩ : S)) :=
            Continuous.subtype_mk (inv_cont r).domRestrict
              (fun x => Set.mem_iUnion.mpr ⟨r, inv_mem r x.2⟩)
          rw [continuousOn_iff_continuous_domRestrict]
          refine hg.congr fun x => ?_
          symm
          exact dite_eq_left x.2 }
    have hDS : D.S = Φ '' U (Work.Fold.oneSign c) := by
      show ψinv (Work.Fold.oneSign c) '' Uinv (Work.Fold.oneSign c) = _
      exact image_subtypeVal_preimage (hUS (Work.Fold.oneSign c)) Φ
    have hDtgt : D.target hc = Work.Fold.foldMap c hc ⁻¹' (Φ '' U (Work.Fold.oneSign c)) := by
      rw [Work.Fold.FoldGlue.target, hDS]
    refine ⟨{ toFun := Φ
              invFun := fun x => (D.invFun hc x : Y)
              source := S
              target := Work.Fold.foldMap c hc ⁻¹' (Φ '' U (Work.Fold.oneSign c))
              map_source' := ?_
              map_target' := ?_
              left_inv' := ?_
              right_inv' := ?_
              open_source := by rw [hS]; exact hopen
              open_target := Work.Fold.isOpen_foldMap_preimage hc htarget_open
              continuousOn_toFun := by rw [hS]; exact hcont
              continuousOn_invFun := ?_ }, ?_, ?_, ?_⟩
    · -- `Φ` maps the source into the fold-preimage of the `+`-piece
      intro x hx
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp (hS ▸ hx)
      have hpU : (⟨x, hx⟩ : S) ∈ D.U r := hr
      have hpS : (⟨x, hx⟩ : S) ∈ D.source :=
        Work.Fold.FoldGlue.mem_source_iff D |>.mpr ⟨r, hpU⟩
      have h1 : D.glued ⟨x, hx⟩ ∈ D.target hc := D.glued_mem_target hc hpS
      have h2 : D.glued ⟨x, hx⟩ = Φ x := D.glued_apply hpU
      rw [h2, hDtgt] at h1
      simpa using h1
    · -- the inverse lands in the source
      intro x hx
      have hx' : x ∈ D.target hc := by rw [hDtgt]; exact hx
      have hmem : D.invFun hc x ∈ D.source := D.invFun_mem hc hx'
      have hmem' : D.invFun hc x ∈ ⋃ r, D.U r := hmem
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hmem'
      show (D.invFun hc x : Y) ∈ ⋃ r, U r
      exact Set.mem_iUnion.mpr ⟨r, hr⟩
    · -- the inverse is a left inverse
      intro x hx
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp (hS ▸ hx)
      have hpU : (⟨x, hx⟩ : S) ∈ D.U r := hr
      have hpS : (⟨x, hx⟩ : S) ∈ D.source :=
        Work.Fold.FoldGlue.mem_source_iff D |>.mpr ⟨r, hpU⟩
      have h1 : D.invFun hc (D.glued ⟨x, hx⟩) = ⟨x, hx⟩ := D.invFun_glued hc hpS
      have h2 : D.glued ⟨x, hx⟩ = Φ x := D.glued_apply hpU
      rw [h2] at h1
      exact congrArg Subtype.val h1
    · -- the inverse is a right inverse
      intro x hx
      have hx' : x ∈ D.target hc := by rw [hDtgt]; exact hx
      have hmem : D.invFun hc x ∈ D.source := D.invFun_mem hc hx'
      have hmem' : D.invFun hc x ∈ ⋃ r, D.U r := hmem
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hmem'
      have h2 : D.glued (D.invFun hc x) = Φ ((D.invFun hc x : S) : Y) :=
        D.glued_apply hr
      have h1 : D.glued (D.invFun hc x) = x := D.glued_invFun hc hx'
      rw [h2] at h1
      exact h1
    · -- the inverse is continuous on the target
      have h1 : ContinuousOn (fun x => (D.invFun hc x : Y)) (D.target hc) :=
        continuous_subtype_val.comp_continuousOn (Work.Fold.invFun_continuousOn D hc)
      rwa [hDtgt] at h1
    · exact hS
    · rfl
    · intro p hp
      rfl
  · -- the source is empty: the chart is the empty one
    have hSe : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hUe : ∀ r, U r = ∅ := fun r =>
      Subset.antisymm (fun x hx => absurd ⟨x, Set.mem_iUnion.mpr ⟨r, hx⟩⟩ hne) (Set.empty_subset _)
    have himgEmpty : Φ '' U (Work.Fold.oneSign c) = ∅ := by
      rw [hUe (Work.Fold.oneSign c)]
      exact image_empty Φ
    refine ⟨{ toFun := Φ
              invFun := fun _ => inv (Work.Fold.oneSign c) 0
              source := ∅
              target := ∅
              map_source' := by simp
              map_target' := by simp
              left_inv' := by simp
              right_inv' := by simp
              open_source := isOpen_empty
              open_target := isOpen_empty
              continuousOn_toFun := continuousOn_empty Φ
              continuousOn_invFun := continuousOn_empty _ }, ?_, ?_, ?_⟩
    · show (∅ : Set Y) = ⋃ r, U r
      exact hSe.symm.trans hS
    · show (∅ : Set E4) = Work.Fold.foldMap c hc ⁻¹' (Φ '' U (Work.Fold.oneSign c))
      rw [himgEmpty, preimage_empty]
    · intro p hp
      exact absurd hp (by simp)

end Work.FoldInst
