import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.rewrite_zero_index
import Submission.Work.OROneRel.rewrite_isReduced
import Submission.Work.OROneRel.rewrite_isCyclicallyReduced_of_expsum_zero
import Submission.Work.OROneRel.magnusSubgroupOf_equiv_freeGroup
import Submission.Work.OROneRel.range_presentedGroupMap
import Submission.Work.OROneRel.presentedGroupMap_injective_mono
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.mk_eq_expand_rewriteAux
import Submission.Work.OROneRel.zeta_mk_eq_expand
import Submission.Work.OROneRel.rho_magRew
import Submission.Work.OROneRel.rewrite_mem_letter
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.OROneRel.sigma_mk
import Submission.Work.OROneRel.finite_relatorLetters
import Submission.Work.OROneRel.presentedGroup_iso_coprod_of_supported
import Submission.Work.OROneRel.FSRestrictSetup

universe u v

namespace Work.OROneRel

variable {α : Type u}

/-- The decorated alphabet of the Magnus rewriting with respect to `t`: this is the generating type
of the base group of the HNN step. -/
abbrev HNNDec (t : α) : Type u := {a : α // a ≠ t} × ℤ

/-- The shift `(s,i) ↦ (s,i+1)` of the decoration index. -/
noncomputable def hnnShift (t : α) : HNNDec t → HNNDec t := fun p => (p.1, p.2 + 1)

/-- The set of decorations that the stable letter is allowed to shift: every decoration whose letter
is not `x`, together with the `x`-decorations of index `≤ b - 1`.  (The `x`-decorations occurring in
the rewritten relator all have index `≤ b`.) -/
noncomputable def hnnS (t x : α) (htx : x ≠ t) (a b : ℤ) : Set (HNNDec t) :=
  {p | p.1 ≠ (⟨x, htx⟩ : {a : α // a ≠ t}) ∨ (a ≤ p.2 ∧ p.2 ≤ b - 1)}

/-- The image of `hnnS` under the shift `(s,i) ↦ (s,i+1)`. -/
noncomputable def hnnS1 (t x : α) (htx : x ≠ t) (a b : ℤ) : Set (HNNDec t) :=
  {p | p.1 ≠ (⟨x, htx⟩ : {a : α // a ≠ t}) ∨ (a + 1 ≤ p.2 ∧ p.2 ≤ b)}

theorem hnnS1_iff (t x : α) (htx : x ≠ t) (a b : ℤ) (p : HNNDec t) :
    p ∈ hnnS1 t x htx a b ↔ (p.1, p.2 - 1) ∈ hnnS t x htx a b := by
  simp only [hnnS1, hnnS, Set.mem_setOf_eq]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩

/-- The shift of the decorations, as an equivalence between the two generating sets `hnnS` and
`hnnS1` of the associated Magnus subgroups. -/
noncomputable def hnnShiftEquiv (t x : α) (htx : x ≠ t) (a b : ℤ) :
    hnnS t x htx a b ≃ hnnS1 t x htx a b where
  toFun p := ⟨hnnShift t p.1, by
    rw [hnnS1_iff]
    have h : ((hnnShift t p.1).1, (hnnShift t p.1).2 - 1) = p.1 := by
      refine Prod.ext rfl ?_
      simp [hnnShift]
    rw [h]
    exact p.2⟩
  invFun p := ⟨(p.1.1, p.1.2 - 1), (hnnS1_iff t x htx a b p.1).mp p.2⟩
  left_inv p := by
    refine Subtype.ext ?_
    refine Prod.ext rfl ?_
    simp [hnnShift]
  right_inv p := by
    refine Subtype.ext ?_
    refine Prod.ext rfl ?_
    simp [hnnShift]


/-! ### Transport of the Freiheitssatz across a change of generating type

The induction hypothesis `FreiheitssatzBelow N` that the Freiheitssatz argument provides is
universe-polymorphic, while the HNN step needs the Freiheitssatz at the rewritten relator
`magRewRel t r` over the decorated alphabet `(α \ {t}) × ℤ`, which lives in the *same* universe as
`α`.  The two lemmas `isReduced_map_of_injective`/`relatorNorm_map_of_injective` below (the
Magnus rewriting of a reduced word stays reduced, and the norm is preserved, under an injective
relabelling of the generators) are the quantitative input; the assembly
`freiheitssatzAt_magRewRel` reduces the relator to its (finite) support in the smaller universe. -/

/-- An injective relabelling of the generators of a free group does not create cancellations: the
image of a reduced word is reduced. -/
theorem isReduced_map_of_injective {γ δ : Type*} (f : γ → δ) (hf : Function.Injective f)
    {L : List (γ × Bool)} (hL : FreeGroup.IsReduced L) :
    FreeGroup.IsReduced (L.map fun p => (f p.1, p.2)) := by
  induction L with
  | nil => exact FreeGroup.IsReduced.nil
  | cons a L ih =>
    cases L with
    | nil => exact FreeGroup.IsReduced.singleton
    | cons b L' =>
      rw [List.map_cons, List.map_cons]
      rw [FreeGroup.isReduced_cons_cons] at hL ⊢
      exact ⟨fun h => hL.1 (hf h), ih hL.2⟩

/-- An injective relabelling of the generators of a free group preserves the norm. -/
theorem relatorNorm_map_of_injective {γ δ : Type*} {f : γ → δ} (hf : Function.Injective f)
    (s : FreeGroup γ) : relatorNorm (FreeGroup.map f s) = relatorNorm s := by
  classical
  have h1 : FreeGroup.IsReduced (FreeGroup.toWord s) :=
    FreeGroup.isReduced_iff_reduce_eq.mpr (FreeGroup.reduce_toWord s)
  have h2 : FreeGroup.IsReduced ((FreeGroup.toWord s).map fun p => (f p.1, p.2)) :=
    isReduced_map_of_injective f hf h1
  have h3 : (FreeGroup.map f s).toWord = (FreeGroup.toWord s).map (fun p => (f p.1, p.2)) := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := s)]
    rw [FreeGroup.map.mk, FreeGroup.toWord_mk, h2.reduce_eq]
  have h4 : s.toWord = FreeGroup.toWord s := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := s)]
    rw [FreeGroup.toWord_mk, h1.reduce_eq]
  rw [relatorNorm, relatorNorm, FreeGroup.norm, FreeGroup.norm, h3, h4, List.length_map]/-! ### The extremal `x`-decorations and the assembly of the statement -/

/-- The reduced word of an element of a free group does not depend on which `DecidableEq` instance on
the generators is used. -/
theorem hnntoWord_inst_irrel {α : Type u} (i1 i2 : DecidableEq α) :
    (@FreeGroup.toWord α i1 : FreeGroup α → List (α × Bool)) = @FreeGroup.toWord α i2 := by
  rw [Subsingleton.elim i1 i2]

/-- **The extremal `x`-decorations of the Magnus rewriting.**  If the reduced word of `r` begins
with the letter `x ≠ t`, then the set of integers `k` with `(⟨x,htx⟩,k) ∈ relatorLetters
(magRewRel t r)` is finite and nonempty (it contains `0` by `rewrite_zero_index`), so it has a least
element `i` and a greatest element `j`, and `i ≤ 0 ≤ j`. -/
theorem hnn_decoration_bounds {α : Type u} [DecidableEq α] (r : FreeGroup α) (t x : α)
    (htx : x ≠ t)
    (hhead : r.toWord.head? = some (x, true) ∨ r.toWord.head? = some (x, false)) :
    ∃ i j : ℤ,
      (⟨x, htx⟩, i) ∈ relatorLetters (magRewRel t r) ∧
      (⟨x, htx⟩, j) ∈ relatorLetters (magRewRel t r) ∧
      (∀ k : ℤ, (⟨x, htx⟩, k) ∈ relatorLetters (magRewRel t r) → i ≤ k ∧ k ≤ j) ∧
      i ≤ 0 ∧ 0 ≤ j := by
  classical
  letI : DecidableEq α := fun a b => Classical.propDecidable (a = b)
  letI : DecidableEq ({a : α // a ≠ t} × ℤ) := fun a b => Classical.propDecidable (a = b)
  have hhead' : (@FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b)) r).head? =
        some (x, true) ∨
      (@FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b)) r).head? =
        some (x, false) := by
    have h := hhead
    rw [hnntoWord_inst_irrel] at h
    exact h
  have hredr : FreeGroup.IsReduced
      (@FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b)) r) :=
    FreeGroup.isReduced_toWord
  have hredw : FreeGroup.IsReduced
      (rewrite t (@FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b)) r)) :=
    rewrite_isReduced t hredr
  have htoWord : (magRewRel t r).toWord =
      rewrite t (@FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b)) r) := by
    rw [magRewRel, FreeGroup.toWord_mk, hredw.reduce_eq]
  have hmem : ∀ p : {a : α // a ≠ t} × ℤ,
      p ∈ relatorLetters (magRewRel t r) ↔ ∃ c : Bool, (p, c) ∈
        rewrite t (@FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b)) r) := by
    intro p
    show (∃ c : Bool, (p, c) ∈ (magRewRel t r).toWord) ↔ _
    rw [htoWord]
  have h0 : (⟨x, htx⟩, (0 : ℤ)) ∈ relatorLetters (magRewRel t r) := by
    rcases hhead' with h | h
    · obtain ⟨p, hp1, hp2, hpmem⟩ := rewrite_zero_index t x htx true h
      refine (hmem ((⟨x, htx⟩, (0 : ℤ)) : {a : α // a ≠ t} × ℤ)).mpr ⟨p.2, ?_⟩
      have hpeq : p = ((⟨x, htx⟩, (0 : ℤ)), p.2) := by
        refine Prod.ext ?_ rfl
        exact Prod.ext hp1 hp2
      rwa [hpeq] at hpmem
    · obtain ⟨p, hp1, hp2, hpmem⟩ := rewrite_zero_index t x htx false h
      refine (hmem ((⟨x, htx⟩, (0 : ℤ)) : {a : α // a ≠ t} × ℤ)).mpr ⟨p.2, ?_⟩
      have hpeq : p = ((⟨x, htx⟩, (0 : ℤ)), p.2) := by
        refine Prod.ext ?_ rfl
        exact Prod.ext hp1 hp2
      rwa [hpeq] at hpmem
  have hfin : ({k : ℤ | (⟨x, htx⟩, k) ∈ relatorLetters (magRewRel t r)}).Finite := by
    apply Set.Finite.subset ((finite_relatorLetters (magRewRel t r)).image Prod.snd)
    intro k hk
    exact ⟨(⟨x, htx⟩, k), hk, rfl⟩
  have hs0 : (0 : ℤ) ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]; exact h0
  have hne : hfin.toFinset.Nonempty := ⟨0, hs0⟩
  refine ⟨hfin.toFinset.min' hne, hfin.toFinset.max' hne, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Set.Finite.mem_toFinset hfin).mp (Finset.min'_mem _ hne)
  · exact (Set.Finite.mem_toFinset hfin).mp (Finset.max'_mem _ hne)
  · intro k hk
    exact ⟨Finset.min'_le _ _ ((Set.Finite.mem_toFinset hfin).mpr hk),
      Finset.le_max' _ _ ((Set.Finite.mem_toFinset hfin).mpr hk)⟩
  · exact Finset.min'_le _ _ hs0
  · exact Finset.le_max' _ _ hs0

/-- **The Freiheitssatz at the Magnus rewriting, across universes.**  If the Freiheitssatz is known
for every relator of norm `< relatorNorm (magRewRel t r) + 1` over every generating type in an
*arbitrary* universe `v`, then it holds at `magRewRel t r` over `(α \ {t}) × ℤ`.  The relator is
supported on finitely many decorations, so one first transports it to a copy of its support in
`Type v`, applies the hypothesis there, and transfers back. -/
theorem hnn_freiheitssatzAt_magRewRel {α : Type u} (r : FreeGroup α) (t : α)
    (IH : ∀ (γ : Type v) (s : FreeGroup γ),
      relatorNorm s < relatorNorm (magRewRel t r) + 1 → FreiheitssatzAt s)
    (fsEquiv : ∀ {γ : Type u} {δ : Type v} (e : γ ≃ δ) (s : FreeGroup γ),
      FreiheitssatzAt s ↔ FreiheitssatzAt (FreeGroup.map e s))
    (fsRestrict : ∀ {γ : Type u} (s : FreeGroup γ) (Z : Set γ) (s' : FreeGroup Z),
      FreeGroup.map (Subtype.val : Z → γ) s' = s → FreiheitssatzAt s' → FreiheitssatzAt s) :
    FreiheitssatzAt (magRewRel t r) := by
  classical
  letI : DecidableEq (HNNDec t) := Classical.decEq _
  have hfin : (relatorLetters (magRewRel t r)).Finite := finite_relatorLetters _
  obtain ⟨r'', hr''⟩ := exists_map_subtype_val_eq_of_supportedOn (magRewRel t r)
    (relatorLetters (magRewRel t r)) (fun a ha => ha)
  haveI : Fintype ↥(relatorLetters (magRewRel t r)) := hfin.fintype
  let e : ↥(relatorLetters (magRewRel t r)) ≃
      ULift.{v} (Fin (Fintype.card ↥(relatorLetters (magRewRel t r)))) :=
    (Fintype.equivFin _).trans Equiv.ulift.symm
  have hn1 : relatorNorm (FreeGroup.map (e : ↥(relatorLetters (magRewRel t r)) →
      ULift.{v} (Fin (Fintype.card ↥(relatorLetters (magRewRel t r))))) r'') =
      relatorNorm r'' := relatorNorm_map_of_injective e.injective r''
  have hn2 : relatorNorm r'' = relatorNorm (magRewRel t r) := by
    have h := (relatorNorm_map_of_injective Subtype.coe_injective r'').symm
    rw [hr''] at h
    exact h
  have hIH : FreiheitssatzAt (FreeGroup.map (e : ↥(relatorLetters (magRewRel t r)) →
      ULift.{v} (Fin (Fintype.card ↥(relatorLetters (magRewRel t r))))) r'') :=
    IH (ULift.{v} (Fin (Fintype.card ↥(relatorLetters (magRewRel t r)))))
      (FreeGroup.map (e : ↥(relatorLetters (magRewRel t r)) →
        ULift.{v} (Fin (Fintype.card ↥(relatorLetters (magRewRel t r))))) r'')
      (by rw [hn1, hn2]; exact Nat.lt_succ_self _)
  exact fsRestrict (magRewRel t r) (relatorLetters (magRewRel t r)) r'' hr''
    ((fsEquiv e r'').mpr hIH)



/-! ### Transport of the Freiheitssatz along an equivalence of generating types -/

/-- An injective relabelling of the generators of a free group creates no cancellations, so the
image of a reduced word is reduced and reducedness can be detected after the relabelling. -/
theorem isReduced_of_isReduced_map {γ δ : Type*} (f : γ → δ) (hf : Function.Injective f)
    {L : List (γ × Bool)} (h : FreeGroup.IsReduced (L.map fun p => (f p.1, p.2))) :
    FreeGroup.IsReduced L := by
  induction L with
  | nil => exact FreeGroup.IsReduced.nil
  | cons a L ih =>
    cases L with
    | nil => exact FreeGroup.IsReduced.singleton
    | cons b L' =>
      rw [List.map_cons, List.map_cons] at h
      rw [FreeGroup.isReduced_cons_cons] at h
      rw [FreeGroup.isReduced_cons_cons]
      exact ⟨fun hab => h.1 (by rw [hab]), ih h.2⟩

/-- The reduced word of the image of `s` under an injective relabelling of the generators. -/
theorem toWord_map_of_injective {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    (f : γ → δ) (hf : Function.Injective f) (s : FreeGroup γ) :
    (FreeGroup.map f s).toWord = (FreeGroup.toWord s).map (fun p => (f p.1, p.2)) := by
  classical
  have h1 : FreeGroup.IsReduced (FreeGroup.toWord s) :=
    FreeGroup.isReduced_iff_reduce_eq.mpr (FreeGroup.reduce_toWord s)
  have h2 : FreeGroup.IsReduced ((FreeGroup.toWord s).map fun p => (f p.1, p.2)) :=
    isReduced_map_of_injective f hf h1
  conv_lhs => rw [← FreeGroup.mk_toWord (x := s)]
  rw [FreeGroup.map.mk, FreeGroup.toWord_mk, h2.reduce_eq]

/-- Cyclic reducedness is detected after an injective relabelling of the generators. -/
theorem isCyclicallyReduced_of_isCyclicallyReduced_map {γ δ : Type*} (f : γ → δ)
    (hf : Function.Injective f) {L : List (γ × Bool)}
    (h : FreeGroup.IsCyclicallyReduced (L.map fun p => (f p.1, p.2))) :
    FreeGroup.IsCyclicallyReduced L := by
  rw [isCyclicallyReduced_iff_isReduced_append_self] at h ⊢
  rw [← List.map_append] at h
  exact isReduced_of_isReduced_map f hf h

/-- Relabelling generators along an equivalence and back is the identity on the free group. -/
theorem map_map_self {γ δ : Type*} (e : γ ≃ δ) (x : FreeGroup γ) :
    FreeGroup.map (⇑e.symm) (FreeGroup.map (⇑e) x) = x := by
  have key : ∀ y : FreeGroup γ, FreeGroup.map (⇑e.symm) (FreeGroup.map (⇑e) y) = y := by
    intro y
    induction y using FreeGroup.induction_on with
    | one => rw [map_one, map_one]
    | of a => rw [FreeGroup.map.of, FreeGroup.map.of, Equiv.symm_apply_apply]
    | inv_of a ih => rw [map_inv, map_inv, ih]
    | mul a b iha ihb => rw [map_mul, map_mul, iha, ihb]
  exact key x

/-- **The Freiheitssatz transports along an equivalence of generating types.** -/
theorem freiheitssatzAt_map_of_equiv {γ : Type u} {δ : Type v} (e : γ ≃ δ) (s : FreeGroup γ)
    (h : FreiheitssatzAt s) : FreiheitssatzAt (FreeGroup.map e s) := by
  classical
  intro hcyc T hT
  -- the relator is cyclically reduced
  have hcyc' : IsCyclicallyReducedRelator s := by
    have h1 : FreeGroup.IsCyclicallyReduced (FreeGroup.toWord (FreeGroup.map e s)) := hcyc
    rw [toWord_map_of_injective e e.injective s] at h1
    exact isCyclicallyReduced_of_isCyclicallyReduced_map e e.injective h1
  -- the generators `e.symm '' T` do not generate `s`
  have hT' : s ∉ Subgroup.closure (FreeGroup.of '' (e.symm '' T)) := by
    intro hmem
    apply hT
    have hle : Subgroup.closure (FreeGroup.of '' (e.symm '' T)) ≤
        Subgroup.comap (FreeGroup.map e) (Subgroup.closure (FreeGroup.of '' T)) := by
      refine (Subgroup.closure_le _).mpr ?_
      intro y hy
      rw [Set.mem_image] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      rw [Set.mem_image] at ha
      obtain ⟨t, ht, rfl⟩ := ha
      have hmem' : FreeGroup.map (⇑e) (FreeGroup.of (e.symm t)) ∈
          Subgroup.closure (FreeGroup.of '' T) := by
        rw [FreeGroup.map.of, Equiv.apply_symm_apply]
        exact Subgroup.subset_closure ⟨t, ht, rfl⟩
      exact hmem'
    exact (Subgroup.mem_comap).mp (hle hmem)
  have hinj := h hcyc' (e.symm '' T) hT'
  -- the two maps between the two presented groups
  let fwd : PresentedGroup ({s} : Set (FreeGroup γ)) →*
      PresentedGroup ({FreeGroup.map e s} : Set (FreeGroup δ)) :=
    PresentedGroup.toGroup (f := fun a : γ => PresentedGroup.of (e a)) (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have hcomp : FreeGroup.lift (fun a : γ => PresentedGroup.of (e a)) =
          (PresentedGroup.mk ({FreeGroup.map e s} : Set (FreeGroup δ))).comp (FreeGroup.map e) := by
        refine FreeGroup.ext_hom _ _ fun a => ?_
        rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply, FreeGroup.map.of]
        rfl
      rw [hcomp, MonoidHom.comp_apply, PresentedGroup.one_of_mem (Set.mem_singleton _)])
  let bwd : PresentedGroup ({FreeGroup.map e s} : Set (FreeGroup δ)) →*
      PresentedGroup ({s} : Set (FreeGroup γ)) :=
    PresentedGroup.toGroup (f := fun b : δ => PresentedGroup.of (e.symm b)) (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have hcomp : FreeGroup.lift (fun b : δ => PresentedGroup.of (e.symm b)) =
          (PresentedGroup.mk ({s} : Set (FreeGroup γ))).comp (FreeGroup.map e.symm) := by
        refine FreeGroup.ext_hom _ _ fun b => ?_
        rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply, FreeGroup.map.of]
        rfl
      rw [hcomp, MonoidHom.comp_apply]
      rw [map_map_self e s]
      exact PresentedGroup.one_of_mem (Set.mem_singleton s))
  have hfwd_inj : Function.Injective fwd := by
    have hcomp : bwd.comp fwd = MonoidHom.id _ := by
      refine PresentedGroup.ext fun a => ?_
      show bwd (fwd (PresentedGroup.of a)) = PresentedGroup.of a
      rw [show fwd (PresentedGroup.of a) = PresentedGroup.of (e a) from
            PresentedGroup.toGroup.of _,
          show bwd (PresentedGroup.of (e a)) = PresentedGroup.of (e.symm (e a)) from
            PresentedGroup.toGroup.of _,
          Equiv.symm_apply_apply]
    refine Function.LeftInverse.injective (g := bwd) fun x => ?_
    have := DFunLike.congr_fun hcomp x
    simpa using this
  -- the bijection between the two generating sets
  let eb : ↥(e.symm '' T) ≃ ↥T :=
    { toFun := fun a => ⟨e a, by
        rcases a.2 with ⟨t, ht, hta⟩
        rwa [← hta, Equiv.apply_symm_apply]⟩
      invFun := fun t => ⟨e.symm t, ⟨t, t.2, rfl⟩⟩
      left_inv := fun a => Subtype.ext (Equiv.symm_apply_apply e a.1)
      right_inv := fun t => Subtype.ext (Equiv.apply_symm_apply e t.1) }
  have hcompat : fwd.comp (presentedGroupMap s (e.symm '' T)) =
      (presentedGroupMap (FreeGroup.map e s) T).comp (FreeGroup.freeGroupCongr eb).toMonoidHom := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    show fwd (presentedGroupMap s (e.symm '' T) (FreeGroup.of a)) =
      presentedGroupMap (FreeGroup.map e s) T (FreeGroup.freeGroupCongr eb (FreeGroup.of a))
    rw [show presentedGroupMap s (e.symm '' T) (FreeGroup.of a) = PresentedGroup.of (a : γ) from
          presentedGroupMap_of_apply a,
        show fwd (PresentedGroup.of (a : γ)) = PresentedGroup.of (e (a : γ)) from
          PresentedGroup.toGroup.of _,
        show (FreeGroup.freeGroupCongr eb) (FreeGroup.of a) = FreeGroup.of (eb a) from
          FreeGroup.map.of,
        presentedGroupMap_of_apply (eb a)]
    rfl
  have hinj2 : Function.Injective
      ((presentedGroupMap (FreeGroup.map e s) T).comp (FreeGroup.freeGroupCongr eb).toMonoidHom) := by
    rw [← hcompat]
    exact hfwd_inj.comp hinj
  intro x y hxy
  obtain ⟨x', rfl⟩ := (FreeGroup.freeGroupCongr eb).surjective x
  obtain ⟨y', rfl⟩ := (FreeGroup.freeGroupCongr eb).surjective y
  have hx'y' : x' = y' := hinj2 (by
    show (presentedGroupMap (FreeGroup.map e s) T)
        ((FreeGroup.freeGroupCongr eb) x') =
      (presentedGroupMap (FreeGroup.map e s) T) ((FreeGroup.freeGroupCongr eb) y')
    exact hxy)
  simpa using congrArg (FreeGroup.freeGroupCongr eb) hx'y'

/-- **The Freiheitssatz is invariant under an equivalence of generating types.** -/
theorem freiheitssatzAt_equiv {γ : Type u} {δ : Type v} (e : γ ≃ δ) (s : FreeGroup γ) :
    FreiheitssatzAt s ↔ FreiheitssatzAt (FreeGroup.map e s) := by
  refine ⟨fun h => freiheitssatzAt_map_of_equiv e s h, fun h => ?_⟩
  have := freiheitssatzAt_map_of_equiv e.symm (FreeGroup.map e s) h
  rwa [map_map_self e s] at this

/-! ### The algebraic core of the HNN step -/

/-- The image of a generator `a ∈ T` in the presented group `⟨r⟩` lies in the Magnus subgroup
generated by `T`. -/
theorem mem_magnusSubgroupOf_of {α : Type u} {r : FreeGroup α} (T : Set α) (a : T) :
    PresentedGroup.of (a : α) ∈ magnusSubgroupOf r T :=
  Subgroup.subset_closure ⟨a, rfl⟩

/-- **The HNN step of the Freiheitssatz, algebraic form.**  Given a cyclically reduced relator `r`
whose exponent sum in `t` is zero (`sigma t r = 1`), such that the `x`-decorations of the Magnus
rewriting `magRewRel t r` all lie in the interval `[a,b]` and `a ≤ 0 ≤ b`, there is an HNN
decomposition of `⟨α | r⟩` with stable letter `t` over the one-relator group `⟨β | magRewRel t r⟩`,
with the associated subgroups generated by the decorations other than the top `x`-decoration `(x,b)`
and by their shift. -/
theorem hnnStepCore_of_bounds {α : Type u} (r : FreeGroup α) (t x : α)
    (hcyc : IsCyclicallyReducedRelator r) (htx : x ≠ t) (ht0 : sigma t r = 1)
    (a b : ℤ)
    (ha : (⟨x, htx⟩, a) ∈ relatorLetters (magRewRel t r))
    (hb : (⟨x, htx⟩, b) ∈ relatorLetters (magRewRel t r))
    (halt : ∀ k : ℤ, (⟨x, htx⟩, k) ∈ relatorLetters (magRewRel t r) → a ≤ k ∧ k ≤ b)
    (ha0 : a ≤ 0) (h0b : 0 ≤ b)
    (hF : FreiheitssatzAt (magRewRel t r)) :
    Nonempty (HNNStepCore r t x a b) := by
  classical
  letI : DecidableEq (HNNDec t) := Classical.decEq _
  have hcycr : FreeGroup.IsCyclicallyReduced r.toWord := by
    simpa [IsCyclicallyReducedRelator] using hcyc
  have hredr : FreeGroup.IsReduced r.toWord := hcycr.isReduced
  have hredw : FreeGroup.IsReduced (rewrite t r.toWord) := rewrite_isReduced t hredr
  have htoWord : (magRewRel t r).toWord = rewrite t r.toWord := by
    rw [magRewRel, FreeGroup.toWord_mk, hredw.reduce_eq]
  have heps : eps t r = 0 := (eps_eq_zero_iff_sigma_eq_one t r).mpr ht0
  have hepsw : wordEps t r.toWord = 0 := by simpa [eps] using heps
  have hcyc' : IsCyclicallyReducedRelator (magRewRel t r) := by
    rw [IsCyclicallyReducedRelator, htoWord]
    exact isCyclicallyReducedRelator_rewrite_toWord t hcycr hepsw
  have hmem_letters : ∀ p : HNNDec t,
      p ∈ relatorLetters (magRewRel t r) ↔ ∃ c : Bool, (p, c) ∈ rewrite t r.toWord := by
    intro p
    rw [relatorLetters, htoWord]
    simp only [Set.mem_ofPred_eq]
  -- the two generating sets satisfy the hypothesis of the Freiheitssatz
  have hbS : (⟨x, htx⟩, b) ∉ hnnS t x htx a b := by
    intro h
    rcases h with h | ⟨-, h2⟩
    · exact h rfl
    · omega
  have hS : magRewRel t r ∉ Subgroup.closure (FreeGroup.of '' hnnS t x htx a b) := by
    intro hmem
    exact hbS ((letters_closure_iff (magRewRel t r) (hnnS t x htx a b)).mp hmem hb)
  have haS1 : (⟨x, htx⟩, a) ∉ hnnS1 t x htx a b := by
    intro h
    rcases (hnnS1_iff t x htx a b (⟨x, htx⟩, a)).mp h with h1 | ⟨h2, -⟩
    · exact h1 rfl
    · omega
  have hS1 : magRewRel t r ∉ Subgroup.closure (FreeGroup.of '' hnnS1 t x htx a b) := by
    intro hmem
    exact haS1 ((letters_closure_iff (magRewRel t r) (hnnS1 t x htx a b)).mp hmem ha)
  have hfrei := hF hcyc'
  -- the two Magnus subgroups and the isomorphism between them
  let A : Subgroup (HNNBase r t) := magnusSubgroupOf (magRewRel t r) (hnnS t x htx a b)
  let B : Subgroup (HNNBase r t) := magnusSubgroupOf (magRewRel t r) (hnnS1 t x htx a b)
  let eA : FreeGroup (hnnS t x htx a b) ≃* A :=
    (MonoidHom.ofInjective (f := presentedGroupMap (magRewRel t r) (hnnS t x htx a b))
        (hfrei (hnnS t x htx a b) hS)).trans
      (MulEquiv.subgroupCongr (range_presentedGroupMap (magRewRel t r) (hnnS t x htx a b)))
  let eB : FreeGroup (hnnS1 t x htx a b) ≃* B :=
    (MonoidHom.ofInjective (f := presentedGroupMap (magRewRel t r) (hnnS1 t x htx a b))
        (hfrei (hnnS1 t x htx a b) hS1)).trans
      (MulEquiv.subgroupCongr (range_presentedGroupMap (magRewRel t r) (hnnS1 t x htx a b)))
  let shE : hnnS t x htx a b ≃ hnnS1 t x htx a b := hnnShiftEquiv t x htx a b
  let φ : A ≃* B := eA.symm.trans ((FreeGroup.freeGroupCongr shE).trans eB)
  let Ext : Type u := HNNExtension (HNNBase r t) A B φ
  have eA_of : ∀ p : hnnS t x htx a b,
      ((eA (FreeGroup.of p)) : A) =
        ⟨PresentedGroup.of (p : HNNDec t), Subgroup.subset_closure ⟨p, rfl⟩⟩ := by
    intro p
    refine Subtype.ext ?_
    simp only [eA, MulEquiv.trans_apply, MonoidHom.ofInjective_apply, MulEquiv.subgroupCongr_apply]
    exact presentedGroupMap_of_apply p
  have eB_of : ∀ p : hnnS1 t x htx a b,
      ((eB (FreeGroup.of p)) : B) =
        ⟨PresentedGroup.of (p : HNNDec t), Subgroup.subset_closure ⟨p, rfl⟩⟩ := by
    intro p
    refine Subtype.ext ?_
    simp only [eB, MulEquiv.trans_apply, MonoidHom.ofInjective_apply, MulEquiv.subgroupCongr_apply]
    exact presentedGroupMap_of_apply p
  have hφeq : φ = eA.symm.trans ((FreeGroup.freeGroupCongr shE).trans eB) := rfl
  have φ_gen : ∀ p : hnnS t x htx a b,
      ((φ ⟨PresentedGroup.of (p : HNNDec t), Subgroup.subset_closure ⟨p, rfl⟩⟩ : B) :
          HNNBase r t)
        = PresentedGroup.of ((shE p : hnnS1 t x htx a b) : HNNDec t) := by
    intro p
    have h1 : eA.symm ⟨PresentedGroup.of (p : HNNDec t), Subgroup.subset_closure ⟨p, rfl⟩⟩ =
        FreeGroup.of p := by
      rw [← eA_of p]
      exact MulEquiv.symm_apply_apply _ _
    rw [hφeq, MulEquiv.trans_apply, h1]
    change ((eB (FreeGroup.map (shE : hnnS t x htx a b → hnnS1 t x htx a b) (FreeGroup.of p)) : B) :
      HNNBase r t) = _
    rw [FreeGroup.map.of]
    exact congrArg (fun z : B => (z : HNNBase r t)) (eB_of (shE p))
  -- the stable letter conjugates a generator of the first associated subgroup to the shifted one
  have hstep : ∀ (p : HNNDec t), p ∈ hnnS t x htx a b →
      (HNNExtension.of (PresentedGroup.of (hnnShift t p)) : Ext) =
        HNNExtension.t * HNNExtension.of (PresentedGroup.of p) * HNNExtension.t⁻¹ := by
    intro p hp
    have hmemA : PresentedGroup.of p ∈ A :=
      Subgroup.subset_closure ⟨(⟨p, hp⟩ : ↥(hnnS t x htx a b)), rfl⟩
    have h := HNNExtension.equiv_eq_conj (φ := φ)
      (⟨PresentedGroup.of p, hmemA⟩ : A)
    have h2 : ((φ ⟨PresentedGroup.of p, hmemA⟩ : B) : HNNBase r t) =
        PresentedGroup.of (hnnShift t p) := by
      have h3 := φ_gen (⟨p, hp⟩ : ↥(hnnS t x htx a b))
      rwa [show ((shE (⟨p, hp⟩ : ↥(hnnS t x htx a b)) : ↥(hnnS1 t x htx a b)) : HNNDec t) =
        hnnShift t p from rfl] at h3
    rw [h2] at h
    exact h
  -- the chain of conjugations along the decoration index
  have hchain : ∀ (y : {a : α // a ≠ t}) (i : ℤ),
      (∀ j : ℤ, 0 ≤ j → j < i → (y, j) ∈ hnnS t x htx a b) →
      (∀ j : ℤ, i ≤ j → j < 0 → (y, j) ∈ hnnS t x htx a b) →
      (HNNExtension.t ^ i * HNNExtension.of (PresentedGroup.of ((y, (0 : ℤ)) : HNNDec t)) *
          HNNExtension.t ^ (-i) : Ext) =
        HNNExtension.of (PresentedGroup.of ((y, i) : HNNDec t)) := by
    intro y i
    induction i using Int.induction_on with
    | zero => intro _ _; simp
    | succ n ih =>
      intro hup hdown
      have hup' : ∀ j : ℤ, 0 ≤ j → j < (n : ℤ) → (y, j) ∈ hnnS t x htx a b :=
        fun j h1 h2 => hup j h1 (by omega)
      have hdown' : ∀ j : ℤ, (n : ℤ) ≤ j → j < 0 → (y, j) ∈ hnnS t x htx a b :=
        fun j h1 h2 => absurd h1 (by omega)
      have hmem : (y, ((n : ℕ) : ℤ)) ∈ hnnS t x htx a b := hup (n : ℤ) (by omega) (by omega)
      have hst := hstep ((y, ((n : ℕ) : ℤ))) hmem
      calc HNNExtension.t ^ ((n : ℤ) + 1) *
              HNNExtension.of (PresentedGroup.of ((y, (0 : ℤ)) : HNNDec t)) *
              HNNExtension.t ^ (-((n : ℤ) + 1))
          = HNNExtension.t * (HNNExtension.t ^ (n : ℤ) *
              HNNExtension.of (PresentedGroup.of ((y, (0 : ℤ)) : HNNDec t)) *
              HNNExtension.t ^ (-(n : ℤ))) * HNNExtension.t⁻¹ := by group
        _ = HNNExtension.t * HNNExtension.of (PresentedGroup.of ((y, ((n : ℕ) : ℤ)) : HNNDec t)) *
              HNNExtension.t⁻¹ := by rw [ih hup' hdown']
        _ = HNNExtension.of (PresentedGroup.of ((y, ((n : ℤ) + 1)) : HNNDec t)) := by
              rw [← hst]
              rfl
    | pred n ih =>
      intro hup hdown
      have hup' : ∀ j : ℤ, 0 ≤ j → j < -((n : ℤ)) → (y, j) ∈ hnnS t x htx a b :=
        fun j h1 h2 => hup j h1 (by omega)
      have hdown' : ∀ j : ℤ, -((n : ℤ)) ≤ j → j < 0 → (y, j) ∈ hnnS t x htx a b :=
        fun j h1 h2 => hdown j (by omega) (by omega)
      have hmem : (y, -((n : ℤ)) - 1) ∈ hnnS t x htx a b :=
        hdown (-((n : ℤ)) - 1) (by omega) (by omega)
      have hst := hstep ((y, -((n : ℤ)) - 1)) hmem
      have hshift : hnnShift t ((y, -((n : ℤ)) - 1) : HNNDec t) = ((y, -((n : ℤ))) : HNNDec t) := by
        refine Prod.ext rfl ?_
        simp [hnnShift]
      rw [hshift] at hst
      calc HNNExtension.t ^ (-((n : ℤ)) - 1) *
              HNNExtension.of (PresentedGroup.of ((y, (0 : ℤ)) : HNNDec t)) *
              HNNExtension.t ^ (-(-((n : ℤ)) - 1))
          = HNNExtension.t⁻¹ * (HNNExtension.t ^ (-((n : ℤ))) *
              HNNExtension.of (PresentedGroup.of ((y, (0 : ℤ)) : HNNDec t)) *
              HNNExtension.t ^ (-(-((n : ℤ))))) * HNNExtension.t := by group
        _ = HNNExtension.t⁻¹ * HNNExtension.of (PresentedGroup.of ((y, -((n : ℤ))) : HNNDec t)) *
              HNNExtension.t := by rw [ih hup' hdown']
        _ = HNNExtension.of (PresentedGroup.of ((y, -((n : ℤ)) - 1) : HNNDec t)) := by
              rw [hst]
              group
  -- the element of the HNN extension attached to a decoration
  set Ψ : HNNDec t → Ext := (fun p =>
    HNNExtension.t ^ (p.2) * HNNExtension.of (PresentedGroup.of ((p.1, (0 : ℤ)) : HNNDec t)) *
      HNNExtension.t ^ (-(p.2))) with hΨ
  have hkey : ∀ p : HNNDec t, p ∈ relatorLetters (magRewRel t r) →
      Ψ p = (HNNExtension.of (PresentedGroup.of p) : Ext) := by
    intro p hp
    by_cases hpx : p.1 = (⟨x, htx⟩ : {a : α // a ≠ t})
    · have hp' : (⟨x, htx⟩, p.2) ∈ relatorLetters (magRewRel t r) := by
        rw [show (⟨x, htx⟩, p.2) = p from Prod.ext hpx.symm rfl]
        exact hp
      have hbnd := halt p.2 hp'
      have hc := hchain p.1 p.2 (fun j hj1 hj2 => Or.inr ⟨by omega, by omega⟩)
        (fun j hj1 hj2 => Or.inr ⟨by omega, by omega⟩)
      simpa only [hΨ] using hc
    · have hc := hchain p.1 p.2 (fun j _ _ => Or.inl hpx) (fun j _ _ => Or.inl hpx)
      simpa only [hΨ] using hc
  -- the map `F α →* Ext` underlying `θ`
  set gt : PresentedGroup ({r} : Set (FreeGroup α)) := PresentedGroup.of t with hgt
  set fα : α → Ext := (fun y =>
    if hy : y = t then HNNExtension.t
    else HNNExtension.of (PresentedGroup.of ((⟨y, hy⟩, (0 : ℤ)) : HNNDec t))) with hfα
  have hcomp : (FreeGroup.lift fα).comp (rho t) = FreeGroup.lift Ψ := by
    refine FreeGroup.ext_hom _ _ fun p => ?_
    show FreeGroup.lift fα (rho t (FreeGroup.of p)) = FreeGroup.lift Ψ (FreeGroup.of p)
    simp only [rho, FreeGroup.lift_apply_of, map_mul, map_zpow, hfα, hΨ]
    rw [dif_pos trivial, dif_neg p.1.2]
  have hrho : rho t (magRewRel t r) = r := by
    have h := rho_magRew t 0 r.toWord
    rw [magRew_zero_eq_rewrite, hepsw] at h
    simpa [magRewRel, FreeGroup.mk_toWord] using h
  have hlift : FreeGroup.lift fα r = 1 := by
    have hmain : FreeGroup.lift fα (rho t (magRewRel t r)) = 1 := by
      rw [← MonoidHom.comp_apply, hcomp]
      have h1 : FreeGroup.lift Ψ (magRewRel t r) =
          FreeGroup.lift (fun p : HNNDec t => (HNNExtension.of (PresentedGroup.of p) : Ext))
            (magRewRel t r) := by
        show FreeGroup.lift Ψ (FreeGroup.mk (rewrite t (@FreeGroup.toWord α (Classical.decEq α) r))) =
          FreeGroup.lift (fun p : HNNDec t => (HNNExtension.of (PresentedGroup.of p) : Ext))
            (FreeGroup.mk (rewrite t (@FreeGroup.toWord α (Classical.decEq α) r)))
        rw [FreeGroup.lift_mk, FreeGroup.lift_mk]
        refine congrArg List.prod (List.map_congr_left ?_)
        intro q hq
        have hq' : q.1 ∈ relatorLetters (magRewRel t r) := (hmem_letters q.1).mpr ⟨q.2, hq⟩
        rw [hkey q.1 hq']
      rw [h1]
      have h4 : FreeGroup.lift (fun p : HNNDec t => (HNNExtension.of (PresentedGroup.of p) : Ext))
          (magRewRel t r) =
          HNNExtension.of (PresentedGroup.mk ({magRewRel t r} : Set (FreeGroup (HNNDec t)))
            (magRewRel t r)) := by
        have h3 : FreeGroup.lift
            (fun p : HNNDec t => (HNNExtension.of (PresentedGroup.of p) : Ext)) =
            (HNNExtension.of).comp
              (PresentedGroup.mk ({magRewRel t r} : Set (FreeGroup (HNNDec t)))) := by
          refine FreeGroup.ext_hom _ _ fun p => ?_
          simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
          rfl
        rw [h3, MonoidHom.comp_apply]
      rw [h4, PresentedGroup.one_of_mem (Set.mem_singleton _), map_one]
    rwa [hrho] at hmain
  -- the two maps between `⟨α | r⟩` and the HNN extension
  set θ : PresentedGroup ({r} : Set (FreeGroup α)) →* Ext :=
    PresentedGroup.toGroup (f := fα) (fun rel hrel => by
      rw [Set.mem_singleton_iff] at hrel
      subst hrel
      exact hlift) with hθ
  set ψ₀ : HNNBase r t →* PresentedGroup ({r} : Set (FreeGroup α)) :=
    PresentedGroup.toGroup
      (f := fun p : HNNDec t => (PresentedGroup.of t) ^ (p.2) * PresentedGroup.of ((p.1 : α)) *
        (PresentedGroup.of t) ^ (-(p.2))) (fun rel hrel => by
      rw [Set.mem_singleton_iff] at hrel
      subst hrel
      have hcomp' : FreeGroup.lift (fun p : HNNDec t => (PresentedGroup.of t) ^ (p.2) *
          PresentedGroup.of ((p.1 : α)) * (PresentedGroup.of t) ^ (-(p.2))) =
          (PresentedGroup.mk ({r} : Set (FreeGroup α))).comp (rho t) := by
        refine FreeGroup.ext_hom _ _ fun p => ?_
        simp only [rho, FreeGroup.lift_apply_of, MonoidHom.comp_apply, map_mul, map_zpow]
        rfl
      rw [hcomp', MonoidHom.comp_apply, hrho]
      exact PresentedGroup.one_of_mem (Set.mem_singleton r)) with hψ₀
  have hψ₀_gen : ∀ p : HNNDec t, ψ₀ (PresentedGroup.of p) =
      (PresentedGroup.of t) ^ (p.2) * PresentedGroup.of ((p.1 : α)) *
        (PresentedGroup.of t) ^ (-(p.2)) := by
    intro p
    simp only [hψ₀, PresentedGroup.toGroup.of]
  have hcompat : ∀ aa : A, gt * ψ₀ (aa : HNNBase r t) = ψ₀ ((φ aa : B) : HNNBase r t) * gt := by
    intro aa
    have key : ∀ w : FreeGroup (↥(hnnS t x htx a b)),
        gt * ψ₀ ((eA w : A) : HNNBase r t) =
          ψ₀ ((φ (eA w) : B) : HNNBase r t) * gt := by
      intro w
      induction w using FreeGroup.induction_on with
      | one => simp only [Subgroup.coe_one, map_one, mul_one, one_mul]
      | of p =>
        have hsh : ((shE p : ↥(hnnS1 t x htx a b)) : HNNDec t) = (p.1.1, p.1.2 + 1) := rfl
        rw [eA_of p, φ_gen p, hψ₀_gen (p : HNNDec t),
          hψ₀_gen ((shE p : ↥(hnnS1 t x htx a b)) : HNNDec t),
          show gt = PresentedGroup.of t from rfl, hsh]
        group
      | inv_of p ih =>
        rw [show eA ((FreeGroup.of p)⁻¹) = (eA (FreeGroup.of p))⁻¹ from map_inv eA _]
        simp only [Subgroup.coe_inv, map_inv]
        have hb : ψ₀ ↑(φ (eA (FreeGroup.of p))) = gt * ψ₀ ↑(eA (FreeGroup.of p)) * gt⁻¹ := by
          rw [ih]
          group
        rw [hb]
        group
      | mul u v ihu ihv =>
        rw [show eA (u * v) = eA u * eA v from map_mul eA u v]
        simp only [Subgroup.coe_mul, map_mul]
        have hau : ψ₀ ↑(φ (eA u)) = gt * ψ₀ ↑(eA u) * gt⁻¹ := by
          rw [ihu]
          group
        have hbv : ψ₀ ↑(φ (eA v)) = gt * ψ₀ ↑(eA v) * gt⁻¹ := by
          rw [ihv]
          group
        rw [hau, hbv]
        group
    have h := key (eA.symm aa)
    rwa [MulEquiv.apply_symm_apply] at h
  set α' : Ext →* PresentedGroup ({r} : Set (FreeGroup α)) :=
    HNNExtension.lift ψ₀ gt hcompat with hα'
  have hαθ : α'.comp θ = MonoidHom.id (PresentedGroup ({r} : Set (FreeGroup α))) := by
    refine PresentedGroup.ext fun y => ?_
    show α' (θ (PresentedGroup.of y)) = PresentedGroup.of y
    rw [show θ (PresentedGroup.of y) = fα y from PresentedGroup.toGroup.of _]
    by_cases hy : y = t
    · rw [hy]
      rw [show fα t = HNNExtension.t from dif_pos rfl, hα']
      rw [HNNExtension.lift_t]
    · rw [show fα y = HNNExtension.of (PresentedGroup.of ((⟨y, hy⟩, (0 : ℤ)) : HNNDec t)) from
        dif_neg hy, hα']
      rw [HNNExtension.lift_of, hψ₀_gen]
      simp
  have hinj : Function.Injective θ := by
    refine Function.LeftInverse.injective (g := α') fun u => ?_
    have h := DFunLike.congr_fun hαθ u
    simpa using h
  refine ⟨A, B, φ, θ, hinj, ?_, ?_, ?_⟩
  · -- `θ` on the generators other than `t`
    intro s hs
    show θ (PresentedGroup.of s) =
      HNNExtension.of (PresentedGroup.of ((⟨s, hs⟩, (0 : ℤ)) : HNNDec t))
    rw [show θ (PresentedGroup.of s) = fα s from PresentedGroup.toGroup.of _]
    exact dif_neg hs
  · -- `θ` on the stable letter
    show θ (PresentedGroup.of t) = HNNExtension.t
    rw [show θ (PresentedGroup.of t) = fα t from PresentedGroup.toGroup.of _]
    exact dif_pos rfl
  · -- the stable letter conjugates the generators other than `x`
    intro s hs hxs i
    have hmem : ((⟨s, hs⟩ : {a : α // a ≠ t}), i) ∈ hnnS t x htx a b := by
      refine Or.inl ?_
      intro h
      exact hxs (Subtype.ext_iff.mp h)
    have hst := hstep ((⟨s, hs⟩, i)) hmem
    rw [show hnnShift t ((⟨s, hs⟩, i)) = ((⟨s, hs⟩, i + 1)) from rfl] at hst
    exact hst.symm

/-! ### Transport of the Freiheitssatz along an injective relabelling of the generators -/

section FSRestrict

variable {γ : Type u}

/-- The reduced word of the image of `s` under an injective relabelling of the generators, with both
`DecidableEq` instances fixed to the classical ones. -/
theorem toWord_map_of_injective_classical {γ δ : Type*} (f : γ → δ) (hf : Function.Injective f)
    (s : FreeGroup γ) :
    (@FreeGroup.toWord δ (Classical.decEq δ) (FreeGroup.map f s)) =
      (@FreeGroup.toWord γ (Classical.decEq γ) s).map (fun p => (f p.1, p.2)) := by
  rw [@toWord_map_of_injective γ δ (Classical.decEq γ) (Classical.decEq δ) f hf s]

/-- If the relator `sz`, viewed in `F(γ)` through the injection `F(Z) → F(γ)`, has cyclically
reduced reduced word, then so does `sz`. -/
theorem isCyclicallyReducedRelator_of_map_subtype_val {Z : Set γ} {sz : FreeGroup Z}
    {s : FreeGroup γ} (hs : FreeGroup.map (Subtype.val : Z → γ) sz = s)
    (h : IsCyclicallyReducedRelator s) : IsCyclicallyReducedRelator sz := by
  classical
  have h1 : FreeGroup.IsCyclicallyReduced
      ((@FreeGroup.toWord Z (Classical.decEq Z) sz).map
        fun p : Z × Bool => (Subtype.val p.1, p.2)) := by
    have h2 : FreeGroup.IsCyclicallyReduced
        (@FreeGroup.toWord γ (Classical.decEq γ) (FreeGroup.map (Subtype.val : Z → γ) sz)) := by
      rw [hs]
      exact h
    rwa [toWord_map_of_injective_classical (Subtype.val : Z → γ) Subtype.val_injective sz] at h2
  exact isCyclicallyReduced_of_isCyclicallyReduced_map (Subtype.val : Z → γ)
    Subtype.val_injective h1

/-- If the generators in `T` do not generate the relator `s = F(Z) ↪ F(γ) sz`, then the generators
in `T ∩ Z` do not generate `sz`. -/
theorem notMem_closure_of_map_subtype_val {Z : Set γ} {sz : FreeGroup Z} {s : FreeGroup γ}
    (hs : FreeGroup.map (Subtype.val : Z → γ) sz = s) {T : Set γ}
    (hT : s ∉ Subgroup.closure (FreeGroup.of '' T)) :
    sz ∉ Subgroup.closure (FreeGroup.of '' {z : Z | (z : γ) ∈ T}) := by
  intro hmem
  apply hT
  rw [← hs]
  have hle : Subgroup.closure (FreeGroup.of '' {z : Z | (z : γ) ∈ T}) ≤
      Subgroup.comap (FreeGroup.map (Subtype.val : Z → γ)) (Subgroup.closure (FreeGroup.of '' T)) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    rw [Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    show FreeGroup.map (Subtype.val : Z → γ) (FreeGroup.of z) ∈
      Subgroup.closure (FreeGroup.of '' T)
    rw [FreeGroup.map.of]
    exact Subgroup.subset_closure ⟨↑z, hz, rfl⟩
  exact (Subgroup.mem_comap).mp (hle hmem)

end FSRestrict

/-- The split of a set `T` of generators into the part lying in `Z` and the part outside `Z`. -/
theorem sigmaComplementEquiv {γ : Type u} (T : Set γ) (Z : Set γ) :
    ∃ e : ↥T ≃ Sigma (CoprodTwoFam ↥{z : Z | (z : γ) ∈ T} ↥{a : T | (a : γ) ∉ Z}),
      (∀ (a : ↥T) (h : (a : γ) ∈ Z), e a = ⟨true, ⟨⟨(a : γ), h⟩, a.2⟩⟩) ∧
      (∀ (a : ↥T) (h : (a : γ) ∉ Z), e a = ⟨false, ⟨a, h⟩⟩) := by
  classical
  let Tz := {z : Z | (z : γ) ∈ T}
  let Tn := {a : T | (a : γ) ∉ Z}
  let f : ↥T → Sigma (CoprodTwoFam ↥Tz ↥Tn) := fun a =>
    if h : (a : γ) ∈ Z then ⟨true, (⟨⟨(a : γ), h⟩, a.2⟩ : Tz)⟩ else ⟨false, (⟨a, h⟩ : Tn)⟩
  let g : Sigma (CoprodTwoFam ↥Tz ↥Tn) → ↥T := fun x =>
    Bool.rec (motive := fun b => CoprodTwoFam ↥Tz ↥Tn b → ↥T)
      (fun y => y.1) (fun z => (⟨(z.1 : γ), z.2⟩ : ↥T)) x.1 x.2
  have hf1 : ∀ (a : ↥T) (h : (a : γ) ∈ Z), f a = ⟨true, (⟨⟨(a : γ), h⟩, a.2⟩ : Tz)⟩ :=
    fun a h => by simp only [f, dif_pos h]
  have hf2 : ∀ (a : ↥T) (h : (a : γ) ∉ Z), f a = ⟨false, (⟨a, h⟩ : Tn)⟩ :=
    fun a h => by simp only [f, dif_neg h]
  have hleft : ∀ a : ↥T, g (f a) = a := by
    intro a
    by_cases ha : (a : γ) ∈ Z
    · rw [hf1 a ha]
    · rw [hf2 a ha]
  have hright : ∀ x : Sigma (CoprodTwoFam ↥Tz ↥Tn), f (g x) = x := by
    rintro ⟨b, y⟩
    cases b with
    | true =>
      have : f (g ⟨true, y⟩) = ⟨true, (⟨⟨(y.1 : γ), y.1.2⟩, y.2⟩ : Tz)⟩ := by
        rw [show g ⟨true, y⟩ = (⟨(y.1 : γ), y.2⟩ : ↥T) from rfl, hf1 _ y.1.2]
      rw [this]
      exact congrArg (Sigma.mk true) (Subtype.ext (Subtype.ext rfl))
    | false =>
      have hnmem : ((y.1 : T) : γ) ∉ Z := y.2
      have : f (g ⟨false, y⟩) = ⟨false, (⟨y.1, hnmem⟩ : Tn)⟩ := by
        rw [show g ⟨false, y⟩ = y.1 from rfl, hf2 _ hnmem]
      rw [this]
      exact congrArg (Sigma.mk false) (Subtype.ext rfl)
  refine ⟨⟨f, g, hleft, hright⟩, ?_, ?_⟩
  · intro a h; exact hf1 a h
  · intro a h; exact hf2 a h

theorem freeGroupEquivCoprodI {α : Type u} {X : Bool → Type u} (e : α ≃ Sigma X) :
    ∃ κ : FreeGroup α ≃* Monoid.CoprodI (fun i => FreeGroup (X i)),
      ∀ a : α, κ (FreeGroup.of a) = (Monoid.CoprodI.of (i := (e a).1)) (FreeGroup.of (e a).2) := by
  classical
  have hbase : ∀ (a : α),
      (Monoid.CoprodI.FreeGroupBasis.coprodI
        (fun i => FreeGroupBasis.ofFreeGroup (X i))).repr.symm (FreeGroup.of (e a)) =
      (Monoid.CoprodI.of (i := (e a).1)) (FreeGroup.of (e a).2) := by
    intro a
    show FreeGroup.lift
      (fun x : Sigma X => Monoid.CoprodI.of (M := fun i => FreeGroup (X i)) (i := x.1)
        (FreeGroupBasis.ofFreeGroup (X x.1) x.2))
      (FreeGroup.of (e a)) =
      Monoid.CoprodI.of (M := fun i => FreeGroup (X i)) (i := (e a).1) (FreeGroup.of (e a).2)
    rw [FreeGroup.lift_apply_of]
    rfl
  refine ⟨(FreeGroup.freeGroupCongr e).trans
    (Monoid.CoprodI.FreeGroupBasis.coprodI (fun i => FreeGroupBasis.ofFreeGroup (X i))).repr.symm, ?_⟩
  intro a
  show (Monoid.CoprodI.FreeGroupBasis.coprodI (fun i => FreeGroupBasis.ofFreeGroup (X i))).repr.symm
    (FreeGroup.freeGroupCongr e (FreeGroup.of a)) = _
  rw [show FreeGroup.freeGroupCongr e (FreeGroup.of a) = FreeGroup.of (e a) from
    FreeGroup.map.of]
  exact hbase a

theorem coprodILiftInjectiveBool {M M' : Bool → Type u} [∀ i, Group (M i)] [∀ i, Group (M' i)]
    (F : ∀ i, M i →* M' i) (hF : ∀ i, Function.Injective (F i)) :
    Function.Injective (Monoid.CoprodI.lift (fun i => (Monoid.CoprodI.of (i := i)).comp (F i))) := by
  classical
  let fi : ∀ i, M i →* Monoid.CoprodI M' := fun i => (Monoid.CoprodI.of (i := i)).comp (F i)
  let g : Sigma M → Sigma M' := fun l => ⟨l.1, F l.1 l.2⟩
  have hg : Function.Injective g := by
    rintro ⟨i, m⟩ ⟨j, n⟩ h
    obtain ⟨hij, hmn⟩ := Sigma.mk.inj h
    subst hij
    exact Sigma.ext rfl (heq_of_eq (hF i (eq_of_heq hmn)))
  let W : Monoid.CoprodI.Word M → Monoid.CoprodI.Word M' := fun w =>
    { toList := w.toList.map g
      ne_one := by
        intro l hl
        obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
        exact fun h => w.ne_one l₀ hl₀ (hF l₀.1 (by simpa using h))
      chain_ne := List.isChain_map_of_isChain g (fun a b hab h => hab h) w.chain_ne }
  have hW_inj : Function.Injective W := by
    intro a b hab
    have h1 : a.toList.map g = b.toList.map g := congrArg Monoid.CoprodI.Word.toList hab
    exact Monoid.CoprodI.Word.ext ((List.map_injective_iff.mpr hg) h1)
  have hWprod : ∀ w : Monoid.CoprodI.Word M, Monoid.CoprodI.lift fi (w.prod) = (W w).prod := by
    intro w
    rw [Monoid.CoprodI.Word.prod, map_list_prod]
    show List.prod ((w.toList.map (fun l => Monoid.CoprodI.of l.2)).map
          (Monoid.CoprodI.lift fi)) =
      List.prod ((w.toList.map g).map (fun l => Monoid.CoprodI.of l.2))
    rw [List.map_map, List.map_map]
    refine congrArg List.prod ?_
    apply List.map_congr_left
    intro l hl
    simp only [Function.comp_apply, g]
    rw [Monoid.CoprodI.lift_of]
    rfl
  have hprod_inj : Function.Injective (Monoid.CoprodI.Word.prod (M := M')) := by
    intro a b h
    exact (Monoid.CoprodI.Word.equiv.symm).injective h
  intro x y hxy
  have hx : Monoid.CoprodI.Word.prod (Monoid.CoprodI.Word.equiv x) = x :=
    Monoid.CoprodI.Word.equiv.left_inv x
  have hy : Monoid.CoprodI.Word.prod (Monoid.CoprodI.Word.equiv y) = y :=
    Monoid.CoprodI.Word.equiv.left_inv y
  have h3 : W (Monoid.CoprodI.Word.equiv x) = W (Monoid.CoprodI.Word.equiv y) := by
    apply hprod_inj
    rw [← hWprod, ← hWprod, hx, hy, hxy]
  rw [← hx, ← hy, hW_inj h3]

theorem presentedGroupEquivCoprodI {γ : Type u} (Z : Set γ) (sz : FreeGroup Z)
    (s : FreeGroup γ) (hs : FreeGroup.map (Subtype.val : Z → γ) sz = s) :
    ∃ Φ : PresentedGroup ({s} : Set (FreeGroup γ)) ≃*
        Monoid.CoprodI (CoprodTwoFam (PresentedGroup ({sz} : Set (FreeGroup Z)))
          (FreeGroup {a : γ // a ∉ Z})),
      (∀ z : Z, Φ (PresentedGroup.of (z : γ)) =
          Monoid.CoprodI.of (i := true) (PresentedGroup.of z)) ∧
      (∀ (a : γ) (ha : a ∉ Z), Φ (PresentedGroup.of a) =
          Monoid.CoprodI.of (i := false) (FreeGroup.of ⟨a, ha⟩)) := by
  classical
  let MM : Type u := PresentedGroup ({sz} : Set (FreeGroup Z))
  let NN : Type u := FreeGroup {a : γ // a ∉ Z}
  let GG : Bool → Type u := CoprodTwoFam MM NN
  let PP : Type u := PresentedGroup ({s} : Set (FreeGroup γ))
  let σ : FreeGroup Z →* FreeGroup γ := FreeGroup.map (Subtype.val : Z → γ)
  let τ : NN →* FreeGroup γ := FreeGroup.map (fun b : {a : γ // a ∉ Z} => (b : γ))
  have hst : Set.MapsTo σ ({sz} : Set (FreeGroup Z)) ({s} : Set (FreeGroup γ)) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx ⊢
    rw [hx]
    exact hs
  let φ₁ : MM →* PP := PresentedGroup.map σ hst
  let φ₂ : NN →* PP := (PresentedGroup.mk ({s} : Set (FreeGroup γ))).comp τ
  let fi : ∀ b : Bool, GG b →* PP := fun b =>
    Bool.rec (motive := fun b => GG b →* PP) φ₂ φ₁ b
  have hfi_true : fi true = φ₁ := rfl
  have hfi_false : fi false = φ₂ := rfl
  let φ : Monoid.CoprodI GG →* PP := Monoid.CoprodI.lift fi
  let θ' : γ → Monoid.CoprodI GG := fun a =>
    if h : a ∈ Z then Monoid.CoprodI.of (i := true) (PresentedGroup.of (⟨a, h⟩ : Z))
    else Monoid.CoprodI.of (i := false) (FreeGroup.of (⟨a, h⟩ : {a : γ // a ∉ Z}))
  have hφ₁_of : ∀ x : Z, φ₁ (PresentedGroup.of x) = PresentedGroup.of (x : γ) := by
    intro x
    change PresentedGroup.map σ hst (PresentedGroup.of x) = PresentedGroup.of (x : γ)
    rw [show PresentedGroup.map σ hst (PresentedGroup.of x) =
        PresentedGroup.mk ({s} : Set (FreeGroup γ)) (σ (FreeGroup.of x)) from rfl]
    rw [show σ (FreeGroup.of x) = FreeGroup.of (x : γ) from FreeGroup.map.of]
    rfl
  have hφ₂_of : ∀ y : {a : γ // a ∉ Z}, φ₂ (FreeGroup.of y) = PresentedGroup.of (y : γ) := by
    intro y
    change (PresentedGroup.mk ({s} : Set (FreeGroup γ))).comp τ (FreeGroup.of y) =
      PresentedGroup.of (y : γ)
    rw [MonoidHom.comp_apply, show τ (FreeGroup.of y) = FreeGroup.of (y : γ) from FreeGroup.map.of]
    rfl
  have hθσ : (FreeGroup.lift θ').comp (FreeGroup.map (Subtype.val : Z → γ)) =
      (Monoid.CoprodI.of (i := true)).comp (PresentedGroup.mk ({sz} : Set (FreeGroup Z))) := by
    refine FreeGroup.ext_hom _ _ fun z => ?_
    show FreeGroup.lift θ' (FreeGroup.map (Subtype.val : Z → γ) (FreeGroup.of z)) =
      Monoid.CoprodI.of (i := true) (PresentedGroup.mk ({sz} : Set (FreeGroup Z)) (FreeGroup.of z))
    rw [show FreeGroup.map (Subtype.val : Z → γ) (FreeGroup.of z) = FreeGroup.of (z : γ) from
      FreeGroup.map.of]
    rw [FreeGroup.lift_apply_of]
    rw [show θ' (z : γ) = Monoid.CoprodI.of (i := true) (PresentedGroup.of z) from dif_pos z.2]
    rfl
  have hθs : FreeGroup.lift θ' s = 1 := by
    rw [← hs, ← MonoidHom.comp_apply, hθσ]
    rw [MonoidHom.comp_apply, PresentedGroup.one_of_mem (Set.mem_singleton sz), map_one]
  let ψ : PP →* Monoid.CoprodI GG :=
    PresentedGroup.toGroup (f := θ') (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hθs)
  have hψ_of : ∀ x : γ, ψ (PresentedGroup.of x) = θ' x := fun x => PresentedGroup.toGroup.of _
  have hφψ : φ.comp ψ = MonoidHom.id PP := by
    refine PresentedGroup.ext fun a => ?_
    show φ (ψ (PresentedGroup.of a)) = PresentedGroup.of a
    rw [hψ_of]
    by_cases ha : a ∈ Z
    · rw [show θ' a = Monoid.CoprodI.of (i := true) (PresentedGroup.of (⟨a, ha⟩ : Z)) from
        dif_pos ha]
      rw [show φ (Monoid.CoprodI.of (i := true) (PresentedGroup.of (⟨a, ha⟩ : Z))) =
        φ₁ (PresentedGroup.of (⟨a, ha⟩ : Z)) from by
          rw [show φ = Monoid.CoprodI.lift fi from rfl,
            show Monoid.CoprodI.lift fi (Monoid.CoprodI.of (i := true) (PresentedGroup.of (⟨a,ha⟩ : Z)))
              = fi true (PresentedGroup.of (⟨a, ha⟩ : Z)) from Monoid.CoprodI.lift_of fi _,
            hfi_true]]
      rw [hφ₁_of]
    · rw [show θ' a = Monoid.CoprodI.of (i := false)
        (FreeGroup.of (⟨a, ha⟩ : {a : γ // a ∉ Z})) from dif_neg ha]
      rw [show φ (Monoid.CoprodI.of (i := false)
          (FreeGroup.of (⟨a, ha⟩ : {a : γ // a ∉ Z}))) =
        φ₂ (FreeGroup.of (⟨a, ha⟩ : {a : γ // a ∉ Z})) from by
          rw [show φ = Monoid.CoprodI.lift fi from rfl,
            show Monoid.CoprodI.lift fi (Monoid.CoprodI.of (i := false)
                (FreeGroup.of (⟨a, ha⟩ : {a : γ // a ∉ Z})))
              = fi false (FreeGroup.of (⟨a, ha⟩ : {a : γ // a ∉ Z})) from
                Monoid.CoprodI.lift_of fi _,
            hfi_false]]
      rw [hφ₂_of]
  have hψφ : ψ.comp φ = MonoidHom.id (Monoid.CoprodI GG) := by
    refine Monoid.CoprodI.ext_hom _ _ fun b => ?_
    cases b with
    | true =>
      rw [MonoidHom.comp_assoc, MonoidHom.id_comp]
      rw [show φ.comp (Monoid.CoprodI.of (i := true)) = φ₁ from by
        rw [show φ = Monoid.CoprodI.lift fi from rfl,
          Monoid.CoprodI.lift_comp_of fi true, hfi_true]]
      refine PresentedGroup.ext fun z => ?_
      show ψ (φ₁ (PresentedGroup.of z)) = Monoid.CoprodI.of (i := true) (PresentedGroup.of z)
      rw [hφ₁_of, hψ_of]
      rw [show θ' (z : γ) =
        Monoid.CoprodI.of (i := true) (PresentedGroup.of (⟨(z : γ), z.2⟩ : Z)) from dif_pos z.2]
    | false =>
      rw [MonoidHom.comp_assoc, MonoidHom.id_comp]
      rw [show φ.comp (Monoid.CoprodI.of (i := false)) = φ₂ from by
        rw [show φ = Monoid.CoprodI.lift fi from rfl,
          Monoid.CoprodI.lift_comp_of fi false, hfi_false]]
      refine FreeGroup.ext_hom _ _ fun y => ?_
      show ψ (φ₂ (FreeGroup.of y)) = Monoid.CoprodI.of (i := false) (FreeGroup.of y)
      rw [hφ₂_of, hψ_of]
      rw [show θ' (y : γ) = Monoid.CoprodI.of (i := false)
        (FreeGroup.of (⟨(y : γ), y.2⟩ : {a : γ // a ∉ Z})) from dif_neg y.2]
  refine ⟨MonoidHom.toMulEquiv ψ φ hφψ hψφ, ?_, ?_⟩
  · intro z
    show ψ (PresentedGroup.of (z : γ)) = Monoid.CoprodI.of (i := true) (PresentedGroup.of z)
    rw [hψ_of]
    rw [show θ' (z : γ) =
      Monoid.CoprodI.of (i := true) (PresentedGroup.of (⟨(z : γ), z.2⟩ : Z)) from dif_pos z.2]
  · intro a ha
    show ψ (PresentedGroup.of a) = Monoid.CoprodI.of (i := false) (FreeGroup.of ⟨a, ha⟩)
    rw [hψ_of]
    rw [show θ' a = Monoid.CoprodI.of (i := false)
      (FreeGroup.of (⟨a, ha⟩ : {a : γ // a ∉ Z})) from dif_neg ha]

theorem freiheitssatzAt_of_restrict {γ : Type u} (s : FreeGroup γ) (Z : Set γ)
    (sz : FreeGroup Z) (hs : FreeGroup.map (Subtype.val : Z → γ) sz = s)
    (h : FreiheitssatzAt sz) : FreiheitssatzAt s := by
  classical
  obtain ⟨Φ, hΦtrue, hΦfalse⟩ :=
    presentedGroupEquivCoprodI Z sz s hs
  intro hcyc T hT
  have hcyc' : IsCyclicallyReducedRelator sz :=
    isCyclicallyReducedRelator_of_map_subtype_val hs hcyc
  have hTz : sz ∉ Subgroup.closure (FreeGroup.of '' {z : Z | (z : γ) ∈ T}) :=
    notMem_closure_of_map_subtype_val hs hT
  have hj : Function.Injective (presentedGroupMap sz {z : Z | (z : γ) ∈ T}) := h hcyc' _ hTz
  let Tz : Set Z := {z : Z | (z : γ) ∈ T}
  let Tn : Set T := {a : T | (a : γ) ∉ Z}
  let X : Bool → Type u := CoprodTwoFam ↥Tz ↥Tn
  let MM : Type u := PresentedGroup ({sz} : Set (FreeGroup Z))
  let NN : Type u := FreeGroup {a : γ // a ∉ Z}
  let GG : Bool → Type u := CoprodTwoFam MM NN
  let incN : ↥Tn → {a : γ // a ∉ Z} := fun a => ⟨(a.1 : γ), a.2⟩
  have hincN : Function.Injective incN := by
    intro a b hab
    have h1 : ((a.1 : T) : γ) = ((b.1 : T) : γ) :=
      congrArg (fun x : {a : γ // a ∉ Z} => (x : γ)) hab
    exact Subtype.ext (Subtype.ext h1)
  let F : ∀ b, FreeGroup (X b) →* GG b :=
    Bool.rec (motive := fun b => FreeGroup (X b) →* GG b)
      (FreeGroup.map incN) (presentedGroupMap sz Tz)
  have hF_true : F true = presentedGroupMap sz Tz := rfl
  have hF_false : F false = FreeGroup.map incN := rfl
  have hF : ∀ b, Function.Injective (F b) := by
    intro b
    cases b with
    | true => exact hj
    | false => exact FreeGroup.map_injective hincN
  obtain ⟨e, he_true, he_false⟩ := sigmaComplementEquiv T Z
  obtain ⟨κ, hκ⟩ := freeGroupEquivCoprodI e
  set L := Monoid.CoprodI.lift (fun b => (Monoid.CoprodI.of (i := b)).comp (F b)) with hL
  have hL_inj : Function.Injective L := coprodILiftInjectiveBool F hF
  have hcompat : Φ.toMonoidHom.comp (presentedGroupMap s T) = L.comp κ.toMonoidHom := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    show Φ (presentedGroupMap s T (FreeGroup.of a)) = L (κ (FreeGroup.of a))
    rw [presentedGroupMap_of_apply]
    by_cases ha : (a : γ) ∈ Z
    · rw [hΦtrue ⟨(a : γ), ha⟩, hκ a, he_true a ha]
      rw [hL, Monoid.CoprodI.lift_of, MonoidHom.comp_apply, hF_true, presentedGroupMap_of_apply]
    · rw [hΦfalse (a : γ) ha, hκ a, he_false a ha]
      rw [hL, Monoid.CoprodI.lift_of, MonoidHom.comp_apply, hF_false, FreeGroup.map.of]
  intro x y hxy
  have h1 : Φ (presentedGroupMap s T x) = Φ (presentedGroupMap s T y) := by rw [hxy]
  have hx' : L (κ x) = L (κ y) := by
    have h2 : Φ (presentedGroupMap s T x) = L (κ x) := by
      show (Φ.toMonoidHom.comp (presentedGroupMap s T)) x = (L.comp κ.toMonoidHom) x
      exact DFunLike.congr_fun hcompat x
    have h3 : Φ (presentedGroupMap s T y) = L (κ y) := by
      show (Φ.toMonoidHom.comp (presentedGroupMap s T)) y = (L.comp κ.toMonoidHom) y
      exact DFunLike.congr_fun hcompat y
    rw [← h2, ← h3]
    exact h1
  exact κ.injective (hL_inj hx')


theorem exists_hnnStepCore {α : Type u} [DecidableEq α] (r : FreeGroup α) (t x : α)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (ht : t ∈ Work.OROneRel.relatorLetters r) (hx : x ∈ Work.OROneRel.relatorLetters r)
    (htx : x ≠ t) (ht0 : Work.OROneRel.sigma t r = 1)
    (hhead : r.toWord.head? = some (x, true) ∨ r.toWord.head? = some (x, false))
    (IH : Work.OROneRel.FreiheitssatzBelow
      (Work.OROneRel.relatorNorm (Work.OROneRel.magRewRel t r) + 1)) :
    ∃ i j : ℤ,
      (⟨x, htx⟩, i) ∈ Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t r) ∧
      (⟨x, htx⟩, j) ∈ Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t r) ∧
      (∀ k : ℤ, (⟨x, htx⟩, k) ∈ Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t r) →
        i ≤ k ∧ k ≤ j) ∧
      i ≤ 0 ∧ 0 ≤ j ∧ Nonempty (Work.OROneRel.HNNStepCore r t x i j) := by
  obtain ⟨i, j, hi, hj, hb, hi0, h0j⟩ := hnn_decoration_bounds r t x htx hhead
  exact ⟨i, j, hi, hj, hb, hi0, h0j,
    hnnStepCore_of_bounds r t x hcyc htx ht0 i j hi hj hb hi0 h0j
      (hnn_freiheitssatzAt_magRewRel r t IH freiheitssatzAt_equiv freiheitssatzAt_of_restrict)⟩

end Work.OROneRel
