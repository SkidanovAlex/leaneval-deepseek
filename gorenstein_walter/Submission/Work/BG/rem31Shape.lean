import Mathlib
import Submission.Work.BG.r31Aux
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.rem31Structure
import Submission.Work.BG.indexTwoCliffordRestrict
import Submission.Work.BG.restrictEqOfInvariantConstituent
import Submission.Work.BG.restrictConjBySubgroupOf
import Submission.Work.BG.conjByEqSelfOfSupZpowersEqTop
import Submission.Work.BG.indexTwoMackey
import Submission.Work.BG.indexTwoInduceIrreducible
import Submission.Work.BG.indexTwoInduceNormTwo
import Submission.Work.BG.CharBridge
import Submission.OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import Submission.Work.BG.s02_assemblyCore
/-!
# `Work.BG.rem31Shape` — Bender–Glauberman, Remark 3.1 (the shape of `ν|_U`)

For a finite group `X = H_0 = U S_0` with `U` normal, `H_0/U` cyclic and `S_0' = ⟨c^2⟩` central
in `H_0` (the §3 hypothesis, `Work.GW2.C16.Sec3Hyp`), every irreducible character `ν` of `H_0`
restricts to `U` as either a single irreducible character `a` (then `|Λν| = |H_0 : U|`) or as a
sum `a + a^c` of two distinct irreducible characters of equal degree (then
`2 |Λν| = |H_0 : U|`).

The proof splits off the subgroup `W = U⟨c^2⟩` of index two in `H_0` (where `c` generates
`H_0/U`, `Work.BG.rem31Structure`), takes a constituent `σ` of `ν|_W` and applies index-two
Clifford theory (`Work.BG.indexTwoCliffordRestrict`) to `ν|_W`; the constituent `a` of `σ|_U` is
then `W`-invariant, so multiplicity one in `σ|_U` follows from
`Work.BG.restrictEqOfInvariantConstituent`.  The two cases `σ^c = σ` and `σ^c ≠ σ` give the two
alternatives, and the orbit sizes follow from the orthogonality relation `Work.BG.rem31Orth`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

set_option maxHeartbeats 800000

section Main

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

theorem rem31shape_aux (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Rem31ShapeProp D C := by
  intro hDC hS3 ν hν
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype ↥(Uin C) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(Uin C) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨c, hcsup, hccent, hcinfU, hcinfU2, hcindex, hcnotmem⟩ := rem31Structure D C hDC hS3
  set W : Subgroup ↥C.P.H0 := Uin C ⊔ Subgroup.zpowers (c ^ 2) with hWdef
  have hUW : Uin C ≤ W := le_sup_left
  have hWindex : W.index = 2 := hcindex
  haveI : W.Normal := Subgroup.normal_of_index_eq_two hWindex
  haveI : ((Uin C).subgroupOf W).Normal := inferInstance
  haveI : Fintype ↥W := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥W : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype ↥((Uin C).subgroupOf W) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥((Uin C).subgroupOf W) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hc2mem : c ^ 2 ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  -- the constituent σ of ν|_W and a₀ of σ|_U
  obtain ⟨σ, hσover⟩ := IrreducibleCharacter.exists_liesOver (G := ↥C.P.H0) W ⟨ν, hν⟩
  obtain ⟨a₀, ha₀over⟩ := IrreducibleCharacter.exists_liesOver (G := ↥W)
    ((Uin C).subgroupOf W) σ
  -- generators of `↥W`
  have hgenWsup : (Uin C).subgroupOf W ⊔
      Subgroup.zpowers (⟨c ^ 2, hc2mem⟩ : ↥W) = ⊤ := by
    have h1 : (Uin C ⊔ Subgroup.zpowers (c ^ 2)).subgroupOf W = ⊤ := by
      rw [show Uin C ⊔ Subgroup.zpowers (c ^ 2) = W from rfl, Subgroup.subgroupOf_self]
    rw [Subgroup.subgroupOf_sup (le_sup_left : Uin C ≤ W)
      (le_sup_right : Subgroup.zpowers (c ^ 2) ≤ W)] at h1
    have h2 : (Subgroup.zpowers (c ^ 2)).subgroupOf W
        = Subgroup.zpowers (⟨c ^ 2, hc2mem⟩ : ↥W) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, by rw [← hk, Subgroup.coe_zpow]⟩
    rwa [h2] at h1
  have hgenW : Subgroup.closure (((Uin C).subgroupOf W : Set ↥W) ∪ {⟨c ^ 2, hc2mem⟩}) = ⊤ :=
    closure_union_singleton_eq_top _ _ hgenWsup
  -- a₀ is `W`-invariant
  have hc2fix : ClassFunction.conjBy (G := ↥W) (H := (Uin C).subgroupOf W)
      (⟨c ^ 2, hc2mem⟩ : ↥W) (a₀ : ClassFunction ↥((Uin C).subgroupOf W) ℂ)
      = (a₀ : ClassFunction ↥((Uin C).subgroupOf W) ℂ) := by
    ext x
    rw [ClassFunction.conjBy_apply]
    refine congrArg (fun y : ↥((Uin C).subgroupOf W) =>
      (a₀ : ClassFunction ↥((Uin C).subgroupOf W) ℂ) y) ?_
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hccent]
    group
  have ha₀inv : ∀ g : ↥W, IrreducibleCharacter.conjBy (G := ↥W) g a₀ = a₀ := fun g => by
    apply IrreducibleCharacter.ext
    exact conjByEqSelfOfSupZpowersEqTop ((Uin C).subgroupOf W) (⟨c ^ 2, hc2mem⟩ : ↥W)
      hgenWsup _ hc2fix g
  have hσres : ClassFunction.restrict ((Uin C).subgroupOf W) (σ : ClassFunction ↥W ℂ)
      = (a₀ : ClassFunction ↥((Uin C).subgroupOf W) ℂ) :=
    restrictEqOfInvariantConstituent (G := ↥W) (H := (Uin C).subgroupOf W)
      ⟨c ^ 2, hc2mem⟩ hgenW σ a₀ ha₀over ha₀inv
  -- the transport iso and `a`
  let eU := Subgroup.subgroupOfEquivOfLe hUW
  let a : ClassFunction ↥(Uin C) ℂ :=
    ClassFunction.compHom eU.symm.toMonoidHom (a₀ : ClassFunction ↥((Uin C).subgroupOf W) ℂ)
  have ha_irr : IsIrreducibleCharacter a :=
    IsIrreducibleCharacter.compHom_of_surjective eU.symm.surjective a₀.isIrreducible
  have ha_eq : ClassFunction.compHom eU.toMonoidHom a
      = (a₀ : ClassFunction ↥((Uin C).subgroupOf W) ℂ) := by
    show ClassFunction.compHom eU.toMonoidHom
      (ClassFunction.compHom eU.symm.toMonoidHom _) = _
    rw [compHom_compHom]
    have hid : eU.symm.toMonoidHom.comp eU.toMonoidHom
        = MonoidHom.id ↥((Uin C).subgroupOf W) := by
      ext x
      simp [eU]
    rw [hid, compHom_id]
  have hI2 := indexTwoCliffordRestrict (H := W) hWindex c hcnotmem σ ⟨ν, hν⟩ hσover
  -- Rem31Orth input
  have horth : ClassFunction.inner (ClassFunction.restrict (Uin C) ν)
      (ClassFunction.restrict (Uin C) ν) = (D.n : ℂ) / ((lamOrbit C ν).ncard : ℂ) :=
    ((rem31Orth D C) hDC ν ν hν hν).1 (s02c_LamEquiv_refl C ν)
  have hfin : (lamOrbit C ν).Finite := by
    rw [← orbit_eq_lamOrbit C ν]
    exact Set.finite_range fun β : lamDual C => β • ν
  have hKne : ((lamOrbit C ν).ncard : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Set.ncard_ne_zero_of_mem (s02c_LamEquiv_refl C ν) hfin)
  by_cases hσinv : ClassFunction.conjBy (G := ↥C.P.H0) (H := W) c (σ : ClassFunction ↥W ℂ)
      = (σ : ClassFunction ↥W ℂ)
  · -- Case (i): σ is X-invariant
    have hνW : ClassFunction.restrict W (ν : ClassFunction ↥C.P.H0 ℂ)
        = (σ : ClassFunction ↥W ℂ) := hI2.1 hσinv
    have hνU : ClassFunction.restrict (Uin C) ν = a := by
      refine compHom_injective eU.toMonoidHom eU.surjective ?_
      calc ClassFunction.compHom eU.toMonoidHom (ClassFunction.restrict (Uin C) ν)
          = ClassFunction.restrict ((Uin C).subgroupOf W) (ClassFunction.restrict W ν) :=
            (ClassFunction.restrict_subgroupOf_restrict hUW ν).symm
        _ = ClassFunction.restrict ((Uin C).subgroupOf W) (σ : ClassFunction ↥W ℂ) := by
            rw [hνW]
        _ = ClassFunction.compHom eU.toMonoidHom a := hσres ▸ ha_eq.symm
    refine ⟨a, ha_irr, Or.inl ⟨hνU, ?_⟩⟩
    have hinner : ClassFunction.inner (ClassFunction.restrict (Uin C) ν)
        (ClassFunction.restrict (Uin C) ν) = 1 := by
      rw [hνU]
      exact inner_self_eq_one a ha_irr
    have hcast : ((lamOrbit C ν).ncard : ℂ) = (D.n : ℂ) := by
      rw [hinner] at horth
      rw [eq_div_iff hKne] at horth
      simpa using horth
    exact Nat.cast_injective hcast
  · -- Case (ii): σ is not X-invariant
    have hνW : ClassFunction.restrict W (ν : ClassFunction ↥C.P.H0 ℂ)
        = (σ : ClassFunction ↥W ℂ)
          + ClassFunction.conjBy (G := ↥C.P.H0) (H := W) c (σ : ClassFunction ↥W ℂ) :=
      hI2.2 hσinv
    have hconjU : ClassFunction.restrict ((Uin C).subgroupOf W)
          (ClassFunction.conjBy (G := ↥C.P.H0) (H := W) c (σ : ClassFunction ↥W ℂ))
        = ClassFunction.compHom eU.toMonoidHom
            (ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) c a) := by
      have hmid : ClassFunction.compHom eU.symm.toMonoidHom
          (ClassFunction.restrict ((Uin C).subgroupOf W) (σ : ClassFunction ↥W ℂ)) = a := by
        rw [hσres]
      rw [restrictConjBySubgroupOf hUW c (σ : ClassFunction ↥W ℂ), hmid]
    have hνU : ClassFunction.restrict (Uin C) ν
        = a + ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) c a := by
      refine compHom_injective eU.toMonoidHom eU.surjective ?_
      calc ClassFunction.compHom eU.toMonoidHom (ClassFunction.restrict (Uin C) ν)
          = ClassFunction.restrict ((Uin C).subgroupOf W) (ClassFunction.restrict W ν) :=
            (ClassFunction.restrict_subgroupOf_restrict hUW ν).symm
        _ = ClassFunction.restrict ((Uin C).subgroupOf W) (σ : ClassFunction ↥W ℂ)
              + ClassFunction.restrict ((Uin C).subgroupOf W)
                  (ClassFunction.conjBy (G := ↥C.P.H0) (H := W) c (σ : ClassFunction ↥W ℂ)) := by
            rw [hνW, restrict_add]
        _ = ClassFunction.compHom eU.toMonoidHom a
              + ClassFunction.compHom eU.toMonoidHom
                  (ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) c a) := by
            rw [hconjU, hσres, ← ha_eq]
        _ = ClassFunction.compHom eU.toMonoidHom
              (a + ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) c a) :=
            (compHom_add eU.toMonoidHom a _).symm
    have hane : a ≠ ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) c a := by
      intro hcontra
      have haXinv : ∀ g : ↥C.P.H0,
          IrreducibleCharacter.conjBy (G := ↥C.P.H0) (H := Uin C) g ⟨a, ha_irr⟩
            = ⟨a, ha_irr⟩ := fun g => by
        apply IrreducibleCharacter.ext
        exact conjByEqSelfOfSupZpowersEqTop (Uin C) c hcsup a hcontra.symm g
      have hover : IrreducibleCharacter.LiesOver (Uin C) ⟨ν, hν⟩ ⟨a, ha_irr⟩ := by
        rw [IrreducibleCharacter.liesOver_iff, ClassFunction.restrictionMultiplicity_def, hνU]
        exact inner_add_self_ne_zero a (ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) c a)
          ha_irr (ClassFunction.IsIrreducibleCharacter.conjBy (H := Uin C) ha_irr c)
      have hPD : ClassFunction.restrict (Uin C) ν = a :=
        restrictEqOfInvariantConstituent (G := ↥C.P.H0) (H := Uin C) c
          (closure_union_singleton_eq_top (Uin C) c hcsup)
          ⟨ν, hν⟩ ⟨a, ha_irr⟩ hover haXinv
      have hkey : a + a = a := by
        rw [← hcontra] at hνU
        rw [← hνU, hPD]
      have hazero : a = 0 := add_left_cancel (hkey.trans (add_zero a).symm)
      have ha1 : a (1 : ↥(Uin C)) ≠ 0 := by
        obtain ⟨d, hd, hdeq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ⟨a, ha_irr⟩
        rw [hdeq]
        exact_mod_cast hd.ne'
      exact ha1 (by rw [hazero]; rfl)
    refine ⟨a, ha_irr, Or.inr ⟨ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) c a,
      ClassFunction.IsIrreducibleCharacter.conjBy (H := Uin C) ha_irr c,
      (fun h => hane h.symm), ?_, hνU, ?_⟩⟩
    · rw [← IrreducibleCharacter.coe_conjBy (G := ↥C.P.H0) (H := Uin C) c ⟨a, ha_irr⟩]
      exact conjBy_apply_one (G := ↥C.P.H0) (H := Uin C) c ⟨a, ha_irr⟩
    · have hinner : ClassFunction.inner (ClassFunction.restrict (Uin C) ν)
          (ClassFunction.restrict (Uin C) ν) = 2 := by
        rw [hνU]
        refine inner_add_add_eq_two a (ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) c a)
          ha_irr (ClassFunction.IsIrreducibleCharacter.conjBy (H := Uin C) ha_irr c) ?_
        intro hh
        exact hane (congrArg (fun z : IrreducibleCharacter ↥(Uin C) =>
          (z : ClassFunction ↥(Uin C) ℂ)) hh)
      rw [hinner] at horth
      rw [eq_div_iff hKne] at horth
      have hcast : 2 * (lamOrbit C ν).ncard = D.n := by
        apply Nat.cast_injective (R := ℂ)
        push_cast
        simpa [mul_comm] using horth
      exact hcast

end Main



open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **Bender–Glauberman Remark 3.1** (BG 1981, p. 208): the shape of `ν|_U`. -/
theorem rem31Shape {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Rem31ShapeProp D C :=
  rem31shape_aux D C

end Work.BG
