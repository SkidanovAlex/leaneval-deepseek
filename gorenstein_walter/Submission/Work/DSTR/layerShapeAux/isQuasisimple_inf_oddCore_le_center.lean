import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.ASM.oddCore_odd

set_option linter.style.haveILetI false

namespace Work.DSTR.layerShapeAux

/-- **Feit–Thompson for finite groups in an arbitrary universe.** `Work.GW2.FeitThompsonProp` is
stated (like every other `Work.GW2` `Prop`) for groups in `Type`, while the lemmas below live in
`Type*`.  To apply it we push a finite group `α` into `Type` through its regular representation:
`α` embeds (`MulAction.toPermHom`) into `Equiv.Perm α`, which is identified with the `Type`-valued
group `Equiv.Perm (Fin (Nat.card α))` via `Equiv.permCongrHom`; the range is a finite group of the
same (odd) order living in `Type`, so `hFT` applies to it, and solvability descends back to `α`
along the resulting `MulEquiv`. -/
theorem isSolvable_of_odd_of_feitThompson {α : Type*} [Group α] [Finite α]
    (hFT : Work.GW2.FeitThompsonProp) (hodd : Odd (Nat.card α)) : Group.IsSolvable α := by
  classical
  letI := Fintype.ofFinite α
  let φ : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let e : Equiv.Perm α ≃* Equiv.Perm (Fin (Fintype.card α)) := Equiv.permCongrHom φ
  let ρ : α →* Equiv.Perm α := MulAction.toPermHom α α
  let ψ : α →* Equiv.Perm (Fin (Fintype.card α)) := e.toMonoidHom.comp ρ
  have hρinj : Function.Injective ρ := by
    intro a b h
    have h1 : (ρ a) 1 = (ρ b) 1 := by rw [h]
    simpa [ρ, MulAction.toPermHom_apply, MulAction.toPerm_apply, smul_eq_mul] using h1
  have hψinj : Function.Injective ψ := by
    intro a b h
    exact hρinj (e.injective (by simpa [ψ] using h))
  have hbij : Function.Bijective ψ.rangeRestrict :=
    ⟨fun a b h => hψinj (by simpa using congrArg Subtype.val h),
     ψ.rangeRestrict_surjective⟩
  let e3 : α ≃* ↥ψ.range := MulEquiv.ofBijective ψ.rangeRestrict hbij
  have hcard : Nat.card α = Nat.card ↥ψ.range := Nat.card_congr e3.toEquiv
  haveI : Group.IsSolvable ↥ψ.range := hFT ↥ψ.range (hcard ▸ hodd)
  exact Group.isSolvable_of_surjective (f := e3.symm.toMonoidHom) e3.symm.surjective

/-- **Piece of DS7 (`Work.DSTR.layerShape`).** `E ∩ O(X) ≤ Z(E)` for a quasisimple subgroup `E`
of a finite group `X` (`O(X)` is `Work.GW2.oddCore X`, the largest normal odd-order subgroup).

Route: `M := E ⊓ Work.GW2.oddCore X` is normal in `E` (the odd core is normal in `X`); let
`ν : ↥E →* (↥E ⧸ Subgroup.center ↥E)` be the quotient map and
`μ := ν.comp (Subgroup.inclusion inf_le_left) : ↥M →* (↥E ⧸ Subgroup.center ↥E)`. Since the target
is simple (`hEq.2`) and `μ.range` is normal in it, `μ.range = ⊥` or `⊤`. In case `⊥`, every element
of `M` is central in `E` — that is the goal. In case `⊤`, the simple group `↥E ⧸ Z(E)` is a
quotient of `↥M`, which has odd order because `Nat.card ↥M ∣ Nat.card (Work.GW2.oddCore X)` and
`Work.ASM.oddCore_odd` (import `Submission.Work.ASM.oddCore_odd`), so is solvable by `hFT`; then
`↥E` is solvable (`Group.isSolvable_of_subgroup_quotient` with `Z(E)` abelian), while
`commutator ↥E = ⊤` (transport `hEq.1 : ⁅E,E⁆ = E` along `E.subtype` using
`Subgroup.map_commutator`) and `↥E` is nontrivial, contradicting
`Group.IsSolvable.commutator_lt_top_of_nontrivial`. -/
theorem isQuasisimple_inf_oddCore_le_center {X : Type*} [Group X] [Finite X]
    (hFT : Work.GW2.FeitThompsonProp) {E : Subgroup X} (hEq : Work.GW2.IsQuasisimple E) :
    E ⊓ Work.GW2.oddCore X ≤ (Subgroup.center ↥E).map E.subtype := by
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxE, hxO⟩ := hx
  haveI : (Work.GW2.oddCore X).Normal := Work.GW2.oddCore_normal X
  -- `M.subgroupOf E` is normal in `↥E`
  have hMK : ((E ⊓ Work.GW2.oddCore X).subgroupOf E).Normal := by
    rw [Subgroup.inf_subgroupOf_left]
    exact (Work.GW2.oddCore_normal X).subgroupOf E
  -- the composite `μ : ↥M →* ↥E ⧸ Z(E)`
  let μ : ↥(E ⊓ Work.GW2.oddCore X) →* (↥E ⧸ Subgroup.center ↥E) :=
    (QuotientGroup.mk' (Subgroup.center ↥E)).comp
      (Subgroup.inclusion (inf_le_left : E ⊓ Work.GW2.oddCore X ≤ E))
  -- its range is normal in the simple quotient
  have hμran : μ.range =
      ((E ⊓ Work.GW2.oddCore X).subgroupOf E).map (QuotientGroup.mk' (Subgroup.center ↥E)) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hμnorm : μ.range.Normal := by
    rw [hμran]
    exact hMK.map _ (QuotientGroup.mk'_surjective _)
  haveI := hEq.2
  have hxM : x ∈ E ⊓ Work.GW2.oddCore X := Subgroup.mem_inf.mpr ⟨hxE, hxO⟩
  have hcase : μ.range = ⊥ ∨ μ.range = ⊤ := by
    haveI := hμnorm
    exact Subgroup.Normal.eq_bot_or_eq_top μ.range
  rcases hcase with hbot | htop
  · -- `μ.range = ⊥`: every element of `M` is central in `E`
    have hzero : μ ⟨x, hxM⟩ = 1 := by
      have : μ ⟨x, hxM⟩ ∈ (⊥ : Subgroup (↥E ⧸ Subgroup.center ↥E)) := by
        rw [← hbot]
        exact MonoidHom.mem_range.mpr ⟨⟨x, hxM⟩, rfl⟩
      simpa using this
    have hincl :
        (Subgroup.inclusion (inf_le_left : E ⊓ Work.GW2.oddCore X ≤ E)) ⟨x, hxM⟩ =
          ⟨x, hxE⟩ :=
      Subtype.ext rfl
    have hk : (QuotientGroup.mk' (Subgroup.center ↥E)) ⟨x, hxE⟩ = 1 := by
      have h := hzero
      simp only [μ, MonoidHom.comp_apply] at h
      rwa [hincl] at h
    have hmem : ⟨x, hxE⟩ ∈ Subgroup.center ↥E := by
      rw [QuotientGroup.mk'_apply] at hk
      exact (QuotientGroup.eq_one_iff _).mp hk
    exact Subgroup.mem_map.mpr ⟨⟨x, hxE⟩, hmem, rfl⟩
  · -- `μ.range = ⊤`: the simple quotient is a quotient of the odd-order group `↥M`, contradiction
    have hsurj : Function.Surjective μ := MonoidHom.range_eq_top.mp htop
    haveI hsolM : Group.IsSolvable ↥(E ⊓ Work.GW2.oddCore X) :=
      isSolvable_of_odd_of_feitThompson hFT
        (Odd.of_dvd_nat (Work.ASM.oddCore_odd X)
          (Subgroup.card_dvd_of_le
            (inf_le_right : E ⊓ Work.GW2.oddCore X ≤ Work.GW2.oddCore X)))
    haveI hsolQ : Group.IsSolvable (↥E ⧸ Subgroup.center ↥E) :=
      Group.isSolvable_of_surjective hsurj
    haveI hsolE : Group.IsSolvable ↥E :=
      Group.isSolvable_of_subgroup_quotient (Subgroup.center ↥E)
    haveI hnt : Nontrivial ↥E :=
      Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥E))
    have hmaptop : Subgroup.map E.subtype (⊤ : Subgroup ↥E) = E := by
      rw [← Subgroup.subgroupOf_self E, Subgroup.subgroupOf_map_subtype]
      simp
    have hcomm : commutator ↥E = ⊤ := by
      have h1 : Subgroup.map E.subtype ⁅(⊤ : Subgroup ↥E), ⊤⁆ =
          Subgroup.map E.subtype (⊤ : Subgroup ↥E) := by
        rw [Subgroup.map_commutator, hmaptop, hEq.1]
      exact Subgroup.map_injective E.subtype_injective h1
    exact absurd hcomm (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥E))

end Work.DSTR.layerShapeAux
