/-
Higman's Lemma 8: irreducibility of the `ξ`-module `D / A` from a covering hypothesis.

This is the general form of `Work.Higman.MSA.L8.l8_quot_irred` in which the structural data of
the situation of Higman's Lemma 8 (`powSub D 2 ≤ A`, `⁅D,D⁆ = A`, exponent data, ...) has been
replaced by the two facts that are actually used:

* `hPC : ⁅⊤, D⁆ ≤ A` -- `P` acts trivially on `D/A`, so every subgroup between `A` and `D` is
  normal in `P`;
* `hcover` -- the only normal, `ξ`-invariant subgroups between `A` and `D` are `A` and `D`.

The proof lifts a `ξ`-invariant subgroup `K ≤ D/A` to a subgroup `E ≤ D` with `A ≤ E` via the
correspondence theorem, shows `E` is normal and `ξ`-invariant, and applies `hcover`.
-/

import Mathlib
import Submission.Work.Higman.MSA.l8_quot_irred
import Submission.Work.Higman.MSA.l8_triv
import Submission.Work.Higman.MSA.l8_local

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.H8

open Work.Higman.MSA

theorem quot_irred_of_cover {P : Type} [Group P] [Finite P]
    {h : Work.Higman.IsSuzuki2Grp P} {A D : Subgroup P} [A.Normal]
    (hAinv : Subgroup.map (MulEquiv.toMonoidHom h.xi) A = A)
    (hDinv : Subgroup.map (MulEquiv.toMonoidHom h.xi) D = D)
    (hAD : A ≤ D)
    (hPC : ⁅(⊤ : Subgroup P), D⁆ ≤ A)
    (hcover : ∀ E : Subgroup P, E.Normal → Subgroup.map (MulEquiv.toMonoidHom h.xi) E = E →
      A ≤ E → E ≤ D → E = A ∨ E = D) :
    ∀ K : Subgroup (↥D ⧸ (A.subgroupOf D)),
      K.map (Work.Higman.MSA.L8.xiQuot h hAinv hDinv).toMonoidHom = K → K = ⊥ ∨ K = ⊤ := by
  intro K hK
  -- `K` is stable under the action on elements.
  have hW : ∀ v ∈ K, L8.xiQuot h hAinv hDinv v ∈ K := by
    intro v hv
    have h1 := Subgroup.mem_map_of_mem (L8.xiQuot h hAinv hDinv).toMonoidHom hv
    rwa [hK] at h1
  -- Lift `K` to a subgroup `Ds` of `↥D`, then to a subgroup `E` of `P`.
  set Ds : Subgroup ↥D := K.comap (QuotientGroup.mk' (A.subgroupOf D)) with hDs
  have hmemDs : ∀ u : ↥D, u ∈ Ds ↔ QuotientGroup.mk' (A.subgroupOf D) u ∈ K := fun u => Iff.rfl
  set E : Subgroup P := Ds.map D.subtype with hE
  have hAE : A ≤ E := by
    intro a ha
    rw [hE]
    refine Subgroup.mem_map.mpr ⟨⟨a, hAD ha⟩, ?_, rfl⟩
    rw [hmemDs]
    have hx1 : QuotientGroup.mk' (A.subgroupOf D) ⟨a, hAD ha⟩ = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ha)
    rw [hx1]
    exact K.one_mem
  have hED : E ≤ D := by
    rw [hE]
    exact Subgroup.map_subtype_le Ds
  -- `E` is `ξ`-invariant.
  have hEinv_le : E.map (h.xi : MulAut P).toMonoidHom ≤ E := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
    rw [hE]
    refine Subgroup.mem_map.mpr ⟨(L8.xiSubAut h hDinv d : ↥D), ?_, rfl⟩
    rw [hmemDs] at hd ⊢
    have h1 : L8.xiQuot h hAinv hDinv (QuotientGroup.mk' (A.subgroupOf D) d) ∈ K := hW _ hd
    simpa [QuotientGroup.mk'_apply, l8_xiQuot_mk] using h1
  have hEinv : E.map (h.xi : MulAut P).toMonoidHom = E :=
    Subgroup.eq_of_le_of_card_ge hEinv_le
      (le_of_eq (Subgroup.card_map_of_injective (h.xi : MulAut P).injective).symm)
  -- `K` is the image of `Ds` under the quotient map.
  have hKDs : K = Ds.map (QuotientGroup.mk' (A.subgroupOf D)) := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf D) v
      exact ⟨u, (hmemDs u).mpr hv, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact (hmemDs u).mp hu
  -- `E` is normal (`P` acts trivially on `D/A`), so `hcover` applies.
  rcases hcover E (L8.normal_of_le_of_contains (A := A) (C := D) (D := E) hPC hAE hED)
      hEinv hAE hED with h1 | h1
  · left
    have hmap : Ds.map D.subtype = (A.subgroupOf D).map D.subtype := by
      rw [← hE, h1, Subgroup.map_subgroupOf_eq_of_le hAD]
    have hDA : Ds = A.subgroupOf D := Subgroup.map_injective D.subtype_injective hmap
    rw [hKDs, hDA, Subgroup.map_eq_bot_iff]
    intro x hx
    rw [QuotientGroup.ker_mk']
    exact hx
  · right
    have hDtop : Ds = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      have hx : D.subtype x ∈ E := by rw [h1]; exact x.2
      rw [hE] at hx
      obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp hx
      rwa [D.subtype_injective hdx] at hd
    rw [hKDs, hDtop, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (A.subgroupOf D))

end Work.Higman.H8
