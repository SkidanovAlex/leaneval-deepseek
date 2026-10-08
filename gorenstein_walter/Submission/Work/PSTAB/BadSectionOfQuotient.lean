import Mathlib
import Submission.Work.PSTAB.Defs
import Submission.Work.PSTAB.BadSectionQuotient

set_option autoImplicit false

/-!
# `Work.PSTAB.BadSectionOfQuotient`

`NoBadSection` — "has no section that is a noncyclic `2`-group with a unique involution" —
descends to quotients: if `M` has no bad section, then neither does `M ⧸ C`.

A section of `M ⧸ C` is `K ⧸ N` with `K ≤ M ⧸ C` and `N ⊴ K`.  Pulling `K` back along the
projection `π : M →* M ⧸ C` gives `K' = K.comap π ≤ M`, and `π` restricts to a surjective
homomorphism `p : K' →* K` (because `K'.map π = K`); composing with `K →* K ⧸ N` yields a
surjective homomorphism `ψ : K' →* K ⧸ N` with `K' ⧸ ψ.ker ≃* K ⧸ N`.  A subgroup of `K ⧸ N`
is transported back along this isomorphism to a section `K' ⧸ ψ.ker` of `M`, which is
forbidden by `hM : NoBadSection M`.
-/

namespace Work.PSTAB

theorem BadSectionOfQuotient : Work.PSTAB.BadSectionOfQuotientProp := by
  intro M _ _ C _ hM K N _ Q hQ2 hnc hu
  -- `π : M →* M ⧸ C`, `K' = π ⁻¹ K`, and `K' ⧸ ψ.ker ≃* K ⧸ N`.
  let π : M →* M ⧸ C := QuotientGroup.mk' C
  let K' : Subgroup M := K.comap π
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective C
  have hmapK : K'.map π = K := Subgroup.map_comap_eq_self_of_surjective hπ K
  -- the restriction `p : K' →* K` of `π`
  let p : K' →* K :=
    { toFun := fun x => ⟨π x.1, (Subgroup.mem_comap).mp x.2⟩
      map_one' := by ext; simp [π]
      map_mul' := by intro a b; ext; exact map_mul π a.1 b.1 }
  have hp : Function.Surjective p := by
    intro y
    have hy : (y : M ⧸ C) ∈ K'.map π := by rw [hmapK]; exact y.2
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  -- the composite `ψ : K' →* K ⧸ N`
  let ψ : K' →* K ⧸ N := (QuotientGroup.mk' N).comp p
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨y', hy'⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨x, hx⟩ := hp y'
    exact ⟨x, by simp only [ψ, MonoidHom.comp_apply, hx, hy']⟩
  -- `K' ⧸ ψ.ker` is the section of `M` isomorphic to `K ⧸ N`
  let e : (K' ⧸ ψ.ker) ≃* (K ⧸ N) := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  let Q' : Subgroup (K' ⧸ ψ.ker) := Q.comap e
  have hmapQ : Q'.map e = Q := Subgroup.map_comap_eq_self_of_surjective e.surjective Q
  let eQ : ↥Q' ≃* ↥Q :=
    (Subgroup.equivMapOfInjective Q' e e.injective).trans (MulEquiv.subgroupCongr hmapQ)
  -- the three hypotheses transport across `eQ`
  have hQ2' : IsPGroup 2 Q' := hQ2.of_equiv eQ.symm
  have hnc' : ¬ IsCyclic Q' := by
    intro hc
    exact hnc (isCyclic_of_surjective eQ.toMonoidHom eQ.surjective)
  have hu' : ∃! z : Q', orderOf z = 2 := by
    obtain ⟨w, hw, hwu⟩ := hu
    refine ⟨eQ.symm w, ?_, ?_⟩
    · show orderOf (eQ.symm w) = 2
      rw [MulEquiv.orderOf_eq eQ.symm w]; exact hw
    · intro y hy
      have hy' : orderOf (eQ y) = 2 := by rw [MulEquiv.orderOf_eq eQ y]; exact hy
      have h2 : eQ y = w := hwu (eQ y) hy'
      rw [← MulEquiv.symm_apply_apply eQ y, h2]
  exact hM K' ψ.ker Q' hQ2' hnc' hu'

end Work.PSTAB
