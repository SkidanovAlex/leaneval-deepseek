import Mathlib
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.RankOneUniqueness

/-- The hypotheses `hQ : Q ≤ H`, `hQ' : Q' ≤ H'` and
`hψQ : ∀ x : H, (x : G) ∈ Q ↔ (ψ x : G') ∈ Q'` say exactly that `ψ` carries the subset
`Q ⊆ H` bijectively onto the subset `Q' ⊆ H'`. Hence `ψ` restricts to an isomorphism
`Q ≃* Q'`, whose value in `G'` is the value of `ψ` (the form in which the restriction is
used downstream). -/
theorem mapSubgroupEquiv {G G' : Type} [Group G] [Group G'] {H : Subgroup G} {H' : Subgroup G'}
    {Q : Subgroup G} {Q' : Subgroup G'} {ψ : H ≃* H'} (hQ : Q ≤ H) (hQ' : Q' ≤ H')
    (hψQ : ∀ x : H, (x : G) ∈ Q ↔ (ψ x : G') ∈ Q') :
    ∃ e : Q ≃* Q', ∀ x : Q, ((e x : Q') : G') = (ψ ⟨(x : G), hQ x.2⟩ : G') := by
  -- the homomorphism `Q →* H'` induced by `ψ` and the inclusion `Q ≤ H`
  let g : Q →* H' := ψ.toMonoidHom.comp (Subgroup.inclusion hQ)
  have hgapp : ∀ x : Q, g x = ψ ⟨(x : G), hQ x.2⟩ := by
    intro x
    show ψ (Subgroup.inclusion hQ x) = ψ ⟨(x : G), hQ x.2⟩
    rw [show Subgroup.inclusion hQ x = ⟨(x : G), hQ x.2⟩ from
      Subtype.ext (Subgroup.coe_inclusion hQ x)]
  -- by hypothesis its range lies in `Q'`, viewed as a subgroup of `H'`
  have hgmem : ∀ x : Q, g x ∈ Q'.subgroupOf H' := by
    intro x
    rw [Subgroup.mem_subgroupOf, hgapp x]
    exact (hψQ ⟨(x : G), hQ x.2⟩).mp x.2
  let G₁ : Q →* ↥(Q'.subgroupOf H') := g.codRestrict (Q'.subgroupOf H') hgmem
  have hG₁app : ∀ x : Q, (G₁ x : H') = g x := fun x => rfl
  have hinj : Function.Injective G₁ := by
    intro x y hxy
    have h1 : g x = g y := by
      have h := congrArg (Subtype.val) hxy
      simpa only [hG₁app] using h
    have h2 : (⟨(x : G), hQ x.2⟩ : H) = ⟨(y : G), hQ y.2⟩ := by
      apply ψ.injective
      rw [← hgapp x, ← hgapp y]
      exact h1
    have h3 : (x : G) = (y : G) := congrArg (fun a : H => (a : G)) h2
    exact Subtype.ext h3
  have hsurj : Function.Surjective G₁ := by
    intro z
    have hzmem : ((z : ↥H') : G') ∈ Q' := (Subgroup.mem_subgroupOf (H := Q') (K := H')).mp z.2
    -- `w = ψ⁻¹ z` is an element of `H` whose image lies in `Q'`, hence lies in `Q`
    let w : H := ψ.symm ⟨(z : ↥H'), hQ' hzmem⟩
    have hw : ψ w = ⟨(z : ↥H'), hQ' hzmem⟩ := MulEquiv.apply_symm_apply ψ _
    have hwmem : (w : G) ∈ Q := (hψQ w).mpr (by
      rw [hw]
      exact hzmem)
    refine ⟨⟨(w : G), hwmem⟩, ?_⟩
    apply Subtype.ext
    rw [hG₁app, hgapp]
    show ψ w = (z : ↥H')
    rw [hw]
  refine ⟨(MulEquiv.ofBijective G₁ ⟨hinj, hsurj⟩).trans (Subgroup.subgroupOfEquivOfLe hQ'), ?_⟩
  intro x
  change (((Subgroup.subgroupOfEquivOfLe hQ') (G₁ x) : Q') : G') =
    (ψ ⟨(x : G), hQ x.2⟩ : G')
  rw [Subgroup.subgroupOfEquivOfLe_apply_coe]
  rw [hG₁app, hgapp]

end Work.RankOneUniqueness
