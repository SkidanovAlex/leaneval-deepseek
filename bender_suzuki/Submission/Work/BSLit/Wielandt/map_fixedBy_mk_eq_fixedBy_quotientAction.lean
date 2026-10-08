import Mathlib
import Submission.Work.BSLit.Defs
import Submission.Work.BSLit.Wielandt.PullbackAction
import Submission.Work.Coprime.cocycle_is_coboundary

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `C_{Q/N}(H) = C_Q(H)·N/N` in the `ρ`-language of `Work.BSLit`

Let a finite group `F` act by automorphisms on a finite group `Q` through `ρ : F →* MulAut Q`,
let `N ⊴ Q` be an `F`-invariant subgroup (`N.map (ρ g) = N` for all `g : F`) and let `H ≤ F`.

The main result of this file,

`map_fixedBy_mk_eq_fixedBy_quotientAction`,

says that the image of the fixed-point subgroup `C_Q(H) = Work.BSLit.fixedBy ρ H` under the
canonical projection `Q ↠ Q ⧸ N` is exactly the fixed-point subgroup of the induced action
`Work.BSLit.quotientAction ρ N hN` on the quotient:

`(fixedBy ρ H).map (QuotientGroup.mk' N) = fixedBy (quotientAction ρ N hN) H`.

The inclusion `⊆` is formal.  For the reverse inclusion, given `g : Q` whose coset `gN` is fixed
by `H`, the map `h ↦ g⁻¹ (ρ h g)` is a crossed homomorphism (`1`-cocycle) `H → N` for the action
of `H` on the invariant subgroup `N`, and the hypothesis that `N` is solvable together with
`Nat.Coprime (Nat.card F) (Nat.card Q)` (hence `Nat.Coprime (Nat.card H) (Nat.card N)`) makes it a
coboundary by the Schur–Zassenhaus-based vanishing of `H¹` for coprime actions
(`Work.Coprime.cocycle_is_coboundary`).  The coboundary witness `n ∈ N` exhibits the element
`g n⁻¹ ∈ C_Q(H)` with the same coset as `g`.

The bridge between the abstract `MulDistribMulAction`-formulation of the coprime-action library
and the present `ρ`-formulation is provided by `Submission.Work.BSLit.Wielandt.PullbackAction`
(`pullbackAction`, `pullbackAction_smul`, `isInvariant_pullbackAction`) together with
`FT.instSubgroupMulDistribMulAction` / `FT.coe_subgroup_smul`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.BSLit.Wielandt

/-- `C_Q(H)·N/N ≤ C_{Q/N}(H)`: the image of the fixed points of `H` in `Q` is fixed in the
quotient.  No coprimality, solvability or finiteness hypothesis is needed. -/
theorem map_fixedBy_le_fixedBy_quotientAction {F Q : Type*} [Group F] [Group Q]
    (ρ : F →* MulAut Q) (N : Subgroup Q) [N.Normal] (hN : ∀ g : F, N.map (ρ g) = N)
    (H : Subgroup F) :
    (Work.BSLit.fixedBy ρ H).map (QuotientGroup.mk' N)
      ≤ Work.BSLit.fixedBy (Work.BSLit.quotientAction ρ N hN) H := by
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  rw [Work.BSLit.mem_fixedBy] at hq ⊢
  intro g hg
  rw [QuotientGroup.mk'_apply, Work.BSLit.quotientAction_mk, hq g hg]

theorem map_fixedBy_mk_eq_fixedBy_quotientAction {F Q : Type*} [Group F] [Finite F] [Group Q] [Finite Q]
    (ρ : F →* MulAut Q) (N : Subgroup Q) [N.Normal] (hN : ∀ g : F, N.map (ρ g) = N)
    [Group.IsSolvable ↥N] (hcop : Nat.Coprime (Nat.card F) (Nat.card Q)) (H : Subgroup F) :
    (Work.BSLit.fixedBy ρ H).map (QuotientGroup.mk' N)
      = Work.BSLit.fixedBy (Work.BSLit.quotientAction ρ N hN) H := by
  -- The action of `H` on `Q` (hence on the invariant subgroup `N`) obtained from `ρ`.
  letI actQ : MulDistribMulAction H Q := pullbackAction ρ H
  haveI invN : FT.IsInvariant H N := isInvariant_pullbackAction ρ N hN H
  refine le_antisymm (map_fixedBy_le_fixedBy_quotientAction ρ N hN H) ?_
  -- Reverse inclusion: lift a fixed coset to a fixed point.
  intro x hx
  rw [Work.BSLit.mem_fixedBy] at hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  -- Coprimality for the coefficients `↥N`.
  have hcN : (Nat.card H).Coprime (Nat.card ↥N) :=
    (hcop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card H)).coprime_dvd_right
      (Subgroup.card_subgroup_dvd_card N)
  -- The crossed homomorphism `h ↦ g⁻¹ (ρ h g)` with values in `N`.
  let Φ : H → ↥N := fun h => ⟨g⁻¹ * ρ (h : F) g, by
    have hh : (QuotientGroup.mk' N) (ρ (h : F) g) = (QuotientGroup.mk' N) g := by
      have h' := hx h h.2
      rwa [QuotientGroup.mk'_apply, Work.BSLit.quotientAction_mk] at h'
    have h2 : (ρ (h : F) g)⁻¹ * g ∈ N := QuotientGroup.eq.mp hh
    have h3 := N.inv_mem h2
    simpa using h3⟩
  have hcross : ∀ a b : H, Φ (a * b) = Φ a * (a • Φ b) := by
    intro a b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [FT.coe_subgroup_smul]
    show g⁻¹ * ρ ((a : F) * (b : F)) g
      = (g⁻¹ * ρ (a : F) g) * (a • ((Φ b : ↥N) : Q))
    rw [pullbackAction_smul]
    show g⁻¹ * ρ ((a : F) * (b : F)) g
      = (g⁻¹ * ρ (a : F) g) * ρ (a : F) (g⁻¹ * ρ (b : F) g)
    simp only [map_mul, map_inv, MulAut.mul_apply]
    group
  -- `H¹(H, N) = 0`: the cocycle is a coboundary.
  obtain ⟨n, hn⟩ := Work.Coprime.cocycle_is_coboundary H hcN (Or.inr (inferInstance)) Φ hcross
  refine Subgroup.mem_map.mpr ⟨g * (n : Q)⁻¹, ?_, ?_⟩
  · -- `g n⁻¹` is fixed by `H`.
    rw [Work.BSLit.mem_fixedBy]
    intro f hf
    have h1 := congrArg (Subtype.val) (hn ⟨f, hf⟩)
    simp only [Φ, Subgroup.coe_mul, Subgroup.coe_inv, FT.coe_subgroup_smul,
      pullbackAction_smul] at h1
    have h2 : ρ f g = g * ((n : Q)⁻¹ * ρ f (n : Q)) := by rw [← h1]; group
    rw [map_mul, h2, map_inv]
    group
  · -- and it has the same coset as `g`.
    rw [map_mul, map_inv]
    have hn1 : (QuotientGroup.mk' N) (n : Q) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact n.2
    rw [hn1, inv_one, mul_one]

end Work.BSLit.Wielandt
