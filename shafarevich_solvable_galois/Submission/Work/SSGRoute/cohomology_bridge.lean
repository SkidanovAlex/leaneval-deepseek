import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.End
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bridge between the cocycle predicates of `SSGRoute.Interfaces` and `H¹`

The predicates `SSGRoute.IsCocycleOn`, `SSGRoute.IsLocConstOn`, `SSGRoute.IsCoboundaryOn` of
`Submission/Work/SSGRoute/Interfaces.lean` are stated for a cocycle written on an ambient group
`Γ` (in the SSG application `Γ = Ω ≃ₐ[k] Ω`) and a subgroup `H ≤ Γ`, with the action on the
coefficient module given by a monoid homomorphism `act : Γ →* G`.  The cohomology groups
`Work.GroupCohomology.H1` are stated for the subgroup `↥H` with the action pulled back along
`act.comp H.subtype`.

This file relates the two languages: a function on `⊤` is a coboundary for `act` iff its class in
`H¹(Γ, M)` (with the pulled-back action) is zero.  This is what allows the local conditions of
`Work.SSGRoute.coker_obstruction` ("`ε - α_A` is a coboundary on `decomp k A`") to be read as
statements about the classes of the local data in the decomposition groups.
-/

namespace Work.SSGRoute

open SSGRoute

/-- `H1π x = 0` iff the underlying cochain is a coboundary. -/
theorem h1pi_eq_zero_iff {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
    (x : Work.GroupCohomology.Z1 G M) :
    Work.GroupCohomology.H1π G M x = 0 ↔ (x : G → M) ∈ Work.GroupCohomology.B1 G M := by
  rw [show Work.GroupCohomology.H1π G M x
      = ((x : Work.GroupCohomology.Z1 G M) : _) from rfl]
  rw [QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.mem_comap

/-- The cocycle condition of `Interfaces.lean` on `⊤` is the crossed-homomorphism condition of
`Work.GroupCohomology.Z1` for the pulled-back action. -/
theorem isCocycleOn_iff_mem_Z1 {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] (act : Γ →* G) (f : Γ → M) :
    SSGRoute.IsCocycleOn act ⊤ f ↔
      f ∈ @Work.GroupCohomology.Z1 Γ M _ _ (DistribMulAction.compHom M act) := by
  letI : DistribMulAction Γ M := DistribMulAction.compHom M act
  rw [Work.GroupCohomology.mem_Z1_iff, Work.GroupCohomology.IsCrossedHom]
  change (∀ g ∈ (⊤ : Subgroup Γ), ∀ h ∈ ⊤, f (g * h) = f g + act g • f h) ↔
    ∀ g h : Γ, f (g * h) = g • f h + f g
  constructor
  · intro h g h'
    have h1 := h g trivial h' trivial
    rw [h1, add_comm]
    rfl
  · intro h g _ h' _
    have h1 := h g h'
    rw [h1, add_comm]
    rfl

/-- `IsCoboundaryOn act ⊤ f` iff the cohomology class of `f` is zero, i.e. iff `f ∈ Z¹` and its
class in `H¹` vanishes. -/
theorem isCoboundaryOn_top_iff_class_eq_zero {Γ G M : Type} [Group Γ] [Group G]
    [AddCommGroup M] [DistribMulAction G M] (act : Γ →* G) (f : Γ → M) :
    SSGRoute.IsCoboundaryOn act ⊤ f ↔
      ∃ (hf : f ∈ @Work.GroupCohomology.Z1 Γ M _ _ (DistribMulAction.compHom M act)),
        @Work.GroupCohomology.H1π Γ M _ _ (DistribMulAction.compHom M act) ⟨f, hf⟩ = 0 := by
  constructor
  · rintro ⟨m, hm⟩
    have hB : f ∈ @Work.GroupCohomology.B1 Γ M _ _ (DistribMulAction.compHom M act) := by
      rw [Work.GroupCohomology.mem_B1_iff]
      refine ⟨m, ?_⟩
      funext g
      rw [Work.GroupCohomology.d0_apply]
      exact (hm g trivial).symm
    have hZ : f ∈ @Work.GroupCohomology.Z1 Γ M _ _ (DistribMulAction.compHom M act) :=
      @Work.GroupCohomology.B1_le_Z1 Γ M _ _ (DistribMulAction.compHom M act) f hB
    refine ⟨hZ, ?_⟩
    rw [@h1pi_eq_zero_iff Γ M _ _ (DistribMulAction.compHom M act) ⟨f, hZ⟩]
    exact hB
  · rintro ⟨hf, h0⟩
    have hB : f ∈ @Work.GroupCohomology.B1 Γ M _ _ (DistribMulAction.compHom M act) :=
      (@h1pi_eq_zero_iff Γ M _ _ (DistribMulAction.compHom M act) ⟨f, hf⟩).mp h0
    rw [Work.GroupCohomology.mem_B1_iff] at hB
    obtain ⟨m, hm⟩ := hB
    refine ⟨m, fun g _ => ?_⟩
    rw [← hm, Work.GroupCohomology.d0_apply]
    rfl

/-- The same statement for a subgroup `H ≤ Γ`: the coboundary condition on `H` is the vanishing of
the class in `H¹(↥H, M)` for the pulled-back action `act ∘ H.subtype`. -/
theorem isCoboundaryOn_iff_class_eq_zero {Γ G M : Type} [Group Γ] [Group G]
    [AddCommGroup M] [DistribMulAction G M] (act : Γ →* G) (H : Subgroup Γ) (f : Γ → M) :
    SSGRoute.IsCoboundaryOn act H f ↔
      ∃ (hf : (fun g : ↥H => f g) ∈ @Work.GroupCohomology.Z1 ↥H M _ _
        (DistribMulAction.compHom M (act.comp H.subtype))),
        @Work.GroupCohomology.H1π ↥H M _ _ (DistribMulAction.compHom M (act.comp H.subtype))
          ⟨(fun g : ↥H => f g), hf⟩ = 0 := by
  have hiff : SSGRoute.IsCoboundaryOn act H f ↔
      SSGRoute.IsCoboundaryOn (act.comp H.subtype) ⊤ (fun h : ↥H => f h) := by
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, fun h _ => hm h h.2⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, fun x hx => hm ⟨x, hx⟩ trivial⟩
  rw [hiff]
  exact isCoboundaryOn_top_iff_class_eq_zero (act.comp H.subtype) (fun h : ↥H => f h)

end Work.SSGRoute
