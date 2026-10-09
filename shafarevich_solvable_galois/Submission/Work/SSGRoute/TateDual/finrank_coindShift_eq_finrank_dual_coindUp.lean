import Mathlib
import Submission.Work.SSGRoute.TateDual.Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `dim (Coind(M)/M) = dim (coindUp G (M^∨))^∨`

This file computes both sides of the desired finrank identity

`finrank 𝔽_p (Coind(M)/coindDiag) = finrank 𝔽_p (Dual (coindUp G (M^∨)))`

for a finite `𝔽_p[G]`-module `M`, where `coindDiagSub p G M ⊆ (G → M)` is the diagonal
`{x ↦ x • m}` (`Setup.lean`) and `coindUp G A = ker (coindAug G A) ⊆ (G → A)` is the
`I_G`-twist (`Submission/Work/Tate/CoindUp.lean`), and `DualMod p V = V →ₗ[ZMod p] ZMod p`.

Both sides equal `|G| · d - d`, where `d = finrank 𝔽_p M`:

* the left side is a quotient `Coind(M)/coindDiag` with `finrank (G → M) = |G| · d` and
  `finrank coindDiag = d` (the diagonal is the range of the injective `coindUnitLin`);
* on the right, the dual has the same dimension as its source, and `coindUp G A` is the
  kernel of the *surjective* twisted norm `coindAugLin : (G → A) →ₗ A`, so rank–nullity gives
  `finrank (coindUp G A) = finrank (G → A) - finrank A = |G| · finrank A - finrank A`;
  finally `finrank (DualMod p M) = finrank M`.
-/

namespace Work.SSGRoute.TateDual

/-- The diagonal `coindDiagSub p G M` (an embedded copy of `M`) has the same `𝔽_p`-dimension
as `M`. -/
theorem finrank_coindDiagSub (p : ℕ) (G : Type) [Group G] [Fintype G]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] :
    Module.finrank (ZMod p) ↥(coindDiagSub p G M) = Module.finrank (ZMod p) M := by
  rw [coindDiagSub_eq_range]
  exact LinearMap.finrank_range_of_inj (f := coindUnitLin p G M) (fun a b h => by
    have h1 := congrFun h (1 : G)
    simpa using h1)

/-- The `I_G`-twist `coindUp G A = ker (coindAug)` of a finite `𝔽_p`-module `A` has
`𝔽_p`-dimension `|G| · dim A - dim A`. -/
theorem finrank_coindUp (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (A : Type) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
    [SMulCommClass G (ZMod p) A] [Finite A] :
    Module.finrank (ZMod p) ↥(Work.Tate.coindUp G A)
      = Fintype.card G * Module.finrank (ZMod p) A - Module.finrank (ZMod p) A := by
  -- Identify the pointwise `𝔽_p`-structure on `coindUp` with that of the submodule kernel.
  have htrans : Module.finrank (ZMod p) ↥(Work.Tate.coindUp G A)
      = Module.finrank (ZMod p) ↥(coindUpSub p G A) := by
    apply LinearEquiv.finrank_eq
    refine
    { toFun := fun x =>
        ⟨(x : G → A), (mem_coindUpSub_iff p G A).mpr (Work.Tate.mem_coindUp_iff.mp x.2)⟩
      invFun := fun y =>
        ⟨(y : G → A), Work.Tate.mem_coindUp_iff.mpr ((mem_coindUpSub_iff p G A).mp y.2)⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl
      map_smul' := fun c x => Subtype.ext rfl }
  rw [htrans]
  -- Rank–nullity for the surjective twisted norm `coindAugLin`.
  have hsurj : Function.Surjective (coindAugLin p G A) := Work.Tate.coindAug_surjective
  have hrange : (coindAugLin p G A).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrn := LinearMap.finrank_range_add_finrank_ker (coindAugLin p G A)
  rw [hrange, finrank_top] at hrn
  have hfun : Module.finrank (ZMod p) (G → A)
      = Fintype.card G * Module.finrank (ZMod p) A := by
    rw [Module.finrank_pi_fintype]
    simp
  rw [hfun] at hrn
  show Module.finrank (ZMod p) ↥(coindAugLin p G A).ker
      = Fintype.card G * Module.finrank (ZMod p) A - Module.finrank (ZMod p) A
  exact Nat.eq_sub_of_add_eq (by rw [add_comm]; exact hrn)

theorem finrank_coindShift_eq_finrank_dual_coindUp
    (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] [Finite M] :
    Module.finrank (ZMod p) ((G → M) ⧸ Work.SSGRoute.TateDual.coindDiagSub p G M)
      = Module.finrank (ZMod p)
          (Work.SSGRoute.DualMod p ↥(Work.Tate.coindUp G (Work.SSGRoute.DualMod p M)))
      := by
  -- The shifted side: a quotient of `G → M` by the diagonal.
  have hL : Module.finrank (ZMod p) ((G → M) ⧸ coindDiagSub p G M)
      = Fintype.card G * Module.finrank (ZMod p) M - Module.finrank (ZMod p) M := by
    have hq := Submodule.finrank_quotient_add_finrank (coindDiagSub p G M)
    rw [finrank_coindDiagSub p G M] at hq
    have htop : Module.finrank (ZMod p) (G → M)
        = Fintype.card G * Module.finrank (ZMod p) M := by
      rw [Module.finrank_pi_fintype]
      simp
    rw [htop] at hq
    exact Nat.eq_sub_of_add_eq hq
  -- The twisted side: the dual of `coindUp G (M^∨)`.
  have hR : Module.finrank (ZMod p)
        (Work.SSGRoute.DualMod p ↥(Work.Tate.coindUp G (Work.SSGRoute.DualMod p M)))
      = Fintype.card G * Module.finrank (ZMod p) M - Module.finrank (ZMod p) M := by
    rw [Subspace.dual_finrank_eq]
    rw [finrank_coindUp p G (Work.SSGRoute.DualMod p M)]
    rw [Subspace.dual_finrank_eq]
  rw [hL, hR]

end Work.SSGRoute.TateDual
