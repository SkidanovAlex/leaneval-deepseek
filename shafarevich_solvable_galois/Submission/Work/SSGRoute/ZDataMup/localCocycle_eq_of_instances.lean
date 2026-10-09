import Mathlib
import Submission.Work.SSGRoute.ZDataMup.LocalData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-`K` local cocycle space does not depend on the `G_k`-action instances

`Work.SSGRoute.ZDataMup.localCocycle K H` is the `ZMod p`-submodule of locally constant
`H`-cocycles on `H ≤ G_k`, where `H`-cocycles are taken with respect to the action of
`G_K = Gal(K/k)` on `ZMod p`.  The definition mentions two instance arguments (the
`DistribMulAction` and the compatible `SMulCommClass`), and the goal of this file is that the
resulting submodule is *independent* of them.

The mathematical content is one line: for `H ≤ K.fixingSubgroup` and `g ∈ H`, the restriction
`res k K g` is trivial, so the action occurring in the cocycle identity
`f (g * h) = f g + res k K g • f h` is `1 • f h = f h` in *either* instance.  Hence the two
cocycle predicates are equivalent, and the two submodules have the same carrier.

The formal content is a small instance-independence lemma for `SSGRoute.IsCocycleOn`: the
`•` occurring in the definition of a `DistribMulAction` is not literally the `•` of the
`MulAction` projection, so one uses `D.one_smul`/`D'.one_smul` (the projection form of
`one_smul`), which do agree with the `DistribMulAction`-derived scalar multiplication.
-/

namespace Work.SSGRoute.ZDataMup

/-- **Instance independence of the `1`-cocycle condition for a trivial action.**  If `act` is
trivial on `H`, then being an `H`-cocycle with values in `M` (for `Γ` acting on `M` through
`act`) does not depend on *which* `DistribMulAction` of `G` on `M` is used to interpret the
scalar multiplication: on `H` the action is the identity, so `act g • x = x` in any instance. -/
theorem isCocycleOn_congr_instances {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    (D D' : DistribMulAction G M) (act : Γ →* G) (H : Subgroup Γ)
    (hH : ∀ g ∈ H, act g = 1) (f : Γ → M) :
    @SSGRoute.IsCocycleOn Γ G M _ _ _ D act H f ↔
      @SSGRoute.IsCocycleOn Γ G M _ _ _ D' act H f := by
  constructor
  · intro h g hg h' hh
    have h1 := h g hg h' hh
    rw [hH g hg] at h1
    rw [hH g hg]
    rw [h1]
    congr 1
    exact (D.one_smul (f h')).trans (D'.one_smul (f h')).symm
  · intro h g hg h' hh
    have h1 := h g hg h' hh
    rw [hH g hg] at h1
    rw [hH g hg]
    rw [h1]
    congr 1
    exact (D'.one_smul (f h')).trans (D.one_smul (f h')).symm

theorem localCocycle_eq_of_instances {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K]
    (D : DistribMulAction (K ≃ₐ[k] K) (ZMod p)) (S : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p))
    (D' : DistribMulAction (K ≃ₐ[k] K) (ZMod p)) (S' : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p))
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : H ≤ K.fixingSubgroup) :
    @Work.SSGRoute.ZDataMup.localCocycle p k Ω _ _ _ K _ D S H
      = @Work.SSGRoute.ZDataMup.localCocycle p k Ω _ _ _ K _ D' S' H := by
  apply Submodule.ext
  intro a
  change (@SSGRoute.IsCocycleOn (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) (ZMod p) _ _ _ D (SSGRoute.res k K)
      H a ∧ SSGRoute.IsLocConstOn H a) ↔
    (@SSGRoute.IsCocycleOn (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) (ZMod p) _ _ _ D' (SSGRoute.res k K)
      H a ∧ SSGRoute.IsLocConstOn H a)
  rw [isCocycleOn_congr_instances D D' (SSGRoute.res k K) H
    (fun g hg => res_eq_one_of_mem_fixingSubgroup (hH hg)) a]

end Work.SSGRoute.ZDataMup
