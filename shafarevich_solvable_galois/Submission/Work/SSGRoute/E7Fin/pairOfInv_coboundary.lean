/-
# Clause (3) for the cup-generated local pairing

`E7Fin/cupPairing.lean` defines `pairOfInv inv M H a b = inv (evCupFun M a b)` on locally constant
`1`-cocycles.  This file proves clause **(3)** of the local pairing list for it: the pairing vanishes
when either argument is a coboundary.  The content is the two cup computations
`E7Fin.evCupFun_coboundary_left` (cup of a `1`-coboundary with a `1`-cocycle is a `2`-coboundary)
and `E7Fin.evCupFun_coboundary_right` (the mirror), together with the vanishing of the invariant
`inv` on `2`-coboundaries.
-/
import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.E7Fin.cupPairing
import Submission.Work.SSGRoute.E7Fin.evCupFun_coboundary_left
import Submission.Work.SSGRoute.E7Fin.evCupFun_coboundary_right
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute
open scoped TensorProduct

namespace Work.SSGRoute.E7Fin

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
  [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M T)]
  (H : Subgroup (Ω ≃ₐ[k] Ω))

/-- **Clause (3), first variable**: the cup-generated pairing vanishes when the first argument is a
coboundary. -/
theorem pairOfInv_coboundary_left
    (inv : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (hinv_cob : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c → inv c = 0)
    (hdiagM : ∀ (g : K ≃ₐ[k] K) (x : M) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) = TensorProduct.tmul (ZMod p) (g • x) (g • t))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b)
    (hacob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a) :
    pairOfInv p k Ω K T inv M H a b = 0 := by
  rw [pairOfInv_of_cocycle p k Ω K T inv M H a b ⟨ha.1, hb.1⟩]
  exact hinv_cob H _ (evCupFun_coboundary_left p k Ω K T M hdiagM H a b hacob hb.1 hb.2)

/-- **Clause (3), second variable**: the cup-generated pairing vanishes when the second argument is
a coboundary (the mirror computation, needing the local constancy `hstab` of the orbit maps on the
dual module `DualMod p (M ⊗ T)` in which the cobounding element lives). -/
theorem pairOfInv_coboundary_right
    (inv : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (hinv_cob : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c → inv c = 0)
    (hdiagM : ∀ (g : K ≃ₐ[k] K) (x : M) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) = TensorProduct.tmul (ZMod p) (g • x) (g • t))
    (hstab : ∀ n : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsLocConstOn H (fun g => SSGRoute.res k K g • n))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b)
    (hbcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) :
    pairOfInv p k Ω K T inv M H a b = 0 := by
  rw [pairOfInv_of_cocycle p k Ω K T inv M H a b ⟨ha.1, hb.1⟩]
  exact hinv_cob H _ (evCupFun_coboundary_right p k Ω K T M hdiagM H a b ha.1 ha.2 hbcob hstab)

/-- **Clause (3)**: the cup-generated pairing vanishes when either argument is a coboundary. -/
theorem pairOfInv_coboundary
    (inv : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (hinv_cob : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c → inv c = 0)
    (hdiagM : ∀ (g : K ≃ₐ[k] K) (x : M) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) = TensorProduct.tmul (ZMod p) (g • x) (g • t))
    (hstab : ∀ n : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsLocConstOn H (fun g => SSGRoute.res k K g • n))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b)
    (h : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a ∨
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) :
    pairOfInv p k Ω K T inv M H a b = 0 := by
  rcases h with h | h
  · exact pairOfInv_coboundary_left p k Ω K T M H inv hinv_cob hdiagM a b ha hb h
  · exact pairOfInv_coboundary_right p k Ω K T M H inv hinv_cob hdiagM hstab a b ha hb h

end

end Work.SSGRoute.E7Fin
