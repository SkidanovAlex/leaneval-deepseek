import Mathlib
import Submission.Work.SSGRoute.H9.NarrowMu2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèles positive at the real places

This file isolates the elementary algebraic object underlying the *narrow* modulus of
`Work.SSGRoute.H9.narrowGesU`: the subgroup

  `posIdeles K = {x : 𝕀_K | x is positive at every real place of K}`

of the idèle group, together with the observation that the narrow `E` is the wide `E` intersected
with it (`narrowPowTIdeles_eq_inf`).

The idèle group `𝕀_K` is the restricted product of the `K_vˣ` with respect to the local units, so the
condition at an infinite place `w` reads: for every real structure `hw : w.IsReal` the image of the
`w`-component of `x` under the ring equivalence `K_w ≃+* ℝ` is positive.  At a complex place
`w.IsReal` is empty and the condition is vacuous, which is exactly the definition of
`Work.SSGRoute.H9.IsPosInf`.
-/

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.H9Narrow

/-- **The idèles positive at every real place of `K`.**  The subgroup of `𝕀_K` whose archimedean
components are positive: the group-theoretic embodiment of "the modulus contains the real
places". -/
noncomputable def posIdeles (K : Type*) [Field K] [NumberField K] : Subgroup (Idele K) where
  carrier := {x | ∀ w : InfinitePlace K, Work.SSGRoute.H9.IsPosInf K w (x (Place.ofInfinite w))}
  one_mem' := fun w => Work.SSGRoute.H9.isPosInf_one K w
  mul_mem' := by
    intro x y hx hy w
    rw [Idele.mul_apply]
    exact (hx w).mul (hy w)
  inv_mem' := by
    intro x hx w
    rw [Idele.inv_apply]
    exact (hx w).inv

@[simp] theorem mem_posIdeles {K : Type} [Field K] [NumberField K] {x : Idele K} :
    x ∈ posIdeles K ↔
      ∀ w : InfinitePlace K, Work.SSGRoute.H9.IsPosInf K w (x (Place.ofInfinite w)) :=
  Iff.rfl

/-- **The narrow `E_{T,unr}` is the wide one cut down by the positivity condition.** -/
theorem narrowPowTIdeles_eq_inf (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (T' : Finset (NK.Chebotarev.PrimeIdeal K)) :
    Work.SSGRoute.H9.narrowPowTIdeles K p T' = Work.SSGRoute.powTIdeles K p T' ⊓ posIdeles K :=
  Subgroup.ext fun _ => Iff.rfl

end Work.H9Narrow
