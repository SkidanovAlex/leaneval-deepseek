import Mathlib
import Submission.Work.SSGRoute.H9.NarrowMu2
import Submission.Work.SSGRoute.ges_escape_aux
import Submission.Work.SSGRoute.finiteIndex_gesU
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Openness and finiteness of the narrow modulus

`Work.SSGRoute.H9.narrowGesU K p T'` is the image in `C_K` of `Kˣ · E^{narrow}_{T,unr}`, where
`E^{narrow}` is `powTIdeles` with the extra requirement that the archimedean components be positive.
This file proves that it is **open** (and proves the finite-index part
`narrowGesU_finiteIndex` separately, or leaves it to the companion statement) — the pair consumed by
`GrunwaldEscapeCore.exists_abelian_classField_inside` when the class field of the narrow modulus is
constructed.

Openness: `narrowPowTIdeles` is the intersection of the open `powTIdeles` with the positivity
conditions at the (finitely many) real places, each of which is open because the comparison
`e_{w} > 0` is the preimage of `Ioi 0` under the continuous (indeed isometric) comparison
`v.Completion ≃ ℝ`; the passage to the image in `C_K` is `QuotientGroup.isOpenMap_coe`.
-/

open scoped Pointwise
open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
open NK.GlobalCFT
open NK.Chebotarev

namespace Work.SSGRoute.H9

variable {K : Type} [Field K] [NumberField K]

/-- **The positivity condition at an infinite place is open.**  `IsPosInf` is an intersection, over
the (subsingleton type of) proofs that the place is real, of the sets `e_{w} > 0`, each of which is
the preimage of `Ioi 0` under the composition of the (continuous) evaluation at the place, the
projection to the completion, and the (isometric) identification with `ℝ`. -/
theorem isOpen_posInf (w : InfinitePlace K) :
    IsOpen {x : Idele K | IsPosInf K w (x (Place.ofInfinite w))} := by
  have hcont : ∀ hw : w.IsReal, Continuous fun x : Idele K =>
      NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
        (((x (Place.ofInfinite w) : (Place.localField K (Place.ofInfinite w))ˣ)) : w.Completion) := by
    intro hw
    have h1 : Continuous fun x : (Πʳ v : Place K,
        [(Place.localField K v)ˣ, Place.localUnits K v]) => x (Place.ofInfinite w) :=
      RestrictedProduct.continuous_eval
        (R := fun v : Place K => (Place.localField K v)ˣ)
        (A := fun v : Place K => (Place.localUnits K v : Set _))
        (Place.ofInfinite w)
    have h2 : Continuous fun y : (Place.localField K (Place.ofInfinite w))ˣ => (y : w.Completion) :=
      Units.continuous_val
    have h3 : Continuous (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw :
        w.Completion → ℝ) :=
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous
    exact h3.comp (h2.comp h1)
  have hset : {x : Idele K | IsPosInf K w (x (Place.ofInfinite w))} =
      ⋂ hw : w.IsReal, {x : Idele K | 0 < NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
        hw (((x (Place.ofInfinite w) : (Place.localField K (Place.ofInfinite w))ˣ)) : w.Completion)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, IsPosInf]
  rw [hset]
  haveI : Finite w.IsReal :=
    Finite.of_injective (fun _ : w.IsReal => (() : PUnit)) (fun a b _ => Subsingleton.elim a b)
  exact isOpen_iInter_of_finite fun hw => isOpen_lt continuous_const (hcont hw)

/-- **The narrow `E_{T,unr}` is open.** -/
theorem isOpen_narrowPowTIdeles (p : ℕ) (hp : p.Prime) (T' : Finset (PrimeIdeal K)) :
    IsOpen ((narrowPowTIdeles K p T') : Set (Idele K)) := by
  have hset : ((narrowPowTIdeles K p T') : Set (Idele K)) =
      ((Work.SSGRoute.powTIdeles K p T' : Subgroup (Idele K)) : Set (Idele K)) ∩
        ⋂ w : InfinitePlace K, {x : Idele K | IsPosInf K w (x (Place.ofInfinite w))} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, SetLike.mem_coe, mem_narrowPowTIdeles,
      Set.mem_setOf_eq]
  rw [hset]
  exact (Work.SSGRoute.isOpen_powTIdeles (K := K) hp T').inter
    (isOpen_iInter_of_finite fun w => isOpen_posInf w)

/-- The narrow `U` is the image of the narrow idèles under `mk` (the principal idèles lie in the
kernel). -/
theorem narrowGesU_eq_map (p : ℕ) (T' : Finset (PrimeIdeal K)) :
    narrowGesU K p T' = (narrowPowTIdeles K p T').map (IdeleClassGroup.mk K) := by
  rw [narrowGesU, Subgroup.map_sup]
  have hbot : Subgroup.map (IdeleClassGroup.mk K) (Idele.principalSubgroup K) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    have hker : (Idele.principalSubgroup K : Subgroup (Idele K)) ≤ (IdeleClassGroup.mk K).ker := by
      rw [Work.SSGRoute.ker_mk_eq_principal]
    exact hker
  rw [hbot, bot_sup_eq]

/-- **The narrow `U` is open.** -/
theorem isOpen_narrowGesU (p : ℕ) (hp : p.Prime) (T' : Finset (PrimeIdeal K)) :
    IsOpen ((narrowGesU K p T') : Set (IdeleClassGroup K)) := by
  rw [narrowGesU_eq_map, Subgroup.coe_map]
  exact QuotientGroup.isOpenMap_coe (N := Idele.principalSubgroup K) _
    (isOpen_narrowPowTIdeles p hp T')

end Work.SSGRoute.H9
