import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.UchidaKummer.Approximation.isOpenEllPowSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for the escape-form Grünwald theorem (piece 1: the subgroup `U`)

This module holds the pieces of the construction of the open finite-index subgroup
`U ≤ C_K = 𝕀_K ⧸ Kˣ` used by the escape-form Grünwald theorem
(`Submission/Work/SSGRoute/NOTE_ges_zmod_escape_route.md`, §2 step 3 and §3ter):

  `U := im(Kˣ · E)`,  `E := {x ∈ 𝕀_K : x 𝔭 ∈ (K𝔭ˣ)ᵖ (𝔭 ∈ T),  x 𝔭 ∈ O𝔭ˣ (𝔭 ∉ T)}`.

## What is here (all proved, no `sorry`)

* `isOpen_forall_mem_localUnits'`, `isOpen_forall_mem_localUnits`, `idelesUnitsOutside`,
  `mem_idelesUnitsOutside`, `isOpen_idelesUnitsOutside` — the idèles that are local units outside a
  prescribed set of places form an open set (Mathlib `RestrictedProduct.isOpen_forall_imp_mem` at
  `A v := Place.localUnits K v` plus `Place.isOpen_localUnits`).  Note: the statement has to be
  phrased through the `def Idele` (with `exact`, not `simpa`), since `Idele K` is definitionally the
  restricted product but `simpa` does not see through it.
* `isOpen_idele_powAt` — the `p`-th power clause at the finite primes of `T` is open.  This uses the
  **local** input `NK.UchidaKummer.isOpenEllPowSubgroup` (`ellPowSubgroup = (powMonoidHom p).range`),
  already proved in the workspace (Hensel's lemma when `p` is a residue unit, the `p`-adic logarithm
  otherwise).
* `powAtPlaces`, `powTIdeles` — the place set of `T` and the subgroup `E` above as an explicit
  `Subgroup (Idele K)` (the shape of `KummerCase.kummerE` / `TIdeles`), with `mem_powTIdeles` and
  `isOpen_powTIdeles`.
* `map_principal_powTIdeles` and `isOpen_gesU` — `U = im(Kˣ · E)` is open in `C_K`: `Kˣ` lies in the
  kernel of the quotient map, so `U = im(E)`, and the image of an open set under the (open) quotient
  map is open.

The finite-index half of piece 1 is not here yet; see the note §3ter/§3quater for the route
(`P ⊔ E_congr ⊆ P ⊔ E` with `congruenceSubgroupId` and `Subgroup.index_antitone`, or the direct
class-group computation).
-/

open scoped NumberField RestrictedProduct

namespace Work.SSGRoute

variable {K : Type*} [Field K] [NumberField K]

/-! ## Openness of the unit clause -/

/-- **The idèles that are local units outside a prescribed set of places form an open set.**
Stated on the underlying restricted product, where the local-unit subgroups are the defining
`A v` (`RestrictedProduct.isOpen_forall_imp_mem`). -/
theorem isOpen_forall_mem_localUnits' (X : Set (NK.GlobalCFT.Place K)) :
    IsOpen {x : Πʳ v : NK.GlobalCFT.Place K,
        [(NK.GlobalCFT.Place.localField K v)ˣ, NK.GlobalCFT.Place.localUnits K v] |
      ∀ v : NK.GlobalCFT.Place K, v ∉ X → x v ∈ NK.GlobalCFT.Place.localUnits K v} :=
  RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : NK.GlobalCFT.Place K => (NK.GlobalCFT.Place.localField K v)ˣ)
    (A := fun v : NK.GlobalCFT.Place K => (NK.GlobalCFT.Place.localUnits K v : Set _))
    (p := fun v : NK.GlobalCFT.Place K => v ∉ X)
    (fun v => NK.GlobalCFT.Place.isOpen_localUnits v)

/-- The same statement for the idèle group `𝕀_K` (`Idele K` is definitionally the restricted
product above, so this is the previous lemma transported along the definition). -/
theorem isOpen_forall_mem_localUnits (X : Set (NK.GlobalCFT.Place K)) :
    IsOpen {x : NK.GlobalCFT.Idele K |
      ∀ v : NK.GlobalCFT.Place K, v ∉ X → x v ∈ NK.GlobalCFT.Place.localUnits K v} :=
  isOpen_forall_mem_localUnits' (K := K) X

/-- The set of idèles that are local units outside a prescribed set `X` of places, as a set of
idèles (this is `NK.GlobalCFTdeep.TIdeles` with the set presented as a complement). -/
def idelesUnitsOutside (K : Type*) [Field K] [NumberField K] (X : Set (NK.GlobalCFT.Place K)) :
    Set (NK.GlobalCFT.Idele K) :=
  {x | ∀ v : NK.GlobalCFT.Place K, v ∉ X → x v ∈ NK.GlobalCFT.Place.localUnits K v}

theorem mem_idelesUnitsOutside {X : Set (NK.GlobalCFT.Place K)} {x : NK.GlobalCFT.Idele K} :
    x ∈ idelesUnitsOutside K X ↔
      ∀ v : NK.GlobalCFT.Place K, v ∉ X → x v ∈ NK.GlobalCFT.Place.localUnits K v := Iff.rfl

theorem isOpen_idelesUnitsOutside (X : Set (NK.GlobalCFT.Place K)) :
    IsOpen (idelesUnitsOutside K X) :=
  isOpen_forall_mem_localUnits (K := K) X

/-! ## Openness of the `p`-th power clause -/

/-- **The `p`-th power clause at a finite set of primes is open**, stated on the underlying
restricted product (see the note in the module docstring about `Idele K` vs `Πʳ`). -/
theorem isOpen_powAt' {p : ℕ} (hp : p.Prime) (T : Finset (NK.Chebotarev.PrimeIdeal K)) :
    IsOpen {x : Πʳ v : NK.GlobalCFT.Place K,
        [(NK.GlobalCFT.Place.localField K v)ˣ, NK.GlobalCFT.Place.localUnits K v] |
      ∀ 𝔭 ∈ T, x (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
        (NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p : Set _)} := by
  rw [show {x : Πʳ v : NK.GlobalCFT.Place K,
        [(NK.GlobalCFT.Place.localField K v)ˣ, NK.GlobalCFT.Place.localUnits K v] |
      ∀ 𝔭 ∈ T, x (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
        (NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p : Set _)} =
      ⋂ 𝔭 ∈ T, {x : Πʳ v : NK.GlobalCFT.Place K,
          [(NK.GlobalCFT.Place.localField K v)ˣ, NK.GlobalCFT.Place.localUnits K v] |
        x (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
          (NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p : Set _)} from by
    ext x; simp]
  refine isOpen_biInter_finset fun 𝔭 _ => ?_
  have hcont : Continuous fun x : Πʳ v : NK.GlobalCFT.Place K,
      [(NK.GlobalCFT.Place.localField K v)ˣ, NK.GlobalCFT.Place.localUnits K v] =>
      x (NK.GlobalCFT.Place.ofFinite 𝔭) :=
    RestrictedProduct.continuous_eval
      (R := fun v : NK.GlobalCFT.Place K => (NK.GlobalCFT.Place.localField K v)ˣ)
      (A := fun v : NK.GlobalCFT.Place K => (NK.GlobalCFT.Place.localUnits K v : Set _))
      (NK.GlobalCFT.Place.ofFinite 𝔭)
  exact ((NK.UchidaKummer.Approximation.isOpenEllPowSubgroup K p hp) 𝔭).preimage hcont

/-- **The `p`-th power clause at a finite set of primes is open.**  The local input is
`NK.UchidaKummer.Approximation.isOpenEllPowSubgroup`. -/
theorem isOpen_idele_powAt {p : ℕ} (hp : p.Prime) (T : Finset (NK.Chebotarev.PrimeIdeal K)) :
    IsOpen {x : NK.GlobalCFT.Idele K | ∀ 𝔭 ∈ T,
      x (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
        (NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p : Set _)} :=
  isOpen_powAt' (K := K) hp T

/-! ## The subgroup `E` and the openness of `U` -/

/-- The set of places of `K` that lie above the finite primes of `T` (as a set of places; the
archimedean places are vacuously in it, where the unit condition is vacuous anyway). -/
def powAtPlaces (K : Type*) [Field K] [NumberField K]
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) : Set (NK.GlobalCFT.Place K) :=
  {v | ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, NK.GlobalCFT.Place.ofFinite 𝔭 = v → 𝔭 ∈ T}

/-- **The subgroup `E`.**  The idèles whose components at the primes of `T` are `p`-th powers and
whose components outside the places above `T` are local units. -/
def powTIdeles (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) : Subgroup (NK.GlobalCFT.Idele K) where
  carrier := {x | (∀ 𝔭 ∈ T, x (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
      (NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p : Set _)) ∧
    (∀ v : NK.GlobalCFT.Place K, v ∉ powAtPlaces K T →
        x v ∈ NK.GlobalCFT.Place.localUnits K v)}
  one_mem' := ⟨fun 𝔭 _ => Subgroup.one_mem _, fun v _ => Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨fun 𝔭 h𝔭 => by
        rw [NK.GlobalCFT.Idele.mul_apply]
        exact Subgroup.mul_mem _ (hx1 𝔭 h𝔭) (hy1 𝔭 h𝔭),
      fun v hv => by
        rw [NK.GlobalCFT.Idele.mul_apply]
        exact Subgroup.mul_mem _ (hx2 v hv) (hy2 v hv)⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨fun 𝔭 h𝔭 => by
        rw [NK.GlobalCFT.Idele.inv_apply]
        exact Subgroup.inv_mem _ (hx1 𝔭 h𝔭),
      fun v hv => by
        rw [NK.GlobalCFT.Idele.inv_apply]
        exact Subgroup.inv_mem _ (hx2 v hv)⟩

@[simp] theorem mem_powTIdeles {p : ℕ} {T : Finset (NK.Chebotarev.PrimeIdeal K)}
    {x : NK.GlobalCFT.Idele K} :
    x ∈ powTIdeles K p T ↔
      (∀ 𝔭 ∈ T, x (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
          (NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p : Set _)) ∧
      (∀ v : NK.GlobalCFT.Place K, v ∉ powAtPlaces K T →
          x v ∈ NK.GlobalCFT.Place.localUnits K v) := Iff.rfl

/-- **`E` is open.** -/
theorem isOpen_powTIdeles {p : ℕ} (hp : p.Prime)
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) :
    IsOpen (powTIdeles K p T : Set (NK.GlobalCFT.Idele K)) := by
  have hset : (powTIdeles K p T : Set (NK.GlobalCFT.Idele K)) =
      {x : NK.GlobalCFT.Idele K | ∀ 𝔭 ∈ T,
          x (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
            (NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p : Set _)} ∩
        idelesUnitsOutside K (powAtPlaces K T) := rfl
  rw [hset]
  exact (isOpen_idele_powAt (K := K) hp T).inter (isOpen_idelesUnitsOutside _)

/-- The kernel of the quotient map `𝕀_K → C_K` is the group of principal idèles. -/
theorem ker_mk_eq_principal :
    (NK.GlobalCFT.IdeleClassGroup.mk K).ker = NK.GlobalCFT.Idele.principalSubgroup K := by
  ext x
  rw [MonoidHom.mem_ker, ← map_one (NK.GlobalCFT.IdeleClassGroup.mk K),
    NK.GlobalCFT.IdeleClassGroup.mk_eq_mk_iff]
  simp [NK.GlobalCFT.Idele.mem_principalSubgroup]

/-- `U = im(Kˣ · E)` is the image of `E` alone, since `Kˣ` lies in the kernel of the quotient
map. -/
theorem map_principal_powTIdeles {p : ℕ} (T : Finset (NK.Chebotarev.PrimeIdeal K)) :
    ((NK.GlobalCFT.Idele.principalSubgroup K ⊔ powTIdeles K p T).map
        (NK.GlobalCFT.IdeleClassGroup.mk K)) =
      (powTIdeles K p T).map (NK.GlobalCFT.IdeleClassGroup.mk K) := by
  have hbot : Subgroup.map (NK.GlobalCFT.IdeleClassGroup.mk K)
      (NK.GlobalCFT.Idele.principalSubgroup K) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    change NK.GlobalCFT.Idele.principalSubgroup K ≤
      (NK.GlobalCFT.IdeleClassGroup.mk K).ker
    rw [ker_mk_eq_principal]
  rw [Subgroup.map_sup, hbot, bot_sup_eq]

/-- **`U = im(Kˣ · E)` is open in the idèle class group.** -/
theorem isOpen_gesU {p : ℕ} (hp : p.Prime) (T : Finset (NK.Chebotarev.PrimeIdeal K)) :
    IsOpen (((NK.GlobalCFT.Idele.principalSubgroup K ⊔ powTIdeles K p T).map
      (NK.GlobalCFT.IdeleClassGroup.mk K) : Subgroup (NK.GlobalCFT.IdeleClassGroup K)) :
        Set (NK.GlobalCFT.IdeleClassGroup K)) := by
  rw [map_principal_powTIdeles (K := K) (p := p) T,
    Subgroup.coe_map]
  exact QuotientGroup.isOpenMap_coe (N := NK.GlobalCFT.Idele.principalSubgroup K) _
    (isOpen_powTIdeles (K := K) hp T)

end Work.SSGRoute
