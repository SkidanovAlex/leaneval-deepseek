/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Step A of the construction of `Thm61Step`: the ambient ring `P = P^{U_N}_{ω,τ}`

[JZLA20, Theorem 6.1]: for a finitely generated subgroup `H ≤ G` (with `G` locally indicable),
a normal `N ⊴ H` with `H/N ≅ ℤ` and a generator `t` of `H` modulo `N`, the *ambient ring*
`P = P^{U_N}_{ω,τ}` is the ultraproduct of [JZLA20, (4)] applied to the `∗`-regular closure
`U_N` of `φ(K[N])` in `U`, equipped with the twist `τ = conj by φ(t)`.

This file constructs:

* `phiN`, the map `K[↥N] →+* U`;
* `UN`, the `∗`-subring `U_N = starRegularClosure (starSubringClosure (range phiN)) ⊆ U`;
* `uUnit`, the unit `φ t` of `U`;
* `tauAction`, the `Multiplicative ℤ`-action on `U_N` given by conjugation by `φ(t)`;
* `rkN`, the pullback of `rkU` to `U_N`, with its faithfulness and `τ`-compatibility;
* `stepA_envelope_exists`: the existence of the natural extension `rkE` of `rkN` and of the
  series envelope `P = P^{U_N}_{ω,τ}` with the injective series map `Ψ : U_N((t;τ)) →+* P`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.Thm61Step
import Submission.Work.ORHughesFree.HughesFree
import Submission.Work.ORHughesFree.Section6.ConjAction
import Submission.Work.ORHughesFree.NaturalExtension.SeriesEnvelope
import Submission.Work.ORHughesFree.NaturalExtension.naturalExtension_exists
import Submission.Work.ORHughesFree.NaturalExtension.starRegular_subring_positiveDefinite
import Submission.Work.ORHughesFree.Instances
import Submission.Work.Section6.seriesEnvelope_exists
import Submission.Work.Section6.starRegularClosure_range_conj
import Submission.Work.Section6.conj_zpow_star
import Submission.Work.Subring.conjRingEquiv_exists
import Submission.Work.RankAPI.rk_map_conj

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Section6

open Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U] [StarRing U]
  [IsStarRegular U]

/-- The composite `K[↥N] →+* K[↥H] →+* K[G] →+* U`. -/
noncomputable def phiN (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H) :
    MonoidAlgebra K ↥N →+* U :=
  (φ.comp (inducedMapRing (K := K) H)).comp (MonoidAlgebra.mapDomainRingHom K N.subtype)

/-- The `∗`-regular closure `U_N` of the image of `K[↥N]` in `U` ([JZLA20, Theorem 6.1]). -/
noncomputable def UN (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H) :
    StarSubring U :=
  starRegularClosure (starSubringClosure (Set.range (phiN φ H N)))

/-- The carrier of `U_N`. -/
abbrev UNty (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H) : Type _ :=
  ↥(UN φ H N)

/-- `U_N` as a subring of `U`. -/
noncomputable def UNsub (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H) :
    Subring U :=
  (UN φ H N).toSubring

theorem mem_UN {φ : MonoidAlgebra K G →+* U} {H : Subgroup G} {N : Subgroup H} {x : U}
    (hx : x ∈ Set.range (phiN φ H N)) : x ∈ (UN φ H N : Set U) :=
  subset_starRegularClosure _ (subset_starSubringClosure _ hx)

/-- `U_N` is `∗`-regular. -/
instance instIsStarRegularUN (φ : MonoidAlgebra K G →+* U) (H : Subgroup G)
    (N : Subgroup H) : IsStarRegular (UNty φ H N) :=
  instIsStarRegularStarRegularClosure (starSubringClosure (Set.range (phiN φ H N)))

/-- `U_N` is positive definite. -/
theorem hposN (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hpos : IsPositiveDefiniteStarRegular U) : IsPositiveDefiniteStarRegular (UNty φ H N) :=
  NaturalExtension.starRegular_subring_positiveDefinite (Subring.subtype (UNsub φ H N))
    Subtype.coe_injective (fun v => rfl) hpos

/-- The image of `K[↥N]` inside `U_N`. -/
noncomputable def phiNcod (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H) :
    MonoidAlgebra K ↥N →+* UNty φ H N where
  toFun x := ⟨phiN φ H N x, mem_UN ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

@[simp] theorem phiNcod_apply (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (x : MonoidAlgebra K ↥N) : ((phiNcod φ H N x : UNty φ H N) : U) = phiN φ H N x := rfl

/-- The coercion of `U_N` commutes with `star`. -/
@[simp] theorem star_coe_UN {φ : MonoidAlgebra K G →+* U} {H : Subgroup G} {N : Subgroup H}
    (z : UNty φ H N) : ((star z : UNty φ H N) : U) = star (z : U) := rfl

/-- The unit `φ (single t 1)` of `U`. -/
noncomputable def uUnit (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (t : H) : Uˣ where
  val := (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t 1)
  inv := (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ 1)
  val_inv := by
    have h : MonoidAlgebra.single t (1 : K) * MonoidAlgebra.single t⁻¹ (1 : K) = 1 := by
      rw [MonoidAlgebra.single_mul_single, mul_inv_cancel, one_mul]
      exact MonoidAlgebra.one_def.symm
    rw [← map_mul, h, map_one]
  inv_val := by
    have h : MonoidAlgebra.single t⁻¹ (1 : K) * MonoidAlgebra.single t (1 : K) = 1 := by
      rw [MonoidAlgebra.single_mul_single, inv_mul_cancel, one_mul]
      exact MonoidAlgebra.one_def.symm
    rw [← map_mul, h, map_one]

@[simp] theorem uUnit_val (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (t : H) :
    ((uUnit φ H t : Uˣ) : U) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K)) := rfl

@[simp] theorem uUnit_inv_val (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (t : H) :
    (((uUnit φ H t)⁻¹ : Uˣ) : U) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K)) := rfl

/-- `U_N` is invariant under conjugation by the unitary `φ(t)` ([JZLA20, Theorem 6.1], from the
normality of `N` in `H`). -/
theorem UN_conj_mem (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K))) :
    (∀ x ∈ (UN φ H N : Set U),
        ((uUnit φ H t : Uˣ) : U) * x * (((uUnit φ H t)⁻¹ : Uˣ) : U) ∈ (UN φ H N : Set U)) ∧
      (∀ x ∈ (UN φ H N : Set U),
        (((uUnit φ H t)⁻¹ : Uˣ) : U) * x * ((uUnit φ H t : Uˣ) : U) ∈ (UN φ H N : Set U)) :=
  starRegularClosure_range_conj φ H N hN t hstar

/-- The inner automorphism of `U_N` given by conjugation by `φ(t)`. -/
noncomputable def conjUN (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K))) :
    UNty φ H N ≃+* UNty φ H N :=
  (Work.Subring.conjRingEquiv_exists (UNsub φ H N) (uUnit φ H t)
    (UN_conj_mem φ H N hN t hstar).1 (UN_conj_mem φ H N hN t hstar).2).choose

theorem conjUN_apply (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K)))
    (x : UNty φ H N) :
    ((conjUN φ H N hN t hstar x : UNty φ H N) : U) =
      ((uUnit φ H t : Uˣ) : U) * (x : U) * (((uUnit φ H t)⁻¹ : Uˣ) : U) :=
  (Work.Subring.conjRingEquiv_exists (UNsub φ H N) (uUnit φ H t)
    (UN_conj_mem φ H N hN t hstar).1 (UN_conj_mem φ H N hN t hstar).2).choose_spec.1 x

theorem conjUN_symm_apply (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K)))
    (x : UNty φ H N) :
    (((conjUN φ H N hN t hstar).symm x : UNty φ H N) : U) =
      (((uUnit φ H t)⁻¹ : Uˣ) : U) * (x : U) * ((uUnit φ H t : Uˣ) : U) :=
  (Work.Subring.conjRingEquiv_exists (UNsub φ H N) (uUnit φ H t)
    (UN_conj_mem φ H N hN t hstar).1 (UN_conj_mem φ H N hN t hstar).2).choose_spec.2 x

/-- Powers of a ring automorphism preserve `star` if the automorphism does. -/
theorem ringEquiv_zpow_star {S : Type} [Ring S] [StarRing S] (e : S ≃+* S)
    (he : ∀ x : S, star (e x) = e (star x)) (k : ℤ) (x : S) :
    star ((e ^ k) x) = (e ^ k) (star x) := by
  have hes : ∀ y : S, star (e⁻¹ y) = e⁻¹ (star y) := by
    intro y
    have h : star y = e (star (e⁻¹ y)) := by
      have h2 := he (e⁻¹ y)
      rwa [show e (e⁻¹ y) = y from by simp] at h2
    have h3 : e⁻¹ (star y) = star (e⁻¹ y) := by
      rw [h]
      simp
    exact h3.symm
  exact zpow_induction_right (g := e)
    (P := fun w : S ≃+* S => ∀ x : S, star (w x) = w (star x)) (fun x => by simp)
    (fun a ha x => by
      rw [show (a * e) x = a (e x) from by simp,
        show (a * e) (star x) = a (e (star x)) from by simp, ha, he])
    (fun a ha x => by
      rw [show (a * e⁻¹) x = a (e⁻¹ x) from by simp,
        show (a * e⁻¹) (star x) = a (e⁻¹ (star x)) from by simp, ha, hes]) k x

/-- `φ(t)` is a unitary of `U`. -/
theorem uUnit_star (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K))) :
    star ((uUnit φ H t : Uˣ) : U) = (((uUnit φ H t)⁻¹ : Uˣ) : U) := hstar

/-- The inner automorphism `conjUN` commutes with `star`. -/
theorem conjUN_star (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K)))
    (x : UNty φ H N) :
    star (conjUN φ H N hN t hstar x) = conjUN φ H N hN t hstar (star x) := by
  apply Subtype.ext
  rw [star_coe_UN, conjUN_apply, conjUN_apply, star_coe_UN]
  simpa using conj_zpow_star (uUnit φ H t) (uUnit_star φ H t hstar) 1 (x : U)

/-- `star` commutes with the powers of the twist. -/
theorem conjUN_zpow_star (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K)))
    (k : ℤ) (x : UNty φ H N) :
    star ((conjUN φ H N hN t hstar ^ k) x) = (conjUN φ H N hN t hstar ^ k) (star x) :=
  ringEquiv_zpow_star _ (conjUN_star φ H N hN t hstar) k x

/-- **The twist `τ` of [JZLA20, Theorem 6.1]**: `Multiplicative ℤ` acts on `U_N` by
`(ofAdd k) • x = φ(t)^k x φ(t)^{-k}`, the extension to `U_N` of the automorphism of `K[N]` given
by left conjugation by `t`. -/
noncomputable def tauAction (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K))) :
    MulSemiringAction (Multiplicative ℤ) (UNty φ H N) :=
  Work.ORHughesFree.RingEquiv.mulSemiringActionZpow (conjUN φ H N hN t hstar)

/-- The action of the twist on `ofAdd k` is the `k`-th power of `conjUN`. -/
theorem tauAction_smul_eq (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K)))
    (k : ℤ) (x : UNty φ H N) :
    letI := tauAction φ H N hN t hstar
    ((Multiplicative.ofAdd k) • x) = (conjUN φ H N hN t hstar ^ k) x := by
  letI := tauAction φ H N hN t hstar
  exact Work.ORHughesFree.RingEquiv.mulSemiringActionZpow_smul (conjUN φ H N hN t hstar) k x

/-- The formula for the twist at the generator `k = 1`. -/
theorem tauAction_one_smul (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K)))
    (x : UNty φ H N) :
    letI := tauAction φ H N hN t hstar
    (((Multiplicative.ofAdd (1 : ℤ)) • x : UNty φ H N) : U) =
      ((uUnit φ H t : Uˣ) : U) * (x : U) * (((uUnit φ H t)⁻¹ : Uˣ) : U) := by
  letI := tauAction φ H N hN t hstar
  rw [tauAction_smul_eq φ H N hN t hstar 1 x, zpow_one]
  exact conjUN_apply φ H N hN t hstar x

/-- **The twist is `∗`-compatible**. -/
theorem tauAction_star (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K))) :
    letI := tauAction φ H N hN t hstar
    ∀ (m : Multiplicative ℤ) (x : UNty φ H N), star (m • x) = m • star x := by
  letI := tauAction φ H N hN t hstar
  intro m x
  have hm : m = Multiplicative.ofAdd (Multiplicative.toAdd m) := rfl
  rw [hm, tauAction_smul_eq φ H N hN t hstar (Multiplicative.toAdd m) x,
    tauAction_smul_eq φ H N hN t hstar (Multiplicative.toAdd m) (star x)]
  exact conjUN_zpow_star φ H N hN t hstar _ x

/-- The pullback of `rkU` to `U_N`. -/
noncomputable def rkN (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (rkU : SylvesterRank U) : SylvesterRank (UNty φ H N) :=
  SylvesterRank.pullback (Subring.subtype (UNsub φ H N)) rkU

/-- `rkN` is faithful if `rkU` is. -/
theorem rkN_faithful (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (rkU : SylvesterRank U) (hfaith : rkU.IsFaithful) : (rkN φ H N rkU).IsFaithful := by
  intro a ha
  have h1 : rkU.rk 1 1 (oneByOne (a : U)) = 0 := ha
  exact Subtype.ext (hfaith (a : U) h1)

/-- **The twist is rank-preserving**: `rkN` is `τ`-compatible. -/
theorem rkN_tauCompatible (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K)))
    (rkU : SylvesterRank U) :
    letI := tauAction φ H N hN t hstar
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (UNty φ H N)),
      (rkN φ H N rkU).rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) =
        (rkN φ H N rkU).rk n m A := by
  letI := tauAction φ H N hN t hstar
  intro n m A
  have hmap : (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)).map
        (Subring.subtype (UNsub φ H N)) =
      (A.map (Subring.subtype (UNsub φ H N))).map
        (fun y : U => ((uUnit φ H t : Uˣ) : U) * y * (((uUnit φ H t)⁻¹ : Uˣ) : U)) := by
    ext i j
    simp only [Matrix.map_apply]
    exact tauAction_one_smul φ H N hN t hstar (A i j)
  show rkU.rk n m ((A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)).map
      (Subring.subtype (UNsub φ H N))) =
    rkU.rk n m (A.map (Subring.subtype (UNsub φ H N)))
  rw [hmap]
  exact Work.RankAPI.rk_map_conj rkU (uUnit φ H t) n m (A.map (Subring.subtype (UNsub φ H N)))

/-! ### The ambient ring `P = P^{U_N}_{ω,τ}` -/

/-- **Step A**: the natural extension `rkE` of `rkN` to the skew Laurent polynomial ring, and the
series envelope `P = P^{U_N}_{ω,τ}` with its structure map `f_ω` and its injective series map
`Ψ : U_N((t;τ)) →+* P` ([JZLA20, (4)]). -/
theorem stepA_envelope_exists (hpos : IsPositiveDefiniteStarRegular U)
    (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H) (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K)))
    (rkU : SylvesterRank U) (hfaith : rkU.IsFaithful)
    [tau : MulSemiringAction (Multiplicative ℤ) (UNty φ H N)]
    (hstarτ : ∀ (m : Multiplicative ℤ) (x : UNty φ H N), star (m • x) = m • star x)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (UNty φ H N)),
      (rkN φ H N rkU).rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) =
        (rkN φ H N rkU).rk n m A) :
    ∃ rkE : SylvesterRank (SkewMonoidAlgebra (UNty φ H N) (Multiplicative ℤ)),
      IsNaturalExtension (rkN φ H N rkU) rkE ∧
      Nonempty (Work.ORHughesFree.NaturalExtension.SeriesEnvelope (U := UNty φ H N)
        (hposN φ H N hpos) (rkN φ H N rkU) hstarτ hτ rkE) := by
  haveI : IsPositiveDefiniteStarRegular (UNty φ H N) := hposN φ H N hpos
  obtain ⟨rkE, hE⟩ := NaturalExtension.naturalExtension_exists (rkN φ H N rkU) hτ
  exact ⟨rkE, hE,
    seriesEnvelope_exists (hposN φ H N hpos) (rkN φ H N rkU)
      (rkN_faithful φ H N rkU hfaith) hstarτ hτ rkE hE⟩

end Work.Section6
