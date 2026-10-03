/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conjugation by a unit, and the `τ`-invariance of `D_{N,U_N}`

Step B of the construction of `Thm61Step` needs the twist `τ` (`(ofAdd k) • x = φ(t)^k x φ(t)^{-k}`)
on the division closure `D_{N,U_N}` of `φ(K[N])` in `U_N = starRegularClosure
(starSubringClosure (range φ_N))`.

The mathematical content is the normality of `N` in `H`: conjugation by `t` permutes the
group-like generators `φ_N (single n 1)` of `D_{N,U_N}`, hence (being a ring automorphism) it
preserves the division closure.  This is the input to the twist on `D_{N,P}` required by
`Prop51Data`.
-/
import Mathlib
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.DivisionClosure.mapsTo_divisionClosure_of_image_eq
import Submission.Work.Section6.StepA
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecompAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ORHughesFree

/-- **Conjugation by a unit of a ring, as a ring automorphism**: `x ↦ u x u⁻¹`. -/
noncomputable def conjRingEquiv {U : Type} [Ring U] (u : Uˣ) : U ≃+* U where
  toFun x := (u : U) * x * ((u⁻¹ : Uˣ) : U)
  invFun x := ((u⁻¹ : Uˣ) : U) * x * (u : U)
  left_inv x := by
    show ((u⁻¹ : Uˣ) : U) * ((u : U) * x * ((u⁻¹ : Uˣ) : U)) * (u : U) = x
    rw [show ((u⁻¹ : Uˣ) : U) * ((u : U) * x * ((u⁻¹ : Uˣ) : U)) * (u : U)
        = (((u⁻¹ : Uˣ) : U) * (u : U)) * x * (((u⁻¹ : Uˣ) : U) * (u : U)) by noncomm_ring,
      Units.inv_mul]
    simp
  right_inv x := by
    show (u : U) * (((u⁻¹ : Uˣ) : U) * x * (u : U)) * ((u⁻¹ : Uˣ) : U) = x
    rw [show (u : U) * (((u⁻¹ : Uˣ) : U) * x * (u : U)) * ((u⁻¹ : Uˣ) : U)
        = ((u : U) * ((u⁻¹ : Uˣ) : U)) * x * ((u : U) * ((u⁻¹ : Uˣ) : U)) by noncomm_ring,
      Units.mul_inv]
    simp
  map_mul' x y := by
    show (u : U) * (x * y) * ((u⁻¹ : Uˣ) : U) =
      ((u : U) * x * ((u⁻¹ : Uˣ) : U)) * ((u : U) * y * ((u⁻¹ : Uˣ) : U))
    rw [show ((u : U) * x * ((u⁻¹ : Uˣ) : U)) * ((u : U) * y * ((u⁻¹ : Uˣ) : U))
        = (u : U) * x * (((u⁻¹ : Uˣ) : U) * (u : U)) * y * ((u⁻¹ : Uˣ) : U) by noncomm_ring,
      Units.inv_mul]
    simp [mul_assoc]
  map_add' x y := by
    show (u : U) * (x + y) * ((u⁻¹ : Uˣ) : U) =
      (u : U) * x * ((u⁻¹ : Uˣ) : U) + (u : U) * y * ((u⁻¹ : Uˣ) : U)
    noncomm_ring

theorem conjRingEquiv_apply {U : Type} [Ring U] (u : Uˣ) (x : U) :
    conjRingEquiv u x = (u : U) * x * ((u⁻¹ : Uˣ) : U) := rfl

end Work.ORHughesFree

namespace Work.Section6

open Work.ORHughesFree
open Work.ORHughesFree.DivisionClosure

variable {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H} {t : H}

/-- **The generator set `range φ_N` is invariant under conjugation by `φ(t)`** (i.e. under the
twist `τ`), because `N ⊴ H`: conjugation by `t` permutes the group-like elements of `K[N]`, and
this is exactly the identity `Work.ORHughesFree.HughesFree.inclN_smul` for `k = 1`. -/
theorem conj_uUnit_phiN_key
    (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    [SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K))
    {U : Type} [Ring U] (φ : MonoidAlgebra K G →+* U) (a : MonoidAlgebra K N) :
    (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K)) * phiN φ H N a *
        (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K)) =
      phiN φ H N ((Multiplicative.ofAdd (1 : ℤ)) • a) := by
  rw [show phiN φ H N ((Multiplicative.ofAdd (1 : ℤ)) • a) =
      (φ.comp (inducedMapRing (K := K) H))
        (HughesFree.inclN K H N ((Multiplicative.ofAdd (1 : ℤ)) • a)) from rfl,
    HughesFree.inclN_smul (K := K) htN hact (1 : ℤ) a,
    show phiN φ H N a = (φ.comp (inducedMapRing (K := K) H))
        (HughesFree.inclN K H N a) from rfl,
    map_mul, map_mul, zpow_one, zpow_neg_one]

/-- **`D_{N,U_N}` is invariant under conjugation by `φ(t)`.** -/
theorem conj_uUnit_phiN_mem
    (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    [SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K))
    {U : Type} [Ring U] [StarRing U] [IsStarRegular U] (φ : MonoidAlgebra K G →+* U) :
    Set.MapsTo (conjRingEquiv (uUnit φ H t))
      (divisionClosure (Set.range (phiN φ H N)))
      (divisionClosure (Set.range (phiN φ H N))) := by
  set D : Subring U := divisionClosure (Set.range (phiN φ H N)) with hD
  set f : U →+* U := (conjRingEquiv (uUnit φ H t)).toRingHom with hf
  have hgen : Set.range (phiN φ H N) ⊆ ((D.comap f : Subring U) : Set U) := by
    rintro x ⟨a, rfl⟩
    have hx : f (phiN φ H N a) = phiN φ H N ((Multiplicative.ofAdd (1 : ℤ)) • a) := by
      rw [hf]
      change (uUnit φ H t : U) * phiN φ H N a * (((uUnit φ H t)⁻¹ : Uˣ) : U) =
        phiN φ H N ((Multiplicative.ofAdd (1 : ℤ)) • a)
      rw [uUnit_val, uUnit_inv_val]
      exact conj_uUnit_phiN_key htN hact φ a
    exact subset_divisionClosure _ ⟨_, hx.symm⟩
  have hT : ∀ x ∈ D.comap f, ∀ y, x * y = 1 → y * x = 1 → y ∈ D.comap f := by
    intro x hx y hxy hyx
    refine inverse_mem_divisionClosure hx ?_ ?_
    · rw [← map_mul, hxy, map_one]
    · rw [← map_mul, hyx, map_one]
  have hle : D ≤ D.comap f :=
    le_trans (divisionClosure_mono hgen) (divisionClosure_le_of_invClosed _ hT)
  intro x hx
  exact hle hx

end Work.Section6
