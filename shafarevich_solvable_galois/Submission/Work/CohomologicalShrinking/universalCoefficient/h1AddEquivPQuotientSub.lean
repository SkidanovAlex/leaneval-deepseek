/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The universal-coefficient identification `H₁(S, A) ≅ A ⊗ S/S'Sᵖ` for `S`-trivial `A`

Let `p` be a prime, `Γ` a group, `S ≤ Γ` a subgroup and `A` a `𝔽_p`-linear representation of `Γ`
on which `S` acts trivially.  Then

  `H₁(S, A) ≅ A ⊗_{𝔽_p} S/(S'Sᵖ)`,

the "universal coefficient" form of `H₁` of a group acting trivially, with the elementary abelian
quotient `S/(S'Sᵖ)` written as `Additive (pCentralQuotient p S 0)`.

The proof has two ingredients.

* Mathlib's `groupHomology.H1AddEquivOfIsTrivial` identifies `H₁(S, A) ≅ Sᵃᵇ ⊗_ℤ A` because `S`
  acts trivially on `A`.
* Since `A` is an `𝔽_p`-module, `Sᵃᵇ ⊗_ℤ A ≅ (Sᵃᵇ/pSᵃᵇ) ⊗_{𝔽_p} A`; the second ingredient is
  therefore an identification of `Sᵃᵇ/pSᵃᵇ` with `Additive (pCentralQuotient p S 0)`, which is
  obtained from the surjection `Abelianization S → pCentralQuotient p S 0`.

The general base-change step is isolated in `tensorQuotSMulAddEquiv`: if `π : M →+ N` is a
surjective additive map onto an `𝔽_p`-module `N` whose kernel consists of `p`-divisible elements,
then `M ⊗_ℤ V ≅ N ⊗_{𝔽_p} V` for every `𝔽_p`-module `V`.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Semidirect
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

set_option linter.unusedSectionVars false

namespace Work.CohomologicalShrinking.universalCoefficient

open scoped TensorProduct
open scoped IsMulCommutative

universe u

/-! ## A base-change lemma for `p`-divisible kernels -/

/-- **Base change along a `p`-divisible surjection.**
If `π : M →+ N` is a surjective additive homomorphism onto an `𝔽_p`-module `N` whose kernel
consists of `p`-divisible elements (`m ∈ ker π → ∃ z, m = p • z`), then for every `𝔽_p`-module `V`
the tensor power `M ⊗_ℤ V` is isomorphic to `N ⊗_{𝔽_p} V`. -/
theorem tensorQuotSMulAddEquiv (p : ℕ) [NeZero p] {M : Type u} [AddCommGroup M]
    {N : Type u} [AddCommGroup N] [Module (ZMod p) N]
    (π : M →+ N) (hπ : Function.Surjective π)
    (hker : ∀ m, π m = 0 → ∃ z, m = (p : ℤ) • z)
    (V : Type u) [AddCommGroup V] [Module (ZMod p) V] :
    Nonempty (M ⊗[ℤ] V ≃+ N ⊗[ZMod p] V) := by
  classical
  haveI : TensorProduct.CompatibleSMul ℤ (ZMod p) N V :=
    ⟨fun r m n => by
      have h1 : r • m = (r.val : ℤ) • m := by
        rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (ZMod p) r.val m, ZMod.natCast_zmod_val]
      have h2 : r • n = (r.val : ℤ) • n := by
        rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (ZMod p) r.val n, ZMod.natCast_zmod_val]
      rw [h1, h2, TensorProduct.smul_tmul]⟩
  have hpV : ∀ v : V, (p : ℤ) • v = 0 := by
    intro v
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (ZMod p) p v, ZMod.natCast_self]
    exact zero_smul _ _
  have hpmul : ∀ (z : M) (v : V), ((p : ℤ) • z) ⊗ₜ[ℤ] v = 0 := by
    intro z v
    rw [TensorProduct.smul_tmul, hpV, TensorProduct.tmul_zero]
  let σ : N → M := fun n => Classical.choose (hπ n)
  have hσ : ∀ n, π (σ n) = n := fun n => Classical.choose_spec (hπ n)
  have hσ_add : ∀ n n' : N, ∃ z : M, σ (n + n') = σ n + σ n' + (p:ℤ) • z := by
    intro n n'
    obtain ⟨z, hz⟩ := hker (σ (n + n') - σ n - σ n')
      (by rw [map_sub, map_sub, hσ, hσ, hσ]; abel)
    have h1 := sub_eq_iff_eq_add.mp hz
    have h2 := sub_eq_iff_eq_add.mp h1
    exact ⟨z, by rw [h2]; abel⟩
  have hσ_zero : ∃ z : M, σ 0 = (p:ℤ) • z := by
    obtain ⟨z, hz⟩ := hker (σ 0) (hσ 0)
    exact ⟨z, hz⟩
  have hσ_smul : ∀ (r : ℤ) (n : N), ∃ z : M, σ (r • n) = r • σ n + (p:ℤ) • z := by
    intro r n
    obtain ⟨z, hz⟩ := hker (σ (r • n) - r • σ n) (by rw [map_sub, map_zsmul, hσ, hσ]; abel)
    exact ⟨z, by rw [sub_eq_iff_eq_add.mp hz]; abel⟩
  have hσ_eq : ∀ m : M, ∃ z : M, σ (π m) = m + (p:ℤ) • z := by
    intro m
    obtain ⟨z, hz⟩ := hker (σ (π m) - m) (by rw [map_sub, hσ]; abel)
    exact ⟨z, by rw [sub_eq_iff_eq_add.mp hz]; abel⟩
  let F : M ⊗[ℤ] V →+ N ⊗[ZMod p] V :=
    TensorProduct.liftAddHom
      { toFun := fun m => { toFun := fun v => π m ⊗ₜ[ZMod p] v
                            map_zero' := by simp
                            map_add' := fun v v' => by rw [TensorProduct.tmul_add] }
        map_zero' := by ext v; simp
        map_add' := fun m m' => by
          ext v
          change π (m + m') ⊗ₜ[ZMod p] v = π m ⊗ₜ[ZMod p] v + π m' ⊗ₜ[ZMod p] v
          rw [map_add, TensorProduct.add_tmul] }
      (fun r m v => by
        show π (r • m) ⊗ₜ[ZMod p] v = π m ⊗ₜ[ZMod p] (r • v)
        rw [map_zsmul, TensorProduct.smul_tmul])
  have hF : ∀ (m : M) (v : V), F (m ⊗ₜ[ℤ] v) = π m ⊗ₜ[ZMod p] v := by
    intro m v
    exact TensorProduct.liftAddHom_tmul _ _ m v
  let g₀ : N ⊗[ℤ] V →+ M ⊗[ℤ] V :=
    TensorProduct.liftAddHom
      { toFun := fun n => { toFun := fun v => σ n ⊗ₜ[ℤ] v
                            map_zero' := by simp
                            map_add' := fun v v' => by rw [TensorProduct.tmul_add] }
        map_zero' := by
          ext v
          change σ 0 ⊗ₜ[ℤ] v = 0
          obtain ⟨z, hz⟩ := hσ_zero
          rw [hz, hpmul]
        map_add' := fun n n' => by
          ext v
          change σ (n + n') ⊗ₜ[ℤ] v = σ n ⊗ₜ[ℤ] v + σ n' ⊗ₜ[ℤ] v
          obtain ⟨z, hz⟩ := hσ_add n n'
          rw [hz, TensorProduct.add_tmul, TensorProduct.add_tmul, hpmul, add_zero] }
      (fun r n v => by
        show σ (r • n) ⊗ₜ[ℤ] v = σ n ⊗ₜ[ℤ] (r • v)
        obtain ⟨z, hz⟩ := hσ_smul r n
        rw [hz, TensorProduct.add_tmul, hpmul, add_zero, TensorProduct.smul_tmul])
  let G : N ⊗[ZMod p] V →+ M ⊗[ℤ] V :=
    g₀.comp ((TensorProduct.mapOfCompatibleSMul ℤ (ZMod p) (ZMod p) N V).toAddMonoidHom)
  have hG : ∀ (n : N) (v : V), G (n ⊗ₜ[ZMod p] v) = σ n ⊗ₜ[ℤ] v := by
    intro n v
    show g₀ ((TensorProduct.mapOfCompatibleSMul ℤ (ZMod p) (ZMod p) N V)
      (n ⊗ₜ[ZMod p] v)) = σ n ⊗ₜ[ℤ] v
    rw [TensorProduct.mapOfCompatibleSMul_tmul]
    exact TensorProduct.liftAddHom_tmul _ _ n v
  have hGF : ∀ x : M ⊗[ℤ] V, G (F x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m v =>
      rw [hF m v, hG (π m) v]
      obtain ⟨z, hz⟩ := hσ_eq m
      rw [hz, TensorProduct.add_tmul, hpmul, add_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hFG : ∀ y : N ⊗[ZMod p] V, F (G y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul n v => rw [hG n v, hF (σ n) v, hσ n]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact ⟨AddEquiv.ofBijective F ⟨fun a b hab => by
    have h := congrArg G hab
    rwa [hGF a, hGF b] at h, fun y => ⟨G y, hFG y⟩⟩⟩

/-! ## The surjection `Abelianization S → pCentralQuotient p S 0` -/

variable (p : ℕ) (G : Type) [Group G]

/-- The canonical surjection `S → S/(S'Sᵖ) = pCentralQuotient p S 0`, written as the composite of
`S ≃ S` (the identification of `S` with the top subgroup) followed by the quotient map. -/
noncomputable def pQuotMap : G →* Work.Shrinking.pCentralQuotient p G 0 :=
  (QuotientGroup.mk' ((Work.Shrinking.pCentralSeries p G 1).subgroupOf
      (Work.Shrinking.pCentralSeries p G 0))).comp
    (Subgroup.topEquiv (G := G)).symm.toMonoidHom

/-- The kernel of `pQuotMap` is the second term of the descending `p`-central series. -/
theorem pQuotMap_ker : (pQuotMap p G).ker = Work.Shrinking.pCentralSeries p G 1 := by
  ext x
  show x ∈ (Subgroup.topEquiv (G := G)).symm.toMonoidHom ⁻¹'
      (QuotientGroup.mk' ((Work.Shrinking.pCentralSeries p G 1).subgroupOf
        ⊤)).ker ↔ x ∈ Work.Shrinking.pCentralSeries p G 1
  rw [QuotientGroup.ker_mk', Set.mem_preimage]
  change ((Subgroup.topEquiv (G := G)).symm x : ↥(⊤ : Subgroup G)) ∈
      (Work.Shrinking.pCentralSeries p G 1).subgroupOf (⊤ : Subgroup G) ↔
    x ∈ Work.Shrinking.pCentralSeries p G 1
  rw [Subgroup.mem_subgroupOf]
  simp

/-- The canonical surjection `S → S/(S'Sᵖ)` is surjective. -/
theorem pQuotMap_surjective : Function.Surjective (pQuotMap p G) :=
  (QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv (G := G)).symm.surjective

/-- The canonical map `Sᵃᵇ → S/(S'Sᵖ)`, induced by `pQuotMap` through the abelianization. -/
noncomputable def abToPQuot : Abelianization G →* Work.Shrinking.pCentralQuotient p G 0 :=
  Abelianization.lift (pQuotMap p G)

theorem abToPQuot_of (x : G) : abToPQuot p G (Abelianization.of x) = pQuotMap p G x := rfl

theorem abToPQuot_surjective : Function.Surjective (abToPQuot p G) := by
  intro y
  obtain ⟨x, rfl⟩ := pQuotMap_surjective p G y
  exact ⟨Abelianization.of x, abToPQuot_of p G x⟩

/-- The subgroup of `p`-th powers of the abelianization `Sᵃᵇ`. -/
def pthPowerSubgroup : Subgroup (Abelianization G) where
  carrier := {x | ∃ w, w ^ p = x}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, by rw [mul_pow]⟩
  inv_mem' := by rintro x ⟨a, rfl⟩; exact ⟨a⁻¹, by rw [inv_pow]⟩

/-- The kernel of `Sᵃᵇ → S/(S'Sᵖ)` consists of `p`-th powers. -/
theorem abToPQuot_ker_le_pthPower : (abToPQuot p G).ker ≤ pthPowerSubgroup p G := by
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator G) x
  have hg : g ∈ (pQuotMap p G).ker := by
    rw [MonoidHom.mem_ker]
    rw [← abToPQuot_of p G g]
    exact hx
  rw [pQuotMap_ker] at hg
  rw [show Work.Shrinking.pCentralSeries p G 1 =
      Work.Shrinking.powSubgroup p (⊤ : Subgroup G) ⊔ ⁅⊤, ⊤⁆ from rfl] at hg
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := Work.Shrinking.powSubgroup p (⊤ : Subgroup G))
      (t := ⁅⊤, ⊤⁆)).mp hg
  have hb1 : Abelianization.of b = 1 := by
    rw [← MonoidHom.mem_ker, Abelianization.ker_of G, commutator_def G]
    exact hb
  have hmem : Abelianization.of a ∈
      (Work.Shrinking.powSubgroup p (⊤ : Subgroup G)).map Abelianization.of :=
    Subgroup.mem_map_of_mem _ ha
  have hmap : (Work.Shrinking.powSubgroup p (⊤ : Subgroup G)).map Abelianization.of ≤
      pthPowerSubgroup p G := by
    rw [Work.Shrinking.powSubgroup, MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro z ⟨w, ⟨y, -, rfl⟩, rfl⟩
    exact ⟨Abelianization.of y, by rw [map_pow]⟩
  show Abelianization.of (a * b) ∈ pthPowerSubgroup p G
  rw [map_mul, hb1, mul_one]
  exact hmap hmem

/-- The canonical additive surjection `Sᵃᵇ → S/(S'Sᵖ)`, written in additive notation. -/
noncomputable def pQuotAddHom : Additive (Abelianization G) →+
    Additive (Work.Shrinking.pCentralQuotient p G 0) where
  toFun x := Additive.ofMul (abToPQuot p G (Additive.toMul x))
  map_zero' := by simp
  map_add' x y := by simp [map_mul]

theorem pQuotAddHom_surjective : Function.Surjective (pQuotAddHom p G) := by
  intro y
  obtain ⟨x, hx⟩ := abToPQuot_surjective p G (Additive.toMul y)
  refine ⟨Additive.ofMul x, ?_⟩
  show Additive.ofMul (abToPQuot p G (Additive.toMul (Additive.ofMul x))) = y
  rw [show Additive.toMul (Additive.ofMul x) = x from rfl, hx]
  exact Additive.ofMul.symm_apply_apply y

theorem pQuotAddHom_ker (m : Additive (Abelianization G)) (hm : pQuotAddHom p G m = 0) :
    ∃ z : Additive (Abelianization G), m = (p : ℤ) • z := by
  have h1 : abToPQuot p G (Additive.toMul m) = 1 := by
    have h := hm
    change Additive.ofMul (abToPQuot p G (Additive.toMul m)) = 0 at h
    rw [show (0 : Additive (Work.Shrinking.pCentralQuotient p G 0)) =
        Additive.ofMul 1 from rfl] at h
    exact Additive.ofMul.injective h
  obtain ⟨w, hw⟩ := abToPQuot_ker_le_pthPower p G h1
  refine ⟨Additive.ofMul w, ?_⟩
  rw [show m = Additive.ofMul (Additive.toMul m) from (Additive.ofMul.symm_apply_apply m).symm,
      ← hw, natCast_zsmul]
  simp

/-! ## The universal-coefficient isomorphism -/

/-- **The universal-coefficient identification** `H₁(S, A) ≅ A ⊗_{𝔽_p} S/(S'Sᵖ)` for a
representation `A` of `Γ` on which `S ≤ Γ` acts trivially. -/
theorem h1AddEquivPQuotientSub (p : ℕ) [Fact p.Prime] {Γ : Type} [Group Γ] (S : Subgroup Γ)
    (A : Rep.{0,0,0} (ZMod p) Γ) [Representation.IsTrivial (A.ρ.comp S.subtype)] :
    Nonempty (groupHomology.H1 (Rep.res S.subtype A) ≃+
      TensorProduct (ZMod p) (Additive (Work.Shrinking.pCentralQuotient p S 0)) A.V) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : (Rep.res S.subtype A).IsTrivial := inferInstance
  obtain ⟨e⟩ := tensorQuotSMulAddEquiv p (pQuotAddHom p S) (pQuotAddHom_surjective p S)
    (pQuotAddHom_ker p S) A.V
  exact ⟨(groupHomology.H1AddEquivOfIsTrivial (Rep.res S.subtype A)).trans e⟩

end Work.CohomologicalShrinking.universalCoefficient
