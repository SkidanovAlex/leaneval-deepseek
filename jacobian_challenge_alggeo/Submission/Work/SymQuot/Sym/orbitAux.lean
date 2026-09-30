/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `A`-algebra homomorphisms out of an invariant ring extension form a single `G`-orbit

Let `A` be a commutative ring, `B` a commutative `A`-algebra, `G` a finite group acting on `B` by
`A`-algebra automorphisms, and assume that `A` is exactly the fixed subring of the action
(`Algebra.IsInvariant A B G`).  Then for any field `F` with `A → F`, any two `A`-algebra
homomorphisms `B →ₐ[A] F` lie in the same `G`-orbit:

`orbitAux : ∃ g : G, ∀ b : B, ψ b = φ (g • b)`.

The proof has two ingredients.

* `orbitAux_exists_algEquiv_of_normal`: if `M/k` is a normal algebraic field extension and `F` is
  any field, then two `k`-algebra homomorphisms `M →ₐ[k] F` differ by a `k`-automorphism of `M`.
  (Every root of `minpoly k x` in `F` is a conjugate of `x`, hence lies in the image of the other
  embedding.)

* `orbitAux_same_ker`: in the case where `φ` and `ψ` have equal kernels, `G` acts transitively on
  the *prime ideals* of `B` lying over a fixed prime of `A`
  (`Algebra.IsInvariant.exists_smul_of_under_eq`), and the residue extension
  `Frac (B ⧸ Q) / Frac (A ⧸ q)` is normal (`Ideal.IsFractionRing.normal`), with
  `MulAction.stabilizer G Q` surjecting onto its automorphism group
  (`IsFractionRing.stabilizerHom_surjective`).

Both statements are special instances of the fact that `Spec B → Spec A` has the `G`-orbits as
its fibres, on geometric points.
-/
import Mathlib
import Submission.Work.SymQuot.Sym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.



open Polynomial
open scoped Pointwise

namespace Work.SymQuot.Sym

/-- Two `k`-algebra homomorphisms out of a normal algebraic extension `M/k` into any field `F`
differ by a `k`-automorphism of `M`. -/
theorem orbitAux_exists_algEquiv_of_normal {k M F : Type*} [Field k] [Field M] [Field F]
    [Algebra k M] [Algebra k F] [Normal k M] (φ ψ : M →ₐ[k] F) :
    ∃ σ : M ≃ₐ[k] M, ∀ x, ψ x = φ (σ x) := by
  have hrange : ∀ x : M, ψ x ∈ φ.range := by
    intro x
    have hsplitsM : ((minpoly k x).map (algebraMap k M)).Splits :=
      (inferInstance : Normal k M).splits x
    have hmonic : (minpoly k x).Monic :=
      minpoly.monic ((inferInstance : Normal k M).isIntegral x)
    have hsplitsF : ((minpoly k x).map (algebraMap k F)).Splits := by
      have h := hsplitsM.map (φ : M →+* F)
      rwa [map_map, AlgHom.comp_algebraMap] at h
    have hroots : ((minpoly k x).map (algebraMap k F)).roots
        = ((minpoly k x).map (algebraMap k M)).roots.map (φ : M → F) := by
      have h := hsplitsM.roots_map_of_injective (i := (φ : M →+* F))
        (fun a b hab => φ.injective hab)
      rwa [map_map, AlgHom.comp_algebraMap] at h
    have hmonicF : ((minpoly k x).map (algebraMap k F)).Monic := hmonic.map (algebraMap k F)
    have hzero : ((minpoly k x).map (algebraMap k F)).eval (ψ x) = 0 := by
      rw [eval_map, ← aeval_def, Polynomial.aeval_algHom_apply ψ x (minpoly k x),
        minpoly.aeval, map_zero]
    have hprod : (Multiset.map (fun r => ψ x - r)
        ((minpoly k x).map (algebraMap k F)).roots).prod = 0 := by
      rw [← Splits.eval_eq_prod_roots_of_monic hsplitsF hmonicF (ψ x)]
      exact hzero
    rw [hroots, Multiset.map_map] at hprod
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod)
    exact (AlgHom.mem_range φ).mpr ⟨r, (sub_eq_zero.mp hr).symm⟩
  let ψ' : M →ₐ[k] ↥φ.range := ψ.codRestrict φ.range hrange
  let e : M ≃ₐ[k] ↥φ.range := AlgEquiv.ofInjective φ φ.injective
  have he : ∀ x : M, (e x : F) = φ x := fun x => AlgEquiv.ofInjective_apply φ φ.injective x
  let σ : M →ₐ[k] M := e.symm.toAlgHom.comp ψ'
  have hbij : Function.Bijective σ := AlgHom.normal_bijective k M M σ
  refine ⟨AlgEquiv.ofBijective σ hbij, fun x => ?_⟩
  have h1 : φ (σ x) = ψ x := by
    have h2 := he (e.symm (ψ' x))
    rw [AlgEquiv.apply_symm_apply] at h2
    have h3 : (ψ' x : F) = ψ x := rfl
    rw [h3] at h2
    exact h2.symm
  change ψ x = φ (σ x)
  exact h1.symm

/-- The equal-kernel case: two `A`-algebra homomorphisms `B →ₐ[A] F` with the same kernel are
related by an element of `G`. -/
theorem orbitAux_same_ker {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] {F : Type*} [Field F] [Algebra A F]
    (φ ψ : B →ₐ[A] F) (hker : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom) :
    ∃ g : G, ∀ b : B, ψ b = φ (g • b) := by
  classical
  let Q : Ideal B := RingHom.ker φ.toRingHom
  have hQprime : Q.IsPrime := RingHom.ker_isPrime _
  have hQψ : Q = RingHom.ker ψ.toRingHom := hker
  let q : Ideal A := Q.under A
  have hqprime : q.IsPrime := Ideal.IsPrime.under A Q
  haveI : Q.IsPrime := hQprime
  haveI : q.IsPrime := hqprime
  haveI hLies : Q.LiesOver q := Ideal.over_under Q
  have hφ0 : ∀ a : B, a ∈ Q → φ a = 0 := fun a ha => RingHom.mem_ker.mp ha
  have hψ0 : ∀ a : B, a ∈ Q → ψ a = 0 := fun a ha => RingHom.mem_ker.mp (hQψ ▸ ha)
  let φbar : B ⧸ Q →ₐ[A] F := Ideal.Quotient.liftₐ Q φ hφ0
  let ψbar : B ⧸ Q →ₐ[A] F := Ideal.Quotient.liftₐ Q ψ hψ0
  have hφbarmk : ∀ b : B, φbar (Ideal.Quotient.mk Q b) = φ b := fun b =>
    show (Ideal.Quotient.liftₐ Q φ hφ0) (Ideal.Quotient.mk Q b) = φ b from by
      rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
      rfl
  have hψbarmk : ∀ b : B, ψbar (Ideal.Quotient.mk Q b) = ψ b := fun b =>
    show (Ideal.Quotient.liftₐ Q ψ hψ0) (Ideal.Quotient.mk Q b) = ψ b from by
      rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
      rfl
  have hφbarinj : Function.Injective φbar := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hφbarmk, hφbarmk] at hxy
    rw [Ideal.Quotient.eq]
    exact RingHom.mem_ker.mpr (by rw [map_sub]; exact sub_eq_zero.mpr hxy)
  have hψbarinj : Function.Injective ψbar := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hψbarmk, hψbarmk] at hxy
    rw [Ideal.Quotient.eq, hQψ]
    exact RingHom.mem_ker.mpr (by rw [map_sub]; exact sub_eq_zero.mpr hxy)
  let k := FractionRing (A ⧸ q)
  let M := FractionRing (B ⧸ Q)
  haveI : IsFractionRing (A ⧸ q) k := inferInstance
  haveI : IsFractionRing (B ⧸ Q) M := inferInstance
  haveI : IsScalarTower (A ⧸ q) (B ⧸ Q) M := inferInstance
  haveI : FaithfulSMul (A ⧸ q) M := by
    rw [faithfulSMul_iff_algebraMap_injective,
        IsScalarTower.algebraMap_eq (A ⧸ q) (B ⧸ Q) M]
    exact (IsFractionRing.injective (B ⧸ Q) M).comp Ideal.algebraMap_quotient_injective
  letI : Algebra k M := FractionRing.liftAlgebra (A ⧸ q) M
  haveI : IsScalarTower (A ⧸ q) k M := FractionRing.isScalarTower_liftAlgebra (A ⧸ q) M
  haveI hnorm : Normal k M := Ideal.IsFractionRing.normal G q Q k M
  let φhat : M →ₐ[A] F :=
    IsFractionRing.liftAlgHom (R := A) (A := B ⧸ Q) (K := M) (L := F) (g := φbar) hφbarinj
  let ψhat : M →ₐ[A] F :=
    IsFractionRing.liftAlgHom (R := A) (A := B ⧸ Q) (K := M) (L := F) (g := ψbar) hψbarinj
  have hφhat_alg : ∀ x : B ⧸ Q, φhat (algebraMap (B ⧸ Q) M x) = φbar x := fun x => by
    change IsFractionRing.liftAlgHom (R := A) (A := B ⧸ Q) (K := M) (L := F)
      (g := φbar) hφbarinj (algebraMap (B ⧸ Q) M x) = φbar x
    rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    rfl
  have hψhat_alg : ∀ x : B ⧸ Q, ψhat (algebraMap (B ⧸ Q) M x) = ψbar x := fun x => by
    change IsFractionRing.liftAlgHom (R := A) (A := B ⧸ Q) (K := M) (L := F)
      (g := ψbar) hψbarinj (algebraMap (B ⧸ Q) M x) = ψbar x
    rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    rfl
  have hbar_eq_pt : ∀ x : A ⧸ q,
      φbar (algebraMap (A ⧸ q) (B ⧸ Q) x) = ψbar (algebraMap (A ⧸ q) (B ⧸ Q) x) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : algebraMap (A ⧸ q) (B ⧸ Q) (Ideal.Quotient.mk q a)
        = Ideal.Quotient.mk Q (algebraMap A B a) := by simp
    rw [h1, hφbarmk, hψbarmk, φ.commutes, ψ.commutes]
  have hagree : (φhat : M →+* F).comp (algebraMap k M)
      = (ψhat : M →+* F).comp (algebraMap k M) := by
    apply IsFractionRing.ringHom_ext (A := A ⧸ q) (K := k) (L := F)
    intro x
    show φhat (algebraMap k M (algebraMap (A ⧸ q) k x))
      = ψhat (algebraMap k M (algebraMap (A ⧸ q) k x))
    rw [← IsScalarTower.algebraMap_apply (A ⧸ q) k M x,
      IsScalarTower.algebraMap_apply (A ⧸ q) (B ⧸ Q) M x,
      hφhat_alg, hψhat_alg]
    exact hbar_eq_pt x
  letI : Algebra k F := ((φhat : M →+* F).comp (algebraMap k M)).toAlgebra
  have hφhat_k : ∀ c : k, φhat (algebraMap k M c) = algebraMap k F c := fun c => rfl
  have hψhat_k : ∀ c : k, ψhat (algebraMap k M c) = algebraMap k F c := fun c => by
    rw [RingHom.algebraMap_toAlgebra]
    show ψhat (algebraMap k M c) = φhat (algebraMap k M c)
    exact (RingHom.congr_fun hagree c).symm
  let φhatk : M →ₐ[k] F := { toRingHom := φhat.toRingHom, commutes' := hφhat_k }
  let ψhatk : M →ₐ[k] F := { toRingHom := ψhat.toRingHom, commutes' := hψhat_k }
  obtain ⟨σ, hσ⟩ := orbitAux_exists_algEquiv_of_normal φhatk ψhatk
  obtain ⟨τ, hτ⟩ := IsFractionRing.stabilizerHom_surjective G q Q k M σ
  refine ⟨τ.1, fun b => ?_⟩
  calc ψ b = ψbar (Ideal.Quotient.mk Q b) := (hψbarmk b).symm
    _ = ψhat (algebraMap (B ⧸ Q) M (Ideal.Quotient.mk Q b)) := (hψhat_alg _).symm
    _ = ψhatk (algebraMap (B ⧸ Q) M (Ideal.Quotient.mk Q b)) := rfl
    _ = φhatk (σ (algebraMap (B ⧸ Q) M (Ideal.Quotient.mk Q b))) := hσ _
    _ = φhat (σ (algebraMap (B ⧸ Q) M (Ideal.Quotient.mk Q b))) := rfl
    _ = φhat ((IsFractionRing.stabilizerHom G q Q k M τ)
          (algebraMap (B ⧸ Q) M (Ideal.Quotient.mk Q b))) := by rw [hτ]
    _ = φhat (algebraMap (B ⧸ Q) M (Ideal.Quotient.mk Q (τ.1 • b))) := by
          rw [IsFractionRing.stabilizerHom_apply_apply_mk]
    _ = φbar (Ideal.Quotient.mk Q (τ.1 • b)) := hφhat_alg _
    _ = φ (τ.1 • b) := hφbarmk _

/-- Any two `A`-algebra homomorphisms `B →ₐ[A] F` from an `A`-algebra whose `A` is the fixed
subring of a finite group `G` into a field `F` lie in the same `G`-orbit. -/
theorem orbitAux {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] {F : Type*} [Field F] [Algebra A F]
    (φ ψ : B →ₐ[A] F) : ∃ g : G, ∀ b : B, ψ b = φ (g • b) := by
  let P : Ideal B := RingHom.ker φ.toRingHom
  let Q : Ideal B := RingHom.ker ψ.toRingHom
  have hPprime : P.IsPrime := RingHom.ker_isPrime _
  have hQprime : Q.IsPrime := RingHom.ker_isPrime _
  haveI : P.IsPrime := hPprime
  haveI : Q.IsPrime := hQprime
  have hunder : P.under A = Q.under A := by
    ext a
    simp only [Ideal.mem_under, P, Q, RingHom.mem_ker]
    rw [show φ.toRingHom (algebraMap A B a) = algebraMap A F a from φ.commutes a,
        show ψ.toRingHom (algebraMap A B a) = algebraMap A F a from ψ.commutes a]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G P Q hunder
  let φ' : B →ₐ[A] F := φ.comp ((MulSemiringAction.toAlgEquiv A B (G := G) g⁻¹).toAlgHom)
  have hφ'b : ∀ b : B, φ' b = φ (g⁻¹ • b) := fun b => by
    simp [φ']
  have key : ∀ b : B, b ∈ (g • P : Ideal B) ↔ φ (g⁻¹ • b) = 0 := fun b => by
    rw [show b ∈ (g • P : Ideal B) ↔ g⁻¹ • b ∈ P from Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact RingHom.mem_ker
  have hker' : RingHom.ker φ'.toRingHom = RingHom.ker ψ.toRingHom := by
    have hgoal : (RingHom.ker ψ.toRingHom : Ideal B) = (g • P : Ideal B) := hg
    rw [hgoal]
    ext b
    show φ' b = 0 ↔ b ∈ (g • P : Ideal B)
    rw [hφ'b b, key b]
  obtain ⟨τ, hτ⟩ := orbitAux_same_ker G φ' ψ hker'
  exact ⟨g⁻¹ * τ, fun b => by rw [hτ b, hφ'b (τ • b), mul_smul]⟩

end Work.SymQuot.Sym
