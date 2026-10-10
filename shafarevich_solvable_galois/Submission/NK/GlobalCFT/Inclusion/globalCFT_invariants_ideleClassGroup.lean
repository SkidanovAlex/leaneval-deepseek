import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.GaloisClassGroup
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_idele_smul_eq_self_iff
import Submission.NK.GlobalCFT.Inclusion.hilbert90_cocycle
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Inclusion

open NK.GlobalCFT

/-- The diagonal embedding `Kˣ →* 𝕀[K]` is injective: an element of `Kˣ` is determined by its
image in any single local field `K_vˣ`, and the canonical map `K → K_v` is injective because both
are fields. -/
theorem globalCFT_principalIdele_injective (K : Type*) [Field K] [NumberField K] :
    Function.Injective (Idele.principalIdele K) := by
  intro y z h
  let v : Place K := Classical.choice (inferInstance : Nonempty (Place K))
  have h' : (Idele.principalIdele K y) v = (Idele.principalIdele K z) v :=
    congrFun (congrArg Subtype.val h) v
  exact Units.map_injective
    (f := (algebraMap K (Place.localField K v)).toMonoidHom) (RingHom.injective _)
    (by simpa using h')

/-- The easy half of the invariance statement: a class in the image of the inclusion of idèle class
groups is fixed by `Gal(L/K)`, because it is the class of `φ x` and `φ x` is a fixed idèle
(`NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_smul`). -/
theorem globalCFT_invariants_ge_range {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (ψ : C[K] →* C[L])
    (hψ : ∀ x : 𝕀[K], ψ (IdeleClassGroup.mk K x) = IdeleClassGroup.mk L (φ x)) :
    ∀ q : C[L], q ∈ ψ.range → ∀ σ : L ≃ₐ[K] L, σ • q = q := by
  rintro q ⟨r, rfl⟩ σ
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K r
  rw [hψ x, IdeleClassGroup.smul_mk, globalCFT_ideleInclusion_smul u hu φ hφ σ x]

/-- **The hard half of the invariance statement.**  A class `q ∈ C_L` fixed by `Gal(L/K)` lies in
the image of `C_K → C_L`.

Let `x` be an idèle representing `q`.  Since `q` is fixed, `x⁻¹ · (σ · x)` is a principal idèle
for every `σ`; write it as `(c σ)` with `c σ ∈ Lˣ`.  The elements `c σ` form a `1`-cocycle
(`c (σ * τ) = c σ · σ (c τ)`), so by Hilbert 90
(`NK.GlobalCFT.Inclusion.hilbert90_cocycle`) there is `β ∈ Lˣ` with `c σ = σ β / β`.  Then
`y := x · (β)⁻¹` is a *fixed* idèle with the same class as `x`, so by the idèle-level statement
of the Galois invariants (`NK.GlobalCFT.Inclusion.globalCFT_idele_smul_eq_self_iff`) it is the
image of an idèle `z` of `K`; hence `q = ψ (mk K z)`. -/
theorem globalCFT_invariants_le_range {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (ψ : C[K] →* C[L])
    (hψ : ∀ x : 𝕀[K], ψ (IdeleClassGroup.mk K x) = IdeleClassGroup.mk L (φ x))
    (q : C[L]) (hq : ∀ σ : L ≃ₐ[K] L, σ • q = q) : q ∈ ψ.range := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L q
  -- `x⁻¹ * (σ • x)` is a principal idèle: the defect of the representative `x`
  have hmem : ∀ σ : L ≃ₐ[K] L, x⁻¹ * (σ • x) ∈ Idele.principalSubgroup L := by
    intro σ
    have h1 : (σ • x)⁻¹ * x ∈ Idele.principalSubgroup L := by
      rw [← IdeleClassGroup.mk_eq_mk_iff, ← IdeleClassGroup.smul_mk]
      exact hq σ
    simpa only [mul_inv_rev, inv_inv] using Subgroup.inv_mem _ h1
  choose c hc using fun σ => Idele.mem_principalSubgroup.mp (hmem σ)
  -- `hc σ : principalIdele L (c σ) = x⁻¹ * (σ • x)`
  have hc' : ∀ σ : L ≃ₐ[K] L, σ • x = x * Idele.principalIdele L (c σ) := by
    intro σ
    rw [hc σ]
    group
  -- the defect is a cocycle
  have hcocycle : ∀ σ τ : L ≃ₐ[K] L,
      c (σ * τ) = c σ * Units.map σ.toMonoidHom (c τ) := by
    intro σ τ
    apply globalCFT_principalIdele_injective L
    apply mul_left_cancel (a := x)
    calc x * Idele.principalIdele L (c (σ * τ))
        = (σ * τ) • x := (hc' (σ * τ)).symm
      _ = σ • (τ • x) := by rw [mul_smul]
      _ = σ • (x * Idele.principalIdele L (c τ)) := by rw [hc' τ]
      _ = (σ • x) * Idele.principalIdele L (Units.map σ.toMonoidHom (c τ)) := by
            rw [MulDistribMulAction.smul_mul, Galois.globalCFT_smul_principalIdele]
      _ = x * (Idele.principalIdele L (c σ) *
            Idele.principalIdele L (Units.map σ.toMonoidHom (c τ))) := by
            rw [hc' σ, mul_assoc]
      _ = x * Idele.principalIdele L (c σ * Units.map σ.toMonoidHom (c τ)) := by rw [map_mul]
  -- Hilbert 90 computes the defect as a coboundary
  obtain ⟨β, hβ⟩ := hilbert90_cocycle c hcocycle
  -- the corrected idèle `y := x * (β)⁻¹` is fixed
  set y : 𝕀[L] := x * (Idele.principalIdele L β)⁻¹ with hydef
  have hsmul_inv : ∀ (σ : L ≃ₐ[K] L),
      σ • (Idele.principalIdele L β)⁻¹ =
        (Idele.principalIdele L (Units.map σ.toMonoidHom β))⁻¹ := by
    intro σ
    rw [smul_inv', Galois.globalCFT_smul_principalIdele]
  have hyfix : ∀ σ : L ≃ₐ[K] L, σ • y = y := by
    intro σ
    rw [hydef, MulDistribMulAction.smul_mul, hc' σ, hsmul_inv, hβ σ, map_mul, map_inv]
    simp [mul_comm, mul_assoc, mul_left_comm]
  -- a fixed idèle is the image of an idèle of `K`
  obtain ⟨z, hz⟩ := (globalCFT_idele_smul_eq_self_iff u hu φ hφ y).mp hyfix
  refine ⟨IdeleClassGroup.mk K z, ?_⟩
  rw [hψ z, hz]
  -- `y` and `x` differ by the principal idèle `(β)`
  rw [IdeleClassGroup.mk_eq_mk_iff, Idele.mem_principalSubgroup]
  refine ⟨β, ?_⟩
  rw [hydef]
  group

/-- **The Galois invariants of the idèle class group are the image of the idèle class group of
the base field.**  For `L / K` a finite Galois extension of number fields and a monoid
homomorphism `φ : 𝕀[K] →* 𝕀[L]` whose `w`-component is the canonical local embedding
`K_{u w}ˣ → L_wˣ`, the induced homomorphism `ψ : C_K →* C_L` on idèle class groups has as its
range exactly the subgroup of classes fixed by `Gal(L/K)`.

This is the `H⁰`-computation `C_K ≅ (C_L)^{Gal(L/K)}` of class field theory: the inclusion
`C_K → C_L^{Gal(L/K)}` is surjective because `H¹(Gal(L/K), Lˣ) = 0` (Hilbert 90) combined with
the local fixed-field theorem for decomposition groups. -/
theorem globalCFT_invariants_ideleClassGroup {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (ψ : C[K] →* C[L])
    (hψ : ∀ x : 𝕀[K], ψ (IdeleClassGroup.mk K x) = IdeleClassGroup.mk L (φ x))
    (q : C[L]) :
    (∀ σ : L ≃ₐ[K] L, σ • q = q) ↔ q ∈ ψ.range :=
  ⟨globalCFT_invariants_le_range u hu φ hφ ψ hψ q,
    globalCFT_invariants_ge_range u hu φ hφ ψ hψ q⟩

end NK.GlobalCFT.Inclusion
