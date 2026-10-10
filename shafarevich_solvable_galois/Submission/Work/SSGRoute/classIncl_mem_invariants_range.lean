import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Submission.Work.SSGRoute.classIncl_isCanonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open NK.GlobalCFT

/-- **The `H⁰`-computation `C_k ≅ (C_K)^{Gal(K/k)}` in the `Ext`-core vocabulary.**  A class of
the idèle class group `C_K` fixed by all of `Gal(K/k)` lies in the image of the canonical
inclusion `C_k → C_K` induced by the local embeddings `k_vˣ → K_wˣ`.

This is the surjectivity half of
`NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup` (the class field theory statement
that `(C_K)^{Gal(K/k)} = image(C_k)`, whose hard direction is Hilbert 90 for `Kˣ`), transported
to the representation-theoretic `classIncl` used by the Poitou–Tate core: by
`classIncl_isCanonical` the morphism `classIncl k k K` is the canonical inclusion of idèle class
groups, so the `H⁰`-statement applies verbatim. -/
theorem classIncl_mem_invariants_range (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (a : SSGRoute.PTExt.classesK k K)
    (ha : ∀ σ : K ≃ₐ[k] K, (SSGRoute.PTExt.classesK k K).ρ σ a = a) :
    ∃ a₀ : SSGRoute.PTExt.classesK k k, (SSGRoute.PTExt.classIncl k k K).hom a₀ = a := by
  classical
  -- The canonical inclusion `C_k → C_K` is induced by a local embedding `φ` of idèle groups.
  obtain ⟨u, hu, φ, hφ, hι⟩ := classIncl_isCanonical k k K
  obtain ⟨ψ, hψ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists u hu φ hφ
  -- `ψ` computes `classIncl` on the classes of idèles.
  have hψ_eq : ∀ y : IdeleClassGroup k,
      ψ y = Additive.toMul ((classIncl k k K).hom (Additive.ofMul y)) := by
    intro y
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective k y
    rw [hψ x]
    exact (congrArg Additive.toMul (hι x)).symm
  -- `a`, read as an element of `C_K`.
  let q : IdeleClassGroup K := Additive.toMul a
  -- The hypothesis `ha` says exactly that `q` is fixed by `Gal(K/k)`.
  have hfix : ∀ σ : K ≃ₐ[k] K, σ • q = q := fun σ => by
    have h := ha σ
    have h' : Additive.ofMul (σ • q) = Additive.ofMul q := h
    exact Additive.ofMul.injective h'
  -- The `H⁰`-computation of class field theory: a fixed class is in the image of `ψ`.
  obtain ⟨y, hy⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_invariants_le_range u hu φ hφ ψ hψ q hfix
  refine ⟨Additive.ofMul y, ?_⟩
  show (classIncl k k K).hom (Additive.ofMul y) = Additive.ofMul q
  have h2 : Additive.toMul ((classIncl k k K).hom (Additive.ofMul y)) = q := by
    rw [← hψ_eq y]
    exact hy
  exact congrArg Additive.ofMul h2

end Work.SSGRoute
