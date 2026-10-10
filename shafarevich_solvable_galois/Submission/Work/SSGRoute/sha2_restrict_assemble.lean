import Mathlib.FieldTheory.KrullTopology
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.sha2_restrict_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ш²(k,E)` dies on `G_K`: the base-change assembly

Given the *base case* at the base field `↥K` with the bottom intermediate field
(`∀ c ∈ З2loc p ↥K Ω ⊥ E, IsCoboundary2On (res ↥K ⊥) ⊤ c` — i.e. the vanishing of `Ш²(↥K,E)` for
a trivially acted finite `𝔽_p`-module `E`, the classical Hasse principle), every locally trivial
continuous `2`-cocycle of `G_k` with values in a finite `Gal(K/k)`-module `E` is a continuous
coboundary on `G_K`.

The transport is `Work.SSGRoute.toGkHom`: for `g : Ω ≃ₐ[K] Ω` the element `toGkHom K g ∈ G_k` has
`res k K (toGkHom K g) = 1`, so on `G_K` the coefficient action of `G_k` becomes the trivial one;
decomposition groups, involutions and local constancy transport along `toGkHom`, and the primitive
of the base case (a cochain on `Gal(Ω/↥K)`) is transported back to `G_k` by `isLocConstOn_extract`.
-/

set_option linter.ambiguousOpen false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise Classical

section Assemble

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **Reduction of `sha2_restrict_vanish` to the base case at `K`.** -/
theorem sha2_restrict_vanish_of_base (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [DistribMulAction ((⊥ : IntermediateField K Ω) ≃ₐ[K] (⊥ : IntermediateField K Ω)) E]
    [SMulCommClass ((⊥ : IntermediateField K Ω) ≃ₐ[K] (⊥ : IntermediateField K Ω)) (ZMod p) E]
    (htriv : ∀ (g : (⊥ : IntermediateField K Ω) ≃ₐ[K] (⊥ : IntermediateField K Ω)) (m : E),
      g • m = m)
    (hbase : ∀ c : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → E,
      c ∈ Z2loc p (↥K) Ω (⊥ : IntermediateField K Ω) E →
        SSGRoute.IsCoboundary2On (SSGRoute.res (↥K) (⊥ : IntermediateField K Ω)) ⊤ c)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E) (hc : c ∈ Z2loc p k Ω K E) :
    SSGRoute.IsCoboundary2On (SSGRoute.res k K) K.fixingSubgroup c := by
  classical
  -- the transported cocycle
  set cK : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → E := fun g h => c (toGkHom K g) (toGkHom K h) with hcKdef
  have hcK : cK ∈ Z2loc p (↥K) Ω (⊥ : IntermediateField K Ω) E := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact isCocycle2_toGk p K E htriv c hc.1
    · exact isLocConst2_toGk (K := K) hc.2.1
    · intro A hA
      exact isCoboundary2On_toGk_place K E htriv c A
        (hc.2.2.1 A (isFinPlace_of_isFinPlace K A hA))
    · intro σ hσ
      refine isCoboundary2On_toGk_involution K E htriv c σ hσ ?_
      have : (toGkHom K σ) ^ 2 = 1 := by rw [pow_two, ← map_mul, ← pow_two, hσ, map_one]
      exact hc.2.2.2 (toGkHom K σ) this
  -- the primitive supplied by the base case
  obtain ⟨b, hb, hbc⟩ := hbase cK hcK
  refine ⟨fun σ => if h : σ ∈ K.fixingSubgroup then
      b ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, h⟩) else 0, ?_, ?_⟩
  · exact isLocConstOn_extract (K := K) hb
  · intro g hg h hh
    have hgker : SSGRoute.res k K g = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker K]
      exact hg
    have hgu : g * h ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hg hh
    show c g h = SSGRoute.res k K g • (if h' : h ∈ K.fixingSubgroup then
          b ((IntermediateField.fixingSubgroupEquiv K) ⟨h, h'⟩) else 0)
        - (if h' : g * h ∈ K.fixingSubgroup then
          b ((IntermediateField.fixingSubgroupEquiv K) ⟨g * h, h'⟩) else 0)
        + (if h' : g ∈ K.fixingSubgroup then
          b ((IntermediateField.fixingSubgroupEquiv K) ⟨g, h'⟩) else 0)
    rw [dif_pos hh, dif_pos hgu, dif_pos hg, hgker, one_smul]
    have hkey : ((IntermediateField.fixingSubgroupEquiv K) ⟨g * h, hgu⟩ : Ω ≃ₐ[K] Ω) =
        ((IntermediateField.fixingSubgroupEquiv K) ⟨g, hg⟩) *
          ((IntermediateField.fixingSubgroupEquiv K) ⟨h, hh⟩) := by
      have h1 : (⟨g * h, hgu⟩ : ↥(K.fixingSubgroup)) = ⟨g, hg⟩ * ⟨h, hh⟩ := Subtype.ext rfl
      rw [h1, map_mul]
    have hch : cK ((IntermediateField.fixingSubgroupEquiv K) ⟨g, hg⟩)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨h, hh⟩) = c g h := by
      simp only [hcKdef]
      rw [toGkHom_fixingSubgroupEquiv, toGkHom_fixingSubgroupEquiv]
    rw [← hch, hbc _ trivial _ trivial, htriv, hkey]

end Assemble

end Work.SSGRoute
