import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ArchDictionary.archCruxLinkedGen
import Submission.Work.SSGRoute.PT.decompK_linked
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Assembling `archimedeanDictNonsplit` from the comparison square

The four clauses of the target force `βc = Φ ∘ π` for a *group isomorphism*
`Φ : Ac ≅ L` (`Ac = Z¹(⟨c⟩,E)/B¹(⟨c⟩)`, `L = Ext¹_{D_w}(E'|,K_wˣ)`), and clause (4) says exactly
that `Φ` carries `ρ̄ b := [b|⟨c⟩]` to `γ̄ b := extLoc w (extToIdeles (globalDictionaryCanon … b))`.

The pieces (L1) (`Ac ≅ L`), (α) (`ker ρ̄ ⊆ ker γ̄`) and (β) (`ker γ̄ ⊆ ker ρ̄`) supply such a `Φ`:
for `p = 2` both `Ac` and `L` are elementary abelian `2`-groups, and an isomorphism of the images of
`ρ̄` and `γ̄` extends to an automorphism of `Ac`; for odd `p`, `Ac` is trivial
(`Ac_subsingleton_of_odd`) and any isomorphism will do.

This file contains the *assembly* only: it takes the square
`∃ Φ, ∀ b (global, locally constant), Φ (ρ̄ b) = γ̄ b` as an input and produces the target.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- **Assembly of the target from the comparison square.** -/
theorem archimedeanDictNonsplit_of_square (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (w : NK.GlobalCFT.Place ↥K) (φ : Ω →+* ℂ)
    (hwinf : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥)
    (hsq : ∃ Φ : (Ac (K := K) (E := E) c) ≃+ CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (Eprime p k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1,
      ∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        Φ (AcOfFun (K := K) (E := E) c b)
          = SSGRoute.PTExt.extLoc (k := k) w
              (SSGRoute.PTExt.extToIdeles (k := k)
                (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))) :
    ∃ βc : ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1,
      (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
        βc (b + b') = βc b + βc b') ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (βc b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)) ∧
      (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ βc b = y) ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        SSGRoute.PTExt.extLoc (k := k) w
          (SSGRoute.PTExt.extToIdeles (k := k)
            (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = βc b) := by
  classical
  obtain ⟨Φ, hΦ⟩ := hsq
  refine ⟨fun b => if h : b ∈ Zc K E c then Φ (Acπ (K := K) (E := E) c ⟨b, h⟩) else 0,
    ?_, ?_, ?_, ?_⟩
  · -- (1) additivity on the cocycles of `⟨c⟩`
    intro b b' hb hb'
    have hmb : b ∈ Zc K E c := hb
    have hmb' : b' ∈ Zc K E c := hb'
    have hmb'' : (b + b') ∈ Zc K E c := (Zc K E c).add_mem hmb hmb'
    dsimp only
    rw [dif_pos hmb'', dif_pos hmb, dif_pos hmb']
    rw [show (⟨b + b', hmb''⟩ : ↥(Zc K E c)) = ⟨b, hmb⟩ + ⟨b', hmb'⟩ from Subtype.ext rfl,
      map_add, map_add]
  · -- (2) the kernel is the coboundaries
    intro b hb
    have hmb : b ∈ Zc K E c := hb
    dsimp only
    rw [dif_pos hmb, AddEquiv.map_eq_zero_iff, Acπ_eq_zero_iff, mem_Bc]
  · -- (3) surjectivity
    intro y
    obtain ⟨z, hz⟩ := Acπ_surjective (K := K) (E := E) c (Φ.symm y)
    refine ⟨(z : (Ω ≃ₐ[k] Ω) → E), z.2, ?_⟩
    dsimp only
    rw [dif_pos z.2, hz, AddEquiv.apply_symm_apply]
  · -- (4) the comparison square
    intro b hb hl
    have hmb : b ∈ Zc K E c := mem_Zc_of_global (K := K) (E := E) hb
    dsimp only
    rw [dif_pos hmb, ← hΦ b hb hl]
    exact congrArg Φ (AcOfFun_eq (K := K) (E := E) c b hmb)

end

end Work.SSGRoute.ArchDictionary
