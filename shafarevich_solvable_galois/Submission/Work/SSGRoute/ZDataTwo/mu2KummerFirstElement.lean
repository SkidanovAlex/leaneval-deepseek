import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK
import Submission.Work.SSGRoute.grunwald_over_K_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Grünwald + Kummer "first element" at every prime `p`, including `p = 2`

`Work.SSGRoute.GrunwaldEscapeCore.grunwald_kummer_first_element` is the first half of the
Grünwald-with-escape core: given a continuous additive datum `g` on `G_K = K.fixingSubgroup` and a
continuous additive correction `h A` on each local group `decomp k A ⊓ G_K` (`A ∈ T`), there is
`a ∈ Kˣ` whose Kummer character restricts to `g + h A` on every one of those local groups.

Its statement carries the hypothesis `hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1`,
which the odd-`p` escape lane uses (and which its own proof does not in fact invoke; the docstring of
that file records this).  For `p = 2` with involutions present that hypothesis is *false*, so the
lemma cannot be applied, even though the argument does not need it.  This module proves the
hypothesis-free version:

`Work.SSGRoute.GrunwaldEscapeCore.kummerFirstElement_noImag`

— for **every** prime `p` (`Fact p.Prime`), with no condition on the involutions of `G_K`.  The
proof is the one of `grunwald_kummer_first_element` with the unused hypothesis deleted:

* the local datum `f A := g + h A` on `decomp k A ⊓ K.fixingSubgroup` is additive (`hg`, `hh`) and
  continuous (`hgc`, `hhc`, using `g 1 = 0`), which is the only bookkeeping;
* Grünwald's theorem over the base field `K` (`Work.SSGRoute.grunwald_over_K_general`, which has no
  hypothesis on `p` or on `ζ`) realises `f` by a continuous additive cochain `z` on `G_K`;
* Kummer theory over `K` (`Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK`)
  realises `z` by the Kummer character of some `a ∈ Kˣ`.

This is the `p = 2` input of the escape realisation `mu2EscapeRealisation`; it is a genuine step at
`p = 2` because the odd-`p` statement is not applicable there.
-/

namespace Work.SSGRoute.GrunwaldEscapeCore

open _root_.SSGRoute

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem kummerFirstElement_noImag (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0) :
    ∃ a : (↥K)ˣ, ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ) := by
  classical
  -- ## the local datum `f A := g + h A` on the local group `decomp k A ⊓ G_K`
  let f : ∀ A : {A // A ∈ T},
      ↥(SSGRoute.decomp k (A : ValuationSubring Ω) ⊓ K.fixingSubgroup) → ZMod p :=
    fun A δ => g ((δ : Ω ≃ₐ[k] Ω)) + h (A : ValuationSubring Ω) ((δ : Ω ≃ₐ[k] Ω))
  have hg_one : g 1 = 0 := by
    have h1 := hg 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [one_mul] at h1
    exact add_left_cancel (by rw [add_zero]; exact h1.symm)
  have hf : ∀ A : {A // A ∈ T},
      ∀ a b : ↥(SSGRoute.decomp k (A : ValuationSubring Ω) ⊓ K.fixingSubgroup),
      f A (a * b) = f A a + f A b := by
    intro A a b
    have haK : (a : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp a.2).2
    have hbK : (b : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp b.2).2
    dsimp only [f]
    rw [Subgroup.coe_mul, hg _ haK _ hbK,
      hh (A : ValuationSubring Ω) A.2 a a.2 b b.2]
    abel
  have hfc : ∀ A : {A // A ∈ T},
      ∃ U : Subgroup ↥(SSGRoute.decomp k (A : ValuationSubring Ω) ⊓ K.fixingSubgroup),
        IsOpen (U : Set ↥(SSGRoute.decomp k (A : ValuationSubring Ω) ⊓ K.fixingSubgroup)) ∧
        ∀ x ∈ U, f A x = 0 := by
    intro A
    obtain ⟨Vg, hVgopen, hVg⟩ := hgc
    obtain ⟨Vh, hVhopen, hVh⟩ := hhc (A : ValuationSubring Ω) A.2
    refine ⟨Subgroup.comap (Subgroup.subtype
      (SSGRoute.decomp k (A : ValuationSubring Ω) ⊓ K.fixingSubgroup)) (Vg ⊓ Vh), ?_, ?_⟩
    · rw [Subgroup.coe_comap, Subgroup.coe_inf]
      exact (hVgopen.inter hVhopen).preimage continuous_subtype_val
    · intro x hx
      have hxV : (x : Ω ≃ₐ[k] Ω) ∈ Vg ⊓ Vh := hx
      have hxK : (x : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp x.2).2
      have hgx : g (x : Ω ≃ₐ[k] Ω) = 0 := by
        have h1 := hVg 1 (Subgroup.one_mem _) (x : Ω ≃ₐ[k] Ω)
          (Subgroup.mem_inf.mp hxV).1 hxK
        simpa [hg_one] using h1
      have hhx : h (A : ValuationSubring Ω) (x : Ω ≃ₐ[k] Ω) = 0 :=
        hVh (x : Ω ≃ₐ[k] Ω) (Subgroup.mem_inf.mp hxV).2 x.2
      dsimp only [f]
      rw [hgx, hhx, add_zero]
  -- ## Grünwald's theorem over `K` realises the local datum on `G_K`
  have hζΩ : IsPrimitiveRoot (((ζ : ↥K)) : Ω) p :=
    hζ.map_of_injective (algebraMap ↥K Ω).injective
  obtain ⟨z, hzadd, hzloc, hzagree⟩ :=
    Work.SSGRoute.grunwald_over_K_general (p := p) (k := k) (Ω := Ω) K (((ζ : ↥K)) : Ω)
      hζΩ ζ.2 T hTfin hTdisj f hf hfc
  -- ## Kummer theory over `K` turns `z` into the Kummer character of an element of `Kˣ`
  obtain ⟨a, ha⟩ :=
    Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK
      (p := p) (k := k) (Ω := Ω) K ζ hζ z hzadd hzloc
  refine ⟨a, ?_⟩
  intro A hA σ
  have hσK : (σ : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp σ.2).2
  have hz1 : z (σ : Ω ≃ₐ[k] Ω) = f ⟨A, hA⟩ σ := hzagree ⟨A, hA⟩ σ
  have hz2 : z (σ : Ω ≃ₐ[k] Ω) =
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
        ((IntermediateField.fixingSubgroupEquiv K) ⟨(σ : Ω ≃ₐ[k] Ω), hσK⟩) :=
    ha (σ : Ω ≃ₐ[k] Ω) hσK
  calc g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω)
      = f ⟨A, hA⟩ σ := rfl
    _ = z (σ : Ω ≃ₐ[k] Ω) := hz1.symm
    _ = Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          ((IntermediateField.fixingSubgroupEquiv K) ⟨(σ : Ω ≃ₐ[k] Ω), hσK⟩) := hz2
    _ = Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ) := rfl

end Work.SSGRoute.GrunwaldEscapeCore
