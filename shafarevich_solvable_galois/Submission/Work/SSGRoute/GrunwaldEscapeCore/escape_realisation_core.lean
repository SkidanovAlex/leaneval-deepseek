import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_correction
import Submission.Work.SSGRoute.GrunwaldEscapeCore.grunwald_kummer_first_element
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Grünwald with escape, specialised to `L₁ := N`, `L₂ := K` (node N2 of the Step-4 design)

This module proves `Work.SSGRoute.GrunwaldEscapeCore.escape_realisation_core` from its two halves:

* `Work.SSGRoute.GrunwaldEscapeCore.grunwald_kummer_first_element` (proved, axiom-clean) — the
  Grünwald + Kummer step: a single `a ∈ Kˣ` whose Kummer character realises the local datum
  `g + h A` at every `A ∈ T`;
* `Work.SSGRoute.GrunwaldEscapeCore.escape_correction` — the class-field-theoretic correction: a
  `b ∈ Kˣ` with the *same* local data at `T` and whose Kummer character is unramified outside the
  `K`-conjugates of `T` and of one auxiliary place `Q`, which is finite, split completely in `N`
  and not `K`-conjugate to any element of `T`.

The class realising the datum is the zero extension `Work.SSGRoute.ZSplit.nodeKummerCocharZMod` of
the Kummer character of `b`; `ZSplit.nodeKummerCocharZMod_add` and
`ZSplit.nodeKummerCocharZMod_locConst` (both proved) give additivity and local constancy, and
`ZSplit.nodeKummerCocharZMod_apply` identifies its values on `G_K` with `kummerCharZMod`.

Why the two orthogonality hypotheses of the general node collapse here: with `L₂ := K` the
character form of the second hypothesis is vacuous (every `χ` vanishing on `K.fixingSubgroup`
vanishes on `decomp k A ⊓ K.fixingSubgroup ⊆ K.fixingSubgroup`), and the second disjunct of the
first hypothesis (`∀ χ`, vanishing on `L₁.fixingSubgroup = N.fixingSubgroup` implies vanishing on
the local group) follows from `SSGRoute.IsSplitIn k N A`, which is exactly the second disjunct of
this module's `horth`. The remaining arithmetic — that the *datum* `g + h A` at the places where
`h A` vanishes is orthogonal to the characters of `N/K` unramified outside `T` — is supplied by the
reciprocity computation recorded in `NOTE_escape_correction_route.md` §0 and carried out inside
`escape_correction`.
-/

namespace Work.SSGRoute.GrunwaldEscapeCore

open _root_.SSGRoute
open scoped Pointwise

theorem escape_realisation_core (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      SSGRoute.IsSplitIn k N A) :
    ∃ (z : (Ω ≃ₐ[k] Ω) → ZMod p) (Q : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k N Q ∧
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, z (x * y) = z x + z y) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = g σ + h A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → (¬ Work.SSGRoute.gesKConj K Q B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  classical
  haveI hAlgClosed : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  -- the primitive `p`-th root of unity, viewed in `K`
  set ζK : ↥K := ⟨ζ, hζK⟩ with hζKdef
  have hζK' : IsPrimitiveRoot ζK p :=
    ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- `hKimag` is vacuous for `p ≠ 2`
  have hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1 :=
    fun h2 => absurd h2 hp
  -- (a) Grünwald + Kummer: the element realising the datum at `T`
  obtain ⟨a, ha⟩ := grunwald_kummer_first_element p k Ω K ζK hζK' hKimag T hTfin hTdisj
    g hg hgc h hh hhc
  -- (b) the class-field-theoretic correction: an element with the same local data whose Kummer
  -- character is unramified outside the classes of `T` and of a single place split in `N`
  obtain ⟨Q, b, hQfin, hQsplit, hQnotT, hagree, hesc⟩ :=
    escape_correction p hp k Ω K N hKN ζK hζK' hKimag T hTfin hTdisj hTcov g hg hgc hgram
      h hh hhc horth a ha
  refine ⟨ZSplit.nodeKummerCocharZMod K ζ hζK hζ b, Q, hQfin, hQsplit, hQnotT, ?_, ?_, ?_, ?_⟩
  · -- additivity on `G_K`
    exact ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b
  · -- local constancy on `G_K`
    exact ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ b
  · -- the prescribed local datum at `T`
    intro A hA σ hσ
    have hσK : (σ : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := b) hσK]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨(σ : Ω ≃ₐ[k] Ω), hσK⟩ =
        Work.SSGRoute.gesLocalToGalK K ⟨σ, hσ⟩ := rfl
    rw [hto]
    exact (hagree A hA ⟨σ, hσ⟩).symm
  · -- unramified outside the classes of `T` and of `Q`
    intro B hB hnotT hnotQ σ hσ hI
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := b) hσ]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ =
        Work.SSGRoute.gesGalKOfFixing K σ hσ := rfl
    rw [hto]
    exact hesc B hB hnotT hnotQ σ hσ hI

end Work.SSGRoute.GrunwaldEscapeCore
