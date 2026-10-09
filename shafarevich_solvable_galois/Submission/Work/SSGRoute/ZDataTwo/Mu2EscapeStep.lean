import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
import Submission.Work.SSGRoute.ZDataTwo.mu2KummerFirstElement
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` escape realisation, assembled from its two arithmetic halves

`Work.SSGRoute.mu2EscapeRealisation` — the `p = 2` member of the Grünwald-with-escape family
(`escape_realisation_core` is the odd-`p` one) — is the input that the section-four recursion of the
exceptional case consumes at every step.  This module *assembles* it from

* `Work.SSGRoute.GrunwaldEscapeCore.kummerFirstElement_noImag` (proved here, `p = 2`-ready: the
  odd-`p` statement carries an unused hypothesis `hKimag` which is false at `p = 2`), i.e.
  Grünwald + Kummer theory producing `a ∈ Kˣ` realising the datum on the local groups of `T`;
* the **correction** `Work.SSGRoute.ZDataTwo.Mu2EscapeCorrection` — the genuinely class-field
  theoretic half, isolated below as a standalone `Prop`: move the ramification of `a` outside
  `cs(T)` onto one *new* prime `Q` (chosen by Čebotarev in a ray class, split completely in the
  level `N`), keeping the local data at `T`, and — the `p = 2` addition — keeping total positivity
  (`b` must kill the involutions of `G_K`).  This is the `p = 2` analogue of
  `GrunwaldEscapeCore.grunwald_escape_correction` (which carries `hKimag`, unusable at `p = 2`);
  its proof is the same ray-class construction with the *real places inside the modulus*, so that
  the correction element `γ` is totally positive, together with a sign adjustment of the first
  element (weak approximation at the real places).  It is the one deep rung of this module.

The assembly itself is the one of `GrunwaldEscapeCore.escape_realisation_core`: the realising class
is the global Kummer cochain `ZSplit.nodeKummerCocharZMod K ζ hζK hζ b`, whose additivity, local
constancy, prescribed local data and unramifiedness come from the banked lemmas
(`nodeKummerCocharZMod_add`, `nodeKummerCocharZMod_locConst`, `nodeKummerCocharZMod_apply`) plus the
two halves above; the archimedean clause `z c = 0` for involutions `c` is exactly the extra clause
of the correction.
-/

open scoped Pointwise

set_option linter.unusedVariables false

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

/-- **The correction half of the `p = 2` escape realisation** (as a standalone proposition).

Given a class `a ∈ Kˣ` which realises the datum `g + h A` on the local groups of the finite place
set `T` (one place per `G_K`-class), there are a finite place `Q`, split completely in the level
`N` and lying outside the `G_k`-classes of `T`, and a class `b ∈ Kˣ`, such that

* `b` has the *same* local data at `T` as `a`;
* `b` kills the involutions of `G_K` (total positivity — the `p = 2` addition);
* `b` is unramified outside the `G_K`-classes of `T` and of the single new prime `Q`.

This is `GrunwaldEscapeCore.grunwald_escape_correction` at `p = 2`, specialised to
`L₁ = N`, `L₂ = K`, with the two archimedean hypotheses `hginf`/`hhinf` (the datum kills the
involutions) mirroring the paper's "`y_P = 0` for `P ∈ S_∞`" and with the conclusion strengthened by
total positivity. -/
def Mu2EscapeCorrection (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup) →
      ∃ A ∈ T, SSGRoute.IsConjPlace k A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨ SSGRoute.IsSplitIn k N A)
    (hginf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0)
    (hhinf : ∀ A ∈ T, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → h A c = 0) : Prop :=
  ∀ a : (↥K)ˣ,
    (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ)) →
    ∃ (Q : ValuationSubring Ω) (b : (↥K)ˣ),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k N Q ∧
      (∀ A ∈ T, ¬ SSGRoute.IsConjPlace k A Q) ∧
      (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
            (Work.SSGRoute.gesLocalToGalK K σ) =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
            (Work.SSGRoute.gesLocalToGalK K σ)) ∧
      (∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
          (Work.SSGRoute.gesGalKOfFixing K c hc) = 0) ∧
      (∀ (B : ValuationSubring Ω), SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) →
        (¬ Work.SSGRoute.gesKConj K Q B) →
        ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k B σ →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
            (Work.SSGRoute.gesGalKOfFixing K σ hσ) = 0)

/-- **The `p = 2` escape realisation from its correction half.**  This is
`GrunwaldEscapeCore.escape_realisation_core` at `p = 2` (with the archimedean clause
`z c = 0` for involutions), assembled from the `p = 2`-ready Grünwald + Kummer step
(`GrunwaldEscapeCore.kummerFirstElement_noImag`) and the correction
(`Work.SSGRoute.ZDataTwo.Mu2EscapeCorrection`).

The resulting class is the global Kummer cochain of the corrected element `b`. -/
theorem mu2EscapeRealisation_of_correction (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ : Ω ≃ₐ[k] Ω, τ ∈ K.fixingSubgroup ∧ τ • A = B) → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup) →
      ∃ A ∈ T, SSGRoute.IsConjPlace k A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨ SSGRoute.IsSplitIn k N A)
    (hginf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0)
    (hhinf : ∀ A ∈ T, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → h A c = 0)
    (hcorr : Mu2EscapeCorrection k Ω K N hKN ⟨ζ, hζK⟩
      (ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) T hTfin (fun A hA B hB h => hTdisj A hA B hB h)
      hTcov g hg hgc hgram h hh hhc horth hginf hhinf) :
    ∃ (z : (Ω ≃ₐ[k] Ω) → ZMod 2) (Q : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k N Q ∧
      (∀ A ∈ T, ¬ SSGRoute.IsConjPlace k A Q) ∧
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, z (x * y) = z x + z y) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = g σ + h A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ ∃ τ : Ω ≃ₐ[k] Ω, τ ∈ K.fixingSubgroup ∧ τ • A = B) →
        (¬ ∃ τ : Ω ≃ₐ[k] Ω, τ ∈ K.fixingSubgroup ∧ τ • Q = B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  classical
  haveI hAlgClosed : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  set ζK : ↥K := ⟨ζ, hζK⟩ with hζKdef
  have hζK' : IsPrimitiveRoot ζK 2 :=
    ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- (a) Grünwald + Kummer: the element realising the datum at `T`
  obtain ⟨a, ha⟩ := Work.SSGRoute.GrunwaldEscapeCore.kummerFirstElement_noImag 2 k Ω K ζK hζK'
    T hTfin (fun A hA B hB h => hTdisj A hA B hB h) g hg hgc h hh hhc
  -- (b) the correction: the same local data at `T`, total positivity, and one escaping prime
  obtain ⟨Q, b, hQfin, hQsplit, hQnotT, hagree, hinv, hunr⟩ := hcorr a ha
  refine ⟨ZSplit.nodeKummerCocharZMod K ζ hζK hζ b, Q, hQfin, hQsplit, hQnotT, ?_, ?_, ?_, ?_, ?_⟩
  · exact ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b
  · exact ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ b
  · -- total positivity: the corrected class kills the involutions
    intro c hc hc2
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := b) hc]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩ =
        Work.SSGRoute.gesGalKOfFixing K c hc := rfl
    rw [hto]
    exact hinv c hc hc2
  · -- the prescribed local data at `T`
    intro A hA σ hσ
    have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
    have hσd : σ ∈ SSGRoute.decomp k A := (Subgroup.mem_inf.mp hσ).1
    set σ' : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) :=
      ⟨σ, Subgroup.mem_inf.mpr ⟨hσd, hσK⟩⟩ with hσ'def
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := b) hσK]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ =
        Work.SSGRoute.gesLocalToGalK K σ' := rfl
    rw [hto, hagree A hA σ']
    exact (ha A hA σ').symm
  · -- unramified outside the classes of `T` and of `Q`
    intro B hB hnotT hnotQ σ hσK hσI
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := b) hσK]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ =
        Work.SSGRoute.gesGalKOfFixing K σ hσK := rfl
    rw [hto]
    exact hunr B hB (fun A hA hc => hnotT A hA hc) (fun hc => hnotQ hc) σ hσK hσI

end Work.SSGRoute.ZDataTwo
