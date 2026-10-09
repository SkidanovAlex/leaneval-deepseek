import Mathlib
import Submission.Work.SSGRoute.H9.swZSixOfHistK
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary computations for the refined confinement of the §4 recursion

This file collects the two purely computational ingredients of
`Work.SSGRoute.H9.swHistChi_confinement_proved`:

* `correctionDatum_own` / `correctionDatum_sibling`: the value of the correction datum at the
  `K`-class of its own escape prime (`−g`) and at a *sibling* of it (`−z − g`);
* `histDatum_escape_block_own` / `histDatum_escape_block_sibling`: the accumulated datum of a history
  at a block of the `k`-place of the `l`-th escape prime, where all the corrections of the *other*
  stages vanish because the escape primes have pairwise distinct `k`-places;
* `histK_not_isConjPlace_of_isConjPlace`: the pairwise `k`-disjointness of the escape classes in the
  form used by the accumulation (`Work.SSGRoute.H9.histK_escape_kdisj`, unwound).
-/

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open scoped Pointwise

set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-- **The correction datum at the `K`-class of its own escape prime is `−g`.** -/
theorem correctionDatum_own (K : IntermediateField k Ω) (g z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (Q A : ValuationSubring Ω) (h : Work.SSGRoute.gesKConj K Q A) :
    Work.SSGRoute.ZDataMup.correctionDatum K g z Q A = fun τ => - g τ := by
  funext τ
  simp only [Work.SSGRoute.ZDataMup.correctionDatum, if_pos h]

/-- **The correction datum at a sibling of its escape prime is `−z − g`.** -/
theorem correctionDatum_sibling (K : IntermediateField k Ω) (g z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (Q A : ValuationSubring Ω) (h1 : ¬ Work.SSGRoute.gesKConj K Q A)
    (h2 : SSGRoute.IsConjPlace k Q A) :
    Work.SSGRoute.ZDataMup.correctionDatum K g z Q A = fun τ => - z τ - g τ := by
  funext τ
  simp only [Work.SSGRoute.ZDataMup.correctionDatum, if_neg h1, if_pos h2]

/-- **The accumulated datum at the `K`-class of the `l`-th escape prime.**  All the corrections of
the other stages vanish (their escape primes have `k`-distinct places, `hsep`), and the correction of
stage `l` is `−½y`. -/
theorem histDatum_escape_block_own {n : ℕ} (K : IntermediateField k Ω)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (Q : Fin n → ValuationSubring Ω) (z : Fin n → (Ω ≃ₐ[k] Ω) → ZMod p)
    (l : Fin n) (A : ValuationSubring Ω) (h : Work.SSGRoute.gesKConj K (Q l) A)
    (hsep : ∀ j : Fin n, j ≠ l → ¬ SSGRoute.IsConjPlace k (Q j) A) :
    Work.SSGRoute.ZDataMup.histDatum K y (fun j => (Q j, z j)) A
      = fun τ => -((2 : ZMod p)⁻¹ * y τ) := by
  classical
  funext τ
  show Finset.univ.sum (fun j : Fin n =>
      Work.SSGRoute.ZDataMup.correctionDatum K (fun σ => (2 : ZMod p)⁻¹ * y σ) (z j) (Q j) A τ)
    = -((2 : ZMod p)⁻¹ * y τ)
  rw [Finset.sum_eq_single l]
  · have h0 := congrFun (correctionDatum_own K (fun σ => (2 : ZMod p)⁻¹ * y σ) (z l) (Q l) A h) τ
    simpa using h0
  · intro j _ hj
    have h0 := congrFun (Work.SSGRoute.ZDataMup.correctionDatum_eq_zero_of_not_conjPlace K
      (fun σ => (2 : ZMod p)⁻¹ * y σ) (z j) (Q j) A (hsep j hj)) τ
    simpa using h0
  · intro hmem; exact absurd (Finset.mem_univ l) hmem

/-- **The accumulated datum at a sibling of the `l`-th escape prime.** -/
theorem histDatum_escape_block_sibling {n : ℕ} (K : IntermediateField k Ω)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (Q : Fin n → ValuationSubring Ω) (z : Fin n → (Ω ≃ₐ[k] Ω) → ZMod p)
    (l : Fin n) (A : ValuationSubring Ω) (h1 : ¬ Work.SSGRoute.gesKConj K (Q l) A)
    (hA : SSGRoute.IsConjPlace k (Q l) A)
    (hsep : ∀ j : Fin n, j ≠ l → ¬ SSGRoute.IsConjPlace k (Q j) A) :
    Work.SSGRoute.ZDataMup.histDatum K y (fun j => (Q j, z j)) A
      = fun τ => - z l τ - (2 : ZMod p)⁻¹ * y τ := by
  classical
  funext τ
  show Finset.univ.sum (fun j : Fin n =>
      Work.SSGRoute.ZDataMup.correctionDatum K (fun σ => (2 : ZMod p)⁻¹ * y σ) (z j) (Q j) A τ)
    = - z l τ - (2 : ZMod p)⁻¹ * y τ
  rw [Finset.sum_eq_single l]
  · have h0 := congrFun (correctionDatum_sibling K (fun σ => (2 : ZMod p)⁻¹ * y σ)
      (z l) (Q l) A h1 hA) τ
    simpa using h0
  · intro j _ hj
    have h0 := congrFun (Work.SSGRoute.ZDataMup.correctionDatum_eq_zero_of_not_conjPlace K
      (fun σ => (2 : ZMod p)⁻¹ * y σ) (z j) (Q j) A (hsep j hj)) τ
    simpa using h0
  · intro hmem; exact absurd (Finset.mem_univ l) hmem

/-- **The accumulated datum of a Kummer history vanishes on the `T₀`-blocks.** -/
theorem histDatumK_eq_zero_on_T0 (K N : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k N] [IsGalois k N]
    (S : Finset (ValuationSubring Ω)) (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p) (f : ℕ → (ValuationSubring Ω × (↥K)ˣ))
    (hf : HistK (p := p) K N ζ hζ hζK S y f) (m : ℕ) {A : ValuationSubring Ω}
    (hA : A ∈ Work.SSGRoute.ZDataMup.kleadReps K S) :
    histDatumK (p := p) K ζ hζK hζ S y m f A = 0 := by
  simp only [histDatumK, histClass]
  exact Work.SSGRoute.ZDataMup.histDatum_eq_zero_on_T0 (p := p) K N S y _
    (histClass_HistInv K N ζ hζ hζK S y f hf) m A hA

/-- **The accumulated datum of a Kummer history at the `K`-class of the `l`-th escape prime is
`−½y`.** -/
theorem histDatumK_escape_block_own (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (S : Finset (ValuationSubring Ω)) (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (m : ℕ) {l : ℕ} (hlm : l < m)
    {A : ValuationSubring Ω} (h : Work.SSGRoute.gesKConj K ((f l).1) A)
    (hsep : ∀ j : ℕ, j ≠ l → ¬ SSGRoute.IsConjPlace k ((f j).1) A) :
    histDatumK (p := p) K ζ hζK hζ S y m f A = fun τ => -((2 : ZMod p)⁻¹ * y τ) := by
  simp only [histDatumK, histClass]
  exact histDatum_escape_block_own (p := p) K y (fun j : Fin m => (f (j : ℕ)).1)
    (fun j : Fin m => Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f (j : ℕ)).2)
    ⟨l, hlm⟩ A h (fun j hj => hsep (j : ℕ) (fun hh => hj (Fin.ext hh)))

/-- **The accumulated datum of a Kummer history at a sibling of the `l`-th escape prime is
`−χ_{b_l} − ½y`.** -/
theorem histDatumK_escape_block_sibling (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (S : Finset (ValuationSubring Ω)) (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (m : ℕ) {l : ℕ} (hlm : l < m)
    {A : ValuationSubring Ω} (h1 : ¬ Work.SSGRoute.gesKConj K ((f l).1) A)
    (hA : SSGRoute.IsConjPlace k ((f l).1) A)
    (hsep : ∀ j : ℕ, j ≠ l → ¬ SSGRoute.IsConjPlace k ((f j).1) A) :
    histDatumK (p := p) K ζ hζK hζ S y m f A
      = fun τ => - histChi K ζ hζK hζ f l τ - (2 : ZMod p)⁻¹ * y τ := by
  simp only [histDatumK, histClass, histChi]
  exact histDatum_escape_block_sibling (p := p) K y (fun j : Fin m => (f (j : ℕ)).1)
    (fun j : Fin m => Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f (j : ℕ)).2)
    ⟨l, hlm⟩ A h1 hA (fun j hj => hsep (j : ℕ) (fun hh => hj (Fin.ext hh)))

/-- **The escape classes of a `HistK`-history are pairwise `k`-disjoint**, in the form consumed by
the accumulation: if `A` is `k`-conjugate to the `l`-th escape prime then no other escape prime is
`k`-conjugate to `A`. -/
theorem histK_not_isConjPlace_of_isConjPlace (K N : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k N] [IsGalois k N]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (hf : HistK (p := p) K N ζ hζ hζK S y f)
    {l : ℕ} {A : ValuationSubring Ω} (hA : SSGRoute.IsConjPlace k ((f l).1) A) :
    ∀ j : ℕ, j ≠ l → ¬ SSGRoute.IsConjPlace k ((f j).1) A := by
  intro j hj h
  have h2 : SSGRoute.IsConjPlace k ((f j).1) ((f l).1) :=
    SSGRoute.isConjPlace_trans h (SSGRoute.isConjPlace_symm hA)
  rcases lt_or_gt_of_ne hj with hjl | hlj
  · exact (histK_escape_kdisj (p := p) K N ζ hζ hζK S y f hf hjl) h2
  · exact (histK_escape_kdisj (p := p) K N ζ hζ hζK S y f hf hlj)
      (SSGRoute.isConjPlace_symm h2)

end Work.SSGRoute.H9
