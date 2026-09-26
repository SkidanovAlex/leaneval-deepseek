import Mathlib
import Submission.Work.PTCert.GlueDefs

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/GlueDefs.lean` (definitions + Props; read it first) glues the
kernel-checked certificate data to the proved generic chain (`Chain.lean`, `Math.lean`,
`Interfaces.lean`; all their Props are already PROVED: avgPrinciple, labelPrinciple, gramSOS,
avgGram, avgMatInvariant, rowFormula, psdOfBlock, psdSignedPerm, ldlScaledPrinciple,
twistedFourierCriterion, residualAbsorption, letterAction, signCodes8, sigmaGroupFacts, modelSound,
permCheckKSound, ...). The design note is `NOTES_LEAD_glue.md` at the workspace root.
Do NOT change GlueDefs.lean. If the statement is false, `declare_false` with a concrete counterexample.
Put helper lemmas in your own file or under `Submission/Work/PTCert/<yourLemma>/`.
Route. Let h σ x : ∃ y, f y = σ * f x * σ⁻¹ (hypothesis). Then `conjAct f σ x = Classical.choose (h σ x)`
(unfold with `dif_pos`), so `f (conjAct f σ x) = σ * f x * σ⁻¹` (Classical.choose_spec). Everything
follows from this + injectivity:
- ConjAction: injective f and the equation above.
- composition: f (conjAct (σ*τ) x) = (σ*τ) f x (σ*τ)⁻¹ = σ (τ f x τ⁻¹) σ⁻¹ = f (conjAct σ (conjAct τ x));
  σ*τ ∈ Sg (IsFinSubgroup), injectivity.
- `conjAct f 1 x = x`: f y = 1 * f x * 1⁻¹ = f x has the solution y = x, so the `dif` takes the
  `choose` branch and injectivity gives choose = x.
- bijective: left and right inverse `conjAct f σ⁻¹` (σ⁻¹ ∈ Sg; composition + identity).
- last item: injectivity.
-/

namespace Work.PTCert

open Submission.PTCert

/-- The chosen value of `conjAct f σ x` satisfies the defining equation of `conjAct`, whenever the
latter has a solution.  This is the only place where the `Classical.choose` in the definition of
`conjAct` is unfolded. -/
theorem conjAct_spec {G : Type} [Group G] {ι : Type} (f : ι → G) (σ : G) (x : ι)
    (h : ∃ y, f y = σ * f x * σ⁻¹) : f (conjAct f σ x) = σ * f x * σ⁻¹ := by
  unfold conjAct
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem conjActFacts : ConjActFacts := by
  intro G _inst Sg hSg ι f hf hclo
  obtain ⟨h1mem, hmul, hinv⟩ := hSg
  have hspec : ∀ (σ : G) (hσ : σ ∈ Sg) (x : ι), f (conjAct f σ x) = σ * f x * σ⁻¹ :=
    fun σ hσ x => conjAct_spec f σ x (hclo σ hσ x)
  have hcomp : ∀ σ ∈ Sg, ∀ τ ∈ Sg, ∀ x, conjAct f (σ * τ) x = conjAct f σ (conjAct f τ x) := by
    intro σ hσ τ hτ x
    refine hf ?_
    rw [hspec (σ * τ) (hmul σ hσ τ hτ) x, hspec σ hσ (conjAct f τ x), hspec τ hτ x]
    group
  have hone : ∀ x, conjAct f 1 x = x := by
    intro x
    refine hf ?_
    rw [hspec 1 h1mem x]
    simp
  have hleft : ∀ σ ∈ Sg, ∀ x, conjAct f σ (conjAct f σ⁻¹ x) = x := by
    intro σ hσ x
    rw [← hcomp σ hσ σ⁻¹ (hinv σ hσ) x, mul_inv_cancel, hone]
  have hright : ∀ σ ∈ Sg, ∀ x, conjAct f σ⁻¹ (conjAct f σ x) = x := by
    intro σ hσ x
    rw [← hcomp σ⁻¹ (hinv σ hσ) σ hσ x, inv_mul_cancel, hone]
  refine ⟨⟨hf, fun σ hσ x => hspec σ hσ x⟩, hcomp, hone, ?_, ?_⟩
  · intro σ hσ
    exact ⟨fun x y hxy => calc x = conjAct f σ⁻¹ (conjAct f σ x) := (hright σ hσ x).symm
        _ = conjAct f σ⁻¹ (conjAct f σ y) := by rw [hxy]
        _ = y := hright σ hσ y,
      fun y => ⟨conjAct f σ⁻¹ y, hleft σ hσ y⟩⟩
  · intro σ hσ x y hy
    refine hf ?_
    rw [hspec σ hσ x, hy]

end Work.PTCert
