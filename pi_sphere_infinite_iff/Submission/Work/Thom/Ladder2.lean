import Mathlib
import Submission.Work.Thom.Ladder

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The five lemma for two long exact sequences, in the "`M`-first" enumeration

`Work.Thom.five_lemma_LES` enumerates both sequences from their *third* term, which is what makes
the ladder squares match without any degree arithmetic, but then the terms of the first sequence run
over the degrees `1, 2, 3, …` only, so the base degree `0` of the Thom isomorphism is not covered.

This file gives the complementary enumeration: the sequences are written

`M k --F--> P k --G--> Q k --δ--> M (k+1)`

so that the conclusion `∀ k, IsIso (TM k)` covers the degrees `k = 0, 1, 2, …`.  The price is that
the two "left end" cases (`k = 0` of the injectivity and of the surjectivity chase) are not supplied
by the exactness of the sequences, and must be added as hypotheses:

* `f₁ : ker (F₁ 0) = ⊥` — nothing to the left of the first sequence (for the base of a
  Mayer--Vietoris ladder this is automatic);
* `f₂ : ker (F₂ 0) ⊆ range (TM 0)` — the second sequence's left end is *in the image* of the
  ladder map (this is the statement that the piece cohomology vanishes below the rank, so that the
  pair's left end is trivial).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Thom

noncomputable section

/-- **The five lemma for two long exact sequences, `M`-first enumeration.** -/
theorem five_lemma_LES' {M₁ P₁ Q₁ M₂ P₂ Q₂ : ℕ → ModuleCat ℤ}
    (F₁ : ∀ k, M₁ k ⟶ P₁ k) (G₁ : ∀ k, P₁ k ⟶ Q₁ k) (δ₁ : ∀ k, Q₁ k ⟶ M₁ (k + 1))
    (F₂ : ∀ k, M₂ k ⟶ P₂ k) (G₂ : ∀ k, P₂ k ⟶ Q₂ k) (δ₂ : ∀ k, Q₂ k ⟶ M₂ (k + 1))
    (e₂₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (F₁ k))
      = LinearMap.ker (ModuleCat.Hom.hom (G₁ k)))
    (e₃₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (G₁ k))
      = LinearMap.ker (ModuleCat.Hom.hom (δ₁ k)))
    (e₁₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (δ₁ k))
      = LinearMap.ker (ModuleCat.Hom.hom (F₁ (k + 1))))
    (e₂₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (F₂ k))
      = LinearMap.ker (ModuleCat.Hom.hom (G₂ k)))
    (e₃₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (G₂ k))
      = LinearMap.ker (ModuleCat.Hom.hom (δ₂ k)))
    (e₁₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (δ₂ k))
      = LinearMap.ker (ModuleCat.Hom.hom (F₂ (k + 1))))
    (TM : ∀ k, M₁ k ⟶ M₂ k) (TP : ∀ k, P₁ k ⟶ P₂ k) (TQ : ∀ k, Q₁ k ⟶ Q₂ k)
    (f₁ : LinearMap.ker (ModuleCat.Hom.hom (F₁ 0)) = ⊥)
    (f₂ : ∀ u : M₂ 0, ModuleCat.Hom.hom (F₂ 0) u = 0 →
      ∃ x : M₁ 0, ModuleCat.Hom.hom (TM 0) x = u)
    (hF : ∀ k, F₁ k ≫ TP k = TM k ≫ F₂ k) (hG : ∀ k, G₁ k ≫ TQ k = TP k ≫ G₂ k)
    (hδ : ∀ k, δ₁ k ≫ TM (k + 1) = TQ k ≫ δ₂ k)
    (hP : ∀ k, IsIso (TP k)) (hQ : ∀ k, IsIso (TQ k)) :
    ∀ k, IsIso (TM k) := by
  have hF' : ∀ j, ModuleCat.Hom.hom (TP j) ∘ₗ ModuleCat.Hom.hom (F₁ j)
      = ModuleCat.Hom.hom (F₂ j) ∘ₗ ModuleCat.Hom.hom (TM j) := by
    intro j
    have h := congrArg ModuleCat.Hom.hom (hF j)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact h
  have hG' : ∀ j, ModuleCat.Hom.hom (TQ j) ∘ₗ ModuleCat.Hom.hom (G₁ j)
      = ModuleCat.Hom.hom (G₂ j) ∘ₗ ModuleCat.Hom.hom (TP j) := by
    intro j
    have h := congrArg ModuleCat.Hom.hom (hG j)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact h
  have hδ' : ∀ j, ModuleCat.Hom.hom (TM (j + 1)) ∘ₗ ModuleCat.Hom.hom (δ₁ j)
      = ModuleCat.Hom.hom (δ₂ j) ∘ₗ ModuleCat.Hom.hom (TQ j) := by
    intro j
    have h := congrArg ModuleCat.Hom.hom (hδ j)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact h
  haveI hPm : ∀ j, Mono (TP j) := fun j => ((isIso_iff_mono_and_epi _).mp (hP j)).1
  haveI hPe : ∀ j, Epi (TP j) := fun j => ((isIso_iff_mono_and_epi _).mp (hP j)).2
  haveI hQm : ∀ j, Mono (TQ j) := fun j => ((isIso_iff_mono_and_epi _).mp (hQ j)).1
  haveI hQe : ∀ j, Epi (TQ j) := fun j => ((isIso_iff_mono_and_epi _).mp (hQ j)).2
  have hinjP : ∀ j, Function.Injective (ModuleCat.Hom.hom (TP j)) :=
    fun j => (ModuleCat.mono_iff_injective _).mp (hPm j)
  have hsurjP : ∀ j, Function.Surjective (ModuleCat.Hom.hom (TP j)) :=
    fun j => (ModuleCat.epi_iff_surjective _).mp (hPe j)
  have hinjQ : ∀ j, Function.Injective (ModuleCat.Hom.hom (TQ j)) :=
    fun j => (ModuleCat.mono_iff_injective _).mp (hQm j)
  have hsurjQ : ∀ j, Function.Surjective (ModuleCat.Hom.hom (TQ j)) :=
    fun j => (ModuleCat.epi_iff_surjective _).mp (hQe j)
  intro k
  rw [isIso_iff_mono_and_epi]
  constructor
  · rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    have hx : ModuleCat.Hom.hom (TM k) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hF0 : ModuleCat.Hom.hom (F₁ k) (x - y) = 0 := by
      apply hinjP k
      have h1 : ModuleCat.Hom.hom (TP k) (ModuleCat.Hom.hom (F₁ k) (x - y))
          = ModuleCat.Hom.hom (F₂ k) (ModuleCat.Hom.hom (TM k) (x - y)) := by
        have h := LinearMap.congr_fun (hF' k) (x - y)
        rwa [LinearMap.comp_apply, LinearMap.comp_apply] at h
      rw [h1, hx]
      simp only [map_zero]
    rcases k with _ | k'
    · have hmem : x - y ∈ (⊥ : Submodule ℤ ↑(M₁ 0)) := by
        rw [← f₁]
        exact LinearMap.mem_ker.mpr hF0
      rw [Submodule.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
    · obtain ⟨w, hw⟩ := (show x - y ∈ LinearMap.range (ModuleCat.Hom.hom (δ₁ k')) from by
        rw [e₁₁ k']
        exact LinearMap.mem_ker.mpr hF0)
      have hTMδ : ModuleCat.Hom.hom (TM (k' + 1)) (ModuleCat.Hom.hom (δ₁ k') w) = 0 := by
        rw [hw]; exact hx
      have hδ2 : ModuleCat.Hom.hom (δ₂ k') (ModuleCat.Hom.hom (TQ k') w) = 0 := by
        have h := LinearMap.congr_fun (hδ' k') w
        rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
        rw [← h, hTMδ]
      obtain ⟨u, hu⟩ := (show ModuleCat.Hom.hom (TQ k') w
          ∈ LinearMap.range (ModuleCat.Hom.hom (G₂ k')) from by
        rw [e₃₂ k']
        exact LinearMap.mem_ker.mpr hδ2)
      obtain ⟨v, hv⟩ := hsurjP k' u
      have hwu : w = ModuleCat.Hom.hom (G₁ k') v := by
        apply hinjQ k'
        rw [← hu, ← hv]
        exact (LinearMap.congr_fun (hG' k') v).symm
      have h0 : ModuleCat.Hom.hom (δ₁ k') (ModuleCat.Hom.hom (G₁ k') v) = 0 := by
        have hmem : ModuleCat.Hom.hom (G₁ k') v ∈ LinearMap.range (ModuleCat.Hom.hom (G₁ k')) :=
          ⟨v, rfl⟩
        rw [e₃₁ k'] at hmem
        exact LinearMap.mem_ker.mp hmem
      rw [hwu, h0] at hw
      exact sub_eq_zero.mp hw.symm
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    obtain ⟨z, hz⟩ := hsurjP k (ModuleCat.Hom.hom (F₂ k) y)
    have hG1z : ModuleCat.Hom.hom (G₁ k) z = 0 := by
      have h1 : ModuleCat.Hom.hom (TQ k) (ModuleCat.Hom.hom (G₁ k) z) = 0 := by
        have h2 : ModuleCat.Hom.hom (TQ k) (ModuleCat.Hom.hom (G₁ k) z)
            = ModuleCat.Hom.hom (G₂ k) (ModuleCat.Hom.hom (TP k) z) := by
          have h := LinearMap.congr_fun (hG' k) z
          rwa [LinearMap.comp_apply, LinearMap.comp_apply] at h
        rw [h2, hz]
        have hmem : ModuleCat.Hom.hom (F₂ k) y ∈ LinearMap.range (ModuleCat.Hom.hom (F₂ k)) :=
          ⟨y, rfl⟩
        rw [e₂₂ k] at hmem
        exact LinearMap.mem_ker.mp hmem
      exact hinjQ k (by rw [h1]; simp only [map_zero])
    obtain ⟨x, hx⟩ := (show z ∈ LinearMap.range (ModuleCat.Hom.hom (F₁ k)) from by
      rw [e₂₁ k]
      exact LinearMap.mem_ker.mpr hG1z)
    have hdiff : ModuleCat.Hom.hom (F₂ k) (ModuleCat.Hom.hom (TM k) x - y) = 0 := by
      rw [map_sub]
      have h1 : ModuleCat.Hom.hom (F₂ k) (ModuleCat.Hom.hom (TM k) x)
          = ModuleCat.Hom.hom (TP k) (ModuleCat.Hom.hom (F₁ k) x) :=
        (LinearMap.congr_fun (hF' k) x).symm
      rw [h1, hx, hz, sub_self]
    rcases k with _ | k'
    · obtain ⟨x', hx'⟩ := f₂ (ModuleCat.Hom.hom (TM 0) x - y) hdiff
      exact ⟨x - x', by rw [map_sub, hx']; abel⟩
    · obtain ⟨u, hu⟩ := (show ModuleCat.Hom.hom (TM (k' + 1)) x - y
          ∈ LinearMap.range (ModuleCat.Hom.hom (δ₂ k')) from by
        rw [e₁₂ k']
        exact LinearMap.mem_ker.mpr hdiff)
      obtain ⟨w, hw⟩ := hsurjQ k' u
      refine ⟨x - ModuleCat.Hom.hom (δ₁ k') w, ?_⟩
      have h1 : ModuleCat.Hom.hom (TM (k' + 1)) (ModuleCat.Hom.hom (δ₁ k') w)
          = ModuleCat.Hom.hom (TM (k' + 1)) x - y := by
        have h := LinearMap.congr_fun (hδ' k') w
        rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
        rw [h, hw, hu]
      rw [map_sub, h1]
      abel

end

end Work.Thom
