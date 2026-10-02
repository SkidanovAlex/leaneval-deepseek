import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The middle term of a morphism of short exact sequences of chain complexes, in a range

If `φ : S₁ ⟶ S₂` is a morphism of short exact short complexes of chain complexes of `ℤ`-modules
(degrees `ℕ`, differential decreasing) and `φ.τ₁`, `φ.τ₃` induce isomorphisms on homology in all
degrees `< N` and epimorphisms in degree `N`, then so does `φ.τ₂`.  This is the "five lemma for the
middle term" of a map of long exact homology sequences.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ComposableArrows
open HomologicalComplex

namespace Work.Serre.SPC

noncomputable section

/-- **The middle term of a morphism of short exact sequences of chain complexes, in a range.** -/
theorem tauTwoRange {S₁ S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (N : ℕ) (hN : 2 ≤ N)
    (h₁ : ∀ i : ℕ, i < N → IsIso (homologyMap φ.τ₁ i))
    (h₃ : ∀ i : ℕ, i < N → IsIso (homologyMap φ.τ₃ i))
    (h₁N : Epi (homologyMap φ.τ₁ N))
    (h₃N : Epi (homologyMap φ.τ₃ N)) :
    (∀ i : ℕ, i < N → IsIso (homologyMap φ.τ₂ i)) ∧
      Epi (homologyMap φ.τ₂ N) := by
  classical
  have hEpi₁ : ∀ i : ℕ, i ≤ N → Epi (homologyMap φ.τ₁ i) := by
    intro i hi
    rcases lt_or_eq_of_le hi with h | h
    · haveI := h₁ i h; infer_instance
    · subst h; exact h₁N
  have hEpi₃ : ∀ i : ℕ, i ≤ N → Epi (homologyMap φ.τ₃ i) := by
    intro i hi
    rcases lt_or_eq_of_le hi with h | h
    · haveI := h₃ i h; infer_instance
    · subst h; exact h₃N
  have hMono₁ : ∀ i : ℕ, i < N → Mono (homologyMap φ.τ₁ i) := by
    intro i h; haveI := h₁ i h; infer_instance
  have hMono₃ : ∀ i : ℕ, i < N → Mono (homologyMap φ.τ₃ i) := by
    intro i h; haveI := h₃ i h; infer_instance
  -- ## (A) `Epi (φ₂ i)` for `1 ≤ i ≤ N`, from the chunk `A_i → B_i → C_i → A_{i-1}`
  have keyEpi : ∀ i : ℕ, 1 ≤ i → i ≤ N → Epi (homologyMap φ.τ₂ i) := by
    intro i hi1 hiN
    have hij : (ComplexShape.down ℕ).Rel i (i - 1) := by
      rw [ComplexShape.down_Rel]; omega
    have hαβ₁ : (ComposableArrows.mk₂ (homologyMap S₁.f i)
        (homologyMap S₁.g i)).Exact :=
      (hS₁.homology_exact₂ i).exact_toComposableArrows
    have hβδ₁ : (ComposableArrows.mk₂ (homologyMap S₁.g i)
        (hS₁.δ i (i - 1) hij)).Exact :=
      (hS₁.homology_exact₃ i (i - 1) hij).exact_toComposableArrows
    have hαβ₂ : (ComposableArrows.mk₂ (homologyMap S₂.f i)
        (homologyMap S₂.g i)).Exact :=
      (hS₂.homology_exact₂ i).exact_toComposableArrows
    have hβδ₂ : (ComposableArrows.mk₂ (homologyMap S₂.g i)
        (hS₂.δ i (i - 1) hij)).Exact :=
      (hS₂.homology_exact₃ i (i - 1) hij).exact_toComposableArrows
    have hR₁ : (ComposableArrows.mk₃ (homologyMap S₁.f i) (homologyMap S₁.g i)
        (hS₁.δ i (i - 1) hij)).Exact :=
      ComposableArrows.exact_of_δ₀ hαβ₁ (by
        show (ComposableArrows.mk₂ (homologyMap S₁.g i) (hS₁.δ i (i - 1) hij)).Exact
        exact hβδ₁)
    have hR₂ : (ComposableArrows.mk₃ (homologyMap S₂.f i) (homologyMap S₂.g i)
        (hS₂.δ i (i - 1) hij)).Exact :=
      ComposableArrows.exact_of_δ₀ hαβ₂ (by
        show (ComposableArrows.mk₂ (homologyMap S₂.g i) (hS₂.δ i (i - 1) hij)).Exact
        exact hβδ₂)
    let ψ : ComposableArrows.mk₃ (homologyMap S₁.f i) (homologyMap S₁.g i)
          (hS₁.δ i (i - 1) hij) ⟶
        ComposableArrows.mk₃ (homologyMap S₂.f i) (homologyMap S₂.g i)
          (hS₂.δ i (i - 1) hij) :=
      ComposableArrows.homMk₃ (homologyMap φ.τ₁ i) (homologyMap φ.τ₂ i)
        (homologyMap φ.τ₃ i) (homologyMap φ.τ₁ (i - 1))
        (naturality' (HomologicalComplex.HomologySequence.mapComposableArrows₂ φ i) 0 1)
        (naturality' (HomologicalComplex.HomologySequence.mapComposableArrows₂ φ i) 1 2)
        (HomologicalComplex.HomologySequence.δ_naturality φ hS₁ hS₂ i (i - 1) hij)
    have key := Abelian.epi_of_epi_of_epi_of_mono ψ hR₁ hR₂
      (show Epi (app' ψ 0) from hEpi₁ i hiN)
      (show Epi (app' ψ 2) from hEpi₃ i hiN)
      (show Mono (app' ψ 3) from hMono₁ (i - 1) (by omega))
    have hψ : app' ψ 1 = homologyMap φ.τ₂ i := rfl
    rwa [hψ] at key
  -- ## (B) `Mono (φ₂ i)` for `i < N`, from the chunk `C_{i+1} → A_i → B_i → C_i`
  have keyMono : ∀ i : ℕ, i < N → Mono (homologyMap φ.τ₂ i) := by
    intro i hiN
    have hij : (ComplexShape.down ℕ).Rel (i + 1) i := by
      rw [ComplexShape.down_Rel]
    have hδ₁ : (ComposableArrows.mk₂ (hS₁.δ (i + 1) i hij)
        (homologyMap S₁.f i)).Exact :=
      (hS₁.homology_exact₁ (i + 1) i hij).exact_toComposableArrows
    have hαβ₁ : (ComposableArrows.mk₂ (homologyMap S₁.f i)
        (homologyMap S₁.g i)).Exact :=
      (hS₁.homology_exact₂ i).exact_toComposableArrows
    have hδ₂ : (ComposableArrows.mk₂ (hS₂.δ (i + 1) i hij)
        (homologyMap S₂.f i)).Exact :=
      (hS₂.homology_exact₁ (i + 1) i hij).exact_toComposableArrows
    have hαβ₂ : (ComposableArrows.mk₂ (homologyMap S₂.f i)
        (homologyMap S₂.g i)).Exact :=
      (hS₂.homology_exact₂ i).exact_toComposableArrows
    have hR₁ : (ComposableArrows.mk₃ (hS₁.δ (i + 1) i hij) (homologyMap S₁.f i)
        (homologyMap S₁.g i)).Exact :=
      ComposableArrows.exact_of_δ₀ hδ₁ (by
        show (ComposableArrows.mk₂ (homologyMap S₁.f i) (homologyMap S₁.g i)).Exact
        exact hαβ₁)
    have hR₂ : (ComposableArrows.mk₃ (hS₂.δ (i + 1) i hij) (homologyMap S₂.f i)
        (homologyMap S₂.g i)).Exact :=
      ComposableArrows.exact_of_δ₀ hδ₂ (by
        show (ComposableArrows.mk₂ (homologyMap S₂.f i) (homologyMap S₂.g i)).Exact
        exact hαβ₂)
    let ψ : ComposableArrows.mk₃ (hS₁.δ (i + 1) i hij) (homologyMap S₁.f i)
          (homologyMap S₁.g i) ⟶
        ComposableArrows.mk₃ (hS₂.δ (i + 1) i hij) (homologyMap S₂.f i)
          (homologyMap S₂.g i) :=
      ComposableArrows.homMk₃ (homologyMap φ.τ₃ (i + 1)) (homologyMap φ.τ₁ i)
        (homologyMap φ.τ₂ i) (homologyMap φ.τ₃ i)
        (HomologicalComplex.HomologySequence.δ_naturality φ hS₁ hS₂ (i + 1) i hij)
        (naturality' (HomologicalComplex.HomologySequence.mapComposableArrows₂ φ i) 0 1)
        (naturality' (HomologicalComplex.HomologySequence.mapComposableArrows₂ φ i) 1 2)
    have key := Abelian.mono_of_epi_of_mono_of_mono ψ hR₁ hR₂
      (show Epi (app' ψ 0) from hEpi₃ (i + 1) (by omega))
      (show Mono (app' ψ 1) from hMono₁ i hiN)
      (show Mono (app' ψ 3) from hMono₃ i hiN)
    have hψ : app' ψ 2 = homologyMap φ.τ₂ i := rfl
    rwa [hψ] at key
  -- ## (C) `Epi (φ₂ 0)`, the bottom degree
  have keyEpi0 : Epi (homologyMap φ.τ₂ 0) := by
    have hR₂ := HomologicalComplex.HomologySequence.composableArrows₂_exact hS₂ 0
    have hβ : Epi ((HomologicalComplex.HomologySequence.composableArrows₂ S₁ 0).map' 1 2) := by
      haveI : Epi S₁.g := hS₁.epi_g
      have hh := epi_homologyMap_of_epi_of_not_rel S₁.g 0 (fun j hj => by
        rw [ComplexShape.down_Rel] at hj; omega)
      show Epi (homologyMap S₁.g 0)
      exact hh
    have key := Abelian.epi_of_epi_of_epi_of_epi
      (HomologicalComplex.HomologySequence.mapComposableArrows₂ φ 0) hR₂ hβ
      (show Epi (app' (HomologicalComplex.HomologySequence.mapComposableArrows₂ φ 0) 0)
        from hEpi₁ 0 (by omega))
      (show Epi (app' (HomologicalComplex.HomologySequence.mapComposableArrows₂ φ 0) 2)
        from hEpi₃ 0 (by omega))
    have hψ : app' (HomologicalComplex.HomologySequence.mapComposableArrows₂ φ 0) 1
        = homologyMap φ.τ₂ 0 := rfl
    rwa [hψ] at key
  constructor
  · intro i hi
    have hepi : Epi (homologyMap φ.τ₂ i) := by
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; exact keyEpi0
      · exact keyEpi i h (le_of_lt hi)
    have hmono : Mono (homologyMap φ.τ₂ i) := keyMono i hi
    haveI := hepi
    haveI := hmono
    exact isIso_of_mono_of_epi _
  · exact keyEpi N (by omega) le_rfl

end

end Work.Serre.SPC
