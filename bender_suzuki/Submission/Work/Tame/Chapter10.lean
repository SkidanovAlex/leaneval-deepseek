import Submission.Work.Tame.Tau

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.Chapter10` — Feit–Thompson §10: coherent and subcoherent sets of characters

This module continues `Work.Tame` with the definitions of Feit–Thompson Chapter III §10
(pp. 809–816):

* the *weight* `‖χ‖²` and `x(𝓢₁)` of p. 810;
* `IsExtension`: an extension of the Dade map `τ` in the sense of Definition 10.1(ii);
* `FTCoherent`: **Definition 10.1** — a set `𝓢` of generalized characters of `𝔏 = N(L̂)` is
  coherent for `τ`;
* `Aset`: the set `𝓐(𝓢₁, τ₁; 𝓣, τ₂)` of p. 810;
* `Subcoherent`: **Definition 10.2** — the pair `(𝓢₁, τ*)` is subcoherent in `𝓢`;
* `Hyp10_2` (**Hypothesis 10.2**, p. 814) and `Hyp10_1` (**Hypothesis 10.1**, p. 811).

## Remarks on the formalisation

* Feit–Thompson compare *degrees* and *weights* of generalized characters.  A generalized
  character has an integral degree and a natural weight `⟨χ,χ⟩`; we read both off as real numbers
  (`rdeg`, `rwt`).  For generalized characters this is exact.
* `𝓒(𝓢)` (p. 810) denotes the complex span of a set of class functions; it is `CSpan`.
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.Tame

universe u

variable {Y : Type*}

section Weight

variable [Group Y] [Fintype Y]

/-- The *degree* `χ(1)` of a class function, read as a real number (Feit–Thompson compare
degrees of generalized characters, which are integers). -/
def rdeg (χ : Y → ℂ) : ℝ := (χ 1).re

/-- The *weight* `‖χ‖² = ⟨χ,χ⟩` (Feit–Thompson p. 810), read as a real number.  For a
generalized character `χ` this is the natural number `⟨χ,χ⟩`. -/
def rwt (χ : Y → ℂ) : ℝ := (Coherence.cfInner χ χ).re

/-- Feit–Thompson's `x(𝓢₁)` (p. 810): the smallest weight of any character in `𝓢₁` of minimum
degree.  We return `0` for the empty set. -/
noncomputable def xMin (S : Finset (Y → ℂ)) : ℝ :=
  if h : S.Nonempty then
    let d : ℝ := Finset.min' (S.image rdeg) (Finset.image_nonempty.mpr h)
    Finset.min' ((S.filter (fun χ => rdeg χ = d)).image rwt) (by
      obtain ⟨χ, hχS, hχd⟩ := Finset.mem_image.mp (Finset.min'_mem (S.image rdeg) _)
      exact Finset.image_nonempty.mpr ⟨χ, Finset.mem_filter.mpr ⟨hχS, hχd⟩⟩)
  else 0

/-- The complex span `𝓒(𝓢)` of a finite set of class functions (Feit–Thompson p. 810). -/
def CSpan (S : Finset (Y → ℂ)) : Submodule ℂ (Y → ℂ) := Submodule.span ℂ (S : Set (Y → ℂ))

end Weight

variable {X : Type u} [Group X] [Fintype X]

/-- `τ'` is an *extension of `τ` to `𝓢`* in the sense of Feit–Thompson Definition 10.1(ii): it
agrees with the Dade map `τ` of (9.4) on `𝓘₀(𝓢) = ℤ[𝓢]⁰`, it is an isometry on all of `ℤ[𝓢]`, and
it maps `𝓢` into generalized characters of `X`. -/
def IsExtension (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X)
    (S : Finset (↥(Lgrp Lhat) → ℂ)) (τ' : (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (X → ℂ)) : Prop :=
  (∀ α ∈ Coherence.ZSpan0 S, τ' α = tau Lhat n Hs α) ∧
    Coherence.IsometryOnAll S τ' ∧ ∀ χ ∈ S, CharCore.IsVChar (τ' χ)

/-- **Feit–Thompson Definition 10.1** (p. 809).  A set `𝓢` of generalized characters of
`𝔏 = N(L̂)` is *coherent* (for the tamely imbedded set `L̂` and its Dade map `τ` of (9.4)) if

(i) `𝓘₀(𝓢) ≠ 0`, i.e. `ℤ[𝓢]⁰ ≠ 0`;
(ii) `τ` extends from `𝓘₀(𝓢)` to an isometry of `ℤ[𝓢]` whose values on `𝓢` are generalized
characters of `X`;
(iii) `𝓘₀(𝓢) ⊆ 𝓘₀(L̂)`, i.e. every element of `𝓘₀(𝓢) = ℤ[𝓢]⁰` vanishes outside `L̂`.

Feit–Thompson's (iii) is the condition on the *degree-zero integral combinations* of the members
of `𝓢`, not on the members themselves; the two differ (e.g. `X = S₃`, `L̂ = {1} ∪ (transpositions)`,
`𝓢 = {triv, sign}`: `triv - sign` vanishes off `L̂` while neither member does). -/
def FTCoherent (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X)
    (S : Finset (↥(Lgrp Lhat) → ℂ)) : Prop :=
  Coherence.ZSpan0 S ≠ ⊥ ∧
    (∀ α ∈ Coherence.ZSpan0 S, ∀ l : ↥(Lgrp Lhat), (l : X) ∉ Lhat → α l = 0) ∧
    Coherence.Coherent S (tau Lhat n Hs)

theorem FTCoherent.isExtension {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    {S : Finset (↥(Lgrp Lhat) → ℂ)} (h : FTCoherent Lhat n Hs S) :
    ∃ τ' : (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (X → ℂ), IsExtension Lhat n Hs S τ' := by
  obtain ⟨τ', h1, h2, h3⟩ := h.2.2
  exact ⟨τ', h1, h2, fun χ hχ => CharCore.IsVChar_iff_coherence (τ' χ) |>.mpr (h3 χ hχ)⟩

/-- Feit–Thompson p. 810: the set `𝓐(𝓢₁, τ₁; 𝓣, τ₂)`.  `α` lies in it if
(i) `α ∈ 𝓘₀(𝓢)`, and
(ii) `α^τ = Δ₁ + Δ₂` with
 (a) `Δ₂ ∈ 𝓒(𝓣^{τ₂})`,
 (b) `Δ₁` is not orthogonal to `𝓘₀(𝓢₁)^τ`,
 (c) `‖Δ₁‖² ≤ x(𝓢₁)`. -/
def Aset (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X)
    (S : Finset (↥(Lgrp Lhat) → ℂ)) (S1 : Finset (↥(Lgrp Lhat) → ℂ))
    (τ1 : (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (X → ℂ))
    (T : Finset (↥(Lgrp Lhat) → ℂ)) (τ2 : (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (X → ℂ))
    (α : ↥(Lgrp Lhat) → ℂ) : Prop :=
  α ∈ Coherence.ZSpan0 S ∧
    ∃ Δ1 Δ2 : X → ℂ,
      tau Lhat n Hs α = Δ1 + Δ2 ∧
        Δ2 ∈ CSpan (T.image τ2) ∧
        (∃ β ∈ Coherence.ZSpan0 S1, Coherence.cfInner Δ1 (τ1 β) ≠ 0) ∧
        rwt Δ1 ≤ xMin S1

/-- **Feit–Thompson Definition 10.2** (p. 811).  Let `𝓢₁ ⊆ 𝓢` be a coherent subset and let `τ*`
be an extension of `τ` to `𝓢₁`.  The pair `(𝓢₁, τ*)` is *subcoherent* in `𝓢` if, whenever `𝓣` is a
coherent subset of `𝓢` orthogonal to `𝓢₁` (the coherence of `𝓣` is a hypothesis here, as in
Feit–Thompson's phrase "any coherent subset"), and `τ₁`, `τ₂` are extensions of `τ` to `𝓢₁`, `𝓣`:

(i) `𝓢₁^{τ₁}` is orthogonal to `𝓣^{τ₂}`;
(ii) if `α ∈ 𝓐(𝓢₁, τ₁; 𝓣, τ₂)`, then `α^τ` is a sum of two generalized characters, one of which
is orthogonal to `𝓢₁^{τ*}`, and the other is in `±𝓢₁^{τ*}`. -/
def Subcoherent (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X)
    (S : Finset (↥(Lgrp Lhat) → ℂ)) (S1 : Finset (↥(Lgrp Lhat) → ℂ))
    (τstar : (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (X → ℂ)) : Prop :=
  FTCoherent Lhat n Hs S1 ∧ IsExtension Lhat n Hs S1 τstar ∧
    ∀ (T : Finset (↥(Lgrp Lhat) → ℂ))
      (τ1 τ2 : (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (X → ℂ)),
      T ⊆ S → FTCoherent Lhat n Hs T → (∀ χ ∈ S1, ∀ ψ ∈ T, Coherence.cfInner χ ψ = 0) →
        IsExtension Lhat n Hs S1 τ1 → IsExtension Lhat n Hs T τ2 →
        (∀ χ ∈ S1, ∀ ψ ∈ T, Coherence.cfInner (τ1 χ) (τ2 ψ) = 0) ∧
          (∀ α : ↥(Lgrp Lhat) → ℂ, Aset Lhat n Hs S S1 τ1 T τ2 α →
            ∃ Δ1 Δ2 : X → ℂ, tau Lhat n Hs α = Δ1 + Δ2 ∧
              (∀ χ ∈ S1, Coherence.cfInner Δ1 (τstar χ) = 0) ∧
              (∃ χ ∈ S1, Δ2 = τstar χ ∨ Δ2 = -τstar χ))

end Work.Tame

namespace Work.Tame

open Classical

/-- Monotonicity of `Subcoherent` in the ambient set: if `𝓢₁ ⊆ 𝓢' ⊆ 𝓢` and `(𝓢₁, τ*)` is
subcoherent in `𝓢`, then it is subcoherent in `𝓢'`.  Both the quantifier over `𝓣` (which is a
subset of the ambient set) and the set `𝓐(𝓢₁, τ₁; 𝓣, τ₂)` (which is defined in terms of `ℤ[𝓢]⁰`)
are monotone under shrinking `𝓢` to `𝓢'`. -/
theorem Subcoherent.mono {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} {S S' S1 : Finset (↥(Lgrp Lhat) → ℂ)}
    {τstar : (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (X → ℂ)}
    (hS1 : S1 ⊆ S') (hSS : S' ⊆ S)
    (h : Subcoherent Lhat n Hs S S1 τstar) :
    Subcoherent Lhat n Hs S' S1 τstar := by
  obtain ⟨hc, hext, hmain⟩ := h
  refine ⟨hc, hext, fun T τ1 τ2 hT hcohT horth he1 he2 => ?_⟩
  obtain ⟨h1, h2⟩ := hmain T τ1 τ2 (fun x hx => hSS (hT hx)) hcohT horth he1 he2
  exact ⟨h1, fun α hα => h2 α ⟨Coherence.zSpan0_mono hSS hα.1, hα.2⟩⟩

end Work.Tame
