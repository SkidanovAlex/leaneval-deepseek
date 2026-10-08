import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.mem_AU_iff
import Submission.Work.Tame.inConjAU_iff
import Submission.Work.Tame.mem_X0_iff
import Submission.Work.Tame.ft95_tau_apply_of_mem_AL
import Submission.Work.Tame.ft95_tau_eq_zero_of_not_isConj
import Submission.Work.Tame.cfInner_tau_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

open Classical

/-- Local copy: `L ∈ 𝔏_j` is an element of `𝔄_L` (the case `A = A' = L` of the hypothesis that
`θ` is constant on `𝔄_L`). -/
private theorem ft95_self_mem_ALofIdx {X : Type*} [Group X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} {j : Idx n} {L : ↥(Lgrp Lhat)}
    (hL : (L : X) ∈ LofIdx Lhat n Hs j) :
    (L : X) ∈ ALofIdx Lhat n Hs j (L : X) := by
  cases j <;> simp [ALofIdx, AL]

/-- Local copy: a class function takes equal values on conjugate elements. -/
private theorem ft95_apply_of_isConj {X : Type*} [Group X] {f : X → ℂ}
    (hf : CharCore.IsClassFun f) {a b : X} (h : IsConj a b) : f a = f b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  exact (hf a c).symm

/-- Local copy: the Dade map `τ` of (9.4) is a class function of `X`. -/
private theorem ft95_isClassFun_tau {X : Type*} [Group X] [Fintype X] (Lhat : Set X) (n : ℕ)
    (Hs : Fin n → Subgroup X) (α : ↥(Lgrp Lhat) → ℂ) :
    CharCore.IsClassFun (tau Lhat n Hs α) := by
  have heq : tau Lhat n Hs α =
      Induction.indFun (Lgrp Lhat) α +
        ∑ i : Fin n, Induction.indFun (Lgrp (Hs i : Set X))
          (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α) := by
    funext x
    rw [tau_apply]
    simp only [Pi.add_apply, Finset.sum_apply]
  rw [heq]
  exact (Work.Induction.isClassFun_indFun _ _).add
    (CharCore.IsClassFun.sum _ _ (fun i _ => Work.Induction.isClassFun_indFun _ _))

/-- **Feit–Thompson Lemma 9.5** (p. 808).  Let `θ` be a class function of `𝔛` which is constant on
`𝔄_L` for every `L ∈ ⋃_{i=0}^n 𝔏_i`, and let `𝔛₀` be the set of elements of `𝔛` conjugate to an
element of some `𝔄_L` (i.e. `{x | inConjAU Lhat n Hs x}`).  Then

`(1/|𝔛|)·Σ_{x ∈ 𝔛₀} θ(x) = (1/|𝔏|)·Σ_{L ∈ L̂^#} θ(L)`.

Feit–Thompson's proof: define `α ∈ 𝓒₀(L̂)` by `α(L) = θ(L)` for `L ∈ L̂^#` and `α = 0` elsewhere;
Lemma 9.1 gives `α^τ(x) = θ(x)` for `x ∈ 𝔛₀` and `α^τ(x) = 0` off `𝔛₀`, and Lemma 9.3 applied to
`α` gives the identity.  The special case `θ = 1_𝔛` is `|𝔛₀|/|𝔛| = |L̂^#|/|𝔏|`, used in §26, §32
and §33.

NOTE: `L0set Lhat = {l ∈ L̂ | l ≠ 1 ∧ C(l) ⊆ 𝔏}` (see `Submission/Work/Tame/NOTES.md` §2), which is
the reading of Feit–Thompson's `𝔏₀` forced by this very corollary: with the other reading one
would have `1 ∈ 𝔄_1` and `1 ∈ 𝔛₀` whenever `𝔏 = ⊤`, and the special case `θ = 1_𝔛` would fail. -/
theorem ft9_5 {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs)
    {θ : X → ℂ} (hθc : CharCore.IsClassFun θ)
    (hθ : ∀ j : Idx n, ∀ L : ↥(Lgrp Lhat), (L : X) ∈ LofIdx Lhat n Hs j →
      ∀ A ∈ ALofIdx Lhat n Hs j (L : X),
      ∀ A' ∈ ALofIdx Lhat n Hs j (L : X), θ A = θ A') :
    (Fintype.card X : ℂ)⁻¹ * ∑ x : X, (if inConjAU Lhat n Hs x then θ x else 0) =
      (Fintype.card ↥(Lgrp Lhat) : ℂ)⁻¹ * ∑ l : ↥(Lgrp Lhat),
        (if (l : X) ∈ punct Lhat then θ l else 0) := by
  -- Feit–Thompson's `α ∈ 𝓒₀(L̂)`: `α(L) = θ(L)` for `L ∈ L̂^#`, `α = 0` elsewhere.
  let α : ↥(Lgrp Lhat) → ℂ := fun l => if (l : X) ∈ punct Lhat then θ l else 0
  -- `α` vanishes off `L̂` and at `1`.
  have hαvan : ∀ l : ↥(Lgrp Lhat), (l : X) ∉ Lhat → α l = 0 := by
    intro l hl
    simp only [α, if_neg (fun hp => hl (mem_punct.mp hp).1)]
  have hαone : α 1 = 0 := by
    have h1 : ¬ (((1 : ↥(Lgrp Lhat)) : X) ∈ punct Lhat) := by
      intro hp; exact (mem_punct.mp hp).2 rfl
    simp only [α, if_neg h1]
  -- Conjugation by `h ∈ 𝔏 = N(L̂)` preserves `L̂^#`.
  have hconj : ∀ (h : ↥(Lgrp Lhat)) (a : X),
      a ∈ punct Lhat ↔ (h : X) * a * (h : X)⁻¹ ∈ punct Lhat := by
    intro h a
    have hbij : a ∈ Lhat ↔ (h : X) * a * (h : X)⁻¹ ∈ Lhat := mem_Lgrp.mp h.2 a
    have hne : (h : X) * a * (h : X)⁻¹ = 1 ↔ a = 1 := by
      constructor
      · intro h1
        have : a = (h : X)⁻¹ * ((h : X) * a * (h : X)⁻¹) * (h : X) := by group
        rw [this, h1]; group
      · intro h1; rw [h1]; group
    simp only [mem_punct]
    exact ⟨fun ⟨ha, ha1⟩ => ⟨hbij.mp ha, fun h1 => ha1 (hne.mp h1)⟩,
      fun ⟨hc, hc1⟩ => ⟨hbij.mpr hc, fun h1 => hc1 (hne.mpr h1)⟩⟩
  -- `α` is a class function of `𝔏`.
  have hαc : CharCore.IsClassFun α := by
    intro g h
    have hcoe : ((h * g * h⁻¹ : ↥(Lgrp Lhat)) : X) = (h : X) * (g : X) * (h : X)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    simp only [α]
    rw [hcoe]
    by_cases hg : (g : X) ∈ punct Lhat
    · rw [if_pos ((hconj h (g : X)).mp hg), if_pos hg]
      exact hθc (g : X) (h : X)
    · rw [if_neg (fun hc => hg ((hconj h (g : X)).mpr hc)), if_neg hg]
  have hαC0 : α ∈ C0 Lhat := ⟨hαc, hαvan, hαone⟩
  -- Lemma 9.1: `α^τ(x) = θ(x)` on `𝔛₀` and `α^τ(x) = 0` off it.
  have htau : ∀ x : X, tau Lhat n Hs α x = if inConjAU Lhat n Hs x then θ x else 0 := by
    intro x
    by_cases hx : inConjAU Lhat n Hs x
    · rw [if_pos hx]
      obtain ⟨j, L, hL, A, hA, hc⟩ := hx
      have hLpunct : (L : X) ∈ punct Lhat := by
        cases j with
        | none => exact ⟨hL.1, hL.2.1⟩
        | some i => exact ⟨hL.1.1, hL.1.2.1⟩
      have hαL : α L = θ (L : X) := by simp only [α, if_pos hLpunct]
      calc tau Lhat n Hs α x = tau Lhat n Hs α A :=
            ft95_apply_of_isConj (ft95_isClassFun_tau Lhat n Hs α) hc
        _ = α L := ft95_tau_apply_of_mem_AL h hD hαC0 hL hA
        _ = θ (L : X) := hαL
        _ = θ x := by
            rw [← hθ j L hL A hA (L : X) (ft95_self_mem_ALofIdx hL)]
            exact (ft95_apply_of_isConj hθc hc).symm
    · rw [if_neg hx]
      exact ft95_tau_eq_zero_of_not_isConj h hD hαC0 hx
  -- Lemma 9.3 applied to `α`.
  have h3 := cfInner_tau_one h hD hαC0
  rw [Coherence.cfInner_apply, Coherence.cfInner_apply] at h3
  simp only [Pi.one_apply, map_one, mul_one] at h3
  have hsum : (∑ x : X, (if inConjAU Lhat n Hs x then θ x else 0)) =
      ∑ x : X, tau Lhat n Hs α x :=
    Finset.sum_congr rfl (fun x _ => (htau x).symm)
  rw [hsum, h3]

end Work.Tame
