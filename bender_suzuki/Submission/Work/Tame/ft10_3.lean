import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.Chapter10
import Submission.Work.Tame.Hyp
import Submission.Work.Tame.irr_vanishes_off_hatN
import Submission.Work.Tame.mem_hatNp_iff
import Submission.Work.Tame.one_mem_hatN
import Submission.Work.Tame.conj_mem_hatNp_and_notMem
import Submission.Work.Tame.centralizer_le_normalizer_of_mem_hatNp
import Submission.Work.Tame.Dset_eq_empty_iff
import Submission.Work.Tame.ft10_1_lemma
import Submission.Work.Tame.tau_apply_one
import Submission.Work.Tame.isVChar_tau
import Submission.Work.Tame.indFun_hatNp_apply
import Submission.Work.Tame.ft10_3_key_v2
import Submission.Work.Tame.ft10_2
import Submission.Work.Tame.vchar_const_of_orth_restriction

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

open Classical
open scoped Pointwise

variable {X : Type*} [Group X] [Fintype X]

/-- Feit--Thompson Definition 9.1(ii)(e): for a non-trivial supporting subgroup `𝔎 = Hs i` of a
tamely imbedded set, the set `Ñ_i = hatN (Hs i)` is itself a *tamely imbedded* subset of `X`
with no supporting subgroups: it is the T. I. set of the degenerate case `𝔫 = 0`. -/
theorem isTamelyImbedded_hatN {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hD : (Dset Lhat).Nonempty) (i : Fin n) :
    IsTamelyImbedded (hatN (Hs i)) 0 (fun j : Fin 0 => Hs i) := by
  classical
  have hK : Hs i ≠ ⊥ := h.supp_ne_bot hD i
  have hnorm : Lgrp (hatN (Hs i)) = Lgrp (Hs i : Set X) := h.supp_hatN_norm hD i
  -- `𝔇(Ñ_i) = ∅`: every non-identity element of `Ñ_i` has its centralizer inside `𝔑_i = N(Ñ_i)`.
  have hDempty : Dset (hatN (Hs i)) = ∅ := by
    rw [Dset_eq_empty_iff]
    intro l hl hl1
    have hlNp : l ∈ hatNp (Hs i) := mem_punct.mpr ⟨hl, hl1⟩
    have hc := centralizer_le_normalizer_of_mem_hatNp (h.supp_ti hD i) (h.supp_hatN_norm hD i) hlNp
    rwa [hnorm]
  have hDne : ¬ (Dset (hatN (Hs i))).Nonempty := by rw [hDempty]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact one_mem_hatN hK
  · -- `Ñ_i ⊆ N(Ñ_i) = N(𝔎_i)`
    intro x hx
    rw [hnorm]
    exact (mem_hatNCore_iff_local.mp hx.1).1
  · -- conjugacy condition: the T. I. property of `Ñ_i^#`
    intro a ha b hb hconj
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    by_cases ha1 : a = 1
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [ha1] at hg ⊢
      rw [← hg]; simp
    · have haNp : a ∈ hatNp (Hs i) := mem_punct.mpr ⟨ha, ha1⟩
      have hb1 : b ≠ 1 := by
        intro hb1
        apply ha1
        calc a = g⁻¹ * b * g := by rw [← hg]; group
          _ = 1 := by rw [hb1]; simp
      have hbNp : b ∈ hatNp (Hs i) := mem_punct.mpr ⟨hb, hb1⟩
      have hgL : g ∈ Lgrp (hatN (Hs i)) := by
        rw [hnorm]
        by_contra hgnot
        have h2 := (conj_mem_hatNp_and_notMem h hD i).2 g hgnot b hbNp
        apply h2
        have hgz : g⁻¹ * b * g = a := by rw [← hg]; group
        rwa [hgz]
      exact ⟨g, hgL, hg.symm⟩
  · intro hne; exact False.elim (hDne hne)
  · intro hne; exact False.elim (hDne hne)
  · intro hne; exact False.elim (hDne hne)
  · intro hne; exact False.elim (hDne hne)
  · intro hne; exact False.elim (hDne hne)
  · intro hne; exact False.elim (hDne hne)
  · intro hne; exact False.elim (hDne hne)
  · intro hne; exact False.elim (hDne hne)
  · intro hne; exact False.elim (hDne hne)
  · intro hne; exact False.elim (hDne hne)
  · intro l₀ hmem
    rw [hDempty] at hmem
    exact absurd hmem (by simp)

/-- The degree `f 1` of a virtual character `f` of a finite group is an integer. -/
theorem isVChar_apply_one_eq_int {G : Type*} [Group G] [Fintype G] {f : G → ℂ}
    (hf : CharCore.IsVChar f) : ∃ z : ℤ, f 1 = (z : ℂ) := by
  classical
  obtain ⟨c, hc⟩ := CharCore.isVChar_iff_exists_int_coeffs.mp hf
  have hdeg : ∀ χ : {χ : G → ℂ // χ ∈ CharCore.Irr G},
      ∃ n : ℕ, 0 < n ∧ (χ : G → ℂ) 1 = (n : ℂ) :=
    fun χ => Coherence.irr_degree_pos ((CharCore.mem_Irr_iff_coherence).mp χ.2)
  choose n _hn hn1 using hdeg
  refine ⟨∑ χ, c χ * (n χ : ℤ), ?_⟩
  rw [hc, Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun χ _ => by rw [Pi.smul_apply, smul_eq_mul, hn1 χ])]
  push_cast
  rfl

/-- **Feit--Thompson (10.16)**: the restriction of `τ'λ` to `𝔑ᵢ` is orthogonal to `θ₁ - θ₂`
for any two irreducible characters `θ₁, θ₂` of `𝔑ᵢ` with the same restriction `α` to `𝔎ᵢ` and
`(α, 1_{𝔎ᵢ}) = 0`.

PROOF SKETCH (the paper's argument, with the gap repaired).  Suppose
`X := ⟪τ'λ|_𝔑, θ₁-θ₂⟫ ≠ 0`.  For a member `μ ∈ 𝓢` and an irreducible `μ' ∈ 𝓢` put
`α_{μ'} := μ'(1)·μ - μ(1)·μ' ∈ ℤ[𝓢]⁰` (integer coefficients: degrees of virtual characters are
integers).  By `tau_res_quotient` (Feit--Thompson Lemma 9.2, second part)
`⟪τ'(α_{μ'})|_𝔑, θ₁-θ₂⟫ = 0`, i.e. `μ'(1)·X = μ(1)·⟪τ'μ'|_𝔑, θ₁-θ₂⟫   (*)`.

Apply this to the two distinct irreducible members `λ₁, λ₂ ∈ 𝓢` given by `h2`.  Since `X ≠ 0`
and `λ_j(1) ≠ 0`, the numbers `Y_j := ⟪τ'λ_j|_𝔑, θ₁-θ₂⟫` are non-zero, so `τ'λ_j = ±Θ_{i(j)}`,
where `Θ₁, Θ₂` are the images of `θ₁, θ₂` under the isometry extension of `{θ₁, θ₂}`
(Lemma 10.1, via `Coherence.coherent_of_norm_two_lift`, whose isometry hypothesis is the T. I.
isometry `‖(θ₁-θ₂)^*‖² = 2`, proved with `indFun_hatNp_apply` from `‖θ₁-θ₂‖² = 2`); then
`Θ₁ - Θ₂ = (θ₁-θ₂)^*`.  Each `Θ_j = ±` an irreducible character and `⟨Θ_a, Θ_b⟩ = δ_{ab}`.  Since
`Y_j` is thus `±1` and `(*)` reads `λ_j(1)|X| = |μ(1)|`, one gets `λ₁(1) = λ₂(1) =: d` and
`Y₁ = Y₂`.

Necessarily `i(1) ≠ i(2)` (otherwise `λ₁^τ = ±λ₂^τ`, contradicting `⟨λ₁, λ₂⟩ = 0`), so say
`τ'λ₁ = δΘ₁`, `τ'λ₂ = -δΘ₂`; then `Y₁ = δ = Y₂`.  Hence `W := τ'(λ₁ - λ₂) = δ(Θ₁ + Θ₂)`.  But
`λ₁(1) = λ₂(1)`, so `λ₁ - λ₂ ∈ ℤ[𝓢]⁰` and `W = τ'(λ₁-λ₂) = τ(λ₁-λ₂)`, which has degree `0`
(`tau_apply_one`); hence `Θ₁(1) + Θ₂(1) = 0`.  On the other hand
`(θ₁-θ₂)^*(1) = [X:𝔑](θ₁(1) - θ₂(1)) = 0` because `θ₁|_𝔎 = θ₂|_𝔎 = α` forces `θ₁(1) = θ₂(1)`.
Therefore `0 = (Θ₁-Θ₂)(1) = Θ₁(1) - Θ₂(1) = 2Θ₁(1) ≠ 0`, a contradiction.

NOTE (the repair).  The paper asserts "the sign is independent of `j`" in order to derive a
contradiction from `λ₁(1)λ₂ - λ₂(1)λ₁ ∈ 𝓘₀(𝓢)`.  That assertion is *false* as stated: `(*)` in fact
forces the signs to be opposite and the degrees equal.  The contradiction is instead obtained from
the *degree* of `τ(λ₁-λ₂)`, which uses only that `θ₁` and `θ₂` have the same degree (they have the
same restriction to `𝔎ᵢ`), so no extra hypothesis is needed. -/
theorem ft10_3_key {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X} {i : Fin n}
    (h : Hyp10_2 Lhat n Hs i)
    {S : Finset (↥(Lgrp Lhat) → ℂ)} (hcoh : FTCoherent Lhat n Hs S)
    (hv : ∀ χ ∈ S, CharCore.IsVChar χ)
    (horth : ∀ χ ∈ S, ∀ ψ ∈ S, χ ≠ ψ → Coherence.cfInner χ ψ = 0)
    (h2 : ∃ χ ∈ S, ∃ ψ ∈ S, χ ≠ ψ ∧ χ ∈ CharCore.Irr ↥(Lgrp Lhat) ∧
      ψ ∈ CharCore.Irr ↥(Lgrp Lhat))
    {τ' : (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (X → ℂ)} (hτ' : IsExtension Lhat n Hs S τ')
    {lam : ↥(Lgrp Lhat) → ℂ} (hlam : lam ∈ S)
    {θ₁ θ₂ : ↥(Lgrp (Hs i : Set X)) → ℂ}
    (hθ₁ : θ₁ ∈ CharCore.Irr ↥(Lgrp (Hs i : Set X)))
    (hθ₂ : θ₂ ∈ CharCore.Irr ↥(Lgrp (Hs i : Set X)))
    {α : ↥(Hs i) → ℂ}
    (hα1 : ∀ hh : ↥(Hs i), θ₁ ⟨(hh : X), (Hs i).le_normalizer hh.2⟩ = α hh)
    (hα2 : ∀ hh : ↥(Hs i), θ₂ ⟨(hh : X), (Hs i).le_normalizer hh.2⟩ = α hh)
    (hα0 : Coherence.cfInner α (1 : ↥(Hs i) → ℂ) = 0) :
    Coherence.cfInner (fun N : ↥(Lgrp (Hs i : Set X)) => τ' lam (N : X)) (θ₁ - θ₂) = 0 :=
  ft10_3_key_v2 h hcoh hv horth h2 hτ' hlam hθ₁ hθ₂ hα1 hα2 hα0

/-- **Feit–Thompson Lemma 10.3** (p. 814).  Assume Hypothesis 10.2 for `𝔎_i`.  Let `𝓢` be a coherent
subset of `𝓘(L̂)` — formalised as: `FTCoherent Lhat n Hs S` together with `IsVChar χ` for every
`χ ∈ S` — consisting of pairwise orthogonal characters of `𝔏` and containing at least two
irreducible characters.  Then for *any* extension `τ'` of `τ` to `𝓢` and any member `lam` of `𝓢`
the image `lam^τ` is constant on the cosets of `𝔎_i` which lie in `𝔑_i − 𝔎_i`:
`τ' lam (N·H) = τ' lam N` for `N ∈ 𝔑_i`, `N ∉ 𝔎_i`, `H ∈ 𝔎_i`.

Feit–Thompson's proof: for distinct irreducible `θ₁, θ₂` of `𝔑_i` with `𝔎_i ⊄ ker θ_j` and
`θ₁|_{𝔎_i} = θ₂|_{𝔎_i}`, Lemma 10.1 extends the isometry `(θ₁ - θ₂)^*` of the T. I. set `Ñ_i` to
an isometry on `𝓘({θ₁,θ₂})` with images `Θ₁, Θ₂`; if `(lam^τ|_{𝔑_i}, θ₁ - θ₂) ≠ 0` then
`lam_j^τ = ±Θ_j` for two distinct irreducible `lam_1, lam_2 ∈ 𝓢`, and applying the same argument to
`lam_1(1)lam_2 - lam_2(1)lam_1 ∈ 𝓘₀(𝓢)` (Lemma 9.2) gives a contradiction.  The conclusion follows
from Lemma 10.2, whose statement is `∀ N ∈ 𝔑_i, N ∉ 𝔎_i, ∀ H ∈ 𝔎_i, Θ (N·H) = Θ N`. -/
theorem ft10_3 {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} {i : Fin n} (h : Hyp10_2 Lhat n Hs i)
    {S : Finset (↥(Lgrp Lhat) → ℂ)} (hcoh : FTCoherent Lhat n Hs S)
    (hv : ∀ χ ∈ S, CharCore.IsVChar χ)
    (horth : ∀ χ ∈ S, ∀ ψ ∈ S, χ ≠ ψ → Coherence.cfInner χ ψ = 0)
    (h2 : ∃ χ ∈ S, ∃ ψ ∈ S, χ ≠ ψ ∧ χ ∈ CharCore.Irr ↥(Lgrp Lhat) ∧
      ψ ∈ CharCore.Irr ↥(Lgrp Lhat))
    {τ' : (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (X → ℂ)} (hτ' : IsExtension Lhat n Hs S τ') :
    ∀ lam ∈ S, ∀ N : X, N ∈ Lgrp (Hs i : Set X) → N ∉ (Hs i : Set X) →
      ∀ H : X, H ∈ Hs i → τ' lam (N * H) = τ' lam N := by
  intro lam hlam N hN hNK H hH
  refine vchar_const_of_orth_restriction h (hτ'.2.2 lam hlam) ?_ N hN hNK H hH
  intro α hα0 θ₁ hθ₁ θ₂ hθ₂ hα1 hα2
  exact ft10_3_key h hcoh hv horth h2 hτ' hlam hθ₁ hθ₂ hα1 hα2 hα0

end Work.Tame
