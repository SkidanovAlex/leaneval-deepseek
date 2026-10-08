import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.Chapter10
import Submission.Work.Tame.isVChar_tau
import Submission.Work.Tame.tau_apply_one
import Submission.Work.Tame.cfInner_tau_tau

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.ft10_1_lemma` — Feit–Thompson Lemma 10.1 (p. 809)

Feit–Thompson, *Solvability of groups of odd order*, Pacific J. Math. **13** (1963), p. 809,
transcription `Submission/Work/ft1963/tex/ch3a.md`:

> **LEMMA 10.1.** *Suppose that `L̂` is a tamely imbedded subset of `𝔛`.  Let `𝓢 = {λ_i | 1 ≤ i ≤ n}`
> with `n ≥ 2`.  Assume that for `1 ≤ i ≤ n`, `λ_i` is an irreducible character of `𝔏`.
> Furthermore `λ_i(L) = λ_1(L)` for `L ∈ 𝔏 − L̂^#`.  Then `𝓢` is coherent.*

The proof, following the paper (p. 809–810), is assembled here from the ingredients of Chapter III:

* the lattice computation of `NOTES.md` §4 (`zSpan0_apply_eq_zero_of_common`,
  `isVChar_of_mem_zSpan_irr`): every element of `ℤ[𝓢]⁰` is a generalized character of `𝔏`
  vanishing off `L̂^#`, so that `𝓘₀(𝓢) ⊆ 𝓘₀(L̂)` — Feit–Thompson's Definition 10.1(iii);
* `ℤ[𝓢]⁰ ≠ 0` — Definition 10.1(i) — because a difference of two distinct members of `𝓢` lies in
  `ℤ[𝓢]⁰` and is non-zero;
* Feit–Thompson's Lemma 9.4 (`cfInner_tau_tau`): the Dade map `τ` of (9.4) is an isometry on
  `ℤ[𝓢]⁰ ⊆ 𝓘₀(L̂)`;
* `isVChar_tau` (after (9.4)) and `tau_apply_one`: `τ (χ − x₀)` is a virtual character of degree
  `0`;
* the norm-two lift `Coherence.coherent_of_norm_two_lift`, which produces the coherent extension of
  `τ` from `ℤ[𝓢]⁰` to `ℤ[𝓢]` (via `Coherence.vchar_norm_two_deg_zero` and
  `Coherence.exists_common_of_pairwise_inner_one_nonempty`).

Note that Definition 10.1(iii) — as formalised in `FTCoherent` — is the condition
`𝓘₀(𝓢) ⊆ 𝓘₀(L̂)` on the *degree-zero integral combinations* of `𝓢`, not on the members of `𝓢`
individually (see `NOTES.md` §4); the hypotheses of the lemma supply it, as the first two items
above show.
-/

namespace Work.Tame

open Classical

/-! ## Two elementary lemmas on the lattice `ℤ[S]⁰` -/

section Lattice

variable {G : Type*} [Group G] [Fintype G]

/-- **Degree-zero combinations of a common-degree set vanish where the set does.**

If `α ∈ ℤ[S]⁰`, all elements of `S` have the same non-zero degree `d`, and all elements of `S`
agree pairwise at a point `l`, then `α l = 0`.  (Writing `α = ∑ c_χ • χ`, the degree-zero
condition `0 = α 1 = (∑ c_χ)·d` forces `∑ c_χ = 0`, whence `α l = (∑ c_χ)·χ₀ l = 0`.) -/
theorem zSpan0_apply_eq_zero_of_common {S : Finset (G → ℂ)} {α : G → ℂ}
    (hα : α ∈ Coherence.ZSpan0 S) {d : ℂ} (hd : d ≠ 0)
    (hdeg : ∀ x ∈ S, x 1 = d) {l : G} (hl : ∀ x ∈ S, ∀ y ∈ S, x l = y l) :
    α l = 0 := by
  by_cases hne : S.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨c, hc⟩ := Coherence.mem_zSpan.mp (Coherence.zSpan0_le_zSpan S hα)
    -- the coefficient sum is zero
    have hsum1 : (∑ x : S, (c x : ℂ) * ((x : G → ℂ) 1)) = (∑ x : S, (c x : ℂ)) * d := by
      have hstep : ∀ x : S, (c x : ℂ) * ((x : G → ℂ) 1) = (c x : ℂ) * d :=
        fun x => by rw [hdeg (x : G → ℂ) x.2]
      rw [Finset.sum_congr rfl (fun x _ => hstep x), ← Finset.sum_mul]
    have h1 : α 1 = (∑ x : S, (c x : ℂ)) * d := by
      rw [hc, Coherence.sum_coeff_apply]
      exact hsum1
    have h0 : α 1 = 0 := hα.2
    have hsum0 : ∑ x : S, (c x : ℂ) = 0 := by
      rw [h0] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right hd
    -- and hence the value at `l`
    have hsum2 : (∑ x : S, (c x : ℂ) * ((x : G → ℂ) l)) =
        (∑ x : S, (c x : ℂ)) * ((x₀ : G → ℂ) l) := by
      have hstep : ∀ x : S, (c x : ℂ) * ((x : G → ℂ) l) =
          (c x : ℂ) * ((x₀ : G → ℂ) l) :=
        fun x => by rw [hl (x : G → ℂ) x.2 x₀ hx₀]
      rw [Finset.sum_congr rfl (fun x _ => hstep x), ← Finset.sum_mul]
    have h2 : α l = (∑ x : S, (c x : ℂ)) * ((x₀ : G → ℂ) l) := by
      rw [hc, Coherence.sum_coeff_apply]
      exact hsum2
    rw [h2, hsum0, zero_mul]
  · -- `S = ∅`: then `ℤ[S] = 0`.
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hbot : α = 0 := by
      have hz : α ∈ Coherence.ZSpan (∅ : Finset (G → ℂ)) := by
        rw [← hne]
        exact Coherence.zSpan0_le_zSpan S hα
      simpa using hz
    rw [hbot]
    rfl

/-- An integral combination of irreducible characters is a virtual character. -/
theorem isVChar_of_mem_zSpan_irr {S : Finset (G → ℂ)} {α : G → ℂ}
    (hα : α ∈ Coherence.ZSpan S) (hS : ∀ χ ∈ S, χ ∈ Coherence.Irr G) :
    Coherence.IsVChar α := by
  obtain ⟨c, hc⟩ := Coherence.mem_zSpan.mp hα
  exact Coherence.isVChar_iff_coeff.mpr ⟨S, (fun x hx => hS x hx), c, hc⟩

end Lattice

/-- **Feit–Thompson Lemma 10.1** (p. 809).  Let `L̂` be tamely imbedded in `X` in the
non-degenerate sense `HasTameData` (see `Submission/Work/Tame/NOTES.md` §1), and let `𝓢` be a set
of at least two irreducible characters of `𝔏 = N(L̂)` which all take the same value outside `L̂^#`
(`∀ l ∉ punct Lhat, χ l = ψ l`, which in particular makes them all of the same degree, since
`1 ∉ L̂^#`).  Then `𝓢` is coherent for the Dade map `τ` of (9.4).

The proof reduces to `Work.Coherence.coherent_of_norm_two_lift`: the differences `χ - ψ` lie in
`𝓘₀(L̂)` (all members agree off `L̂^#` and have the same degree, so any degree-zero integral
combination vanishes off `L̂^#` and at `1`), `cfInner_tau_tau` (Lemma 9.4) makes `τ` an isometry on
`ℤ[𝓢]⁰`, `isVChar_tau` makes `τ (χ - ψ)` a virtual character and `tau_apply_one` makes it of
degree `0`.  `Coherence.vchar_norm_two_deg_zero` then exhibits `τ (χ - ψ)` as a difference of two
irreducibles and `Coherence.exists_common_of_pairwise_inner_one_nonempty` supplies the common
member. -/
theorem ft10_1_lemma {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs)
    {S : Finset (↥(Lgrp Lhat) → ℂ)} (hS : ∀ χ ∈ S, χ ∈ CharCore.Irr ↥(Lgrp Lhat))
    (h2 : 2 ≤ S.card)
    (heq : ∀ χ ∈ S, ∀ ψ ∈ S, ∀ l : ↥(Lgrp Lhat), (l : X) ∉ punct Lhat → χ l = ψ l) :
    FTCoherent Lhat n Hs S := by
  classical
  -- `1 ∉ L̂^#`
  have hone : ((1 : ↥(Lgrp Lhat)) : X) ∉ punct Lhat := by
    simp [punct]
  -- all members of `𝓢` have a common degree and a common value off `L̂^#`
  have hsame1 : ∀ χ ∈ S, ∀ ψ ∈ S, χ 1 = ψ 1 := fun χ hχ ψ hψ => heq χ hχ ψ hψ 1 hone
  -- `𝓢` is non-empty, and we fix a member `x₀`
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x₀, hx₀S⟩ := hSne
  -- the common degree is non-zero
  have hdx : x₀ 1 ≠ 0 := by
    obtain ⟨m, hm, hval⟩ :=
      Coherence.irr_degree_pos ((CharCore.mem_Irr_iff_coherence).mp (hS x₀ hx₀S))
    rw [hval]
    exact Nat.cast_ne_zero.mpr hm.ne'
  -- the hypotheses `𝔎_i ⊓ 𝔏 = ⊥` of Lemma 9.1, from `IsTamelyImbedded` and `HasTameData`
  have hinf : ∀ i : Fin n, Hs i ⊓ Lgrp Lhat = ⊥ := by
    rcases hD with hne | hn0
    · exact fun i => h.supp_inf hne i
    · subst hn0
      intro i
      exact Fin.elim0 i
  -- `x - x₀ ∈ ℤ[𝓢]⁰`
  have hsub_mem : ∀ x ∈ S, x - x₀ ∈ Coherence.ZSpan0 S := by
    intro x hx
    rw [Coherence.mem_zSpan0]
    refine ⟨AddSubgroup.sub_mem _ (Coherence.self_mem_zSpan hx)
      (Coherence.self_mem_zSpan hx₀S), ?_⟩
    rw [Pi.sub_apply, hsame1 x hx x₀ hx₀S, sub_self]
  -- **Definition 10.1(iii)**: `𝓘₀(𝓢) ⊆ 𝓘₀(L̂)`
  have hI0 : ∀ α ∈ Coherence.ZSpan0 S, α ∈ I0 Lhat := by
    intro α hα
    rw [mem_I0]
    refine ⟨?_, ?_, hα.2⟩
    · exact (CharCore.IsVChar_iff_coherence α).mpr
        (isVChar_of_mem_zSpan_irr (Coherence.zSpan0_le_zSpan S hα)
          (fun χ hχ => (CharCore.mem_Irr_iff_coherence).mp (hS χ hχ)))
    · intro l hl
      exact zSpan0_apply_eq_zero_of_common hα hdx (fun x hx => hsame1 x hx x₀ hx₀S)
        (fun x hx y hy => heq x hx y hy l (fun hp => hl (Set.sdiff_subset hp)))
  -- **Definition 10.1(i)**: `ℤ[𝓢]⁰ ≠ 0`
  have hZne : Coherence.ZSpan0 S ≠ ⊥ := by
    intro hbot
    obtain ⟨χ, hχS, ψ, hψS, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have hmem : χ - ψ ∈ Coherence.ZSpan0 S := by
      rw [Coherence.mem_zSpan0]
      refine ⟨AddSubgroup.sub_mem _ (Coherence.self_mem_zSpan hχS)
        (Coherence.self_mem_zSpan hψS), ?_⟩
      rw [Pi.sub_apply, hsame1 χ hχS ψ hψS, sub_self]
    rw [hbot] at hmem
    have hzero : χ - ψ = 0 := by simpa using hmem
    exact hne (sub_eq_zero.mp hzero)
  refine ⟨hZne, ?_, ?_⟩
  · intro α hα l hl
    exact (hI0 α hα).2.1 l hl
  · -- **Definition 10.1(ii)**: apply the norm-two lift, `Coherence.coherent_of_norm_two_lift`.
    refine Coherence.coherent_of_norm_two_lift (H := ↥(Lgrp Lhat)) (G := X)
      ?_ hx₀S ?_ hdx ?_ ?_ ?_ h2
    · exact Coherence.irr_orthonormal_finset
        (fun x hx => (CharCore.mem_Irr_iff_coherence).mp (hS x hx))
    · intro x hx
      exact hsame1 x hx x₀ hx₀S
    · -- `τ` is an isometry on `ℤ[𝓢]⁰` (Lemma 9.4)
      exact ⟨fun α hα β hβ => cfInner_tau_tau h hD (hI0 α hα) (hI0 β hβ)⟩
    · -- `τ (χ - ψ)` is a virtual character (after (9.4))
      intro x hx
      exact (CharCore.IsVChar_iff_coherence _).mp
        (isVChar_tau h hD (hI0 (x - x₀) (hsub_mem x hx)))
    · -- `τ (χ - ψ)` has degree zero
      intro x hx
      exact tau_apply_one hinf (hsub_mem x hx).2

end Work.Tame
