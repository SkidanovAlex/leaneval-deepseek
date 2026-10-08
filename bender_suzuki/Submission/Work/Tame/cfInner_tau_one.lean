import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.cfInner_tau_one` — Feit–Thompson Lemma 9.3 (p. 807)

Source: W. Feit and J. G. Thompson, *Solvability of groups of odd order*, Pacific J. Math. **13**
(1963), 775–1029, Chapter III, p. 807; transcription `Submission/Work/ft1963/tex/ch3a.md`.

> **LEMMA 9.3.** *Suppose that `L̂` is a tamely imbedded subset of `𝔛`.  If `α ∈ 𝓒₀(L̂)` and
> `α^τ` is defined by (9.4) then `(α^τ, 1_𝔛)_𝔛 = (α, 1_𝔏)_𝔏`.*

## The proof, and why it is short

Feit–Thompson prove this by counting conjugacy classes: they choose representatives `L_j` of the
classes `ℭ_j` of `𝔛` meeting `L̂^#`, note that the elements of `𝔛` conjugate to an element of
`𝔄_{L_j}` number `|ℭ_j|·|𝔄_{L_j}| = (|𝔛|/|C(L_j)|)·|𝔄_{L_j}|`, and use Lemma 9.1 and (9.3)
`|C(L)| = |C(L) ∩ 𝔏|·|𝔄_L|` to turn the sum over these classes into
`(1/|𝔏|)Σ_j (|𝔏|/|C(L_j) ∩ 𝔏|)α(L_j) = (α, 1_𝔏)_𝔏`.

There is, however, a *counting-free* proof of the same identity, and that is the one formalised
here.  Both sides of the statement are "inner product with the trivial character", i.e. (up to the
normalisation by `|·|`) the *total sum* of the function.  Now (9.4) exhibits `α^τ` as a sum of
induced functions
`α^τ = Ind_𝔏^𝔛 α + Σ_{i=1}^n Ind_{𝔑_i}^𝔛 (α_{i1} - α_{i2})`,
and Frobenius reciprocity at the trivial character (`Work.Induction.frobenius_reciprocity`)
computes the inner product of any `Ind_H^X ψ` with `1_𝔛` as `(ψ, 1_H)_H`, i.e. as
`(1/|H|)Σ_{h ∈ H} ψ(h)`.  So it suffices that the *degrees* of the correction terms vanish:

`(α_{i1}, 1_𝔑)_𝔑 = (α_{i2}, 1_𝔑)_𝔑`.

This is `cfInner_alphaI1I2_one_index` below, and it is purely an index computation.  By (ii)(c),
`𝔑_i = 𝔎_i(𝔏 ∩ 𝔑_i)` with `𝔎_i ∩ 𝔏 = 1`, so the projection `projEC : 𝔑_i → 𝔏 ∩ 𝔑_i` has all
fibres of cardinality `|𝔎_i|` and `|𝔑_i| = |𝔎_i|·|𝔏 ∩ 𝔑_i|`; hence
`Σ_{N ∈ 𝔑_i} α_{i1}(N) = |𝔎_i|·Σ_{M ∈ 𝔏 ∩ 𝔑_i} α(M)`, while `α_{i2} = Ind_{𝔏∩𝔑_i}^{𝔑_i}(α|)` has
`Σ_{N ∈ 𝔑_i} α_{i2}(N) = |𝔑_i : 𝔏 ∩ 𝔑_i|·Σ_{M ∈ 𝔏∩𝔑_i} α(M)` by Frobenius reciprocity again.
The two are equal by the index relation.

In particular the counting of conjugacy classes, the class-function property of `α`, and the
`τ`-values of Lemma 9.1 are *not* needed for Lemma 9.3: the hypothesis `α ∈ 𝓒₀(L̂)` is used in
the paper only because 9.3 is applied through 9.4/9.5, where `α` is (part of) an element of
`𝓒₀(L̂)`; the identity itself holds for every `α` (and indeed for every function
`↥𝔏 → ℂ`).  The formal statement below keeps the hypothesis, as requested.

The only group-theoretic input is the decomposition `𝔑_i = 𝔎_i ⊔ (𝔏 ⊓ 𝔑_i)` together with
`𝔎_i ⊓ 𝔏 = ⊥` of Definition 9.1(ii)(c); `HasTameData` normalises the degenerate case
`𝔇 = ∅` (see `Submission/Work/Tame/NOTES.md` §1): either `𝔇 ≠ ∅`, so that (ii)(c) is available,
or `n = 0`, in which case the sum in (9.4) is empty.
-/

noncomputable section

set_option linter.unusedVariables false

open Classical

namespace Work.Tame

variable {X : Type*}

/-- **The index computation behind Feit–Thompson Lemma 9.3** (p. 807).

With `𝔏 = N(L̂)`, `𝔑 = N(K)` and `α_{i1} = alphaI1LM Lhat K α` the inflation `N ↦ α(projEC N)`
of `α` along the projection `projEC : 𝔑 → 𝔏 ⊓ 𝔑` of the decomposition `𝔑 = 𝔎(𝔏 ⊓ 𝔑)`, and
`α_{i2} = alphaI2LM Lhat K α = Ind_{𝔏 ⊓ 𝔑}^{𝔑}(α|_{𝔏 ⊓ 𝔑})`: if `𝔑 = 𝔎 ⊔ (𝔏 ⊓ 𝔑)` and
`𝔎 ⊓ 𝔏 = ⊥` then `α_{i1}` and `α_{i2}` have the same inner product with the trivial character
of `𝔑` — equivalently, the same degree `(1/|𝔑|)Σ_{N ∈ 𝔑} α_{ij}(N)`.

Indeed `projEC` is the projection onto the second factor of the direct product
`𝔑 = 𝔎·(𝔏 ⊓ 𝔑)` (all fibres have cardinality `|𝔎|`, and `|𝔑| = |𝔎|·|𝔏 ⊓ 𝔑|`), so
`(1/|𝔑|)Σ_{N ∈ 𝔑} α_{i1}(N) = (|𝔎|/|𝔑|)Σ_{M ∈ 𝔏 ⊓ 𝔑} α(M)`, while Frobenius reciprocity gives
`(α_{i2}, 1)_𝔑 = (α|, 1)_{𝔏 ⊓ 𝔑} = (1/|𝔏 ⊓ 𝔑|)Σ_{M ∈ 𝔏 ⊓ 𝔑} α(M)`. -/
theorem cfInner_alphaI1I2_one_index {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {K : Subgroup X}
    (hsup : Lgrp (K : Set X) = K ⊔ (Lgrp Lhat ⊓ Lgrp (K : Set X)))
    (hinf : K ⊓ Lgrp Lhat = ⊥) (α : ↥(Lgrp Lhat) → ℂ) :
    Coherence.cfInner (alphaI1LM Lhat K α - alphaI2LM Lhat K α)
      (1 : ↥(Lgrp (K : Set X)) → ℂ) = 0 := by
  -- The bijection `𝔎 × (𝔏 ⊓ 𝔑) ≃ 𝔑`, `(H, M) ↦ HM`, given by `𝔑 = 𝔎 ⊔ (𝔏 ⊓ 𝔑)`, `𝔎 ⊓ 𝔏 = ⊥`.
  let e : K × ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)) → ↥(Lgrp (K : Set X)) :=
    fun p => ⟨(p.1 : X) * (p.2 : X),
      (Lgrp (K : Set X)).mul_mem (Subgroup.le_normalizer p.1.2) p.2.2.2⟩
  have hdis : Disjoint K (Lgrp Lhat ⊓ Lgrp (K : Set X)) := by
    rw [Subgroup.disjoint_def]
    intro x hx hx'
    have hx2 : x ∈ K ⊓ Lgrp Lhat := ⟨hx, hx'.1⟩
    simpa [hinf] using hx2
  have he_inj : Function.Injective e := by
    intro p q hpq
    have hval : (p.1 : X) * (p.2 : X) = (q.1 : X) * (q.2 : X) := by
      have := congrArg (fun t : ↥(Lgrp (K : Set X)) => (t : X)) hpq
      simpa [e] using this
    exact Subgroup.mul_injective_of_disjoint hdis hval
  have he_surj : Function.Surjective e := by
    intro N
    refine ⟨(⟨(N : X) * ((projEC Lhat K N : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)⁻¹,
      mul_projEC_inv_mem hsup N⟩, projEC Lhat K N), ?_⟩
    ext
    simp only [e]
    rw [inv_mul_cancel_right]
  let E : K × ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)) ≃ ↥(Lgrp (K : Set X)) :=
    Equiv.ofBijective e ⟨he_inj, he_surj⟩
  -- `projEC` is the second coordinate of the decomposition.
  have hproj : ∀ p : K × ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)), projEC Lhat K (E p) = p.2 := by
    intro p
    have hp : ((E p : ↥(Lgrp (K : Set X))) : X) = (p.1 : X) * (p.2 : X) := rfl
    refine projEC_eq_of hinf ?_
    rw [hp, mul_inv_cancel_right]
    exact p.1.2
  -- Hence `Σ_{N ∈ 𝔑} α_{i1}(N) = |𝔎|·Σ_{M ∈ 𝔏 ⊓ 𝔑} α(M)`.
  have hsum : (∑ N : ↥(Lgrp (K : Set X)),
        α (Subgroup.inclusion inf_le_left (projEC Lhat K N))) =
      (Nat.card K : ℂ) * ∑ M : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)),
        α (Subgroup.inclusion inf_le_left M) := by
    have h1 := Fintype.sum_equiv E
      (fun p : K × ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)) => α (Subgroup.inclusion inf_le_left p.2))
      (fun N : ↥(Lgrp (K : Set X)) => α (Subgroup.inclusion inf_le_left (projEC Lhat K N)))
      (fun p => by rw [hproj p])
    rw [← h1, Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Nat.card_eq_fintype_card]
  -- and `|𝔑| = |𝔎|·|𝔏 ⊓ 𝔑|`.
  have hcard : Nat.card ↥(Lgrp (K : Set X))
      = Nat.card K * Nat.card ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)) := by
    rw [← Nat.card_congr E, Nat.card_prod]
  -- `(α_{i1}, 1_𝔑)_𝔑 = (1/|𝔑|)·Σ_{N ∈ 𝔑} α_{i1}(N)`.
  have hI1 : Coherence.cfInner (alphaI1LM Lhat K α) (1 : ↥(Lgrp (K : Set X)) → ℂ) =
      (Nat.card ↥(Lgrp (K : Set X)) : ℂ)⁻¹ *
        ∑ N : ↥(Lgrp (K : Set X)), α (Subgroup.inclusion inf_le_left (projEC Lhat K N)) := by
    rw [Coherence.cfInner_apply]
    simp only [alphaI1LM_apply, Pi.one_apply, map_one, mul_one]
    rw [Nat.card_eq_fintype_card]
  -- `(α_{i2}, 1_𝔑)_𝔑 = (1/|𝔏 ⊓ 𝔑|)·Σ_{M ∈ 𝔏 ⊓ 𝔑} α(M)`, by Frobenius reciprocity.
  have hI2 : Coherence.cfInner (alphaI2LM Lhat K α) (1 : ↥(Lgrp (K : Set X)) → ℂ) =
      (Nat.card ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)) : ℂ)⁻¹ *
        ∑ M : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)), α (Subgroup.inclusion inf_le_left M) := by
    let H : Subgroup ↥(Lgrp (K : Set X)) :=
      (Lgrp Lhat ⊓ Lgrp (K : Set X)).subgroupOf (Lgrp (K : Set X))
    let φ : ↥H → ℂ := fun m => α (Subgroup.inclusion inf_le_left
      ((Subgroup.subgroupOfEquivOfLe
        (inf_le_right : Lgrp Lhat ⊓ Lgrp (K : Set X) ≤ Lgrp (K : Set X))) m))
    have hI2eq : alphaI2LM Lhat K α = Induction.indFun H φ := by
      funext N
      rw [alphaI2LM_apply]
    have hfr : Coherence.cfInner (Induction.indFun H φ) (1 : ↥(Lgrp (K : Set X)) → ℂ)
        = Coherence.cfInner φ (1 : ↥H → ℂ) :=
      Induction.frobenius_reciprocity H φ (1 : ↥(Lgrp (K : Set X)) → ℂ)
        (Work.Coherence.isClassFun_const 1)
    rw [hI2eq, hfr, Coherence.cfInner_apply]
    simp only [Pi.one_apply, map_one, mul_one]
    have hsum' := Fintype.sum_equiv
      (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : Lgrp Lhat ⊓ Lgrp (K : Set X) ≤ Lgrp (K : Set X))).toEquiv
      (fun m : ↥H => φ m)
      (fun M : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)) => α (Subgroup.inclusion inf_le_left M))
      (fun m => rfl)
    rw [← Nat.card_eq_fintype_card, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : Lgrp Lhat ⊓ Lgrp (K : Set X) ≤ Lgrp (K : Set X))).toEquiv,
      hsum']
  rw [Coherence.cfInner_sub_left, sub_eq_zero, hI1, hI2, hsum, hcard]
  push_cast
  rw [mul_inv_rev]
  have hK0 : (Nat.card K : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- **Feit–Thompson Lemma 9.3** (p. 807).  If `L̂` is tamely imbedded in `X`, `α ∈ 𝓒₀(L̂)` and
`α^τ` is defined by (9.4), then `(α^τ, 1_𝔛)_𝔛 = (α, 1_𝔏)_𝔏`.

Feit–Thompson's proof: let `ℭ_1, ℭ_2, …` be the conjugacy classes of `𝔛` meeting `L̂^#` and let
`L_j ∈ ℭ_j ∩ L̂^#` be chosen in `⋃_{i=0}^n 𝔏_i`; the number of elements of `𝔛` conjugate to an
element of `𝔄_{L_j}` is `|ℭ_j|·|𝔄_{L_j}| = (|𝔛|/|C(L_j)|)·|𝔄_{L_j}|`, and (9.3)
`|C(L)| = |C(L) ∩ 𝔏|·|𝔄_L|` turns the sum over these classes into
`(1/|𝔏|)Σ_j (|𝔏|/|C(L_j) ∩ 𝔏|)α(L_j) = (α, 1_𝔏)_𝔏`.  (The `HasTameData` hypothesis is the
normalisation of Definition 9.1; see NOTES.md §1.)

Formally we expand (9.4) and use Frobenius reciprocity at the trivial character, which reduces
the identity to the vanishing of the degrees of the correction terms `α_{i1} - α_{i2}`
(`cfInner_alphaI1I2_one_index`); see the module docstring. -/
theorem cfInner_tau_one {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) :
    Coherence.cfInner (tau Lhat n Hs α) (1 : X → ℂ) =
      Coherence.cfInner α (1 : ↥(Lgrp Lhat) → ℂ) := by
  -- Frobenius reciprocity at the trivial character: `(Ind_H^X ψ, 1_𝔛)_𝔛 = (ψ, 1_H)_H`.
  have ind_one : ∀ (H : Subgroup X) (ψ : ↥H → ℂ),
      Coherence.cfInner (Induction.indFun H ψ) (1 : X → ℂ) =
        Coherence.cfInner ψ (1 : ↥H → ℂ) :=
    fun H ψ => Induction.frobenius_reciprocity H ψ (1 : X → ℂ)
      (Work.Coherence.isClassFun_const 1)
  -- (9.4) as an identity of functions.
  have htau : tau Lhat n Hs α = Induction.indFun (Lgrp Lhat) α +
      ∑ i : Fin n, Induction.indFun (Lgrp (Hs i : Set X))
        (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α) := by
    funext x
    rw [tau_apply]
    simp only [Pi.add_apply, Finset.sum_apply]
  -- The correction terms have degree `0`.
  have hkey : ∀ i : Fin n,
      Coherence.cfInner (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α)
        (1 : ↥(Lgrp (Hs i : Set X)) → ℂ) = 0 := by
    intro i
    rcases hD with hD' | hn
    · exact cfInner_alphaI1I2_one_index (h.supp_prod hD' i) (h.supp_inf hD' i) α
    · exact absurd i.isLt (by omega)
  have hsum : Coherence.cfInner (∑ i : Fin n, Induction.indFun (Lgrp (Hs i : Set X))
        (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α)) (1 : X → ℂ) = 0 := by
    rw [Coherence.cfInner_sum_left]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [ind_one (Lgrp (Hs i : Set X))]
    exact hkey i
  rw [htau, Coherence.cfInner_add_left, hsum, add_zero, ind_one]

end Work.Tame
