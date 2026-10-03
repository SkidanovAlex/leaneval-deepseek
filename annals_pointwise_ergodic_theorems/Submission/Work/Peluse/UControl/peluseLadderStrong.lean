import Mathlib
import Submission.Work.Peluse.UControl.peluseLadder

/-!
# Peluse's Lemma 5.7, *correct* statement — and the hypothesis Theorem 3.5 has to carry

Two statement-level findings of the session are recorded here.

## 1. The existentials of Lemma 5.7 must be outside the per-instance quantifiers

The first draft of the statement (`Submission/Work/Peluse/UControl/peluseLadder.lean`) placed
`∃ t' c` *inside* the universal block over `A, M₁, M₂, N, γ, γ', f`.  With that placement the
statement is *vacuous*: taking `K = C₀ = 1` the non-degeneracy hypothesis reads `(γγ')^{-1} ≤ M₁M₂`,
which forces `γ'M₁M₂ ≥ 1`, hence every direction set of the conclusion is nonempty, hence (by the
peel identity, `Work.Peluse.UControl.boxNormPow_pos'`) every box norm in the conclusion is
*positive*, and `t' = 1`, `c = min_{s₀}(RHS s₀)/(2γ)` finishes.  The proof of the statement on disk
(`ladderStep.lean`) is exactly this and does not use the concatenation hypothesis at all; see
`ladderStep_WARNING.md`.  In the paper `t'` and the implied constant depend only on the datum
`(k, kω, p, D)` (the paper's `≪_{C,t,(k_ω)} 1`), which is what `PeluseLadderStrong` below records.

## 2. Theorem 3.5 must be stated with general integer shifts

In the source's proof of Lemma 5.7, Theorem 3.5 is applied with the peeled directions
`p_{i₀}(a)·a'_{s₀} + b_{a,ω}` (where `b_{a,ω}` is the *integer* `(p_i(a)a_{i,r})_{i,r}·ω −
p_{i₀}(a)a_{i₀,r₀}`), i.e. with coefficient `c = p_{i₀}(a)` and *absolute* shifts `d_{ω} = b_{a,ω}`.
`Work.Peluse.PeluseConcatenation` only allows the directions `arithIcc (c * (a + b_i)) M₁`, i.e. it
forces the shift to be a *multiple* of the coefficient `c`; that is strictly too little (the paper's
own `b_i` are integral, but the proof needs `c·a + d_i`).  `PeluseConcatRel` below is the
corresponding repair, which is the form Lemma 5.7's proof actually consumes.  Whoever owns
`Nodes.lean` may prefer to strengthen `PeluseConcatenation` itself; the repair is a strict
generalisation of the paper's statement (shifts `d_i := c·b_i`).

## 3. The witnesses of Theorem 3.5 must be uniform in the coefficient

A second, independent defect (found by the delegated prover of `ladderStrong`): in
`PeluseConcatenation` the witnesses `s', C', A, K` are quantified *after* `∀ c`, whereas in the
source `s' ≪_s 1` depends only on the shift constant and the level.  Since the coefficient used in
Lemma 5.7's proof is `c = p_{i₀}(a)`, which varies with `a ∈ A` and is unbounded, per-coefficient
witnesses cannot be combined into the datum-fixed ones that `PeluseLadderStrong` demands.  The
statement `PeluseConcatFixed` below carries *both* repairs, and it is from it that
`ladderStrong` is now delegated.

## 4. Notes for the prover of `ladderStrong`

* The free shift constant `C` of `PeluseConcatFixed` has to be instantiated with the bound for the
  peeled shifts (`b_{a,ω}`), which depends on the datum `(k, kω, p, D)` only — the integer division
  `C·N/M₁` in `PeluseConcatFixed` matches the source's real bound for integral shifts.
* The datum `kω ≡ 0` gives hypothesis level `0`, so `PeluseConcatFixed` (whose level is `≥ 1`) cannot
  be invoked there; that case needs a separate argument (monotonicity of the box norm in the level,
  `Work.Peluse.Concat.boxNormPow_succ_ge_general`).
* The task is the whole of the source's §5 proof of Lemma 5.7 (pigeonhole over the parameter box,
  the peel expansion (5.7), the reindexing, and the assembly), not a short derivation.

-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- **Peluse's Theorem 3.5 with general integer shifts**: the same statement as
`Work.Peluse.PeluseConcatenation`, except that the family averaged over is
`arithIcc (c * (a : ℤ) + d i) M₁` for *arbitrary* `d : Fin s → ℤ` (rather than
`arithIcc (c * ((a : ℤ) + b i)) M₁`, which forces the shift to be a multiple of `c`).  Every
instance of the original statement is an instance of this one (`d i := c * b i`); this is the form
in which the proof of Lemma 5.7 applies Theorem 3.5. -/
def PeluseConcatRel : Prop :=
  ∀ (c : ℤ), 0 < c → ∀ C : ℕ, ∀ s : ℕ, 1 ≤ s →
    ∃ s' : ℕ, 1 ≤ s' ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ A : ℝ, 1 ≤ A ∧ ∃ K : ℕ, 1 ≤ K ∧
      ∀ (N M₁ M₂ : ℕ) (d : Fin s → ℤ) (δ δ' : ℝ) (f : ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
        (∀ i : Fin s, |d i| ≤ (C : ℤ) * (N : ℤ) / (M₁ : ℤ)) →
        SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        0 < δ → δ ≤ 1 → 0 < δ' → A * δ' ≤ δ ^ K →
        A ≤ (M₂ : ℝ) * (δ * δ') ^ K →
        δ ≤ (M₂ : ℝ)⁻¹ * ∑ a ∈ Finset.Icc 1 M₂,
          boxNorm s (fun i : Fin s => arithIcc (c * (a : ℤ) + d i) M₁) (symIcc N) f →
        C' * (δ * δ') ^ K ≤
          uNorm s' (arithIcc c (⌊δ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) (symIcc N) f

/-- **Peluse's Theorem 3.5, fully repaired.**  Two repairs relative to
`Work.Peluse.PeluseConcatenation` (`Nodes.lean`):

* the witnesses `s', C', A, K` are quantified *before* the coefficient `c` (and before the scale
  data), as in the source — the source's `s' ≪_s 1` depends only on the shift constant and on the
  level `s`, not on `c` nor on `N, M₁, M₂, δ, δ', f`.  In `PeluseConcatenation` they are placed after
  `∀ c`, which makes the theorem *weaker* than the source's and blocks the proof of Lemma 5.7 (the
  coefficient produced there is `c = p_{i₀}(a)`, which varies with `a ∈ A` and is unbounded);
* the averaged family is `arithIcc (c * (a : ℤ) + d i) M₁` with *arbitrary* integer shifts
  `d : Fin s → ℤ`, i.e. the shift need not be a multiple of the coefficient — which is the form
  Lemma 5.7's proof needs (its shifts are the integer `b_{a,ω}`).

Every instance of `PeluseConcatenation` is an instance of this statement (`d i := c * b i`). -/
def PeluseConcatFixed : Prop :=
  ∀ C : ℕ, ∀ s : ℕ, 1 ≤ s →
    ∃ s' : ℕ, 1 ≤ s' ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ A : ℝ, 1 ≤ A ∧ ∃ K : ℕ, 1 ≤ K ∧
      ∀ (c : ℤ), 0 < c →
      ∀ (N M₁ M₂ : ℕ) (d : Fin s → ℤ) (δ δ' : ℝ) (f : ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
        (∀ i : Fin s, |d i| ≤ (C : ℤ) * (N : ℤ) / (M₁ : ℤ)) →
        SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        0 < δ → δ ≤ 1 → 0 < δ' → A * δ' ≤ δ ^ K →
        A ≤ (M₂ : ℝ) * (δ * δ') ^ K →
        δ ≤ (M₂ : ℝ)⁻¹ * ∑ a ∈ Finset.Icc 1 M₂,
          boxNorm s (fun i : Fin s => arithIcc (c * (a : ℤ) + d i) M₁) (symIcc N) f →
        C' * (δ * δ') ^ K ≤
          uNorm s' (arithIcc c (⌊δ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) (symIcc N) f

/-- **Peluse's Lemma 5.7**, with the paper's quantifier placement: the exponent `K`, the constant
`C₀`, the number `t'` of long directions and the constant `c` depend only on the datum
`(k, kω, p, D)` — not on the instance `(A, M₁, M₂, N, γ, γ', f)`.  This is the statement whose
proof needs the paper's argument (pigeonhole, box-norm expansion, Theorem 3.5), and it is the form
the ladder's consumer (Proposition 3.6) needs.

The hypotheses are those of `Work.Peluse.UControl.PeluseLadder`; only the quantifier placement of
`(t', c)` and the conclusion's uniformity in `s₀` are made explicit. -/
def PeluseLadderStrong : Prop :=
  ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ) (kω : SlotSet ι k → ℕ)
    (p : ι → (Fin n → ℤ) → ℤ) (D : ℕ),
    ∃ (K : ℕ) (C₀ : ℝ) (t' : ℕ) (c : ℝ),
      1 ≤ K ∧ 0 < C₀ ∧ 1 ≤ t' ∧ 0 < c ∧
      ∀ (A : Finset (Fin n → ℤ)) (M₁ M₂ N : ℕ) (γ γ' : ℝ) (f : (Fin n → ℤ) → ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N →
        ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ)) →
        0 < γ → γ ≤ 1 → 0 < γ' → γ' ≤ γ ^ K →
        (∀ i a, a ∈ A → 0 < p i a) →
        (∀ i a, a ∈ A → p i a * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ)) →
        (∀ i a, a ∈ A → |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ)) →
        (∀ a ∈ A, ∀ x, ‖f a x‖ ≤ 1) → (∀ a ∈ A, SupportIn (f a) N) →
        C₀ * (γ * γ') ^ (-(K : ℤ)) ≤ (M₁ : ℝ) * (M₂ : ℝ) →
        γ ≤ ((A.card : ℝ))⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
              ∑ a ∈ A, ∑ a' ∈ paramBox (k := k) M₂,
                boxNorm (Fintype.card (FamIdx kω))
                  (fun j : Fin (Fintype.card (FamIdx kω)) =>
                    pDirFam p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) (f a) →
        ∀ s₀ : Slot ι k,
          c * γ ^ K ≤
            ((A.card : ℝ))⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
              ∑ a ∈ A, ∑ b ∈ paramBox (k := k) M₂,
                boxNorm (Fintype.card (ConclIdx s₀ kω t'))
                  (fun j : Fin (Fintype.card (ConclIdx s₀ kω t')) =>
                    conclDir p M₁ M₂ γ' s₀ t' a b
                      ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j))
                  (symIcc N) (f a)

end

end Work.Peluse.UControl

