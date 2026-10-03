/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The intermediate theorems of Peluse's inverse theorem, as `Prop`s

This module records, as `Prop`-valued definitions, the intermediate theorems of Peluse's paper
(*Bounds for sets with no polynomial progressions*, Forum Math. Pi **8** (2020), arXiv:1909.00309),
specialised to the single progression `(x, x + y, x + P(y))` that Krause–Mirek–Tao need
(`deg P = d ≥ 2`).  They are the "chapters" of Area A2:

* `PeluseConcatenation` — Theorem 3.5 (the main concatenation result), chapter (ii);
* `PeluseUControl` — Propositions 3.4 + 3.6 and Theorem 3.7 together with Corollary 3.8: an average
  of box norms of the *dual function* `F₂` is controlled by a `U^s`-norm; chapter (i) (§§4-6);
* `PeluseULowering` — Lemma 3.9 iterated together with Lemma 2.4 (`U²` inverse theorem), Lemma 3.10
  (major arcs) and §9: `U^s`-control of `F₂` yields a long progression on which `f₁` has large
  average; chapter (iii) (§§7-9);
* `PeluseU2Inverse` — Peluse's Lemma 2.4 (the only `U^s` inverse theorem used, `s = 2`);
* `PeluseMajorArc` — Lemma 3.10 / Lemma 8.1 in the case `ℓ = 2` (Weyl + major arcs).

`Submission/Work/Peluse/Assembly.lean` derives `AreaA2` from `PeluseUControl` and
`PeluseULowering`; the other three nodes are recorded because they are the (independent) inputs of
those two, and because they are the natural targets for further work on this area.

Nothing here is an axiom: these are `Prop`-valued definitions, used as explicit hypotheses, in the
style of `Work.Analysis.IWMultiplier.IWMultiplierBoundStatement_even`.
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse

noncomputable section

/-! ## Two bookkeeping devices -/

/-- A computable bound for `|P (y)|`, `y ∈ [0,M]`: `∑_i |a_i| M^i ≥ |P y|` whenever `0 ≤ y ≤ M`. -/
def polySup (P : ℤ[X]) (M : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).natAbs * M ^ i

/-- The scale relation `L ≍ M ^ d`, used for the shift sets `c[δ' M^d]` of the `U^s`-norms. -/
def Scaled (L M d : ℕ) : Prop := (M : ℝ) ^ d / 2 ≤ (L : ℝ) ∧ (L : ℝ) ≤ 2 * (M : ℝ) ^ d

/-- The support box `[-L, L]` with `L = N + polySup P M` containing the support of the dual
function `dualFn M P f₀ f₁` whenever `f₀, f₁` are supported in `[-N, N]` and `M ≤ N`. -/
def dSup (P : ℤ[X]) (N M : ℕ) : ℕ := N + polySup P M

/-! ## Chapter (ii): concatenation (Peluse, Theorem 3.5) -/

/-- **Propositions 3.4 and 3.6 + Theorem 3.7 + Corollary 3.8** (Peluse §§4-6) — chapters (i) and
(ii), in the normalisation used by `PeluseCrux`.

**SUPERSEDED / OFF-ROUTE (lead audit, `PW_A6_A2_LEAD.md` §2.3–2.5, 2026-10-03).**  This `Prop`
quantifies over *every* shift length `D ≥ 1` with `C·D ≤ δ^K N^d` and carries no non-degeneracy,
which is stronger than Peluse's Theorem 3.7 (that needs `δ' ≪ δ^{O(1)}` and
`N ≫ (1/(δδ'))^{O(1)}`); the fleet itself refuted the `C = 1` band form.  The crux only ever
instantiates `D = ⌊δ_U^{K₁}N^d/C₁⌋` (`crux_of_nodes.lean`).  The current route replaces this node by
`PeluseUControlPaper` (`PaperRoute/`, owner L1701), built from the **proved faithful**
`prop34Holds : Prop34 P` (Peluse's Proposition 3.4) together with `Prop36S` (Peluse §5).
This definition is kept (not deleted) for reference; do not spend new work on it — use
`PeluseUControlPaper` instead.

If `f₀, f₁, f₂` are `1`-bounded, supported in `[-N₀,N₀]`, the x-range `N₀` and the number `N` of
polynomial values satisfy `N₀ ≤ A' N^d` and `N^d ≤ A' δ^{-1} N₀` (the scale imbalance is at most
`A' δ^{-1}`), the shift range `D` is polynomially small in `δ` (`D ≤ δ^K N^d`, i.e. `δ' ≪ δ^{O(1)}`,
which is what the PET induction of §4 needs), and `δ ≤ ‖Λ^{N₀,N}_{X,P}(f₀,f₁,f₂)‖`, then the
`U^s`-norm of the dual function `F₂ = dualFn N P f₀ f₁` at scale `c[D]` (`c = P.leadingCoeff`) is at
least `δ^{O(1)}`, for some `s ≪_d 1`.

The exact constant is displayed as `C A'^K δ^{-K}`: the exponent `K` is uniform (it is the one
fixed by the statement), while the dependence on the scale imbalance `A'` is polynomial, which is
what the paper gives. -/
def PeluseUControl (P : Polynomial ℤ) : Prop :=
  ∃ s : ℕ, 2 ≤ s ∧ ∀ A' : ℝ, 1 ≤ A' → ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
    ∀ (N N₀ D : ℕ) (f₀ f₁ f₂ : ℤ → ℂ) (δ : ℝ),
      2 ≤ P.natDegree → 1 ≤ N → 1 ≤ N₀ →
      (N₀ : ℝ) ≤ A' * (N : ℝ) ^ P.natDegree →
      (N : ℝ) ^ P.natDegree ≤ A' * (δ⁻¹) * (N₀ : ℝ) →
      0 < δ → δ ≤ 1 → 1 ≤ D → (C : ℝ) * (D : ℝ) ≤ δ ^ K * (N : ℝ) ^ P.natDegree →
      SupportIn f₀ N₀ → SupportIn f₁ N₀ → SupportIn f₂ N₀ →
      (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) → (∀ x : ℤ, ‖f₂ x‖ ≤ 1) →
      δ ≤ ‖LambdaZ N₀ N P f₀ f₁ f₂‖ →
      δ ^ K ≤ (C : ℝ) * A' ^ K * (δ⁻¹) ^ K *
        uNormPow s (arithIcc P.leadingCoeff D) (symIcc (dSup P N₀ N)) (dualFn N P f₀ f₁)

/-- **Peluse's Lemma 2.4** (the `U²` inverse theorem in the form used, with the weight `μ_{δ'L}`):
there are constants `C', K > 0` (absolute) such that for `1`-bounded `f` supported in `[-L,L]`, if
`‖f‖_{U²_{[δ'L]}([-L,L])} ≥ δ` then `f` correlates with a character: there is `β ∈ ℝ` with
`|∑_x f(x) e(βx)| ≥ C' (δδ')^K L`.

The factor `L` is the paper's normalisation `|E_{x∈[L]} f(x)e(βx)| ≫ (δδ')^{O(1)}` (without it the
node is true but trivial — Parseval alone gives it — and useless to `PeluseULowering`, see the
lead's audit `NODES_AUDIT_LEAD.md` §3). -/
def PeluseU2Inverse : Prop :=
  ∃ C' : ℝ, 0 < C' ∧ ∃ K : ℕ, 1 ≤ K ∧
    ∀ (L : ℕ) (δ δ' : ℝ) (f : ℤ → ℂ),
      1 ≤ L → 0 < δ → δ ≤ 1 → 0 < δ' → δ' ≤ 1 →
      SupportIn f L → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      δ ≤ uNorm 2 (arithIcc 1 ((⌊δ' * (L : ℝ)⌋).toNat)) (symIcc L) f →
      ∃ β : ℝ,
        C' * (δ * δ') ^ K * (L : ℝ) ≤
          ‖∑' x : ℤ, f x * Complex.exp (2 * Real.pi * Complex.I * β * x)‖

/-- **Peluse's Lemma 3.10 / Lemma 8.1** for `ℓ = 2` (Weyl sums and major arcs), specialised to the
progression `(x, x + y, x + P(y))`: if the dual function `F₂` correlates with the character
`x ↦ e(βx)` at scale `N`, then `β` is a major arc: `‖t β‖ ≲_{P} δ^{-O(1)}/M^d` for some
`t ≪_P δ^{-O(1)}`.  Here `‖·‖ = distInt` is the distance to the nearest integer (the paper's `‖·‖`),
and the implied constants are displayed as `C'` — they must *not* be quantified away, because the
hypothesis allows `δ = 1` (machine-checked refutations of both the version without `C'` and of the
version using `|tβ|` are recorded in `NOTES_Peluse_majorarc_FALSE.md` at the workspace root).

Per the lead's audit, no scale relation (`Scaled`) or `M ≤ N` is needed: the proof is Plancherel
plus Weyl's inequality on the exponential sum in the `y`-variable. -/
def PeluseMajorArc (P : Polynomial ℤ) : Prop :=
  ∃ C' : ℝ, 0 < C' ∧ ∃ K : ℕ, 1 ≤ K ∧
    ∀ (N M : ℕ) (f₀ f₁ : ℤ → ℂ) (β δ : ℝ),
      2 ≤ P.natDegree → 1 ≤ N → 1 ≤ M →
      0 < δ → δ ≤ 1 → SupportIn f₀ N → SupportIn f₁ N →
      (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
      δ * (N : ℝ) ≤ ‖∑' x : ℤ, dualFn M P f₀ f₁ x * Complex.exp (2 * Real.pi * Complex.I * β * x)‖ →
      ∃ t : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ C' * (δ⁻¹) ^ K ∧
        distInt ((t : ℝ) * β) ≤ C' * (δ⁻¹) ^ K / (M : ℝ) ^ P.natDegree

/-- **Lemma 3.9 (degree lowering) iterated + Lemma 2.4 + §9** — chapter (iii), in the
normalisation used by `PeluseCrux`.

If the dual function `F₂ = dualFn N P f₀ f₁` has `U^s`-norm at least `δ` at scale `c[D]`
(`s ≥ 2`, `c = P.leadingCoeff`, `1 ≤ D ≤ N^d`, i.e. the shift parameter `δ' = D/N^d ∈ (0,1]`),
and the scale relations of `PeluseUControl` hold, then `f₁` has large average along a long
arithmetic progression:

  `∑_x |E_{m ≤ N'} f₁ (x + q m)| ≥ δ^{O(1)} N / C`,  with `q ≪ δ^{-O(1)}`,  `N' ≥ δ^{O(1)} N`.

As in Peluse's Lemma 3.9, a *small* shift parameter `δ' = D/N^d` is paid for in the conclusion
(the factor `(δ δ')^K = δ^K (D/N^d)^K`, displayed below): the paper allows any `0 < δ' ≤ 1` in that
lemma and loses `(δδ')^{O(1)}`.  This is what makes the composition with `PeluseUControl` work —
there the shift parameter is `≍ δ^{K}`. -/
def PeluseULowering (P : Polynomial ℤ) : Prop :=
  ∀ s : ℕ, 2 ≤ s → ∀ A' : ℝ, 1 ≤ A' → ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
    ∀ (N N₀ D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ : ℝ),
      2 ≤ P.natDegree → 1 ≤ N → 1 ≤ N₀ →
      (N₀ : ℝ) ≤ A' * (N : ℝ) ^ P.natDegree →
      (N : ℝ) ^ P.natDegree ≤ A' * (δ⁻¹) * (N₀ : ℝ) →
      0 < δ → δ ≤ 1 → 1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ P.natDegree →
      SupportIn f₀ N₀ → SupportIn f₁ N₀ →
      (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
      δ ≤ uNormPow s (arithIcc P.leadingCoeff D) (symIcc (dSup P N₀ N)) (dualFn N P f₀ f₁) →
      ∃ q N' : ℕ, 1 ≤ q ∧
        (q : ℝ) ≤ (C : ℝ) * A' ^ K *
          ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K * (δ⁻¹) ^ K ∧
        1 ≤ N' ∧ N' ≤ N ∧
        δ ^ K * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ K * (N : ℝ) ≤
          (C : ℝ) * A' ^ K * ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K * (δ⁻¹) ^ K * (N' : ℝ) ∧
        δ ^ K * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ K * (N₀ : ℝ) ≤
          (C : ℝ) * A' ^ K * ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K * (δ⁻¹) ^ K *
            progAvgSum N' (q : ℤ) f₁

/-- **The crux of Area A2**, in the normalisation of the target statement.

This is the two chapters

(a) (Peluse §§4-6, Propositions 3.4 and 3.6, Theorems 3.5 and 3.7, Corollary 3.8): *PET control by
an average of box norms* together with *concatenation*, giving `U^s`-control of the dual function
`F₂ = dualFn N P f₀ f₁` at a polynomially small scale, and

(b) (Peluse §§7-9, Lemmas 3.9, 2.4, 3.10 and the §9 argument): *degree lowering*, the `U²` inverse
theorem, the major-arc (Weyl) lemma, and the final van der Corput argument that recovers the
progression average of `f₁`,

packaged in exactly the form that the elementary reduction `AreaA2_of_crux`
(`Submission/Work/Peluse/Assembly.lean`) needs.  In Peluse's notation the statement below is her
Theorem 3.3 for the progression `(x, x+y, x+P(y))`, written with `N` = the number `M` of polynomial
values, `N₀` = the `x`-range `N`, and with the correlation normalised as
`δ N^d ≤ ‖Λ^{N₀,N}_{X,P}(f₀,f₁,f₂)‖ · N₀` (which is `δ N^d ≤ |⟨Ã_N(f₁,f₂), f₀⟩|` when `f₀` is
supported in `[-N₀,N₀]`, by `bilinPair_AhalfZ_eq`).

The hypothesis `A δ^{-K} ≤ N` is the non-degenerate case: for `N` smaller than that the conclusion
of `PeluseInverseKMT` is vacuous (its first alternative holds).  The finer intermediate nodes are
`PeluseConcatenation`, `PeluseUControl`, `PeluseU2Inverse`, `PeluseMajorArc` and `PeluseULowering`
above; this packaging is the interface consumed by the assembly. -/
def PeluseCrux (P : Polynomial ℤ) : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
    ∀ (N N₀ : ℕ) (δ : ℝ) (f₀ f₁ f₂ : ℤ → ℂ),
      2 ≤ P.natDegree → 1 ≤ N → 0 < δ → δ ≤ 1 → 1 ≤ N₀ →
      A * (δ⁻¹) ^ K ≤ (N : ℝ) →
      (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
      SupportIn f₀ N₀ → SupportIn f₁ N₀ → SupportIn f₂ N₀ →
      (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) → (∀ x : ℤ, ‖f₂ x‖ ≤ 1) →
      δ * (N : ℝ) ^ P.natDegree ≤ ‖LambdaZ N₀ N P f₀ f₁ f₂‖ * (N₀ : ℝ) →
      ∃ q N' : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (C : ℝ) * (δ⁻¹) ^ K ∧ 1 ≤ N' ∧ N' ≤ N ∧
        δ ^ K * (N : ℝ) ≤ (C : ℝ) * (N' : ℝ) ∧
        δ ^ K * (N : ℝ) ^ P.natDegree ≤ (C : ℝ) * progAvgSum N' (q : ℤ) f₁

end

end Work.Peluse
