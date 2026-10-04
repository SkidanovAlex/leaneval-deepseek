import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalcStep1.laplacian_pow_mul_comm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3 / Symbol calculus, step 0: the *flat* pieces of the order reduction

This file starts the (missing) **symbol-calculus layer** that the target
`Work.Diff.STE.B3.ENormB_pair_J_commutator_v2` needs.  The analysis there (see its header and
`HANDOFF.md`, session-5 note) reduces that target to the standard order reduction

  `[Qk, J] = Σ_{i,j} [Δ_i, S_j]`,   `Δ_i = R_i* Λ^k R_i` (order `2k`),  `S_j = R_j* S_ε R_j` (order 0),

i.e. to the fact that **the commutator of two operators with scalar symbols on `T*M` is one order
lower**, together with the exact conjugation identity (`P := comp_τ ∘ Λ^k ∘ comp_σ` is the flat
Laplacian power written in the chart-`j` variable)

  `[Λ^k, comp_σ ∘ S_ε ∘ comp_τ] = comp_σ ∘ [P, S_ε] ∘ comp_τ`,
  `[P, S_ε] = Σ_{|β|≤2k} [M_{A_β}, S_ε] ∂^β`  (constant-coefficient `∂^β` commute with `S_ε`).

Everything therefore rests on the **flat multiplier commutator** `[M_A, S_ε]` and its `ε`-uniform
`ε`-gain, where `S_ε` is the Friedrichs cutoff of a profile `ρ` that — unlike in the older
`CSq_trunc_sub_le` / `CSq_succ_commutator_le` (`ρ ≡ 1` on the unit ball) — only satisfies
`ρ 0 = 1`, `‖ρ‖ ≤ 1`, smoothness, and `ρ y = 0` for `2 < Σ yᵢ²`.

The three statements below are the smallest standalone targets for that layer.  All three are
*true*; the first is the analogue of the existing `CSq_succ_commutator_le` with the support
hypothesis in place of `ρ ≡ 1` (the proof changes only in the case analysis: `|ρ (εn) − ρ (εm)|`
must be bounded by `min 2 (L ε |n − m|)` **and** the support of the difference forces
`min ⟨n⟩ ⟨m⟩ ≤ 3/ε`), the second is the analogue of `CSq_trunc_sub_le` in the same style, and the
third is the first-order case of the scalar-symbol order reduction (`P = Σᵢ Mᵢ ∂ᵢ`, so
`[P,S_ε] = Σᵢ [Mᵢ,S_ε] ∂ᵢ` is of order `0`, uniformly in `ε`, whereas the naive order is `1`).

Do not confuse the two roles of `S_ε`: as a `CSq`-multiplier (`trunc ρ ε` on coefficient families)
in the first two statements, and as the function-level cutoff `flatCut` in the third.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3.SymCalc

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **Friedrichs cutoff at scale `ε`** applied to a `1`-periodic function: multiply the `k`-th
Fourier coefficient by `ρ (ε • k)` and reassemble.  This is the function-level version of
`Work.Diff.STE.trunc ρ ε` (it is the operator written `S_ε` in the analysis). -/
def flatCut (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (g : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff g))

/-- The **flat Laplacian** `Λ = Σᵢ ∂ᵢ∂ᵢ` on the torus. -/
def lapC (g : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => ∑ i, Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x

/-- **Composition with a map** `T`: the "chart transfer" `comp_T`, `(comp_T g)(x) = g (T x)`. -/
def compMap (T : (ι → ℝ) → (ι → ℝ)) (g : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => g (T x)

/-- The **chart-`j` cutoff transported into the chart-`i` variable**: with `T = τ` (`x = τ s`)
and `T' = σ = τ⁻¹`, this is `comp_σ ∘ S_ε ∘ comp_τ`, i.e. `S_ε` acting in the *other* chart's
coordinates — the operator denoted `V` in the analysis of
`Work.Diff.STE.B3.ENormB_pair_J_commutator_v2`. -/
def conjCut (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ)) (g : (ι → ℝ) → ℂ) :
    (ι → ℝ) → ℂ :=
  compMap T' (flatCut ρ ε (compMap T g))

/-- The symbol of the **flat Laplacian**, `λ(m) = Σⱼ (2π mⱼ)²` (a local copy of
`Work.Diff.STE.B3.lamSym`, kept here so that this file depends only on `Torus`).  The multiplier
with symbol `λ^k` is `Λ^k` in the analysis. -/
def flatLam (m : ι → ℤ) : ℝ :=
  ∑ j, (2 * Real.pi * (m j : ℝ)) ^ 2

/-- The Euclidean norm of a lattice vector, as a real number (the `ℓ²` norm of the coefficients). -/
def flatNorm (m : ι → ℤ) : ℝ := Real.sqrt (∑ j, ((m j : ℝ)) ^ 2)

/-- **PIECE 0a — the symbol-difference bound** (the one non-elementary input of PIECE 0).

With `P(m) = flatLam m = Σⱼ (2π mⱼ)²` the symbol of the flat Laplacian,

  `|P(m)^k − P(m − l)^k| ≤ C · (‖l‖² + ‖m‖‖l‖) · (‖m‖ + ‖l‖)^{2k−2}`,  `‖x‖ = flatNorm x`,

with `C` depending only on `k` and `ι`.  Proof: `P^k − Q^k = (P − Q) Σ_{j<k} P^j Q^{k−1−j}`,
`|P(m) − P(m−l)| = (2π)²|2⟨m,l⟩ − ‖l‖²| ≤ (2π)²(2‖m‖‖l‖ + ‖l‖²)`, and each of the `k` summands is
`≤ (2π)^{2(k−1)} max(‖m‖,‖m−l‖)^{2k−2} ≤ (2π)^{2(k−1)}(‖m‖+‖l‖)^{2k−2}`.

The two regimes of the Schur step of PIECE 0 are read off from it: for `‖l‖ ≤ ‖m‖` it gives
`≲ ‖l‖‖m‖^{2k−1}` (the `‖l‖²‖m‖^{2k−2}` term is smaller), and for `‖l‖ ≥ ‖m‖` it gives `≲ ‖l‖^{2k}`.
The sharper `‖l‖` (rather than `‖l‖²`) in the first regime is what the weighted `ℓ²` sum needs. -/
theorem flatLam_pow_sub_bound
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m l : ι → ℤ,
        |(flatLam m) ^ k - (flatLam (m - l)) ^ k|
          ≤ C * ((flatNorm l) ^ 2 + flatNorm m * flatNorm l)
              * (flatNorm m + flatNorm l) ^ (2 * k - 2) := by
  sorry

/-- **PIECE 0 — the Leibniz estimate for `[Λ^k, M_a]`** (the diagonal's core).

`Λ^k` is the flat Laplacian power (the multiplier with symbol `λ^k`) and `M_a` the multiplier with
coefficient family `a` (the convolution `conv a`).  Their commutator `[Λ^k, M_a]` is an honest
differential operator of order `2k−1` (Leibniz), so it loses exactly `2k−1` derivatives:

  `CSq s ([Λ^k, M_a] c) ≤ C · CSq (s + 2k − 1) c`.

This is the piece that the **diagonal** contribution `R_i* ([Λ^k, M_{ψ_i²}] (id − S_ε)) R_i` of
`[Qk, J]` needs: no symbol calculus, only the product rule and the boundedness of `id − S_ε`. -/
theorem laplacian_pow_mul_comm_le
    (a : (ι → ℤ) → ℂ)
    (ha : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖a k‖))
    (k : ℕ) (hk : 1 ≤ k) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ c : (ι → ℤ) → ℂ,
        Summable (fun m : ι → ℤ =>
            (Work.Diff.STE.wt m) ^ (s + 2 * k - 1) * ‖c m‖ ^ 2) →
        Work.Diff.STE.CSq s
            (fun m => (((flatLam m) ^ k : ℝ) : ℂ) * Work.Diff.STE.conv a c m
              - Work.Diff.STE.conv a (fun m => (((flatLam m) ^ k : ℝ) : ℂ) * c m) m)
          ≤ C * Work.Diff.STE.CSq (s + 2 * k - 1) c := by
  sorry

/-- **PIECE 1 — the flat multiplier commutator, `ε`-uniformly of order `−1`.**

This is `CSq_succ_commutator_le` with the hypothesis `ρ = 1` on the unit ball replaced by the
*support* hypothesis `ρ y = 0` for `2 < Σ yᵢ²`.  (`a` is the coefficient family of the multiplier
`M_a`; the two sides are the coefficient families of `M_a (S_ε c)` and `S_ε (M_a c)`.) -/
theorem flat_multiplier_commutator
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρ0 : ρ 0 = 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (a : (ι → ℤ) → ℂ)
    (ha : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖a k‖))
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ c : (ι → ℤ) → ℂ,
        Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) →
        Work.Diff.STE.CSq (s + 1)
            (fun k => Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
              - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k)
          ≤ C * Work.Diff.STE.CSq s c := by
  sorry

/-- **PIECE 2 — the Friedrichs high-pass gain at scale `ε`.**

`CSq_trunc_sub_le` with `ρ = 1` on the unit ball replaced by `ρ 0 = 1` and a Lipschitz bound
(no support hypothesis is needed here): the pointwise estimate `‖1 - ρ (ε • k)‖ ≤ L ε ⟨k⟩` gives
the one-derivative gain with the `ε²`. -/
theorem friedrichs_high_pass
    (ρ : (ι → ℝ) → ℝ)
    (hρ0 : ρ 0 = 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ c : (ι → ℤ) → ℂ,
        Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + 1) * ‖c k‖ ^ 2) →
        Work.Diff.STE.CSq s (fun k => c k - Work.Diff.STE.trunc ρ ε c k)
          ≤ (C * ε ^ 2) * Work.Diff.STE.CSq (s + 1) c := by
  sorry

/-- **PIECE 3 — first-order scalar-symbol order reduction (the variable-coefficient case).**

For a first-order operator `P g = Σᵢ Mᵢ · ∂ᵢ g` with `C^∞` `1`-periodic coefficients `Mᵢ` that are
bounded together with their first derivatives, the commutator with the cutoff `S_ε` is bounded on
the `Hˢ` scale **uniformly in `ε ∈ (0,1]`** (its naive order is `1`; the commutator has order `0`).
This is the form in which identity (2) of the analysis is consumed: `[P,S_ε] = Σᵢ [Mᵢ,S_ε] ∂ᵢ`. -/
theorem firstOrder_comm_trunc_le
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρ0 : ρ 0 = 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (M : ι → (ι → ℝ) → ℝ)
    (hMsm : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (M i))
    (hMper : ∀ i, Work.Diff.STE.Periodic1 (M i))
    (CM : ℝ) (hCM : ∀ (i : ι) (x : ι → ℝ), ‖M i x‖ ≤ CM)
    (CM1 : ℝ) (hCM1 : ∀ (i : ι) (x : ι → ℝ),
      ‖Work.Diff.STE.pdR i (M i) x‖ ≤ CM1)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ g : (ι → ℝ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) g → Work.Diff.STE.Periodic1 g → Summable (fun k : ι → ℤ =>
            (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2) →
        Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
            ((fun x => ∑ i, ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i (flatCut ρ ε g) x)
              - flatCut ρ ε (fun x => ∑ i, ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i g x)))
          ≤ C * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff g) := by
  sorry

/-- **PIECE 4-edge (`conj_cut_s0`) — the low-regularity end of the cross crux, standalone.**

This is the `s = 0` case of PIECE 4's analytic content, isolated so that the *interior* range
(`s ≥ 1`) can be discharged from `flat_multiplier_commutator` (cite it with `s' := s − 1` on
`dmulMulti α c`: the derivative raises the weight by `|α|`, giving back `s + 1`; `[P,S_ε]` has
order `1` and each `[M_{A_β},S_ε]∂^β` order `|β| − 1 ≤ 1`, so there is no deficit there).

Here `a` is the coefficient family of the multiplier `M_a`, `dmulMulti α c` is the coefficient
family of `∂^α` applied to the function with coefficients `c`, and `trunc ρ ε` is `S_ε`.  The
statement is that for `|α| ≤ 2` (the only cases produced by the conjugate Laplacian, whose
coefficients are `A_{ij}` and `B_i`)

  `CSq 0 ( M_a (S_ε (∂^α c)) − S_ε (M_a (∂^α c)) ) ≤ C · CSq 1 c`,

`ε`-uniformly.  This is the case where PIECE 1 *cannot be instantiated* (`s' = −1`), and it is the
only place where a raw kernel/Schur estimate loses a factor `⟨m⟩`: the pointwise increment bound
`|ρ(εm) − ρ(ε(m−l))| ≤ min 2 (L ε |l|)` must be combined with the **support** of the difference
(it vanishes unless `min ⟨m⟩ ⟨m−l⟩ ≲ 1/ε`) exactly as in the proof of
`flat_multiplier_commutator`, run on `dmulMulti α c`. -/
theorem mulDeriv_comm_trunc_s0_le
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρ0 : ρ 0 = 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (a : (ι → ℤ) → ℂ)
    (ha : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖a k‖))
    (α : ι → ℕ) (hα : (∑ i, α i) ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ c : (ι → ℤ) → ℂ,
        Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ 1 * ‖c m‖ ^ 2) →
        Work.Diff.STE.CSq 0
            (fun m => Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε
                (Work.Diff.STE.dmulMulti α c)) m
              - Work.Diff.STE.trunc ρ ε
                (Work.Diff.STE.conv a (Work.Diff.STE.dmulMulti α c)) m)
          ≤ C * Work.Diff.STE.CSq 1 c := by
  sorry

/-- **PIECE 3/4-`k` — the sharp derivative-weighted flat multiplier commutator, all orders.**

The `k`-th order versions of PIECE 3 and PIECE 4 both consume this single statement: for the
Friedrichs cutoff `trunc ρ ε = S_ε`, a multiplier `M_a` and `∂^α` with `|α| = ∑ᵢ αᵢ ≥ 1`,

  `CSq s ( M_a (S_ε (∂^α c)) − S_ε (M_a (∂^α c)) ) ≤ C · CSq (s + |α| − 1) c`,  `ε`-uniform,

i.e. `[M_a, S_ε] ∘ ∂^α` is of order `|α| − 1` and no better, and the `ε`-uniformity survives the
composition (this is the sharp point: citing PIECE 1 naively gives `CSq s ≤ C CSq (s + |α|)`, one
weight too many).  Both extremes are covered: for `s + |α| ≥ 2` it is PIECE 1 cited with
`s' := s + |α| − 2` on `dmulMulti α c`; for the low regularity end (`s + |α| ≤ 1`, in particular
`s = 0`, `|α| ∈ {1,2}`, which is what the conjugate Laplacian's coefficients produce) it needs the
support argument: `|ρ(εm) − ρ(ε(m−l))| ≤ min 2 (L ε |l|)` together with "the increment vanishes
unless `min ⟨m⟩ ⟨m−l⟩ ≲ 1/ε`", run directly on `dmulMulti α c`.

Its `s = 0, |α| = 2` case is the separately named `mulDeriv_comm_trunc_s0_le`; the general statement
here is what the `k`-th order commutators (`Λ^k` in place of `Λ`, i.e. a conjugate operator of order
`2k` with coefficients up to order `2k`) reduce to:

  `[Λ^k, conjCut ρ ε T T'] = compMap T' ∘ [P_k, S_ε] ∘ compMap T`,  `P_k := compMap T ∘ lapC^k ∘ compMap T'`,
  `[P_k, S_ε] = Σ_{|β|≤2k} [M_{A_β}, S_ε] ∂^β`  ⟹ order `2k − 1`, uniformly in `ε`.

For a general variable-coefficient operator `P = Σ_{|β|≤m} M_β ∂^β` this is the `k`-th order form
of PIECE 3: `[P, S_ε]` is bounded `CSq s → CSq (s + m − 1)` by summing the present statement over
`β` (the coefficients `M_β` are bounded, and their bounds enter the constant). -/
theorem mulDeriv_comm_trunc_le
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρ0 : ρ 0 = 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (a : (ι → ℤ) → ℂ)
    (ha : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖a k‖))
    (s : ℕ) (α : ι → ℕ) (hα : 1 ≤ ∑ i, α i) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ c : (ι → ℤ) → ℂ,
        Summable (fun m : ι → ℤ =>
            (Work.Diff.STE.wt m) ^ (s + (∑ i, α i) - 1) * ‖c m‖ ^ 2) →
        Work.Diff.STE.CSq s
            (fun m => Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε
                (Work.Diff.STE.dmulMulti α c)) m
              - Work.Diff.STE.trunc ρ ε
                (Work.Diff.STE.conv a (Work.Diff.STE.dmulMulti α c)) m)
          ≤ C * Work.Diff.STE.CSq (s + (∑ i, α i) - 1) c := by
  sorry

/-- **PIECE D (the diagonal) — `[Λ^k, M_a] ∘ (id − S_ε)` is of order `2k − 1`, `ε`-uniformly.**

The flat core of the *diagonal* contribution to the target's left-hand side.  In B3 the `i`-th
diagonal term is `R_i* ([Λ^k, M_{ζ_i²}] (id − S_ε)) R_i` (using `R_i* R_i = M_{ζ_i²}`, available
instance-free as `Work.Diff.STE.B3.Rstar_R_eq_zeta_sq_free`, and `Λ^k S_ε = S_ε Λ^k` in one chart);
so what is needed is the flat operator `[Λ^k, M_a] ∘ (id − S_ε)` being of order `2k − 1`, i.e.
`CSq s ≤ C · CSq (s + 2k − 1)` — a two-line corollary of PIECE 0
(`laplacian_pow_mul_comm_le`) together with the trivial `‖1 − ρ(ε•m)‖ ≤ 2`, which bounds
`CSq (s+2k−1) (c − trunc ρ ε c) ≤ 4 CSq (s+2k−1) c`.

Note the shape: unlike PIECE 1/3, no `ε`-gain is needed here — `id − S_ε` is only used for its
*boundedness*, and the one derivative that the diagonal needs comes entirely from the Leibniz
commutator `[Λ^k, M_a]`.  That is why the diagonal is elementary and why it is independent of the
cross-term in-flight lemmas. -/
theorem laplacian_pow_mul_highpass_le
    (ρ : (ι → ℝ) → ℝ)
    (hρ0 : ρ 0 = 1)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (a : (ι → ℤ) → ℂ)
    (ha : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖a k‖))
    (k : ℕ) (hk : 1 ≤ k) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ c : (ι → ℤ) → ℂ,
        Summable (fun m : ι → ℤ =>
            (Work.Diff.STE.wt m) ^ (s + 2 * k - 1) * ‖c m‖ ^ 2) →
        Work.Diff.STE.CSq s
            (fun m => (((flatLam m) ^ k : ℝ) : ℂ)
                * Work.Diff.STE.conv a
                    (fun m => c m - Work.Diff.STE.trunc ρ ε c m) m
              - Work.Diff.STE.conv a
                  (fun m => (((flatLam m) ^ k : ℝ) : ℂ)
                    * (c m - Work.Diff.STE.trunc ρ ε c m)) m)
          ≤ C * Work.Diff.STE.CSq (s + 2 * k - 1) c := by
  obtain ⟨C, hC, hCb⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.laplacian_pow_mul_comm_le a ha k hk s
  refine ⟨4 * C, by linarith [hC], ?_⟩
  intro ε hε hε1 c hc
  let g : (ι → ℤ) → ℂ := fun m => c m - Work.Diff.STE.trunc ρ ε c m
  have hgnorm : ∀ m : ι → ℤ, ‖g m‖ ≤ 2 * ‖c m‖ := by
    intro m
    have h1 : ‖((ρ (ε • (fun i => (m i : ℝ))) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hρb _
    have htr : Work.Diff.STE.trunc ρ ε c m
        = ((ρ (ε • (fun i => (m i : ℝ))) : ℝ) : ℂ) * c m := rfl
    have hrew : g m = (1 - ((ρ (ε • (fun i => (m i : ℝ))) : ℝ) : ℂ)) * c m := by
      simp only [g, htr]
      ring
    rw [hrew, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h2 := norm_sub_le (1 : ℂ) (((ρ (ε • (fun i => (m i : ℝ))) : ℝ) : ℂ))
    simp only [norm_one] at h2
    linarith
  have hle : ∀ m : ι → ℤ, (Work.Diff.STE.wt m) ^ (s + 2 * k - 1) * ‖g m‖ ^ 2
      ≤ 4 * ((Work.Diff.STE.wt m) ^ (s + 2 * k - 1) * ‖c m‖ ^ 2) := by
    intro m
    have h := hgnorm m
    have hsq : ‖g m‖ ^ 2 ≤ 4 * ‖c m‖ ^ 2 := by
      nlinarith [h, norm_nonneg (g m), norm_nonneg (c m)]
    calc (Work.Diff.STE.wt m) ^ (s + 2 * k - 1) * ‖g m‖ ^ 2
        ≤ (Work.Diff.STE.wt m) ^ (s + 2 * k - 1) * (4 * ‖c m‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) _)
      _ = 4 * ((Work.Diff.STE.wt m) ^ (s + 2 * k - 1) * ‖c m‖ ^ 2) := by ring
  have hsumg : Summable (fun m : ι → ℤ =>
      (Work.Diff.STE.wt m) ^ (s + 2 * k - 1) * ‖g m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) _) (sq_nonneg _))
      hle (hc.mul_left 4)
  have hmono : Work.Diff.STE.CSq (s + 2 * k - 1) g
      ≤ 4 * Work.Diff.STE.CSq (s + 2 * k - 1) c := by
    have h4 : Summable (fun m : ι → ℤ =>
        4 * ((Work.Diff.STE.wt m) ^ (s + 2 * k - 1) * ‖c m‖ ^ 2)) := hc.mul_left 4
    have htsum := Summable.tsum_le_tsum hle hsumg h4
    calc Work.Diff.STE.CSq (s + 2 * k - 1) g
        = ∑' m : ι → ℤ, (Work.Diff.STE.wt m) ^ (s + 2 * k - 1) * ‖g m‖ ^ 2 := rfl
      _ ≤ ∑' m : ι → ℤ, 4 * ((Work.Diff.STE.wt m) ^ (s + 2 * k - 1) * ‖c m‖ ^ 2) := htsum
      _ = 4 * Work.Diff.STE.CSq (s + 2 * k - 1) c := by
          rw [tsum_mul_left]
          rfl
  have hg := hCb g hsumg
  show Work.Diff.STE.CSq s
      (fun m => (((flatLam m) ^ k : ℝ) : ℂ) * Work.Diff.STE.conv a g m
        - Work.Diff.STE.conv a (fun m => (((flatLam m) ^ k : ℝ) : ℂ) * g m) m)
      ≤ 4 * C * Work.Diff.STE.CSq (s + 2 * k - 1) c
  exact hg.trans (le_trans (mul_le_mul_of_nonneg_left hmono hC) (le_of_eq (by ring)))

/-- **PIECE 4 (the composition piece) — the commutator with the *transported* cutoff.**

This is the piece that the cross terms `i ≠ j` of `[Qk, J]` really need (the "composition with
`comp_σ`/`comp_τ`" piece).  With `T = τ` the chart-2-to-chart-1 transition (`x = τ s`) and
`T' = τ⁻¹` its inverse, and `V = conjCut ρ ε T T' = comp_σ ∘ S_ε ∘ comp_τ`, the claim is that

  `[Λ, V] = comp_σ ∘ [P, S_ε] ∘ comp_τ`,   `P := comp_τ ∘ Λ ∘ comp_σ` (the flat Laplacian in the
  other variable, an explicit variable-coefficient operator),

is of order `1` (one order lower than `Λ ∘ V`, of order 2), **uniformly in `ε ∈ (0,1]`**.  The
conjugation is exact — `comp_σ` and `comp_τ` are inverse to each other, so the two "outer" copies
cancel and `P` commutes with `S_ε` as far as the top order goes — which is why the naive
component-level estimate (which gives order `2`) is not the truth.  Verified numerically in the
1-D two-chart model: `‖[Λ,V]g‖_{L²}/‖g‖_{H¹} → 0.297` for `ε = 0.4/m`, `m = 4 … 64`. -/
theorem conj_cut_comm_laplacian_le
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρ0 : ρ 0 = 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (T T' : (ι → ℝ) → (ι → ℝ))
    (hTsm : ContDiff ℝ (⊤ : ℕ∞) T) (hTsm' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x)
    (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ g : (ι → ℝ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) g → Work.Diff.STE.Periodic1 g →
        Summable (fun k : ι → ℤ =>
            (Work.Diff.STE.wt k) ^ (s + 1) * ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2) →
        Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x =>
            lapC (conjCut ρ ε T T' g) x - conjCut ρ ε T T' (lapC g) x))
          ≤ C * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff g) := by
  sorry

end Work.Diff.STE.B3.SymCalc
