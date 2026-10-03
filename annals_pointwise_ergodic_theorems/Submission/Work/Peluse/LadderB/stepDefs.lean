import Mathlib
import Submission.Work.Peluse.Holds.LadderDefs
import Submission.Work.Peluse.BoxNorm.boxNormPow_le_one

/-!
# `Work.Peluse.ladderStepB` — the corrected one-step interface of the concatenation ladder

This is Peluse's Lemma 5.6 (*Bounds for sets with no polynomial progressions*, arXiv:1909.00309,
§5) in the form that the ladder of `Holds.boxLadder` actually iterates, i.e. the one-step statement
needed by the frozen bridge `Work.Peluse.C46.ConcatBridgeShortA`.

## Why this replaces `Work.Peluse.ladderStepA`

`ladderStepA` (`Submission/Work/Peluse/LadderStepDefs.lean`) is **FALSE**: it was refuted by a
delegated prover (`Peluse/LadderA/ladderStepAZero`) with the *large-averaging-range* degeneration
(see `NOTES_concatBridgeShortA_SESSION3.md` §1): its non-degeneracy
`2 ≤ L·γ^K·(D'/(M₁L))^{K-1}` does not mention the averaging range `M₁`, so the short-window box
average in the hypothesis can stay bounded below while the uniformity norm of the conclusion, taken
at a window `D'` that grows with `M₁`, decays to `0` (for a random-sign `f`, every level-`t` box
norm at such a window is `≍ t/D'`).

The data condition of the source's Lemma 5.6 is `M₁M₂ ≫_s (γ γ')^{-O_s(1)}`, where (in the
source's notation) the box norm is taken at the **long** direction length `M₁` and averaged over
the **small** range `M₂ ≤ M₁`; in the ladder's variables the averaging range is `M₁` and the
short/long direction lengths are `L` and `D' = γ'·M₁·L`.  The condition therefore carries the
factor `M₁L`, and the normalisation `γ` is the **observed** box-norm value at the state's level —
which, by `x ≤ boxLadder …`, is at least the state's own root `x^{1/2^t}`.

## The statement

`ladderStepB j` says: there are `s' ≥ 1`, `0 < C ≤ 1`, `k ≥ 1`, depending only on `j`, such that
for every datum with

* **both** conditions of the source, at the state's own normalisation `ρ := x^{1/2^t}` (which is a
  lower bound for the observed one, `x ≤ boxLadder (j+1) …`): the data condition
  `1 ≤ (M₁L)·(ρ·γ')^k` and the *scale* condition `γ'^k ≤ ρ`, where `γ' := D'/(M₁L)`.  The second is
  the source's hypothesis `γ' ≪_s γ^{O_s(1)}` with `γ` the observed box-norm value; without it the
  statement is refuted by the same degeneration as `ladderStepA` (`γ' = 1`, `ρ ≍ 1`, `M₁ → ∞`,
  see the reviewer's and §1's counterexamples).  Taking `k` as large as the source's exponents is
  legitimate (a larger exponent only weakens `C x^k ≤ …`, since `x ≤ 1`),


* the structural conditions of the ladder (`1 ≤ M₁`, `1 ≤ L`, **`2 ≤ L`** — the collapsed-window
  non-degeneracy, which the frozen data supply with the existential constant (`A = 8` gives
  `L = ⌊γ'M₂⌋ ≥ 7`) — `L ≤ M₁`, `1 ≤ D' ≤ M₁L`, `D' ≤ N`, `M₁L ≤ N/c`, `SupportIn f N`,
  `‖f‖_∞ ≤ 1`), and
* `0 < x ≤ 1` and **the source's data condition at the state's own normalisation**
  `ρ := x^{1/2^t}` (`t = 2^{j+1}−1+n` the level of the input state) and `γ' := D'/(M₁L)`:
  `1 ≤ (M₁L)·(ρ·γ')^k`, and
* `x ≤ boxLadder (j+1) n M₁ c (ωOf (j+1)) L D' N f`,

one has `C·x^k ≤ boxLadder j (n+s') M₁ c (ωOf j) L D' N f`.

Since the observed value `x^{1/2^t}` satisfies `x ≤ boxLadder (j+1) …`, the condition above is the
*weakest* form of the source's requirement that is still usable: the source's own
`(M₁L)(ρ_obs γ')^{O(1)} ≫ 1` follows because `ρ_obs ≥ x^{1/2^t}` and `k` may be taken as large as
the source's exponent.

## How the frozen hypotheses supply the condition

With `A` the frozen existential constant and `K ≥ 1`, one has `M₂ ≥ A(γγ')^{-K}`, hence
`M₁L ≥ γ'M₂ ≥ A γ^{1−K}γ'^{1−K}`; comparing this with `(ρ_kγ')^{-k}` at the running value
`ρ_k = x_k^{1/2^{t_k}}`, `x_k = ladderCst_k(C₁γ^K)^{ladderKexp_k}`, the `γ'`-exponent comparison
gives `K ≥ k+1`, the `γ`-exponent comparison requires `k·ladderKexp_k/t_k ≤ 1` (the running-value
obstruction), and the `C₁`-exponent is absorbed by `C₁ ≤ γ^{-K}`.  The branch on which the
`γ`-comparison fails is the *carve*: failure is the **upper** bound `M₁L < (ρ_kγ')^{-k}`, which is
exactly the input the diagonal/mass branch needs (`D' ≈ γ'·L·M₁` is then controlled). -/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse

noncomputable section

/-- **The corrected one-step statement of the concatenation ladder** (Peluse's Lemma 5.6 with the
source's data condition `M₁M₂ ≫ (γγ')^{-O(1)}` at the state's own normalisation). -/
def ladderStepB (j : ℕ) : Prop :=
  ∃ s' : ℕ, ∃ C : ℝ, ∃ k : ℕ,
    1 ≤ s' ∧ 0 < C ∧ C ≤ 1 ∧ 1 ≤ k ∧
    ∀ (c : ℤ), 0 < c → ∀ (M₁ L D' N n : ℕ) (f : ℤ → ℂ) (x : ℝ),
      1 ≤ M₁ → 1 ≤ L → 2 ≤ L → L ≤ M₁ → 1 ≤ D' → D' ≤ M₁ * L → D' ≤ N → 1 ≤ N →
      ((M₁ : ℝ) * (L : ℝ) ≤ (N : ℝ) / (c : ℝ)) →
      SupportIn f N → (∀ y : ℤ, ‖f y‖ ≤ 1) →
      0 < x → x ≤ 1 →
      1 ≤ ((M₁ : ℝ) * (L : ℝ))
            * (x ^ (1 / (2 : ℝ) ^ (2 ^ (j + 1) - 1 + n))
                * ((D' : ℝ) / ((M₁ : ℝ) * (L : ℝ)))) ^ k →
      ((D' : ℝ) / ((M₁ : ℝ) * (L : ℝ))) ^ k
          ≤ x ^ (1 / (2 : ℝ) ^ (2 ^ (j + 1) - 1 + n)) →
      x ≤ Holds.boxLadder (j + 1) n M₁ c (Holds.omegaOf (j + 1)) L D' N f →
      C * x ^ k ≤ Holds.boxLadder j (n + s') M₁ c (Holds.omegaOf j) L D' N f

/-! ## The norm form (the form the source's Lemma 5.6 actually has)

`Holds.boxLadder` averages the `2^level`-th **powers** of the box norms, and `ladderStepB` is fed
their **roots**; that conversion is what makes the norm-exponent pick up a factor
`2^{t_k}·k/t_{k+1}` per step (`NOTES_concatBridgeShortA_SESSION3.md` §9).  The source's Lemma 5.6
never does this: its hypothesis *and* its conclusion are averages of box **norms** at their own
levels, and its loss `γ^{O_s(1)}` is a power of the old *norm* with a **constant** exponent.  The
statements below are that form.

The two forms are interconvertible for `1`-bounded `f` (`0 ≤ boxNorm ≤ 1`):

* power ⟹ norm: `boxLadder ≤ boxLadderNorm` (each `u^{2^t} ≤ u` for `u ∈ [0,1]`);
* norm ⟹ power: `(boxLadderNorm)^{2^t} ≤ boxLadder` (Jensen for `x ↦ x^{2^t}`).

so the assembly can move between them per state. -/

/-- The average over `h, h' ∈ [1,M₁]^j` of the `(2^j-1+n)`-level box **norm** of `f` at the direction
sets `c((h-h')·ω)[D]` — the norm-level companion of `Holds.boxLadder`. -/
def boxLadderNorm (j n M₁ : ℕ) (c : ℤ) (ωOf : Fin (2 ^ j - 1) → (Fin j → Bool))
    (L D' N : ℕ) (f : ℤ → ℂ) : ℝ :=
  ((M₁ : ℝ))⁻¹ ^ (2 * j) *
    ∑ h : Fin j → Fin M₁, ∑ h' : Fin j → Fin M₁,
      Work.Peluse.boxNorm (2 ^ j - 1 + n) (Holds.ladderSlots j n M₁ c ωOf L D' h h')
        (Work.Peluse.symIcc N) f

/-- **The norm-form one-step statement of the concatenation ladder** (Peluse's Lemma 5.6 in its own
normalisation: averages of box *norms*, with both the data condition `M₁M₂ ≫ (γγ')^{-O(1)}` and the
scale condition `γ' ≪ γ^{O(1)}` stated at the state's own normalisation `γ`, `γ' := D'/(M₁L)`).

There are `s' ≥ 1`, `0 < C ≤ 1`, `k ≥ 1`, depending only on `j`, such that for every datum with the
ladder's structural conditions (including the collapsed-window non-degeneracy `2 ≤ L`) and

* `1 ≤ (M₁L)·(γ·γ')^k`     (the data condition, with the averaging range `M₁`),
* `γ'^k ≤ γ`               (the scale condition),
* `γ ≤ boxLadderNorm (j+1) n …`  (the state, at its own level),

one has `C·γ^k ≤ boxLadderNorm j (n+s') …`.  No level, and no root-taking, occurs: the `s`-fold
iteration multiplies the *norm* exponent by the step exponents only, so the accumulated exponent is
`∏_{i} k_i` and the source's `M₁M₂ ≫ (γγ')^{-O_s(1)}` at the top level covers the whole ladder.

**The frozen conditions are carried, verbatim.**  `A·γ' ≤ γ^K` and `A ≤ M₂(γγ')^K`, with the
threshold `max 1 (C₁^{-10^6}) ≤ A` of the assembly's choice, are hypotheses here — not derived.
`_cba/scan1.py` (see `NOTES_concatBridgeShortA_SESSION3.md` §12) shows this is *necessary*: without
them the scale-tuned chirp family refutes the statement at `K = 1` (the conclusion's ratio decays
like `M₁^{-1/2^{s'}}` while every data-level condition holds), and the admissibility of that family
is exactly `K ≤ log_A(1/C₁)` — impossible once `A ≥ C₁^{-10^6}`.  With the two frozen conditions
present the step's proof has the `A^K ≲ 1/C₁` exclusion available, and the assembly supplies both
hypotheses *verbatim from its own frozen data*, which is why the carve's data-condition content
disappears (only the non-degeneracy `2 ≤ L`, the state, and the two frozen conditions remain). -/
def ladderStepC (j : ℕ) : Prop :=
  ∃ s' : ℕ, ∃ C : ℝ, ∃ k₀ : ℕ,
    1 ≤ s' ∧ 0 < C ∧ C ≤ 1 ∧ 1 ≤ k₀ ∧
    ∀ (C₁ A : ℝ) (K M₂ : ℕ), 0 < C₁ → max 8 (C₁ ^ (-(10 ^ 6 : ℝ))) ≤ A → 1 ≤ K → 1 ≤ M₂ →
    ∀ (c : ℤ), 0 < c → ∀ (M₁ L D' N n : ℕ) (f : ℤ → ℂ) (γ : ℝ) (k : ℕ),
      k₀ ≤ k →
      1 ≤ M₁ → 1 ≤ L → 2 ≤ L → M₂ ≤ M₁ → L ≤ M₁ → 1 ≤ D' → D' ≤ M₁ * L → D' ≤ N → 1 ≤ N →
      ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ)) →
      ((M₁ : ℝ) * (L : ℝ) ≤ (N : ℝ) / (c : ℝ)) →
      SupportIn f N → (∀ y : ℤ, ‖f y‖ ≤ 1) →
      0 < γ → γ ≤ 1 →
      -- the frozen data conditions, verbatim (they are what the assembly has)
      A * ((D' : ℝ) / ((M₁ : ℝ) * (L : ℝ))) ≤ γ ^ K →
      A ≤ (M₂ : ℝ) * (γ * ((D' : ℝ) / ((M₁ : ℝ) * (L : ℝ)))) ^ K →
      -- the frozen *window* relation `L = ⌊γ'M₂⌋`: it is what ties the short window to `M₂`,
      -- and without it `L` is decoupled from the data (`NOTES…SESSION3.md` §12 and the review of
      -- `ladderStepCRedraft`)
      A ≤ (L : ℝ) * γ ^ ((K : ℝ) - 1)
            * (((D' : ℝ) / ((M₁ : ℝ) * (L : ℝ)))) ^ ((K : ℝ) - 1) →
      -- the derived data condition (implied by the frozen ones when `k ≤ K`; kept for convenience)
      1 ≤ ((M₁ : ℝ) * (L : ℝ))
            * (γ * ((D' : ℝ) / ((M₁ : ℝ) * (L : ℝ)))) ^ k →
      ((D' : ℝ) / ((M₁ : ℝ) * (L : ℝ))) ^ k ≤ γ →
      γ ≤ boxLadderNorm (j + 1) n M₁ c (Holds.omegaOf (j + 1)) L D' N f →
      C * γ ^ k ≤ boxLadderNorm j (n + s') M₁ c (Holds.omegaOf j) L D' N f

/-! ## The bookkeeping of the norm-form ladder

The assembly `concatBridgeShortA_of_ladderStepC` iterates `ladderStepC` along the levels
`j = s-1-k`.  Its running data are a **norm** and an **exponent** (no level, no root-taking — §9):

* `a_0 := 1`,  `a_{k+1} := a_k · k_k`  with  `k_k := max a_k (k₀ (s-1-k))`;
* `γ_0 := min 1 (C₁γ^K)`,  `γ_{k+1} := Cs (s-1-k) · γ_k^{k_k}`.

`k_k` is the exponent passed to the step at stage `k`: it is `≥ k₀` by construction, so the
*conditioned* interface applies, and it is `≥ a_k`, which is what makes the step's scale condition
`γ'^{k_k} ≤ γ_k` follow from the frozen `Aγ' ≤ γ^K` and `A ≥ C₁^{-10^6}` (§16). -/

/-- The accumulated ladder exponent `a_k` of the norm-form assembly. -/
def ladderA (s : ℕ) (k₀ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | (k + 1) => ladderA s k₀ k * max (ladderA s k₀ k) (k₀ (s - 1 - k))

/-- The running norm `γ_k` of the norm-form assembly. -/
def ladderGam (s : ℕ) (Cs : ℕ → ℝ) (k₀ : ℕ → ℕ) (C₁ γ : ℝ) (K : ℕ) : ℕ → ℝ
  | 0 => min 1 (C₁ * γ ^ K)
  | (k + 1) => Cs (s - 1 - k)
      * (ladderGam s Cs k₀ C₁ γ K k) ^ (max (ladderA s k₀ k) (k₀ (s - 1 - k)))

lemma ladderA_zero (s : ℕ) (k₀ : ℕ → ℕ) : ladderA s k₀ 0 = 1 := rfl

lemma ladderA_succ (s k : ℕ) (k₀ : ℕ → ℕ) :
    ladderA s k₀ (k + 1) = ladderA s k₀ k * max (ladderA s k₀ k) (k₀ (s - 1 - k)) := rfl

lemma ladderGam_zero (s : ℕ) (Cs : ℕ → ℝ) (k₀ : ℕ → ℕ) (C₁ γ : ℝ) (K : ℕ) :
    ladderGam s Cs k₀ C₁ γ K 0 = min 1 (C₁ * γ ^ K) := rfl

lemma ladderGam_succ (s k : ℕ) (Cs : ℕ → ℝ) (k₀ : ℕ → ℕ) (C₁ γ : ℝ) (K : ℕ) :
    ladderGam s Cs k₀ C₁ γ K (k + 1) = Cs (s - 1 - k)
      * (ladderGam s Cs k₀ C₁ γ K k) ^ (max (ladderA s k₀ k) (k₀ (s - 1 - k))) := rfl

lemma ladderA_pos (s : ℕ) (k₀ : ℕ → ℕ) : ∀ k, 1 ≤ ladderA s k₀ k
  | 0 => le_refl 1
  | (k + 1) => by
      rw [ladderA_succ]
      exact one_le_mul (ladderA_pos s k₀ k)
        (le_trans (ladderA_pos s k₀ k) (le_max_left _ _))

end

end Work.Peluse
