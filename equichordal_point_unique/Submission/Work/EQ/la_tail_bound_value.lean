import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.charVal_props
import Submission.Work.EQ.charVal_set
import Submission.Work.EQ.la_nnas
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.H0_tail_bounded
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.germC_snd_deriv
import Submission.Work.EQ.fan_sep
import Submission.Work.EQ.charVal_main
import Submission.Work.EQ.H0_fibre_defs
import Submission.Work.EQ.chainWord_eventually_true_pos
import Submission.Work.EQ.FanTri.Base
import Submission.Work.EQ.FanTri.fan_split2
import Submission.Work.EQ.FanTri.fan_decay
import Submission.Work.EQ.LaTB.la_fan_trichotomy
import Submission.Work.EQ.LaTB.la_fan_trichotomy_v2
import Submission.Work.EQ.LaTB.flattening_impossible
import Submission.Work.EQ.LaTB.flattening_impossible_bwd
import Submission.Work.EQ.LaTB.isChainWord_append_true
import Submission.Work.EQ.LaTB.exists_level_uniform

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped Topology

noncomputable section

/-! # `Work.EQ.la_tail_bound_value`

Rychlik's Theorem 8(3) for a fixed value, uniformly over all the regular components of that
value: over an annulus `Ann r₁ r₂` of ratio `> 1/λ` inside a small ball, the tail indices of all
the chains of all the regular components with value `c` are uniformly bounded, provided `c` has
no *descendant* regular value `c * μ₁ * μ₂` with `(μ₁, μ₂) ≠ (1,1)` in `CharSet a h`.

This file contains (a) the elementary bookkeeping (the shifted tail conditions, the minimal word
of a chain, a subsequence lemma), and (b) the assembly `ltbv_main`, which takes the analytic
pieces as hypotheses.  The pieces are provided by companion files under `Submission/Work/EQ/LaTB/`:

* `LaTB.la_fan_trichotomy_v2` — the fan trichotomy with case (i) = *literally constant* words,
  case (ii) = `ε₀ ++ true^(s k) ++ C k` with `charVal (C k) = μ₁ ∈ (0,1]`, case (iii) = the
  shrinking fan;
* `LaTB.flattening_impossible`, `LaTB.flattening_impossible_bwd` — case (iii) is impossible
  (Rychlik's omitted step: `no_near_axis_segment` across the segment);
* `LaTB.case_i_words_bounded` — case (i) bounds the words whose fan map agrees with a fixed
  `fan ε₀` on a disc and whose length is the chain's tail index;
* `LaTB.case_ii_reflection_le` — case (ii) produces a regular component with value `c₀ * μ₁ * μ₂`
  (the descendant value);
* `LaTB.isChainWord_append_true` — a chain word can be extended by stationary letters beyond the
  tail index (this is how the case-(i) alternative is fed into the case-(ii) interface);
* `LaTB.exists_level_uniform` — one common reading level `N` for the whole sequence.

The argument (Rychlik's Lemma 5.1): if the tail indices over the annulus were unbounded, the
minimal reading words of the chains have unbounded length, and the trichotomy puts them in case
(i) (bounded, contradiction), case (iii) (impossible), or case (ii) (which produces a descendant
regular value, contradicting the hypothesis).  The hypotheses supply the two parameters
`ψ₁ (q k) ∈ Ann r₁ r₂` and `λ^N ψ₂ (q k) ∈ Ann r₁ r₂` at the two reading levels `0` and `-N`;
the level `N` exists for the whole sequence by `LaTB.exists_level_uniform`, because
`ρ* ≤ ‖ψ₁ ψ₂‖` keeps `‖ψ₂‖` above `r₁` inside the annulus (this is why the square root of the
`H0_invParam_ge` constant is taken in `δ`). -/

/-! ## UPDATE (session 4): the correct shape of the remaining gap and the route

`ltbv_main` and everything below are unchanged and still proved.  The single `sorry` is `href` in
`la_tail_bound_value`.  What session 4 established (read `Submission/Work/EQ/LTBV_NOTES.md` and the
module notes of `Submission/Work/EQ/LTBV/` for the full account):

* `Work.EQ.LTBV.transfer` and `Work.EQ.LTBV.junction_regComp` ARE proved (real proofs), and
  `Work.EQ.LTBV.matched_annulus` as well.
* `Work.EQ.LTBV.reflection_open` is **vacuous**, hence useless: it proves its statement by showing
  that its hypotheses (with one *common* smallness scale `ρ` for `‖ψ₁‖` and `‖λ^N ψ₂‖`) are
  unsatisfiable above the threshold `ρ = √(λ^N ρ*)` — see its `no_data_of_small_rho` — so its
  conclusion is asserted nowhere.  Do not use it.
* **The obstruction.**  The level-`0`-side function `ζ ↦ bwdP a s (fan a h ε₀ ζ)` is analytic only
  where all the intermediate fan *parameters* are small: `Work.EQ.bwdP a l (Work.EQ.fan a h ε u) =
  Work.EQ.fan a h (l.reverse ++ ε) (u/λ^{|l|})` amplifies the parameter by `λ^{-|l|}`
  (`Work.EQ.exists_slitPlane_bwdP_fan`, `Work.EQ.analyticOnNhd_bwdP`), so on an annulus of scale
  `≫ λ^N` its analyticity *cannot* be obtained from the workspace's estimates unless the *value* is
  small compared with the annulus.  This is why every earlier statement of a reflection lemma on an
  arbitrary annulus was declared false or became vacuous.
* **The route that works** avoids that description: parametrise the *middle* from the far end
  *by forward branches*, so that the only fans involved have small arguments.  Concretely, the gap
  is now split into two delegated lemmas (files under `Submission/Work/EQ/LTBV/`):
  1. `Work.EQ.LTBV.limit_point_junction` — the case-(ii) reading data (values `c k → c₀`, chains of
     regular components over the annulus, the two long-true-run readings) produces a *point*
     `ζ₀ ≠ 0` and a sign list `s'` of length `N` with the junction identity
     `bwdP a s' (fan a h ε₀ ζ₀) = eqMirror (fan a h η₀ (λ^N * ((c₀ μ₁ μ₂) / ζ₀)))`,
     by `tb_fan_run_limit` on both ends plus closedness of the `N`-step relation
     (`bwdP_bwdWord_take`).  The sign list need not be constant (letters flip across the cut).
  2. `Work.EQ.LTBV.point_junction_regComp` — that junction identity *at one point*, i.e.
     `IsChain a h (candChain a h ε₀ η₀ s' N C ζ₀)` for `C = c₀ μ₁ μ₂`, already yields
     `∃ T, IsRegComp a h T C`.  Proof: define the family by parametrising the middle from the far
     end (far point `eqMirror (fan η₀ (λ^N C/ζ))`, then *forward* branches `fwdC`/`fwdAlt` up to
     level `0`, then the `ε₀`-fan), analytic on the radicand-nonzero set; the level-`0` point of
     that family and `fan a h ε₀ ζ` are analytic near `ζ₀` and agree at `ζ₀`, so they agree on the
     connected component, where the family is a genuine family of chains with `ψ₁ = ζ`, `ψ₂ = C/ζ`;
     `Work.EQ.exists_regular_of_family` finishes.

  Then `href` follows: from the `href` data (which uses `IsChainWord` at the reading depth, hence
  the plain readings of `limit_point_junction` plus `ψ₁ ≠ 0` and the two annulus conditions) get
  `ζ₀`, `s'`; pass from the point junction to `IsChain (candChain …)` — this is the *seam* pair,
  all other consecutive pairs of `candChain` being automatically regular given the smallness — and
  apply `point_junction_regComp` with the *given* `μ₁, μ₂`, whose non-triviality
  `(μ₁ ≠ 1 ∨ μ₂ ≠ 1)` is supplied by the caller `ltbv_main`.  Note that with the *matching*
  `λ^N ‖c‖ = r₁ r₂` of the given annulus both smallness hypotheses of `point_junction_regComp` hold
  at scale `r₂`, which is why the matched-annulus bookkeeping (`matched_annulus`, `transfer`) is
  available if a scale-free form should be wanted instead.
- Everything else in `ltbv_main` (the trichotomy, the four-way case analysis, the `hci` handling of
  the `μ₁ = μ₂ = 1` branch, `exists_level_uniform`) is proved and untouched.

### Verdicts on the two delegated pieces (both came back MIS-STATED, with reasons — read them)

* `Work.EQ.LTBV.point_junction_regComp` (the pointwise junction ⇒ descendant): the prover showed the
  hypothesis is strictly weaker than what the consumers can use, and the analytic-family route is
  not available in the workspace.  Two concrete obstructions:
  (a) the intermediate points of `Work.EQ.bwdP a (s.take k) (fan a h ε₀ ζ₀)` are *not* known to
      keep their radicands off the branch cut of `z ↦ z^(1/2)`: `Work.EQ.fwdC`/`Work.EQ.fwdAlt`
      (and `invBranch`) are analytic only off the cut, so the forward recursion from the far end
      cannot be continued analytically past a cut crossing;
  (b) consequently the identity-principle upgrade from the single parameter `ζ₀` to a component is
      not valid with the tools at hand.
* `Work.EQ.LTBV.limit_point_junction` (the case-(ii) readings ⇒ the point junction): the prover
  disproved the *documented* route: the union `R_N = ⋃_{|s| = N} graph (bwdP a s)` is **not
  closed** (Lean-checked counterexample, `a = 1/2`: `Q k = (O₁.1 + 1/k, 0) → O₁` with
  `invBranch a true Q k → (5/4, 0) ≠ O₂ = bwdP a true O₁`; the labelled limit leaves the union of
  the graphs).  Hence a limit of labelled chains is a labelled chain only when the limit point is
  *non-degenerate* (no intermediate backward image equal to `O₁`), and
  `Work.EQ.bwdP_fan_degenerate_countable` only says the degenerate parameters of a fixed word form
  a *countable* set.

### What this means for the gap (session 4 conclusion)

The reflection must be produced from an **uncountable** input, not from a point or a single sequence:
the bad (degenerate) configurations form only a countable set, and Rychlik's `(135)–(136)` argument
uses exactly that — an open set (equivalently an uncountable set) of parameters where the labelled
relation holds, so that the exceptional set `B_N` can be discarded.  Two proved producers exist in
the workspace:

* `Work.EQ.H0_junction_value_of_cluster` (`Submission/Work/EQ/H0_junction_value_of_cluster.lean`):
  from an *uncountable* cluster set `Z` with chains `X z k ∈ H0`, `ψ₁ (X z k) → z`,
  `ψ (X z k) → c₀`, it produces words `ε, η, s`, a depth `N` and `μ₁, μ₂ ∈ CharSet` such that the
  junction set `{w : ‖w‖ < δ ∧ ‖λ^N (μ₁μ₂c₀/w)‖ < δ ∧ bwdP a s (fan ε w) =
  eqMirror (fan η (λ^N (μ₁μ₂c₀/w)))}` is uncountable.  It is *unpinned*: `μ₁, μ₂` are the ones its
  own trichotomy finds, and the degenerate parameters are removed by countability, so it is exactly
  the "uncountable junction set" input.
* `Work.EQ.H0_branch_counting_uniform` (`Submission/Work/EQ/H0_branch_counting_uniform.lean`):
  an uncountable junction set `Z ⊆ Ann r₁ r₂` for a fixed datum plus the analyticity hypothesis
  `hana` (∃ open `U ⊇ Z` with `AnalyticAt` and nonvanishing radicands for all partial `bwdP`'s)
  yields `∃ p ∈ H0, ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = C`.
* `Work.EQ.LTBV.junction_regComp` is the same conclusion from a junction identity on an open
  connected set.

So the natural next target is a *pinned* version of the cluster lemma: the same conclusion as
`H0_junction_value_of_cluster` but with `μ₁, μ₂` *given* by the caller's case-(ii) data (that is
what `href` provides), together with the `hana`-type analyticity, and then
`H0_branch_counting_uniform` finishes.  The remaining production problem is the *uncountable cluster
set* in the `href` setting: the chains `q k` give one sequence; the uncountable family has to come
from the local sections of the components `S k` (via `H0_structure`, whose sections give an open —
hence uncountable — set of parameters for each `k`), which is precisely the missing link.  Note also
that with the *matching* `λ^N‖c‖ = r₁r₂` the smallness conditions of both producers collapse to
`r₂ < δ`, so the matched-annulus bookkeeping (`matched_annulus`, `transfer`) is the right scale.
-/

/-! ## The multiplier -/

lemma ltbv_lam_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]; exact div_pos (by linarith) (by linarith)

lemma ltbv_lam_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]; linarith

lemma ltbv_lamC_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ((eqLam a : ℝ) : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_zero, ne_eq, Complex.ofReal_inj]
  exact ne_of_gt (ltbv_lam_pos ha0 ha1)

/-- The principal axis point `A₁ = (-1/2, 0)`. -/
abbrev ltbvA1 : ℂ × ℂ := ((-1 / 2 : ℂ), (0 : ℂ))

/-- `charVal a h [] = 1`: the empty word has characteristic value `1` (its second coordinate
*is* the stable germ's, so the ratio of the derivatives is `1`). -/
theorem ltbv_charVal_nil {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) : charVal a h [] = 1 := by
  have hd : deriv (fun u => (germC a h u).2) 0 ≠ 0 := by
    rw [germC_snd_deriv ha0 ha1 hh]
    have h1 : (0 : ℝ) < (1 - a) / 2 := by linarith
    exact_mod_cast (ne_of_gt h1)
  have hfun : (fun u => (fan a h [] u).2) = fun u => (germC a h u).2 := by
    funext u; rw [fan_nil]
  rw [charVal, hfun]
  exact div_self hd

/-- `fan a h [] 0 = A₁`: the empty word is centred at `A₁`. -/
theorem ltbv_fan_nil_centre {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) : fan a h [] 0 = ltbvA1 := by
  obtain ⟨ρ, hρ, -, hg0, -, -, -⟩ := germC_facts ha0 ha1 hh
  rw [fan_nil]
  exact hg0

/-! ## The backward tail condition -/

/-- `bwdTailP a h q M`: from the index `-M` on, the chain datum `q` follows the principal
unstable leaf, `q.1 (-n) = ugermC a h (λⁿ ψ₂ q)`. -/
def bwdTailP (a : ℝ) (h : ℂ → ℂ) (q : ChainData) (M : ℕ) : Prop :=
  ∀ k : ℕ, M ≤ k → q.1 (-(k : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ k * q.2.2)

theorem ltbv_bwdTailP_iff {a : ℝ} {h : ℂ → ℂ} (q : ChainData) (M : ℕ) :
    bwdTailP a h q M ↔ TailP a h (mirrorChain q) M := by
  constructor
  · intro h k hk
    rw [mirrorChain_fst, mirrorChain_psi1]
    rw [h k hk]
    simp [ugermC, eqMirror]
  · intro h k hk
    have h1 := h k hk
    rw [mirrorChain_fst, mirrorChain_psi1] at h1
    have h2 := congrArg eqMirror h1
    simpa [ugermC, eqMirror] using h2

/-! ## The minimal reading word of a chain -/

/-- **The minimal word of a chain.**  Every chain has a word whose letters are the labels of its
steps from index `0`, of length exactly its tail index, and the chain equals the fan value of
that word at `ψ₁`. -/
theorem ltbv_minimal_word {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {q : ChainData}
    (hq : IsChain a h q) :
    ∃ ε : List Bool, IsChainWord a h q (tailIdx a h q) ε ∧ ε.length = tailIdx a h q ∧
      q.1 0 = fan a h ε q.2.1 ∧
      (∀ n : ℕ, tailIdx a h q ≤ n →
        q.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.1)) := by
  obtain ⟨ε, hε⟩ := exists_isChainWord ha0 ha1 (tailIdx a h q) q hq
    (fun n hn => (tailIdx_le_iff (tailP_of_isChain hq)).mp le_rfl n hn)
  exact ⟨ε, hε, hε.1, hε.2.1, fun n hn => (tailIdx_le_iff (tailP_of_isChain hq)).mp le_rfl n hn⟩

/-! ## The shift -/

/-- **`TailP` under the integer shift.** -/
theorem ltbv_tailP_shiftZ {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    (p : ChainData) (N M : ℕ) :
    TailP a h (shiftZ a (N : ℤ) p) M ↔ TailP a h p (M + N) := by
  have hne : ((eqLam a : ℝ) : ℂ) ≠ 0 := ltbv_lamC_ne_zero ha0 ha1
  constructor
  · intro hM n hn
    have hn' : M ≤ n - N := by omega
    have h1 := hM (n - N) hn'
    rw [shiftZ_fst, shiftZ_psi1] at h1
    have h2 : (((n - N : ℕ) : ℤ) + (N : ℤ)) = ((n : ℕ) : ℤ) := by omega
    rw [h2] at h1
    rw [h1]
    congr 1
    rw [← zpow_natCast (n := n - N), ← mul_assoc, ← zpow_add₀ hne, h2, zpow_natCast]
  · intro hM n hn
    have h1 := hM (n + N) (by omega)
    rw [shiftZ_fst, shiftZ_psi1]
    have h2 : ((n : ℤ) + (N : ℤ)) = ((n + N : ℕ) : ℤ) := by push_cast; ring
    rw [h2, h1]
    congr 1
    rw [zpow_natCast, ← mul_assoc, ← pow_add]

/-- The tail index grows by at most `N` when the chain is shifted by `σ^N`. -/
theorem ltbv_tailIdx_le_shiftZ {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {p : ChainData} (hp : IsChain a h p) (N : ℕ) :
    tailIdx a h p ≤ tailIdx a h (shiftZ a (N : ℤ) p) + N := by
  have hq : IsChain a h (shiftZ a (N : ℤ) p) := isChain_shiftZ ha0 ha1 hp (N : ℤ)
  refine tailIdx_le (tailP_of_isChain hp) ?_
  exact (ltbv_tailP_shiftZ ha0 ha1 p N (tailIdx a h (shiftZ a (N : ℤ) p))).mp
    (TailP_tailIdx (tailP_of_isChain hq))

/-! ## Unbounded sequences have a subsequence tending to infinity -/

theorem ltbv_subseq_atTop (f : ℕ → ℕ) (h : ¬ ∃ B : ℕ, ∀ k, f k ≤ B) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun k => f (ψ k)) atTop atTop := by
  have hex : ∀ N n : ℕ, ∃ k, n < k ∧ N ≤ f k := by
    intro N n
    by_contra hcon
    push_neg at hcon
    refine h ⟨max N ((Finset.range (n + 1)).sup f), fun k => ?_⟩
    by_cases hk : k ≤ n
    · exact le_trans (Finset.le_sup (f := f) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
        (le_max_right _ _)
    · exact le_trans (le_of_lt (hcon k (by omega))) (le_max_left _ _)
  choose g hg1 hg2 using hex
  let ψ : ℕ → ℕ := fun n => Nat.rec (g 0 0) (fun m p => g (m + 1) p) n
  have hψstep : ∀ n, ψ n < ψ (n + 1) := by
    intro n
    dsimp only [ψ]
    exact hg1 (n + 1) (ψ n)
  have hψf : ∀ n, n ≤ f (ψ n) := by
    intro n
    cases n with
    | zero => dsimp only [ψ]; exact hg2 0 0
    | succ m => dsimp only [ψ]; exact hg2 (m + 1) (ψ m)
  refine ⟨ψ, strictMono_nat_of_lt_succ hψstep, ?_⟩
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨b, fun n hn => le_trans hn (hψf n)⟩


open Complex Filter _root_.Topology
open scoped Topology

/-! ## Assembly helpers -/

/-- Membership in the closed annulus, unpacked. -/
lemma ltbv_mem_Ann {r₁ r₂ : ℝ} {z : ℂ} (h : z ∈ Ann r₁ r₂) : r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ := h

@[simp] lemma ltbv_eqMirror_invol' (P : ℂ × ℂ) : eqMirror (eqMirror P) = P := by
  simp [eqMirror]

lemma ltbv_shiftZ_mirror_fst (a : ℝ) (j : ℤ) (p : ChainData) :
    (shiftZ a j (mirrorChain p)).1 0 = eqMirror (p.1 (-j)) := by
  rw [shiftZ_fst, mirrorChain_fst, zero_add]

/-- The reading of a chain at the negative level `-N`, read through the shifted mirror chain. -/
lemma ltbv_bwd_eq_of_isChainWord {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    (q : ChainData) (N : ℕ) (ηw : List Bool)
    (hw : IsChainWord a h (shiftZ a (N : ℤ) (mirrorChain q)) ηw.length ηw) :
    q.1 (-(N : ℤ)) = eqMirror (fan a h ηw (((eqLam a : ℝ) : ℂ) ^ (N : ℤ) * q.2.2)) := by
  have h1 := hw.2.1
  rw [ltbv_shiftZ_mirror_fst, shiftZ_psi1, mirrorChain_psi1] at h1
  have h2 := congrArg eqMirror h1
  rw [ltbv_eqMirror_invol'] at h2
  exact h2

/-- A word whose suffix is already the germ, prefixed by `ε₀` and a run of principal steps,
agrees with `fan ε₀` near `0`. -/
lemma ltbv_eqOn_of_germ_tail {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {δ : ℝ}
    {C : List Bool} (hgerm : Set.EqOn (fan a h C) (germC a h) (Metric.ball 0 δ))
    (hinv : ∀ u : ℂ, u ∈ Metric.ball 0 δ →
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u)
    (ε₀ : List Bool) (n : ℕ) :
    Set.EqOn (fan a h (ε₀ ++ List.replicate n true ++ C)) (fan a h ε₀) (Metric.ball 0 δ) := by
  have htail : Set.EqOn (fan a h (List.replicate n true ++ C)) (germC a h) (Metric.ball 0 δ) :=
    LaTB.fan_true_prepend_eq_germ ha0 ha1 hgerm hinv n
  have hmain : Set.EqOn (fan a h (ε₀ ++ (List.replicate n true ++ C))) (fan a h ε₀)
      (Metric.ball 0 δ) :=
    LaTB.fan_prepend_eq_of_germ ha0 ha1 (w := List.replicate n true ++ C) htail ε₀
  simpa [List.append_assoc] using hmain

/-! ## State of this file and the one remaining gap (2026-09-26)

**Proved and `sorry`-free here:**

* `ltbv_main` — the whole trichotomy assembly of Rychlik's Lemma 5.1, with the analytic pieces as
  hypotheses; its conclusion is *exactly* the statement of `Work.EQ.la_tail_bound_value`.
  The proof is in the file (witness extraction, the shift of the tail index, the `hlvl` level, the
  minimal words, both trichotomy applications and the four-way case analysis).
* the bookkeeping: `ltbv_minimal_word`, `ltbv_tailP_shiftZ`, `ltbv_tailIdx_le_shiftZ`,
  `ltbv_bwdTailP_iff`, `ltbv_charVal_nil`, `ltbv_fan_nil_centre`, plus helpers.

**Proved pieces it consumes (modules of `Submission/Work/EQ/LaTB/`):**

* `LaTB.la_fan_trichotomy_v2` — case (i) is literally constant words, case (ii) allows
  `charVal = 1`, case (iii) is the shrinking fan;
* `LaTB.flattening_impossible`, `LaTB.flattening_impossible_bwd` — case (iii) is impossible;
* `LaTB.case_i_words_bounded` — case (i) bounds the minimal words;
* `LaTB.isChainWord_append_true` — a chain word can be padded by principal letters;
* `LaTB.exists_level_uniform` — one common reading level for a whole sequence.

**The one remaining gap.**  `href` in the proof of `la_tail_bound_value` below is the case-(ii)
"reflection": from the case-(ii) reading data of a sequence of chains of *regular* components of
values `c k → c₀` over an annulus, produce a regular component of value `c₀ * μ₁ * μ₂`.
Everything else in Rychlik's Lemma 5.1 is done.  Its shape is the *corrected* one: it produces an
absolute smallness radius `δs` (`r₂ < δs`, added to the min defining the `δ` of the conclusion)
and it assumes `0 < N`.  Both are what the source's step (136) uses ("`δ` must be small enough so
that the conclusion of Lemma 14 holds and `δ < δ₀`, where `δ₀` is given by Thm 7"), and `0 < N` is
*derivable* inside `ltbv_main` from the two annulus conditions at level `0`, because
`N = 0` would give `‖c‖ ≤ r₂² < ρ ≤ ‖c‖` (using `r₂ < δ ≤ √ρ` and `H0_invParam_ge`).  The matching
statement is delegated as `Submission/Work/EQ/LaTB/case_ii_reflection_small`.

**Status of that gap (2026-09-26, after the third attempt).**  The delegate declared it
mis-stated/under-hypothesised again (`declared FALSE`, judgment only, no counterexample) with the
following substantive point, which supersedes the earlier "the annulus must be scaled-small"
objections and should be read as the real content of the gap:

* every route to `∃ T, IsRegComp a h T (c₀μ₁μ₂)` goes through the *candidate family*
  `m ζ : ψ₁ = ζ, ψ₂ = C/ζ`, `C = c₀μ₁μ₂`, together with the junction identity
  `(J)  bwdP a s (fan a h ε₀ ζ) = eqMirror (fan a h η₀ (λ^N C / ζ))`
  on an open set `U`;
* the *left* side of `(J)` is the one that obstructs analyticity on the annulus:
  `bwdP a (s.take j) (fan a h ε₀ ζ) = fan a h ((s.take j).reverse ++ ε₀) (ζ / λ^j)`
  (`Work.EQ.bwdP_fan_eq_fan`), whose deepest parameter is `ζ/λ^N ≥ r₁/λ^N`;
* parametrising the *same* points from the level `-N` end (via `shiftZ a N (mirrorChain ·)`)
  *does* give small parameters — at the level `-N + k` point the parameter is
  `λ^{k+N}‖ψ₂‖ ≤ λ^N ‖C‖/r₁ ≈ r₂ < δ` — so the *family* (with its middle taken from the `-N`
  end) is analytic by `fan_estimates`; but the junction is exactly the statement that this
  "from the `-N` end" description and the "from the level `0` end" description agree, and it is
  the *level-`0`-side* function `bwdP a s (fan ε₀ ·)` whose analyticity on the annulus is needed
  to run the identity theorem.  That analyticity is Rychlik's "maximal annulus
  `A(r₁⁽ⁿ⁾,r₂⁽ⁿ⁾) ⊆ A` on which the left-hand side is defined" and meromorphic continuation
  (`refs/rychlik.txt` (135)-(136)) — the piece that is *not* in this workspace.

Concrete sub-lemmas that would build it, in increasing order of difficulty (all with fixed data
`ε₀, η₀, s, N, C` and a small annulus):
1. **(provable now)** the *limit* junction: if `(X k, Y k) ∈ R_N` (`X k = bwdP a s_k Y k`,
   `s_k` of length `N`) and `X k → X`, `Y k → Y` with the intermediate points of `Y` off the
   branch cut, then `X = bwdP a s Y` for some `s` of length `N` (`R_N` is closed; finitely many
   sign lists).  Combined with `Work.EQ.tb_fan_run_limit` this gives `(J)` at the limit parameter
   `ζ₀` (and hence, with the rescalings `ζ ↦ μ₁ζ`, the descendant curve through one point).
2. **(provable now)** the analyticity, on the small annulus, of the candidate chain whose middle
   is taken from the level `-N` end (all fan parameters `≤ λ^N‖C‖/r₁ < δ`): a `def` of that
   family plus `AnalyticOnNhd` for each coordinate (`fan_estimates` + composition).
3. **(the hard core)** the identity theorem/maximal-annulus step: `(J)` on an open set implies
   `(J)` on the whole annulus (or at least on an uncountable set), which is what
   `Work.EQ.exists_regular_of_readable` consumes.  Its difficulty is that the level-`0`-side
   function `bwdP a s (fan ε₀ ·)` is analytic only where the intermediate points avoid the
   isotropic lines through `O₁`, and one must show that this holds on (a dense/uncountable part
   of) the annulus for the limit data.

What is known about this gap (collected here so that it need not be rediscovered):

1. The **local mechanism** is already in the workspace: `Work.EQ.tb_fan_run_limit`
   (`Submission/Work/EQ/tb_fan_run.lean`, `sorry`-free) gives, quantitatively and uniformly in the
   trailing word `C`, `fan (ε₀ ++ true^j ++ C) u → fan ε₀ (μ u)` with `μ = charVal a h C` when
   `fan C 0 = A₁` and `‖μ‖ ≤ 1`.  This is precisely the "run of principal letters acts as the
   identity, the return word acts by its characteristic value" statement.
2. The **last mile** is already in the workspace: `Work.EQ.exists_regular_of_readable`
   (`Submission/Work/EQ/H0_reg_wset.lean`, `sorry`-free) turns the *uncountability* of the
   junction set
   `Z = {z | r₁ ≤ ‖z‖ ≤ r₂ ∧ ∃ s, s.length = N ∧
        bwdP a s (fan a h ε z) = eqMirror (fan a h η (λ^N (C/z)))}`
   into a regular component of value `C`.  Its hypotheses are `r₂ < δ₀` and `‖C‖/r₁ ≤ δ₀` with
   `δ₀ ~ min(δ_fan, ρ_germ) · λ^N / 2`, i.e. the annulus must be *scaled-small* relative to the
   level `N` (this is the reason the earlier statement of the reflection step on disk was declared
   false: the raw case-(ii) data only gives `r₂ < r`).
3. So the missing ingredient is exactly: *case (ii) ⟹ the junction set `Z` for the descendant
   value `C = c₀ * μ₁ * μ₂` is uncountable*.  The intended route (Rychlik (135)–(136)) is: for each
   `k` the chain `q k` gives the junction (an exact identity, see `Work.EQ.junction` /
   `bwdP_bwdWord_take` in `Submission/Work/EQ/limit_analysis.lean`), the pairs
   `(q k .1 0, q k .1 (-N))` lie in the closed "`N`-step relation" `R_N` (i.e.
   `X = bwdP a s Y` for some `s` of length `N`), and `tb_fan_run_limit` shows that after the
   rescaling `z ↦ μ₁ z` these pairs converge to the pairs of the *descendant* curve
   `z ↦ (fan ε₀ (μ₁ z), eqMirror (fan η₀ (λ^N μ₂ c₀ / z)))`.  Since `R_N` is a closed analytic
   subset of `ℂ²` (a finite union of graphs of analytic maps) and this curve is analytic, the set
   of `z` where the relation holds is analytic in the annulus, and Rychlik's meromorphic
   continuation (an instance of the 1-dimensional structure theorem for analytic sets: a closed
   analytic subset of a domain is either discrete or the whole domain) upgrades "one point" to
   "the whole annulus".
   The obstacles are (a) the analyticity of `z ↦ bwdP a s (fan ε₀ z)` on the *large* annulus
   (`Work.EQ.analyticOnNhd_bwdP` needs the intermediate radicands off the branch cut; the crude
   sufficient condition "the initial parameter is `< δ λ^N`" is what forces the `λ^N` in
   `exists_regular_of_readable`), and (b) ruling out the "discrete" alternative.
4. Two structural facts that a future proof should exploit:
   * the depth-`M` reading of a chain is *locally constant* along the `ψ₁`-sections of `H0`
     (`Work.EQ.H0_structure`), hence constant on every connected component of `H0`; therefore the
     **tail index is constant on every connected component of `H0`**, and the conclusion of
     `la_tail_bound_value` is equivalent to "the set of regular components of value `c` meeting
     `Ann r₁ r₂` is finite";
   * `Work.EQ.chain_eq_candChain_of_reading` (candidate chains with bounded tails) and
     `Work.EQ.exists_regular_of_candChain` are the other two entry points to "regular component of
     a prescribed value".
-/

/-! ## The assembly interface -/

/-- **The trichotomy assembly of Rychlik's Lemma 5.1, with the analytic pieces as hypotheses.**
Its conclusion is exactly the statement of `Work.EQ.la_tail_bound_value`; the hypotheses are the
pieces of `Submission/Work/EQ/LaTB/`. -/
theorem ltbv_main {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r)
    (htri : ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℕ → List Bool, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ ε₀ : List Bool, ∀ k, ε (φ k) = ε₀) ∨
       (∃ (ε₀ ε₁ : List Bool) (s : ℕ → ℕ) (C : ℕ → List Bool),
          Tendsto s atTop atTop ∧
          (∀ k, ε (φ k) = ε₀ ++ List.replicate (s k) true ++ C k) ∧
          (∀ k, fan a h (C k) 0 = ltbvA1 ∧ charVal a h (C k) = charVal a h ε₁) ∧
          fan a h ε₁ 0 = ltbvA1 ∧ (charVal a h ε₁).im = 0 ∧ 0 < (charVal a h ε₁).re ∧
          (charVal a h ε₁).re ≤ 1) ∨
       ((∀ n : ℕ, ∀ᶠ k in atTop, n ≤ nonA1Count a h (ε (φ k))) ∧
          ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ u ∈ Metric.ball (0 : ℂ) δ,
            ‖(fan a h (ε (φ k)) u).1 - (fan a h (ε (φ k)) 0).1‖ < η ∧
            ‖(fan a h (ε (φ k)) u).2‖ < η *
              ‖(fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ)‖)))
    (hflatF : ∃ δres : ℝ, 0 < δres ∧ ∀ (r₁ r₂ : ℝ) (c₀ : ℂ),
      0 < r₁ → r₁ < r₂ → r₂ < δres → 1 / eqLam a < r₂ / r₁ →
      ∃ η : ℝ, 0 < η ∧ ∀ (q : ChainData), q ∈ H0 a h → q.2.1 ∈ Ann r₁ r₂ → q.2.1 * q.2.2 = c₀ →
        ∀ ε : List Bool, q.1 0 = fan a h ε q.2.1 →
        ¬ (‖(fan a h ε q.2.1).1 - (fan a h ε 0).1‖ < η ∧
           ‖(fan a h ε q.2.1).2‖ < η *
             ‖(fan a h ε q.2.1).1 - ((a / 2 : ℝ) : ℂ)‖))
    (hflatB : ∃ δres : ℝ, 0 < δres ∧ ∀ (r₁ r₂ : ℝ) (c₀ : ℂ),
      0 < r₁ → r₁ < r₂ → r₂ < δres → 1 / eqLam a < r₂ / r₁ →
      ∃ η : ℝ, 0 < η ∧ ∀ (q : ChainData) (l : ℤ) (η' : List Bool), q ∈ H0 a h →
        q.2.1 ∈ Ann r₁ r₂ → q.2.1 * q.2.2 = c₀ →
        r₁ ≤ (eqLam a) ^ l * ‖q.2.2‖ → (eqLam a) ^ l * ‖q.2.2‖ ≤ r₂ →
        q.1 (-l) = eqMirror (fan a h η' (((eqLam a : ℝ) : ℂ) ^ l * q.2.2)) →
        ¬ (‖(fan a h η' (((eqLam a : ℝ) : ℂ) ^ l * q.2.2)).1 -
              (fan a h η' 0).1‖ < η ∧
           ‖(fan a h η' (((eqLam a : ℝ) : ℂ) ^ l * q.2.2)).2‖ <
             η * ‖(fan a h η' (((eqLam a : ℝ) : ℂ) ^ l * q.2.2)).1 -
                   ((a / 2 : ℝ) : ℂ)‖))
    (hci : ∃ δfan : ℝ, 0 < δfan ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ δfan → ∀ {ε₀ : List Bool},
      ∃ M : ℕ, ∀ (q : ChainData) (ε : List Bool), IsChain a h q → ‖q.2.1‖ < δ →
        q.1 0 = fan a h ε q.2.1 → tailIdx a h q = ε.length →
        Set.EqOn (fan a h ε) (fan a h ε₀) (Metric.ball 0 δ) → ε.length ≤ M)
    (hpad : ∀ {p : ChainData} {N : ℕ} {ε : List Bool} {ρg : ℝ}
      (_hp : IsChain a h p) (_hw : IsChainWord a h p N ε)
      (_hN : ∀ n : ℕ, N ≤ n → p.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.1))
      (_hstep : ∀ u : ℂ, ‖u‖ < ρg →
        invBranch a true (germC a h (((eqLam a : ℝ) : ℂ) * u)) = germC a h u)
      (_hsmall : ‖p.2.1‖ < ρg) (t : ℕ),
      IsChainWord a h p (N + t) (ε ++ List.replicate t true))
    (hlvl : ∀ (r₁ r₂ : ℝ), 0 < r₁ → r₁ < r₂ → 1 / eqLam a < r₂ / r₁ → ∀ (t : ℕ → ℝ),
      (∀ k, r₁ ≤ t k) → (∃ B : ℝ, ∀ k, t k ≤ B) →
      ∃ N : ℕ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ k, r₁ ≤ (eqLam a) ^ N * t (ψ k) ∧ (eqLam a) ^ N * t (ψ k) ≤ r₂)
    (href : ∃ δs : ℝ, 0 < δs ∧ ∀ (r₁ r₂ : ℝ), 0 < r₁ → r₁ < r₂ → r₂ < r → r₂ < δs →
      1 / eqLam a < r₂ / r₁ →
      ∀ (N : ℕ), 0 < N → ∀ (c₀ μ₁ μ₂ : ℂ), μ₁ ∈ CharSet a h → μ₂ ∈ CharSet a h →
      (μ₁ ≠ 1 ∨ μ₂ ≠ 1) →
      ∀ (S : ℕ → Set ChainData) (q : ℕ → ChainData) (c : ℕ → ℂ) (ε₀ η₀ : List Bool)
        (C D : ℕ → List Bool) (s t : ℕ → ℕ),
      (∀ k, IsRegComp a h (S k) (c k)) → (∀ k, q k ∈ S k) →
      (∀ k, (q k).2.1 ∈ Ann r₁ r₂ ∧ (q k).2.1 * (q k).2.2 = c k ∧
        r₁ ≤ (eqLam a) ^ (N : ℤ) * ‖(q k).2.2‖ ∧
        (eqLam a) ^ (N : ℤ) * ‖(q k).2.2‖ ≤ r₂) →
      Tendsto c atTop (nhds c₀) → Tendsto s atTop atTop → Tendsto t atTop atTop →
      (∀ k, IsChainWord a h (q k) (ε₀ ++ List.replicate (s k) true ++ C k).length
        (ε₀ ++ List.replicate (s k) true ++ C k)) →
      (∀ k, tailIdx a h (q k) ≤ (ε₀ ++ List.replicate (s k) true ++ C k).length) →
      (∀ k, fan a h (C k) 0 = ltbvA1 ∧ charVal a h (C k) = μ₁) →
      (∀ k, IsChainWord a h (shiftZ a (N : ℤ) (mirrorChain (q k)))
        (η₀ ++ List.replicate (t k) true ++ D k).length
        (η₀ ++ List.replicate (t k) true ++ D k)) →
      (∀ k, tailIdx a h (shiftZ a (N : ℤ) (mirrorChain (q k))) ≤
        (η₀ ++ List.replicate (t k) true ++ D k).length) →
      (∀ k, fan a h (D k) 0 = ltbvA1 ∧ charVal a h (D k) = μ₂) →
      ∃ T : Set ChainData, IsRegComp a h T (c₀ * μ₁ * μ₂)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r₁ r₂ : ℝ),
      0 < r₁ → r₁ < r₂ → r₂ < δ → 1 / eqLam a < r₂ / r₁ →
      ∀ c : ℂ, ∀ (S : ℕ → Set ChainData),
        (∀ n, IsRegComp a h (S n) c) →
        (∀ μ₁ ∈ CharSet a h, ∀ μ₂ ∈ CharSet a h,
          (μ₁ ≠ 1 ∨ μ₂ ≠ 1) → ∀ T : Set ChainData,
            ¬ IsRegComp a h T (c * μ₁ * μ₂)) →
        ∃ M : ℕ, ∀ n, ∀ q ∈ S n, q.2.1 ∈ Ann r₁ r₂ →
          (∀ k : ℕ, M ≤ k → q.1 (k : ℤ) =
            germC a h (((eqLam a : ℝ) : ℂ) ^ k * q.2.1)) ∧
          (∀ k : ℕ, M ≤ k → q.1 (-(k : ℤ)) =
            ugermC a h (((eqLam a : ℝ) : ℂ) ^ k * q.2.2)) := by
  obtain ⟨δt, hδt0, htri'⟩ := htri
  obtain ⟨δF, hδF0, hflatF'⟩ := hflatF
  obtain ⟨δB, hδB0, hflatB'⟩ := hflatB
  obtain ⟨δc, hδc0, hci'⟩ := hci
  obtain ⟨δs, hδs0, href'⟩ := href
  obtain ⟨ρ, hρ0, hρge⟩ := H0_invParam_ge ha0 ha1 hh
  obtain ⟨-, -, -, δ₄, hδ₄0, hinv₄⟩ := germC_diff_at_zero ha0 ha1 hh
  obtain ⟨δ₃, hδ₃0, hprops₃, -⟩ := charVal_props ha0 ha1 hh
  have hlam0 : 0 < eqLam a := ltbv_lam_pos ha0 ha1
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ,
      δ = min δs (min δt (min δF (min δB (min δc (min δ₃ (min δ₄ (min (Real.sqrt ρ) r))))))) :=
    ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδdef]
    repeat' apply lt_min
    · exact hδs0
    · exact hδt0
    · exact hδF0
    · exact hδB0
    · exact hδc0
    · exact hδ₃0
    · exact hδ₄0
    · exact Real.sqrt_pos.mpr hρ0
    · exact hh.1
  have hδs : δ ≤ δs := by rw [hδdef]; exact min_le_left _ _
  have hδt : δ ≤ δt := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδF : δ ≤ δF := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδB : δ ≤ δB := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδc : δ ≤ δc := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hδ3 : δ ≤ δ₃ := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hδ4 : δ ≤ δ₄ := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))))
  have hδsqrt : δ ≤ Real.sqrt ρ := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _)))))))
  have hδr : δ ≤ r := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_right _ _)))))))
  refine ⟨δ, hδ0, ?_⟩
  intro r₁ r₂ hr₁ hr₁₂ hr₂ hratio c S hS hdesc
  show ∃ M : ℕ, ∀ n, ∀ q ∈ S n, q.2.1 ∈ Ann r₁ r₂ → TailP a h q M ∧ bwdTailP a h q M
  by_contra hcon
  have hcon' : ∀ M, ∃ n : ℕ, ∃ q : ChainData,
      q ∈ S n ∧ q.2.1 ∈ Ann r₁ r₂ ∧ ¬ (TailP a h q M ∧ bwdTailP a h q M) := by
    intro M
    by_contra h
    apply hcon
    refine ⟨M, fun n q hq hann => ?_⟩
    by_contra h2
    exact h ⟨n, q, hq, hann, h2⟩
  choose nf qf hqmem hqann hqnot using hcon'
  have hqH : ∀ M, qf M ∈ H0 a h := fun M => (hS (nf M)).1 (hqmem M)
  have hchain : ∀ M, IsChain a h (qf M) := fun M => isChain_of_mem_H0 (hqH M)
  have hprod : ∀ M, (qf M).2.1 * (qf M).2.2 = c := fun M => (hS (nf M)).2.2 (qf M) (hqmem M)
  have hbig : ∀ M, M < max (tailIdx a h (qf M)) (tailIdx a h (mirrorChain (qf M))) := by
    intro M
    have hp1 : ∃ N, TailP a h (qf M) N := tailP_of_isChain (hchain M)
    have hp2 : ∃ N, TailP a h (mirrorChain (qf M)) N :=
      tailP_of_isChain (isChain_mirrorChain (hchain M))
    rcases not_and_or.mp (hqnot M) with hna | hna
    · have hlt : M < tailIdx a h (qf M) := by
        rw [← not_le]
        exact fun hle => hna ((tailIdx_le_iff hp1).mp hle)
      exact lt_of_lt_of_le hlt (le_max_left _ _)
    · have hlt : M < tailIdx a h (mirrorChain (qf M)) := by
        rw [← not_le]
        exact fun hle => hna ((ltbv_bwdTailP_iff (qf M) M).mpr ((tailIdx_le_iff hp2).mp hle))
      exact lt_of_lt_of_le hlt (le_max_right _ _)
  have hr₁r₂ : r₁ * r₂ < ρ := by
    have h1 : r₁ * r₂ < r₂ * r₂ := by nlinarith [hr₁, hr₁₂]
    have h2 : r₂ * r₂ ≤ δ * δ :=
      mul_self_le_mul_self (le_of_lt (lt_trans hr₁ hr₁₂)) (le_of_lt hr₂)
    have h3 : δ * δ ≤ ρ := by
      have h := mul_self_le_mul_self (le_of_lt hδ0) hδsqrt
      rwa [Real.mul_self_sqrt (le_of_lt hρ0)] at h
    linarith
  have ht₁ : ∀ M, r₁ ≤ ‖(qf M).2.2‖ := by
    intro M
    have hψ₁ : r₁ ≤ ‖(qf M).2.1‖ := (ltbv_mem_Ann (hqann M)).1
    have hpos : 0 < ‖(qf M).2.1‖ := lt_of_lt_of_le hr₁ hψ₁
    have hρc : ρ ≤ ‖c‖ := by
      have h := hρge (qf M) (hqH M)
      rwa [hprod M] at h
    have h1 : r₁ * ‖(qf M).2.1‖ < ρ :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (ltbv_mem_Ann (hqann M)).2 (le_of_lt hr₁)) hr₁r₂
    have h2 : r₁ * ‖(qf M).2.1‖ ≤ ‖(qf M).2.1‖ * ‖(qf M).2.2‖ := by
      rw [← norm_mul, hprod M]
      exact le_trans (le_of_lt h1) hρc
    rw [mul_comm r₁] at h2
    exact le_of_mul_le_mul_left h2 hpos
  have ht₂ : ∃ B : ℝ, ∀ M, ‖(qf M).2.2‖ ≤ B := ⟨‖c‖ / r₁, fun M => by
    have hψ₁ : r₁ ≤ ‖(qf M).2.1‖ := (ltbv_mem_Ann (hqann M)).1
    have h1 : ‖(qf M).2.1‖ * ‖(qf M).2.2‖ = ‖c‖ := by rw [← norm_mul, hprod M]
    have h2 : ‖(qf M).2.2‖ = ‖c‖ / ‖(qf M).2.1‖ := by
      rw [eq_div_iff (ne_of_gt (lt_of_lt_of_le hr₁ hψ₁)), mul_comm]
      exact h1
    rw [h2]
    exact div_le_div_of_nonneg_left (norm_nonneg c) hr₁ hψ₁⟩
  obtain ⟨N, ψ, hψmono, hψlvl⟩ := hlvl r₁ r₂ hr₁ hr₁₂ hratio (fun M => ‖(qf M).2.2‖) ht₁ ht₂
  let qq : ℕ → ChainData := fun k => qf (ψ k)
  have hqq_chain : ∀ k, IsChain a h (qq k) := fun k => hchain (ψ k)
  have hqqH : ∀ k, qq k ∈ H0 a h := fun k => hqH (ψ k)
  have hqqann : ∀ k, (qq k).2.1 ∈ Ann r₁ r₂ := fun k => hqann (ψ k)
  have hqqprod : ∀ k, (qq k).2.1 * (qq k).2.2 = c := fun k => hprod (ψ k)
  have hqqlvl : ∀ k, r₁ ≤ (eqLam a) ^ N * ‖(qq k).2.2‖ ∧
      (eqLam a) ^ N * ‖(qq k).2.2‖ ≤ r₂ := fun k => hψlvl k
  have hminε : ∀ j : ℕ, ∃ ε : List Bool, IsChainWord a h (qq j) (tailIdx a h (qq j)) ε ∧
      ε.length = tailIdx a h (qq j) ∧ ((qq j).1 0 = fan a h ε (qq j).2.1) ∧
      (∀ n : ℕ, tailIdx a h (qq j) ≤ n →
        (qq j).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * (qq j).2.1)) :=
    fun j => ltbv_minimal_word ha0 ha1 (hqq_chain j)
  let ε : ℕ → List Bool := fun j => Classical.choose (hminε j)
  have hεw : ∀ j, IsChainWord a h (qq j) (tailIdx a h (qq j)) (ε j) :=
    fun j => (Classical.choose_spec (hminε j)).1
  have hεlen : ∀ j, (ε j).length = tailIdx a h (qq j) :=
    fun j => (Classical.choose_spec (hminε j)).2.1
  have hεfan : ∀ j, (qq j).1 0 = fan a h (ε j) (qq j).2.1 :=
    fun j => (Classical.choose_spec (hminε j)).2.2.1
  let pp : ℕ → ChainData := fun j => shiftZ a (N : ℤ) (mirrorChain (qq j))
  have hpp_chain : ∀ j, IsChain a h (pp j) :=
    fun j => isChain_shiftZ ha0 ha1 (isChain_mirrorChain (hqq_chain j)) (N : ℤ)
  have hppnorm : ∀ j, ‖(pp j).2.1‖ = (eqLam a) ^ N * ‖(qq j).2.2‖ := by
    intro j
    simp only [pp, shiftZ_psi1, mirrorChain_psi1, zpow_natCast, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
  have hminη : ∀ j : ℕ, ∃ η : List Bool, IsChainWord a h (pp j) (tailIdx a h (pp j)) η ∧
      η.length = tailIdx a h (pp j) ∧ ((pp j).1 0 = fan a h η (pp j).2.1) ∧
      (∀ n : ℕ, tailIdx a h (pp j) ≤ n →
        (pp j).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * (pp j).2.1)) :=
    fun j => ltbv_minimal_word ha0 ha1 (hpp_chain j)
  let η : ℕ → List Bool := fun j => Classical.choose (hminη j)
  have hηw : ∀ j, IsChainWord a h (pp j) (tailIdx a h (pp j)) (η j) :=
    fun j => (Classical.choose_spec (hminη j)).1
  have hηlen : ∀ j, (η j).length = tailIdx a h (pp j) :=
    fun j => (Classical.choose_spec (hminη j)).2.1
  have hηfan : ∀ j, (pp j).1 0 = fan a h (η j) (pp j).2.1 :=
    fun j => (Classical.choose_spec (hminη j)).2.2.1
  obtain ⟨φ₁, hφ₁mono, hcase₁⟩ := htri' ε
  obtain ⟨φ₂, hφ₂mono, hcase₂⟩ := htri' (fun k => η (φ₁ k))
  let φ : ℕ → ℕ := fun k => φ₁ (φ₂ k)
  have hφmono : StrictMono φ := hφ₁mono.comp hφ₂mono
  let qseq : ℕ → ChainData := fun k => qq (φ k)
  let pseq : ℕ → ChainData := fun k => pp (φ k)
  let εseq : ℕ → List Bool := fun k => ε (φ k)
  let ηseq : ℕ → List Bool := fun k => η (φ k)
  have hqseqchain : ∀ k, IsChain a h (qseq k) := fun k => hqq_chain (φ k)
  have hpseqchain : ∀ k, IsChain a h (pseq k) := fun k => hpp_chain (φ k)
  have hqseqH : ∀ k, qseq k ∈ H0 a h := fun k => hqqH (φ k)
  have hqseqann : ∀ k, (qseq k).2.1 ∈ Ann r₁ r₂ := fun k => hqqann (φ k)
  have hqseqprod : ∀ k, (qseq k).2.1 * (qseq k).2.2 = c := fun k => hqqprod (φ k)
  have hqseqlvl : ∀ k, r₁ ≤ (eqLam a) ^ N * ‖(qseq k).2.2‖ ∧
      (eqLam a) ^ N * ‖(qseq k).2.2‖ ≤ r₂ := fun k => hqqlvl (φ k)
  have hpseqnorm : ∀ k, ‖(pseq k).2.1‖ = (eqLam a) ^ N * ‖(qseq k).2.2‖ := fun k => hppnorm (φ k)
  have hεw' : ∀ k, IsChainWord a h (qseq k) (tailIdx a h (qseq k)) (εseq k) := fun k => hεw (φ k)
  have hεlen' : ∀ k, (εseq k).length = tailIdx a h (qseq k) := fun k => hεlen (φ k)
  have hεfan' : ∀ k, (qseq k).1 0 = fan a h (εseq k) (qseq k).2.1 := fun k => hεfan (φ k)
  have hηw' : ∀ k, IsChainWord a h (pseq k) (tailIdx a h (pseq k)) (ηseq k) := fun k => hηw (φ k)
  have hηlen' : ∀ k, (ηseq k).length = tailIdx a h (pseq k) := fun k => hηlen (φ k)
  have hηfan' : ∀ k, (pseq k).1 0 = fan a h (ηseq k) (pseq k).2.1 := fun k => hηfan (φ k)
  have hbigφ : ∀ k, ψ (φ k) <
      max (tailIdx a h (qseq k)) (tailIdx a h (mirrorChain (qseq k))) := fun k => hbig (ψ (φ k))
  have hεres : ∃ (ε₀e : List Bool) (Ce : ℕ → List Bool) (se : ℕ → ℕ) (μ₁e : ℂ),
      μ₁e ∈ CharSet a h ∧ Tendsto se atTop atTop ∧
      (∀ k, IsChainWord a h (qseq k) (ε₀e ++ List.replicate (se k) true ++ Ce k).length
        (ε₀e ++ List.replicate (se k) true ++ Ce k)) ∧
      (∀ k, tailIdx a h (qseq k) ≤ (ε₀e ++ List.replicate (se k) true ++ Ce k).length) ∧
      (∀ k, fan a h (Ce k) 0 = ltbvA1 ∧ charVal a h (Ce k) = μ₁e) ∧
      (μ₁e = 1 → ∃ A : ℕ, ∀ k, tailIdx a h (qseq k) ≤ A) := by
    rcases hcase₁ with h1 | h2 | h3
    · obtain ⟨ε₀f, hε₀f⟩ := h1
      have hεseq_eq : ∀ k, εseq k = ε₀f := fun k => hε₀f (φ₂ k)
      have htailε : ∀ k, tailIdx a h (qseq k) = ε₀f.length := by
        intro k
        rw [← hεlen' k, hεseq_eq k]
      refine ⟨ε₀f, (fun _ => []), (fun k => k), 1, ?_, tendsto_id, ?_, ?_, ?_, ?_⟩
      · simp [CharSet]
      · intro k
        have hpadk : IsChainWord a h (qseq k) (tailIdx a h (qseq k) + k)
            (ε₀f ++ List.replicate k true) :=
          hpad (p := qseq k) (N := tailIdx a h (qseq k)) (ε := ε₀f) (ρg := δ₄)
            (hqseqchain k)
            (by rw [← hεseq_eq k]; exact hεw' k)
            (TailP_tailIdx (tailP_of_isChain (hqseqchain k)))
            (fun u hu => hinv₄ u (by rw [Metric.mem_ball, dist_zero_right]; exact hu))
            (lt_of_le_of_lt (ltbv_mem_Ann (hqseqann k)).2 (lt_of_lt_of_le hr₂ hδ4)) k
        simpa [List.append_nil, List.length_append, htailε k] using hpadk
      · intro k
        have hk := htailε k
        simp only [List.length_append, List.length_replicate, List.append_nil, hk]
        omega
      · intro k
        exact ⟨ltbv_fan_nil_centre ha0 ha1 hh, ltbv_charVal_nil ha0 ha1 hh⟩
      · intro _
        exact ⟨ε₀f.length, fun k => le_of_eq (htailε k)⟩
    · obtain ⟨ε₀f, ε₁f, sf, Cf, hstf, hwordf, hCf, hε₁f0, himf, hposf, hlef⟩ := h2
      have hεseq_word : ∀ k, εseq k = ε₀f ++ List.replicate (sf (φ₂ k)) true ++ Cf (φ₂ k) :=
        fun k => hwordf (φ₂ k)
      have hstf' : Tendsto (fun k => sf (φ₂ k)) atTop atTop := hstf.comp (StrictMono.tendsto_atTop hφ₂mono)
      have hword' : ∀ k, IsChainWord a h (qseq k)
          (ε₀f ++ List.replicate (sf (φ₂ k)) true ++ Cf (φ₂ k)).length
          (ε₀f ++ List.replicate (sf (φ₂ k)) true ++ Cf (φ₂ k)) := by
        intro k
        have h := hεw' k
        rw [← hεlen' k, hεseq_word k] at h
        exact h
      have hle' : ∀ k, tailIdx a h (qseq k) ≤
          (ε₀f ++ List.replicate (sf (φ₂ k)) true ++ Cf (φ₂ k)).length := by
        intro k
        rw [← hεlen' k, hεseq_word k]
      by_cases hmu1 : charVal a h ε₁f = 1
      · refine ⟨ε₀f, (fun k => Cf (φ₂ k)), (fun k => sf (φ₂ k)), 1, ?_, hstf', ?_, ?_, ?_, ?_⟩
        · simp [CharSet]
        · exact hword'
        · exact hle'
        · intro k
          exact ⟨(hCf (φ₂ k)).1, by rw [(hCf (φ₂ k)).2, hmu1]⟩
        · intro _
          obtain ⟨M, hM⟩ := hci' hδ0 hδc (ε₀ := ε₀f)
          refine ⟨M, fun k => ?_⟩
          have hEqOn : Set.EqOn (fan a h (εseq k)) (fan a h ε₀f) (Metric.ball 0 δ) := by
            rw [hεseq_word k]
            have hger : Set.EqOn (fan a h (Cf (φ₂ k))) (germC a h) (Metric.ball 0 δ₃) :=
              (hprops₃ (Cf (φ₂ k)) (hCf (φ₂ k)).1).2.2.2 (by rw [(hCf (φ₂ k)).2, hmu1])
            exact ltbv_eqOn_of_germ_tail ha0 ha1
              (fun u hu => hger (Metric.ball_subset_ball hδ3 hu))
              (fun u hu => hinv₄ u (Metric.ball_subset_ball hδ4 hu))
              ε₀f (sf (φ₂ k))
          have h1 : (εseq k).length ≤ M :=
            hM (qseq k) (εseq k) (hqseqchain k)
              (lt_of_le_of_lt (ltbv_mem_Ann (hqseqann k)).2 hr₂)
              (hεfan' k) (hεlen' k).symm hEqOn
          rwa [hεlen' k] at h1
      · refine ⟨ε₀f, (fun k => Cf (φ₂ k)), (fun k => sf (φ₂ k)), charVal a h ε₁f,
          Or.inr ⟨ε₁f, hε₁f0, rfl⟩, hstf', ?_, ?_, ?_, ?_⟩
        · exact hword'
        · exact hle'
        · intro k
          exact ⟨(hCf (φ₂ k)).1, by rw [(hCf (φ₂ k)).2]⟩
        · intro h
          exact absurd h hmu1
    · obtain ⟨-, hflat⟩ := h3
      exfalso
      obtain ⟨η₀f, hη₀fpos, hη₀f⟩ := hflatF' r₁ r₂ c hr₁ hr₁₂ (lt_of_lt_of_le hr₂ hδF) hratio
      have hev' : ∀ᶠ j in atTop, ∀ u ∈ Metric.ball (0 : ℂ) δt,
          ‖(fan a h (εseq j) u).1 - (fan a h (εseq j) 0).1‖ < η₀f ∧
          ‖(fan a h (εseq j) u).2‖ < η₀f *
            ‖(fan a h (εseq j) u).1 - ((a / 2 : ℝ) : ℂ)‖ :=
        (StrictMono.tendsto_atTop hφ₂mono).eventually (hflat η₀f hη₀fpos)
      obtain ⟨k, hk⟩ := hev'.exists
      have hu : (qseq k).2.1 ∈ Metric.ball (0 : ℂ) δt := by
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_le_of_lt (ltbv_mem_Ann (hqseqann k)).2 (lt_of_lt_of_le hr₂ hδt)
      exact hη₀f (qseq k) (hqseqH k) (hqseqann k) (hqseqprod k) (εseq k) (hεfan' k) (hk _ hu)
  have hηres : ∃ (η₀e : List Bool) (De : ℕ → List Bool) (te : ℕ → ℕ) (μ₂e : ℂ),
      μ₂e ∈ CharSet a h ∧ Tendsto te atTop atTop ∧
      (∀ k, IsChainWord a h (pseq k) (η₀e ++ List.replicate (te k) true ++ De k).length
        (η₀e ++ List.replicate (te k) true ++ De k)) ∧
      (∀ k, tailIdx a h (pseq k) ≤ (η₀e ++ List.replicate (te k) true ++ De k).length) ∧
      (∀ k, fan a h (De k) 0 = ltbvA1 ∧ charVal a h (De k) = μ₂e) ∧
      (μ₂e = 1 → ∃ B : ℕ, ∀ k, tailIdx a h (pseq k) ≤ B) := by
    rcases hcase₂ with h1 | h2 | h3
    · obtain ⟨η₀f, hη₀f⟩ := h1
      have hηseq_eq : ∀ k, ηseq k = η₀f := fun k => hη₀f k
      have htailη : ∀ k, tailIdx a h (pseq k) = η₀f.length := by
        intro k
        rw [← hηlen' k, hηseq_eq k]
      have hsmallη : ∀ k, ‖(pseq k).2.1‖ ≤ r₂ := by
        intro k
        rw [hpseqnorm k]
        exact (hqseqlvl k).2
      refine ⟨η₀f, (fun _ => []), (fun k => k), 1, ?_, tendsto_id, ?_, ?_, ?_, ?_⟩
      · simp [CharSet]
      · intro k
        have hpadk : IsChainWord a h (pseq k) (tailIdx a h (pseq k) + k)
            (η₀f ++ List.replicate k true) :=
          hpad (p := pseq k) (N := tailIdx a h (pseq k)) (ε := η₀f) (ρg := δ₄)
            (hpseqchain k)
            (by rw [← hηseq_eq k]; exact hηw' k)
            (TailP_tailIdx (tailP_of_isChain (hpseqchain k)))
            (fun u hu => hinv₄ u (by rw [Metric.mem_ball, dist_zero_right]; exact hu))
            (lt_of_le_of_lt (hsmallη k) (lt_of_lt_of_le hr₂ hδ4)) k
        simpa [List.append_nil, List.length_append, htailη k] using hpadk
      · intro k
        have hk := htailη k
        simp only [List.length_append, List.length_replicate, List.append_nil, hk]
        omega
      · intro k
        exact ⟨ltbv_fan_nil_centre ha0 ha1 hh, ltbv_charVal_nil ha0 ha1 hh⟩
      · intro _
        exact ⟨η₀f.length, fun k => le_of_eq (htailη k)⟩
    · obtain ⟨η₀f, η₁f, tf, Df, hstf, hwordf, hDf, hη₁f0, himf, hposf, hlef⟩ := h2
      have hηseq_word : ∀ k, ηseq k = η₀f ++ List.replicate (tf k) true ++ Df k :=
        fun k => hwordf k
      have hword' : ∀ k, IsChainWord a h (pseq k)
          (η₀f ++ List.replicate (tf k) true ++ Df k).length
          (η₀f ++ List.replicate (tf k) true ++ Df k) := by
        intro k
        have h := hηw' k
        rw [← hηlen' k, hηseq_word k] at h
        exact h
      have hle' : ∀ k, tailIdx a h (pseq k) ≤
          (η₀f ++ List.replicate (tf k) true ++ Df k).length := by
        intro k
        rw [← hηlen' k, hηseq_word k]
      have hsmallη : ∀ k, ‖(pseq k).2.1‖ ≤ r₂ := by
        intro k
        rw [hpseqnorm k]
        exact (hqseqlvl k).2
      by_cases hmu2 : charVal a h η₁f = 1
      · refine ⟨η₀f, Df, tf, 1, ?_, hstf, ?_, ?_, ?_, ?_⟩
        · simp [CharSet]
        · exact hword'
        · exact hle'
        · intro k
          exact ⟨(hDf k).1, by rw [(hDf k).2, hmu2]⟩
        · intro _
          obtain ⟨M, hM⟩ := hci' hδ0 hδc (ε₀ := η₀f)
          refine ⟨M, fun k => ?_⟩
          have hEqOn : Set.EqOn (fan a h (ηseq k)) (fan a h η₀f) (Metric.ball 0 δ) := by
            rw [hηseq_word k]
            have hger : Set.EqOn (fan a h (Df k)) (germC a h) (Metric.ball 0 δ₃) :=
              (hprops₃ (Df k) (hDf k).1).2.2.2 (by rw [(hDf k).2, hmu2])
            exact ltbv_eqOn_of_germ_tail ha0 ha1
              (fun u hu => hger (Metric.ball_subset_ball hδ3 hu))
              (fun u hu => hinv₄ u (Metric.ball_subset_ball hδ4 hu))
              η₀f (tf k)
          have h1 : (ηseq k).length ≤ M :=
            hM (pseq k) (ηseq k) (hpseqchain k)
              (lt_of_le_of_lt (hsmallη k) hr₂)
              (hηfan' k) (hηlen' k).symm hEqOn
          rwa [hηlen' k] at h1
      · refine ⟨η₀f, Df, tf, charVal a h η₁f,
          Or.inr ⟨η₁f, hη₁f0, rfl⟩, hstf, ?_, ?_, ?_, ?_⟩
        · exact hword'
        · exact hle'
        · intro k
          exact ⟨(hDf k).1, by rw [(hDf k).2]⟩
        · intro h
          exact absurd h hmu2
    · obtain ⟨-, hflat⟩ := h3
      exfalso
      obtain ⟨η₀f, hη₀fpos, hη₀f⟩ := hflatB' r₁ r₂ c hr₁ hr₁₂ (lt_of_lt_of_le hr₂ hδB) hratio
      have hev : ∀ᶠ k in atTop, ∀ u ∈ Metric.ball (0 : ℂ) δt,
          ‖(fan a h (ηseq k) u).1 - (fan a h (ηseq k) 0).1‖ < η₀f ∧
          ‖(fan a h (ηseq k) u).2‖ < η₀f *
            ‖(fan a h (ηseq k) u).1 - ((a / 2 : ℝ) : ℂ)‖ := hflat η₀f hη₀fpos
      obtain ⟨k, hk⟩ := hev.exists
      have hu : (((eqLam a : ℝ) : ℂ)) ^ (N : ℤ) * (qseq k).2.2 ∈ Metric.ball (0 : ℂ) δt := by
        rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_zpow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hlam0, zpow_natCast]
        exact lt_of_le_of_lt (hqseqlvl k).2 (lt_of_lt_of_le hr₂ hδt)
      have hlev1 : r₁ ≤ (eqLam a) ^ (N : ℤ) * ‖(qseq k).2.2‖ := by
        rw [zpow_natCast]; exact (hqseqlvl k).1
      have hlev2 : (eqLam a) ^ (N : ℤ) * ‖(qseq k).2.2‖ ≤ r₂ := by
        rw [zpow_natCast]; exact (hqseqlvl k).2
      have hread : (qseq k).1 (-(N : ℤ)) =
          eqMirror (fan a h (ηseq k) (((eqLam a : ℝ) : ℂ) ^ (N : ℤ) * (qseq k).2.2)) :=
        ltbv_bwd_eq_of_isChainWord ha0 ha1 (qseq k) N (ηseq k) (by
          have h := hηw' k
          rwa [← hηlen' k] at h)
      exact hη₀f (qseq k) (N : ℤ) (ηseq k) (hqseqH k) (hqseqann k) (hqseqprod k)
        hlev1 hlev2 hread (hk _ hu)
  obtain ⟨ε₀e, Ce, se, μ₁e, hμ₁mem, hse, hεW, hεle, hCe, hAbnd⟩ := hεres
  obtain ⟨η₀e, De, te, μ₂e, hμ₂mem, hte, hηW, hηle, hDe, hBbnd⟩ := hηres
  by_cases hne : μ₁e ≠ 1 ∨ μ₂e ≠ 1
  · -- the reading level is positive: otherwise the two annulus conditions at level `0`
    -- already force `‖c‖ ≤ r₂² < ρ ≤ ‖c‖`
    have hNpos : 0 < N := by
      by_contra hN
      have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
      have hρc : ρ ≤ ‖c‖ := by
        have h := hρge (qseq 0) (hqseqH 0)
        rwa [hqseqprod 0] at h
      have hψ₁ : ‖(qseq 0).2.1‖ ≤ r₂ := (ltbv_mem_Ann (hqseqann 0)).2
      have hψ₂ : ‖(qseq 0).2.2‖ ≤ r₂ := by
        have h := (hqseqlvl 0).2
        rwa [hN0, pow_zero, one_mul] at h
      have hle : ‖c‖ ≤ r₂ * r₂ := by
        rw [← hqseqprod 0, norm_mul]
        exact mul_le_mul hψ₁ hψ₂ (norm_nonneg _) (le_trans (norm_nonneg _) hψ₁)
      have hr₂sqrt : r₂ < Real.sqrt ρ := lt_of_lt_of_le hr₂ hδsqrt
      have hr₂sq : r₂ * r₂ < ρ := by
        nlinarith [Real.sq_sqrt hρ0.le, Real.sqrt_nonneg ρ, hr₂sqrt,
          lt_trans hr₁ hr₁₂]
      linarith
    obtain ⟨T, hT⟩ := href' r₁ r₂ hr₁ hr₁₂ (lt_of_lt_of_le hr₂ hδr) (lt_of_lt_of_le hr₂ hδs)
      hratio N hNpos c μ₁e μ₂e
      hμ₁mem hμ₂mem hne (fun k => S (nf (ψ (φ k)))) qseq (fun _ => c) ε₀e η₀e Ce De se te
      (fun k => hS (nf (ψ (φ k)))) (fun k => hqmem (ψ (φ k)))
      (fun k => ⟨hqseqann k, hqseqprod k, by rw [zpow_natCast]; exact (hqseqlvl k).1,
        by rw [zpow_natCast]; exact (hqseqlvl k).2⟩)
      tendsto_const_nhds hse hte hεW hεle hCe hηW hηle hDe
    exact hdesc μ₁e hμ₁mem μ₂e hμ₂mem hne T hT
  · push_neg at hne
    obtain ⟨hμ₁1, hμ₂1⟩ := hne
    obtain ⟨A, hA⟩ := hAbnd hμ₁1
    obtain ⟨B, hB⟩ := hBbnd hμ₂1
    have hcontr : ∀ k : ℕ, k < max A (B + N) := by
      intro k
      have h1 : ψ (φ k) <
          max (tailIdx a h (qseq k)) (tailIdx a h (mirrorChain (qseq k))) := hbigφ k
      have h2 : tailIdx a h (mirrorChain (qseq k)) ≤ B + N := by
        have h3 := ltbv_tailIdx_le_shiftZ ha0 ha1 (isChain_mirrorChain (hqseqchain k)) N
        exact le_trans h3 (Nat.add_le_add_right (hB k) N)
      have h4 : max (tailIdx a h (qseq k)) (tailIdx a h (mirrorChain (qseq k))) ≤
          max A (B + N) :=
        max_le (le_trans (hA k) (le_max_left _ _)) (le_trans h2 (le_max_right _ _))
      have h5 : k ≤ ψ (φ k) := le_trans (hφmono.id_le k) (hψmono.id_le (φ k))
      exact lt_of_lt_of_le (lt_of_le_of_lt h5 h1) h4
    exact absurd (hcontr (max A (B + N))) (lt_irrefl _)

/-- **Rychlik Thm 8(3) for a fixed value, uniformly over all the regular components of that value.**

If `c` has no *descendant* regular value (`c * μ₁ * μ₂` with `(μ₁,μ₂) ≠ (1,1)` in `CharSet a h`),
then over an annulus `Ann r₁ r₂` of ratio `> 1/λ` inside a small ball the tail indices of *all*
chains of *all* regular components of value `c` are uniformly bounded: from one depth `M` on, each
such chain is exactly the stable germ forward and the unstable germ backward.

This is the analytic core of Rychlik's Lemma 5.1: an unbounded sequence of tail indices gives,
by the fan trichotomy, case (iii) (impossible by the parity separation across the segment) or
case (ii) (which produces the forbidden descendant value), while case (i) contradicts the
*minimality* of the tail index. -/
theorem la_tail_bound_value {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r₁ r₂ : ℝ),
      0 < r₁ → r₁ < r₂ → r₂ < δ → 1 / Work.EQ.eqLam a < r₂ / r₁ →
      ∀ c : ℂ, ∀ (S : ℕ → Set Work.EQ.ChainData),
        (∀ n, Work.EQ.IsRegComp a h (S n) c) →
        (∀ μ₁ ∈ Work.EQ.CharSet a h, ∀ μ₂ ∈ Work.EQ.CharSet a h,
          (μ₁ ≠ 1 ∨ μ₂ ≠ 1) → ∀ T : Set Work.EQ.ChainData,
            ¬ Work.EQ.IsRegComp a h T (c * μ₁ * μ₂)) →
        ∃ M : ℕ, ∀ n, ∀ q ∈ S n, q.2.1 ∈ Work.EQ.Ann r₁ r₂ →
          (∀ k : ℕ, M ≤ k → q.1 (k : ℤ) =
            Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ k * q.2.1)) ∧
          (∀ k : ℕ, M ≤ k → q.1 (-(k : ℤ)) =
            Work.EQ.ugermC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ k * q.2.2)) := by
  sorry

/-! ## SESSION 6 additions

The pieces below were added in session 6.  They are the elementary parts of the *unpinned*
route to `la_tail_bound_value` (see the session-6 section of `Submission/Work/EQ/LTBV_NOTES.md`):
the trichotomy predicate `ltbvTrich` (case (i) = *literally constant* words, i.e. the shape of
`Work.EQ.LaTB.la_fan_trichotomy_v2`), its monotonicity in the radius, its production from
`la_fan_trichotomy_v2`, and the observation that a returning word with a `false` letter has no
characteristic value `1` (Rychlik's `ν ξ = 1 ⟹ ξ = ∅`, refined to *letters*). -/

/-- **The fan trichotomy with *literally constant* case (i)** (the shape of
`Work.EQ.LaTB.la_fan_trichotomy_v2`, packaged as a predicate at a fixed radius `δ`).  This is the
body of the `htri` hypothesis of `ltbv_main`. -/
def ltbvTrich (a : ℝ) (h : ℂ → ℂ) (δ : ℝ) : Prop :=
  ∀ ε : ℕ → List Bool, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ((∃ ε₀ : List Bool, ∀ k, ε (φ k) = ε₀) ∨
     (∃ (ε₀ ε₁ : List Bool) (s : ℕ → ℕ) (C : ℕ → List Bool),
        Tendsto s atTop atTop ∧
        (∀ k, ε (φ k) = ε₀ ++ List.replicate (s k) true ++ C k) ∧
        (∀ k, fan a h (C k) 0 = ltbvA1 ∧ charVal a h (C k) = charVal a h ε₁) ∧
        fan a h ε₁ 0 = ltbvA1 ∧ (charVal a h ε₁).im = 0 ∧ 0 < (charVal a h ε₁).re ∧
        (charVal a h ε₁).re ≤ 1) ∨
     ((∀ n : ℕ, ∀ᶠ k in atTop, n ≤ nonA1Count a h (ε (φ k))) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ u ∈ Metric.ball (0 : ℂ) δ,
          ‖(fan a h (ε (φ k)) u).1 - (fan a h (ε (φ k)) 0).1‖ < η ∧
          ‖(fan a h (ε (φ k)) u).2‖ < η *
            ‖(fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ)‖))

/-- The trichotomy holds at every radius below the one supplied by
`Work.EQ.LaTB.la_fan_trichotomy_v2` (cases (i) and (ii) do not mention `δ`, and case (iii)
restricts to the smaller ball). -/
theorem ltbvTrich_mono {a : ℝ} {h : ℂ → ℂ} {δ δ' : ℝ} (htri : ltbvTrich a h δ)
    (hδδ' : δ' ≤ δ) : ltbvTrich a h δ' := by
  intro ε
  obtain ⟨φ, hφ, hcase⟩ := htri ε
  refine ⟨φ, hφ, ?_⟩
  rcases hcase with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ⟨h3.1, fun η hη => ?_⟩)
    filter_upwards [h3.2 η hη] with k hk
    exact fun u hu => hk u (Metric.ball_subset_ball hδδ' hu)

/-- **The trichotomy of `Work.EQ.LaTB.la_fan_trichotomy_v2` as the predicate `ltbvTrich`.** -/
theorem ltbvTrich_of_v2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) : ∃ δ : ℝ, 0 < δ ∧ ltbvTrich a h δ := by
  obtain ⟨δ, hδ, htri⟩ := LaTB.la_fan_trichotomy_v2 ha0 ha1 hh
  exact ⟨δ, hδ, htri⟩

/-- **A returning word containing `false` has no characteristic value `1`.**  This is the
workspace form of Rychlik's `ν ξ = 1 ⟹ ξ = ∅` (Theorem 7, end of the proof): by
`Work.EQ.charVal_props`, `charVal ε = 1` forces *every* letter of `ε` to be `true`. -/
theorem ltbv_charVal_ne_one_of_false {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {ε : List Bool} (hε : fan a h ε 0 = ltbvA1)
    (hfalse : false ∈ ε) : charVal a h ε ≠ 1 := by
  intro h1
  obtain ⟨-, -, -, δ₀, hδ₀, hinv⟩ := germC_diff_at_zero ha0 ha1 hh
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ :=
    walk_bounds (a := a) ha0 ha1
  have hcv := charVal_of_closed ha0 ha1 hh (by simpa [ltbvA1] using hε)
  have hclosed := stAux_eq_zero_of_closed ha0 ha1 hh (by simpa [ltbvA1] using hε)
  have hwt : wtAux a ε.reverse 0 = 1 := by
    have h2 : ((wtAux a ε.reverse 0 : ℝ) : ℂ) = 1 := by rw [← hcv]; exact h1
    exact_mod_cast h2
  have hall := w13 ε.reverse hclosed hwt
  exact hall false (List.mem_reverse.mpr hfalse) |> fun h => by simp at h

/-- `charValSet a h ⊆ CharSet a h`. -/
theorem ltbv_charValSet_subset_CharSet (a : ℝ) (h : ℂ → ℂ) :
    charValSet a h ⊆ CharSet a h := by
  intro μ hμ
  rcases hμ with rfl | ⟨ε, hε, rfl⟩
  · exact Set.mem_union_left _ rfl
  · exact Set.mem_union_right _ ⟨ε, by simpa [ltbvA1] using hε, rfl⟩

/-- A value that is constant on a connected component of `H0` gives a regular component. -/
theorem ltbv_isRegComp_of_component {a : ℝ} {h : ℂ → ℂ} {C : ℂ} {p : ChainData}
    (hp : p ∈ H0 a h)
    (hconst : ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = C) :
    ∃ T : Set ChainData, IsRegComp a h T C :=
  ⟨connectedComponentIn (H0 a h) p,
    fun _ hq => connectedComponentIn_subset (H0 a h) p hq, ⟨p, hp, rfl⟩, hconst⟩

/-- **Failure extraction.**  If no depth `M` bounds the tails of all the chains of the components
`S n` over the annulus, then there is a sequence of chains `Q M ∈ S (K M)`, `ψ₁ (Q M) ∈ Ann r₁ r₂`,
whose *forward* or *backward* tail index exceeds `M`. -/
theorem ltbv_failure_extract {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r₁ r₂ : ℝ}
    {c : ℂ} {S : ℕ → Set ChainData} (hS : ∀ n, IsRegComp a h (S n) c)
    (hfail : ¬ ∃ M : ℕ, ∀ n, ∀ q ∈ S n, q.2.1 ∈ Ann r₁ r₂ →
      TailP a h q M ∧ bwdTailP a h q M) :
    ∃ (K : ℕ → ℕ) (Q : ℕ → ChainData),
      (∀ M, Q M ∈ S (K M) ∧ (Q M).2.1 ∈ Ann r₁ r₂) ∧
      ∀ M, M < tailIdx a h (Q M) ∨ M < tailIdx a h (mirrorChain (Q M)) := by
  have hbad : ∀ M : ℕ, ∃ n, ∃ q ∈ S n, q.2.1 ∈ Ann r₁ r₂ ∧
      ¬ (TailP a h q M ∧ bwdTailP a h q M) := by
    intro M
    by_contra hno
    exact hfail ⟨M, fun n q hq hqa => by
      by_contra hx
      exact hno ⟨n, q, hq, hqa, hx⟩⟩
  choose n q hq hqann hbad' using hbad
  have hchain : ∀ M, IsChain a h (q M) := fun M => isChain_of_mem_H0 ((hS (n M)).1 (hq M))
  have hmirror : ∀ M, IsChain a h (mirrorChain (q M)) := fun M => isChain_mirrorChain (hchain M)
  refine ⟨n, q, fun M => ⟨hq M, hqann M⟩, fun M => ?_⟩
  rcases not_and_or.mp (hbad' M) with hn | hn
  · left
    have h1 : ¬ TailP a h (q M) M := hn
    by_contra hle
    exact h1 ((tailIdx_le_iff (tailP_of_isChain (hchain M))).mp (not_lt.mp hle))
  · right
    have h1 : ¬ bwdTailP a h (q M) M := hn
    rw [ltbv_bwdTailP_iff] at h1
    by_contra hle
    exact h1 ((tailIdx_le_iff (tailP_of_isChain (hmirror M))).mp (not_lt.mp hle))

end

end Work.EQ
