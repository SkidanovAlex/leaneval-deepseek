import Submission.ThreePages
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

/-!
# The root-point log bound (`EnergyRootBound`)

For the approximating polynomial `P_n = ∏_{i=1}^n (X − α_{n,i})` of
`μ = muS` (see `Submission/ThreePages.lean`), with real roots `α_{n,k}`,
prove that for every root `α_k` (i.e. `k ∈ Icc 1 n`):

    | n·U^μ(α_k) + Σ_{j ≠ k} log|α_k − α_j| | ≤ C·log(n+2)

where `U^μ(x) = logPotential muS (x : ℂ)` and the sum runs over
`j ∈ (Finset.Icc 1 n).erase k`.

## Why it is true (and how to formalise it)

From `ThreePages.approx_potential_bound`:

    ∃C>0 ∀n≥2 ∀x∈Icc aSerre bSerre, 0 < rho n x →
      |(n:ℝ)·U^μ(x) + log |(approxPoly n).eval x| − log (rho n x)| ≤ C·log((n:ℝ)+2).

For x near α_k (x ≠ α_k, x ∈ [aSerre,bSerre]), the nearest root is α_k itself:
`rho n x = |x − α_k|` (because all other roots are at distance ≥ s =
(Csp·n)^{-2} from α_k, and we take |x−α_k| < s/2, so for j≠k,
|x − α_j| ≥ s − |x−α_k| > |x−α_k|).  Also `log |(approxPoly n).eval x| =
Σ_{j∈Icc 1 n} log|x − α_j|` (`ThreePages.log_abs_eval`).  Substituting
`log rho = log|x−α_k|` and cancelling gives, for those x:

    |(n:ℝ)·U^μ(x) + Σ_{j∈(Icc 1 n).erase k} log|x − α_j|| ≤ C·log((n:ℝ)+2).   (*)

Both sides of (*) are continuous functions of x at x = α_k (each
`x ↦ log|x − α_j|` is continuous at α_k since α_j ≠ α_k; the finite sum is a
sum of continuous functions; and `x ↦ U^μ(x)` is continuous by
`PotentialContinuity.logPotential_continuous_real`).  Taking the limit x→α_k
inside the absolute value gives the claim.

In Lean the cleanest formulation: fix the inequality (*) and push it through
a limit.  Concretely, prove a helper (in this file):

    lemma abs_value_le_of_eventually_le {g : ℝ → ℝ} {a M : ℝ} {S : Set ℝ}
        (hg : ContinuousAt g a)
        (h : ∀ᶠ x in 𝓝[S] a, g x ≤ M) : g a ≤ M

  using `le_of_tendsto_of_tendsto` together with `hg.continuousWithinAt` /
  `ContinuousAt.tendsto` + `nhdsWithin_le_nhds` + `Filter.Tendsto.mono_left`
  (g → g a along 𝓝[S] a since g is continuous at a) and the constant M.
  Then apply it with  g(x) := |(n:ℝ)·U^μ(x) + Σ_{j∈erase k} log|x − α_j|| ,
  S := Set.Icc aSerre bSerre, a := alpha n k, M := C·log((n:ℝ)+2).
  To get the "eventually ≤ M" hypothesis: use `eventually_nhdsWithin_iff`,
  and take the neighbourhood of `a` to be the open interval
  `(a − s/2, a + s/2)` where `s = (Csp·n)^{-2}` (Csp from
  `Quantile.exists_spacing`, `1 ≤ Csp`).  For any x in that interval with
  x ∈ [aSerre,bSerre] (and even x = a is fine — or handle it by the standard
  trick of putting the eventual statement on the PUNCTURED filter
  𝓝[S \ {a}] a, where x ≠ a), verify: x is not a root, `rho n x = |x−a| > 0`,
  `x ∈ Icc aSerre bSerre`, so `approx_potential_bound` gives (*) — one then
  rewrites `log |eval x P| = Σ_j log|x−α_j|` (log_abs_eval) and `log rho =
  log|x−a|` inside the absolute value and cancels the `log|x−a|` terms, using
  `Finset.sum_erase_add` type identities (the j = k term splits off).

## Useful facts (exact statements — verified in this workspace)

* `Quantile.exists_spacing` :
    ∃ C ≥ 1, ∀ n≥2, ∀i, 1≤i → i<n → (C·(n:ℝ))⁻¹^2 ≤ alpha n (i+1) − alpha n i
  From it prove pairwise spacing: for `k,j ∈ Icc 1 n`, `k ≠ j`:
  `(Csp·(n:ℝ))⁻¹^2 ≤ |alpha n k − alpha n j|` (if j>k telescope the sum of
  consecutive gaps; j<k symmetric).  Add this as a helper lemma.
* `alpha_mem_Icc {n i} (hn : 1 ≤ n) (hi : 1 ≤ i) (hin : i ≤ n) : alpha n i ∈ Icc aSerre bSerre`
* `alpha_strict_mono {n i j} (hn : 1≤n) (hi : 1≤i) (hij : i<j) (hjn : j≤n) : alpha n i < alpha n j`
* `ThreePages.rho_le_root`, `rho_nonneg`, `rho_eq_inf`, `exists_index_rho`,
  `rho_pos_eval_ne_zero`, `log_abs_eval`
* `approx_potential_bound` (above)
* `logPotential_continuous_real : Continuous (fun x : ℝ => logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ))`
  (since `muS` is this serreMeasure, give it as `Continuous fun x => logPotential muS (x:ℂ)`
  by `simpa [muS]`).
* continuity of each term: `Real.continuousAt_log {x} (hx : x ≠ 0) : ContinuousAt Real.log x`;
  with `ContinuousAt.abs`, `.comp`, `.sub`, `.add`, `.mul` you can assemble
  `ContinuousAt (fun x => Real.log |x - alpha n j|) (alpha n k)` when `j ≠ k`
  (prove `|alpha n k - alpha n j| ≠ 0` from strict monotonicity), and
  continuity of a FINITE SUM of `ContinuousAt` functions by induction on the
  Finset (`Finset.induction_on`) using `ContinuousAt.add` (the method
  `ContinuousAt.sum` does NOT exist in this mathlib; do it by induction).
* API notes for this mathlib (2026, Lean v4.33): import
  `Submission.ThreePages` FIRST.  `open scoped Real BigOperators`.  Names
  from the Submission files are reliable; test uncertain names with `#check`.
  `ContinuousAt.sum` does not exist; neither does `Finset.card_Icc` (use
  `Nat.card_Icc` if needed). `measure_mono_null`, `measure_union` etc need
  `open MeasureTheory`.

The statement below is exactly what `Submission.EnergyHalf` needs; do not
change it.  You may add helper lemmas above it in this file.
-/

noncomputable section

open MeasureTheory
open Filter
open scoped Real BigOperators
open Polynomial

namespace Submission.EnergyRootBound

open Submission.Quantile
open Submission.PotentialContinuity
open Submission.SerreExample
open Submission.ThreePages
open Submission.PotentialDefs

/-- In the punctured neighbourhood of a point of `[aSerre,bSerre]` which is not
the right endpoint there are points of the interval arbitrarily close: right
direction. -/
private lemma exists_close_right {a : ℝ} (haL : aSerre ≤ a) (haR : a ≤ bSerre)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hdir : a < bSerre) :
    ∃ y : ℝ, y ∈ ((Set.Icc aSerre bSerre ∩ {x : ℝ | |x - a| < r}) \ {a}) ∧
      |y - a| < ε := by
  let d : ℝ := min (min (r / 2) (ε / 2)) ((bSerre - a) / 2)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hdr : d < r := by
    have hd1 : d ≤ r / 2 := by
      dsimp [d]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    nlinarith
  have hde : d < ε := by
    have hd1 : d ≤ ε / 2 := by
      dsimp [d]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith
  have hdb : d < bSerre - a := by
    have hd1 : d ≤ (bSerre - a) / 2 := by
      dsimp [d]
      exact min_le_right _ _
    nlinarith
  refine ⟨a + d, ?memT, ?dist⟩
  · have hy1 : a + d ∈ Set.Icc aSerre bSerre := by
      rw [Set.mem_Icc]
      constructor <;> linarith [haL, haR, hd, hdb]
    have hy2 : |a + d - a| < r := by
      rw [abs_of_pos (by linarith : 0 < (a + d) - a)]
      nlinarith [hdr]
    have hy3 : a + d ≠ a := by linarith
    exact ⟨⟨hy1, hy2⟩, hy3⟩
  · rw [abs_of_pos (by linarith : 0 < (a + d) - a)]
    nlinarith [hde]

/-- In the punctured neighbourhood of a point of `[aSerre,bSerre]` which is not
the left endpoint there are points of the interval arbitrarily close: left
direction. -/
private lemma exists_close_left {a : ℝ} (haL : aSerre ≤ a) (haR : a ≤ bSerre)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hdir : aSerre < a) :
    ∃ y : ℝ, y ∈ ((Set.Icc aSerre bSerre ∩ {x : ℝ | |x - a| < r}) \ {a}) ∧
      |y - a| < ε := by
  let d : ℝ := min (min (r / 2) (ε / 2)) ((a - aSerre) / 2)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hdr : d < r := by
    have hd1 : d ≤ r / 2 := by
      dsimp [d]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    nlinarith
  have hde : d < ε := by
    have hd1 : d ≤ ε / 2 := by
      dsimp [d]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith
  have hda : d < a - aSerre := by
    have hd1 : d ≤ (a - aSerre) / 2 := by
      dsimp [d]
      exact min_le_right _ _
    nlinarith
  refine ⟨a - d, ?memT, ?dist⟩
  · have hy1 : a - d ∈ Set.Icc aSerre bSerre := by
      rw [Set.mem_Icc]
      constructor <;> linarith [haL, haR, hd, hda]
    have hy2 : |a - d - a| < r := by
      rw [show |a - d - a| = d by
        rw [abs_of_neg (by linarith : (a - d) - a < 0)]
        ring]
      exact hdr
    have hy3 : a - d ≠ a := by linarith
    exact ⟨⟨hy1, hy2⟩, hy3⟩
  · rw [show |(a - d) - a| = d by
      rw [abs_of_neg (by linarith : (a - d) - a < 0)]
      ring]
    exact hde

/-- A root `a ∈ [aSerre,bSerre]` lies in the closure of the punctured
`[aSerre,bSerre]`-neighbourhood `(Icc ∩ ball a r) \ {a}` (the interval has no
isolated points). -/
private lemma mem_closure_punct_Icc_ball {a r : ℝ} (ha : a ∈ Set.Icc aSerre bSerre)
    (hr : 0 < r) :
    a ∈ closure (((Set.Icc aSerre bSerre ∩ {x : ℝ | |x - a| < r}) \ {a}) : Set ℝ) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_cases hR : a < bSerre
  · rcases exists_close_right ha.1 ha.2 hr hε hR with ⟨y, hyT, hyd⟩
    exact ⟨y, hyT, by simpa [Real.dist_eq, abs_sub_comm] using hyd⟩
  · have hEqa : a = bSerre := le_antisymm ha.2 (le_of_not_gt hR)
    have hL : aSerre < a := by linarith [a_lt_b]
    rcases exists_close_left ha.1 ha.2 hr hε hL with ⟨y, hyT, hyd⟩
    exact ⟨y, hyT, by simpa [Real.dist_eq, abs_sub_comm] using hyd⟩

/-- If `|g| ≤ M` throughout a set `T` whose closure contains `a`, and `g` is
continuous at `a`, then `|g a| ≤ M`. -/
private lemma abs_le_of_eventually_abs_le {g : ℝ → ℝ} {T : Set ℝ} {a M : ℝ}
    (haT : a ∈ closure T) (hg : ContinuousAt g a) (h : ∀ y ∈ T, |g y| ≤ M) :
    |g a| ≤ M := by
  have hle : g a ≤ M := by
    exact ContinuousWithinAt.closure_le haT hg.continuousWithinAt continuousWithinAt_const
      (by intro y hy; exact (abs_le.mp (h y hy)).2)
  have hneg : -g a ≤ M := by
    exact ContinuousWithinAt.closure_le haT (ContinuousAt.neg hg).continuousWithinAt continuousWithinAt_const
      (by
        intro y hy
        have hb := abs_le.mp (h y hy)
        change -g y ≤ M
        linarith [hb.1])
  rw [abs_le]
  constructor
  · linarith [hneg]
  · exact hle


/-- If `x` is closer to `alpha n k` than half the minimal separation `s`, the
nearest root to `x` is `alpha n k` itself: `rho n x = |x - alpha n k|`. -/
private lemma rho_eq_self_of_close {n k : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s)
    (hsep : ∀ j : ℕ, j ∈ Finset.Icc 1 n → j ≠ k → s ≤ |alpha n k - alpha n j|)
    (hk : k ∈ Finset.Icc 1 n) (x : ℝ) (hx : |x - alpha n k| < s / 2) :
    rho n x = |x - alpha n k| := by
  have hn1 : 1 ≤ n := by omega
  apply le_antisymm
  · exact rho_le_root hn1 x hk
  · have hcloser : ∀ i ∈ Finset.Icc 1 n, |x - alpha n k| ≤ |x - alpha n i| := by
      intro i hi
      by_cases hik : i = k
      · subst i
        rfl
      · have hsep_i : s ≤ |alpha n k - alpha n i| := hsep i hi hik
        have htri : |alpha n k - alpha n i| ≤ |alpha n k - x| + |x - alpha n i| := by
          calc |alpha n k - alpha n i| = |(alpha n k - x) + (x - alpha n i)| := by
                  congr 1
                  ring
               _ ≤ |alpha n k - x| + |x - alpha n i| := abs_add_le _ _
        have hlt : |x - alpha n k| < |x - alpha n i| := by
          have h1 : s ≤ |x - alpha n k| + |x - alpha n i| := by
            calc s ≤ |alpha n k - alpha n i| := hsep_i
                 _ ≤ |alpha n k - x| + |x - alpha n i| := htri
                 _ = |x - alpha n k| + |x - alpha n i| := by rw [abs_sub_comm]
          nlinarith
        exact le_of_lt hlt
    rw [rho_eq_inf hn1 x]
    exact Finset.le_inf' (Icc_one_n_nonempty hn1) (fun i : ℕ => |x - alpha n i|) hcloser

/-- Near a root the `n·U^μ + Σ_{j≠k} log|·−α_j|` quantity inherits the
`approx_potential_bound` estimate (the `j = k` log term cancels with `log ρ`). -/
private lemma abs_bound_at_close {n k : ℕ} {M : ℝ} (hn : 2 ≤ n)
    (hMain : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → 0 < rho n x →
      |(n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
          - Real.log (rho n x)| ≤ M)
    {s : ℝ} (hs : 0 < s)
    (hsep : ∀ j : ℕ, j ∈ Finset.Icc 1 n → j ≠ k → s ≤ |alpha n k - alpha n j|)
    (hk : k ∈ Finset.Icc 1 n) (x : ℝ)
    (hxI : x ∈ Set.Icc aSerre bSerre) (hxa : x ≠ alpha n k)
    (hxclose : |x - alpha n k| < s / 2) :
    |(n : ℝ) * logPotential muS (x : ℂ) +
        (∑ j ∈ (Finset.Icc 1 n).erase k, Real.log |x - alpha n j|)| ≤ M := by
  have hn1 : 1 ≤ n := by omega
  have hrhoeq : rho n x = |x - alpha n k| := rho_eq_self_of_close hn hs hsep hk x hxclose
  have hrho_pos : 0 < rho n x := by
    rw [hrhoeq]
    exact abs_pos.mpr (sub_ne_zero.mpr hxa)
  have hB := hMain x hxI hrho_pos
  have hlog := log_abs_eval n hn1 x hrho_pos
  have hS : (∑ i ∈ Finset.Icc 1 n, Real.log |x - alpha n i|) =
      (∑ j ∈ (Finset.Icc 1 n).erase k, Real.log |x - alpha n j|) +
        Real.log |x - alpha n k| := by
    simpa using (Finset.sum_erase_add (Finset.Icc 1 n) (fun i : ℕ => Real.log |x - alpha n i|) hk).symm
  have hmainrewr :
      (n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
          - Real.log (rho n x)
        = (n : ℝ) * logPotential muS (x : ℂ) +
            (∑ j ∈ (Finset.Icc 1 n).erase k, Real.log |x - alpha n j|) := by
    rw [hlog, hrhoeq, hS]
    ring
  rw [← hmainrewr]
  exact hB


/-- A finite sum of functions each continuous at `a` is continuous at `a`
(induction on the finset; `ContinuousAt.sum` is not in this library). -/
private lemma continuousAt_finset_sum {ι : Type*} (t : Finset ι) {a : ℝ} {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ t, ContinuousAt (f i) a) :
    ContinuousAt (fun x : ℝ => ∑ i ∈ t, f i x) a := by
  classical
  revert hf
  refine Finset.induction_on t ?_ ?_
  · intro hf
    simpa using (continuousAt_const : ContinuousAt (fun x : ℝ => (0 : ℝ)) a)
  · intro i s his ih hf
    have hsum : (fun x : ℝ => ∑ p ∈ insert i s, f p x) =
        (fun x : ℝ => f i x + ∑ p ∈ s, f p x) := by
      funext x
      simpa using (Finset.sum_insert (a := i) (s := s) (f := fun p => f p x) his)
    rw [hsum]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- `x ↦ ∑_{j ≠ k} log |x − α_j|` is continuous at the root `α_k`
(each term is: the other roots are distinct from `α_k`). -/
private lemma continuousAt_log_erase_sum (n : ℕ) (hn : 1 ≤ n) (k : ℕ)
    (hk : k ∈ Finset.Icc 1 n) :
    ContinuousAt (fun x : ℝ =>
      ∑ j ∈ (Finset.Icc 1 n).erase k, Real.log |x - alpha n j|) (alpha n k) := by
  apply continuousAt_finset_sum
  intro j hj
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
  have hjin : j ∈ Finset.Icc 1 n := (Finset.mem_erase.mp hj).2
  have hkj1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hjn : j ≤ n := (Finset.mem_Icc.mp hjin).2
  have hne : alpha n k - alpha n j ≠ 0 := by
    intro hz
    have hEq : alpha n k = alpha n j := sub_eq_zero.mp hz
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · have hmono : alpha n j < alpha n k :=
        alpha_strict_mono hn (Finset.mem_Icc.mp hjin).1 hlt (Finset.mem_Icc.mp hk).2
      linarith
    · have hmono : alpha n k < alpha n j := alpha_strict_mono hn hkj1 hgt hjn
      linarith
  have hAbs : ContinuousAt (fun x : ℝ => |x - alpha n j|) (alpha n k) :=
    (continuousAt_id.sub continuousAt_const).abs
  have hLog : ContinuousAt (fun x : ℝ => Real.log |x - alpha n j|) (alpha n k) :=
    hAbs.log (abs_ne_zero.mpr hne)
  simpa using hLog

/-- `x ↦ n·U^μ(x) + Σ_{j≠k} log|x−α_j|` is continuous at `α_k` (for
`n ≥ 2`, `k ∈ Icc 1 n`). -/
private lemma continuousAt_g (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : k ∈ Finset.Icc 1 n) :
    ContinuousAt (fun x : ℝ =>
      (n : ℝ) * logPotential muS (x : ℂ) +
        (∑ j ∈ (Finset.Icc 1 n).erase k, Real.log |x - alpha n j|)) (alpha n k) := by
  have hn1 : 1 ≤ n := by omega
  have hUcont : Continuous (fun x : ℝ => logPotential muS (x : ℂ)) := by
    simpa [muS] using logPotential_continuous_real
  have hA : ContinuousAt (fun x : ℝ => (n : ℝ) * logPotential muS (x : ℂ)) (alpha n k) :=
    (continuousAt_const.mul hUcont.continuousAt)
  exact hA.add (continuousAt_log_erase_sum n hn1 k hk)


/-- Any two distinct roots `alpha n k`, `alpha n j` (`1 ≤ k, j ≤ n`) are
separated by a positive polynomial gap. -/
private lemma roots_pairwise_separated (n : ℕ) (hn : 2 ≤ n) :
    ∃ s : ℝ, 0 < s ∧ ∀ k : ℕ, k ∈ Finset.Icc 1 n → ∀ j : ℕ,
      j ∈ Finset.Icc 1 n → k ≠ j → s ≤ |alpha n k - alpha n j| := by
  rcases exists_spacing with ⟨Csp, hCsp1, hCsp⟩
  let s : ℝ := (Csp * (n : ℝ))⁻¹ ^ 2
  have hn1 : 1 ≤ n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hCspR : 0 < Csp := by linarith
  have hs : 0 < s := by
    dsimp [s]
    exact pow_pos (inv_pos.mpr (mul_pos hCspR hnR)) 2
  refine ⟨s, hs, ?_⟩
  have hsep_lt : ∀ {k j : ℕ}, k ∈ Finset.Icc 1 n → j ∈ Finset.Icc 1 n → k < j →
      s ≤ |alpha n k - alpha n j| := by
    intro k j hk hj hlt
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    have hmono : alpha n k < alpha n j := alpha_strict_mono hn1 hk1 hlt hjn
    have hle : k ≤ j - 1 := by omega
    have htel := Finset.sum_Icc_sub (m := k) (n := j - 1) hle (fun i : ℕ => alpha n i)
    have hjj : (j - 1) + 1 = j := by omega
    have hsub : alpha n j - alpha n k =
        (∑ i ∈ Finset.Icc k (j - 1), (alpha n (i + 1) - alpha n i)) := by
      rw [htel, hjj]
    have hsum_le : s ≤ (∑ i ∈ Finset.Icc k (j - 1), (alpha n (i + 1) - alpha n i)) := by
      have hterms : ∀ i ∈ Finset.Icc k (j - 1),
          s ≤ alpha n (i + 1) - alpha n i := by
        intro i hi
        have hki : k ≤ i := (Finset.mem_Icc.mp hi).1
        have hii : i ≤ j - 1 := (Finset.mem_Icc.mp hi).2
        have hi1 : 1 ≤ i := by omega
        have hin : i < n := by omega
        exact hCsp n hn i hi1 hin
      have hsums : (∑ i ∈ Finset.Icc k (j - 1), s) ≤
          (∑ i ∈ Finset.Icc k (j - 1), (alpha n (i + 1) - alpha n i)) :=
        Finset.sum_le_sum (by intro i hi; exact hterms i hi)
      have hcard1 : (1 : ℝ) ≤ ((Finset.Icc k (j - 1)).card : ℝ) := by
        have hc : 1 ≤ (Finset.Icc k (j - 1)).card := by
          rw [Nat.card_Icc]
          omega
        exact_mod_cast hc
      calc
        s = (1 : ℝ) * s := by ring
        _ ≤ ((Finset.Icc k (j - 1)).card : ℝ) * s := by
              exact mul_le_mul_of_nonneg_right hcard1 (le_of_lt hs)
        _ = (∑ i ∈ Finset.Icc k (j - 1), s) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (∑ i ∈ Finset.Icc k (j - 1), (alpha n (i + 1) - alpha n i)) := hsums
    calc
      s ≤ (∑ i ∈ Finset.Icc k (j - 1), (alpha n (i + 1) - alpha n i)) := hsum_le
      _ = alpha n j - alpha n k := hsub.symm
      _ = |alpha n j - alpha n k| := (abs_of_pos (sub_pos.mpr hmono)).symm
      _ = |alpha n k - alpha n j| := abs_sub_comm _ _
  intro k hk j hj hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hsep_lt hk hj hlt
  · have h1 : s ≤ |alpha n j - alpha n k| := hsep_lt hj hk hgt
    rwa [abs_sub_comm] at h1


/-- The log |P| + nU quantity is O(log n) at every root (energy half, step 1). -/
theorem root_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, k ∈ Finset.Icc 1 n →
      |(n : ℝ) * logPotential muS ((alpha n k : ℝ) : ℂ) +
          (∑ j ∈ (Finset.Icc 1 n).erase k, Real.log |alpha n k - alpha n j|)|
        ≤ C * Real.log ((n : ℝ) + 2) := by
  rcases approx_potential_bound with ⟨C, hCpos, hMain⟩
  refine ⟨C, hCpos, ?_⟩
  intro n hn k hk
  let a : ℝ := alpha n k
  let M : ℝ := C * Real.log ((n : ℝ) + 2)
  let g : ℝ → ℝ := fun x : ℝ =>
    (n : ℝ) * logPotential muS (x : ℂ) +
      (∑ j ∈ (Finset.Icc 1 n).erase k, Real.log |x - alpha n j|)
  have haIcc : a ∈ Set.Icc aSerre bSerre := by
    dsimp [a]
    exact alpha_mem_Icc (by omega : 1 ≤ n) (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
  rcases roots_pairwise_separated n hn with ⟨s, hs0, hsep⟩
  have hMain' : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → 0 < rho n x →
      |(n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
          - Real.log (rho n x)| ≤ M := by
    intro x hxI hrho
    simpa [M] using hMain n hn x hxI hrho
  have hNear : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → x ≠ a → |x - a| < s / 2 →
      |g x| ≤ M := by
    intro x hxI hxa hxc
    have hsep' : ∀ j : ℕ, j ∈ Finset.Icc 1 n → j ≠ k → s ≤ |alpha n k - alpha n j| := by
      intro j hj hjk
      exact hsep k hk j hj (Ne.symm hjk)
    have hb := abs_bound_at_close hn hMain' hs0 hsep' hk x hxI hxa (by simpa [a] using hxc)
    simpa [g] using hb
  have hg : ContinuousAt g a := by
    dsimp [g, a]
    exact continuousAt_g n hn k hk
  let T : Set ℝ := ((Set.Icc aSerre bSerre ∩ {x : ℝ | |x - a| < s / 2}) \ {a})
  have hTcl : a ∈ closure T := by
    dsimp [T]
    exact mem_closure_punct_Icc_ball haIcc (by linarith)
  have hAll : ∀ y ∈ T, |g y| ≤ M := by
    intro y hy
    have hyI : y ∈ Set.Icc aSerre bSerre := (hy.1).1
    have hyB : |y - a| < s / 2 := by simpa using (hy.1).2
    have hyn : y ≠ a := by simpa using hy.2
    exact hNear y hyI hyn hyB
  have hAbs : |g a| ≤ M := abs_le_of_eventually_abs_le hTcl hg hAll
  simpa [g, a, M] using hAbs

end Submission.EnergyRootBound
