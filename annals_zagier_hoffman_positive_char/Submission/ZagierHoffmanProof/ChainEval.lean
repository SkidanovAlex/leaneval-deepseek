import Submission.ZagierHoffmanProof.LSeriesEvalDepth

/-!
# The chain-sum normalisation of the `L`-series evaluation (C3 of the ζ_A ↔ CMPL bridge)

`LSeriesEvalDepth.evalSeriesGen_atLrcutGen` evaluates the depth-`r` `L`-series as `evalIter`, whose
recursion peels the **first** factor of the tuple with the outermost `tsum` and keeps the running
index as an *offset* (`N + i`).

The ζ_A side of the bridge (Dac (4.2) / AT09 (2.4.1)) is instead the sum over the *chain*
`d_1 > d_2 > ⋯ > d_r ≥ 0` with the **smallest** index outermost.  To compare the two we reformulate
`evalIter` as the chain sum over the *indices themselves*:

  `evalIter θ q ω L N = ∑' d, [N ≤ d]·Y_1(d)·evalIter θ q ω L.tail (d+1)`.

This is the shape in which the ζ_A side is proved, and it is the starting point of the reordering
(see `Submission/PLAN.md`, session log).

## Main results

* `tsum_ite_le` — the half-line summation identity `∑'_d [N ≤ d]·H d = ∑'_i H (N+i)`.
* `tsum_fin_cons`, `tsum_fin_snoc` — the two way of splitting a `tsum` over `Fin (r+1) → ℕ`.
* `evalIterB`, `evalIter_eq_evalIterB`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset Filter
open scoped WithZero Topology
open SummationFilter

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-! ## §1. General summation lemmas -/

/-- **Summation over the half-line `{d | N ≤ d}`**: reindexing by `d = N + i`. -/
lemma tsum_ite_le (N : ℕ) (H : ℕ → K) :
    (∑' d : ℕ, if N ≤ d then H d else 0) = ∑' i : ℕ, H (N + i) := by
  have h1 : (fun d : ℕ => if N ≤ d then H d else 0)
      = Set.indicator {d : ℕ | N ≤ d} H := by
    funext d
    rw [Set.indicator_apply]
    simp
  rw [h1, ← _root_.tsum_subtype]
  have hbij : Function.Bijective
      (fun i : ℕ => (⟨N + i, Nat.le_add_right N i⟩ : {d : ℕ // N ≤ d})) :=
    ⟨fun i j h => by simpa using congrArg Subtype.val h,
      fun x => ⟨x.1 - N, Subtype.ext (Nat.add_sub_cancel' x.2)⟩⟩
  have h2 : (∑' x : {d : ℕ // N ≤ d}, H x.1) = ∑' i : ℕ, H (N + i) := by
    conv_lhs => rw [← Equiv.tsum_eq (Equiv.ofBijective _ hbij)
      (fun x : {d : ℕ // N ≤ d} => H x.1)]
    simp
  exact h2

/-- Splitting a `tsum` over `Fin (r+1) → ℕ` by the first coordinate. -/
theorem tsum_fin_cons {r : ℕ} {G : (Fin (r+1) → ℕ) → K} (hG : Summable G) :
    (∑' v : Fin (r+1) → ℕ, G v) = ∑' (d : ℕ) (w : Fin r → ℕ), G (Fin.cons d w) := by
  rw [← Equiv.tsum_eq (Fin.consEquiv (fun _ : Fin (r+1) => ℕ)) G]
  rw [Summable.tsum_prod]
  · rfl
  · exact (Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (r+1) => ℕ))).mpr hG

/-- Splitting a `tsum` over `Fin (r+1) → ℕ` by the last coordinate. -/
theorem tsum_fin_snoc {r : ℕ} {G : (Fin (r+1) → ℕ) → K} (hG : Summable G) :
    (∑' v : Fin (r+1) → ℕ, G v) = ∑' (d : ℕ) (w : Fin r → ℕ), G (Fin.snoc w d) := by
  rw [← Equiv.tsum_eq (Fin.snocEquiv (fun _ : Fin (r+1) => ℕ)) G]
  rw [Summable.tsum_prod]
  · rfl
  · exact (Equiv.summable_iff (Fin.snocEquiv (fun _ : Fin (r+1) => ℕ))).mpr hG

/-! ## §2. The chain form of the `L`-series evaluation -/

/-- The chain form of the iterated value: the recursion is on the indices themselves,
`evalIterB L N = ∑' d, [N ≤ d]·Y_1(d)·evalIterB L.tail (d+1)`. -/
noncomputable def evalIterB (θ : K) (q : ℕ) [FrobPow K q] (ω : PowerSeries K) :
    List (ℕ × PowerSeries K) → ℕ → K
  | [], _ => 1
  | (s, Q) :: rest, N => ∑' d : ℕ,
      (if N ≤ d then evalSeriesGen (frobTwist (R := K) (p := q) d (ω ^ s * Q)) θ else 0)
        * evalIterB θ q ω rest (d + 1)

@[simp] lemma evalIterB_nil (θ : K) (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (N : ℕ) :
    evalIterB θ q ω ([] : List (ℕ × PowerSeries K)) N = 1 := rfl

lemma evalIterB_cons (θ : K) (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (s : ℕ) (Q : PowerSeries K) (rest : List (ℕ × PowerSeries K)) (N : ℕ) :
    evalIterB θ q ω ((s, Q) :: rest) N = ∑' d : ℕ,
      (if N ≤ d then evalSeriesGen (frobTwist (R := K) (p := q) d (ω ^ s * Q)) θ else 0)
        * evalIterB θ q ω rest (d + 1) := rfl

/-- **The chain form of the depth-`r` evaluation**: replacing the running offset `N+i` by the
index `d = N+i` itself. -/
theorem evalIter_eq_evalIterB (θ : K) (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (Lst : List (ℕ × PowerSeries K)) (N : ℕ) :
    evalIter θ q ω Lst N = evalIterB θ q ω Lst N := by
  induction Lst generalizing N with
  | nil => rw [evalIter_nil, evalIterB_nil]
  | cons a rest ih =>
    obtain ⟨s, Q⟩ := a
    rw [evalIter_cons, evalIterB_cons]
    have key : ∀ i : ℕ,
        evalSeriesGen (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)) θ
          * evalIter θ q ω rest (N + i + 1)
        = evalSeriesGen (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)) θ
          * evalIterB θ q ω rest (N + i + 1) := fun i => by rw [ih (N + i + 1)]
    rw [tsum_congr key]
    rw [← tsum_ite_le (K := K) N (fun d : ℕ =>
      evalSeriesGen (frobTwist (R := K) (p := q) d (ω ^ s * Q)) θ
        * evalIterB θ q ω rest (d + 1))]
    refine tsum_congr fun d => ?_
    by_cases h : N ≤ d <;> simp [h]

end ZagierHoffmanPositiveChar
