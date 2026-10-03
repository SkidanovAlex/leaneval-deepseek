import Mathlib
import Submission.Work.A3.Weil.Defs

/-!
# The support decomposition of the iterated autocorrelation of a phase sequence

Let `φ : ℤ → ℝ` be a phase and `u = phaseSeq φ N` the zero-extended phase sequence
`m ↦ e(φ m) = exp (2πi φ m)` on the window `wRange N = [0, N-1]`.  Unwinding the recursion,
the `k`-fold autocorrelation `iterCorr k l u n` is the signed product

`∏_{ε : Fin k → Bool} (u (n + ∑_{i, ε i} l i)) ^ (±1)`,

so it vanishes as soon as one of the shifted points `n + ∑_{i ∈ A} l i` (`A ⊆ {0,…,k-1}`
running over the `2^k` subsets of shifts) leaves the window.  The set of `n` for which *all*
of them stay inside is the integer interval

`[a, b] = [max 0 (∑ i, max 0 (-l i)), min (N-1) (N-1 - ∑ i, max 0 (l i))] ⊆ wRange N`,

and on it the signed product collapses to the single exponential
`e (iterDiff k l φ n)` of the `k`-fold difference of the phase.

This is the structural half of the geometric-sum bound for the `k`-fold correlation
(`Work.A3.Weil.norm_iterCorr_phase_le`); the other half is the first-derivative test for an
affine phase (`Work.A3.Weil.norm_sum_exp_affine_le_geomBound`).

## Implementation

The set of involved shifts is indexed by `ε : Fin k → Bool`, with `shiftSum l ε` the
corresponding partial sum.  The predicate `Good l N n` says that all the shifted points
`n + shiftSum l ε` lie in `wRange N`; the main work is

* `good_iff_mem_Icc`: `Good l N n` is equivalent to `n ∈ Icc a b` — the `2^k` shift
  conditions collapse to the single interval `[a,b]` because the partial sums `shiftSum l ε`
  range exactly over `[∑ i, min 0 (l i), ∑ i, max 0 (l i)]`;
* `iterCorr_phaseSeq_eq`: the pointwise formula
  `iterCorr k l (phaseSeq φ N) n = if Good l N n then e (iterDiff k l φ n) else 0`,
  proved by induction on `k`, using the recursion `Good (k+1) ↔ Good k (·) ∧ Good k (· + l k)`
  (`good_succ`) and the multiplicativity identity
  `e (ψ (x+h)) * conj (e (ψ x)) = e (ψ (x+h) - ψ x)` (`EphaseW_mul_star`);
* the target, obtained by summing the pointwise formula over `wRange N`.
-/

namespace Work.A3.Weil

open Finset
open scoped BigOperators
open Classical

noncomputable section

/-! ## The shifts attached to a `Bool`-valued index -/

/-- The shift `∑ i, if ε i then l i else 0` attached to `ε : Fin k → Bool`: the partial sum
of the shifts `l i` over those `i` with `ε i = true`. -/
def shiftSum {k : ℕ} (l : Fin k → ℤ) (ε : Fin k → Bool) : ℤ :=
  ∑ i, if ε i then l i else 0

/-- The total negative part `∑ i, max 0 (-(l i))` of the shifts: the largest amount by which a
partial sum `shiftSum l ε` can exceed `0` on the left. -/
def loIdx {k : ℕ} (l : Fin k → ℤ) : ℤ := ∑ i, max 0 (-(l i))

/-- The total positive part `∑ i, max 0 (l i)` of the shifts. -/
def hiIdx {k : ℕ} (l : Fin k → ℤ) : ℤ := ∑ i, max 0 (l i)

/-- `Good l N n` holds when all the points `n + shiftSum l ε`, `ε : Fin k → Bool`, lie in the
window `wRange N`. -/
def Good {k : ℕ} (l : Fin k → ℤ) (N : ℕ) (n : ℤ) : Prop :=
  ∀ ε : Fin k → Bool, n + shiftSum l ε ∈ wRange N

/-- The unit exponential `e (φ n) = exp (((2 * π * φ n : ℝ) : ℂ) * I)` of a real phase. -/
def EphaseW (φ : ℤ → ℝ) : ℤ → ℂ :=
  fun m => Complex.exp (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I)

/-! ## The arithmetic of the shifts -/

lemma shiftSum_false {k : ℕ} (l : Fin k → ℤ) : shiftSum l (fun _ => false) = 0 := by
  simp [shiftSum]

lemma shiftSum_le_hiIdx {k : ℕ} (l : Fin k → ℤ) (ε : Fin k → Bool) :
    shiftSum l ε ≤ hiIdx l := by
  rw [shiftSum, hiIdx]
  exact Finset.sum_le_sum (fun i _ => by by_cases h : ε i <;> simp [h])

lemma neg_loIdx_le_shiftSum {k : ℕ} (l : Fin k → ℤ) (ε : Fin k → Bool) :
    -loIdx l ≤ shiftSum l ε := by
  rw [shiftSum, loIdx, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases h : ε i
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

/-- The partial sums `shiftSum l ε` attain the lower endpoint `-loIdx l`. -/
lemma exists_shiftSum_eq_neg_loIdx {k : ℕ} (l : Fin k → ℤ) :
    ∃ ε : Fin k → Bool, shiftSum l ε = -loIdx l := by
  refine ⟨fun i => decide (l i < 0), ?_⟩
  rw [shiftSum, loIdx, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : l i < 0
  · have h' : 0 ≤ -(l i) := by omega
    simp [h, max_eq_right h']
  · have h' : -(l i) ≤ 0 := by omega
    simp [h, max_eq_left h']

/-- The partial sums `shiftSum l ε` attain the upper endpoint `hiIdx l`. -/
lemma exists_shiftSum_eq_hiIdx {k : ℕ} (l : Fin k → ℤ) :
    ∃ ε : Fin k → Bool, shiftSum l ε = hiIdx l := by
  refine ⟨fun i => decide (0 < l i), ?_⟩
  rw [shiftSum, hiIdx]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : 0 < l i
  · have h' : 0 ≤ l i := by omega
    simp [h, max_eq_right h']
  · have h' : l i ≤ 0 := by omega
    simp [h, max_eq_left h']

/-- **The `2^k` shift conditions collapse to one interval.**  All the shifted points
`n + shiftSum l ε` lie in `wRange N` if and only if
`n ∈ [max 0 (loIdx l), min (N-1) (N-1 - hiIdx l)]`. -/
lemma good_iff_mem_Icc {k : ℕ} (l : Fin k → ℤ) (N : ℕ) (n : ℤ) :
    Good l N n ↔
      n ∈ Finset.Icc (max 0 (loIdx l)) (min ((N : ℤ) - 1) ((N : ℤ) - 1 - hiIdx l)) := by
  constructor
  · intro h
    obtain ⟨εl, hεl⟩ := exists_shiftSum_eq_neg_loIdx l
    obtain ⟨εh, hεh⟩ := exists_shiftSum_eq_hiIdx l
    have h0 := h (fun _ => false)
    rw [shiftSum_false, add_zero, wRange, Finset.mem_Icc] at h0
    have hl := h εl
    have hh := h εh
    rw [hεl, wRange, Finset.mem_Icc] at hl
    rw [hεh, wRange, Finset.mem_Icc] at hh
    rw [Finset.mem_Icc]
    omega
  · intro hn ε
    have hb1 := neg_loIdx_le_shiftSum l ε
    have hb2 := shiftSum_le_hiIdx l ε
    rw [Finset.mem_Icc] at hn
    rw [wRange, Finset.mem_Icc]
    omega

/-! ## The recursion of `Good` along the last shift -/

lemma shiftSum_snoc {k : ℕ} (l : Fin (k + 1) → ℤ) (ε : Fin k → Bool) (b : Bool) :
    shiftSum l (Fin.snoc ε b) =
      shiftSum (fun i => l i.castSucc) ε + (if b then l (Fin.last k) else 0) := by
  simp only [shiftSum]
  rw [Fin.sum_univ_castSucc]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by simp [Fin.snoc_castSucc])
  · simp [Fin.snoc_last]

/-- Splitting the shift conditions according to the last coordinate. -/
lemma good_succ {k : ℕ} (l : Fin (k + 1) → ℤ) (N : ℕ) (n : ℤ) :
    Good l N n ↔ Good (fun i : Fin k => l i.castSucc) N n ∧
      Good (fun i : Fin k => l i.castSucc) N (n + l (Fin.last k)) := by
  constructor
  · intro h
    constructor
    · intro ε
      have h' := h (Fin.snoc ε false)
      rw [shiftSum_snoc, if_neg (by simp)] at h'
      simpa using h'
    · intro ε
      have h' := h (Fin.snoc ε true)
      rw [shiftSum_snoc, if_pos rfl] at h'
      simpa only [add_assoc, add_comm, add_left_comm] using h'
  · rintro ⟨h1, h2⟩ ε
    have heq : ε = Fin.snoc (Fin.init ε) (ε (Fin.last k)) := (Fin.snoc_init_self ε).symm
    rw [heq, shiftSum_snoc]
    by_cases hb : ε (Fin.last k)
    · rw [if_pos hb]
      have h' := h2 (Fin.init ε)
      simpa only [add_assoc, add_comm, add_left_comm] using h'
    · rw [if_neg hb]
      have h' := h1 (Fin.init ε)
      simpa using h'

/-! ## The exponential identity for one shift -/

/-- Conjugating the exponential of a shifted phase telescopes to the exponential of the
difference: `e (ψ (x+h)) * conj (e (ψ x)) = e (ψ (x+h) - ψ x)`. -/
lemma EphaseW_mul_star (h : ℤ) (D : ℤ → ℝ) (x : ℤ) :
    EphaseW D (x + h) * star (EphaseW D x) = EphaseW (fun y => D (y + h) - D y) x := by
  simp only [EphaseW, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-! ## The pointwise formula -/

/-- **The autocorrelation of a zero-extended phase sequence.**  Away from the interval
`[max 0 (loIdx l), min (N-1) (N-1 - hiIdx l)]` the `k`-fold autocorrelation vanishes, and on it
it is the exponential `e (iterDiff k l φ ·)` of the `k`-fold difference of the phase. -/
theorem iterCorr_phaseSeq_eq : ∀ (k : ℕ) (l : Fin k → ℤ) (φ : ℤ → ℝ) (N : ℕ) (n : ℤ),
    iterCorr k l (phaseSeq φ N) n
      = if Good l N n then EphaseW (iterDiff k l φ) n else 0 := by
  classical
  intro k
  induction k with
  | zero =>
      intro l φ N n
      have hG : Good l N n ↔ n ∈ wRange N := by
        constructor
        · intro h; simpa [Good, shiftSum] using h (fun i => Fin.elim0 i)
        · intro h ε; simpa [Good, shiftSum] using h
      rw [hG]
      simp only [iterCorr, iterDiff, EphaseW, phaseSeq]
      by_cases h : n ∈ wRange N <;> simp [h]
  | succ k ih =>
      intro l φ N n
      simp only [iterCorr]
      rw [ih (fun i => l i.castSucc) φ N (n + l (Fin.last k)), ih (fun i => l i.castSucc) φ N n]
      have hgood := good_succ l N n
      by_cases h1 : Good (fun i => l i.castSucc) N (n + l (Fin.last k))
      · by_cases h2 : Good (fun i => l i.castSucc) N n
        · rw [if_pos h1, if_pos h2, if_pos (hgood.mpr ⟨h2, h1⟩)]
          rw [EphaseW_mul_star]
          rfl
        · rw [if_neg h2, if_neg (fun hG => h2 (hgood.mp hG).1)]
          simp
      · rw [if_neg h1, if_neg (fun hG => h1 (hgood.mp hG).2)]
        by_cases h2 : Good (fun i => l i.castSucc) N n
        · rw [if_pos h2]; simp
        · rw [if_neg h2]; simp

/-- **Structural form of the `k`-fold correlation of a phase sequence.**  The `k`-fold
autocorrelation of the zero-extended phase sequence `phaseSeq φ N`, summed over `wRange N`,
equals the sum of the exponentials `e (iterDiff k l φ n)` over a sub-interval
`Icc a b ⊆ wRange N`. -/
theorem iterCorr_phaseSeq_eq_sum_Icc (k : ℕ) (l : Fin k → ℤ) (φ : ℤ → ℝ) (N : ℕ) :
    ∃ a b : ℤ, Finset.Icc a b ⊆ Work.A3.Weil.wRange N ∧
      ∑ n ∈ Work.A3.Weil.wRange N,
          Work.A3.Weil.iterCorr k l (Work.A3.Weil.phaseSeq φ N) n
        = ∑ n ∈ Finset.Icc a b,
            Complex.exp (((2 * Real.pi * Work.A3.Weil.iterDiff k l φ n : ℝ) : ℂ) * Complex.I) := by
  classical
  have hsub : Finset.Icc (max 0 (loIdx l)) (min ((N : ℤ) - 1) ((N : ℤ) - 1 - hiIdx l))
      ⊆ Work.A3.Weil.wRange N := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Work.A3.Weil.wRange, Finset.mem_Icc]
    exact ⟨le_trans (le_max_left _ _) hn.1, le_trans hn.2 (min_le_left _ _)⟩
  refine ⟨max 0 (loIdx l), min ((N : ℤ) - 1) ((N : ℤ) - 1 - hiIdx l), hsub, ?_⟩
  have hiff : ∀ n : ℤ, Good l N n ↔
      n ∈ Finset.Icc (max 0 (loIdx l)) (min ((N : ℤ) - 1) ((N : ℤ) - 1 - hiIdx l)) :=
    fun n => good_iff_mem_Icc l N n
  calc ∑ n ∈ Work.A3.Weil.wRange N, Work.A3.Weil.iterCorr k l (Work.A3.Weil.phaseSeq φ N) n
      = ∑ n ∈ Work.A3.Weil.wRange N,
          (if n ∈ Finset.Icc (max 0 (loIdx l)) (min ((N : ℤ) - 1) ((N : ℤ) - 1 - hiIdx l))
            then Complex.exp (((2 * Real.pi * Work.A3.Weil.iterDiff k l φ n : ℝ) : ℂ) * Complex.I)
            else 0) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [iterCorr_phaseSeq_eq k l φ N n]
        simp only [EphaseW]
        by_cases h : n ∈ Finset.Icc (max 0 (loIdx l)) (min ((N : ℤ) - 1) ((N : ℤ) - 1 - hiIdx l))
        · rw [if_pos ((hiff n).mpr h), if_pos h]
        · rw [if_neg (fun hG => h ((hiff n).mp hG)), if_neg h]
    _ = ∑ n ∈ Work.A3.Weil.wRange N ∩
          Finset.Icc (max 0 (loIdx l)) (min ((N : ℤ) - 1) ((N : ℤ) - 1 - hiIdx l)),
          Complex.exp (((2 * Real.pi * Work.A3.Weil.iterDiff k l φ n : ℝ) : ℂ) * Complex.I) :=
        Finset.sum_ite_mem _ _ _
    _ = ∑ n ∈ Finset.Icc (max 0 (loIdx l)) (min ((N : ℤ) - 1) ((N : ℤ) - 1 - hiIdx l)),
          Complex.exp (((2 * Real.pi * Work.A3.Weil.iterDiff k l φ n : ℝ) : ℂ) * Complex.I) := by
        rw [Finset.inter_eq_right.mpr hsub]

end

end Work.A3.Weil
