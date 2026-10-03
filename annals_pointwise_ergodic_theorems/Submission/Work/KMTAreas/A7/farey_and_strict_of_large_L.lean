/-
# The Farey condition and the strict main-regime inequality hold for large `L`

`Work.KMTAreas.A7.lmax_le_of_not_farey` proves that in the regime

  `splitCut ρ L < N`,  `L = max (max l₁ l₂) (max k₁ k₂)`

the *failure* of the quantitative Farey (Shannon) condition `2^{k₁}·arithQ ρ l₁·8 ≤ N` forces
`L ≤ B ρ` for a bound depending on `ρ` alone.  Consequently, for all sufficiently large `L`
(hence for `L > B` with `B` chosen below) the Farey condition *holds*.

(Formally the lemma is applied with the pair `(l₁,l₂)` replaced by `(max l₁ l₂, l₂)`: this gives
the modulus `arithQ ρ (max l₁ l₂)` required below, the scale `max (max (max l₁ l₂) l₂) (max k₁ k₂)`
being the same as `max (max l₁ l₂) (max k₁ k₂)`.)

This file packages that conclusion together with the companion statement that the *strict* form
`k₁ + 2·uScale ρ L + 1 ≤ Log N` of the main-regime condition holds automatically in the regime
`splitCut ρ L < N`, again for all large `L`: from `splitCut ρ L < N` one gets
`2^{uScale ρ L} ≤ Nat.log 2 N`, and for large `L` one has `k₁ ≤ L ≤ uScale ρ L` and
`3·uScale ρ L + 1 ≤ 2^{uScale ρ L}` (the elementary `three_mul_add_one_le_two_pow`), so
`k₁ + 2·uScale ρ L + 1 ≤ 2^{uScale ρ L} ≤ Log N`.

Thus both conclusions are *uniform* once `L` exceeds a constant depending on `ρ` only; this is
what lets the large-scale analysis (`Work.KMTAreas.A7.VarpLossLarge`, `ModApprox`) state its
hypotheses unconditionally in `l₁,l₂,k₁,k₂`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lmax_le_of_not_farey
import Submission.Work.KMTAreas.A7.fiberOpVarNonFareyBounded

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open Work.Analysis.IonescuWainger
open Work.Analysis.EndVar

/-! ## Elementary arithmetic helpers -/

/-- The Ionescu–Weinger common denominator `arithQ ρ l` is monotone in the height `l`: the sets
`P_{≤l}` increase with `l` (`iwP_mono`), hence so does the lcm of the denominators. -/
theorem arithQ_mono (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : Monotone (arithQ ρ) := by
  intro l l' h
  have h1 : arithQ ρ l = iwQl ρ l := Nat.max_eq_right (Nat.succ_le_of_lt (iwQl_pos (ρ := ρ) (l := l)))
  have h2 : arithQ ρ l' = iwQl ρ l' :=
    Nat.max_eq_right (Nat.succ_le_of_lt (iwQl_pos (ρ := ρ) (l := l')))
  rw [h1, h2]
  refine Nat.le_of_dvd (iwQl_pos (ρ := ρ) (l := l')) ?_
  rw [iwQl]
  exact Finset.lcm_mono (iwP_mono hρ hρ1 h)

/-- `3u + 1 ≤ 2^u` for `u ≥ 5`. -/
theorem three_mul_add_one_le_two_pow {u : ℕ} (hu : 5 ≤ u) : 3 * u + 1 ≤ 2 ^ u := by
  induction u with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n <;> norm_num at *
    · have hih := ih h
      rw [pow_succ]
      omega

/-- For `ρ > 0` and all large `L` the scale count `uScale ρ L = ⌊2^{2ρL}⌋` dominates both `L`
and the constant `5`. -/
theorem exists_uScale_ge (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → L ≤ uScale ρ L ∧ 5 ≤ uScale ρ L := by
  obtain ⟨L₀, hL₀⟩ := pow_dominates_linear ρ hρ 5
  refine ⟨L₀, fun L hL => ?_⟩
  have h := hL₀ L hL
  have hLle : ((L : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by linarith
  have h5le : (5 : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by linarith
  have hu : uScale ρ L = ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋₊ := by
    simp only [uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat, Nat.cast_one, one_mul]
  rw [hu]
  exact ⟨Nat.le_floor hLle, Nat.le_floor h5le⟩

/-- `splitCut ρ L < N` together with `L` large forces the strict main-regime inequality
`k₁ + 2·uScale ρ L + 1 ≤ Log N` whenever `k₁ ≤ L`. -/
theorem strict_of_splitCut_lt {ρ : ℝ} (_hρ : 0 < ρ) {k₁ L N : ℕ} (hk₁ : k₁ ≤ L)
    (hL : L ≤ uScale ρ L) (h5 : 5 ≤ uScale ρ L)
    (hsplit : splitCut ρ L < N) :
    k₁ + 2 * uScale ρ L + 1 ≤ (logN N).toNat := by
  have hsplit' : 2 ^ (2 ^ uScale ρ L) < N := by simpa only [splitCut, uScale] using hsplit
  -- `2 ^ uScale ρ L ≤ Log N`
  have h2u_le_log : 2 ^ uScale ρ L ≤ Nat.log 2 N :=
    Nat.le_log_of_pow_le (by norm_num) (le_of_lt hsplit')
  have hlog1 : 2 ^ uScale ρ L ≤ Nat.log 2 (max N 2) :=
    h2u_le_log.trans (Nat.log_mono_right (le_max_left N 2))
  have hlogN : (logN N).toNat = Nat.log 2 (max N 2) := by
    rw [Work.Analysis.EndVar.logN, Int.toNat_natCast]
  rw [hlogN]
  have h3 := three_mul_add_one_le_two_pow h5
  omega

/-! ## The main statement -/

theorem farey_and_strict_of_large_L (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ B : ℕ, ∀ (l₁ l₂ k₁ k₂ N : ℕ),
      Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N →
      B < max (max l₁ l₂) (max k₁ k₂) →
      ((2 : ℝ) ^ k₁ * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) * 8 ≤ (N : ℝ)) ∧
        k₁ + 2 * Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) + 1
          ≤ (Work.Analysis.EndVar.logN N).toNat := by
  obtain ⟨Bfun, hBfun⟩ := lmax_le_of_not_farey ρ hρ hρ1
  obtain ⟨L₀, hL₀⟩ := exists_uScale_ge ρ hρ
  refine ⟨max (Bfun ρ) L₀, ?_⟩
  intro l₁ l₂ k₁ k₂ N hsplit hB
  -- `L = max (max l₁ l₂) (max k₁ k₂)` is large, so both the `ρ`-bound and `L₀` are exceeded
  have hBlt : Bfun ρ < max (max l₁ l₂) (max k₁ k₂) := lt_of_le_of_lt (le_max_left _ _) hB
  have hL₀L : L₀ ≤ max (max l₁ l₂) (max k₁ k₂) :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hB)
  have hk₁L : k₁ ≤ max (max l₁ l₂) (max k₁ k₂) := by omega
  -- `lmax_le_of_not_farey` is stated with `arithQ ρ l₁`; instantiating it at `l₁ := max l₁ l₂`
  -- gives the required modulus `arithQ ρ (max l₁ l₂)` (`max` is idempotent).
  have hmaxeq : max (max (max l₁ l₂) l₂) (max k₁ k₂) = max (max l₁ l₂) (max k₁ k₂) := by omega
  have hsplit' : splitCut ρ (max (max (max l₁ l₂) l₂) (max k₁ k₂)) < N := by
    rw [hmaxeq]; exact hsplit
  -- **Part (1): the Farey condition.**  Its failure would force `L ≤ Bfun ρ`.
  have hfarey : (2 : ℝ) ^ k₁ * (arithQ ρ (max l₁ l₂) : ℝ) * 8 ≤ (N : ℝ) := by
    by_contra hnot
    have hle := hBfun (max l₁ l₂) l₂ k₁ k₂ N hsplit' hnot
    rw [hmaxeq] at hle
    omega
  -- **Part (2): the strict main-regime inequality.**  `splitCut ρ L < N` already gives it.
  have hu := hL₀ (max (max l₁ l₂) (max k₁ k₂)) hL₀L
  exact ⟨hfarey, strict_of_splitCut_lt hρ hk₁L hu.1 hu.2 hsplit⟩

end Work.KMTAreas.A7
