import Mathlib
import Submission.S5_sHat
import Submission.S5Tele

/-! Claim 3 (paper), left side: for arcs at distance ≥ π/n to the LEFT of θ0
(`hi ≤ θ0 − π/n`), `Σ |∫_{I_i} sin(2n(θ−θ0))/(θ−θ0)| ≤ 1/π`.

Ingredient: `S5.arc_LK_far_bound` gives per-arc
`|∫_I LK| ≤ |1/(hi−θ0) − 1/(lo−θ0)|/n` (already proven in Submission.S5),
and `1/(θ−θ0)` is antitone on the arcs left of θ0 (`S5.inv_sub_anti`).
Telescope over the filter `{i | hi ≤ θ0 − π/n}` via
`S5Tele.sum_var_le_anti` with `A = qA n`, `B = θ0 − π/n`
(only when the filter is non-empty, in which case `qA n ≤ B`; otherwise the
sum is 0), and `h(θ) = 1/(θ−θ0)`: the result is
`≤ (1/n)·|h(B)−h(A)| = (1/n)(n/π + 1/(qA−θ0)) ≤ 1/π`.  -/

noncomputable section
open scoped BigOperators
open MeasureTheory
set_option autoImplicit false

/- This mathlib revision spells big-operator sums `∑ x ∈ s, ...` (there is no
`∑ x in s, ...`).  The statement below uses the `in` spelling, so provide a
local macro implementing it. -/
syntax "∑ " ident " in " term ", " term : term
macro_rules
  | `(∑ $x in $s, $b) => `(∑ $x ∈ $s, $b)

namespace Submission
namespace S5C3L

/-- `1/(θ−θ0)` is antitone while `θ < θ0`: `x ≤ y < θ0 ⟹ 1/(y−θ0) ≤ 1/(x−θ0)` -/
lemma inv_sub_anti_left {θ0 x y : ℝ} (hxy : x ≤ y) (hy : y < θ0) :
    1 / (y - θ0) ≤ 1 / (x - θ0) := by
  have hx0 : x - θ0 ≠ 0 := by linarith
  have hy0 : y - θ0 ≠ 0 := by linarith
  have hfrac : 1 / (y - θ0) - 1 / (x - θ0) = (x - y) / ((y - θ0) * (x - θ0)) := by
    field_simp [hy0, hx0]
    ring
  have hden : 0 < (y - θ0) * (x - θ0) := by
    have hyneg : y - θ0 < 0 := by linarith
    have hxneg : x - θ0 < 0 := by linarith
    exact mul_pos_of_neg_of_neg hyneg hxneg
  have hle0 : 1 / (y - θ0) - 1 / (x - θ0) ≤ 0 := by
    rw [hfrac]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
  linarith

/-- Claim 3 (left side) -/
theorem left_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i in (Finset.univ.filter (fun i : Fin N => (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ))),
        |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|)
      ≤ 1 / Real.pi := by
  classical
  let h : ℝ → ℝ := fun θ => 1 / (θ - θ0)
  let B : ℝ := θ0 - Real.pi / (n : ℝ)
  let P : Fin N → Prop := fun i => (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ)
  let s : Finset (Fin N) := Finset.univ.filter P
  have hnpos : 0 < (n : ℝ) := S5.nR_pos hn16
  have hB_lt_θ0 : B < θ0 := by
    have hπn : 0 < Real.pi / (n : ℝ) := by positivity
    dsimp [B]
    linarith
  have hper : ∀ i : Fin N, i ∈ s → (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) := by
    intro i hi
    have hmem : i ∈ Finset.univ.filter P := by
      simpa [s, P] using hi
    exact (Finset.mem_filter.mp hmem).2
  change (∑ i ∈ s, |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|) ≤ 1 / Real.pi
  by_cases hS : s = ∅
  · rw [hS]
    simp
    simpa using (Real.pi_pos.le : (0 : ℝ) ≤ Real.pi)
  · have hsNE : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    rcases hsNE with ⟨i0, hi0mem⟩
    have hPi0 : (F.arc i0).hi ≤ θ0 - Real.pi / (n : ℝ) := (Finset.mem_filter.mp hi0mem).2
    have hAB : S5.qA n ≤ B := by
      have h1 := S5.arc_lo_ge_qA hn16 F i0        -- qA ≤ lo i0
      have h2 := Family.Grid.lo_le_hi (F.arc i0)  -- lo i0 ≤ hi i0
      dsimp [B]
      linarith
    have hanti : AntitoneOn h (Set.Icc (S5.qA n) B) := by
      intro x hx y hy hxy
      dsimp [h]
      exact inv_sub_anti_left (θ0 := θ0) hxy (by linarith [hy.2, hB_lt_θ0])
    have htele : (∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)|) ≤
        |h B - h (S5.qA n)| := by
      have hh := S5Tele.sum_var_le_anti (s := s) (lo := fun i : Fin N => (F.arc i).lo)
        (hi := fun i : Fin N => (F.arc i).hi) (A := S5.qA n) (B := B) hAB
        (hA := fun i hi => S5.arc_lo_ge_qA hn16 F i)
        (hB := hper)
        (hle := fun i hi => Family.Grid.lo_le_hi (F.arc i))
        (hsep := fun i hi j hj hij =>
          (S5.arc_sep hn16 F hij).elim
            (fun hlt => Or.inl (le_of_lt hlt))
            (fun hlt => Or.inr (le_of_lt hlt)))
        (h := h) hanti
      simpa using hh
    have hsum_step : (∑ i ∈ s,
          |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|)
        ≤ ∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)| / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hfar : (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨
          θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo := Or.inl (hper i hi)
      have hb := S5.arc_LK_far_bound n N hn16 F i hθ0a hθ0b hfar
      simpa [h] using hb
    have hval : |h B - h (S5.qA n)| = h (S5.qA n) - h B := by
      rw [abs_sub_comm]
      apply abs_of_nonneg
      rw [sub_nonneg]
      dsimp [h]
      exact inv_sub_anti_left (θ0 := θ0) (x := S5.qA n) (y := B) hAB (by linarith [hB_lt_θ0])
    have hA_le_0 : 1 / (S5.qA n - θ0) ≤ 0 := by
      have hden : S5.qA n - θ0 < 0 := by
        have hAB' : S5.qA n ≤ θ0 - Real.pi / (n : ℝ) := by
          dsimp [B] at hAB
          exact hAB
        have hπn : 0 < Real.pi / (n : ℝ) := by positivity
        linarith
      rw [div_le_iff_of_neg hden]
      norm_num
    have hB_val : 1 / (B - θ0) = - (n : ℝ) / Real.pi := by
      have hπn : Real.pi / (n : ℝ) ≠ 0 :=
        div_ne_zero (ne_of_gt Real.pi_pos) (ne_of_gt hnpos)
      dsimp [B]
      field_simp [hπn]
      ring
    have hfin : h (S5.qA n) - h B ≤ (n : ℝ) / Real.pi := by
      dsimp [h]
      calc
        1 / (S5.qA n - θ0) - 1 / (B - θ0)
            = 1 / (S5.qA n - θ0) + (n : ℝ) / Real.pi := by
                rw [hB_val]
                ring
        _ ≤ 0 + (n : ℝ) / Real.pi := by
                exact add_le_add hA_le_0 (le_rfl : (n : ℝ) / Real.pi ≤ (n : ℝ) / Real.pi)
        _ = (n : ℝ) / Real.pi := by ring
    have habs_le : |h B - h (S5.qA n)| ≤ (n : ℝ) / Real.pi := by
      rw [hval]
      exact hfin
    have hdiv : |h B - h (S5.qA n)| / (n : ℝ) ≤ 1 / Real.pi := by
      calc
        |h B - h (S5.qA n)| / (n : ℝ) ≤ ((n : ℝ) / Real.pi) / (n : ℝ) :=
          div_le_div_of_nonneg_right habs_le (le_of_lt hnpos)
        _ = 1 / Real.pi := by field_simp [ne_of_gt hnpos]
    calc
      (∑ i ∈ s, |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|)
          ≤ ∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)| / (n : ℝ) := hsum_step
      _ = (∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)|) / (n : ℝ) := by
          rw [← Finset.sum_div]
      _ ≤ |h B - h (S5.qA n)| / (n : ℝ) :=
          div_le_div_of_nonneg_right htele (le_of_lt hnpos)
      _ ≤ 1 / Real.pi := hdiv

end S5C3L
end Submission
