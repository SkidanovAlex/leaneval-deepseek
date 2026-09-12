import Mathlib
import Submission.S5_sHat
import Submission.S5Tele

/-! Claim 3 (paper), right side: for arcs at distance ≥ π/n to the RIGHT of θ0
(`θ0 + π/n ≤ lo`), `Σ |∫_{I_i} sin(2n(θ−θ0))/(θ−θ0)| ≤ 1/π`.

Ingredient: `S5.arc_LK_far_bound` (per-arc bound) and
`S5.inv_sub_anti` (`1/(θ−θ0)` antitone right of θ0).  Telescope over the
filter `{i | θ0 + π/n ≤ lo}` via `S5Tele.sum_var_le_anti` with
`A = θ0 + π/n`, `B = qB n`, `h(θ)=1/(θ−θ0)`: result
`≤ (1/n)·|h(B)−h(A)| = (1/n)(n/π − 1/(qB−θ0)) ≤ 1/π`.  -/

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
namespace S5C3R

/-- `1/(θ−θ0)` is antitone while `θ0 < θ`: `θ0 < x ≤ y ⟹ 1/(y−θ0) ≤ 1/(x−θ0)` -/
lemma inv_sub_anti_right {θ0 x y : ℝ} (hx0 : 0 < x - θ0) (hxy : x ≤ y) :
    1 / (y - θ0) ≤ 1 / (x - θ0) := by
  exact S5.inv_rev_of_pos hx0 (by linarith)

/-- Claim 3 (right side) -/
theorem right_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i in (Finset.univ.filter (fun i : Fin N => θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo)),
        |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|)
      ≤ 1 / Real.pi := by
  classical
  let h : ℝ → ℝ := fun θ => 1 / (θ - θ0)
  let A : ℝ := θ0 + Real.pi / (n : ℝ)
  let P : Fin N → Prop := fun i => θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo
  let s : Finset (Fin N) := Finset.univ.filter P
  have hnpos : 0 < (n : ℝ) := S5.nR_pos hn16
  have hπn_pos : 0 < Real.pi / (n : ℝ) := by
    exact div_pos Real.pi_pos hnpos
  have hper : ∀ i : Fin N, i ∈ s → θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo := by
    intro i hi
    have hmem : i ∈ Finset.univ.filter P := by
      simpa [s] using hi
    exact (Finset.mem_filter.mp hmem).2
  change (∑ i ∈ s, |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|) ≤ 1 / Real.pi
  by_cases hS : s = ∅
  · rw [hS]
    simp
    simpa using (Real.pi_pos.le : (0 : ℝ) ≤ Real.pi)
  · have hsNE : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    rcases hsNE with ⟨i0, hi0mem⟩
    have hPi0 : θ0 + Real.pi / (n : ℝ) ≤ (F.arc i0).lo := hper i0 hi0mem
    have hAB : A ≤ S5.qB n := by
      have h1 := S5.arc_hi_le_qB hn16 F i0        -- hi i0 ≤ qB n
      have h2 := Family.Grid.lo_le_hi (F.arc i0)  -- lo i0 ≤ hi i0
      dsimp [A]
      linarith
    have hA_lo : ∀ i ∈ s, A ≤ (F.arc i).lo := by
      intro i hi
      have hp := hper i hi
      dsimp [A]
      exact hp
    have hanti : AntitoneOn h (Set.Icc A (S5.qB n)) := by
      intro x hx y hy hxy
      dsimp [h]
      have hxA : A ≤ x := hx.1
      have hxpos : 0 < x - θ0 := by
        dsimp [A] at hxA
        linarith
      exact inv_sub_anti_right (θ0 := θ0) hxpos hxy
    have htele : (∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)|) ≤
        |h (S5.qB n) - h A| := by
      have hh := S5Tele.sum_var_le_anti (s := s) (lo := fun i : Fin N => (F.arc i).lo)
        (hi := fun i : Fin N => (F.arc i).hi) (A := A) (B := S5.qB n) hAB
        (hA := hA_lo)
        (hB := fun i hi => S5.arc_hi_le_qB hn16 F i)
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
          θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo := Or.inr (hper i hi)
      have hb := S5.arc_LK_far_bound n N hn16 F i hθ0a hθ0b hfar
      simpa [h] using hb
    have hA_mθ0 : A - θ0 = Real.pi / (n : ℝ) := by
      dsimp [A]
      ring
    have hA_mθ0_pos : 0 < A - θ0 := by
      rw [hA_mθ0]
      exact hπn_pos
    have hA_val : 1 / (A - θ0) = (n : ℝ) / Real.pi := by
      rw [hA_mθ0]
      exact one_div_div Real.pi (n : ℝ)
    have hqB_mθ0_pos : 0 < S5.qB n - θ0 := by
      have h1 : Real.pi / (n : ℝ) ≤ S5.qB n - θ0 := by
        have hAB' : A ≤ S5.qB n := hAB
        dsimp [A] at hAB'
        linarith
      exact lt_of_lt_of_le hπn_pos h1
    have hqB_inv_nonneg : 0 ≤ 1 / (S5.qB n - θ0) :=
      div_nonneg (by norm_num) (le_of_lt hqB_mθ0_pos)
    have hfin : h A - h (S5.qB n) ≤ (n : ℝ) / Real.pi := by
      dsimp [h]
      calc
        1 / (A - θ0) - 1 / (S5.qB n - θ0)
            = (n : ℝ) / Real.pi - 1 / (S5.qB n - θ0) := by rw [hA_val]
        _ ≤ (n : ℝ) / Real.pi - 0 := sub_le_sub_left hqB_inv_nonneg ((n : ℝ) / Real.pi)
        _ = (n : ℝ) / Real.pi := by ring
    have hmon : h (S5.qB n) ≤ h A := by
      dsimp [h]
      exact S5.inv_rev_of_pos hA_mθ0_pos (by linarith)
    have hval : |h (S5.qB n) - h A| = h A - h (S5.qB n) := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr hmon)
    have habs_le : |h (S5.qB n) - h A| ≤ (n : ℝ) / Real.pi := by
      rw [hval]
      exact hfin
    have hdiv : |h (S5.qB n) - h A| / (n : ℝ) ≤ 1 / Real.pi := by
      calc
        |h (S5.qB n) - h A| / (n : ℝ) ≤ ((n : ℝ) / Real.pi) / (n : ℝ) :=
          div_le_div_of_nonneg_right habs_le (le_of_lt hnpos)
        _ = 1 / Real.pi := by field_simp [ne_of_gt hnpos]
    calc
      (∑ i ∈ s, |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|)
          ≤ ∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)| / (n : ℝ) := hsum_step
      _ = (∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)|) / (n : ℝ) := by
          rw [← Finset.sum_div]
      _ ≤ |h (S5.qB n) - h A| / (n : ℝ) :=
          div_le_div_of_nonneg_right htele (le_of_lt hnpos)
      _ ≤ 1 / Real.pi := hdiv

end S5C3R
end Submission
