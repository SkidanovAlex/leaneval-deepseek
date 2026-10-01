import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Commons.NumberTheory.Linnik.tentWeight_spec

namespace Commons.NumberTheory.Linnik

/-! The tent weight `tentWeight L K x` (Heath-Brown 1992, §13) is the continuous
function that vanishes outside `[L - 2K, L]`, rises linearly from `0` (at
`L - 2K`) to `K` (at `L - K`) and falls back to `0` (at `L`).  On the support
interval it agrees with `min (x - (L - 2*K)) (L - x)`, so its integral over the
support is the area `K ^ 2` of the tent. -/

/-- `∫ (x - u)` over `u..v` is the triangle `(v-u)^2/2`. -/
lemma integral_id_sub_left (u v : ℝ) :
    (∫ x in u..v, x - u) = (v - u) ^ 2 / 2 := by
  have hfun : (fun x : ℝ => x - u) = (fun x : ℝ => x + -u) := by
    funext x
    ring
  have htr := intervalIntegral.integral_comp_add_right (f := fun x : ℝ => x)
    (d := -u) (a := u) (b := v)
  rw [hfun, htr]
  rw [integral_id]
  ring

/-- `∫ (v - x)` over `u..v` is the triangle `(v-u)^2/2`. -/
lemma integral_const_sub_id (u v : ℝ) :
    (∫ x in u..v, v - x) = (v - u) ^ 2 / 2 := by
  have hfun : (fun x : ℝ => v - x) = fun x => -(x + -v) := by
    funext x
    ring
  rw [hfun]
  rw [intervalIntegral.integral_neg]
  have htr := intervalIntegral.integral_comp_add_right (f := fun x : ℝ => x)
    (d := -v) (a := u) (b := v)
  rw [htr]
  rw [integral_id]
  ring

/-- On the support interval `[L - 2*K, L]` the tent weight equals
`min (x - (L - 2*K)) (L - x)`. -/
lemma tentWeight_eq_min (L K : ℝ) :
    ∀ x ∈ Set.Icc (L - 2 * K) L,
      tentWeight L K x = min (x - (L - 2 * K)) (L - x) := by
  intro x hx
  have h1 : L - 2 * K ≤ x := hx.1
  have h2 : x ≤ L := hx.2
  rw [tentWeight_spec]
  by_cases hx1 : x ≤ L - 2 * K
  · simp [hx1]
    have hmin : min (x - (L - 2 * K)) (L - x) = 0 := by
      have hxa : x = L - 2 * K := le_antisymm hx1 h1
      have hle : x - (L - 2 * K) ≤ L - x := by linarith
      rw [min_eq_left hle, hxa]
      ring
    exact hmin.symm
  · by_cases hx2 : x ≤ L - K
    · simp [hx1, hx2]
      linarith
    · simp [hx1, hx2, h2]
      linarith

/-- Area under the tent: the integral of `tentWeight L K` over its support
`(L - 2*K, L]` is `K ^ 2`. -/
theorem tentWeight_area {L K : ℝ} (hK : 0 ≤ K) (h2K : 2 * K ≤ L) :
    (∫ t in (L - 2 * K : ℝ)..(L : ℝ), tentWeight L K t) = K ^ 2 := by
  let a := L - 2 * K
  let b := L - K
  let c := L
  have hac : a ≤ c := by dsimp [a, c]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hbc : b ≤ c := by dsimp [b, c]; linarith
  have hmid : 2 * b = a + c := by dsimp [a, b, c]; ring
  let g : ℝ → ℝ := fun x => min (x - a) (c - x)
  have hgcont : Continuous g := by
    dsimp [g]
    exact Continuous.min (continuous_sub_right a) (continuous_sub_left c)
  have hEq : Set.EqOn (tentWeight L K) g (Set.uIcc a c) := by
    rw [Set.uIcc_of_le hac]
    intro x hx
    have hx1 : x ∈ Set.Icc (L - 2 * K) L := by
      simpa [a, c] using hx
    rw [tentWeight_eq_min L K x hx1]
  have hI1 : (∫ t in a..c, tentWeight L K t) = ∫ t in a..c, g t :=
    intervalIntegral.integral_congr hEq
  have hsplit : (∫ t in a..c, g t) = (∫ t in a..b, g t) + ∫ t in b..c, g t := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (hgcont.intervalIntegrable a b) (hgcont.intervalIntegrable b c)
  have hL : (∫ t in a..b, g t) = ∫ t in a..b, t - a := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hab]
    intro x hx
    dsimp [g]
    have hle : x - a ≤ c - x := by linarith [hx.2, hmid]
    exact min_eq_left hle
  have hR : (∫ t in b..c, g t) = ∫ t in b..c, c - t := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hbc]
    intro x hx
    dsimp [g]
    have hle : c - x ≤ x - a := by linarith [hx.1, hmid]
    exact min_eq_right hle
  calc
    (∫ t in (L - 2 * K : ℝ)..(L : ℝ), tentWeight L K t)
        = ∫ t in a..c, tentWeight L K t := by simp [a, c]
    _ = ∫ t in a..c, g t := hI1
    _ = (∫ t in a..b, g t) + ∫ t in b..c, g t := hsplit
    _ = (∫ t in a..b, t - a) + (∫ t in b..c, c - t) := by rw [hL, hR]
    _ = (b - a) ^ 2 / 2 + (c - b) ^ 2 / 2 := by
        rw [integral_id_sub_left, integral_const_sub_id]
    _ = K ^ 2 := by dsimp [a, b, c]; ring

end Commons.NumberTheory.Linnik