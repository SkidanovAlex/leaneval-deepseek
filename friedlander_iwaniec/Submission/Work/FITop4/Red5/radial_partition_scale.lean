/-
# `Submission.Work.FITop4.Red5.radial_partition_scale`

The **scaled radial partition of unity**.  This is the same construction as
`Submission.Work.FITop4.Red5.radial_partition_le` (the clamped-quintic telescoping partition of
`(N, 2N]` into pieces supported in `(a_i, (1+θ)a_i]`), but with the derivative bound measured at
the *local* left end `a_i` of each piece rather than at the global lower end `N`:

  `|p_i^{(j)}| ≤ cMoll j · (θ a_i)^{-j}`   (`j ≤ 2`),

which is the form of (4.14) actually used in the paper.  The point is that on the piece `i` the
natural scale of the bump is `W = θ a_i/4`, and since `N ≤ a_i ≤ 2N` the global choice
`W = θN/4`, which the telescoping partition forces, is within a factor `256` of the local one —
well inside the slack of the absolute constants `cMoll 1 = 2^10`, `cMoll 2 = 2^20`.
-/
import Mathlib
import Submission.Work.FITop4.Red5.radial_partition_le

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators
open Work.FITop4.Bump4

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary constants at the local scale

Both bounds only use `θ A ≤ 8W`, i.e. `A ≤ 2N` at `W = θN/4`; the absolute constants `cMoll 1` and
`cMoll 2` leave ample slack. -/

/-- First-derivative bound at the local scale `A`: `4/W ≤ cMoll 1 · (θA)^{-1}` when `θA ≤ 8W`. -/
lemma four_div_W_le_cMoll_one_rpow (θ A W : ℝ) (hW : 0 < W) (hθ : 0 < θ)
    (hA : 0 < A) (hθA : θ * A ≤ 8 * W) :
    (4 : ℝ) / W ≤ cMoll 1 * (θ * A) ^ (-((1 : ℕ) : ℝ)) := by
  have hpos : 0 < θ * A := mul_pos hθ hA
  have hneg : (θ * A) ^ (-((1 : ℕ) : ℝ)) = 1 / (θ * A) := by
    rw [show (-((1 : ℕ) : ℝ)) = (-(1 : ℝ)) from by norm_num, Real.rpow_neg_one, one_div]
  rw [hneg, show cMoll 1 = 1024 from by unfold cMoll; norm_num,
      show (1024 : ℝ) * (1 / (θ * A)) = 1024 / (θ * A) from by ring]
  rw [div_le_div_iff₀ hW hpos]
  nlinarith [hθA, hW]

/-- Second-derivative bound at the local scale `A`: `12/W² ≤ cMoll 2 · (θA)^{-2}` when
`θA ≤ 8W`. -/
lemma twelve_div_Wsq_le_cMoll_two_rpow (θ A W : ℝ) (hW : 0 < W) (hθ : 0 < θ)
    (hA : 0 < A) (hθA : θ * A ≤ 8 * W) :
    (12 : ℝ) / W ^ 2 ≤ cMoll 2 * (θ * A) ^ (-((2 : ℕ) : ℝ)) := by
  have hpos : 0 < θ * A := mul_pos hθ hA
  have hneg : (θ * A) ^ (-((2 : ℕ) : ℝ)) = 1 / (θ * A) ^ 2 := by
    rw [show (-((2 : ℕ) : ℝ)) = (-(2 : ℝ)) from by norm_num,
        Real.rpow_neg (le_of_lt hpos), Real.rpow_two, one_div]
  rw [hneg, show cMoll 2 = (2 : ℝ) ^ 20 from by unfold cMoll; norm_num,
      show (2 : ℝ) ^ 20 * (1 / (θ * A) ^ 2) = (2 : ℝ) ^ 20 / (θ * A) ^ 2 from by ring]
  have hsq : (θ * A) ^ 2 ≤ (8 * W) ^ 2 := by nlinarith [hθA, hpos, hW]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < W ^ 2)
        (by positivity : (0 : ℝ) < (θ * A) ^ 2)]
  nlinarith [hsq, hW]

/-! ## The scaled radial partition of unity -/

theorem radial_partition_scale (N : ℕ) (θ : ℝ) (hN : 1 ≤ N) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ (K : ℕ) (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ),
      (∀ i, ContDiff ℝ 2 (p i)) ∧
      (∀ i u, 0 ≤ p i u) ∧ (∀ i u, p i u ≤ 1) ∧
      (∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i) ∧
      (∀ i, (N : ℝ) ≤ a i ∧ a i ≤ 2 * (N : ℝ)) ∧
      (∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1) ∧
      (∀ u, (N : ℝ) + θ * (N : ℝ) / 2 < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) = 1) ∧
      (∀ i j, j ≤ 2 → ∀ u,
        |iteratedDeriv j (p i) u| ≤ cMoll j * (θ * a i) ^ (-(j : ℝ))) ∧
      ((K : ℝ) ≤ 4 / θ + 4) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hθne : θ ≠ 0 := ne_of_gt hθ0
  -- the piece width
  set W : ℝ := θ * (N : ℝ) / 4 with hWdef
  have hWpos : 0 < W := by rw [hWdef]; positivity
  have hWne : W ≠ 0 := ne_of_gt hWpos
  have hθN : θ * (N : ℝ) = 4 * W := by rw [hWdef]; ring
  have hNW : (N : ℝ) / W = 4 / θ := by
    rw [hWdef]; field_simp
  -- the number of pieces
  have hxeq : (2 * (N : ℝ) - radc N W 0) / W = 4 / θ - 1 := by
    have h2 : 2 * (N : ℝ) - radc N W 0 = (N : ℝ) - W := by unfold radc; ring
    rw [h2, sub_div, div_self hWne, hNW]
  set M : ℕ := Nat.ceil ((2 * (N : ℝ) - radc N W 0) / W) with hMdef
  have hxpos : 0 < (2 * (N : ℝ) - radc N W 0) / W := by
    rw [hxeq]
    have : (4 : ℝ) ≤ 4 / θ := by rw [le_div_iff₀ hθ0]; nlinarith
    linarith
  have hMge1 : 1 ≤ M := by
    rw [hMdef]
    exact Nat.succ_le_of_lt (Nat.ceil_pos.mpr hxpos)
  -- `c_M ≥ 2N`
  have hMW : 2 * (N : ℝ) ≤ radc N W M := by
    have h1 : (2 * (N : ℝ) - radc N W 0) / W ≤ (M : ℝ) := by
      rw [hMdef]; exact Nat.le_ceil _
    have h2 : 2 * (N : ℝ) - radc N W 0 ≤ (M : ℝ) * W := by
      have := mul_le_mul_of_nonneg_right h1 (le_of_lt hWpos)
      rwa [div_mul_cancel₀ _ hWne] at this
    have h3 := radc_zero_add N W M
    linarith
  -- `M W < N` and `M < 4/θ`
  have hxnonneg : 0 ≤ (2 * (N : ℝ) - radc N W 0) / W := le_of_lt hxpos
  have hceil : (M : ℝ) < (2 * (N : ℝ) - radc N W 0) / W + 1 := by
    rw [hMdef]; exact Nat.ceil_lt_add_one hxnonneg
  have hceil' : (M : ℝ) < (N : ℝ) / W := by
    have hsum : (2 * (N : ℝ) - radc N W 0) / W + 1 = (N : ℝ) / W := by
      rw [hxeq, ← hNW]; ring
    rwa [hsum] at hceil
  have hMltN : (M : ℝ) * W < (N : ℝ) := by
    have := mul_lt_mul_of_pos_right hceil' hWpos
    rwa [div_mul_cancel₀ _ hWne] at this
  have hMlt_count : (M : ℝ) < 4 / θ := by
    rw [← hNW]; exact hceil'
  -- the support-box inequality `3W ≤ θ a_k`
  have hThreeW : ∀ k : ℕ, 3 * W ≤ θ * rada N W k := by
    intro k
    have h1 : θ * rada N W k = θ * (N : ℝ) + θ * ((k : ℝ) * W) := by unfold rada; ring
    rw [h1, hθN]
    have h2 : 0 ≤ θ * ((k : ℝ) * W) :=
      mul_nonneg (le_of_lt hθ0) (mul_nonneg (Nat.cast_nonneg k) (le_of_lt hWpos))
    linarith
  -- telescoping identity for the finite sum
  have hsumfun : ∀ u : ℝ,
      (∑ i : Fin M, (stepScaled W (radc N W ↑i) - stepScaled W (radc N W (↑i + 1))) u)
        = stepScaled W (radc N W 0) u - stepScaled W (radc N W M) u := by
    intro u
    simp only [Pi.sub_apply]
    rw [Fin.sum_univ_eq_sum_range
      (fun k => (stepScaled W (radc N W k) u - stepScaled W (radc N W (k + 1)) u)) M]
    exact Finset.sum_range_sub' (fun k => stepScaled W (radc N W k) u) M
  refine ⟨M, fun i => rada N W (i : ℕ),
    fun i => stepScaled W (radc N W (i : ℕ)) - stepScaled W (radc N W ((i : ℕ) + 1)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `C²`
    intro i
    exact (contDiff_stepScaled W _).sub (contDiff_stepScaled W _)
  · -- nonnegativity
    intro i u
    dsimp only
    rw [stepScaled_sub_succ N W hWne]
    exact radBump_nonneg _
  · -- upper bound `≤ 1`
    intro i u
    dsimp only
    rw [stepScaled_sub_succ N W hWne]
    exact radBump_le_one _
  · -- support
    intro i u hne
    dsimp only at hne
    rw [stepScaled_sub_succ N W hWne] at hne
    have hpos : 0 < (u - radc N W (i : ℕ)) / W := by
      by_contra h
      exact hne (radBump_eq_zero_of_nonpos _ (le_of_not_gt h))
    have hlt2 : (u - radc N W (i : ℕ)) / W < 2 := by
      by_contra h
      exact hne (radBump_eq_zero_of_two_le _ (le_of_not_gt h))
    have hu1 : radc N W (i : ℕ) < u := by
      rw [div_pos_iff_of_pos_right hWpos] at hpos
      linarith
    have hu2 : u < radc N W (i : ℕ) + 2 * W := by
      rw [div_lt_iff₀ hWpos] at hlt2
      linarith
    constructor
    · have h : rada N W (i : ℕ) = radc N W (i : ℕ) - W := by
        rw [radc_eq_rada_add]; ring
      linarith
    · have h3 : radc N W (i : ℕ) + 2 * W = rada N W (i : ℕ) + 3 * W := by
        rw [radc_eq_rada_add]; ring
      have h4 : rada N W (i : ℕ) + 3 * W ≤ (1 + θ) * rada N W (i : ℕ) := by
        have h5 := hThreeW (i : ℕ)
        linarith
      linarith
  · -- the left ends lie in `[N, 2N]`
    intro i
    constructor
    · unfold rada
      have : 0 ≤ ((i : ℕ) : ℝ) * W := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hWpos)
      linarith
    · have hkM : ((i : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast i.2
      have h1 : ((i : ℕ) : ℝ) * W < (M : ℝ) * W := mul_lt_mul_of_pos_right hkM hWpos
      have h2 : ((i : ℕ) : ℝ) * W < (N : ℝ) := lt_trans h1 hMltN
      unfold rada
      linarith
  · -- `Σ ≤ 1` on `(N, 2N]`
    intro u _ _
    rw [hsumfun u]
    have h1 := quinticStep_le_one ((u - radc N W 0) / W)
    have h2 := quinticStep_nonneg ((u - radc N W M) / W)
    unfold stepScaled
    linarith
  · -- `Σ = 1` on `(N + θN/2, 2N]`
    intro u h1 h2
    rw [hsumfun u]
    have hrad0 : radc N W 0 = (N : ℝ) + W := by unfold radc; push_cast; ring
    have h2W : θ * (N : ℝ) / 2 = 2 * W := by linarith [hθN]
    have hc0 : 1 ≤ (u - radc N W 0) / W := by
      rw [le_div_iff₀ hWpos, hrad0]
      linarith
    have hcM : (u - radc N W M) / W ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt hWpos)
      linarith
    unfold stepScaled
    rw [quinticStep_eq_one_of_one_le _ hc0, quinticStep_eq_zero_of_nonpos _ hcM]
    ring
  · -- the derivative bounds, measured at the *local* left end `a i`
    intro i j hj u
    dsimp only
    have hai_ge : (N : ℝ) ≤ rada N W (↑i) := by
      unfold rada
      have h : 0 ≤ ((i : ℕ) : ℝ) * W :=
        mul_nonneg (Nat.cast_nonneg _) (le_of_lt hWpos)
      linarith
    have hai_le : rada N W (↑i) ≤ 2 * (N : ℝ) := by
      have hkM : ((i : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast i.2
      have h1 : ((i : ℕ) : ℝ) * W < (M : ℝ) * W := mul_lt_mul_of_pos_right hkM hWpos
      have h2 : ((i : ℕ) : ℝ) * W < (N : ℝ) := lt_trans h1 hMltN
      unfold rada
      linarith
    have hai_pos : 0 < rada N W (↑i) := lt_of_lt_of_le hNpos hai_ge
    have hθa_pos : 0 < θ * rada N W (↑i) := mul_pos hθ0 hai_pos
    have hθa_le : θ * rada N W (↑i) ≤ 8 * W := by
      have h1 : θ * rada N W (↑i) ≤ θ * (2 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hai_le (le_of_lt hθ0)
      have h2 : θ * (2 * (N : ℝ)) = 8 * W := by
        rw [show θ * (2 * (N : ℝ)) = 2 * (θ * (N : ℝ)) by ring, hθN]; ring
      linarith
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with hj0 | hj1 | hj2
    · -- `j = 0`
      rw [hj0]
      have h1 : |(stepScaled W (radc N W (↑i))
            - stepScaled W (radc N W (↑i + 1))) u| ≤ 1 := by
        have hnn : 0 ≤ (stepScaled W (radc N W (↑i))
            - stepScaled W (radc N W (↑i + 1))) u := by
          rw [stepScaled_sub_succ N W hWne]; exact radBump_nonneg _
        rw [abs_of_nonneg hnn, stepScaled_sub_succ N W hWne]
        exact radBump_le_one _
      simpa [iteratedDeriv_zero, cMoll_zero, neg_zero, Real.rpow_zero] using h1
    · -- `j = 1`
      rw [hj1]
      have hdir : |iteratedDeriv 1
            (stepScaled W (radc N W (↑i)) - stepScaled W (radc N W (↑i + 1))) u| ≤ 4 / W :=
        abs_iteratedDeriv_one_sub_stepScaled W _ _ hWpos u
      have hb : (4 : ℝ) / W ≤ cMoll 1 * (θ * rada N W (↑i)) ^ (-((1 : ℕ) : ℝ)) :=
        four_div_W_le_cMoll_one_rpow θ (rada N W (↑i)) W hWpos hθ0 hai_pos hθa_le
      exact le_trans hdir hb
    · -- `j = 2`
      rw [hj2]
      have hdir : |iteratedDeriv 2
            (stepScaled W (radc N W (↑i)) - stepScaled W (radc N W (↑i + 1))) u| ≤ 12 / W ^ 2 :=
        abs_iteratedDeriv_two_sub_stepScaled W _ _ hWpos u
      have hb : (12 : ℝ) / W ^ 2 ≤ cMoll 2 * (θ * rada N W (↑i)) ^ (-((2 : ℕ) : ℝ)) :=
        twelve_div_Wsq_le_cMoll_two_rpow θ (rada N W (↑i)) W hWpos hθ0 hai_pos hθa_le
      exact le_trans hdir hb
  · -- the number of pieces
    linarith [hMlt_count]

end

end Work.FITop4.Red5
