/-
# `Submission.Work.FITop4.Red5.radial_partition_le`

The **radial partition of unity (4.12)** of the Friedlander–Iwaniec §§4–5.2 reduction.

For `1 ≤ N` and `0 < θ ≤ 1/4` we build an explicit family of `C²` functions `p_i`, each supported
in `(a_i, (1+θ)a_i]` with `N ≤ a_i ≤ 2N`, such that

* `Σ_i p_i ≤ 1` on `(N,2N]`, with equality on `(N + θN/2, 2N]`;
* `|p_i^{(j)}| ≤ cMoll j · (θN)^{-j}` for `j ≤ 2`;
* the number of pieces is at most `4/θ + 4`.

The construction is the classical *telescoping* one.  With `W = θN/4` we set the grid points
`c_k = N + (k+1)W` and the piece `p_k = S_k - S_{k+1}` where `S_k u = quinticStep ((u - c_k)/W)`
is the clamped quintic step of width `W` (the `C²` Hermite step of `Submission.Work.FITop4.Bump4`).
Then `p_k u = radBump ((u - c_k)/W)` for the bump `radBump t = quinticStep t - quinticStep (t-1)`,
which is supported in `(0,2)`; and the finite sum telescopes,
`Σ_{k<M} p_k u = S_0 u - S_M u`, so it equals `1` on the window `(N + θN/2, 2N]` and is `≤ 1`
everywhere on `(N, 2N]`.  The piece `p_k` is supported in `(c_k, c_k + 2W)` and the choice of the
left end `a_k = c_k - W` makes `(c_k, c_k+2W) ⊆ (a_k, (1+θ)a_k] ⊆ (N, ∞)` because `θ a_k ≥ θN = 4W ≥ 3W`.
-/
import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop4.Bump4
import Submission.Work.FITop4.Bump4.QuinticAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators
open Work.FITop4.Bump4

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The bump `radBump t = quinticStep t − quinticStep (t−1)` -/

/-- The `C²` bump obtained as the difference of the clamped quintic step at `t` and at `t-1`.
It is supported in `(0,2)` and satisfies `0 ≤ radBump ≤ 1`. -/
def radBump (t : ℝ) : ℝ := quinticStep t - quinticStep (t - 1)

lemma radBump_nonneg (t : ℝ) : 0 ≤ radBump t := by
  unfold radBump
  by_cases ht : t ≤ 0
  · rw [quinticStep_eq_zero_of_nonpos t ht,
        quinticStep_eq_zero_of_nonpos (t - 1) (by linarith)]
    norm_num
  · have ht' : 0 < t := not_le.mp ht
    by_cases ht1 : 1 ≤ t
    · by_cases ht2 : 2 ≤ t
      · rw [quinticStep_eq_one_of_one_le t ht1,
            quinticStep_eq_one_of_one_le (t - 1) (by linarith)]
        norm_num
      · rw [quinticStep_eq_one_of_one_le t ht1]
        linarith [quinticStep_le_one (t - 1)]
    · have ht1' : t < 1 := not_le.mp ht1
      rw [quinticStep_eq_zero_of_nonpos (t - 1) (by linarith)]
      linarith [quinticStep_nonneg t]

lemma radBump_le_one (t : ℝ) : radBump t ≤ 1 := by
  unfold radBump
  linarith [quinticStep_le_one t, quinticStep_nonneg (t - 1)]

lemma radBump_eq_zero_of_nonpos (t : ℝ) (ht : t ≤ 0) : radBump t = 0 := by
  unfold radBump
  rw [quinticStep_eq_zero_of_nonpos t ht,
      quinticStep_eq_zero_of_nonpos (t - 1) (by linarith)]
  ring

lemma radBump_eq_zero_of_two_le (t : ℝ) (ht : 2 ≤ t) : radBump t = 0 := by
  unfold radBump
  rw [quinticStep_eq_one_of_one_le t (by linarith),
      quinticStep_eq_one_of_one_le (t - 1) (by linarith)]
  ring

/-- `|a - b| ≤ |a| + |b|`, in a form that does not trigger the `simp` normal form for `|x*y|`. -/
lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_sub_le a 0 b
  rw [sub_zero, zero_sub, abs_neg] at h
  exact h

/-! ## 2. The scaled clamped step and its two derivatives -/

/-- The clamped quintic step of width `W`, translated to `c`. -/
def stepScaled (W c : ℝ) : ℝ → ℝ := fun u => quinticStep ((u - c) / W)

lemma contDiff_stepScaled (W c : ℝ) : ContDiff ℝ 2 (stepScaled W c) := by
  unfold stepScaled
  exact contDiff_quinticStep.comp (by fun_prop)

lemma hasDerivAt_stepScaled (W c u : ℝ) :
    HasDerivAt (stepScaled W c) ((1 / W) * qstep1 ((u - c) / W)) u := by
  unfold stepScaled
  have hinner : HasDerivAt (fun v : ℝ => (v - c) / W) (1 / W) u := by
    have h2 := ((hasDerivAt_id u).sub_const c).div_const W
    simpa using h2
  have h := (quinticStep_hasDerivAt ((u - c) / W)).comp u hinner
  have hv : qstep1 ((u - c) / W) * (1 / W) = (1 / W) * qstep1 ((u - c) / W) := by ring
  rwa [hv] at h

lemma deriv_stepScaled (W c u : ℝ) :
    deriv (stepScaled W c) u = (1 / W) * qstep1 ((u - c) / W) :=
  (hasDerivAt_stepScaled W c u).deriv

lemma deriv_stepScaled_eq (W c : ℝ) :
    deriv (stepScaled W c) = fun u => (1 / W) * qstep1 ((u - c) / W) :=
  funext (deriv_stepScaled W c)

lemma hasDerivAt_deriv_stepScaled (W c u : ℝ) :
    HasDerivAt (fun v : ℝ => (1 / W) * qstep1 ((v - c) / W))
      ((1 / W ^ 2) * qstep2 ((u - c) / W)) u := by
  have hinner : HasDerivAt (fun v : ℝ => (v - c) / W) (1 / W) u := by
    have h2 := ((hasDerivAt_id u).sub_const c).div_const W
    simpa using h2
  have h := (qstep1_hasDerivAt ((u - c) / W)).comp u hinner
  have h2 := h.const_mul (1 / W)
  have hv : (1 / W) * (qstep2 ((u - c) / W) * (1 / W)) = (1 / W ^ 2) * qstep2 ((u - c) / W) := by
    ring
  rwa [hv] at h2

lemma deriv2_stepScaled (W c u : ℝ) :
    deriv (deriv (stepScaled W c)) u = (1 / W ^ 2) * qstep2 ((u - c) / W) := by
  rw [deriv_stepScaled_eq]
  exact (hasDerivAt_deriv_stepScaled W c u).deriv

lemma iteratedDeriv_one_stepScaled (W c u : ℝ) :
    iteratedDeriv 1 (stepScaled W c) u = (1 / W) * qstep1 ((u - c) / W) := by
  rw [iteratedDeriv_one, deriv_stepScaled]

lemma iteratedDeriv_two_stepScaled (W c u : ℝ) :
    iteratedDeriv 2 (stepScaled W c) u = (1 / W ^ 2) * qstep2 ((u - c) / W) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, deriv_stepScaled_eq]
  exact (hasDerivAt_deriv_stepScaled W c u).deriv

/-- The first derivative of a difference of two scaled steps is bounded by `4/W`. -/
lemma abs_iteratedDeriv_one_sub_stepScaled (W c₁ c₂ : ℝ) (hW : 0 < W) (u : ℝ) :
    |iteratedDeriv 1 (stepScaled W c₁ - stepScaled W c₂) u| ≤ 4 / W := by
  rw [iteratedDeriv_sub (n := 1) ((contDiff_stepScaled W c₁).contDiffAt.of_le (by norm_num))
        ((contDiff_stepScaled W c₂).contDiffAt.of_le (by norm_num)),
      iteratedDeriv_one_stepScaled, iteratedDeriv_one_stepScaled]
  have hb1 : |(1 / W) * qstep1 ((u - c₁) / W)| ≤ 2 / W := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / W)]
    calc (1 / W) * |qstep1 ((u - c₁) / W)| ≤ (1 / W) * 2 :=
          mul_le_mul_of_nonneg_left (abs_qstep1_le _) (by positivity)
      _ = 2 / W := by ring
  have hb2 : |(1 / W) * qstep1 ((u - c₂) / W)| ≤ 2 / W := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / W)]
    calc (1 / W) * |qstep1 ((u - c₂) / W)| ≤ (1 / W) * 2 :=
          mul_le_mul_of_nonneg_left (abs_qstep1_le _) (by positivity)
      _ = 2 / W := by ring
  calc |(1 / W) * qstep1 ((u - c₁) / W) - (1 / W) * qstep1 ((u - c₂) / W)|
      ≤ |(1 / W) * qstep1 ((u - c₁) / W)| + |(1 / W) * qstep1 ((u - c₂) / W)| :=
        abs_sub_le_abs_add _ _
    _ ≤ 2 / W + 2 / W := add_le_add hb1 hb2
    _ = 4 / W := by ring

/-- The second derivative of a difference of two scaled steps is bounded by `12/W²`. -/
lemma abs_iteratedDeriv_two_sub_stepScaled (W c₁ c₂ : ℝ) (hW : 0 < W) (u : ℝ) :
    |iteratedDeriv 2 (stepScaled W c₁ - stepScaled W c₂) u| ≤ 12 / W ^ 2 := by
  rw [iteratedDeriv_sub (n := 2) (contDiff_stepScaled W c₁).contDiffAt
        (contDiff_stepScaled W c₂).contDiffAt,
      iteratedDeriv_two_stepScaled, iteratedDeriv_two_stepScaled]
  have hb1 : |(1 / W ^ 2) * qstep2 ((u - c₁) / W)| ≤ 6 / W ^ 2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / W ^ 2)]
    calc (1 / W ^ 2) * |qstep2 ((u - c₁) / W)| ≤ (1 / W ^ 2) * 6 :=
          mul_le_mul_of_nonneg_left (abs_qstep2_le _) (by positivity)
      _ = 6 / W ^ 2 := by ring
  have hb2 : |(1 / W ^ 2) * qstep2 ((u - c₂) / W)| ≤ 6 / W ^ 2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / W ^ 2)]
    calc (1 / W ^ 2) * |qstep2 ((u - c₂) / W)| ≤ (1 / W ^ 2) * 6 :=
          mul_le_mul_of_nonneg_left (abs_qstep2_le _) (by positivity)
      _ = 6 / W ^ 2 := by ring
  calc |(1 / W ^ 2) * qstep2 ((u - c₁) / W) - (1 / W ^ 2) * qstep2 ((u - c₂) / W)|
      ≤ |(1 / W ^ 2) * qstep2 ((u - c₁) / W)| + |(1 / W ^ 2) * qstep2 ((u - c₂) / W)| :=
        abs_sub_le_abs_add _ _
    _ ≤ 6 / W ^ 2 + 6 / W ^ 2 := add_le_add hb1 hb2
    _ = 12 / W ^ 2 := by ring

/-! ## 3. The radial grid -/

/-- The left end `a_k = N + kW` of the `k`-th piece. -/
def rada (N : ℕ) (W : ℝ) (k : ℕ) : ℝ := (N : ℝ) + (k : ℝ) * W

/-- The grid point `c_k = N + (k+1)W = a_k + W`. -/
def radc (N : ℕ) (W : ℝ) (k : ℕ) : ℝ := (N : ℝ) + ((k : ℝ) + 1) * W

lemma radc_eq_rada_add (N : ℕ) (W : ℝ) (k : ℕ) : radc N W k = rada N W k + W := by
  unfold radc rada; ring

lemma radc_succ (N : ℕ) (W : ℝ) (k : ℕ) : radc N W (k + 1) = radc N W k + W := by
  unfold radc; push_cast; ring

lemma radc_zero_add (N : ℕ) (W : ℝ) (k : ℕ) : radc N W k = radc N W 0 + (k : ℝ) * W := by
  unfold radc; push_cast; ring

lemma stepScaled_sub (W c u : ℝ) (hW : W ≠ 0) :
    stepScaled W c u - stepScaled W (c + W) u = radBump ((u - c) / W) := by
  unfold stepScaled radBump
  have h : u - (c + W) = (u - c) - W := by ring
  rw [h, div_sub_one hW]

lemma stepScaled_sub_succ (N : ℕ) (W : ℝ) (hW : W ≠ 0) (k : ℕ) (u : ℝ) :
    (stepScaled W (radc N W k) - stepScaled W (radc N W (k + 1))) u
      = radBump ((u - radc N W k) / W) := by
  rw [Pi.sub_apply, radc_succ N W k]
  exact stepScaled_sub W (radc N W k) u hW

/-! ## 4. The radial partition of unity (4.12) -/

/-- **The radial partition of unity (4.12).**  For `1 ≤ N` and `0 < θ ≤ 1/4` there are finitely
many `C²` functions `p_i`, each supported in `(a_i, (1+θ)a_i]` with `N ≤ a_i ≤ 2N`, such that

* `Σ_i p_i ≤ 1` on `(N, 2N]`, with equality on `(N + θN/2, 2N]` — the *deficit* `1 − Σ_i p_i` is
  supported on the strip `(N, N + θN/2]`, which is the paper's "residual contribution ... at most
  `O(θA(x)(log x)^4)`";
* `|p_i^{(j)}| ≤ cMoll j·(θN)^{-j}` for `j ≤ 2` (the (4.14) bounds with the absolute constants);
* the number of pieces is at most `4/θ + 4`. -/
theorem radial_partition_le (N : ℕ) (θ : ℝ) (hN : 1 ≤ N) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ (K : ℕ) (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ),
      (∀ i, ContDiff ℝ 2 (p i)) ∧
      (∀ i u, 0 ≤ p i u) ∧ (∀ i u, p i u ≤ 1) ∧
      (∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i) ∧
      (∀ i, (N : ℝ) ≤ a i ∧ a i ≤ 2 * (N : ℝ)) ∧
      (∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1) ∧
      (∀ u, (N : ℝ) + θ * (N : ℝ) / 2 < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) = 1) ∧
      (∀ i j, j ≤ 2 → ∀ u,
        |iteratedDeriv j (p i) u| ≤ cMoll j * (θ * (N : ℝ)) ^ (-(j : ℝ))) ∧
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
  · -- the derivative bounds
    intro i j hj u
    dsimp only
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    have hcM0 : cMoll 0 = 1 := cMoll_zero
    have hcM1 : cMoll 1 = 1024 := by unfold cMoll; norm_num
    have hcM2 : cMoll 2 = (2 : ℝ) ^ 20 := by unfold cMoll; norm_num
    have hexp1 : (-((1 : ℕ) : ℝ)) = -(1 : ℝ) := by norm_num
    have hexp2 : (-((2 : ℕ) : ℝ)) = -(2 : ℝ) := by norm_num
    have hrpow1 : (θ * (N : ℝ)) ^ (-((1 : ℕ) : ℝ)) = 1 / (4 * W) := by
      rw [hexp1, Real.rpow_neg_one, hθN, one_div]
    have hrpow2 : (θ * (N : ℝ)) ^ (-((2 : ℕ) : ℝ)) = 1 / (4 * W) ^ 2 := by
      have hpos : 0 ≤ θ * (N : ℝ) := le_of_lt (mul_pos hθ0 hNpos)
      rw [hexp2, Real.rpow_neg hpos, hθN, Real.rpow_two, one_div]
    have hR1 : cMoll 1 * (θ * (N : ℝ)) ^ (-((1 : ℕ) : ℝ)) = 256 / W := by
      rw [hcM1, hrpow1]
      field_simp
      ring
    have hR2 : cMoll 2 * (θ * (N : ℝ)) ^ (-((2 : ℕ) : ℝ)) = 65536 / W ^ 2 := by
      rw [hcM2, hrpow2]
      have h4 : (4 * W) ^ 2 = 16 * W ^ 2 := by ring
      rw [h4]
      have h2 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
      rw [h2]
      field_simp
      ring
    rcases hj' with hj0 | hj1 | hj2
    · rw [hj0]
      have hnn : 0 ≤ (stepScaled W (radc N W ↑i) - stepScaled W (radc N W (↑i + 1))) u := by
        rw [stepScaled_sub_succ N W hWne]; exact radBump_nonneg _
      have hle : (stepScaled W (radc N W ↑i) - stepScaled W (radc N W (↑i + 1))) u ≤ 1 := by
        rw [stepScaled_sub_succ N W hWne]; exact radBump_le_one _
      have hgoal : |(stepScaled W (radc N W ↑i) - stepScaled W (radc N W (↑i + 1))) u| ≤ 1 := by
        rw [abs_of_nonneg hnn]; exact hle
      simpa [iteratedDeriv_zero, hcM0, neg_zero, Real.rpow_zero] using hgoal
    · rw [hj1, hR1]
      calc |iteratedDeriv 1
            (stepScaled W (radc N W ↑i) - stepScaled W (radc N W (↑i + 1))) u|
          ≤ 4 / W := abs_iteratedDeriv_one_sub_stepScaled W _ _ hWpos u
        _ ≤ 256 / W := div_le_div_of_nonneg_right (by norm_num) (le_of_lt hWpos)
    · rw [hj2, hR2]
      calc |iteratedDeriv 2
            (stepScaled W (radc N W ↑i) - stepScaled W (radc N W (↑i + 1))) u|
          ≤ 12 / W ^ 2 := abs_iteratedDeriv_two_sub_stepScaled W _ _ hWpos u
        _ ≤ 65536 / W ^ 2 :=
            div_le_div_of_nonneg_right (by norm_num) (by positivity : (0 : ℝ) ≤ W ^ 2)
  · -- the number of pieces
    linarith [hMlt_count]

end

end Work.FITop4.Red5
