import Mathlib
import Submission.Work.WilG3.Defs
import Submission.Work.WilG3.ForwardGrowth
import Submission.Work.WilG3.BackwardGrowth
import Submission.Work.WilG3.AbsSubMul

namespace Work.WilG3

/-! ## The induction step of the discrete `C^r` lemma

`WilG3.DiscreteCrCore` is proved by induction on `j`.  The analytic content sits in the
following step: given a triple `g₀, g₁, g₂` of functions on `I = (0,1)` with `g₁ = g₀'`,
`g₂ = g₁'`, all three of constant sign on `I`, and given the inductive bound
`|g₀ z| < M^j` for every `z` at distance `> j/M` from the endpoints of `I`, then `g₁` is bounded
by `M^{j+1}` at every `y` at distance `> (j+1)/M` from the endpoints.

The proof is the BNZ argument: suppose `|g₁ y| ≥ M^{j+1}`.  Pick `σ = ±1` so that `σ g₁ ≥ 0` on
`I`; then `f := σ g₁` is the derivative of `σ g₀` and `f y = |g₁ y| ≥ M^{j+1}`.  The constant
sign of `g₂` makes `f` monotone on `I`, so `f ≥ M^{j+1}` on the one-sided interval of length
`1/M` starting (or ending) at `y`; the quantitative mean value estimate `ForwardGrowth` /
`BackwardGrowth` applied to `σ g₀` on that interval yields a point `z`, still at distance
`> j/M` from the endpoints, with `|g₀ z - g₀ y| ≥ M^j`.  But `g₀` has constant sign, so `g₀ y`
and `g₀ z` have the same sign and both have absolute value `< M^j`, whence
`|g₀ z - g₀ y| < M^j` (`AbsSubMul`) — a contradiction. -/

/-- The induction step of `DiscreteCrCore`, with the tower abstracted to a single triple of
functions. -/
theorem discreteCr_step (j : ℕ) (M : ℝ) (hM : 0 < M) (g0 g1 g2 : ℝ → ℝ)
    (hder0 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g0 (g1 x) x)
    (hder1 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g1 (g2 x) x)
    (hs1 : (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ g1 x) ∨
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, g1 x ≤ 0))
    (hs2 : (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ g2 x) ∨
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, g2 x ≤ 0))
    (hs0 : (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ g0 x) ∨
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, g0 x ≤ 0))
    (hIH : ∀ z ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < z → z < 1 - (j : ℝ) / M →
      |g0 z| < M ^ j)
    (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    (hyl : ((j : ℝ) + 1) / M < y) (hyu : y < 1 - ((j : ℝ) + 1) / M) :
    |g1 y| < M ^ (j + 1) := by
  by_contra hc
  rw [not_lt] at hc
  have h1M : 0 < 1 / M := one_div_pos.mpr hM
  have hMne : M ≠ 0 := ne_of_gt hM
  have hjM_nn : 0 ≤ (j : ℝ) / M := div_nonneg (Nat.cast_nonneg j) (le_of_lt hM)
  have hjM1 : ((j : ℝ) + 1) / M = (j : ℝ) / M + 1 / M := by rw [add_div]
  -- the point `y` and the two candidates `y ± 1/M` all lie in the admissible range for `hIH`
  have hjl : (j : ℝ) / M < y := by rw [hjM1] at hyl; linarith
  have hju : y < 1 - (j : ℝ) / M := by rw [hjM1] at hyu; linarith
  have hyu2 : y + 1 / M < 1 - (j : ℝ) / M := by rw [hjM1] at hyu; linarith
  have hyl2 : (j : ℝ) / M < y - 1 / M := by rw [hjM1] at hyl; linarith
  have hpow : M ^ (j + 1) / M = M ^ j := by
    rw [pow_succ, mul_div_cancel_right₀ _ hMne]
  -- the contradiction, once a point `z` with `M^j ≤ |g₀ z - g₀ y|` is produced
  have hcontr : ∀ z ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < z → z < 1 - (j : ℝ) / M →
      M ^ j ≤ |g0 z - g0 y| → False := by
    intro z hz hzl hzu hle
    have hzy : |g0 z| < M ^ j := hIH z hz hzl hzu
    have hyy : |g0 y| < M ^ j := hIH y hy hjl hju
    have hpos : 0 ≤ g0 y * g0 z := by
      rcases hs0 with h | h
      · exact mul_nonneg (h y hy) (h z hz)
      · exact mul_nonneg_of_nonpos_of_nonpos (h y hy) (h z hz)
    have habs : |g0 y - g0 z| < M ^ j := AbsSubMul hyy hzy hpos
    rw [abs_sub_comm] at habs
    linarith
  rcases hs1 with hg1nn | hg1np
  · -- `g₁ ≥ 0` on `I`: then `σ = 1` and `|g₁ y| = g₁ y`
    have hgy : M ^ (j + 1) ≤ g1 y := by
      have h0y : 0 ≤ g1 y := hg1nn y hy
      rwa [abs_of_nonneg h0y] at hc
    have hyplus_mem : y + 1 / M ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨by linarith [hy.1], by linarith [hyu2, hjM_nn]⟩
    have hyplus_l : (j : ℝ) / M < y + 1 / M := by linarith
    have hyminus_mem : y - 1 / M ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨by linarith [hyl2, hjM_nn], by linarith [hy.2]⟩
    have hyminus_u : y - 1 / M < 1 - (j : ℝ) / M := by linarith [hju]
    rcases hs2 with hg2nn | hg2np
    · -- `g₂ ≥ 0`: `g₁` is nondecreasing, take the forward step
      have hab : y + 1 / M < 1 := by linarith [hyu2, hjM_nn]
      have hgr := ForwardGrowth (v := g0) (v' := g1) (v'' := g2)
        hder0 hder1 hg2nn hM hy.1 hab hgy
      rw [hpow] at hgr
      exact hcontr (y + 1 / M) hyplus_mem hyplus_l hyu2 (le_trans hgr (le_abs_self _))
    · -- `g₂ ≤ 0`: `g₁` is nonincreasing, take the backward step
      have ham : 0 < y - 1 / M := by linarith [hyl2, hjM_nn]
      have hgr := BackwardGrowth (v := g0) (v' := g1) (v'' := g2)
        hder0 hder1 hg2np hM ham hy.2 hgy
      rw [hpow] at hgr
      have hle : M ^ j ≤ |g0 (y - 1 / M) - g0 y| := by
        calc M ^ j ≤ g0 y - g0 (y - 1 / M) := hgr
          _ = -(g0 (y - 1 / M) - g0 y) := by ring
          _ ≤ |g0 (y - 1 / M) - g0 y| := neg_le_abs _
      exact hcontr (y - 1 / M) hyminus_mem hyl2 hyminus_u hle
  · -- `g₁ ≤ 0` on `I`: then `σ = -1` and `|g₁ y| = -g₁ y`
    have hgy : M ^ (j + 1) ≤ -g1 y := by
      have h0y : g1 y ≤ 0 := hg1np y hy
      rwa [abs_of_nonpos h0y] at hc
    have hyplus_mem : y + 1 / M ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨by linarith [hy.1], by linarith [hyu2, hjM_nn]⟩
    have hyplus_l : (j : ℝ) / M < y + 1 / M := by linarith
    have hyminus_mem : y - 1 / M ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨by linarith [hyl2, hjM_nn], by linarith [hy.2]⟩
    have hyminus_u : y - 1 / M < 1 - (j : ℝ) / M := by linarith [hju]
    rcases hs2 with hg2nn | hg2np
    · -- `g₂ ≥ 0`: `-g₁` is nonincreasing, take the backward step
      have ham : 0 < y - 1 / M := by linarith [hyl2, hjM_nn]
      have hv0 : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
          HasDerivAt (fun t => -g0 t) ((fun t => -g1 t) x) x :=
        fun x hx => (hder0 x hx).neg
      have hv1 : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
          HasDerivAt (fun t => -g1 t) ((fun t => -g2 t) x) x :=
        fun x hx => (hder1 x hx).neg
      have hv2 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, (fun t => -g2 t) x ≤ 0 :=
        fun x hx => neg_nonpos.mpr (hg2nn x hx)
      have hgr := BackwardGrowth (v := fun t => -g0 t) (v' := fun t => -g1 t)
        (v'' := fun t => -g2 t) hv0 hv1 hv2 hM ham hy.2 hgy
      rw [hpow] at hgr
      have hle : M ^ j ≤ |g0 (y - 1 / M) - g0 y| := by
        calc M ^ j ≤ -g0 y - -(g0 (y - 1 / M)) := hgr
          _ = g0 (y - 1 / M) - g0 y := by ring
          _ ≤ |g0 (y - 1 / M) - g0 y| := le_abs_self _
      exact hcontr (y - 1 / M) hyminus_mem hyl2 hyminus_u hle
    · -- `g₂ ≤ 0`: `-g₁` is nondecreasing, take the forward step
      have hab : y + 1 / M < 1 := by linarith [hyu2, hjM_nn]
      have hv0 : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
          HasDerivAt (fun t => -g0 t) ((fun t => -g1 t) x) x :=
        fun x hx => (hder0 x hx).neg
      have hv1 : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
          HasDerivAt (fun t => -g1 t) ((fun t => -g2 t) x) x :=
        fun x hx => (hder1 x hx).neg
      have hv2 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ (fun t => -g2 t) x :=
        fun x hx => neg_nonneg.mpr (hg2np x hx)
      have hgr := ForwardGrowth (v := fun t => -g0 t) (v' := fun t => -g1 t)
        (v'' := fun t => -g2 t) hv0 hv1 hv2 hM hy.1 hab hgy
      rw [hpow] at hgr
      have hle : M ^ j ≤ |g0 (y + 1 / M) - g0 y| := by
        calc M ^ j ≤ -g0 (y + 1 / M) - -(g0 y) := hgr
          _ = -(g0 (y + 1 / M) - g0 y) := by ring
          _ ≤ |g0 (y + 1 / M) - g0 y| := neg_le_abs _
      exact hcontr (y + 1 / M) hyplus_mem hyplus_l hyu2 hle

-- Abstract core of BNZ arXiv 2202.05305 §5.1 (their Lemma 5.4). Semantics: `u 0, u 1, ...` is a
-- tower of one-dimensional derivatives on `I = (0,1)` (`u (j+1)` is the derivative of `u j`);
-- each `u j` has constant sign on `I` for `j ≤ r+1`, and `u 0` maps `I` into `(0,1)`.  Then
-- `|u j| < M^j` on the part of `I` at distance more than `j/M` from the endpoints, `j ≤ r`.
-- Proof (BNZ): induction on `j`.  If `|u (j+1) x| ≥ M^(j+1)` at an admissible `x`, the constant
-- signs of `u (j+1)`, `u (j+2)` make `u (j+1)` monotone, so `|u (j+1)| ≥ M^(j+1)` on a one-sided
-- interval of length `1/M`; the quantitative MVT `Work.WilG3.LeSubOfLeDeriv` for `u j` on that
-- interval gives `|u j y - u j x| ≥ M^j` for some `y` still at distance `> j/M` from the boundary,
-- contradicting the induction hypothesis at `x` and at `y` plus the constant sign of `u j`.
-- Useful Mathlib input: `monotoneOn_of_deriv_nonneg` for the monotonicity step,
-- `derivWithin_of_mem_nhds`/`iteratedDerivWithin_succ` if you prefer `deriv` to `HasDerivAt`.
--
-- Note the two `M^j` facts must be strict: `|u j| < M^j` at both endpoints and constancy of sign
-- give `|u j y - u j x| < M^j`, while the MVT gives `≥ M^j`.
theorem DiscreteCrCore (r : ℕ) (M : ℝ) (hM : 1 < M) (u : ℕ → ℝ → ℝ)
    (hder : ∀ j ≤ r, ∀ y ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (u j) (u (j + 1) y) y)
    (hsign : ∀ j ≤ r + 1, (∀ y ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ u j y) ∨
      (∀ y ∈ Set.Ioo (0 : ℝ) 1, u j y ≤ 0))
    (h0 : ∀ y ∈ Set.Ioo (0 : ℝ) 1, |u 0 y| < 1) :
    ∀ j ≤ r, ∀ y ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < y → y < 1 - (j : ℝ) / M →
      |u j y| < M ^ j := by
  have hMpos : (0 : ℝ) < M := by linarith
  intro j
  induction j with
  | zero =>
    intro _ y hy _ _
    simpa using h0 y hy
  | succ j ih =>
    intro hj y hy hyl hyu
    have hj1 : j ≤ r := Nat.le_of_succ_le hj
    have hyl' : ((j : ℝ) + 1) / M < y := by
      simpa only [Nat.cast_add, Nat.cast_one] using hyl
    have hyu' : y < 1 - ((j : ℝ) + 1) / M := by
      simpa only [Nat.cast_add, Nat.cast_one] using hyu
    exact discreteCr_step j M hMpos (u j) (u (j + 1)) (u (j + 2))
      (hder j hj1) (hder (j + 1) hj)
      (hsign (j + 1) (by omega)) (hsign (j + 2) (by omega)) (hsign j (by omega))
      (ih hj1) y hy hyl' hyu'

end Work.WilG3
