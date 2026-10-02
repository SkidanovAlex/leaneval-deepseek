import Mathlib
import Submission.Work.LandLeaves.expansion_of_one_lt_norm_deriv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Cases of the Snail lemma in path (Milnor) form

This file contains, in a standalone module with no dependency on any `sorry`,

* `deriv_shift_germ_path` — the derivative of the germ obtained by translating the fixed point to
  the origin;
* `no_snail_of_one_lt_norm_deriv_path` — the **repelling case**: if `1 < ‖deriv g z₀‖` then no
  continuous forward path `p` in `ℂ ∖ {z₀}` with `g (p t) = p (t + 1)` converges to `z₀`;

and, in `snailPathNotRootOfUnity.lean`, the **irrationally indifferent case**:
`(deriv g z₀) ^ q ≠ 1` for all `q ≥ 1` and `‖deriv g z₀‖ = 1` is incompatible with such a path.

These are the two cases that the *landing chain* consumes on top of `deriv g z₀ = 1`; they are the
path-form replacements for the orbit-form statement (which is equivalent to the Snail principle and
therefore not an available input).  The remaining case, `(deriv g z₀) ^ q = 1`, `deriv g z₀ ≠ 1`,
is handled by the descent-chart argument of `LandLeaves/snailLemmaMilnor.lean`.
-/

open Filter
open scoped Topology

namespace Work.LandLeaves.Snail

/-- Shifting the fixed point to the origin does not change the derivative there. -/
theorem deriv_shift_germ_path {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) :
    deriv (fun w : ℂ => g (w + z₀) - z₀) 0 = deriv g z₀ := by
  have h₁ : HasDerivAt (fun w : ℂ => w + z₀) (1 : ℂ) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).add_const z₀
  have h₂ : HasDerivAt g (deriv g z₀) ((fun w : ℂ => w + z₀) 0) := by
    simpa using hg.differentiableAt.hasDerivAt
  have h₃ : HasDerivAt (fun w : ℂ => g (w + z₀)) (deriv g z₀ * 1) 0 := h₂.comp 0 h₁
  have h₄ : HasDerivAt (fun w : ℂ => g (w + z₀) - z₀) (deriv g z₀ * 1) 0 := h₃.sub_const z₀
  rw [h₄.deriv]; ring

/-- **Repelling case of the Snail lemma in path form.**  If `1 < ‖deriv g z₀‖`, no continuous
forward path `p` in `ℂ ∖ {z₀}` with `g (p t) = p (t + 1)` can converge to `z₀`: along the integer
parameters the distance to `z₀` grows geometrically, by the local expansion
`expansion_of_one_lt_norm_deriv`. -/
theorem no_snail_of_one_lt_norm_deriv_path {g : ℂ → ℂ} {z₀ : ℂ} {p : ℝ → ℂ}
    (hg : AnalyticAt ℂ g z₀) (hfix : g z₀ = z₀) (hlarge : 1 < ‖deriv g z₀‖)
    (hne : ∀ t ∈ Set.Ici (0 : ℝ), p t ≠ z₀)
    (hshift : ∀ t ∈ Set.Ici (0 : ℝ), g (p t) = p (t + 1))
    (hlim : Tendsto p atTop (𝓝 z₀)) : False := by
  obtain ⟨ε, hε, c, hc, hbound⟩ := expansion_of_one_lt_norm_deriv hg hlarge
  have hseq : Tendsto (fun n : ℕ => p (n : ℝ)) atTop (𝓝 z₀) :=
    hlim.comp tendsto_natCast_atTop_atTop
  rw [Metric.tendsto_nhds] at hseq
  have hev : ∀ᶠ n : ℕ in atTop, ‖p (n : ℝ) - z₀‖ < ε := by
    filter_upwards [hseq ε hε] with n hn
    simpa [dist_eq_norm] using hn
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hstep : ∀ n : ℕ, N ≤ n → c * ‖p (n : ℝ) - z₀‖ ≤ ‖p ((n + 1 : ℕ) : ℝ) - z₀‖ := by
    intro n hn
    have hb := hbound (p (n : ℝ)) (hN n hn)
    rw [hfix] at hb
    have harg : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [harg, ← hshift (n : ℝ) (by simp)]
    exact hb
  have hgrowth : ∀ k : ℕ, c ^ k * ‖p (N : ℝ) - z₀‖ ≤ ‖p ((N + k : ℕ) : ℝ) - z₀‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h2 := hstep (N + k) (Nat.le_add_right N k)
        calc c ^ (k + 1) * ‖p (N : ℝ) - z₀‖ = c * (c ^ k * ‖p (N : ℝ) - z₀‖) := by ring
          _ ≤ c * ‖p ((N + k : ℕ) : ℝ) - z₀‖ :=
                mul_le_mul_of_nonneg_left ih (le_of_lt (lt_trans zero_lt_one hc))
          _ ≤ ‖p ((N + k + 1 : ℕ) : ℝ) - z₀‖ := by simpa [Nat.add_assoc] using h2
  have hpos : 0 < ‖p (N : ℝ) - z₀‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hne (N : ℝ) (by simp)
  have hsmall : ∀ᶠ m : ℕ in atTop, ‖p (m : ℝ) - z₀‖ < ‖p (N : ℝ) - z₀‖ := by
    filter_upwards [hseq ‖p (N : ℝ) - z₀‖ hpos] with m hm
    simpa [dist_eq_norm] using hm
  rw [Filter.eventually_atTop] at hsmall
  obtain ⟨M, hM⟩ := hsmall
  set m := max M (N + 2) with hm
  have hmM : M ≤ m := le_max_left _ _
  have hmN : N + 2 ≤ m := le_max_right _ _
  have hle := hgrowth (m - N)
  have hmn : N + (m - N) = m := Nat.add_sub_of_le (le_trans (Nat.le_add_right N 2) hmN)
  rw [hmn] at hle
  have hc2 : 1 < c ^ (m - N) := by
    calc (1 : ℝ) < c := hc
      _ = c ^ 1 := (pow_one c).symm
      _ ≤ c ^ (m - N) := pow_le_pow_right₀ (le_of_lt hc) (by omega)
  have : ‖p (N : ℝ) - z₀‖ < c ^ (m - N) * ‖p (N : ℝ) - z₀‖ := by nlinarith
  have hlt := hM m hmM
  linarith [hle, this, hlt]

end Work.LandLeaves.Snail
