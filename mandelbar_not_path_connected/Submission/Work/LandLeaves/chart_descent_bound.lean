/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# The chart-descent bound (Snail lemma, "descent" step)

For a germ `h(z) = z + c z^r + O(z^{r+1})` of order `r ≥ 2` at `0`, the coordinate
`u = 1/((r-1) c z^{r-1})` linearises the leading term: writing `u = g z`, one has
`g (h z) = g z - 1 + O(z)`, and since `z = O(‖u‖^{-1/(r-1)})` this gives the estimate
`‖g(h z) - (g z - 1)‖ ≤ M ‖u‖^{-1/(r-1)}` for `‖u‖` large, which is exactly what the
"descent" chart of the Snail lemma needs.

The content is the second-order Taylor estimate `norm_inv_pow_taylor` /
`norm_pow_inv_sub_linear` from `chart_descent_prelim`, assembled in `chart_descent_step`,
together with the elementary observation that the map `z ↦ 1/((r-1)c z^{r-1})` is exactly the
`(1/(r-1))`-power of a constant times `‖z‖^{-1}`.
-/
import Mathlib
import Submission.Work.LandLeaves.chart_descent_prelim
import Submission.Work.LandLeaves.rpow_norm_inv_eq
import Submission.Work.LandLeaves.chart_descent_step

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- **The chart-descent bound, parametrised by the order `n + 1 ≥ 2`.**  If `h` is a germ at `0`
with `h z = z + c z^{n+1} + O(z^{n+2})`, then for `z` with `‖1/((n:ℂ) c z^n)‖` large,
`1/((n:ℂ) c (h z)^n)` differs from `1/((n:ℂ) c z^n) - 1` by at most a constant times
`‖1/((n:ℂ) c z^n)‖^{-1/n}`. -/
theorem chart_descent_bound_aux {h : ℂ → ℂ} {c : ℂ} {n : ℕ}
    (hn : 1 ≤ n) (hc : c ≠ 0)
    (happrox : ∃ ρ : ℝ, 0 < ρ ∧ ∃ A : ℝ, 0 ≤ A ∧
      ∀ z : ℂ, ‖z‖ < ρ → ‖h z - z - c * z ^ (n + 1)‖ ≤ A * ‖z‖ ^ (n + 2)) :
    ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ z : ℂ, z ≠ 0 → R ≤ ‖(1 : ℂ) / ((n : ℂ) * c * z ^ n)‖ →
        ‖(1 : ℂ) / ((n : ℂ) * c * (h z) ^ n)
          - ((1 : ℂ) / ((n : ℂ) * c * z ^ n) - 1)‖
        ≤ M * ‖(1 : ℂ) / ((n : ℂ) * c * z ^ n)‖ ^ (-(1 : ℝ) / (n : ℝ)) := by
  obtain ⟨ρ, hρ, A, hA, happ⟩ := happrox
  have hn0 : (0 : ℕ) < n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hABpos : 0 < ‖c‖ + A := by linarith
  -- a radius `δ` inside the approximation neighbourhood, with `(‖c‖+A) δ ≤ 1/2` and `δ ≤ 1`
  set δ : ℝ := min (ρ / 2) (min 1 (1 / (2 * (‖c‖ + A)))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    apply lt_min
    · linarith
    · apply lt_min
      · norm_num
      · exact one_div_pos.mpr (by linarith)
  have hδle1 : δ ≤ 1 := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδleB : δ ≤ 1 / (2 * (‖c‖ + A)) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδlt : δ < ρ := by
    have : δ ≤ ρ / 2 := by rw [hδdef]; exact min_le_left _ _
    linarith
  have hδB : (‖c‖ + A) * δ ≤ 1 / 2 := by
    have h2 : 0 < 2 * (‖c‖ + A) := by linarith
    calc (‖c‖ + A) * δ ≤ (‖c‖ + A) * (1 / (2 * (‖c‖ + A))) :=
          mul_le_mul_of_nonneg_left hδleB (by linarith)
      _ = 1 / 2 := by field_simp
  have hkpos : 0 < (n : ℝ) * ‖c‖ := by positivity
  have hδnpos : 0 < ((n : ℝ) * ‖c‖) * δ ^ n := by positivity
  refine ⟨max 1 (1 / (((n : ℝ) * ‖c‖) * δ ^ n)), ?_,
    (A / ‖c‖ + (4 : ℝ) ^ n * (‖c‖ + A) ^ 2 / ((n : ℝ) * ‖c‖))
      * ((n : ℝ) * ‖c‖) ^ (-(1 : ℝ) / (n : ℝ)), ?_, ?_⟩
  · exact lt_max_iff.mpr (Or.inl one_pos)
  · apply mul_nonneg
    · have h4n : (0 : ℝ) ≤ (4 : ℝ) ^ n := by positivity
      have hdiv : 0 ≤ (4 : ℝ) ^ n * (‖c‖ + A) ^ 2 / ((n : ℝ) * ‖c‖) := by positivity
      have : 0 ≤ A / ‖c‖ := by positivity
      linarith
    · exact Real.rpow_nonneg (le_of_lt hkpos) _
  · intro z hz hR
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    -- the norm of the chart coordinate
    have hnorm : ‖(1 : ℂ) / ((n : ℂ) * c * z ^ n)‖ = (((n : ℝ) * ‖c‖) * ‖z‖ ^ n)⁻¹ := by
      rw [norm_div, norm_one, norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
      ring
    -- the hypothesis `R ≤ ‖·‖` forces `‖z‖ ≤ δ`
    have hzdelta : ‖z‖ ≤ δ := by
      have hx : 1 / (((n : ℝ) * ‖c‖) * δ ^ n) ≤ ‖(1 : ℂ) / ((n : ℂ) * c * z ^ n)‖ :=
        le_trans (le_max_right _ _) hR
      rw [one_div, hnorm] at hx
      have h2 : ((n : ℝ) * ‖c‖) * ‖z‖ ^ n ≤ ((n : ℝ) * ‖c‖) * δ ^ n :=
        (inv_le_inv₀ hδnpos (by positivity)).mp hx
      have h3 : ‖z‖ ^ n ≤ δ ^ n := le_of_mul_le_mul_left h2 hkpos
      exact (pow_le_pow_iff_left₀ (norm_nonneg z) (le_of_lt hδpos) (by omega : n ≠ 0)).mp h3
    -- the local estimate
    have hstep := chart_descent_step n hn c hc A hA h δ hδpos hδle1 hδB
      (fun z hz => happ z (by linarith))
    have hbound := hstep z hz hzdelta
    -- convert `‖z‖` into a power of the chart coordinate
    have hrel := rpow_norm_inv_eq n hn0 c z hc hz
    calc ‖(1 : ℂ) / ((n : ℂ) * c * (h z) ^ n) - ((1 : ℂ) / ((n : ℂ) * c * z ^ n) - 1)‖
        ≤ (A / ‖c‖ + (4 : ℝ) ^ n * (‖c‖ + A) ^ 2 / ((n : ℝ) * ‖c‖)) * ‖z‖ := hbound
      _ = (A / ‖c‖ + (4 : ℝ) ^ n * (‖c‖ + A) ^ 2 / ((n : ℝ) * ‖c‖))
            * (((n : ℝ) * ‖c‖) ^ (-(1 : ℝ) / (n : ℝ))
                * ‖(1 : ℂ) / ((n : ℂ) * c * z ^ n)‖ ^ (-(1 : ℝ) / (n : ℝ))) := by
          rw [hrel]
      _ = ((A / ‖c‖ + (4 : ℝ) ^ n * (‖c‖ + A) ^ 2 / ((n : ℝ) * ‖c‖))
              * ((n : ℝ) * ‖c‖) ^ (-(1 : ℝ) / (n : ℝ)))
            * ‖(1 : ℂ) / ((n : ℂ) * c * z ^ n)‖ ^ (-(1 : ℝ) / (n : ℝ)) := by
          ring

/-- **The chart-descent bound** (Hubbard–Schleicher, "Multicorns are not path connected",
the descent step of the Snail lemma): for a germ `h` of order `r ≥ 2` at `0` the coordinate
`u = 1/((r-1) c z^{r-1})` linearises `h` up to an error of size `O(‖u‖^{-1/(r-1)})`. -/
theorem chart_descent_bound {h : ℂ → ℂ} {c : ℂ} {r : ℕ}
    (hr : 2 ≤ r) (hc : c ≠ 0) (h0 : h 0 = 0)
    (happrox : ∃ ρ : ℝ, 0 < ρ ∧ ∃ A : ℝ, 0 ≤ A ∧
      ∀ z : ℂ, ‖z‖ < ρ → ‖h z - z - c * z ^ r‖ ≤ A * ‖z‖ ^ (r + 1)) :
    ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ z : ℂ, z ≠ 0 → R ≤ ‖(1 : ℂ) / ((r - 1 : ℂ) * c * z ^ (r - 1))‖ →
        ‖(1 : ℂ) / ((r - 1 : ℂ) * c * (h z) ^ (r - 1))
          - ((1 : ℂ) / ((r - 1 : ℂ) * c * z ^ (r - 1)) - 1)‖
        ≤ M * ‖(1 : ℂ) / ((r - 1 : ℂ) * c * z ^ (r - 1))‖ ^ (-(1 : ℝ) / ((r : ℝ) - 1)) := by
  have hn1 : 1 ≤ r - 1 := by omega
  have hrcast : (((r - 1 : ℕ)) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    norm_num
  have hccast : (((r - 1 : ℕ)) : ℂ) = (r : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    norm_num
  obtain ⟨ρ, hρ, A, hA, happ⟩ := happrox
  have happ' : ∀ z : ℂ, ‖z‖ < ρ →
      ‖h z - z - c * z ^ ((r - 1) + 1)‖ ≤ A * ‖z‖ ^ ((r - 1) + 2) := by
    intro z hz
    have h1 : ((r - 1) + 1) = r := Nat.succ_pred_eq_of_pos (by omega : 0 < r)
    have h2 : ((r - 1) + 2) = r + 1 := by omega
    rw [h1, h2]
    exact happ z hz
  obtain ⟨R, hR, M, hM, hbound⟩ := chart_descent_bound_aux (n := r - 1) hn1 hc
    ⟨ρ, hρ, A, hA, happ'⟩
  refine ⟨R, hR, M, hM, ?_⟩
  intro z hz hRz
  have hRz' : R ≤ ‖(1 : ℂ) / (((r - 1 : ℕ) : ℂ) * c * z ^ (r - 1))‖ := by
    rw [hccast]; exact hRz
  have hthis := hbound z hz hRz'
  rw [hccast, hrcast] at hthis
  exact hthis

end Work.LandLeaves
