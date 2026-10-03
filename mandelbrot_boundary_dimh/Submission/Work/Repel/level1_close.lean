import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Spec
import Submission.Work.Repel.piExp_sub_one_bound
import Submission.Work.Repel.piExp_gap_bound

/-!
# REPEL, level 1: the rescaled return map is close to the rescaled horn map

Shishikura §6, Step 1.  The level-1 germ of the perturbation is
`ǧ = germ1 s R = ζ ↦ s · pushdown R (ζ/s)` where `R = R̃_f` is the lifted return map of the
perturbed map; the base germ is `g₀ = germ1 s d.E = ζ ↦ s · pushdown Ẽ_{f₀} (ζ/s)`.
On `π(K) ∪ {π w | |Im w| ≥ y}` (a compact lift plus a neighbourhood of the ends) the return map
satisfies `‖R w + 1/α - Ẽ_{f₀} w‖ < δ`, and we must translate this `δ`-closeness of the *lifts*
into closeness of the *pushed-down germs*.

Writing `w = log(ζ/s)/(2πi)` and `π = piExp`, the whole content is the estimate
`‖π (R w) - π (Ẽ w)‖ ≤ B · (8 ‖1 - π(-1/α)‖ + 32 π δ)`
under `‖π (Ẽ w)‖ ≤ B`, which we obtain from the factorisation
`π (R w) - π (Ẽ w) = π (Ẽ w) · (c·(π e - 1) + (c - 1))`,  `c = π(-1/α)`,  `e = R w + 1/α - Ẽ w`,
together with `‖π e - 1‖ ≤ 4πδ` (the linear regime of `exp`) and the elementary numerical
inequality `4πδ‖c‖ ≤ 32πδ + 7‖c-1‖` (valid because `4πδ ≤ 1/4`).

No hypothesis on `α` is needed: the `8` in front of `‖1 - π(-1/α)‖` absorbs the factor
`‖π(-1/α)‖` that appears when `e - 1/α` is expanded.

The two analytic/numerical ingredients are proved separately: `Work.Repel.piExp_sub_one_bound`
(module `Submission.Work.Repel.piExp_sub_one_bound`) and `Work.Repel.piExp_gap_bound`
(module `Submission.Work.Repel.piExp_gap_bound`).  `δ ≥ 0` is derived from the non-vacuity of
`hclose` (the set `K ∪ {|Im| ≥ y}` is nonempty, e.g. at `i(|y| + 1)`), so the case `δ < 0` of
the hypotheses is eliminated rather than being assumed away.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open Work.Horn.MandelDim

noncomputable section

/-- `π(a + b) = π a · π b` for `π = piExp`. -/
theorem level1_piExp_add (a b : ℂ) : piExp (a + b) = piExp a * piExp b := by
  rw [piExp, piExp, piExp, ← Complex.exp_add]
  congr 1
  ring

/-- Pure algebra: the difference of the pushed-down values factors through the lift error
`e = F w + 1/α - G w`. -/
theorem level1_piExp_diff_factor (F G : ℂ → ℂ) (α w : ℂ) :
    piExp (F w) - piExp (G w) =
      piExp (G w) * (piExp (-(1 / α)) * (piExp (F w + 1 / α - G w) - 1) +
        (piExp (-(1 / α)) - 1)) := by
  have hadd : ∀ a b : ℂ, piExp (a + b) = piExp a * piExp b := level1_piExp_add
  have h1 : piExp (F w) = piExp (G w) * piExp (F w - G w) := by
    rw [← hadd (G w) (F w - G w)]
    congr 1
    ring
  have h2 : F w - G w = (F w + 1 / α - G w) + (-(1 / α)) := by ring
  rw [h1, h2, hadd (F w + 1 / α - G w) (-(1 / α))]
  ring

/-- **Step 1 of §6 (level 1).**  If the lifted return map `R` is `δ`-close to the lifted horn map
`d.E` on `K ∪ {|Im| ≥ y}` in the sense `‖R w + 1/α - d.E w‖ < δ`, and `π (d.E w)` is bounded by
`B` on the lifted set `L`, then the rescaled pushdowns `germ1 s R` and `germ1 s d.E` are close
on `L`. -/
theorem level1_close {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (α : ℂ) (R : ℂ → ℂ)
    {K : Set ℂ} {y δ B : ℝ} {s : ℂ} (hs : s ≠ 0) (hδ : δ ≤ 1 / (16 * Real.pi)) (hB0 : 0 ≤ B)
    (hclose : ∀ w ∈ K ∪ {w : ℂ | y ≤ |w.im|}, ‖R w + 1 / α - d.E w‖ < δ)
    (L : Set ℂ)
    (hL : ∀ ζ ∈ L, ζ ≠ 0 → Complex.log (ζ / s) / (2 * Real.pi * I) ∈
      (K ∪ {w : ℂ | y ≤ |w.im|}))
    (hB : ∀ ζ ∈ L, ζ ≠ 0 →
      ‖piExp (d.E (Complex.log (ζ / s) / (2 * Real.pi * I)))‖ ≤ B) :
    ∀ ζ ∈ L, ‖germ1 s R ζ - germ1 s d.E ζ‖ ≤
      ‖s‖ * B * (8 * ‖1 - piExp (-(1 / α))‖ + 32 * Real.pi * δ) := by
  intro ζ hζL
  -- `δ ≥ 0`, from the non-vacuity of the hypothesis `hclose`
  have hδ0 : 0 ≤ δ := by
    have hw : ((((|y| + 1 : ℝ)) : ℂ) * Complex.I) ∈ (K ∪ {w : ℂ | y ≤ |w.im|}) := by
      right
      simp only [Set.mem_ofPred_eq]
      rw [Complex.mul_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        add_zero, mul_one]
      rw [abs_of_nonneg (by positivity)]
      linarith [le_abs_self y]
    exact le_trans (norm_nonneg _) (le_of_lt (hclose _ hw))
  rcases eq_or_ne ζ 0 with h0 | hne
  · -- `ζ = 0`: both germs vanish at `0`
    rw [h0, germ1_zero, germ1_zero, sub_zero, norm_zero]
    have h1 : (0:ℝ) ≤ 8 * ‖1 - piExp (-(1 / α))‖ + 32 * Real.pi * δ := by
      have := norm_nonneg (1 - piExp (-(1 / α)))
      nlinarith [Real.pi_pos, hδ0]
    exact mul_nonneg (mul_nonneg (norm_nonneg s) hB0) h1
  · set w : ℂ := Complex.log (ζ / s) / (2 * Real.pi * I) with hwdef
    have hζs : ζ / s ≠ 0 := div_ne_zero hne hs
    have hwS : w ∈ K ∪ {w : ℂ | y ≤ |w.im|} := hL ζ hζL hne
    have hRw : germ1 s R ζ = s * piExp (R w) := by
      rw [germ1_apply, pushdown_of_ne R hζs, hwdef]
    have hEw : germ1 s d.E ζ = s * piExp (d.E w) := by
      rw [germ1_apply, pushdown_of_ne d.E hζs, hwdef]
    -- the estimate on the lifted level
    have hnorm : ‖piExp (R w) - piExp (d.E w)‖ ≤
        B * (4 * Real.pi * δ * ‖piExp (-(1 / α))‖ + ‖piExp (-(1 / α)) - 1‖) := by
      rw [level1_piExp_diff_factor R d.E α w]
      have hb1 := norm_mul_le (piExp (d.E w))
        (piExp (-(1 / α)) * (piExp (R w + 1 / α - d.E w) - 1) + (piExp (-(1 / α)) - 1))
      have hb2 : ‖piExp (-(1 / α)) * (piExp (R w + 1 / α - d.E w) - 1) +
            (piExp (-(1 / α)) - 1)‖ ≤
          ‖piExp (-(1 / α))‖ * ‖piExp (R w + 1 / α - d.E w) - 1‖ +
            ‖piExp (-(1 / α)) - 1‖ := by
        refine le_trans (norm_add_le _ _) (le_of_eq ?_)
        rw [norm_mul]
      have hb3 : ‖piExp (R w + 1 / α - d.E w) - 1‖ ≤ 4 * Real.pi * δ :=
        piExp_sub_one_bound hδ (le_of_lt (hclose w hwS))
      have hBw : ‖piExp (d.E w)‖ ≤ B := hB ζ hζL hne
      have hb1' : ‖piExp (d.E w) * (piExp (-(1 / α)) * (piExp (R w + 1 / α - d.E w) - 1) +
            (piExp (-(1 / α)) - 1))‖ ≤
          B * (‖piExp (-(1 / α))‖ * ‖piExp (R w + 1 / α - d.E w) - 1‖ +
            ‖piExp (-(1 / α)) - 1‖) :=
        le_trans hb1 (mul_le_mul hBw hb2 (norm_nonneg _) hB0)
      refine le_trans hb1' (mul_le_mul_of_nonneg_left ?_ hB0)
      have hb4 := mul_le_mul_of_nonneg_left hb3 (norm_nonneg (piExp (-(1 / α))))
      linarith [hb4, norm_nonneg (piExp (-(1 / α)) - 1)]
    -- absorb `‖pi(-1/α)‖` into the constant `8`
    have hA2 : ‖piExp (R w) - piExp (d.E w)‖ ≤
        B * (8 * ‖1 - piExp (-(1 / α))‖ + 32 * Real.pi * δ) := by
      refine le_trans hnorm (mul_le_mul_of_nonneg_left ?_ hB0)
      rw [norm_sub_rev (1 : ℂ) (piExp (-(1 / α)))]
      linarith [piExp_gap_bound (piExp (-(1 / α))) hδ0 hδ]
    rw [hRw, hEw]
    calc ‖s * piExp (R w) - s * piExp (d.E w)‖
        = ‖s‖ * ‖piExp (R w) - piExp (d.E w)‖ := by
          rw [show s * piExp (R w) - s * piExp (d.E w) =
            s * (piExp (R w) - piExp (d.E w)) by ring, norm_mul]
      _ ≤ ‖s‖ * (B * (8 * ‖1 - piExp (-(1 / α))‖ + 32 * Real.pi * δ)) :=
          mul_le_mul_of_nonneg_left hA2 (norm_nonneg s)
      _ = ‖s‖ * B * (8 * ‖1 - piExp (-(1 / α))‖ + 32 * Real.pi * δ) := by ring

end

end Work.Repel
