import Mathlib
import Submission.Work.LinnikAreas.TuranOther.Defs
import Submission.Work.LinnikAreas.TuranOther.twMultMax
import Submission.Work.LinnikContract.Defs

/-!
# `Work.LinnikAreas.TuranOther.twAuxBounds`

The two hypotheses of Turán's power-sum theorem
(`Work.LinnikAreas.DhK.turanWeighted`, in its weighted form) for the twisted zero multiset of
`D(s) = ζ(s)·L(s,χ₀)·L(s+iγ,χ)·L(s+iγ,χ₀χ)`:

* **the Weyl/mass hypothesis** — the weighted sum
  `∑_u w(u)·‖z(u)‖/(‖z(u₀)‖+‖z(u)‖)` converges and is bounded by `‖1+α-u₀‖²·C·(log q + 1)`,
  where `w(u) = twMult u` is the multiplicity and `z(u) = twZ u` the zero weight; and

* **the power sums** — `∑_u w(u)·z(u)^j` converges (for `1 ≤ j`) and its real part is `twSum`.

Everything here is a *transfer* statement: the mass hypothesis `hMass` already bounds
`∑_u w(u)/‖1+α-u‖² = ∑_u w(u)·‖zval α u‖`, and since `twZ` agrees with `zval` on the zero
multiset and vanishes off it, the weighted power sums are dominated by that sum because
`‖z(u)‖ ≤ ‖z(u₀)‖` for all `u` in the multiset (`hmax`): indeed
`w(u)·‖z(u)‖^j ≤ ‖z(u₀)‖^{j-1}·w(u)·‖z(u)‖`.  For the Weyl sum a purely arithmetic bound
suffices: `1/(‖z(u₀)‖+‖z(u)‖) ≤ ‖1+α-u₀‖²` (as `‖z(u₀)‖ = ‖1+α-u₀‖^{-2}`), so dividing by
`‖z(u₀)‖ + ‖z(u)‖` never costs more than multiplying by `‖1+α-u₀‖²`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators Topology

noncomputable section

namespace Work.LinnikAreas.TuranOther

/-! ## Elementary properties of `twZ` -/

/-- `twZ` agrees with the power-sum variable `zval` on the zero multiset. -/
lemma twZ_eq_zval_of_ne {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (β₀ γ α : ℝ)
    (u : ℂ) (h : twMult χ₀ χ β₀ γ u ≠ 0) : twZ χ₀ χ β₀ γ α u = zval α u := by
  rw [twZ, if_neg h]

/-- `twZ` vanishes off the zero multiset. -/
lemma twZ_eq_zero_of_eq_zero {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q)
    (β₀ γ α : ℝ) (u : ℂ) (h : twMult χ₀ χ β₀ γ u = 0) : twZ χ₀ χ β₀ γ α u = 0 := by
  rw [twZ, if_pos h]

/-- The zero weight is dominated by the power-sum variable. -/
lemma norm_twZ_le {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (β₀ γ α : ℝ) (u : ℂ) :
    ‖twZ χ₀ χ β₀ γ α u‖ ≤ ‖zval α u‖ := by
  by_cases h : twMult χ₀ χ β₀ γ u = 0
  · rw [twZ, if_pos h]; simp
  · rw [twZ, if_neg h]

/-! ## Two arithmetic / summability lemmas -/

/-- **The weighted ratio bound.**  If `X·M₀ = 1` then dividing by `M₀ + M` costs at most the
factor `X`: `w·M/(M₀+M) ≤ X·(w·M)` whenever `w, M ≥ 0` and `M₀ > 0`.

This is the elementary estimate behind the Weyl-sum hypothesis: with `M = ‖z(u)‖`,
`M₀ = ‖z(u₀)‖` and `X = ‖1+α-u₀‖² = 1/M₀`, the summand
`w(u)·‖z(u)‖/(‖z(u₀)‖+‖z(u)‖)` is bounded by `X` times the mass summand `w(u)·‖z(u)‖`. -/
lemma mul_div_add_le {w M M₀ X : ℝ} (hw : 0 ≤ w) (hM : 0 ≤ M) (hM₀ : 0 < M₀)
    (hX : X * M₀ = 1) : w * (M / (M₀ + M)) ≤ X * (w * M) := by
  have hXnn : 0 ≤ X := by
    by_contra h
    have h' : X * M₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp h)) hM₀.le
    rw [hX] at h'
    norm_num at h'
  rcases eq_or_lt_of_le hM with hM0 | hMpos
  · rw [← hM0]; simp
  · have hden : 0 < M₀ + M := by linarith
    rw [← mul_div_assoc, div_le_iff₀ hden]
    have h3 : X * M₀ ≤ X * (M₀ + M) := mul_le_mul_of_nonneg_left (by linarith) hXnn
    calc w * M = w * M * (X * M₀) := by rw [hX, mul_one]
      _ ≤ w * M * (X * (M₀ + M)) := mul_le_mul_of_nonneg_left h3 (mul_nonneg hw hM)
      _ = X * (w * M) * (M₀ + M) := by ring

/-- **Summability of weighted `j`-th powers.**  If `w ≥ 0`, `‖Z i‖ ≤ M i`, `M` is bounded by `M₀`
wherever `w` does not vanish, and `∑ w·M` converges, then `∑ w·Z^j` converges for `j ≥ 1`.

The point is that `‖Z i‖^j = ‖Z i‖^{j-1}·‖Z i‖ ≤ M₀^{j-1}·M i` on the support of `w`, while off
it both sides vanish. -/
lemma summable_weighted_pow {ι : Type*} (w : ι → ℝ) (Z : ι → ℂ) (M : ι → ℝ) (M₀ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hZ : ∀ i, ‖Z i‖ ≤ M i)
    (hM₀ : 0 ≤ M₀) (hmax : ∀ i, w i ≠ 0 → M i ≤ M₀)
    (hsum : Summable fun i => w i * M i) (j : ℕ) (hj : 1 ≤ j) :
    Summable fun i => (w i : ℂ) * (Z i) ^ j := by
  refine Summable.of_norm_bounded (g := fun i => M₀ ^ (j - 1) * (w i * M i))
    (hsum.mul_left _) (fun i => ?_)
  rcases eq_or_lt_of_le (hw i) with hw0 | hwpos
  · rw [← hw0]; simp
  · have hn : ‖(w i : ℂ) * (Z i) ^ j‖ = w i * ‖Z i‖ ^ j := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i), norm_pow]
    have hMi : M i ≤ M₀ := hmax i (ne_of_gt hwpos)
    have hpowj : ‖Z i‖ ^ j = ‖Z i‖ ^ (j - 1) * ‖Z i‖ := by
      conv_lhs => rw [← Nat.sub_add_cancel hj, pow_succ]
    have h2 : ‖Z i‖ ^ (j - 1) ≤ M₀ ^ (j - 1) :=
      pow_le_pow_left₀ (norm_nonneg _) (le_trans (hZ i) hMi) _
    rw [hn, hpowj]
    calc w i * (‖Z i‖ ^ (j - 1) * ‖Z i‖)
        ≤ w i * (M₀ ^ (j - 1) * M i) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul h2 (hZ i) (norm_nonneg _) (pow_nonneg hM₀ _)) (hw i)
      _ = M₀ ^ (j - 1) * (w i * M i) := by ring

/-! ## The pointwise comparison with the mass sum -/

/-- **Pointwise Weyl--mass comparison.**  Off the zero multiset both sides vanish; on it,
`‖twZ u‖ = ‖zval α u‖` and `‖zval α u₀‖ = ‖1+α-u₀‖^{-2}`, so that dividing by
`‖twZ u₀‖ + ‖twZ u‖` is dominated by multiplication by `‖1+α-u₀‖²`. -/
lemma twAux_pointwise {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (β₀ γ α : ℝ)
    (hα : 1 ≤ α) (u₀ : ℂ) (hu₀ : twMult χ₀ χ β₀ γ u₀ ≠ 0) (u : ℂ) :
    ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) *
        (‖twZ χ₀ χ β₀ γ α u‖ / (‖twZ χ₀ χ β₀ γ α u₀‖ + ‖twZ χ₀ χ β₀ γ α u‖))
      ≤ ‖(1 : ℂ) + (α : ℂ) - u₀‖ ^ 2 *
        (((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖(1 : ℂ) + (α : ℂ) - u‖ ^ 2) := by
  by_cases h : twMult χ₀ χ β₀ γ u = 0
  · rw [h]; simp
  · rw [twZ_eq_zval_of_ne χ₀ χ β₀ γ α u h, twZ_eq_zval_of_ne χ₀ χ β₀ γ α u₀ hu₀]
    -- `1 + α` is not a zero of the twisted product, so `1 + α - u₀ ≠ 0`
    have hc₀ : (1 : ℂ) + (α : ℂ) - u₀ ≠ 0 := by
      intro hc
      have h2 : (1 : ℂ) + (α : ℂ) = u₀ := sub_eq_zero.mp hc
      exact hu₀ (by rw [← h2]; exact twMult_one_add_alpha_eq_zero χ₀ χ β₀ γ α hα)
    have hX : ‖(1 : ℂ) + (α : ℂ) - u₀‖ ^ 2 * ‖zval α u₀‖ = 1 := by
      rw [norm_zval_eq α u₀, mul_one_div_cancel (a := ‖(1 : ℂ) + (α : ℂ) - u₀‖ ^ 2)
        (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc₀))]
    have hM₀pos : 0 < ‖zval α u₀‖ := by
      rw [norm_zval_eq α u₀]
      exact one_div_pos.mpr (pow_pos (norm_pos_iff.mpr hc₀) 2)
    have hkey := mul_div_add_le (w := ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ))
      (M := ‖zval α u‖) (M₀ := ‖zval α u₀‖) (X := ‖(1 : ℂ) + (α : ℂ) - u₀‖ ^ 2)
      (Nat.cast_nonneg _) (norm_nonneg _) hM₀pos hX
    have hR : ‖(1 : ℂ) + (α : ℂ) - u₀‖ ^ 2 *
        (((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖(1 : ℂ) + (α : ℂ) - u‖ ^ 2)
        = ‖(1 : ℂ) + (α : ℂ) - u₀‖ ^ 2 *
          (((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) * ‖zval α u‖) := by
      rw [norm_zval_eq α u, mul_one_div]
    rw [hR]
    exact hkey

/-! ## The main statement -/

theorem twAuxBounds {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (β₀ γ α : ℝ)
    (hα : 1 ≤ α) (C : ℝ)
    (hMass : Summable (fun u : ℂ =>
        ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖(1 : ℂ) + (α : ℂ) - u‖ ^ 2) ∧
      (∑' u : ℂ, ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖(1 : ℂ) + (α : ℂ) - u‖ ^ 2)
        ≤ C * (Real.log (q : ℝ) + 1))
    (u₀ : ℂ) (hu₀ : twMult χ₀ χ β₀ γ u₀ ≠ 0)
    (hmax : ∀ u : ℂ, twMult χ₀ χ β₀ γ u ≠ 0 → ‖zval α u‖ ≤ ‖zval α u₀‖)
    (j : ℕ) (hj : 1 ≤ j) :
    Summable (fun u : ℂ => ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) *
        (‖twZ χ₀ χ β₀ γ α u‖ / (‖twZ χ₀ χ β₀ γ α u₀‖ + ‖twZ χ₀ χ β₀ γ α u‖))) ∧
      (∑' u : ℂ, ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) *
        (‖twZ χ₀ χ β₀ γ α u‖ / (‖twZ χ₀ χ β₀ γ α u₀‖ + ‖twZ χ₀ χ β₀ γ α u‖)))
        ≤ ‖(1 : ℂ) + (α : ℂ) - u₀‖ ^ 2 * (C * (Real.log (q : ℝ) + 1)) ∧
    Summable (fun u : ℂ => ((((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) : ℂ) * (twZ χ₀ χ β₀ γ α u) ^ j)) ∧
    (∑' u : ℂ, ((((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) : ℂ) * (twZ χ₀ χ β₀ γ α u) ^ j)).re
      = twSum χ₀ χ β₀ γ α j := by
  classical
  set X : ℝ := ‖(1 : ℂ) + (α : ℂ) - u₀‖ ^ 2 with hXdef
  -- the pointwise comparison against the mass sum
  have hpt : ∀ u : ℂ, ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) *
        (‖twZ χ₀ χ β₀ γ α u‖ / (‖twZ χ₀ χ β₀ γ α u₀‖ + ‖twZ χ₀ χ β₀ γ α u‖))
      ≤ X * (((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖(1 : ℂ) + (α : ℂ) - u‖ ^ 2) := by
    intro u
    have h := twAux_pointwise χ₀ χ β₀ γ α hα u₀ hu₀ u
    rwa [← hXdef] at h
  have hSumm1 : Summable (fun u : ℂ => ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) *
        (‖twZ χ₀ χ β₀ γ α u‖ / (‖twZ χ₀ χ β₀ γ α u₀‖ + ‖twZ χ₀ χ β₀ γ α u‖))) := by
    refine Summable.of_nonneg_of_le (f := fun u : ℂ => X *
      (((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖(1 : ℂ) + (α : ℂ) - u‖ ^ 2)) (fun u => ?_) (fun u => ?_)
      (hMass.1.mul_left X)
    · exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (norm_nonneg _) (by positivity))
    · exact hpt u
  have hle1 : (∑' u : ℂ, ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) *
        (‖twZ χ₀ χ β₀ γ α u‖ / (‖twZ χ₀ χ β₀ γ α u₀‖ + ‖twZ χ₀ χ β₀ γ α u‖)))
      ≤ X * (C * (Real.log (q : ℝ) + 1)) := by
    calc (∑' u : ℂ, ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) *
          (‖twZ χ₀ χ β₀ γ α u‖ / (‖twZ χ₀ χ β₀ γ α u₀‖ + ‖twZ χ₀ χ β₀ γ α u‖)))
        ≤ (∑' u : ℂ, X *
            (((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖(1 : ℂ) + (α : ℂ) - u‖ ^ 2)) :=
          Summable.tsum_le_tsum hpt hSumm1 (hMass.1.mul_left X)
      _ = X * (∑' u : ℂ, ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖(1 : ℂ) + (α : ℂ) - u‖ ^ 2) :=
          tsum_mul_left
      _ ≤ X * (C * (Real.log (q : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hMass.2 (by positivity)
  -- summability of the weighted `j`-th powers
  have hsumM : Summable (fun u : ℂ => ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) * ‖zval α u‖) :=
    hMass.1.congr (fun u => by rw [norm_zval_eq α u, mul_one_div])
  have hSumm3 : Summable (fun u : ℂ =>
      ((((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) : ℂ) * (twZ χ₀ χ β₀ γ α u) ^ j)) :=
    summable_weighted_pow (w := fun u : ℂ => ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ))
      (Z := fun u : ℂ => twZ χ₀ χ β₀ γ α u) (M := fun u : ℂ => ‖zval α u‖)
      (M₀ := ‖zval α u₀‖) (fun u => Nat.cast_nonneg _)
      (fun u => norm_twZ_le χ₀ χ β₀ γ α u) (norm_nonneg _)
      (fun u h => hmax u (Nat.cast_ne_zero.mp h)) hsumM j hj
  -- the power sums agree with those of `zval`
  have hpointwise : ∀ u : ℂ,
      ((((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) : ℂ) * (twZ χ₀ χ β₀ γ α u) ^ j)
        = ((((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) : ℂ) * (zval α u) ^ j) := by
    intro u
    by_cases h : twMult χ₀ χ β₀ γ u = 0
    · rw [h]; simp [twZ, h]
    · rw [twZ, if_neg h]
  have hsummzv : Summable (fun u : ℂ =>
      ((((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) : ℂ) * (zval α u) ^ j)) :=
    hSumm3.congr hpointwise
  have htsumeq : (∑' u : ℂ, ((((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) : ℂ) * (twZ χ₀ χ β₀ γ α u) ^ j))
      = ∑' u : ℂ, ((((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) : ℂ) * (zval α u) ^ j) :=
    tsum_congr hpointwise
  have hre : (∑' u : ℂ, ((((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) : ℂ) * (zval α u) ^ j)).re
      = twSum χ₀ χ β₀ γ α j := by
    rw [Complex.re_tsum hsummzv, twSum]
    exact tsum_congr (fun u => by simp [Complex.mul_re])
  refine ⟨hSumm1, ?_, hSumm3, ?_⟩
  · rw [hXdef]; exact hle1
  · rw [htsumeq]; exact hre

end Work.LinnikAreas.TuranOther

end
