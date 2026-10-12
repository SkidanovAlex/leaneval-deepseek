import Mathlib.Tactic.Have
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.SymAPI
import Submission.Work.OneBodyKin.TruncDefs
import Submission.Work.OneBodyKin.integrable_bsKern
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.famSym_Ftrunc_bound`

**A uniform, quadratic-in-`q` bound on the symbol of the projected moving-box family at the
truncated FS cut-off.**  For the truncations `Ftrunc c n = [· − c]₊² · 1_{· ≤ n}` of
`TruncDefs.lean` we show

    `∃ A B ≥ 0,  ∀ n q,  |famSym ℓ (Ftrunc c n) q| ≤ A ‖q‖² + B`,

with `A, B` **independent of `n`**.  This is the domination hypothesis that turns the pointwise
convergence `famSym ℓ (Ftrunc c n) q → famSym ℓ (fsKinCoeff c) q` (`famSym_Ftrunc_tendsto`) into a
dominated-convergence statement in `q` (the sibling residual `SymbolIntegralRhsTendsto`), where the
growth of `Ftrunc c n` with `n` would otherwise make any `n`-dependent constant useless.

## The bound, term by term

With `famSym = symA − 2(2π)⁻³ boxHat · symD + symC` (`Defs.lean`) it is enough to bound the three
symbol terms uniformly in `n`, using only two facts about the truncations:

* `Ftrunc c n r ≤ [r − c]₊² ≤ 2(1 + c²)(1 + r²)`, so the *radial weight* of `Ftrunc c n` grows at
  most quadratically in `‖q‖ — uniformly in `n`;
* `|profHat p| ≤ C (1 + ‖p‖)⁻⁶` (the hypothesis `hd`), which makes every weighted integral of
  `profHat` used below finite (in dimension `3`, `(1+‖p‖)⁻⁴` is integrable).

Concretely,
* `symA ℓ F q = (2π)⁻³ ∫_p F‖q + ℓ⁻¹p‖ profHat(p)²` gains `‖q‖²` through
  `F‖q + ℓ⁻¹p‖ ≤ 2(1+c²)(1 + 2‖q‖² + 2ℓ⁻²‖p‖²)` and `∫ (1 + ‖p‖²)profHat² < ∞`;
* `symD ℓ F q = ∫_p F‖p‖ profHat(ℓp) profHat(ℓ(q−p))` is bounded by the *constant*
  `2(1+c²)·max C 1·∫_p (1+‖p‖²)|profHat(ℓp)|`, by replacing the second profile factor by its
  supremum `max C 1` and using the weight `F ‖p‖ ≤ 2(1+c²)(1+‖p‖²)`;
* `symC ℓ F q = symA ℓ F 0 · ℓ⁻⁶ · boxHat(ℓq)²` is bounded by the *same* constant `B` that bounds
  `symA ℓ F 0` at `q = 0`, since `|boxHat ℓ q| ≤ ℓ³` (`abs_boxHat_le`).

There is no measurability issue: the two integral bounds are obtained from
`norm_integral_le_of_norm_le`, which needs only the integrability of the *dominating* function.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The bump profile under the decay hypothesis

Everything below uses only

* the *sup* bound `|profHat p| ≤ C` (from `hd` and `‖p‖ ≥ 0`),
* the *weighted* integrability of `profHat` and of its square, which `hd` supplies through the
  comparison `(1+‖p‖²)|profHat p|^k ≤ (max C 1)² (1+‖p‖)^{−4}` (and `(1+‖p‖)^{-4} ∈ L¹` in
  dimension `3`).
-/

/-- `hd` written with a real power: `|profHat p| ≤ C (1+‖p‖)^{-6}`. -/
private lemma profHat_abs_le_rpow {C : ℝ}
    (hd : ∀ p : ℝ³, |profHat p| ≤ C / (1 + ‖p‖) ^ 6) (p : ℝ³) :
    |profHat p| ≤ C * (1 + ‖p‖) ^ (-(6:ℝ)) := by
  refine (hd p).trans (le_of_eq ?_)
  have hx : (0:ℝ) < 1 + ‖p‖ := by positivity
  have h6 : (1 + ‖p‖) ^ (6:ℝ) = (1 + ‖p‖) ^ 6 := Real.rpow_natCast _ 6
  calc C / (1 + ‖p‖) ^ 6 = C * ((1 + ‖p‖) ^ 6)⁻¹ := by rw [div_eq_mul_inv]
    _ = C * (((1 + ‖p‖) ^ (6:ℝ))⁻¹) := by rw [← h6]
    _ = C * (1 + ‖p‖) ^ (-(6:ℝ)) := by rw [← Real.rpow_neg hx.le (6:ℝ)]

/-- The uniform bound underlying the decay hypothesis: `|profHat p| ≤ C`. -/
private lemma profHat_abs_le_const {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ p : ℝ³, |profHat p| ≤ C / (1 + ‖p‖) ^ 6) (p : ℝ³) : |profHat p| ≤ C := by
  refine (hd p).trans ?_
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + ‖p‖) ^ 6)]
  have h1 : (1:ℝ) ≤ (1 + ‖p‖) ^ 6 := one_le_pow₀ (by linarith [norm_nonneg p])
  simpa using mul_le_mul_of_nonneg_left h1 hC

/-- `(1 + ‖p‖)^{-4}` is integrable on `ℝ³` — the master dominating function. -/
private lemma integrable_one_add_norm_four :
    Integrable (fun p : ℝ³ => (1 + ‖p‖) ^ (-(4:ℝ))) :=
  integrable_one_add_norm (E := ℝ³) (μ := volume) (r := (4:ℝ)) (by
    rw [finrank_euclideanSpace_fin]; norm_num)

/-- The scaled master dominating function: `κ (1+‖p‖)^{-4}`. -/
private lemma integrable_div_four (κ : ℝ) :
    Integrable (fun p : ℝ³ => κ / (1 + ‖p‖) ^ 4) := by
  have h := integrable_one_add_norm_four.const_mul κ
  refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
  have hx : (0:ℝ) < 1 + ‖p‖ := by positivity
  have h4 : (1 + ‖p‖) ^ (4:ℝ) = (1 + ‖p‖) ^ 4 := Real.rpow_natCast _ 4
  show κ * (1 + ‖p‖) ^ (-(4:ℝ)) = κ / (1 + ‖p‖) ^ 4
  rw [div_eq_mul_inv, ← h4, ← Real.rpow_neg hx.le (4:ℝ)]

/-- The square of the profile against the decay hypothesis. -/
private lemma profHat_sq_div_le {C : ℝ}
    (hd : ∀ p : ℝ³, |profHat p| ≤ C / (1 + ‖p‖) ^ 6) (p : ℝ³) :
    profHat p ^ 2 ≤ C ^ 2 / (1 + ‖p‖) ^ 12 := by
  have hx : (0:ℝ) < 1 + ‖p‖ := by positivity
  have h1 : |profHat p| ≤ C / (1 + ‖p‖) ^ 6 := hd p
  calc profHat p ^ 2 = |profHat p| ^ 2 := (sq_abs _).symm
    _ ≤ (C / (1 + ‖p‖) ^ 6) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = C ^ 2 / (1 + ‖p‖) ^ 12 := by rw [div_pow]; ring

/-- The weighted square of the profile: `(1+‖p‖²) profHat(p)² ≤ (max C 1)² (1+‖p‖)^{-4}`. -/
private lemma profHat_sq_weight_div_le {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ p : ℝ³, |profHat p| ≤ C / (1 + ‖p‖) ^ 6) (p : ℝ³) :
    (1 + ‖p‖ ^ 2) * profHat p ^ 2 ≤ (max C 1) ^ 2 / (1 + ‖p‖) ^ 4 := by
  have hx : (0:ℝ) < 1 + ‖p‖ := by positivity
  have h1 : (1 + ‖p‖ ^ 2) ≤ (1 + ‖p‖) ^ 2 := by nlinarith [norm_nonneg p]
  have h2 : profHat p ^ 2 ≤ C ^ 2 / (1 + ‖p‖) ^ 12 := profHat_sq_div_le hd p
  have hstep : (1 + ‖p‖ ^ 2) * profHat p ^ 2 ≤ C ^ 2 / (1 + ‖p‖) ^ 10 := by
    refine (mul_le_mul h1 h2 (sq_nonneg _) (by positivity)).trans (le_of_eq ?_)
    have : (1 + ‖p‖) ^ 2 * (C ^ 2 / (1 + ‖p‖) ^ 12) = C ^ 2 / (1 + ‖p‖) ^ 10 := by
      field_simp
    exact this
  refine hstep.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hCmax : C ≤ max C 1 := le_max_left _ _
  have h1c : C ^ 2 ≤ (max C 1) ^ 2 := pow_le_pow_left₀ hC hCmax 2
  calc C ^ 2 * (1 + ‖p‖) ^ 4 ≤ (max C 1) ^ 2 * (1 + ‖p‖) ^ 4 :=
        mul_le_mul_of_nonneg_right h1c (by positivity)
    _ ≤ (max C 1) ^ 2 * (1 + ‖p‖) ^ 10 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact pow_le_pow_right₀ (by linarith [norm_nonneg p]) (by norm_num : 4 ≤ 10)

/-- The weighted profile itself: `(1+‖p‖²)|profHat p| ≤ (max C 1)² (1+‖p‖)^{-4}`. -/
private lemma profHat_abs_weight_div_le {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ p : ℝ³, |profHat p| ≤ C / (1 + ‖p‖) ^ 6) (p : ℝ³) :
    (1 + ‖p‖ ^ 2) * |profHat p| ≤ (max C 1) ^ 2 / (1 + ‖p‖) ^ 4 := by
  have hx : (0:ℝ) < 1 + ‖p‖ := by positivity
  have h1 : (1 + ‖p‖ ^ 2) ≤ (1 + ‖p‖) ^ 2 := by nlinarith [norm_nonneg p]
  have h2 : |profHat p| ≤ C / (1 + ‖p‖) ^ 6 := hd p
  have hstep : (1 + ‖p‖ ^ 2) * |profHat p| ≤ C / (1 + ‖p‖) ^ 4 := by
    refine (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)).trans (le_of_eq ?_)
    have : (1 + ‖p‖) ^ 2 * (C / (1 + ‖p‖) ^ 6) = C / (1 + ‖p‖) ^ 4 := by
      field_simp
    exact this
  refine hstep.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hCmax : C ≤ max C 1 := le_max_left _ _
  have hmax0 : (0:ℝ) ≤ max C 1 := le_trans hC hCmax
  have hmax1 : (1:ℝ) ≤ max C 1 := le_max_right _ _
  have h1c : C ≤ (max C 1) ^ 2 := by nlinarith
  have h4 : (1:ℝ) ≤ (1 + ‖p‖) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg p])
  nlinarith [h1c, h4, hmax0, sq_nonneg (max C 1)]

/-- `profHat²` is integrable under the decay hypothesis. -/
private lemma integrable_profHat_sq {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ p : ℝ³, |profHat p| ≤ C / (1 + ‖p‖) ^ 6) :
    Integrable (fun p : ℝ³ => profHat p ^ 2) := by
  have hcap := profHat_sq_weight_div_le hC hd
  refine (integrable_div_four ((max C 1) ^ 2)).mono' ?_ ?_
  · exact (stronglyMeasurable_profHat.pow 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun p => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : (0:ℝ) ≤ 1 + ‖p‖ ^ 2 := by positivity
    have h2 : profHat p ^ 2 ≤ (1 + ‖p‖ ^ 2) * profHat p ^ 2 := by
      rw [add_mul, one_mul]
      exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    exact h2.trans (hcap p)

/-- `‖p‖² profHat(p)²` is integrable under the decay hypothesis. -/
private lemma integrable_profHat_sq_normSq {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ p : ℝ³, |profHat p| ≤ C / (1 + ‖p‖) ^ 6) :
    Integrable (fun p : ℝ³ => ‖p‖ ^ 2 * profHat p ^ 2) := by
  refine (integrable_div_four ((max C 1) ^ 2)).mono' ?_ ?_
  · exact ((continuous_norm.pow 2).aestronglyMeasurable.mul
      (stronglyMeasurable_profHat.pow 2).aestronglyMeasurable)
  · refine Filter.Eventually.of_forall (fun p => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    refine (mul_le_mul_of_nonneg_right (by linarith [norm_nonneg p]) (sq_nonneg _)).trans
      (profHat_sq_weight_div_le hC hd p)

/-- `(1+‖p‖²) |profHat (ℓ p)|` is integrable for `ℓ > 0` under the decay hypothesis. -/
private lemma integrable_profHat_abs_scale {ℓ C : ℝ} (hℓ : 0 < ℓ) (hC : 0 ≤ C)
    (hd : ∀ p : ℝ³, |profHat p| ≤ C / (1 + ‖p‖) ^ 6) :
    Integrable (fun p : ℝ³ => (1 + ‖p‖ ^ 2) * |profHat (ℓ • p)|) := by
  have hk0 : (0:ℝ) < min 1 ℓ := lt_min one_pos hℓ
  have hk1 : min 1 ℓ ≤ 1 := min_le_left _ _
  have hkl : min 1 ℓ ≤ ℓ := min_le_right _ _
  have hbase : ∀ p : ℝ³, (min 1 ℓ) * (1 + ‖p‖) ≤ 1 + ℓ * ‖p‖ := by
    intro p
    have hkk1 : min 1 ℓ ≤ 1 := hk1
    have hkkl : min 1 ℓ ≤ ℓ := hkl
    have hrn : (0:ℝ) ≤ ‖p‖ := norm_nonneg p
    nlinarith [mul_nonneg (sub_nonneg.mpr hkkl) hrn, mul_nonneg (sub_nonneg.mpr hkk1) (by norm_num : (0:ℝ) ≤ 1)]
  have hmain : Integrable (fun p : ℝ³ => (1 + ‖p‖ ^ 2) * ‖profHat (ℓ • p)‖) := by
    refine (integrable_div_four ((max C 1) ^ 2 / (min 1 ℓ) ^ 6)).mono' ?_ ?_
    · exact ((continuous_const.add (continuous_norm.pow 2)).aestronglyMeasurable.mul
        ((stronglyMeasurable_profHat.comp_measurable
          (measurable_id.const_smul ℓ)).norm).aestronglyMeasurable)
    · refine Filter.Eventually.of_forall (fun p => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
      have h1 : (1 + ‖p‖ ^ 2) ≤ (1 + ‖p‖) ^ 2 := by linarith [norm_nonneg p]
      have hns : ‖ℓ • p‖ = ℓ * ‖p‖ := by rw [norm_smul, Real.norm_of_nonneg hℓ.le]
      have h2 : ‖profHat (ℓ • p)‖ ≤ C / (1 + ℓ * ‖p‖) ^ 6 := by
        rw [Real.norm_eq_abs, ← hns]; exact hd (ℓ • p)
      have hbase0 : (0:ℝ) < (min 1 ℓ) * (1 + ‖p‖) := by positivity
      have h3 : C / (1 + ℓ * ‖p‖) ^ 6 ≤ C / ((min 1 ℓ) * (1 + ‖p‖)) ^ 6 :=
        div_le_div_of_nonneg_left hC (pow_pos hbase0 6) (pow_le_pow_left₀ hbase0.le (hbase p) 6)
      have hstep : (1 + ‖p‖ ^ 2) * ‖profHat (ℓ • p)‖ ≤ C / (min 1 ℓ) ^ 6 / (1 + ‖p‖) ^ 4 := by
        refine (mul_le_mul h1 (h2.trans h3) (norm_nonneg _) (by positivity)).trans (le_of_eq ?_)
        have : (1 + ‖p‖) ^ 2 * (C / ((min 1 ℓ) * (1 + ‖p‖)) ^ 6)
            = C / (min 1 ℓ) ^ 6 / (1 + ‖p‖) ^ 4 := by
          rw [mul_pow]
          field_simp
        exact this
      refine hstep.trans ?_
      have h1c : C ≤ (max C 1) ^ 2 := by
        have := le_max_left C (1:ℝ)
        nlinarith [le_max_right C (1:ℝ), sq_nonneg (max C 1)]
      exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right h1c (by positivity))
        (by positivity)
  exact hmain.congr (Filter.Eventually.of_forall (fun p => by simp only [Real.norm_eq_abs]))

/-! ## 2. Uniform bounds on the individual symbol terms -/

/-- The truncations grow at most quadratically, uniformly in `n`. -/
private lemma Ftrunc_abs_le (c : ℝ) (n : ℕ) (r : ℝ) :
    |Ftrunc c n r| ≤ 2 * (1 + c ^ 2) * (1 + r ^ 2) := by
  rw [Ftrunc_apply]
  by_cases h : r ≤ (n : ℝ)
  · rw [if_pos h]
    have hnn : (0:ℝ) ≤ max (r - c) 0 := le_max_right _ _
    have h1 : max (r - c) 0 ≤ |r| + |c| := by
      refine max_le ?_ ?_
      · linarith [le_abs_self r, neg_le_abs c]
      · positivity
    have h2 : (max (r - c) 0) ^ 2 ≤ (|r| + |c|) ^ 2 := pow_le_pow_left₀ hnn h1 2
    have h3 : (|r| + |c|) ^ 2 ≤ 2 * (1 + c ^ 2) * (1 + r ^ 2) := by
      have hs : |c| ^ 2 = c ^ 2 := sq_abs c
      have hr : |r| ^ 2 = r ^ 2 := sq_abs r
      nlinarith [sq_nonneg (|r| - |c|), sq_nonneg r, sq_nonneg c, abs_nonneg r, abs_nonneg c]
    have hfs : fsKinCoeff c r = (max (r - c) 0) ^ 2 := rfl
    rw [hfs, abs_of_nonneg (sq_nonneg _)]
    linarith
  · rw [if_neg h, abs_zero]
    positivity

/-- **Uniform bound on `symA`** with explicit constants, for a radial symbol `F` bounded by
`β (1+r²)`.  The constants involve only `β`, `ℓ` and the two profile integrals. -/
private lemma symA_bound_self {ℓ β : ℝ} (hℓ : 0 < ℓ) (hβ : 0 ≤ β) {F : ℝ → ℝ}
    (hF : ∀ r : ℝ, |F r| ≤ β * (1 + r ^ 2))
    (hint0 : Integrable (fun p : ℝ³ => profHat p ^ 2))
    (hint2 : Integrable (fun p : ℝ³ => ‖p‖ ^ 2 * profHat p ^ 2)) (q : ℝ³) :
    |symA ℓ F q|
      ≤ (2 * ((2 * Real.pi) ^ 3)⁻¹ * β * (∫ p : ℝ³, profHat p ^ 2)) * ‖q‖ ^ 2
        + ((2 * Real.pi) ^ 3)⁻¹ * β * ((∫ p : ℝ³, profHat p ^ 2)
          + 2 * ℓ⁻¹ ^ 2 * (∫ p : ℝ³, ‖p‖ ^ 2 * profHat p ^ 2)) := by
  have hc0 : (0:ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  have hI0 : (0:ℝ) ≤ ∫ p : ℝ³, profHat p ^ 2 := integral_nonneg (fun p => sq_nonneg _)
  have hI2 : (0:ℝ) ≤ ∫ p : ℝ³, ‖p‖ ^ 2 * profHat p ^ 2 :=
    integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hgint : Integrable
      (fun p : ℝ³ => β * (1 + 2 * ‖q‖ ^ 2 + 2 * ℓ⁻¹ ^ 2 * ‖p‖ ^ 2) * profHat p ^ 2) := by
    have h1 : Integrable (fun p : ℝ³ => (β * (1 + 2 * ‖q‖ ^ 2)) * profHat p ^ 2) :=
      hint0.const_mul _
    have h2 : Integrable (fun p : ℝ³ => (β * 2 * ℓ⁻¹ ^ 2) * (‖p‖ ^ 2 * profHat p ^ 2)) :=
      hint2.const_mul _
    refine (h1.add h2).congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Pi.add_apply]
    ring
  have hpt : ∀ p : ℝ³, ‖F ‖q + ℓ⁻¹ • p‖ * profHat p ^ 2‖
      ≤ β * (1 + 2 * ‖q‖ ^ 2 + 2 * ℓ⁻¹ ^ 2 * ‖p‖ ^ 2) * profHat p ^ 2 := by
    intro p
    rw [Real.norm_eq_abs]
    have hnorm : ‖q + ℓ⁻¹ • p‖ ^ 2 ≤ 2 * ‖q‖ ^ 2 + 2 * ℓ⁻¹ ^ 2 * ‖p‖ ^ 2 := by
      have h1 : ‖q + ℓ⁻¹ • p‖ ≤ ‖q‖ + ℓ⁻¹ * ‖p‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ℓ⁻¹)]
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖q‖ - ℓ⁻¹ * ‖p‖), norm_nonneg q, norm_nonneg p]
    rw [abs_mul, abs_of_nonneg (sq_nonneg (profHat p))]
    have h1 : |F ‖q + ℓ⁻¹ • p‖| ≤ β * (1 + ‖q + ℓ⁻¹ • p‖ ^ 2) := hF _
    have h2 : (1 + ‖q + ℓ⁻¹ • p‖ ^ 2) ≤ 1 + 2 * ‖q‖ ^ 2 + 2 * ℓ⁻¹ ^ 2 * ‖p‖ ^ 2 := by linarith
    calc |F ‖q + ℓ⁻¹ • p‖| * profHat p ^ 2
        ≤ (β * (1 + ‖q + ℓ⁻¹ • p‖ ^ 2)) * profHat p ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ ≤ (β * (1 + 2 * ‖q‖ ^ 2 + 2 * ℓ⁻¹ ^ 2 * ‖p‖ ^ 2)) * profHat p ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hβ) (sq_nonneg _)
  have hmain : |symA ℓ F q|
      ≤ ((2 * Real.pi) ^ 3)⁻¹
          * ∫ p : ℝ³, β * (1 + 2 * ‖q‖ ^ 2 + 2 * ℓ⁻¹ ^ 2 * ‖p‖ ^ 2) * profHat p ^ 2 := by
    rw [symA, abs_mul, abs_of_nonneg hc0]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    exact norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hpt)
  have hsplit : (∫ p : ℝ³, β * (1 + 2 * ‖q‖ ^ 2 + 2 * ℓ⁻¹ ^ 2 * ‖p‖ ^ 2) * profHat p ^ 2)
      = β * (1 + 2 * ‖q‖ ^ 2) * (∫ p : ℝ³, profHat p ^ 2)
        + β * 2 * ℓ⁻¹ ^ 2 * (∫ p : ℝ³, ‖p‖ ^ 2 * profHat p ^ 2) := by
    have hcongr : (fun p : ℝ³ => β * (1 + 2 * ‖q‖ ^ 2 + 2 * ℓ⁻¹ ^ 2 * ‖p‖ ^ 2) * profHat p ^ 2)
        = fun p : ℝ³ => (β * (1 + 2 * ‖q‖ ^ 2)) * profHat p ^ 2
            + (β * 2 * ℓ⁻¹ ^ 2) * (‖p‖ ^ 2 * profHat p ^ 2) := by
      funext p; ring
    rw [hcongr, integral_add (hint0.const_mul _) (hint2.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hsplit] at hmain
  calc |symA ℓ F q|
      ≤ ((2 * Real.pi) ^ 3)⁻¹
          * (β * (1 + 2 * ‖q‖ ^ 2) * (∫ p : ℝ³, profHat p ^ 2)
            + β * 2 * ℓ⁻¹ ^ 2 * (∫ p : ℝ³, ‖p‖ ^ 2 * profHat p ^ 2)) := hmain
    _ = (2 * ((2 * Real.pi) ^ 3)⁻¹ * β * (∫ p : ℝ³, profHat p ^ 2)) * ‖q‖ ^ 2
        + ((2 * Real.pi) ^ 3)⁻¹ * β * ((∫ p : ℝ³, profHat p ^ 2)
          + 2 * ℓ⁻¹ ^ 2 * (∫ p : ℝ³, ‖p‖ ^ 2 * profHat p ^ 2)) := by ring

/-- **Uniform bound on `symD`** with an explicit constant, for a radial symbol `F` bounded by
`β (1+r²)`: replacing the second profile factor by `max C 1` gives a constant independent of `q`
(and of the symbol). -/
private lemma symD_bound_self {ℓ β C : ℝ} (hℓ : 0 < ℓ) (hβ : 0 ≤ β) (hC : 0 ≤ C) {F : ℝ → ℝ}
    (hF : ∀ r : ℝ, |F r| ≤ β * (1 + r ^ 2))
    (hprof : ∀ p : ℝ³, |profHat p| ≤ max C 1)
    (hint : Integrable (fun p : ℝ³ => (1 + ‖p‖ ^ 2) * |profHat (ℓ • p)|)) (q : ℝ³) :
    |symD ℓ F q| ≤ β * (max C 1) * (∫ p : ℝ³, (1 + ‖p‖ ^ 2) * |profHat (ℓ • p)|) := by
  have hM0 : (0:ℝ) ≤ max C 1 := le_trans hC (le_max_left _ _)
  have hgint : Integrable
      (fun p : ℝ³ => β * (max C 1) * ((1 + ‖p‖ ^ 2) * |profHat (ℓ • p)|)) := hint.const_mul _
  have hpt : ∀ p : ℝ³, ‖F ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q - p))‖
      ≤ β * (max C 1) * ((1 + ‖p‖ ^ 2) * |profHat (ℓ • p)|) := by
    intro p
    rw [Real.norm_eq_abs]
    have h1 : |F ‖p‖| ≤ β * (1 + ‖p‖ ^ 2) := hF _
    have h2 : |profHat (ℓ • (q - p))| ≤ max C 1 := hprof _
    calc |F ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q - p))|
        = |F ‖p‖| * |profHat (ℓ • p)| * |profHat (ℓ • (q - p))| := by rw [abs_mul, abs_mul]
      _ ≤ (β * (1 + ‖p‖ ^ 2)) * |profHat (ℓ • p)| * (max C 1) :=
          mul_le_mul (mul_le_mul h1 (le_refl _) (abs_nonneg _) (by positivity)) h2
            (abs_nonneg _) (by positivity)
      _ = β * (max C 1) * ((1 + ‖p‖ ^ 2) * |profHat (ℓ • p)|) := by ring
  calc |symD ℓ F q|
      = ‖∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q - p))‖ := by
        rw [symD, Real.norm_eq_abs]
    _ ≤ ∫ p : ℝ³, β * (max C 1) * ((1 + ‖p‖ ^ 2) * |profHat (ℓ • p)|) :=
        norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hpt)
    _ = β * (max C 1) * (∫ p : ℝ³, (1 + ‖p‖ ^ 2) * |profHat (ℓ • p)|) := by
        rw [integral_const_mul]

/-! ## 3. The main theorem -/

theorem famSym_Ftrunc_bound {ℓ c C : ℝ} (hℓ : 0 < ℓ) (hC : 0 ≤ C)
    (hd : ∀ p : EuclideanSpace ℝ (Fin 3), |Work.OneBodyKin.profHat p| ≤ C / (1 + ‖p‖) ^ 6) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (n : ℕ) (q : EuclideanSpace ℝ (Fin 3)),
      |Work.OneBodyKin.famSym ℓ (Work.OneBodyKin.Ftrunc c n) q| ≤ A * ‖q‖ ^ 2 + B := by
  have hβ0 : (0:ℝ) ≤ 2 * (1 + c ^ 2) := by positivity
  have hint0 : Integrable (fun p : ℝ³ => profHat p ^ 2) := integrable_profHat_sq hC hd
  have hint2 : Integrable (fun p : ℝ³ => ‖p‖ ^ 2 * profHat p ^ 2) :=
    integrable_profHat_sq_normSq hC hd
  have hintD : Integrable (fun p : ℝ³ => (1 + ‖p‖ ^ 2) * |profHat (ℓ • p)|) :=
    integrable_profHat_abs_scale hℓ hC hd
  have hprofsup : ∀ p : ℝ³, |profHat p| ≤ max C 1 := fun p =>
    (profHat_abs_le_const hC hd p).trans (le_max_left _ _)
  have hI0 : (0:ℝ) ≤ ∫ p : ℝ³, profHat p ^ 2 := integral_nonneg (fun p => sq_nonneg _)
  have hI2 : (0:ℝ) ≤ ∫ p : ℝ³, ‖p‖ ^ 2 * profHat p ^ 2 :=
    integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hID : (0:ℝ) ≤ ∫ p : ℝ³, (1 + ‖p‖ ^ 2) * |profHat (ℓ • p)| :=
    integral_nonneg (fun p => mul_nonneg (by positivity) (abs_nonneg _))
  have hπ0 : (0:ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  set A : ℝ := 2 * ((2 * Real.pi) ^ 3)⁻¹ * (2 * (1 + c ^ 2)) * (∫ p : ℝ³, profHat p ^ 2)
    with hA
  set B : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * (2 * (1 + c ^ 2))
    * ((∫ p : ℝ³, profHat p ^ 2) + 2 * ℓ⁻¹ ^ 2 * (∫ p : ℝ³, ‖p‖ ^ 2 * profHat p ^ 2))
    with hB
  set D : ℝ := (2 * (1 + c ^ 2)) * (max C 1) * (∫ p : ℝ³, (1 + ‖p‖ ^ 2) * |profHat (ℓ • p)|)
    with hD
  have hA0 : (0:ℝ) ≤ A := by
    rw [hA]; exact mul_nonneg (mul_nonneg (by positivity) hβ0) hI0
  have hB0 : (0:ℝ) ≤ B := by
    rw [hB]
    exact mul_nonneg (mul_nonneg hπ0 hβ0)
      (add_nonneg hI0 (mul_nonneg (by positivity) hI2))
  have hD0 : (0:ℝ) ≤ D := by
    rw [hD]
    exact mul_nonneg (mul_nonneg hβ0 (le_trans hC (le_max_left _ _))) hID
  have hBtot0 : (0:ℝ) ≤ 2 * B + 2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 * D :=
    add_nonneg (by linarith) (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hD0)
  refine ⟨A, 2 * B + 2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 * D, hA0, hBtot0, fun n q => ?_⟩
  have hsymA : |symA ℓ (Ftrunc c n) q| ≤ A * ‖q‖ ^ 2 + B := by
    rw [hA, hB]
    exact symA_bound_self hℓ hβ0 (Ftrunc_abs_le c n) hint0 hint2 q
  have hsymD : |symD ℓ (Ftrunc c n) q| ≤ D := by
    rw [hD]
    exact symD_bound_self hℓ hβ0 hC (Ftrunc_abs_le c n) hprofsup hintD q
  have hsymC : |symC ℓ (Ftrunc c n) q| ≤ B := by
    rw [hB]
    have h0 : |symA ℓ (Ftrunc c n) 0|
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * (2 * (1 + c ^ 2))
          * ((∫ p : ℝ³, profHat p ^ 2) + 2 * ℓ⁻¹ ^ 2 * (∫ p : ℝ³, ‖p‖ ^ 2 * profHat p ^ 2)) := by
      have h := symA_bound_self (F := Ftrunc c n) hℓ hβ0 (Ftrunc_abs_le c n) hint0 hint2 0
      simpa using h
    have hbox : |boxHat ℓ q| ≤ ℓ ^ 3 := abs_boxHat_le hℓ.le q
    have hb6 : |boxHat ℓ q| ^ 2 ≤ ℓ ^ 6 := by
      calc |boxHat ℓ q| ^ 2 ≤ (ℓ ^ 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hbox 2
        _ = ℓ ^ 6 := by ring
    have hinv : (0:ℝ) ≤ (ℓ ^ 6)⁻¹ := by positivity
    calc |symC ℓ (Ftrunc c n) q|
        = |symA ℓ (Ftrunc c n) 0| * (ℓ ^ 6)⁻¹ * |boxHat ℓ q| ^ 2 := by
          rw [symC, abs_mul, abs_mul, abs_of_nonneg hinv, abs_pow]
      _ ≤ (((2 * Real.pi) ^ 3)⁻¹ * (2 * (1 + c ^ 2))
            * ((∫ p : ℝ³, profHat p ^ 2) + 2 * ℓ⁻¹ ^ 2 * (∫ p : ℝ³, ‖p‖ ^ 2 * profHat p ^ 2)))
            * (ℓ ^ 6)⁻¹ * ℓ ^ 6 := by
          refine mul_le_mul (mul_le_mul h0 (le_refl _) hinv (by
            positivity)) hb6 (by positivity) (by positivity)
      _ = ((2 * Real.pi) ^ 3)⁻¹ * (2 * (1 + c ^ 2))
            * ((∫ p : ℝ³, profHat p ^ 2) + 2 * ℓ⁻¹ ^ 2 * (∫ p : ℝ³, ‖p‖ ^ 2 * profHat p ^ 2)) := by
          rw [mul_assoc, inv_mul_cancel₀ (by positivity : (ℓ:ℝ) ^ 6 ≠ 0), mul_one]
  have htri : |famSym ℓ (Ftrunc c n) q|
      ≤ |symA ℓ (Ftrunc c n) q|
        + 2 * ((2 * Real.pi) ^ 3)⁻¹ * |boxHat ℓ q| * |symD ℓ (Ftrunc c n) q|
        + |symC ℓ (Ftrunc c n) q| := by
    have habs : |symA ℓ (Ftrunc c n) q
          - 2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat ℓ q * symD ℓ (Ftrunc c n) q|
        ≤ |symA ℓ (Ftrunc c n) q|
          + |2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat ℓ q * symD ℓ (Ftrunc c n) q| := abs_sub _ _
    have heq : |2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat ℓ q * symD ℓ (Ftrunc c n) q|
        = 2 * ((2 * Real.pi) ^ 3)⁻¹ * |boxHat ℓ q| * |symD ℓ (Ftrunc c n) q| := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hπ0]
    rw [famSym]
    calc |symA ℓ (Ftrunc c n) q - 2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat ℓ q * symD ℓ (Ftrunc c n) q
            + symC ℓ (Ftrunc c n) q|
        ≤ |symA ℓ (Ftrunc c n) q - 2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat ℓ q * symD ℓ (Ftrunc c n) q|
            + |symC ℓ (Ftrunc c n) q| := abs_add_le _ _
      _ ≤ (|symA ℓ (Ftrunc c n) q|
            + |2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat ℓ q * symD ℓ (Ftrunc c n) q|)
            + |symC ℓ (Ftrunc c n) q| := by linarith [habs]
      _ = |symA ℓ (Ftrunc c n) q|
            + 2 * ((2 * Real.pi) ^ 3)⁻¹ * |boxHat ℓ q| * |symD ℓ (Ftrunc c n) q|
            + |symC ℓ (Ftrunc c n) q| := by rw [heq]
  refine htri.trans ?_
  have hbox : |boxHat ℓ q| ≤ ℓ ^ 3 := abs_boxHat_le hℓ.le q
  have h2 : 2 * ((2 * Real.pi) ^ 3)⁻¹ * |boxHat ℓ q| * |symD ℓ (Ftrunc c n) q|
      ≤ 2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 * D :=
    mul_le_mul (mul_le_mul_of_nonneg_left hbox (by positivity)) hsymD (abs_nonneg _)
      (by positivity)
  linarith [hsymA, hsymC, h2]

end Work.OneBodyKin
