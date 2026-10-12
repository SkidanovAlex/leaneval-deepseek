import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.TruncDefs
import Submission.Work.OneBodyKin.integrable_chiMul_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.famSym_Ftrunc_tendsto` — the truncated symbols converge pointwise

The symbol `famSym ℓ F q` of the projected moving-box family form (`Defs.lean`) is a sum of three
explicit `p`-integrals,

    `famSym ℓ F q = symA ℓ F q − 2(2π)⁻³ boxHat ℓ q · symD ℓ F q + symC ℓ F q`,

each of which is *linear in the radial symbol* `F`.  The FS cut-off `fsKinCoeff c = [· − c]₊²`
is the increasing pointwise limit of the truncated symbols `Ftrunc c n` (`TruncDefs.lean`), and
the present lemma is the analytic step that lets one pass to the limit in the symbol-integral
identity `bsFamilyForm_eq_symbolIntegral` (see `SymbolIntegral_fsKinCoeff`):

    `symA ℓ (Ftrunc c n) q → symA ℓ (fsKinCoeff c) q`,  and likewise for `symD`, `symC`.

## The domination

The only input beyond the definitions is the polynomial decay of the bump profile,

    `|profHat p| ≤ C / (1 + ‖p‖)^6`      (`hd`),

together with `ℓ > 0`.  For `symA` the integrand is
`Ftrunc c n ‖q + ℓ⁻¹•p‖ · profHat(p)²`, so (all three factors being nonnegative)

    `Ftrunc c n ‖q + ℓ⁻¹•p‖ profHat(p)² ≤ (1+|c|)²(1+‖q+ℓ⁻¹•p‖)² · C²(1+‖p‖)^{-12}`,

and `1 + ‖q + ℓ⁻¹•p‖ ≤ (1+‖q‖)·max 1 ℓ⁻¹ · (1+‖p‖)` (`onePlusNorm_add_le`,
`onePlusNorm_smul_le`) turns this into

    `≤ K · (1 + ‖p‖)^{-10}`,     `K = (1+|c|)² ((1+‖q‖) max 1 ℓ⁻¹)² C²`,

whose integral is finite in dimension `3` (`integrable_inv_onePlusNorm_pow` with
`k = 10 > 3`).  The same computation for `symD`, using in addition the matching *lower* bound
`min 1 ℓ · (1+‖p‖) ≤ 1 + ℓ‖p‖` and `1 + ‖p‖ ≤ (1+‖q‖)(1+‖q−p‖)` to merge the two profile decays
into one decay in the *unshifted* variable, again lands exactly on the exponent `-10`.

Everything is then Lebesgue dominated convergence
(`MeasureTheory.tendsto_integral_of_dominated_convergence`) with the pointwise limit
`Ftrunc c n r → fsKinCoeff c r` (`TruncDefs.Ftrunc_tendsto`).
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

/-! ## Integrability of the polynomial weight -/

/-- **The polynomial weight `(1 + ‖p‖)^{-k}` is Lebesgue-integrable on `ℝ³` for `k > 3`.**
This is the Japanese-bracket integrability `integrable_one_add_norm` in dimension `3`
(`finrank ℝ ℝ³ = 3`), rewritten from the real power `(1 + ‖p‖)^{-k}` to the reciprocal power
`((1 + ‖p‖)^k)⁻¹`. -/
theorem integrable_inv_onePlusNorm_pow {k : ℕ} (hk : 3 < k) :
    MeasureTheory.Integrable (fun p : ℝ³ => ((1 + ‖p‖) ^ k)⁻¹) := by
  have hk' : ((Module.finrank ℝ ℝ³ : ℝ)) < (k : ℝ) := by
    have h3 : Module.finrank ℝ ℝ³ = 3 := by simp
    rw [h3]; exact_mod_cast hk
  refine (integrable_one_add_norm (μ := (volume : Measure ℝ³)) hk').congr ?_
  filter_upwards with p
  rw [Real.rpow_neg (by positivity) (k : ℝ), Real.rpow_natCast]

/-! ## A polynomial bound for the cut-off symbol -/

/-- **The FS cut-off coefficient grows at most quadratically**:
`[r − c]₊² ≤ (1 + |c|)² (1 + r)²` for `r ≥ 0`.  Indeed
`(r − c)₊ ≤ r + |c| ≤ (1 + |c|)(1 + r)` for `r ≥ 0`. -/
lemma fsKinCoeff_le_mul_sq (c r : ℝ) (hr : 0 ≤ r) :
    fsKinCoeff c r ≤ (1 + |c|) ^ 2 * (1 + r) ^ 2 := by
  have h1 : max (r - c) 0 ≤ r + |c| := by
    rcases le_total r c with h | h
    · rw [max_eq_right (by linarith)]; positivity
    · rw [max_eq_left (by linarith)]; linarith [neg_le_abs c]
  have h2 : r + |c| ≤ (1 + |c|) * (1 + r) := by
    nlinarith [abs_nonneg c, hr]
  have h3 : fsKinCoeff c r ≤ (r + |c|) ^ 2 := by
    rw [fsKinCoeff]
    exact pow_le_pow_left₀ (le_max_right _ _) h1 2
  have h4 : (r + |c|) ^ 2 ≤ ((1 + |c|) * (1 + r)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  calc fsKinCoeff c r ≤ (r + |c|) ^ 2 := h3
    _ ≤ ((1 + |c|) * (1 + r)) ^ 2 := h4
    _ = (1 + |c|) ^ 2 * (1 + r) ^ 2 := by ring

/-! ## Triangle-inequality estimates -/

/-- `1 + ‖a + b‖ ≤ (1 + ‖a‖)(1 + ‖b‖)`. -/
lemma onePlusNorm_add_le (a b : ℝ³) : 1 + ‖a + b‖ ≤ (1 + ‖a‖) * (1 + ‖b‖) := by
  have h : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  nlinarith [norm_nonneg a, norm_nonneg b]

/-- `1 + ‖t • p‖ ≤ max 1 |t| · (1 + ‖p‖)`. -/
lemma onePlusNorm_smul_le (t : ℝ) (p : ℝ³) :
    1 + ‖t • p‖ ≤ max 1 |t| * (1 + ‖p‖) := by
  rw [norm_smul, Real.norm_eq_abs]
  rcases le_total |t| 1 with h | h
  · have hm : max 1 |t| = 1 := max_eq_left h
    rw [hm, one_mul]
    nlinarith [norm_nonneg p, abs_nonneg t]
  · have hm : max 1 |t| = |t| := max_eq_right h
    rw [hm]
    nlinarith [norm_nonneg p, abs_nonneg t]

/-- `1 + ‖p‖ ≤ (1 + ‖q‖)(1 + ‖q − p‖)`: the momentum `p` cannot be much larger than the shift `q`
without being far from `q`, which is what makes the two decays of `symD` combine into one decay
in the *unshifted* variable. -/
lemma onePlusNorm_le_onePlus_mul_sub (q p : ℝ³) :
    1 + ‖p‖ ≤ (1 + ‖q‖) * (1 + ‖q - p‖) := by
  have h : ‖p‖ ≤ ‖q‖ + ‖q - p‖ := by
    have h1 : p = q + (p - q) := by abel
    calc ‖p‖ = ‖q + (p - q)‖ := by rw [← h1]
      _ ≤ ‖q‖ + ‖p - q‖ := norm_add_le q (p - q)
      _ = ‖q‖ + ‖q - p‖ := by rw [norm_sub_rev]
  nlinarith [norm_nonneg q, norm_nonneg (q - p)]

/-- **The matching lower bound for the rescaled momentum**: for `ℓ > 0`,
`min 1 ℓ · (1 + ‖p‖) ≤ 1 + ℓ‖p‖`.  Hence the decay `(1 + ℓ‖p‖)^{-6}` of `profHat (ℓ • p)` is a
decay in `p` with the constant `min 1 ℓ`. -/
lemma min_mul_onePlusNorm_le_smul {ℓ : ℝ} (_hℓ : 0 < ℓ) (p : ℝ³) :
    min 1 ℓ * (1 + ‖p‖) ≤ 1 + ℓ * ‖p‖ := by
  have hp : 0 ≤ ‖p‖ := norm_nonneg p
  rcases le_total ℓ 1 with h | h
  · have hm : min 1 ℓ = ℓ := min_eq_right h
    rw [hm]; nlinarith
  · have hm : min 1 ℓ = 1 := min_eq_left h
    rw [hm, one_mul]; nlinarith

/-! ## 1. Pointwise domination of the three symbol integrands -/

/-- **Domination of the `symA` integrand.**  With `hd` the profile decay and `ℓ > 0`, the
integrand of `symA ℓ (Ftrunc c n) q` is bounded, *uniformly in `n`*, by the integrable weight
`((1+|c|)²((1+‖q‖) max 1 ℓ⁻¹)²C²)·(1+‖p‖)^{-10}`. -/
private lemma symA_integrand_bound {ℓ c C : ℝ} (hℓ : 0 < ℓ) (hC : 0 ≤ C)
    (hd : ∀ p : ℝ³, |profHat p| ≤ C / (1 + ‖p‖) ^ 6) (q : ℝ³) :
    ∀ (n : ℕ) (p : ℝ³),
      ‖Ftrunc c n ‖q + ℓ⁻¹ • p‖ * profHat p ^ 2‖
        ≤ ((1 + |c|) ^ 2 * ((1 + ‖q‖) * max 1 ℓ⁻¹) ^ 2 * C ^ 2) * ((1 + ‖p‖) ^ 10)⁻¹ := by
  intro n p
  have hx : (0 : ℝ) < 1 + ‖p‖ := by positivity
  have hQ : (0 : ℝ) ≤ 1 + ‖q‖ := by positivity
  have hshift : 1 + ‖q + ℓ⁻¹ • p‖ ≤ ((1 + ‖q‖) * max 1 ℓ⁻¹) * (1 + ‖p‖) := by
    have h1 := onePlusNorm_add_le q (ℓ⁻¹ • p)
    have h2 := onePlusNorm_smul_le ℓ⁻¹ p
    have h3 : |ℓ⁻¹| = ℓ⁻¹ := abs_of_pos (inv_pos.mpr hℓ)
    calc 1 + ‖q + ℓ⁻¹ • p‖ ≤ (1 + ‖q‖) * (1 + ‖ℓ⁻¹ • p‖) := h1
      _ ≤ (1 + ‖q‖) * (max 1 |ℓ⁻¹| * (1 + ‖p‖)) := mul_le_mul_of_nonneg_left h2 hQ
      _ = ((1 + ‖q‖) * max 1 ℓ⁻¹) * (1 + ‖p‖) := by rw [h3]; ring
  have hprof : profHat p ^ 2 ≤ (C / (1 + ‖p‖) ^ 6) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hd p) 2
  have hf0 : 0 ≤ Ftrunc c n ‖q + ℓ⁻¹ • p‖ * profHat p ^ 2 :=
    mul_nonneg (Ftrunc_nonneg c n _) (sq_nonneg _)
  have hC2 : (1 + ‖p‖) ^ 2 * (C / (1 + ‖p‖) ^ 6) ^ 2 = C ^ 2 * ((1 + ‖p‖) ^ 10)⁻¹ := by
    field_simp
  rw [Real.norm_of_nonneg hf0]
  calc Ftrunc c n ‖q + ℓ⁻¹ • p‖ * profHat p ^ 2
      ≤ fsKinCoeff c ‖q + ℓ⁻¹ • p‖ * profHat p ^ 2 :=
        mul_le_mul_of_nonneg_right (Ftrunc_le_fsKinCoeff c n _) (sq_nonneg _)
    _ ≤ ((1 + |c|) ^ 2 * (1 + ‖q + ℓ⁻¹ • p‖) ^ 2) * profHat p ^ 2 :=
        mul_le_mul_of_nonneg_right (fsKinCoeff_le_mul_sq c _ (norm_nonneg _)) (sq_nonneg _)
    _ ≤ ((1 + |c|) ^ 2 * (((1 + ‖q‖) * max 1 ℓ⁻¹) * (1 + ‖p‖)) ^ 2)
          * (C / (1 + ‖p‖) ^ 6) ^ 2 := by
        refine mul_le_mul ?_ hprof (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hshift 2) (sq_nonneg _)
    _ = ((1 + |c|) ^ 2 * ((1 + ‖q‖) * max 1 ℓ⁻¹) ^ 2 * C ^ 2) * ((1 + ‖p‖) ^ 10)⁻¹ := by
        field_simp

/-- **Decay of the rescaled profile along `p ↦ ℓ • p`**: with `ℓ > 0` the decay of `profHat` at
`ℓ • p` is a decay in `p`, with the constant `(min 1 ℓ)^{-6}` coming from
`min_mul_onePlusNorm_le_smul`. -/
private lemma profHat_smul_bound {ℓ C : ℝ} (hℓ : 0 < ℓ) (hC : 0 ≤ C)
    (hd : ∀ p : ℝ³, |profHat p| ≤ C / (1 + ‖p‖) ^ 6) (p : ℝ³) :
    |profHat (ℓ • p)| ≤ C * ((min 1 ℓ) ^ 6)⁻¹ * ((1 + ‖p‖) ^ 6)⁻¹ := by
  have hm : (0 : ℝ) < min 1 ℓ := lt_min one_pos hℓ
  have hx : (0 : ℝ) < 1 + ‖p‖ := by positivity
  have hnorm : ‖ℓ • p‖ = ℓ * ‖p‖ := by rw [norm_smul, Real.norm_of_nonneg hℓ.le]
  have h1 : |profHat (ℓ • p)| ≤ C / (1 + ℓ * ‖p‖) ^ 6 := by
    have h := hd (ℓ • p)
    rwa [hnorm] at h
  have h2 : min 1 ℓ * (1 + ‖p‖) ≤ 1 + ℓ * ‖p‖ := min_mul_onePlusNorm_le_smul hℓ p
  have h4 : C / (1 + ℓ * ‖p‖) ^ 6 ≤ C / (min 1 ℓ * (1 + ‖p‖)) ^ 6 :=
    div_le_div_of_nonneg_left hC (pow_pos (mul_pos hm hx) 6)
      (pow_le_pow_left₀ (le_of_lt (mul_pos hm hx)) h2 6)
  have h5 : C / (min 1 ℓ * (1 + ‖p‖)) ^ 6
      = C * ((min 1 ℓ) ^ 6)⁻¹ * ((1 + ‖p‖) ^ 6)⁻¹ := by
    rw [mul_pow, div_eq_mul_inv, mul_inv]
    ring
  calc |profHat (ℓ • p)| ≤ C / (1 + ℓ * ‖p‖) ^ 6 := h1
    _ ≤ C / (min 1 ℓ * (1 + ‖p‖)) ^ 6 := h4
    _ = C * ((min 1 ℓ) ^ 6)⁻¹ * ((1 + ‖p‖) ^ 6)⁻¹ := h5

/-- **Merging the two profile decays of `symD`**: since `1 + ‖p‖ ≤ (1+‖q‖)(1+‖q−p‖)`
(`onePlusNorm_le_onePlus_mul_sub`), the decay in `q − p` is dominated by the decay in
`p` at the cost of the factor `(1+‖q‖)^6`. -/
private lemma inv_pow_six_le (q p : ℝ³) :
    ((1 + ‖q - p‖) ^ 6)⁻¹ ≤ (1 + ‖q‖) ^ 6 * ((1 + ‖p‖) ^ 6)⁻¹ := by
  have hle : 1 + ‖p‖ ≤ (1 + ‖q‖) * (1 + ‖q - p‖) := onePlusNorm_le_onePlus_mul_sub q p
  have h6 : (1 + ‖p‖) ^ 6 ≤ (1 + ‖q‖) ^ 6 * (1 + ‖q - p‖) ^ 6 := by
    calc (1 + ‖p‖) ^ 6 ≤ ((1 + ‖q‖) * (1 + ‖q - p‖)) ^ 6 :=
          pow_le_pow_left₀ (by positivity) hle 6
      _ = (1 + ‖q‖) ^ 6 * (1 + ‖q - p‖) ^ 6 := mul_pow _ _ 6
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖p‖) ^ 6),
    inv_mul_eq_div, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + ‖q - p‖) ^ 6)]
  exact h6

/-- **Domination of the `symD` integrand.**  All three factors are estimated separately – the
symbol factor by `(1+|c|)²(1+‖p‖)²`, the two profile factors by the rescaled decays – and the
product of the `x`-powers is exactly the integrable weight `(1+‖p‖)^{-10}`
(because `min 1 ℓ`-rescaling contributes `(1+‖p‖)^{-6}` twice and the shift contributes a
quadratic growth). -/
private lemma symD_integrand_bound {ℓ c C : ℝ} (hℓ : 0 < ℓ) (hC : 0 ≤ C)
    (hd : ∀ p : ℝ³, |profHat p| ≤ C / (1 + ‖p‖) ^ 6) (q : ℝ³) :
    ∀ (n : ℕ) (p : ℝ³),
      ‖Ftrunc c n ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q - p))‖
        ≤ ((1 + |c|) ^ 2 * C ^ 2 * ((min 1 ℓ) ^ 6)⁻¹ * ((min 1 ℓ) ^ 6)⁻¹ * (1 + ‖q‖) ^ 6)
            * ((1 + ‖p‖) ^ 10)⁻¹ := by
  intro n p
  have hm : (0 : ℝ) < min 1 ℓ := lt_min one_pos hℓ
  have hx : (0 : ℝ) < 1 + ‖p‖ := by positivity
  have hm6 : (0 : ℝ) ≤ ((min 1 ℓ) ^ 6)⁻¹ := inv_nonneg.mpr (pow_nonneg (le_of_lt hm) 6)
  have hx6 : (0 : ℝ) ≤ ((1 + ‖p‖) ^ 6)⁻¹ := inv_nonneg.mpr (pow_nonneg (le_of_lt hx) 6)
  have hy6 : (0 : ℝ) ≤ ((1 + ‖q - p‖) ^ 6)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖q - p‖) 6)
  have hA : (0 : ℝ) ≤ (1 + |c|) ^ 2 * (1 + ‖p‖) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hB : (0 : ℝ) ≤ C * ((min 1 ℓ) ^ 6)⁻¹ * ((1 + ‖p‖) ^ 6)⁻¹ :=
    mul_nonneg (mul_nonneg hC hm6) hx6
  have hD : (0 : ℝ) ≤ C * ((min 1 ℓ) ^ 6)⁻¹ * ((1 + ‖q - p‖) ^ 6)⁻¹ :=
    mul_nonneg (mul_nonneg hC hm6) hy6
  have hCm6 : (0 : ℝ) ≤ C * ((min 1 ℓ) ^ 6)⁻¹ := mul_nonneg hC hm6
  have hF : |Ftrunc c n ‖p‖| ≤ (1 + |c|) ^ 2 * (1 + ‖p‖) ^ 2 := by
    rw [abs_of_nonneg (Ftrunc_nonneg c n ‖p‖)]
    exact (Ftrunc_le_fsKinCoeff c n ‖p‖).trans (fsKinCoeff_le_mul_sq c ‖p‖ (norm_nonneg p))
  have hP1 := profHat_smul_bound hℓ hC hd p
  have hP2 := profHat_smul_bound hℓ hC hd (q - p)
  have hY := inv_pow_six_le q p
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  calc |Ftrunc c n ‖p‖| * |profHat (ℓ • p)| * |profHat (ℓ • (q - p))|
      ≤ ((1 + |c|) ^ 2 * (1 + ‖p‖) ^ 2) * (C * ((min 1 ℓ) ^ 6)⁻¹ * ((1 + ‖p‖) ^ 6)⁻¹)
          * (C * ((min 1 ℓ) ^ 6)⁻¹ * ((1 + ‖q - p‖) ^ 6)⁻¹) := by
        refine mul_le_mul (mul_le_mul hF hP1 (abs_nonneg _) hA) hP2 (abs_nonneg _)
          (mul_nonneg hA hB)
    _ ≤ ((1 + |c|) ^ 2 * (1 + ‖p‖) ^ 2) * (C * ((min 1 ℓ) ^ 6)⁻¹ * ((1 + ‖p‖) ^ 6)⁻¹)
          * (C * ((min 1 ℓ) ^ 6)⁻¹ * ((1 + ‖q‖) ^ 6 * ((1 + ‖p‖) ^ 6)⁻¹)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hA hB)
        exact mul_le_mul_of_nonneg_left hY hCm6
    _ = ((1 + |c|) ^ 2 * C ^ 2 * ((min 1 ℓ) ^ 6)⁻¹ * ((min 1 ℓ) ^ 6)⁻¹ * (1 + ‖q‖) ^ 6)
            * ((1 + ‖p‖) ^ 10)⁻¹ := by
        field_simp

/-! ## 2. Convergence of the three symbol terms -/

/-- **`symA` converges along the truncations.** -/
private lemma tendsto_symA_Ftrunc {ℓ c C : ℝ} (hℓ : 0 < ℓ) (hC : 0 ≤ C)
    (hd : ∀ p : ℝ³, |profHat p| ≤ C / (1 + ‖p‖) ^ 6) (q : ℝ³) :
    Filter.Tendsto (fun n : ℕ => symA ℓ (Ftrunc c n) q) Filter.atTop
      (nhds (symA ℓ (fsKinCoeff c) q)) := by
  have hbound := symA_integrand_bound (c := c) hℓ hC hd q
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ³ => ((1 + |c|) ^ 2 * ((1 + ‖q‖) * max 1 ℓ⁻¹) ^ 2 * C ^ 2)
        * ((1 + ‖p‖) ^ 10)⁻¹) :=
    (integrable_inv_onePlusNorm_pow (k := 10) (by norm_num)).const_mul _
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun p : ℝ³ => Ftrunc c n ‖q + ℓ⁻¹ • p‖ * profHat p ^ 2) volume := by
    intro n
    have hcont : Continuous (fun p : ℝ³ => q + ℓ⁻¹ • p) :=
      continuous_const.add (continuous_id.const_smul ℓ⁻¹)
    have h1 : Measurable (fun p : ℝ³ => Ftrunc c n ‖q + ℓ⁻¹ • p‖) :=
      (measurable_Ftrunc c n).comp (continuous_norm.comp hcont).measurable
    have h2 : Measurable (fun p : ℝ³ => profHat p ^ 2) := (continuous_profHat.pow 2).measurable
    exact (h1.mul h2).aestronglyMeasurable
  have hlim : ∀ᵐ p ∂(volume : Measure ℝ³),
      Filter.Tendsto (fun n : ℕ => Ftrunc c n ‖q + ℓ⁻¹ • p‖ * profHat p ^ 2)
        Filter.atTop (nhds (fsKinCoeff c ‖q + ℓ⁻¹ • p‖ * profHat p ^ 2)) :=
    Filter.Eventually.of_forall fun p =>
      (Ftrunc_tendsto c ‖q + ℓ⁻¹ • p‖).mul_const (profHat p ^ 2)
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
      (F := fun (n : ℕ) (p : ℝ³) => Ftrunc c n ‖q + ℓ⁻¹ • p‖ * profHat p ^ 2)
      (f := fun p : ℝ³ => fsKinCoeff c ‖q + ℓ⁻¹ • p‖ * profHat p ^ 2)
      (fun p : ℝ³ =>
        ((1 + |c|) ^ 2 * ((1 + ‖q‖) * max 1 ℓ⁻¹) ^ 2 * C ^ 2) * ((1 + ‖p‖) ^ 10)⁻¹)
      hmeas hInt (fun n => Filter.Eventually.of_forall (hbound n)) hlim
  have hthis := hmain.const_mul (((2 * Real.pi) ^ 3)⁻¹)
  simpa only [symA] using hthis

/-- **`symD` converges along the truncations.** -/
private lemma tendsto_symD_Ftrunc {ℓ c C : ℝ} (hℓ : 0 < ℓ) (hC : 0 ≤ C)
    (hd : ∀ p : ℝ³, |profHat p| ≤ C / (1 + ‖p‖) ^ 6) (q : ℝ³) :
    Filter.Tendsto (fun n : ℕ => symD ℓ (Ftrunc c n) q) Filter.atTop
      (nhds (symD ℓ (fsKinCoeff c) q)) := by
  have hbound := symD_integrand_bound (c := c) hℓ hC hd q
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ³ => ((1 + |c|) ^ 2 * C ^ 2 * ((min 1 ℓ) ^ 6)⁻¹ * ((min 1 ℓ) ^ 6)⁻¹
        * (1 + ‖q‖) ^ 6) * ((1 + ‖p‖) ^ 10)⁻¹) :=
    (integrable_inv_onePlusNorm_pow (k := 10) (by norm_num)).const_mul _
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun p : ℝ³ => Ftrunc c n ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q - p))) volume := by
    intro n
    have h1 : Measurable (fun p : ℝ³ => Ftrunc c n ‖p‖) :=
      (measurable_Ftrunc c n).comp continuous_norm.measurable
    have h2 : Measurable (fun p : ℝ³ => profHat (ℓ • p)) :=
      continuous_profHat.measurable.comp (continuous_id.const_smul ℓ).measurable
    have h3 : Measurable (fun p : ℝ³ => profHat (ℓ • (q - p))) :=
      continuous_profHat.measurable.comp
        ((continuous_const.sub continuous_id).const_smul ℓ).measurable
    exact ((h1.mul h2).mul h3).aestronglyMeasurable
  have hlim : ∀ᵐ p ∂(volume : Measure ℝ³),
      Filter.Tendsto
        (fun n : ℕ => Ftrunc c n ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q - p)))
        Filter.atTop (nhds (fsKinCoeff c ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q - p)))) :=
    Filter.Eventually.of_forall fun p =>
      ((Ftrunc_tendsto c ‖p‖).mul_const (profHat (ℓ • p))).mul_const (profHat (ℓ • (q - p)))
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
      (F := fun (n : ℕ) (p : ℝ³) => Ftrunc c n ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q - p)))
      (f := fun p : ℝ³ => fsKinCoeff c ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q - p)))
      (fun p : ℝ³ =>
        ((1 + |c|) ^ 2 * C ^ 2 * ((min 1 ℓ) ^ 6)⁻¹ * ((min 1 ℓ) ^ 6)⁻¹ * (1 + ‖q‖) ^ 6)
          * ((1 + ‖p‖) ^ 10)⁻¹)
      hmeas hInt (fun n => Filter.Eventually.of_forall (hbound n)) hlim
  simpa only [symD] using hmain

/-! ## 3. Assembly -/

/-- **The symbol of the truncated FS cut-off converges pointwise to the symbol of the cut-off.**
This is the pointwise (in `q`) convergence used in `SymbolIntegralRhsTendsto` to pass to the limit
in the symbol-integral identity `SymbolIntegral_fsKinCoeff`. -/
theorem famSym_Ftrunc_tendsto {ℓ c C : ℝ} (hℓ : 0 < ℓ) (hC : 0 ≤ C)
    (hd : ∀ p : EuclideanSpace ℝ (Fin 3), |Work.OneBodyKin.profHat p| ≤ C / (1 + ‖p‖) ^ 6)
    (q : EuclideanSpace ℝ (Fin 3)) :
    Filter.Tendsto (fun n : ℕ => Work.OneBodyKin.famSym ℓ (Work.OneBodyKin.Ftrunc c n) q)
      Filter.atTop
      (nhds (Work.OneBodyKin.famSym ℓ (Submission.BoseGases.fsKinCoeff c) q)) := by
  have hA := tendsto_symA_Ftrunc (c := c) hℓ hC hd q
  have hD := tendsto_symD_Ftrunc (c := c) hℓ hC hd q
  have hCc : Filter.Tendsto (fun n : ℕ => symC ℓ (Ftrunc c n) q) Filter.atTop
      (nhds (symC ℓ (fsKinCoeff c) q)) := by
    have h1 := (tendsto_symA_Ftrunc (c := c) (q := (0 : ℝ³)) hℓ hC hd).mul_const ((ℓ ^ 6)⁻¹)
    have h2 := h1.mul_const ((boxHat ℓ q) ^ 2)
    simpa only [symC] using h2
  have hcross : Filter.Tendsto
      (fun n : ℕ => 2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat ℓ q * symD ℓ (Ftrunc c n) q)
      Filter.atTop
      (nhds (2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat ℓ q * symD ℓ (fsKinCoeff c) q)) :=
    hD.const_mul (2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat ℓ q)
  have hmain : Filter.Tendsto
      (fun n : ℕ => symA ℓ (Ftrunc c n) q - 2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat ℓ q
          * symD ℓ (Ftrunc c n) q + symC ℓ (Ftrunc c n) q)
      Filter.atTop
      (nhds (symA ℓ (fsKinCoeff c) q - 2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat ℓ q
          * symD ℓ (fsKinCoeff c) q + symC ℓ (fsKinCoeff c) q)) :=
    (hA.sub hcross).add hCc
  exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => rfl) hmain

end Work.OneBodyKin
