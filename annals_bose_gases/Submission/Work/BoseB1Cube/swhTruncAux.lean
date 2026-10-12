import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.abs_wSmallScaled_div_convScale_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.swhTruncAux` — two elementary facts for the truncation node

The node `Work.BoseB1Cube.swhTruncFacts` (the truncation of the interaction potential `v` at a
level `K`, with the *scattering numerator* `g₀ = v(1−ω₀)` in the error) needs two elementary
facts, kept here so that the node's own file stays readable:

* **`truncTail_exists`** — for an integrable nonnegative (a.e.) function `g` and every `ε > 0`
  there is a level `K ≥ 0` with `∫ (g − K)₊ ≤ ε`.  This is what produces the truncation level:
  the tail `(g₀ − K)₊` of the scattering numerator is the error the node is allowed to make.
  (Proof: monotone/dominated convergence along the sequence `K = n`, with the dominating
  function `|g|`.)

* **`abs_wSmallPair_le_of_supported`** — the pointwise domination of the localised two-body
  kernel by the two small-box cutoffs, with a *general* numerator `f` that vanishes outside
  `ball 0 R` and is bounded by `Bv`:
  `|wSmallPair M ℓ d u f x y| ≤ 2·Bv·(smallConvLower M)⁻¹·χ_B(x)·χ_B(y)`.
  This is the general form of `Work.BoseB1Cube.abs_wSmallPair_v_le` (there `f = v`), and it is
  the estimate that makes the truncated potential `min v K` a *bounded* numerator `Bv = K`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Truncation tail.**  For an integrable function `g` that is nonnegative a.e. and every
`ε > 0` there is a level `K ≥ 0` with `∫ (g − K)₊ ≤ ε`. -/
theorem truncTail_exists {g : E3 → ℝ} (hgint : MeasureTheory.Integrable g)
    (hg : 0 ≤ᵐ[MeasureTheory.volume] g) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ (∫ z : E3, max (g z - K) 0) ≤ ε := by
  have hFmeas : ∀ n : ℕ, AEStronglyMeasurable (fun z : E3 => max (g z - (n : ℝ)) 0)
      (volume : Measure E3) := by
    intro n
    have h1 : AEMeasurable (fun z : E3 => g z - (n : ℝ)) (volume : Measure E3) :=
      hgint.aemeasurable.sub aemeasurable_const
    exact ((h1.max aemeasurable_const)).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ z ∂(volume : Measure E3), ‖max (g z - (n : ℝ)) 0‖ ≤ |g z| := by
    intro n
    filter_upwards [hg] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact le_trans (max_le (by linarith) hz) (le_abs_self _)
  have hlim : ∀ᵐ z ∂(volume : Measure E3),
      Filter.Tendsto (fun n : ℕ => max (g z - (n : ℝ)) 0) Filter.atTop (𝓝 0) := by
    filter_upwards with z
    obtain ⟨N, hN⟩ := exists_nat_ge (g z)
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun n hn => hn⟩] with n hn
    have h0 : g z - (n : ℝ) ≤ 0 := by
      have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact (by rw [max_comm]; exact (max_eq_left h0).symm)
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun n : ℕ => fun z : E3 => max (g z - (n : ℝ)) 0)
    (f := fun _ : E3 => (0 : ℝ)) (fun z : E3 => |g z|) hFmeas hgint.abs hbound hlim
  simp only [MeasureTheory.integral_zero] at hmain
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hmain) ε hε
  refine ⟨(N : ℝ), Nat.cast_nonneg N, ?_⟩
  have h1 := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at h1
  exact le_of_lt (lt_of_le_of_lt (le_abs_self _) h1)

/-- **Pointwise domination of the localised two-body kernel**, general numerator.

If the numerator `f` vanishes outside `ball 0 R` and is bounded by `Bv` in modulus, then on the
dilute regime (`R ≤ ℓd/16`, `R ≤ ℓ·chiR0`) the renormalised kernel is bounded by
`2·Bv/smallConvLower M` and hence

    |wSmallPair M ℓ d u f x y| ≤ 2·Bv·(smallConvLower M)⁻¹·χ_{B(u)}(x)·χ_{B(u)}(y) .

(The two renormalisation denominators are `≥ smallConvLower M` and `≥ 1/2` on the support of
`f`, and both cutoff factors are nonnegative.) -/
theorem abs_wSmallPair_le_of_supported {f : E3 → ℝ} {R Bv : ℝ}
    (hfsupp : ∀ z : E3, R ≤ ‖z‖ → f z = 0) (hfb : ∀ z : E3, |f z| ≤ Bv)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRd : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (u x y : E3) :
    |Submission.BoseGases.wSmallPair M ℓ d u f x y| ≤
      2 * Bv * (Work.SmallBoxSliding.smallConvLower M)⁻¹ *
        (Submission.BoseGases.chiSmallB M ℓ d u x * Submission.BoseGases.chiSmallB M ℓ d u y) := by
  have hmid := Work.BoseFixB1.abs_wSmallScaled_div_convScale_le (M := M) hM hℓ hd hfsupp hfb
    hRd hRχ (x - y)
  have hx0 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hy0 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u y :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u y
  have hBv0 : 0 ≤ Bv := le_trans (abs_nonneg (f 0)) (hfb 0)
  have hscpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hrhs : 0 ≤ 2 * Bv / Work.SmallBoxSliding.smallConvLower M :=
    div_nonneg (by linarith) hscpos.le
  have hstep : Submission.BoseGases.chiSmallB M ℓ d u x *
        |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)
          / Submission.BoseGases.convScale ℓ (x - y)| *
        Submission.BoseGases.chiSmallB M ℓ d u y
      ≤ Submission.BoseGases.chiSmallB M ℓ d u x *
        (2 * Bv / Work.SmallBoxSliding.smallConvLower M) *
        Submission.BoseGases.chiSmallB M ℓ d u y :=
    mul_le_mul (mul_le_mul_of_nonneg_left hmid hx0) le_rfl hy0 (mul_nonneg hx0 hrhs)
  calc |Submission.BoseGases.wSmallPair M ℓ d u f x y|
      = Submission.BoseGases.chiSmallB M ℓ d u x *
          |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)
            / Submission.BoseGases.convScale ℓ (x - y)| *
          Submission.BoseGases.chiSmallB M ℓ d u y := by
        unfold Submission.BoseGases.wSmallPair
        rw [abs_mul, abs_mul, abs_of_nonneg hx0, abs_of_nonneg hy0]
    _ ≤ Submission.BoseGases.chiSmallB M ℓ d u x *
          (2 * Bv / Work.SmallBoxSliding.smallConvLower M) *
          Submission.BoseGases.chiSmallB M ℓ d u y := hstep
    _ = 2 * Bv * (Work.SmallBoxSliding.smallConvLower M)⁻¹ *
          (Submission.BoseGases.chiSmallB M ℓ d u x * Submission.BoseGases.chiSmallB M ℓ d u y) := by
        rw [div_eq_mul_inv]; ring

end Work.BoseB1Cube
