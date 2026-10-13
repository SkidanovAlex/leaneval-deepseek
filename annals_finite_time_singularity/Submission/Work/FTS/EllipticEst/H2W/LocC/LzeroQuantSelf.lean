import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthBound
import Submission.Work.FTS.EllipticEst.H2W.Lzb.LzeroSingCosBoundClean
import Submission.Work.FTS.EllipticEst.H2W.Lzb.WronDerivs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.LocC

set_option autoImplicit false

/-!
# `LocC/LzeroQuantSelf` — the quantitative one-variable `θ`-growth bound for a slice

`lzeroGrowthBound` (`H2W/lzeroGrowthBound.lean`) proves, for `u` of class `C^∞` on `(0, π/2)`
with `∫_{Iθ} sinθcos²θ·|Lzero1 u| < ∞`, that `|u θ| ≤ C·(θ⁻¹ + (π/2-θ)⁻¹)` for *some* constant
`C`, but neither its statement nor its proof exposes the dependence of `C` on `u`.  The
*locally uniform in `z`* slice bound of `H2W/pzIterSliceGrowth3LocC` needs the constant to be
controlled by two explicit quantities of the slice `u` only:

* `K u = ∫_{Iθ} sinθcos²θ·|Lzero1 u|`, the weighted source mass, and
* `|u(π/4)| + |deriv u (π/4)|`, the data at the interior reference angle `π/4`.

`growthExplicit` below is the explicit-constant form of `lzeroGrowthBound`: a verbatim re-run of
its proof with the constant `4|c₁(π/4)| + 16B₀K + 2(|c₂(π/4)|+2K)B₀` exposed and `B₀` a
parameter.  The two Cramer coefficients at `π/4` are *fixed* linear functionals of
`(u(π/4), u'(π/4))` (`cCoef1_pi4_le`, `cCoef2_pi4_le`), so the whole constant is dominated by a
universal multiple of `K u + |u(π/4)| + |deriv u(π/4)|`.  That yields
`lzeroGrowthQuantL1Self`, the quantitative form consumed by the local slice bound.
-/

/-- **The explicit-constant form of `lzeroGrowthBound`.**  Under the two hypotheses of
`lzeroGrowthBound` and with `B0` a bound for `|LzeroSing θ · cos θ|` on the open interval,

  `|u θ| ≤ (4|c₁(π/4)| + 16B₀K + 2(|c₂(π/4)| + 2K)B₀)·(θ⁻¹ + (π/2-θ)⁻¹)`,

`K = ∫_{Iθ} ψ|Lzero1 u|`, `c₁`, `c₂` the Cramer coefficients of `u`. -/
theorem growthExplicit {u : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ)
    {B0 : ℝ} (hB0nn : 0 ≤ B0)
    (hB0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.LzeroSing θ * Real.cos θ| ≤ B0) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ (4 * |Work.FTS.EllipticEst.H2W.cCoef1 u (Real.pi / 4)|
            + 16 * B0 * (∫ s in Work.Spaces.Iθ,
                Work.FTS.EllipticEst.H2W.psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)
            + 2 * (|Work.FTS.EllipticEst.H2W.cCoef2 u (Real.pi / 4)|
              + 2 * (∫ s in Work.Spaces.Iθ,
                  Work.FTS.EllipticEst.H2W.psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)) * B0)
        * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hu 2
  obtain ⟨hwr1, hwr2⟩ := Work.FTS.EllipticEst.H2W.Lzb.WronDerivs hu2
  have hder1 := Work.FTS.EllipticEst.H2W.hasDerivAt_cCoef1 (u := u) hwr1
  have hder2 := Work.FTS.EllipticEst.H2W.hasDerivAt_cCoef2 (u := u) hwr2
  have hψint : IntegrableOn
      (fun s => Work.FTS.EllipticEst.H2W.psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)
      Work.Spaces.Iθ := by
    simpa only [Work.FTS.EllipticEst.H2W.psiW] using hint
  let K : ℝ := ∫ s in Work.Spaces.Iθ,
    Work.FTS.EllipticEst.H2W.psiW s * |Work.FTS.EllipticEst.Lzero1 u s|
  have hKnn : 0 ≤ K := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun s hs => ?_)
    exact mul_nonneg (Work.FTS.EllipticEst.H2W.psiW_nonneg hs) (abs_nonneg _)
  intro θ hθ
  change |u θ| ≤ (4 * |Work.FTS.EllipticEst.H2W.cCoef1 u (Real.pi / 4)|
        + 16 * B0 * K
        + 2 * (|Work.FTS.EllipticEst.H2W.cCoef2 u (Real.pi / 4)| + 2 * K) * B0)
      * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹)
  have hθ0 : (0:ℝ) < θ := hθ.1
  have hθπ : θ < Real.pi / 2 := hθ.2
  have hτ : 0 < Real.pi / 2 - θ := by linarith
  have hinv : 1 ≤ θ⁻¹ + (Real.pi / 2 - θ)⁻¹ := one_le_inv_add hθ
  have hC2nn : 0 ≤ |cCoef2 u (Real.pi / 4)| + 2 * K := by positivity
  have hcramer := cramer_id u hθ
  have hy2 : |Work.FTS.EllipticEst.LzeroSing θ|
      ≤ B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹) := by
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ0, Real.pi_pos], hθπ⟩
    have hb : |Work.FTS.EllipticEst.LzeroSing θ| * Real.cos θ ≤ B0 := by
      have h := hB0 θ hθ
      rwa [abs_mul, abs_of_pos hcos] at h
    calc |Work.FTS.EllipticEst.LzeroSing θ| ≤ B0 / Real.cos θ := (le_div_iff₀ hcos).mpr hb
      _ = B0 * (Real.cos θ)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹) :=
          mul_le_mul_of_nonneg_left (inv_cos_le hθ) hB0nn
  have hc2 : |cCoef2 u θ| ≤ |cCoef2 u (Real.pi / 4)| + 2 * K := by
    have h := abs_cCoef2_sub_le hu2 hder2 hψint hθ
    calc |cCoef2 u θ| = |cCoef2 u (Real.pi / 4) + (cCoef2 u θ - cCoef2 u (Real.pi / 4))| := by
          ring_nf
      _ ≤ |cCoef2 u (Real.pi / 4)| + |cCoef2 u θ - cCoef2 u (Real.pi / 4)| := abs_add_le _ _
      _ ≤ |cCoef2 u (Real.pi / 4)| + 2 * K := by linarith
  rcases le_total θ (Real.pi / 4) with hle | hge
  · -- Case `θ ≤ π/4`
    have hy1 : |Real.sin (2 * θ)| ≤ 2 * θ := by
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith [Real.pi_pos]))]
      exact sin_two_mul_le_two_mul (by linarith)
    have hc1 : |cCoef1 u θ| ≤ |cCoef1 u (Real.pi / 4)| + B0 * ((Real.pi / θ) * K) := by
      have h := abs_cCoef1_sub_le_left hu2 hder1 hψint hB0nn hB0 hθ0 hle
      calc |cCoef1 u θ| = |cCoef1 u (Real.pi / 4) + (cCoef1 u θ - cCoef1 u (Real.pi / 4))| := by
            ring_nf
        _ ≤ |cCoef1 u (Real.pi / 4)| + |cCoef1 u θ - cCoef1 u (Real.pi / 4)| := abs_add_le _ _
        _ ≤ |cCoef1 u (Real.pi / 4)| + B0 * ((Real.pi / θ) * K) := by linarith
    have hsum : |u θ| ≤ (|cCoef1 u (Real.pi / 4)| + B0 * ((Real.pi / θ) * K)) * (2 * θ)
        + (|cCoef2 u (Real.pi / 4)| + 2 * K)
          * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := by
      calc |u θ| = |cCoef1 u θ * Real.sin (2 * θ)
            + cCoef2 u θ * Work.FTS.EllipticEst.LzeroSing θ| := by rw [hcramer]
        _ ≤ |cCoef1 u θ * Real.sin (2 * θ)|
              + |cCoef2 u θ * Work.FTS.EllipticEst.LzeroSing θ| := abs_add_le _ _
        _ = |cCoef1 u θ| * |Real.sin (2 * θ)|
              + |cCoef2 u θ| * |Work.FTS.EllipticEst.LzeroSing θ| := by rw [abs_mul, abs_mul]
        _ ≤ (|cCoef1 u (Real.pi / 4)| + B0 * ((Real.pi / θ) * K)) * (2 * θ)
              + (|cCoef2 u (Real.pi / 4)| + 2 * K)
                * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := by
            have h1 : |cCoef1 u θ| * |Real.sin (2 * θ)|
                ≤ (|cCoef1 u (Real.pi / 4)| + B0 * ((Real.pi / θ) * K)) * (2 * θ) :=
              mul_le_mul hc1 hy1 (abs_nonneg _) (by positivity)
            have h2 : |cCoef2 u θ| * |Work.FTS.EllipticEst.LzeroSing θ|
                ≤ (|cCoef2 u (Real.pi / 4)| + 2 * K)
                  * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) :=
              mul_le_mul hc2 hy2 (abs_nonneg _) (by positivity)
            linarith
    have hEq : (|cCoef1 u (Real.pi / 4)| + B0 * ((Real.pi / θ) * K)) * (2 * θ)
        + (|cCoef2 u (Real.pi / 4)| + 2 * K)
          * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹))
        = 2 * |cCoef1 u (Real.pi / 4)| * θ + 2 * B0 * Real.pi * K
          + (|cCoef2 u (Real.pi / 4)| + 2 * K) * (B0 * (Real.pi / 2))
            * (Real.pi / 2 - θ)⁻¹ := by
      field_simp
    have harith := arith_left (C1 := |cCoef1 u (Real.pi / 4)|)
      (C2 := |cCoef2 u (Real.pi / 4)| + 2 * K) (B0 := B0) (K := K) (θ := θ)
      (τ := Real.pi / 2 - θ) (abs_nonneg _) hC2nn hB0nn hKnn hθ0 hτ
      (by linarith [hle, Real.pi_lt_four]) hinv
    calc |u θ| ≤ (|cCoef1 u (Real.pi / 4)| + B0 * ((Real.pi / θ) * K)) * (2 * θ)
          + (|cCoef2 u (Real.pi / 4)| + 2 * K)
            * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := hsum
      _ = 2 * |cCoef1 u (Real.pi / 4)| * θ + 2 * B0 * Real.pi * K
          + (|cCoef2 u (Real.pi / 4)| + 2 * K) * (B0 * (Real.pi / 2))
            * (Real.pi / 2 - θ)⁻¹ := hEq
      _ ≤ (4 * |cCoef1 u (Real.pi / 4)| + 16 * B0 * K
            + 2 * (|cCoef2 u (Real.pi / 4)| + 2 * K) * B0)
          * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := harith
  · -- Case `θ ≥ π/4`
    have hy1 : |Real.sin (2 * θ)| ≤ 2 * (Real.pi / 2 - θ) := by
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith [Real.pi_pos]))]
      exact sin_two_mul_le_two_sub hge (le_of_lt hθπ)
    have hc1 : |cCoef1 u θ|
        ≤ |cCoef1 u (Real.pi / 4)|
          + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K) := by
      have h := abs_cCoef1_sub_le_right hu2 hder1 hψint hB0nn hB0 hge hθπ
      calc |cCoef1 u θ| = |cCoef1 u (Real.pi / 4) + (cCoef1 u θ - cCoef1 u (Real.pi / 4))| := by
            ring_nf
        _ ≤ |cCoef1 u (Real.pi / 4)| + |cCoef1 u θ - cCoef1 u (Real.pi / 4)| := abs_add_le _ _
        _ ≤ |cCoef1 u (Real.pi / 4)|
              + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K) := by
            linarith
    have hsum : |u θ|
        ≤ (|cCoef1 u (Real.pi / 4)|
              + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
            * (2 * (Real.pi / 2 - θ))
          + (|cCoef2 u (Real.pi / 4)| + 2 * K)
            * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := by
      calc |u θ| = |cCoef1 u θ * Real.sin (2 * θ)
            + cCoef2 u θ * Work.FTS.EllipticEst.LzeroSing θ| := by rw [hcramer]
        _ ≤ |cCoef1 u θ * Real.sin (2 * θ)|
              + |cCoef2 u θ * Work.FTS.EllipticEst.LzeroSing θ| := abs_add_le _ _
        _ = |cCoef1 u θ| * |Real.sin (2 * θ)|
              + |cCoef2 u θ| * |Work.FTS.EllipticEst.LzeroSing θ| := by rw [abs_mul, abs_mul]
        _ ≤ (|cCoef1 u (Real.pi / 4)|
              + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
            * (2 * (Real.pi / 2 - θ))
              + (|cCoef2 u (Real.pi / 4)| + 2 * K)
                * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := by
            have h1 : |cCoef1 u θ| * |Real.sin (2 * θ)|
                ≤ (|cCoef1 u (Real.pi / 4)|
                    + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
                  * (2 * (Real.pi / 2 - θ)) :=
              mul_le_mul hc1 hy1 (abs_nonneg _) (by positivity)
            have h2 : |cCoef2 u θ| * |Work.FTS.EllipticEst.LzeroSing θ|
                ≤ (|cCoef2 u (Real.pi / 4)| + 2 * K)
                  * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) :=
              mul_le_mul hc2 hy2 (abs_nonneg _) (by positivity)
            linarith
    have hEq : (|cCoef1 u (Real.pi / 4)|
          + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
        * (2 * (Real.pi / 2 - θ))
        + (|cCoef2 u (Real.pi / 4)| + 2 * K)
          * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹))
        = 2 * |cCoef1 u (Real.pi / 4)| * (Real.pi / 2 - θ)
          + B0 * (Real.pi ^ 2 / Real.sqrt 2) * K * (Real.pi / 2 - θ)⁻¹
          + (|cCoef2 u (Real.pi / 4)| + 2 * K) * (B0 * (Real.pi / 2))
            * (Real.pi / 2 - θ)⁻¹ := by
      have hc2t : (Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2))
          * (2 * (Real.pi / 2 - θ)) = (Real.pi ^ 2 / Real.sqrt 2) * (Real.pi / 2 - θ)⁻¹ := by
        have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
        have hτne : Real.pi / 2 - θ ≠ 0 := ne_of_gt hτ
        field_simp
      have hsplit : (|cCoef1 u (Real.pi / 4)|
            + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
          * (2 * (Real.pi / 2 - θ))
          = |cCoef1 u (Real.pi / 4)| * (2 * (Real.pi / 2 - θ))
            + B0 * K * ((Real.pi ^ 2 / Real.sqrt 2) * (Real.pi / 2 - θ)⁻¹) := by
        rw [show (|cCoef1 u (Real.pi / 4)|
              + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
            * (2 * (Real.pi / 2 - θ))
            = |cCoef1 u (Real.pi / 4)| * (2 * (Real.pi / 2 - θ))
              + B0 * K * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2))
                  * (2 * (Real.pi / 2 - θ))) by ring,
          hc2t]
      rw [hsplit]
      ring
    have harith := arith_right (C1 := |cCoef1 u (Real.pi / 4)|)
      (C2 := |cCoef2 u (Real.pi / 4)| + 2 * K) (B0 := B0) (K := K) (θ := θ)
      (τ := Real.pi / 2 - θ) (abs_nonneg _) hC2nn hB0nn hKnn hθ0 hτ
      (by linarith [hge, Real.pi_lt_four]) hinv
    calc |u θ|
        ≤ (|cCoef1 u (Real.pi / 4)|
              + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
            * (2 * (Real.pi / 2 - θ))
          + (|cCoef2 u (Real.pi / 4)| + 2 * K)
            * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := hsum
      _ = 2 * |cCoef1 u (Real.pi / 4)| * (Real.pi / 2 - θ)
          + B0 * (Real.pi ^ 2 / Real.sqrt 2) * K * (Real.pi / 2 - θ)⁻¹
          + (|cCoef2 u (Real.pi / 4)| + 2 * K) * (B0 * (Real.pi / 2))
            * (Real.pi / 2 - θ)⁻¹ := hEq
      _ ≤ (4 * |cCoef1 u (Real.pi / 4)| + 16 * B0 * K
            + 2 * (|cCoef2 u (Real.pi / 4)| + 2 * K) * B0)
          * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := harith
/-! ## The two Cramer coefficients at the interior reference angle -/

/-- **The first Cramer coefficient at `π/4`.**  `c₁ u (π/4) = -wron(u, LzeroSing)(π/4)·cos(π/4)`
is a fixed linear functional of `(u(π/4), deriv u (π/4))`, with coefficients `LzeroSing'(π/4)`
and `LzeroSing(π/4)`; the first is bounded by `|LzeroSing'(π/4)| + 1` and the second by `2B₀`
because `cos(π/4) ≥ 1/2`. -/
theorem cCoef1_pi4_le (u : ℝ → ℝ) {B0 : ℝ} (hB0nn : 0 ≤ B0)
    (hB0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.LzeroSing θ * Real.cos θ| ≤ B0) :
    |Work.FTS.EllipticEst.H2W.cCoef1 u (Real.pi / 4)|
      ≤ (Real.sqrt 2 / 2) * ((|deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| + 1) + 2 * B0)
        * (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|) := by
  have hπ4 : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcospos : 0 < Real.cos (Real.pi / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  -- `|LzeroSing (π/4)| ≤ 2 B0` from `|LzeroSing (π/4) · cos (π/4)| ≤ B0` and `cos (π/4) ≥ 1/2`
  have hls : |Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| ≤ 2 * B0 := by
    have h := hB0 (Real.pi / 4) hπ4
    rw [abs_mul, Real.cos_pi_div_four,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / 2)] at h
    have h1 : (1 : ℝ) / 2 ≤ Real.sqrt 2 / 2 := by
      have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      linarith
    have h2 : |Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| * ((1 : ℝ) / 2)
        ≤ |Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| * (Real.sqrt 2 / 2) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    nlinarith [h, h2, abs_nonneg (Work.FTS.EllipticEst.LzeroSing (Real.pi / 4))]
  have hbound : |u (Real.pi / 4) * deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)
        - deriv u (Real.pi / 4) * Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)|
      ≤ ((|deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| + 1) + 2 * B0)
        * (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|) := by
    have h2 : |u (Real.pi / 4) * deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)
          - deriv u (Real.pi / 4) * Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)|
        ≤ |u (Real.pi / 4) * deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)|
          + |deriv u (Real.pi / 4) * Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (u (Real.pi / 4) * deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4))
          (-(deriv u (Real.pi / 4) * Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)))
    rw [abs_mul, abs_mul] at h2
    have hA : 0 ≤ |deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| + 1 := by positivity
    have hB : 0 ≤ 2 * B0 := by linarith
    have hx : 0 ≤ |u (Real.pi / 4)| := abs_nonneg _
    have hy : 0 ≤ |deriv u (Real.pi / 4)| := abs_nonneg _
    nlinarith [h2, hls, hA, hB, hx, hy, abs_nonneg (deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4))]
  calc |Work.FTS.EllipticEst.H2W.cCoef1 u (Real.pi / 4)|
      = Real.cos (Real.pi / 4) * |u (Real.pi / 4) * deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)
          - deriv u (Real.pi / 4) * Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| := by
        rw [Work.FTS.EllipticEst.H2W.cCoef1, Work.FTS.EllipticEst.H2W.wron]
        rw [abs_neg, abs_mul, abs_of_pos hcospos]
        ring
    _ ≤ Real.sqrt 2 / 2 * (((|deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| + 1) + 2 * B0)
          * (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)) := by
        rw [Real.cos_pi_div_four]
        exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (Real.sqrt 2 / 2) * ((|deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| + 1) + 2 * B0)
        * (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|) := by ring

/-- **The second Cramer coefficient at `π/4`.**  `c₂ u (π/4) = -wron(sin 2·, u)(π/4)·cos(π/4)`
equals `-(√2/2)·deriv u (π/4)`, since `sin(π/2) = 1` and `deriv (sin 2·)(π/4) = 2 cos(π/2) = 0`.
The same constant as in `cCoef1_pi4_le` dominates it because it is at least `√2/2`. -/
theorem cCoef2_pi4_le (u : ℝ → ℝ) {B0 : ℝ} (hB0nn : 0 ≤ B0) :
    |Work.FTS.EllipticEst.H2W.cCoef2 u (Real.pi / 4)|
      ≤ (Real.sqrt 2 / 2) * ((|deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| + 1) + 2 * B0)
        * (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|) := by
  have hcospos : 0 < Real.cos (Real.pi / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hs2 : Real.sin (2 * (Real.pi / 4)) = 1 := by
    have h : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
    rw [h, Real.sin_pi_div_two]
  have hder : deriv (fun t : ℝ => Real.sin (2 * t)) (Real.pi / 4) = 0 := by
    have h : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * (Real.pi / 4)) * 2)
        (Real.pi / 4) := by
      simpa only [id_eq, one_mul, mul_one] using ((hasDerivAt_id (Real.pi / 4)).const_mul 2).sin
    rw [h.deriv]
    have h2 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
    rw [h2, Real.cos_pi_div_two]
    ring
  have hAle : Real.sqrt 2 / 2
      ≤ (Real.sqrt 2 / 2) * ((|deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| + 1) + 2 * B0) := by
    have h1 : (1 : ℝ) ≤ (|deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| + 1) + 2 * B0 := by
      have := abs_nonneg (deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4))
      linarith
    have h2 : 0 ≤ Real.sqrt 2 / 2 := by positivity
    nlinarith [h1, h2]
  have hD : |deriv u (Real.pi / 4)| ≤ |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| :=
    le_add_of_nonneg_left (abs_nonneg _)
  have hkey : |Work.FTS.EllipticEst.H2W.cCoef2 u (Real.pi / 4)|
      = Real.sqrt 2 / 2 * |deriv u (Real.pi / 4)| := by
    rw [Work.FTS.EllipticEst.H2W.cCoef2, Work.FTS.EllipticEst.H2W.wron]
    rw [hs2, hder]
    rw [one_mul, zero_mul, sub_zero]
    rw [abs_neg, abs_mul, abs_of_pos hcospos, Real.cos_pi_div_four, mul_comm]
  rw [hkey]
  have hstep : Real.sqrt 2 / 2 * |deriv u (Real.pi / 4)|
      ≤ Real.sqrt 2 / 2 * (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|) :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  have hstep2 : Real.sqrt 2 / 2 * (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
      ≤ (Real.sqrt 2 / 2) * ((|deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| + 1) + 2 * B0)
        * (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|) := by
    have hDnn : 0 ≤ |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| := by positivity
    have := mul_le_mul_of_nonneg_right hAle hDnn
    linarith [this]
  linarith [hstep, hstep2]

/-- **Bounds on both Cramer coefficients at `π/4` by the data of `u` only.** -/
theorem cCoefPi4Bound {B0 : ℝ} (hB0nn : 0 ≤ B0)
    (hB0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.LzeroSing θ * Real.cos θ| ≤ B0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ → ℝ,
      |Work.FTS.EllipticEst.H2W.cCoef1 u (Real.pi / 4)|
          ≤ A * (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
        ∧ |Work.FTS.EllipticEst.H2W.cCoef2 u (Real.pi / 4)|
          ≤ A * (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|) :=
  ⟨(Real.sqrt 2 / 2) * ((|deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4)| + 1) + 2 * B0),
    by positivity,
    fun u => ⟨cCoef1_pi4_le u hB0nn hB0, cCoef2_pi4_le u hB0nn⟩⟩

/-! ## The integral bookkeeping: `∫_{Iθ}(f + c) = ∫_{Iθ} f + c·(π/2)` -/

/-- A set integral over `Iθ = [0, π/2]` is the corresponding interval integral. -/
private lemma integral_Iθ_congr (g : ℝ → ℝ) :
    (∫ s in Work.Spaces.Iθ, g s) = ∫ s in (0 : ℝ)..(Real.pi / 2), g s := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [Work.Spaces.Iθ, intervalIntegral.integral_of_le (f := g) hle]
  exact (MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc)).symm

/-- The integral over `Iθ` of a function with an added constant. -/
private lemma integral_Iθ_add_const (f : ℝ → ℝ) (c : ℝ)
    (hf : MeasureTheory.IntegrableOn f Work.Spaces.Iθ) :
    (∫ s in Work.Spaces.Iθ, (f s + c)) = (∫ s in Work.Spaces.Iθ, f s) + c * (Real.pi / 2) := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hfint : IntervalIntegrable f volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hle]
    exact hf.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hcint : IntervalIntegrable (fun _ : ℝ => c) volume 0 (Real.pi / 2) :=
    intervalIntegrable_const
  rw [integral_Iθ_congr (fun s => f s + c), integral_Iθ_congr f,
    intervalIntegral.integral_add hfint hcint, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  ring

/-- **The quantitative one-variable `θ`-growth bound.**  There is a universal `C > 0` such that
every `C^∞` slice `u` on `(0, π/2)` with `∫_{Iθ} sinθcos²θ·|Lzero1 u| < ∞` satisfies

  `|u θ| ≤ C·(∫_{Iθ} sinθcos²θ·|Lzero1 u| + |u(π/4)| + |deriv u(π/4)|)·(θ⁻¹ + (π/2-θ)⁻¹)`.

This is the form in which the constant is *controlled by the data*, which is what makes the
slice bound uniform in `z` when applied to the slices `θ ↦ ∂_z^mΨ(z,·)`. -/
theorem lzeroGrowthQuantL1Self : ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ →
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ C * (∫ s in Work.Spaces.Iθ,
            Real.sin s * Real.cos s ^ 2 * |Work.FTS.EllipticEst.Lzero1 u s|
          + |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
        * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
  obtain ⟨B0, hB0pos, hB0⟩ := Work.FTS.EllipticEst.H2W.Lzb.LzeroSingCosBoundClean
  have hB0nn : 0 ≤ B0 := le_of_lt hB0pos
  obtain ⟨A, hAnn, hA⟩ := cCoefPi4Bound hB0nn hB0
  refine ⟨2 * (4 * A + 2 * A * B0 + 20 * B0) + 1, by positivity, fun u hu hint θ hθ => ?_⟩
  obtain ⟨hc1, hc2⟩ := hA u
  have hmain := growthExplicit hu hint hB0nn hB0 θ hθ
  -- `K` is the weighted source mass, `D` the data at the reference angle `π/4`
  set K : ℝ := ∫ s in Work.Spaces.Iθ,
    Work.FTS.EllipticEst.H2W.psiW s * |Work.FTS.EllipticEst.Lzero1 u s| with hKdef
  set D : ℝ := |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| with hDdef
  -- `J` is the bracket of the statement: the integral of the sum
  set J : ℝ := ∫ s in Work.Spaces.Iθ,
    (Real.sin s * Real.cos s ^ 2 * |Work.FTS.EllipticEst.Lzero1 u s|
      + |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|) with hJdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun s hs => ?_)
    exact mul_nonneg (Work.FTS.EllipticEst.H2W.psiW_nonneg hs) (abs_nonneg _)
  have hDnn : 0 ≤ D := by rw [hDdef]; positivity
  have hc1' : |Work.FTS.EllipticEst.H2W.cCoef1 u (Real.pi / 4)| ≤ A * D := by
    rw [hDdef]; exact hc1
  have hc2' : |Work.FTS.EllipticEst.H2W.cCoef2 u (Real.pi / 4)| ≤ A * D := by
    rw [hDdef]; exact hc2
  have hmain' : |u θ| ≤ (4 * |Work.FTS.EllipticEst.H2W.cCoef1 u (Real.pi / 4)|
        + 16 * B0 * K
        + 2 * (|Work.FTS.EllipticEst.H2W.cCoef2 u (Real.pi / 4)| + 2 * K) * B0)
      * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := hmain
  have hC0le : 4 * |Work.FTS.EllipticEst.H2W.cCoef1 u (Real.pi / 4)|
        + 16 * B0 * K
        + 2 * (|Work.FTS.EllipticEst.H2W.cCoef2 u (Real.pi / 4)| + 2 * K) * B0
      ≤ (4 * A + 2 * A * B0 + 20 * B0) * (K + D) := by
    have h1 : 0 ≤ |Work.FTS.EllipticEst.H2W.cCoef1 u (Real.pi / 4)| := abs_nonneg _
    have h2 : 0 ≤ |Work.FTS.EllipticEst.H2W.cCoef2 u (Real.pi / 4)| := abs_nonneg _
    nlinarith [h1, h2, hc1', hc2', hAnn, hB0nn, hKnn, hDnn,
      mul_nonneg hAnn hDnn, mul_nonneg hAnn hKnn,
      mul_nonneg (mul_nonneg hAnn hDnn) hB0nn]
  -- the bracket `J` in terms of `K` and `D`
  have hJeq : J = K + D * (Real.pi / 2) := by
    have hfun : (fun s : ℝ => Real.sin s * Real.cos s ^ 2 * |Work.FTS.EllipticEst.Lzero1 u s|
          + |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
        = (fun s : ℝ => Real.sin s * Real.cos s ^ 2 * |Work.FTS.EllipticEst.Lzero1 u s|
            + D) := by
      rw [hDdef]; funext s; ring
    have hKfun : (fun s : ℝ => Work.FTS.EllipticEst.H2W.psiW s
          * |Work.FTS.EllipticEst.Lzero1 u s|)
        = (fun s : ℝ => Real.sin s * Real.cos s ^ 2 * |Work.FTS.EllipticEst.Lzero1 u s|) := by
      funext s
      rw [Work.FTS.EllipticEst.H2W.psiW]
    rw [hJdef]
    calc (∫ s in Work.Spaces.Iθ,
          (Real.sin s * Real.cos s ^ 2 * |Work.FTS.EllipticEst.Lzero1 u s|
            + |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|))
        = (∫ s in Work.Spaces.Iθ,
            (Real.sin s * Real.cos s ^ 2 * |Work.FTS.EllipticEst.Lzero1 u s| + D)) := by
          rw [hfun]
      _ = (∫ s in Work.Spaces.Iθ,
            Real.sin s * Real.cos s ^ 2 * |Work.FTS.EllipticEst.Lzero1 u s|)
            + D * (Real.pi / 2) :=
          integral_Iθ_add_const
            (fun s : ℝ => Real.sin s * Real.cos s ^ 2 * |Work.FTS.EllipticEst.Lzero1 u s|) D hint
      _ = K + D * (Real.pi / 2) := by rw [← hKfun, hKdef]
  have hJnn : 0 ≤ J := by
    rw [hJeq]
    have hpi : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    nlinarith [hKnn, hDnn, hpi]
  have hKD : K + D ≤ 2 * J := by
    rw [hJeq]
    have hpi : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
    nlinarith [hKnn, hDnn, hpi]
  have hQ : 0 ≤ 4 * A + 2 * A * B0 + 20 * B0 := by positivity
  have h1 : (4 * A + 2 * A * B0 + 20 * B0) * (K + D)
      ≤ (4 * A + 2 * A * B0 + 20 * B0) * (2 * J) := mul_le_mul_of_nonneg_left hKD hQ
  have h2 : (2 * (4 * A + 2 * A * B0 + 20 * B0)) * J
      ≤ (2 * (4 * A + 2 * A * B0 + 20 * B0) + 1) * J := by nlinarith [hJnn]
  have hfinal : 4 * |Work.FTS.EllipticEst.H2W.cCoef1 u (Real.pi / 4)|
        + 16 * B0 * K
        + 2 * (|Work.FTS.EllipticEst.H2W.cCoef2 u (Real.pi / 4)| + 2 * K) * B0
      ≤ (2 * (4 * A + 2 * A * B0 + 20 * B0) + 1) * J := by
    have h3 : (4 * A + 2 * A * B0 + 20 * B0) * (2 * J)
        = (2 * (4 * A + 2 * A * B0 + 20 * B0)) * J := by ring
    linarith [hC0le, h1, h2, h3.le]
  have hρ : 0 ≤ θ⁻¹ + (Real.pi / 2 - θ)⁻¹ :=
    add_nonneg (inv_nonneg.mpr hθ.1.le) (inv_nonneg.mpr (by linarith [hθ.2]))
  exact le_trans hmain' (mul_le_mul_of_nonneg_right hfinal hρ)

end Work.FTS.EllipticEst.H2W.LocC
