import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngAWeak.chiDefs
import Submission.Work.FTS.EllipticEst.AngAWeak.AngWeakDefs
import Submission.Work.FTS.EllipticEst.AngAWeak.corrLeftRate
import Submission.Work.FTS.EllipticEst.AngAWeak.corrRightRate

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-- `x ^ p → 0` as `x → 0⁺` for `p > 0`. -/
lemma tendsto_rpow_nhdsGT_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun x : ℝ => x ^ p) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h : Tendsto (fun x : ℝ => (x⁻¹) ^ (-p)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (tendsto_rpow_neg_atTop hp).comp tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [Real.inv_rpow (le_of_lt hx) (-p), Real.rpow_neg (le_of_lt hx) p, inv_inv]

/-- `sin(2θ) ≥ 4θ/π` for `0 < θ < π/8`. -/
lemma sin_two_ge_left {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8)) :
    4 * θ / Real.pi ≤ Real.sin (2 * θ) := by
  have h1 : 0 ≤ 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ ≤ Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
  have h := Real.mul_le_sin h1 h2
  calc 4 * θ / Real.pi = 2 / Real.pi * (2 * θ) := by ring
    _ ≤ Real.sin (2 * θ) := h

/-- `sin(2θ) ≥ 4(π/2 - θ)/π` for `π/2 - π/8 < θ < π/2`. -/
lemma sin_two_ge_right {θ : ℝ} (hθ : θ ∈ Set.Ioo (Real.pi / 2 - Real.pi / 8) (Real.pi / 2)) :
    4 * (Real.pi / 2 - θ) / Real.pi ≤ Real.sin (2 * θ) := by
  have h0 : 0 ≤ 2 * (Real.pi / 2 - θ) := by linarith [hθ.2]
  have h2 : 2 * (Real.pi / 2 - θ) ≤ Real.pi / 2 := by linarith [hθ.1, Real.pi_pos]
  have h := Real.mul_le_sin h0 h2
  have heq : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
    rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
  rw [heq]
  calc 4 * (Real.pi / 2 - θ) / Real.pi = 2 / Real.pi * (2 * (Real.pi / 2 - θ)) := by ring
    _ ≤ Real.sin (2 * (Real.pi / 2 - θ)) := h

/-- Squeeze helper: if `d → 0⁺` and `|g| ≤ C · d ^ p` with `p > 0`, then `g → 0`. -/
lemma tendsto_zero_of_le_rpow {α : Type*} {l : Filter α} {g d : α → ℝ} {C p : ℝ}
    (hp : 0 < p) (hd : Tendsto d l (nhdsWithin 0 (Set.Ioi 0)))
    (h : ∀ᶠ x in l, |g x| ≤ C * (d x) ^ p) : Tendsto g l (nhds 0) := by
  have hlim : Tendsto (fun x => C * (d x) ^ p) l (nhds 0) := by
    have h1 : Tendsto (fun x => (d x) ^ p) l (nhds 0) := (tendsto_rpow_nhdsGT_zero hp).comp hd
    simpa using h1.const_mul C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [Real.norm_eq_abs]
  exact squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) h hlim

/-- Left endpoint: `sin(2θ)^{-r} ≤ (4/π)^{-r} θ^{-r}` for `r ≥ 0`, `0 < θ < π/8`. -/
lemma sin_two_rpow_le_left {r θ : ℝ} (hr : 0 ≤ r) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8)) :
    (Real.sin (2 * θ)) ^ (-r) ≤ (4 / Real.pi) ^ (-r) * θ ^ (-r) := by
  have hθpos : 0 < θ := hθ.1
  have hsin : 4 * θ / Real.pi ≤ Real.sin (2 * θ) := sin_two_ge_left hθ
  have h1 : (Real.sin (2 * θ)) ^ (-r) ≤ (4 * θ / Real.pi) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hsin (by linarith)
  have h2 : (4 * θ / Real.pi) ^ (-r) = (4 / Real.pi) ^ (-r) * θ ^ (-r) := by
    rw [show 4 * θ / Real.pi = (4 / Real.pi) * θ by ring,
      Real.mul_rpow (by positivity) (le_of_lt hθpos)]
  rw [h2] at h1
  exact h1

/-- Right endpoint: `sin(2θ)^{-r} ≤ (4/π)^{-r} (π/2 - θ)^{-r}` for `r ≥ 0`,
`π/2 - π/8 < θ < π/2`. -/
lemma sin_two_rpow_le_right {r θ : ℝ} (hr : 0 ≤ r)
    (hθ : θ ∈ Set.Ioo (Real.pi / 2 - Real.pi / 8) (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (-r) ≤ (4 / Real.pi) ^ (-r) * (Real.pi / 2 - θ) ^ (-r) := by
  have hδpos : 0 < Real.pi / 2 - θ := sub_pos.mpr hθ.2
  have hsin : 4 * (Real.pi / 2 - θ) / Real.pi ≤ Real.sin (2 * θ) := sin_two_ge_right hθ
  have h1 : (Real.sin (2 * θ)) ^ (-r) ≤ (4 * (Real.pi / 2 - θ) / Real.pi) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hsin (by linarith)
  have h2 : (4 * (Real.pi / 2 - θ) / Real.pi) ^ (-r)
      = (4 / Real.pi) ^ (-r) * (Real.pi / 2 - θ) ^ (-r) := by
    rw [show 4 * (Real.pi / 2 - θ) / Real.pi = (4 / Real.pi) * (Real.pi / 2 - θ) by ring,
      Real.mul_rpow (by positivity) (le_of_lt hδpos)]
  rw [h2] at h1
  exact h1

/-- The corrected slice is `u - L` near `0⁺` (where the cut-off is `1`). -/
lemma corrSlice_eq_of_lt {u : ℝ → ℝ} {L θ : ℝ} (hθ : θ ≤ Real.pi / 8) :
    corrSlice u L θ = u θ - L := by
  simp only [corrSlice, chiAng_eq_one hθ, mul_one]

/-- The corrected slice is `u` near `π/2` (where the cut-off is `0`). -/
lemma corrSlice_eq_of_gt {u : ℝ → ℝ} {L θ : ℝ} (hθ : Real.pi / 4 ≤ θ) :
    corrSlice u L θ = u θ := by
  simp only [corrSlice, chiAng_eq_zero hθ, mul_zero, sub_zero]

/-- Near `0⁺` (where the cut-off is locally `1`) the derivative of the corrected slice is that
of `u`. -/
lemma deriv_corrSlice_eq_of_lt {u : ℝ → ℝ} {L θ : ℝ} (hθ : θ < Real.pi / 8) :
    deriv (corrSlice u L) θ = deriv u θ := by
  have hev : corrSlice u L =ᶠ[𝓝 θ] fun x => u x - L := by
    filter_upwards [chiAng_eventuallyEq_one hθ] with x hx
    simp only [corrSlice, hx, mul_one]
  rw [hev.deriv_eq, deriv_sub_const]

/-- Near `π/2` (where the cut-off is locally `0`) the derivative of the corrected slice is that
of `u`. -/
lemma deriv_corrSlice_eq_of_gt {u : ℝ → ℝ} {L θ : ℝ} (hθ : Real.pi / 4 < θ) :
    deriv (corrSlice u L) θ = deriv u θ := by
  have hev : corrSlice u L =ᶠ[𝓝 θ] fun x => u x - 0 := by
    filter_upwards [chiAng_eventuallyEq_zero hθ] with x hx
    simp only [corrSlice, hx, mul_zero]
  rw [hev.deriv_eq, deriv_sub_const]

theorem corrSlice_limits (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) {u : ℝ → ℝ} {L : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hu2 : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.AngAWeak.wq q θ) Work.Spaces.Iθ)
    (hLu2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2
        * Work.FTS.EllipticEst.AngAWeak.wq q θ) Work.Spaces.Iθ)
    (hL : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    (Filter.Tendsto (fun θ => Work.FTS.EllipticEst.AngAWeak.corrSlice u L θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      (Filter.Tendsto (fun θ => (Work.FTS.EllipticEst.AngAWeak.corrSlice u L θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(1 + q))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      (Filter.Tendsto (fun θ => deriv (Work.FTS.EllipticEst.AngAWeak.corrSlice u L) θ
          * Work.FTS.EllipticEst.AngAWeak.corrSlice u L θ
          * Work.FTS.EllipticEst.AngAWeak.wq q θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      (Filter.Tendsto (fun θ => Work.FTS.EllipticEst.AngAWeak.corrSlice u L θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) ∧
      (Filter.Tendsto (fun θ => (Work.FTS.EllipticEst.AngAWeak.corrSlice u L θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(1 + q)))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) ∧
      (Filter.Tendsto (fun θ => deriv (Work.FTS.EllipticEst.AngAWeak.corrSlice u L) θ
          * Work.FTS.EllipticEst.AngAWeak.corrSlice u L θ
          * Work.FTS.EllipticEst.AngAWeak.wq q θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  obtain ⟨M, hMpos, hMbd⟩ := corrLeftRate q hq0 hq1 hsm hu2 hLu2 hL
  obtain ⟨K, hKpos, hKbd⟩ := corrRightRate q hq0 hq1 hsm hu2 hLu2
  have hMnn : 0 ≤ M := le_of_lt hMpos
  have hKnn : 0 ≤ K := le_of_lt hKpos
  -- the two filters and the two "distance to the endpoint" functions
  have hdL : Tendsto (fun θ : ℝ => θ) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_nhdsWithin_of_tendsto_nhds tendsto_id, self_mem_nhdsWithin⟩
  have hdR : Tendsto (fun θ : ℝ => Real.pi / 2 - θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 (Real.pi / 2))
          (𝓝 (Real.pi / 2 - Real.pi / 2)) := tendsto_const_nhds.sub tendsto_id
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      have hθ' : θ < Real.pi / 2 := by simpa using hθ
      exact sub_pos.mpr hθ'
  -- membership of the intervals where the cut-off is constant
  have hmeL : Set.Ioo (0 : ℝ) (Real.pi / 8) ∈ nhdsWithin 0 (Set.Ioi 0) := by
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 8)] with θ hθ hθ0
    exact ⟨hθ0, hθ.2⟩
  have hmeR : Set.Ioo (Real.pi / 2 - Real.pi / 8) (Real.pi / 2)
      ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [Ioo_mem_nhds
      (by linarith [Real.pi_pos] : Real.pi / 2 - Real.pi / 8 < Real.pi / 2)
      (by linarith [Real.pi_pos] : Real.pi / 2 < Real.pi / 2 + 1)] with θ hθ hθ2
    exact ⟨hθ.1, hθ2⟩
  -- (1) `corrSlice → 0` at `0⁺`
  have h1 : Tendsto (fun θ => corrSlice u L θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine tendsto_zero_of_le_rpow (p := 1) (d := fun θ : ℝ => θ) (C := M) one_pos hdL ?_
    filter_upwards [hmeL] with θ hθ
    rw [corrSlice_eq_of_lt hθ.2.le, Real.rpow_one]
    exact (hMbd θ hθ).1
  -- (2, left) `corrSlice² · sin(2θ)^{-(1+q)} → 0` at `0⁺`
  have h2 : Tendsto (fun θ => (corrSlice u L θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + q)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine tendsto_zero_of_le_rpow (p := 1 - q) (d := fun θ : ℝ => θ)
      (C := M ^ 2 * (4 / Real.pi) ^ (-(1 + q))) (by linarith) hdL ?_
    filter_upwards [hmeL] with θ hθ
    have hθpos : 0 < θ := hθ.1
    have hsin : 4 * θ / Real.pi ≤ Real.sin (2 * θ) := sin_two_ge_left hθ
    have hsinpos : 0 < Real.sin (2 * θ) := lt_of_lt_of_le (by positivity) hsin
    have habs : |corrSlice u L θ| ≤ M * θ := by
      rw [corrSlice_eq_of_lt hθ.2.le]
      exact (hMbd θ hθ).1
    have hrs : (Real.sin (2 * θ)) ^ (-(1 + q)) ≤ (4 / Real.pi) ^ (-(1 + q)) * θ ^ (-(1 + q)) :=
      sin_two_rpow_le_left (by linarith) hθ
    have hpow : θ ^ 2 * θ ^ (-(1 + q)) = θ ^ (1 - q) := by
      have hθ2 : θ ^ 2 = θ ^ (2 : ℝ) := (Real.rpow_two θ).symm
      rw [hθ2, ← Real.rpow_add hθpos]
      congr 1
      ring
    calc |(corrSlice u L θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + q))|
        = |corrSlice u L θ| ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + q)) := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg (corrSlice u L θ)), sq_abs,
              abs_of_nonneg (Real.rpow_nonneg (le_of_lt hsinpos) _)]
      _ ≤ (M * θ) ^ 2 * ((4 / Real.pi) ^ (-(1 + q)) * θ ^ (-(1 + q))) :=
            mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) habs 2) hrs
              (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
      _ = M ^ 2 * (4 / Real.pi) ^ (-(1 + q)) * θ ^ (1 - q) := by
            rw [mul_pow]
            rw [show M ^ 2 * θ ^ 2 * ((4 / Real.pi) ^ (-(1 + q)) * θ ^ (-(1 + q)))
                  = M ^ 2 * (4 / Real.pi) ^ (-(1 + q)) * (θ ^ 2 * θ ^ (-(1 + q))) by ring,
              hpow]
  -- (3, left) `deriv corrSlice · corrSlice · wq q → 0` at `0⁺`
  have h3 : Tendsto (fun θ => deriv (corrSlice u L) θ * corrSlice u L θ * wq q θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine tendsto_zero_of_le_rpow (p := 1 - q) (d := fun θ : ℝ => θ)
      (C := M ^ 2 * (4 / Real.pi) ^ (-q)) (by linarith) hdL ?_
    filter_upwards [hmeL] with θ hθ
    have hθpos : 0 < θ := hθ.1
    have hsinpos : 0 < Real.sin (2 * θ) :=
      lt_of_lt_of_le (by positivity) (sin_two_ge_left hθ)
    have hrs : (Real.sin (2 * θ)) ^ (-q) ≤ (4 / Real.pi) ^ (-q) * θ ^ (-q) :=
      sin_two_rpow_le_left (by linarith) hθ
    have hb1 : |deriv (corrSlice u L) θ| ≤ M := by
      rw [deriv_corrSlice_eq_of_lt hθ.2]
      exact (hMbd θ hθ).2.2
    have hb2 : |corrSlice u L θ| ≤ M * θ := by
      rw [corrSlice_eq_of_lt hθ.2.le]
      exact (hMbd θ hθ).1
    have hb3 : |wq q θ| ≤ (4 / Real.pi) ^ (-q) * θ ^ (-q) := by
      have hwqnn : 0 ≤ wq q θ := by
        rw [wq]
        exact Real.rpow_nonneg (le_of_lt hsinpos) _
      rw [abs_of_nonneg hwqnn, wq]
      exact hrs
    have hpow1 : θ ^ (1 : ℝ) * θ ^ (-q) = θ ^ (1 - q) := by
      have hexp : (1 : ℝ) + (-q) = 1 - q := by ring
      rw [← Real.rpow_add hθpos, hexp]
    calc |deriv (corrSlice u L) θ * corrSlice u L θ * wq q θ|
        = |deriv (corrSlice u L) θ| * |corrSlice u L θ| * |wq q θ| := by
            rw [abs_mul, abs_mul]
      _ ≤ M * (M * θ) * ((4 / Real.pi) ^ (-q) * θ ^ (-q)) :=
            mul_le_mul (mul_le_mul hb1 hb2 (abs_nonneg _) hMnn) hb3 (abs_nonneg _)
              (mul_nonneg hMnn (mul_nonneg hMnn (le_of_lt hθpos)))
      _ = M ^ 2 * (4 / Real.pi) ^ (-q) * θ ^ (1 - q) := by
            rw [show M * (M * θ) * ((4 / Real.pi) ^ (-q) * θ ^ (-q))
                  = M ^ 2 * (4 / Real.pi) ^ (-q) * (θ ^ (1 : ℝ) * θ ^ (-q)) by
                rw [Real.rpow_one]; ring,
              hpow1]
  -- (4) `corrSlice → 0` at `(π/2)⁻`
  have h4 : Tendsto (fun θ => corrSlice u L θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine tendsto_zero_of_le_rpow (p := 1) (d := fun θ : ℝ => Real.pi / 2 - θ)
      (C := K) one_pos hdR ?_
    filter_upwards [hmeR] with θ hθ
    rw [corrSlice_eq_of_gt (by linarith [hθ.1, Real.pi_pos] : Real.pi / 4 ≤ θ), Real.rpow_one]
    exact (hKbd θ hθ).1
  -- (5, right) `corrSlice² · sin(2θ)^{-(1+q)} → 0` at `(π/2)⁻`
  have h5 : Tendsto (fun θ => (corrSlice u L θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + q)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine tendsto_zero_of_le_rpow (p := 1 - q) (d := fun θ : ℝ => Real.pi / 2 - θ)
      (C := K ^ 2 * (4 / Real.pi) ^ (-(1 + q))) (by linarith) hdR ?_
    filter_upwards [hmeR] with θ hθ
    have hδpos : 0 < Real.pi / 2 - θ := sub_pos.mpr hθ.2
    have hθ4 : Real.pi / 4 < θ := by linarith [hθ.1, Real.pi_pos]
    have hsin : 4 * (Real.pi / 2 - θ) / Real.pi ≤ Real.sin (2 * θ) := sin_two_ge_right hθ
    have hsinpos : 0 < Real.sin (2 * θ) := lt_of_lt_of_le (by positivity) hsin
    have habs : |corrSlice u L θ| ≤ K * (Real.pi / 2 - θ) := by
      rw [corrSlice_eq_of_gt hθ4.le]
      exact (hKbd θ hθ).1
    have hrs : (Real.sin (2 * θ)) ^ (-(1 + q))
        ≤ (4 / Real.pi) ^ (-(1 + q)) * (Real.pi / 2 - θ) ^ (-(1 + q)) :=
      sin_two_rpow_le_right (by linarith) hθ
    have hpow : (Real.pi / 2 - θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(1 + q))
        = (Real.pi / 2 - θ) ^ (1 - q) := by
      have hδ2 : (Real.pi / 2 - θ) ^ 2 = (Real.pi / 2 - θ) ^ (2 : ℝ) :=
        (Real.rpow_two _).symm
      rw [hδ2, ← Real.rpow_add hδpos]
      congr 1
      ring
    calc |(corrSlice u L θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + q))|
        = |corrSlice u L θ| ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + q)) := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg (corrSlice u L θ)), sq_abs,
              abs_of_nonneg (Real.rpow_nonneg (le_of_lt hsinpos) _)]
      _ ≤ (K * (Real.pi / 2 - θ)) ^ 2 * ((4 / Real.pi) ^ (-(1 + q))
            * (Real.pi / 2 - θ) ^ (-(1 + q))) :=
            mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) habs 2) hrs
              (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
      _ = K ^ 2 * (4 / Real.pi) ^ (-(1 + q)) * (Real.pi / 2 - θ) ^ (1 - q) := by
            rw [mul_pow]
            rw [show K ^ 2 * (Real.pi / 2 - θ) ^ 2
                    * ((4 / Real.pi) ^ (-(1 + q)) * (Real.pi / 2 - θ) ^ (-(1 + q)))
                  = K ^ 2 * (4 / Real.pi) ^ (-(1 + q))
                    * ((Real.pi / 2 - θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(1 + q))) by ring,
              hpow]
  -- (6, right) `deriv corrSlice · corrSlice · wq q → 0` at `(π/2)⁻`
  have h6 : Tendsto (fun θ => deriv (corrSlice u L) θ * corrSlice u L θ * wq q θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine tendsto_zero_of_le_rpow (p := 1 - q) (d := fun θ : ℝ => Real.pi / 2 - θ)
      (C := K ^ 2 * (4 / Real.pi) ^ (-q)) (by linarith) hdR ?_
    filter_upwards [hmeR] with θ hθ
    have hδpos : 0 < Real.pi / 2 - θ := sub_pos.mpr hθ.2
    have hθ4 : Real.pi / 4 < θ := by linarith [hθ.1, Real.pi_pos]
    have hsinpos : 0 < Real.sin (2 * θ) :=
      lt_of_lt_of_le (by positivity) (sin_two_ge_right hθ)
    have hb1 : |deriv (corrSlice u L) θ| ≤ K := by
      rw [deriv_corrSlice_eq_of_gt hθ4]
      exact (hKbd θ hθ).2
    have hb2 : |corrSlice u L θ| ≤ K * (Real.pi / 2 - θ) := by
      rw [corrSlice_eq_of_gt hθ4.le]
      exact (hKbd θ hθ).1
    have hb3 : |wq q θ| ≤ (4 / Real.pi) ^ (-q) * (Real.pi / 2 - θ) ^ (-q) := by
      have hwqnn : 0 ≤ wq q θ := by
        rw [wq]
        exact Real.rpow_nonneg (le_of_lt hsinpos) _
      rw [abs_of_nonneg hwqnn, wq]
      exact sin_two_rpow_le_right (by linarith) hθ
    have hpow1 : (Real.pi / 2 - θ) ^ (1 : ℝ) * (Real.pi / 2 - θ) ^ (-q)
        = (Real.pi / 2 - θ) ^ (1 - q) := by
      have hexp : (1 : ℝ) + (-q) = 1 - q := by ring
      rw [← Real.rpow_add hδpos, hexp]
    calc |deriv (corrSlice u L) θ * corrSlice u L θ * wq q θ|
        = |deriv (corrSlice u L) θ| * |corrSlice u L θ| * |wq q θ| := by
            rw [abs_mul, abs_mul]
      _ ≤ K * (K * (Real.pi / 2 - θ)) * ((4 / Real.pi) ^ (-q) * (Real.pi / 2 - θ) ^ (-q)) :=
            mul_le_mul (mul_le_mul hb1 hb2 (abs_nonneg _) hKnn) hb3 (abs_nonneg _)
              (mul_nonneg hKnn (mul_nonneg hKnn (le_of_lt hδpos)))
      _ = K ^ 2 * (4 / Real.pi) ^ (-q) * (Real.pi / 2 - θ) ^ (1 - q) := by
            rw [show K * (K * (Real.pi / 2 - θ))
                    * ((4 / Real.pi) ^ (-q) * (Real.pi / 2 - θ) ^ (-q))
                  = K ^ 2 * (4 / Real.pi) ^ (-q)
                    * ((Real.pi / 2 - θ) ^ (1 : ℝ) * (Real.pi / 2 - θ) ^ (-q)) by
                rw [Real.rpow_one]; ring,
              hpow1]
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Work.FTS.EllipticEst.AngAWeak
