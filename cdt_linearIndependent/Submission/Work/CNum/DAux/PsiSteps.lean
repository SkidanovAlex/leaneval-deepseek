import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.C2_setup
import Submission.Work.CNum.C2_Psi_antitone
import Submission.Work.CNum.AlpBound
import Submission.Work.CNum.DAux.DeltaBound
import Submission.Work.CNum.DAux.SinHalfBound
import Submission.Work.CNum.DAux.C2PsiHasDerivAt

/-!
# `Work.CNum.DAux.PsiSteps`

Elementary "small step" bounds for the `C₂`-arc angle `Ψ = C2Psi`:

* on the interval `θ ∈ [2π·245/1024, 2π·779/1024]`, whose half `t = θ/2` lies in
  `[p0, p1] = [245π/1024, 779π/1024]`, the function `Ψ` is `300`-Lipschitz, so that
  `Ψ (θ/2) - Ψ (θ'/2) ≤ 300·(θ' - θ)/2 ≤ 300·π/1024 ≤ 1` whenever `θ ≤ θ'` and
  `θ' - θ ≤ 2π/1024`;
* `Ψ (α/2) - Ψ (p0) ≤ 1`, where `Ψ (α/2) = α/2 < 1` and `Ψ (p0) ≥ 0` because
  `p0 ≤ π/2` and `Ψ` is antitone with `Ψ (π/2) = 0`;
* `Ψ (p1) - Ψ (π - α/2) ≤ 1`, which is the same statement by the symmetry
  `Ψ (π - t) = -Ψ t` (`p1 = π - p0`).

The Lipschitz constant comes from `Ψ' t = 1 - sin t/√(C² - cos² t)`: on `[p0, p1]`
one has `|Ψ' t| ≤ 1/√(sin² p0 - σ²) ≤ 300` because `sin t ≥ sin p0` there and
`√(sin² p0 - σ²) ≥ 1/300` (`SinHalfBound`).
-/

namespace Work.CNum.DAux

open Real

noncomputable section

/-- Left endpoint `245π/1024` of the `θ/2`-interval. -/
def p0 : ℝ := 245 * Real.pi / 1024
/-- Right endpoint `779π/1024 = π - 245π/1024`. -/
def p1 : ℝ := 779 * Real.pi / 1024

lemma p0_pos : 0 < p0 := by rw [p0]; positivity

lemma p0_le_halfpi : p0 ≤ Real.pi / 2 := by
  rw [p0]; nlinarith [Real.pi_pos]

lemma p1_eq : p1 = Real.pi - p0 := by rw [p0, p1]; ring

lemma p0_le_p1 : p0 ≤ p1 := by rw [p0, p1]; nlinarith [Real.pi_pos]

lemma half_alpR_lt_p0 : Work.CNum.alpR / 2 < p0 := by
  have h := DeltaBound
  rw [p0]
  linarith

lemma p1_lt_pi_sub : p1 < Real.pi - Work.CNum.alpR / 2 := by
  have h := half_alpR_lt_p0
  rw [p1_eq]
  linarith

lemma mem_Ioo_of_mem_p {z : ℝ} (hz : z ∈ Set.Icc p0 p1) :
    z ∈ Set.Ioo (Work.CNum.alpR / 2) (Real.pi - Work.CNum.alpR / 2) :=
  ⟨lt_of_lt_of_le half_alpR_lt_p0 hz.1, lt_of_le_of_lt hz.2 p1_lt_pi_sub⟩

/-- The exact symmetry of `Ψ` about `π/2`: `Ψ (π - t) = -Ψ t`. -/
lemma C2Psi_pi_sub (t : ℝ) :
    Work.CNum.C2Psi (Real.pi - t) = -Work.CNum.C2Psi t := by
  rw [Work.CNum.C2Psi, Work.CNum.C2Psi, Real.cos_pi_sub, neg_div, Real.arcsin_neg]
  ring

lemma C2Psi_half_alpR : Work.CNum.C2Psi (Work.CNum.alpR / 2) = Work.CNum.alpR / 2 := by
  rw [Work.CNum.C2Psi, Work.CNum.cos_half_alpR, div_self Work.CNum.C2C_ne_zero,
    Real.arcsin_one]
  ring

lemma C2Psi_half_pi : Work.CNum.C2Psi (Real.pi / 2) = 0 := by
  rw [Work.CNum.C2Psi, Real.cos_pi_div_two, zero_div, Real.arcsin_zero]
  ring

/-- `sin` is at least `sin p0` on `[p0, p1] = [p0, π - p0]`. -/
lemma sin_p0_le {x : ℝ} (hx : x ∈ Set.Icc p0 p1) : Real.sin p0 ≤ Real.sin x := by
  have hx' : x ∈ Set.Icc p0 (Real.pi - p0) := by rw [← p1_eq]; exact hx
  have hp0_mem : p0 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [p0_pos, Real.pi_pos], p0_le_halfpi⟩
  rcases le_total x (Real.pi / 2) with hxle | hxle
  · exact Real.strictMonoOn_sin.monotoneOn hp0_mem
      ⟨by linarith [hx.1, p0_pos, Real.pi_pos], hxle⟩ hx.1
  · have hy_ge : p0 ≤ Real.pi - x := by linarith [hx'.2]
    have hy_le : Real.pi - x ≤ Real.pi / 2 := by linarith [hxle]
    have hsym : Real.sin x = Real.sin (Real.pi - x) := (Real.sin_pi_sub x).symm
    rw [hsym]
    exact Real.strictMonoOn_sin.monotoneOn hp0_mem
      ⟨by linarith [hy_ge, p0_pos, Real.pi_pos], hy_le⟩ hy_ge

lemma C2σ_lt_sin_p0 : Work.CNum.C2σ < Real.sin p0 := by
  have hmem0 : Work.CNum.alpR / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Work.CNum.alpR_pos, Real.pi_pos], by linarith [Work.CNum.alpR_lt_pi]⟩
  have hmemp : p0 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [p0_pos, Real.pi_pos], p0_le_halfpi⟩
  have h := Real.strictMonoOn_sin hmem0 hmemp half_alpR_lt_p0
  rwa [Work.CNum.sin_half_alpR] at h

/-- The `C₂`-arc derivative of `Ψ`, evaluated at `x ∈ [p0, p1]`, is bounded by `300`. -/
lemma slope_bound {x : ℝ} (hx : x ∈ Set.Icc p0 p1) :
    |(1 : ℝ) - Real.sin x / Real.sqrt (Work.CNum.C2C ^ 2 - Real.cos x ^ 2)| ≤ 300 := by
  have hδ := DeltaBound
  have hge : Real.sin p0 ≤ Real.sin x := sin_p0_le hx
  have hsin_p0_pos : 0 < Real.sin p0 := lt_trans Work.CNum.C2σ_pos C2σ_lt_sin_p0
  have hsin_gt : Work.CNum.C2σ < Real.sin x := lt_of_lt_of_le C2σ_lt_sin_p0 hge
  have hge0 : 0 ≤ Real.sin x := le_trans hsin_p0_pos.le hge
  have harg : 0 < Real.sin x ^ 2 - Work.CNum.C2σ ^ 2 := by
    nlinarith [hsin_gt, hge0, Work.CNum.C2σ_pos]
  -- identify `C2C^2 - cos^2 x` with `sin^2 x - σ^2`
  have hid : Work.CNum.C2C ^ 2 - Real.cos x ^ 2 = Real.sin x ^ 2 - Work.CNum.C2σ ^ 2 := by
    rw [← Work.CNum.one_sub_C2σ_sq]
    linarith [Real.sin_sq_add_cos_sq x]
  -- the square root is at least `1/300` on the interval
  have hsqrt_ge : (1 : ℝ) / 300 ≤ Real.sqrt (Real.sin x ^ 2 - Work.CNum.C2σ ^ 2) := by
    have hbase := SinHalfBound hδ
    have hsq : Real.sin p0 ^ 2 - Work.CNum.C2σ ^ 2 ≤
        Real.sin x ^ 2 - Work.CNum.C2σ ^ 2 := by nlinarith [hge, hsin_p0_pos]
    exact le_trans hbase (Real.sqrt_le_sqrt hsq)
  have hwpos : 0 < Real.sqrt (Work.CNum.C2C ^ 2 - Real.cos x ^ 2) := by
    rw [hid]; exact Real.sqrt_pos.mpr harg
  have hw300 : Real.sqrt (Work.CNum.C2C ^ 2 - Real.cos x ^ 2) ≥ (1 : ℝ) / 300 := by
    rw [hid]; exact hsqrt_ge
  have hq_nonneg : 0 ≤ Real.sin x / Real.sqrt (Work.CNum.C2C ^ 2 - Real.cos x ^ 2) :=
    div_nonneg hge0 hwpos.le
  have hq_le : Real.sin x / Real.sqrt (Work.CNum.C2C ^ 2 - Real.cos x ^ 2) ≤ 300 := by
    have h1 : Real.sin x / Real.sqrt (Work.CNum.C2C ^ 2 - Real.cos x ^ 2)
        ≤ 1 / Real.sqrt (Work.CNum.C2C ^ 2 - Real.cos x ^ 2) :=
      div_le_div_of_nonneg_right (Real.sin_le_one x) hwpos.le
    have h2 : 1 / Real.sqrt (Work.CNum.C2C ^ 2 - Real.cos x ^ 2) ≤ 300 := by
      rw [div_le_iff₀ hwpos]
      nlinarith [hw300]
    linarith
  rw [abs_le]
  constructor <;> linarith

lemma diffAt_of_mem {z : ℝ} (hz : z ∈ Set.Icc p0 p1) :
    DifferentiableAt ℝ Work.CNum.C2Psi z :=
  (C2PsiHasDerivAt (mem_Ioo_of_mem_p hz)).differentiableAt

lemma deriv_bound {z : ℝ} (hz : z ∈ Set.Icc p0 p1) :
    ‖deriv Work.CNum.C2Psi z‖ ≤ 300 := by
  rw [(C2PsiHasDerivAt (mem_Ioo_of_mem_p hz)).deriv, Real.norm_eq_abs]
  exact slope_bound hz

theorem PsiSteps : (∀ θ θ' : ℝ, 2 * Real.pi * 245 / 1024 ≤ θ → θ ≤ θ' → θ' ≤ 2 * Real.pi * 779 / 1024 → θ' - θ ≤ 2 * Real.pi / 1024 → Work.CNum.C2Psi (θ / 2) - Work.CNum.C2Psi (θ' / 2) ≤ 1) ∧ (Work.CNum.C2Psi (Work.CNum.alpR / 2) - Work.CNum.C2Psi (2 * Real.pi * 245 / 1024 / 2) ≤ 1) ∧ (Work.CNum.C2Psi (2 * Real.pi * 779 / 1024 / 2) - Work.CNum.C2Psi ((2 * Real.pi - Work.CNum.alpR) / 2) ≤ 1) := by
  have hC2Psi_pos : 0 ≤ Work.CNum.C2Psi p0 := by
    have hA : p0 ∈ Set.Ioo (Work.CNum.alpR / 2) (Real.pi - Work.CNum.alpR / 2) :=
      mem_Ioo_of_mem_p (Set.left_mem_Icc.mpr p0_le_p1)
    have hB : Real.pi / 2 ∈ Set.Ioo (Work.CNum.alpR / 2) (Real.pi - Work.CNum.alpR / 2) :=
      ⟨by linarith [Work.CNum.alpR_lt_pi], by linarith [Work.CNum.alpR_lt_pi]⟩
    have hlt : p0 < Real.pi / 2 := by rw [p0]; nlinarith [Real.pi_pos]
    have h := Work.CNum.C2_Psi_antitone hA hB hlt
    rw [C2Psi_half_pi] at h
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro θ θ' hθ1 hθ2 hθ3 hθ4
    have hx : θ / 2 ∈ Set.Icc p0 p1 := by
      rw [p0, p1]
      constructor <;> linarith [Real.pi_pos]
    have hy : θ' / 2 ∈ Set.Icc p0 p1 := by
      rw [p0, p1]
      constructor <;> linarith [Real.pi_pos]
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => diffAt_of_mem hz) (fun z hz => deriv_bound hz)
      (convex_Icc p0 p1) hx hy
    have hnorm : ‖θ' / 2 - θ / 2‖ = θ' / 2 - θ / 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg]; linarith
    rw [hnorm] at hmvt
    have hstep : 300 * (θ' / 2 - θ / 2) ≤ 1 := by
      have h1 : θ' / 2 - θ / 2 = (θ' - θ) / 2 := by ring
      rw [h1]
      linarith [hθ4, Real.pi_lt_d4]
    have hle : Work.CNum.C2Psi (θ / 2) - Work.CNum.C2Psi (θ' / 2)
        ≤ ‖Work.CNum.C2Psi (θ' / 2) - Work.CNum.C2Psi (θ / 2)‖ := by
      rw [Real.norm_eq_abs]
      have := neg_le_abs (Work.CNum.C2Psi (θ' / 2) - Work.CNum.C2Psi (θ / 2))
      linarith
    linarith
  · have h1 : Work.CNum.C2Psi (Work.CNum.alpR / 2) = Work.CNum.alpR / 2 := C2Psi_half_alpR
    have h2 : Work.CNum.alpR / 2 ≤ 1 := by
      have := Work.CNum.AlpBound.2; linarith
    rw [h1, show 2 * Real.pi * 245 / 1024 / 2 = p0 by rw [p0]; ring]
    linarith
  · have hsym1 : Work.CNum.C2Psi p1 = -Work.CNum.C2Psi p0 := by
      rw [p1_eq]; exact C2Psi_pi_sub p0
    have hsym2 : Work.CNum.C2Psi (Real.pi - Work.CNum.alpR / 2)
        = -Work.CNum.C2Psi (Work.CNum.alpR / 2) := C2Psi_pi_sub (Work.CNum.alpR / 2)
    have h1 : Work.CNum.C2Psi (Work.CNum.alpR / 2) = Work.CNum.alpR / 2 := C2Psi_half_alpR
    have h2 : Work.CNum.alpR / 2 ≤ 1 := by
      have := Work.CNum.AlpBound.2; linarith
    rw [show 2 * Real.pi * 779 / 1024 / 2 = p1 by rw [p1]; ring,
      show (2 * Real.pi - Work.CNum.alpR) / 2 = Real.pi - Work.CNum.alpR / 2 by ring,
      hsym1, hsym2, h1]
    linarith

end

end Work.CNum.DAux
