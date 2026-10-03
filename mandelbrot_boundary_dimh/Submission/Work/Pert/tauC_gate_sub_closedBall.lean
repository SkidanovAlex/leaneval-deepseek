import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.tauC_gate_bound
import Submission.Work.Pert.Basic
import Submission.Work.Pert.norm_alpha_mul_le_one_of_InF1_QAdm

/-!
# PERT · `Work.Pert.tauC_gate_sub_closedBall`

Shishikura (A.1.7)(ii) in its *perturbation-form* shape: on the lower gate `Qm Ξ α` the perturbed
coordinate `τ_f` is bounded by `16π/Ξ`, the bound being derived only from the normal-form data
(`1 - σ u(0) = exp (2πi α)` with `u(0)` bounded below by `1/2`), the class condition `α ∈ 𝓕₁`
(`|Im α| < Re α`) and the admissibility of the gate `Q(Ξ - 1/α, -Ξ)`.

The mathematical content is the constant-`8π` bound `‖σ‖ ≤ 8π‖α‖` for the multiplier `σ`:
`σ u(0) = 1 - exp (2πi α)` gives `‖σ‖ ≤ 2‖1 - exp (2πi α)‖`, and the gate hypothesis
`Re (1/α) > 2Ξ + 4 > 4` together with `InF1 α` forces

  `‖exp (2πi α) - 1‖ ≤ 4π‖α‖`      (`exp_two_pi_mul_I_alpha_sub_one_le`),

which is exactly `‖(exp z - 1)/z‖ ≤ 2` at `z = 2πi α`.  Writing `z = x + iy` (`x = Re z`,
`y = Im z`) and noting `y(1 + (x/y)²) = 2π/Re(1/α) ≤ π/2`, the elementary bound
`‖exp z - 1‖² = (eˣ - 1)² + 2eˣ(1 - cos y) ≤ 4(x² + y²)` follows from
`eˣ - 1 ≤ 2x` (valid for `0 ≤ x ≤ π/4`, the `𝓕₁`-cone pinning `x ≤ (1/2)y(1 + (x/y)²) ≤ π/4`),
`1 - cos y ≤ y²/2` and `eˣ ≤ 4`.  For `x ≤ 0` the sharper `(1 - eˣ)² ≤ x²` is used instead.

The `τ`-bound itself is then `Work.Pert.tauC_gate_bound` (the `ρmin = 10⁶/Ξ` instance of the
lattice-distance analysis), fed with `‖α‖Ξ ≤ 1`, which is also a consequence of the gate
admissibility (`Work.Pert.norm_alpha_mul_le_one_of_InF1_QAdm`).
-/

set_option linter.unusedVariables false

namespace Work.Pert

open MandelDim Complex

noncomputable section

/-- **The `Re`/`Im` expansion of `normSq (exp z - 1)`.**  For every `z`,
`‖exp z - 1‖² = (e^{Re z} - 1)² + 2 e^{Re z} (1 - cos (Im z))`; the two terms measure the
"radial" and the "angular" defect of the exponential. -/
private lemma normSq_exp_sub_one (z : ℂ) : Complex.normSq (Complex.exp z - 1)
    = (Real.exp z.re - 1) ^ 2 + 2 * Real.exp z.re * (1 - Real.cos z.im) := by
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.exp_re, Complex.exp_im]
  simp only [sub_zero]
  have htrig : Real.cos z.im ^ 2 + Real.sin z.im ^ 2 = 1 := Real.cos_sq_add_sin_sq z.im
  have key : (Real.exp z.re * Real.cos z.im - 1) * (Real.exp z.re * Real.cos z.im - 1)
      + (Real.exp z.re * Real.sin z.im) * (Real.exp z.re * Real.sin z.im)
      = Real.exp z.re ^ 2 * (Real.cos z.im ^ 2 + Real.sin z.im ^ 2)
        - 2 * Real.exp z.re * Real.cos z.im + 1 := by ring
  rw [key, htrig]
  ring

/-- The Taylor bound `eˣ ≤ 1 + 2x` on `[0,1]` (three terms of the exponential series). -/
private lemma exp_le_one_add_two_mul {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + 2 * x := by
  have h := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  nlinarith [h, sq_nonneg (x - 1), sq_nonneg x, h0, h1]

/-- **`‖(exp z - 1)/z‖ ≤ 2` in the gate cone.**  If `y = Im z > 0` and
`y (1 + (Re z / y)²) ≤ π/2` (equivalently `Re z ≤ π/4` and `|Re z| ≤ y`-type constraints
coming from `α ∈ 𝓕₁`), then `‖exp z - 1‖ ≤ 2‖z‖`. -/
private lemma norm_exp_le_two_norm {x y : ℝ} (hy : 0 < y)
    (hcon : y * (1 + (x / y) ^ 2) ≤ Real.pi / 2) :
    ‖Complex.exp ((x : ℂ) + (y : ℂ) * Complex.I) - 1‖
      ≤ 2 * ‖((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hz
  have hzre : z.re = x := by simp [hz]
  have hzim : z.im = y := by simp [hz]
  have hnormSqz : Complex.normSq z = x ^ 2 + y ^ 2 := by
    rw [Complex.normSq_apply, hzre, hzim]; ring
  have hkey := normSq_exp_sub_one z
  rw [hzre, hzim] at hkey
  have hcosle : 1 - Real.cos y ≤ y ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := y); linarith
  have hcos1 : Real.cos y ≤ 1 := Real.cos_le_one y
  have hbound : Complex.normSq (Complex.exp z - 1) ≤ 4 * Complex.normSq z := by
    rw [hkey, hnormSqz]
    by_cases hx : 0 ≤ x
    · -- `0 ≤ x`: here `x ≤ π/4`, so `eˣ ≤ 1 + 2x ≤ 4`.
      have hx_le : x ≤ Real.pi / 4 := by
        have ht : x = (x / y) * y := by field_simp
        have h2t : 2 * (x / y) ≤ 1 + (x / y) ^ 2 := by nlinarith [sq_nonneg (x / y - 1)]
        have hmul : (y / 2) * (2 * (x / y)) ≤ (y / 2) * (1 + (x / y) ^ 2) :=
          mul_le_mul_of_nonneg_left h2t (by linarith)
        have h1 : x ≤ (y / 2) * (1 + (x / y) ^ 2) := by
          calc x = (x / y) * y := ht
            _ = (y / 2) * (2 * (x / y)) := by ring
            _ ≤ (y / 2) * (1 + (x / y) ^ 2) := hmul
        have h2 : (y / 2) * (1 + (x / y) ^ 2) ≤ Real.pi / 4 := by linarith [hcon]
        linarith
      have hx1 : x ≤ 1 := by linarith [Real.pi_lt_four]
      have he1 : Real.exp x ≤ 1 + 2 * x := exp_le_one_add_two_mul hx hx1
      have he4 : Real.exp x ≤ 4 := by
        have h4 : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
        linarith [Real.exp_one_lt_three, h4]
      have hpos : 0 < Real.exp x := Real.exp_pos x
      have hge : 0 ≤ Real.exp x - 1 := by
        have := Real.add_one_le_exp x
        linarith
      have hA : (Real.exp x - 1) ^ 2 ≤ 4 * x ^ 2 := by nlinarith [he1, hpos, hge, hx]
      have hB : 2 * Real.exp x * (1 - Real.cos y) ≤ 4 * y ^ 2 := by
        nlinarith [hcosle, hcos1, he4, hpos]
      linarith
    · -- `x < 0`: here `(1 - eˣ)² ≤ x²` and `eˣ ≤ 1`.
      have hxlt : x < 0 := lt_of_not_ge hx
      have he1 : Real.exp x ≤ 1 := by
        have h := Real.exp_le_exp.mpr hxlt.le
        simpa using h
      have hone : 1 - Real.exp x ≤ -x := by
        have h := Real.add_one_le_exp x
        linarith
      have hA : (Real.exp x - 1) ^ 2 ≤ x ^ 2 := by nlinarith [hone]
      have hB : 2 * Real.exp x * (1 - Real.cos y) ≤ y ^ 2 := by
        nlinarith [hcosle, hcos1, he1, Real.exp_pos x]
      nlinarith [hA, hB, sq_nonneg y]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hbound
  have hsq : ‖Complex.exp z - 1‖ ^ 2 ≤ (2 * ‖z‖) ^ 2 := by rw [mul_pow]; linarith
  have h2 := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h2

/-- **`‖exp (2πi α) - 1‖ ≤ 4π‖α‖` on the gate cone.**  `α ∈ 𝓕₁` puts `α` in the cone
`|Im α| < Re α`, and `Re (1/α) > 4` says `‖α‖² < Re α / 4`; at `z = 2πi α` this is precisely
`y(1 + (x/y)²) = 2π/Re(1/α) < π/2` for `x = Re z`, `y = Im z`. -/
private lemma exp_two_pi_mul_I_alpha_sub_one_le {α : ℂ} (hF1 : MandelDim.InF1 α)
    (hre : 4 < (1 / α).re) :
    ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖ ≤ 4 * Real.pi * ‖α‖ := by
  have ha : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hF1
  have hne : α ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hnspos : 0 < Complex.normSq α := Complex.normSq_pos.mpr hne
  have hns : Complex.normSq α = α.re ^ 2 + α.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have hinv : (1 / α).re = α.re / Complex.normSq α := by rw [one_div, Complex.inv_re]
  have h4 : 4 * Complex.normSq α < α.re := by
    rw [hinv] at hre
    rw [lt_div_iff₀ hnspos] at hre
    linarith
  have hquarter : Complex.normSq α / α.re ≤ 1 / 4 := by
    rw [div_le_iff₀ ha]; linarith
  set x : ℝ := -2 * Real.pi * α.im with hxdef
  set y : ℝ := 2 * Real.pi * α.re with hydef
  have hy : 0 < y := by rw [hydef]; positivity
  have hcon : y * (1 + (x / y) ^ 2) ≤ Real.pi / 2 := by
    have hxy' : x / y = -α.im / α.re := by
      rw [hxdef, hydef]
      field_simp
    rw [hxy', hydef]
    have hcomp : 2 * Real.pi * α.re * (1 + (-α.im / α.re) ^ 2)
        = 2 * Real.pi * (Complex.normSq α / α.re) := by
      rw [hns]
      field_simp
    rw [hcomp]
    nlinarith [hquarter, Real.pi_pos]
  have hmain := norm_exp_le_two_norm hy hcon
  have hz : ((x : ℂ) + (y : ℂ) * Complex.I) = 2 * Real.pi * Complex.I * α := by
    rw [hxdef, hydef]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_re, Complex.add_im]
  have hznorm : ‖((x : ℂ) + (y : ℂ) * Complex.I)‖ = 2 * Real.pi * ‖α‖ := by
    rw [hz, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  calc ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖
      = ‖Complex.exp ((x : ℂ) + (y : ℂ) * Complex.I) - 1‖ := by rw [hz]
    _ ≤ 2 * ‖((x : ℂ) + (y : ℂ) * Complex.I)‖ := hmain
    _ = 2 * (2 * Real.pi * ‖α‖) := by rw [hznorm]
    _ = 4 * Real.pi * ‖α‖ := by ring

/-- **The multiplier bound `‖σ‖ ≤ 8π‖α‖`** from the normal-form equation `1 - σ u(0) = e^{2πi α}`
and `‖u(0)‖ ≥ 1/2`. -/
private lemma sigma_le_eight_pi_norm {u : ℂ → ℂ} {σ α : ℂ} (hu0 : 1 / 2 ≤ ‖u 0‖)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hexp : ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖ ≤ 4 * Real.pi * ‖α‖) :
    ‖σ‖ ≤ 8 * Real.pi * ‖α‖ := by
  have hσu : σ * u 0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
    rw [← hnorm]; ring
  have h1 : ‖σ‖ * ‖u 0‖ = ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
    rw [← norm_mul, hσu]
  have h2 : ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ ≤ 4 * Real.pi * ‖α‖ := by
    rw [norm_sub_rev]; exact hexp
  have hu0pos : 0 < ‖u 0‖ := by linarith
  have hle : 1 / ‖u 0‖ ≤ 2 := by rw [div_le_iff₀ hu0pos]; linarith
  calc ‖σ‖ = ‖σ‖ * ‖u 0‖ / ‖u 0‖ := (mul_div_cancel_right₀ ‖σ‖ (ne_of_gt hu0pos)).symm
    _ = ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ / ‖u 0‖ := by rw [h1]
    _ ≤ (4 * Real.pi * ‖α‖) / ‖u 0‖ := div_le_div_of_nonneg_right h2 hu0pos.le
    _ = 4 * Real.pi * ‖α‖ * (1 / ‖u 0‖) := by rw [div_eq_mul_one_div]
    _ ≤ 4 * Real.pi * ‖α‖ * 2 := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 8 * Real.pi * ‖α‖ := by ring

/-- **PERT gate bound in perturbation form.**  For a perturbation whose normal-form data
`(σ, α)` satisfy `1 - σ u(0) = exp (2πi α)` with `u(0)` bounded below by `1/2`, with `α ∈ 𝓕₁` and
with the lower gate `Q(Ξ - 1/α, -Ξ)` admissible, the perturbed coordinate `τ_f` is bounded by
`16π/Ξ` on that gate. -/
theorem tauC_gate_sub_closedBall {Ξ : ℝ} (hΞ : 0 < Ξ) {rr : ℝ} (hrr : 0 < rr)
    {u : ℂ → ℂ} {σ α : ℂ}
    (hudiff : DifferentiableOn ℂ u (Metric.ball 0 rr))
    (hu : ∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hinf : MandelDim.InF1 α)
    (hadm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))) :
    ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.closedBall (0 : ℂ) (16 * Real.pi / Ξ) := by
  -- the gate admissibility supplies `Re (1/α) > 2Ξ + 4 > 4`
  have hre4 : 4 < (1 / α).re := by
    have h := two_mul_add_four_lt_inv_re hadm
    linarith
  -- `‖u 0‖ ≥ 1/2`
  have hu0 : 1 / 2 ≤ ‖u 0‖ := (hu 0 (by rw [Metric.mem_ball]; simpa using hrr)).1
  -- the multiplier bound `‖σ‖ ≤ 8π‖α‖`
  have hσ : ‖σ‖ ≤ 8 * Real.pi * ‖α‖ :=
    sigma_le_eight_pi_norm hu0 hnorm (exp_two_pi_mul_I_alpha_sub_one_le hinf hre4)
  -- smallness of `α`: `‖α‖ Ξ ≤ 1`
  have hsmall : ‖α‖ * Ξ ≤ 1 := norm_alpha_mul_le_one_of_InF1_QAdm hΞ hinf hadm
  intro z hz
  have hb := tauC_gate_bound (α := α) (σ := σ) hΞ hinf hσ hsmall z hz
  simpa [Metric.mem_closedBall, dist_eq_norm] using hb

end

end Work.Pert
