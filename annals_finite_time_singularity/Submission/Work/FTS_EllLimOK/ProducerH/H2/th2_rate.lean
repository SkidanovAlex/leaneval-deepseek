import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCSinRate
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgRate
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Dev.slice_deriv_bound
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.slice_package_bounds
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDerivDz.second_theta_deriv_DzIter_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Stability.mul_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK/ProducerH/H2/th2_rate` — the endpoint rate of `∂_θ²(E g)`

The target is the *uniform modulus* of the angular second derivative of the stream function
produced by the L3 producer:

  `∃ K β > 0, ∀ g ∈ ClassC, ∀ z ∈ [a₀,b₀], ∀ θ ∈ (0,π/2),
      |∂_θ²(E g)(z,θ)| ≤ K · Xn6 α g · (min θ (π/2-θ))^β`

## Proof structure

Write `S θ = (E g) z θ` (a slice of the stream function) and `G = Lzero (E g) z`, so that on
`(0,π/2)`

  `S'' = tan θ · S' + (cos θ)^{-2} · S − 6 S − G`     (`Dev.slice_data`).

The available uniform inputs are

* `|S''| ≤ M₁ Xn6` (`SecondDeriv.second_theta_deriv_le_Xn6`),
* `|S| ≤ M Xn6`, `|(sin 2θ)/2) S' + S| ≤ M Xn6`, `|G| ≤ M Xn6`
  (`SecondDeriv.slice_package_bounds`),
* `|G| ≤ C₀ Xn6 (min θ (π/2−θ))^β` with `β = α/20 = (γ−1)/2` (`BoxAux.lzero_rate`),
* `|S'| ≤ C₂ Xn6`, `|S| ≤ C₂ Xn6 θ`, `|S| ≤ C₂ Xn6 (π/2−θ)` (`Dev.slice_deriv_bound`).

Then, for `θ ≤ π/4` (where `min θ (π/2−θ) = θ`), every term of the ODE is `O(θ^β)`:
`tan θ ≤ 2θ`, `(cos θ)^{-2} ≤ 2`, `S = O(θ)`, `G = O(θ^β)` — this is `end_rate_zero` below.

For `θ > π/4` (where `min θ (π/2−θ) = π/2 − θ`) the `tan θ S'` and `(cos θ)^{-2} S` terms are
singular separately and have to be combined; the Φ-identity of `BoxAux.th2Ident`,
`(cos θ)^3 (S'' + 4S + G) = ∫_θ^{π/2} sin t cos²t G t`, turns the bound into the integral
estimate `BoxAux.cos_inv_cube_mul_integral_le`, giving again the rate `β` — this is
`Dev.end_rate_pi_half`.

Both ends produce `β = α/20 > 0`, and the two constants are merged.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Elementary helpers -/

/-- `|a + b - c - d| ≤ |a| + |b| + |c| + |d|`. -/
theorem abs_add_sub_sub_le (a b c d : ℝ) : |a + b - c - d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a + b - c - d| ≤ |a + b| + |c + d| := by
    have he : a + b - c - d = (a + b) - (c + d) := by ring
    rw [he]; exact abs_sub _ _
  have h2 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  have h3 : |c + d| ≤ |c| + |d| := abs_add_le _ _
  linarith

/-- `|a + b + c| ≤ |a| + |b| + |c|`. -/
theorem abs_add_add_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h2 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-- `θ ≤ θ^β` for `0 < θ ≤ 1`, `β ≤ 1`. -/
theorem self_le_rpow {θ β : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hβ1 : β ≤ 1) : θ ≤ θ ^ β := by
  calc θ = θ ^ (1:ℝ) := (Real.rpow_one θ).symm
    _ ≤ θ ^ β := Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1 hβ1

/-- `tan θ ≤ 2θ` on `(0, π/4]` (via `sin θ ≤ θ` and `cos θ ≥ √2/2 ≥ 1/2`). -/
theorem tan_le_two_mul {θ : ℝ} (hθ0 : 0 < θ) (hθ4 : θ ≤ Real.pi/4) :
    Real.tan θ ≤ 2 * θ := by
  have hθ2 : θ < Real.pi/2 := by linarith [hθ4, Real.pi_pos]
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩
  have hcos_ge : Real.sqrt 2 / 2 ≤ Real.cos θ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := Real.pi/4) hθ0.le
      (by linarith [Real.pi_pos, hθ4]) hθ4
    rwa [Real.cos_pi_div_four] at h
  have hc : 1 ≤ 2 * Real.cos θ := by
    have h1 : (1:ℝ) ≤ Real.sqrt 2 := by
      have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
      nlinarith [Real.sqrt_nonneg 2, h2]
    linarith
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcos_pos]
  have hs := Real.sin_le hθ0.le
  nlinarith [hs, hc, hθ0]

/-- **The `θ → 0⁺` end game.**  If the angular slice solves the slice ODE on `(0,π/2)` and
`|S| ≤ M θ`, `|S'| ≤ N`, `|G| ≤ C θ^β` at the point `θ ∈ (0,π/4]`, then `|S''| ≤ (2N+8M+C) θ^β`
there: the singular-looking terms `tan θ S'` and `(cos θ)^{-2} S` are both `O(θ)`. -/
theorem end_rate_zero {S G : ℝ → ℝ} {β C M N θ : ℝ}
    (hβ1 : β ≤ 1) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hθ : θ ∈ Set.Ioc (0:ℝ) (Real.pi/4))
    (hode : deriv (deriv S) θ = Real.tan θ * deriv S θ + ((Real.cos θ)^2)⁻¹ * S θ - 6 * S θ - G θ)
    (hSb : |S θ| ≤ M * θ) (hDb : |deriv S θ| ≤ N) (hGr : |G θ| ≤ C * θ ^ β) :
    |deriv (deriv S) θ| ≤ (2*N + 8*M + C) * θ ^ β := by
  have hθ0 : 0 < θ := hθ.1
  have hθ4 : θ ≤ Real.pi/4 := hθ.2
  have hθ2 : θ < Real.pi/2 := by linarith [hθ4, Real.pi_pos]
  have hθ1 : θ ≤ 1 := by nlinarith [Real.pi_lt_four]
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩
  have htan_nonneg : 0 ≤ Real.tan θ := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg (Real.sin_nonneg_of_mem_Icc ⟨hθ0.le, by linarith⟩) hcos_pos.le
  have htan : Real.tan θ ≤ 2 * θ := tan_le_two_mul hθ0 hθ4
  have hcos_sq_inv : ((Real.cos θ)^2)⁻¹ ≤ 2 := by
    have hcos_ge : Real.sqrt 2 / 2 ≤ Real.cos θ := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := Real.pi/4) hθ0.le
        (by linarith [Real.pi_pos, hθ4]) hθ4
      rwa [Real.cos_pi_div_four] at h
    have h2 : (Real.sqrt 2 / 2)^2 ≤ (Real.cos θ)^2 := by
      apply pow_le_pow_left₀ (by positivity); exact hcos_ge
    have h3 : (Real.sqrt 2 / 2)^2 = 1/2 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    rw [inv_le_iff_one_le_mul₀ (pow_pos hcos_pos 2)]
    nlinarith [h2, h3]
  have hA : |Real.tan θ * deriv S θ| ≤ 2 * θ * N := by
    rw [abs_mul, abs_of_nonneg htan_nonneg]
    nlinarith [hDb, htan, hθ0, hN]
  have hB : |((Real.cos θ)^2)⁻¹ * S θ| ≤ 2 * (M * θ) := by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    nlinarith [hSb, hcos_sq_inv, mul_nonneg hM hθ0.le, abs_nonneg (S θ)]
  have hD : |6 * S θ| ≤ 6 * (M * θ) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6)]
    nlinarith [hSb, hM, hθ0]
  have hmain : |deriv (deriv S) θ| ≤ 2*θ*N + 2*(M*θ) + 6*(M*θ) + C*θ^β := by
    rw [hode]
    calc |Real.tan θ * deriv S θ + ((Real.cos θ)^2)⁻¹ * S θ - 6 * S θ - G θ|
        ≤ |Real.tan θ * deriv S θ| + |((Real.cos θ)^2)⁻¹ * S θ| + |6 * S θ| + |G θ| :=
          abs_add_sub_sub_le _ _ _ _
      _ ≤ 2*θ*N + 2*(M*θ) + 6*(M*θ) + C*θ^β := by linarith
  have hθβ : 0 ≤ θ ^ β := Real.rpow_nonneg hθ0.le β
  have hθε : θ ≤ θ ^ β := self_le_rpow hθ0 hθ1 hβ1
  have h1 : 2 * θ * N ≤ 2 * N * θ ^ β := by nlinarith [hθβ, hθε, hN]
  have h2 : 2 * (M*θ) ≤ 2 * M * θ ^ β := by nlinarith [hθβ, hθε, hM]
  have h3 : 6 * (M*θ) ≤ 6 * M * θ ^ β := by nlinarith [hθβ, hθε, hM]
  linarith [hmain, h1, h2, h3]

/-! ## The target -/

theorem th2_rate {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀) :
    ∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |deriv (deriv (fun θ' => (E g) z θ')) θ|
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g * (min θ (Real.pi / 2 - θ)) ^ β := by
  obtain ⟨M₁, hM₁pos, hM₁⟩ :=
    Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6 hα hα4 hE ha₀ hab
  obtain ⟨M, hMpos, hM⟩ :=
    Work.FTS_EllLimOK.ProducerH.SecondDeriv.slice_package_bounds hα hα4 hE ha₀ hab
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Work.FTS_EllLimOK.ProducerH.BoxAux.lzero_rate hα hα4 hE ha₀ hab
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Dev.slice_deriv_bound hα hα4 hE ha₀ hab
  have hβeq : (Work.Spaces.gam α - 1) / 2 = α / 20 := by
    rw [Work.Spaces.gam_sub_one]; ring
  have hβ0 : (0:ℝ) < α / 20 := by linarith
  have hβ1 : α / 20 ≤ 1 := by linarith
  refine ⟨10 * C₂ + C₀ + (100 * (C₀ + C₂) + 1), by positivity, α / 20, hβ0, ?_⟩
  intro g hg z hz θ hθ
  have hzpos : 0 < z := lt_of_lt_of_le ha₀ hz.1
  have hX0 : (0 : ℝ) ≤ Work.FTS.StrongGlobal.Xn6 α g := Xn6_nonneg α g
  obtain ⟨hS2, hGc, hode⟩ := Dev.slice_data hα hα4 hE hg hzpos
  obtain ⟨hD1, hS1, hS1'⟩ := hC₂ g hg z hz
  have hD2 : ∀ θ' ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      |deriv (deriv (fun θ'' => (E g) z θ'')) θ'| ≤ M₁ * Work.FTS.StrongGlobal.Xn6 α g :=
    fun θ' hθ' => hM₁ g hg z hz θ' hθ'
  have hGh : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      |Work.Elliptic.Lzero (E g) z t| ≤ C₀ * Work.FTS.StrongGlobal.Xn6 α g := by
    intro t ht
    have h := hC₀ g hg z hz t ht
    rw [hβeq] at h
    have hmm1 : min t (Real.pi/2 - t) ≤ 1 := by
      rcases le_total t (Real.pi/2 - t) with hc | hc
      · rw [min_eq_left hc]; nlinarith [ht.2, Real.pi_lt_four]
      · rw [min_eq_right hc]; nlinarith [Real.pi_lt_four]
    have hmm0 : 0 ≤ min t (Real.pi/2 - t) := le_of_lt (lt_min ht.1 (by linarith [ht.2]))
    have hr : (min t (Real.pi/2 - t)) ^ (α/20) ≤ 1 := Real.rpow_le_one hmm0 hmm1 hβ0.le
    have hX : (0:ℝ) ≤ C₀ * Work.FTS.StrongGlobal.Xn6 α g := mul_nonneg hC₀pos.le hX0
    calc |Work.Elliptic.Lzero (E g) z t|
        ≤ C₀ * Work.FTS.StrongGlobal.Xn6 α g * (min t (Real.pi/2 - t)) ^ (α/20) := h
      _ ≤ C₀ * Work.FTS.StrongGlobal.Xn6 α g * 1 :=
          mul_le_mul_of_nonneg_left hr hX
      _ = C₀ * Work.FTS.StrongGlobal.Xn6 α g := by ring
  have hGr : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      |Work.Elliptic.Lzero (E g) z t| ≤ C₀ * Work.FTS.StrongGlobal.Xn6 α g
        * (Real.pi / 2 - t) ^ (α/20) := by
    intro t ht
    have h := hC₀ g hg z hz t ht
    rw [hβeq] at h
    have hmm0 : 0 ≤ min t (Real.pi/2 - t) := le_of_lt (lt_min ht.1 (by linarith [ht.2]))
    have hle : min t (Real.pi/2 - t) ≤ Real.pi/2 - t := min_le_right _ _
    have hr : (min t (Real.pi/2 - t)) ^ (α/20) ≤ (Real.pi/2 - t) ^ (α/20) :=
      Real.rpow_le_rpow hmm0 hle hβ0.le
    have hX : (0:ℝ) ≤ C₀ * Work.FTS.StrongGlobal.Xn6 α g := mul_nonneg hC₀pos.le hX0
    exact le_trans h (mul_le_mul_of_nonneg_left hr hX)
  have hWb : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      |deriv (deriv (fun θ' => (E g) z θ')) t + 4 * (E g) z t + Work.Elliptic.Lzero (E g) z t|
        ≤ (M₁ + 4 * M + M) * Work.FTS.StrongGlobal.Xn6 α g := by
    intro t ht
    have h1 : |deriv (deriv (fun θ' => (E g) z θ')) t| ≤ M₁ * Work.FTS.StrongGlobal.Xn6 α g :=
      hD2 t ht
    have h2 : |(E g) z t| ≤ M * Work.FTS.StrongGlobal.Xn6 α g := (hM g hg z hz t ht).1
    have h3 : |Work.Elliptic.Lzero (E g) z t| ≤ M * Work.FTS.StrongGlobal.Xn6 α g :=
      (hM g hg z hz t ht).2.2
    have h4 : |(4:ℝ) * (E g) z t| ≤ 4 * (M * Work.FTS.StrongGlobal.Xn6 α g) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    calc |deriv (deriv (fun θ' => (E g) z θ')) t + 4 * (E g) z t + Work.Elliptic.Lzero (E g) z t|
        ≤ |deriv (deriv (fun θ' => (E g) z θ')) t| + |4 * (E g) z t|
          + |Work.Elliptic.Lzero (E g) z t| := abs_add_add_le _ _ _
      _ ≤ (M₁ + 4 * M + M) * Work.FTS.StrongGlobal.Xn6 α g := by
          nlinarith [h1, h4, h3, hX0, hM, hM₁pos.le]
  by_cases hcase : θ ≤ Real.pi / 4
  · -- the `θ → 0` end: `min θ (π/2 - θ) = θ`
    have hmin : min θ (Real.pi / 2 - θ) = θ := min_eq_left (by linarith)
    rw [hmin]
    have hGrθ : |Work.Elliptic.Lzero (E g) z θ| ≤ C₀ * Work.FTS.StrongGlobal.Xn6 α g
        * θ ^ (α/20) := by
      have h := hC₀ g hg z hz θ hθ
      rw [hβeq, min_eq_left (by linarith)] at h
      exact h
    have h := end_rate_zero (S := fun θ' => (E g) z θ') (G := Work.Elliptic.Lzero (E g) z)
      (β := α/20) (C := C₀ * Work.FTS.StrongGlobal.Xn6 α g)
      (M := C₂ * Work.FTS.StrongGlobal.Xn6 α g) (N := C₂ * Work.FTS.StrongGlobal.Xn6 α g)
      hβ1 (mul_nonneg hC₂pos.le hX0) (mul_nonneg hC₂pos.le hX0)
      ⟨hθ.1, hcase⟩ (hode θ hθ) (hS1 θ hθ) (hD1 θ hθ) hGrθ
    have hK : (2 * (C₂ * Work.FTS.StrongGlobal.Xn6 α g) + 8 * (C₂ * Work.FTS.StrongGlobal.Xn6 α g)
        + C₀ * Work.FTS.StrongGlobal.Xn6 α g)
        ≤ (10 * C₂ + C₀ + (100 * (C₀ + C₂) + 1)) * Work.FTS.StrongGlobal.Xn6 α g := by
      nlinarith [hX0, hC₀pos, hC₂pos]
    calc |deriv (deriv (fun θ' => (E g) z θ')) θ|
        ≤ (2 * (C₂ * Work.FTS.StrongGlobal.Xn6 α g) + 8 * (C₂ * Work.FTS.StrongGlobal.Xn6 α g)
            + C₀ * Work.FTS.StrongGlobal.Xn6 α g) * θ ^ (α/20) := h
      _ ≤ ((10 * C₂ + C₀ + (100 * (C₀ + C₂) + 1)) * Work.FTS.StrongGlobal.Xn6 α g)
            * θ ^ (α/20) :=
          mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hθ.1.le _)
  · -- the `π/2` end: `min θ (π/2 - θ) = π/2 - θ`
    have hcase' : Real.pi / 4 < θ := not_le.mp hcase
    have hmin : min θ (Real.pi / 2 - θ) = Real.pi / 2 - θ := min_eq_right (by linarith)
    rw [hmin]
    have h := Dev.end_rate_pi_half (S := fun θ' => (E g) z θ') (G := Work.Elliptic.Lzero (E g) z)
      (β := α/20) (MG := C₀ * Work.FTS.StrongGlobal.Xn6 α g)
      (CS := C₂ * Work.FTS.StrongGlobal.Xn6 α g)
      (MW := (M₁ + 4 * M + M) * Work.FTS.StrongGlobal.Xn6 α g)
      hβ0 hβ1 (mul_nonneg hC₀pos.le hX0) (mul_nonneg hC₂pos.le hX0)
      hS2 hGc (fun t ht => hGh t ht) hode (fun t ht => hWb t ht)
      (fun t ht => hGr t ht) (fun t ht => hS1' t ht) θ ⟨hcase', hθ.2⟩
    have hK : (100 * (C₀ * Work.FTS.StrongGlobal.Xn6 α g
          + C₂ * Work.FTS.StrongGlobal.Xn6 α g))
        ≤ (10 * C₂ + C₀ + (100 * (C₀ + C₂) + 1)) * Work.FTS.StrongGlobal.Xn6 α g := by
      nlinarith [hX0, hC₀pos, hC₂pos]
    calc |deriv (deriv (fun θ' => (E g) z θ')) θ|
        ≤ (100 * (C₀ * Work.FTS.StrongGlobal.Xn6 α g
            + C₂ * Work.FTS.StrongGlobal.Xn6 α g)) * (Real.pi / 2 - θ) ^ (α/20) := h
      _ ≤ ((10 * C₂ + C₀ + (100 * (C₀ + C₂) + 1)) * Work.FTS.StrongGlobal.Xn6 α g)
            * (Real.pi / 2 - θ) ^ (α/20) :=
          mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (by linarith [hθ.2]) _)

end Work.FTS_EllLimOK.ProducerH.H2
