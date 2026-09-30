import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.mrlas.Psi2_defs
import Submission.Work.BMF.mrlas.Psi2_assembly
import Submission.Work.BMF.mrlas.T_p_bound
import Submission.Work.BMF.mrlas.summable_Psi_series
import Submission.Work.BMF.mrlas.primes_log_summable
import Submission.Work.BMF.mrlas.gp_eq_geom_powerseries
import Submission.Work.BMF.mrlas.differentiableOn_gp
import Submission.Work.BMF.mrlas.powerSeries_circle_inv_L2
import Submission.Work.BMF.mrlas.periodic_window_integral_le
import Submission.Work.BMF.mrlas.resonance_arith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `L²` window bound for `Ψ₂ = Ψ - Ψ₁` on the line `Re s = 1+α`

This is a *self-contained* replacement for `Work.BMF.mrlas.Psi2_L2_bound`, whose dependency
`Work.BMF.mrlas.resonance_integral` is a stub containing a `sorry`.  Everything used here is
proved inside this file or in sorry-free leaf modules.

The two ingredients are

* the pointwise bound `‖Ψ₂ f s‖ ≤ 16 (log 2) ‖(gp f 2 s)⁻¹‖ + 32 K` on `Re s > 1`
  (`Work.BMF.mrlas.Psi2_pointwise_of`, assembled from `T_p_bound`, `summable_Psi_series` and
  `primes_log_summable`), and
* the resonance estimate `∫_c^{c+1} ‖(gp f 2 (1+α+iτ))⁻¹‖² dτ ≤ C/α` for `0 < α ≤ 1`,
  reproved below (`cdiv_resonance_integral`).

Combining the two with `Work.BMF.mrlas.Psi2_integral_bound_of` gives the stated bound.
-/

namespace Work.BMF.mrlas

open Finset Real Complex MeasureTheory intervalIntegral
open scoped BigOperators

noncomputable section

open MeasureTheory intervalIntegral
open scoped BigOperators



/-- **Periodic-window reduction.** If `g` is a nonnegative, continuous, `2π`-periodic function and
`h τ = g (-log 2 · τ)`, then the integral of `h` over any unit window is at most `1/log 2` times
the integral of `g` over one period.  (The `τ`-parametrisation `τ ↦ -log 2 · τ` sweeps one period
of `g` over an interval of length `2π/log 2 > 1`.) -/
lemma cdiv_window_le {g h : ℝ → ℝ} {c : ℝ}
    (hper : Function.Periodic g (2 * Real.pi)) (hcont : Continuous g) (hnn : ∀ x, 0 ≤ g x)
    (heq : ∀ τ : ℝ, h τ = g ((-Real.log 2) * τ)) :
    (∫ τ in c..(c+1), h τ) ≤ (1 / Real.log 2) * (∫ θ in (0)..(2 * Real.pi), g θ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsub : (∫ τ in c..(c+1), h τ)
      = (1 / Real.log 2) * (∫ θ in ((-(c+1)) * Real.log 2)..((-c) * Real.log 2), g θ) := by
    rw [intervalIntegral.integral_congr (fun τ _ => heq τ)]
    rw [intervalIntegral.integral_comp_mul_left g (by linarith : (-Real.log 2) ≠ 0)]
    have h1 : (-Real.log 2) * c = (-c) * Real.log 2 := by ring
    have h2 : (-Real.log 2) * (c + 1) = (-(c+1)) * Real.log 2 := by ring
    rw [h1, h2, intervalIntegral.integral_symm]
    simp only [smul_eq_mul, inv_neg, neg_mul, mul_neg, neg_neg]
    field_simp
  rw [hsub]
  have hp : (0:ℝ) < 2 * Real.pi := by positivity
  have hL0 : (0:ℝ) ≤ Real.log 2 := hlog.le
  have hLp : Real.log 2 ≤ 2 * Real.pi := by
    have := Real.log_two_lt_d9; linarith [Real.pi_gt_three]
  have hwin := periodic_window_integral_le hp hper hnn hL0 hLp hcont (a := (-(c+1)) * Real.log 2)
  have harg : (-(c+1)) * Real.log 2 + Real.log 2 = (-c) * Real.log 2 := by ring
  rw [harg] at hwin
  exact mul_le_mul_of_nonneg_left hwin (by positivity)

/-- The pointwise identification of `gp f 2` on the line `Re s = 1+α` with the power series in
`z = 2^{-(1+α)} e^{iθ}`: `gp f 2 (1+α - iθ/log 2) = Σ_e f(2^e) (2^{-(1+α)} e^{iθ})^e`. -/
lemma cdiv_gp_eq_circle_series (f : ℕ → ℂ) (α : ℝ) :
    ∀ θ : ℝ, Work.BMF.gp f 2 ((((1+α:ℝ)):ℂ) + ((((-θ/Real.log 2:ℝ)):ℂ)) * Complex.I)
      = ∑' e : ℕ, f (2^e) * ((((2:ℝ)^(-(1+α)) : ℝ) : ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^e := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  intro θ
  rw [gp_eq_geom_powerseries f (1+α) (-θ/Real.log 2)]
  apply tsum_congr
  intro e
  have hX : (-((-θ/Real.log 2) * Real.log 2)) = θ := by field_simp
  rw [hX]

/-- The circle sum `θ ↦ Σ_e f(2^e) (2^{-(1+α)} e^{iθ})^e` is `2π`-periodic in `θ`. -/
lemma cdiv_circle_series_periodic (f : ℕ → ℂ) (α : ℝ) :
    ∀ θ : ℝ, (∑' e : ℕ, f (2^e) * ((((2:ℝ)^(-(1+α)) : ℝ) : ℂ) * Complex.exp (((θ + 2*Real.pi : ℝ):ℂ) * Complex.I))^e)
      = ∑' e : ℕ, f (2^e) * ((((2:ℝ)^(-(1+α)) : ℝ) : ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^e := by
  intro θ
  apply tsum_congr
  intro e
  have hX : Complex.exp (((θ + 2*Real.pi : ℝ):ℂ) * Complex.I) = Complex.exp ((θ:ℂ) * Complex.I) := by
    have harg : ((θ + 2*Real.pi : ℝ):ℂ) * Complex.I = (θ:ℂ)*Complex.I + (2*Real.pi:ℂ)*Complex.I := by push_cast; ring
    rw [harg, Complex.exp_add]
    have h2 : Complex.exp ((2*Real.pi:ℂ)*Complex.I) = 1 := by
      rw [show (2*Real.pi:ℂ)*Complex.I = 2 * (Real.pi:ℂ) * Complex.I by ring]
      exact Complex.exp_two_pi_mul_I
    rw [h2, mul_one]
  rw [hX]

/-- `gp f 2` does not vanish on the half-plane `Re s > 1` for bounded `f` with `f 1 = 1`:
the tail of the local power series has modulus `≤ 2^{-σ}/(1-2^{-σ}) < 1`. -/
lemma cdiv_gp_ne_zero_line (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {s : ℂ} (hσ : 1 < s.re) : Work.BMF.gp f 2 s ≠ 0 := by
  have hle := norm_gp_sub_one_le f hf1 hb Nat.prime_two (by linarith : 0 < s.re)
  have hu2 : ‖u 2 s‖ < 1/2 := by
    rw [norm_u (by norm_num) s]
    have h2 : (2:ℝ)^(-1:ℝ) = 1/2 := by rw [Real.rpow_neg_one]; norm_num
    have h3 := Real.rpow_lt_rpow_of_exponent_lt (x := (2:ℝ)) (by norm_num) (show -s.re < (-1:ℝ) by linarith)
    rwa [h2] at h3
  have hden : 0 < 1 - ‖u 2 s‖ := by linarith
  have hlt : ‖u 2 s‖ / (1 - ‖u 2 s‖) < 1 := by
    rw [div_lt_one hden]; linarith
  intro h0
  rw [h0] at hle
  simp at hle
  linarith

/-- Bound for the inverse of the local Euler factor at the prime `2` on the line `Re s = 1+α`:
`∫_c^{c+1} ‖(g_2(1+α+iτ))⁻¹‖² dτ ≤ C/α` for `0 < α ≤ 1`, with `C` absolute.

This is exactly the statement of the stub file `Work.BMF.mrlas.resonance_integral`; prove it from
scratch so that the reader does not depend on that stub.

WARNING about a tempting but FALSE shortcut: `‖g_2(1+α+iτ)‖ ≥ (1-2q)/(1-q)` with `q = 2^{-(1+α)}`
(`Work.BMF.mrlas.gp_lower_bound`, `Work.BMF.mrlas.norm_u`) degenerates as `α → 0` (e.g.
`f(2^e) = (-1)^e` gives `g_2(1+α) = (1-2q)/(1-q) = O(α)`), so there is no uniform pointwise lower
bound and the integral is NOT bounded by an absolute constant.

The true mechanism (discussed by the reviewers): `g_2(s) = Σ_e f(2^e) z^e` with `z = 2^{-s}`,
`|z| = q < 1/2`; the power series `1 + A(z)`, `A(z) = Σ_{e≥1} f(2^e) z^e`, is zero-free for `|z| ≤ 1/2`
(since `|A| ≤ |z|/(1-|z|) ≤ 1` with equality only at `|z| = 1/2`, `z = 1/2`, excluded by `q < 1/2`),
and `‖1/g_2‖²` is a rational function of `z` whose `τ`-integral near its minimum is `≍ 1/(α² + (θ-θ₀)²)`,
integrating to `O(1/α)` over a unit `τ`-window. -/
theorem cdiv_resonance_integral :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 → (∀ n, ‖f n‖ ≤ 1) →
      ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ c : ℝ,
        (∫ τ in c..(c+1), ‖(Work.BMF.gp f 2 ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ ^ 2)
          ≤ C / α := by
  obtain ⟨C0, hC0pos, hC0⟩ := powerSeries_circle_inv_L2
  refine ⟨4 * C0 / Real.log 2, ?_, ?_⟩
  · have h : 0 < Real.log 2 := Real.log_pos (by norm_num); positivity
  · intro f hf1 hb α hα0 hα1 c
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    -- The circle mean-square bound from `powerSeries_circle_inv_L2`.
    have hcircle : (∫ θ in (0)..(2*Real.pi),
        ‖(∑' e : ℕ, f (2^e) * ((((2:ℝ)^(-(1+α)) : ℝ) : ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^e)⁻¹‖^2)
        ≤ C0 / (1 - 2 * (2:ℝ)^(-(1+α))) := by
      refine hC0 (fun e : ℕ => f (2^e)) ?_ ?_ ((2:ℝ)^(-(1+α))) ?_ ?_
      · simpa using hf1
      · intro n; exact hb (2^n)
      · exact Real.rpow_pos_of_pos (by norm_num) _
      · have h2 : (2:ℝ)^(-1:ℝ) = 1/2 := by rw [Real.rpow_neg_one]; norm_num
        have h3 := Real.rpow_lt_rpow_of_exponent_lt (x := (2:ℝ)) (by norm_num) (show -(1+α) < (-1:ℝ) by linarith)
        rwa [h2] at h3
    -- Continuity of the circle mean square, via continuity of `gp f 2` on the line and the
    -- pointwise identification `cdiv_gp_eq_circle_series`.
    have hcont : Continuous (fun θ : ℝ =>
        ‖(∑' e : ℕ, f (2^e) * ((((2:ℝ)^(-(1+α)) : ℝ) : ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^e)⁻¹‖^2) := by
      have hgp : Continuous (fun θ : ℝ =>
          ‖(Work.BMF.gp f 2 ((((1+α:ℝ)):ℂ) + ((((-θ/Real.log 2:ℝ)):ℂ)) * Complex.I))⁻¹‖^2) := by
        have hdiff : DifferentiableOn ℂ (fun z : ℂ => Work.BMF.gp f 2 z) {z : ℂ | 1 < z.re} :=
          differentiableOn_gp f hb Nat.prime_two
        have hmem : ∀ θ : ℝ, ((((1+α : ℝ)) : ℂ) + ((((-θ/Real.log 2 : ℝ)):ℂ)) * Complex.I) ∈ {z : ℂ | 1 < z.re} := by
          intro θ
          simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
          linarith
        have hne : ∀ θ : ℝ, Work.BMF.gp f 2 ((((1+α : ℝ)) : ℂ) + ((((-θ/Real.log 2 : ℝ)):ℂ)) * Complex.I) ≠ 0 := by
          intro θ
          apply cdiv_gp_ne_zero_line f hf1 hb
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
          linarith
        exact ((((hdiff.continuousOn.comp_continuous (by fun_prop) hmem)).inv₀ hne).norm).pow 2
      exact hgp.congr (fun θ => by rw [cdiv_gp_eq_circle_series f α θ])
    -- `2π`-periodicity of the circle mean square.
    have hper : Function.Periodic (fun θ : ℝ =>
        ‖(∑' e : ℕ, f (2^e) * ((((2:ℝ)^(-(1+α)) : ℝ) : ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^e)⁻¹‖^2) (2*Real.pi) := by
      intro θ
      change ‖(∑' e : ℕ, f (2^e) * ((((2:ℝ)^(-(1+α)) : ℝ) : ℂ) * Complex.exp (((θ + 2*Real.pi : ℝ):ℂ) * Complex.I))^e)⁻¹‖^2
        = ‖(∑' e : ℕ, f (2^e) * ((((2:ℝ)^(-(1+α)) : ℝ) : ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^e)⁻¹‖^2
      rw [cdiv_circle_series_periodic f α θ]
    have hnn : ∀ θ : ℝ, 0 ≤ ‖(∑' e : ℕ, f (2^e) * ((((2:ℝ)^(-(1+α)) : ℝ) : ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^e)⁻¹‖^2 := by
      intro θ; positivity
    -- The pointwise identity `h τ = g (-log 2 · τ)`.
    have heq : ∀ τ : ℝ, ‖(Work.BMF.gp f 2 ((((1+α:ℝ)):ℂ) + (τ:ℂ)*Complex.I))⁻¹‖^2
        = (fun θ : ℝ => ‖(∑' e : ℕ, f (2^e) * ((((2:ℝ)^(-(1+α)) : ℝ) : ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^e)⁻¹‖^2) (((-Real.log 2)*τ)) := by
      intro τ
      rw [gp_eq_geom_powerseries f (1+α) τ]
      apply congrArg (fun w : ℂ => ‖w⁻¹‖^2)
      apply tsum_congr
      intro e
      have hX : (-(τ * Real.log 2)) = (-Real.log 2) * τ := by ring
      rw [hX]
    have hwin := cdiv_window_le (c := c) hper hcont hnn heq
    calc (∫ τ in c..(c+1), ‖(Work.BMF.gp f 2 ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ ^ 2)
        ≤ (1/Real.log 2) * (∫ θ in (0)..(2*Real.pi), ‖(∑' e : ℕ, f (2^e) * ((((2:ℝ)^(-(1+α)) : ℝ) : ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^e)⁻¹‖^2) := hwin
      _ ≤ (1/Real.log 2) * (C0 / (1 - 2 * (2:ℝ)^(-(1+α)))) :=
          mul_le_mul_of_nonneg_left hcircle (le_of_lt (one_div_pos.mpr hlog))
      _ ≤ (4 * C0 / Real.log 2) / α := resonance_arith C0 hC0pos.le α hα0 hα1

/-- **The L² window bound for `Ψ₂ = Ψ - Ψ₁` on the line `Re s = 1+α`**, `0 < α ≤ 1`.

This is the statement of `Submission.Work.BMF.mrlas.Psi2_L2_bound`, needed here as a *fresh*
module because its dependency `Submission.Work.BMF.mrlas.resonance_integral` contains a `sorry`.
The proof of `Submission.Work.BMF.mrlas.psi2_L2_self` (which reduces to the sorry-free helper
`Submission.Work.BMF.mrlas.Psi2_integral_bound_of` of `Psi2_assembly` plus a *self-contained*
resonance estimate `∫_c^{c+1} ‖(gp f 2 (1+α+iτ))⁻¹‖² dτ ≤ C/α`) can be adapted; that resonance
estimate must be reproved inside this file (the route is in
`Submission.Work.BMF.mrlas.resonance_integral_self`, whose ingredients `gp_eq_geom_powerseries`,
`differentiableOn_gp`, `powerSeries_circle_inv_L2`, `periodic_window_integral_le`,
`resonance_arith` are sorry-free).  Everything must be sorry-free. -/
theorem casdiv_psi2_l2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 → (∀ n, ‖f n‖ ≤ 1) →
      ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ c : ℝ,
        (∫ τ in c..(c+1), ‖Work.BMF.Psi2 f ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
          ≤ C / α := by
  obtain ⟨Cr, hCrpos, hres⟩ := cdiv_resonance_integral
  obtain ⟨K, hK0, hK⟩ := primes_log_summable
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * (16 * Real.log 2) ^ 2 * Cr + 2 * (32 * K) ^ 2, ?_, ?_⟩
  · have h1 : 0 < (16 * Real.log 2) ^ 2 := pow_pos (mul_pos (by norm_num) hlog) 2
    have h2 : 0 ≤ (32 * K) ^ 2 := sq_nonneg _
    nlinarith [h1, h2, hCrpos]
  intro f hf1 hb α hα hα1 c
  refine Psi2_integral_bound_of (16 * Real.log 2) (32 * K) (by positivity) (by linarith)
    (fun f' hf1' hb' s hs => Psi2_pointwise_of T_p_bound summable_Psi_series K hK f' hf1' hb' hs)
    Cr hres f hf1 hb α hα hα1 c

end

end Work.BMF.mrlas
