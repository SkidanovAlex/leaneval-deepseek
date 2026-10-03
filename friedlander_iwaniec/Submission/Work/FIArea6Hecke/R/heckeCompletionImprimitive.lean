import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.thetaOdd_poisson
import Submission.Work.FIArea5.S16Hecke.heckeFE_defs
import Submission.Work.FIArea5.S16Hecke.heckeFE_of_theta
import Submission.Work.FIArea5.S16Hecke.thetaHol_exp_decay
import Submission.Work.FIArea5.S16Hecke.mellin_thetaHol
import Submission.Work.FIArea5.S16Hecke.rpow_mul_exp_neg_bounded
import Submission.Work.FIArea6Hecke.R.thetaHol_meas_li
import Submission.Work.FIArea6Hecke.R.gaussSum_zero_of_nontrivial
import Submission.Work.FIArea6Hecke.R.thetaDual_decay
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea6Hecke.S16HeckeCompletionPrimitive
import Submission.Work.FIPlan.Interface

/-!
# `Work.FIArea6Hecke.R.heckeCompletionImprimitive`

Analytic continuation (indeed entireness) of the completed Hecke `L`-function of the
Grössencharacter `ψ_m(z) = χ(z)(z/|z|)^m` of `ℚ(i)` for a strict character `χ` mod `4d` that is
*there is no assumption of primitivity*: the only hypothesis on `χ` is that `ψ_m` is non-trivial on
the primary units mod `4d` (so that `ψ_m` is a genuine, non-principal Größencharacter and the
`L`-function has no pole).

Route.  Hecke's theta series `θ(u) = Σ_{z odd} χ(z)z^m e^{-πu|z|²}` satisfies the *Poisson*
identity `thetaOdd_eq_poisson_form` for every strict `χ` (no primitivity): it expresses `θ` as
`C u^{-(m+1)}` times the dual sum `heckeDual`, whose summands carry `e^{-π|ξ|²/(u(4d)²)}` with
`|ξ|² ≥ 1` and whose `ξ = 0` coefficient vanishes (that is exactly the hypothesis on `ψ_m`).
Hence `θ(u) = O(e^{-δ/u})` as `u → 0⁺` (`hci_thetaOdd_decay_small`).  Splitting the Mellin integral
of `θ` at `c = 1/(4d)²` into its low part `∫_0^c` (controlled by the `e^{-δ/u}` decay, via the
generic lemma `hci_mellin_analyticOn_compact_exp_decay`) and its high part `∫_c^∞` (controlled by
the exponential decay at `∞`, via `mellin_cut_props`), both pieces are entire, and on
`re s > 1 + m/2` their sum is the Mellin transform of `θ`, i.e.
`Γ(s + m/2)π^{-(s+m/2)}L(s,ψ_m)`.  Multiplying by `(4d)^s π^{m/2}` gives the completion
`(4d/π)^s Γ(s + m/2)L(s,ψ_m)` and hence the theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology

namespace Work.FIArea6Hecke.R

open Work.FIArea5.S16Hecke
open Work.FIPlan
noncomputable section
open Work.FIArea5.S16Hecke
open Work.FIPlan

/-! ## Generic analytic input -/

lemma hci_exp_neg_div_isBigO_rpow_neg (δ : ℝ) (hδ : 0 < δ) (b : ℝ) :
    (fun u : ℝ => Real.exp (-δ / u)) =O[𝓝[>] (0:ℝ)] (fun u : ℝ => u ^ (-b)) := by
  have hφ : Tendsto (fun u : ℝ => u⁻¹) (𝓝[>] (0:ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have h2 : (fun u : ℝ => Real.exp (-δ * u⁻¹)) =o[𝓝[>] (0:ℝ)] (fun u : ℝ => u⁻¹ ^ b) :=
    (isLittleO_exp_neg_mul_rpow_atTop hδ b).comp_tendsto hφ
  refine (h2.isBigO).congr' ?_ ?_
  · filter_upwards with u
    rw [div_eq_mul_inv]
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact (Real.rpow_neg_eq_inv_rpow u b).symm

theorem hci_mellin_analyticOn_compact_exp_decay (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (g : ℝ → ℂ)
    (hli : LocallyIntegrableOn g (Set.Ioi 0))
    (h0 : ∀ u : ℝ, c ≤ u → g u = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → u ≤ c → ‖g u‖ ≤ C * Real.exp (-δ / u)) :
    (∀ t : ℂ, MellinConvergent g t) ∧ AnalyticOn ℂ (fun t : ℂ => mellin g t) Set.univ := by
  obtain ⟨C, _hCpos, hC⟩ := hdec
  have htop : g =O[atTop] (fun t : ℝ => Real.exp (-Real.pi * t)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop c] with u hu
    rw [h0 u hu, norm_zero, one_mul]
    exact norm_nonneg _
  have hbot : ∀ b : ℝ, g =O[𝓝[>] (0:ℝ)] (fun u : ℝ => u ^ (-b)) := by
    intro b
    have h1 : g =O[𝓝[>] (0:ℝ)] (fun u : ℝ => Real.exp (-δ / u)) := by
      refine IsBigO.of_bound C ?_
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hc)] with u hu1 hu2
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hC u hu1 (le_of_lt hu2)
    exact h1.trans (hci_exp_neg_div_isBigO_rpow_neg δ hδ b)
  refine ⟨fun t => mellinConvergent_of_isBigO_rpow_exp (a := Real.pi) Real.pi_pos hli htop
      (hbot (t.re - 1)) (by linarith), ?_⟩
  rw [Complex.analyticOn_univ_iff_differentiable]
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp (a := Real.pi) Real.pi_pos hli htop
    (hbot (s.re - 1)) (by linarith)


def hci_heckeDual (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) : ℂ :=
  ∑' ξ : ℤ × ℤ, gaussSum d chi ⟨ξ.1, ξ.2⟩ *
    (((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m *
    Complex.exp (-(Real.pi : ℂ) * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) /
      ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2)))

lemma hci_thetaOdd_eq_poisson (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : IsCharMod4dStrict d chi) (m : ℕ) {u : ℝ} (hu : 0 < u) :
    thetaOdd chi m u =
      (1 / (((4 * d : ℕ) : ℂ) ^ 2)) * (-Complex.I) ^ m * ((u : ℂ) ^ (m + 1))⁻¹ *
        hci_heckeDual d chi m u :=
  thetaOdd_eq_poisson_form d hd chi hchi m hu

lemma hci_norm_exp_arg (d : ℕ) (u : ℝ) (a b : ℤ) :
    ‖Complex.exp (-(Real.pi : ℂ) * (((a : ℂ) ^ 2 + (b : ℂ) ^ 2) /
      ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2)))‖
      = Real.exp (-(Real.pi * (((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (u * ((4 * (d : ℝ)) ^ 2))))) := by
  have hz : (-(Real.pi : ℂ) * (((a : ℂ) ^ 2 + (b : ℂ) ^ 2) /
      ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2)))
      = (((-(Real.pi * (((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (u * ((4 * (d : ℝ)) ^ 2)))))) : ℝ) := by
    push_cast
    ring
  rw [hz, Complex.norm_exp_ofReal]

lemma hci_norm_poly_le (d : ℕ) (hd : 1 ≤ d) (a b : ℤ) (m : ℕ) :
    ‖(((a : ℂ) + Complex.I * (b : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m‖
      ≤ (2 + (a : ℝ) ^ 2 + (b : ℝ) ^ 2) ^ m := by
  rw [norm_pow, norm_div]
  have hK : ‖(((4 * d : ℕ) : ℂ))‖ = (4 * (d : ℝ)) := by
    rw [Complex.norm_natCast]; push_cast; ring
  rw [hK]
  have h4d1 : (1 : ℝ) ≤ 4 * (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have h4dpos : (0 : ℝ) < 4 * (d : ℝ) := by linarith
  have hnum : ‖((a : ℂ) + Complex.I * (b : ℂ))‖ ≤ 2 + (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
    calc ‖((a : ℂ) + Complex.I * (b : ℂ))‖ ≤ ‖(a : ℂ)‖ + ‖Complex.I * (b : ℂ)‖ := norm_add_le _ _
      _ = |(a : ℝ)| + |(b : ℝ)| := by
            rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, Complex.norm_intCast]
      _ ≤ 2 + (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
            have h1 : |(a : ℝ)| ≤ 1 + (a : ℝ) ^ 2 := by nlinarith [abs_nonneg (a:ℝ), sq_abs (a:ℝ)]
            have h2 : |(b : ℝ)| ≤ 1 + (b : ℝ) ^ 2 := by nlinarith [abs_nonneg (b:ℝ), sq_abs (b:ℝ)]
            linarith
  have hq : ‖((a : ℂ) + Complex.I * (b : ℂ))‖ / (4 * (d : ℝ)) ≤ 2 + (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
    rw [div_le_iff₀ h4dpos]
    nlinarith [hnum, h4d1]
  have hqnn : 0 ≤ ‖((a : ℂ) + Complex.I * (b : ℂ))‖ / (4 * (d : ℝ)) := by positivity
  exact pow_le_pow_left₀ hqnn hq m

lemma hci_exp_decay_le (d : ℕ) (hd : 1 ≤ d) {u : ℝ} (hu : 0 < u)
    (hule : u ≤ 1 / ((4 * (d:ℝ))^2)) {a b : ℤ} (hab : (a,b) ≠ 0) :
    Real.exp (-(Real.pi * (((a:ℝ)^2 + (b:ℝ)^2) / (u * ((4*(d:ℝ))^2)))))
      ≤ Real.exp (-(Real.pi / (u * ((4*(d:ℝ))^2)))) *
        Real.exp (Real.pi / ((4*(d:ℝ))^2)) *
        Real.exp (-(Real.pi / ((4*(d:ℝ))^2)) * ((a:ℝ)^2 + (b:ℝ)^2)) := by
  have hKpos : 0 < (4*(d:ℝ))^2 := by positivity
  have hK1 : 1 ≤ (4*(d:ℝ))^2 := by
    have h4d1 : (1:ℝ) ≤ 4*(d:ℝ) := by
      have : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      linarith
    nlinarith
  have hs1 : 1 ≤ (a:ℝ)^2 + (b:ℝ)^2 := Work.FIArea6Hecke.R.one_le_sq_add_sq hab
  have hule1 : u ≤ 1 := by
    have h : 1 / ((4*(d:ℝ))^2) ≤ 1 := (div_le_one hKpos).mpr (by linarith)
    linarith
  have h1u : 1 ≤ 1/u := by rw [one_div]; exact (one_le_inv₀ hu).mpr hule1
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hEq : (-(Real.pi/(u*(4*(d:ℝ))^2)) + (Real.pi/(4*(d:ℝ))^2 + -(Real.pi/(4*(d:ℝ))^2)*((a:ℝ)^2+(b:ℝ)^2)))
      - (-(Real.pi * (((a:ℝ)^2+(b:ℝ)^2)/(u*(4*(d:ℝ))^2))))
      = (Real.pi/(4*(d:ℝ))^2)*(((a:ℝ)^2+(b:ℝ)^2)-1)*(1/u-1) := by
    field_simp
    ring
  have hnn : 0 ≤ (Real.pi/(4*(d:ℝ))^2)*(((a:ℝ)^2+(b:ℝ)^2)-1)*(1/u-1) :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  linarith

lemma hci_norm_summand_le (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ)
    (hchi : IsCharMod4dStrict d chi)
    (hzero : gaussSum d chi 0 = 0 ∨ 1 ≤ m) {u : ℝ} (hu : 0 < u)
    (hule : u ≤ 1 / ((4 * (d:ℝ))^2)) (ξ : ℤ × ℤ) :
    ‖gaussSum d chi ⟨ξ.1, ξ.2⟩ *
      (((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m *
      Complex.exp (-(Real.pi : ℂ) * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) /
        ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2)))‖
      ≤ Real.exp (-(Real.pi / (2 * (4*(d:ℝ))^2)) / u) *
        (((4*d:ℕ):ℝ)^2 * 2^m * Real.exp (Real.pi / (4*(d:ℝ))^2) *
          ((1 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m *
            Real.exp (-(Real.pi / (4*(d:ℝ))^2) * ((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)))) := by
  have hδ : Real.exp (-(Real.pi/(u*(4*(d:ℝ))^2))) ≤
      Real.exp (-(Real.pi / (2*(4*(d:ℝ))^2)) / u) := by
    apply Real.exp_le_exp.mpr
    have hEq : -(Real.pi / (2*(4*(d:ℝ))^2)) / u - (-(Real.pi/(u*(4*(d:ℝ))^2)))
        = Real.pi/(2 * u * (4*(d:ℝ))^2) := by field_simp; ring
    have hpos : 0 ≤ Real.pi/(2 * u * (4*(d:ℝ))^2) := by positivity
    linarith
  rw [norm_mul, norm_mul]
  rcases eq_or_ne ξ 0 with hξ | hξ
  · have h1 : ξ.1 = 0 := by rw [hξ]; rfl
    have h2 : ξ.2 = 0 := by rw [hξ]; rfl
    rw [h1, h2]
    rcases hzero with hz | hm
    · rw [show (⟨(0:ℤ),(0:ℤ)⟩ : GaussianInt) = 0 from rfl, hz]
      simp only [zero_mul, norm_zero]
      positivity
    · have hzb : ((((0:ℤ):ℂ) + Complex.I*(((0:ℤ):ℂ))) / (((4*d:ℕ):ℂ))) = 0 := by simp
      rw [hzb]
      simp only [zero_pow (by omega : m ≠ 0), mul_zero, zero_mul, norm_zero]
      positivity
  · have hs1 : 1 ≤ (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2 := Work.FIArea6Hecke.R.one_le_sq_add_sq hξ
    have hg : ‖gaussSum d chi ⟨ξ.1, ξ.2⟩‖ ≤ ((4*d:ℕ):ℝ)^2 := norm_gaussSum_le d chi hchi.1 ⟨ξ.1,ξ.2⟩
    have hp : ‖(((ξ.1:ℂ)+Complex.I*(ξ.2:ℂ))/(((4*d:ℕ):ℂ)))^m‖
        ≤ (2 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m := hci_norm_poly_le d hd ξ.1 ξ.2 m
    have he : ‖Complex.exp (-(Real.pi:ℂ)*(((ξ.1:ℂ)^2+(ξ.2:ℂ)^2)/((u:ℂ)*(((4*d:ℕ):ℂ))^2)))‖
        = Real.exp (-(Real.pi * (((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2) / (u * ((4*(d:ℝ))^2))))) :=
      hci_norm_exp_arg d u ξ.1 ξ.2
    have hstep1 : ‖gaussSum d chi ⟨ξ.1, ξ.2⟩‖ *
          ‖(((ξ.1:ℂ)+Complex.I*(ξ.2:ℂ))/(((4*d:ℕ):ℂ)))^m‖ *
          ‖Complex.exp (-(Real.pi:ℂ)*(((ξ.1:ℂ)^2+(ξ.2:ℂ)^2)/((u:ℂ)*(((4*d:ℕ):ℂ))^2)))‖
        ≤ ((4*d:ℕ):ℝ)^2 * (2 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m *
          Real.exp (-(Real.pi * (((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2) / (u * ((4*(d:ℝ))^2))))) :=
      mul_le_mul (mul_le_mul hg hp (norm_nonneg _) (by positivity)) (le_of_eq he)
        (norm_nonneg _) (by positivity)
    have hstep2 : ((4*d:ℕ):ℝ)^2 * (2 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m *
          Real.exp (-(Real.pi * (((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2) / (u * ((4*(d:ℝ))^2)))))
        ≤ ((4*d:ℕ):ℝ)^2 * 2^m * (1 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m *
          Real.exp (-(Real.pi * (((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2) / (u * ((4*(d:ℝ))^2))))) := by
      have h2 : (2 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m
          ≤ 2^m * (1 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) m
      have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ ((4*d:ℕ):ℝ)^2)
      calc ((4*d:ℕ):ℝ)^2 * (2 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m *
              Real.exp (-(Real.pi * (((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2) / (u * ((4*(d:ℝ))^2)))))
          = ((4*d:ℕ):ℝ)^2 * ((2 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m *
              Real.exp (-(Real.pi * (((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2) / (u * ((4*(d:ℝ))^2)))))) := by ring
        _ ≤ ((4*d:ℕ):ℝ)^2 * ((2^m * (1 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m) *
              Real.exp (-(Real.pi * (((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2) / (u * ((4*(d:ℝ))^2)))))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)) (by positivity)
        _ = ((4*d:ℕ):ℝ)^2 * 2^m * (1 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m *
              Real.exp (-(Real.pi * (((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2) / (u * ((4*(d:ℝ))^2))))) := by ring
    have hstep3 : ((4*d:ℕ):ℝ)^2 * 2^m * (1 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m *
          Real.exp (-(Real.pi * (((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2) / (u * ((4*(d:ℝ))^2)))))
        ≤ ((4*d:ℕ):ℝ)^2 * 2^m * (1 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m *
          (Real.exp (-(Real.pi / (u * ((4*(d:ℝ))^2)))) *
            Real.exp (Real.pi / ((4*(d:ℝ))^2)) *
            Real.exp (-(Real.pi / ((4*(d:ℝ))^2)) * ((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2))) :=
      mul_le_mul_of_nonneg_left (hci_exp_decay_le d hd hu hule hξ) (by positivity)
    have hstep4 : ((4*d:ℕ):ℝ)^2 * 2^m * (1 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m *
          (Real.exp (-(Real.pi / (u * ((4*(d:ℝ))^2)))) *
            Real.exp (Real.pi / ((4*(d:ℝ))^2)) *
            Real.exp (-(Real.pi / ((4*(d:ℝ))^2)) * ((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)))
        ≤ Real.exp (-(Real.pi / (2 * (4*(d:ℝ))^2)) / u) *
          (((4*d:ℕ):ℝ)^2 * 2^m * Real.exp (Real.pi / (4*(d:ℝ))^2) *
            ((1 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m *
              Real.exp (-(Real.pi / (4*(d:ℝ))^2) * ((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)))) := by
      rw [show ((4*d:ℕ):ℝ)^2 * 2^m * (1 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m *
            (Real.exp (-(Real.pi / (u * ((4*(d:ℝ))^2)))) *
              Real.exp (Real.pi / ((4*(d:ℝ))^2)) *
              Real.exp (-(Real.pi / ((4*(d:ℝ))^2)) * ((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)))
          = Real.exp (-(Real.pi / (u * ((4*(d:ℝ))^2)))) *
            (((4*d:ℕ):ℝ)^2 * 2^m * Real.exp (Real.pi / (4*(d:ℝ))^2) *
              ((1 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m *
                Real.exp (-(Real.pi / (4*(d:ℝ))^2) * ((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)))) from by ring]
      exact mul_le_mul_of_nonneg_right hδ (by positivity)
    exact le_trans hstep1 (le_trans hstep2 (le_trans hstep3 hstep4))

lemma hci_heckeDual_decay (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ)
    (hchi : IsCharMod4dStrict d chi)
    (hzero : gaussSum d chi 0 = 0 ∨ 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → u ≤ 1 / ((4 * (d:ℝ)) ^ 2) →
      ‖hci_heckeDual d chi m u‖ ≤ C * Real.exp (-(Real.pi / (2 * (4*(d:ℝ))^2)) / u) := by
  set Ψ : ℤ × ℤ → ℝ := fun ξ => ((4*d:ℕ):ℝ)^2 * 2^m * Real.exp (Real.pi / (4*(d:ℝ))^2) *
      ((1 + (ξ.1:ℝ)^2 + (ξ.2:ℝ)^2)^m *
        Real.exp (-(Real.pi / (4*(d:ℝ))^2) * ((ξ.1:ℝ)^2 + (ξ.2:ℝ)^2))) with hΨ
  have hΨsum : Summable Ψ := by
    rw [hΨ]
    refine Summable.mul_left _ ?_
    have h := Work.FIArea5.S16.summable_int_prod_exp_neg_sq_add
      (c := Real.pi/(4*(d:ℝ))^2) (by positivity) 0 m
    refine h.congr (fun ξ => ?_)
    simp only [zero_mul, add_zero]
    ring
  refine ⟨∑' ξ, Ψ ξ, ?_, ?_⟩
  · refine hΨsum.tsum_pos (fun ξ => ?_) 0 ?_
    · rw [hΨ]; positivity
    · rw [hΨ]; simp only [Prod.fst_zero, Prod.snd_zero, Int.cast_zero]; positivity
  · intro u hu hule
    have hpt : ∀ ξ : ℤ × ℤ, ‖gaussSum d chi ⟨ξ.1, ξ.2⟩ *
        (((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m *
        Complex.exp (-(Real.pi : ℂ) * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) /
          ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2)))‖
        ≤ Real.exp (-(Real.pi / (2 * (4*(d:ℝ))^2)) / u) * Ψ ξ :=
      fun ξ => hci_norm_summand_le d hd chi m hchi hzero hu hule ξ
    have hsum2 : Summable (fun ξ : ℤ × ℤ => ‖gaussSum d chi ⟨ξ.1, ξ.2⟩ *
        (((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m *
        Complex.exp (-(Real.pi : ℂ) * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) /
          ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2)))‖) :=
      Summable.of_nonneg_of_le (fun ξ => norm_nonneg _) hpt (hΨsum.mul_left _)
    calc ‖hci_heckeDual d chi m u‖
        ≤ Real.exp (-(Real.pi / (2 * (4*(d:ℝ))^2)) / u) * ∑' ξ : ℤ × ℤ, Ψ ξ := by
          calc ‖hci_heckeDual d chi m u‖
              = ‖∑' ξ : ℤ × ℤ, gaussSum d chi ⟨ξ.1, ξ.2⟩ *
                  (((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m *
                  Complex.exp (-(Real.pi : ℂ) * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) /
                    ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2)))‖ := by rw [hci_heckeDual]
            _ ≤ ∑' ξ : ℤ × ℤ, ‖gaussSum d chi ⟨ξ.1, ξ.2⟩ *
                  (((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m *
                  Complex.exp (-(Real.pi : ℂ) * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) /
                    ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2)))‖ := norm_tsum_le_tsum_norm hsum2
            _ ≤ ∑' ξ : ℤ × ℤ, Real.exp (-(Real.pi / (2 * (4*(d:ℝ))^2)) / u) * Ψ ξ :=
                Summable.tsum_le_tsum hpt hsum2 (hΨsum.mul_left _)
            _ = Real.exp (-(Real.pi / (2 * (4*(d:ℝ))^2)) / u) * ∑' ξ : ℤ × ℤ, Ψ ξ :=
                tsum_mul_left
      _ = (∑' ξ : ℤ × ℤ, Ψ ξ) * Real.exp (-(Real.pi / (2 * (4*(d:ℝ))^2)) / u) :=
          mul_comm _ _

lemma hci_thetaOdd_decay_small (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ)
    (hchi : IsCharMod4dStrict d chi)
    (hzero : gaussSum d chi 0 = 0 ∨ 1 ≤ m) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ u : ℝ, 0 < u → u ≤ 1 / ((4*(d:ℝ))^2) →
      ‖thetaOdd chi m u‖ ≤ C * Real.exp (-δ / u) := by
  obtain ⟨C, hCpos, hdec⟩ := hci_heckeDual_decay d hd chi m hchi hzero
  obtain ⟨D, hDnn, hDb⟩ := rpow_mul_exp_neg_bounded
    (Real.pi / (4*(4*(d:ℝ))^2)) (by positivity) (((m+1 : ℕ) : ℝ)) (by positivity)
  refine ⟨max (C*D/(4*(d:ℝ))^2) 1, Real.pi / (4*(4*(d:ℝ))^2),
    lt_max_of_lt_right (by norm_num), by positivity, ?_⟩
  intro u hu hule
  have hpois := hci_thetaOdd_eq_poisson d hd chi hchi m hu
  rw [hpois, norm_mul, norm_mul, norm_mul]
  have hb1 : ‖(1 / (((4 * d : ℕ) : ℂ) ^ 2))‖ = 1 / (4*(d:ℝ))^2 := by
    rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
    push_cast; ring
  have hb2 : ‖(-Complex.I)^m‖ = 1 := by rw [norm_pow, norm_neg, Complex.norm_I, one_pow]
  have hb3 : ‖((u : ℂ) ^ (m + 1))⁻¹‖ = (1/u)^(m+1) := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    rw [one_div, inv_pow]
  rw [hb1, hb2, hb3, mul_one]
  have hCb : ‖hci_heckeDual d chi m u‖ ≤ C * Real.exp (-(Real.pi/(2*(4*(d:ℝ))^2))/u) := hdec u hu hule
  have hkey : (1/u)^(m+1) * Real.exp (-(Real.pi/(2*(4*(d:ℝ))^2))/u)
      ≤ D * Real.exp (-(Real.pi/(4*(4*(d:ℝ))^2))/u) := by
    have hx : 0 ≤ 1/u := by positivity
    have hDb' := hDb (1/u) hx
    rw [Real.rpow_natCast] at hDb'
    have harg : -(Real.pi/(4*(4*(d:ℝ))^2) * (1/u)) = -(Real.pi/(4*(4*(d:ℝ))^2))/u := by ring
    rw [harg] at hDb'
    have h1 : Real.exp (-(Real.pi/(2*(4*(d:ℝ))^2))/u)
        = Real.exp (-(Real.pi/(4*(4*(d:ℝ))^2))/u) * Real.exp (-(Real.pi/(4*(4*(d:ℝ))^2))/u) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h1, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hDb' (Real.exp_nonneg _)
  calc (1/(4*(d:ℝ))^2) * (1/u)^(m+1) * ‖hci_heckeDual d chi m u‖
      ≤ (1/(4*(d:ℝ))^2) * (1/u)^(m+1) * (C * Real.exp (-(Real.pi/(2*(4*(d:ℝ))^2))/u)) :=
          mul_le_mul_of_nonneg_left hCb (by positivity)
    _ = (C/(4*(d:ℝ))^2) * ((1/u)^(m+1) * Real.exp (-(Real.pi/(2*(4*(d:ℝ))^2))/u)) := by ring
    _ ≤ (C/(4*(d:ℝ))^2) * (D * Real.exp (-(Real.pi/(4*(4*(d:ℝ))^2))/u)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (C*D/(4*(d:ℝ))^2) * Real.exp (-(Real.pi/(4*(4*(d:ℝ))^2))/u) := by ring
    _ ≤ max (C*D/(4*(d:ℝ))^2) 1 * Real.exp (-(Real.pi/(4*(4*(d:ℝ))^2))/u) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)


/-! ## The low cut, the high cut and the assembly -/

lemma hci_thetaHol_eq_inv_unitSum_mul (chi : GaussianInt → ℂ) (m : ℕ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) (hU : unitSum chi m ≠ 0)
    (u : ℝ) : thetaHol chi m u = (unitSum chi m)⁻¹ * thetaOdd chi m u := by
  have h := thetaOdd_eq_unitSum_mul_thetaHol chi m hmul u
  rw [h, inv_mul_cancel_left₀ hU]

lemma hci_countable_gaussianInt : Countable GaussianInt :=
  Function.Injective.countable (f := fun z : GaussianInt => (z.re, z.im)) (fun a b h => by
    have h1 : a.re = b.re := congrArg Prod.fst h
    have h2 : a.im = b.im := congrArg Prod.snd h
    ext <;> assumption)

lemma hci_thetaHol_aestronglyMeasurable (chi : GaussianInt → ℂ) (m : ℕ) :
    AEStronglyMeasurable (fun u : ℝ => thetaHol chi m u) volume := by
  haveI : Countable GaussianInt := hci_countable_gaussianInt
  have h : AEStronglyMeasurable
      (fun u : ℝ => ∑' z : GaussianInt, thetaSummand chi m u z) volume :=
    MeasureTheory.AEStronglyMeasurable.tsum
      (fun z => (Work.FIArea6Hecke.R.continuous_thetaSummand chi m z).aestronglyMeasurable)
  refine h.congr ?_
  filter_upwards with u
  exact (thetaHol_eq_tsum chi m u).symm

lemma hci_lowCut_facts (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (k : ℕ)
    (hchi : IsCharMod4dStrict d chi) (hU : unitSum chi k ≠ 0)
    (hzero : gaussSum d chi 0 = 0 ∨ 1 ≤ k) :
    (∀ t : ℂ, MellinConvergent (fun u : ℝ =>
        if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0) t) ∧
    AnalyticOn ℂ (fun t : ℂ => mellin (fun u : ℝ =>
        if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0) t) Set.univ := by
  obtain ⟨C, δ, hCpos, hδpos, hdec⟩ := hci_thetaOdd_decay_small d hd chi k hchi hzero
  have hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  obtain ⟨-, hli⟩ := Work.FIArea6Hecke.R.thetaHol_meas_li (chi := chi) (m := k) hb
  have hcpos : 0 < 1/((4*(d:ℝ))^2) := by positivity
  have hmeasg : AEStronglyMeasurable
      (fun u : ℝ => if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0) volume :=
    (hci_thetaHol_aestronglyMeasurable chi k).indicator measurableSet_Iio
  have hlig : LocallyIntegrableOn
      (fun u : ℝ => if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0) (Set.Ioi 0) :=
    hli.mono hmeasg (Filter.Eventually.of_forall (fun u => by
      show ‖(if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0)‖ ≤ ‖thetaHol chi k u‖
      split_ifs with h <;> simp))
  have h0g : ∀ u : ℝ, 1/((4*(d:ℝ))^2) ≤ u →
      (fun u : ℝ => if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0) u = 0 := by
    intro u hu
    show (if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0) = 0
    exact if_neg (not_lt.mpr hu)
  have hdecg : ∃ C' : ℝ, 0 < C' ∧ ∀ u : ℝ, 0 < u → u ≤ 1/((4*(d:ℝ))^2) →
      ‖(fun u : ℝ => if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0) u‖
        ≤ C' * Real.exp (-δ / u) := by
    refine ⟨max (C / ‖unitSum chi k‖) 1, lt_max_of_lt_right (by norm_num), ?_⟩
    intro u hu huc
    show ‖(if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0)‖ ≤ max (C / ‖unitSum chi k‖) 1 * Real.exp (-δ / u)
    by_cases hlt : u < 1/((4*(d:ℝ))^2)
    · rw [if_pos hlt]
      rw [hci_thetaHol_eq_inv_unitSum_mul chi k hchi.1.2.1 hU u, norm_mul, norm_inv]
      have h1 : ‖unitSum chi k‖⁻¹ * ‖thetaOdd chi k u‖
          ≤ ‖unitSum chi k‖⁻¹ * (C * Real.exp (-δ / u)) :=
        mul_le_mul_of_nonneg_left (hdec u hu hlt.le) (by positivity)
      have h3 : ‖unitSum chi k‖⁻¹ * (C * Real.exp (-δ / u))
          ≤ max (C / ‖unitSum chi k‖) 1 * Real.exp (-δ / u) := by
        have heq : ‖unitSum chi k‖⁻¹ * (C * Real.exp (-δ / u))
            = (C / ‖unitSum chi k‖) * Real.exp (-δ / u) := by rw [div_eq_mul_inv]; ring
        rw [heq]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
      exact le_trans h1 h3
    · rw [if_neg hlt, norm_zero]
      exact mul_nonneg (lt_max_of_lt_right (by norm_num)).le (Real.exp_nonneg _)
  exact hci_mellin_analyticOn_compact_exp_decay (1/((4*(d:ℝ))^2)) δ hcpos hδpos
    (fun u : ℝ => if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0) hlig h0g hdecg

lemma hci_highCut_facts (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (k : ℕ)
    (hchi : IsCharMod4dStrict d chi) :
    (∀ t : ℂ, MellinConvergent (fun u : ℝ =>
        if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0) t) ∧
    AnalyticOn ℂ (fun t : ℂ => mellin (fun u : ℝ =>
        if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0) t) Set.univ := by
  have hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  obtain ⟨-, hli⟩ := Work.FIArea6Hecke.R.thetaHol_meas_li (chi := chi) (m := k) hb
  have hmeasg : AEStronglyMeasurable
      (fun u : ℝ => if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0) volume :=
    (hci_thetaHol_aestronglyMeasurable chi k).indicator measurableSet_Ici
  have hlig : LocallyIntegrableOn
      (fun u : ℝ => if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0) (Set.Ioi 0) :=
    hli.mono hmeasg (Filter.Eventually.of_forall (fun u => by
      show ‖(if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0)‖ ≤ ‖thetaHol chi k u‖
      split_ifs with h <;> simp))
  have hlt0 : 1/((4*(d:ℝ))^2) < 1/(4*(d:ℝ)) := by
    have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hpos : 0 < 4*(d:ℝ) := by linarith
    have hgt : (1:ℝ) < 4*(d:ℝ) := by linarith
    have hlt : 4*(d:ℝ) < (4*(d:ℝ))^2 := by
      have h := mul_lt_mul_of_pos_left hgt hpos
      simpa [mul_one, sq] using h
    rw [one_div, one_div]
    exact (inv_lt_inv₀ (by positivity : (0:ℝ) < (4*(d:ℝ))^2) hpos).mpr hlt
  have hcpos0 : 0 < 1/((4*(d:ℝ))^2) := by positivity
  have h0g : ∀ u : ℝ, u ≤ (1/((4*(d:ℝ))^2))/2 →
      (fun u : ℝ => if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0) u = 0 := by
    intro u hu
    show (if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0) = 0
    rw [if_neg]
    intro hcu
    linarith
  have hdecg : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      ‖(fun u : ℝ => if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0) u‖
        ≤ C * Real.exp (-Real.pi * u) := by
    obtain ⟨C₀, hC₀nn, hC₀⟩ := thetaHol_exp_decay d hd chi k hb
    refine ⟨C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d),
      Work.FIArea5.S16Hecke.thetaC d, Work.FIArea5.S16Hecke.thetaC_pos hd, ?_⟩
    intro u hu
    show ‖(if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0)‖
        ≤ C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d) * Real.exp (-Real.pi * u)
    have hu' : 1/(4*(d:ℝ)) ≤ u := by
      have h : Work.FIArea5.S16Hecke.thetaC d ≤ u := hu
      rwa [Work.FIArea5.S16Hecke.thetaC] at h
    have hlu : 1/((4*(d:ℝ))^2) < u := lt_of_lt_of_le hlt0 hu'
    rw [if_pos (le_of_lt hlu)]
    calc ‖thetaHol chi k u‖
        ≤ C₀ * Real.exp (-Real.pi * (u - Work.FIArea5.S16Hecke.thetaC d)) := hC₀ u hu
      _ = C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d) * Real.exp (-Real.pi * u) := by
          rw [show -Real.pi * (u - Work.FIArea5.S16Hecke.thetaC d)
              = Real.pi * Work.FIArea5.S16Hecke.thetaC d + -Real.pi * u by ring, Real.exp_add]
          ring
  exact mellin_cut_props ((1/((4*(d:ℝ))^2))/2) (by positivity)
    (fun u : ℝ => if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0)
    hmeasg.aemeasurable.restrict hlig h0g hdecg

lemma hci_mellin_thetaHol_eq (chi : GaussianInt → ℂ) (m : ℕ) (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    {s : ℂ} (hs : 1 + (m : ℝ) / 2 < s.re) :
    mellin (thetaHol chi m) s = Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) *
      heckeLSeries chi (m : ℤ) (s - (m : ℂ) / 2) := by
  rw [mellin, ← mellin_thetaHol chi m hb hs]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  rw [smul_eq_mul]; ring

lemma hci_completion_of_nat_strict (d : ℕ) (chi : GaussianInt → ℂ) (k : ℕ) (hd : 1 ≤ d)
    (hchi : IsCharMod4dStrict d chi) (hU : unitSum chi k ≠ 0)
    (hzero : gaussSum d chi 0 = 0 ∨ 1 ≤ k) :
    ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      ∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d (k : ℤ) s * heckeLSeries chi (k : ℤ) s := by
  have hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  obtain ⟨hlowconv, hlowan⟩ := hci_lowCut_facts d hd chi k hchi hU hzero
  obtain ⟨hhighconv, hhighan⟩ := hci_highCut_facts d hd chi k hchi
  refine ⟨fun s : ℂ => (((4*d:ℕ):ℂ))^s * ((Real.pi : ℂ)^((k:ℂ)/2)) *
      (mellin (fun u : ℝ => if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0) (s + (k:ℂ)/2) +
       mellin (fun u : ℝ => if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0) (s + (k:ℂ)/2)),
    ?_, ?_⟩
  · have hcompL : AnalyticOn ℂ (fun s : ℂ => mellin (fun u : ℝ =>
        if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0) (s + (k:ℂ)/2)) Set.univ := by
      refine hlowan.comp ?_ (fun x _ => Set.mem_univ _)
      refine DifferentiableOn.analyticOn ?_ isOpen_univ
      intro s _
      exact (differentiableAt_id.add_const _).differentiableWithinAt
    have hcompH : AnalyticOn ℂ (fun s : ℂ => mellin (fun u : ℝ =>
        if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0) (s + (k:ℂ)/2)) Set.univ := by
      refine hhighan.comp ?_ (fun x _ => Set.mem_univ _)
      refine DifferentiableOn.analyticOn ?_ isOpen_univ
      intro s _
      exact (differentiableAt_id.add_const _).differentiableWithinAt
    exact ((Work.FIArea5.S16Hecke.analyticOn_fourd_cpow d hd).mul
      (analyticOn_const (v := ((Real.pi : ℂ)^((k:ℂ)/2))))).mul (hcompL.add hcompH)
  · intro s hs
    show (((4*d:ℕ):ℂ))^s * ((Real.pi : ℂ)^((k:ℂ)/2)) *
        (mellin (fun u : ℝ => if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0) (s + (k:ℂ)/2)
         + mellin (fun u : ℝ => if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0) (s + (k:ℂ)/2))
      = Work.FITop4.Bridge.heckeArch d (k : ℤ) s * heckeLSeries chi (k : ℤ) s
    have ht : 1 + (k:ℝ)/2 < (s + (k:ℂ)/2).re := by
      have h2 : (s + (k:ℂ)/2).re = s.re + (k:ℝ)/2 := by
        rw [Complex.add_re]
        congr 1
        have : (k:ℂ)/2 = (((k:ℝ)/2 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
      rw [h2]
      exact lt_of_lt_of_le hs (le_add_of_nonneg_right (by positivity))
    have hsplit : mellin (fun u : ℝ => if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0)
          (s + (k:ℂ)/2)
        + mellin (fun u : ℝ => if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0)
          (s + (k:ℂ)/2) = mellin (thetaHol chi k) (s + (k:ℂ)/2) := by
      have hL : MellinConvergent
          (fun u : ℝ => if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0)
          (s + (k:ℂ)/2) := hlowconv _
      have hH : MellinConvergent
          (fun u : ℝ => if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0)
          (s + (k:ℂ)/2) := hhighconv _
      rw [mellin, mellin, mellin, ← integral_add hL hH]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
      rw [← smul_add]
      congr 1
      show (if u < 1/((4*(d:ℝ))^2) then thetaHol chi k u else 0)
        + (if 1/((4*(d:ℝ))^2) ≤ u then thetaHol chi k u else 0) = thetaHol chi k u
      by_cases h : u < 1/((4*(d:ℝ))^2)
      · rw [if_pos h, if_neg (not_le_of_gt h), add_zero]
      · rw [if_neg h, if_pos (le_of_not_gt h), zero_add]
    rw [hsplit, hci_mellin_thetaHol_eq chi k hb ht]
    rw [show s + (k:ℂ)/2 - (k:ℂ)/2 = s by ring]
    rw [Work.FITop4.Bridge.heckeArch]
    have hgam : s + ((|(((k:ℤ)):ℝ)|/2 : ℝ) : ℂ) = s + (k:ℂ)/2 := by
      congr 1
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (((k:ℤ)):ℝ))]
      push_cast; ring
    rw [hgam]
    have hfour : (((4*d:ℕ):ℂ))^s * ((Real.pi : ℂ)^((k:ℂ)/2)) *
        ((Real.pi : ℂ)^(-(s + (k:ℂ)/2))) = (4 * ((d:ℝ):ℂ) / (Real.pi:ℂ))^s := by
      rw [Work.FIArea5.S16Hecke.fourd_pow_pi_pow d hd k s]
      congr 1
      push_cast; ring
    rw [show (((4*d:ℕ):ℂ))^s * ((Real.pi : ℂ)^((k:ℂ)/2)) *
            (Complex.Gamma (s + (k:ℂ)/2) * (Real.pi:ℂ)^(-(s+(k:ℂ)/2)) *
              heckeLSeries chi (k:ℤ) s)
          = (((4*d:ℕ):ℂ))^s * ((Real.pi : ℂ)^((k:ℂ)/2)) * (Real.pi:ℂ)^(-(s+(k:ℂ)/2)) *
            (Complex.Gamma (s + (k:ℂ)/2) * heckeLSeries chi (k:ℤ) s) from by ring]
    rw [hfour]
    ring

/-! ## Conjugation of strict characters (re-proved locally) -/

lemma hci_isCharMod4d_conj {d : ℕ} {chi : GaussianInt → ℂ}
    (h : Work.FITop3.IsCharMod4d d chi) :
    Work.FITop3.IsCharMod4d d (fun z => star (chi z)) := by
  obtain ⟨h1, hmul, hb, hper, hv⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [h1, star_one]
  · intro z w
    show star (chi (z * w)) = star (chi z) * star (chi w)
    rw [hmul z w, star_mul]
    ring
  · intro z; simp only [norm_star]; exact hb z
  · intro z w hzw
    show star (chi z) = star (chi w)
    rw [hper z w hzw]
  · intro z hz
    show star (chi z) = 0
    rw [hv z hz, star_zero]

lemma hci_isCharMod4dStrict_conj {d : ℕ} {chi : GaussianInt → ℂ}
    (h : IsCharMod4dStrict d chi) :
    IsCharMod4dStrict d (fun z => star (chi z)) :=
  ⟨hci_isCharMod4d_conj h.1, fun z hz => by simp only [h.2 z hz, star_zero]⟩

lemma hci_star_heckeArch (d : ℕ) (m : ℤ) (s : ℂ) (hd : 1 ≤ d) :
    star (Work.FITop4.Bridge.heckeArch d m (star s)) = Work.FITop4.Bridge.heckeArch d (-m) s := by
  have hpos : (0:ℝ) < 4 * (d:ℝ) / Real.pi := by positivity
  have hne : ((((4 * (d:ℝ) / Real.pi : ℝ)) : ℂ) ≠ 0) := by
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt hpos
  have hlog : (starRingEnd ℂ) (Complex.log ((((4 * (d:ℝ) / Real.pi : ℝ)) : ℂ)))
      = Complex.log ((((4 * (d:ℝ) / Real.pi : ℝ)) : ℂ)) := by
    rw [← Complex.ofReal_log hpos.le]; exact Complex.conj_ofReal _
  have hbase : (4 * ((d : ℝ) : ℂ) / ((Real.pi : ℝ) : ℂ))
      = (((4 * (d : ℝ) / Real.pi : ℝ)) : ℂ) := by push_cast; ring
  have hcnj : star (((((4 * (d:ℝ) / Real.pi : ℝ)) : ℂ)) ^ (star s))
      = ((((4 * (d:ℝ) / Real.pi : ℝ)) : ℂ)) ^ s := by
    simp only [Complex.star_def]
    rw [Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne,
      ← Complex.exp_conj, map_mul, hlog, starRingEnd_self_apply]
  have habs : |(((-m : ℤ)) : ℝ)| = |((m : ℤ) : ℝ)| := by
    rw [show (((-m : ℤ)) : ℝ) = -((m : ℤ) : ℝ) by push_cast; ring, abs_neg]
  have hG : star (Complex.Gamma (star s + ((|((m : ℤ) : ℝ)| / 2 : ℝ) : ℂ)))
      = Complex.Gamma (s + ((|((m : ℤ) : ℝ)| / 2 : ℝ) : ℂ)) := by
    simp only [Complex.star_def]
    rw [← Complex.Gamma_conj]
    congr 1
    simp only [map_add, starRingEnd_self_apply, Complex.conj_ofReal]
  unfold Work.FITop4.Bridge.heckeArch
  rw [hbase, star_mul, hcnj, habs, hG]
  ring

/-! ## Positive weights: twisted character, then conjugation for negative weights -/

lemma hci_completion_nat_big (d : ℕ) (chi : GaussianInt → ℂ) (k : ℕ) (hd : 1 ≤ d)
    (hchi : IsCharMod4dStrict d chi) (hk : 1 ≤ k) :
    ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      ∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d (k : ℤ) s * heckeLSeries chi (k : ℤ) s := by
  have hst' : IsCharMod4dStrict d (twist chi k) := twist_isCharMod4dStrict d hd chi k hchi
  have hU' : unitSum (twist chi k) k ≠ 0 := by
    rw [twist_unitSum d hd chi k hchi.1]; norm_num
  have hzero' : gaussSum d (twist chi k) 0 = 0 ∨ 1 ≤ k := Or.inr hk
  obtain ⟨Lam, hAn, hag⟩ := hci_completion_of_nat_strict d (twist chi k) k hd hst' hU' hzero'
  refine ⟨Lam, hAn, fun s hs => ?_⟩
  rw [hag s hs, Work.FIArea6Hecke.heckeLSeries_twist chi k]

lemma hci_completion_nat_pos (d : ℕ) (chi : GaussianInt → ℂ) (k : ℕ) (hd : 1 ≤ d)
    (hchi : IsCharMod4dStrict d chi)
    (hne : ∃ z : GaussianInt, IsPrimary z ∧ IsUnitMod4d d z ∧ psi chi (k : ℤ) z ≠ 1) :
    ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      ∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d (k : ℤ) s * heckeLSeries chi (k : ℤ) s := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · have hst' : IsCharMod4dStrict d (twist chi k) := twist_isCharMod4dStrict d hd chi k hchi
    have hU' : unitSum (twist chi k) k ≠ 0 := by
      rw [twist_unitSum d hd chi k hchi.1]; norm_num
    have hnt : ∃ z : GaussianInt, IsPrimary z ∧ IsUnitMod4d d z ∧ twist chi k z ≠ 1 := by
      obtain ⟨z, hzp, hzu, hzne⟩ := hne
      refine ⟨z, hzp, hzu, ?_⟩
      rw [twist_eq_of_isPrimary chi k hzp]
      rw [hk0] at hzne
      simpa [psi] using hzne
    have hzero' : gaussSum d (twist chi k) 0 = 0 :=
      Work.FIArea6Hecke.R.gaussSum_zero_of_nontrivial hd hst' hnt
    obtain ⟨Lam, hAn, hag⟩ := hci_completion_of_nat_strict d (twist chi k) k hd hst' hU' (Or.inl hzero')
    exact ⟨Lam, hAn, fun s hs => by
      rw [hag s hs, Work.FIArea6Hecke.heckeLSeries_twist chi k]⟩
  · exact hci_completion_nat_big d chi k hd hchi hkpos

theorem heckeCompletionImprimitive (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (hd : 1 ≤ d)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hne : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
      Work.FIArea5.S16Hecke.psi chi m z ≠ 1) :
    ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d m s *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s) := by
  by_cases hm : 0 ≤ m
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = (k : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
    obtain ⟨Lam, hAn, hag⟩ := hci_completion_nat_pos d chi k hd hchi hne
    refine ⟨Lam, hAn, fun s hs => ?_⟩
    have hs' : 1 + (k : ℝ) / 2 < s.re := by
      have h1 : |(((k : ℤ)) : ℝ)| = (k : ℝ) := by simp
      simpa [h1] using hs
    rw [hag s hs']
  · push_neg at hm
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -((k : ℕ) : ℤ) := ⟨m.natAbs, by omega⟩
    have hk : 1 ≤ k := by omega
    have hchi' : IsCharMod4dStrict d (fun z => star (chi z)) := hci_isCharMod4dStrict_conj hchi
    obtain ⟨L0, hAn0, hag0⟩ := hci_completion_nat_big d (fun z => star (chi z)) k hd hchi' hk
    refine ⟨fun s => star (L0 (star s)), ?_, ?_⟩
    · refine DifferentiableOn.analyticOn ?_ isOpen_univ
      intro z _
      have h1 : DifferentiableAt ℂ L0 (star z) := (hAn0.analyticAt (Filter.univ_mem)).differentiableAt
      have h2 := DifferentiableAt.conj_conj (f := L0) (x := star z) h1
      have h2' : DifferentiableAt ℂ (fun s => star (L0 (star s))) (star (star z)) := h2
      rw [star_star] at h2'
      exact h2'.differentiableWithinAt
    · intro s hs
      have hs' : 1 + (((k : ℕ) : ℝ)) / 2 < (star s).re := by
        rw [Complex.star_def, Complex.conj_re]
        have h1 : |(((-((k : ℕ) : ℤ)) : ℤ) : ℝ)| = (((k : ℕ)) : ℝ) := by
          rw [show (((-((k:ℕ):ℤ)) : ℤ) : ℝ) = -(((k:ℕ):ℝ)) by push_cast; ring, abs_neg,
            abs_of_nonneg (by positivity)]
        simpa [h1] using hs
      have h0 := hag0 (star s) hs'
      have hA : star (Work.FITop4.Bridge.heckeArch d ((k : ℕ) : ℤ) (star s))
          = Work.FITop4.Bridge.heckeArch d (-((k : ℕ) : ℤ)) s := hci_star_heckeArch d ((k:ℕ):ℤ) s hd
      have hB : star (heckeLSeries (fun z => star (chi z)) ((k : ℕ) : ℤ) (star s))
          = heckeLSeries chi (-((k : ℕ) : ℤ)) s := by
        rw [← Work.FIArea5.S16Hecke.heckeLSeries_conj (fun z => star (chi z)) k s]
        congr 1
        funext z
        simp
      show star (L0 (star s)) = _
      rw [h0, star_mul, hA, hB]
      ring

end
end Work.FIArea6Hecke.R


