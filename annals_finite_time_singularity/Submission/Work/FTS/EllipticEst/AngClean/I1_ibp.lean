/-
Copyright: work module for the Elgindi finite-time singularity project.

# `I1_ibp`, de-tainted

This is a verbatim copy of `Submission/Work/FTS/EllipticEst/AngSecond/I1_ibp.lean` in which the
cut-off identity `Work.AngSecond.I1_cutoff_identity` (whose proof imports the three
`sorry`-carrying modules `AngSecond.{slice_nice_ibp,swap_IP_cut,swap_nice}`) is replaced by the
from-scratch, `sorry`-free `Work.FTS.EllipticEst.AngSecond.I1_cutoff_identity_alt` of
`Submission/Work/FTS/EllipticEst/AngSecond/I1_cut_alt.lean`.  Nothing else is changed, so
`Work.FTS.EllipticEst.AngSecond.I1_ibp_identity` has the same name and statement, but no longer
inherits `sorryAx`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.EllipticEst.AngSecond.I1_defs
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
import Submission.Work.FTS.EllipticEst.AngClean.I1_cut_alt
import Submission.Work.AngSecond.I1_honesty

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# The radial integration by parts of `I₁` (`Work.FTS.EllipticEst.AngSecond.I1_ibp_identity`)

Removing the cut-off `χ_n` from the cut-off identity `I1_cutoff_identity` gives the honest
identity

  `IP (z²∂_zzΨ) (∂_θθΨ) = - IP (z∂_zΨ) (z ∂_z∂_θθΨ) - IP (z∂_zΨ) (cw · ∂_θθΨ)`,

`cw z = 2(z-1)/(1+z)`, which is the point where the `z`-derivative of the paper's `I₁` is moved
onto the other factor.  Every step is a dominated-convergence limit in `n` of the corresponding
object of the cut-off identity, the dominating functions being the `z`-integrands of the
`IPMem`-honest pairings.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Real ContDiff

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-! ## The `z`-integrands of the pairings -/

/-- The integrand of the `θ`-inner integral of `IP (z²∂_zzΨ) (∂_θθΨ)`. -/
def Akern (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ

/-- The `z`-integrand of `IP (G Ψ) (Φ Ψ)`. -/
def Phi1 (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z

/-- The `z`-integrand of `IP (G Ψ) (H Ψ)`. -/
def BHfun (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, sig θ * (G Ψ z θ * H Ψ z θ) * w2 z

/-- The `z`-integrand of `IP (G Ψ) (cw · Φ Ψ)`. -/
def Cwfun (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, sig θ * (G Ψ z θ * (cw z * Phi Ψ z θ)) * w2 z

/-- The `θ`-integrand of the `z`-integrand `Bfun` of the limit of the right-hand side of the
cut-off identity (`χ_n → 1`). -/
def Ainner (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  sig θ * w2 z * (2 * G Ψ z θ * Phi Ψ z θ + G Ψ z θ * H Ψ z θ
    - 4 * G Ψ z θ * Phi Ψ z θ / (1 + z))

/-- The limit of the `z`-integrand of the right-hand side of the cut-off identity. -/
def Bfun (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Ainner Ψ z θ

/-- The `z`-outer function of the right-hand side of the cut-off identity. -/
def nfun (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, sig θ * nice n Ψ z θ

/-- The `z`-integrand of `IP (z²∂_zzΨ) (∂_θθΨ)`. -/
def Afun (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, Akern Ψ z θ

/-! ## Membership of the cut-off transition regions -/

/-- For a fixed `z > 0` the cut-offs are eventually equal to `1` (they equal `1` on
`[2/(n+1), 2(n+1)]` and every fixed positive `z` lies in that interval for large `n`). -/
theorem cut_eventually_one (z : ℝ) (hz : 0 < z) :
    ∀ᶠ n : ℕ in Filter.atTop, Work.FTS.EllipticEst.cut n z = 1 := by
  obtain ⟨M, hM⟩ := exists_nat_ge (max (2 / z) (z / 2))
  refine Filter.eventually_atTop.mpr ⟨M, fun n hn => ?_⟩
  have hM1 : (2 / z : ℝ) ≤ (M : ℝ) := le_trans (le_max_left _ _) hM
  have hM2 : (z / 2 : ℝ) ≤ (M : ℝ) := le_trans (le_max_right _ _) hM
  have hn' : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  refine Work.FTS.EllipticEst.cut_eq_one_of_mem n ?_ ?_
  · rw [div_le_iff₀ hn1]
    have h2z : 2 ≤ z * (M : ℝ) := by
      rw [div_le_iff₀ hz] at hM1
      linarith
    nlinarith
  · nlinarith

/-- Almost every `z ∈ Iz` is positive. -/
theorem ae_pos_of_Iz : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 < z := by
  have hdiff : ∀ᵐ z ∂(volume : MeasureTheory.Measure ℝ), z ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  filter_upwards [MeasureTheory.ae_mono Measure.restrict_le_self hdiff,
    ae_restrict_mem measurableSet_Ici] with z hz hzI
  exact lt_of_le_of_ne hzI (Ne.symm hz)

/-! ## Integrability of the cut-off factors -/

theorem integrableOn_cut_mul {X : ℝ → ℝ} (hX : IntegrableOn X Work.Spaces.Iz) (n : ℕ) :
    IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z * X z) Work.Spaces.Iz := by
  refine (hX.norm).mono' ?_ ?_
  · exact ((cut_contDiff n).continuous.aestronglyMeasurable.mul hX.aestronglyMeasurable)
  · filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_le.mpr
      ⟨by linarith [Work.FTS.EllipticEst.cut_nonneg n z],
       Work.FTS.EllipticEst.cut_le_one n z⟩)

theorem integrableOn_cutDeriv_mul {X : ℝ → ℝ} (hX : IntegrableOn X Work.Spaces.Iz) (n : ℕ) :
    IntegrableOn (fun z => X z * (z * deriv (Work.FTS.EllipticEst.cut n) z)) Work.Spaces.Iz := by
  obtain ⟨K, hKpos, hKbound, -, -⟩ := cut_deriv_uniform
  refine (hX.norm.const_mul K).mono' ?_ ?_
  · exact (hX.aestronglyMeasurable.mul
      ((continuous_id.mul (continuous_deriv_cut n)).aestronglyMeasurable))
  · filter_upwards with z
    simp only [Real.norm_eq_abs, abs_mul]
    calc |X z| * (|z| * |deriv (Work.FTS.EllipticEst.cut n) z|)
        = |X z| * |z * deriv (Work.FTS.EllipticEst.cut n) z| := by rw [abs_mul]
      _ ≤ |X z| * K := mul_le_mul_of_nonneg_left (hKbound n z) (abs_nonneg _)
      _ = K * |X z| := by ring

/-! ## The two dominated-convergence limits -/

theorem tendsto_setIntegral_cut_mul {X : ℝ → ℝ} (hX : IntegrableOn X Work.Spaces.Iz) :
    Filter.Tendsto (fun n : ℕ => ∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.cut n z * X z) Filter.atTop
      (nhds (∫ z in Work.Spaces.Iz, X z)) := by
  obtain ⟨K, hKpos, hKbound, hKtend, -⟩ := cut_deriv_uniform
  have hbound : ∀ n : ℕ, ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      ‖Work.FTS.EllipticEst.cut n z * X z‖ ≤ ‖X z‖ := by
    intro n
    filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_le.mpr
      ⟨by linarith [Work.FTS.EllipticEst.cut_nonneg n z],
       Work.FTS.EllipticEst.cut_le_one n z⟩)
  have hlim : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.cut n z * X z) Filter.atTop
        (nhds (X z)) := by
    filter_upwards [ae_pos_of_Iz] with z hz
    have h := (hKtend z hz).mul_const (X z)
    simpa using h
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iz) (F := fun n z =>
      Work.FTS.EllipticEst.cut n z * X z) (f := X) (fun z => ‖X z‖)
    (fun n => (cut_contDiff n).continuous.aestronglyMeasurable.mul hX.aestronglyMeasurable)
    hX.norm hbound hlim
  simpa using hmain

theorem tendsto_setIntegral_cutDeriv_mul {X : ℝ → ℝ} (hX : IntegrableOn X Work.Spaces.Iz) :
    Filter.Tendsto (fun n : ℕ => ∫ z in Work.Spaces.Iz,
        X z * (z * deriv (Work.FTS.EllipticEst.cut n) z)) Filter.atTop (nhds 0) := by
  obtain ⟨K, hKpos, hKbound, -, hKderiv⟩ := cut_deriv_uniform
  have hbound : ∀ n : ℕ, ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      ‖X z * (z * deriv (Work.FTS.EllipticEst.cut n) z)‖ ≤ K * ‖X z‖ := by
    intro n
    filter_upwards with z
    simp only [Real.norm_eq_abs, abs_mul]
    calc |X z| * (|z| * |deriv (Work.FTS.EllipticEst.cut n) z|)
        = |X z| * |z * deriv (Work.FTS.EllipticEst.cut n) z| := by rw [abs_mul]
      _ ≤ |X z| * K := mul_le_mul_of_nonneg_left (hKbound n z) (abs_nonneg _)
      _ = K * |X z| := by ring
  have hlim : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Filter.Tendsto (fun n : ℕ => X z * (z * deriv (Work.FTS.EllipticEst.cut n) z))
        Filter.atTop (nhds 0) := by
    filter_upwards with z
    have h := (hKderiv z).const_mul (X z)
    simpa using h
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iz) (F := fun n z =>
      X z * (z * deriv (Work.FTS.EllipticEst.cut n) z)) (f := fun _ => (0 : ℝ))
    (fun z => K * ‖X z‖)
    (fun n => hX.aestronglyMeasurable.mul
      ((continuous_id.mul (continuous_deriv_cut n)).aestronglyMeasurable))
    (hX.norm.const_mul K) hbound hlim
  simpa using hmain

/-! ## Pointwise identities for the `z`-integrands -/

theorem measurable_cw : Measurable cw := by
  unfold cw; measurability

theorem cw_eq {z : ℝ} (hz : 0 ≤ z) : cw z = 2 - 4 / (1 + z) := by
  have h1 : (1 : ℝ) + z ≠ 0 := by positivity
  rw [cw]
  field_simp
  ring

theorem abs_cw_le_two {z : ℝ} (hz : 0 ≤ z) : |cw z| ≤ 2 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : |z - 1| ≤ 1 + z := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [cw, abs_div, abs_mul, abs_of_pos h1]
  rw [div_le_iff₀ h1]
  have h3 : |(2 : ℝ)| = 2 := by norm_num
  rw [h3]
  linarith

theorem integrableOn_aInner (Ψ : ℝ → ℝ → ℝ) (hUφ : IPMem (G Ψ) (Phi Ψ))
    (hUH : IPMem (G Ψ) (H Ψ)) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (Ainner Ψ z) Work.Spaces.Iθ := by
  have hmGφ : IntegrableOn (fun θ => sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun (hUφ.1 z hz) ?_ measurableSet_Icc
    intro θ _; ring
  have hmGH : IntegrableOn (fun θ => sig θ * (G Ψ z θ * H Ψ z θ) * w2 z)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun (hUH.1 z hz) ?_ measurableSet_Icc
    intro θ _; ring
  have h1 : IntegrableOn (fun θ => (2 : ℝ) * (sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z))
      Work.Spaces.Iθ := hmGφ.const_mul 2
  have h3 : IntegrableOn (fun θ => (4 / (1 + z)) * (sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z))
      Work.Spaces.Iθ := hmGφ.const_mul _
  refine MeasureTheory.IntegrableOn.congr_fun ((h1.add hmGH).sub h3) ?_ measurableSet_Icc
  intro θ _
  simp only [Ainner, G, Phi, H, Pi.add_apply, Pi.sub_apply]
  ring

/-- The `θ`-inner integral of the cut-off identity, written through the two `z`-integrands. -/
theorem nfun_eq (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hUφ : IPMem (G Ψ) (Phi Ψ))
    (hUH : IPMem (G Ψ) (H Ψ)) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    nfun n Ψ z = Work.FTS.EllipticEst.cut n z * Bfun Ψ z
      + Phi1 Ψ z * (z * deriv (Work.FTS.EllipticEst.cut n) z) := by
  have hmGφ : IntegrableOn (fun θ => sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun (hUφ.1 z hz) ?_ measurableSet_Icc
    intro θ _; ring
  have hAint := integrableOn_aInner Ψ hUφ hUH hz
  rw [nfun, Bfun, Phi1]
  rw [show (∫ θ in Work.Spaces.Iθ, sig θ * nice n Ψ z θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.cut n z * Ainner Ψ z θ
          + (z * deriv (Work.FTS.EllipticEst.cut n) z)
            * (sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z)) from
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
        simp only [nice, Ainner, G, Phi, H]; ring)]
  rw [MeasureTheory.integral_add (hAint.const_mul _) (hmGφ.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  ring

/-- The limit `Bfun` of the `z`-integrand of the right-hand side of the cut-off identity. -/
theorem Bfun_eq (Ψ : ℝ → ℝ → ℝ) (hUφ : IPMem (G Ψ) (Phi Ψ)) (hUH : IPMem (G Ψ) (H Ψ))
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    Bfun Ψ z = cw z * Phi1 Ψ z + BHfun Ψ z := by
  have hmGφ : IntegrableOn (fun θ => sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun (hUφ.1 z hz) ?_ measurableSet_Icc
    intro θ _; ring
  have hmGH : IntegrableOn (fun θ => sig θ * (G Ψ z θ * H Ψ z θ) * w2 z)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun (hUH.1 z hz) ?_ measurableSet_Icc
    intro θ _; ring
  rw [Bfun, Phi1, BHfun]
  rw [show (∫ θ in Work.Spaces.Iθ, Ainner Ψ z θ)
      = ∫ θ in Work.Spaces.Iθ, (cw z * (sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z)
          + sig θ * (G Ψ z θ * H Ψ z θ) * w2 z) from
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
        simp only [Ainner, G, Phi, H]; rw [cw_eq hz]; ring)]
  rw [MeasureTheory.integral_add (hmGφ.const_mul _) hmGH,
    MeasureTheory.integral_const_mul]

/-! ## Integrability of the `z`-integrands, from the `IPMem` hypotheses -/

theorem integrableOn_Afun (Ψ : ℝ → ℝ → ℝ)
    (hQ : IPMem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Work.Spaces.pthIter 2 Ψ)) :
    IntegrableOn (Afun Ψ) Work.Spaces.Iz := by
  refine MeasureTheory.IntegrableOn.congr_fun hQ.2 ?_ measurableSet_Ici
  intro z _
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => by simp only [Akern])

theorem integrableOn_Phi1 (Ψ : ℝ → ℝ → ℝ) (hUφ : IPMem (G Ψ) (Phi Ψ)) :
    IntegrableOn (Phi1 Ψ) Work.Spaces.Iz := by
  refine MeasureTheory.IntegrableOn.congr_fun hUφ.2 ?_ measurableSet_Ici
  intro z _
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

theorem integrableOn_BHfun (Ψ : ℝ → ℝ → ℝ) (hUH : IPMem (G Ψ) (H Ψ)) :
    IntegrableOn (BHfun Ψ) Work.Spaces.Iz := by
  refine MeasureTheory.IntegrableOn.congr_fun hUH.2 ?_ measurableSet_Ici
  intro z _
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

theorem integrableOn_cwPhi1 (Ψ : ℝ → ℝ → ℝ) (hPhi1 : IntegrableOn (Phi1 Ψ) Work.Spaces.Iz) :
    IntegrableOn (fun z => cw z * Phi1 Ψ z) Work.Spaces.Iz := by
  refine (hPhi1.norm.const_mul 2).mono' ?_ ?_
  · exact measurable_cw.aestronglyMeasurable.mul hPhi1.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    simp only [Real.norm_eq_abs, abs_mul]
    calc |cw z| * |Phi1 Ψ z| ≤ 2 * |Phi1 Ψ z| :=
          mul_le_mul_of_nonneg_right (abs_cw_le_two hz) (abs_nonneg _)
      _ = 2 * ‖Phi1 Ψ z‖ := by rw [Real.norm_eq_abs]

theorem integrableOn_Bfun (Ψ : ℝ → ℝ → ℝ) (hUφ : IPMem (G Ψ) (Phi Ψ))
    (hUH : IPMem (G Ψ) (H Ψ)) : IntegrableOn (Bfun Ψ) Work.Spaces.Iz := by
  have h1 := integrableOn_cwPhi1 Ψ (integrableOn_Phi1 Ψ hUφ)
  have h2 := integrableOn_BHfun Ψ hUH
  refine MeasureTheory.IntegrableOn.congr_fun (h1.add h2) ?_ measurableSet_Ici
  intro z hz
  exact (Bfun_eq Ψ hUφ hUH hz).symm

/-! ## The cut-off identity in the language of the `z`-integrands -/

theorem IP_cut_eq (n : ℕ) (Ψ : ℝ → ℝ → ℝ) :
    IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
        (Work.Spaces.pthIter 2 Ψ)
      = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z * Afun Ψ z := by
  rw [IP]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [show (∫ θ in Work.Spaces.Iθ, (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        * Work.FTS.EllipticEst.cut n z) z θ * (Work.Spaces.pthIter 2 Ψ) z θ * w2 z * sig θ)
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.cut n z
          * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * Work.Spaces.pthIter 2 Ψ z θ
              * w2 z * sig θ) from
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_const_mul]
  rfl

/-! ## The limit `n → ∞` -/

/-- **The radial integration by parts of `I₁`.** -/
theorem I1_ibp_identity (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ)
    (hQ : IPMem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Work.Spaces.pthIter 2 Ψ))
    (hU : IPMem (G Ψ) (G Ψ)) (hφ : IPMem (Phi Ψ) (Phi Ψ)) (hH : IPMem (H Ψ) (H Ψ)) :
    IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.pthIter 2 Ψ)
      = - IP (G Ψ) (H Ψ) - IP (G Ψ) (fun z θ => cw z * Phi Ψ z θ) := by
  obtain ⟨hUφ, hUH, -, -⟩ := Work.AngSecond.I1_honesty Ψ hΨ hU hφ hH
  have hAfun : IntegrableOn (Afun Ψ) Work.Spaces.Iz := integrableOn_Afun Ψ hQ
  have hPhi1 : IntegrableOn (Phi1 Ψ) Work.Spaces.Iz := integrableOn_Phi1 Ψ hUφ
  have hBfun : IntegrableOn (Bfun Ψ) Work.Spaces.Iz := integrableOn_Bfun Ψ hUφ hUH
  have hkey : ∀ n : ℕ, (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z * Afun Ψ z)
      = (- (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z * Bfun Ψ z))
        - (∫ z in Work.Spaces.Iz, Phi1 Ψ z * (z * deriv (Work.FTS.EllipticEst.cut n) z)) := by
    intro n
    have h1 := I1_cutoff_identity_alt n Ψ hΨ
    rw [IP_cut_eq n Ψ] at h1
    have h2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, sig θ * nice n Ψ z θ)
        = (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z * Bfun Ψ z)
          + (∫ z in Work.Spaces.Iz,
              Phi1 Ψ z * (z * deriv (Work.FTS.EllipticEst.cut n) z)) := by
      rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, sig θ * nice n Ψ z θ)
          = ∫ z in Work.Spaces.Iz, (Work.FTS.EllipticEst.cut n z * Bfun Ψ z
              + Phi1 Ψ z * (z * deriv (Work.FTS.EllipticEst.cut n) z)) from
          setIntegral_congr_fun measurableSet_Ici (fun z hz => nfun_eq n Ψ hUφ hUH hz)]
      exact MeasureTheory.integral_add (integrableOn_cut_mul hBfun n)
        (integrableOn_cutDeriv_mul hPhi1 n)
    rw [h1, h2]
    ring
  have htA := tendsto_setIntegral_cut_mul hAfun
  have htB := tendsto_setIntegral_cut_mul hBfun
  have htC := tendsto_setIntegral_cutDeriv_mul hPhi1
  have hseq : (fun n : ℕ => ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z * Afun Ψ z)
      = fun n : ℕ => (- (∫ z in Work.Spaces.Iz,
            Work.FTS.EllipticEst.cut n z * Bfun Ψ z))
          - (∫ z in Work.Spaces.Iz,
              Phi1 Ψ z * (z * deriv (Work.FTS.EllipticEst.cut n) z)) :=
    funext hkey
  rw [hseq] at htA
  have hlim : (∫ z in Work.Spaces.Iz, Afun Ψ z)
      = (- (∫ z in Work.Spaces.Iz, Bfun Ψ z)) - 0 := tendsto_nhds_unique htA (htB.neg.sub htC)
  have hA : (∫ z in Work.Spaces.Iz, Afun Ψ z)
      = IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.pthIter 2 Ψ) := by
    rw [IP]
    refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by simp only [Akern])
  have hPhi1c : (∫ z in Work.Spaces.Iz, cw z * Phi1 Ψ z)
      = IP (G Ψ) (fun z θ => cw z * Phi Ψ z θ) := by
    rw [show (∫ z in Work.Spaces.Iz, cw z * Phi1 Ψ z)
        = ∫ z in Work.Spaces.Iz, Cwfun Ψ z from
        setIntegral_congr_fun measurableSet_Ici (fun z _ => by
          rw [Cwfun, Phi1, ← MeasureTheory.integral_const_mul]
          exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring))]
    rw [IP]
    exact setIntegral_congr_fun measurableSet_Ici (fun z _ =>
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring))
  have hBHc : (∫ z in Work.Spaces.Iz, BHfun Ψ z) = IP (G Ψ) (H Ψ) := by
    rw [IP]
    exact setIntegral_congr_fun measurableSet_Ici (fun z _ =>
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring))
  have hBZ : (∫ z in Work.Spaces.Iz, Bfun Ψ z)
      = IP (G Ψ) (H Ψ) + IP (G Ψ) (fun z θ => cw z * Phi Ψ z θ) := by
    have hsplit : (∫ z in Work.Spaces.Iz, Bfun Ψ z)
        = ∫ z in Work.Spaces.Iz, (cw z * Phi1 Ψ z + BHfun Ψ z) :=
      setIntegral_congr_fun measurableSet_Ici (fun z hz => Bfun_eq Ψ hUφ hUH hz)
    rw [hsplit, MeasureTheory.integral_add (integrableOn_cwPhi1 Ψ hPhi1)
      (integrableOn_BHfun Ψ hUH), hPhi1c, hBHc]
    ring
  have hgoal : (∫ z in Work.Spaces.Iz, Afun Ψ z)
      = - IP (G Ψ) (H Ψ) - IP (G Ψ) (fun z θ => cw z * Phi Ψ z θ) := by
    rw [hlim, hBZ]
    ring
  rw [← hA]
  exact hgoal

end Work.FTS.EllipticEst.AngSecond
