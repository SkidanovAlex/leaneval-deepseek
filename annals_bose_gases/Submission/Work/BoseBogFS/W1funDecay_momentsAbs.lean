import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Submission.Work.BoseBogFS.decay_radial_complex_explicit
import Submission.Work.BoseBogFS.g0_profile_scale_facts
import Submission.Work.BoseBogFS.momentbound_theta_factor
import Submission.Work.BoseBoxFock.kinFT_comp_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open MeasureTheory Metric
open scoped Real Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)
set_option maxHeartbeats 1000000

/-- Elementary arithmetic: for `R > 0`, `x ≥ 0` and `m ≤ 2`,
`R^(m+1)/(1+R*x) ≤ (1+R)^3/(1+x)`. -/
lemma rpow_ratio_le {R x : ℝ} {m : ℕ} (hR : 0 < R) (hx : 0 ≤ x) (hm : m ≤ 2) :
    R ^ (m + 1) / (1 + R * x) ≤ (1 + R) ^ 3 / (1 + x) := by
  have hR0 : (0 : ℝ) ≤ R := le_of_lt hR
  have h1 : R ^ (m + 1) ≤ (1 + R) ^ 3 := by
    have h : m + 1 ≤ 3 := by omega
    exact le_trans (pow_le_pow_left₀ hR0 (by linarith) (m + 1))
      (pow_le_pow_right₀ (by linarith) h)
  have h2 : R ^ m ≤ (1 + R) ^ 3 := by
    have h : m ≤ 3 := by omega
    exact le_trans (pow_le_pow_left₀ hR0 (by linarith) m) (pow_le_pow_right₀ (by linarith) h)
  have h2' : R ^ (m + 1) ≤ R * (1 + R) ^ 3 := by
    calc R ^ (m + 1) = R ^ m * R := pow_succ R m
      _ ≤ (1 + R) ^ 3 * R := mul_le_mul_of_nonneg_right h2 hR0
      _ = R * (1 + R) ^ 3 := by ring
  have hkey : R ^ (m + 1) * (1 + x) ≤ (1 + R) ^ 3 * (1 + R * x) := by
    have hx1 : x * R ^ (m + 1) ≤ x * (R * (1 + R) ^ 3) := mul_le_mul_of_nonneg_left h2' hx
    nlinarith [h1, hx1, hx, mul_nonneg hx hR0]
  have hd1 : (0 : ℝ) < 1 + R * x := by positivity
  have hd2 : (0 : ℝ) < 1 + x := by linarith
  rw [div_le_div_iff₀ hd1 hd2]
  linarith [hkey]

/-- Pointwise identity of the scaled picture: the moment function of `W₁` evaluated at
`R • z`, written in terms of the rescaled weight
`ρ(t) = R^m · g₀((R t) • e₀)` and the smooth factor
`G z = z_j^m · theta ((χ⋆χ)(ε z)) · beta z`, where `ε = R/ℓ`. -/
lemma W1fun_scaled_pointwise {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) {m : ℕ} {j : Fin 3} (z : E3) :
    (((R • z).ofLp j : ℝ) ^ m) * Work.BoseFixR.W1fun v h ℓ (R • z)
      = (R ^ m * Submission.BoseGases.g0 v h ((R * ‖z‖) • Work.BoseFixR.LatGreen.axis0))
          * (((z.ofLp j : ℝ) ^ m * theta (Submission.BoseGases.convScale (R / ℓ)⁻¹ z))
              * beta z) := by
  have hR0 : (0 : ℝ) ≤ R := le_of_lt hR
  have hsmul : ((R • z).ofLp j : ℝ) = R * (z.ofLp j : ℝ) := by simp
  have hg0 : Submission.BoseGases.g0 v h (R • z)
      = Submission.BoseGases.g0 v h ((R * ‖z‖) • Work.BoseFixR.LatGreen.axis0) := by
    rw [Work.BoseFixR.LatGreen.g0_eq_axisProfile h hvrad (R • z), norm_smul,
      Real.norm_of_nonneg hR0]
  have hscale : Submission.BoseGases.convScale ℓ (R • z)
      = Submission.BoseGases.convScale (R / ℓ)⁻¹ z := by
    show Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi
        ((ℓ⁻¹) • (R • z)) = Submission.BoseGases.conv3 Submission.BoseGases.chi
          Submission.BoseGases.chi (((R / ℓ)⁻¹)⁻¹ • z)
    rw [smul_smul, inv_inv]
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  have hW1 : Work.BoseFixR.W1fun v h ℓ (R • z)
      = Submission.BoseGases.g0 v h (R • z) / Submission.BoseGases.convScale ℓ (R • z) := rfl
  obtain ⟨hvan, _hmeas, _hint, _hintb⟩ :=
    g0_profile_scale_facts (v := v) (h := h) (R := R) hR hv hvrad hv_supp
  by_cases hzero : Submission.BoseGases.g0 v h (R • z) = 0
  · rw [hW1, hzero, zero_div, mul_zero, ← hg0, hzero, mul_zero, zero_mul]
  · have hzlt : ‖z‖ < 1 := by
      by_contra hcon
      have hge : (1 : ℝ) ≤ ‖z‖ := le_of_not_gt hcon
      exact hzero (by rw [hg0]; exact hvan ‖z‖ hge)
    have hβ : beta z = 1 := beta_one (le_of_lt hzlt)
    have hconv : (1 / 2 : ℝ) ≤ Submission.BoseGases.convScale ℓ (R • z) := by
      refine Submission.BoseGases.convScale_ge_half_ball hℓ hR0 hRℓ ?_
      rw [norm_smul, Real.norm_of_nonneg hR0]
      exact mul_le_of_le_one_right hR0 (le_of_lt hzlt)
    have hcne : Submission.BoseGases.convScale ℓ (R • z) ≠ 0 := by linarith
    have hquarter : (1 / 4 : ℝ) ≤ Submission.BoseGases.convScale ℓ (R • z) := by linarith
    have hθ : theta (Submission.BoseGases.convScale (R / ℓ)⁻¹ z)
        = (Submission.BoseGases.convScale ℓ (R • z))⁻¹ := by
      rw [← hscale]
      rw [theta_eq_inv hquarter, inv_eq_one_div]
    rw [hW1, hg0, hθ, hβ, hsmul, mul_pow, div_eq_mul_inv]
    ring

theorem W1funDecay_momentsAbs : ∃ K : ℝ, 0 ≤ K ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ℓ : ℝ}, 0 < R → 0 < ℓ → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
    tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
    R ≤ ℓ * Submission.BoseGases.chiR0 →
      (∀ (m : ℕ), m ≤ 2 → ∀ j : Fin 3, ∀ q : EuclideanSpace ℝ (Fin 3),
        ‖Submission.BoseGases.kinFT
            (fun y : EuclideanSpace ℝ (Fin 3) =>
              (((y.ofLp j : ℝ) ^ m) * Work.BoseFixR.W1fun v h ℓ y : ℂ)) q‖
          ≤ K * (1 + R) ^ 3 / (1 + ‖q‖)) := by
  have key : ∀ (m : ℕ) (j : Fin 3), ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε →
      ε ≤ Submission.BoseGases.chiR0 →
      (∫ η : E3, (1 + ‖η‖) * ‖FourierTransform.fourier
        (fun z : E3 => (((((z.ofLp j) ^ m : ℝ)
          * theta (Submission.BoseGases.convScale (ε⁻¹) z) * beta z : ℝ)) : ℂ)) η‖) ≤ C :=
    fun m j => momentbound_theta_factor (m := m) (j := j)
  choose Cb hCbnn hCbb using key
  refine ⟨∑ m ∈ Finset.range 3, ∑ j : Fin 3,
    2 * (16 * Real.pi + 8) * (2 * Real.pi) ^ 2 * Cb m j, ?_, ?_⟩
  · refine Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun j _ => ?_
    have h := hCbnn m j
    positivity
  · intro v h R ℓ hR hℓ hv hvrad hv_supp hRℓ m hm j q
    have hR0 : (0 : ℝ) ≤ R := le_of_lt hR
    obtain ⟨hvan, hmeas, hint, hintb⟩ :=
      g0_profile_scale_facts (v := v) (h := h) (R := R) hR hv hvrad hv_supp
    have hεpos : 0 < R / ℓ := div_pos hR hℓ
    have hεchi : R / ℓ ≤ Submission.BoseGases.chiR0 := by
      rw [div_le_iff₀ hℓ]
      simpa [mul_comm] using hRℓ
    set u : E3 → ℂ := fun y => (((y.ofLp j : ℝ) ^ m) * Work.BoseFixR.W1fun v h ℓ y : ℂ) with hu
    set ρ : ℝ → ℝ :=
      fun t => R ^ m * Submission.BoseGases.g0 v h ((R * t) • Work.BoseFixR.LatGreen.axis0)
      with hρdef
    set G : E3 → ℝ := fun z =>
      ((z.ofLp j : ℝ) ^ m * theta (Submission.BoseGases.convScale (R / ℓ)⁻¹ z)) * beta z
      with hGdef
    have hρvan : ∀ t : ℝ, 1 ≤ t → ρ t = 0 := by
      intro t ht
      simp only [hρdef, hvan t ht, mul_zero]
    have hρmeas : AEStronglyMeasurable ρ (volume.restrict (Set.Ioi (0 : ℝ))) := hmeas.const_mul _
    have hρint : IntegrableOn (fun t : ℝ => t * |ρ t|) (Set.Ioi (0 : ℝ)) := by
      have hh : IntegrableOn
          (fun t : ℝ => R ^ m * (t * |Submission.BoseGases.g0 v h ((R * t) • Work.BoseFixR.LatGreen.axis0)|))
          (Set.Ioi (0 : ℝ)) := hint.const_mul (R ^ m)
      refine hh.congr_fun (fun t ht => ?_) measurableSet_Ioi
      show R ^ m * (t * |Submission.BoseGases.g0 v h ((R * t) • Work.BoseFixR.LatGreen.axis0)|)
        = t * |ρ t|
      simp only [hρdef]
      rw [abs_mul, abs_of_nonneg (pow_nonneg hR0 m)]
      ring
    have hρbound : (∫ t in Set.Ioi (0 : ℝ), t * |ρ t|) ≤ R ^ m * (2 / R ^ 2) := by
      have heq : (∫ t in Set.Ioi (0 : ℝ), t * |ρ t|)
          = R ^ m * (∫ t in Set.Ioi (0 : ℝ),
              t * |Submission.BoseGases.g0 v h ((R * t) • Work.BoseFixR.LatGreen.axis0)|) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        simp only [hρdef]
        rw [abs_mul, abs_of_nonneg (pow_nonneg hR0 m)]
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hintb (pow_nonneg hR0 m)
    have hGcd : ∀ n : ℕ, ContDiff ℝ n G := by
      intro n
      simp only [hGdef]
      refine ContDiff.mul ?_ (beta_contDiff n)
      refine ContDiff.mul (by fun_prop) ?_
      exact (theta_contDiff n).comp
        ((Work.BoseFixR.LatGreen.convScale_contDiff (R / ℓ)⁻¹).of_le (WithTop.coe_le_coe.mpr le_top))
    have hGcs : HasCompactSupport G := by
      simp only [hGdef]
      exact beta_hasCompactSupport.mul_left
    have hA := decay_radial_complex_explicit (ρ := ρ) (G := G) (R := 1) one_pos
      hρvan hρmeas hρint hGcd hGcs (R • q)
    have hMle : (∫ η : E3,
        (1 + ‖η‖) * ‖FourierTransform.fourier (fun x : E3 => (G x : ℂ)) η‖) ≤ Cb m j := by
      simp only [hGdef]
      exact hCbb m j (R / ℓ) hεpos hεchi
    have hA' : ‖∫ z : E3, (((ρ ‖z‖ : ℝ) : ℂ) * ((G z : ℝ) : ℂ))
          * Complex.exp (-(Complex.I * (inner ℝ (R • q) z : ℂ)))‖
        ≤ ((16 * Real.pi + 8) * (∫ r in Set.Ioi (0 : ℝ), r * |ρ r|) * (2 * Real.pi) ^ 2 * Cb m j)
          / (1 + ‖R • q‖) := by
      refine hA.trans ?_
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc (8 * Real.pi * ((1 : ℝ) + 1) + 8) * (∫ r in Set.Ioi (0 : ℝ), r * |ρ r|)
              * (2 * Real.pi) ^ 2
              * (∫ η : E3,
                  (1 + ‖η‖) * ‖FourierTransform.fourier (fun x : E3 => (G x : ℂ)) η‖)
          ≤ (8 * Real.pi * ((1 : ℝ) + 1) + 8) * (∫ r in Set.Ioi (0 : ℝ), r * |ρ r|)
              * (2 * Real.pi) ^ 2 * Cb m j :=
            mul_le_mul_of_nonneg_left hMle (by
              have hL : (0:ℝ) ≤ ∫ r in Set.Ioi (0 : ℝ), r * |ρ r| :=
                setIntegral_nonneg measurableSet_Ioi (fun r hr => mul_nonneg hr.le (abs_nonneg _))
              positivity)
        _ = (16 * Real.pi + 8) * (∫ r in Set.Ioi (0 : ℝ), r * |ρ r|)
              * (2 * Real.pi) ^ 2 * Cb m j := by ring
    have hsub := Work.BoseBoxFock.kinFT_comp_smul (ℓ := R) hR u (R • q)
    have hRinv : R⁻¹ • (R • q) = q := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hR), one_smul]
    rw [hRinv] at hsub
    have hkin : Submission.BoseGases.kinFT u q
        = (↑(R ^ 3) : ℂ) * ∫ y : E3,
            Complex.exp (-(Complex.I * (inner ℝ (R • q) y : ℂ))) * u (R • y) := by
      have hne : (↑(R ^ 3) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact pow_ne_zero 3 (ne_of_gt hR)
      rw [hsub]
      rw [Complex.ofReal_inv (R ^ 3), ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    have hpt : ∀ z : E3, Complex.exp (-(Complex.I * (inner ℝ (R • q) z : ℂ))) * u (R • z)
        = (((ρ ‖z‖ : ℝ) : ℂ) * ((G z : ℝ) : ℂ))
          * Complex.exp (-(Complex.I * (inner ℝ (R • q) z : ℂ))) := by
      intro z
      have hmain : u (R • z) = (((ρ ‖z‖ : ℝ) : ℂ) * ((G z : ℝ) : ℂ)) := by
        have hp := W1fun_scaled_pointwise (v := v) (h := h) hR hℓ hv hvrad hv_supp hRℓ
          (m := m) (j := j) z
        simp only [hu, hρdef, hGdef]
        exact_mod_cast hp
      rw [hmain, mul_comm (Complex.exp (-(Complex.I * (inner ℝ (R • q) z : ℂ))))]
    have hcpos : (0 : ℝ) ≤ 2 * (16 * Real.pi + 8) * (2 * Real.pi) ^ 2 := by positivity
    have hKnn : (0 : ℝ) ≤ 2 * (16 * Real.pi + 8) * (2 * Real.pi) ^ 2 * Cb m j :=
      mul_nonneg hcpos (hCbnn m j)
    have hKle : 2 * (16 * Real.pi + 8) * (2 * Real.pi) ^ 2 * Cb m j
        ≤ ∑ m ∈ Finset.range 3, ∑ j : Fin 3,
            2 * (16 * Real.pi + 8) * (2 * Real.pi) ^ 2 * Cb m j := by
      have hmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
      refine le_trans
        (Finset.single_le_sum (s := Finset.univ)
          (f := fun j' : Fin 3 => 2 * (16 * Real.pi + 8) * (2 * Real.pi) ^ 2 * Cb m j')
          (fun j' _ => mul_nonneg hcpos (hCbnn m j')) (Finset.mem_univ j)) ?_
      refine Finset.single_le_sum (s := Finset.range 3)
        (f := fun m' : ℕ => ∑ j' : Fin 3,
          2 * (16 * Real.pi + 8) * (2 * Real.pi) ^ 2 * Cb m' j') ?_ hmem
      intro m' _
      exact Finset.sum_nonneg fun j' _ => mul_nonneg hcpos (hCbnn m' j')
    calc ‖Submission.BoseGases.kinFT u q‖
        = ‖(↑(R ^ 3) : ℂ) * ∫ y : E3,
            Complex.exp (-(Complex.I * (inner ℝ (R • q) y : ℂ))) * u (R • y)‖ := by rw [hkin]
      _ = R ^ 3 * ‖∫ y : E3,
            Complex.exp (-(Complex.I * (inner ℝ (R • q) y : ℂ))) * u (R • y)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hR0 3)]
      _ = R ^ 3 * ‖∫ z : E3, (((ρ ‖z‖ : ℝ) : ℂ) * ((G z : ℝ) : ℂ))
            * Complex.exp (-(Complex.I * (inner ℝ (R • q) z : ℂ)))‖ := by
            rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      _ ≤ R ^ 3 * (((16 * Real.pi + 8) * (∫ r in Set.Ioi (0 : ℝ), r * |ρ r|)
            * (2 * Real.pi) ^ 2 * Cb m j) / (1 + ‖R • q‖)) :=
            mul_le_mul_of_nonneg_left hA' (pow_nonneg hR0 3)
      _ ≤ R ^ 3 * (((16 * Real.pi + 8) * (R ^ m * (2 / R ^ 2))
            * (2 * Real.pi) ^ 2 * Cb m j) / (1 + R * ‖q‖)) := by
            rw [norm_smul, Real.norm_of_nonneg hR0]
            have hn16 : (0 : ℝ) ≤ 16 * Real.pi + 8 := by positivity
            have hn2π : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := by positivity
            have hL : (0 : ℝ) ≤ ∫ r in Set.Ioi (0 : ℝ), r * |ρ r| :=
              setIntegral_nonneg measurableSet_Ioi (fun r hr => mul_nonneg hr.le (abs_nonneg _))
            have hkey2 : ((16 * Real.pi + 8) * (2 * Real.pi) ^ 2)
                  * ((∫ r in Set.Ioi (0 : ℝ), r * |ρ r|) * Cb m j)
                ≤ ((16 * Real.pi + 8) * (2 * Real.pi) ^ 2)
                  * ((R ^ m * (2 / R ^ 2)) * Cb m j) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρbound (hCbnn m j))
                (mul_nonneg hn16 hn2π)
            have hden : (0 : ℝ) < 1 + R * ‖q‖ := by
              have hq := norm_nonneg q
              nlinarith [mul_nonneg hR0 hq]
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hR0 3)
            refine div_le_div_of_nonneg_right ?_ hden.le
            calc (16 * Real.pi + 8) * (∫ r in Set.Ioi (0 : ℝ), r * |ρ r|)
                    * (2 * Real.pi) ^ 2 * Cb m j
                = ((16 * Real.pi + 8) * (2 * Real.pi) ^ 2)
                    * ((∫ r in Set.Ioi (0 : ℝ), r * |ρ r|) * Cb m j) := by ring
              _ ≤ ((16 * Real.pi + 8) * (2 * Real.pi) ^ 2)
                    * ((R ^ m * (2 / R ^ 2)) * Cb m j) := hkey2
              _ = (16 * Real.pi + 8) * (R ^ m * (2 / R ^ 2))
                    * (2 * Real.pi) ^ 2 * Cb m j := by ring
      _ = 2 * (16 * Real.pi + 8) * (2 * Real.pi) ^ 2 * Cb m j
            * (R ^ (m + 1) / (1 + R * ‖q‖)) := by
            field_simp
            ring
      _ ≤ 2 * (16 * Real.pi + 8) * (2 * Real.pi) ^ 2 * Cb m j
            * ((1 + R) ^ 3 / (1 + ‖q‖)) := by
            refine mul_le_mul_of_nonneg_left (rpow_ratio_le hR (norm_nonneg q) hm) hKnn
      _ ≤ (∑ m ∈ Finset.range 3, ∑ j : Fin 3,
            2 * (16 * Real.pi + 8) * (2 * Real.pi) ^ 2 * Cb m j)
            * ((1 + R) ^ 3 / (1 + ‖q‖)) := by
            refine mul_le_mul_of_nonneg_right hKle (div_nonneg (by positivity) (by positivity))
      _ = (∑ m ∈ Finset.range 3, ∑ j : Fin 3,
            2 * (16 * Real.pi + 8) * (2 * Real.pi) ^ 2 * Cb m j) * (1 + R) ^ 3 / (1 + ‖q‖) := by
            rw [mul_div_assoc]

end Work.BoseBogFS
