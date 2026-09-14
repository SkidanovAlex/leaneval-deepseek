import Submission.NBody.MarchalTransferLimit
import Submission.NBody.MarchalPairRatio
import Submission.NBody.MarchalClusterShapeSecondDeriv
import Submission.NBody.MarchalOutsideVelocity

/-!
# Assembling the hypotheses of the transfer

`Submission.NBody.tendsto_transfer_of_data` (`Submission/NBody/MarchalTransferLimit.lean`) needs
four analytic inputs about the rescaled configurations `q^λ`.  This module produces them from the
Sundman asymptotics:

* `eventually_uniform_rescaledCentered` — uniform convergence `q^λ → q̄` on `(0,T]`.

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- `λ^{-2/3}√I = t^{2/3}√(I/(tλ)^{4/3})`. -/
private lemma rpow_sqrt_key (I lam t : ℝ) (hI : 0 ≤ I) (hlam : 0 < lam) (ht : 0 < t) :
    lam ^ (-(2:ℝ)/3) * Real.sqrt I = t ^ ((2:ℝ)/3) * Real.sqrt (I / (t * lam) ^ ((4:ℝ)/3)) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have h1 : (I / (t * lam) ^ ((4:ℝ)/3)) ^ ((1:ℝ)/2)
      = I ^ ((1:ℝ)/2) / (t * lam) ^ ((2:ℝ)/3) := by
    rw [Real.div_rpow hI (Real.rpow_nonneg (mul_pos ht hlam).le _)]
    rw [← Real.rpow_mul (mul_pos ht hlam).le]
    norm_num
  rw [h1, Real.mul_rpow ht.le hlam.le]
  field_simp
  rw [mul_right_comm, ← Real.rpow_add hlam]
  norm_num

/-- `|√a - √b| ≤ |a - b| / √b` for `a ≥ 0`, `b > 0`. -/
private lemma abs_sqrt_sub_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    |Real.sqrt a - Real.sqrt b| ≤ |a - b| / Real.sqrt b := by
  have hb' : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hab : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    have h1 : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha
    have h2 : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
    nlinarith [h1, h2]
  have h : Real.sqrt a - Real.sqrt b = (a - b) / (Real.sqrt a + Real.sqrt b) := by
    rw [eq_div_iff (by positivity : Real.sqrt a + Real.sqrt b ≠ 0)]
    exact hab
  rw [h, abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.sqrt a + Real.sqrt b)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hb'
    (le_add_of_nonneg_left (Real.sqrt_nonneg a))

/-- **Uniform convergence of the blow-up.**  The convergence `q^λ → q̄` is uniform on `(0,T]`, which
is what the dominated-convergence transfer needs in order to keep the perturbed configurations away
from collisions. -/
theorem eventually_uniform_rescaledCentered {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε κ T : ℝ} {sbar : EN E N}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hκ : 0 < κ) (hT : 0 < T)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hs : Tendsto (fun s : ℝ => clusterShape m k (x s)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ (lam : ℝ) in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      ‖rescaledCentered m k x lam t - blowUpProfile κ sbar t‖ ≤ η := by
  -- constants
  have hM1 : (0:ℝ) < ‖sbar‖ + 1 := by positivity
  have hM2 : (0:ℝ) < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hc₁ : (0:ℝ) < (Real.sqrt κ * η) / (4 * (T ^ ((2:ℝ)/3) * (‖sbar‖ + 1))) := by positivity
  have hc₂ : (0:ℝ) < η / (4 * (T ^ ((2:ℝ)/3) * Real.sqrt κ)) := by positivity
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ Ioo (0:ℝ) δ,
      |clusterInertia m k (x u) / u ^ ((4:ℝ)/3) - κ| ≤
        (Real.sqrt κ * η) / (4 * (T ^ ((2:ℝ)/3) * (‖sbar‖ + 1))) := by
    have h1 : ∀ᶠ u in nhdsWithin (0:ℝ) (Ioi 0),
        |clusterInertia m k (x u) / u ^ ((4:ℝ)/3) - κ| ≤
          (Real.sqrt κ * η) / (4 * (T ^ ((2:ℝ)/3) * (‖sbar‖ + 1))) :=
      hIn.eventually (Metric.closedBall_mem_nhds κ hc₁)
    rw [eventually_nhdsWithin_iff] at h1
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp h1
    exact ⟨δ, hδpos, fun u hu => hδ u (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu.1]; exact hu.2) hu.1⟩
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ Ioo (0:ℝ) δ,
      ‖clusterShape m k (x u) - sbar‖ ≤ η / (4 * (T ^ ((2:ℝ)/3) * Real.sqrt κ)) := by
    have h1 : ∀ᶠ u in nhdsWithin (0:ℝ) (Ioi 0),
        ‖clusterShape m k (x u) - sbar‖ ≤ η / (4 * (T ^ ((2:ℝ)/3) * Real.sqrt κ)) :=
      by
      filter_upwards [hs.eventually (Metric.closedBall_mem_nhds sbar hc₂)] with u hu
      simpa only [dist_eq_norm] using hu
    rw [eventually_nhdsWithin_iff] at h1
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp h1
    exact ⟨δ, hδpos, fun u hu => hδ u (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu.1]; exact hu.2) hu.1⟩
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ Ioo (0:ℝ) δ,
      ‖clusterShape m k (x u)‖ ≤ ‖sbar‖ + 1 := by
    have h1 : ∀ᶠ u in nhdsWithin (0:ℝ) (Ioi 0),
        ‖clusterShape m k (x u) - sbar‖ ≤ 1 := by
      filter_upwards [hs.eventually (Metric.closedBall_mem_nhds sbar (by norm_num : (0:ℝ) < 1))]
        with u hu
      simpa only [dist_eq_norm] using hu
    rw [eventually_nhdsWithin_iff] at h1
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp h1
    refine ⟨δ, hδpos, fun u hu => ?_⟩
    have h2 := hδ u (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu.1]; exact hu.2) hu.1
    calc ‖clusterShape m k (x u)‖ = ‖(clusterShape m k (x u) - sbar) + sbar‖ := by rw [sub_add_cancel]
      _ ≤ ‖clusterShape m k (x u) - sbar‖ + ‖sbar‖ := norm_add_le _ _
      _ ≤ 1 + ‖sbar‖ := by linarith
      _ = ‖sbar‖ + 1 := by ring
  set δ₃ : ℝ := min (min δ₁ δ₂) (min δ₀ ε) with hδ₃
  have hδ₃pos : 0 < δ₃ := lt_min (lt_min hδ₁pos hδ₂pos) (lt_min hδ₀pos hε)
  filter_upwards [self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (show 0 < δ₃ / T from div_pos hδ₃pos hT)] with lam hlam hlamδ
  intro t ht
  have hlam0 : 0 < lam := hlam
  have hlamlt : lam < δ₃ / T := hlamδ.2
  have hδT : T * (δ₃ / T) = δ₃ := by field_simp
  have hlt : t * lam < δ₃ := by
    have h2 : T * lam < δ₃ := by rw [← hδT]; exact mul_lt_mul_of_pos_left hlamlt hT
    linarith [mul_le_mul_of_nonneg_right ht.2 hlam0.le]
  have hu : t * lam ∈ Ioo (0:ℝ) δ₃ := ⟨mul_pos ht.1 hlam0, hlt⟩
  have hδ₃_le₁ : δ₃ ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₃_le₂ : δ₃ ≤ δ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₃_le₀ : δ₃ ≤ δ₀ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₃_leε : δ₃ ≤ ε := le_trans (min_le_right _ _) (min_le_right _ _)
  have hu₁ : t * lam ∈ Ioo (0:ℝ) δ₁ := ⟨hu.1, lt_of_lt_of_le hu.2 hδ₃_le₁⟩
  have hu₂ : t * lam ∈ Ioo (0:ℝ) δ₂ := ⟨hu.1, lt_of_lt_of_le hu.2 hδ₃_le₂⟩
  have hu₀ : t * lam ∈ Ioo (0:ℝ) δ₀ := ⟨hu.1, lt_of_lt_of_le hu.2 hδ₃_le₀⟩
  have huε : t * lam ∈ Ioo (0:ℝ) ε := ⟨hu.1, lt_of_lt_of_le hu.2 hδ₃_leε⟩
  set u : ℝ := t * lam with hu_def
  have hIpos : 0 < clusterInertia m k (x u) := clusterInertia_pos hm hk2 (hnc u huε)
  have hcm : cmRel m k (x u) = Real.sqrt (clusterInertia m k (x u)) • clusterShape m k (x u) :=
    cmRel_eq_sqrt_smul_clusterShape hIpos
  -- the key factorisation
  have hkey : lam ^ (-(2:ℝ)/3) * Real.sqrt (clusterInertia m k (x u))
      = t ^ ((2:ℝ)/3) * Real.sqrt (clusterInertia m k (x u) / u ^ ((4:ℝ)/3)) := by
    rw [hu_def]
    exact rpow_sqrt_key _ _ _ hIpos.le hlam0 ht.1
  -- the two small quantities
  have hA : |Real.sqrt (clusterInertia m k (x u) / u ^ ((4:ℝ)/3)) - Real.sqrt κ| ≤
      η / (4 * (T ^ ((2:ℝ)/3) * (‖sbar‖ + 1))) := by
    have ha : (0:ℝ) ≤ clusterInertia m k (x u) / u ^ ((4:ℝ)/3) :=
      div_nonneg hIpos.le (Real.rpow_nonneg hu.1.le _)
    have h1 := abs_sqrt_sub_sqrt_le ha hκ
    have h2 := hδ₁ u hu₁
    have h3 : |clusterInertia m k (x u) / u ^ ((4:ℝ)/3) - κ| / Real.sqrt κ
        ≤ ((Real.sqrt κ * η) / (4 * (T ^ ((2:ℝ)/3) * (‖sbar‖ + 1)))) / Real.sqrt κ :=
      div_le_div_of_nonneg_right h2 hM2.le
    have h4 : ((Real.sqrt κ * η) / (4 * (T ^ ((2:ℝ)/3) * (‖sbar‖ + 1)))) / Real.sqrt κ
        = η / (4 * (T ^ ((2:ℝ)/3) * (‖sbar‖ + 1))) := by
      field_simp
    linarith [h1, h3, h4.ge, h4.le]
  have hB : ‖clusterShape m k (x u) - sbar‖ ≤ η / (4 * (T ^ ((2:ℝ)/3) * Real.sqrt κ)) :=
    hδ₂ u hu₂
  have hC : ‖clusterShape m k (x u)‖ ≤ ‖sbar‖ + 1 := hδ₀ u hu₀
  have hM1pos : (0:ℝ) < T ^ ((2:ℝ)/3) * (‖sbar‖ + 1) := by positivity
  have hT23 : (0:ℝ) < T ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos hT _
  have ht23le : t ^ ((2:ℝ)/3) ≤ T ^ ((2:ℝ)/3) :=
    Real.rpow_le_rpow ht.1.le ht.2 (by norm_num)
  set A : ℝ := Real.sqrt (clusterInertia m k (x u) / u ^ ((4:ℝ)/3)) with hAdef
  set S : EN E N := clusterShape m k (x u) with hSdef
  have h2 : |A - Real.sqrt κ| * ‖S‖ ≤ η / (4 * T ^ ((2:ℝ)/3)) := by
    have h4 : |A - Real.sqrt κ| * (‖sbar‖ + 1) ≤ η / (4 * T ^ ((2:ℝ)/3)) := by
      have h5 := mul_le_mul_of_nonneg_right hA hM1.le
      have h6 : (η / (4 * (T ^ ((2:ℝ)/3) * (‖sbar‖ + 1)))) * (‖sbar‖ + 1)
          = η / (4 * T ^ ((2:ℝ)/3)) := by
        rw [div_mul_eq_mul_div]
        field_simp
      linarith [h5, h6.le, h6.ge]
    nlinarith [hC, h4, abs_nonneg (A - Real.sqrt κ),
      le_abs_self (A - Real.sqrt κ), neg_abs_le (A - Real.sqrt κ), hM1]
  have h3 : Real.sqrt κ * ‖S - sbar‖ ≤ η / (4 * T ^ ((2:ℝ)/3)) := by
    have h5 := mul_le_mul_of_nonneg_left hB hM2.le
    have h6 : Real.sqrt κ * (η / (4 * (T ^ ((2:ℝ)/3) * Real.sqrt κ)))
        = η / (4 * T ^ ((2:ℝ)/3)) := by
      field_simp
    linarith [h5, h6.le, h6.ge]
  have h1' : ‖(A - Real.sqrt κ) • S + Real.sqrt κ • (S - sbar)‖
      ≤ |A - Real.sqrt κ| * ‖S‖ + Real.sqrt κ * ‖S - sbar‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg hM2.le]
  have hres' : rescaledCentered m k x lam t - blowUpProfile κ sbar t
      = t ^ ((2:ℝ)/3) • ((A - Real.sqrt κ) • S + Real.sqrt κ • (S - sbar)) := by
    rw [rescaledCentered, blowUpProfile, hcm, hu_def]
    simp only [smul_smul]
    rw [hkey]
    rw [hAdef, hSdef]
    module
  rw [hres']
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  have h10 : t ^ ((2:ℝ)/3) * ‖(A - Real.sqrt κ) • S + Real.sqrt κ • (S - sbar)‖
      ≤ t ^ ((2:ℝ)/3) * (η / (4 * T ^ ((2:ℝ)/3)) + η / (4 * T ^ ((2:ℝ)/3))) :=
    mul_le_mul_of_nonneg_left (le_trans h1' (by linarith [h2, h3])) (Real.rpow_nonneg ht.1.le _)
  have h11 : t ^ ((2:ℝ)/3) * (η / (4 * T ^ ((2:ℝ)/3)) + η / (4 * T ^ ((2:ℝ)/3)))
      = t ^ ((2:ℝ)/3) * (η / (4 * T ^ ((2:ℝ)/3)))
        + t ^ ((2:ℝ)/3) * (η / (4 * T ^ ((2:ℝ)/3))) := by ring
  have h7 : t ^ ((2:ℝ)/3) * (η / (4 * T ^ ((2:ℝ)/3))) ≤ η / 4 := by
    have h8 : t ^ ((2:ℝ)/3) / (4 * T ^ ((2:ℝ)/3)) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [ht23le]
    have h9 : t ^ ((2:ℝ)/3) * (η / (4 * T ^ ((2:ℝ)/3)))
        = η * (t ^ ((2:ℝ)/3) / (4 * T ^ ((2:ℝ)/3))) := by ring
    rw [h9]
    nlinarith [h8, hη]
  linarith [h10, h11.le, h11.ge, h7]

end Submission.NBody
