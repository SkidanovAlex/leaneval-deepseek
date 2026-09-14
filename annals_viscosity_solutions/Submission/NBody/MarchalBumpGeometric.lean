import Submission.NBody.MarchalBumpSign
import Submission.Commons.Analysis.Integral.intervalIntegrable_potential_gain_integrand

/-!
# The geometric potential gain of the symmetric bump

Combining the coordinate form of the rescaled pair differences (`MarchalBumpSign`) with the
one-sided bounds on the pair separations and the outward sign condition, this file derives the
quantitative potential gain of the symmetric bump on the blown-up colliding cluster.

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

theorem bump_potential_bound_eventually {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε κ T c C : ℝ} {sbar : EN E N} {i₀ : Fin N} (δ : E)
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hκ : 0 < κ) (hT : 0 < T)
    (hc : 0 < c) (hCc : c < C) (hi₀ : i₀ ∈ k) (hδ : δ ≠ 0)
    (hδT : ‖δ‖ ≤ T / 4) (htA : (‖δ‖ / C) ^ ((3:ℝ)/2) ≤ T / 2)
    (htB : (‖δ‖ / c) ^ ((3:ℝ)/2) ≤ T / 2)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hs : Tendsto (fun s : ℝ => clusterShape m k (x s))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar))
    (hsep : ∀ j ∈ k.erase i₀, sbar i₀ ≠ sbar j)
    (hpos : ∀ j ∈ k.erase i₀, 0 < inner ℝ (sbar i₀ - sbar j) δ)
    (hqmeas : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ j ∈ k.erase i₀,
      MeasureTheory.AEStronglyMeasurable
        (fun t => rescaledCentered m k x lam t i₀ - rescaledCentered m k x lam t j)
        (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) T)))
    (hevbound : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T, ∀ j ∈ k.erase i₀,
      c * t ^ ((2:ℝ)/3) ≤ ‖rescaledCentered m k x lam t i₀ - rescaledCentered m k x lam t j‖ ∧
      ‖rescaledCentered m k x lam t i₀ - rescaledCentered m k x lam t j‖ ≤ C * t ^ ((2:ℝ)/3)) :
    ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      ∫ t in (0:ℝ)..T,
        (clusterPotential m k (rescaledCentered m k x lam t + stdPert m k i₀ δ T t)
          - clusterPotential m k (rescaledCentered m k x lam t))
        ≤ -(∑ j ∈ k.erase i₀, m i₀ * m j)
            * (‖δ‖ ^ ((1:ℝ)/2) * (1 - c ^ 2 / C ^ 2) / (2 * C ^ ((3:ℝ)/2)))
          + (∑ j ∈ k.erase i₀, m i₀ * m j)
            * (2 * ‖δ‖ / (c * (T / 2) ^ ((2:ℝ)/3))) := by
  have hsign_ev : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ j ∈ k.erase i₀, ∀ t ∈ Ioc (0:ℝ) T,
      0 ≤ inner ℝ (rescaledCentered m k x lam t i₀ - rescaledCentered m k x lam t j) δ := by
    rw [Finset.eventually_all]
    intro j hj
    exact eventually_pair_inner_sign (k := k) (x := x) (sbar := sbar) δ hε hκ hT hnc hIn hs
      hm hk2 (hpos j hj)
  have hsign_ev' : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T, ∀ j ∈ k.erase i₀,
      0 ≤ inner ℝ (rescaledCentered m k x lam t i₀ - rescaledCentered m k x lam t j) δ :=
    hsign_ev.mono fun lam h t ht j hj => h j hj t ht
  filter_upwards [hsign_ev', hevbound, hqmeas] with lam hsign hbound hqmeas
  refine bump_potential_bound hm hi₀ δ hδ hT hc hCc hδT htA htB
    (rescaledCentered m k x lam) hbound hsign hqmeas ?_
  intro j hj
  have h := Commons.Analysis.Integral.intervalIntegrable_potential_gain_integrand
    (fun t => rescaledCentered m k x lam t i₀ - rescaledCentered m k x lam t j) δ T c C
    hT hc hCc hδ hδT htA htB (fun t ht => hbound t ht j hj) (fun t ht => hsign t ht j hj)
    (hqmeas j hj)
  refine h.congr fun t _ => ?_
  rw [stdVar_eq_ite hδ]

/-- **Uniform two-sided bounds with explicit constants.**  Version of
`eventually_pair_separation_bounds` in which the constant is the explicit limit
`√κ · ‖s̄ᵢ - s̄ⱼ‖` of the separation ratio. -/
theorem eventually_pair_separation_bounds_explicit {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε κ T : ℝ} {sbar : EN E N}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hκ : 0 < κ) (hT : 0 < T)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hs : Tendsto (fun s : ℝ => clusterShape m k (x s))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar))
    {i j : Fin N} (hi : i ∈ k) (hj : j ∈ k) (hsbar : sbar i ≠ sbar j) :
    ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      (Real.sqrt κ * ‖sbar i - sbar j‖) / 2 * t ^ ((2:ℝ)/3)
          ≤ ‖rescaledCentered m k x lam t i - rescaledCentered m k x lam t j‖ ∧
        ‖rescaledCentered m k x lam t i - rescaledCentered m k x lam t j‖
          ≤ 2 * (Real.sqrt κ * ‖sbar i - sbar j‖) * t ^ ((2:ℝ)/3) := by
  classical
  set K : ℝ := Real.sqrt κ * ‖sbar i - sbar j‖ with hK
  have hKpos : 0 < K := by
    rw [hK]
    exact mul_pos (Real.sqrt_pos.mpr hκ) (norm_pos_iff.mpr (sub_ne_zero.mpr hsbar))
  have hlim := tendsto_pair_separation_ratio (m := m) (k := k) (x := x) (ε := ε) (κ := κ)
    (sbar := sbar) hm hk2 hε hκ hnc hIn hs hi hj (fun h => hsbar (by rw [h]))
  have hlim' : Tendsto (fun s : ℝ => ‖cmRel m k (x s) i - cmRel m k (x s) j‖ / s ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds K) := by
    rw [hK]; exact hlim
  obtain ⟨ε', hε'pos, hε'le, hε'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ∀ s ∈ Ioo (0:ℝ) ε',
      K / 2 ≤ ‖cmRel m k (x s) i - cmRel m k (x s) j‖ / s ^ ((2:ℝ)/3) ∧
        ‖cmRel m k (x s) i - cmRel m k (x s) j‖ / s ^ ((2:ℝ)/3) ≤ 2 * K := by
    have h1 : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0), K / 2 < ‖cmRel m k (x s) i - cmRel m k (x s) j‖
        / s ^ ((2:ℝ)/3) := hlim'.eventually (eventually_gt_nhds (by linarith))
    have h2 : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0), ‖cmRel m k (x s) i - cmRel m k (x s) j‖
        / s ^ ((2:ℝ)/3) < 2 * K := hlim'.eventually (eventually_lt_nhds (by linarith))
    rw [eventually_nhdsWithin_iff] at h1 h2
    obtain ⟨δ1, hδ1pos, hδ1⟩ := Metric.eventually_nhds_iff_ball.mp h1
    obtain ⟨δ2, hδ2pos, hδ2⟩ := Metric.eventually_nhds_iff_ball.mp h2
    refine ⟨min (min δ1 δ2) ε, lt_min (lt_min hδ1pos hδ2pos) hε, min_le_right _ _, ?_⟩
    intro s hs'
    have hs0 : 0 < s := hs'.1
    have hb1 : s ∈ Metric.ball (0:ℝ) δ1 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs0]
      exact lt_of_lt_of_le hs'.2 (le_trans (min_le_left _ _) (min_le_left _ _))
    have hb2 : s ∈ Metric.ball (0:ℝ) δ2 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs0]
      exact lt_of_lt_of_le hs'.2 (le_trans (min_le_left _ _) (min_le_right _ _))
    exact ⟨(hδ1 s hb1 hs0).le, (hδ2 s hb2 hs0).le⟩
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show 0 < ε' / T from div_pos hε'pos hT)]
    with lam hlam hlamlt
  intro t ht
  have hlam0 : 0 < lam := hlam
  have htl : t * lam < ε' := by
    have h1 : t * lam ≤ T * lam := mul_le_mul_of_nonneg_right ht.2 hlam0.le
    have h2 : T * lam < T * (ε' / T) := mul_lt_mul_of_pos_left hlamlt.2 hT
    have h3 : T * (ε' / T) = ε' := by field_simp
    linarith
  have hs' : t * lam ∈ Ioo (0:ℝ) ε' := ⟨mul_pos ht.1 hlam0, htl⟩
  obtain ⟨hb1, hb2⟩ := hε' (t * lam) hs'
  have hs0 : 0 < t * lam := mul_pos ht.1 hlam0
  have hresc : rescaledCentered m k x lam t i - rescaledCentered m k x lam t j
      = lam ^ (-(2:ℝ)/3) • (cmRel m k (x (t * lam)) i - cmRel m k (x (t * lam)) j) := by
    unfold rescaledCentered
    rw [PiLp.smul_apply (fun _ : Fin N => E), PiLp.smul_apply (fun _ : Fin N => E), smul_sub]
  have hnorm : ‖rescaledCentered m k x lam t i - rescaledCentered m k x lam t j‖
      = lam ^ (-(2:ℝ)/3) * ‖cmRel m k (x (t * lam)) i - cmRel m k (x (t * lam)) j‖ := by
    rw [hresc, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hlam0 _)]
  have hkey2 : lam ^ (-(2:ℝ)/3) * lam ^ ((2:ℝ)/3) = 1 := by
    rw [show (-(2:ℝ)/3) = -((2:ℝ)/3) by norm_num, ← Real.rpow_add hlam0]
    norm_num
  have hkey : lam ^ (-(2:ℝ)/3) * (t * lam) ^ ((2:ℝ)/3) = t ^ ((2:ℝ)/3) := by
    rw [Real.mul_rpow ht.1.le hlam0.le,
      mul_comm (t ^ ((2:ℝ)/3)) (lam ^ ((2:ℝ)/3)), ← mul_assoc, hkey2, one_mul]
  have hb1' : K / 2 * (t * lam) ^ ((2:ℝ)/3)
      ≤ ‖cmRel m k (x (t * lam)) i - cmRel m k (x (t * lam)) j‖ := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hs0 _)] at hb1
    linarith
  have hb2' : ‖cmRel m k (x (t * lam)) i - cmRel m k (x (t * lam)) j‖
      ≤ 2 * K * (t * lam) ^ ((2:ℝ)/3) := by
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hs0 _)] at hb2
    linarith
  constructor
  · have hlow : lam ^ (-(2:ℝ)/3) * (K / 2 * (t * lam) ^ ((2:ℝ)/3))
        = K / 2 * t ^ ((2:ℝ)/3) := by nlinarith [hkey]
    rw [hnorm, ← hlow]
    exact mul_le_mul_of_nonneg_left hb1' (le_of_lt (Real.rpow_pos_of_pos hlam0 _))
  · rw [hnorm]
    calc lam ^ (-(2:ℝ)/3) * ‖cmRel m k (x (t * lam)) i - cmRel m k (x (t * lam)) j‖
        ≤ lam ^ (-(2:ℝ)/3) * (2 * K * (t * lam) ^ ((2:ℝ)/3)) :=
          mul_le_mul_of_nonneg_left hb2' (le_of_lt (Real.rpow_pos_of_pos hlam0 _))
      _ = 2 * K * (lam ^ (-(2:ℝ)/3) * (t * lam) ^ ((2:ℝ)/3)) := by ring
      _ = 2 * K * t ^ ((2:ℝ)/3) := by rw [hkey]


end Submission.NBody

