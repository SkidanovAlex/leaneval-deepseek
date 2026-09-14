import Submission.NBody.MarchalClusterShapeSecondDeriv
import Submission.NBody.MarchalClusterBlowUp
import Submission.NBody.MarchalClusterAsymptotic3
import Submission.NBody.MarchalClusterFull

/-!
# The pair separations of a colliding cluster

Two consequences of the Sundman asymptotics which the gain estimates (Phase C/D of the Marchal
chapter) need:

* the ratio `‖qᵢ - qⱼ‖ / s^{2/3}` of two bodies of a colliding cluster converges to
  `√κ · ‖s̄ᵢ - s̄ⱼ‖`;
* hence the *uniform in `λ`* two-sided bounds `(K/2) t^{2/3} ≤ ‖q^λᵢ(t) - q^λⱼ(t)‖ ≤ 2K t^{2/3}` on
  `(0,T]` for all small `λ`, where `q^λ` is the rescaled (blown-up) centred configuration.  This is
  the reason the blow-up route needs no uniformity argument in `λ`: the rescaling carries the same
  exponent `2/3`, so the ratio is *independent* of `λ`.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The ratio `‖qᵢ - qⱼ‖ / s^{2/3}` converges.**  For a colliding cluster `k` (isolated), the
separation of two bodies of the cluster, divided by `s^{2/3}`, converges to
`√κ · ‖s̄ᵢ - s̄ⱼ‖`.  This is the input for the uniform two-sided bounds used in the gain estimates:
the ratio is what it is for the (rescaled) curve `q^λ` because the rescaling has the same exponent
`2/3`. -/
theorem tendsto_pair_separation_ratio {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε κ : ℝ} {sbar : EN E N} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε)
    (hκ : 0 < κ) (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hs : Tendsto (fun s : ℝ => clusterShape m k (x s))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar))
    {i j : Fin N} (hi : i ∈ k) (hj : j ∈ k) (hij : i ≠ j) :
    Tendsto (fun s : ℝ => ‖cmRel m k (x s) i - cmRel m k (x s) j‖ / s ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ * ‖sbar i - sbar j‖)) := by
  have hIpos : ∀ s ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x s) :=
    fun s hs' => clusterInertia_pos hm hk2 (hnc s hs')
  -- convergence of `√(I/s^{4/3})`
  have hroot : Tendsto (fun s : ℝ => Real.sqrt (clusterInertia m k (x s) / s ^ ((4:ℝ)/3)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hIn
  -- convergence of the shape difference
  have hci : Tendsto (fun s : ℝ => clusterShape m k (x s) i)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (sbar i)) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin N => E) i).continuousAt.tendsto).comp hs
  have hcj : Tendsto (fun s : ℝ => clusterShape m k (x s) j)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (sbar j)) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin N => E) j).continuousAt.tendsto).comp hs
  have hdiff : Tendsto (fun s : ℝ =>
      ‖clusterShape m k (x s) i - clusterShape m k (x s) j‖)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ‖sbar i - sbar j‖) := (hci.sub hcj).norm
  refine (hroot.mul hdiff).congr' ?_
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hε] with s hs0 hsε
  have hIs : 0 < clusterInertia m k (x s) := hIpos s hsε
  have hrootpos : 0 < Real.sqrt (clusterInertia m k (x s)) := Real.sqrt_pos.mpr hIs
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hcm : cmRel m k (x s) = Real.sqrt (clusterInertia m k (x s)) • clusterShape m k (x s) :=
    cmRel_eq_sqrt_smul_clusterShape hIs
  have hmi : cmRel m k (x s) i = Real.sqrt (clusterInertia m k (x s)) • clusterShape m k (x s) i := by
    rw [hcm, PiLp.smul_apply (fun _ : Fin N => E)]
  have hmj : cmRel m k (x s) j = Real.sqrt (clusterInertia m k (x s)) • clusterShape m k (x s) j := by
    rw [hcm, PiLp.smul_apply (fun _ : Fin N => E)]
  have hnorm : ‖cmRel m k (x s) i - cmRel m k (x s) j‖
      = Real.sqrt (clusterInertia m k (x s))
        * ‖clusterShape m k (x s) i - clusterShape m k (x s) j‖ := by
    rw [hmi, hmj, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hrootpos]
  have hsqrt : Real.sqrt (clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      = Real.sqrt (clusterInertia m k (x s)) / s ^ ((2:ℝ)/3) := by
    rw [Real.sqrt_div (le_of_lt hIs)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hs0)]
    norm_num
  rw [hnorm, hsqrt, div_mul_eq_mul_div]

/-- **Uniform two-sided bounds for the rescaled separations.**  For an isolated colliding cluster
`k` and two bodies `i ≠ j` of `k`, there is `K > 0` such that for all sufficiently small `λ > 0`
and all `t ∈ (0,T]` the rescaled separation `‖q^λᵢ(t) - q^λⱼ(t)‖` is between `K/2 · t^{2/3}` and
`2K · t^{2/3}`.  This is the uniform-in-`λ` estimate which the gain computations need: the rescaling
carries the same exponent `2/3`, so the ratio does not depend on `λ`. -/
theorem eventually_pair_separation_bounds {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε κ T : ℝ} {sbar : EN E N} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε)
    (hκ : 0 < κ) (hT : 0 < T) (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hs : Tendsto (fun s : ℝ => clusterShape m k (x s))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar))
    {i j : Fin N} (hi : i ∈ k) (hj : j ∈ k) (hsbar : sbar i ≠ sbar j) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ (lam : ℝ) in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      K / 2 * t ^ ((2:ℝ)/3)
          ≤ ‖rescaledCentered m k x lam t i - rescaledCentered m k x lam t j‖ ∧
        ‖rescaledCentered m k x lam t i - rescaledCentered m k x lam t j‖
          ≤ 2 * K * t ^ ((2:ℝ)/3) := by
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
  clear hlim
  -- the ratio is eventually within `[K/2, 2K]`
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
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show 0 < ε' / T from div_pos hε'pos hT)]
    with lam hlam hlamlt
  intro t ht
  have hlam0 : 0 < lam := hlam
  have htl : t * lam < ε' := by
    have h1 : t * lam ≤ T * lam := mul_le_mul_of_nonneg_right ht.2 hlam0.le
    have h2 : T * lam < T * (ε' / T) := mul_lt_mul_of_pos_left hlamlt.2 hT
    have h3 : T * (ε' / T) = ε' := by field_simp
    linarith
  have hs : t * lam ∈ Ioo (0:ℝ) ε' := ⟨mul_pos ht.1 hlam0, htl⟩
  obtain ⟨hb1, hb2⟩ := hε' (t * lam) hs
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
        = K / 2 * t ^ ((2:ℝ)/3) := by
      nlinarith [hkey]
    rw [hnorm, ← hlow]
    exact mul_le_mul_of_nonneg_left hb1' (le_of_lt (Real.rpow_pos_of_pos hlam0 _))
  · rw [hnorm]
    calc lam ^ (-(2:ℝ)/3) * ‖cmRel m k (x (t * lam)) i - cmRel m k (x (t * lam)) j‖
        ≤ lam ^ (-(2:ℝ)/3) * (2 * K * (t * lam) ^ ((2:ℝ)/3)) :=
          mul_le_mul_of_nonneg_left hb2' (le_of_lt (Real.rpow_pos_of_pos hlam0 _))
      _ = 2 * K * (lam ^ (-(2:ℝ)/3) * (t * lam) ^ ((2:ℝ)/3)) := by ring
      _ = 2 * K * t ^ ((2:ℝ)/3) := by rw [hkey]


end Submission.NBody
