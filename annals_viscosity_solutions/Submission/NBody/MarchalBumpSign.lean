import Submission.NBody.MarchalPairRatio
import Submission.NBody.MarchalBumpPotential

/-!
# The outward sign condition for the blown-up pair differences

Part of the assembly of Marchal's theorem (`Submission/ROADMAP.md`, SESSION 29), Step 3: the
rescaled pair differences of a colliding cluster are `t^{2/3}` times the scaled normalised
configuration differences, hence their inner product with the outward displacement `δ` is
eventually nonnegative (the outward-displacement lemma gives a strictly positive limit).

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

/-- The rescaled centred configuration differences are the parabolic rescaling of the normalised
configuration differences. -/
lemma rescaledCentered_coord_sub {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {i j : Fin N} {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    (hI : 0 < clusterInertia m k (x (t * lam))) :
    rescaledCentered m k x lam t i - rescaledCentered m k x lam t j
      = t ^ ((2:ℝ)/3) • (Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)) •
          (clusterShape m k (x (t * lam)) i - clusterShape m k (x (t * lam)) j)) := by
  have htl : (0:ℝ) < t * lam := mul_pos ht hlam
  have h1 : ∀ i : Fin N, rescaledCentered m k x lam t i
      = lam ^ (-(2:ℝ)/3) • (cmRel m k (x (t * lam)) i) := by
    intro i
    rw [rescaledCentered, PiLp.smul_apply (fun _ : Fin N => E)]
  have h2 : ∀ i : Fin N, cmRel m k (x (t * lam)) i
      = Real.sqrt (clusterInertia m k (x (t * lam))) • (clusterShape m k (x (t * lam)) i) := by
    intro i
    rw [cmRel_eq_sqrt_smul_clusterShape hI, PiLp.smul_apply (fun _ : Fin N => E)]
  rw [h1, h1, h2, h2, ← smul_sub, ← smul_sub, smul_smul, smul_smul]
  congr 1
  have hsqrt : Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3))
      = Real.sqrt (clusterInertia m k (x (t * lam))) / (t * lam) ^ ((2:ℝ)/3) := by
    rw [Real.sqrt_div (le_of_lt hI)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt htl)]
    norm_num
  rw [hsqrt]
  have hkey : lam ^ (-(2:ℝ)/3) = t ^ ((2:ℝ)/3) / (t * lam) ^ ((2:ℝ)/3) := by
    rw [Real.mul_rpow ht.le hlam.le, show (-(2:ℝ)/3) = -((2:ℝ)/3) by norm_num,
      Real.rpow_neg hlam.le]
    field_simp
  rw [hkey]
  ring

/-- The scaled normalised pair difference converges to `√κ • (s̄ᵢ - s̄ⱼ)`. -/
lemma tendsto_scaledClusterShape_pair_sub {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε κ : ℝ} {sbar : EN E N}
    (hκ : 0 < κ) (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hs : Tendsto (fun s : ℝ => clusterShape m k (x s))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar))
    {i j : Fin N} :
    Tendsto (fun s : ℝ => Real.sqrt (clusterInertia m k (x s) / s ^ ((4:ℝ)/3)) •
        (clusterShape m k (x s) i - clusterShape m k (x s) j))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ • (sbar i - sbar j))) := by
  have hroot : Tendsto (fun s : ℝ => Real.sqrt (clusterInertia m k (x s) / s ^ ((4:ℝ)/3)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hIn
  have hci : Tendsto (fun s : ℝ => clusterShape m k (x s) i)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (sbar i)) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin N => E) i).continuousAt.tendsto).comp hs
  have hcj : Tendsto (fun s : ℝ => clusterShape m k (x s) j)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (sbar j)) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin N => E) j).continuousAt.tendsto).comp hs
  exact hroot.smul (hci.sub hcj)

/-- **The outward sign condition for the blown-up pair differences.**  If the limit shape separates
`i₀` from `j` in the direction `δ`, then for all small `λ` and all `t ∈ (0,T]` the rescaled pair
`q^λ i₀ - q^λ j` has nonnegative inner product with `δ`. -/
theorem eventually_pair_inner_sign {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε κ T : ℝ} {sbar : EN E N} {i₀ j : Fin N} (δ : E)
    (hε : 0 < ε) (hκ : 0 < κ) (hT : 0 < T)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hs : Tendsto (fun s : ℝ => clusterShape m k (x s))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar))
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card)
    (hpos : 0 < inner ℝ (sbar i₀ - sbar j) δ) :
    ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      0 ≤ inner ℝ (rescaledCentered m k x lam t i₀ - rescaledCentered m k x lam t j) δ := by
  have hG := tendsto_scaledClusterShape_pair_sub (k := k) (x := x) (ε := ε) hκ hnc hIn hs
    (i := i₀) (j := j)
  have hinner : Tendsto (fun s : ℝ => inner ℝ
      (Real.sqrt (clusterInertia m k (x s) / s ^ ((4:ℝ)/3)) •
        (clusterShape m k (x s) i₀ - clusterShape m k (x s) j)) δ)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (inner ℝ (Real.sqrt κ • (sbar i₀ - sbar j)) δ)) :=
    hG.inner tendsto_const_nhds
  have hlimpos : 0 < inner ℝ (Real.sqrt κ • (sbar i₀ - sbar j)) δ := by
    rw [real_inner_smul_left]
    exact mul_pos (Real.sqrt_pos.mpr hκ) hpos
  have hev : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0), (0:ℝ) < inner ℝ
      (Real.sqrt (clusterInertia m k (x s) / s ^ ((4:ℝ)/3)) •
        (clusterShape m k (x s) i₀ - clusterShape m k (x s) j)) δ :=
    hinner.eventually (eventually_gt_nhds hlimpos)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hεT : 0 < ε / T := div_pos hε hT
  refine (eventually_nhdsWithin_iff).mpr ?_
  refine Metric.eventually_nhds_iff_ball.mpr ⟨min (η / T) (ε / T),
    lt_min (div_pos hηpos hT) hεT, ?_⟩
  intro lam hlam hlampos
  intro t ht
  have hltη : lam < η / T := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hlampos] at hlam
    exact lt_of_lt_of_le hlam (min_le_left _ _)
  have hltε : lam < ε / T := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hlampos] at hlam
    exact lt_of_lt_of_le hlam (min_le_right _ _)
  have hlt : lam * t < η := by
    have h1 : t * lam ≤ T * lam := mul_le_mul_of_nonneg_right ht.2 hlampos.le
    have h2 : T * lam < T * (η / T) := mul_lt_mul_of_pos_left hltη hT
    have h3 : T * (η / T) = η := by field_simp
    linarith [mul_comm t lam]
  have hltE : lam * t < ε := by
    have h1 : t * lam ≤ T * lam := mul_le_mul_of_nonneg_right ht.2 hlampos.le
    have h2 : T * lam < T * (ε / T) := mul_lt_mul_of_pos_left hltε hT
    have h3 : T * (ε / T) = ε := by field_simp
    linarith [mul_comm t lam]
  have hηmem : lam * t ∈ Metric.ball (0:ℝ) η := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (mul_pos hlampos ht.1)]
    exact hlt
  have hsign := le_of_lt (hη (lam * t) hηmem (mul_pos hlampos ht.1))
  have hI : 0 < clusterInertia m k (x (t * lam)) := by
    rw [mul_comm lam t] at hltE
    exact clusterInertia_pos hm hk2 (hnc (t * lam) ⟨mul_pos ht.1 hlampos, hltE⟩)
  rw [rescaledCentered_coord_sub hlampos ht.1 hI, real_inner_smul_left]
  exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (by simpa only [mul_comm lam t] using hsign)

end Submission.NBody

