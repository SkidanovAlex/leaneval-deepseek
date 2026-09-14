import Submission.NBody.MarchalEndgameData
import Submission.NBody.MarchalPairRatio

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- A single pair term of the cluster potential is bounded by the whole sum. -/
lemma pair_term_le_clusterPotential {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) {k : Finset (Fin N)}
    {x : EN E N} {i j : Fin N} (hi : i ∈ k) (hj : j ∈ k) (hij : i ≠ j) :
    m i * m j * (r x i j)⁻¹ ≤ clusterPotential m k x := by
  classical
  rw [clusterPotential]
  have h0 : ∀ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
      0 ≤ m p.1 * m p.2 * (r x p.1 p.2)⁻¹ := fun p _ =>
    mul_nonneg (mul_nonneg (hm p.1) (hm p.2)) (inv_nonneg.mpr (by rw [r]; exact dist_nonneg))
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hmem : (i, j) ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, hi, hj⟩
    exact Finset.single_le_sum h0 hmem
  · have hmem : (j, i) ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, hj, hi⟩
    have h := Finset.single_le_sum h0 hmem
    rwa [show m j * m i * (r x j i)⁻¹ = m i * m j * (r x i j)⁻¹ from by
      rw [r_eq_norm_sub, r_eq_norm_sub, norm_sub_rev]; ring] at h

/-- The normalised separation of a pair of the cluster. -/
lemma norm_clusterShape_sub_eq {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {i j : Fin N}
    (hi : i ∈ k) (hj : j ∈ k) (hI : 0 < clusterInertia m k x) :
    ‖clusterShape m k x i - clusterShape m k x j‖
      = ‖x i - x j‖ / Real.sqrt (clusterInertia m k x) := by
  have h1 : clusterShape m k x i = (Real.sqrt (clusterInertia m k x))⁻¹ • (cmRel m k x i) :=
    clusterShape_apply m k x i
  have h2 : clusterShape m k x j = (Real.sqrt (clusterInertia m k x))⁻¹ • (cmRel m k x j) :=
    clusterShape_apply m k x j
  rw [h1, h2, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hI))]
  have h3 : cmRel m k x i - cmRel m k x j = x i - x j := by
    rw [cmRel_apply_of_mem hi, cmRel_apply_of_mem hj]
    abel
  rw [h3, inv_mul_eq_div]

/-- **The limit shape of a colliding cluster has distinct positions.**  A pair of the cluster which
is separated by `t^{2/3}` in the normalised shape cannot collapse in the limit, because the cluster
potential is exactly of order `t^{-2/3}` (every single pair term is bounded by it). -/
theorem shape_pair_ne_of_asymptotic {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε κ : ℝ} {sbar : EN E N} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε)
    (hκ : 0 < κ) (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hUn : Tendsto (fun s : ℝ => clusterPotential m k (x s) * s ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ)))
    {lam : ℕ → ℝ} (hlampos : ∀ n, 0 < lam n)
    (hlamT : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)))
    (hs : Tendsto (fun n => clusterShape m k (x (lam n))) atTop (nhds sbar))
    {i j : Fin N} (hi : i ∈ k) (hj : j ∈ k) (hij : i ≠ j) :
    sbar i ≠ sbar j := by
  classical
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  set C : ℝ := (2:ℝ)/9 * κ + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; linarith
  set c : ℝ := m i * m j / (C * Real.sqrt (κ + 1)) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact div_pos (mul_pos (hm i) (hm j))
      (mul_pos hCpos (Real.sqrt_pos.mpr (by linarith)))
  -- the limit of the normalised separation
  have hshape : Tendsto (fun n : ℕ => ‖clusterShape m k (x (lam n)) i - clusterShape m k (x (lam n)) j‖)
      atTop (nhds ‖sbar i - sbar j‖) := by
    have h1 : Tendsto (fun n : ℕ => clusterShape m k (x (lam n)) i) atTop (nhds (sbar i)) :=
      ((PiLp.continuous_apply 2 (fun _ : Fin N => E) i).continuousAt.tendsto).comp hs
    have h2 : Tendsto (fun n : ℕ => clusterShape m k (x (lam n)) j) atTop (nhds (sbar j)) :=
      ((PiLp.continuous_apply 2 (fun _ : Fin N => E) j).continuousAt.tendsto).comp hs
    exact (h1.sub h2).norm
  -- the lower bound, eventually
  have hlow : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0),
      c ≤ ‖clusterShape m k (x s) i - clusterShape m k (x s) j‖ := by
    have hU : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0),
        clusterPotential m k (x s) * s ^ ((2:ℝ)/3) < C :=
      hUn.eventually (Iio_mem_nhds (by rw [hCdef]; linarith))
    have hI : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0),
        clusterInertia m k (x s) / s ^ ((4:ℝ)/3) < κ + 1 :=
      hIn.eventually (Iio_mem_nhds (by linarith))
    have hsε : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0), s < ε := by
      filter_upwards [Ioo_mem_nhdsGT hε] with s hs
      exact hs.2
    filter_upwards [hU, hI, hsε, self_mem_nhdsWithin] with s hUs hIs hsε' hs0
    have hspos : 0 < s := hs0
    have hnc' : WithoutCollisions (x s) := hnc s ⟨hspos, hsε'⟩
    have hIpos : 0 < clusterInertia m k (x s) := clusterInertia_pos hm hk2 hnc'
    have hupos : 0 < s ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos hspos _
    have hu2 : (s ^ ((2:ℝ)/3)) ^ 2 = s ^ ((4:ℝ)/3) := by
      rw [sq, ← Real.rpow_add hspos]
      norm_num
    have hrpos : 0 < r (x s) i j := by
      rw [r]
      exact dist_pos.mpr ((r_ne_zero_iff (x s) i j).mp (hnc' i j hij))
    -- the pair lower bound
    have hpair := pair_term_le_clusterPotential (m := m) hm0 hi hj hij (x := x s)
    have hUle : clusterPotential m k (x s) ≤ C / s ^ ((2:ℝ)/3) := by
      rw [le_div_iff₀ hupos]
      exact le_of_lt hUs
    have hrij : m i * m j / C * s ^ ((2:ℝ)/3) ≤ r (x s) i j := by
      have h1 : m i * m j / r (x s) i j ≤ C / s ^ ((2:ℝ)/3) := by
        have h2 : m i * m j * (r (x s) i j)⁻¹ = m i * m j / r (x s) i j := by rw [div_eq_mul_inv]
        rw [← h2]
        exact le_trans hpair hUle
      rw [div_le_div_iff₀ hrpos hupos] at h1
      have h3 : m i * m j * s ^ ((2:ℝ)/3) / C ≤ r (x s) i j := by
        rw [div_le_iff₀ hCpos]
        linarith [h1]
      calc m i * m j / C * s ^ ((2:ℝ)/3) = m i * m j * s ^ ((2:ℝ)/3) / C := by ring
        _ ≤ r (x s) i j := h3
    -- the inertia bound
    have hIle : clusterInertia m k (x s) ≤ (κ + 1) * (s ^ ((2:ℝ)/3)) ^ 2 := by
      have h := le_of_lt hIs
      have h2 : clusterInertia m k (x s) / s ^ ((4:ℝ)/3) * s ^ ((4:ℝ)/3)
          ≤ (κ + 1) * s ^ ((4:ℝ)/3) :=
        mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hspos.le _)
      rw [div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hspos _))] at h2
      calc clusterInertia m k (x s) ≤ (κ + 1) * s ^ ((4:ℝ)/3) := h2
        _ = (κ + 1) * (s ^ ((2:ℝ)/3)) ^ 2 := by rw [hu2]
    have hsqrt : Real.sqrt (clusterInertia m k (x s))
        ≤ Real.sqrt (κ + 1) * s ^ ((2:ℝ)/3) := by
      calc Real.sqrt (clusterInertia m k (x s))
          ≤ Real.sqrt ((κ + 1) * (s ^ ((2:ℝ)/3)) ^ 2) := Real.sqrt_le_sqrt hIle
        _ = Real.sqrt (κ + 1) * s ^ ((2:ℝ)/3) := by
            rw [Real.sqrt_mul (by linarith : (0:ℝ) ≤ κ + 1), Real.sqrt_sq hupos.le]
    -- the normalised separation
    rw [norm_clusterShape_sub_eq hi hj hIpos]
    have hCsqrtpos : 0 < C * Real.sqrt (κ + 1) := mul_pos hCpos (Real.sqrt_pos.mpr (by linarith))
    have hsqrtpos : 0 < Real.sqrt (clusterInertia m k (x s)) := Real.sqrt_pos.mpr hIpos
    rw [hcdef, le_div_iff₀ hsqrtpos]
    have hfac : 0 ≤ m i * m j / (C * Real.sqrt (κ + 1)) :=
      div_nonneg (mul_nonneg (hm i).le (hm j).le) hCsqrtpos.le
    calc m i * m j / (C * Real.sqrt (κ + 1)) * Real.sqrt (clusterInertia m k (x s))
        ≤ m i * m j / (C * Real.sqrt (κ + 1)) * (Real.sqrt (κ + 1) * s ^ ((2:ℝ)/3)) :=
          mul_le_mul_of_nonneg_left hsqrt hfac
      _ = m i * m j / C * s ^ ((2:ℝ)/3) := by
          field_simp
      _ ≤ r (x s) i j := hrij
      _ = ‖x s i - x s j‖ := r_eq_norm_sub (x s) i j
  have hlowseq : ∀ᶠ n in atTop, c ≤ ‖clusterShape m k (x (lam n)) i - clusterShape m k (x (lam n)) j‖ :=
    hlamT.eventually hlow
  have hlim : c ≤ ‖sbar i - sbar j‖ :=
    isClosed_Ici.mem_of_tendsto hshape hlowseq
  intro h
  rw [h, sub_self, norm_zero] at hlim
  exact absurd hlim (not_le.mpr hcpos)

end Submission.NBody
