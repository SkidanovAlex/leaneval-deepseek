import Submission.NBody.MarchalThirdDerivAsymptotic

/-!
# Bounding the jolt of a colliding cluster

Ferrario--Terracini's `as:lim2` (`t^2 s_i'' -> 0`) needs, besides the boundedness of `t^2 s''`
(proved in `MarchalClusterShapeSecondDeriv`), the boundedness of `t^3 s_jolt`.  Via the third-order
identity `eq:dddotqi` of the paper, that reduces to

* `t^(7/3) * |q_jolt_i|` bounded (the jolt of the centre-of-mass-relative configuration), and
* the already available bounds `t^(5/3) * I_jolt`, `t^2 * s''`, `t * s'`, `|s|`.

This file proves the jolt bound.  The key input is `exists_norm_jolt_le`
(`Submission/NBody/MarchalThirdDeriv.lean`), which bounds the internal part of the jolt of a body of
the cluster by `A * Cv * sqrt(U_k) * U_k^3`; the passage from `U_k` to the asymptotics uses
`U_k <= I_k'' + 8C + 2` and `I_k'' * t^(2/3) -> (4/9) kappa`.

Everything in this file is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators Topology
open InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The setup of the jolt bound.**  On a shrunk interval, the internal potential is at least `1`
and bounded by `I_k'' + 8C + 2`, and every velocity is bounded by `Ckv * sqrt (I_k'' + 4C)`. -/
theorem exists_velocity_potential_second_deriv_bounds {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε)
    (hC : 0 < C) (hν : 0 < ν) (hCv : 0 ≤ Cv)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |clusterRelEnergy m k (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |crossWork m k (x t) (cmRel m k (x t))| ≤ C)
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x t) ν)
    (hv : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k,
      ‖deriv x t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (x t)))
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    ∃ Ckv : ℝ, 0 ≤ Ckv ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε ∧ ∀ t ∈ Ioo (0:ℝ) ε₁,
      1 ≤ clusterPotential m k (x t) ∧
      clusterPotential m k (x t)
        ≤ deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t + 8 * C + 2 ∧
      1 ≤ deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t ∧
      (∀ j : Fin N, ‖deriv x t j‖
        ≤ Ckv * Real.sqrt (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t + 4 * C)) := by
  classical
  obtain ⟨i0, hi0⟩ : k.Nonempty := Finset.card_pos.mp (by omega)
  have hkne : k.Nonempty := ⟨i0, hi0⟩
  obtain ⟨κ, hκpos, hκ⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    obtain ⟨i1, -, hi1⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N)) m
      ⟨i0, Finset.mem_univ i0⟩
    exact ⟨m i1, hm i1, fun i => hi1 i (Finset.mem_univ i)⟩
  obtain ⟨ck, hckpos, hcksp⟩ := exists_const_le_clusterPotential (E := E) hm k hk2
  -- the third-order differentiability in the `deriv (deriv x)` form
  have hd3' : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t :=
    hd3
  -- the acceleration bound of a body of the cluster
  obtain ⟨A, hApos, hA⟩ := exists_norm_accel_rel_le (E := E) (N := N) (m := m) (k := k) (ν := ν)
    hm hν hkne
  -- the bound on the velocity of the centre of mass
  have hacc : ∀ t ∈ Ioo (0:ℝ) ε,
      ‖clusterCM m k (iteratedDeriv 2 x t)‖
        ≤ (clusterMass m k)⁻¹
          * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j)
              * (ν⁻¹) ^ 2) := by
    intro t ht
    rw [hode t ht]
    exact norm_clusterCM_weightedGrad_le hm hν (hsep t ht) (hnc t ht)
  have hAcm : 0 ≤ (clusterMass m k)⁻¹
      * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j) * (ν⁻¹) ^ 2) :=
    mul_nonneg (inv_nonneg.mpr (clusterMass_nonneg (fun i => (hm i).le) k))
      (mul_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hm i).le (hm j).le) (sq_nonneg _))
  have hcm : ∀ t ∈ Ioo (0:ℝ) (ε / 4), ‖clusterCM m k (deriv x t)‖
      ≤ (clusterMass m k)⁻¹
          * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j)
              * (ν⁻¹) ^ 2) * (ε / 4)
        + ‖clusterCM m k (deriv x (ε / 4))‖ := by
    refine exists_bound_clusterCM_deriv hε hAcm (fun t ht => hd2 t ?_) (fun t ht => hacc t ?_)
    · exact ⟨ht.1, by linarith [ht.2, hε]⟩
    · exact ⟨ht.1, by linarith [ht.2, hε]⟩
  -- shrink the interval so that `I_k ≤ C₀ := min 1 (ck/2)²`
  set C₀ : ℝ := min 1 (min ((ck / 2) ^ 2) ((ck / (24 * C)) ^ 2)) with hC₀
  have hC₀pos : 0 < C₀ := by
    rw [hC₀]; exact lt_min one_pos (lt_min (by positivity) (by positivity))
  have hsC₀a : Real.sqrt C₀ ≤ ck / 2 := by
    rw [hC₀]
    refine le_trans (Real.sqrt_le_sqrt (le_trans (min_le_right _ _) (min_le_left _ _))) ?_
    rw [Real.sqrt_sq (by positivity)]
  have hsC₀b : Real.sqrt C₀ ≤ ck / (24 * C) := by
    rw [hC₀]
    refine le_trans (Real.sqrt_le_sqrt (le_trans (min_le_right _ _) (min_le_right _ _))) ?_
    rw [Real.sqrt_sq (by positivity)]
  have hxev : ∀ t ∈ Ioo (0:ℝ) ε, ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hx s hs
  have hevI : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), clusterInertia m k (x t) < C₀ :=
    hI.eventually (isOpen_Iio.mem_nhds hC₀pos)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp (by
    rw [eventually_nhdsWithin_iff] at hevI; exact hevI)
  set ε₁ : ℝ := min (min δ (ε / 4)) ε with hε₁def
  have hε₁pos : 0 < ε₁ := by
    rw [hε₁def]; exact lt_min (lt_min hδpos (by linarith)) hε
  have hε₁le : ε₁ ≤ ε := by rw [hε₁def]; exact min_le_right _ _
  have hε₁le4 : ε₁ ≤ ε / 4 := by
    rw [hε₁def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hε₁leδ : ε₁ ≤ δ := by
    rw [hε₁def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hε₁ : ∀ t ∈ Ioo (0:ℝ) ε₁, clusterInertia m k (x t) ≤ C₀ := by
    intro t ht
    refine le_of_lt (hδ t ?_ ht.1)
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact lt_of_lt_of_le ht.2 hε₁leδ
  have hmem : ∀ t ∈ Ioo (0:ℝ) ε₁, t ∈ Ioo (0:ℝ) ε :=
    fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hε₁le⟩
  have hmem4 : ∀ t ∈ Ioo (0:ℝ) ε₁, t ∈ Ioo (0:ℝ) (ε/4) :=
    fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hε₁le4⟩
  -- the constants of the final bound
  set CCM : ℝ := (clusterMass m k)⁻¹
      * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j) * (ν⁻¹) ^ 2)
        * (ε / 4) + ‖clusterCM m k (deriv x (ε / 4))‖ with hCCMdef
  have hCCM0 : 0 ≤ CCM := by
    rw [hCCMdef]
    have h1 : 0 ≤ (clusterMass m k)⁻¹
        * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j) * (ν⁻¹) ^ 2)
        * (ε / 4) := mul_nonneg hAcm (by linarith)
    linarith [norm_nonneg (clusterCM m k (deriv x (ε / 4)))]
  have hCMval : ∀ t ∈ Ioo (0:ℝ) (ε / 4), ‖clusterCM m k (deriv x t)‖ ≤ CCM := by
    intro t ht
    rw [hCCMdef]
    exact hcm t ht
  -- the constant of the internal estimate and the (larger) constant of the external one
  set Ckv₀ : ℝ := Cv + Real.sqrt (κ⁻¹) + CCM + 1 with hCkv₀
  have hCkv₀0 : 0 ≤ Ckv₀ := by
    rw [hCkv₀]
    have h1 : 0 ≤ Real.sqrt (κ⁻¹) := Real.sqrt_nonneg _
    linarith [h1, hCCM0, hCv]
  set Ckv : ℝ := Cv * Real.sqrt (8 * C + 3) + Real.sqrt (κ⁻¹) + CCM + 1 with hCkv
  have hCkv0 : 0 ≤ Ckv := by
    rw [hCkv]
    have h1 : 0 ≤ Real.sqrt (κ⁻¹) := Real.sqrt_nonneg _
    have h2 : 0 ≤ Cv * Real.sqrt (8 * C + 3) := mul_nonneg hCv (Real.sqrt_nonneg _)
    linarith
  have hmono : Ckv₀ ≤ Ckv := by
    rw [hCkv₀, hCkv]
    have hs : (1:ℝ) ≤ Real.sqrt (8 * C + 3) := Real.one_le_sqrt.mpr (by linarith)
    have h2 : Cv ≤ Cv * Real.sqrt (8 * C + 3) := le_mul_of_one_le_right hCv hs
    linarith
  refine ⟨Ckv, hCkv0, ε₁, hε₁pos, hε₁le, ?_⟩
  intro t ht
  have htε := hmem t ht
  set P : ℝ := deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t with hPdef
  have hPval : P = 4 * clusterRelEnergy m k (x t) (deriv x t) + 2 * clusterPotential m k (x t)
      + 2 * crossWork m k (x t) (cmRel m k (x t)) := by
    rw [hPdef]
    exact deriv_deriv_clusterInertia_curve_eq hm hkne (hnc t htε) (hxev t htε) (hd2 t htε)
      (hode t htε)
  have hIpos : 0 < clusterInertia m k (x t) := clusterInertia_pos hm hk2 (hnc t htε)
  have hrootpos : 0 < Real.sqrt (clusterInertia m k (x t)) := Real.sqrt_pos.mpr hIpos
  have hPbig : ck ≤ (P + 6 * C) * Real.sqrt (clusterInertia m k (x t)) := by
    have h := clusterInertia_second_deriv_ge_rel (k := k) (x := x) (C := C) (ck := ck) hm hkne
      (le_trans (neg_le_neg (hE t htε)) (neg_abs_le _))
      (le_trans (neg_le_neg (hW t htε)) (neg_abs_le _))
      (hcksp (x t) (hnc t htε)) (hxev t htε) (hd2 t htε) (hode t htε) (hnc t htε)
    rw [iteratedDeriv_two_eq_deriv_deriv (fun s : ℝ => clusterInertia m k (x s)) t, ← hPdef] at h
    have h1 := mul_le_mul_of_nonneg_right h hrootpos.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hrootpos)] at h1
  have hsI24 : Real.sqrt (clusterInertia m k (x t)) ≤ ck / (24 * C) :=
    le_trans (Real.sqrt_le_sqrt (hε₁ t ht)) hsC₀b
  have h64 : 6 * C * Real.sqrt (clusterInertia m k (x t)) ≤ ck / 4 := by
    have h2 : 6 * C * (ck / (24 * C)) = ck / 4 := by field_simp; ring
    have h3 := mul_le_mul_of_nonneg_left hsI24 (by positivity : (0:ℝ) ≤ 6 * C)
    linarith [h3, h2.le]
  have hPr : (3/4) * ck ≤ P * Real.sqrt (clusterInertia m k (x t)) := by
    nlinarith [hPbig, h64]
  have hP1 : 1 ≤ P := by
    have h6 : Real.sqrt (clusterInertia m k (x t)) ≤ ck / 2 :=
      le_trans (Real.sqrt_le_sqrt (hε₁ t ht)) hsC₀a
    nlinarith [hPr, hrootpos, h6, hckpos]
  have hPbound : ck / 2 ≤ P * (clusterInertia m k (x t)) ^ ((1:ℝ)/2) := by
    rw [← Real.sqrt_eq_rpow]
    linarith [hPr]
  have hU0 : 0 ≤ clusterPotential m k (x t) := clusterPotential_nonneg (fun i => (hm i).le) k (x t)
  have hUΦ : clusterPotential m k (x t) ≤ P + 8 * C + 2 := by
    have h1 := (abs_le.mp (hE t htε)).1
    have h2 := (abs_le.mp (hW t htε)).1
    rw [hPval]; linarith
  have hR : clusterKineticSq m k (cmRel m k (deriv x t)) ≤ P + 4 * C := by
    have h1 := (abs_le.mp (hE t htε)).1
    have h2 := (abs_le.mp (hW t htε)).1
    have hid : clusterKineticSq m k (cmRel m k (deriv x t))
        = 2 * clusterRelEnergy m k (x t) (deriv x t) + 2 * clusterPotential m k (x t) := by
      unfold clusterRelEnergy clusterRelKinetic
      ring
    rw [hPval, hid]; linarith
  have hM1 : 1 ≤ P + 4 * C := by linarith
  have hM0 : 0 ≤ P + 4 * C := by linarith
  have hsM1 : 1 ≤ Real.sqrt (P + 4 * C) := Real.one_le_sqrt.mpr hM1
  have hsM0 : 0 ≤ Real.sqrt (P + 4 * C) := Real.sqrt_nonneg _
  have hvel : ∀ j : Fin N, ‖deriv x t j‖ ≤ Ckv * Real.sqrt (P + 4 * C) := by
    intro j
    by_cases hj : j ∈ k
    · have hq : ‖(cmRel m k (deriv x t)) j‖ ^ 2
          ≤ clusterKineticSq m k (cmRel m k (deriv x t)) / κ := by
        rw [le_div_iff₀ hκpos, show clusterKineticSq m k (cmRel m k (deriv x t))
              = ∑ i ∈ k, m i * ‖(cmRel m k (deriv x t)) i‖ ^ 2 from rfl]
        calc ‖(cmRel m k (deriv x t)) j‖ ^ 2 * κ
            ≤ ‖(cmRel m k (deriv x t)) j‖ ^ 2 * m j :=
              mul_le_mul_of_nonneg_left (hκ j) (sq_nonneg _)
          _ = m j * ‖(cmRel m k (deriv x t)) j‖ ^ 2 := by ring
          _ ≤ ∑ i ∈ k, m i * ‖(cmRel m k (deriv x t)) i‖ ^ 2 :=
              Finset.single_le_sum (f := fun i : Fin N => m i * ‖(cmRel m k (deriv x t)) i‖ ^ 2)
                (fun i _ => mul_nonneg (hm i).le (sq_nonneg _)) hj
      have hqn : ‖(cmRel m k (deriv x t)) j‖
          ≤ Real.sqrt (clusterKineticSq m k (cmRel m k (deriv x t)) / κ) := by
        calc ‖(cmRel m k (deriv x t)) j‖ = Real.sqrt (‖(cmRel m k (deriv x t)) j‖ ^ 2) :=
              (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (clusterKineticSq m k (cmRel m k (deriv x t)) / κ) :=
              Real.sqrt_le_sqrt hq
      have hsq : Real.sqrt (clusterKineticSq m k (cmRel m k (deriv x t)) / κ)
          ≤ Real.sqrt (κ⁻¹) * Real.sqrt (P + 4 * C) := by
        rw [div_eq_mul_inv, Real.sqrt_mul
          (clusterKineticSq_nonneg (fun i => (hm i).le) k (cmRel m k (deriv x t))),
          mul_comm (Real.sqrt (clusterKineticSq m k (cmRel m k (deriv x t))))
            (Real.sqrt (κ⁻¹))]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hR) (Real.sqrt_nonneg _)
      have hsplit : ‖deriv x t j‖
          ≤ ‖(cmRel m k (deriv x t)) j‖ + ‖clusterCM m k (deriv x t)‖ := by
        rw [cmRel_apply_of_mem hj]
        calc ‖(deriv x t) j‖
            = ‖((deriv x t) j - clusterCM m k (deriv x t)) + clusterCM m k (deriv x t)‖ := by
              rw [sub_add_cancel]
          _ ≤ ‖(deriv x t) j - clusterCM m k (deriv x t)‖ + ‖clusterCM m k (deriv x t)‖ :=
              norm_add_le _ _
      have hCM := hCMval t (hmem4 t ht)
      have hCMle : CCM ≤ CCM * Real.sqrt (P + 4 * C) :=
        le_mul_of_one_le_right hCCM0 hsM1
      have h7 : ‖deriv x t j‖ ≤ Ckv₀ * Real.sqrt (P + 4 * C) := by
        rw [hCkv₀]
        nlinarith [hsplit, hqn, hsq, hCM, hCMle, hCv, hCCM0, hsM0, hsM1, hM0,
          Real.sqrt_nonneg (κ⁻¹)]
      exact le_trans h7 (mul_le_mul_of_nonneg_right hmono (Real.sqrt_nonneg _))
    · have h1 := hv t htε j hj
      -- `U ≤ (8C+3)(P+4C)`
      have hUle : clusterPotential m k (x t) ≤ (8 * C + 3) * (P + 4 * C) := by
        have h2 : P + 8 * C + 2 ≤ (8 * C + 3) * (P + 4 * C) := by nlinarith [hM1, hM0, hC]
        linarith [hUΦ, h2]
      have hsq : Real.sqrt (clusterPotential m k (x t))
          ≤ Real.sqrt (8 * C + 3) * Real.sqrt (P + 4 * C) := by
        calc Real.sqrt (clusterPotential m k (x t))
            ≤ Real.sqrt ((8 * C + 3) * (P + 4 * C)) := Real.sqrt_le_sqrt hUle
          _ = Real.sqrt (8 * C + 3) * Real.sqrt (P + 4 * C) :=
              Real.sqrt_mul (by positivity) _
      have h1' : ‖deriv x t j‖ ≤ Cv * Real.sqrt (8 * C + 3) * Real.sqrt (P + 4 * C) := by
        calc ‖deriv x t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (x t)) := h1
          _ ≤ Cv * (Real.sqrt (8 * C + 3) * Real.sqrt (P + 4 * C)) :=
              mul_le_mul_of_nonneg_left hsq hCv
          _ = Cv * Real.sqrt (8 * C + 3) * Real.sqrt (P + 4 * C) := by ring
      have hA : Cv * Real.sqrt (8 * C + 3) * Real.sqrt (P + 4 * C)
          ≤ Ckv * Real.sqrt (P + 4 * C) := by
        rw [hCkv]
        refine mul_le_mul_of_nonneg_right ?_ hsM0
        linarith [Real.sqrt_nonneg (κ⁻¹), hCCM0]
      exact le_trans h1' hA
  have hode_t : deriv (deriv x) t = ∇_[m] (U m) (x t) := by
    rw [← iteratedDeriv_two_eq_deriv_deriv x t]
    exact hode t htε
  have hU1 : 1 ≤ clusterPotential m k (x t) := by
    have h1 := hcksp (x t) (hnc t htε)
    have h2 : Real.sqrt (clusterInertia m k (x t)) ≤ ck :=
      le_trans (le_trans (Real.sqrt_le_sqrt (hε₁ t ht)) hsC₀a) (by linarith [hckpos])
    have h3 : ck / ck ≤ ck / Real.sqrt (clusterInertia m k (x t)) :=
      div_le_div_of_nonneg_left hckpos.le hrootpos h2
    have h4 : ck / ck = 1 := div_self (ne_of_gt hckpos)
    linarith [h1, h3, h4.le]
  exact ⟨hU1, hUΦ, hP1, hvel⟩

/-- **`cmRel` is bounded by a uniform coordinate bound.** -/
lemma norm_cmRel_le {m : Fin N → ℝ} {k : Finset (Fin N)} {v : EN E N} {B : ℝ}
    (hm : ∀ i, 0 < m i) (hB : 0 ≤ B) (hv : ∀ i ∈ k, ‖v i‖ ≤ B) :
    ‖cmRel m k v‖
      ≤ Real.sqrt (k.card : ℝ) * (B + (clusterMass m k)⁻¹ * ((∑ i ∈ k, m i) * B)) := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hmk0 : 0 ≤ clusterMass m k := clusterMass_nonneg hm0 k
  set X : ℝ := (clusterMass m k)⁻¹ * ((∑ i ∈ k, m i) * B) with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg (inv_nonneg.mpr hmk0)
      (mul_nonneg (Finset.sum_nonneg fun i _ => hm0 i) hB)
  have hCM : ‖clusterCM m k v‖ ≤ X := by
    rw [clusterCM, hX]
    have h1 : ‖(clusterMass m k)⁻¹ • ∑ i ∈ k, m i • v i‖
        = (clusterMass m k)⁻¹ * ‖∑ i ∈ k, m i • v i‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hmk0)]
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hmk0)
    calc ‖∑ i ∈ k, m i • v i‖ ≤ ∑ i ∈ k, ‖m i • v i‖ := norm_sum_le _ _
      _ = ∑ i ∈ k, m i * ‖v i‖ :=
          Finset.sum_congr rfl fun i _ => by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hm0 i)]
      _ ≤ ∑ i ∈ k, m i * B :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hv i hi) (hm0 i)
      _ = (∑ i ∈ k, m i) * B := by rw [Finset.sum_mul]
  have hterm : ∀ i ∈ k, ‖(cmRel m k v) i‖ ≤ B + X := by
    intro i hi
    rw [cmRel_apply_of_mem hi]
    exact le_trans (norm_sub_le _ _) (add_le_add (hv i hi) hCM)
  have hsq : ‖cmRel m k v‖ ^ 2 ≤ (k.card : ℝ) * (B + X) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ i : Fin N, ‖(cmRel m k v) i‖ ^ 2
        = ∑ i ∈ Finset.univ.filter (fun i : Fin N => i ∈ k), ‖(cmRel m k v) i‖ ^ 2 := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : i ∈ k
          · rw [if_pos hi]
          · rw [if_neg hi, cmRel_apply_of_notMem hi]; simp
      _ = ∑ i ∈ k, ‖(cmRel m k v) i‖ ^ 2 := by
          congr 1
          ext i
          simp
      _ ≤ ∑ _i ∈ k, (B + X) ^ 2 :=
          Finset.sum_le_sum fun i hi =>
            pow_le_pow_left₀ (norm_nonneg _) (hterm i hi) 2
      _ = (k.card : ℝ) * (B + X) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ‖cmRel m k v‖ = Real.sqrt (‖cmRel m k v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((k.card : ℝ) * (B + X) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (k.card : ℝ) * (B + X) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (add_nonneg hB hX0)]
    _ = Real.sqrt (k.card : ℝ) * (B + (clusterMass m k)⁻¹ * ((∑ i ∈ k, m i) * B)) := by
        rw [hX]

/-- **The jolt of the centre-of-mass relative configuration is `O(t^{-7/3})`.** -/
theorem exists_bound_rpow_seven_thirds_cmRel_third_deriv {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv κ : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv) (hκ : 0 < κ)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |clusterRelEnergy m k (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |crossWork m k (x t) (cmRel m k (x t))| ≤ C)
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x t) ν)
    (hv : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k,
      ‖deriv x t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (x t)))
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hSec : Tendsto (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
      * t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ))) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      t ^ ((7:ℝ)/3) * ‖cmRel m k (deriv (deriv (deriv x)) t)‖ ≤ C' := by
  classical
  obtain ⟨i0, hi0⟩ : k.Nonempty := Finset.card_pos.mp (by omega)
  have hkne : k.Nonempty := ⟨i0, hi0⟩
  obtain ⟨Ckv, hCkv0, ε₁, hε₁pos, hε₁le, hsetup⟩ :=
    exists_velocity_potential_second_deriv_bounds (m := m) (k := k) (x := x) (ε := ε) (C := C)
      (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI
  set Cv' : ℝ := Ckv * Real.sqrt (10 * C + 2) + Cv with hCv'def
  have hCv'0 : 0 ≤ Cv' := by
    rw [hCv'def]
    have h1 : 0 ≤ Real.sqrt (10 * C + 2) := Real.sqrt_nonneg _
    have h2 : 0 ≤ Ckv * Real.sqrt (10 * C + 2) := mul_nonneg hCkv0 h1
    linarith
  obtain ⟨A, hApos, hjolt⟩ := exists_norm_jolt_le (E := E) (N := N) (m := m) (k := k) (ν := ν)
    (Cv := Cv') hm hν hCv'0 hkne
  -- the per-coordinate jolt bound
  have hjoltapply : ∀ t ∈ Ioo (0:ℝ) ε₁, ∀ i ∈ k,
      ‖deriv (deriv (deriv x)) t i‖
        ≤ A * Cv' * Real.sqrt (clusterPotential m k (x t))
            * (clusterPotential m k (x t)) ^ 3 := by
    intro t ht i hi
    obtain ⟨hU1, hUΦ, hP1, hvel⟩ := hsetup t ht
    have htε : t ∈ Ioo (0:ℝ) ε := ⟨ht.1, lt_of_lt_of_le ht.2 hε₁le⟩
    have hU0 : 0 ≤ clusterPotential m k (x t) := le_trans zero_le_one hU1
    have hPval : deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
        = 4 * clusterRelEnergy m k (x t) (deriv x t) + 2 * clusterPotential m k (x t)
          + 2 * crossWork m k (x t) (cmRel m k (x t)) := by
      have hxev : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
        filter_upwards [isOpen_Ioo.mem_nhds htε] with s hs
        exact hx s hs
      exact deriv_deriv_clusterInertia_curve_eq hm hkne (hnc t htε) hxev (hd2 t htε)
        (hode t htε)
    have hPle : deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t + 4 * C
        ≤ (10 * C + 2) * clusterPotential m k (x t) := by
      have h1 := (abs_le.mp (hE t htε)).2
      have h2 := (abs_le.mp (hW t htε)).2
      rw [hPval]
      nlinarith [h1, h2, hU1, hC.le]
    have hz1 : ∀ j ∈ k, ‖deriv x t j‖ ≤ Cv' * Real.sqrt (clusterPotential m k (x t)) := by
      intro j hj
      have h1 := hvel j
      have h2 : Real.sqrt (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t + 4 * C)
          ≤ Real.sqrt (10 * C + 2) * Real.sqrt (clusterPotential m k (x t)) := by
        rw [← Real.sqrt_mul (by linarith : (0:ℝ) ≤ 10 * C + 2)]
        exact Real.sqrt_le_sqrt hPle
      have h3 : Ckv * Real.sqrt (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t + 4 * C)
          ≤ Ckv * (Real.sqrt (10 * C + 2)
              * Real.sqrt (clusterPotential m k (x t))) :=
        mul_le_mul_of_nonneg_left h2 hCkv0
      have h4 : Ckv * Real.sqrt (10 * C + 2) ≤ Cv' := by
        rw [hCv'def]; linarith
      calc ‖deriv x t j‖
          ≤ Ckv * Real.sqrt (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
              + 4 * C) := h1
        _ ≤ Ckv * (Real.sqrt (10 * C + 2) * Real.sqrt (clusterPotential m k (x t))) := h3
        _ = (Ckv * Real.sqrt (10 * C + 2)) * Real.sqrt (clusterPotential m k (x t)) := by ring
        _ ≤ Cv' * Real.sqrt (clusterPotential m k (x t)) :=
            mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg _)
    have hz2 : ∀ j ∉ k, ‖deriv x t j‖ ≤ Cv' * Real.sqrt (clusterPotential m k (x t)) := by
      intro j hj
      have h4 : Cv ≤ Cv' := by
        rw [hCv'def]
        linarith [mul_nonneg hCkv0 (Real.sqrt_nonneg (10 * C + 2))]
      calc ‖deriv x t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (x t)) := hv t htε j hj
        _ ≤ Cv' * Real.sqrt (clusterPotential m k (x t)) :=
            mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg _)
    have h := hjolt (x t) (deriv x t) (hsep t htε) (hnc t htε) hU1 hz1 hz2 i hi
    have hsum : (∑ j ∈ Finset.univ.erase i, m j • pairJolt (x t) (deriv x t) j i)
        = ∑ j ∈ Finset.univ.erase i,
            ((m j * (‖x t j - x t i‖ ^ 3)⁻¹) • (deriv x t j - deriv x t i)
              - (3 * (m j * ((‖x t j - x t i‖ ^ 5)⁻¹
                  * inner ℝ (x t j - x t i) (deriv x t j - deriv x t i))))
                • (x t j - x t i)) :=
      Finset.sum_congr rfl fun j _ => smul_pairJolt (m j) (x t) (deriv x t) j i
    rw [iteratedDeriv_three_apply (m := m) (x := x) (ε := ε) (t := t)
      (fun i => ne_of_gt (hm i)) htε hx (hd3 t htε) hode hnc i, hsum]
    exact h
  -- the `cmRel` bound
  have hcm : ∀ t ∈ Ioo (0:ℝ) ε₁,
      ‖cmRel m k (deriv (deriv (deriv x)) t)‖
        ≤ Real.sqrt (k.card : ℝ) * (1 + (clusterMass m k)⁻¹ * (∑ i ∈ k, m i))
            * (A * Cv' * Real.sqrt (clusterPotential m k (x t))
                * (clusterPotential m k (x t)) ^ 3) := by
    intro t ht
    have hU1 := (hsetup t ht).1
    have hU0 : 0 ≤ clusterPotential m k (x t) := le_trans zero_le_one hU1
    have hB : 0 ≤ A * Cv' * Real.sqrt (clusterPotential m k (x t))
        * (clusterPotential m k (x t)) ^ 3 := by
      have h1 : 0 ≤ Real.sqrt (clusterPotential m k (x t)) := Real.sqrt_nonneg _
      have h2 : 0 ≤ (clusterPotential m k (x t)) ^ 3 := by positivity
      have h3 : 0 ≤ A * Cv' * Real.sqrt (clusterPotential m k (x t)) :=
        mul_nonneg (mul_nonneg hApos.le hCv'0) h1
      exact mul_nonneg h3 h2
    have h := norm_cmRel_le (m := m) (k := k) (v := deriv (deriv (deriv x)) t)
      (B := A * Cv' * Real.sqrt (clusterPotential m k (x t)) * (clusterPotential m k (x t)) ^ 3)
      hm hB (fun i hi => hjoltapply t ht i hi)
    calc ‖cmRel m k (deriv (deriv (deriv x)) t)‖
        ≤ Real.sqrt (k.card : ℝ) * ((A * Cv' * Real.sqrt (clusterPotential m k (x t))
              * (clusterPotential m k (x t)) ^ 3)
            + (clusterMass m k)⁻¹ * ((∑ i ∈ k, m i)
              * (A * Cv' * Real.sqrt (clusterPotential m k (x t))
                  * (clusterPotential m k (x t)) ^ 3))) := h
      _ = Real.sqrt (k.card : ℝ) * (1 + (clusterMass m k)⁻¹ * (∑ i ∈ k, m i))
            * (A * Cv' * Real.sqrt (clusterPotential m k (x t))
                * (clusterPotential m k (x t)) ^ 3) := by ring
  -- the final bound
  set Pmax : ℝ := (4:ℝ)/9 * κ + 1 with hPmax
  have hPmaxpos : 0 < Pmax := by rw [hPmax]; positivity
  have hcoef : 0 ≤ Real.sqrt (k.card : ℝ) * (1 + (clusterMass m k)⁻¹ * (∑ i ∈ k, m i)) := by
    have hmk0 : 0 ≤ clusterMass m k := clusterMass_nonneg (fun i => (hm i).le) k
    have h1 : 0 ≤ (1:ℝ) + (clusterMass m k)⁻¹ * (∑ i ∈ k, m i) :=
      add_nonneg zero_le_one (mul_nonneg (inv_nonneg.mpr hmk0)
        (Finset.sum_nonneg fun i _ => (hm i).le))
    exact mul_nonneg (Real.sqrt_nonneg _) h1
  have hevP : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      t ^ ((2:ℝ)/3) * deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t ≤ Pmax := by
    have h := hSec.eventually (isOpen_Iio.mem_nhds
      (show (4:ℝ)/9 * κ < Pmax by rw [hPmax]; linarith))
    filter_upwards [h] with t ht
    rw [mul_comm]
    exact le_of_lt ht
  refine ⟨Real.sqrt (k.card : ℝ) * (1 + (clusterMass m k)⁻¹ * (∑ i ∈ k, m i))
      * (A * Cv' * (8 * C + 3) ^ ((7:ℝ)/2) * Pmax ^ ((7:ℝ)/2)), by positivity, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hε₁pos, hevP] with t ht hPt
  have ht0 : 0 < t := ht.1
  obtain ⟨hU1, hUΦ, hP1, hvel⟩ := hsetup t ht
  have hU0 : 0 ≤ clusterPotential m k (x t) := le_trans zero_le_one hU1
  have hP0 : 0 ≤ deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t :=
    le_trans zero_le_one hP1
  have h8 : (0:ℝ) ≤ 8 * C + 3 := by linarith
  have hbase : (0:ℝ) < (8 * C + 3) * deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t :=
    mul_pos (by linarith : (0:ℝ) < 8 * C + 3) (lt_of_lt_of_le one_pos hP1)
  have hPhi : clusterPotential m k (x t)
      ≤ (8 * C + 3) * deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t := by
    nlinarith [hUΦ, hP1, hC.le]
  have hkey : Real.sqrt (clusterPotential m k (x t)) * (clusterPotential m k (x t)) ^ 3
      ≤ ((8 * C + 3) * deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) ^ ((7:ℝ)/2) := by
    have h1 : Real.sqrt (clusterPotential m k (x t))
        ≤ Real.sqrt (8 * C + 3)
          * Real.sqrt (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) := by
      rw [← Real.sqrt_mul h8]
      exact Real.sqrt_le_sqrt hPhi
    have h2 : (clusterPotential m k (x t)) ^ 3
        ≤ ((8 * C + 3) * deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) ^ 3 :=
      pow_le_pow_left₀ hU0 hPhi 3
    refine le_trans (mul_le_mul h1 h2 (by positivity) (by positivity)) ?_
    have h3 : Real.sqrt (8 * C + 3)
          * Real.sqrt (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t)
        = ((8 * C + 3) * deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t)
            ^ ((1:ℝ)/2) := by
      rw [← Real.sqrt_mul h8, Real.sqrt_eq_rpow]
    rw [h3, ← Real.rpow_natCast
        ((8 * C + 3) * deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) 3,
      ← Real.rpow_add hbase]
    norm_num
  have hB : A * Cv' * Real.sqrt (clusterPotential m k (x t)) * (clusterPotential m k (x t)) ^ 3
      ≤ A * Cv' * ((8 * C + 3) * deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t)
          ^ ((7:ℝ)/2) := by
    rw [show A * Cv' * Real.sqrt (clusterPotential m k (x t)) * (clusterPotential m k (x t)) ^ 3
        = A * Cv' * (Real.sqrt (clusterPotential m k (x t))
            * (clusterPotential m k (x t)) ^ 3) by ring]
    exact mul_le_mul_of_nonneg_left hkey (mul_nonneg hApos.le hCv'0)
  have hPt2 : t ^ ((7:ℝ)/3) * (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t)
        ^ ((7:ℝ)/2) ≤ Pmax ^ ((7:ℝ)/2) := by
    have h7 : t ^ ((7:ℝ)/3) = (t ^ ((2:ℝ)/3)) ^ ((7:ℝ)/2) := by
      rw [← Real.rpow_mul ht0.le]
      norm_num
    rw [h7]
    have hcomb : (t ^ ((2:ℝ)/3)) ^ ((7:ℝ)/2)
          * (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) ^ ((7:ℝ)/2)
        = (t ^ ((2:ℝ)/3)
            * deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) ^ ((7:ℝ)/2) :=
      (Real.mul_rpow (x := t ^ ((2:ℝ)/3))
        (y := deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) (z := (7:ℝ)/2)
        (Real.rpow_nonneg ht0.le _) hP0).symm
    rw [hcomb]
    exact Real.rpow_le_rpow (by positivity) hPt (by norm_num)
  have hAB : t ^ ((7:ℝ)/3) * (A * Cv' * ((8 * C + 3)
        * deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) ^ ((7:ℝ)/2))
      ≤ A * Cv' * (8 * C + 3) ^ ((7:ℝ)/2) * Pmax ^ ((7:ℝ)/2) := by
    have h4 : ((8 * C + 3) * deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t)
          ^ ((7:ℝ)/2)
        = (8 * C + 3) ^ ((7:ℝ)/2)
          * (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) ^ ((7:ℝ)/2) :=
      Real.mul_rpow h8 hP0
    rw [h4]
    have hcoef2 : 0 ≤ A * Cv' * (8 * C + 3) ^ ((7:ℝ)/2) :=
      mul_nonneg (mul_nonneg hApos.le hCv'0) (Real.rpow_nonneg h8 _)
    refine le_trans (le_of_eq ?_) (le_trans (mul_le_mul_of_nonneg_left hPt2 hcoef2) (le_of_eq ?_))
    · ring
    · ring
  calc t ^ ((7:ℝ)/3) * ‖cmRel m k (deriv (deriv (deriv x)) t)‖
      ≤ t ^ ((7:ℝ)/3) * (Real.sqrt (k.card : ℝ)
          * (1 + (clusterMass m k)⁻¹ * (∑ i ∈ k, m i))
          * (A * Cv' * Real.sqrt (clusterPotential m k (x t))
              * (clusterPotential m k (x t)) ^ 3)) :=
        mul_le_mul_of_nonneg_left (hcm t ht) (by positivity)
    _ = Real.sqrt (k.card : ℝ) * (1 + (clusterMass m k)⁻¹ * (∑ i ∈ k, m i))
          * (t ^ ((7:ℝ)/3) * (A * Cv' * Real.sqrt (clusterPotential m k (x t))
              * (clusterPotential m k (x t)) ^ 3)) := by ring
    _ ≤ Real.sqrt (k.card : ℝ) * (1 + (clusterMass m k)⁻¹ * (∑ i ∈ k, m i))
          * (A * Cv' * (8 * C + 3) ^ ((7:ℝ)/2) * Pmax ^ ((7:ℝ)/2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoef
        exact le_trans (mul_le_mul_of_nonneg_left hB (by positivity)) hAB

end Submission.NBody
