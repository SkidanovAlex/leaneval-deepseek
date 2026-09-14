import Submission.NBody.MarchalThirdDeriv2
import Submission.NBody.MarchalClusterFull
import Submission.Commons.Analysis.Calculus.second_deriv_asymptotic_of_third_deriv_bound
import Submission.Commons.Analysis.Calculus.sundman_asymptotic_ratio

/-!
# The third-derivative bound in the form of the Sundman refinement

Ferrario–Terracini's refinement `(6.19)` of the Sundman asymptotics needs, for the moment of inertia
`I_k` of a colliding cluster,

    `|I_k'''| ≤ e (I_k'')^{(2b-3)/(b-2)}`  (with `b = 4`, exponent `5/2`).

This file assembles that inequality from `abs_third_deriv_clusterInertia_le`
(`Submission/NBody/MarchalThirdDeriv2.lean`), by choosing the parameter `Φ` of that lemma to be
`I_k'' + 8C + 2` where `C` bounds the relative energy, the interaction work and the inertia.

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

/-- **The third-derivative bound for a colliding cluster.**  There is a constant `e > 0` and a
shrunk interval on which `|I_k'''| ≤ e (I_k'')^{5/2}`. -/
theorem exists_third_deriv_bound {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε C ν Cv : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C)
    (hν : 0 < ν) (hCv : 0 ≤ Cv)
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
    ∃ e : ℝ, 0 < e ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε ∧
      ∀ t ∈ Ioo (0:ℝ) ε₁,
        |deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t|
          ≤ e * (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t)
              ^ ((2 * 4 - 3) / (4 - 2) : ℝ) := by
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
  set Emain : ℝ := (6 * A * Real.sqrt (clusterMass m k)
      + 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Ckv
        + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C₀) * (∑ j : Fin N, m j) * (2 * Ckv))
      + 2) * (8 * C + 3) ^ ((5:ℝ)/2) with hEmain
  have hEmainpos : 0 < Emain := by
    rw [hEmain]
    refine mul_pos ?_ (Real.rpow_pos_of_pos (by linarith) _)
    have h1 : 0 ≤ 6 * A * Real.sqrt (clusterMass m k) := by positivity
    have h2 : 0 ≤ 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Ckv
        + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C₀) * (∑ j : Fin N, m j) * (2 * Ckv)) := by
      have h2a : 0 ≤ 2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Ckv := by positivity
      have h2b : 0 ≤ 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C₀) * (∑ j : Fin N, m j)
          * (2 * Ckv) := by
        have h1 : (0:ℝ) ≤ 4 := by norm_num
        have h2 : (0:ℝ) ≤ (ν⁻¹) ^ 3 := by positivity
        have h3 : (0:ℝ) ≤ Real.sqrt (clusterMass m k * C₀) := Real.sqrt_nonneg _
        have h4 : (0:ℝ) ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
        have h5 : (0:ℝ) ≤ 2 * Ckv := by linarith
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4) h5
      linarith
    linarith
  refine ⟨Emain, hEmainpos, ε₁, hε₁pos, hε₁le, ?_⟩
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
      have hUle : clusterPotential m k (x t) ≤ (8 * C + 3) * (P + 4 * C) := by
        have h2 : P + 8 * C + 2 ≤ (8 * C + 3) * (P + 4 * C) := by nlinarith [hM1, hM0, hC]
        linarith [hUΦ, h2]
      have hsq' : Real.sqrt (clusterPotential m k (x t))
          ≤ Real.sqrt (8 * C + 3) * Real.sqrt (P + 4 * C) := by
        calc Real.sqrt (clusterPotential m k (x t))
            ≤ Real.sqrt ((8 * C + 3) * (P + 4 * C)) := Real.sqrt_le_sqrt hUle
          _ = Real.sqrt (8 * C + 3) * Real.sqrt (P + 4 * C) :=
              Real.sqrt_mul (by positivity) _
      have h1' : ‖deriv x t j‖ ≤ Cv * Real.sqrt (8 * C + 3) * Real.sqrt (P + 4 * C) := by
        calc ‖deriv x t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (x t)) := h1
          _ ≤ Cv * (Real.sqrt (8 * C + 3) * Real.sqrt (P + 4 * C)) :=
              mul_le_mul_of_nonneg_left hsq' hCv
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
  have hacc2 : ∀ i ∈ k, ‖(cmRel m k (deriv (deriv x) t)) i‖ ≤ A * (P + 8 * C + 2) ^ 2 := by
    intro i hi
    rw [hode_t, cmRel_apply_of_mem hi]
    refine le_trans (hA (x t) (hsep t htε) (hnc t htε) hU1 i hi) ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hU0 hUΦ 2) hApos.le
  have hmain := abs_third_deriv_clusterInertia_le (m := m) (k := k) (x := x) (ε := ε₁) (t := t)
    (Φ := P + 8 * C + 2) (A := A) (C := C₀) (Cv := Ckv) (M := P + 4 * C) (κ := κ) (ν := ν)
    hm hκ hκpos hkne ht
    (fun s hs => hx s (hmem s hs))
    (fun s hs => by
      rw [← iteratedDeriv_two_eq_deriv_deriv x s]
      exact hd2 s (hmem s hs))
    (fun s hs => hd3 s (hmem s hs))
    (fun s hs => hode s (hmem s hs))
    (fun s hs => hnc s (hmem s hs))
    (by linarith) hApos.le hC₀pos.le hCkv0 hν (hsep t htε)
    hacc2 hvel hR hM0 (by linarith) hUΦ (hε₁ t ht)
  have hrpow : (P + 8 * C + 2) ^ 2 * Real.sqrt (P + 8 * C + 2)
      = (P + 8 * C + 2) ^ ((5:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ 2,
      ← Real.rpow_add (by linarith : (0:ℝ) < P + 8 * C + 2)]
    norm_num
  have hΦle : P + 8 * C + 2 ≤ (8 * C + 3) * P := by nlinarith [hP1, hC]
  have hPpos : 0 < P := lt_of_lt_of_le one_pos hP1
  have hrpow2 : (P + 8 * C + 2) ^ ((5:ℝ)/2) ≤ (8 * C + 3) ^ ((5:ℝ)/2) * P ^ ((5:ℝ)/2) := by
    rw [← Real.mul_rpow (by linarith : (0:ℝ) ≤ 8 * C + 3) hPpos.le]
    exact Real.rpow_le_rpow (by linarith) hΦle (by norm_num)
  have hconst0 : 0 ≤ 6 * A * Real.sqrt (clusterMass m k)
      + 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Ckv
        + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C₀) * (∑ j : Fin N, m j) * (2 * Ckv))
      + 2 := by
    have h1 : 0 ≤ 6 * A * Real.sqrt (clusterMass m k) := by positivity
    have h2 : 0 ≤ 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Ckv
        + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C₀) * (∑ j : Fin N, m j)
            * (2 * Ckv)) := by
      have h2a : 0 ≤ 2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Ckv := by positivity
      have h2b : 0 ≤ 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C₀) * (∑ j : Fin N, m j)
          * (2 * Ckv) := by
        have hb1 : (0:ℝ) ≤ 4 := by norm_num
        have hb2 : (0:ℝ) ≤ (ν⁻¹) ^ 3 := by positivity
        have hb3 : (0:ℝ) ≤ Real.sqrt (clusterMass m k * C₀) := Real.sqrt_nonneg _
        have hb4 : (0:ℝ) ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
        have hb5 : (0:ℝ) ≤ 2 * Ckv := by linarith
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hb1 hb2) hb3) hb4) hb5
      linarith
    linarith
  calc |deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t|
      ≤ (6 * A * Real.sqrt (clusterMass m k)
          + 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Ckv
            + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C₀) * (∑ j : Fin N, m j)
                * (2 * Ckv)) + 2)
          * ((P + 8 * C + 2) ^ 2 * Real.sqrt (P + 8 * C + 2)) := hmain
    _ = (6 * A * Real.sqrt (clusterMass m k)
          + 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Ckv
            + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C₀) * (∑ j : Fin N, m j)
                * (2 * Ckv)) + 2) * ((P + 8 * C + 2) ^ ((5:ℝ)/2)) := by rw [hrpow]
    _ ≤ (6 * A * Real.sqrt (clusterMass m k)
          + 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Ckv
            + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C₀) * (∑ j : Fin N, m j)
                * (2 * Ckv)) + 2) * ((8 * C + 3) ^ ((5:ℝ)/2) * P ^ ((5:ℝ)/2)) :=
        mul_le_mul_of_nonneg_left hrpow2 hconst0
    _ = Emain * P ^ ((2 * 4 - 3) / (4 - 2) : ℝ) := by
        rw [hEmain]
        rw [show ((5:ℝ)/2) = (2 * 4 - 3) / (4 - 2) by norm_num]
        ring


/-- **The refinement of Sundman's asymptotics for a colliding cluster**: the second derivative of
the moment of inertia satisfies `Ï_k √(I_k) → η/4` for some `η > 0`.  Together with
`clusterInertia_asymptotic` (`I_k ~ κ t^{4/3}`) this gives `Ï_k ~ (4/9) κ t^{-2/3}`. -/
theorem clusterInertia_second_deriv_asymptotic {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv)
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
    ∃ η : ℝ, 0 < η ∧ Tendsto
      (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
        * (clusterInertia m k (x t)) ^ ((1:ℝ)/2))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (η / 4)) := by
  classical
  obtain ⟨i0, hi0⟩ : k.Nonempty := Finset.card_pos.mp (by omega)
  have hkne : k.Nonempty := ⟨i0, hi0⟩
  obtain ⟨ck, hckpos, hcksp⟩ := exists_const_le_clusterPotential (E := E) hm k hk2
  -- the third-derivative bound
  obtain ⟨e, hepos, εT, hεTpos, hεTle, hthird⟩ := exists_third_deriv_bound (m := m) (k := k)
    (x := x) (ε := ε) (C := C) (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode
    hsep hv hI
  -- differentiability bookkeeping
  have hxev : ∀ t ∈ Ioo (0:ℝ) ε, ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hx s hs
  have hd2' : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) t) t :=
    fun t ht => (hd2 t ht).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x t)
  have hfpos0 : ∀ t ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x t) :=
    fun t ht => clusterInertia_pos hm hk2 (hnc t ht)
  -- shrink the interval so that `√(I_k) < ck/(12 C)`
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt (clusterInertia m k (x t)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have h1 := Real.continuous_sqrt.continuousAt.tendsto.comp hI
    simpa only [Function.comp_def, Real.sqrt_zero] using h1
  have hthr : (0:ℝ) < ck / (12 * C) := by positivity
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      Real.sqrt (clusterInertia m k (x t)) < ck / (12 * C) :=
    hsqrt.eventually (isOpen_Iio.mem_nhds hthr)
  obtain ⟨ε₁, hε₁pos, hε₁le, hε₁⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε ∧
      ∀ t ∈ Ioo (0:ℝ) ε₁, Real.sqrt (clusterInertia m k (x t)) < ck / (12 * C) := by
    rw [eventually_nhdsWithin_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hev
    refine ⟨min δ ε, lt_min hδpos hε, min_le_right _ _, fun t ht => hδ t ?_ ht.1⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact lt_of_lt_of_le ht.2 (min_le_left _ _)
  have hmem : ∀ t ∈ Ioo (0:ℝ) ε₁, t ∈ Ioo (0:ℝ) ε :=
    fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hε₁le⟩
  -- the interval on which everything holds
  set ε₂ : ℝ := min εT ε₁ with hε₂def
  have hε₂pos : 0 < ε₂ := by rw [hε₂def]; exact lt_min hεTpos hε₁pos
  have hmemT : ∀ t ∈ Ioo (0:ℝ) ε₂, t ∈ Ioo (0:ℝ) εT :=
    fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (by rw [hε₂def]; exact min_le_left _ _)⟩
  have hmem1 : ∀ t ∈ Ioo (0:ℝ) ε₂, t ∈ Ioo (0:ℝ) ε₁ :=
    fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (by rw [hε₂def]; exact min_le_right _ _)⟩
  have hmemε : ∀ t ∈ Ioo (0:ℝ) ε₂, t ∈ Ioo (0:ℝ) ε :=
    fun t ht => hmem t (hmem1 t ht)
  -- the basic objects of the Sundman analysis
  have hfpos : ∀ t ∈ Ioo (0:ℝ) ε₂, 0 < clusterInertia m k (x t) :=
    fun t ht => hfpos0 t (hmemε t ht)
  have hf1 : ∀ t ∈ Ioo (0:ℝ) ε₂,
      HasDerivAt (fun s : ℝ => clusterInertia m k (x s))
        (deriv (fun s : ℝ => clusterInertia m k (x s)) t) t :=
    fun t ht => hasDerivAt_clusterInertia_curve (hxev t (hmemε t ht))
  have hf2 : ∀ t ∈ Ioo (0:ℝ) ε₂,
      HasDerivAt (deriv (fun s : ℝ => clusterInertia m k (x s)))
        (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) t :=
    fun t ht => hasDerivAt_deriv_clusterInertia_curve (hxev t (hmemε t ht))
      (hd2' t (hmemε t ht))
  have hf3 : ∀ t ∈ Ioo (0:ℝ) ε₂,
      HasDerivAt (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))))
        (deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t) t :=
    fun t ht => hasDerivAt_deriv_deriv_clusterInertia_curve (m := m) (k := k) (x := x)
      (ε := ε₂) ht (fun s hs => hx s (hmemε s hs)) (fun s hs => hd2' s (hmemε s hs))
      (fun s hs => hd3 s (hmemε s hs))
  have hineq : ∀ t ∈ Ioo (0:ℝ) ε₂,
      (deriv (fun s : ℝ => clusterInertia m k (x s)) t) ^ (2:ℕ)
        ≤ 4 * clusterInertia m k (x t) * deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
          + 16 * C * clusterInertia m k (x t) := by
    intro t ht
    have h := clusterInertia_deriv_sq_le_rel (k := k) (x := x) (C := C) hm hkne
      (hE t (hmemε t ht)) (hW t (hmemε t ht)) (hxev t (hmemε t ht)) (hd2 t (hmemε t ht))
      (hode t (hmemε t ht)) (hnc t (hmemε t ht))
    rwa [iteratedDeriv_two_eq_deriv_deriv
      (fun s : ℝ => clusterInertia m k (x s)) t] at h
  have hbound : ∀ t ∈ Ioo (0:ℝ) ε₂,
      ck / 2 ≤ deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
        * (clusterInertia m k (x t)) ^ ((1:ℝ)/2) := by
    intro t ht
    have h := clusterInertia_second_deriv_ge_rel (k := k) (x := x) (C := C) (ck := ck) hm hkne
      (le_trans (neg_le_neg (hE t (hmemε t ht))) (neg_abs_le _))
      (le_trans (neg_le_neg (hW t (hmemε t ht))) (neg_abs_le _))
      (hcksp (x t) (hnc t (hmemε t ht))) (hxev t (hmemε t ht)) (hd2 t (hmemε t ht))
      (hode t (hmemε t ht)) (hnc t (hmemε t ht))
    rw [iteratedDeriv_two_eq_deriv_deriv (fun s : ℝ => clusterInertia m k (x s)) t] at h
    have hrootpos : 0 < Real.sqrt (clusterInertia m k (x t)) :=
      Real.sqrt_pos.mpr (hfpos t ht)
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hrootpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hrootpos), add_mul] at hmul
    have h6 : 6 * C * Real.sqrt (clusterInertia m k (x t)) < ck / 2 := by
      have h1 : 6 * C * Real.sqrt (clusterInertia m k (x t)) < 6 * C * (ck / (12 * C)) :=
        mul_lt_mul_of_pos_left (hε₁ t (hmem1 t ht)) (by positivity)
      have h2 : 6 * C * (ck / (12 * C)) = ck / 2 := by field_simp; ring
      linarith [h1, h2.le]
    have hPr : ck / 2 ≤ deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
        * Real.sqrt (clusterInertia m k (x t)) := by linarith [hmul, h6]
    rwa [← Real.sqrt_eq_rpow]
  have hmono : ∀ t ∈ Ioo (0:ℝ) ε₂,
      0 ≤ deriv (fun s : ℝ => clusterInertia m k (x s)) t :=
    deriv_nonneg_of_second_deriv_mul_sqrt_ge hε₂pos (by positivity) hf1 hf2 hfpos hbound hI
  -- Sundman's argument: `(f')²/f^{1/2} → η`
  obtain ⟨η, hηpos, hη⟩ := Commons.Analysis.Calculus.sundman_asymptotic_ratio
    (f := fun s : ℝ => clusterInertia m k (x s)) (b := 4) (c := 16 * C) (d := ck / 2)
    hε₂pos (by norm_num) (by positivity) hf1 hf2 hfpos hineq hmono hI (fun t ht => by
      rw [show ((4:ℝ) - 2)/4 = (1:ℝ)/2 by norm_num]
      exact hbound t ht)
  -- the refinement
  have hbound' : ∀ t ∈ Ioo (0:ℝ) ε₂,
      ck / 2 ≤ deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
        * (clusterInertia m k (x t)) ^ (((4:ℝ) - 2) / 4) := by
    intro t ht
    rw [show (((4:ℝ)) - 2) / 4 = (1:ℝ)/2 by norm_num]
    exact hbound t ht
  have hthird' : ∀ t ∈ Ioo (0:ℝ) ε₂,
      |deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t|
        ≤ e * (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) ^ ((2 * 4 - 3) / (4 - 2) : ℝ) :=
    fun t ht => hthird t (hmemT t ht)
  refine ⟨η, hηpos, ?_⟩
  have hfin := Commons.Analysis.Calculus.second_deriv_asymptotic_of_third_deriv_bound
    (f := fun s : ℝ => clusterInertia m k (x s)) (b := 4) (c := 16 * C) (d := ck / 2) (e := e)
    (η := η) (ε := ε₂) hε₂pos (by norm_num) (by positivity) hepos hηpos
    hf1 hf2 hf3 hfpos hineq hmono hI hbound' hthird' hη
  have hb : (4 - 2 : ℝ) / 4 = (1:ℝ)/2 := by norm_num
  rw [hb] at hfin
  exact hfin

end Submission.NBody
