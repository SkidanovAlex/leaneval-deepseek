import Submission.NBody.MarchalClusterPlumbing
import Submission.Commons.Analysis.Calculus.sundman_asymptotic_ratio
import Submission.Commons.Analysis.Calculus.rpow_asymptotic_of_deriv_sq_div_asymptotic

/-!
# Sundman's asymptotic law for a colliding cluster

The classical asymptotic law of Sundman–Sperling–Sperner: if `x` is a solution of Newton's
equations on `(0, ε)`, collision free there, and the bodies of the cluster `k` (`2 ≤ #k`) collapse
at `t = 0` (`I_k(x(t)) → 0`) while its energy relative to the centre of mass and its interaction
work with the other bodies stay bounded, then there is `κ > 0` with

    `I_k(x(t)) = κ t^{4/3} + o(t^{4/3})`,   i.e.   `I_k(x(t)) / t^{4/3} → κ`.

The proof follows Ferrario–Terracini (`propo:asy`), i.e. Sundman's argument:

* `Ï_k = 4E_k^{rel} + 2U_k + 2W_k` (`deriv_deriv_clusterInertia_curve_eq`);
* Ostrogradsky + the boundedness of `E_k^{rel}` and `W_k` give `(İ_k)² ≤ 4 I_k Ï_k + 16 C I_k`;
* Sperner's a priori bound `U_k ≥ c/√(I_k)` gives `Ï_k I_k^{1/2} ≥ c/2` once `I_k` is small, whence
  also `İ_k ≥ 0` (`deriv_nonneg_of_second_deriv_mul_sqrt_ge`);
* `sundman_asymptotic_ratio` (with `b = 4`) produces `η > 0` with `(İ_k)² / I_k^{1/2} → η`, and
  `rpow_asymptotic_of_deriv_sq_div_asymptotic` turns this into `I_k/t^{4/3} → ((3/4)√η)^{4/3}`.

Everything in this file is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators Topology
open InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Sundman's asymptotic law for a colliding cluster.** -/
theorem clusterInertia_asymptotic {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε C : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |clusterRelEnergy m k (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |crossWork m k (x t) (cmRel m k (x t))| ≤ C)
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ) := by
  classical
  obtain ⟨i0, hi0⟩ : k.Nonempty := by
    rcases Finset.eq_empty_or_nonempty k with h | h
    · rw [h] at hk2; simp at hk2
    · exact h
  -- Sperner's bound
  obtain ⟨ck, hckpos, hcksp⟩ := exists_const_le_clusterPotential (E := E) hm k hk2
  -- the cluster's colliding solution has positive inertia
  have hfpos0 : ∀ t ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x t) :=
    fun t ht => clusterInertia_pos hm hk2 (hnc t ht)
  -- eventual differentiability
  have hxev : ∀ t ∈ Ioo (0:ℝ) ε, ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hx s hs
  have hd2' : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) t) t :=
    fun t ht => (hd2 t ht).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x t)
  -- shrink the interval so that `√(I_k) ≤ ck/(12 C)`
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
  have hmem : ∀ t ∈ Ioo (0:ℝ) ε₁, t ∈ Ioo (0:ℝ) ε := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hε₁le⟩
  -- the function `f = I_k ∘ x` on `(0, ε₁)`
  have hfpos : ∀ t ∈ Ioo (0:ℝ) ε₁, 0 < clusterInertia m k (x t) :=
    fun t ht => hfpos0 t (hmem t ht)
  have hf1 : ∀ t ∈ Ioo (0:ℝ) ε₁,
      HasDerivAt (fun s : ℝ => clusterInertia m k (x s))
        (deriv (fun s : ℝ => clusterInertia m k (x s)) t) t :=
    fun t ht => hasDerivAt_clusterInertia_curve (hxev t (hmem t ht))
  have hf2 : ∀ t ∈ Ioo (0:ℝ) ε₁,
      HasDerivAt (deriv (fun s : ℝ => clusterInertia m k (x s)))
        (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) t :=
    fun t ht => hasDerivAt_deriv_clusterInertia_curve (hxev t (hmem t ht)) (hd2' t (hmem t ht))
  have hlim : Tendsto (fun s : ℝ => clusterInertia m k (x s)) (nhdsWithin (0:ℝ) (Ioi 0))
      (nhds 0) := hI
  -- the second derivative in the Lagrange–Jacobi form
  have hd2val : ∀ t ∈ Ioo (0:ℝ) ε₁,
      deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
        = 4 * clusterRelEnergy m k (x t) (deriv x t) + 2 * clusterPotential m k (x t)
          + 2 * crossWork m k (x t) (cmRel m k (x t)) :=
    fun t ht => deriv_deriv_clusterInertia_curve_eq hm ⟨i0, hi0⟩ (hnc t (hmem t ht))
      (hxev t (hmem t ht)) (hd2 t (hmem t ht)) (hode t (hmem t ht))
  -- Ostrogradsky's inequality with `b = 4`, `c = 16 C`
  have hineq : ∀ t ∈ Ioo (0:ℝ) ε₁,
      (deriv (fun s : ℝ => clusterInertia m k (x s)) t) ^ (2:ℕ)
        ≤ 4 * clusterInertia m k (x t) * deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
          + 16 * C * clusterInertia m k (x t) := by
    intro t ht
    have h := clusterInertia_deriv_sq_le_rel (k := k) (x := x) (C := C) hm ⟨i0, hi0⟩
      (hE t (hmem t ht)) (hW t (hmem t ht)) (hxev t (hmem t ht)) (hd2 t (hmem t ht))
      (hode t (hmem t ht)) (hnc t (hmem t ht))
    rwa [iteratedDeriv_two_eq_deriv_deriv
      (fun s : ℝ => clusterInertia m k (x s)) t] at h
  -- the lower bound `Ï_k √(I_k) ≥ ck/2`
  have hbound : ∀ t ∈ Ioo (0:ℝ) ε₁,
      ck / 2 ≤ deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
        * (clusterInertia m k (x t)) ^ ((1:ℝ)/2) := by
    intro t ht
    have htε := hmem t ht
    have h := clusterInertia_second_deriv_ge_rel (k := k) (x := x) (C := C) (ck := ck) hm ⟨i0, hi0⟩
      (le_trans (neg_le_neg (hE t htε)) (neg_abs_le _))
      (le_trans (neg_le_neg (hW t htε)) (neg_abs_le _))
      (hcksp (x t) (hnc t htε)) (hxev t htε) (hd2 t htε) (hode t htε) (hnc t htε)
    rw [iteratedDeriv_two_eq_deriv_deriv (fun s : ℝ => clusterInertia m k (x s)) t] at h
    have hrootpos : 0 < Real.sqrt (clusterInertia m k (x t)) := Real.sqrt_pos.mpr (hfpos t ht)
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hrootpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hrootpos), add_mul] at hmul
    have h6 : 6 * C * Real.sqrt (clusterInertia m k (x t)) ≤ ck / 2 := by
      have h1 : 6 * C * Real.sqrt (clusterInertia m k (x t)) < 6 * C * (ck / (12 * C)) :=
        mul_lt_mul_of_pos_left (hε₁ t ht) (by positivity)
      have h2 : 6 * C * (ck / (12 * C)) = ck / 2 := by
        field_simp
        norm_num
      linarith
    rw [← Real.sqrt_eq_rpow]
    linarith
  -- monotonicity of `f'`
  have hmono : ∀ t ∈ Ioo (0:ℝ) ε₁, 0 ≤ deriv (fun s : ℝ => clusterInertia m k (x s)) t :=
    deriv_nonneg_of_second_deriv_mul_sqrt_ge hε₁pos (by positivity) hf1 hf2 hfpos hbound hlim
  -- Sundman's argument
  obtain ⟨η, hηpos, hη⟩ := Commons.Analysis.Calculus.sundman_asymptotic_ratio (f := fun s : ℝ => clusterInertia m k (x s))
    (b := 4) (c := 16 * C) (d := ck / 2) hε₁pos (by norm_num) (by positivity) hf1 hf2 hfpos
    hineq hmono hlim (fun t ht => by
      rw [show ((4:ℝ) - 2)/4 = (1:ℝ)/2 by norm_num]
      exact hbound t ht)
  -- integrate the ratio
  have hfint : ∀ a u : ℝ, 0 < a → a ≤ u → u < ε₁ →
      IntervalIntegrable (deriv (fun s : ℝ => clusterInertia m k (x s))) MeasureTheory.volume a u := by
    intro a u ha hau hu
    refine ContinuousOn.intervalIntegrable fun s hs => ?_
    rw [uIcc_of_le hau] at hs
    exact ((hf2 s ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hu⟩).differentiableAt).continuousAt.continuousWithinAt
  have hfinal := Commons.Analysis.Calculus.rpow_asymptotic_of_deriv_sq_div_asymptotic
    (f := fun s : ℝ => clusterInertia m k (x s)) (b := 4) (η := η) hε₁pos (by norm_num) hηpos
    hf1 hfint hfpos hmono hlim hη
  refine ⟨((3:ℝ)/4 * Real.sqrt η) ^ ((4:ℝ)/3), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  have hb11 : (4:ℝ) / (4 - 1) = 4 / 3 := by norm_num
  have hb12 : (4 - 1) / 4 = (3:ℝ) / 4 := by norm_num
  rw [hb11, hb12] at hfinal
  exact hfinal

end Submission.NBody

namespace Submission.NBody

end Submission.NBody
