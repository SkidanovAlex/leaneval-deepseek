import Submission.NBody.MarchalThirdDerivAsymptotic
import Submission.NBody.MarchalClusterAsymptotic
import Submission.Commons.Analysis.Calculus.deriv_tendsto_of_deriv_sq_div_asymptotic

/-!
# The full asymptotic package for a colliding cluster

Ferrario--Terracini's `propo:asy` gives, for an isolated cluster `k` collapsing at `t = 0`
(`I_k(x t) → 0`), not only `I_k(x t) = κ t^{4/3} + o(t^{4/3})` but the whole list of
asymptotic equivalents.  Writing `f = I_k ∘ x`, this file packages:

* `f t / t^{4/3} → κ`;
* `f'(t) / t^{1/3} → (4/3) κ`;
* `f''(t) t^{2/3} → (4/9) κ`;
* `f''(t) √(f t) → (4/9) κ^{3/2}`.

Everything is proved from the same Sundman run (so the constants κ agree by construction).

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

/-- **The full asymptotic package for a colliding cluster.** -/
theorem clusterInertia_asymptotics_of_isolated {m : Fin N → ℝ} {k : Finset (Fin N)}
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
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ) ∧
      Tendsto (fun t : ℝ => deriv (fun s : ℝ => clusterInertia m k (x s)) t / t ^ ((1:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3 * κ)) ∧
      Tendsto (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
        * t ^ ((2:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ)) ∧
      Tendsto (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
        * (clusterInertia m k (x t)) ^ ((1:ℝ)/2))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ ^ ((3:ℝ)/2))) := by
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
  -- the constant `K = (3/4)√η` and `κ = K^{4/3}`
  set K : ℝ := (3:ℝ)/4 * Real.sqrt η with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hsqrtη : Real.sqrt η = (4:ℝ)/3 * K := by rw [hKdef]; ring
  have hKmul : K * K ^ ((1:ℝ)/3) = K ^ ((4:ℝ)/3) := by
    have h := Real.rpow_add hKpos (1:ℝ) ((1:ℝ)/3)
    rw [show (1:ℝ) + 1/3 = (4:ℝ)/3 by norm_num, Real.rpow_one] at h
    exact h.symm
  have hK2 : (K ^ ((4:ℝ)/3)) ^ ((3:ℝ)/2) = K ^ 2 := by
    rw [← Real.rpow_mul hKpos.le, show ((4:ℝ)/3) * ((3:ℝ)/2) = (2:ℝ) by norm_num]
    exact Real.rpow_natCast K 2
  have hηK4 : η / 4 = (4:ℝ)/9 * K ^ 2 := by
    have hsq : K ^ 2 = (9:ℝ)/16 * η := by
      rw [hKdef, mul_pow, Real.sq_sqrt hηpos.le]; ring
    rw [hsq]; ring
  -- the third-derivative refinement: `f'' √f → η/4`
  have hfin2 : Tendsto
      (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
        * (clusterInertia m k (x t)) ^ ((1:ℝ)/2))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (η / 4)) := by
    have hfin := Commons.Analysis.Calculus.second_deriv_asymptotic_of_third_deriv_bound
      (f := fun s : ℝ => clusterInertia m k (x s)) (b := 4) (c := 16 * C) (d := ck / 2) (e := e)
      (η := η) (ε := ε₂) hε₂pos (by norm_num) (by positivity) hepos hηpos
      hf1 hf2 hf3 hfpos hineq hmono hI hbound' hthird' hη
    have hb : (4 - 2 : ℝ) / 4 = (1:ℝ)/2 := by norm_num
    rwa [hb] at hfin
  -- the interval integrability needed by `rpow_asymptotic_of_deriv_sq_div_asymptotic`
  have hfint : ∀ a u : ℝ, 0 < a → a ≤ u → u < ε₂ →
      IntervalIntegrable (deriv (fun s : ℝ => clusterInertia m k (x s))) MeasureTheory.volume a u := by
    intro a u ha hau hu
    refine ContinuousOn.intervalIntegrable fun s hs => ?_
    rw [uIcc_of_le hau] at hs
    exact ((hf2 s ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hu⟩).differentiableAt).continuousAt.continuousWithinAt
  -- (1) `I_k / t^{4/3} → κ`
  have hconj1 : Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (K ^ ((4:ℝ)/3))) := by
    have hfinal := Commons.Analysis.Calculus.rpow_asymptotic_of_deriv_sq_div_asymptotic
      (f := fun s : ℝ => clusterInertia m k (x s)) (b := 4) (η := η) (ε := ε₂)
      hε₂pos (by norm_num) hηpos hf1 hfint hfpos hmono hI hη
    rw [show (4:ℝ) / (4 - 1) = (4:ℝ)/3 by norm_num,
        show (4 - 1) / 4 = (3:ℝ)/4 by norm_num] at hfinal
    rwa [← hKdef] at hfinal
  -- (2) `İ_k / t^{1/3} → (4/3) κ`
  have hconj2 : Tendsto
      (fun t : ℝ => deriv (fun s : ℝ => clusterInertia m k (x s)) t / t ^ ((1:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3 * K ^ ((4:ℝ)/3))) := by
    have hfinal := Commons.Analysis.Calculus.deriv_tendsto_of_deriv_sq_div_asymptotic
      (f := fun s : ℝ => clusterInertia m k (x s)) (b := 4) (η := η) (ε := ε₂)
      hε₂pos (by norm_num) hηpos hf1 hfpos hmono hI hη
    rw [show (1:ℝ) / (4 - 1) = (1:ℝ)/3 by norm_num,
        show ((4:ℝ) - 1) / 4 = (3:ℝ)/4 by norm_num] at hfinal
    have htgt : Real.sqrt η * ((3:ℝ)/4 * Real.sqrt η) ^ ((1:ℝ)/3)
        = (4:ℝ)/3 * K ^ ((4:ℝ)/3) := by
      rw [← hKdef, hsqrtη, mul_assoc, hKmul]
    rwa [htgt] at hfinal
  -- (3) `Ï_k t^{2/3} → (4/9) κ`
  have hconj3 : Tendsto (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
      * t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * K ^ ((4:ℝ)/3))) := by
    have hB : Tendsto (fun t : ℝ => t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t)))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((K ^ ((4:ℝ)/3)) ^ (-(1:ℝ)/2))) := by
      have hpow : Tendsto (fun t : ℝ => (clusterInertia m k (x t) / t ^ ((4:ℝ)/3)) ^ (-(1:ℝ)/2))
          (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((K ^ ((4:ℝ)/3)) ^ (-(1:ℝ)/2))) :=
        hconj1.rpow_const (Or.inl (ne_of_gt (Real.rpow_pos_of_pos hKpos ((4:ℝ)/3))))
      refine Filter.Tendsto.congr' ?_ hpow
      filter_upwards [Ioo_mem_nhdsGT hε₂pos] with t ht
      have ht0 : 0 < t := ht.1
      have hft : 0 < clusterInertia m k (x t) := hfpos t ht
      rw [Real.div_rpow (le_of_lt hft) (Real.rpow_nonneg (le_of_lt ht0) _)]
      rw [Real.rpow_div_two_eq_sqrt (-1) (le_of_lt hft),
          Real.rpow_div_two_eq_sqrt (-1) (Real.rpow_nonneg (le_of_lt ht0) _)]
      rw [Real.rpow_neg_one, Real.rpow_neg_one, div_inv_eq_mul]
      rw [Real.sqrt_eq_rpow (clusterInertia m k (x t)),
          Real.sqrt_eq_rpow (t ^ ((4:ℝ)/3)), ← Real.rpow_mul (le_of_lt ht0), inv_mul_eq_div]
      rw [show ((4:ℝ)/3) * (1/(2:ℝ)) = (2:ℝ)/3 by norm_num]
    have hprod := hfin2.mul hB
    have hlim3 : (η / 4) * (K ^ ((4:ℝ)/3)) ^ (-(1:ℝ)/2) = (4:ℝ)/9 * K ^ ((4:ℝ)/3) := by
      have h1 : (K ^ ((4:ℝ)/3)) ^ (-(1:ℝ)/2) = K ^ (-(2:ℝ)/3) := by
        rw [← Real.rpow_mul hKpos.le,
          show ((4:ℝ)/3) * (-(1:ℝ)/2) = -(2:ℝ)/3 by norm_num]
      rw [h1, hηK4, mul_assoc,
        show K ^ (2:ℕ) = K ^ ((2:ℝ)) from (Real.rpow_natCast K 2).symm, ← Real.rpow_add hKpos]
      norm_num
    rw [hlim3] at hprod
    refine Filter.Tendsto.congr' ?_ hprod
    filter_upwards [Ioo_mem_nhdsGT hε₂pos] with t ht
    have hft : 0 < clusterInertia m k (x t) := hfpos t ht
    rw [← Real.sqrt_eq_rpow]
    have hne : Real.sqrt (clusterInertia m k (x t)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hft)
    field_simp
  refine ⟨K ^ ((4:ℝ)/3), Real.rpow_pos_of_pos hKpos _, hconj1, hconj2, hconj3, ?_⟩
  have hlim4 : η / 4 = (4:ℝ)/9 * (K ^ ((4:ℝ)/3)) ^ ((3:ℝ)/2) := by rw [hK2, hηK4]
  rwa [hlim4] at hfin2

end Submission.NBody
