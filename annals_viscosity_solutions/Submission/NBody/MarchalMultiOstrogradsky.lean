import Submission.NBody.MarchalMultiInertia
import Submission.NBody.MarchalRelEnergy
import Submission.NBody.MarchalSundmanGeneral

/-!
# The Ostrogradsky and Sundman estimates for a sum of clusters

For the sum `f = ∑_{k∈ks} I_k` of the moments of inertia of a family of clusters one has, exactly as
for a single cluster,

* the Ostrogradsky (Cauchy–Schwarz) inequality `f'² ≤ 4 f f'' + 16 C f` — from the bounds
  `|∑_k E^{rel}_k| ≤ C` and `|∑_k W_k| ≤ C` (the sum of the energies and of the interaction works);
* the lower bound `d/√f ≤ f'' + 6 C` — from the same bounds and Sperner's estimate
  `∑_k c_k/√(I_k) ≤ ∑_k U_k`;
* and therefore Sundman's asymptotic law `f(t) / t^{4/3} → κ > 0`.

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

/-- **Sperner's a priori bound for a sum of clusters.**  If every cluster of the family `ks` has at
least two bodies, there is `c > 0` with `c/√(∑_{k∈ks} I_k) ≤ ∑_{k∈ks} U_k` at every collision-free
configuration. -/
theorem exists_const_le_multiPotential {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    (ks : Finset (Finset (Fin N))) (hne2 : ∀ k ∈ ks, 2 ≤ k.card) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : EN E N, WithoutCollisions x →
      c / Real.sqrt (multiInertia m ks x) ≤ multiPotential m ks x := by
  classical
  rcases Finset.eq_empty_or_nonempty ks with hem | ⟨k0, hk0⟩
  · refine ⟨1, one_pos, fun x _ => ?_⟩
    simp [hem, multiInertia, multiPotential]
  let c : Finset (Fin N) → ℝ := fun k =>
    if hk : k ∈ ks then Classical.choose (exists_const_le_clusterPotential (E := E) hm k (hne2 k hk))
    else 1
  have hcpos : ∀ k ∈ ks, 0 < c k := by
    intro k hk
    simp only [c, dif_pos hk]
    exact (Classical.choose_spec
      (exists_const_le_clusterPotential (E := E) hm k (hne2 k hk))).1
  have hc : ∀ k ∈ ks, ∀ x : EN E N, WithoutCollisions x →
      c k / Real.sqrt (clusterInertia m k x) ≤ clusterPotential m k x := by
    intro k hk x hx
    simp only [c, dif_pos hk]
    exact (Classical.choose_spec
      (exists_const_le_clusterPotential (E := E) hm k (hne2 k hk))).2 x hx
  have hCpos : 0 < ∑ k ∈ ks, c k :=
    Finset.sum_pos (fun k hk => hcpos k hk) ⟨k0, hk0⟩
  refine ⟨∑ k ∈ ks, c k, hCpos, fun x hnc => ?_⟩
  have hIk : ∀ k ∈ ks, 0 < clusterInertia m k x :=
    fun k hk => clusterInertia_pos hm (hne2 k hk) hnc
  have hf : 0 < multiInertia m ks x :=
    Finset.sum_pos (fun k hk => hIk k hk) ⟨k0, hk0⟩
  have hle : ∀ k ∈ ks, clusterInertia m k x ≤ multiInertia m ks x := by
    intro k hk
    exact Finset.single_le_sum (f := fun k => clusterInertia m k x)
      (fun k _ => clusterInertia_nonneg (fun i => (hm i).le) k x) hk
  have hstep : ∀ k ∈ ks, c k / Real.sqrt (multiInertia m ks x)
      ≤ c k / Real.sqrt (clusterInertia m k x) := by
    intro k hk
    exact div_le_div_of_nonneg_left (hcpos k hk).le (Real.sqrt_pos.mpr (hIk k hk))
      (Real.sqrt_le_sqrt (hle k hk))
  calc (∑ k ∈ ks, c k) / Real.sqrt (multiInertia m ks x)
      = ∑ k ∈ ks, c k / Real.sqrt (multiInertia m ks x) := by rw [Finset.sum_div]
    _ ≤ ∑ k ∈ ks, c k / Real.sqrt (clusterInertia m k x) := Finset.sum_le_sum hstep
    _ ≤ ∑ k ∈ ks, clusterPotential m k x := Finset.sum_le_sum fun k hk => hc k hk x hnc
    _ = multiPotential m ks x := rfl

/-- **Ostrogradsky's inequality for a sum of clusters.** -/
theorem multiInertia_deriv_sq_le {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {ε t C : ℝ} (hm : ∀ i, 0 < m i) (hne : ∀ k ∈ ks, k.Nonempty)
    (htm : t ∈ Ioo (0:ℝ) ε)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd2 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x s) s)
    (hode : ∀ s ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x s = ∇_[m] (U m) (x s))
    (hE : |multiRelEnergy m ks (x t) (deriv x t)| ≤ C)
    (hW : |multiCrossWork m ks (x t)| ≤ C) :
    (deriv (fun s : ℝ => multiInertia m ks (x s)) t) ^ (2:ℕ)
      ≤ 4 * multiInertia m ks (x t)
          * deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
        + 16 * C * multiInertia m ks (x t) := by
  classical
  have hxev : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
    filter_upwards [isOpen_Ioo.mem_nhds htm] with s hs
    exact hx s hs
  set A : ℝ := ∑ k ∈ ks, massInner m (cmRel m k (x t)) (cmRel m k (deriv x t)) with hA
  set R : ℝ := ∑ k ∈ ks, clusterRelKinetic m k (deriv x t) with hR
  set Q : ℝ := multiRelEnergy m ks (x t) (deriv x t) with hQ
  set P : ℝ := multiPotential m ks (x t) with hP
  set W : ℝ := multiCrossWork m ks (x t) with hW'
  -- the first derivative
  have hsum := hasDerivAt_sum_apply ks (fun k (s : ℝ) => clusterInertia m k (x s))
    (fun k => deriv (fun s : ℝ => clusterInertia m k (x s)) t) t
    (fun k _ => hasDerivAt_clusterInertia_curve (k := k) hxev)
  have hderiv : deriv (fun s : ℝ => multiInertia m ks (x s)) t = 2 * A := by
    have h1 : deriv (fun s : ℝ => multiInertia m ks (x s)) t
        = ∑ k ∈ ks, deriv (fun s : ℝ => clusterInertia m k (x s)) t := by
      rw [show (fun s : ℝ => multiInertia m ks (x s))
          = (fun s : ℝ => ∑ k ∈ ks, clusterInertia m k (x s)) from rfl]
      exact hsum.deriv
    rw [h1, hA, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k hk =>
      deriv_clusterInertia_curve (m := m) (k := k) (x := x) (t := t) hxev
  -- the Lagrange-Jacobi identity
  have hLJ' : deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t = 4 * Q + 2 * P + 2 * W := by
    rw [hQ, hP, hW']
    exact deriv_deriv_multiInertia_curve_eq (m := m) (ks := ks) (x := x) (ε := ε) (t := t)
      hm hne htm hnc hx hd2 hode
  -- Ostrogradsky in the summed form
  have hCS : A ^ 2 ≤ (∑ k ∈ ks, clusterInertia m k (x t)) * R := by
    rw [hA, hR]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul ks
      (fun k _ => clusterInertia_nonneg (fun i => (hm i).le) k (x t))
      (fun k _ => clusterKineticSq_nonneg (fun i => (hm i).le) k (cmRel m k (deriv x t)))
      (fun k _ => ?_)
    exact ostrogradsky (fun i => (hm i).le) k (x t) (deriv x t)
  have hKrel : ∀ k ∈ ks, clusterRelKinetic m k (deriv x t)
      = 2 * clusterRelEnergy m k (x t) (deriv x t) + 2 * clusterPotential m k (x t) := by
    intro k hk
    unfold clusterRelEnergy clusterRelKinetic
    ring
  have hRK : R = 2 * Q + 2 * P := by
    rw [hR, hQ, hP, multiRelEnergy, multiPotential]
    rw [Finset.sum_congr rfl hKrel, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hff : 0 ≤ multiInertia m ks (x t) := multiInertia_nonneg (fun i => (hm i).le) ks (x t)
  have hfI : multiInertia m ks (x t) = ∑ k ∈ ks, clusterInertia m k (x t) := rfl
  have hQlo : -C ≤ Q := (abs_le.mp hE).1
  have hWlo : -C ≤ W := (abs_le.mp hW).1
  have h1 : (deriv (fun s : ℝ => multiInertia m ks (x s)) t) ^ (2:ℕ)
      ≤ 4 * multiInertia m ks (x t) * R := by
    rw [hderiv, hfI]
    nlinarith [hCS]
  have h2 : 4 * multiInertia m ks (x t) * R
      ≤ 4 * multiInertia m ks (x t) * deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
        + 16 * C * multiInertia m ks (x t) := by
    rw [hRK, hLJ']
    nlinarith [hQlo, hWlo, hff]
  exact le_trans h1 h2

/-- **The lower bound on the second derivative of a sum of clusters.** -/
theorem multiInertia_second_deriv_ge {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {ε t C ck : ℝ} (hm : ∀ i, 0 < m i) (hne : ∀ k ∈ ks, k.Nonempty)
    (htm : t ∈ Ioo (0:ℝ) ε)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd2 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x s) s)
    (hode : ∀ s ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x s = ∇_[m] (U m) (x s))
    (hE : -C ≤ multiRelEnergy m ks (x t) (deriv x t))
    (hW : -C ≤ multiCrossWork m ks (x t))
    (hU : ck / Real.sqrt (multiInertia m ks (x t)) ≤ multiPotential m ks (x t)) :
    ck / Real.sqrt (multiInertia m ks (x t))
      ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t + 6 * C := by
  have hLJ' := deriv_deriv_multiInertia_curve_eq (m := m) (ks := ks) (x := x) (ε := ε) (t := t)
    hm hne htm hnc hx hd2 hode
  have key : 2 * (multiPotential m ks (x t))
      ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t + 6 * C := by
    rw [hLJ']
    linarith
  linarith [hU, key, multiPotential_nonneg (fun i => (hm i).le) ks (x t)]

/-- **Sundman's asymptotic law for a simultaneous collision of several clusters.** -/
theorem multiInertia_asymptotic {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {ε C : ℝ} (hm : ∀ i, 0 < m i) (hne : ∀ k ∈ ks, k.Nonempty)
    (hne2 : ∀ k ∈ ks, 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |multiRelEnergy m ks (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |multiCrossWork m ks (x t)| ≤ C)
    (hfpos : ∀ t ∈ Ioo (0:ℝ) ε, 0 < multiInertia m ks (x t))
    (hI : Tendsto (fun t : ℝ => multiInertia m ks (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun t : ℝ => multiInertia m ks (x t) / t ^ ((4:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ) := by
  classical
  obtain ⟨c, hcpos, hcksp⟩ := exists_const_le_multiPotential (E := E) hm ks hne2
  -- eventual differentiability
  have hxev : ∀ t ∈ Ioo (0:ℝ) ε, ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hx s hs
  have hd2' : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) t) t :=
    fun t ht => (hd2 t ht).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x t)
  -- shrink the interval so that `√f ≤ c/(12 C)`
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt (multiInertia m ks (x t)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have h1 := Real.continuous_sqrt.continuousAt.tendsto.comp hI
    simpa only [Function.comp_def, Real.sqrt_zero] using h1
  have hthr : (0:ℝ) < c / (12 * C) := by positivity
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      Real.sqrt (multiInertia m ks (x t)) < c / (12 * C) :=
    hsqrt.eventually (isOpen_Iio.mem_nhds hthr)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hev
  obtain ⟨ε₁, hε₁pos, hε₁le, hε₁⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε ∧
      ∀ t ∈ Ioo (0:ℝ) ε₁, Real.sqrt (multiInertia m ks (x t)) < c / (12 * C) := by
    refine ⟨min δ ε, lt_min hδpos hε, min_le_right _ _, fun t ht => hδ t ?_ ht.1⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact lt_of_lt_of_le ht.2 (min_le_left _ _)
  have hmem : ∀ t ∈ Ioo (0:ℝ) ε₁, t ∈ Ioo (0:ℝ) ε := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hε₁le⟩
  have hfpos₁ : ∀ t ∈ Ioo (0:ℝ) ε₁, 0 < multiInertia m ks (x t) := fun t ht => hfpos t (hmem t ht)
  have hf1 : ∀ t ∈ Ioo (0:ℝ) ε₁,
      HasDerivAt (fun s : ℝ => multiInertia m ks (x s))
        (deriv (fun s : ℝ => multiInertia m ks (x s)) t) t :=
    fun t ht => hasDerivAt_multiInertia_curve (hxev t (hmem t ht))
  have hf2 : ∀ t ∈ Ioo (0:ℝ) ε₁,
      HasDerivAt (deriv (fun s : ℝ => multiInertia m ks (x s)))
        (deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t) t :=
    fun t ht => hasDerivAt_deriv_multiInertia_curve (htm := ht)
      (fun s hs => hx s (hmem s hs)) (fun s hs => hd2' s (hmem s hs))
  -- the two estimates
  have hineq : ∀ t ∈ Ioo (0:ℝ) ε₁,
      (deriv (fun s : ℝ => multiInertia m ks (x s)) t) ^ (2:ℕ)
        ≤ 4 * multiInertia m ks (x t)
            * deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
          + 16 * C * multiInertia m ks (x t) :=
    fun t ht => multiInertia_deriv_sq_le (m := m) (ks := ks) (x := x) (ε := ε₁) (t := t)
      (C := C) hm hne ht (fun s hs => hnc s (hmem s hs)) (fun s hs => hx s (hmem s hs))
      (fun s hs => hd2 s (hmem s hs)) (fun s hs => hode s (hmem s hs))
      (hE t (hmem t ht)) (hW t (hmem t ht))
  have hbound : ∀ t ∈ Ioo (0:ℝ) ε₁,
      c / 2 ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
        * (multiInertia m ks (x t)) ^ ((1:ℝ)/2) := by
    intro t ht
    have htε := hmem t ht
    have h := multiInertia_second_deriv_ge (m := m) (ks := ks) (x := x) (ε := ε) (t := t)
      (C := C) (ck := c) hm hne htε (fun s hs => hnc s hs) (fun s hs => hx s hs)
      (fun s hs => hd2 s hs) (fun s hs => hode s hs)
      (le_trans (neg_le_neg (hE t htε)) (neg_abs_le _))
      (le_trans (neg_le_neg (hW t htε)) (neg_abs_le _))
      (hcksp (x t) (hnc t htε))
    have hrootpos : 0 < Real.sqrt (multiInertia m ks (x t)) := Real.sqrt_pos.mpr (hfpos₁ t ht)
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hrootpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hrootpos), add_mul] at hmul
    have h6 : 6 * C * Real.sqrt (multiInertia m ks (x t)) ≤ c / 2 := by
      have h1 : 6 * C * Real.sqrt (multiInertia m ks (x t)) < 6 * C * (c / (12 * C)) :=
        mul_lt_mul_of_pos_left (hε₁ t ht) (by positivity)
      have h2 : 6 * C * (c / (12 * C)) = c / 2 := by field_simp; ring
      linarith
    rw [← Real.sqrt_eq_rpow]
    linarith
  refine rpow_asymptotic_of_hineq_hbound (f := fun s : ℝ => multiInertia m ks (x s))
    (C := C) (d := c) hε₁pos hC hcpos hf1 hf2 hfpos₁ hineq hbound ?_
  exact hI

end Submission.NBody