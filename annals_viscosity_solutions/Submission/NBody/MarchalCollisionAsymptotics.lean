import Submission.NBody.MarchalClusterAsymptotic2
import Submission.NBody.MarchalClusterAsymptotic3
import Submission.NBody.MarchalRelEnergy
import Submission.NBody.MarchalClassAsymptotic
import Submission.NBody.MarchalSelfScaledVelocity
import Submission.NBody.MarchalSolutionThirdDeriv
import Submission.NBody.MarchalCollisionSolutionData

/-!
# The full Sundman asymptotics at a collision of a minimiser

This module feeds the whole Sundman chain (`clusterInertia_asymptotics_of_isolated`) at an isolated
collision time `t₀` of an `h`-minimiser, for a collision class `k`.  Concretely, all the analytic
inputs of the chain are produced from the geometry on the collision-free side `(t₀, t₀ + ε)`:

* `hx`, `hd2`, `hode` — the Newton data (`exists_solution_data_of_minimizer`);
* `hd3` — the third-order data (`hasDerivAt_deriv_deriv_of_solution`);
* `hE` — the bound on the centre-of-mass-relative energy (`exists_relEnergy_bound_of_kinetic`,
  Ferrario--Terracini `lemma:bounded_energy`, from the sum-level kinetic bound);
* `hW` — the *positional* interaction-work bound (`abs_crossWork_cmRel_le`, one-sided separation);
* `hv` — the outside velocities controlled by the cluster's potential scale
  (`exists_scaled_outside_velocity_bound_of_collision`);
* `hI` — `I_k → 0` at the collision time (continuity).

The conclusion is the five asymptotics of Ferrario--Terracini `propo:asy`: `I_k ∼ κ t^{4/3}`,
`İ_k ∼ (4/3) κ t^{1/3}`, `Ï_k ∼ (4/9) κ t^{-2/3}`, `U_k ∼ (2/9) κ t^{-2/3}` and
`K^{rel}_k ∼ (4/9) κ t^{-2/3}`.

Everything in this file is fully proved.
-/

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

/-- **The five Sundman asymptotics at a collision of a minimiser.** -/
theorem clusterInertia_asymptotics_at_collision {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b t₀ : ℝ} {k : Finset (Fin N)}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b) (hk2 : 2 ≤ k.card)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) {ε ν : ℝ} (hε : 0 < ε) (hεb : t₀ + ε ≤ b)
    (hnc : ∀ t ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ t))
    (hν : 0 < ν) (hsepw : ∀ t ∈ Ioo t₀ (t₀ + ε), ClusterSeparatedWeak k (γ t) ν)
    (hI0 : clusterInertia m k (γ t₀) = 0) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun t : ℝ => clusterInertia m k (γ (t₀ + t)) / t ^ ((4:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ) ∧
      Tendsto (fun t : ℝ => deriv (fun s : ℝ => clusterInertia m k (γ (t₀ + s))) t
        / t ^ ((1:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3 * κ)) ∧
      Tendsto (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (γ (t₀ + s)))) t
        * t ^ ((2:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ)) ∧
      Tendsto (fun t : ℝ => clusterPotential m k (γ (t₀ + t)) * t ^ ((2:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ)) ∧
      Tendsto (fun t : ℝ => clusterRelKinetic m k (deriv (fun s : ℝ => γ (t₀ + s)) t)
        * t ^ ((2:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ)) := by
  classical
  have hkne : k.Nonempty := Finset.card_pos.mp (by omega)
  have hmne : ∀ i, m i ≠ 0 := fun i => ne_of_gt (hm i)
  -- the collision
  have hcoll : ¬ WithoutCollisions (γ t₀) := by
    intro hnc'
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < k.card)
    have h1 : γ t₀ i = γ t₀ j := (clusterInertia_eq_zero_iff hm k (γ t₀)).mp hI0 i hi j hj
    exact (hnc' i j hij) (by rw [r_eq_norm_sub, h1, sub_self, norm_zero])
  -- the shifted curve and the working interval
  set D : ℝ := min ε 1 with hDdef
  have hDpos : 0 < D := lt_min hε one_pos
  have hDle : D ≤ ε := min_le_left _ _
  have hDb : t₀ + D ≤ b := by linarith
  let x : ℝ → EN E N := fun s => γ (t₀ + s)
  have hncD' : ∀ t ∈ Ioo t₀ (t₀ + D), WithoutCollisions (γ t) := fun t ht =>
    hnc t ⟨ht.1, by linarith [ht.2, hDle]⟩
  have hncD : ∀ u ∈ Ioo (0:ℝ) D, WithoutCollisions (x u) := fun u hu =>
    hncD' (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hsepwD : ∀ u ∈ Ioo (0:ℝ) D, ClusterSeparatedWeak k (x u) ν := fun u hu =>
    hsepw (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2, hDle]⟩
  -- the Newton data
  have hsol := exists_solution_data_of_minimizer (m := m) (h := h) hm hh hab hac hmin hfin
    (S := Ioo t₀ (t₀ + D))
    (fun t ht => ⟨lt_trans ht₀.1 ht.1, by linarith [ht.2, hDb]⟩)
    (fun t ht => hncD' t ht)
  have hnewton : ∀ u ∈ Ioo (0:ℝ) D,
      HasDerivAt γ (deriv γ (t₀ + u)) (t₀ + u) ∧
      HasDerivAt (deriv γ) (iteratedDeriv 2 γ (t₀ + u)) (t₀ + u) ∧
      iteratedDeriv 2 γ (t₀ + u) = ∇_[m] (U m) (γ (t₀ + u)) := fun u hu => by
    have h := hsol (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    exact ⟨h.1.self_of_nhds, h.2.1, h.2.2⟩
  have hx : ∀ u ∈ Ioo (0:ℝ) D, HasDerivAt x (deriv x u) u := fun u hu => by
    have h1 : HasDerivAt (fun s : ℝ => γ (t₀ + s)) (deriv γ (t₀ + u)) u :=
      (hnewton u hu).1.comp_const_add t₀ u
    have h2 : deriv x u = deriv γ (t₀ + u) := deriv_shiftCurve_eq t₀ u
    rw [h2]
    exact h1
  have hd2 : ∀ u ∈ Ioo (0:ℝ) D, HasDerivAt (deriv x) (iteratedDeriv 2 x u) u := fun u hu => by
    have h1 : HasDerivAt (fun s : ℝ => deriv γ (t₀ + s)) (iteratedDeriv 2 γ (t₀ + u)) u :=
      (hnewton u hu).2.1.comp_const_add t₀ u
    have h2 : deriv x = fun s : ℝ => deriv γ (t₀ + s) := by
      funext s; exact deriv_shiftCurve_eq t₀ s
    rw [h2]
    have h3 : iteratedDeriv 2 x u = iteratedDeriv 2 γ (t₀ + u) :=
      iteratedDeriv_two_shiftCurve_eq t₀ u
    rw [h3]
    exact h1
  have hode : ∀ u ∈ Ioo (0:ℝ) D, iteratedDeriv 2 x u = ∇_[m] (U m) (x u) := fun u hu => by
    have h3 : iteratedDeriv 2 x u = iteratedDeriv 2 γ (t₀ + u) :=
      iteratedDeriv_two_shiftCurve_eq t₀ u
    rw [h3]
    exact (hnewton u hu).2.2
  have hd3 : ∀ u ∈ Ioo (0:ℝ) D, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) u) u :=
    fun u hu => hasDerivAt_deriv_deriv_of_solution (m := m) (x := x) (ε := D) (t := u) hmne hu
      hx hd2 hncD hode
  -- the kinetic bound and the energy bound
  obtain ⟨Ck, hCkpos, hkin⟩ := exists_kinetic_bound_at_collision (m := m) (h := h) (γ := γ)
    (a := a) (b := b) (t₀ := t₀) (ε := D) hm hh hab hac hmin hfin ht₀ hcoll hDpos hDb hncD'
  have hkin' : ∀ᶠ u in 𝓝[>] (0:ℝ), kinetic m (deriv x u) ≤ Ck * u ^ (-((2:ℝ)/3)) := by
    filter_upwards [hkin] with u hu
    show kinetic m (deriv (fun s : ℝ => γ (t₀ + s)) u) ≤ Ck * u ^ (-((2:ℝ)/3))
    rw [deriv_shiftCurve_eq t₀ u] at hu ⊢
    exact hu
  have hd2' : ∀ u ∈ Ioo (0:ℝ) D, HasDerivAt (deriv x) (deriv (deriv x) u) u := fun u hu =>
    (hd2 u hu).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x u)
  have hode' : ∀ u ∈ Ioo (0:ℝ) D, deriv (deriv x) u = ∇_[m] (U m) (x u) := fun u hu =>
    (iteratedDeriv_two_eq_deriv_deriv x u).symm.trans (hode u hu)
  obtain ⟨Ce, hCepos, δe, hδepos, hδele, henergy⟩ :=
    exists_relEnergy_bound_of_kinetic (m := m) (k := k) (x := x) (ε := D) (ν := ν) (Ck := Ck)
      hm hkne hDpos hν hCkpos hncD hx hd2' hode' hsepwD hkin'
  -- the interaction-work bound
  set Cw : ℝ := 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) with hCwdef
  have hCw0 : 0 ≤ Cw := by
    rw [hCwdef]
    have h1 : 0 ≤ (ν⁻¹) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
    have h3 : 0 ≤ Real.sqrt (clusterMass m k) := Real.sqrt_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3
  -- the inertia tends to `0`
  have hItend : Tendsto (fun u : ℝ => clusterInertia m k (x u)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have hcont : Tendsto (fun u : ℝ => γ (t₀ + u)) (𝓝 (0:ℝ)) (𝓝 (γ t₀)) := by
      have h1 : Tendsto (fun u : ℝ => t₀ + u) (𝓝 (0:ℝ)) (𝓝 t₀) := by
        have h2 : Tendsto (fun _ : ℝ => t₀) (𝓝 (0:ℝ)) (𝓝 t₀) := tendsto_const_nhds
        have h3 : Tendsto (fun u : ℝ => u) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := tendsto_id
        simpa using h2.add h3
      have h4 : ContinuousAt γ t₀ := by
        have h5 : ContinuousOn γ (Icc a b) := by
          have h := hac.continuousOn
          rwa [uIcc_of_le hab.le] at h
        exact h5.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
      exact h4.tendsto.comp h1
    have h6 : Tendsto (fun u : ℝ => clusterInertia m k (γ (t₀ + u))) (nhdsWithin (0:ℝ) (Ioi 0))
        (nhds (clusterInertia m k (γ t₀))) :=
      ((continuous_clusterInertia m k).continuousAt.tendsto.comp hcont).mono_left nhdsWithin_le_nhds
    simpa [hI0] using h6
  -- the interval on which the inertia is at most `1`
  obtain ⟨δI, hδIpos, hδI⟩ : ∃ δI : ℝ, 0 < δI ∧ ∀ u ∈ Ioo (0:ℝ) δI, clusterInertia m k (x u) ≤ 1 := by
    have hev := hItend.eventually (isOpen_Iio.mem_nhds one_pos)
    rw [eventually_nhdsWithin_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hev
    refine ⟨δ, hδpos, fun u hu => le_of_lt (hδ u ?_ hu.1)⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu.1]
    exact hu.2
  -- the common interval
  set δ : ℝ := min (min δe δI) D with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδepos hδIpos) hDpos
  have hδleD : δ ≤ D := min_le_right _ _
  have hδleδe : δ ≤ δe := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδleI : δ ≤ δI := le_trans (min_le_left _ _) (min_le_right _ _)
  have hmem : ∀ u ∈ Ioo (0:ℝ) δ, u ∈ Ioo (0:ℝ) D :=
    fun u hu => ⟨hu.1, lt_of_lt_of_le hu.2 hδleD⟩
  have hE : ∀ u ∈ Ioo (0:ℝ) δ, |clusterRelEnergy m k (x u) (deriv x u)| ≤ max Ce Cw + 1 :=
    fun u hu => le_trans (henergy u ⟨hu.1, lt_of_lt_of_le hu.2 hδleδe⟩)
      (by linarith [le_max_left Ce Cw])
  have hW : ∀ u ∈ Ioo (0:ℝ) δ, |crossWork m k (x u) (cmRel m k (x u))| ≤ max Ce Cw + 1 := by
    intro u hu
    have h1 := abs_crossWork_cmRel_le (m := m) (k := k) (x := x u) (v := x u) (ν := ν)
      hm hν (hsepwD u (hmem u hu))
    have h2 : clusterRelKinetic m k (x u) = clusterInertia m k (x u) :=
      clusterRelKinetic_eq_clusterInertia m k (x u)
    rw [h2] at h1
    have hs : Real.sqrt (clusterInertia m k (x u)) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (hδI u ⟨hu.1, lt_of_lt_of_le hu.2 hδleI⟩)
    have hnn : 0 ≤ (2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j)) * Real.sqrt (clusterMass m k) := by
      have h := hCw0; rw [hCwdef] at h; exact h
    have hle : (2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j)) * Real.sqrt (clusterMass m k)
        * Real.sqrt (clusterInertia m k (x u)) ≤ Cw := by
      calc (2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j)) * Real.sqrt (clusterMass m k)
            * Real.sqrt (clusterInertia m k (x u))
          ≤ (2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j)) * Real.sqrt (clusterMass m k) * 1 :=
            mul_le_mul_of_nonneg_left hs hnn
        _ = Cw := by rw [mul_one]
    exact le_trans h1 (le_trans hle (by linarith [le_max_right Ce Cw]))
  -- the scaled outside-velocity bound
  obtain ⟨Cv, hCv0, hv⟩ := exists_scaled_outside_velocity_bound_of_collision (m := m) (h := h)
    (γ := γ) (a := a) (b := b) (t₀ := t₀) (ε := ε) (ν := ν) (k := k)
    hm hh hab hk2 hac hmin hfin ht₀ hε hεb hnc hν hsepw hI0
  obtain ⟨δv, hδvpos, hvδ⟩ : ∃ δv : ℝ, 0 < δv ∧ ∀ u ∈ Ioo (0:ℝ) δv, ∀ j ∉ k,
      ‖deriv γ (t₀ + u) j‖ ≤ Cv * Real.sqrt (clusterPotential m k (γ (t₀ + u))) :=
    exists_forall_Ioo_of_eventually_nhdsGT hv
  -- shrink the interval once more to accommodate the velocity bound
  set δ' : ℝ := min δ δv with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδpos hδvpos
  have hδ'leδ : δ' ≤ δ := min_le_left _ _
  have hδ'leδv : δ' ≤ δv := min_le_right _ _
  have hmem' : ∀ u ∈ Ioo (0:ℝ) δ', u ∈ Ioo (0:ℝ) D :=
    fun u hu => hmem u ⟨hu.1, lt_of_lt_of_le hu.2 hδ'leδ⟩
  have hE' : ∀ u ∈ Ioo (0:ℝ) δ', |clusterRelEnergy m k (x u) (deriv x u)| ≤ max Ce Cw + 1 :=
    fun u hu => hE u ⟨hu.1, lt_of_lt_of_le hu.2 hδ'leδ⟩
  have hW' : ∀ u ∈ Ioo (0:ℝ) δ', |crossWork m k (x u) (cmRel m k (x u))| ≤ max Ce Cw + 1 :=
    fun u hu => hW u ⟨hu.1, lt_of_lt_of_le hu.2 hδ'leδ⟩
  have hv' : ∀ u ∈ Ioo (0:ℝ) δ', ∀ j ∉ k,
      ‖deriv x u j‖ ≤ Cv * Real.sqrt (clusterPotential m k (x u)) := by
    intro u hu j hj
    have h := hvδ u ⟨hu.1, lt_of_lt_of_le hu.2 hδ'leδv⟩ j hj
    dsimp only [x]
    rw [deriv_shiftCurve_eq t₀ u]
    exact h
  -- apply the chain
  obtain ⟨κ, hκpos, hIn, hDer, hSec, hU, hKin⟩ :=
    clusterPotential_asymptotic_of_isolated (m := m) (k := k) (x := x) (ε := δ')
      (C := max Ce Cw + 1) (ν := ν) (Cv := Cv) hm hk2 hδ'pos (by positivity) hν hCv0.le
      (fun u hu => hncD u (hmem' u hu)) hE' hW'
      (fun u hu => hx u (hmem' u hu)) (fun u hu => hd2 u (hmem' u hu))
      (fun u hu => hd3 u (hmem' u hu))
      (fun u hu => hode u (hmem' u hu)) (fun u hu => hsepwD u (hmem' u hu)) hv' hItend
  -- convert the statements to the `γ` form
  refine ⟨κ, hκpos, ?_, ?_, ?_, ?_, ?_⟩
  · refine Filter.Tendsto.congr' ?_ hIn
    filter_upwards [self_mem_nhdsWithin] with u hu
    dsimp only [x]
  · refine Filter.Tendsto.congr' ?_ hDer
    filter_upwards [self_mem_nhdsWithin] with u hu
    dsimp only [x]
  · refine Filter.Tendsto.congr' ?_ hSec
    filter_upwards [self_mem_nhdsWithin] with u hu
    dsimp only [x]
  · refine Filter.Tendsto.congr' ?_ hU
    filter_upwards [self_mem_nhdsWithin] with u hu
    dsimp only [x]
  · refine Filter.Tendsto.congr' ?_ hKin
    filter_upwards [self_mem_nhdsWithin] with u hu
    dsimp only [x]


/-- **Ferrario–Terracini `as:lim1` at a collision of a minimiser**: `t · ṡ → 0`, where `s` is the
normalised configuration of the collision class `k`.  This is the shape-control hypothesis `hts` of
the endgame. -/
theorem tendsto_mul_deriv_clusterShape_at_collision {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b t₀ : ℝ} {k : Finset (Fin N)}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b) (hk2 : 2 ≤ k.card)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) {ε ν : ℝ} (hε : 0 < ε) (hεb : t₀ + ε ≤ b)
    (hnc : ∀ t ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ t))
    (hν : 0 < ν) (hsepw : ∀ t ∈ Ioo t₀ (t₀ + ε), ClusterSeparatedWeak k (γ t) ν)
    (hI0 : clusterInertia m k (γ t₀) = 0) :
    Tendsto (fun t : ℝ => t • deriv (fun s : ℝ => clusterShape m k (γ (t₀ + s))) t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by

  classical
  have hkne : k.Nonempty := Finset.card_pos.mp (by omega)
  have hmne : ∀ i, m i ≠ 0 := fun i => ne_of_gt (hm i)
  -- the collision
  have hcoll : ¬ WithoutCollisions (γ t₀) := by
    intro hnc'
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < k.card)
    have h1 : γ t₀ i = γ t₀ j := (clusterInertia_eq_zero_iff hm k (γ t₀)).mp hI0 i hi j hj
    exact (hnc' i j hij) (by rw [r_eq_norm_sub, h1, sub_self, norm_zero])
  -- the shifted curve and the working interval
  set D : ℝ := min ε 1 with hDdef
  have hDpos : 0 < D := lt_min hε one_pos
  have hDle : D ≤ ε := min_le_left _ _
  have hDb : t₀ + D ≤ b := by linarith
  let x : ℝ → EN E N := fun s => γ (t₀ + s)
  have hncD' : ∀ t ∈ Ioo t₀ (t₀ + D), WithoutCollisions (γ t) := fun t ht =>
    hnc t ⟨ht.1, by linarith [ht.2, hDle]⟩
  have hncD : ∀ u ∈ Ioo (0:ℝ) D, WithoutCollisions (x u) := fun u hu =>
    hncD' (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hsepwD : ∀ u ∈ Ioo (0:ℝ) D, ClusterSeparatedWeak k (x u) ν := fun u hu =>
    hsepw (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2, hDle]⟩
  -- the Newton data
  have hsol := exists_solution_data_of_minimizer (m := m) (h := h) hm hh hab hac hmin hfin
    (S := Ioo t₀ (t₀ + D))
    (fun t ht => ⟨lt_trans ht₀.1 ht.1, by linarith [ht.2, hDb]⟩)
    (fun t ht => hncD' t ht)
  have hnewton : ∀ u ∈ Ioo (0:ℝ) D,
      HasDerivAt γ (deriv γ (t₀ + u)) (t₀ + u) ∧
      HasDerivAt (deriv γ) (iteratedDeriv 2 γ (t₀ + u)) (t₀ + u) ∧
      iteratedDeriv 2 γ (t₀ + u) = ∇_[m] (U m) (γ (t₀ + u)) := fun u hu => by
    have h := hsol (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    exact ⟨h.1.self_of_nhds, h.2.1, h.2.2⟩
  have hx : ∀ u ∈ Ioo (0:ℝ) D, HasDerivAt x (deriv x u) u := fun u hu => by
    have h1 : HasDerivAt (fun s : ℝ => γ (t₀ + s)) (deriv γ (t₀ + u)) u :=
      (hnewton u hu).1.comp_const_add t₀ u
    have h2 : deriv x u = deriv γ (t₀ + u) := deriv_shiftCurve_eq t₀ u
    rw [h2]
    exact h1
  have hd2 : ∀ u ∈ Ioo (0:ℝ) D, HasDerivAt (deriv x) (iteratedDeriv 2 x u) u := fun u hu => by
    have h1 : HasDerivAt (fun s : ℝ => deriv γ (t₀ + s)) (iteratedDeriv 2 γ (t₀ + u)) u :=
      (hnewton u hu).2.1.comp_const_add t₀ u
    have h2 : deriv x = fun s : ℝ => deriv γ (t₀ + s) := by
      funext s; exact deriv_shiftCurve_eq t₀ s
    rw [h2]
    have h3 : iteratedDeriv 2 x u = iteratedDeriv 2 γ (t₀ + u) :=
      iteratedDeriv_two_shiftCurve_eq t₀ u
    rw [h3]
    exact h1
  have hode : ∀ u ∈ Ioo (0:ℝ) D, iteratedDeriv 2 x u = ∇_[m] (U m) (x u) := fun u hu => by
    have h3 : iteratedDeriv 2 x u = iteratedDeriv 2 γ (t₀ + u) :=
      iteratedDeriv_two_shiftCurve_eq t₀ u
    rw [h3]
    exact (hnewton u hu).2.2
  have hd3 : ∀ u ∈ Ioo (0:ℝ) D, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) u) u :=
    fun u hu => hasDerivAt_deriv_deriv_of_solution (m := m) (x := x) (ε := D) (t := u) hmne hu
      hx hd2 hncD hode
  -- the kinetic bound and the energy bound
  obtain ⟨Ck, hCkpos, hkin⟩ := exists_kinetic_bound_at_collision (m := m) (h := h) (γ := γ)
    (a := a) (b := b) (t₀ := t₀) (ε := D) hm hh hab hac hmin hfin ht₀ hcoll hDpos hDb hncD'
  have hkin' : ∀ᶠ u in 𝓝[>] (0:ℝ), kinetic m (deriv x u) ≤ Ck * u ^ (-((2:ℝ)/3)) := by
    filter_upwards [hkin] with u hu
    show kinetic m (deriv (fun s : ℝ => γ (t₀ + s)) u) ≤ Ck * u ^ (-((2:ℝ)/3))
    rw [deriv_shiftCurve_eq t₀ u] at hu ⊢
    exact hu
  have hd2' : ∀ u ∈ Ioo (0:ℝ) D, HasDerivAt (deriv x) (deriv (deriv x) u) u := fun u hu =>
    (hd2 u hu).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x u)
  have hode' : ∀ u ∈ Ioo (0:ℝ) D, deriv (deriv x) u = ∇_[m] (U m) (x u) := fun u hu =>
    (iteratedDeriv_two_eq_deriv_deriv x u).symm.trans (hode u hu)
  obtain ⟨Ce, hCepos, δe, hδepos, hδele, henergy⟩ :=
    exists_relEnergy_bound_of_kinetic (m := m) (k := k) (x := x) (ε := D) (ν := ν) (Ck := Ck)
      hm hkne hDpos hν hCkpos hncD hx hd2' hode' hsepwD hkin'
  -- the interaction-work bound
  set Cw : ℝ := 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) with hCwdef
  have hCw0 : 0 ≤ Cw := by
    rw [hCwdef]
    have h1 : 0 ≤ (ν⁻¹) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
    have h3 : 0 ≤ Real.sqrt (clusterMass m k) := Real.sqrt_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3
  -- the inertia tends to `0`
  have hItend : Tendsto (fun u : ℝ => clusterInertia m k (x u)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have hcont : Tendsto (fun u : ℝ => γ (t₀ + u)) (𝓝 (0:ℝ)) (𝓝 (γ t₀)) := by
      have h1 : Tendsto (fun u : ℝ => t₀ + u) (𝓝 (0:ℝ)) (𝓝 t₀) := by
        have h2 : Tendsto (fun _ : ℝ => t₀) (𝓝 (0:ℝ)) (𝓝 t₀) := tendsto_const_nhds
        have h3 : Tendsto (fun u : ℝ => u) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := tendsto_id
        simpa using h2.add h3
      have h4 : ContinuousAt γ t₀ := by
        have h5 : ContinuousOn γ (Icc a b) := by
          have h := hac.continuousOn
          rwa [uIcc_of_le hab.le] at h
        exact h5.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
      exact h4.tendsto.comp h1
    have h6 : Tendsto (fun u : ℝ => clusterInertia m k (γ (t₀ + u))) (nhdsWithin (0:ℝ) (Ioi 0))
        (nhds (clusterInertia m k (γ t₀))) :=
      ((continuous_clusterInertia m k).continuousAt.tendsto.comp hcont).mono_left nhdsWithin_le_nhds
    simpa [hI0] using h6
  -- the interval on which the inertia is at most `1`
  obtain ⟨δI, hδIpos, hδI⟩ : ∃ δI : ℝ, 0 < δI ∧ ∀ u ∈ Ioo (0:ℝ) δI, clusterInertia m k (x u) ≤ 1 := by
    have hev := hItend.eventually (isOpen_Iio.mem_nhds one_pos)
    rw [eventually_nhdsWithin_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hev
    refine ⟨δ, hδpos, fun u hu => le_of_lt (hδ u ?_ hu.1)⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu.1]
    exact hu.2
  -- the common interval
  set δ : ℝ := min (min δe δI) D with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδepos hδIpos) hDpos
  have hδleD : δ ≤ D := min_le_right _ _
  have hδleδe : δ ≤ δe := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδleI : δ ≤ δI := le_trans (min_le_left _ _) (min_le_right _ _)
  have hmem : ∀ u ∈ Ioo (0:ℝ) δ, u ∈ Ioo (0:ℝ) D :=
    fun u hu => ⟨hu.1, lt_of_lt_of_le hu.2 hδleD⟩
  have hE : ∀ u ∈ Ioo (0:ℝ) δ, |clusterRelEnergy m k (x u) (deriv x u)| ≤ max Ce Cw + 1 :=
    fun u hu => le_trans (henergy u ⟨hu.1, lt_of_lt_of_le hu.2 hδleδe⟩)
      (by linarith [le_max_left Ce Cw])
  have hW : ∀ u ∈ Ioo (0:ℝ) δ, |crossWork m k (x u) (cmRel m k (x u))| ≤ max Ce Cw + 1 := by
    intro u hu
    have h1 := abs_crossWork_cmRel_le (m := m) (k := k) (x := x u) (v := x u) (ν := ν)
      hm hν (hsepwD u (hmem u hu))
    have h2 : clusterRelKinetic m k (x u) = clusterInertia m k (x u) :=
      clusterRelKinetic_eq_clusterInertia m k (x u)
    rw [h2] at h1
    have hs : Real.sqrt (clusterInertia m k (x u)) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (hδI u ⟨hu.1, lt_of_lt_of_le hu.2 hδleI⟩)
    have hnn : 0 ≤ (2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j)) * Real.sqrt (clusterMass m k) := by
      have h := hCw0; rw [hCwdef] at h; exact h
    have hle : (2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j)) * Real.sqrt (clusterMass m k)
        * Real.sqrt (clusterInertia m k (x u)) ≤ Cw := by
      calc (2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j)) * Real.sqrt (clusterMass m k)
            * Real.sqrt (clusterInertia m k (x u))
          ≤ (2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j)) * Real.sqrt (clusterMass m k) * 1 :=
            mul_le_mul_of_nonneg_left hs hnn
        _ = Cw := by rw [mul_one]
    exact le_trans h1 (le_trans hle (by linarith [le_max_right Ce Cw]))
  -- the scaled outside-velocity bound
  obtain ⟨Cv, hCv0, hv⟩ := exists_scaled_outside_velocity_bound_of_collision (m := m) (h := h)
    (γ := γ) (a := a) (b := b) (t₀ := t₀) (ε := ε) (ν := ν) (k := k)
    hm hh hab hk2 hac hmin hfin ht₀ hε hεb hnc hν hsepw hI0
  obtain ⟨δv, hδvpos, hvδ⟩ : ∃ δv : ℝ, 0 < δv ∧ ∀ u ∈ Ioo (0:ℝ) δv, ∀ j ∉ k,
      ‖deriv γ (t₀ + u) j‖ ≤ Cv * Real.sqrt (clusterPotential m k (γ (t₀ + u))) :=
    exists_forall_Ioo_of_eventually_nhdsGT hv
  -- shrink the interval once more to accommodate the velocity bound
  set δ' : ℝ := min δ δv with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδpos hδvpos
  have hδ'leδ : δ' ≤ δ := min_le_left _ _
  have hδ'leδv : δ' ≤ δv := min_le_right _ _
  have hmem' : ∀ u ∈ Ioo (0:ℝ) δ', u ∈ Ioo (0:ℝ) D :=
    fun u hu => hmem u ⟨hu.1, lt_of_lt_of_le hu.2 hδ'leδ⟩
  have hE' : ∀ u ∈ Ioo (0:ℝ) δ', |clusterRelEnergy m k (x u) (deriv x u)| ≤ max Ce Cw + 1 :=
    fun u hu => hE u ⟨hu.1, lt_of_lt_of_le hu.2 hδ'leδ⟩
  have hW' : ∀ u ∈ Ioo (0:ℝ) δ', |crossWork m k (x u) (cmRel m k (x u))| ≤ max Ce Cw + 1 :=
    fun u hu => hW u ⟨hu.1, lt_of_lt_of_le hu.2 hδ'leδ⟩
  have hv' : ∀ u ∈ Ioo (0:ℝ) δ', ∀ j ∉ k,
      ‖deriv x u j‖ ≤ Cv * Real.sqrt (clusterPotential m k (x u)) := by
    intro u hu j hj
    have h := hvδ u ⟨hu.1, lt_of_lt_of_le hu.2 hδ'leδv⟩ j hj
    dsimp only [x]
    rw [deriv_shiftCurve_eq t₀ u]
    exact h
  -- apply the shape limit
  have hshape := tendsto_mul_deriv_clusterShape (m := m) (k := k) (x := x) (ε := δ')
    (C := max Ce Cw + 1) (ν := ν) (Cv := Cv) hm hk2 hδ'pos (by positivity) hν hCv0.le
    (fun u hu => hncD u (hmem' u hu)) hE' hW'
    (fun u hu => hx u (hmem' u hu)) (fun u hu => hd2 u (hmem' u hu))
    (fun u hu => hd3 u (hmem' u hu)) (fun u hu => hode u (hmem' u hu))
    (fun u hu => hsepwD u (hmem' u hu)) hv' hItend
  refine Filter.Tendsto.congr' ?_ hshape
  filter_upwards [self_mem_nhdsWithin] with u hu
  dsimp only [x]

end Submission.NBody
