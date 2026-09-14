import Submission.NBody.MarchalCollisionAsymptotics
import Submission.NBody.MarchalSeqShapeUniform
import Submission.NBody.MarchalSeqWindow
import Submission.NBody.MarchalSeqLeft
import Submission.NBody.MarchalModelTwoSidedApply
import Submission.NBody.MarchalBumpTwoSided
import Submission.NBody.MarchalSelfScaledVelocity
import Submission.NBody.MarchalReflectMinimizer
import Submission.NBody.MarchalSeqBump

/-!
# The data of a collision: the right side

At an interior collision time `t₀` of an `h`-minimiser, on the right of `t₀`, the whole endgame
needs: a radius `δ`, constants `C` (energy/work), `Cv` (scaled outside velocity), `κ` (the
Ferrario--Terracini constant), the Newton data, and the five asymptotics of `propo:asy` together
with the shape control `t • ṡ → 0`.  This module packages all of them in a single existential.
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

/-- **The collision data on the right of a collision of a minimiser.** -/
theorem exists_collision_data_right {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b t₀ : ℝ}
    {k : Finset (Fin N)}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b) (hk2 : 2 ≤ k.card)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) {ε ν : ℝ} (hε : 0 < ε) (hεb : t₀ + ε ≤ b)
    (hnc : ∀ t ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ t))
    (hcoll : ¬ WithoutCollisions (γ t₀))
    (hν : 0 < ν) (hsepw : ∀ t ∈ Ioo t₀ (t₀ + ε), ClusterSeparatedWeak k (γ t) ν)
    (hI0 : clusterInertia m k (γ t₀) = 0) :
    ∃ δ C Cv κ : ℝ, 0 < δ ∧ δ ≤ ε ∧ 0 < C ∧ 0 ≤ Cv ∧ 0 < κ ∧
      (∀ t ∈ Ioo (0:ℝ) δ, ClusterSeparatedWeak k (shiftCurve γ t₀ t) ν) ∧
      (∀ t ∈ Ioo (0:ℝ) δ, WithoutCollisions (shiftCurve γ t₀ t)) ∧
      (∀ t ∈ Ioo (0:ℝ) δ,
        |clusterRelEnergy m k (shiftCurve γ t₀ t) (deriv (shiftCurve γ t₀) t)| ≤ C) ∧
      (∀ t ∈ Ioo (0:ℝ) δ,
        |crossWork m k (shiftCurve γ t₀ t) (cmRel m k (shiftCurve γ t₀ t))| ≤ C) ∧
      (∀ t ∈ Ioo (0:ℝ) δ, ∀ j ∉ k, ‖deriv (shiftCurve γ t₀) t j‖
        ≤ Cv * Real.sqrt (clusterPotential m k (shiftCurve γ t₀ t))) ∧
      (∀ t ∈ Ioo (0:ℝ) δ, HasDerivAt (shiftCurve γ t₀) (deriv (shiftCurve γ t₀) t) t) ∧
      (∀ t ∈ Ioo (0:ℝ) δ,
        HasDerivAt (deriv (shiftCurve γ t₀)) (iteratedDeriv 2 (shiftCurve γ t₀) t) t) ∧
      (∀ t ∈ Ioo (0:ℝ) δ, HasDerivAt (deriv (deriv (shiftCurve γ t₀)))
        (deriv (deriv (deriv (shiftCurve γ t₀))) t) t) ∧
      (∀ t ∈ Ioo (0:ℝ) δ, iteratedDeriv 2 (shiftCurve γ t₀) t = ∇_[m] (U m) (shiftCurve γ t₀ t)) ∧
      Tendsto (fun t : ℝ => clusterInertia m k (shiftCurve γ t₀ t))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Tendsto (fun t : ℝ => clusterInertia m k (shiftCurve γ t₀ t) / t ^ ((4:ℝ)/3))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds κ) ∧
      Tendsto (fun t : ℝ => clusterPotential m k (shiftCurve γ t₀ t) * t ^ ((2:ℝ)/3))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ((2:ℝ)/9 * κ)) ∧
      Tendsto (fun t : ℝ => deriv (fun s : ℝ => clusterInertia m k (shiftCurve γ t₀ s)) t
        / t ^ ((1:ℝ)/3)) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ((4:ℝ)/3 * κ)) ∧
      Tendsto (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (shiftCurve γ t₀ s))) t
        * t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ((4:ℝ)/9 * κ)) ∧
      Tendsto (fun t : ℝ => t • deriv (fun u : ℝ => clusterShape m k (shiftCurve γ t₀ u)) t)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  classical
  have hkne : k.Nonempty := Finset.card_pos.mp (by omega)
  have hmne : ∀ i, m i ≠ 0 := fun i => ne_of_gt (hm i)
  let x : ℝ → EN E N := shiftCurve γ t₀
  have hxeq : ∀ s : ℝ, x s = γ (t₀ + s) := fun s => rfl
  -- the asymptotics (continuum limits) and the shape control
  obtain ⟨κ, hκpos, hIn, hDn, hSec, hU, hKrel⟩ :=
    clusterInertia_asymptotics_at_collision (m := m) (h := h) (γ := γ) (a := a) (b := b)
      (t₀ := t₀) (k := k) hm hh hab hk2 hac hmin hfin ht₀ hε hεb hnc hν hsepw hI0
  have hts := tendsto_mul_deriv_clusterShape_at_collision (m := m) (h := h) (γ := γ) (a := a)
    (b := b) (t₀ := t₀) (k := k) hm hh hab hk2 hac hmin hfin ht₀ hε hεb hnc hν hsepw hI0
  -- the working interval
  set D : ℝ := min ε 1 with hDdef
  have hDpos : 0 < D := lt_min hε one_pos
  have hDle : D ≤ ε := min_le_left _ _
  have hDb : t₀ + D ≤ b := by linarith
  have hncD : ∀ u ∈ Ioo (0:ℝ) D, WithoutCollisions (x u) := fun u hu =>
    hnc (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2, hDle]⟩
  have hsepwD : ∀ u ∈ Ioo (0:ℝ) D, ClusterSeparatedWeak k (x u) ν := fun u hu =>
    hsepw (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2, hDle]⟩
  -- the Newton data
  have hsol := exists_solution_data_of_minimizer (m := m) (h := h) hm hh hab hac hmin hfin
    (S := Ioo t₀ (t₀ + D))
    (fun t ht => ⟨lt_trans ht₀.1 ht.1, by linarith [ht.2, hDb]⟩)
    (fun t ht => hnc t ⟨ht.1, by linarith [ht.2, hDle]⟩)
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
    (a := a) (b := b) (t₀ := t₀) (ε := D) hm hh hab hac hmin hfin ht₀ hcoll hDpos hDb
    (fun t ht => hnc t ⟨ht.1, by linarith [ht.2, hDle]⟩)
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
  have hItend : Tendsto (fun u : ℝ => clusterInertia m k (x u))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
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
    simpa only [x, shiftCurve, hI0] using h6
  -- the interval on which the inertia is at most `1`
  obtain ⟨δI, hδIpos, hδI⟩ : ∃ δI : ℝ, 0 < δI ∧ ∀ u ∈ Ioo (0:ℝ) δI,
      clusterInertia m k (x u) ≤ 1 := by
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
        _ = Cw := by rw [hCwdef, mul_one]
    exact le_trans h1 (le_trans hle (by linarith [le_max_right Ce Cw]))
  -- the scaled outside-velocity bound
  obtain ⟨Cv, hCv0, hv⟩ := exists_scaled_outside_velocity_bound_of_collision (m := m) (h := h)
    (γ := γ) (a := a) (b := b) (t₀ := t₀) (ε := ε) (ν := ν) (k := k)
    hm hh hab hk2 hac hmin hfin ht₀ hε hεb hnc hν hsepw hI0
  obtain ⟨δv, hδvpos, hvδ⟩ : ∃ δv : ℝ, 0 < δv ∧ ∀ u ∈ Ioo (0:ℝ) δv, ∀ j ∉ k,
      ‖deriv (shiftCurve γ t₀) u j‖ ≤ Cv * Real.sqrt (clusterPotential m k (shiftCurve γ t₀ u)) := by
    obtain ⟨δv, hδvpos, hvδ⟩ := exists_forall_Ioo_of_eventually_nhdsGT hv
    refine ⟨δv, hδvpos, fun u hu j hj => ?_⟩
    have h := hvδ u hu j hj
    rw [show deriv (shiftCurve γ t₀) u = deriv γ (t₀ + u) from deriv_shiftCurve_eq t₀ u]
    exact h
  -- shrink once more
  set δ' : ℝ := min δ δv with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδpos hδvpos
  have hδ'leδ : δ' ≤ δ := min_le_left _ _
  have hδ'leδv : δ' ≤ δv := min_le_right _ _
  have hmem' : ∀ u ∈ Ioo (0:ℝ) δ', u ∈ Ioo (0:ℝ) D :=
    fun u hu => hmem u ⟨hu.1, lt_of_lt_of_le hu.2 hδ'leδ⟩
  refine ⟨δ', max Ce Cw + 1, Cv, κ, hδ'pos,
    le_trans (le_trans hδ'leδ hδleD) hDle, by positivity, hCv0.le, hκpos,
    fun u hu => hsepwD u (hmem' u hu),
    fun u hu => hncD u (hmem' u hu),
    fun u hu => hE u ⟨hu.1, lt_of_lt_of_le hu.2 hδ'leδ⟩,
    fun u hu => hW u ⟨hu.1, lt_of_lt_of_le hu.2 hδ'leδ⟩,
    fun u hu => hvδ u ⟨hu.1, lt_of_lt_of_le hu.2 hδ'leδv⟩,
    fun u hu => hx u (hmem' u hu),
    fun u hu => hd2 u (hmem' u hu),
    fun u hu => hd3 u (hmem' u hu),
    fun u hu => hode u (hmem' u hu),
    hItend, ?_, ?_, ?_, ?_, hts⟩
  · refine Filter.Tendsto.congr' ?_ hIn
    filter_upwards [self_mem_nhdsWithin] with u hu
    dsimp only [x, shiftCurve]
  · refine Filter.Tendsto.congr' ?_ hU
    filter_upwards [self_mem_nhdsWithin] with u hu
    dsimp only [x, shiftCurve]
  · refine Filter.Tendsto.congr' ?_ hDn
    filter_upwards [self_mem_nhdsWithin] with u hu
    dsimp only [x, shiftCurve]
  · refine Filter.Tendsto.congr' ?_ hSec
    filter_upwards [self_mem_nhdsWithin] with u hu
    dsimp only [x, shiftCurve]

/-- **The collision data on the left of a collision of a minimiser.**  Obtained by reflecting the
curve about `t₀`, so that the "right side" statement applies to `reflectCurve γ t₀`. -/
theorem exists_collision_data_left {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b t₀ : ℝ}
    {k : Finset (Fin N)}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b) (hk2 : 2 ≤ k.card)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) {ε ν : ℝ} (hε : 0 < ε) (hεa : a ≤ t₀ - ε)
    (hncL : ∀ t ∈ Ioo (t₀ - ε) t₀, WithoutCollisions (γ t))
    (hcoll : ¬ WithoutCollisions (γ t₀))
    (hν : 0 < ν) (hsepwL : ∀ t ∈ Ioo (t₀ - ε) t₀, ClusterSeparatedWeak k (γ t) ν)
    (hI0 : clusterInertia m k (γ t₀) = 0) :
    ∃ δ C Cv κ : ℝ, 0 < δ ∧ δ ≤ ε ∧ 0 < C ∧ 0 ≤ Cv ∧ 0 < κ ∧
      (∀ t ∈ Ioo (0:ℝ) δ, ClusterSeparatedWeak k (reflectCurve γ t₀ t) ν) ∧
      (∀ t ∈ Ioo (0:ℝ) δ, WithoutCollisions (reflectCurve γ t₀ t)) ∧
      (∀ t ∈ Ioo (0:ℝ) δ,
        |clusterRelEnergy m k (reflectCurve γ t₀ t) (deriv (reflectCurve γ t₀) t)| ≤ C) ∧
      (∀ t ∈ Ioo (0:ℝ) δ,
        |crossWork m k (reflectCurve γ t₀ t) (cmRel m k (reflectCurve γ t₀ t))| ≤ C) ∧
      (∀ t ∈ Ioo (0:ℝ) δ, ∀ j ∉ k, ‖deriv (reflectCurve γ t₀) t j‖
        ≤ Cv * Real.sqrt (clusterPotential m k (reflectCurve γ t₀ t))) ∧
      (∀ t ∈ Ioo (0:ℝ) δ, HasDerivAt (reflectCurve γ t₀) (deriv (reflectCurve γ t₀) t) t) ∧
      (∀ t ∈ Ioo (0:ℝ) δ,
        HasDerivAt (deriv (reflectCurve γ t₀)) (iteratedDeriv 2 (reflectCurve γ t₀) t) t) ∧
      (∀ t ∈ Ioo (0:ℝ) δ, HasDerivAt (deriv (deriv (reflectCurve γ t₀)))
        (deriv (deriv (deriv (reflectCurve γ t₀))) t) t) ∧
      (∀ t ∈ Ioo (0:ℝ) δ,
        iteratedDeriv 2 (reflectCurve γ t₀) t = ∇_[m] (U m) (reflectCurve γ t₀ t)) ∧
      Tendsto (fun t : ℝ => clusterInertia m k (reflectCurve γ t₀ t))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Tendsto (fun t : ℝ => clusterInertia m k (reflectCurve γ t₀ t) / t ^ ((4:ℝ)/3))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds κ) ∧
      Tendsto (fun t : ℝ => clusterPotential m k (reflectCurve γ t₀ t) * t ^ ((2:ℝ)/3))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ((2:ℝ)/9 * κ)) ∧
      Tendsto (fun t : ℝ => deriv (fun s : ℝ => clusterInertia m k (reflectCurve γ t₀ s)) t
        / t ^ ((1:ℝ)/3)) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ((4:ℝ)/3 * κ)) ∧
      Tendsto (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (reflectCurve γ t₀ s))) t
        * t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ((4:ℝ)/9 * κ)) ∧
      Tendsto (fun t : ℝ => t • deriv (fun u : ℝ => clusterShape m k (reflectCurve γ t₀ u)) t)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  classical
  have hmin' : IsHMinimizer m h (reflectCurve γ t₀) (t₀ - b) (t₀ - a) :=
    isHMinimizer_reflectCurve hab.le hmin
  have hac' : AbsolutelyContinuousOnInterval (reflectCurve γ t₀) (t₀ - b) (t₀ - a) :=
    absolutelyContinuousOnInterval_reflectCurve hac
  have h0 : (0:ℝ) ∈ Ioo (t₀ - b) (t₀ - a) := ⟨by linarith [ht₀.2], by linarith [ht₀.1]⟩
  have hcoll' : ¬ WithoutCollisions (reflectCurve γ t₀ 0) := by
    simpa only [reflectCurve, sub_zero] using hcoll
  have hnc' : ∀ t ∈ Ioo (0:ℝ) (0 + ε), WithoutCollisions (reflectCurve γ t₀ t) := by
    intro t ht
    rw [zero_add] at ht
    have h1 : t₀ - t ∈ Ioo (t₀ - ε) t₀ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [reflectCurve] using hncL (t₀ - t) h1
  have hsepw' : ∀ t ∈ Ioo (0:ℝ) (0 + ε), ClusterSeparatedWeak k (reflectCurve γ t₀ t) ν := by
    intro t ht
    rw [zero_add] at ht
    have h1 : t₀ - t ∈ Ioo (t₀ - ε) t₀ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [reflectCurve] using hsepwL (t₀ - t) h1
  have hI0' : clusterInertia m k (reflectCurve γ t₀ 0) = 0 := by
    simpa only [reflectCurve, sub_zero] using hI0
  obtain ⟨δ, C, Cv, κ, hδpos, hδε, hCpos, hCvnn, hκpos, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14⟩ := exists_collision_data_right (m := m) (h := h)
      (γ := reflectCurve γ t₀) (a := t₀ - b) (b := t₀ - a) (t₀ := 0) (k := k)
      hm hh (by linarith) hk2 hac' hmin' hfin h0 hε (by linarith) hnc' hcoll' hν hsepw' hI0'
  have hsh : shiftCurve (reflectCurve γ t₀) 0 = reflectCurve γ t₀ := by
    funext u; simp only [shiftCurve, zero_add]
  simp only [hsh] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  exact ⟨δ, C, Cv, κ, hδpos, hδε, hCpos, hCvnn, hκpos, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14⟩


/-! ## The sequential window bound at a collision -/

/-- **The right window bound at a collision of a minimiser.**  This is `seq_action_window_bound`
with all its hypotheses discharged from the collision data. -/
theorem seq_action_window_bound_of_collision {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b t₀ T : ℝ} {k : Finset (Fin N)}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b) (hk2 : 2 ≤ k.card)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) {ε ν : ℝ} (hε : 0 < ε) (hεb : t₀ + ε ≤ b)
    (hnc : ∀ t ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ t))
    (hcoll : ¬ WithoutCollisions (γ t₀))
    (hν : 0 < ν) (hsepw : ∀ t ∈ Ioo t₀ (t₀ + ε), ClusterSeparatedWeak k (γ t) ν)
    (hI0 : clusterInertia m k (γ t₀) = 0)
    {T : ℝ} (hT : 0 < T)
    {i₀ : Fin N} (hi₀ : i₀ ∈ k)
    {sbar : EN E N} (hsbarnc : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbar i ≠ sbar j)
    {lam : ℕ → ℝ} (hlampos : ∀ n, 0 < lam n)
    (hlamT : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)))
    (hs : Tendsto (fun n => clusterShape m k (shiftCurve γ t₀ (lam n))) atTop (nhds sbar))
    {δ : E} (hδ : δ ≠ 0) (hδT : 2 * ‖δ‖ ≤ T)
    (hgood : ∀ j ∈ k.erase i₀,
      (inner ℝ (sbar i₀ - sbar j) δ) ^ 2 < ‖sbar i₀ - sbar j‖ ^ 2 * ‖δ‖ ^ 2) :
    ∃ (κ : ℝ) (K : ℕ → ℝ), 0 < κ ∧
      Tendsto K atTop (nhds (modelDiff m k i₀ κ sbar T δ)) ∧
      ∀ᶠ n in atTop, (∫ t in t₀..(t₀ + lam n * T),
        (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t)
          - lagR m h (γ t) (deriv γ t)))
        ≤ (lam n) ^ ((1:ℝ)/3) * K n + (lam n) ^ ((5:ℝ)/3) * restBound m k δ T ν := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  obtain ⟨δ₀, C, Cv, κ, hδ₀pos, hδ₀ε, hCpos, hCvnn, hκpos, hsepU, hncU, hE, hW, hvU, hder,
    hd2, hd3, hode, hI0t, hIn, hUlim, hDn, hSec, hts⟩ :=
    exists_collision_data_right (m := m) (h := h) (γ := γ) (a := a) (b := b) (t₀ := t₀) (k := k)
      hm hh hab hk2 hac hmin hfin ht₀ hε hεb hnc hcoll hν hsepw hI0
  have hlamT0 : Tendsto lam atTop (nhds 0) := hlamT.mono_right nhdsWithin_le_nhds
  have hseqUG := seq_shape_uniform_limit_at_collision (m := m) (k := k) (γ := γ) (t₀ := t₀)
    (T := T) (ε := δ₀) (ν := ν) (C := C) (Cv := Cv) (sbar := sbar) (lam := lam)
    hm hk2 hδ₀pos hT hCpos hν hCvnn hncU hE hW hder hd2 hd3 hode hsepU hvU hI0t
    hlampos hlamT hs hts
  have hac' : ∀ᶠ n in atTop, AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam n * T) := by
    have hev : ∀ᶠ n in atTop, lam n < ε / T :=
      hlamT0.eventually (isOpen_Iio.mem_nhds (div_pos hε hT))
    filter_upwards [hev] with n hn
    have hlt : lam n * T < ε := (lt_div_iff₀ hT).mp hn
    refine hac.mono ?_
    rw [Set.uIcc_of_le (by nlinarith [hlampos n, hT]), Set.uIcc_of_le hab.le]
    exact Set.Icc_subset_Icc ht₀.1.le (by linarith [hεb])
  obtain ⟨K, hKlim, hKbd⟩ := seq_action_window_bound (m := m) (h := h) (k := k) (i₀ := i₀)
    (γ := γ) (t₀ := t₀) (T := T) (δ := δ) (κ := κ) (sbar := sbar) (lam := lam)
    (ε := δ₀) (C := C) (Cv := Cv) (ν := ν) (Cd := 1)
    hm hi₀ hk2 hδ hT hδT hκpos hsbarnc hgood hlampos hlamT0 hδ₀pos hCpos hν hCvnn
    (by norm_num : (0:ℝ) < 1) hncU hE hW hder hd2 hd3 hode hsepU hvU hI0t hIn hUlim hDn hts
    hseqUG hac'
  exact ⟨κ, K, hκpos, hKlim, hKbd⟩

/-- **The left window bound at a collision of a minimiser.**  Obtained from the right window bound
applied to the reflected curve. -/
theorem seq_action_window_bound_left_of_collision {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b t₀ T : ℝ} {k : Finset (Fin N)}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b) (hk2 : 2 ≤ k.card)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) {ε ν : ℝ} (hε : 0 < ε) (hεa : a ≤ t₀ - ε)
    (hnc : ∀ t ∈ Ioo (t₀ - ε) t₀, WithoutCollisions (γ t))
    (hcoll : ¬ WithoutCollisions (γ t₀))
    (hν : 0 < ν) (hsepw : ∀ t ∈ Ioo (t₀ - ε) t₀, ClusterSeparatedWeak k (γ t) ν)
    (hI0 : clusterInertia m k (γ t₀) = 0)
    {T : ℝ} (hT : 0 < T)
    {i₀ : Fin N} (hi₀ : i₀ ∈ k)
    {sbar : EN E N} (hsbarnc : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbar i ≠ sbar j)
    {lam : ℕ → ℝ} (hlampos : ∀ n, 0 < lam n)
    (hlamT : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)))
    (hs : Tendsto (fun n => clusterShape m k (reflectCurve γ t₀ (lam n))) atTop (nhds sbar))
    {δ : E} (hδ : δ ≠ 0) (hδT : 2 * ‖δ‖ ≤ T)
    (hgood : ∀ j ∈ k.erase i₀,
      (inner ℝ (sbar i₀ - sbar j) δ) ^ 2 < ‖sbar i₀ - sbar j‖ ^ 2 * ‖δ‖ ^ 2) :
    ∃ (κ : ℝ) (K : ℕ → ℝ), 0 < κ ∧
      Tendsto K atTop (nhds (modelDiff m k i₀ κ sbar T δ)) ∧
      ∀ᶠ n in atTop, (∫ t in (t₀ - lam n * T)..t₀,
        (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t)
          - lagR m h (γ t) (deriv γ t)))
        ≤ (lam n) ^ ((1:ℝ)/3) * K n + (lam n) ^ ((5:ℝ)/3) * restBound m k δ T ν := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hacL : AbsolutelyContinuousOnInterval (reflectCurve γ t₀) (t₀ - b) (t₀ - a) :=
    absolutelyContinuousOnInterval_reflectCurve hac
  have hminL : IsHMinimizer m h (reflectCurve γ t₀) (t₀ - b) (t₀ - a) :=
    isHMinimizer_reflectCurve hab.le hmin
  have h0 : (0:ℝ) ∈ Ioo (t₀ - b) (t₀ - a) := ⟨by linarith [ht₀.2], by linarith [ht₀.1]⟩
  have hcollL : ¬ WithoutCollisions (reflectCurve γ t₀ 0) := by
    simpa only [reflectCurve, sub_zero] using hcoll
  have hncL : ∀ t ∈ Ioo (0:ℝ) (0 + ε), WithoutCollisions (reflectCurve γ t₀ t) := by
    intro t ht
    rw [zero_add] at ht
    have h1 : t₀ - t ∈ Ioo (t₀ - ε) t₀ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [reflectCurve] using hnc (t₀ - t) h1
  have hsepwL : ∀ t ∈ Ioo (0:ℝ) (0 + ε), ClusterSeparatedWeak k (reflectCurve γ t₀ t) ν := by
    intro t ht
    rw [zero_add] at ht
    have h1 : t₀ - t ∈ Ioo (t₀ - ε) t₀ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [reflectCurve] using hsepw (t₀ - t) h1
  have hI0L : clusterInertia m k (reflectCurve γ t₀ 0) = 0 := by
    simpa only [reflectCurve, sub_zero] using hI0
  have hs' : Tendsto (fun n => clusterShape m k (shiftCurve (reflectCurve γ t₀) 0 (lam n)))
      atTop (nhds sbar) := by
    refine hs.congr' ?_
    filter_upwards with n
    rw [shiftCurve, zero_add]
  obtain ⟨κ, K, hκ, hKlim, hKbd⟩ := seq_action_window_bound_of_collision (m := m) (h := h)
    (γ := reflectCurve γ t₀) (a := t₀ - b) (b := t₀ - a) (t₀ := 0) (k := k)
    (ε := ε) (ν := ν) (T := T) (i₀ := i₀) (sbar := sbar) (lam := lam) (δ := δ)
    hm hh (by linarith) hk2 hacL hminL hfin h0 hε (by linarith) hncL hcollL hν hsepwL hI0L
    hT hi₀ hsbarnc hlampos hlamT hs' hδ hδT hgood
  refine ⟨κ, K, hκ, hKlim, ?_⟩
  filter_upwards [hKbd] with n hn
  rw [left_window_eq (fun i => (hm i).le) h δ T (lam n) t₀ γ]
  simpa only [zero_add] using hn

/-! ## Integrability of the bump Lagrangian difference -/

/-- **The bump Lagrangian difference is interval integrable** on the (right) window, given the
integrability of the five rescaled pieces of the transfer identity. -/
theorem intervalIntegrable_bump_lagR_diff {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0) {lam T t₀ h : ℝ} (hlam : 0 < lam)
    (hT : 0 < T) {γ : ℝ → EN E N}
    (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T))
    (h1 : IntervalIntegrable (fun s : ℝ => massInner m (deriv (bumpRescaled m k γ t₀ lam) s)
        (deriv (stdVarVec m k i₀ δ T) s)) volume (0:ℝ) T)
    (h2 : IntervalIntegrable (fun s : ℝ => ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
        volume (0:ℝ) T)
    (h3 : IntervalIntegrable (fun s : ℝ => clusterPotential m k
        (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s)) volume (0:ℝ) T)
    (h4 : IntervalIntegrable (fun s : ℝ => clusterPotential m k
        (bumpRescaled m k γ t₀ lam s)) volume (0:ℝ) T)
    (h5 : IntervalIntegrable (fun s : ℝ => clusterPotentialRest m k
        (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
          - clusterPotentialRest m k (γ (t₀ + lam * s))) volume (0:ℝ) T) :
    IntervalIntegrable (fun t : ℝ => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t))
      volume t₀ (t₀ + lam * T) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  -- the rescaled integrand
  have hR : IntervalIntegrable (fun s : ℝ => lam ^ (-(2:ℝ)/3) *
        (massInner m (deriv (bumpRescaled m k γ t₀ lam) s) (deriv (stdVarVec m k i₀ δ T) s)
          + (1 / 2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2
          + (clusterPotential m k (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s)
              - clusterPotential m k (bumpRescaled m k γ t₀ lam s)))
      + (clusterPotentialRest m k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
          - clusterPotentialRest m k (γ (t₀ + lam * s)))) volume (0:ℝ) T :=
    (((h1.add (h2.const_mul (1/2))).add (h3.sub h4)).const_mul
      (lam ^ (-(2:ℝ)/3))).add h5
  have hae := bump_lagR_diff_ae (h := h) hm hi₀ hδ hlam hT hac
  set F : ℝ → ℝ := fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
      (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t) with hFdef
  have hGint : Integrable (fun s : ℝ => F (t₀ + lam * s)) (volume.restrict (Set.Ioc (0:ℝ) T)) :=
    hR.1.congr hae.symm
  have hG : IntervalIntegrable (fun s : ℝ => F (t₀ + lam * s)) volume (0:ℝ) T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr hGint
  -- change of variables: `t ↦ t₀ + λs`
  have hG' : IntervalIntegrable (fun x : ℝ => F (lam * x + t₀)) volume ((0:ℝ) / lam)
      ((lam * T) / lam) := by
    rw [zero_div, mul_div_cancel_left₀ T hlam.ne']
    refine hG.congr fun x _ => ?_
    rw [add_comm]
  have hG1 : IntervalIntegrable (fun u : ℝ => F (u + t₀)) volume (0:ℝ) (lam * T) :=
    (IntervalIntegrable.comp_mul_left_iff (f := fun u : ℝ => F (u + t₀)) (c := lam)
      (a := (0:ℝ)) (b := lam * T) hlam.ne').mp hG'
  have hF : IntervalIntegrable F volume (0 + t₀) (lam * T + t₀) :=
    (IntervalIntegrable.comp_add_right_iff (f := F) (c := t₀) (a := (0:ℝ)) (b := lam * T)).mp hG1
  simpa only [zero_add, add_zero, add_comm] using hF
/-- **The bump Lagrangian difference is interval integrable on the left window**, given the
integrability of the reflected (right) window. -/
theorem intervalIntegrable_bump_lagR_diff_left {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0) {lam T t₀ h : ℝ}
    (hlam : 0 < lam) (hT : 0 < T) {γ : ℝ → EN E N}
    (hR : IntervalIntegrable (fun u : ℝ => lagR m h (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀) u)
        (deriv (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀)) u)
      - lagR m h (reflectCurve γ t₀ u) (deriv (reflectCurve γ t₀) u)) volume (0:ℝ) (lam * T)) :
    IntervalIntegrable (fun t : ℝ => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t))
      volume (t₀ - lam * T) t₀ := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  set HL : ℝ → ℝ := fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
      (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t) with hHL
  have hsub : IntervalIntegrable (fun x : ℝ => HL (t₀ - x)) volume (0:ℝ) (lam * T) :=
    hR.congr fun u _ => (lagR_bumpCurve_reflect_eq (fun i => (hm i).le) h δ T lam t₀ γ u).symm
  have hsub2 : IntervalIntegrable (fun x : ℝ => HL (t₀ - x)) volume (lam * T) (0:ℝ) :=
    ⟨hsub.2, hsub.1⟩
  have h := (IntervalIntegrable.comp_sub_left_iff (f := HL) (c := t₀) (a := t₀ - lam * T)
    (b := t₀)).mp (by simpa using hsub2)
  simpa only [sub_self, hHL] using h

end Submission.NBody
