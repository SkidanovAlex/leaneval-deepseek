import Submission.NBody.MarchalMultiJolt
import Submission.NBody.MarchalMultiBound
import Submission.NBody.MarchalMultiKineticBound
import Submission.NBody.MarchalMultiOutsideKinetic
import Submission.NBody.MarchalMultiSetup
import Submission.NBody.MarchalCollPartition
import Submission.NBody.MarchalCollisionSolutionData
import Submission.NBody.MarchalSolutionThirdDeriv
import Submission.NBody.MarchalCollClass

/-!
# The kinetic-energy bound at a collision time (FT `lemma:K_bound`)

The geometry of the Marchal chapter (F1), fifth layer.  On the collision-free side `(t₀, t₀ + ε)` of
a collision time of a minimiser, the total kinetic energy is bounded by `C t^{-2/3}`.  This is the
quantitative input of the Rolle--Sperner step (`MarchalLocMinIsolated`) and of every blow-up module.

The proof runs the sum-level (multi-cluster) Sundman theory of `MarchalMultiJolt` with the family of
collision classes at `t₀`: all of its hypotheses are the *one-sided* separation of the classes plus
the Newton data on the collision-free side, both of which come from the geometry.

Everything in this file is fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The derivative of the shifted curve `u ↦ γ (t₀ + u)`. -/
lemma deriv_shiftCurve_eq {γ : ℝ → EN E N} (t₀ u : ℝ) :
    deriv (fun s : ℝ => γ (t₀ + s)) u = deriv γ (t₀ + u) :=
  deriv_comp_const_add γ t₀ u

/-- The second iterate of the derivative of the shifted curve. -/
lemma iteratedDeriv_two_shiftCurve_eq {γ : ℝ → EN E N} (t₀ u : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => γ (t₀ + s)) u = iteratedDeriv 2 γ (t₀ + u) := by
  rw [iteratedDeriv_two_eq_deriv_deriv, iteratedDeriv_two_eq_deriv_deriv]
  have h2 : deriv (fun s : ℝ => γ (t₀ + s)) = fun s : ℝ => deriv γ (t₀ + s) := by
    funext s; exact deriv_shiftCurve_eq t₀ s
  rw [h2]
  exact deriv_comp_const_add (deriv γ) t₀ u

/-- An eventual statement at `0⁺` holds pointwise on a right neighbourhood. -/
lemma exists_forall_Ioo_of_eventually_nhdsGT {P : ℝ → Prop}
    (h : ∀ᶠ t in 𝓝[>] (0:ℝ), P t) : ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo (0:ℝ) δ, P t := by
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp h
  refine ⟨δ, hδpos, fun t ht => hδ t ?_ ht.1⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
  exact ht.2

/-- **The kinetic-energy bound at a collision time.**  Let `γ` be an `h`-minimiser on `[a,b]` with a
collision at the interior time `t₀`, and suppose `γ` is collision free on `(t₀, t₀ + ε)`.  Then on
the shifted curve `u ↦ γ (t₀ + u)` the total kinetic energy is bounded by `C u^{-2/3}` near `0⁺`. -/
theorem exists_kinetic_bound_at_collision {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b t₀ ε : ℝ} (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) (hcoll : ¬ WithoutCollisions (γ t₀))
    (hε : 0 < ε) (hεb : t₀ + ε ≤ b)
    (hnc : ∀ t ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ t)) :
    ∃ Ck : ℝ, 0 < Ck ∧ ∀ᶠ u in 𝓝[>] (0:ℝ),
      kinetic m (deriv (fun s : ℝ => γ (t₀ + s)) u) ≤ Ck * u ^ (-((2:ℝ)/3)) := by
  classical
  -- a positive lower bound for the masses
  obtain ⟨κ, hκpos, hκle⟩ : ∃ κ : ℝ, 0 < κ ∧ ∀ i, κ ≤ m i := by
    by_cases hne : (Finset.univ : Finset (Fin N)).Nonempty
    · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N)) m hne
      exact ⟨m i₀, hm i₀, fun i => hi₀ i (Finset.mem_univ i)⟩
    · refine ⟨1, one_pos, fun i => ?_⟩
      exact absurd (Finset.mem_univ i)
        (Finset.eq_empty_iff_forall_notMem.mp (Finset.not_nonempty_iff_eq_empty.mp hne) i)
  have hmne : ∀ i, m i ≠ 0 := fun i => ne_of_gt (hm i)
  -- the collision
  have hcoll' : ∃ i j : Fin N, i ≠ j ∧ r (γ t₀) i j = 0 := by
    by_contra hc
    exact hcoll fun i j hij hr => hc ⟨i, j, hij, hr⟩
  obtain ⟨i₁, j₁, hij₁, hr₁⟩ := hcoll'
  have heq₁ : γ t₀ j₁ = γ t₀ i₁ := by
    have h := hr₁
    rw [r_eq_norm_sub, norm_eq_zero, sub_eq_zero] at h
    exact h.symm
  have hks2 : 2 ≤ (collClass γ t₀ i₁).card :=
    two_le_card_collClass_of_exists hij₁.symm heq₁
  have hksne : (collClasses γ t₀).Nonempty :=
    ⟨collClass γ t₀ i₁, mem_collClasses.mpr ⟨i₁, rfl, hks2⟩⟩
  have hne : ∀ k ∈ collClasses γ t₀, k.Nonempty := fun k hk => collClasses_nonempty hk
  have hne2 : ∀ k ∈ collClasses γ t₀, 2 ≤ k.card := fun k hk => collClasses_card hk
  have hedj : ∀ k ∈ collClasses γ t₀, ∀ k' ∈ collClasses γ t₀, k ≠ k' → Disjoint k k' :=
    disjoint_collClasses
  -- continuity and the geometric data
  have hcont : ContinuousOn γ (Icc a b) := by
    have h := hac.continuousOn
    rwa [uIcc_of_le hab.le] at h
  have hcontAt : ContinuousAt γ t₀ := hcont.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  obtain ⟨ν, hνpos, ε₁, hε₁pos, hsep₁⟩ := exists_separation_of_collClasses (γ := γ) hcont ht₀
  obtain ⟨γc, hγcpos, hγmle, ε₂, hε₂pos, hIbd⟩ :=
    exists_clusterInertia_bound_of_collClasses hm hcont ht₀
  -- the working intervals
  set D : ℝ := min ε (min ε₁ ε₂) with hDdef
  have hDpos : 0 < D := lt_min hε (lt_min hε₁pos hε₂pos)
  have hDle : D ≤ ε := le_trans (min_le_left _ _) le_rfl
  have hDle₁ : D ≤ ε₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hDle₂ : D ≤ ε₂ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hDb : t₀ + D ≤ b := by linarith
  set E₀ : ℝ := D / 4 with hE₀def
  have hE₀pos : 0 < E₀ := by rw [hE₀def]; linarith
  have hE₀le : E₀ ≤ D := by rw [hE₀def]; linarith
  let x : ℝ → EN E N := fun s => γ (t₀ + s)
  have hx_apply : ∀ s : ℝ, x s = γ (t₀ + s) := fun s => rfl
  -- collision freeness
  have hncE : ∀ u ∈ Ioo (0:ℝ) D, WithoutCollisions (x u) := fun u hu =>
    hnc (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2, hDle]⟩
  have hnc₀ : ∀ u ∈ Ioo (0:ℝ) E₀, WithoutCollisions (x u) := fun u hu =>
    hncE u ⟨hu.1, lt_of_lt_of_le hu.2 hE₀le⟩
  have hncEv : ∀ᶠ u in 𝓝[>] (0:ℝ), WithoutCollisions (x u) := by
    filter_upwards [Ioo_mem_nhdsGT hE₀pos] with u hu
    exact hnc₀ u hu
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
  have hd2' : ∀ u ∈ Ioo (0:ℝ) D, HasDerivAt (deriv x) (deriv (deriv x) u) u := fun u hu =>
    (hd2 u hu).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x u)
  have hode' : ∀ u ∈ Ioo (0:ℝ) D, deriv (deriv x) u = ∇_[m] (U m) (x u) := fun u hu =>
    (iteratedDeriv_two_eq_deriv_deriv x u).symm.trans (hode u hu)
  -- the separation and the inertia bounds on the two intervals
  have hsepE : ∀ u ∈ Ioo (0:ℝ) D, ∀ k ∈ collClasses γ t₀, ClusterSeparatedWeak k (x u) ν :=
    fun u hu => (hsep₁ (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2, hDle₁]⟩).1
  have hsepTE : ∀ u ∈ Ioo (0:ℝ) D, ∀ i ∉ collUnion γ t₀, ∀ j ∉ collUnion γ t₀,
      i ≠ j → ν ≤ r (x u) i j :=
    fun u hu => (hsep₁ (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2, hDle₁]⟩).2
  have hIkE : ∀ u ∈ Ioo (0:ℝ) D, ∀ k ∈ collClasses γ t₀, clusterInertia m k (x u) ≤ γc :=
    fun u hu => hIbd (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2, hDle₂]⟩
  have hsep₀ : ∀ u ∈ Ioo (0:ℝ) E₀, ∀ k ∈ collClasses γ t₀, ClusterSeparatedWeak k (x u) ν :=
    fun u hu => hsepE u ⟨hu.1, lt_of_lt_of_le hu.2 hE₀le⟩
  have hsepT₀ : ∀ u ∈ Ioo (0:ℝ) E₀, ∀ i ∉ collUnion γ t₀, ∀ j ∉ collUnion γ t₀,
      i ≠ j → ν ≤ r (x u) i j :=
    fun u hu => hsepTE u ⟨hu.1, lt_of_lt_of_le hu.2 hE₀le⟩
  have hIk₀ : ∀ u ∈ Ioo (0:ℝ) E₀, ∀ k ∈ collClasses γ t₀, clusterInertia m k (x u) ≤ γc :=
    fun u hu => hIkE u ⟨hu.1, lt_of_lt_of_le hu.2 hE₀le⟩
  have hncE₀ : ∀ u ∈ Ioo (0:ℝ) E₀, WithoutCollisions (x u) := hnc₀
  have hx₀ : ∀ u ∈ Ioo (0:ℝ) E₀, HasDerivAt x (deriv x u) u :=
    fun u hu => hx u ⟨hu.1, lt_of_lt_of_le hu.2 hE₀le⟩
  have hd2₀ : ∀ u ∈ Ioo (0:ℝ) E₀, HasDerivAt (deriv x) (iteratedDeriv 2 x u) u :=
    fun u hu => hd2 u ⟨hu.1, lt_of_lt_of_le hu.2 hE₀le⟩
  have hd2''₀ : ∀ u ∈ Ioo (0:ℝ) E₀, HasDerivAt (deriv x) (deriv (deriv x) u) u :=
    fun u hu => hd2' u ⟨hu.1, lt_of_lt_of_le hu.2 hE₀le⟩
  have hode₀ : ∀ u ∈ Ioo (0:ℝ) E₀, iteratedDeriv 2 x u = ∇_[m] (U m) (x u) :=
    fun u hu => hode u ⟨hu.1, lt_of_lt_of_le hu.2 hE₀le⟩
  have hode''₀ : ∀ u ∈ Ioo (0:ℝ) E₀, deriv (deriv x) u = ∇_[m] (U m) (x u) :=
    fun u hu => hode' u ⟨hu.1, lt_of_lt_of_le hu.2 hE₀le⟩
  -- the sum-level energy bound (its conclusion lives on `(0, D/4) = (0, E₀)`)
  obtain ⟨Ce, hCe0, hDbound⟩ := exists_multiRelEnergy_bound (m := m) (ks := collClasses γ t₀)
    (x := x) (ε := D) (ν := ν) hm hDpos hνpos hne hedj hncE hx hd2' hode' hsepE hsepTE
  -- the sum-level interaction-work bound
  obtain ⟨Cw, hCw0, hWbound⟩ := exists_multiCrossWork_bound (m := m) (ks := collClasses γ t₀)
    (x := x) (ε := E₀) (ν := ν) (γ := γc) hm hE₀pos hνpos hγcpos.le hγmle hsep₀ hIk₀
  -- the outside kinetic energy bound
  have hsepU₀ : ∀ u ∈ Ioo (0:ℝ) E₀, ClusterSeparated (multiUnion (collClasses γ t₀)) (x u) ν :=
    fun u hu => clusterSeparated_multiUnion (hsep₀ u hu) (hsepT₀ u hu)
  obtain ⟨Cout, hCout0, hKout⟩ := exists_multiOutsideKineticSq_bound (m := m)
    (ks := collClasses γ t₀) (x := x) (ε := E₀) (ν := ν) hm hE₀pos hνpos hsepU₀ hnc₀ hode₀ hd2₀
  -- the centre-of-mass kinetic energy bound (conclusion on `(0, E/4)`)
  obtain ⟨Ccm, hCcm0, hKcm⟩ := exists_multiCMKineticSq_bound (m := m) (ks := collClasses γ t₀)
    (x := x) (ε := D) (ν := ν) hm hDpos hνpos hne hsepE hncE hode hd2
  -- energy conservation
  have hH : ∀ u ∈ Ioo (0:ℝ) E₀, energy m x u = energy m x (E₀ / 2) := fun u hu =>
    energy_eq_of_mem_Ioo hmne hx₀ hd2₀ hode₀ hnc₀ hu ⟨by linarith, by linarith⟩
  -- the boundedness of the interaction potential
  have hRest0 : ∀ u ∈ Ioo (0:ℝ) E₀,
      multiRestPotential m (collClasses γ t₀) (x u) ≤ (∑ p ∈ pairFinset N, m p.1 * m p.2) / ν :=
    fun u hu => multiRestPotential_le (fun i => (hm i).le) hνpos hedj (hsep₀ u hu) (hsepT₀ u hu)
  -- the Lagrange--Jacobi identity
  have hLJ : ∀ u ∈ Ioo (0:ℝ) E₀,
      deriv (deriv (fun s : ℝ => multiInertia m (collClasses γ t₀) (x s))) u
        = 4 * multiRelEnergy m (collClasses γ t₀) (x u) (deriv x u)
          + 2 * multiPotential m (collClasses γ t₀) (x u)
          + 2 * multiCrossWork m (collClasses γ t₀) (x u) := fun u hu =>
    deriv_deriv_multiInertia_curve_eq hm hne hu hnc₀ hx₀ hd2₀ hode₀
  -- the inertia tends to `0`
  have hI : Tendsto (fun u : ℝ => multiInertia m (collClasses γ t₀) (x u))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    refine tendsto_multiInertia_zero fun k hk => ?_
    obtain ⟨i, rfl, -⟩ := mem_collClasses.mp hk
    refine tendsto_clusterInertia_collClass_shift (m := m) (γ := γ) (t₀ := t₀) (i₀ := i) ?_ hcontAt
    exact ne_of_gt (clusterMass_pos hm ⟨i, mem_collClass_self γ t₀ i⟩)
  -- the potential diverges
  have hU : Tendsto (fun u : ℝ => multiPotential m (collClasses γ t₀) (x u))
      (𝓝[>] (0:ℝ)) atTop :=
    tendsto_multiPotential_atTop hm hksne hne2 hncEv hI
  -- the total inertia is positive
  have hfpos : ∀ u ∈ Ioo (0:ℝ) E₀, 0 < multiInertia m (collClasses γ t₀) (x u) :=
    fun u hu => multiInertia_pos_of_withoutCollisions hm hksne hne2 (hnc₀ u hu)
  -- a common constant for the three bounded quantities
  set R : ℝ := (∑ p ∈ pairFinset N, m p.1 * m p.2) / ν with hRdef
  set C : ℝ := max (max Ce Cw) R + 1 with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
      (le_add_of_nonneg_left
        (le_trans hCe0 (le_trans (le_max_left Ce Cw) (le_max_left (max Ce Cw) R))))
  have hCeC : Ce ≤ C :=
    le_trans (le_trans (le_max_left Ce Cw) (le_max_left (max Ce Cw) R))
      (le_add_of_nonneg_right (by norm_num))
  have hCwC : Cw ≤ C :=
    le_trans (le_trans (le_max_right Ce Cw) (le_max_left (max Ce Cw) R))
      (le_add_of_nonneg_right (by norm_num))
  have hRC : R ≤ C :=
    le_trans (le_max_right (max Ce Cw) R) (le_add_of_nonneg_right (by norm_num))
  have hDbound' : ∀ u ∈ Ioo (0:ℝ) E₀,
      |multiRelEnergy m (collClasses γ t₀) (x u) (deriv x u)| ≤ C :=
    fun u hu => le_trans (hDbound u hu) hCeC
  have hWbound' : ∀ u ∈ Ioo (0:ℝ) E₀, |multiCrossWork m (collClasses γ t₀) (x u)| ≤ C :=
    fun u hu => le_trans (hWbound u hu) hCwC
  have hRest0 : ∀ u ∈ Ioo (0:ℝ) E₀,
      multiRestPotential m (collClasses γ t₀) (x u) ≤ (∑ p ∈ pairFinset N, m p.1 * m p.2) / ν :=
    fun u hu => multiRestPotential_le (fun i => (hm i).le) hνpos hedj (hsep₀ u hu) (hsepT₀ u hu)
  have hRest : ∀ u ∈ Ioo (0:ℝ) E₀, multiRestPotential m (collClasses γ t₀) (x u) ≤ C :=
    fun u hu => le_trans (hRest0 u hu) (by rw [← hRdef] at *; exact hRC)
  -- the two eventual interfaces
  have hevKin := eventually_kinetic_le_multiSecondDeriv (m := m) (ks := collClasses γ t₀)
    (x := x) (ε := E₀) (C := C) hE₀pos hCpos hH hRest hDbound' hWbound' hLJ hU
  have hevP1 := eventually_one_le_multiSecondDeriv (m := m) (ks := collClasses γ t₀)
    (x := x) (ε := E₀) (C := C) hE₀pos hCpos hDbound' hWbound' hLJ hU
  -- shrink to pointwise statements on an interval
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := exists_forall_Ioo_of_eventually_nhdsGT hevKin
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := exists_forall_Ioo_of_eventually_nhdsGT hevP1
  set E₁ : ℝ := min (min δ₁ δ₂) E₀ with hE₁def
  have hE₁pos : 0 < E₁ := by rw [hE₁def]; exact lt_min (lt_min hδ₁pos hδ₂pos) hE₀pos
  have hE₁le : E₁ ≤ E₀ := by rw [hE₁def]; exact min_le_right _ _
  have hE₁δ₁ : E₁ ≤ δ₁ := by
    rw [hE₁def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hE₁δ₂ : E₁ ≤ δ₂ := by
    rw [hE₁def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hmem : ∀ u ∈ Ioo (0:ℝ) E₁, u ∈ Ioo (0:ℝ) E₀ :=
    fun u hu => ⟨hu.1, lt_of_lt_of_le hu.2 hE₁le⟩
  have hKin : ∀ u ∈ Ioo (0:ℝ) E₁, kinetic m (deriv x u)
      ≤ 2 * deriv (deriv (fun s : ℝ => multiInertia m (collClasses γ t₀) (x s))) u :=
    fun u hu => hδ₁ u ⟨hu.1, lt_of_lt_of_le hu.2 hE₁δ₁⟩
  have hP1 : ∀ u ∈ Ioo (0:ℝ) E₁,
      1 ≤ deriv (deriv (fun s : ℝ => multiInertia m (collClasses γ t₀) (x s))) u :=
    fun u hu => hδ₂ u ⟨hu.1, lt_of_lt_of_le hu.2 hE₁δ₂⟩
  have hPerr : ∀ u ∈ Ioo (0:ℝ) E₁, 2 * multiPotential m (collClasses γ t₀) (x u)
      ≤ deriv (deriv (fun s : ℝ => multiInertia m (collClasses γ t₀) (x s))) u + 6 * C :=
    fun u hu => two_multiPotential_le_multiSecondDeriv (hDbound' u (hmem u hu))
      (hWbound' u (hmem u hu)) (hLJ u (hmem u hu))
  -- the sum-level kinetic bound
  have hfin' : ∃ Ck : ℝ, 0 < Ck ∧ ∀ᶠ u in 𝓝[>] (0:ℝ),
      kinetic m (deriv x u) ≤ Ck * u ^ (-((2:ℝ)/3)) :=
    multiInertia_kinetic_bound (m := m) (ks := collClasses γ t₀) (x := x) (ε := E₁) (ν := ν)
      (C := C) (cU := 2) (Cout := Cout) (Ccm2 := Ccm) hm hγmle hγcpos hne hne2 hedj hE₁pos hCpos
      hνpos (by norm_num) (fun u hu => hnc₀ u (hmem u hu)) (fun u hu => hx₀ u (hmem u hu))
      (fun u hu => hd2''₀ u (hmem u hu))
      (fun u hu => hasDerivAt_deriv_deriv_of_solution hmne (hmem u hu) hx₀ hd2₀ hnc₀ hode₀)
      (fun u hu => hode₀ u (hmem u hu)) (fun u hu => hKout u (hmem u hu))
      (fun u hu => hKcm u (hmem u hu)) (fun u hu => hDbound' u (hmem u hu))
      (fun u hu => hWbound' u (hmem u hu)) (fun u hu => hsep₀ u (hmem u hu))
      (fun u hu => hIk₀ u (hmem u hu)) hKin hPerr hP1
      (fun u hu => hfpos u (hmem u hu)) hI
  obtain ⟨Ck, hCkpos, hCk⟩ := hfin'
  exact ⟨Ck, hCkpos, hCk⟩

end Submission.NBody
