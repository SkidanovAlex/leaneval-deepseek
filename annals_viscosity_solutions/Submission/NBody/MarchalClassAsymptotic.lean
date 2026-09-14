import Submission.NBody.MarchalReflectMinimizer
import Submission.NBody.MarchalClusterAsymptotic
import Submission.NBody.MarchalCollisionSolutionData
import Submission.NBody.MarchalIsolatedCollision

/-!
# Sundman's first-order asymptotics for a collision class of a minimiser

The variation of the standard-variation argument (the endgame of the Marchal chapter) needs, at an
isolated collision time `t₀` of a minimiser `γ`, the first-order Sundman asymptotics

    `I_k(x(t₀+t)) ∼ κ t^{4/3}`   (`t → 0⁺`)

for a collision class `k`.  The analytic inputs of `clusterInertia_asymptotic` are the boundedness
of the centre-of-mass-relative energy (Ferrario--Terracini `lemma:bounded_energy`) and of the
interaction work, both of which are supplied here from the geometry on the collision-free side:

* `exists_relEnergy_bound_of_kinetic` — the energy bound, from the sum-level kinetic bound
  `K ≤ C u^{-2/3}` of `MarchalKineticBoundAtCollision` (Ferrario--Terracini `lemma:K_bound`);
* the positional interaction-work bound `abs_crossWork_cmRel_le`, using the one-sided separation of
  the class.

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

/-- **Sundman's asymptotics for a collision class of a minimiser.**  Let `γ` be an `h`-minimiser on
`[a,b]` with an isolated collision at the interior time `t₀`, and let `k` be a cluster with at least
two bodies which fully collides at `t₀` and is separated from its complement on the collision-free
side.  Then there is `κ > 0` with `I_k(γ(t₀+t))/t^{4/3} → κ` as `t → 0⁺`. -/
theorem clusterInertia_asymptotic_of_collision {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b t₀ ε ν : ℝ} {k : Finset (Fin N)}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b) (hk2 : 2 ≤ k.card)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) (hε : 0 < ε) (hεb : t₀ + ε ≤ b)
    (hnc : ∀ t ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ t))
    (hν : 0 < ν) (hsepw : ∀ t ∈ Ioo t₀ (t₀ + ε), ClusterSeparatedWeak k (γ t) ν)
    (hI0 : clusterInertia m k (γ t₀) = 0) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun t : ℝ => clusterInertia m k (γ (t₀ + t)) / t ^ ((4:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ) := by
  classical
  have hkne : k.Nonempty := Finset.card_pos.mp (by omega)
  -- the collision at `t₀`
  have hcoll : ¬ WithoutCollisions (γ t₀) := by
    intro hnc'
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < k.card)
    have h1 : γ t₀ i = γ t₀ j := (clusterInertia_eq_zero_iff hm k (γ t₀)).mp hI0 i hi j hj
    exact (hnc' i j hij) (by rw [r_eq_norm_sub, h1, sub_self, norm_zero])
  -- the working interval
  set D : ℝ := min ε 1 with hDdef
  have hDpos : 0 < D := lt_min hε one_pos
  have hDle : D ≤ ε := min_le_left _ _
  have hDb : t₀ + D ≤ b := by linarith
  let x : ℝ → EN E N := fun s => γ (t₀ + s)
  have hncD : ∀ u ∈ Ioo (0:ℝ) D, WithoutCollisions (x u) := fun u hu =>
    hnc (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2, hDle]⟩
  have hncD' : ∀ t ∈ Ioo t₀ (t₀ + D), WithoutCollisions (γ t) := fun t ht =>
    hnc t ⟨ht.1, by linarith [ht.2, hDle]⟩
  -- the Newton data on the shifted curve
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
  have hd2 : ∀ u ∈ Ioo (0:ℝ) D, HasDerivAt (deriv x) (deriv (deriv x) u) u := fun u hu => by
    have h1 : HasDerivAt (fun s : ℝ => deriv γ (t₀ + s)) (iteratedDeriv 2 γ (t₀ + u)) u :=
      (hnewton u hu).2.1.comp_const_add t₀ u
    have h2 : deriv x = fun s : ℝ => deriv γ (t₀ + s) := by
      funext s; exact deriv_shiftCurve_eq t₀ s
    rw [h2]
    have h3 : iteratedDeriv 2 x u = iteratedDeriv 2 γ (t₀ + u) :=
      iteratedDeriv_two_shiftCurve_eq t₀ u
    have h3 : deriv (fun s : ℝ => deriv γ (t₀ + s)) u = iteratedDeriv 2 γ (t₀ + u) := by
      rw [deriv_comp_const_add, iteratedDeriv_two_eq_deriv_deriv]
    rw [h3]
    exact h1
  have hode : ∀ u ∈ Ioo (0:ℝ) D, deriv (deriv x) u = ∇_[m] (U m) (x u) := fun u hu => by
    have h2 : deriv x = fun s : ℝ => deriv γ (t₀ + s) := by
      funext s; exact deriv_shiftCurve_eq t₀ s
    rw [h2, deriv_comp_const_add, ← iteratedDeriv_two_eq_deriv_deriv]
    exact (hnewton u hu).2.2
  -- the separation and the inertia limit
  have hsepwD : ∀ u ∈ Ioo (0:ℝ) D, ClusterSeparatedWeak k (x u) ν := fun u hu =>
    hsepw (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2, hDle]⟩
  have hcontAt : ContinuousAt γ t₀ := by
    have hcont : ContinuousOn γ (Icc a b) := by
      have h := hac.continuousOn
      rwa [uIcc_of_le hab.le] at h
    exact hcont.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hI : Tendsto (fun u : ℝ => clusterInertia m k (x u)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have hc : Tendsto (fun u : ℝ => γ (t₀ + u)) (𝓝 (0:ℝ)) (𝓝 (γ t₀)) := by
      have h1 : Tendsto (fun u : ℝ => t₀ + u) (𝓝 (0:ℝ)) (𝓝 t₀) := by
        have h2 : Tendsto (fun _ : ℝ => t₀) (𝓝 (0:ℝ)) (𝓝 t₀) := tendsto_const_nhds
        have h3 : Tendsto (fun u : ℝ => u) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := tendsto_id
        simpa using h2.add h3
      exact hcontAt.tendsto.comp h1
    have h1 : Tendsto (fun u : ℝ => clusterInertia m k (γ (t₀ + u))) (nhdsWithin (0:ℝ) (Ioi 0))
        (nhds (clusterInertia m k (γ t₀))) :=
      ((continuous_clusterInertia m k).continuousAt.tendsto.comp hc).mono_left nhdsWithin_le_nhds
    simpa [hI0] using h1
  -- the kinetic bound (FT `lemma:K_bound`)
  obtain ⟨Ck, hCkpos, hkin⟩ := exists_kinetic_bound_at_collision (m := m) (h := h) (γ := γ)
    (a := a) (b := b) (t₀ := t₀) (ε := D) hm hh hab hac hmin hfin ht₀ hcoll hDpos hDb hncD'
  have hkin' : ∀ᶠ u in 𝓝[>] (0:ℝ),
      kinetic m (deriv x u) ≤ Ck * u ^ (-((2:ℝ)/3)) := by
    filter_upwards [hkin] with u hu
    show kinetic m (deriv (fun s : ℝ => γ (t₀ + s)) u) ≤ Ck * u ^ (-((2:ℝ)/3))
    rw [deriv_shiftCurve_eq t₀ u] at hu ⊢
    exact hu
  -- the relative-energy bound (FT `lemma:bounded_energy`)
  obtain ⟨Ce, hCepos, δ, hδpos, hδle, henergy⟩ :=
    exists_relEnergy_bound_of_kinetic (m := m) (k := k) (x := x) (ε := D) (ν := ν) (Ck := Ck)
      hm hkne hDpos hν hCkpos hncD hx hd2 hode hsepwD hkin'
  set δ' : ℝ := min δ (D / 2) with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδpos (by linarith)
  have hδ'le : δ' ≤ D := le_trans (min_le_right _ _) (by linarith)
  have hδ'leδ : δ' ≤ δ := le_trans (min_le_left _ _) le_rfl
  -- the interaction-work bound
  set Cw : ℝ := 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) with hCwdef
  have hCw0 : 0 ≤ Cw := by
    rw [hCwdef]
    have h1 : 0 ≤ (ν⁻¹) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
    have h3 : 0 ≤ Real.sqrt (clusterMass m k) := Real.sqrt_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3
  -- shrink so that `I_k ≤ 1` on the interval
  have hevI : ∀ᶠ u in nhdsWithin (0:ℝ) (Ioi 0), clusterInertia m k (x u) < 1 :=
    hI.eventually (isOpen_Iio.mem_nhds one_pos)
  rw [eventually_nhdsWithin_iff] at hevI
  obtain ⟨D₁, hD₁pos, hD₁⟩ := Metric.eventually_nhds_iff_ball.mp hevI
  set δ'' : ℝ := min δ' (min D₁ (D / 2)) with hδ''def
  have hδ''pos : 0 < δ'' := lt_min hδ'pos (lt_min hD₁pos (by linarith))
  have hδ''le : δ'' ≤ δ' := le_trans (min_le_left _ _) le_rfl
  have hδ''le₁ : δ'' ≤ D₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ''leD : δ'' ≤ D := le_trans hδ''le hδ'le
  have hIle : ∀ u ∈ Ioo (0:ℝ) δ'', clusterInertia m k (x u) ≤ 1 := by
    intro u hu
    refine le_of_lt (hD₁ u ?_ hu.1)
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu.1]
    exact lt_of_lt_of_le hu.2 hδ''le₁
  have hW : ∀ u ∈ Ioo (0:ℝ) δ'',
      |crossWork m k (x u) (cmRel m k (x u))| ≤ Cw := by
    intro u hu
    have huD : u ∈ Ioo (0:ℝ) D := ⟨hu.1, lt_of_lt_of_le hu.2 hδ''leD⟩
    have h1 := abs_crossWork_cmRel_le (m := m) (k := k) (x := x u) (v := x u) (ν := ν)
      hm hν (hsepwD u huD)
    have h2 : clusterRelKinetic m k (x u) = clusterInertia m k (x u) :=
      clusterRelKinetic_eq_clusterInertia m k (x u)
    rw [h2] at h1
    refine le_trans h1 ?_
    rw [hCwdef]
    have hs : Real.sqrt (clusterInertia m k (x u)) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (hIle u hu)
    exact mul_le_of_le_one_right (by positivity) hs
  -- the energy bound on the final interval
  have hE : ∀ u ∈ Ioo (0:ℝ) δ'',
      |clusterRelEnergy m k (x u) (deriv x u)| ≤ |Ce| + 1 := by
    intro u hu
    have h1 := henergy u ⟨hu.1, lt_of_lt_of_le hu.2
      (le_trans hδ''le hδ'leδ)⟩
    linarith [le_abs_self Ce]
  -- apply Sundman's theorem
  have hnc'' : ∀ u ∈ Ioo (0:ℝ) δ'', WithoutCollisions (x u) :=
    fun u hu => hncD u ⟨hu.1, lt_of_lt_of_le hu.2 hδ''leD⟩
  have hx'' : ∀ u ∈ Ioo (0:ℝ) δ'', HasDerivAt x (deriv x u) u :=
    fun u hu => hx u ⟨hu.1, lt_of_lt_of_le hu.2 hδ''leD⟩
  have hd2'' : ∀ u ∈ Ioo (0:ℝ) δ'', HasDerivAt (deriv x) (deriv (deriv x) u) u :=
    fun u hu => hd2 u ⟨hu.1, lt_of_lt_of_le hu.2 hδ''leD⟩
  have hode'' : ∀ u ∈ Ioo (0:ℝ) δ'', deriv (deriv x) u = ∇_[m] (U m) (x u) :=
    fun u hu => hode u ⟨hu.1, lt_of_lt_of_le hu.2 hδ''leD⟩
  have hd2it : ∀ u ∈ Ioo (0:ℝ) δ'', HasDerivAt (deriv x) (iteratedDeriv 2 x u) u := fun u hu =>
    (hd2'' u hu).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x u).symm
  have hodeit : ∀ u ∈ Ioo (0:ℝ) δ'', iteratedDeriv 2 x u = ∇_[m] (U m) (x u) :=
    fun u hu => (iteratedDeriv_two_eq_deriv_deriv x u).trans (hode'' u hu)
  have hI'' : Tendsto (fun u : ℝ => clusterInertia m k (x u)) (nhdsWithin (0:ℝ) (Ioi 0))
      (nhds 0) := hI
  have hE' : ∀ u ∈ Ioo (0:ℝ) δ'',
      |clusterRelEnergy m k (x u) (deriv x u)| ≤ |Ce| + 1 + Cw :=
    fun u hu => le_trans (hE u hu) (le_add_of_nonneg_right hCw0)
  have hW' : ∀ u ∈ Ioo (0:ℝ) δ'',
      |crossWork m k (x u) (cmRel m k (x u))| ≤ |Ce| + 1 + Cw :=
    fun u hu => le_trans (hW u hu)
      (le_add_of_nonneg_left (add_nonneg (abs_nonneg Ce) zero_le_one))
  obtain ⟨κ, hκpos, hκ⟩ := clusterInertia_asymptotic (m := m) (k := k) (x := x) (ε := δ'')
    (C := |Ce| + 1 + Cw) hm hk2 hδ''pos (by positivity) hnc'' hE' hW' hx'' hd2it hodeit hI''
  exact ⟨κ, hκpos, hκ⟩

/-! ## The asymptotics on the left of the collision time -/

/-- **Sundman's asymptotics for a collision class, on the left of the collision time.**  The
reflection of `γ` at `t₀` turns the left side into a right side, so this is a direct consequence of
`clusterInertia_asymptotic_of_collision` applied to `reflectCurve γ t₀`. -/
theorem clusterInertia_asymptotic_of_collision_left {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b t₀ ε ν : ℝ} {k : Finset (Fin N)}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b) (hk2 : 2 ≤ k.card)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) (hε : 0 < ε) (hεa : a ≤ t₀ - ε)
    (hnc : ∀ t ∈ Ioo (t₀ - ε) t₀, WithoutCollisions (γ t))
    (hν : 0 < ν) (hsepw : ∀ t ∈ Ioo (t₀ - ε) t₀, ClusterSeparatedWeak k (γ t) ν)
    (hI0 : clusterInertia m k (γ t₀) = 0) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun t : ℝ => clusterInertia m k (γ (t₀ - t)) / t ^ ((4:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ) := by
  -- the reflected curve, as a curve on `[t₀ - b, t₀ - a]`
  have hmin' : IsHMinimizer m h (reflectCurve γ t₀) (t₀ - b) (t₀ - a) :=
    isHMinimizer_reflectCurve hab.le hmin
  have hac' : AbsolutelyContinuousOnInterval (reflectCurve γ t₀) (t₀ - b) (t₀ - a) :=
    absolutelyContinuousOnInterval_reflectCurve hac
  have ht₀' : (0:ℝ) ∈ Ioo (t₀ - b) (t₀ - a) := ⟨by linarith [ht₀.2], by linarith [ht₀.1]⟩
  have hεb' : (0:ℝ) + ε ≤ t₀ - a := by linarith
  have hnc' : ∀ t ∈ Ioo (0:ℝ) (0 + ε), WithoutCollisions (reflectCurve γ t₀ t) := by
    intro t ht
    have h1 : t₀ - t ∈ Ioo (t₀ - ε) t₀ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa [reflectCurve] using hnc (t₀ - t) h1
  have hsepw' : ∀ t ∈ Ioo (0:ℝ) (0 + ε), ClusterSeparatedWeak k (reflectCurve γ t₀ t) ν := by
    intro t ht
    have h1 : t₀ - t ∈ Ioo (t₀ - ε) t₀ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa [reflectCurve] using hsepw (t₀ - t) h1
  have hI0' : clusterInertia m k (reflectCurve γ t₀ 0) = 0 := by
    simpa [reflectCurve] using hI0
  obtain ⟨κ, hκpos, hκ⟩ := clusterInertia_asymptotic_of_collision (m := m) (h := h)
    (γ := reflectCurve γ t₀) (a := t₀ - b) (b := t₀ - a) (t₀ := 0) (ε := ε) (ν := ν) (k := k)
    hm hh (by linarith) hk2 hac' hmin' hfin ht₀' hε hεb' hnc' hν hsepw' hI0'
  refine ⟨κ, hκpos, ?_⟩
  simpa only [zero_add, reflectCurve] using hκ

/-- **Sundman's asymptotics for a collision class, on both sides of the collision time.** -/
theorem clusterInertia_asymptotic_of_collision_two_sided {m : Fin N → ℝ} {h : ℝ}
    {γ : ℝ → EN E N} {a b t₀ ε ν : ℝ} {k : Finset (Fin N)}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b) (hk2 : 2 ≤ k.card)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) (hε : 0 < ε) (hεb : t₀ + ε ≤ b) (hεa : a ≤ t₀ - ε)
    (hncR : ∀ t ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ t))
    (hncL : ∀ t ∈ Ioo (t₀ - ε) t₀, WithoutCollisions (γ t))
    (hν : 0 < ν) (hsepwR : ∀ t ∈ Ioo t₀ (t₀ + ε), ClusterSeparatedWeak k (γ t) ν)
    (hsepwL : ∀ t ∈ Ioo (t₀ - ε) t₀, ClusterSeparatedWeak k (γ t) ν)
    (hI0 : clusterInertia m k (γ t₀) = 0) :
    (∃ κ : ℝ, 0 < κ ∧ Tendsto (fun t : ℝ => clusterInertia m k (γ (t₀ + t)) / t ^ ((4:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ)) ∧
    (∃ κ : ℝ, 0 < κ ∧ Tendsto (fun t : ℝ => clusterInertia m k (γ (t₀ - t)) / t ^ ((4:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ)) :=
  ⟨clusterInertia_asymptotic_of_collision hm hh hab hk2 hac hmin hfin ht₀ hε hεb hncR hν
      hsepwR hI0,
    clusterInertia_asymptotic_of_collision_left hm hh hab hk2 hac hmin hfin ht₀ hε hεa hncL hν
      hsepwL hI0⟩


end Submission.NBody
