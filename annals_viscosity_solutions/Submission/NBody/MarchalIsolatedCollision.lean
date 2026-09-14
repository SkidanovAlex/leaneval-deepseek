import Submission.NBody.MarchalCollClass
import Submission.NBody.MarchalCollPartition
import Submission.NBody.MarchalClusterPlumbing
import Submission.NBody.MarchalSperner
import Submission.NBody.MarchalMultiEnergyBound
import Submission.NBody.MarchalCollisionSolutionData
import Submission.NBody.EnergyAe
import Submission.NBody.Minimizer
import Submission.Commons.Analysis.Interval.interior_argmax_of_zero_ends
import Submission.Commons.Analysis.Calculus.deriv_deriv_nonpos_of_localMax

/-!
# A locally minimal collision is isolated (Ferrario--Terracini `coro:loc_min`)

This file proves the geometric heart of the Marchal chapter: for an action-minimising curve, a
collision time which realises the maximal number of colliding pairs in a neighbourhood is
**isolated** (no other collision time nearby).

The two ingredients are

* the **maximality/continuity** argument: for `t` close to `t₁`, every pair colliding at `t` also
  collides at `t₁` (continuity); choosing `t₁` to maximise the number of colliding pairs makes this
  inclusion an equality, so the collision classes of `t` and of `t₁` coincide.  Consequently a
  colliding cluster `k` at `t₁` collides at every nearby collision time;

* the **Rolle--Sperner** argument, in the form that needs *no* energy bound: at an interior maximum
  of `F = I_k ∘ γ` one has `F'' ≤ 0`, while the Lagrange--Jacobi identity
  `F'' = 4E + 2U + 2W` together with `E = K/2 - U ≥ -U` and the *positional* bound
  `|W| ≤ c_W √F` gives `U ≤ c_W √F`; Sperner's a priori bound `c/√F ≤ U` then forces
  `F ≥ c/c_W`, so a "sandwich" of two zeros of `F` with positive values in between cannot shrink to
  the collision time.

Everything in this file is fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## 1. The maximal number of colliding pairs -/

/-- The pairs of distinct bodies which collide at the time `t`. -/
noncomputable def collPairs (γ : ℝ → EN E N) (t : ℝ) : Finset (Fin N × Fin N) := by
  classical
  exact (Finset.univ.product Finset.univ).filter (fun p => p.1 ≠ p.2 ∧ γ t p.1 = γ t p.2)

lemma mem_collPairs {γ : ℝ → EN E N} {t : ℝ} {p : Fin N × Fin N} :
    p ∈ collPairs γ t ↔ p.1 ≠ p.2 ∧ γ t p.1 = γ t p.2 := by
  classical
  simp [collPairs]

lemma collPairs_card_le (γ : ℝ → EN E N) (t : ℝ) : (collPairs γ t).card ≤ N * N := by
  classical
  calc (collPairs γ t).card
      ≤ ((Finset.univ : Finset (Fin N)).product Finset.univ).card :=
        Finset.card_le_card (fun p hp => (Finset.mem_filter.mp hp).1)
    _ = N * N := by simp [Finset.card_product]

/-- **Transfer of collisions along a continuous curve.**  Close to a point of continuity of `γ`,
every pair which collides at `t` also collides at `t₁`. -/
lemma exists_collPairs_subset_of_continuousWithinAt {γ : ℝ → EN E N} {c d t₁ : ℝ}
    (hcont : ContinuousOn γ (Icc c d)) (ht₁ : t₁ ∈ Icc c d) :
    ∃ ε > 0, ∀ t ∈ Icc c d, |t - t₁| < ε → collPairs γ t ⊆ collPairs γ t₁ := by
  classical
  set P : Finset (Fin N × Fin N) :=
    (Finset.univ.product Finset.univ).filter (fun p => γ t₁ p.1 ≠ γ t₁ p.2) with hP
  have hev : ∀ᶠ t in 𝓝[Icc c d] t₁, ∀ p ∈ P, γ t p.1 ≠ γ t p.2 := by
    refine (Finset.eventually_all P).mpr fun p hp => ?_
    have hp' : γ t₁ p.1 ≠ γ t₁ p.2 := (Finset.mem_filter.mp hp).2
    have h1 : ContinuousWithinAt (fun t : ℝ => γ t p.1) (Icc c d) t₁ :=
      ((PiLp.continuous_apply 2 (fun _ : Fin N => E) p.1).continuousAt).comp_continuousWithinAt
        (hcont.continuousWithinAt ht₁)
    have h2 : ContinuousWithinAt (fun t : ℝ => γ t p.2) (Icc c d) t₁ :=
      ((PiLp.continuous_apply 2 (fun _ : Fin N => E) p.2).continuousAt).comp_continuousWithinAt
        (hcont.continuousWithinAt ht₁)
    have h3 : ∀ᶠ t in 𝓝[Icc c d] t₁, γ t p.1 - γ t p.2 ≠ 0 :=
      (h1.sub h2).tendsto.eventually_ne (sub_ne_zero.mpr hp')
    filter_upwards [h3] with t ht
    exact sub_ne_zero.mp ht
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨ε, hεpos, fun t ht hlt => ?_⟩
  intro p hp
  rw [mem_collPairs] at hp ⊢
  refine ⟨hp.1, ?_⟩
  by_contra hne
  have hpP : p ∈ P :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
  have hball : t ∈ Metric.ball t₁ ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact hlt
  exact (hε ⟨hball, ht⟩ p hpP) hp.2

/-! ## 2. Vanishing inertia means total collision -/

/-- The inertia of a cluster vanishes exactly when all its bodies occupy the same point. -/
lemma clusterInertia_eq_zero_iff {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) (k : Finset (Fin N))
    (x : EN E N) : clusterInertia m k x = 0 ↔ ∀ i ∈ k, ∀ j ∈ k, x i = x j := by
  constructor
  · intro h i hi j hj
    rw [clusterInertia, Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (hm i).le (sq_nonneg _))] at h
    have h1 : x i = clusterCM m k x := by
      have h2 := h i hi
      have h3 : ‖x i - clusterCM m k x‖ ^ 2 = 0 := by
        have := mul_eq_zero.mp h2
        rcases this with h4 | h4
        · exact absurd h4 (ne_of_gt (hm i))
        · exact h4
      have h5 : ‖x i - clusterCM m k x‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
      exact sub_eq_zero.mp (norm_eq_zero.mp h5)
    have h6 : x j = clusterCM m k x := by
      have h2 := h j hj
      have h3 : ‖x j - clusterCM m k x‖ ^ 2 = 0 := by
        have := mul_eq_zero.mp h2
        rcases this with h4 | h4
        · exact absurd h4 (ne_of_gt (hm j))
        · exact h4
      have h5 : ‖x j - clusterCM m k x‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
      exact sub_eq_zero.mp (norm_eq_zero.mp h5)
    rw [h1, h6]
  · intro h
    rcases Finset.eq_empty_or_nonempty k with hem | hne
    · rw [hem, clusterInertia, Finset.sum_empty]
    · have hmk : clusterMass m k ≠ 0 := ne_of_gt (clusterMass_pos hm hne)
      obtain ⟨i₀, hi₀⟩ := hne
      have hcm : clusterCM m k x = x i₀ := clusterCM_eq_of_all_eq hmk (fun i hi => h i hi i₀ hi₀)
      rw [clusterInertia, hcm]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [h i hi i₀ hi₀, sub_self, norm_zero]
      ring

/-! ## 3. The Rolle--Sperner contradiction -/

/-- **The Rolle--Sperner contradiction.**  If `F = I_k ∘ γ` is continuous on `W`, solves Newton's
equations (and is collision free) wherever it is positive, if the Sperner bound `c/√F ≤ U_k`, the
*positional* bound `|W_k| ≤ c_W √F` and a lower bound `E ≥ -C₁` for the relative energy hold on
`{F > 0}`, and if `F < θ²` on `[a,b]` for a `θ` with `(2C₁ + c_W + 1)θ ≤ c`, then two zeros of `F`
at the ends of `[a,b]` with a positive value in between are impossible. -/
theorem false_of_sandwich_sperner {m : Fin N → ℝ} {k : Finset (Fin N)} {γ : ℝ → EN E N}
    {W : Set ℝ} {a b cS cW C₁ θ : ℝ} (hm : ∀ i, 0 < m i) (hkne : k.Nonempty)
    (hab : a < b) (habW : Icc a b ⊆ W)
    (hcont : ContinuousOn (fun t : ℝ => clusterInertia m k (γ t)) W)
    (ha : clusterInertia m k (γ a) = 0) (hb : clusterInertia m k (γ b) = 0)
    (hpos : ∃ x ∈ Ioo a b, 0 < clusterInertia m k (γ x))
    (hnc : ∀ t ∈ W, 0 < clusterInertia m k (γ t) → WithoutCollisions (γ t))
    (hsol : ∀ t ∈ W, 0 < clusterInertia m k (γ t) →
      (∀ᶠ s in 𝓝 t, HasDerivAt γ (deriv γ s) s) ∧
      HasDerivAt (deriv γ) (iteratedDeriv 2 γ t) t ∧
      iteratedDeriv 2 γ t = ∇_[m] (U m) (γ t))
    (hcS : 0 < cS)
    (hSperner : ∀ t ∈ W, 0 < clusterInertia m k (γ t) →
      cS / Real.sqrt (clusterInertia m k (γ t)) ≤ clusterPotential m k (γ t))
    (hcW : 0 < cW)
    (hW : ∀ t ∈ W, 0 < clusterInertia m k (γ t) →
      |crossWork m k (γ t) (cmRel m k (γ t))| ≤ cW * Real.sqrt (clusterInertia m k (γ t)))
    (hc1 : 0 ≤ C₁)
    (hE : ∀ t ∈ W, 0 < clusterInertia m k (γ t) →
      -C₁ ≤ clusterRelEnergy m k (γ t) (deriv γ t))
    (hθpos : 0 < θ) (hθ1 : θ ≤ 1) (hθ : (2 * C₁ + cW + 1) * θ ≤ cS)
    (hsmall : ∀ t ∈ Icc a b, clusterInertia m k (γ t) < θ ^ 2) : False := by
  classical
  set F : ℝ → ℝ := fun t => clusterInertia m k (γ t) with hF
  obtain ⟨t, ht, hmax, -⟩ :=
    Commons.Analysis.Interval.interior_argmax_of_zero_ends hab (hcont.mono habW) ha hb hpos
  have hFt : 0 < clusterInertia m k (γ t) := by
    obtain ⟨x, hx, hfx⟩ := hpos
    exact lt_of_lt_of_le hfx (hmax x (Ioo_subset_Icc_self hx))
  have htW : t ∈ W := habW (Ioo_subset_Icc_self ht)
  obtain ⟨hxev, hd2γ, hode⟩ := hsol t htW hFt
  have hd1 : HasDerivAt F (deriv F t) t := hasDerivAt_clusterInertia_curve hxev
  have hd2 : HasDerivAt (deriv F) (deriv (deriv F) t) t :=
    hasDerivAt_deriv_clusterInertia_curve hxev
      (hd2γ.congr_deriv (iteratedDeriv_two_eq_deriv_deriv γ t))
  have hloc : IsLocalMax F t := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
    exact hmax y (Ioo_subset_Icc_self hy)
  have hzero : deriv F t = 0 := hloc.deriv_eq_zero
  have hsecond : deriv (deriv F) t ≤ 0 :=
    Commons.Analysis.Calculus.deriv_deriv_nonpos_of_localMax (f := F)
      (hd1.congr_deriv hzero) hd2 hloc
  -- the Lagrange--Jacobi identity at the maximum
  have hLJ : deriv (deriv F) t
      = 4 * clusterRelEnergy m k (γ t) (deriv γ t) + 2 * clusterPotential m k (γ t)
        + 2 * crossWork m k (γ t) (cmRel m k (γ t)) :=
    deriv_deriv_clusterInertia_curve_eq hm hkne (hnc t htW hFt) hxev hd2γ hode
  rw [hLJ] at hsecond
  -- the lower bounds
  have hE' := hE t htW hFt
  have hWt := hW t htW hFt
  have hWlow : -cW * Real.sqrt (clusterInertia m k (γ t))
      ≤ crossWork m k (γ t) (cmRel m k (γ t)) := by
    have h1 := neg_abs_le (crossWork m k (γ t) (cmRel m k (γ t)))
    linarith [hWt, h1]
  have hkey : 2 * clusterPotential m k (γ t)
      ≤ 4 * C₁ + 2 * cW * Real.sqrt (clusterInertia m k (γ t)) := by
    linarith [hsecond, hE', hWlow]
  -- Sperner times the square root
  have hroot : 0 < Real.sqrt (clusterInertia m k (γ t)) := Real.sqrt_pos.mpr hFt
  have hsq : Real.sqrt (clusterInertia m k (γ t)) * Real.sqrt (clusterInertia m k (γ t))
      = clusterInertia m k (γ t) := by
    rw [← sq, Real.sq_sqrt (clusterInertia_nonneg (fun i => (hm i).le) k (γ t))]
  have hsperner := hSperner t htW hFt
  have hkey' : cS ≤ 2 * C₁ * Real.sqrt (clusterInertia m k (γ t))
      + cW * clusterInertia m k (γ t) := by
    have h1 : cS / Real.sqrt (clusterInertia m k (γ t)) * Real.sqrt (clusterInertia m k (γ t))
        ≤ (2 * C₁ + cW * Real.sqrt (clusterInertia m k (γ t)))
          * Real.sqrt (clusterInertia m k (γ t)) := by
      refine mul_le_mul_of_nonneg_right ?_ hroot.le
      linarith [hsperner, hkey]
    have h2 : cS / Real.sqrt (clusterInertia m k (γ t)) * Real.sqrt (clusterInertia m k (γ t))
        = cS := by field_simp
    have h3 : (2 * C₁ + cW * Real.sqrt (clusterInertia m k (γ t)))
          * Real.sqrt (clusterInertia m k (γ t))
        = 2 * C₁ * Real.sqrt (clusterInertia m k (γ t)) + cW * clusterInertia m k (γ t) := by
      have h4 : cW * Real.sqrt (clusterInertia m k (γ t)) * Real.sqrt (clusterInertia m k (γ t))
          = cW * clusterInertia m k (γ t) := by rw [mul_assoc, hsq]
      rw [add_mul, h4]
    linarith [h1, h2, h3]
  -- the threshold
  have hroot_lt : Real.sqrt (clusterInertia m k (γ t)) < θ :=
    (Real.sqrt_lt' hθpos).mpr (hsmall t (Ioo_subset_Icc_self ht))
  have hIlt : clusterInertia m k (γ t) < θ := by nlinarith [hsmall t (Ioo_subset_Icc_self ht),
    hθpos, hθ1]
  have hb1 : 2 * C₁ * Real.sqrt (clusterInertia m k (γ t)) ≤ 2 * C₁ * θ :=
    mul_le_mul_of_nonneg_left hroot_lt.le (by linarith)
  have hb2 : cW * clusterInertia m k (γ t) ≤ cW * θ := mul_le_mul_of_nonneg_left hIlt.le hcW.le
  have hlt : (2 * C₁ + cW) * θ < (2 * C₁ + cW + 1) * θ := by nlinarith [hθpos]
  linarith [hkey', hb1, hb2, hlt, hθ]

/-- **No sandwiched zeros near a locally minimal collision.** -/
theorem exists_no_sandwich_of_sperner {m : Fin N → ℝ} {k : Finset (Fin N)} {γ : ℝ → EN E N}
    {W : Set ℝ} {t₁ ν C₁ : ℝ} (hm : ∀ i, 0 < m i) (hkne : k.Nonempty) (hk2 : 2 ≤ k.card)
    (hcont : ContinuousOn (fun t : ℝ => clusterInertia m k (γ t)) W)
    (ht₁W : t₁ ∈ W)
    (hF0 : clusterInertia m k (γ t₁) = 0)
    (hnc : ∀ t ∈ W, 0 < clusterInertia m k (γ t) → WithoutCollisions (γ t))
    (hsol : ∀ t ∈ W, 0 < clusterInertia m k (γ t) →
      (∀ᶠ s in 𝓝 t, HasDerivAt γ (deriv γ s) s) ∧
      HasDerivAt (deriv γ) (iteratedDeriv 2 γ t) t ∧
      iteratedDeriv 2 γ t = ∇_[m] (U m) (γ t))
    (hν : 0 < ν)
    (hsep : ∀ t ∈ W, 0 < clusterInertia m k (γ t) → ClusterSeparatedWeak k (γ t) ν)
    (hc1 : 0 ≤ C₁)
    (hE : ∀ t ∈ W, 0 < clusterInertia m k (γ t) →
      -C₁ ≤ clusterRelEnergy m k (γ t) (deriv γ t)) :
    ∃ η > 0, η ≤ 1 ∧ ∀ a b : ℝ, a < b → Icc a b ⊆ W → |a - t₁| < η → |b - t₁| < η →
      clusterInertia m k (γ a) = 0 → clusterInertia m k (γ b) = 0 →
      ¬ ∃ x ∈ Ioo a b, 0 < clusterInertia m k (γ x) := by
  classical
  obtain ⟨cS, hcS, hSp⟩ := exists_const_le_clusterPotential (E := E) hm k hk2
  obtain ⟨i₀, hi₀⟩ := hkne
  have hkne' : k.Nonempty := ⟨i₀, hi₀⟩
  set cW : ℝ := 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) with hcWdef
  have hmass : 0 < ∑ j : Fin N, m j :=
    lt_of_lt_of_le (hm i₀)
      (Finset.single_le_sum (f := m) (fun j _ => (hm j).le) (Finset.mem_univ i₀))
  have hcWpos : 0 < cW := by
    rw [hcWdef]
    have h1 : 0 < (ν⁻¹) ^ 2 := pow_pos (inv_pos.mpr hν) 2
    have h3 : 0 < Real.sqrt (clusterMass m k) := Real.sqrt_pos.mpr (clusterMass_pos hm hkne')
    positivity
  set θ : ℝ := min 1 (cS / (2 * C₁ + cW + 1)) with hθdef
  have hθpos : 0 < θ := lt_min one_pos (div_pos hcS (by linarith))
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hden : 0 < 2 * C₁ + cW + 1 := by linarith
  have hθ : (2 * C₁ + cW + 1) * θ ≤ cS := by
    have h1 : θ ≤ cS / (2 * C₁ + cW + 1) := min_le_right _ _
    calc (2 * C₁ + cW + 1) * θ ≤ (2 * C₁ + cW + 1) * (cS / (2 * C₁ + cW + 1)) :=
          mul_le_mul_of_nonneg_left h1 hden.le
      _ = cS := by field_simp
  have hθ2pos : 0 < θ ^ 2 := pow_pos hθpos 2
  -- the window on which `F` is below the threshold
  have hcontAt : ContinuousWithinAt (fun t : ℝ => clusterInertia m k (γ t)) W t₁ :=
    hcont t₁ ht₁W
  have hev : ∀ᶠ t in 𝓝[W] t₁, clusterInertia m k (γ t) < θ ^ 2 :=
    hcontAt.eventually (isOpen_Iio.mem_nhds (by simp only [hF0]; exact hθ2pos))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨min δ 1, lt_min hδpos one_pos, min_le_right _ _, ?_⟩
  intro a b hab habW ha' hb' ha hb hpos'
  refine false_of_sandwich_sperner (W := W) (a := a) (b := b) (cS := cS) (cW := cW) (C₁ := C₁)
    (θ := θ) hm hkne' hab habW hcont ha hb hpos' hnc hsol hcS ?_ hcWpos ?_ hc1 hE hθpos hθ1 hθ ?_
  · intro t htW hFt
    exact hSp (γ t) (hnc t htW hFt)
  · intro t htW hFt
    have h1 := hsep t htW hFt
    have h2 := abs_crossWork_cmRel_le (m := m) (k := k) (x := γ t) (v := γ t) (ν := ν) hm hν h1
    have h3 : clusterRelKinetic m k (γ t) = clusterInertia m k (γ t) :=
      clusterRelKinetic_eq_clusterInertia m k (γ t)
    rw [h3] at h2
    rw [hcWdef]
    exact h2
  · intro t ht
    have h3 : a ≤ t := (Set.mem_Icc.mp ht).1
    have h4 : t ≤ b := (Set.mem_Icc.mp ht).2
    have h5 : -(min δ 1) < a - t₁ := (abs_lt.mp ha').1
    have h8 : b - t₁ < min δ 1 := (abs_lt.mp hb').2
    have ht_lt : |t - t₁| < δ := by
      rw [abs_lt]
      constructor
      · have h6 : min δ 1 ≤ δ := min_le_left δ 1
        linarith
      · have h6 : min δ 1 ≤ δ := min_le_left δ 1
        linarith
    exact hδ ⟨by rw [Metric.mem_ball, Real.dist_eq]; exact ht_lt, habW ht⟩

/-- **A locally minimal collision exists.**  If a continuous curve has a collision in `[c,d]`,
then there is a collision time `t₁ ∈ [c,d]` with a neighbourhood on which the set of colliding
pairs is *locally constant*: the collision classes do not change. -/
theorem exists_local_min_pairs {γ : ℝ → EN E N} {c d : ℝ}
    (hcont : ContinuousOn γ (Icc c d)) (hcoll : ∃ t ∈ Icc c d, ¬ WithoutCollisions (γ t)) :
    ∃ t₁ ∈ Icc c d, ¬ WithoutCollisions (γ t₁) ∧ ∃ ε > 0, ∀ t ∈ Icc c d,
      |t - t₁| < ε → (∃ i j, i ≠ j ∧ γ t i = γ t j) →
        collPairs γ t = collPairs γ t₁ := by
  classical
  set S : Set ℝ := {t | t ∈ Icc c d ∧ ¬ WithoutCollisions (γ t)} with hSdef
  obtain ⟨t₀, ht₀⟩ := hcoll
  have hSne : S.Nonempty := ⟨t₀, ht₀⟩
  -- the minimal number of colliding pairs over the collision set
  have hex : ∃ n : ℕ, (∃ t ∈ S, (collPairs γ t).card = n) ∧
      ∀ m, (∃ t ∈ S, (collPairs γ t).card = m) → n ≤ m := by
    set L : Finset (Fin (N * N + 1)) :=
      Finset.univ.filter (fun m => ∃ t ∈ S, (collPairs γ t).card = m.val) with hL
    have hLne : L.Nonempty := by
      refine ⟨⟨(collPairs γ t₀).card, Nat.lt_succ_of_le (collPairs_card_le γ t₀)⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, t₀, ht₀, rfl⟩⟩
    obtain ⟨m₁, hm₁, hmin⟩ := Finset.exists_min_image L (fun m : Fin (N * N + 1) => m.val) hLne
    refine ⟨m₁.val, (Finset.mem_filter.mp hm₁).2, fun m hm => ?_⟩
    have hmle : m ≤ N * N := by
      obtain ⟨t, -, hte⟩ := hm
      rw [← hte]
      exact collPairs_card_le γ t
    have h2 : (⟨m, Nat.lt_succ_of_le hmle⟩ : Fin (N * N + 1)) ∈ L :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
    have h3 : m₁.val ≤ (⟨m, Nat.lt_succ_of_le hmle⟩ : Fin (N * N + 1)).val := hmin _ h2
    simpa using h3
  obtain ⟨n₁, ⟨t₁, ht₁S, ht₁card⟩, ht₁min⟩ := hex
  obtain ⟨ε, hεpos, hε⟩ := exists_collPairs_subset_of_continuousWithinAt hcont ht₁S.1
  refine ⟨t₁, ht₁S.1, ht₁S.2, ε, hεpos, fun t ht hlt hcol => ?_⟩
  have hsub : collPairs γ t ⊆ collPairs γ t₁ := hε t ht hlt
  have htS : t ∈ S := ⟨ht, fun hnc => by
    obtain ⟨i, j, hij, heq⟩ := hcol
    exact (hnc i j hij) (by rw [r_eq_norm_sub, heq, sub_self, norm_zero])⟩
  have hcard : (collPairs γ t₁).card ≤ (collPairs γ t).card := by
    rw [ht₁card]
    exact ht₁min _ ⟨t, htS, rfl⟩
  exact Finset.eq_of_subset_of_card_le hsub hcard

/-- **A locally minimal collision exists** (collision-class form).  If a continuous curve has a
collision in `[c,d]`, then there is a collision time `t₁ ∈ [c,d]`, a colliding pair at `t₁`, and a
neighbourhood on which *every* collision makes the whole collision class of `t₁` collide: the
collision classes are locally constant. -/
theorem exists_local_min_collision {γ : ℝ → EN E N} {c d : ℝ}
    (hcont : ContinuousOn γ (Icc c d)) (hcoll : ∃ t ∈ Icc c d, ¬ WithoutCollisions (γ t)) :
    ∃ t₁ ∈ Icc c d, ∃ i₁ : Fin N, 2 ≤ (collClass γ t₁ i₁).card ∧ ∃ ε > 0,
      ∀ t ∈ Icc c d, |t - t₁| < ε → (∃ i j, i ≠ j ∧ γ t i = γ t j) →
        ∀ i ∈ collClass γ t₁ i₁, ∀ j ∈ collClass γ t₁ i₁, γ t i = γ t j := by
  classical
  obtain ⟨t₁, ht₁, hcoll₁, ε, hεpos, hε⟩ := exists_local_min_pairs hcont hcoll
  obtain ⟨a, b, hab, heqab⟩ : ∃ a b : Fin N, a ≠ b ∧ γ t₁ a = γ t₁ b := by
    by_contra h
    refine hcoll₁ fun i j hij hcon => h ⟨i, j, hij, ?_⟩
    rw [r_eq_norm_sub, norm_eq_zero, sub_eq_zero] at hcon
    exact hcon
  refine ⟨t₁, ht₁, a, two_le_card_collClass_of_exists hab.symm heqab.symm, ε, hεpos,
    fun t ht hlt hcol => ?_⟩
  have heq : collPairs γ t = collPairs γ t₁ := hε t ht hlt hcol
  intro i hi j hj
  rw [mem_collClass] at hi hj
  by_cases hij : i = j
  · rw [hij]
  · have hmem : (i, j) ∈ collPairs γ t₁ := mem_collPairs.mpr ⟨hij, by rw [hi, hj]⟩
    exact (mem_collPairs.mp (heq.symm ▸ hmem)).2

end Submission.NBody
