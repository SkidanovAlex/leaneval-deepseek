import Submission.NBody.MarchalClassAsymptotic
import Submission.NBody.MarchalRelEnergy
import Submission.NBody.MarchalSperner

/-!
# The self-scaled bound on the outside velocities at a collision

The jolt (third-derivative) estimates of the Sundman chain control the bodies **outside** the
colliding cluster `k` by the *cluster's own* acceleration scale:

    `‖ẋ_j‖ ≤ Cv * √(Ï_k + 4C)`     (`j ∉ k`).

This is the form in which the constant-velocity hypothesis `‖ẋ_j‖ ≤ Cv` is actually used
(`abs_third_deriv_clusterInertia_le`), and it is *true* without any hypothesis on the number of
colliding clusters: the sum-level kinetic bound gives `‖ẋ_j‖ ≤ C u^{-1/3}`, while Sperner's bound
together with the first-order asymptotics gives `Ï_k ≥ c u^{-2/3}`.

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

/-- `t^{-2/3} → +∞` as `t → 0⁺`. -/
lemma tendsto_rpow_neg_two_thirds_nhdsGT_atTop :
    Tendsto (fun t : ℝ => t ^ (-((2:ℝ)/3))) (nhdsWithin (0:ℝ) (Ioi 0)) atTop := by
  have h1 : Tendsto (fun t : ℝ => t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhdsWithin (0:ℝ) (Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_rpow_two_thirds_nhdsWithin_zero, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Real.rpow_pos_of_pos ht _
  have h2 : Tendsto (fun t : ℝ => (t ^ ((2:ℝ)/3))⁻¹) (nhdsWithin (0:ℝ) (Ioi 0)) atTop :=
    h1.inv_tendsto_nhdsGT_zero
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Real.rpow_neg ht.le]

/-- **The outside velocities are bounded by the acceleration scale of the colliding cluster.**  For
an `h`-minimiser with an isolated collision at `t₀` and a collision class `k`, there are constants
`Cv, C > 0` with `‖ẋ_j(t₀+t)‖ ≤ Cv √(Ï_k(t₀+t) + 4C)` for every `j ∉ k` and every small `t > 0`. -/
theorem exists_selfScaled_outside_velocity_bound {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b t₀ ε ν : ℝ} {k : Finset (Fin N)}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b) (hk2 : 2 ≤ k.card)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) (hε : 0 < ε) (hεb : t₀ + ε ≤ b)
    (hnc : ∀ t ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ t))
    (hν : 0 < ν) (hsepw : ∀ t ∈ Ioo t₀ (t₀ + ε), ClusterSeparatedWeak k (γ t) ν)
    (hI0 : clusterInertia m k (γ t₀) = 0) :
    ∃ Cv C : ℝ, 0 < Cv ∧ 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ j ∉ k,
        ‖deriv γ (t₀ + t) j‖
          ≤ Cv * Real.sqrt (deriv (deriv (fun s : ℝ => clusterInertia m k (γ (t₀ + s)))) t + 4 * C) := by
  classical
  have hkne : k.Nonempty := Finset.card_pos.mp (by omega)
  -- a positive lower bound for the masses
  obtain ⟨κm, hκmpos, hκm⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    obtain ⟨i₀, hi₀⟩ := hkne
    obtain ⟨i₁, -, hi₁⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N)) m
      ⟨i₀, Finset.mem_univ i₀⟩
    exact ⟨m i₁, hm i₁, fun i => hi₁ i (Finset.mem_univ i)⟩
  -- the collision at `t₀`
  have hcoll : ¬ WithoutCollisions (γ t₀) := by
    intro hnc'
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < k.card)
    have h1 : γ t₀ i = γ t₀ j := (clusterInertia_eq_zero_iff hm k (γ t₀)).mp hI0 i hi j hj
    exact (hnc' i j hij) (by rw [r_eq_norm_sub, h1, sub_self, norm_zero])
  -- the working interval and the shifted curve
  set D : ℝ := min ε 1 with hDdef
  have hDpos : 0 < D := lt_min hε one_pos
  have hDle : D ≤ ε := min_le_left _ _
  have hDb : t₀ + D ≤ b := by linarith
  let x : ℝ → EN E N := fun s => γ (t₀ + s)
  have hncD' : ∀ t ∈ Ioo t₀ (t₀ + D), WithoutCollisions (γ t) := fun t ht =>
    hnc t ⟨ht.1, by linarith [ht.2, hDle]⟩
  have hncD : ∀ u ∈ Ioo (0:ℝ) D, WithoutCollisions (x u) := fun u hu =>
    hncD' (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
  -- the Newton data on the shifted curve
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
  have hxev : ∀ u ∈ Ioo (0:ℝ) D, ∀ᶠ s in 𝓝 u, HasDerivAt x (deriv x s) s := fun u hu => by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with s hs
    exact hx s hs
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
  -- the kinetic bound
  obtain ⟨Ck, hCkpos, hkin⟩ := exists_kinetic_bound_at_collision (m := m) (h := h) (γ := γ)
    (a := a) (b := b) (t₀ := t₀) (ε := D) hm hh hab hac hmin hfin ht₀ hcoll hDpos hDb hncD'
  have hkin' : ∀ᶠ u in 𝓝[>] (0:ℝ), kinetic m (deriv x u) ≤ Ck * u ^ (-((2:ℝ)/3)) := by
    filter_upwards [hkin] with u hu
    show kinetic m (deriv (fun s : ℝ => γ (t₀ + s)) u) ≤ Ck * u ^ (-((2:ℝ)/3))
    rw [deriv_shiftCurve_eq t₀ u] at hu ⊢
    exact hu
  -- the relative-energy bound and the interaction-work bound
  have hsepwD : ∀ u ∈ Ioo (0:ℝ) D, ClusterSeparatedWeak k (x u) ν := fun u hu =>
    hsepw (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hode' : ∀ u ∈ Ioo (0:ℝ) D, deriv (deriv x) u = ∇_[m] (U m) (x u) := fun u hu =>
    (iteratedDeriv_two_eq_deriv_deriv x u).symm.trans (hode u hu)
  have hd2' : ∀ u ∈ Ioo (0:ℝ) D, HasDerivAt (deriv x) (deriv (deriv x) u) u := fun u hu =>
    (hd2 u hu).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x u)
  have hode' : ∀ u ∈ Ioo (0:ℝ) D, deriv (deriv x) u = ∇_[m] (U m) (x u) := fun u hu =>
    (iteratedDeriv_two_eq_deriv_deriv x u).symm.trans (hode u hu)
  obtain ⟨Ce, hCepos, δ, hδpos, hδle, henergy⟩ :=
    exists_relEnergy_bound_of_kinetic (m := m) (k := k) (x := x) (ε := D) (ν := ν) (Ck := Ck)
      hm hkne hDpos hν hCkpos hncD hx hd2' hode' hsepwD hkin'
  -- the first-order asymptotics of the inertia
  obtain ⟨κ, hκpos, hκ⟩ := clusterInertia_asymptotic_of_collision (m := m) (h := h) (γ := γ)
    (a := a) (b := b) (t₀ := t₀) (ε := D) (ν := ν) (k := k) hm hh hab hk2 hac hmin hfin ht₀
    hDpos hDb hncD' hν (fun t ht => hsepw t ⟨ht.1, by linarith [ht.2, hDle]⟩) hI0
  -- Sperner's constant
  obtain ⟨ck, hckpos, hcksp⟩ := exists_const_le_clusterPotential (E := E) hm k hk2
  -- the interaction-work constant
  set Cw : ℝ := 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) with hCwdef
  have hCw0 : 0 ≤ Cw := by
    rw [hCwdef]
    have h1 : 0 ≤ (ν⁻¹) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
    have h3 : 0 ≤ Real.sqrt (clusterMass m k) := Real.sqrt_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3
  set C : ℝ := max Ce Cw + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCeC : Ce ≤ C := by rw [hCdef]; linarith [le_max_left Ce Cw]
  have hCwC : Cw ≤ C := by rw [hCdef]; linarith [le_max_right Ce Cw]
  -- the eventual statements
  have hEev : ∀ᶠ u in 𝓝[>] (0:ℝ),
      |clusterRelEnergy m k (x u) (deriv x u)| ≤ C := by
    filter_upwards [Ioo_mem_nhdsGT hδpos] with u hu
    exact le_trans (henergy u hu) hCeC
  have hWev : ∀ᶠ u in 𝓝[>] (0:ℝ),
      |crossWork m k (x u) (cmRel m k (x u))| ≤ C := by
    have hIev : ∀ᶠ u in 𝓝[>] (0:ℝ), clusterInertia m k (x u) < 1 := by
      have h0 : Tendsto (fun u : ℝ => clusterInertia m k (x u)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
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
          ((continuous_clusterInertia m k).continuousAt.tendsto.comp hcont).mono_left
            nhdsWithin_le_nhds
        simpa [hI0] using h6
      exact h0.eventually (isOpen_Iio.mem_nhds one_pos)
    filter_upwards [hIev, Ioo_mem_nhdsGT hDpos] with u hI1 hu
    have h1 := abs_crossWork_cmRel_le (m := m) (k := k) (x := x u) (v := x u) (ν := ν)
      hm hν (hsepwD u hu)
    have h2 : clusterRelKinetic m k (x u) = clusterInertia m k (x u) :=
      clusterRelKinetic_eq_clusterInertia m k (x u)
    rw [h2] at h1
    refine le_trans h1 ?_
    have hs : Real.sqrt (clusterInertia m k (x u)) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (le_of_lt hI1)
    have hnn : 0 ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) := by
      have h := hCw0; rw [hCwdef] at h; exact h
    have h2' : 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
        * Real.sqrt (clusterInertia m k (x u)) ≤ Cw := by
      rw [hCwdef]
      calc 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
            * Real.sqrt (clusterInertia m k (x u))
          ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) * 1 :=
            mul_le_mul_of_nonneg_left hs hnn
        _ = 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) := by ring
    exact le_trans h2' hCwC
  have hIub : ∀ᶠ u in 𝓝[>] (0:ℝ), clusterInertia m k (x u) ≤ 2 * κ * u ^ ((4:ℝ)/3) := by
    have h1 : ∀ᶠ u in nhdsWithin (0:ℝ) (Ioi 0),
        clusterInertia m k (x u) / u ^ ((4:ℝ)/3) < 2 * κ :=
      hκ.eventually (eventually_lt_nhds (by linarith))
    filter_upwards [h1, self_mem_nhdsWithin] with u h1u hu
    have hu0 : 0 < u := hu
    rw [div_lt_iff₀ (Real.rpow_pos_of_pos hu0 _)] at h1u
    linarith
  have hncev : ∀ᶠ u in 𝓝[>] (0:ℝ), WithoutCollisions (x u) := by
    filter_upwards [Ioo_mem_nhdsGT hDpos] with u hu
    exact hncD u hu
  have hscale : ∀ᶠ u in 𝓝[>] (0:ℝ),
      6 * C ≤ (ck / (2 * Real.sqrt (2 * κ))) * u ^ (-((2:ℝ)/3)) := by
    have h0 : Tendsto (fun u : ℝ => (ck / (2 * Real.sqrt (2 * κ))) * u ^ (-((2:ℝ)/3)))
        (nhdsWithin (0:ℝ) (Ioi 0)) atTop :=
      tendsto_rpow_neg_two_thirds_nhdsGT_atTop.const_mul_atTop (by positivity)
    exact h0.eventually (eventually_ge_atTop (6 * C))
  -- combine
  have hmain : ∀ᶠ u in 𝓝[>] (0:ℝ), ∀ j ∉ k,
      ‖deriv x u j‖ ≤ Real.sqrt (2 * Ck / κm) * Real.sqrt (2 * Real.sqrt (2 * κ) / ck)
        * Real.sqrt (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) u + 4 * C) := by
    filter_upwards [hkin', hEev, hWev, hIub, hncev, hscale, Ioo_mem_nhdsGT hDpos]
      with u hk_u he_u hw_u hi_u hnc_u hs_u huD
    have hu0 : 0 < u := huD.1
    have hncx : WithoutCollisions (x u) := hnc_u
    have hIpos : 0 < clusterInertia m k (x u) := clusterInertia_pos hm hk2 hncx
    have hrootpos : 0 < Real.sqrt (clusterInertia m k (x u)) := Real.sqrt_pos.mpr hIpos
    have hsp := hcksp (x u) hncx
    -- the lower bound on `Ï_k` via the Lagrange--Jacobi identity
    have hE' : -C ≤ clusterRelEnergy m k (x u) (deriv x u) := (abs_le.mp he_u).1
    have hW' : -C ≤ crossWork m k (x u) (cmRel m k (x u)) := (abs_le.mp hw_u).1
    have hge := clusterInertia_second_deriv_ge_rel (m := m) (k := k) (x := x) (t := u)
      (C := C) (ck := ck) hm hkne hE' hW' hsp (hxev u huD) (hd2 u huD) (hode u huD) hncx
    -- (A) `√(I_k) ≤ √(2κ) u^{2/3}`
    have h2κ : 0 < 2 * κ := by linarith
    have hsIub : Real.sqrt (clusterInertia m k (x u)) ≤ Real.sqrt (2 * κ) * u ^ ((2:ℝ)/3) := by
      calc Real.sqrt (clusterInertia m k (x u)) ≤ Real.sqrt (2 * κ * u ^ ((4:ℝ)/3)) :=
            Real.sqrt_le_sqrt hi_u
        _ = Real.sqrt (2 * κ) * u ^ ((2:ℝ)/3) := by
            rw [Real.sqrt_mul h2κ.le]
            rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hu0.le]
            norm_num
    -- (B) `ck/√(I_k) ≥ (ck/√(2κ)) u^{-2/3}`
    have hsmall : ck / (Real.sqrt (2 * κ) * u ^ ((2:ℝ)/3))
        ≤ ck / Real.sqrt (clusterInertia m k (x u)) := by
      refine div_le_div_of_nonneg_left hckpos.le hrootpos hsIub
    have hrw : ck / (Real.sqrt (2 * κ) * u ^ ((2:ℝ)/3))
        = (ck / Real.sqrt (2 * κ)) * u ^ (-((2:ℝ)/3)) := by
      rw [Real.rpow_neg hu0.le, div_eq_mul_inv, mul_inv, ← mul_assoc, ← div_eq_mul_inv,
        div_eq_mul_inv]
      rfl
    -- (C) `c₀ u^{-2/3} ≤ Ï_k`, `c₀ := ck/(2√(2κ))`
    have hP : (ck / (2 * Real.sqrt (2 * κ))) * u ^ (-((2:ℝ)/3))
        ≤ deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) u := by
      have h1 : (ck / Real.sqrt (2 * κ)) * u ^ (-((2:ℝ)/3))
          ≤ iteratedDeriv 2 (fun s : ℝ => clusterInertia m k (x s)) u + 6 * C := by
        rw [← hrw]; exact le_trans hsmall hge
      rw [iteratedDeriv_two_eq_deriv_deriv] at h1
      have h3 : 2 * ((ck / (2 * Real.sqrt (2 * κ))) * u ^ (-((2:ℝ)/3)))
          = (ck / Real.sqrt (2 * κ)) * u ^ (-((2:ℝ)/3)) := by ring
      linarith [hs_u]
    -- (D) `√(Ï + 4C) ≥ √c₀ u^{-1/3}`
    have hP0 : 0 ≤ deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) u := by
      have h0 : 0 ≤ (ck / (2 * Real.sqrt (2 * κ))) * u ^ (-((2:ℝ)/3)) :=
        mul_nonneg (by positivity) (Real.rpow_nonneg hu0.le _)
      linarith
    have hsP : Real.sqrt ((ck / (2 * Real.sqrt (2 * κ))) * u ^ (-((2:ℝ)/3)))
        ≤ Real.sqrt (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) u + 4 * C) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsq : Real.sqrt ((ck / (2 * Real.sqrt (2 * κ))) * u ^ (-((2:ℝ)/3)))
        = Real.sqrt (ck / (2 * Real.sqrt (2 * κ))) * u ^ (-((1:ℝ)/3)) := by
      have hB : Real.sqrt (u ^ (-((2:ℝ)/3))) = u ^ (-((1:ℝ)/3)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hu0.le]
        norm_num
      rw [Real.sqrt_mul (by positivity), hB]
    -- (E) the velocity bound
    intro j hj
    have hmj : κm ≤ m j := hκm j
    have hmjpos : 0 < m j := hm j
    have hsqj : ‖deriv x u j‖ ^ 2 ≤ 2 * Ck * u ^ (-((2:ℝ)/3)) / m j := by
      rw [le_div_iff₀ hmjpos]
      have hsum : (∑ i : Fin N, m i * ‖deriv x u i‖ ^ 2) ≤ 2 * Ck * u ^ (-((2:ℝ)/3)) := by
        have h := hk_u
        rw [kinetic] at h
        linarith
      have h1 := Finset.single_le_sum (f := fun i : Fin N => m i * ‖deriv x u i‖ ^ 2)
        (fun i _ => mul_nonneg (hm i).le (sq_nonneg _)) (Finset.mem_univ j)
      linarith
    have htarget : ‖deriv x u j‖ ≤ Real.sqrt (2 * Ck / κm) * u ^ (-((1:ℝ)/3)) := by
      have hbase : 0 ≤ Real.sqrt (2 * Ck / κm) * u ^ (-((1:ℝ)/3)) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hu0.le _)
      have h2 : ‖deriv x u j‖ ^ 2
          ≤ (Real.sqrt (2 * Ck / κm) * u ^ (-((1:ℝ)/3))) ^ 2 := by
        have hA : 0 ≤ 2 * Ck * u ^ (-((2:ℝ)/3)) :=
          mul_nonneg (by positivity) (Real.rpow_nonneg hu0.le _)
        calc ‖deriv x u j‖ ^ 2 ≤ 2 * Ck * u ^ (-((2:ℝ)/3)) / m j := hsqj
          _ ≤ 2 * Ck * u ^ (-((2:ℝ)/3)) / κm :=
              div_le_div_of_nonneg_left hA hκmpos hmj
          _ = (Real.sqrt (2 * Ck / κm) * u ^ (-((1:ℝ)/3))) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast,
                ← Real.rpow_mul hu0.le]
              norm_num
              ring
      exact le_trans (le_abs_self _) (le_trans (sq_le_sq.mp h2) (by rw [abs_of_nonneg hbase]))
    -- combine
    calc ‖deriv x u j‖
        ≤ Real.sqrt (2 * Ck / κm) * u ^ (-((1:ℝ)/3)) := htarget
      _ = Real.sqrt (2 * Ck / κm) / Real.sqrt (ck / (2 * Real.sqrt (2 * κ)))
            * (Real.sqrt (ck / (2 * Real.sqrt (2 * κ))) * u ^ (-((1:ℝ)/3))) := by
            field_simp
      _ = Real.sqrt (2 * Ck / κm)
            * Real.sqrt (2 * Real.sqrt (2 * κ) / ck)
            * (Real.sqrt (ck / (2 * Real.sqrt (2 * κ))) * u ^ (-((1:ℝ)/3))) := by
            congr 1
            rw [show Real.sqrt (2 * Real.sqrt (2 * κ) / ck)
                = (Real.sqrt (ck / (2 * Real.sqrt (2 * κ))))⁻¹ from ?_]
            · rw [div_eq_mul_inv]
            · rw [← Real.sqrt_inv]
              congr 1
              field_simp
      _ ≤ Real.sqrt (2 * Ck / κm) * Real.sqrt (2 * Real.sqrt (2 * κ) / ck)
            * Real.sqrt (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) u + 4 * C) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [← hsq]
            exact hsP
  refine ⟨Real.sqrt (2 * Ck / κm) * Real.sqrt (2 * Real.sqrt (2 * κ) / ck), C,
    by positivity, hCpos, ?_⟩
  filter_upwards [hmain] with u hu
  intro j hj
  have h := hu j hj
  dsimp only [x] at h
  rwa [deriv_shiftCurve_eq t₀ u] at h


/-! ## From the acceleration scale to the potential scale -/

/-- **The cluster's acceleration scale is controlled by its potential scale.**  If the potential is
at least `1` and the relative energy and the interaction work are bounded by `C`, then
`√(Ï_k + 4C') ≤ √(2 + max 0 (6C + 4C')) · √(U_k)`.  This converts between the two self-scaled forms
of the velocity bound (`√(Ï_k + 4C')` and `√(U_k)`). -/
theorem sqrt_secondDeriv_add_le_sqrt_potential {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C C' : ℝ}
    (hm : ∀ i, 0 < m i) (hk : k.Nonempty) (hε : 0 < ε)
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |clusterRelEnergy m k (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |crossWork m k (x t) (cmRel m k (x t))| ≤ C)
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hU1 : ∀ t ∈ Ioo (0:ℝ) ε, 1 ≤ clusterPotential m k (x t)) :
    ∀ᶠ t in 𝓝[>] (0:ℝ),
      Real.sqrt (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t + 4 * C')
        ≤ Real.sqrt (2 + max 0 (6 * C + 4 * C')) * Real.sqrt (clusterPotential m k (x t)) := by
  filter_upwards [Ioo_mem_nhdsGT hε] with t ht
  have h1 := hU1 t ht
  have hU0 : 0 ≤ clusterPotential m k (x t) := le_trans zero_le_one h1
  have hxev : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hx s hs
  have hLJ : deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
      = 4 * clusterRelEnergy m k (x t) (deriv x t) + 2 * clusterPotential m k (x t)
        + 2 * crossWork m k (x t) (cmRel m k (x t)) := by
    rw [← iteratedDeriv_two_eq_deriv_deriv]
    exact iteratedDeriv_two_clusterInertia_rel hm hk (hnc t ht) hxev (hd2 t ht) (hode t ht)
  have hP : deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t + 4 * C'
      ≤ (2 + max 0 (6 * C + 4 * C')) * clusterPotential m k (x t) := by
    have h2 := (abs_le.mp (hE t ht)).2
    have h3 := (abs_le.mp (hW t ht)).2
    have h4 : max 0 (6 * C + 4 * C') ≤ max 0 (6 * C + 4 * C') * clusterPotential m k (x t) :=
      le_mul_of_one_le_right (le_max_left _ _) h1
    have h5 : 6 * C + 4 * C' ≤ max 0 (6 * C + 4 * C') := le_max_right _ _
    rw [hLJ]
    nlinarith [h2, h3, h4, h5, h1, hU0]
  calc Real.sqrt (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t + 4 * C')
      ≤ Real.sqrt ((2 + max 0 (6 * C + 4 * C')) * clusterPotential m k (x t)) :=
        Real.sqrt_le_sqrt hP
    _ = Real.sqrt (2 + max 0 (6 * C + 4 * C')) * Real.sqrt (clusterPotential m k (x t)) :=
        Real.sqrt_mul (by positivity) _


/-- **The outside velocities at a collision, in the potential-scale form.**  For an `h`-minimiser with
an isolated collision at `t₀` and a collision class `k`, there is `Cv > 0` with
`‖ẋ_j(t₀+t)‖ ≤ Cv √(U_k(γ(t₀+t)))` for every `j ∉ k` and every small `t > 0`.  This is the form of
the velocity bound consumed by the jolt estimates of the Sundman chain. -/
theorem exists_scaled_outside_velocity_bound_of_collision {m : Fin N → ℝ} {h : ℝ}
    {γ : ℝ → EN E N} {a b t₀ ε ν : ℝ} {k : Finset (Fin N)}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b) (hk2 : 2 ≤ k.card)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) (hε : 0 < ε) (hεb : t₀ + ε ≤ b)
    (hnc : ∀ t ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ t))
    (hν : 0 < ν) (hsepw : ∀ t ∈ Ioo t₀ (t₀ + ε), ClusterSeparatedWeak k (γ t) ν)
    (hI0 : clusterInertia m k (γ t₀) = 0) :
    ∃ Cv : ℝ, 0 < Cv ∧ ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ j ∉ k,
      ‖deriv γ (t₀ + t) j‖ ≤ Cv * Real.sqrt (clusterPotential m k (γ (t₀ + t))) := by
  classical
  have hkne : k.Nonempty := Finset.card_pos.mp (by omega)
  -- the collision at `t₀`
  have hcoll : ¬ WithoutCollisions (γ t₀) := by
    intro hnc'
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < k.card)
    have h1 : γ t₀ i = γ t₀ j := (clusterInertia_eq_zero_iff hm k (γ t₀)).mp hI0 i hi j hj
    exact (hnc' i j hij) (by rw [r_eq_norm_sub, h1, sub_self, norm_zero])
  -- the working interval, the shifted curve and the Newton data
  set D : ℝ := min ε 1 with hDdef
  have hDpos : 0 < D := lt_min hε one_pos
  have hDle : D ≤ ε := min_le_left _ _
  have hDb : t₀ + D ≤ b := by linarith
  let x : ℝ → EN E N := fun s => γ (t₀ + s)
  have hncD' : ∀ t ∈ Ioo t₀ (t₀ + D), WithoutCollisions (γ t) := fun t ht =>
    hnc t ⟨ht.1, by linarith [ht.2, hDle]⟩
  have hncD : ∀ u ∈ Ioo (0:ℝ) D, WithoutCollisions (x u) := fun u hu =>
    hncD' (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
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
  have hxev : ∀ u ∈ Ioo (0:ℝ) D, ∀ᶠ s in 𝓝 u, HasDerivAt x (deriv x s) s := fun u hu => by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with s hs
    exact hx s hs
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
  -- the kinetic bound
  obtain ⟨Ck, hCkpos, hkin⟩ := exists_kinetic_bound_at_collision (m := m) (h := h) (γ := γ)
    (a := a) (b := b) (t₀ := t₀) (ε := D) hm hh hab hac hmin hfin ht₀ hcoll hDpos hDb hncD'
  have hkin' : ∀ᶠ u in 𝓝[>] (0:ℝ), kinetic m (deriv x u) ≤ Ck * u ^ (-((2:ℝ)/3)) := by
    filter_upwards [hkin] with u hu
    show kinetic m (deriv (fun s : ℝ => γ (t₀ + s)) u) ≤ Ck * u ^ (-((2:ℝ)/3))
    rw [deriv_shiftCurve_eq t₀ u] at hu ⊢
    exact hu
  -- the relative-energy bound
  have hsepwD : ∀ u ∈ Ioo (0:ℝ) D, ClusterSeparatedWeak k (x u) ν := fun u hu =>
    hsepw (t₀ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
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
  -- the inertia tends to `0` at `t₀`
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
  -- Sperner's constant
  obtain ⟨ck, hckpos, hcksp⟩ := exists_const_le_clusterPotential (E := E) hm k hk2
  -- the self-scaled velocity bound
  obtain ⟨Cv', C', hCv'0, hC'0, hself⟩ := exists_selfScaled_outside_velocity_bound (m := m)
    (h := h) (γ := γ) (a := a) (b := b) (t₀ := t₀) (ε := ε) (ν := ν) (k := k)
    hm hh hab hk2 hac hmin hfin ht₀ hε hεb hnc hν hsepw hI0
  -- the common constant for the energy and the interaction work
  set C : ℝ := max Ce Cw with hCdef
  have hCeC : Ce ≤ C := le_max_left _ _
  have hCwC : Cw ≤ C := le_max_right _ _
  -- the interval on which the inertia is small
  obtain ⟨δI, hδIpos, hδI⟩ : ∃ δI : ℝ, 0 < δI ∧ ∀ u ∈ Ioo (0:ℝ) δI,
      clusterInertia m k (x u) < min 1 (ck ^ 2) := by
    have hminpos : 0 < min 1 (ck ^ 2) := lt_min one_pos (by positivity)
    have hev := hItend.eventually (isOpen_Iio.mem_nhds hminpos)
    rw [eventually_nhdsWithin_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hev
    refine ⟨δ, hδpos, fun u hu => hδ u ?_ hu.1⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu.1]
    exact hu.2
  -- the common interval
  set δ'' : ℝ := min (min δe D) δI with hδ''def
  have hδ''pos : 0 < δ'' := lt_min (lt_min hδepos hDpos) hδIpos
  have hδ''leD : δ'' ≤ D := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ''leδe : δ'' ≤ δe := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ''leI : δ'' ≤ δI := min_le_right _ _
  have hIle : ∀ u ∈ Ioo (0:ℝ) δ'', clusterInertia m k (x u) ≤ min 1 (ck ^ 2) :=
    fun u hu => le_of_lt (hδI u ⟨hu.1, lt_of_lt_of_le hu.2 hδ''leI⟩)
  have hsmall : ∀ u ∈ Ioo (0:ℝ) δ'', clusterInertia m k (x u) ≤ 1 :=
    fun u hu => le_trans (hIle u hu) (min_le_left _ _)
  have hsqrtI : ∀ u ∈ Ioo (0:ℝ) δ'', Real.sqrt (clusterInertia m k (x u)) ≤ ck := by
    intro u hu
    have h1 : clusterInertia m k (x u) ≤ ck ^ 2 := le_trans (hIle u hu) (min_le_right _ _)
    calc Real.sqrt (clusterInertia m k (x u)) ≤ Real.sqrt (ck ^ 2) := Real.sqrt_le_sqrt h1
      _ = ck := Real.sqrt_sq hckpos.le
  have hU1 : ∀ u ∈ Ioo (0:ℝ) δ'', 1 ≤ clusterPotential m k (x u) := by
    intro u hu
    have hncx : WithoutCollisions (x u) := hncD u ⟨hu.1, lt_of_lt_of_le hu.2 hδ''leD⟩
    have h1 := hcksp (x u) hncx
    have h2 : Real.sqrt (clusterInertia m k (x u)) ≤ ck := hsqrtI u hu
    have h3 : 0 < Real.sqrt (clusterInertia m k (x u)) :=
      Real.sqrt_pos.mpr (clusterInertia_pos hm hk2 hncx)
    have h4 : ck / ck ≤ ck / Real.sqrt (clusterInertia m k (x u)) :=
      div_le_div_of_nonneg_left hckpos.le h3 h2
    have h5 : ck / ck = 1 := div_self (ne_of_gt hckpos)
    linarith [h1, h4, h5.le]
  have hE'' : ∀ u ∈ Ioo (0:ℝ) δ'', |clusterRelEnergy m k (x u) (deriv x u)| ≤ C := by
    intro u hu
    refine le_trans (henergy u ⟨hu.1, lt_of_lt_of_le hu.2 hδ''leδe⟩) hCeC
  have hW'' : ∀ u ∈ Ioo (0:ℝ) δ'',
      |crossWork m k (x u) (cmRel m k (x u))| ≤ C := by
    intro u hu
    have huD : u ∈ Ioo (0:ℝ) D := ⟨hu.1, lt_of_lt_of_le hu.2 hδ''leD⟩
    have h1 := abs_crossWork_cmRel_le (m := m) (k := k) (x := x u) (v := x u) (ν := ν)
      hm hν (hsepwD u huD)
    have h2 : clusterRelKinetic m k (x u) = clusterInertia m k (x u) :=
      clusterRelKinetic_eq_clusterInertia m k (x u)
    rw [h2] at h1
    refine le_trans (le_trans h1 ?_) hCwC
    have hs : Real.sqrt (clusterInertia m k (x u)) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (hsmall u hu)
    have hnn : 0 ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) := by
      have h := hCw0; rw [hCwdef] at h; exact h
    calc 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
          * Real.sqrt (clusterInertia m k (x u))
        ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) * 1 :=
          mul_le_mul_of_nonneg_left hs hnn
      _ = 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) := by ring
  -- the conversion from the acceleration scale to the potential scale
  have hconv := sqrt_secondDeriv_add_le_sqrt_potential (m := m) (k := k) (x := x) (ε := δ'')
    (C := C) (C' := C') hm hkne hδ''pos hE'' hW''
    (fun u hu => hx u ⟨hu.1, lt_of_lt_of_le hu.2 hδ''leD⟩)
    (fun u hu => hd2 u ⟨hu.1, lt_of_lt_of_le hu.2 hδ''leD⟩)
    (fun u hu => hode u ⟨hu.1, lt_of_lt_of_le hu.2 hδ''leD⟩)
    (fun u hu => hncD u ⟨hu.1, lt_of_lt_of_le hu.2 hδ''leD⟩) hU1
  refine ⟨Cv' * Real.sqrt (2 + max 0 (6 * C + 4 * C')), by positivity, ?_⟩
  filter_upwards [hself, hconv] with u hself_u hconv_u
  intro j hj
  dsimp only [x] at hself_u hconv_u ⊢
  calc ‖deriv γ (t₀ + u) j‖
      ≤ Cv' * Real.sqrt (deriv (deriv (fun s : ℝ => clusterInertia m k (γ (t₀ + s)))) u
          + 4 * C') := hself_u j hj
    _ ≤ Cv' * (Real.sqrt (2 + max 0 (6 * C + 4 * C'))
          * Real.sqrt (clusterPotential m k (γ (t₀ + u)))) :=
        mul_le_mul_of_nonneg_left hconv_u hCv'0.le
    _ = Cv' * Real.sqrt (2 + max 0 (6 * C + 4 * C'))
          * Real.sqrt (clusterPotential m k (γ (t₀ + u))) := by ring

end Submission.NBody
