import Submission.NBody.MarchalMultiInertia
import Submission.NBody.MarchalMultiOstrogradsky
import Submission.NBody.MarchalIsolatedCollision
import Submission.NBody.MarchalCollPartition
import Submission.NBody.MarchalMultiEnergyBoundAtCollision

/-!
# A locally minimal collision is isolated (sum-level form)

At an interior collision time there may be several collision classes.  The relative energy of a
single class is not a priori bounded (the other classes blow up), but the *sum* of the relative
energies of all the classes is.  Following Ferrario--Terracini one therefore runs the
Rolle--Sperner argument for

    `F = multiInertia m ks ∘ γ`,   `ks = collClasses γ t₁`,

whose Lagrange--Jacobi identity reads `F'' = 4·E^{rel} + 2·U + 2·W` with `E^{rel} = multiRelEnergy`
(the sum of the relative energies, bounded by `exists_multiRelEnergy_bound_at_collision`),
`U = multiPotential` (Sperner: `exists_const_le_multiPotential`) and
`W = multiCrossWork` (the positional work bound, obtained by summing the single-class bounds).

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

/-- The sum of the moments of inertia is continuous. -/
lemma continuous_multiInertia (m : Fin N → ℝ) (ks : Finset (Finset (Fin N))) :
    Continuous (fun x : EN E N => multiInertia m ks x) := by
  have hunfold : multiInertia m ks = fun x : EN E N => ∑ k ∈ ks, clusterInertia m k x := rfl
  rw [hunfold]
  exact continuous_finsetSum _ fun k _ => continuous_clusterInertia m k

/-! ## 1. The Lagrange--Jacobi identity for `multiInertia`, pointwise -/

/-- If the derivative relation holds eventually at `t`, it holds eventually at every nearby point
(an eventual statement gives an open neighbourhood). -/
lemma eventually_eventually_hasDerivAt_of_eventually {x : ℝ → EN E N} {t : ℝ}
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s) :
    ∀ᶠ s in 𝓝 t, ∀ᶠ r in 𝓝 s, HasDerivAt x (deriv x r) r := by
  rcases _root_.mem_nhds_iff.mp hx with ⟨U, hUsub, hUopen, htU⟩
  filter_upwards [hUopen.mem_nhds htU] with s hs
  exact Filter.eventually_of_mem (hUopen.mem_nhds hs) hUsub

/-- **The derivative of the derivative of the sum of the moments of inertia**, pointwise. -/
lemma hasDerivAt_deriv_multiInertia_pointwise {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {t : ℝ}
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : HasDerivAt (deriv x) (deriv (deriv x) t) t) :
    HasDerivAt (deriv (fun s : ℝ => multiInertia m ks (x s)))
      (deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t) t := by
  have hxloc := eventually_eventually_hasDerivAt_of_eventually hx
  have hderiv : deriv (fun s : ℝ => multiInertia m ks (x s)) =ᶠ[𝓝 t]
      (fun s : ℝ => ∑ k ∈ ks, deriv (fun r : ℝ => clusterInertia m k (x r)) s) := by
    filter_upwards [hxloc] with s hs
    have hsum := hasDerivAt_sum_apply ks (fun k (r : ℝ) => clusterInertia m k (x r))
      (fun k => deriv (fun r : ℝ => clusterInertia m k (x r)) s) s
      (fun k _ => hasDerivAt_clusterInertia_curve (k := k) (t := s) (x := x) hs)
    exact hsum.deriv
  have hsum2 : HasDerivAt
      (fun s : ℝ => ∑ k ∈ ks, deriv (fun r : ℝ => clusterInertia m k (x r)) s)
      (∑ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t) t :=
    hasDerivAt_sum_apply ks (fun k (s : ℝ) => deriv (fun r : ℝ => clusterInertia m k (x r)) s)
      (fun k => deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t) t
      (fun k _ => hasDerivAt_deriv_clusterInertia_curve (k := k) (t := t) hx hd2)
  have hval : deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
      = ∑ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t := by
    rw [Filter.EventuallyEq.deriv_eq hderiv]
    exact hsum2.deriv
  rw [hval]
  exact hsum2.congr_of_eventuallyEq hderiv

/-- **The Lagrange--Jacobi identity for a family of clusters**, pointwise form. -/
theorem deriv_deriv_multiInertia_pointwise {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {t : ℝ} (hm : ∀ i, 0 < m i) (hne : ∀ k ∈ ks, k.Nonempty)
    (hnc : WithoutCollisions (x t))
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : iteratedDeriv 2 x t = ∇_[m] (U m) (x t)) :
    deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
      = 4 * multiRelEnergy m ks (x t) (deriv x t)
        + 2 * multiPotential m ks (x t) + 2 * multiCrossWork m ks (x t) := by
  have hxloc := eventually_eventually_hasDerivAt_of_eventually hx
  have hderiv : deriv (fun s : ℝ => multiInertia m ks (x s)) =ᶠ[𝓝 t]
      (fun s : ℝ => ∑ k ∈ ks, deriv (fun r : ℝ => clusterInertia m k (x r)) s) := by
    filter_upwards [hxloc] with s hs
    have hsum := hasDerivAt_sum_apply ks (fun k (r : ℝ) => clusterInertia m k (x r))
      (fun k => deriv (fun r : ℝ => clusterInertia m k (x r)) s) s
      (fun k _ => hasDerivAt_clusterInertia_curve (k := k) (t := s) (x := x) hs)
    exact hsum.deriv
  have hsum2 : HasDerivAt
      (fun s : ℝ => ∑ k ∈ ks, deriv (fun r : ℝ => clusterInertia m k (x r)) s)
      (∑ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t) t :=
    hasDerivAt_sum_apply ks (fun k (s : ℝ) => deriv (fun r : ℝ => clusterInertia m k (x r)) s)
      (fun k => deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t) t
      (fun k _ => hasDerivAt_deriv_clusterInertia_curve (k := k) (t := t) hx
        (hd2.congr_deriv (iteratedDeriv_two_eq_deriv_deriv x t)))
  have hval : deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
      = ∑ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t := by
    rw [Filter.EventuallyEq.deriv_eq hderiv]
    exact hsum2.deriv
  have hcluster : ∀ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t
      = 4 * clusterRelEnergy m k (x t) (deriv x t) + 2 * clusterPotential m k (x t)
        + 2 * crossWork m k (x t) (cmRel m k (x t)) :=
    fun k hk => deriv_deriv_clusterInertia_curve_eq hm (hne k hk) hnc hx hd2 hode
  rw [hval, Finset.sum_congr rfl hcluster]
  simp only [multiRelEnergy, multiPotential, multiCrossWork]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]

/-! ## 2. The position of the zero set of `multiInertia` -/

/-- **`multiInertia` vanishes exactly when every cluster of the family fully collides.** -/
lemma multiInertia_eq_zero_iff {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    (ks : Finset (Finset (Fin N))) (x : EN E N) :
    multiInertia m ks x = 0 ↔ ∀ k ∈ ks, ∀ i ∈ k, ∀ j ∈ k, x i = x j := by
  rw [multiInertia, Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => clusterInertia_nonneg (fun i => (hm i).le) k x)]
  constructor
  · intro h k hk
    exact (clusterInertia_eq_zero_iff hm k x).mp (h k hk)
  · intro h k hk
    exact (clusterInertia_eq_zero_iff hm k x).mpr (h k hk)

/-! ## 3. The positional work bound for a family of clusters -/

/-- **The interaction work of a family of clusters.**  Under the one-sided separation of every
cluster from its complement, `|multiCrossWork| ≤ cW · √(multiInertia)` with
`cW = ∑_{k∈ks} 2(ν⁻¹)²(∑m)√(m_k)`. -/
theorem abs_multiCrossWork_le {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))} {x : EN E N}
    {ν : ℝ} (hm : ∀ i, 0 < m i) (hν : 0 < ν)
    (hsep : ∀ k ∈ ks, ClusterSeparatedWeak k x ν) :
    |multiCrossWork m ks x|
      ≤ (∑ k ∈ ks, 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k))
          * Real.sqrt (multiInertia m ks x) := by
  classical
  have hIk : ∀ k ∈ ks, 0 ≤ clusterInertia m k x :=
    fun k _ => clusterInertia_nonneg (fun i => (hm i).le) k x
  have hle : ∀ k ∈ ks, clusterInertia m k x ≤ multiInertia m ks x :=
    fun k hk => Finset.single_le_sum (f := fun k => clusterInertia m k x)
      (fun k _ => hIk k ‹k ∈ ks›) hk
  have hstep : ∀ k ∈ ks, |crossWork m k x (cmRel m k x)|
      ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
          * Real.sqrt (multiInertia m ks x) := by
    intro k hk
    have h1 := abs_crossWork_cmRel_le (m := m) (k := k) (x := x) (v := x) hm hν (hsep k hk)
    have h3 : clusterRelKinetic m k x = clusterInertia m k x :=
      clusterRelKinetic_eq_clusterInertia m k x
    rw [h3] at h1
    have h4 : Real.sqrt (clusterInertia m k x) ≤ Real.sqrt (multiInertia m ks x) :=
      Real.sqrt_le_sqrt (hle k hk)
    have h5 : 0 ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (Finset.sum_nonneg fun j _ => (hm j).le))
        (Real.sqrt_nonneg _)
    calc |crossWork m k x (cmRel m k x)|
        ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
            * Real.sqrt (clusterInertia m k x) := h1
      _ ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
            * Real.sqrt (multiInertia m ks x) :=
          mul_le_mul_of_nonneg_left h4 h5
  calc |multiCrossWork m ks x|
      = |∑ k ∈ ks, crossWork m k x (cmRel m k x)| := rfl
    _ ≤ ∑ k ∈ ks, |crossWork m k x (cmRel m k x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ ks, 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
          * Real.sqrt (multiInertia m ks x) := Finset.sum_le_sum hstep
    _ = (∑ k ∈ ks, 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k))
          * Real.sqrt (multiInertia m ks x) := by
        rw [Finset.sum_mul]


/-! ## 4. The zero set of `multiInertia` for the collision classes -/

/-- If the colliding pairs at the times `t` and `t₁` coincide, then every cluster of
`collClasses γ t₁` fully collides at the time `t`. -/
lemma multiInertia_collClasses_eq_zero_of_collPairs_eq {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {γ : ℝ → EN E N} {t t₁ : ℝ} (h : collPairs γ t = collPairs γ t₁) :
    multiInertia m (collClasses γ t₁) (γ t) = 0 := by
  classical
  rw [multiInertia_eq_zero_iff hm]
  intro k hk i hi j hj
  obtain ⟨i₀, rfl, -⟩ := mem_collClasses.mp hk
  rw [mem_collClass] at hi hj
  have hij : γ t₁ i = γ t₁ j := hi.trans hj.symm
  by_cases hij' : i = j
  · rw [hij']
  · have hmem : (i, j) ∈ collPairs γ t₁ := mem_collPairs.mpr ⟨hij', hij⟩
    rw [← h] at hmem
    exact (mem_collPairs.mp hmem).2

/-! ## 5. The Rolle--Sperner contradiction for a family of clusters -/

/-- **The Rolle--Sperner contradiction (sum level).**  If `F = multiInertia m ks ∘ γ` is
continuous on `W`, solves Newton's equations (and is collision free) wherever it is positive, if
the Sperner bound `cS/√F ≤ U`, the positional bound `|W_c| ≤ cW √F` and the lower bound
`E ≥ -C₁` for the *sum* of the relative energies hold on `{F > 0}`, and if `F < θ²` on `[a,b]`
for a `θ` with `(2C₁ + cW + 1)θ ≤ cS`, then two zeros of `F` at the ends of `[a,b]` with a
positive value in between are impossible. -/
theorem false_of_sandwich_multiSperner {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {γ : ℝ → EN E N} {W : Set ℝ} {a b cS cW C₁ θ : ℝ} (hm : ∀ i, 0 < m i)
    (hne : ∀ k ∈ ks, k.Nonempty) (hab : a < b) (habW : Icc a b ⊆ W)
    (hcont : ContinuousOn (fun t : ℝ => multiInertia m ks (γ t)) W)
    (ha : multiInertia m ks (γ a) = 0) (hb : multiInertia m ks (γ b) = 0)
    (hpos : ∃ x ∈ Ioo a b, 0 < multiInertia m ks (γ x))
    (hnc : ∀ t ∈ W, 0 < multiInertia m ks (γ t) → WithoutCollisions (γ t))
    (hsol : ∀ t ∈ W, 0 < multiInertia m ks (γ t) →
      (∀ᶠ s in 𝓝 t, HasDerivAt γ (deriv γ s) s) ∧
      HasDerivAt (deriv γ) (iteratedDeriv 2 γ t) t ∧
      iteratedDeriv 2 γ t = ∇_[m] (U m) (γ t))
    (hcS : 0 < cS)
    (hSperner : ∀ t ∈ W, 0 < multiInertia m ks (γ t) →
      cS / Real.sqrt (multiInertia m ks (γ t)) ≤ multiPotential m ks (γ t))
    (hcW : 0 < cW)
    (hW : ∀ t ∈ W, 0 < multiInertia m ks (γ t) →
      |multiCrossWork m ks (γ t)| ≤ cW * Real.sqrt (multiInertia m ks (γ t)))
    (hc1 : 0 ≤ C₁)
    (hE : ∀ t ∈ W, 0 < multiInertia m ks (γ t) →
      -C₁ ≤ multiRelEnergy m ks (γ t) (deriv γ t))
    (hθpos : 0 < θ) (hθ1 : θ ≤ 1) (hθ : (2 * C₁ + cW + 1) * θ ≤ cS)
    (hsmall : ∀ t ∈ Icc a b, multiInertia m ks (γ t) < θ ^ 2) : False := by
  classical
  obtain ⟨t, ht, hmax, -⟩ :=
    Commons.Analysis.Interval.interior_argmax_of_zero_ends hab (hcont.mono habW) ha hb hpos
  have hFt : 0 < multiInertia m ks (γ t) := by
    obtain ⟨x, hx, hfx⟩ := hpos
    exact lt_of_lt_of_le hfx (hmax x (Ioo_subset_Icc_self hx))
  have htW : t ∈ W := habW (Ioo_subset_Icc_self ht)
  obtain ⟨hxev, hd2γ, hode⟩ := hsol t htW hFt
  have hd1 : HasDerivAt (fun s : ℝ => multiInertia m ks (γ s))
      (deriv (fun s : ℝ => multiInertia m ks (γ s)) t) t := hasDerivAt_multiInertia_curve hxev
  have hd2 : HasDerivAt (deriv (fun s : ℝ => multiInertia m ks (γ s)))
      (deriv (deriv (fun s : ℝ => multiInertia m ks (γ s))) t) t :=
    hasDerivAt_deriv_multiInertia_pointwise hxev
      (hd2γ.congr_deriv (iteratedDeriv_two_eq_deriv_deriv γ t))
  have hloc : IsLocalMax (fun s : ℝ => multiInertia m ks (γ s)) t := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
    exact hmax y (Ioo_subset_Icc_self hy)
  have hzero : deriv (fun s : ℝ => multiInertia m ks (γ s)) t = 0 := hloc.deriv_eq_zero
  have hsecond : deriv (deriv (fun s : ℝ => multiInertia m ks (γ s))) t ≤ 0 :=
    Commons.Analysis.Calculus.deriv_deriv_nonpos_of_localMax (hd1.congr_deriv hzero) hd2 hloc
  have hLJ : deriv (deriv (fun s : ℝ => multiInertia m ks (γ s))) t
      = 4 * multiRelEnergy m ks (γ t) (deriv γ t) + 2 * multiPotential m ks (γ t)
        + 2 * multiCrossWork m ks (γ t) :=
    deriv_deriv_multiInertia_pointwise hm hne (hnc t htW hFt) hxev hd2γ hode
  rw [hLJ] at hsecond
  have hE' := hE t htW hFt
  have hWt := hW t htW hFt
  have hWlow : -cW * Real.sqrt (multiInertia m ks (γ t)) ≤ multiCrossWork m ks (γ t) := by
    have h1 := neg_abs_le (multiCrossWork m ks (γ t))
    linarith [hWt, h1]
  have hkey : 2 * multiPotential m ks (γ t)
      ≤ 4 * C₁ + 2 * cW * Real.sqrt (multiInertia m ks (γ t)) := by
    linarith [hsecond, hE', hWlow]
  have hroot : 0 < Real.sqrt (multiInertia m ks (γ t)) := Real.sqrt_pos.mpr hFt
  have hsq : Real.sqrt (multiInertia m ks (γ t)) * Real.sqrt (multiInertia m ks (γ t))
      = multiInertia m ks (γ t) := by
    rw [← sq, Real.sq_sqrt (multiInertia_nonneg (fun i => (hm i).le) ks (γ t))]
  have hsperner := hSperner t htW hFt
  have hkey' : cS ≤ 2 * C₁ * Real.sqrt (multiInertia m ks (γ t))
      + cW * multiInertia m ks (γ t) := by
    have h1 : cS / Real.sqrt (multiInertia m ks (γ t)) * Real.sqrt (multiInertia m ks (γ t))
        ≤ (2 * C₁ + cW * Real.sqrt (multiInertia m ks (γ t)))
          * Real.sqrt (multiInertia m ks (γ t)) := by
      refine mul_le_mul_of_nonneg_right ?_ hroot.le
      linarith [hsperner, hkey]
    have h2 : cS / Real.sqrt (multiInertia m ks (γ t)) * Real.sqrt (multiInertia m ks (γ t))
        = cS := by field_simp
    have h3 : (2 * C₁ + cW * Real.sqrt (multiInertia m ks (γ t)))
          * Real.sqrt (multiInertia m ks (γ t))
        = 2 * C₁ * Real.sqrt (multiInertia m ks (γ t)) + cW * multiInertia m ks (γ t) := by
      have h4 : cW * Real.sqrt (multiInertia m ks (γ t)) * Real.sqrt (multiInertia m ks (γ t))
          = cW * multiInertia m ks (γ t) := by rw [mul_assoc, hsq]
      rw [add_mul, h4]
    linarith [h1, h2, h3]
  have hroot_lt : Real.sqrt (multiInertia m ks (γ t)) < θ :=
    (Real.sqrt_lt' hθpos).mpr (hsmall t (Ioo_subset_Icc_self ht))
  have hIlt : multiInertia m ks (γ t) < θ := by
    nlinarith [hsmall t (Ioo_subset_Icc_self ht), hθpos, hθ1]
  have hb1 : 2 * C₁ * Real.sqrt (multiInertia m ks (γ t)) ≤ 2 * C₁ * θ :=
    mul_le_mul_of_nonneg_left hroot_lt.le (by linarith)
  have hb2 : cW * multiInertia m ks (γ t) ≤ cW * θ := mul_le_mul_of_nonneg_left hIlt.le hcW.le
  have hlt : (2 * C₁ + cW) * θ < (2 * C₁ + cW + 1) * θ := by nlinarith [hθpos]
  linarith [hkey', hb1, hb2, hlt, hθ]

/-! ## 6. No sandwiched zeros near a locally minimal collision (sum level) -/

/-- **No sandwiched zeros near a locally minimal collision** (sum level).  Under the hypotheses of
the Rolle--Sperner contradiction, with the constants produced internally from Sperner's bound and
the positional work bound, no interval `[a,b]` close to `t₁` whose endpoints are zeros of
`multiInertia` can contain a positive value. -/
theorem exists_no_sandwich_multi {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))} {γ : ℝ → EN E N}
    {W : Set ℝ} {t₁ ν C₁ : ℝ} (hm : ∀ i, 0 < m i) (hksne : ks.Nonempty)
    (hne2 : ∀ k ∈ ks, 2 ≤ k.card)
    (hcont : ContinuousOn (fun t : ℝ => multiInertia m ks (γ t)) W)
    (ht₁W : t₁ ∈ W)
    (hF0 : multiInertia m ks (γ t₁) = 0)
    (hnc : ∀ t ∈ W, 0 < multiInertia m ks (γ t) → WithoutCollisions (γ t))
    (hsol : ∀ t ∈ W, 0 < multiInertia m ks (γ t) →
      (∀ᶠ s in 𝓝 t, HasDerivAt γ (deriv γ s) s) ∧
      HasDerivAt (deriv γ) (iteratedDeriv 2 γ t) t ∧
      iteratedDeriv 2 γ t = ∇_[m] (U m) (γ t))
    (hν : 0 < ν)
    (hsep : ∀ t ∈ W, 0 < multiInertia m ks (γ t) → ∀ k ∈ ks, ClusterSeparatedWeak k (γ t) ν)
    (hc1 : 0 ≤ C₁)
    (hE : ∀ t ∈ W, 0 < multiInertia m ks (γ t) →
      -C₁ ≤ multiRelEnergy m ks (γ t) (deriv γ t)) :
    ∃ η > 0, η ≤ 1 ∧ ∀ a b : ℝ, a < b → Icc a b ⊆ W → |a - t₁| < η → |b - t₁| < η →
      multiInertia m ks (γ a) = 0 → multiInertia m ks (γ b) = 0 →
      ¬ ∃ x ∈ Ioo a b, 0 < multiInertia m ks (γ x) := by
  classical
  obtain ⟨cS, hcS, hSp⟩ := exists_const_le_multiPotential (E := E) hm ks hne2
  have hne : ∀ k ∈ ks, k.Nonempty := fun k hk => Finset.card_pos.mp (by have := hne2 k hk; omega)
  set cW : ℝ := ∑ k ∈ ks, 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
    with hcWdef
  have hfacpos : ∀ k ∈ ks, 0 < 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) := by
    intro k hk
    have hkne : k.Nonempty := hne k hk
    obtain ⟨i, hi⟩ := hkne
    have hsum : 0 < ∑ j : Fin N, m j :=
      lt_of_lt_of_le (hm i) (Finset.single_le_sum (f := m) (fun j _ => (hm j).le)
        (Finset.mem_univ i))
    have hkne' : k.Nonempty := ⟨i, hi⟩
    have hcm : 0 < clusterMass m k := clusterMass_pos hm hkne'
    have h1 : 0 < (ν⁻¹) ^ 2 := pow_pos (inv_pos.mpr hν) 2
    have h2 : 0 < Real.sqrt (clusterMass m k) := Real.sqrt_pos.mpr hcm
    have h3 : 0 < 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) := by positivity
    exact mul_pos h3 h2
  have hcWpos : 0 < cW := by
    rw [hcWdef]
    obtain ⟨k₀, hk₀⟩ := hksne
    exact Finset.sum_pos (fun k hk => hfacpos k hk) ⟨k₀, hk₀⟩
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
  have hcontAt : ContinuousWithinAt (fun t : ℝ => multiInertia m ks (γ t)) W t₁ := hcont t₁ ht₁W
  have hev : ∀ᶠ t in 𝓝[W] t₁, multiInertia m ks (γ t) < θ ^ 2 :=
    hcontAt.eventually (isOpen_Iio.mem_nhds (by simp only [hF0]; exact hθ2pos))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨min δ 1, lt_min hδpos one_pos, min_le_right _ _, ?_⟩
  intro a b hab habW ha' hb' ha hb hpos'
  refine false_of_sandwich_multiSperner (W := W) (a := a) (b := b) (cS := cS) (cW := cW)
    (C₁ := C₁) (θ := θ) hm hne hab habW hcont ha hb hpos' hnc hsol hcS ?_ hcWpos ?_ hc1 hE
    hθpos hθ1 hθ ?_
  · intro t htW hFt
    exact hSp (γ t) (hnc t htW hFt)
  · intro t htW hFt
    rw [hcWdef]
    exact abs_multiCrossWork_le (m := m) (ks := ks) (x := γ t) (ν := ν) hm hν
      (hsep t htW hFt)
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

/-! ## 7. A locally minimal collision is isolated (sum level) -/

/-- **A locally minimal collision is isolated** (sum level).  If `γ` is an `h`-minimiser with a
collision time `t₁` whose colliding-pair set is locally constant, and the *sum* of the relative
energies of all the collision classes is bounded below near `t₁`, then `t₁` is the only collision
time of `Icc c d` close to it. -/
theorem isolated_of_local_min_multi {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b c d t₁ C₁ εE : ℝ} (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (hcd : Icc c d ⊆ Ioo a b) (ht₁ : t₁ ∈ Icc c d)
    (hcoll₁ : ¬ WithoutCollisions (γ t₁))
    (hloc : ∃ ε > 0, ∀ t ∈ Icc c d, |t - t₁| < ε → (∃ i j, i ≠ j ∧ γ t i = γ t j) →
      collPairs γ t = collPairs γ t₁)
    (hεEpos : 0 < εE)
    (hc1 : 0 ≤ C₁)
    (hE : ∀ t ∈ Icc c d, |t - t₁| < εE → 0 < multiInertia m (collClasses γ t₁) (γ t) →
      -C₁ ≤ multiRelEnergy m (collClasses γ t₁) (γ t) (deriv γ t)) :
    ∃ η > 0, η ≤ 1 ∧ ∀ t ∈ Icc c d, |t - t₁| < η → t ≠ t₁ → WithoutCollisions (γ t) := by
  classical
  set ks : Finset (Finset (Fin N)) := collClasses γ t₁ with hksdef
  have hksne : ks.Nonempty := by
    obtain ⟨i₁, j₁, hij₁, heq₁⟩ : ∃ i j : Fin N, i ≠ j ∧ γ t₁ i = γ t₁ j := by
      by_contra h
      refine hcoll₁ fun i j hij hcon => h ⟨i, j, hij, ?_⟩
      rw [r_eq_norm_sub, norm_eq_zero, sub_eq_zero] at hcon
      exact hcon
    exact ⟨collClass γ t₁ i₁, mem_collClasses.mpr ⟨i₁, rfl,
      two_le_card_collClass_of_exists hij₁.symm heq₁.symm⟩⟩
  have hne2 : ∀ k ∈ ks, 2 ≤ k.card := fun k hk => collClasses_card hk
  have hne : ∀ k ∈ ks, k.Nonempty := fun k hk => Finset.card_pos.mp (by have := hne2 k hk; omega)
  have hF0 : multiInertia m ks (γ t₁) = 0 :=
    multiInertia_collClasses_eq_zero_of_collPairs_eq hm rfl
  have hcontab : ContinuousOn γ (Icc a b) := by
    have h := hac.continuousOn
    rwa [uIcc_of_le hab.le] at h
  have ht₁Ioo : t₁ ∈ Ioo a b := hcd ht₁
  have hcontcd : ContinuousOn γ (Icc c d) :=
    hcontab.mono (fun t ht => ⟨(hcd ht).1.le, (hcd ht).2.le⟩)
  obtain ⟨ν, hνpos, ε₀, hε₀pos, hsepc⟩ := exists_separation_of_collClasses
    (γ := γ) (a := a) (b := b) (t₀ := t₁) hcontab ht₁Ioo
  obtain ⟨ε, hεpos, hloc'⟩ := hloc
  set ε' : ℝ := min (min ε ε₀) εE with hε'def
  have hε'pos : 0 < ε' := lt_min (lt_min hεpos hε₀pos) hεEpos
  have hε'le_ε : ε' ≤ ε := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε'le_εE : ε' ≤ εE := min_le_right _ _
  set W : Set ℝ := Icc c d ∩ Metric.ball t₁ ε' with hWdef
  have ht₁W : t₁ ∈ W := ⟨ht₁, by
    rw [Metric.mem_ball, Real.dist_eq, sub_self, abs_zero]
    exact hε'pos⟩
  have hcontW : ContinuousOn (fun t : ℝ => multiInertia m ks (γ t)) W :=
    ((continuous_multiInertia m ks).comp_continuousOn hcontcd).mono (fun t ht => ht.1)
  -- zeros of `F` are collisions
  have hzero : ∀ t ∈ W, (∃ i j, i ≠ j ∧ γ t i = γ t j) →
      multiInertia m ks (γ t) = 0 := by
    intro t ht hcol
    have hlt_ε : |t - t₁| < ε := by
      have hb : t ∈ Metric.ball t₁ ε' := ht.2
      rw [Metric.mem_ball, Real.dist_eq] at hb
      exact lt_of_lt_of_le hb hε'le_ε
    exact multiInertia_collClasses_eq_zero_of_collPairs_eq hm
      (hloc' t ht.1 hlt_ε hcol)
  have hncW : ∀ t ∈ W, 0 < multiInertia m ks (γ t) → WithoutCollisions (γ t) := by
    intro t ht hFt
    by_contra hcol
    have h1 : ∃ i j, i ≠ j ∧ γ t i = γ t j := by
      by_contra h
      exact hcol fun i j hij hr => h ⟨i, j, hij, by
        rw [r_eq_norm_sub, norm_eq_zero, sub_eq_zero] at hr
        exact hr⟩
    exact absurd (hzero t ht h1) (ne_of_gt hFt)
  -- the Newton data on `{F > 0}`
  have hsolW : ∀ t ∈ W, 0 < multiInertia m ks (γ t) →
      (∀ᶠ s in 𝓝 t, HasDerivAt γ (deriv γ s) s) ∧
      HasDerivAt (deriv γ) (iteratedDeriv 2 γ t) t ∧
      iteratedDeriv 2 γ t = ∇_[m] (U m) (γ t) := by
    intro t ht hFt
    have h := exists_solution_data_of_minimizer (m := m) (h := h) hm hh hab hac hmin hfin
      (S := {s : ℝ | s ∈ W ∧ 0 < multiInertia m ks (γ s)})
      (fun s hs => hcd hs.1.1)
      (fun s hs => hncW s hs.1 hs.2)
    exact h t ⟨ht, hFt⟩
  -- the one-sided separation
  have hsepW : ∀ t ∈ W, 0 < multiInertia m ks (γ t) →
      ∀ k ∈ ks, ClusterSeparatedWeak k (γ t) ν := by
    intro t ht _
    have hb : t ∈ Metric.ball t₁ ε' := ht.2
    rw [Metric.mem_ball, Real.dist_eq] at hb
    have hlt : |t - t₁| < ε₀ := lt_of_lt_of_le hb (le_trans (min_le_left _ _) (min_le_right _ _))
    have hmem : t ∈ Ioo (t₁ - ε₀) (t₁ + ε₀) := by
      rw [abs_lt] at hlt
      exact ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
    exact (hsepc t hmem).1
  -- the no-sandwich statement
  obtain ⟨ηs, hηspos, hηs1, hns⟩ := exists_no_sandwich_multi (m := m) (ks := ks) (γ := γ)
    (W := W) (t₁ := t₁) (ν := ν) (C₁ := C₁) hm hksne hne2 hcontW ht₁W hF0 hncW hsolW
    hνpos hsepW hc1 (fun t ht hFt => hE t ht.1
      (by have hb := ht.2; rw [Metric.mem_ball, Real.dist_eq] at hb; linarith [hε'le_εE]) hFt)
  -- the density of `{F > 0}`
  have hfinOn : actionOn m h γ a b < ⊤ :=
    IsHMinimizer.actionOn_lt_top hmin (hfin (γ a) (γ b))
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ t) :=
    ae_withoutCollisions_of_actionOn_lt_top hac hfinOn
  have hnull : volume ({t : ℝ | ¬ WithoutCollisions (γ t)} ∩ Ioo a b) = 0 := by
    have h1 : volume (({t : ℝ | ¬ WithoutCollisions (γ t)}) ∩ Set.Ioc a b) = 0 := by
      have h2 := MeasureTheory.ae_iff.mp hae
      simpa [Set.inter_comm] using h2
    refine measure_mono_null ?_ h1
    exact Set.inter_subset_inter_right _ (fun t ht => ⟨ht.1, ht.2.le⟩)
  have hdensity : ∀ a' b' : ℝ, a' < b' → Icc a' b' ⊆ W → |a' - t₁| < ηs → |b' - t₁| < ηs →
      ∃ x ∈ Ioo a' b', 0 < multiInertia m ks (γ x) := by
    intro a' b' hab' hsub _ _
    have hdom : Ioo a' b' ⊆ Ioo a b := fun x hx =>
      hcd (hsub (Set.Ioo_subset_Icc_self hx)).1
    have hnull' : volume ({y : ℝ | ¬ WithoutCollisions (γ y)} ∩ Ioo a' b') = 0 :=
      measure_mono_null (Set.inter_subset_inter_right _ hdom) hnull
    have hpos' : (0:ℝ≥0∞) < volume (Ioo a' b') := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    obtain ⟨x, hx, hxnot⟩ :
        ∃ x ∈ Ioo a' b', x ∉ ({y : ℝ | ¬ WithoutCollisions (γ y)} ∩ Ioo a' b') := by
      by_contra h
      push Not at h
      have hsub' : Ioo a' b' ⊆ ({y : ℝ | ¬ WithoutCollisions (γ y)} ∩ Ioo a' b') :=
        fun x hx => h x hx
      have hz : volume (Ioo a' b') = 0 := measure_mono_null hsub' hnull'
      rw [hz] at hpos'
      exact absurd hpos' (lt_irrefl 0)
    have hncx : WithoutCollisions (γ x) := by
      by_contra hxc
      exact hxnot ⟨hxc, hx⟩
    have hne0 : multiInertia m ks (γ x) ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := hksne
      have h2 := hne2 k hk
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < k.card)
      exact (hncx i j hij) (by
        rw [r_eq_norm_sub, norm_eq_zero, sub_eq_zero]
        exact (multiInertia_eq_zero_iff hm ks (γ x)).mp h0 k hk i hi j hj)
    exact ⟨x, hx, lt_of_le_of_ne (multiInertia_nonneg (fun i => (hm i).le) ks (γ x))
      (Ne.symm hne0)⟩
  refine ⟨min ηs ε', lt_min hηspos hε'pos, le_trans (min_le_left _ _) hηs1, ?_⟩
  intro t htcd htlt htne
  by_contra hcol
  have hltηs : |t - t₁| < ηs := lt_of_lt_of_le htlt (min_le_left _ _)
  have hltε' : |t - t₁| < ε' := lt_of_lt_of_le htlt (min_le_right _ _)
  have htW : t ∈ W := ⟨htcd, by rw [Metric.mem_ball, Real.dist_eq]; exact hltε'⟩
  have hcol' : ∃ i j, i ≠ j ∧ γ t i = γ t j := by
    by_contra h
    exact hcol fun i j hij hr => h ⟨i, j, hij, by
      rw [r_eq_norm_sub, norm_eq_zero, sub_eq_zero] at hr
      exact hr⟩
  have hFt : multiInertia m ks (γ t) = 0 := hzero t htW hcol'
  rcases lt_or_gt_of_ne htne with hlt | hgt
  · have hsub : Icc t t₁ ⊆ W := by
      intro u hu
      have hut : t ≤ u := (Set.mem_Icc.mp hu).1
      have huu : u ≤ t₁ := (Set.mem_Icc.mp hu).2
      refine ⟨⟨le_trans htcd.1 hut, le_trans huu ht₁.2⟩, ?_⟩
      rw [Metric.mem_ball, Real.dist_eq]
      have h2u : u - t₁ ≤ 0 := by linarith
      have h2t : t - t₁ ≤ 0 := by linarith
      have h1 : |u - t₁| ≤ |t - t₁| := by
        rw [abs_of_nonpos h2u, abs_of_nonpos h2t]
        linarith
      linarith [h1, hltε']
    have hd := hdensity t t₁ hlt hsub hltηs (by simpa using hηspos)
    exact hns t t₁ hlt hsub hltηs (by simpa using hηspos) hFt hF0 hd
  · have hsub : Icc t₁ t ⊆ W := by
      intro u hu
      have hut : t₁ ≤ u := (Set.mem_Icc.mp hu).1
      have huu : u ≤ t := (Set.mem_Icc.mp hu).2
      refine ⟨⟨le_trans ht₁.1 hut, le_trans huu htcd.2⟩, ?_⟩
      rw [Metric.mem_ball, Real.dist_eq]
      have h2u : 0 ≤ u - t₁ := by linarith
      have h2t : 0 ≤ t - t₁ := by linarith
      have h1 : |u - t₁| ≤ |t - t₁| := by
        rw [abs_of_nonneg h2u, abs_of_nonneg h2t]
        linarith
      linarith [h1, hltε']
    have hd := hdensity t₁ t hgt hsub (by simpa using hηspos) hltηs
    exact hns t₁ t hgt hsub (by simpa using hηspos) hltηs hF0 hFt hd


end Submission.NBody
