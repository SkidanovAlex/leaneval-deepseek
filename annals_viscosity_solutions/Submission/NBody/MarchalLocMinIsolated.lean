import Submission.NBody.MarchalClusterPlumbing
import Submission.NBody.MarchalSperner
import Submission.Commons.Analysis.Calculus.exists_localMax_secondDeriv_nonpos
import Submission.Commons.Analysis.Calculus.deriv_deriv_nonpos_of_localMax
import Submission.Commons.Analysis.Interval.interior_argmax_of_zero_ends
import Mathlib

/-!
# The Rolle--Sperner step: a locally minimal collision is isolated (core)

The geometry of the Marchal chapter (F1), fourth layer.  This is the analytic heart of
Ferrario--Terracini's `coro:loc_min`: if a cluster `k` collides at `t₀` (`I_k(γ t₀) = 0`), the
curve solves Newton's equations wherever `I_k ∘ γ > 0`, and the cluster energy and the interaction
work are bounded there, then the zero set of `F := I_k ∘ γ` **cannot** be sandwiched: there is no
pair of zeros `a < b` with `F > 0` in between, arbitrarily close to `t₀`.

Indeed, at the interior maximum of `F` on `[a,b]` (where `F > 0`) the Lagrange--Jacobi identity
`F'' = 4E^{rel} + 2U + 2W` and the second-derivative test give `2U ≤ 4C₁ + 2C₂`, while Sperner's
a priori bound gives `c/√F ≤ U`; hence `F ≥ (c/(2C₁+C₂))²`.  But `F`, which vanishes at `t₀`, is
small on short intervals.

The `[MeasurableSpace E]` instances are *not* needed here and are not assumed.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The Rolle--Sperner contradiction.**  Under the Newton data (usable wherever the cluster has
positive inertia) and the boundedness of the cluster energy and the interaction work there, a
"sandwich" of two zeros of `I_k ∘ γ` surrounding a positive value is impossible, provided the
cluster inertia stays below the threshold `(c/(2C₁+C₂))²` on the interval.

`c` is the Sperner constant of `exists_const_le_clusterPotential`. -/
theorem false_of_zeros_sandwich {m : Fin N → ℝ} {k : Finset (Fin N)} {γ : ℝ → EN E N}
    {a b c C₁ C₂ : ℝ}
    (hm : ∀ i, 0 < m i) (hkne : k.Nonempty) (hc : 0 < c)
    (hSperner : ∀ x : EN E N, WithoutCollisions x →
      c / Real.sqrt (clusterInertia m k x) ≤ clusterPotential m k x)
    (hab : a < b)
    (hcont : ContinuousOn (fun t : ℝ => clusterInertia m k (γ t)) (Icc a b))
    (ha : clusterInertia m k (γ a) = 0) (hb : clusterInertia m k (γ b) = 0)
    (hpos : ∃ x ∈ Ioo a b, 0 < clusterInertia m k (γ x))
    (hnc : ∀ t, 0 < clusterInertia m k (γ t) → WithoutCollisions (γ t))
    (hsol : ∀ t, 0 < clusterInertia m k (γ t) →
      (∀ᶠ s in 𝓝 t, HasDerivAt γ (deriv γ s) s) ∧
      HasDerivAt (deriv γ) (iteratedDeriv 2 γ t) t ∧
      iteratedDeriv 2 γ t = ∇_[m] (U m) (γ t))
    (hE : ∀ t, 0 < clusterInertia m k (γ t) →
      |clusterRelEnergy m k (γ t) (deriv γ t)| ≤ C₁)
    (hW : ∀ t, 0 < clusterInertia m k (γ t) →
      |crossWork m k (γ t) (cmRel m k (γ t))| ≤ C₂)
    (hsmall : ∀ t ∈ Icc a b,
      clusterInertia m k (γ t) < (c / (|2 * C₁ + C₂| + 1)) ^ 2) : False := by
  classical
  set F : ℝ → ℝ := fun t => clusterInertia m k (γ t) with hF
  obtain ⟨t, ht, hmax, -⟩ :=
    Commons.Analysis.Interval.interior_argmax_of_zero_ends hab hcont ha hb hpos
  have hFt : 0 < F t := by
    obtain ⟨x, hx, hfx⟩ := hpos
    exact lt_of_lt_of_le hfx (hmax x (Ioo_subset_Icc_self hx))
  obtain ⟨hxev, hd2γ, hode⟩ := hsol t hFt
  -- the two derivatives of `F`
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
  -- the Lagrange--Jacobi identity at `t`
  have hLJ : deriv (deriv F) t
      = 4 * clusterRelEnergy m k (γ t) (deriv γ t) + 2 * clusterPotential m k (γ t)
        + 2 * crossWork m k (γ t) (cmRel m k (γ t)) :=
    deriv_deriv_clusterInertia_curve_eq hm hkne (hnc t hFt) hxev hd2γ hode
  rw [hLJ] at hsecond
  -- the two-sided bounds
  have hU : c / Real.sqrt (F t) ≤ clusterPotential m k (γ t) := hSperner (γ t) (hnc t hFt)
  have he1 : -C₁ ≤ clusterRelEnergy m k (γ t) (deriv γ t) := (abs_le.mp (hE t hFt)).1
  have he2 : -C₂ ≤ crossWork m k (γ t) (cmRel m k (γ t)) := (abs_le.mp (hW t hFt)).1
  have hsqrtpos : 0 < Real.sqrt (F t) := Real.sqrt_pos.mpr hFt
  have hcq : 0 < c / Real.sqrt (F t) := div_pos hc hsqrtpos
  have h4 : 2 * clusterPotential m k (γ t) ≤ 4 * C₁ + 2 * C₂ := by linarith
  have hkey : c / Real.sqrt (F t) < |2 * C₁ + C₂| + 1 := by
    have h5 : 2 * C₁ + C₂ ≤ |2 * C₁ + C₂| := le_abs_self _
    have h6 : c / Real.sqrt (F t) ≤ 2 * C₁ + C₂ := by linarith
    linarith
  have h3 : c < (|2 * C₁ + C₂| + 1) * Real.sqrt (F t) := (div_lt_iff₀ hsqrtpos).mp hkey
  have hge : c / (|2 * C₁ + C₂| + 1) < Real.sqrt (F t) :=
    (div_lt_iff₀ (by positivity : (0:ℝ) < |2 * C₁ + C₂| + 1)).mpr (by
      rw [mul_comm] at h3; exact h3)
  have h0 : 0 ≤ c / (|2 * C₁ + C₂| + 1) := le_of_lt (div_pos hc (by positivity))
  have hpow : (c / (|2 * C₁ + C₂| + 1)) ^ 2 < F t := by
    have hm := mul_self_lt_mul_self h0 hge
    rw [← sq, ← sq, Real.sq_sqrt hFt.le] at hm
    exact hm
  exact absurd (hsmall t (Ioo_subset_Icc_self ht)) (not_lt.mpr hpow.le)

/-- **No sandwiched zeros near a collision.**  Under the same Newton data, there is a whole
neighbourhood of `t₀` in which no two zeros of `I_k ∘ γ` can surround a positive value.  This is
Ferrario--Terracini's `coro:loc_min` in the form in which the multi-cluster machinery consumes it
(combine with "`I_k ∘ γ` is positive off a null set" to obtain isolatedness of `t₀`). -/
theorem exists_no_sandwich_of_newton_data {m : Fin N → ℝ} {k : Finset (Fin N)} {γ : ℝ → EN E N}
    {t₀ C₁ C₂ : ℝ} (hm : ∀ i, 0 < m i) (hkne : k.Nonempty) (hk2 : 2 ≤ k.card)
    (hcont : ContinuousOn (fun t : ℝ => clusterInertia m k (γ t)) (Icc (t₀ - 1) (t₀ + 1)))
    (hF0 : clusterInertia m k (γ t₀) = 0)
    (hnc : ∀ t, 0 < clusterInertia m k (γ t) → WithoutCollisions (γ t))
    (hsol : ∀ t, 0 < clusterInertia m k (γ t) →
      (∀ᶠ s in 𝓝 t, HasDerivAt γ (deriv γ s) s) ∧
      HasDerivAt (deriv γ) (iteratedDeriv 2 γ t) t ∧
      iteratedDeriv 2 γ t = ∇_[m] (U m) (γ t))
    (hE : ∀ t, 0 < clusterInertia m k (γ t) →
      |clusterRelEnergy m k (γ t) (deriv γ t)| ≤ C₁)
    (hW : ∀ t, 0 < clusterInertia m k (γ t) →
      |crossWork m k (γ t) (cmRel m k (γ t))| ≤ C₂) :
    ∃ η > 0, η ≤ 1 ∧ ∀ a b : ℝ, a < b → |a - t₀| < η → |b - t₀| < η →
      clusterInertia m k (γ a) = 0 → clusterInertia m k (γ b) = 0 →
      ¬ ∃ x ∈ Ioo a b, 0 < clusterInertia m k (γ x) := by
  classical
  obtain ⟨c, hc, hSperner⟩ := exists_const_le_clusterPotential (E := E) hm k hk2
  set θ : ℝ := |2 * C₁ + C₂| + 1 with hθ
  have hθpos : 0 < θ := by rw [hθ]; positivity
  have hthr : 0 < (c / θ) ^ 2 := pow_pos (div_pos hc hθpos) 2
  -- continuity at `t₀` gives a window on which `F` is below the threshold
  have hcontAt : ContinuousAt (fun t : ℝ => clusterInertia m k (γ t)) t₀ :=
    hcont.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hev : ∀ᶠ t in 𝓝 t₀, clusterInertia m k (γ t) < (c / θ) ^ 2 := by
    refine hcontAt.eventually (isOpen_Iio.mem_nhds ?_)
    simp only [Set.mem_Iio]
    rw [hF0]; exact hthr
  obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨min η 1, lt_min hηpos one_pos, min_le_right _ _, fun a b hab ha hb hza hzb => ?_⟩
  rintro ⟨x, hx, hfx⟩
  have hsub : Icc a b ⊆ Icc (t₀ - 1) (t₀ + 1) := by
    refine Icc_subset_Icc ?_ ?_
    · have := abs_lt.mp (lt_of_lt_of_le ha (min_le_right η 1))
      linarith [this.1]
    · have := abs_lt.mp (lt_of_lt_of_le hb (min_le_right η 1))
      linarith [this.2]
  refine false_of_zeros_sandwich (m := m) (k := k) (γ := γ) (a := a) (b := b) (c := c) hm hkne hc
    hSperner hab (hcont.mono hsub) hza hzb ⟨x, hx, hfx⟩ hnc hsol hE hW ?_
  intro t ht
  have ha' : |a - t₀| < min η 1 := ha
  have hb' : |b - t₀| < min η 1 := hb
  have ha'' := abs_lt.mp ha'
  have hb'' := abs_lt.mp hb'
  have h1 : |t - t₀| < min η 1 := by
    rw [abs_lt]
    exact ⟨by linarith [ha''.1, ht.1], by linarith [hb''.2, ht.2]⟩
  have h2 : |t - t₀| < η := lt_of_lt_of_le h1 (min_le_left η 1)
  exact hη t (by rw [Metric.mem_ball, Real.dist_eq]; exact h2)

/-- **A locally minimal collision is isolated** (`coro:loc_min`, final form).  If in addition the
set where `I_k ∘ γ` is positive is dense near `t₀` (e.g. if it is positive almost everywhere, which
holds for a finite-action minimiser), then `I_k ∘ γ` is positive on a punctured neighbourhood of
`t₀`. -/
theorem exists_pos_near_of_dense {m : Fin N → ℝ} {k : Finset (Fin N)} {γ : ℝ → EN E N}
    {t₀ C₁ C₂ : ℝ} (hm : ∀ i, 0 < m i) (hkne : k.Nonempty) (hk2 : 2 ≤ k.card)
    (hcont : ContinuousOn (fun t : ℝ => clusterInertia m k (γ t)) (Icc (t₀ - 1) (t₀ + 1)))
    (hF0 : clusterInertia m k (γ t₀) = 0)
    (hdense : ∀ a b : ℝ, t₀ - 1 < a → a < b → b < t₀ + 1 →
      ∃ x ∈ Ioo a b, 0 < clusterInertia m k (γ x))
    (hnc : ∀ t, 0 < clusterInertia m k (γ t) → WithoutCollisions (γ t))
    (hsol : ∀ t, 0 < clusterInertia m k (γ t) →
      (∀ᶠ s in 𝓝 t, HasDerivAt γ (deriv γ s) s) ∧
      HasDerivAt (deriv γ) (iteratedDeriv 2 γ t) t ∧
      iteratedDeriv 2 γ t = ∇_[m] (U m) (γ t))
    (hE : ∀ t, 0 < clusterInertia m k (γ t) →
      |clusterRelEnergy m k (γ t) (deriv γ t)| ≤ C₁)
    (hW : ∀ t, 0 < clusterInertia m k (γ t) →
      |crossWork m k (γ t) (cmRel m k (γ t))| ≤ C₂) :
    ∃ ε > 0, ∀ t, |t - t₀| < ε → t ≠ t₀ → 0 < clusterInertia m k (γ t) := by
  obtain ⟨η, hηpos, hη1, hno⟩ :=
    exists_no_sandwich_of_newton_data (m := m) (k := k) (γ := γ) (t₀ := t₀) (C₁ := C₁) (C₂ := C₂)
      hm hkne hk2 hcont hF0 hnc hsol hE hW
  refine ⟨η, hηpos, fun t ht hne => ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  have hFt0 : clusterInertia m k (γ t) = 0 :=
    le_antisymm hcon (clusterInertia_nonneg (fun i => (hm i).le) k (γ t))
  have hab : min t t₀ < max t t₀ := by
    rw [min_lt_max]; exact hne
  have ha0 : clusterInertia m k (γ (min t t₀)) = 0 := by
    rcases le_total t t₀ with h | h
    · rw [min_eq_left h]; exact hFt0
    · rw [min_eq_right h]; exact hF0
  have hb0 : clusterInertia m k (γ (max t t₀)) = 0 := by
    rcases le_total t t₀ with h | h
    · rw [max_eq_right h]; exact hF0
    · rw [max_eq_left h]; exact hFt0
  have haη : |min t t₀ - t₀| < η := by
    rcases le_total t t₀ with h | h
    · rw [min_eq_left h]; exact ht
    · rw [min_eq_right h, sub_self, abs_zero]; exact hηpos
  have hbη : |max t t₀ - t₀| < η := by
    rcases le_total t t₀ with h | h
    · rw [max_eq_right h, sub_self, abs_zero]; exact hηpos
    · rw [max_eq_left h]; exact ht
  have hlo : t₀ - 1 < min t t₀ := by
    rw [abs_lt] at haη
    linarith [haη.1, le_abs_self (min t t₀ - t₀)]
  have hhi : max t t₀ < t₀ + 1 := by
    rw [abs_lt] at hbη
    have := neg_abs_le (max t t₀ - t₀)
    linarith
  obtain ⟨x, hx, hfx⟩ := hdense (min t t₀) (max t t₀) hlo hab hhi
  exact hno (min t t₀) (max t t₀) hab (by simpa using haη) (by simpa using hbη) ha0 hb0
    ⟨x, hx, hfx⟩

end Submission.NBody
