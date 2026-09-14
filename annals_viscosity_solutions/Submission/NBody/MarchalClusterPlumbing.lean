import Submission.NBody.MarchalRelEnergy
import Submission.NBody.MarchalSperner

/-!
# Calculus for the moment of inertia of a cluster along a curve

This module collects the elementary calculus facts about the function

    `f(t) = I_k(x(t)) = clusterInertia m k (x t)`

which Sundman's asymptotic analysis needs: positivity of `f` for a collision-free configuration
with at least two bodies in `k`, and the first two derivative statements in the exact form used by
`Commons.Analysis.Calculus.sundman_asymptotic_ratio` (`HasDerivAt f (deriv f t) t` and
`HasDerivAt (deriv f) (deriv (deriv f) t) t`).

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

/-- **Positivity of the moment of inertia of a cluster.**  If the configuration is collision-free and
the cluster has at least two bodies, then `I_k(x) > 0`. -/
theorem clusterInertia_pos {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    (hk2 : 2 ≤ k.card) {x : EN E N} (hx : WithoutCollisions x) :
    0 < clusterInertia m k x := by
  classical
  obtain ⟨i₁, hi₁⟩ : ∃ i, i ∈ k := by
    rcases Finset.eq_empty_or_nonempty k with h | ⟨i, hi⟩
    · rw [h] at hk2; simp at hk2
    · exact ⟨i, hi⟩
  obtain ⟨j₁, hj₁, hij₁⟩ : ∃ j ∈ k, i₁ ≠ j := by
    by_contra h
    push Not at h
    have hsub : k ⊆ {i₁} := fun j hj => Finset.mem_singleton.mpr (h j hj).symm
    have := Finset.card_le_card hsub
    simp at this
    omega
  set cm : E := clusterCM m k x with hcmdef
  have hdist_pos : 0 < ‖x i₁ - x j₁‖ := by
    have h1 : r x i₁ j₁ ≠ 0 := hx i₁ j₁ hij₁
    rw [r, dist_eq_norm] at h1
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm h1)
  have hIdef : clusterInertia m k x = ∑ i ∈ k, m i * ‖x i - cm‖ ^ 2 := rfl
  have h1 : 0 ≤ m i₁ * ‖x i₁ - cm‖ ^ 2 + m j₁ * ‖x j₁ - cm‖ ^ 2 :=
    add_nonneg (mul_nonneg (hm i₁).le (sq_nonneg _)) (mul_nonneg (hm j₁).le (sq_nonneg _))
  have h2 : 0 < ‖x i₁ - cm‖ ^ 2 + ‖x j₁ - cm‖ ^ 2 := by
    have h4 : ‖x i₁ - x j₁‖ ≤ ‖x i₁ - cm‖ + ‖x j₁ - cm‖ := by
      have h5 : x i₁ - x j₁ = (x i₁ - cm) - (x j₁ - cm) := by abel
      rw [h5]; exact norm_sub_le _ _
    nlinarith [norm_nonneg (x i₁ - cm), norm_nonneg (x j₁ - cm),
      sq_nonneg (‖x i₁ - cm‖ - ‖x j₁ - cm‖)]
  have h3 : 0 < m i₁ * ‖x i₁ - cm‖ ^ 2 + m j₁ * ‖x j₁ - cm‖ ^ 2 := by
    have hmin : 0 < min (m i₁) (m j₁) := lt_min (hm i₁) (hm j₁)
    have hA : 0 ≤ ‖x i₁ - cm‖ ^ 2 := sq_nonneg _
    have hB : 0 ≤ ‖x j₁ - cm‖ ^ 2 := sq_nonneg _
    have hleA := mul_le_mul_of_nonneg_right (min_le_left (m i₁) (m j₁)) hA
    have hleB := mul_le_mul_of_nonneg_right (min_le_right (m i₁) (m j₁)) hB
    nlinarith [h2, hmin, hleA, hleB]
  have hle : m i₁ * ‖x i₁ - cm‖ ^ 2 + m j₁ * ‖x j₁ - cm‖ ^ 2
      ≤ ∑ i ∈ k, m i * ‖x i - cm‖ ^ 2 := by
    have hsub : ({i₁, j₁} : Finset (Fin N)) ⊆ k := by
      intro i hi
      rw [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hi₁
      · exact hj₁
    have hle' := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun i : Fin N => m i * ‖x i - cm‖ ^ 2)
      (s := ({i₁, j₁} : Finset (Fin N))) (t := k) hsub
      (fun i _ _ => mul_nonneg (hm i).le (sq_nonneg _))
    rwa [Finset.sum_pair hij₁] at hle'
  rw [hIdef]
  exact lt_of_lt_of_le h3 hle

/-- The derivative of the moment of inertia of a cluster along a curve, in the mass-inner-product
form. -/
lemma deriv_clusterInertia_curve {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N} {t : ℝ}
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s) :
    deriv (fun s : ℝ => clusterInertia m k (x s)) t
      = 2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv x t)) :=
  (deriv_clusterInertia_eq m k hx).self_of_nhds

/-- `HasDerivAt` form of the first derivative of the moment of inertia of a cluster. -/
lemma hasDerivAt_clusterInertia_curve {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {t : ℝ} (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s) :
    HasDerivAt (fun s : ℝ => clusterInertia m k (x s))
      (deriv (fun s : ℝ => clusterInertia m k (x s)) t) t := by
  have heq : (fun s : ℝ => clusterInertia m k (x s)) =ᶠ[𝓝 t]
      (fun s : ℝ => massInner m (cmRel m k (x s)) (cmRel m k (x s))) :=
    Eventually.of_forall fun s => clusterInertia_eq_massInner m k (x s)
  have hG : HasDerivAt (fun s : ℝ => massInner m (cmRel m k (x s)) (cmRel m k (x s)))
      (2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv x t))) t := by
    have h := hasDerivAt_inertia_pair m k hx.self_of_nhds hx.self_of_nhds
    refine h.congr_deriv ?_
    rw [massInner_comm m (cmRel m k (deriv x t)) (cmRel m k (x t))]
    ring_nf
  have hval : deriv (fun s : ℝ => clusterInertia m k (x s)) t
      = 2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv x t)) := by
    rw [Filter.EventuallyEq.deriv_eq heq]
    exact hG.deriv
  rw [hval]
  exact hG.congr_of_eventuallyEq heq

/-- `HasDerivAt` form of the second derivative of the moment of inertia of a cluster. -/
lemma hasDerivAt_deriv_clusterInertia_curve {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {t : ℝ}
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : HasDerivAt (deriv x) (deriv (deriv x) t) t) :
    HasDerivAt (deriv (fun s : ℝ => clusterInertia m k (x s)))
      (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) t := by
  have hderiv : deriv (fun s : ℝ => clusterInertia m k (x s)) =ᶠ[𝓝 t]
      (fun s : ℝ => 2 * massInner m (cmRel m k (x s)) (cmRel m k (deriv x s))) := by
    filter_upwards [deriv_clusterInertia_eq m k hx] with s hs
    rw [hs]
  have hG : HasDerivAt (fun s : ℝ => 2 * massInner m (cmRel m k (x s)) (cmRel m k (deriv x s)))
      (2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv x) t))
        + 2 * massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv x t))) t := by
    have h := (hasDerivAt_inertia_pair m k hx.self_of_nhds hd2).const_mul 2
    refine h.congr_deriv ?_
    ring_nf
  have h1 : HasDerivAt (deriv (fun s : ℝ => clusterInertia m k (x s)))
      (2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv x) t))
        + 2 * massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv x t))) t :=
    hG.congr_of_eventuallyEq hderiv
  have h2 : deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
      = 2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv x) t))
        + 2 * massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv x t)) := by
    have h3 : iteratedDeriv 2 (fun s : ℝ => clusterInertia m k (x s)) t
        = deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    rw [← h3, iteratedDeriv_two_clusterInertia m k hx hd2]
  rw [h2]
  exact h1

end Submission.NBody

namespace Submission.NBody

/-- `iteratedDeriv 2 f t = deriv (deriv f) t`. -/
lemma iteratedDeriv_two_eq_deriv_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (t : ℝ) : iteratedDeriv 2 f t = deriv (deriv f) t := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]

/-- The second derivative of the moment of inertia of a cluster in the
centre-of-mass-relative Lagrange–Jacobi form. -/
lemma deriv_deriv_clusterInertia_curve_eq {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {t : ℝ} (hm : ∀ i, 0 < m i) (hk : k.Nonempty) (hnc : WithoutCollisions (x t))
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : iteratedDeriv 2 x t = ∇_[m] (U m) (x t)) :
    deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
      = 4 * clusterRelEnergy m k (x t) (deriv x t) + 2 * clusterPotential m k (x t)
        + 2 * crossWork m k (x t) (cmRel m k (x t)) := by
  rw [← iteratedDeriv_two_eq_deriv_deriv (fun s : ℝ => clusterInertia m k (x s)) t]
  exact iteratedDeriv_two_clusterInertia_rel hm hk hnc hx hd2 hode

/-- **Monotonicity of `f'` from the Sundman bound.**  If `f` is a positive `C²` function on
`(0, ε)` with `f(t) → 0` as `t → 0⁺` and `f''(t) f(t)^{1/2} ≥ d > 0`, then `f' ≥ 0`.  (The bound
forces `f'' > 0`, so `f'` is increasing; a negative value of `f'` at some `t₀` would keep `f`
bounded below by `f(t₀) - f'(t₀) t₀ > 0`, contradicting `f(t) → 0`.) -/
lemma deriv_nonneg_of_second_deriv_mul_sqrt_ge {f : ℝ → ℝ} {d ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (hf1 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt f (deriv f t) t)
    (hf2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv f) (deriv (deriv f) t) t)
    (hfpos : ∀ t ∈ Ioo (0:ℝ) ε, 0 < f t)
    (hbound : ∀ t ∈ Ioo (0:ℝ) ε, d ≤ deriv (deriv f) t * (f t) ^ ((1:ℝ)/2))
    (hlim : Tendsto f (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    ∀ t ∈ Ioo (0:ℝ) ε, 0 ≤ deriv f t := by
  intro t₀ ht₀
  by_contra hneg
  rw [not_le] at hneg
  -- `f''` is positive on `(0,ε)`
  have hf2pos : ∀ t ∈ Ioo (0:ℝ) ε, 0 < deriv (deriv f) t := by
    intro t ht
    have hp : 0 < (f t) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos (hfpos t ht) _
    have hb := hbound t ht
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [hb]
  have hmono : StrictMonoOn (deriv f) (Ioo (0:ℝ) ε) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) ?_ ?_
    · intro t ht
      exact ((hf2 t ht).differentiableAt).continuousAt.continuousWithinAt
    · intro t ht
      exact hf2pos t (by simpa only [interior_Ioo] using ht)
  -- for `t ∈ (0, t₀)`: `f t ≥ f t₀ - f' t₀ * (t₀ - t)`
  have hkey : ∀ t ∈ Ioo (0:ℝ) t₀, f t₀ - deriv f t₀ * (t₀ - t) ≤ f t := by
    intro t ht
    have huIcc : uIcc t t₀ = Icc t t₀ := uIcc_of_le ht.2.le
    have hcont : ContinuousOn f (Icc t t₀) := by
      intro s hs
      exact ((hf1 s ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 ht₀.2⟩).continuousAt).continuousWithinAt
    have hcont' : ContinuousOn (deriv f) (uIcc t t₀) := by
      intro s hs
      rw [huIcc] at hs
      exact ((hf2 s ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 ht₀.2⟩).continuousAt).continuousWithinAt
    have hint : IntervalIntegrable (deriv f) MeasureTheory.volume t t₀ := hcont'.intervalIntegrable
    have hFTC : ∫ s in t..t₀, deriv f s = f t₀ - f t :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.2.le hcont
        (fun s hs => hf1 s ⟨lt_trans ht.1 hs.1, lt_trans hs.2 ht₀.2⟩) hint
    have hmono_int : ∫ s in t..t₀, deriv f s ≤ ∫ s in t..t₀, deriv f t₀ := by
      refine intervalIntegral.integral_mono_on ht.2.le hint intervalIntegrable_const ?_
      intro s hs
      rcases eq_or_lt_of_le hs.2 with h | h
      · rw [← h]
      · exact le_of_lt (hmono ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_lt_of_le h ht₀.2.le⟩ ht₀ h)
    rw [hFTC, intervalIntegral.integral_const, smul_eq_mul] at hmono_int
    linarith
  -- pass to the limit `t → 0⁺`
  have hg : Tendsto (fun t : ℝ => f t₀ - deriv f t₀ * (t₀ - t)) (nhdsWithin (0:ℝ) (Ioi 0))
      (nhds (f t₀ - deriv f t₀ * t₀)) := by
    have h1 : Tendsto (fun t : ℝ => t₀ - t) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (t₀ - 0)) :=
      tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds)
    rw [sub_zero] at h1
    simpa using tendsto_const_nhds.sub (h1.const_mul (deriv f t₀))
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), f t₀ - deriv f t₀ * (t₀ - t) ≤ f t := by
    filter_upwards [Ioo_mem_nhdsGT ht₀.1] with t ht
    exact hkey t ⟨ht.1, ht.2⟩
  have hle0 : f t₀ - deriv f t₀ * t₀ ≤ 0 := le_of_tendsto_of_tendsto hg hlim hev
  have hpos : 0 < f t₀ - deriv f t₀ * t₀ := by
    have h1 := hfpos t₀ ht₀
    nlinarith [hneg, ht₀.1]
  linarith

end Submission.NBody
