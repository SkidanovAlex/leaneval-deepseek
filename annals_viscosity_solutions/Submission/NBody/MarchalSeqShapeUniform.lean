import Submission.NBody.MarchalSeqBlowUp
import Submission.NBody.MarchalCollisionAsymptotics
import Submission.Commons.Analysis.Calculus.eventually_forall_Icc_norm_sub_lt_of_slow_variation

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

/-- **The uniform sequential shape limit** (Ferrario--Terracini `as:lim2`).  Combining the
pointwise limit of the normalised configurations with the slow variation `t • ṡ → 0`. -/
theorem seq_shape_uniform_limit {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε T : ℝ} {sbar : EN E N} {lam : ℕ → ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hT : 0 < T)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hslow : Tendsto (fun t : ℝ => t • deriv (fun u : ℝ => clusterShape m k (x u)) t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hlampos : ∀ n, 0 < lam n) (hlamT : Tendsto lam atTop (nhds 0))
    (hpt : ∀ t ∈ Ioc (0:ℝ) T, Tendsto (fun n => clusterShape m k (x (t * lam n))) atTop (nhds sbar)) :
    ∀ t₁ ∈ Ioo (0:ℝ) T, ∀ η > 0, ∀ᶠ n in atTop, ∀ t ∈ Ioc t₁ T,
      ‖clusterShape m k (x (t * lam n)) - sbar‖ < η := by
  intro t₁ ht₁ η hη
  have h2 : 0 < η / 2 := by linarith
  have hslow := Commons.Analysis.Calculus.eventually_forall_Icc_norm_sub_lt_of_slow_variation
    (g := fun u : ℝ => clusterShape m k (x u))
    (g' := fun u : ℝ => deriv (fun v : ℝ => clusterShape m k (x v)) u)
    (a := t₁) (b := T) (δ := ε)
    ht₁.1 ht₁.2.le hε
    (fun t ht => hasDerivAt_clusterShape_of_isolated hm hk2 hε hnc hx ht)
    hslow hlampos hlamT (η / 2) h2
  have hpt' := hpt t₁ ⟨ht₁.1, ht₁.2.le⟩
  filter_upwards [hslow, hpt'.eventually (Metric.ball_mem_nhds sbar h2)] with n hn1 hn2
  intro t ht
  have h3 : ‖clusterShape m k (x (t₁ * lam n)) - sbar‖ < η / 2 := by
    rwa [dist_eq_norm] at hn2
  have h4 := hn1 t ⟨ht.1.le, ht.2⟩
  calc ‖clusterShape m k (x (t * lam n)) - sbar‖
      = ‖(clusterShape m k (x (t * lam n)) - clusterShape m k (x (t₁ * lam n)))
          + (clusterShape m k (x (t₁ * lam n)) - sbar)‖ := by
        congr 1; abel
    _ ≤ ‖clusterShape m k (x (t * lam n)) - clusterShape m k (x (t₁ * lam n))‖
          + ‖clusterShape m k (x (t₁ * lam n)) - sbar‖ := norm_add_le _ _
    _ < η / 2 + η / 2 := add_lt_add h4 h3
    _ = η := by ring

/-- **The uniform sequential shape limit at a collision of a minimiser.** -/
theorem seq_shape_uniform_limit_at_collision {m : Fin N → ℝ} {k : Finset (Fin N)}
    {γ : ℝ → EN E N} {t₀ T ε ν C Cv : ℝ} {sbar : EN E N} {lam : ℕ → ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hT : 0 < T)
    (hC : 0 < C) (hν : 0 < ν) (hCv : 0 ≤ Cv)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (shiftCurve γ t₀ t))
    (hE : ∀ t ∈ Ioo (0:ℝ) ε,
      |clusterRelEnergy m k (shiftCurve γ t₀ t) (deriv (shiftCurve γ t₀) t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε,
      |crossWork m k (shiftCurve γ t₀ t) (cmRel m k (shiftCurve γ t₀ t))| ≤ C)
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (shiftCurve γ t₀) (deriv (shiftCurve γ t₀) t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε,
      HasDerivAt (deriv (shiftCurve γ t₀)) (iteratedDeriv 2 (shiftCurve γ t₀) t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv (shiftCurve γ t₀)))
      (deriv (deriv (deriv (shiftCurve γ t₀))) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε,
      iteratedDeriv 2 (shiftCurve γ t₀) t = ∇_[m] (U m) (shiftCurve γ t₀ t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (shiftCurve γ t₀ t) ν)
    (hv : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k,
      ‖deriv (shiftCurve γ t₀) t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (shiftCurve γ t₀ t)))
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (shiftCurve γ t₀ t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hlampos : ∀ n, 0 < lam n) (hlamT : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)))
    (hs : Tendsto (fun n => clusterShape m k (shiftCurve γ t₀ (lam n))) atTop (nhds sbar))
    (hslow : Tendsto
      (fun t : ℝ => t • deriv (fun u : ℝ => clusterShape m k (shiftCurve γ t₀ u)) t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    ∀ t₁ ∈ Ioo (0:ℝ) T, ∀ η > 0, ∀ᶠ n in atTop, ∀ t ∈ Ioc t₁ T,
      ‖clusterShape m k (shiftCurve γ t₀ (t * lam n)) - sbar‖ < η := by
  have hlam0 : Tendsto lam atTop (nhds 0) := hlamT.mono_right nhdsWithin_le_nhds
  refine seq_shape_uniform_limit (m := m) (k := k) (x := shiftCurve γ t₀) (ε := ε) (T := T)
    (sbar := sbar) (lam := lam) hm hk2 hε hT hnc hx hslow hlampos hlam0 ?_
  intro t ht
  have h := tendsto_clusterShape_seq_mul (m := m) (k := k) (x := shiftCurve γ t₀) (ε := ε)
    (C := C) (ν := ν) (Cv := Cv) (T := T) hm hk2 hε hC hν hCv hT hnc hE hW hx hd2 hd3 hode
    hsep hv hI hlamT hs t ht
  refine h.congr' ?_
  filter_upwards with n
  rw [mul_comm]

end Submission.NBody
