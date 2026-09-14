import Submission.NBody.MarchalPairRatio
import Submission.NBody.MarchalClusterAsymptotic3

/-!
# The velocity bound for the rescaled blow-up

The kinetic difference estimate of the standard-variation computation needs a bound
`‖(q^λ)'(t)‖ ≤ C t^{-1/3}` on the derivative of the rescaled centred configuration, valid
*uniformly* for small `λ`.  This is exactly the same `λ`-independence as for the separations:
the chain rule gives `(q^λ)'(t) = λ^{1/3} · (cmRel ∘ ẋ)(λt)`, so

  `‖(q^λ)'(t)‖_[m] = λ^{1/3} ‖cmRel m k (ẋ(λt))‖_[m]`,

and `‖cmRel m k (ẋ(s))‖_[m]² = R_k(ẋ(s)) = (4/9)κ s^{-2/3} (1+o(1))`, whence the `λ`'s cancel.

Everything in this file is fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The centre-of-mass-relative kinetic square of a cluster is the square of the mass norm of the
centre-of-mass-relative configuration. -/
lemma clusterRelKinetic_eq_weightedNorm_sq {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i)
    (k : Finset (Fin N)) (v : EN E N) :
    clusterRelKinetic m k v = ‖cmRel m k v‖_[m] ^ 2 := by
  have h1 : clusterRelKinetic m k v = ∑ i, m i * ‖(cmRel m k v) i‖ ^ 2 := by
    rw [clusterRelKinetic, clusterKineticSq]
    exact Finset.sum_subset (Finset.subset_univ k) (fun i _ hi => by
      rw [cmRel_apply_of_notMem hi]
      norm_num)
  rw [h1, weightedNorm,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _))]

/-- **The derivative of the rescaled centred configuration.**  The chain rule for
`q^λ(t) = λ^{-2/3} · (cmRel ∘ γ)(λt)`: at a point where `cmRel ∘ γ` has derivative `v`,
the rescaled curve has derivative `λ^{1/3} • v`. -/
lemma deriv_rescaledCentered {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {lam t : ℝ} (hlam : 0 < lam) {v : EN E N}
    (hv : HasDerivAt (fun u : ℝ => cmRel m k (x u)) v (lam * t)) :
    deriv (fun s : ℝ => rescaledCentered m k x lam s) t = lam ^ ((1:ℝ)/3) • v := by
  have hdiff : DifferentiableAt ℝ (fun u : ℝ => cmRel m k (x u)) (lam * t) :=
    hv.differentiableAt
  have hstep : deriv (fun u : ℝ => lam ^ (-(2:ℝ)/3) • cmRel m k (x u)) (lam * t)
      = lam ^ (-(2:ℝ)/3) • v := by
    rw [show (fun u : ℝ => lam ^ (-(2:ℝ)/3) • cmRel m k (x u))
        = lam ^ (-(2:ℝ)/3) • (fun u : ℝ => cmRel m k (x u)) from rfl]
    rw [deriv_const_smul _ hdiff, hv.deriv]
  have hkey := deriv_comp_mul_left lam (fun u : ℝ => lam ^ (-(2:ℝ)/3) • cmRel m k (x u)) t
  rw [hstep] at hkey
  have hcongr : (fun s : ℝ => lam ^ (-(2:ℝ)/3) • cmRel m k (x (lam * s)))
      = fun s : ℝ => rescaledCentered m k x lam s := by
    funext s
    rw [rescaledCentered, mul_comm]
  rw [hcongr] at hkey
  have hval : lam • (lam ^ (-(2:ℝ)/3) • v) = lam ^ ((1:ℝ)/3) • v := by
    rw [smul_smul]
    congr 1
    nth_rewrite 1 [← Real.rpow_one lam]
    rw [← Real.rpow_add hlam, show (1:ℝ) + (-(2:ℝ)/3) = (1:ℝ)/3 by norm_num]
  rw [hval] at hkey
  exact hkey

/-- **The velocity bound for the rescaled centred configuration, uniformly in `λ`.**  For an
isolated colliding cluster `k` there is `Cd > 0` such that for all sufficiently small `λ > 0` and
all `t ∈ (0,T]` the mass norm of the derivative of `q^λ` is at most `Cd · t^{-1/3}`. -/
theorem exists_norm_deriv_rescaledCentered_le {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv T : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv) (hT : 0 < T)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |clusterRelEnergy m k (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |crossWork m k (x t) (cmRel m k (x t))| ≤ C)
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x t) ν)
    (hv : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k,
      ‖deriv x t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (x t)))
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ᶠ (lam : ℝ) in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      ‖deriv (fun s : ℝ => rescaledCentered m k x lam s) t‖_[m] ≤ Cd * t ^ (-(1:ℝ)/3) := by
  obtain ⟨κ, hκpos, _hIn, _hDn, _hSec, _hUn, hRn⟩ :=
    clusterPotential_asymptotic_of_isolated (m := m) (k := k) (x := x) (ε := ε) (C := C)
      (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI
  have hCk : (0:ℝ) ≤ (8:ℝ)/9 * κ := by positivity
  -- the kinetic bound `R_k(ẋ s) ≤ (8/9) κ s^{-2/3}` near `0`
  have hbound : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0),
      clusterRelKinetic m k (deriv x s) ≤ (8/9) * κ * s ^ (-(2:ℝ)/3) := by
    have hlt : (4:ℝ)/9 * κ < (8:ℝ)/9 * κ := by linarith
    have hev := hRn.eventually (eventually_lt_nhds hlt)
    filter_upwards [hev, self_mem_nhdsWithin] with s hs hs0
    have hs0' : 0 < s := hs0
    have h1 : clusterRelKinetic m k (deriv x s) * s ^ ((2:ℝ)/3) < (8:ℝ)/9 * κ := hs
    have h2 : clusterRelKinetic m k (deriv x s)
        = (clusterRelKinetic m k (deriv x s) * s ^ ((2:ℝ)/3)) * s ^ (-(2:ℝ)/3) := by
      rw [mul_assoc, ← Real.rpow_add hs0', show (2:ℝ)/3 + -(2:ℝ)/3 = 0 by norm_num,
        Real.rpow_zero, mul_one]
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1.le (Real.rpow_nonneg hs0'.le _)
  rw [eventually_nhdsWithin_iff] at hbound
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.eventually_nhds_iff_ball.mp hbound
  refine ⟨Real.sqrt ((8/9) * κ) + 1, by positivity, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (show 0 < min (ε / T) (δ₁ / T) from
      lt_min (div_pos hε hT) (div_pos hδ₁pos hT))]
    with lam hlam hlamlt
  intro t ht
  have hlam0 : 0 < lam := hlam
  have hlamε : lam < ε / T := lt_of_lt_of_le hlamlt.2 (min_le_left _ _)
  have hlamδ : lam < δ₁ / T := lt_of_lt_of_le hlamlt.2 (min_le_right _ _)
  have hεT : T * (ε / T) = ε := by field_simp
  have hδT : T * (δ₁ / T) = δ₁ := by field_simp
  have htl : t * lam < ε := by
    have h2 : T * lam < T * (ε / T) := mul_lt_mul_of_pos_left hlamε hT
    linarith [mul_le_mul_of_nonneg_right ht.2 hlam0.le, h2, hεT]
  have htlam : t * lam ∈ Ioo (0:ℝ) ε := ⟨mul_pos ht.1 hlam0, htl⟩
  have hmem : t * lam ∈ Metric.ball (0:ℝ) δ₁ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (mul_pos ht.1 hlam0)]
    have h2 : T * lam < T * (δ₁ / T) := mul_lt_mul_of_pos_left hlamδ hT
    linarith [mul_le_mul_of_nonneg_right ht.2 hlam0.le, h2, hδT]
  have hkin : clusterRelKinetic m k (deriv x (t * lam)) ≤ (8/9) * κ * (t * lam) ^ (-(2:ℝ)/3) :=
    hδ₁ (t * lam) hmem (mul_pos ht.1 hlam0)
  -- the derivative value
  have hsl : lam * t ∈ Ioo (0:ℝ) ε := by
    refine ⟨mul_pos hlam0 ht.1, ?_⟩
    rw [mul_comm]; exact htl
  have hderiv : deriv (fun s : ℝ => rescaledCentered m k x lam s) t
      = lam ^ ((1:ℝ)/3) • cmRel m k (deriv x (t * lam)) := by
    have h := deriv_rescaledCentered (m := m) (k := k) (x := x) hlam0
      (hasDerivAt_cmRel m k (hx (lam * t) hsl))
    rw [mul_comm lam t] at h
    exact h
  rw [hderiv, weightedNorm_smul (fun i => (hm i).le)]
  have hroot : ‖cmRel m k (deriv x (t * lam))‖_[m]
      ≤ Real.sqrt ((8/9) * κ) * (t * lam) ^ (-(1:ℝ)/3) := by
    have hpos : (0:ℝ) < t * lam := mul_pos ht.1 hlam0
    have hnn : 0 ≤ ‖cmRel m k (deriv x (t * lam))‖_[m] := weightedNorm_nonneg m _
    have hbnn : 0 ≤ Real.sqrt ((8/9) * κ) * (t * lam) ^ (-(1:ℝ)/3) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hpos.le _)
    have hsquare : ((8:ℝ)/9 * κ) * (t * lam) ^ (-(2:ℝ)/3)
        = (Real.sqrt ((8/9) * κ) * (t * lam) ^ (-(1:ℝ)/3)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hCk]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
      norm_num
    have h2 : ‖cmRel m k (deriv x (t * lam))‖_[m] ^ 2
        ≤ (Real.sqrt ((8/9) * κ) * (t * lam) ^ (-(1:ℝ)/3)) ^ 2 := by
      rw [← clusterRelKinetic_eq_weightedNorm_sq (fun i => (hm i).le), ← hsquare]
      exact hkin
    nlinarith [h2, hnn, hbnn]
  have hpow : lam ^ ((1:ℝ)/3) * (t * lam) ^ (-(1:ℝ)/3) = t ^ (-(1:ℝ)/3) := by
    rw [Real.mul_rpow ht.1.le hlam0.le]
    rw [mul_comm (t ^ (-(1:ℝ)/3)) _, ← mul_assoc]
    rw [show lam ^ ((1:ℝ)/3) * lam ^ (-(1:ℝ)/3) = 1 by
      rw [← Real.rpow_add hlam0,
        show (1:ℝ)/3 + -(1:ℝ)/3 = 0 by norm_num, Real.rpow_zero]]
    rw [one_mul]
  have habs : |lam ^ ((1:ℝ)/3)| = lam ^ ((1:ℝ)/3) :=
    abs_of_pos (Real.rpow_pos_of_pos hlam0 _)
  rw [habs]
  calc lam ^ ((1:ℝ)/3) * ‖cmRel m k (deriv x (t * lam))‖_[m]
      ≤ lam ^ ((1:ℝ)/3) * (Real.sqrt ((8/9) * κ) * (t * lam) ^ (-(1:ℝ)/3)) :=
        mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hlam0.le _)
    _ = Real.sqrt ((8/9) * κ) * t ^ (-(1:ℝ)/3) := by
        rw [show lam ^ ((1:ℝ)/3) * (Real.sqrt ((8/9) * κ) * (t * lam) ^ (-(1:ℝ)/3))
            = Real.sqrt ((8/9) * κ) * (lam ^ ((1:ℝ)/3) * (t * lam) ^ (-(1:ℝ)/3))
          from by ring, hpow]
    _ ≤ (Real.sqrt ((8/9) * κ) + 1) * t ^ (-(1:ℝ)/3) := by
        have hnn : 0 ≤ t ^ (-(1:ℝ)/3) := Real.rpow_nonneg ht.1.le _
        nlinarith [hnn, Real.sqrt_nonneg ((8:ℝ)/9 * κ)]

end Submission.NBody
