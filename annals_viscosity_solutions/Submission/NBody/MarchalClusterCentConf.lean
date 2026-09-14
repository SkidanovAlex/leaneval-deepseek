import Submission.NBody.MarchalClusterForceRest
import Submission.NBody.MarchalClusterShapeLimit
import Submission.NBody.MarchalClusterShapeAsymptotic
import Submission.NBody.MarchalClusterAsymptotic3
import Submission.Commons.Analysis.Asymptotic.rpow_one_third_deriv_div_sqrt
import Submission.Commons.Analysis.Asymptotic.rpow_four_thirds_mul_sqrt_div_sq
import Submission.Commons.Analysis.Asymptotic.rpow_phi_second_deriv

/-!
# Ferrario–Terracini `propo:cent_conf`: limit configurations are central

For an isolated colliding cluster `k` of a solution of the N-body equations, the normalised
configurations `s(t) = I_k^{-1/2}(x(t) - x_{cm,k}(t))` have, at every accumulation point `s̄`, the
property that `∇_[m]U_k(s̄) = λ s̄` for some `λ` — i.e. `s̄` is a *central configuration*.

The proof is the blow-up computation of the paper.  Along the motion,

    `q = cmRel x = √(I_k) · s`,   `q̈ = cmRel (∇_[m]U (x))`,

and the force identity of `MarchalClusterForceRest` gives

    `q̈ = I_k⁻¹ • ∇_[m]U_k(s) + R`,   `‖R‖ ≤ C`.

Multiplying by `t^{4/3}` and passing to the limit (using the asymptotics
`I_k ~ κ t^{4/3}`, `İ_k ~ (4/3)κ t^{1/3}`, `Ï_k ~ (4/9)κ t^{-2/3}`, `t ṡ → 0`, `t² s̈ → 0`)
produces `∇_[m]U_k(s(t)) → -(2/9) κ^{3/2} s̄`; the limiting configuration `s̄` is collision-free
(`ClusterShapePotential`), so `∇_[m]U_k` is continuous at `s̄` and the conclusion follows.

Everything in this file is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators Topology
open InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The derivative of `√(I_k)` along the motion, in terms of `İ_k`. -/
lemma deriv_clusterSqrtInertia_curve_eq {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε t : ℝ} (ht : t ∈ Ioo (0:ℝ) ε)
    (hpos : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ) :
    deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t
      = deriv (fun s : ℝ => clusterInertia m k (x s)) t
          / (2 * Real.sqrt (clusterInertia m k (x t))) := by
  have hev : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hx s hs
  exact (hasDerivAt_clusterSqrtInertia_curve (hpos t ht) hev).deriv

/-- The second derivative of `√(I_k)` along the motion. -/
lemma deriv_deriv_clusterSqrtInertia_curve_eq {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε t : ℝ} (ht : t ∈ Ioo (0:ℝ) ε)
    (hpos : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ)
    (hd2 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x τ) τ) :
    deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t
      = deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
          / (2 * Real.sqrt (clusterInertia m k (x t)))
        - (deriv (fun s : ℝ => clusterInertia m k (x s)) t) ^ 2
          / (4 * (Real.sqrt (clusterInertia m k (x t))) ^ 3) :=
  (hasDerivAt_deriv_clusterSqrtInertia_curve ht hpos hx hd2).deriv

end Submission.NBody

namespace Submission.NBody

lemma alg_helper {κ : ℝ} (hκ : 0 < κ) :
    ((4:ℝ)/9*κ)/(2*Real.sqrt κ) - ((4:ℝ)/3*κ)^2/(4*(Real.sqrt κ)^3)
      = -(2:ℝ)/9*Real.sqrt κ := by
  have hne : Real.sqrt κ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hκ)
  have hsq : (Real.sqrt κ)^2 = κ := Real.sq_sqrt hκ.le
  have h4 : (Real.sqrt κ)^4 = κ^2 := by
    rw [show (4:ℕ) = 2*2 by norm_num, pow_mul, hsq]
  field_simp
  rw [h4, hsq]
  ring

theorem tendsto_rpow_four_thirds_cmRel_grad_of_asymptotics
    {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N} {ε κ : ℝ} {sbar : EN E N}
    (hε : 0 < ε) (hκ : 0 < κ)
    (hpos : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ))
    (hIn : Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hDer : Tendsto (fun t : ℝ => deriv (fun s : ℝ => clusterInertia m k (x s)) t
      / t ^ ((1:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3*κ)))
    (hSec : Tendsto (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
      * t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9*κ)))
    (hφ1 : ∀ t ∈ Ioo (0:ℝ) ε, deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t
      = deriv (fun s : ℝ => clusterInertia m k (x s)) t
          / (2 * Real.sqrt (clusterInertia m k (x t))))
    (hφ2 : ∀ t ∈ Ioo (0:ℝ) ε, deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t
      = deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
          / (2 * Real.sqrt (clusterInertia m k (x t)))
        - (deriv (fun s : ℝ => clusterInertia m k (x s)) t) ^ 2
          / (4 * (Real.sqrt (clusterInertia m k (x t))) ^ 3))
    (hmain : ∀ t ∈ Ioo (0:ℝ) ε, cmRel m k (∇_[m] (U m) (x t))
      = Real.sqrt (clusterInertia m k (x t))
          • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t
        + deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t
          • clusterShape m k (x t)
        + (2 * deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t)
            • deriv (fun s : ℝ => clusterShape m k (x s)) t)
    (hs : Tendsto (fun t : ℝ => clusterShape m k (x t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar))
    (hts : Tendsto (fun t : ℝ => t • deriv (fun s : ℝ => clusterShape m k (x s)) t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (ht2s : Tendsto (fun t : ℝ => t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    Tendsto (fun t : ℝ => t ^ ((4:ℝ)/3) • cmRel m k (∇_[m] (U m) (x t)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((-(2:ℝ)/9*Real.sqrt κ) • sbar)) := by
  have hfposEv : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), 0 < clusterInertia m k (x t) := by
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    exact hpos t ht
  -- (1)
  have T1 : Tendsto (fun t : ℝ =>
      (t ^ ((4:ℝ)/3) * Real.sqrt (clusterInertia m k (x t)) / t ^ 2)
        • (t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have hc := Commons.Analysis.Asymptotic.rpow_four_thirds_mul_sqrt_div_sq
      (f := fun t : ℝ => clusterInertia m k (x t)) hκ hfposEv hIn
    have h := hc.smul ht2s
    rwa [smul_zero] at h
  -- (3)
  have T3 : Tendsto (fun t : ℝ =>
      (t * (t ^ ((1:ℝ)/3) * deriv (fun s : ℝ => clusterInertia m k (x s)) t
        / Real.sqrt (clusterInertia m k (x t))))
        • deriv (fun s : ℝ => clusterShape m k (x s)) t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have hc := Commons.Analysis.Asymptotic.rpow_one_third_deriv_div_sqrt
      (f := fun t : ℝ => clusterInertia m k (x t))
      (g := fun t : ℝ => deriv (fun s : ℝ => clusterInertia m k (x s)) t)
      hκ hfposEv hIn hDer
    have h := hc.smul hts
    rw [smul_zero] at h
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards with t
    rw [smul_smul, mul_comm]
  -- (2)
  have hphi2lim : Tendsto (fun t : ℝ => t ^ ((4:ℝ)/3)
      * deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (-(2:ℝ)/9*Real.sqrt κ)) := by
    have hbase := Commons.Analysis.Asymptotic.rpow_phi_second_deriv
      (f := fun t : ℝ => clusterInertia m k (x t))
      (g := fun t : ℝ => deriv (fun s : ℝ => clusterInertia m k (x s)) t)
      (h := fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t)
      (κ := κ) (a := (4:ℝ)/3*κ) (b := (4:ℝ)/9*κ) hκ hfposEv hIn hDer hSec
    rw [alg_helper hκ] at hbase
    refine Filter.Tendsto.congr' ?_ hbase
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    rw [hφ2 t ht]
  have T2 : Tendsto (fun t : ℝ => (t ^ ((4:ℝ)/3)
      * deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t)
      • clusterShape m k (x t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((-(2:ℝ)/9*Real.sqrt κ) • sbar)) :=
    hphi2lim.smul hs
  have hcomb := (T1.add T2).add T3
  rw [zero_add, add_zero] at hcomb
  refine Filter.Tendsto.congr' ?_ hcomb
  filter_upwards [Ioo_mem_nhdsGT hε] with t ht
  have ht0 : 0 < t := ht.1
  have htne : t ≠ 0 := ne_of_gt ht0
  rw [hmain t ht]
  have hA : t ^ ((4:ℝ)/3) • (Real.sqrt (clusterInertia m k (x t))
        • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t)
      = (t ^ ((4:ℝ)/3) * Real.sqrt (clusterInertia m k (x t)) / t ^ 2)
        • (t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) := by
    have hscal : (t ^ ((4:ℝ)/3) * Real.sqrt (clusterInertia m k (x t)) / t ^ 2) * t ^ 2
        = t ^ ((4:ℝ)/3) * Real.sqrt (clusterInertia m k (x t)) := by
      field_simp
    simp only [smul_smul]
    rw [hscal]
  have hB : t ^ ((4:ℝ)/3) • (deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t
        • clusterShape m k (x t))
      = (t ^ ((4:ℝ)/3) * deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t)
        • clusterShape m k (x t) := by
    rw [smul_smul]
  have hC : t ^ ((4:ℝ)/3)
        • ((2 * deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t)
            • deriv (fun s : ℝ => clusterShape m k (x s)) t)
      = (t * (t ^ ((1:ℝ)/3) * deriv (fun s : ℝ => clusterInertia m k (x s)) t
          / Real.sqrt (clusterInertia m k (x t))))
        • deriv (fun s : ℝ => clusterShape m k (x s)) t := by
    have hscal : t ^ ((4:ℝ)/3) * (2 * deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t)
        = t * (t ^ ((1:ℝ)/3) * deriv (fun s : ℝ => clusterInertia m k (x s)) t
            / Real.sqrt (clusterInertia m k (x t))) := by
      rw [hφ1 t ht]
      have hrpow : t ^ ((4:ℝ)/3) = t * t ^ ((1:ℝ)/3) := by
        have h := Real.rpow_add ht0 (1:ℝ) ((1:ℝ)/3)
        rw [show (1:ℝ) + 1/3 = (4:ℝ)/3 by norm_num, Real.rpow_one] at h
        exact h
      rw [hrpow]
      ring
    rw [smul_smul, hscal]
  rw [smul_add, smul_add, hA, hB, hC]


/-- Collision-freeness inside the cluster is inherited by the normalised configuration. -/
lemma clusterShape_pair_ne {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j) (hI : 0 < clusterInertia m k x) :
    ∀ i ∈ k, ∀ j ∈ k, i ≠ j → (clusterShape m k x) i ≠ (clusterShape m k x) j := by
  have hφpos : 0 < Real.sqrt (clusterInertia m k x) := Real.sqrt_pos.mpr hI
  have hkk' := cmRel_pair_ne (m := m) (k := k) hkk
  intro a ha b hb hab hcon
  have h3 : (Real.sqrt (clusterInertia m k x))⁻¹ • (cmRel m k x) a
      = (Real.sqrt (clusterInertia m k x))⁻¹ • (cmRel m k x) b := by
    rw [← clusterShape_apply, ← clusterShape_apply]
    exact hcon
  have h4 : (cmRel m k x) a = (cmRel m k x) b := by
    have hh := congrArg (fun w : E => Real.sqrt (clusterInertia m k x) • w) h3
    simpa [smul_smul, mul_inv_cancel₀ (ne_of_gt hφpos)] using hh
  exact hkk' a ha b hb hab h4

/-- **The geometric version of the blow-up limit for `q̈`.**  For an isolated colliding cluster of a
solution of the N-body equations, `t^{4/3} q̈ = t^{4/3} cmRel (∇U (x t))` has the limit
`-(2/9)√κ · s̄`, where `κ` is the Sundman constant of the cluster and `s̄` a limit configuration. -/
theorem tendsto_rpow_four_thirds_cmRel_grad {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv : ℝ} {sbar : EN E N}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv)
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
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hs : Tendsto (fun t : ℝ => clusterShape m k (x t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar)) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ) ∧
      Tendsto (fun t : ℝ => t ^ ((4:ℝ)/3) • cmRel m k (∇_[m] (U m) (x t)))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((-(2:ℝ)/9*Real.sqrt κ) • sbar)) := by
  obtain ⟨κ, hκpos, hIn, hDer, hSec, hUn, _hRn⟩ :=
    clusterPotential_asymptotic_of_isolated (m := m) (k := k) (x := x) (ε := ε) (C := C)
      (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI
  refine ⟨κ, hκpos, hIn, ?_⟩
  have hpos : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ) :=
    fun τ hτ => clusterInertia_pos hm hk2 (hnc τ hτ)
  have hφ1 : ∀ t ∈ Ioo (0:ℝ) ε, deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t
      = deriv (fun s : ℝ => clusterInertia m k (x s)) t
          / (2 * Real.sqrt (clusterInertia m k (x t))) :=
    fun t ht => deriv_clusterSqrtInertia_curve_eq ht hpos hx
  have hφ2 : ∀ t ∈ Ioo (0:ℝ) ε,
      deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t
      = deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
          / (2 * Real.sqrt (clusterInertia m k (x t)))
        - (deriv (fun s : ℝ => clusterInertia m k (x s)) t) ^ 2
          / (4 * (Real.sqrt (clusterInertia m k (x t))) ^ 3) :=
    fun t ht => deriv_deriv_clusterSqrtInertia_curve_eq ht hpos hx hd2
  have hmain : ∀ t ∈ Ioo (0:ℝ) ε, cmRel m k (∇_[m] (U m) (x t))
      = Real.sqrt (clusterInertia m k (x t))
          • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t
        + deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t
          • clusterShape m k (x t)
        + (2 * deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t)
            • deriv (fun s : ℝ => clusterShape m k (x s)) t := by
    intro t ht
    have h := sqrtInertia_smul_deriv_deriv_clusterShape (m := m) (k := k) (x := x) ht hpos hx hd2 hode
    rw [h]
    abel
  have hts := tendsto_mul_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε) (C := C)
    (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI
  have ht2s := tendsto_mul_sq_deriv_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε)
    (C := C) (ν := ν) (Cv := Cv) (κ := κ) hm hk2 hε hC hν hCv hκpos hnc hE hW hx hd2 hd3
    hode hsep hv hI hIn hDer hSec hUn
  exact tendsto_rpow_four_thirds_cmRel_grad_of_asymptotics (m := m) (k := k) (x := x)
    (ε := ε) (κ := κ) (sbar := sbar) hε hκpos hpos hIn hDer hSec hφ1 hφ2 hmain hs hts ht2s


/-- **Componentwise limit of the mass-gradient.**  At a collision-free configuration `s̄` of the
cluster, `(∇_[m]U_k(s(t)))ᵢ → (∇_[m]U_k(s̄))ᵢ` — components of the sum formula. -/
lemma tendsto_clusterGrad_apply {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε : ℝ} {sbar : EN E N}
    (hm : ∀ i, m i ≠ 0) (hε : 0 < ε)
    (hpos : ∀ t ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x t))
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, ∀ i ∈ k, ∀ j ∈ k, i ≠ j → (x t) i ≠ (x t) j)
    (hs : Tendsto (fun t : ℝ => clusterShape m k (x t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar))
    (hcf : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbar i ≠ sbar j) (i : Fin N) :
    Tendsto (fun t : ℝ => (clusterGrad m k (clusterShape m k (x t))) i)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((clusterGrad m k sbar) i)) := by
  by_cases hi : i ∈ k
  · have hform : ∀ t ∈ Ioo (0:ℝ) ε, (clusterGrad m k (clusterShape m k (x t))) i
        = ∑ j ∈ k.erase i,
            (m j * (‖(clusterShape m k (x t)) j - (clusterShape m k (x t)) i‖ ^ 3)⁻¹)
              • ((clusterShape m k (x t)) j - (clusterShape m k (x t)) i) :=
      fun t ht => clusterGrad_apply_of_mem hm
        (clusterShape_pair_ne (hnc t ht) (hpos t ht)) hi
    have hform0 : (clusterGrad m k sbar) i
        = ∑ j ∈ k.erase i, (m j * (‖sbar j - sbar i‖ ^ 3)⁻¹) • (sbar j - sbar i) :=
      clusterGrad_apply_of_mem hm hcf hi
    rw [hform0]
    have hsum : Tendsto (fun t : ℝ => ∑ j ∈ k.erase i,
            (m j * (‖(clusterShape m k (x t)) j - (clusterShape m k (x t)) i‖ ^ 3)⁻¹)
              • ((clusterShape m k (x t)) j - (clusterShape m k (x t)) i))
        (nhdsWithin (0:ℝ) (Ioi 0))
        (nhds (∑ j ∈ k.erase i, (m j * (‖sbar j - sbar i‖ ^ 3)⁻¹) • (sbar j - sbar i))) :=
      tendsto_finsetSum _ fun j hj => ?_
    · refine Filter.Tendsto.congr' ?_ hsum
      filter_upwards [Ioo_mem_nhdsGT hε] with t ht
      exact (hform t ht).symm
    · have hj1 : j ≠ i := (Finset.mem_erase.mp hj).1
      have hj2 : j ∈ k := (Finset.mem_erase.mp hj).2
      have hsi : Tendsto (fun t : ℝ => (clusterShape m k (x t)) i)
          (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (sbar i)) :=
        (PiLp.continuous_apply 2 (fun _ : Fin N => E) i).continuousAt.tendsto.comp hs
      have hsj : Tendsto (fun t : ℝ => (clusterShape m k (x t)) j)
          (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (sbar j)) :=
        (PiLp.continuous_apply 2 (fun _ : Fin N => E) j).continuousAt.tendsto.comp hs
      have hsub : Tendsto
          (fun t : ℝ => (clusterShape m k (x t)) j - (clusterShape m k (x t)) i)
          (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (sbar j - sbar i)) := hsj.sub hsi
      have hne : sbar j - sbar i ≠ 0 :=
        sub_ne_zero.mpr (hcf j hj2 i hi hj1)
      have hnrm : Tendsto
          (fun t : ℝ => ‖(clusterShape m k (x t)) j - (clusterShape m k (x t)) i‖)
          (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ‖sbar j - sbar i‖) := hsub.norm
      have hpow : Tendsto
          (fun t : ℝ => (‖(clusterShape m k (x t)) j - (clusterShape m k (x t)) i‖ ^ 3)⁻¹)
          (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((‖sbar j - sbar i‖ ^ 3)⁻¹)) :=
        (hnrm.pow 3).inv₀ (pow_ne_zero 3 (norm_ne_zero_iff.mpr hne))
      have hconst : Tendsto (fun _ : ℝ => m j) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (m j)) :=
        tendsto_const_nhds
      have h := (hconst.mul hpow).smul hsub
      simpa using h
  · rw [clusterGrad_apply_of_notMem hcf hi]
    refine Filter.Tendsto.congr' ?_
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : E)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    exact (clusterGrad_apply_of_notMem (clusterShape_pair_ne (hnc t ht) (hpos t ht)) hi).symm

/-- **The limit of the mass-gradient of the cluster potential.**  `∇_[m]U_k(s(t))` converges to
`-(2/9)κ^{3/2} s̄`. -/
theorem tendsto_clusterGrad_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv : ℝ} {sbar : EN E N}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv)
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
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hs : Tendsto (fun t : ℝ => clusterShape m k (x t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar)) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun t : ℝ => clusterGrad m k (clusterShape m k (x t)))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((κ * (-(2:ℝ)/9*Real.sqrt κ)) • sbar)) := by
  obtain ⟨κ, hκpos, hIn, hL⟩ := tendsto_rpow_four_thirds_cmRel_grad (m := m) (k := k) (x := x)
    (ε := ε) (C := C) (ν := ν) (Cv := Cv) (sbar := sbar)
    hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI hs
  refine ⟨κ, hκpos, ?_⟩
  have hR := tendsto_rpow_four_thirds_clusterForceRest (m := m) (k := k) (x := x) (ε := ε)
    (ν := ν) hm hk2 hε hν hnc hsep
  have hsub : Tendsto (fun t : ℝ => t ^ ((4:ℝ)/3) • cmRel m k (∇_[m] (U m) (x t))
      - t ^ ((4:ℝ)/3) • clusterForceRest m k (x t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((-(2:ℝ)/9*Real.sqrt κ) • sbar - 0)) := hL.sub hR
  rw [sub_zero] at hsub
  have hG : Tendsto (fun t : ℝ => t ^ ((4:ℝ)/3)
      • ((clusterInertia m k (x t))⁻¹ • clusterGrad m k (clusterShape m k (x t))))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((-(2:ℝ)/9*Real.sqrt κ) • sbar)) := by
    refine Filter.Tendsto.congr' ?_ hsub
    filter_upwards with t
    rw [← smul_sub]
    congr 1
    rw [clusterForceRest]
    abel
  have hfinal := hIn.smul hG
  rw [smul_smul] at hfinal
  refine Filter.Tendsto.congr' ?_ hfinal
  filter_upwards [Ioo_mem_nhdsGT hε] with t ht
  have hIpos : 0 < clusterInertia m k (x t) := clusterInertia_pos hm hk2 (hnc t ht)
  have htne : t ^ ((4:ℝ)/3) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht.1 _)
  have hscal : clusterInertia m k (x t) / t ^ ((4:ℝ)/3)
      * (t ^ ((4:ℝ)/3) * (clusterInertia m k (x t))⁻¹) = 1 := by
    field_simp
  simp only [smul_smul]
  rw [hscal, one_smul]

/-- **Ferrario–Terracini `propo:cent_conf`.**  Every limit of the normalised configurations of an
isolated colliding cluster is a central configuration. -/
theorem isCentralConfig_of_tendsto_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv : ℝ} {sbar : EN E N}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv)
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
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hs : Tendsto (fun t : ℝ => clusterShape m k (x t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar)) :
    IsCentralConfig m k sbar := by
  obtain ⟨κ, hκpos, hIn, _hDer, _hSec, hUn, _hRn⟩ :=
    clusterPotential_asymptotic_of_isolated (m := m) (k := k) (x := x) (ε := ε) (C := C)
      (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI
  have hcf : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbar i ≠ sbar j :=
    withoutCollisions_of_tendsto_clusterShape hm hk2 hε hκpos hnc hIn hUn hs
  obtain ⟨κ', hκ'pos, hG⟩ := tendsto_clusterGrad_clusterShape (m := m) (k := k) (x := x)
    (ε := ε) (C := C) (ν := ν) (Cv := Cv) (sbar := sbar)
    hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI hs
  refine ⟨κ' * (-(2:ℝ)/9*Real.sqrt κ'), ?_⟩
  refine PiLp.ext fun i => ?_
  have h1 : Tendsto (fun t : ℝ => (clusterGrad m k (clusterShape m k (x t))) i)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (((κ' * (-(2:ℝ)/9*Real.sqrt κ')) • sbar) i)) :=
    (PiLp.continuous_apply 2 (fun _ : Fin N => E) i).continuousAt.tendsto.comp hG
  have h2 := tendsto_clusterGrad_apply (m := m) (k := k) (x := x) (ε := ε) (sbar := sbar)
    (fun i => ne_of_gt (hm i)) hε
    (fun t ht => clusterInertia_pos hm hk2 (hnc t ht))
    (fun t ht i hi j hj hij => by
      have hr := hnc t ht i j hij
      intro hcon
      exact hr (by rw [r_eq_norm_sub, hcon, sub_self, norm_zero]))
    hs hcf i
  exact (tendsto_nhds_unique h1 h2).symm

end Submission.NBody
