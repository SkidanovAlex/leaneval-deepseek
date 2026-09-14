import Submission.NBody.MarchalClusterSrcBlowup
import Submission.NBody.MarchalClusterForceRest
import Submission.NBody.MarchalClusterAsymptotic3

/-!
# The blow-up of a colliding solution (Ferrario–Terracini `propo:blowup`, §6)

The rescaled centred configurations `q^λ(t) = λ^{-2/3} q(λ t)` of an isolated colliding cluster
converge, as `λ → 0⁺` and for fixed `t > 0`, to the *parabolic* homothetic collision–ejection
trajectory

    `q̄(t) = √κ · t^{2/3} · s̄`,

where `κ` is the Sundman constant of the cluster (`I_k(x(t)) = κ t^{4/3} + o(t^{4/3})`) and `s̄` a
limit of the normalised configurations.  (In the notation of the paper `I_k = (κ_{FT} t)^{4/3}`,
i.e. `κ_{FT} = κ^{3/4}`, and `(κ_{FT} t)^{2/3} = √κ · t^{2/3}`.)

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

/-- The parabolic blow-up profile `q̄(t) = √κ · t^{2/3} · s̄` (Ferrario–Terracini `eq:barq`,
in our normalisation `I_k(t) ~ κ t^{4/3}`). -/
noncomputable def blowUpProfile (κ : ℝ) (sbar : EN E N) (t : ℝ) : EN E N :=
  (Real.sqrt κ * t ^ ((2:ℝ)/3)) • sbar

/-- The rescaled centred configuration `q^λ(t) = λ^{-2/3} q(λt)`. -/
noncomputable def rescaledCentered (m : Fin N → ℝ) (k : Finset (Fin N)) (x : ℝ → EN E N)
    (lam : ℝ) (t : ℝ) : EN E N :=
  lam ^ (-(2:ℝ)/3) • cmRel m k (x (t * lam))

/-- `λ ↦ λ * t` maps `0⁺` to `0⁺` when `t > 0`. -/
lemma tendsto_mul_right_nhdsWithin {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam : ℝ => lam * t) (nhdsWithin (0:ℝ) (Ioi 0)) (nhdsWithin (0:ℝ) (Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h0 : Tendsto (fun lam : ℝ => lam) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h := h0.mul (tendsto_const_nhds : Tendsto (fun _ : ℝ => t) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds t))
    rwa [zero_mul] at h
  · filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact mul_pos hlam ht

/-- **Pointwise convergence of the blow-up.**  For fixed `t > 0`, the rescaled centred
configurations converge to the parabolic blow-up profile. -/
theorem tendsto_rescaledCentered_pointwise {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε κ : ℝ} {sbar : EN E N}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hκ : 0 < κ)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    {t : ℝ} (ht : 0 < t)
    (hscomp : Tendsto (fun lam : ℝ => clusterShape m k (x (t * lam)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar)) :
    Tendsto (fun lam : ℝ => lam ^ (-(2:ℝ)/3) • cmRel m k (x (t * lam)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((Real.sqrt κ * t ^ ((2:ℝ)/3)) • sbar)) := by
  have hpos : ∀ s ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x s) :=
    fun s hs => clusterInertia_pos hm hk2 (hnc s hs)
  have hscale : Tendsto (fun lam : ℝ => t * lam) (nhdsWithin (0:ℝ) (Ioi 0))
      (nhdsWithin (0:ℝ) (Ioi 0)) := by
    have h := tendsto_mul_right_nhdsWithin ht
    rwa [show (fun lam : ℝ => t * lam) = (fun lam : ℝ => lam * t) from funext fun l => mul_comm t l]
  have hIn' : Tendsto (fun lam : ℝ => clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ) := hIn.comp hscale
  have hc : Tendsto (fun lam : ℝ => Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hIn'
  have hs2 : Tendsto (fun lam : ℝ => t ^ ((2:ℝ)/3) • clusterShape m k (x (t * lam)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (t ^ ((2:ℝ)/3) • sbar)) :=
    hscomp.const_smul _
  have hprod := hc.smul hs2
  rw [show Real.sqrt κ • (t ^ ((2:ℝ)/3) • sbar)
      = (Real.sqrt κ * t ^ ((2:ℝ)/3)) • sbar by rw [smul_smul]] at hprod
  refine Filter.Tendsto.congr' ?_ hprod
  filter_upwards [Ioo_mem_nhdsGT hε, hscale.eventually (Ioo_mem_nhdsGT hε)] with lam hlam hlamt
  have hlam0 : 0 < lam := hlam.1
  have hlamtpos : 0 < t * lam := mul_pos ht hlam0
  have hlamtlt : t * lam < ε := hlamt.2
  have hstep : clusterInertia m k (x (t * lam))
      = (t * lam) ^ ((4:ℝ)/3)
        * (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)) := by
    field_simp
  have hsqu : Real.sqrt (clusterInertia m k (x (t * lam)))
      = Real.sqrt ((t * lam) ^ ((4:ℝ)/3))
        * Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)) := by
    rw [← Real.sqrt_mul (by positivity), ← hstep]
  have hroot : Real.sqrt ((t * lam) ^ ((4:ℝ)/3)) = lam ^ ((2:ℝ)/3) * t ^ ((2:ℝ)/3) := by
    have h1 : Real.sqrt ((t * lam) ^ ((4:ℝ)/3)) = (t * lam) ^ ((2:ℝ)/3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hlamtpos)]
      norm_num
    rw [h1, Real.mul_rpow (le_of_lt ht) (le_of_lt hlam0), mul_comm]
  rw [cmRel_eq_sqrt_smul_clusterShape (hpos (t * lam) ⟨hlamtpos, hlamtlt⟩), hsqu, hroot,
    smul_smul, smul_smul]
  congr 1
  have hneg : lam ^ (-(2:ℝ)/3) = (lam ^ ((2:ℝ)/3))⁻¹ := by
    rw [show (-(2:ℝ)/3) = -((2:ℝ)/3) by norm_num, Real.rpow_neg hlam0.le]
  have hne : lam ^ ((2:ℝ)/3) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlam0 _)
  rw [hneg]
  field_simp


/-- **Pointwise convergence of the blow-up, in geometric form.**  For an isolated colliding cluster
and a limit configuration `s̄` of the normalised configurations, the rescaled centred
configurations converge pointwise to the parabolic blow-up `q̄(t) = √κ t^{2/3} s̄`. -/
theorem tendsto_rescaledCentered_pointwise_of_isolated {m : Fin N → ℝ} {k : Finset (Fin N)}
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
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar))
    {t : ℝ} (ht : 0 < t) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun lam : ℝ => lam ^ (-(2:ℝ)/3) • cmRel m k (x (t * lam)))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((Real.sqrt κ * t ^ ((2:ℝ)/3)) • sbar)) := by
  obtain ⟨κ, hκpos, hIn, _hDer, _hSec, _hUn, _hRn⟩ :=
    clusterPotential_asymptotic_of_isolated (m := m) (k := k) (x := x) (ε := ε) (C := C)
      (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI
  refine ⟨κ, hκpos, ?_⟩
  have hscomp := tendsto_clusterShape_comp_mul_of_isolated (m := m) (k := k) (x := x) (ε := ε)
    (C := C) (ν := ν) (Cv := Cv) (sbar := sbar) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode
    hsep hv hI hs ht
  exact tendsto_rescaledCentered_pointwise (m := m) (k := k) (x := x) (ε := ε) (κ := κ)
    (sbar := sbar) hm hk2 hε hκpos hnc hIn ht hscomp

end Submission.NBody
