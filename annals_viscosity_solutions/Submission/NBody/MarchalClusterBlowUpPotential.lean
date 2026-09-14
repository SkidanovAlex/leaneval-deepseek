import Submission.NBody.MarchalClusterBlowUp
import Submission.NBody.MarchalClusterAsymptotic3

/-!
# The cluster potential along the blow-up

The potential term of the Lagrangian convergence behind Ferrario–Terracini's `propo:blowup`:
along the rescaled centred configuration the cluster potential converges to `t^{-2/3}(2/9)κ`,
which is `U_k(q̄(t))` for the parabolic profile `q̄(t) = √κ t^{2/3} s̄`.

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

/-- The cluster potential of the rescaled centred configuration converges: this is the potential
term of the Lagrangian convergence behind `propo:blowup`. -/
theorem tendsto_clusterPotential_rescaledCentered {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε κ : ℝ} (hε : 0 < ε)
    (hUn : Tendsto (fun s : ℝ => clusterPotential m k (x s) * s ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ)))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam : ℝ => clusterPotential m k (lam ^ (-((2:ℝ)/3)) • cmRel m k (x (t * lam))))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (t ^ (-((2:ℝ)/3)) * ((2:ℝ)/9 * κ))) := by
  have hlamt : Tendsto (fun lam : ℝ => t * lam) (nhdsWithin (0:ℝ) (Ioi 0))
      (nhdsWithin (0:ℝ) (Ioi 0)) := by
    have h := tendsto_mul_right_nhdsWithin ht
    rwa [show (fun lam : ℝ => t * lam) = (fun lam : ℝ => lam * t) from
      funext fun l => mul_comm t l]
  have hUn' : Tendsto (fun lam : ℝ => clusterPotential m k (x (t * lam)) * (t * lam) ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ)) := hUn.comp hlamt
  have hscal : Tendsto (fun lam : ℝ => lam ^ ((2:ℝ)/3) / (t * lam) ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (t ^ (-((2:ℝ)/3)))) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    have h1 : (t * lam) ^ ((2:ℝ)/3) = t ^ ((2:ℝ)/3) * lam ^ ((2:ℝ)/3) :=
      Real.mul_rpow (le_of_lt ht) (le_of_lt hlam)
    have h2 : lam ^ ((2:ℝ)/3) / (t ^ ((2:ℝ)/3) * lam ^ ((2:ℝ)/3))
        = 1 / t ^ ((2:ℝ)/3) := by
      have hln : lam ^ ((2:ℝ)/3) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlam _)
      field_simp
    have h3 : (1 : ℝ) / t ^ ((2:ℝ)/3) = t ^ (-((2:ℝ)/3)) := by
      rw [Real.rpow_neg ht.le ((2:ℝ)/3), one_div]
    rw [h1, h2, h3]
  have hprod := hscal.mul hUn'
  have hlim : t ^ (-((2:ℝ)/3)) * ((2:ℝ)/9 * κ) = t ^ (-((2:ℝ)/3)) * ((2:ℝ)/9 * κ) := rfl
  rw [hlim] at hprod
  refine Filter.Tendsto.congr' ?_ hprod
  filter_upwards [Ioo_mem_nhdsGT hε, hlamt.eventually (Ioo_mem_nhdsGT hε)] with lam hlam hlamt'
  have hl0 : 0 < lam := hlam.1
  have hkey : clusterPotential m k (lam ^ (-((2:ℝ)/3)) • cmRel m k (x (t * lam)))
      = lam ^ ((2:ℝ)/3) / (t * lam) ^ ((2:ℝ)/3)
        * (clusterPotential m k (x (t * lam)) * (t * lam) ^ ((2:ℝ)/3)) := by
    rw [clusterPotential_smul, clusterPotential_cmRel,
      abs_of_nonneg (Real.rpow_nonneg (le_of_lt hl0) _),
      Real.rpow_neg (le_of_lt hl0) ((2:ℝ)/3), inv_inv]
    have hZ : (t * lam) ^ ((2:ℝ)/3) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (mul_pos ht hl0) _)
    field_simp
  rw [hkey]


/-- **Cluster potential along the blow-up, in geometric form.** -/
theorem tendsto_clusterPotential_rescaledCentered_of_isolated {m : Fin N → ℝ}
    {k : Finset (Fin N)} {x : ℝ → EN E N} {ε C ν Cv : ℝ}
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
    {t : ℝ} (ht : 0 < t) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun lam : ℝ => clusterPotential m k (lam ^ (-((2:ℝ)/3)) • cmRel m k (x (t * lam))))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (t ^ (-((2:ℝ)/3)) * ((2:ℝ)/9 * κ))) := by
  obtain ⟨κ, hκpos, _hIn, _hDn, _hSec, hUn, _hRn⟩ :=
    clusterPotential_asymptotic_of_isolated (m := m) (k := k) (x := x) (ε := ε) (C := C)
      (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI
  exact ⟨κ, hκpos, tendsto_clusterPotential_rescaledCentered (m := m) (k := k) (x := x)
    (ε := ε) (κ := κ) hε hUn ht⟩

end Submission.NBody
