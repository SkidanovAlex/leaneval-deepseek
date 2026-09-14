import Submission.NBody.MarchalClusterBlowUp
import Submission.NBody.MarchalClusterShape

/-!
# The derivative of the blow-up (Ferrario–Terracini `bl:1`, second half)

The derivative of the rescaled centred configuration is `(q^λ)'(t) = λ^{1/3} q̇(λ t)`; using the
first-order Leibniz rule `q̇ = √(I_k) ṡ + (İ_k/(2√(I_k))) s` and the asymptotics of `I_k`, `İ_k`
and `t ṡ → 0`, it converges, for fixed `t > 0`, to

    `q̄'(t) = (2/3) √κ · t^{-1/3} · s̄`,

the derivative of the parabolic blow-up `q̄(t) = √κ t^{2/3} s̄`.

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

theorem tendsto_deriv_rescaledCentered_pointwise {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε κ : ℝ} {sbar : EN E N}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hκ : 0 < κ)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd2 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x s) s)
    (hode : ∀ s ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x s = ∇_[m] (U m) (x s))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hDn : Tendsto (fun s : ℝ => deriv (fun u : ℝ => clusterInertia m k (x u)) s
      / s ^ ((1:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3 * κ)))
    (hts : Tendsto (fun u : ℝ => u • deriv (fun u : ℝ => clusterShape m k (x u)) u)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    {t : ℝ} (ht : 0 < t)
    (hscomp : Tendsto (fun lam : ℝ => clusterShape m k (x (t * lam)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar)) :
    Tendsto (fun lam : ℝ => lam ^ ((1:ℝ)/3) • deriv (fun u : ℝ => cmRel m k (x u)) (t * lam))
      (nhdsWithin (0:ℝ) (Ioi 0))
      (nhds (((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) • sbar)) := by
  have hpos : ∀ u ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x u) :=
    fun u hu => clusterInertia_pos hm hk2 (hnc u hu)
  have hev' : ∀ u ∈ Ioo (0:ℝ) ε, ∀ᶠ s in 𝓝 u, HasDerivAt x (deriv x s) s := by
    intro u hu
    filter_upwards [isOpen_Ioo.mem_nhds hu] with s hs
    exact hx s hs
  -- the identity `q̇ = √I • ṡ + (İ / (2√I)) • s`
  have hq : ∀ u ∈ Ioo (0:ℝ) ε, deriv (fun τ : ℝ => cmRel m k (x τ)) u
      = Real.sqrt (clusterInertia m k (x u)) • deriv (fun τ : ℝ => clusterShape m k (x τ)) u
        + (deriv (fun τ : ℝ => clusterInertia m k (x τ)) u
            / (2 * Real.sqrt (clusterInertia m k (x u)))) • clusterShape m k (x u) := by
    intro u hu
    have hI := hpos u hu
    have hrootne : Real.sqrt (clusterInertia m k (x u)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hI)
    have hsn : deriv (fun τ : ℝ => clusterShape m k (x τ)) u
        = (Real.sqrt (clusterInertia m k (x u)))⁻¹ • cmRel m k (deriv x u)
          + (-(deriv (fun τ : ℝ => clusterInertia m k (x τ)) u
              / (2 * (Real.sqrt (clusterInertia m k (x u))) ^ 3))) • cmRel m k (x u) :=
      (hasDerivAt_clusterShape_curve (hI) (hev' u hu)).deriv
    have hcm : cmRel m k (x u)
        = Real.sqrt (clusterInertia m k (x u)) • clusterShape m k (x u) :=
      cmRel_eq_sqrt_smul_clusterShape hI
    have hAB : Real.sqrt (clusterInertia m k (x u))
          * (-(deriv (fun τ : ℝ => clusterInertia m k (x τ)) u
              / (2 * (Real.sqrt (clusterInertia m k (x u))) ^ 3))
              * Real.sqrt (clusterInertia m k (x u)))
        = -(deriv (fun τ : ℝ => clusterInertia m k (x τ)) u
            / (2 * Real.sqrt (clusterInertia m k (x u)))) := by
      field_simp
    have h1 : Real.sqrt (clusterInertia m k (x u))
          • deriv (fun τ : ℝ => clusterShape m k (x τ)) u
        = cmRel m k (deriv x u)
          - (deriv (fun τ : ℝ => clusterInertia m k (x τ)) u
              / (2 * Real.sqrt (clusterInertia m k (x u)))) • clusterShape m k (x u) := by
      rw [hsn, hcm]
      simp only [smul_add, smul_smul]
      rw [mul_inv_cancel₀ hrootne, one_smul, hAB, neg_smul, sub_eq_add_neg]
    have hqval : deriv (fun τ : ℝ => cmRel m k (x τ)) u = cmRel m k (deriv x u) :=
      (hasDerivAt_cmRel m k (hx u hu)).deriv
    rw [hqval, h1]
    abel
  -- scalar limits
  have hlamt : Tendsto (fun lam : ℝ => t * lam) (nhdsWithin (0:ℝ) (Ioi 0))
      (nhdsWithin (0:ℝ) (Ioi 0)) := by
    have h := tendsto_mul_right_nhdsWithin ht
    rwa [show (fun lam : ℝ => t * lam) = (fun lam : ℝ => lam * t) from
      funext fun l => mul_comm t l]
  have hIn' : Tendsto (fun lam : ℝ => clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ) := hIn.comp hlamt
  have hDn' : Tendsto (fun lam : ℝ =>
      deriv (fun u : ℝ => clusterInertia m k (x u)) (t * lam) / (t * lam) ^ ((1:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3 * κ)) := hDn.comp hlamt
  have hsq' : Tendsto
      (fun lam : ℝ => Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hIn'
  have hs' : Tendsto (fun lam : ℝ => clusterShape m k (x (t * lam)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar) := hscomp
  -- `lam • ṡ(t lam) → 0`
  have hts'' : Tendsto (fun lam : ℝ => lam • deriv (fun u : ℝ => clusterShape m k (x u)) (t * lam))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have h := hts.comp hlamt
    have h2 : Tendsto (fun lam : ℝ => t⁻¹ • ((t * lam)
        • deriv (fun u : ℝ => clusterShape m k (x u)) (t * lam)))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (t⁻¹ • (0 : EN E N))) := h.const_smul t⁻¹
    rw [smul_zero] at h2
    refine Filter.Tendsto.congr' ?_ h2
    filter_upwards with lam
    rw [smul_smul]
    congr 1
    field_simp
  -- (1) the first summand of the rescaled derivative
  have hT1 : Tendsto (fun lam : ℝ =>
      (t ^ ((2:ℝ)/3) * Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)))
        • (lam • deriv (fun u : ℝ => clusterShape m k (x u)) (t * lam)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have hcst : Tendsto (fun _ : ℝ => t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0))
        (nhds (t ^ ((2:ℝ)/3))) := tendsto_const_nhds
    have h := (hcst.mul hsq').smul hts''
    rw [smul_zero] at h
    exact h
  -- (2) the second summand
  have hT2 : Tendsto (fun lam : ℝ =>
      ((deriv (fun u : ℝ => clusterInertia m k (x u)) (t * lam) / (t * lam) ^ ((1:ℝ)/3))
          * (t ^ (-(1:ℝ)/3)
              / (2 * Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)))))
        • clusterShape m k (x (t * lam)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) • sbar)) := by
    have hscal : Tendsto (fun lam : ℝ =>
        (deriv (fun u : ℝ => clusterInertia m k (x u)) (t * lam) / (t * lam) ^ ((1:ℝ)/3))
          * (t ^ (-(1:ℝ)/3)
              / (2 * Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)))))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3))) := by
      have hconst : Tendsto (fun _ : ℝ => t ^ (-(1:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0))
          (nhds (t ^ (-(1:ℝ)/3))) := tendsto_const_nhds
      have hden : Tendsto (fun lam : ℝ =>
          2 * Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)))
          (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (2 * Real.sqrt κ)) :=
        tendsto_const_nhds.mul hsq'
      have hinv : Tendsto (fun lam : ℝ =>
          t ^ (-(1:ℝ)/3) / (2 * Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3))))
          (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (t ^ (-(1:ℝ)/3) / (2 * Real.sqrt κ))) :=
        hconst.div hden (by positivity)
      have hprod := hDn'.mul hinv
      have hlim : (4:ℝ)/3 * κ * (t ^ (-(1:ℝ)/3) / (2 * Real.sqrt κ))
          = (2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3) := by
        have hne : Real.sqrt κ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hκ)
        field_simp
        rw [Real.sq_sqrt hκ.le]
        ring
      rwa [hlim] at hprod
    exact hscal.smul hs'
  have hsum := hT1.add hT2
  rw [zero_add] at hsum
  refine Filter.Tendsto.congr' ?_ hsum
  filter_upwards [Ioo_mem_nhdsGT hε, hlamt.eventually (Ioo_mem_nhdsGT hε)] with lam hlam hlamt'
  have hlam0 : 0 < lam := hlam.1
  have hlamtpos : 0 < t * lam := mul_pos ht hlam0
  have hlamtlt : t * lam < ε := hlamt'.2
  have hIpos : 0 < clusterInertia m k (x (t * lam)) := hpos (t * lam) ⟨hlamtpos, hlamtlt⟩
  have hne4 : (t * lam) ^ ((4:ℝ)/3) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlamtpos _)
  have hdecomp : Real.sqrt (clusterInertia m k (x (t * lam)))
      = Real.sqrt ((t * lam) ^ ((4:ℝ)/3))
        * Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hroot4 : Real.sqrt ((t * lam) ^ ((4:ℝ)/3)) = lam ^ ((2:ℝ)/3) * t ^ ((2:ℝ)/3) := by
    have h3 : Real.sqrt ((t * lam) ^ ((4:ℝ)/3)) = (t * lam) ^ ((2:ℝ)/3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hlamtpos)]
      norm_num
    rw [h3, Real.mul_rpow (le_of_lt ht) (le_of_lt hlam0), mul_comm]
  have hZne : Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (div_pos hIpos (Real.rpow_pos_of_pos hlamtpos _)))
  have hl1 : lam ^ ((1:ℝ)/3) * lam ^ ((2:ℝ)/3) = lam := by
    rw [← Real.rpow_add hlam0]
    norm_num
  have hl3 : (t * lam) ^ ((1:ℝ)/3) = lam ^ ((1:ℝ)/3) * t ^ ((1:ℝ)/3) := by
    rw [Real.mul_rpow (le_of_lt ht) (le_of_lt hlam0), mul_comm]
  rw [hq (t * lam) ⟨hlamtpos, hlamtlt⟩, smul_add]
  congr 1
  · have hkmul : lam ^ ((1:ℝ)/3) * Real.sqrt (clusterInertia m k (x (t * lam)))
        = t ^ ((2:ℝ)/3)
            * Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)) * lam := by
      have hcomb : ∀ c Z : ℝ, lam ^ ((1:ℝ)/3) * (lam ^ ((2:ℝ)/3) * c * Z) = c * Z * lam := by
        intro c Z
        rw [show lam ^ ((1:ℝ)/3) * (lam ^ ((2:ℝ)/3) * c * Z)
            = (lam ^ ((1:ℝ)/3) * lam ^ ((2:ℝ)/3)) * (c * Z) by ring, hl1]
        ring
      rw [hdecomp, hroot4]
      exact hcomb (t ^ ((2:ℝ)/3)) _
    simp only [smul_smul]
    rw [hkmul]
  · have hkmul : lam ^ ((1:ℝ)/3) * (deriv (fun u : ℝ => clusterInertia m k (x u)) (t * lam)
          / (2 * Real.sqrt (clusterInertia m k (x (t * lam)))))
        = (deriv (fun u : ℝ => clusterInertia m k (x u)) (t * lam) / (t * lam) ^ ((1:ℝ)/3))
          * (t ^ (-(1:ℝ)/3)
              / (2 * Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)))) := by
      have hneg : t ^ (-(1:ℝ)/3) = (t ^ ((1:ℝ)/3))⁻¹ := by
        rw [show (-(1:ℝ)/3) = -((1:ℝ)/3) by norm_num, Real.rpow_neg (le_of_lt ht)]
      have hl13 : lam ^ ((1:ℝ)/3) * lam ^ ((1:ℝ)/3) = lam ^ ((2:ℝ)/3) := by
        rw [← Real.rpow_add hlam0]
        norm_num
      have ht13 : t ^ ((1:ℝ)/3) * t ^ ((1:ℝ)/3) = t ^ ((2:ℝ)/3) := by
        rw [← Real.rpow_add ht]
        norm_num
      rw [hdecomp, hroot4, hl3, hneg, ← hl13, ← ht13]
      have h6 : lam ^ ((1:ℝ)/3) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlam0 _)
      have h7 : t ^ ((1:ℝ)/3) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
      field_simp
    simp only [smul_smul]
    rw [hkmul]


/-- **Derivative of the blow-up, in geometric form.**  For an isolated colliding cluster and a
limit configuration `s̄` of the normalised configurations, the derivatives of the rescaled centred
configurations converge pointwise to the derivative of the parabolic blow-up. -/
theorem tendsto_deriv_rescaledCentered_pointwise_of_isolated {m : Fin N → ℝ}
    {k : Finset (Fin N)} {x : ℝ → EN E N} {ε C ν Cv : ℝ} {sbar : EN E N}
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
      Tendsto (fun lam : ℝ => lam ^ ((1:ℝ)/3) • deriv (fun u : ℝ => cmRel m k (x u)) (t * lam))
        (nhdsWithin (0:ℝ) (Ioi 0))
        (nhds (((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) • sbar)) := by
  obtain ⟨κ, hκpos, hIn, hDn, _hSec, _hUn, _hRn⟩ :=
    clusterPotential_asymptotic_of_isolated (m := m) (k := k) (x := x) (ε := ε) (C := C)
      (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI
  refine ⟨κ, hκpos, ?_⟩
  have hts := tendsto_mul_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε) (C := C)
    (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI
  have hscomp := tendsto_clusterShape_comp_mul_of_isolated (m := m) (k := k) (x := x)
    (ε := ε) (C := C) (ν := ν) (Cv := Cv) (sbar := sbar) hm hk2 hε hC hν hCv hnc hE hW hx
    hd2 hd3 hode hsep hv hI hs ht
  exact tendsto_deriv_rescaledCentered_pointwise (m := m) (k := k) (x := x) (ε := ε) (κ := κ)
    (sbar := sbar) hm hk2 hε hκpos hnc hx hd2 hode hIn hDn hts ht hscomp

end Submission.NBody
