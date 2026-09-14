import Submission.NBody.MarchalSeqBlowUp
import Submission.NBody.MarchalClusterBlowUpDeriv
import Submission.NBody.MarchalModelKinetic

/-!
# Sequential version of the derivative of the blow-up

Ferrario--Terracini `bl:1`, second half, along a sequence `λ_n → 0⁺`: for fixed `t > 0`,
`(q^{λ_n})'(t) → q̄'(t) = (2/3)√κ t^{-1/3} s̄`.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

variable [Nontrivial E]

/-- Eventually, a sequence tending to `0⁺` lies in `(0,ε)`. -/
lemma eventually_mem_Ioo_of_tendsto_nhdsWithin {lam : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hlam : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0))) :
    ∀ᶠ n in atTop, lam n ∈ Ioo (0:ℝ) ε := by
  rw [tendsto_nhdsWithin_iff] at hlam
  obtain ⟨h0, hpos⟩ := hlam
  filter_upwards [hpos, h0.eventually (eventually_lt_nhds hε)] with n hp hlt
  exact ⟨hp, hlt⟩

/-- The scaled sequence `t λ_n` again tends to `0⁺`. -/
lemma tendsto_mul_seq_nhdsWithin {lam : ℕ → ℝ} {t : ℝ} (ht : 0 < t)
    (hlam : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0))) :
    Tendsto (fun n => t * lam n) atTop (nhdsWithin (0:ℝ) (Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff] at hlam ⊢
  refine ⟨?_, ?_⟩
  · have h := hlam.1.const_mul t
    simpa using h
  · filter_upwards [hlam.2] with n hn
    exact mul_pos ht hn

/-- **`bl:1` (second half), sequential form.**  For fixed `t > 0`, the derivatives of the rescaled
centred configurations converge to the derivative of the parabolic blow-up. -/
theorem tendsto_deriv_rescaledCentered_seq {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε κ T : ℝ} {sbar : EN E N}
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
    {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)))
    (hseq : ∀ t ∈ Ioc (0:ℝ) T,
      Tendsto (fun n => clusterShape m k (x (t * lam n))) atTop (nhds sbar)) :
    ∀ t ∈ Ioc (0:ℝ) T,
      Tendsto (fun n => deriv (rescaledCentered m k x (lam n)) t) atTop
        (nhds (deriv (blowUpProfile κ sbar) t)) := by
  intro t ht
  have ht0 : 0 < t := ht.1
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
  -- scalar limits along the sequence
  have hlamt : Tendsto (fun n => t * lam n) atTop (nhdsWithin (0:ℝ) (Ioi 0)) :=
    tendsto_mul_seq_nhdsWithin ht0 hlam
  have hIn' : Tendsto (fun n => clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3))
      atTop (nhds κ) := hIn.comp hlamt
  have hDn' : Tendsto (fun n =>
      deriv (fun u : ℝ => clusterInertia m k (x u)) (t * lam n) / (t * lam n) ^ ((1:ℝ)/3))
      atTop (nhds ((4:ℝ)/3 * κ)) := hDn.comp hlamt
  have hsq' : Tendsto
      (fun n => Real.sqrt (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3)))
      atTop (nhds (Real.sqrt κ)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hIn'
  have hs' : Tendsto (fun n => clusterShape m k (x (t * lam n))) atTop (nhds sbar) := hseq t ht
  -- `lam • ṡ(t lam) → 0`
  have hts'' : Tendsto (fun n => lam n • deriv (fun u : ℝ => clusterShape m k (x u)) (t * lam n))
      atTop (nhds 0) := by
    have h := hts.comp hlamt
    have h2 : Tendsto (fun n => t⁻¹ • ((t * lam n)
        • deriv (fun u : ℝ => clusterShape m k (x u)) (t * lam n)))
        atTop (nhds (t⁻¹ • (0 : EN E N))) := h.const_smul t⁻¹
    rw [smul_zero] at h2
    refine Filter.Tendsto.congr' ?_ h2
    filter_upwards with n
    rw [smul_smul]
    congr 1
    field_simp
  -- (1) the first summand of the rescaled derivative
  have hT1 : Tendsto (fun n =>
      (t ^ ((2:ℝ)/3) * Real.sqrt (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3)))
        • (lam n • deriv (fun u : ℝ => clusterShape m k (x u)) (t * lam n)))
      atTop (nhds 0) := by
    have hcst : Tendsto (fun _ : ℕ => t ^ ((2:ℝ)/3)) atTop (nhds (t ^ ((2:ℝ)/3))) :=
      tendsto_const_nhds
    have h := (hcst.mul hsq').smul hts''
    rw [smul_zero] at h
    exact h
  -- (2) the second summand
  have hT2 : Tendsto (fun n =>
      ((deriv (fun u : ℝ => clusterInertia m k (x u)) (t * lam n) / (t * lam n) ^ ((1:ℝ)/3))
          * (t ^ (-(1:ℝ)/3)
              / (2 * Real.sqrt (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3)))))
        • clusterShape m k (x (t * lam n)))
      atTop (nhds (((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) • sbar)) := by
    have hscal : Tendsto (fun n =>
        (deriv (fun u : ℝ => clusterInertia m k (x u)) (t * lam n) / (t * lam n) ^ ((1:ℝ)/3))
          * (t ^ (-(1:ℝ)/3)
              / (2 * Real.sqrt (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3)))))
        atTop (nhds ((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3))) := by
      have hconst : Tendsto (fun _ : ℕ => t ^ (-(1:ℝ)/3)) atTop (nhds (t ^ (-(1:ℝ)/3))) :=
        tendsto_const_nhds
      have hden : Tendsto (fun n =>
          2 * Real.sqrt (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3)))
          atTop (nhds (2 * Real.sqrt κ)) :=
        tendsto_const_nhds.mul hsq'
      have hinv : Tendsto (fun n =>
          t ^ (-(1:ℝ)/3) / (2 * Real.sqrt (clusterInertia m k (x (t * lam n))
            / (t * lam n) ^ ((4:ℝ)/3))))
          atTop (nhds (t ^ (-(1:ℝ)/3) / (2 * Real.sqrt κ))) :=
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
  -- identify the rescaled derivative with the two summands
  -- the raw form: `λ_n^{1/3} • q̇(t λ_n)` converges
  have hraw : Tendsto (fun n => lam n ^ ((1:ℝ)/3)
      • deriv (fun u : ℝ => cmRel m k (x u)) (t * lam n)) atTop
      (nhds (((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) • sbar)) := by
    refine Filter.Tendsto.congr' ?_ hsum
    filter_upwards [eventually_mem_Ioo_of_tendsto_nhdsWithin hε hlam,
      eventually_mem_Ioo_of_tendsto_nhdsWithin hε hlamt] with n hn hmn
    have hlam0 : 0 < lam n := hn.1
    have hmem : t * lam n ∈ Ioo (0:ℝ) ε := hmn
    have hIpos : 0 < clusterInertia m k (x (t * lam n)) := hpos (t * lam n) hmem
    have hdecomp : Real.sqrt (clusterInertia m k (x (t * lam n)))
        = Real.sqrt ((t * lam n) ^ ((4:ℝ)/3))
          * Real.sqrt (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3)) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    have hroot4 : Real.sqrt ((t * lam n) ^ ((4:ℝ)/3)) = lam n ^ ((2:ℝ)/3) * t ^ ((2:ℝ)/3) := by
      have h3 : Real.sqrt ((t * lam n) ^ ((4:ℝ)/3)) = (t * lam n) ^ ((2:ℝ)/3) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt (mul_pos ht0 hlam0))]
        norm_num
      rw [h3, Real.mul_rpow (le_of_lt ht0) (le_of_lt hlam0), mul_comm]
    have hl1 : lam n ^ ((1:ℝ)/3) * lam n ^ ((2:ℝ)/3) = lam n := by
      rw [← Real.rpow_add hlam0]
      norm_num
    have hl3 : (t * lam n) ^ ((1:ℝ)/3) = lam n ^ ((1:ℝ)/3) * t ^ ((1:ℝ)/3) := by
      rw [Real.mul_rpow (le_of_lt ht0) (le_of_lt hlam0), mul_comm]
    have hneg : t ^ (-(1:ℝ)/3) = (t ^ ((1:ℝ)/3))⁻¹ := by
      rw [show (-(1:ℝ)/3) = -((1:ℝ)/3) by norm_num, Real.rpow_neg (le_of_lt ht0)]
    have hl13 : lam n ^ ((1:ℝ)/3) * lam n ^ ((1:ℝ)/3) = lam n ^ ((2:ℝ)/3) := by
      rw [← Real.rpow_add hlam0]
      norm_num
    have ht13 : t ^ ((1:ℝ)/3) * t ^ ((1:ℝ)/3) = t ^ ((2:ℝ)/3) := by
      rw [← Real.rpow_add ht0]
      norm_num
    rw [hq (t * lam n) hmem, smul_add]
    congr 1
    · have hkmul : lam n ^ ((1:ℝ)/3) * Real.sqrt (clusterInertia m k (x (t * lam n)))
          = t ^ ((2:ℝ)/3)
              * Real.sqrt (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3))
              * lam n := by
        have hcomb : ∀ c Z : ℝ, lam n ^ ((1:ℝ)/3) * (lam n ^ ((2:ℝ)/3) * c * Z)
            = c * Z * lam n := by
          intro c Z
          rw [show lam n ^ ((1:ℝ)/3) * (lam n ^ ((2:ℝ)/3) * c * Z)
              = (lam n ^ ((1:ℝ)/3) * lam n ^ ((2:ℝ)/3)) * (c * Z) by ring, hl1]
          ring
        rw [hdecomp, hroot4]
        exact hcomb (t ^ ((2:ℝ)/3)) _
      simp only [smul_smul]
      rw [hkmul]
    · have hkmul : lam n ^ ((1:ℝ)/3) * (deriv (fun u : ℝ => clusterInertia m k (x u))
          (t * lam n) / (2 * Real.sqrt (clusterInertia m k (x (t * lam n)))))
          = (deriv (fun u : ℝ => clusterInertia m k (x u)) (t * lam n)
              / (t * lam n) ^ ((1:ℝ)/3))
            * (t ^ (-(1:ℝ)/3)
                / (2 * Real.sqrt (clusterInertia m k (x (t * lam n))
                    / (t * lam n) ^ ((4:ℝ)/3)))) := by
        rw [hdecomp, hroot4, hl3, hneg, ← hl13, ← ht13]
        have h6 : lam n ^ ((1:ℝ)/3) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlam0 _)
        have h7 : t ^ ((1:ℝ)/3) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht0 _)
        field_simp
      simp only [smul_smul]
      rw [hkmul]
  -- bridge to the derivative of the rescaled centred configuration
  have hbridge : (fun n => lam n ^ ((1:ℝ)/3)
      • deriv (fun u : ℝ => cmRel m k (x u)) (t * lam n))
      =ᶠ[atTop] (fun n => deriv (rescaledCentered m k x (lam n)) t) := by
    filter_upwards [eventually_mem_Ioo_of_tendsto_nhdsWithin hε hlam,
      eventually_mem_Ioo_of_tendsto_nhdsWithin hε hlamt] with n hn hmn
    have hlam0 : 0 < lam n := hn.1
    have hmn' : lam n * t ∈ Ioo (0:ℝ) ε := by
      rw [mul_comm]
      exact hmn
    have hv : HasDerivAt (fun u : ℝ => cmRel m k (x u)) (cmRel m k (deriv x (lam n * t)))
        (lam n * t) := hasDerivAt_cmRel m k (hx (lam n * t) hmn')
    have hb := deriv_rescaledCentered (m := m) (k := k) (x := x) hlam0 hv
    have hD : deriv (fun u : ℝ => cmRel m k (x u)) (t * lam n)
        = cmRel m k (deriv x (lam n * t)) := by
      rw [show deriv (fun u : ℝ => cmRel m k (x u)) (t * lam n)
          = cmRel m k (deriv x (t * lam n)) from
        (hasDerivAt_cmRel m k (hx (t * lam n) hmn)).deriv]
      congr 1
      rw [mul_comm]
    rw [hD]
    exact hb.symm
  rw [deriv_blowUpProfile κ sbar ht0]
  exact Filter.Tendsto.congr' hbridge hraw

end Submission.NBody
