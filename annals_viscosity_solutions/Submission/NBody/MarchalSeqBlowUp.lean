import Submission.NBody.MarchalSeqShape
import Submission.NBody.MarchalClusterShapeLimit
import Submission.NBody.MarchalClusterAsymptotic3
import Submission.NBody.MarchalClusterBlowUp
import Submission.Commons.Analysis.Asymptotic.tendsto_comp_mul_seq_of_tendsto_deriv_smul

/-!
# The sequential blow-up (Ferrario--Terracini `propo:srcblowup`)

FT's `propo:srcblowup` asserts: if `s(λ_n)` converges along a sequence `λ_n → 0⁺`, then also
`s(λ_n t) → s(λ_n)` — hence `s(λ_n t) → s̄` — for every fixed `t > 0`.  This is the *only* form in
which the limit of the normalised configuration is available (no genuine limit `s(t) → s̄` is
implied by the asymptotics of `propo:asy`), so the whole blow-up argument is carried out along a
sequence.

The proof is FT's: the mean value inequality gives
`‖s(λ_n t) - s(λ_n)‖ ≤ sup_{(t,1)} ‖ṡ‖ · λ_n (1-t) ≤ ε(1-t)/t` using `u ṡ(u) → 0`.

Here we also record the resulting pointwise convergence of the rescaled centred configuration
`q^{λ_n}(t) = λ_n^{-2/3}·(cmRel ∘ x)(t λ_n) → q̄(t) = √κ t^{2/3} s̄`.
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

/-- The derivative of the normalised configuration along a motion, in the isolated-cluster
situation. -/
lemma hasDerivAt_clusterShape_of_isolated {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ε) :
    HasDerivAt (fun u : ℝ => clusterShape m k (x u))
      (deriv (fun u : ℝ => clusterShape m k (x u)) t) t := by
  have hJpos : 0 < clusterInertia m k (x t) := clusterInertia_pos hm hk2 (hnc t ht)
  have hev : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s :=
    Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo ht) fun s hs => hx s hs
  have h := hasDerivAt_clusterShape_curve hJpos hev
  simpa only [h.deriv] using h

/-- **`propo:srcblowup`, sequential form.**  If along `λ_n → 0⁺` the normalised configurations
converge, then so do the normalised configurations at the rescaled times `t λ_n`. -/
theorem tendsto_clusterShape_seq_mul {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε C ν Cv T : ℝ}
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
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)))
    {sbar : EN E N}
    (hs : Tendsto (fun n => clusterShape m k (x (lam n))) atTop (nhds sbar)) :
    ∀ t ∈ Ioc (0:ℝ) T,
      Tendsto (fun n => clusterShape m k (x (lam n * t))) atTop (nhds sbar) :=
  Commons.Analysis.Asymptotic.tendsto_comp_mul_seq_of_tendsto_deriv_smul (f := fun u : ℝ =>
      clusterShape m k (x u)) hε hT
    (fun u hu => hasDerivAt_clusterShape_of_isolated hm hk2 hε hnc hx hu)
    (tendsto_mul_deriv_clusterShape hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI)
    hlam hs

variable [MeasurableSpace E] [BorelSpace E]

/-- **Pointwise convergence of the sequential blow-up.**  For fixed `t > 0`, the rescaled centred
configurations along `λ_n` converge to the parabolic blow-up profile. -/
theorem tendsto_rescaledCentered_seq {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε κ T : ℝ} {sbar : EN E N}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hκ : 0 < κ)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)))
    (hseq : ∀ t ∈ Ioc (0:ℝ) T,
      Tendsto (fun n => clusterShape m k (x (t * lam n))) atTop (nhds sbar)) :
    ∀ t ∈ Ioc (0:ℝ) T,
      Tendsto (fun n => rescaledCentered m k x (lam n) t) atTop (nhds (blowUpProfile κ sbar t)) := by
  intro t ht
  have ht0 : 0 < t := ht.1
  have hpos : ∀ s ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x s) :=
    fun s hs => clusterInertia_pos hm hk2 (hnc s hs)
  have hscale : Tendsto (fun n => t * lam n) atTop (nhdsWithin (0:ℝ) (Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff] at hlam ⊢
    refine ⟨?_, ?_⟩
    · have h := hlam.1.const_mul t
      simpa using h
    · filter_upwards [hlam.2] with n hn
      exact mul_pos ht0 hn
  have hIn' : Tendsto (fun n => clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3))
      atTop (nhds κ) := hIn.comp hscale
  have hc : Tendsto (fun n => Real.sqrt (clusterInertia m k (x (t * lam n))
      / (t * lam n) ^ ((4:ℝ)/3))) atTop (nhds (Real.sqrt κ)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hIn'
  have hs2 : Tendsto (fun n => t ^ ((2:ℝ)/3) • clusterShape m k (x (t * lam n)))
      atTop (nhds (t ^ ((2:ℝ)/3) • sbar)) := (hseq t ht).const_smul _
  have hprod := hc.smul hs2
  rw [show Real.sqrt κ • (t ^ ((2:ℝ)/3) • sbar)
      = (Real.sqrt κ * t ^ ((2:ℝ)/3)) • sbar by rw [smul_smul]] at hprod
  refine Filter.Tendsto.congr' ?_ hprod
  filter_upwards [hscale.eventually (Ioo_mem_nhdsGT hε)] with n hn
  have hlampos : 0 < lam n := by
    have h1 : 0 < t * lam n := hn.1
    nlinarith [ht0]
  have hu : 0 < t * lam n := hn.1
  have hult : t * lam n < ε := hn.2
  have hstep : clusterInertia m k (x (t * lam n))
      = (t * lam n) ^ ((4:ℝ)/3)
        * (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3)) := by
    field_simp
  have hsqu : Real.sqrt (clusterInertia m k (x (t * lam n)))
      = Real.sqrt ((t * lam n) ^ ((4:ℝ)/3))
        * Real.sqrt (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3)) := by
    rw [← Real.sqrt_mul (by positivity), ← hstep]
  have hroot : Real.sqrt ((t * lam n) ^ ((4:ℝ)/3))
      = lam n ^ ((2:ℝ)/3) * t ^ ((2:ℝ)/3) := by
    have h1 : Real.sqrt ((t * lam n) ^ ((4:ℝ)/3)) = (t * lam n) ^ ((2:ℝ)/3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hu)]
      norm_num
    rw [h1, Real.mul_rpow (le_of_lt ht0) (le_of_lt hlampos), mul_comm]
  rw [show rescaledCentered m k x (lam n) t
      = lam n ^ (-(2:ℝ)/3) • cmRel m k (x (t * lam n)) from rfl,
    cmRel_eq_sqrt_smul_clusterShape (hpos (t * lam n) ⟨hu, hult⟩), hsqu, hroot,
    smul_smul, smul_smul]
  congr 1
  have hneg : lam n ^ (-(2:ℝ)/3) = (lam n ^ ((2:ℝ)/3))⁻¹ := by
    rw [show (-(2:ℝ)/3) = -((2:ℝ)/3) by norm_num, Real.rpow_neg hlampos.le]
  have hne : lam n ^ ((2:ℝ)/3) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlampos _)
  rw [hneg]
  field_simp

end Submission.NBody
