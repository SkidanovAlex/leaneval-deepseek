import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.radA_traces
import Submission.Work.FTS.StrongEps.EpsRLX.N0DiffClassC
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.StreamOps
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.LGammaTMem
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.L12.linPart_tendsto
import Submission.Work.FTS.StrongEps.PZeroAux.softClass_Pz
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.AKSlot
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzSlot
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCThetaHolder
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.THL.theta_holder_of_HkMem
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.Stability.ZcutSmoothCompact
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.hkNorm_PzJeps_le_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The projection `Pz` is bounded in `ℋᵏ` for every order `k ≥ 4` -/

/-- **`Pz` is bounded on `ℋᵏ` for every order `k ∈ [4,6]`, uniformly in `α`.**

`Pz f = f + (−c) • bump` with `c = L₁₂ f 0 / pzNorm`.  The zero-mode coefficient is controlled
by `|L₁₂ f 0| ≤ C₁ ‖f‖_{ℋ⁴} ≤ C₁ ‖f‖_{ℋᵏ}` (`OpenPkg.l12zero_field` and the monotonicity
`HkNorm_mono_of_mem`, valid because `4 ≤ k`), the correction profile is uniformly bounded by
`‖bump‖_{ℋᵏ} ≤ B` (`PZeroAux.exists_HkNorm_bump_le`, `k ≤ 6`), and the two pieces are glued with
the subadditivity `HkNorm_add_fts` and the absolute homogeneity `HkNorm_const_mul` of the open
quadrant norm.  The constant is `A₁ = √2 (1 + C₁ B / pzNorm)`, exactly as in
`E5G.hkNorm_Pz_le_four`. -/
theorem hkNorm_Pz_le_of_ge_four :
    ∃ A : ℝ, 0 < A ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ (k : ℕ), 4 ≤ k → k ≤ 6 →
      ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
        Work.Spaces.HkMem α k f →
          Work.Spaces.HkNorm α k (Work.FTS.StrongEps.Pz f)
            ≤ A * Work.Spaces.HkNorm α k f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongEps.PZeroAux.exists_HkNorm_bump_le
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  have hC₁nn : 0 ≤ C₁ := hC₁pos.le
  refine ⟨Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm), ?_, ?_⟩
  · have h1 : 0 < C₁ * B / Work.FTS.StrongEps.pzNorm :=
      div_pos (mul_pos hC₁pos hBpos) hpzpos
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  · intro α hα k hk4 hk6 f hfsm hmk
    have hα0 : 0 < α := hα.1
    have hα1 : α ≤ 1 := hα.2
    -- descent `ℋᵏ → ℋ⁴` (`4 ≤ k`)
    have hm4 : Work.Spaces.HkMem α 4 f :=
      Work.FTS.OpenPkg.HkMem_mono_open hfsm 4 hk4 hmk
    -- the zero-mode bound, in `ℋ⁴`
    have hl12 : |Work.Construction.L12 f 0| ≤ C₁ * Work.Spaces.HkNorm α 4 f := by
      simpa only [Work.FTS.Nonlin.Xn] using hC₁ α hα0 hα1 f ⟨hfsm, hm4⟩
    -- and ascent `ℋ⁴ → ℋᵏ`
    have hnorm4k : Work.Spaces.HkNorm α 4 f ≤ Work.Spaces.HkNorm α k f :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem hk4 hmk
    have hcoefnn : 0 ≤ C₁ / Work.FTS.StrongEps.pzNorm := div_nonneg hC₁nn hpzpos.le
    -- the correction coefficient is controlled by the `ℋᵏ`-norm
    have hc_bound : |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
        ≤ (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α k f := by
      rw [abs_div, abs_of_pos hpzpos]
      calc |Work.Construction.L12 f 0| / Work.FTS.StrongEps.pzNorm
          ≤ (C₁ * Work.Spaces.HkNorm α 4 f) / Work.FTS.StrongEps.pzNorm :=
            div_le_div_of_nonneg_right hl12 hpzpos.le
        _ = (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 f := by ring
        _ ≤ (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α k f :=
            mul_le_mul_of_nonneg_left hnorm4k hcoefnn
    -- the correction profile
    have hbmem : Work.Spaces.HkMem α k Work.FTS.StrongEps.bump :=
      Work.FTS.StrongEps.PZeroAux.hkMem_bump α k
    have hbnorm : Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump ≤ B :=
      hB α hα k hk6
    have hgbump : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry Work.FTS.StrongEps.bump)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun n => Work.FTS.StrongEps.smoothOpen_bump.forall n
    have hgsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
      Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen _
        Work.FTS.StrongEps.smoothOpen_bump
    have hgmem : Work.Spaces.HkMem α k
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
      Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen _ hbmem
    -- `Pz f` in the additive shape needed by the subadditivity lemma
    have hPz : Work.FTS.StrongEps.Pz f
        = fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ := by
      funext z θ
      rw [Work.FTS.StrongEps.Pz_apply]
      ring
    rw [hPz]
    have hadd := Work.FTS.EllipticEst.HkNorm_add_fts α k
      (fun n => hfsm.forall n) (fun n => hgsm.forall n) hmk hgmem
    have hcm : Work.Spaces.HkNorm α k
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ)
        = |-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)|
          * Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump :=
      Work.FTS.EllipticEst.HkNorm_const_mul α k _ hgbump
    rw [hcm, abs_neg] at hadd
    calc Work.Spaces.HkNorm α k (fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f
            + |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
              * Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump) := hadd
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f
            + (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α k f * B) := by
          refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (Real.sqrt_nonneg 2)
          exact mul_le_mul hc_bound hbnorm (Work.Spaces.HkNorm_nonneg _ _ _)
            (mul_nonneg hcoefnn (Work.Spaces.HkNorm_nonneg _ _ _))
      _ = Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.HkNorm α k f := by ring

/-! ## The main theorem -/

/-- **`Pz ∘ J_ε` is bounded on `ℋᵏ`, uniformly in `α ∈ (0,1]`, `k ∈ [4,6]` and `ε ∈ (0,1]`.**

The mollifier `J_ε` preserves `ℋᵏ` (`HkMem_Jeps`), its `ℋᵏ`-norm grows at most by `e^{Cε/2}`
(the square root of the `E1` bound `HkSq_Jeps_le`), and `Pz` is bounded on `ℋᵏ`
(`hkNorm_Pz_le_of_ge_four`); note that `J_ε f` is `SmoothOpen` for a smooth kernel
(`SmoothOpen_Jeps`).  The resulting constant is `A₁ e^{C/2}`, independent of `ε ≤ 1`. -/
theorem hkNorm_PzJeps_le_gen (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ A : ℝ, 0 < A ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ (k : ℕ), 4 ≤ k → k ≤ 6 →
      ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) 1 → ∀ f : Work.FTS.Galerkin.Fn,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) →
        Work.Spaces.HkMem α k f →
          Work.Spaces.HkNorm α k (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
            ≤ A * Work.Spaces.HkNorm α k f := by
  obtain ⟨A₁, hA₁pos, hA₁⟩ := hkNorm_Pz_le_of_ge_four
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.HkSq_Jeps_le ρ hρ.moll
  refine ⟨A₁ * Real.exp (C / 2), by positivity, ?_⟩
  intro α hα k hk4 hk6 ε hε f hf hmk
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- `J_ε f` is `C^∞` on the open quadrant and of class `ℋᵏ`
  have hsmJ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall
      (Work.FTS.StrongEps.SmoothOpen_Jeps ρ hρ.moll hε0 hf)
  have hmemJ : Work.Spaces.HkMem α k (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε0 hf hmk
  -- the `ℋᵏ`-bound for the mollifier, from the `E1` bound on `HkSq`
  have hsq := hC α hα k ε hε0 hε1 f hf hmk hmemJ
  have hnormJ : Work.Spaces.HkNorm α k (Work.FTS.StrongEps.Jeps ρ ε f)
      ≤ Real.exp (C / 2) * Work.Spaces.HkNorm α k f := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α k (Work.FTS.StrongEps.Jeps ρ ε f))
        ≤ Real.sqrt (Real.exp (C * ε) * Work.Spaces.HkSq α k f) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (Real.exp (C * ε)) * Real.sqrt (Work.Spaces.HkSq α k f) :=
          Real.sqrt_mul (Real.exp_pos _).le _
      _ ≤ Real.exp (C / 2) * Real.sqrt (Work.Spaces.HkSq α k f) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          rw [← Real.exp_half (C * ε)]
          exact Real.exp_le_exp.mpr (by nlinarith [hε1, hCpos.le])
  calc Work.Spaces.HkNorm α k (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
      ≤ A₁ * Work.Spaces.HkNorm α k (Work.FTS.StrongEps.Jeps ρ ε f) :=
        hA₁ α hα k hk4 hk6 _ hsmJ hmemJ
    _ ≤ A₁ * (Real.exp (C / 2) * Work.Spaces.HkNorm α k f) :=
        mul_le_mul_of_nonneg_left hnormJ hA₁pos.le
    _ = A₁ * Real.exp (C / 2) * Work.Spaces.HkNorm α k f := by ring

end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.hkNorm_Pz_le_five =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem hkNorm_Pz_le_five : ∃ A : ℝ, 0 < A ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ f : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 5 f →
      Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.Pz f) ≤ A * Work.Spaces.HkNorm α 5 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongEps.PZeroAux.exists_HkNorm_bump_le
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  have hC₁nn : 0 ≤ C₁ := hC₁pos.le
  refine ⟨Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm), ?_, ?_⟩
  · have h1 : 0 < C₁ * B / Work.FTS.StrongEps.pzNorm :=
      div_pos (mul_pos hC₁pos hBpos) hpzpos
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  · intro α hα f hfsm hm5
    have hα0 : 0 < α := hα.1
    have hα1 : α ≤ 1 := hα.2
    -- the `ℋ⁴`-membership used by the zero-mode estimate
    have hm4 : Work.Spaces.HkMem α 4 f :=
      Work.FTS.OpenPkg.HkMem_mono_open hfsm 4 (by norm_num) hm5
    have hnorm45 : Work.Spaces.HkNorm α 4 f ≤ Work.Spaces.HkNorm α 5 f :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num) hm5
    -- the zero-mode bound, upgraded from `ℋ⁴` to `ℋ⁵`
    have hl12_4 : |Work.Construction.L12 f 0| ≤ C₁ * Work.Spaces.HkNorm α 4 f := by
      simpa only [Work.FTS.Nonlin.Xn] using hC₁ α hα0 hα1 f ⟨hfsm, hm4⟩
    have hl12 : |Work.Construction.L12 f 0| ≤ C₁ * Work.Spaces.HkNorm α 5 f :=
      le_trans hl12_4 (mul_le_mul_of_nonneg_left hnorm45 hC₁nn)
    have hcoefnn : 0 ≤ C₁ / Work.FTS.StrongEps.pzNorm := div_nonneg hC₁nn hpzpos.le
    -- the correction coefficient is controlled by the `ℋ⁵`-norm
    have hc_bound : |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
        ≤ (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 5 f := by
      rw [abs_div, abs_of_pos hpzpos]
      calc |Work.Construction.L12 f 0| / Work.FTS.StrongEps.pzNorm
          ≤ (C₁ * Work.Spaces.HkNorm α 5 f) / Work.FTS.StrongEps.pzNorm :=
            div_le_div_of_nonneg_right hl12 hpzpos.le
        _ = (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 5 f := by ring
    -- the correction profile
    have hbmem : Work.Spaces.HkMem α 5 Work.FTS.StrongEps.bump :=
      Work.FTS.StrongEps.PZeroAux.hkMem_bump α 5
    have hbnorm : Work.Spaces.HkNorm α 5 Work.FTS.StrongEps.bump ≤ B :=
      hB α hα 5 (by norm_num)
    have hgbump : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry Work.FTS.StrongEps.bump)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun n => Work.FTS.StrongEps.smoothOpen_bump.forall n
    have hgsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
      Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen _
        Work.FTS.StrongEps.smoothOpen_bump
    have hgmem : Work.Spaces.HkMem α 5
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
      Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen _ hbmem
    -- `Pz f` in the additive shape needed by the subadditivity lemma
    have hPz : Work.FTS.StrongEps.Pz f
        = fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ := by
      funext z θ
      rw [Work.FTS.StrongEps.Pz_apply]
      ring
    rw [hPz]
    have hadd := Work.FTS.EllipticEst.HkNorm_add_fts α 5
      (fun n => hfsm.forall n) (fun n => hgsm.forall n) hm5 hgmem
    have hcm : Work.Spaces.HkNorm α 5
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ)
        = |-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)|
          * Work.Spaces.HkNorm α 5 Work.FTS.StrongEps.bump :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 5 _ hgbump
    rw [hcm, abs_neg] at hadd
    calc Work.Spaces.HkNorm α 5 (fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 5 f
            + |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
              * Work.Spaces.HkNorm α 5 Work.FTS.StrongEps.bump) := hadd
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 5 f
            + (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 5 f * B) := by
          refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (Real.sqrt_nonneg 2)
          exact mul_le_mul hc_bound hbnorm (Work.Spaces.HkNorm_nonneg _ _ _)
            (mul_nonneg hcoefnn (Work.Spaces.HkNorm_nonneg _ _ _))
      _ = Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.HkNorm α 5 f := by ring

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.BlocksQuadrant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option linter.unusedVariables false





end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT`

**`𝓛_Γ^T x ∈ RegQo α 4` for every profile `x` of the class `ClassC α`, `α ∈ (0,1]`.**

`RegQo α k f = SmoothOpen f ∧ HkMem α k f ∧ BdryTraces α k f` (`EpsE4Thr/OpenClass.lean`).
The three conjuncts:

* `SmoothOpen`: `GalFields.RHS.smoothOpen_LGammaT_of_L12` with the smoothness of the angular
  moment `z ↦ L₁₂ x z` supplied by `ClassCRHS.smoothOpen_L12_radial_classC` (the `ClassC.fsm`
  field);
* `HkMem α 4`: `EpsZero.ClassCHk.HkMem_Lhat_of_classC` + `HkMem_Corr_of_classC` glued by
  `OpenPkg.HkMem_add_of_contDiffOn_four` through `𝓛_Γ^T = 𝓛̂ + Corr`;
* `BdryTraces α 4`: `ClassC.bdryTraces_add` on the same splitting, with
  `TracesAux.BdryTraces_Lhat` (the clean part) and `BdryTraces_Corr` (the transfer part,
  which is `Transfer.Corr_eq_radA` plus `TracesAux.BdryTraces_Gam_mul_rad` fed by the radial
  traces `TracesAux.radA_traces`).

The bounds underlying `radA_traces` are in `regQo_LGammaT_Aux`; the analytic input
(`Qang x k = O(z^{3/2})`, from the Poincaré argument) is `L12Aux.Qang_small_z`, and the
`z`-decay of the transfer profile `ampA` (its `Zop`-iterates are dominated by `z/(1+z)²`) is
`L12Aux.ampA_dzdIter_abs_le`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `L₁₂ x` is `C^n` on `(0,∞)` for a `ClassC` profile. -/
theorem contDiffOn_L12f {α : ℝ} (hα : 0 < α) {x : Fn}
    (hx : Work.FTS.ClassC.ClassC α x) (n : ℕ) :
    ContDiffOn ℝ n (Work.Coercivity.L12f x) (Set.Ioi 0) := by
  rw [L12f_eq_elliptic]
  have hsm := Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hx
  have h := hsm.curry_z (θ := (1 : ℝ) / 2) ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
  exact contDiffOn_infty.mp h n

/-- `radA α x` is `C^n` on `(0,∞)`. -/
theorem contDiffOn_radA {α : ℝ} (hα : 0 < α) {x : Fn}
    (hx : Work.FTS.ClassC.ClassC α x) (n : ℕ) :
    ContDiffOn ℝ n (Work.FTS.CoercivityFix.Transfer.radA α x) (Set.Ioi 0) := by
  have hampA : ContDiffOn ℝ n (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi 0) := by
    by_cases hc : Work.Spaces.c α = 0
    · have hzero : Work.FTS.CoercivityFix.Transfer.ampA α = fun _ : ℝ => 0 := by
        funext z
        simp only [Work.FTS.CoercivityFix.Transfer.ampA, hc, zero_mul, div_zero]
      rw [hzero]
      exact contDiffOn_const
    · exact (contDiffOn_const.mul contDiffOn_id).div
        (contDiffOn_const.mul ((contDiffOn_const.add contDiffOn_id).pow 2))
        (fun z hz => by
          have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
          exact mul_ne_zero hc (pow_ne_zero 2 (ne_of_gt h1)))
  have hampB : ContDiffOn ℝ n (Work.FTS.CoercivityFix.Transfer.ampB α) (Set.Ioi 0) :=
    (contDiffOn_const.mul (contDiffOn_id.pow 2)).div
      ((contDiffOn_const.add contDiffOn_id).pow 3)
      (fun z hz => by
        have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
        exact pow_ne_zero 3 (ne_of_gt h1))
  have hfun : Work.FTS.CoercivityFix.Transfer.radA α x
      = fun z => (Work.Coercivity.L12f (Work.Coercivity.Transport x) 0 / Work.Spaces.c α)
          * Work.FTS.CoercivityFix.Transfer.ampB α z
        + -(Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f x z) := by
    funext z
    simp only [Work.FTS.CoercivityFix.Transfer.radA, Work.FTS.CoercivityFix.Transfer.ampA,
      Work.FTS.CoercivityFix.Transfer.ampB]
    ring
  rw [hfun]
  refine ContDiffOn.add ?_ ?_
  · exact contDiffOn_const.mul hampB
  · exact (hampA.mul (contDiffOn_L12f hα hx n)).neg

/-- A single constant dominating `|Qang x k z| / z^{3/2}` for all `k ≤ 3`, `z ∈ (0,1)`. -/
theorem exists_Qang_bound {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Fn}
    (hx : Work.FTS.ClassC.ClassC α x) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z → z < 1 →
      |Work.Elliptic.Qang x k z| ≤ C * z ^ ((3 : ℝ) / 2) := by
  obtain ⟨C0, hC0, hQ0⟩ := Work.FTS.StrongEps.EpsE4Thr.L12Aux.Qang_small_z hα hx
    (k := 0) (by norm_num)
  obtain ⟨C1, hC1, hQ1⟩ := Work.FTS.StrongEps.EpsE4Thr.L12Aux.Qang_small_z hα hx
    (k := 1) (by norm_num)
  obtain ⟨C2, hC2, hQ2⟩ := Work.FTS.StrongEps.EpsE4Thr.L12Aux.Qang_small_z hα hx
    (k := 2) (by norm_num)
  obtain ⟨C3, hC3, hQ3⟩ := Work.FTS.StrongEps.EpsE4Thr.L12Aux.Qang_small_z hα hx
    (k := 3) (by norm_num)
  set M : ℝ := max (max (max C0 C1) C2) C3 with hM
  have hC0M : C0 ≤ M := by rw [hM]; exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hC1M : C1 ≤ M := by rw [hM]; exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hC2M : C2 ≤ M := by rw [hM]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hC3M : C3 ≤ M := by rw [hM]; exact le_max_right _ _
  refine ⟨M, lt_of_lt_of_le hC0 hC0M, fun k hk z hz hz1 => ?_⟩
  have hzr : 0 ≤ z ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hz.le _
  interval_cases k
  · exact le_trans (hQ0 z hz hz1) (mul_le_mul_of_nonneg_right hC0M hzr)
  · exact le_trans (hQ1 z hz hz1) (mul_le_mul_of_nonneg_right hC1M hzr)
  · exact le_trans (hQ2 z hz hz1) (mul_le_mul_of_nonneg_right hC2M hzr)
  · exact le_trans (hQ3 z hz hz1) (mul_le_mul_of_nonneg_right hC3M hzr)

/-- **The boundary traces of the transfer part** `Corr α x = Γ(θ)·radA α x (z)`. -/
theorem BdryTraces_Corr {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Fn}
    (hx : Work.FTS.ClassC.ClassC α x) :
    Work.FTS.Nonlin.BdryTraces α 4 (Work.FTS.CoercivityFix.Corr α x) := by
  obtain ⟨C, hC, hQ⟩ := exists_Qang_bound hα hx
  obtain ⟨hr0, hr1⟩ := Work.FTS.StrongEps.EpsE4Thr.TracesAux.radA_traces (x := x) hα hx hC
    hQ (fun b => Work.FTS.StrongEps.EpsE4Thr.L12Aux.ampA_dzdIter_abs_le α b)
  have hmain := Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_Gam_mul_rad
    (α := α) (k := 4) (r := Work.FTS.CoercivityFix.Transfer.radA α x) hα.1
    (Cg := 100000) (by norm_num)
    (fun a _ θ hθ0 hθ1 =>
      Work.FTS.LocData6.DthIter_Gam_abs_le6 a (by omega) α hα.1 hα.2
        ⟨le_of_lt hθ0, le_of_lt hθ1⟩)
    (contDiffOn_radA hα.1 hx 5) hr0 hr1
  rw [show Work.FTS.CoercivityFix.Corr α x
      = fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radA α x z from by
    funext z θ
    exact Work.FTS.CoercivityFix.Transfer.Corr_eq_radA α x z θ]
  exact hmain

theorem regQo_LGammaT {α : ℝ} {x : Work.FTS.Galerkin.Fn} (hα : α ∈ Set.Ioc 0 1)
    (hx : Work.FTS.ClassC.ClassC α x) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α 4 (Work.Coercivity.LGammaT α x) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
      (α := α) (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα.1 hx) hx.reg
  · have hmemL : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Lhat x) :=
      Work.FTS.StrongEps.EpsZero.ClassCHk.HkMem_Lhat_of_classC hα.1 hx
    have hmemC : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Corr α x) :=
      Work.FTS.StrongEps.EpsZero.ClassCHk.HkMem_Corr_of_classC hα.1 hα.2 hx
    have hsmC : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Corr α x))
        Work.FTS.EllipticEst.Q0 :=
      Work.FTS.StrongEps.EpsZero.ClassCHk.contDiffOn_Corr_of_classC hα.1 hα.2 hx
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α x]
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
      ((Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hx.reg).forall 4) hsmC hmemL hmemC
  · have hsmL := Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hx.reg
    have hLGT := Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
      (α := α) (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα.1 hx) hx.reg
    have hsmC := Work.FTS.NonlinRows.smoothOpen_sub hLGT hsmL
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α x]
    exact Work.FTS.ClassC.bdryTraces_add hsmL hsmC
      (Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_Lhat hα.1 hx)
      (BdryTraces_Corr hα hx)

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The pointwise bounds on `ℛ(Φ̃_tot)`, `U(Φ̃_tot)`, `V(Φ̃_tot)` -/

/-- **`ℛ(Φ̃_tot)` is bounded on the open quadrant** (at fixed `z > 0`). -/
theorem RopPsiBound {α Cs Ce : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W Φg : ℝ → ℝ → ℝ}
    (hW : Work.FTS.ClassC.ClassC α W) (hell : Work.FTS.VocabO.EllPkgGo α Ce W Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {z : ℝ} (hz : 0 < z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Rop α (PsiTot α Φs W Φg) z θ| ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := star_op_bounds hstar
  obtain ⟨C₂, hC₂0, hC₂⟩ := ell_op_bounds hα.1 hα.2 hell
  have hWm : Work.Spaces.HkMem α 4 W :=
    Work.FTS.OpenPkg.HkMem_mono_open hW.reg 4 (by norm_num) hW.mem
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro θ hθ0 hθ1
  rw [Rop_PsiTot_eq hα.1 hα.2 hstar.smooth hW.reg hWm hell.smooth hz hθ0 hθ1]
  have h1 := (hC₁ hz hθ0 hθ1).1
  have h2 := (hC₂ hz hθ0 hθ1).1
  calc |Work.Construction.Rop α (PsiStar α Φs) z θ
        + Work.Construction.Rop α (PsiEll α W Φg) z θ|
      ≤ |Work.Construction.Rop α (PsiStar α Φs) z θ|
        + |Work.Construction.Rop α (PsiEll α W Φg) z θ| := abs_add_le _ _
    _ ≤ C₁ + C₂ := add_le_add h1 h2

/-- **`V(Φ̃_tot)` is bounded on the open quadrant** (at fixed `z > 0`). -/
theorem VopPsiBound {α Cs Ce : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W Φg : ℝ → ℝ → ℝ}
    (hW : Work.FTS.ClassC.ClassC α W) (hell : Work.FTS.VocabO.EllPkgGo α Ce W Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {z : ℝ} (hz : 0 < z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (PsiTot α Φs W Φg) z θ| ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := star_op_bounds hstar
  obtain ⟨C₂, hC₂0, hC₂⟩ := ell_op_bounds hα.1 hα.2 hell
  have hWm : Work.Spaces.HkMem α 4 W :=
    Work.FTS.OpenPkg.HkMem_mono_open hW.reg 4 (by norm_num) hW.mem
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro θ hθ0 hθ1
  rw [Vop_PsiTot_eq hα.1 hα.2 hstar.smooth hW.reg hWm hell.smooth hz hθ0 hθ1]
  have h1 := (hC₁ hz hθ0 hθ1).2.1
  have h2 := (hC₂ hz hθ0 hθ1).2.1
  calc |Work.Construction.Vop (PsiStar α Φs) z θ
        + Work.Construction.Vop (PsiEll α W Φg) z θ|
      ≤ |Work.Construction.Vop (PsiStar α Φs) z θ|
        + |Work.Construction.Vop (PsiEll α W Φg) z θ| := abs_add_le _ _
    _ ≤ C₁ + C₂ := add_le_add h1 h2

/-- **`U(Φ̃_tot)` is divisible by `sin 2θ`, with a bounded quotient** (at fixed `z > 0`). -/
theorem UopPsiBound {α Cs Ce : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W Φg : ℝ → ℝ → ℝ}
    (hW : Work.FTS.ClassC.ClassC α W) (hell : Work.FTS.VocabO.EllPkgGo α Ce W Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {z : ℝ} (hz : 0 < z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Uop α (PsiTot α Φs W Φg) z θ| ≤ C * |Work.Construction.s2 θ| := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := star_op_bounds hstar
  obtain ⟨C₂, hC₂0, hC₂⟩ := ell_op_bounds hα.1 hα.2 hell
  have hWm : Work.Spaces.HkMem α 4 W :=
    Work.FTS.OpenPkg.HkMem_mono_open hW.reg 4 (by norm_num) hW.mem
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro θ hθ0 hθ1
  rw [Uop_PsiTot_eq hα.1 hα.2 hstar.smooth hW.reg hWm hell.smooth hz hθ0 hθ1]
  have h1 := (hC₁ hz hθ0 hθ1).2.2
  have h2 := (hC₂ hz hθ0 hθ1).2.2
  calc |Work.Construction.Uop α (PsiStar α Φs) z θ
        + Work.Construction.Uop α (PsiEll α W Φg) z θ|
      ≤ |Work.Construction.Uop α (PsiStar α Φs) z θ|
        + |Work.Construction.Uop α (PsiEll α W Φg) z θ| := abs_add_le _ _
    _ ≤ C₁ * |Work.Construction.s2 θ| + C₂ * |Work.Construction.s2 θ| := add_le_add h1 h2
    _ = (C₁ + C₂) * |Work.Construction.s2 θ| := by ring

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology

noncomputable section

set_option maxHeartbeats 1600000

/-- Multiplication of a `C^∞`-quadrant function by the radial factor `z/(1+z)`. -/
theorem smoothOpen_zShift {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * g z θ) := by
  refine Work.FTS.StrongPersist.H6Pair6Aux.so_mul
    (Work.FTS.StrongPersist.H6Pair6Aux.so_radial (fun n => ?_)) hg
  exact contDiffOn_id.div (contDiffOn_const.add contDiffOn_id) (fun z hz => by
    have hz' := hz; simp only [Set.mem_Ioi] at hz'; positivity)

theorem starSlotShift : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    (Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ∧
      Work.Spaces.HkMem α 6 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ)
        ≤ C * α ^ (-(1 : ℝ))) ∧
    (Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkMem α 6
        (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkNorm α 6
        (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
        ≤ C * α ^ (-(1 : ℝ))) ∧
    (Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkMem α 6
        (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkNorm α 6
        (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
        ≤ C * α ^ (-(1 : ℝ))) := by
  obtain ⟨B, hB, hbnd⟩ := DzdIter_oneSubOneAdd_le_local
  obtain ⟨CA, hCA, hA⟩ := starSlotA
  obtain ⟨CB, hCB, hB'⟩ := starSlotB
  obtain ⟨CC, hCC, hC⟩ := starSlotC_aux hB hbnd
  refine ⟨max (max CA CB) CC + 1, by positivity, ?_⟩
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨hAm, hAn⟩ := hA α hαIoc
  obtain ⟨hBm, hBn⟩ := hB' α hαIoc
  obtain ⟨hCm, hCn⟩ := hC α hαIoc
  have hαinv : 1 ≤ α ^ (-(1 : ℝ)) := by
    rw [show (-(1 : ℝ)) = -1 by ring, Real.rpow_neg_one]
    exact (one_le_inv₀ hα).mpr hα1
  have hkey : ∀ D : ℝ, D ≤ max (max CA CB) CC → D ≤ (max (max CA CB) CC + 1)
      * α ^ (-(1 : ℝ)) := by
    intro D hD
    have h1 : D ≤ max (max CA CB) CC + 1 := by linarith
    have h2 : max (max CA CB) CC + 1
        ≤ (max (max CA CB) CC + 1) * α ^ (-(1 : ℝ)) := by
      simpa using mul_le_mul_of_nonneg_left hαinv
        (show (0 : ℝ) ≤ max (max CA CB) CC + 1 by positivity)
    exact le_trans h1 h2
  refine ⟨⟨smoothOpen_zShift (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α), hAm,
      le_trans hAn (hkey CA (le_trans (le_max_left CA CB) (le_max_left _ _)))⟩,
    ⟨smoothOpen_zShift (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dth, hBm,
      le_trans hBn (hkey CB (le_trans (le_max_right CA CB) (le_max_left _ _)))⟩,
    ⟨smoothOpen_zShift (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dz, hCm,
      le_trans hCn (hkey CC (le_max_right _ _))⟩⟩

end

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
