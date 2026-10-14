import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongEps.PZeroAux.softClass_Pz
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.AKSlot
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.Congr
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCSinRate
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.EpsEngine.BlocksDecompDiffAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The `θ`-slices of `Theta α (Fstar α)` are differentiable.**  `Theta α F z θ'` is
`((1/(4α))·L₁₂(F)(z))·sin(2θ')`, i.e. a constant multiple of `sin(2θ')`. -/
theorem differentiableAt_tslice_Theta_Fstar {α z θ : ℝ} :
    DifferentiableAt ℝ
      (fun θ' => Work.Construction.Theta α (Work.Construction.Fstar α) z θ') θ := by
  have hsin : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id θ).const_mul (2 : ℝ)).sin
    simpa only [Work.Construction.s2] using h.differentiableAt
  have h := hsin.const_mul
    ((1 / (4 * α)) * Work.Construction.L12 (Work.Construction.Fstar α) z)
  have heq : (fun θ' => ((1 / (4 * α)) * Work.Construction.L12 (Work.Construction.Fstar α) z)
        * Work.Construction.s2 θ')
      = fun θ' => Work.Construction.Theta α (Work.Construction.Fstar α) z θ' := by
    funext θ'
    simp only [Work.Construction.Theta]
    ring
  rwa [heq] at h

/-- **The `z`-slices of `Theta α (Fstar α)` are differentiable.**  `Theta α F z' θ` is
`((1/(4α))·sin(2θ))·L₁₂(F)(z')`, and `L₁₂(F_*) = 2α/(1+z)` on `(0,∞)`. -/
theorem differentiableAt_zslice_Theta_Fstar {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hz : 0 < z) :
    DifferentiableAt ℝ
      (fun z' => Work.Construction.Theta α (Work.Construction.Fstar α) z' θ) z := by
  have hL : DifferentiableAt ℝ
      (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z :=
    Work.FTS.StrongEps.EpsRLX.ProfRHSAux.differentiableAt_L12_Fstar hα hα1 hz
  have h := hL.const_mul ((1 / (4 * α)) * Work.Construction.s2 θ)
  have heq : (fun z' => ((1 / (4 * α)) * Work.Construction.s2 θ)
        * Work.Construction.L12 (Work.Construction.Fstar α) z')
      = fun z' => Work.Construction.Theta α (Work.Construction.Fstar α) z' θ := by
    funext z'
    simp only [Work.Construction.Theta]
  rwa [heq] at h

/-- **The differentiability hypotheses of the three block decompositions, from open-quadrant smoothness.**  At a point `(z,θ)` of the open quadrant, the eight slice-differentiability inputs of the block decompositions of `Work.FTS.EpsEngine.RopBlockDecomp` / `UopSlot` / `VopSlot` (the z-slices and θ-slices of `PhiTil α f (E f)`, `Φs`, `PhiTil α F_* Φs` and `Theta α F_*`) follow from `SmoothOpen f` + `HkMem α 4 f` (which give `C³`, hence differentiability, of `L₁₂ f` on `(0,∞)`), `SmoothOpen (E f)`, `SmoothOpen Φs` and the explicit `smoothOpen_Theta_Fstar`. -/
theorem BlocksDecompDiffAt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f Φs : ℝ → ℝ → ℝ} {E : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hEf : Work.FTS.EllipticEst.SmoothOpen (E f))
    (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs) :
    (DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α f (E f) z' θ) z ∧
     DifferentiableAt ℝ (fun z' => Φs z' θ) z ∧
     DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
       Φs z' θ) z ∧
     DifferentiableAt ℝ (fun z' => Work.Construction.Theta α (Work.Construction.Fstar α)
       z' θ) z ∧
     DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α f (E f) z θ') θ ∧
     DifferentiableAt ℝ (fun θ' => Φs z θ') θ ∧
     DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
       Φs z θ') θ ∧
     DifferentiableAt ℝ (fun θ' => Work.Construction.Theta α (Work.Construction.Fstar α)
       z θ') θ) := by
  -- the `L₁₂` differentiability input for the datum `f`
  have hLf : DifferentiableAt ℝ (fun z' => Work.Construction.L12 f z') z :=
    Work.FTS.StrongEps.EpsRLX.ProfRHSAux.differentiableAt_L12_of_smoothOpen hα hα1 hf hmem hz
  -- the `z`- and `θ`-slices of the elliptic stream function `E f`
  have hEz : DifferentiableAt ℝ (fun z' => E f z' θ) z :=
    Work.FTS.StrongEps.EComparison.differentiableAt_zslice hEf hz hθ0 hθ1
  have hEt : DifferentiableAt ℝ (fun θ' => E f z θ') θ :=
    Work.FTS.StrongEps.EComparison.differentiableAt_tslice hEf hz hθ0 hθ1
  -- conjuncts 1 and 5: the slices of `PhiTil α f (E f)`
  have h15 := Work.FTS.StrongEps.EpsRLX.ProfRHSAux.differentiableAt_PhiTil
    (α := α) (F := f) (Ψ := E f) hEz hEt hLf
  -- conjuncts 2 and 6: the slices of `Φs`
  have h2 : DifferentiableAt ℝ (fun z' => Φs z' θ) z :=
    Work.FTS.StrongEps.EComparison.differentiableAt_zslice hΦs hz hθ0 hθ1
  have h6 : DifferentiableAt ℝ (fun θ' => Φs z θ') θ :=
    Work.FTS.StrongEps.EComparison.differentiableAt_tslice hΦs hz hθ0 hθ1
  -- conjuncts 3 and 7: the slices of `PhiTil α F_* Φs`
  have h37 := Work.FTS.StrongEps.EpsRLX.ProfRHSAux.PsiStar_diff hα hα1 hΦs hz hθ0 hθ1
  -- conjuncts 4 and 8: the slices of `Theta α F_*`
  have h4 : DifferentiableAt ℝ
      (fun z' => Work.Construction.Theta α (Work.Construction.Fstar α) z' θ) z :=
    differentiableAt_zslice_Theta_Fstar hα hα1 hz
  have h8 : DifferentiableAt ℝ
      (fun θ' => Work.Construction.Theta α (Work.Construction.Fstar α) z θ') θ :=
    differentiableAt_tslice_Theta_Fstar
  exact ⟨h15.1, h2, h37.1, h4, h15.2, h6, h37.2, h8⟩

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.hkNorm_Pz_le_four =====
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

theorem hkNorm_Pz_le_four : ∃ A : ℝ, 0 < A ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ f : Work.FTS.Galerkin.Fn,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.Pz f)
        ≤ A * Work.Spaces.HkNorm α 4 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongEps.PZeroAux.exists_HkNorm_bump_le
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  have hC₁nn : 0 ≤ C₁ := hC₁pos.le
  refine ⟨Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm), ?_, ?_⟩
  · have h1 : 0 < C₁ * B / Work.FTS.StrongEps.pzNorm :=
      div_pos (mul_pos hC₁pos hBpos) hpzpos
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  · intro α hα f hfsm hm4
    have hα0 : 0 < α := hα.1
    have hα1 : α ≤ 1 := hα.2
    -- the zero-mode bound, directly in `ℋ⁴`
    have hl12 : |Work.Construction.L12 f 0| ≤ C₁ * Work.Spaces.HkNorm α 4 f := by
      simpa only [Work.FTS.Nonlin.Xn] using hC₁ α hα0 hα1 f ⟨hfsm, hm4⟩
    have hcoefnn : 0 ≤ C₁ / Work.FTS.StrongEps.pzNorm := div_nonneg hC₁nn hpzpos.le
    -- the correction coefficient is controlled by the `ℋ⁴`-norm
    have hc_bound : |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
        ≤ (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 f := by
      rw [abs_div, abs_of_pos hpzpos]
      calc |Work.Construction.L12 f 0| / Work.FTS.StrongEps.pzNorm
          ≤ (C₁ * Work.Spaces.HkNorm α 4 f) / Work.FTS.StrongEps.pzNorm :=
            div_le_div_of_nonneg_right hl12 hpzpos.le
        _ = (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 f := by ring
    -- the correction profile
    have hbmem : Work.Spaces.HkMem α 4 Work.FTS.StrongEps.bump :=
      Work.FTS.StrongEps.PZeroAux.hkMem_bump α 4
    have hbnorm : Work.Spaces.HkNorm α 4 Work.FTS.StrongEps.bump ≤ B :=
      hB α hα 4 (by norm_num)
    have hgbump : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry Work.FTS.StrongEps.bump)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun n => Work.FTS.StrongEps.smoothOpen_bump.forall n
    have hgsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
      Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen _
        Work.FTS.StrongEps.smoothOpen_bump
    have hgmem : Work.Spaces.HkMem α 4
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
    have hadd := Work.FTS.EllipticEst.HkNorm_add_fts α 4
      (fun n => hfsm.forall n) (fun n => hgsm.forall n) hm4 hgmem
    have hcm : Work.Spaces.HkNorm α 4
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ)
        = |-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)|
          * Work.Spaces.HkNorm α 4 Work.FTS.StrongEps.bump :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 4 _ hgbump
    rw [hcm, abs_neg] at hadd
    calc Work.Spaces.HkNorm α 4 (fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 f
            + |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
              * Work.Spaces.HkNorm α 4 Work.FTS.StrongEps.bump) := hadd
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 f
            + (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 f * B) := by
          refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (Real.sqrt_nonneg 2)
          exact mul_le_mul hc_bound hbnorm (Work.Spaces.HkNorm_nonneg _ _ _)
            (mul_nonneg hcoefnn (Work.Spaces.HkNorm_nonneg _ _ _))
      _ = Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.HkNorm α 4 f := by ring

end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.smoothOpen_epsRHSP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps


end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DthSlot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The `ℋ⁶`-membership and norm bound of the `D_θF_*`-slot. -/
theorem starSlotB : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.Spaces.HkMem α 6
        (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
    Work.Spaces.HkNorm α 6
        (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ C := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 6
  obtain ⟨R, hR0, hrad⟩ := Work.FTS.StrongPersist.AK6.akRho_jet_bound6
  obtain ⟨_SAK, _hSAK, hAKb⟩ := Work.FTS.StrongPersist.AK_Mem6
  choose Sq hSq0 hSq using fun m : ℕ => Work.FTS.StrongPersist.W6Aux.deriv_iter_qfun_bounded m
  set Bq : ℝ := 4 / 3 + Sq 0 + Sq 1 + Sq 2 + Sq 3 + Sq 4 + Sq 5 with hBqdef
  have hBq0 : 0 < Bq := by
    rw [hBqdef]; linarith [hSq0 0, hSq0 1, hSq0 2, hSq0 3, hSq0 4, hSq0 5]
  have hBq43 : (4 : ℝ) / 3 ≤ Bq := by
    rw [hBqdef]; linarith [hSq0 0, hSq0 1, hSq0 2, hSq0 3, hSq0 4, hSq0 5]
  have hBqle : ∀ m : ℕ, m ≤ 5 → Sq m ≤ Bq := by
    intro m hm
    rw [hBqdef]
    interval_cases m <;> linarith [hSq0 0, hSq0 1, hSq0 2, hSq0 3, hSq0 4, hSq0 5]
  set X2 : ℝ := 2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700) with hX2def
  have hX20 : 0 ≤ X2 := by rw [hX2def]; positivity
  refine ⟨Real.sqrt (C₁ * Bq ^ 2 * X2) + 1, by positivity, ?_⟩
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨hAKmem, _⟩ := hAKb α hα hα1
  have hmemAK : Work.Spaces.HkMem α 6 (fun z θ => α * Work.Construction.AK α z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 α hAKmem
  have hSOAK : Work.FTS.EllipticEst.SmoothOpen (fun z θ => α * Work.Construction.AK α z θ) :=
    smoothOpen_alphaAK α
  have hSOa : Work.FTS.EllipticEst.SmoothOpen (fun x (θ : ℝ) => α * Work.Spaces.qfun θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_snd (contDiff_const.mul Work.Spaces.qfun_smooth)
  have haB : ∀ θ ∈ Work.Spaces.Iθ, |α * Work.Spaces.qfun θ| ≤ α * Bq := by
    intro θ hθ
    rw [abs_mul, abs_of_pos hα]
    have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
      have hq' : Work.Spaces.qfun θ = Real.cos (2 * θ) - 1 / 3 := rfl
      rw [hq', abs_le]
      constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
    exact mul_le_mul_of_nonneg_left (le_trans hq hBq43) hα.le
  have hjet : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun x (θ' : ℝ) => α * Work.Spaces.qfun θ') 0 θ|
        ≤ (α * Bq) * Real.sin (2 * θ) := by
    intro i hi hi6 θ hθ
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hDth : Work.Spaces.DthIter (j + 1)
          (fun x (θ' : ℝ) => α * Work.Spaces.qfun θ') 0 θ
        = Work.Spaces.dthU^[j + 1] (fun θ' => α * Work.Spaces.qfun θ') θ := by
      have h := Work.Spaces.DthIter_decomp (j + 1)
        (fun θ' => α * Work.Spaces.qfun θ') (fun _ => (1 : ℝ)) 0 θ
      simpa using h
    have hval : Work.Spaces.dthU^[j + 1] (fun θ' => α * Work.Spaces.qfun θ') θ
        = α * (Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[j] Work.Spaces.qfun) θ) := by
      rw [Function.iterate_succ_apply', Work.Spaces.dthU_apply,
        Work.Spaces.dthU_iter_const_mul, Work.Spaces.deriv_const_mul']
      ring
    rw [hDth, hval, abs_mul, abs_mul, abs_of_pos hα,
      abs_of_nonneg (Work.FTS.LocData.sin_two_nonneg hθ)]
    have hb : |deriv (Work.Spaces.dthU^[j] Work.Spaces.qfun) θ| ≤ Sq j := hSq j θ hθ
    have hj5 : j ≤ 5 := by omega
    have hsin : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.sin_two_nonneg hθ
    calc α * (Real.sin (2 * θ) * |deriv (Work.Spaces.dthU^[j] Work.Spaces.qfun) θ|)
        ≤ α * (Real.sin (2 * θ) * Bq) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (le_trans hb (hBqle j hj5)) hsin) hα.le
      _ = (α * Bq) * Real.sin (2 * θ) := by ring
  obtain ⟨hmem, hsq⟩ := hC₁ α hα hα1 (fun θ => α * Work.Spaces.qfun θ) (α * Bq)
    (mul_pos hα hBq0) hSOa haB hjet (fun z θ => α * Work.Construction.AK α z θ) hSOAK hmemAK
  have hpt := alphaAK_integrand_le hR0 hrad α hα hα1
  have hsqAK : Work.Spaces.HkSq α 6 (fun z θ => α * Work.Construction.AK α z θ) ≤ X2 := by
    rw [hX2def]
    exact Work.FTS.StrongPersist.AK6.hkSq_le_of_integrand_le6 hα hα1
      (by positivity) (by positivity) hpt
  have hid : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        = (α * Work.Spaces.qfun θ) * (α * Work.Construction.AK α z θ) := by
    intro z hz θ hθ
    rw [Dth_Fstar_eq hα z θ hθ,
      show z / (1 + z) * (α * Work.Spaces.qfun θ * Work.Construction.Fstar α z θ)
          = (α * Work.Spaces.qfun θ)
              * (z / (1 + z) * Work.Construction.Fstar α z θ) from by ring,
      zShift_Fstar_eq hα hα1 z hz θ hθ]
  refine ⟨hkMem_congr_Izθ (fun z hz θ hθ => (hid z hz θ hθ).symm) hmem, ?_⟩
  rw [hkNorm_congr_Izθ hid]
  have hnorm : Work.Spaces.HkNorm α 6
      (fun z θ => (fun θ => α * Work.Spaces.qfun θ) θ
        * (fun z θ => α * Work.Construction.AK α z θ) z θ) ≤ Real.sqrt (C₁ * Bq ^ 2 * X2) := by
    rw [Work.Spaces.HkNorm]
    refine Real.sqrt_le_sqrt ?_
    calc Work.Spaces.HkSq α 6 (fun z θ => (fun θ => α * Work.Spaces.qfun θ) θ
          * (fun z θ => α * Work.Construction.AK α z θ) z θ)
        ≤ C₁ * (α * Bq) ^ 2 * Work.Spaces.HkSq α 6
            (fun z θ => α * Work.Construction.AK α z θ) := hsq
      _ ≤ C₁ * (α * Bq) ^ 2 * X2 := mul_le_mul_of_nonneg_left hsqAK (by positivity)
      _ = C₁ * α ^ 2 * Bq ^ 2 * X2 := by ring
      _ ≤ 1 * (C₁ * Bq ^ 2 * X2) := by
          have h1 : α ^ 2 ≤ 1 := by nlinarith [hα, hα1]
          have h3 : (0 : ℝ) ≤ C₁ * Bq ^ 2 * X2 := by positivity
          calc C₁ * α ^ 2 * Bq ^ 2 * X2 = (C₁ * Bq ^ 2 * X2) * α ^ 2 := by ring
            _ ≤ (C₁ * Bq ^ 2 * X2) * 1 := mul_le_mul_of_nonneg_left h1 h3
            _ = 1 * (C₁ * Bq ^ 2 * X2) := by ring
      _ = C₁ * Bq ^ 2 * X2 := by ring
  linarith [hnorm, Real.sqrt_nonneg (C₁ * Bq ^ 2 * X2)]

end

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzSlot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The `ℋ⁶`-membership and norm bound of the `D_zF_*`-slot, given the `D_z`-jet bound of the
radial multiplier `z ↦ (1-z)/(1+z)`. -/
theorem starSlotC_aux {B : ℝ} (hB : 0 ≤ B)
    (hbnd : ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter k (fun y : ℝ => (1 - y) / (1 + y)) z| ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      Work.Spaces.HkMem α 6
          (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkNorm α 6
          (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ C := by
  obtain ⟨R, hR0, hrad⟩ := Work.FTS.StrongPersist.AK6.akRho_jet_bound6
  obtain ⟨K, _hKpos, hKmaj⟩ := radialBounded6_majorant
  obtain ⟨_CAK, _hCAK, hAKb⟩ := Work.FTS.StrongPersist.AK_Mem6
  set Kc : ℝ := K * B ^ 2 with hKcdef
  have hKc0 : 0 ≤ Kc := by rw [hKcdef]; positivity
  have hXsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 - z) / (1 + z)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_radial (fun n =>
      (contDiffOn_const.sub contDiffOn_id).div (contDiffOn_const.add contDiffOn_id)
        (fun z hz => by
          have hz' := hz; simp only [Set.mem_Ioi] at hz'; linarith))
  refine ⟨Real.sqrt (2 * (Kc * 700 * R * 10 ^ 4 + Kc * 49 * 10 ^ 12 * R * 700)) + 1,
    by positivity, ?_⟩
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨hAKmem, _⟩ := hAKb α hα hα1
  have hmemAK : Work.Spaces.HkMem α 6 (fun z θ => α * Work.Construction.AK α z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 α hAKmem
  have hSOAK : Work.FTS.EllipticEst.SmoothOpen (fun z θ => α * Work.Construction.AK α z θ) :=
    smoothOpen_alphaAK α
  -- the pointwise majorant on the open quadrant
  have hmaj : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 6
          (fun z θ => (1 - z) / (1 + z) * (α * Work.Construction.AK α z θ)) z θ
        ≤ Kc * Work.Spaces.HkIntegrand α 6
            (fun z θ => α * Work.Construction.AK α z θ) z θ := by
    intro z θ hz hθ0 hθ1
    have h := hKmaj α (fun z => (1 - z) / (1 + z))
      (fun z θ => α * Work.Construction.AK α z θ) B hXsm hSOAK hB hbnd z θ hz hθ0 hθ1
    rwa [hKcdef]
  -- extend it to the closed quadrant
  have hmaj' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6
          (fun z θ => (1 - z) / (1 + z) * (α * Work.Construction.AK α z θ)) z θ
        ≤ Kc * Work.Spaces.HkIntegrand α 6
            (fun z θ => α * Work.Construction.AK α z θ) z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0, Work.FTS.LocData.HkIntegrand_zero_fst α 6 _ θ,
        Work.FTS.LocData.HkIntegrand_zero_fst α 6 _ θ, mul_zero]
    · by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
      · have hθ1 : (0 : ℝ) < θ := hθi.1
        have hθ2 : θ < Real.pi / 2 := hθi.2
        exact hmaj z θ hzpos hθ1 hθ2
      · have hs : Real.sin (2 * θ) = 0 :=
          Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
        rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 6 _ z θ hs,
          Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 6 _ z θ hs, mul_zero]
  -- honesty
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6
      (fun z θ => (1 - z) / (1 + z) * (α * Work.Construction.AK α z θ)) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hXsm hSOAK).continuousOn_HkIntegrand α 6
  have hmemX : Work.Spaces.HkMem α 6
      (fun z θ => (1 - z) / (1 + z) * (α * Work.Construction.AK α z θ)) :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMemOfContMajorant α 6 hKc0 hcont hmemAK
      (fun z hz θ hθ => hmaj' z hz θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  -- the pointwise bound in the canonical shape
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6
          (fun z θ => (1 - z) / (1 + z) * (α * Work.Construction.AK α z θ)) z θ
        ≤ (1 / (1 + z) ^ 2) *
            (Kc * 700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + Kc * 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
    intro z hz θ hθ
    refine le_trans (hmaj' z hz θ hθ) ?_
    have h := alphaAK_integrand_le hR0 hrad α hα hα1 z hz θ hθ
    calc Kc * Work.Spaces.HkIntegrand α 6 (fun z θ => α * Work.Construction.AK α z θ) z θ
        ≤ Kc * ((1 / (1 + z) ^ 2) * (700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) :=
          mul_le_mul_of_nonneg_left h hKc0
      _ = (1 / (1 + z) ^ 2) * (Kc * (700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) := by ring
      _ = (1 / (1 + z) ^ 2) * (Kc * 700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + Kc * 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by ring
  have hsq := Work.FTS.StrongPersist.AK6.hkSq_le_of_integrand_le6 hα hα1
    (by positivity) (by positivity) hpt
  have hid := Dz_Fstar_eq (α := α)
  refine ⟨hkMem_congr_Izθ (fun z hz θ hθ => (hid z hz θ hθ).symm) hmemX, ?_⟩
  rw [hkNorm_congr_Izθ hid]
  have h1 : Work.Spaces.HkNorm α 6
      (fun z θ => (1 - z) / (1 + z) * (α * Work.Construction.AK α z θ))
      ≤ Real.sqrt (2 * (Kc * 700 * R * 10 ^ 4 + Kc * 49 * 10 ^ 12 * R * 700)) := by
    rw [Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt hsq
  linarith [h1,
    Real.sqrt_nonneg (2 * (Kc * 700 * R * 10 ^ 4 + Kc * 49 * 10 ^ 12 * R * 700))]

end

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
