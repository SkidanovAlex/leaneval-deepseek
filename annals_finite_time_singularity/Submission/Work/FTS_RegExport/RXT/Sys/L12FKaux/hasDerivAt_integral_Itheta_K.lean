import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.Blocks.DthIter_angular_mul_expand
import Submission.Work.FTS.EllipticEst.Blocks.LopIter_sin_two_le
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.ThetaSliceIdent
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Gegenbauer.odd_powers_complete_fixed
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.Blocks.HkMul_ang_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary smoothness and boundedness of the two angular profiles -/

private theorem contDiffAt_sin_two (θ : ℝ) :
    ContDiffAt ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) θ := by
  have hlin : ContDiff ℝ ⊤ (fun t : ℝ => 2 * t) := contDiff_const.mul contDiff_id
  have h : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) :=
    (Real.contDiff_sin (n := ⊤)).comp hlin
  exact h.contDiffAt

private theorem contDiffAt_sin_sq (θ : ℝ) :
    ContDiffAt ℝ ⊤ (fun θ : ℝ => Real.sin θ ^ 2) θ := by
  have h : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin θ ^ 2) := (Real.contDiff_sin (n := ⊤)).pow 2
  exact h.contDiffAt

private theorem abs_sin_two_le_one (θ : ℝ) : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _

private theorem abs_sin_sq_le_one (θ : ℝ) : |Real.sin θ ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  calc Real.sin θ ^ 2 = |Real.sin θ| ^ 2 := by rw [sq_abs]
    _ ≤ 1 := pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one θ)

/-! ## Multiplying by an angular profile preserves `SmoothOpen` -/

private theorem smoothOpen_angMul {a : ℝ → ℝ} (ha : ∀ θ : ℝ, ContDiffAt ℝ ⊤ a θ)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * f z θ) := by
  have haG : ContDiff ℝ ⊤ a := contDiff_iff_contDiffAt.mpr ha
  have haC : ContDiff ℝ Work.Stability.smoothOrder a := haG.of_le le_top
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      Work.FTS.EllipticEst.Q0 :=
    haC.contDiffOn.comp contDiffOn_snd (fun p _ => Set.mem_univ p.2)
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => a p.2 * f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    h1.mul hf
  exact h3

/-! ## The angular factor commutes with `D_z` -/

private theorem DzIter_angular_mul (i : ℕ) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => a θ * f z θ)
      = fun z θ => a θ * Work.Spaces.DzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      show z * deriv (fun z' => a θ * Work.Spaces.DzIter i f z' θ) z
          = a θ * (z * deriv (fun z' => Work.Spaces.DzIter i f z' θ) z)
      rw [deriv_const_mul_field (a θ)]
      ring

/-! ## The termwise bound for one Leibniz summand -/

private theorem angular_summand_sq_le_le (k : ℕ) (a : ℝ → ℝ) (K : ℕ → ℝ)
    (ha1 : ∀ θ : ℝ, |a θ| ≤ 1) (hK : ∀ m : ℕ, 0 ≤ K m)
    (hKb : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 ≤ K m * (Real.sin (2 * θ)) ^ 2) :
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (i j m : ℕ), α ≤ 1 → 1 ≤ i → i + j ≤ k → m ≤ i →
      ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
        ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
            * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by
  intro α f i j m hα1 hi1 hij hmi z θ hθ0 hθ1
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hHe : 0 ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hjk : j ≤ k := by omega
  have hmk : m ≤ k := by omega
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have ha2 : (a θ) ^ 2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg (a θ)) (ha1 θ) 2
      rwa [sq_abs, one_pow] at h
    have hmix := Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi1 hij
    have h0c : ((i.choose 0 : ℝ)) = 1 := by simp
    rw [h0c, Nat.sub_zero]
    simp only [Work.FTS.EllipticEst.LopIter_zero, Nat.cast_one, one_mul]
    calc (a θ * Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (a θ) ^ 2 * (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ 1 * Work.Spaces.HkIntegrand α k f z θ :=
          mul_le_mul ha2 hmix (sq_nonneg _) (by norm_num)
      _ ≤ 1 ^ 2 * (K 0 + 1) * Work.Spaces.HkIntegrand α k f z θ := by
          have h1 : (1 : ℝ) ≤ K 0 + 1 := by linarith [hK 0]
          calc (1 : ℝ) * Work.Spaces.HkIntegrand α k f z θ
              ≤ (K 0 + 1) * Work.Spaces.HkIntegrand α k f z θ :=
                mul_le_mul_of_nonneg_right h1 hHe
            _ = 1 ^ 2 * (K 0 + 1) * Work.Spaces.HkIntegrand α k f z θ := by ring
  · rcases Nat.lt_or_eq_of_le hmi with hlt | heq
    · -- 1 ≤ m < i, so 1 ≤ i - m
      have hpos' : 1 ≤ i - m := by omega
      have hd := hKb m hpos hmk θ hθIoo
      have h6 := Work.FTS.EllipticEst.Blocks.angular_sq_mul_Wt_sq_le
        (K := K m) (d := Work.FTS.EllipticEst.LopIter m a θ)
        (u := Work.Spaces.mixed j (i - m) f z θ) (α := α) (z := z) (θ := θ)
        (hK m) hθIoo hd
      have hmix := Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ (i - m) j hpos' (by omega)
      calc ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          = (i.choose m : ℝ) ^ 2 * ((Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2) := by ring
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * (Work.Spaces.mixed j (i - m) f z θ
              * Work.Spaces.Wt α z θ) ^ 2) := mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmix (hK m)) (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by
            have h1 : K m * Work.Spaces.HkIntegrand α k f z θ
                ≤ (K m + 1) * Work.Spaces.HkIntegrand α k f z θ :=
              mul_le_mul_of_nonneg_right (by linarith) hHe
            calc (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ)
                ≤ (i.choose m : ℝ) ^ 2 * ((K m + 1) * Work.Spaces.HkIntegrand α k f z θ) :=
                  mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
              _ = (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by ring
    · -- m = i, so i - m = 0
      have hz0 : i - m = 0 := by omega
      have hd := hKb m hpos hmk θ hθIoo
      have h7 := Work.FTS.EllipticEst.Blocks.angular_sq_mul_Wt_sq_le_radial
        (K := K m) (d := Work.FTS.EllipticEst.LopIter m a θ)
        (u := Work.Spaces.mixed j (i - m) f z θ) (α := α) (z := z) (θ := θ)
        hα1 (hK m) hθIoo hd
      rw [hz0, Work.Spaces.mixed_zero_right] at h7
      have hz' : (Work.Spaces.DzIter j f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α k f z θ j hjk
      rw [hz0, Work.Spaces.mixed_zero_right]
      calc ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.DzIter j f z θ * Work.Spaces.Wt α z θ) ^ 2
          = (i.choose m : ℝ) ^ 2 * ((Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2) := by ring
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * (Work.Spaces.DzIter j f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
            mul_le_mul_of_nonneg_left h7 (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz' (hK m)) (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by
            have h1 : K m * Work.Spaces.HkIntegrand α k f z θ
                ≤ (K m + 1) * Work.Spaces.HkIntegrand α k f z θ :=
              mul_le_mul_of_nonneg_right (by linarith) hHe
            calc (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ)
                ≤ (i.choose m : ℝ) ^ 2 * ((K m + 1) * Work.Spaces.HkIntegrand α k f z θ) :=
                  mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
              _ = (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by ring

/-! ## The generic estimate on the open quadrant -/

private theorem HkIntegrand_ang_mul_le_int (k : ℕ) (a : ℝ → ℝ) (K : ℕ → ℝ)
    (ha1 : ∀ θ : ℝ, |a θ| ≤ 1)
    (ha : ∀ θ : ℝ, ContDiffAt ℝ ⊤ a θ)
    (hK : ∀ m : ℕ, 0 ≤ K m)
    (hKb : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 ≤ K m * (Real.sin (2 * θ)) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ := by
  set KB : ℝ := ∑ m ∈ Finset.range (k + 1), (K m + 1) with hKBdef
  have hKBpos : 0 < KB := by
    rw [hKBdef]
    exact Finset.sum_pos (fun m _ => by linarith [hK m])
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
  have hKBnn : 0 ≤ KB := le_of_lt hKBpos
  set CB : ℝ := ((2 : ℝ) ^ k) ^ 2 with hCBdef
  have hCBnonneg : 0 ≤ CB := by rw [hCBdef]; positivity
  set Cpair : ℝ := ((k : ℝ) + 1) * CB * KB with hCpairdef
  have hCpairnonneg : 0 ≤ Cpair := by
    rw [hCpairdef]
    exact mul_nonneg (mul_nonneg (by positivity) hCBnonneg) hKBnn
  set C1 : ℝ := ((k : ℝ) + 1) ^ 2 * Cpair with hC1def
  have hC1nonneg : 0 ≤ C1 := by
    rw [hC1def]
    exact mul_nonneg (sq_nonneg _) hCpairnonneg
  refine ⟨((k : ℝ) + 1) + C1, by linarith, ?_⟩
  intro α f hα hα1 hf z θ hz hθ0 hθ1
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hHe : 0 ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZi : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [DzIter_angular_mul i a f]
      have ha2 : (a θ) ^ 2 ≤ 1 := by
        have h := pow_le_pow_left₀ (abs_nonneg (a θ)) (ha1 θ) 2
        rwa [sq_abs, one_pow] at h
      calc (a θ * Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (a θ) ^ 2 * (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
        _ ≤ 1 * (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
            mul_le_mul_of_nonneg_right ha2 (sq_nonneg _)
        _ = (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := one_mul _
        _ ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.sq_le_HkIntegrand_z α k f z θ i hik
    calc (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (k + 1), Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hMi : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ C1 * Work.Spaces.HkIntegrand α k f z θ := by
    have hpair : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
        (1 ≤ i ∧ i + j ≤ k) →
        (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Cpair * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi j hj hc
      obtain ⟨hi1, hij⟩ := hc
      have hik : i ≤ k := by omega
      have hjk : j ≤ k := by omega
      have hexp : Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ
          = ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ := by
        have hag : Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * f z θ) :=
          smoothOpen_angMul ha hf
        rw [← Work.FTS.EllipticEst.SmoothOpen.DthIter_DzIter_eq_mixed hag j i hz hθIoo]
        rw [DzIter_angular_mul j a f]
        rw [Work.FTS.EllipticEst.Blocks.DthIter_angular_mul_expand ha hf i j hz hθIoo]
        exact Finset.sum_congr rfl fun m _ => by
          rw [Work.FTS.EllipticEst.SmoothOpen.DthIter_DzIter_eq_mixed hf j (i - m) hz hθIoo]
      rw [hexp]
      have hstep : (∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ) * Work.Spaces.Wt α z θ
          = ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) := by
        rw [Finset.sum_mul]
      rw [hstep]
      have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
        (f := fun m => (i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
          * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ)
      have hbound : ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
            * Work.FTS.EllipticEst.LopIter m a θ
            * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ CB * KB * Work.Spaces.HkIntegrand α k f z θ := by
        have hchoose : ∀ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 ≤ CB := by
          intro m hm
          have h1 : (i.choose m : ℝ) ≤ (2 : ℝ) ^ k := by
            have h2 : i.choose m ≤ 2 ^ k := le_trans (Nat.choose_le_two_pow i m)
              (Nat.pow_le_pow_right (by norm_num) hik)
            exact_mod_cast h2
          calc (i.choose m : ℝ) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
            _ = CB := by rw [hCBdef]
        have hsumKB : ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
            ≤ CB * KB := by
          have hstep1 : ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
              ≤ ∑ m ∈ Finset.range (i + 1), CB * (K m + 1) := by
            refine Finset.sum_le_sum fun m hm => ?_
            exact mul_le_mul_of_nonneg_right (hchoose m hm) (by linarith [hK m])
          have hstep2 : ∑ m ∈ Finset.range (i + 1), CB * (K m + 1)
              = CB * ∑ m ∈ Finset.range (i + 1), (K m + 1) := by
            rw [Finset.mul_sum]
          have hstep3 : ∑ m ∈ Finset.range (i + 1), (K m + 1) ≤ KB := by
            rw [hKBdef]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro m hm
              simp only [Finset.mem_range] at hm ⊢
              omega
            · intro m _ _
              linarith [hK m]
          calc _ ≤ ∑ m ∈ Finset.range (i + 1), CB * (K m + 1) := hstep1
            _ = CB * ∑ m ∈ Finset.range (i + 1), (K m + 1) := hstep2
            _ ≤ CB * KB := mul_le_mul_of_nonneg_left hstep3 hCBnonneg
        calc ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
                * Work.Spaces.HkIntegrand α k f z θ := by
              refine Finset.sum_le_sum fun m hm => ?_
              have hmi : m ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
              exact angular_summand_sq_le_le k a K ha1 hK hKb α f i j m hα1 hi1 hij hmi
                z θ hθ0 hθ1
          _ = Work.Spaces.HkIntegrand α k f z θ
                * ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun m _ => by ring
          _ ≤ Work.Spaces.HkIntegrand α k f z θ * (CB * KB) :=
              mul_le_mul_of_nonneg_left hsumKB hHe
          _ = CB * KB * Work.Spaces.HkIntegrand α k f z θ := by ring
      have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
        rw [Finset.card_range]
        push_cast
        ring
      have hCBKBnn : 0 ≤ CB * KB * Work.Spaces.HkIntegrand α k f z θ :=
        mul_nonneg (mul_nonneg hCBnonneg hKBnn) hHe
      calc (∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) * ∑ m ∈ Finset.range (i + 1),
              ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
                * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2 := hcs
        _ ≤ (((i : ℝ) + 1)) * (CB * KB * Work.Spaces.HkIntegrand α k f z θ) := by
            rw [hcard]
            exact mul_le_mul_of_nonneg_left hbound (by positivity)
        _ ≤ ((k : ℝ) + 1) * (CB * KB * Work.Spaces.HkIntegrand α k f z θ) := by
            refine mul_le_mul_of_nonneg_right ?_ hCBKBnn
            have : (i : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hik
            linarith
        _ = Cpair * Work.Spaces.HkIntegrand α k f z θ := by
            rw [hCpairdef]
            ring
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
            Cpair * Work.Spaces.HkIntegrand α k f z θ := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc]
            exact hpair i hi j hj hc
          · rw [if_neg hc]
            exact mul_nonneg hCpairnonneg hHe
      _ = C1 * Work.Spaces.HkIntegrand α k f z θ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [hC1def]
          push_cast
          ring
  rw [Work.Spaces.HkIntegrand]
  refine le_trans (add_le_add hZi hMi) (le_of_eq ?_)
  ring

/-! ## Extension to the closed quadrant -/

/-- The pointwise inequality, known on the *open* quadrant, extends to the closed quadrant
`Iz ×ˢ Iθ`: on the two boundary lines `z = 0` and `sin(2θ) = 0` both `ℋ^k`-integrands
vanish (`HkIntegrand_zero_fst`, `HkIntegrand_eq_zero_of_sin_eq_zero`). -/
private theorem closed_of_interior {k : ℕ} {a : ℝ → ℝ} {C : ℝ}
    (hint : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) :
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ := by
  intro α f hα hα1 hf z hz θ hθ
  have hzge : (0 : ℝ) ≤ z := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
  have hθb : (0 : ℝ) ≤ θ ∧ θ ≤ Real.pi / 2 := by
    simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
  rcases eq_or_lt_of_le hzge with h0 | hpos
  · rw [← h0, Work.FTS.LocData.HkIntegrand_zero_fst α k (fun z θ => a θ * f z θ) θ,
      Work.FTS.LocData.HkIntegrand_zero_fst α k f θ, mul_zero]
  · by_cases hs : Real.sin (2 * θ) = 0
    · rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k (fun z θ => a θ * f z θ) z θ hs,
        Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k f z θ hs, mul_zero]
    · have hθ1 : 0 < θ := by
        rcases eq_or_lt_of_le hθb.1 with h | h
        · exact absurd (by rw [← h]; simp) hs
        · exact h
      have hθ2 : θ < Real.pi / 2 := by
        rcases lt_or_eq_of_le hθb.2 with h | h
        · exact h
        · exact absurd (by rw [h, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring,
            Real.sin_pi]) hs
      exact hint α f hα hα1 hf z θ hpos hθ1 hθ2

/-! ## The pointwise inequality on the closed quadrant, for the two profiles -/

private theorem HkIntegrand_mul_ang_le_pt (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin (2 * θ) * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) ∧
      (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin θ ^ 2 * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) := by
  obtain ⟨K2, hK2nn, hK2b⟩ := Work.FTS.EllipticEst.Blocks.LopIter_sin_two_le k
  obtain ⟨K3, hK3nn, hK3b⟩ := Work.FTS.EllipticEst.Blocks.LopIter_sin_sq_le k
  obtain ⟨C2, hC2pos, hC2int⟩ := HkIntegrand_ang_mul_le_int k (fun θ => Real.sin (2 * θ))
    (fun _ => K2) abs_sin_two_le_one contDiffAt_sin_two (fun _ => hK2nn)
    (fun m _ hmk θ hθ => hK2b m hmk θ hθ)
  obtain ⟨C3, hC3pos, hC3int⟩ := HkIntegrand_ang_mul_le_int k (fun θ => Real.sin θ ^ 2)
    (fun _ => K3) abs_sin_sq_le_one contDiffAt_sin_sq (fun _ => hK3nn)
    (fun m hm1 hmk θ hθ => by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact hK3b m' (by omega) θ hθ)
  refine ⟨max C2 C3, lt_max_of_lt_left hC2pos, ?_⟩
  intro α f hα hα1 hf
  constructor
  · refine closed_of_interior (k := k) (a := fun θ => Real.sin (2 * θ)) (C := max C2 C3)
      (fun α f hα hα1 hf z θ hz hθ0 hθ1 => le_trans (hC2int α f hα hα1 hf z θ hz hθ0 hθ1)
        (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Work.Spaces.HkIntegrand_nonneg α k f z θ))) α f hα hα1 hf
  · refine closed_of_interior (k := k) (a := fun θ => Real.sin θ ^ 2) (C := max C2 C3)
      (fun α f hα hα1 hf z θ hz hθ0 hθ1 => le_trans (hC3int α f hα hα1 hf z θ hz hθ0 hθ1)
        (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Work.Spaces.HkIntegrand_nonneg α k f z θ))) α f hα hα1 hf

/-! ## Transfer of `HkMem` and `HkSq` along a pointwise domination of the integrand -/

private theorem HkSq_le_of_integrand_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} (C : ℝ)
    (hmf : Work.Spaces.HkMem α k f)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k g z θ ≤ C * Work.Spaces.HkIntegrand α k f z θ) :
    Work.Spaces.HkSq α k g ≤ C * Work.Spaces.HkSq α k f := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k f z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => Work.Spaces.HkIntegrand α k g z θ)
        (g := fun θ => C * Work.Spaces.HkIntegrand α k f z θ)
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
        ((hmf.1 z hz).const_mul C)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpt z hz θ hθ)
    rwa [MeasureTheory.integral_const_mul] at h1
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have h2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g z θ)
      ≤ ∫ z in Work.Spaces.Iz, C * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      (g := fun z => C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ))
      (Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
      (hmf.2.const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  rwa [MeasureTheory.integral_const_mul] at h2

private theorem HkMem_of_integrand_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} (C : ℝ)
    (hcontg : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmf : Work.Spaces.HkMem α k f)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k g z θ ≤ C * Work.Spaces.HkIntegrand α k f z θ) :
    Work.Spaces.HkMem α k g :=
  Work.FTS.LocData.HkMem_of_majorant α k hcontg
    (fun z hz => (hmf.1 z hz).const_mul C)
    (by
      have h := hmf.2.const_mul C
      have hkey : (fun z => ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k f z θ)
          = fun z => C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
        funext z
        rw [MeasureTheory.integral_const_mul]
      rw [hkey]
      exact h)
    hpt

/-
**Bounded angular profiles do not increase the weighted `ℋ^k`-integrand.**

Namespace `Work.FTS.EllipticEst.Blocks` (fully qualified name
`Work.FTS.EllipticEst.Blocks.HkMul_ang_le`).

CONTENT.  For `f` `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)`
(`Work.FTS.EllipticEst.SmoothOpen f`) and every `α ∈ (0,1]`, the two profiles
`a θ = sin 2θ` and `a θ = sin²θ` satisfy, pointwise on the whole closed quadrant,

  `HkIntegrand α k (a · f) ≤ C_k · HkIntegrand α k f`,

and consequently (with `HkMem` of `f` as the honesty hypothesis)
`HkMem α k (a · f)` and `HkSq α k (a·f) ≤ C_k · HkSq α k f`.

The constant depends only on `k`, never on `α ∈ (0,1]`.

ROUTE (verified by a reviewer).  `D_z` and `D_θ` commute with the `θ`-only factor `a`, so the
pure-`D_z` summands satisfy `D_z^i(a·f) = a·(D_z^if)` exactly and `|a| ≤ 1` gives those terms.
For the mixed summands, the iterated Leibniz rule for the derivation `L = D_θ = sin(2θ)∂_θ`
(`Work.FTS.EllipticEst.Lop_iter_mul`, sorry-free: `L^i(f·g) = Σ_{m≤i} C(i,m)(L^mf)(L^{i-m}g)`)
expands `D_θ^i(D_z^j(a f)) = Σ_{m ≤ i} C(i,m) (D_θ^m a)(D_θ^{i-m}D_z^j f)`.  Every term with
`m < i` is a summand of `HkIntegrand α k f` (at the mixed index `i-m ≥ 1`, same `j`) after
using `sin(2θ)² ≤ 1` and the boundedness of `D_θ^m a`; the term `m = i` is the `D_z`-family
summand `(D_z^j f)²·w²·sin(2θ)^{-γ}` times `(D_θ^i a)²`, and one needs
`(D_θ^i a)² · sin(2θ)^{-γ} ≤ C_i`, i.e. `sin(2θ)^{2-γ} ≤ C_i`.  For `a = sin 2θ` this is the
(sorry-free) weighted angular iterate bound `Work.FTS.EllipticEst.sinIter_weight_bound`
(`D_θ^i(sin 2θ) = sinIter i`); for `a = sin²θ` it is
`Work.FTS.EllipticEst.Blocks.LopIter_sin_sq_le` (sorry-free, `(D_θ^m(sin²θ))² ≤ K·sin(2θ)²`
for `m ≥ 1`).  Again `2 - γ ≥ -η` because `γ = 1 + α/10 ≤ 11/10` and `η = 99/100`, so the
weights with exponent `-γ` are dominated by those with `-η`; the exponent `2-γ` is positive, so
`sin(2θ)^{2-γ} ≤ 1 ≤ sin(2θ)^{-η}` too.

At the two boundary lines `sin(2θ) = 0` and at `z = 0` both sides of the pointwise inequality
vanish (`HkIntegrand_eq_zero_of_sin` / `w 0 = 0`; the same computation as the private lemmas of
`Submission/Work/FTS/EllipticEst/HkNorm_add_le.lean`), so the pointwise inequality extends to
the closed quadrant `Iz ×ˢ Iθ`.

The `HkMem`/`HkSq` consequences follow from the pointwise inequality on the closed quadrant by
`MeasureTheory.integral_mono_of_nonneg` slice by slice (`HkMem f` makes the dominating slice
integrable), then again in `z`; this is the pattern of
`Work.FTS.EllipticEst.HkSq_add_le_of_pointwise`
(`Submission/Work/FTS/EllipticEst/HkNorm_add_le.lean`, sorry-free).

NOTE: this strictly extends the (still `sorry`) sibling
`Submission/Work/FTS/EllipticEst/Blocks/HkIntegrand_mul_angular_le.lean`, which you may read and
port but must not import (it is not sorry-free).  The hypotheses `0 < α`, `α ≤ 1` are exactly
what the `γ`-weight comparison needs.
-/
theorem HkMul_ang_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin (2 * θ) * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) ∧
      (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin θ ^ 2 * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) ∧
      (Work.Spaces.HkMem α k f →
        Work.Spaces.HkMem α k (fun z θ => Real.sin (2 * θ) * f z θ) ∧
        Work.Spaces.HkSq α k (fun z θ => Real.sin (2 * θ) * f z θ)
          ≤ C * Work.Spaces.HkSq α k f ∧
        Work.Spaces.HkMem α k (fun z θ => Real.sin θ ^ 2 * f z θ) ∧
        Work.Spaces.HkSq α k (fun z θ => Real.sin θ ^ 2 * f z θ)
          ≤ C * Work.Spaces.HkSq α k f) := by
  obtain ⟨C, hCpos, hpt⟩ := HkIntegrand_mul_ang_le_pt k
  refine ⟨C, hCpos, ?_⟩
  intro α f hα hα1 hf
  obtain ⟨hpt2, hpt3⟩ := hpt α f hα hα1 hf
  refine ⟨hpt2, hpt3, ?_⟩
  intro hmem
  have hSO2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.sin (2 * θ) * f z θ) :=
    smoothOpen_angMul contDiffAt_sin_two hf
  have hSO3 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.sin θ ^ 2 * f z θ) :=
    smoothOpen_angMul contDiffAt_sin_sq hf
  have hc2 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α k (fun z θ => Real.sin (2 * θ) * f z θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand hSO2 α k
  have hc3 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α k (fun z θ => Real.sin θ ^ 2 * f z θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand hSO3 α k
  exact ⟨HkMem_of_integrand_le α k C hc2 hmem hpt2,
    HkSq_le_of_integrand_le α k C hmem hpt2,
    HkMem_of_integrand_le α k C hc3 hmem hpt3,
    HkSq_le_of_integrand_le α k C hmem hpt3⟩

end Work.Blocks

namespace Work.FTS.EllipticEst.Blocks

/-- Compatibility alias of `Work.Blocks.HkMul_ang_le` under the fully qualified name quoted by
the consumers of the elliptic-estimates chapter (the assembly of
`Work.FTS.EllipticEst.Rop_EllResid_le` refers to this statement as
`Work.FTS.EllipticEst.Blocks.HkMul_ang_le`). -/
theorem HkMul_ang_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin (2 * θ) * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) ∧
      (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin θ ^ 2 * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) ∧
      (Work.Spaces.HkMem α k f →
        Work.Spaces.HkMem α k (fun z θ => Real.sin (2 * θ) * f z θ) ∧
        Work.Spaces.HkSq α k (fun z θ => Real.sin (2 * θ) * f z θ)
          ≤ C * Work.Spaces.HkSq α k f ∧
        Work.Spaces.HkMem α k (fun z θ => Real.sin θ ^ 2 * f z θ) ∧
        Work.Spaces.HkSq α k (fun z θ => Real.sin θ ^ 2 * f z θ)
          ≤ C * Work.Spaces.HkSq α k f) :=
  Work.Blocks.HkMul_ang_le k

end Work.FTS.EllipticEst.Blocks
end
end
-- ===== merged: Submission.Work.EllipticEst.Assembly.PairAuxBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Assembly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Iterated `θ`-derivatives of a function smooth on the open quadrant -/

theorem smoothOpen_pthIter {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (i : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- Multiplication by `tan θ` preserves smoothness on the open quadrant. -/
theorem smoothOpen_tan_mul {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * F z θ) := by
  have htan : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.tan p.2)
      Work.FTS.EllipticEst.Q0 := by
    rw [show (fun p : ℝ × ℝ => Real.tan p.2)
        = fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2 from
      funext fun p => Real.tan_eq_sin_div_cos p.2]
    refine ContDiffOn.div ((Real.contDiff_sin.comp contDiff_snd).contDiffOn)
      ((Real.contDiff_cos.comp contDiff_snd).contDiffOn) (fun p hp => ?_)
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      by linarith [Real.pi_pos]⟩)
  exact htan.mul hF

/-! ## Slice derivatives of a function smooth on the open quadrant -/

theorem hasDerivAt_slice_θ {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' => F z θ') (Work.Spaces.pth F z θ) θ :=
  (((hF.curry_θ hz).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioo.mem_nhds hθ)).hasDerivAt

theorem hasDerivAt_slice_pth {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' => Work.Spaces.pth F z θ') (Work.Spaces.pthIter 2 F z θ) θ := by
  have h := hasDerivAt_slice_θ hF.pth hz hθ
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h

theorem hasDerivAt_slice_z {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun z' => F z' θ) (Work.Spaces.pz F z θ) z :=
  hF.hasDerivAt_slice hθ hz

theorem hasDerivAt_slice_pz {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun z' => Work.Spaces.pz F z' θ) (Work.Spaces.pzIter 2 F z θ) z := by
  have h := hF.hasDerivAt_slice_pzIter 1 hθ hz
  simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h

/-! ## The bridge from the Fréchet derivative of a plane function to its slice derivatives -/

theorem fderiv_fst_eq_deriv {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (h : DifferentiableAt ℝ f x) :
    deriv (fun z : ℝ => f (z, x.2)) x.1 = (fderiv ℝ f x) (1, 0) := by
  have hc : HasDerivAt (fun z : ℝ => ((z, x.2) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) x.1 :=
    (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
  have hcomp : HasDerivAt (fun z : ℝ => f (z, x.2))
      ((fderiv ℝ f x) ((1, 0) : ℝ × ℝ)) x.1 := by
    have hh := h.hasFDerivAt.comp_hasDerivAt x.1 hc
    simpa only [Function.comp_def] using hh
  exact hcomp.deriv

theorem fderiv_snd_eq_deriv {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (h : DifferentiableAt ℝ f x) :
    deriv (fun θ : ℝ => f (x.1, θ)) x.2 = (fderiv ℝ f x) (0, 1) := by
  have hc : HasDerivAt (fun θ : ℝ => ((x.1, θ) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) x.2 :=
    (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
  have hcomp : HasDerivAt (fun θ : ℝ => f (x.1, θ))
      ((fderiv ℝ f x) ((0, 1) : ℝ × ℝ)) x.2 := by
    have hh := h.hasFDerivAt.comp_hasDerivAt x.2 hc
    simpa only [Function.comp_def] using hh
  exact hcomp.deriv

/-! ## Vanishing on the complement of the (topological) support -/

/-- Off the topological support of `g`, the function is locally zero on a *product* of open
sets, so that also its slices (and the slices of its slices) are locally zero. -/
theorem exists_isOpen_local_zero_of_notMem_tsupport {g : ℝ → ℝ → ℝ} {x : ℝ × ℝ}
    (hx : x ∉ tsupport (Function.uncurry g)) :
    ∃ U V : Set ℝ, IsOpen U ∧ IsOpen V ∧ x.1 ∈ U ∧ x.2 ∈ V ∧
      ∀ z ∈ U, ∀ θ ∈ V, g z θ = 0 := by
  have hs : (tsupport (Function.uncurry g))ᶜ ∈ 𝓝 x :=
    (isClosed_tsupport _).isOpen_compl.mem_nhds hx
  have hs' : (tsupport (Function.uncurry g))ᶜ ∈ 𝓝 x.1 ×ˢ 𝓝 x.2 := by
    rw [nhds_prod_eq] at hs; exact hs
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hs'
  obtain ⟨U', hU'sub, hU'open, hxU'⟩ := mem_nhds_iff.mp hU
  obtain ⟨V', hV'sub, hV'open, hxV'⟩ := mem_nhds_iff.mp hV
  refine ⟨U', V', hU'open, hV'open, hxU', hxV', fun z hz θ hθ => ?_⟩
  by_contra hne
  have hmem : (z, θ) ∈ Function.support (Function.uncurry g) := Function.mem_support.mpr hne
  exact (hUV ⟨hU'sub hz, hV'sub hθ⟩) (subset_tsupport _ hmem)

/-- `bslOp α ψ` vanishes off the topological support of `ψ` (all of its derivatives -- plain,
iterated and the `tan θ·ψ` combination -- are derivatives of a locally vanishing function). -/
theorem bslOp_eq_zero_off_tsupport {α : ℝ} {ψ : ℝ → ℝ → ℝ} {x : ℝ × ℝ}
    (hx : x ∉ tsupport (Function.uncurry ψ)) : Work.Elliptic.bslOp α ψ x.1 x.2 = 0 := by
  obtain ⟨U, V, hUopen, hVopen, hxU, hxV, hzero⟩ :=
    exists_isOpen_local_zero_of_notMem_tsupport hx
  have hUmem : U ∈ 𝓝 x.1 := hUopen.mem_nhds hxU
  have hVmem : V ∈ 𝓝 x.2 := hVopen.mem_nhds hxV
  have hzslice : ∀ z ∈ U, ∀ θ ∈ V, (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 z] (fun z' => ψ z' θ) := by
    intro z hz θ hθ
    filter_upwards [hUopen.mem_nhds hz] with z' hz'
    exact (hzero z' hz' θ hθ).symm
  have htslice : ∀ z ∈ U, ∀ θ ∈ V, (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 θ] (fun θ' => ψ z θ') := by
    intro z hz θ hθ
    filter_upwards [hVopen.mem_nhds hθ] with θ' hθ'
    exact (hzero z hz θ' hθ').symm
  have h0 : ψ x.1 x.2 = 0 := hzero x.1 hxU x.2 hxV
  have hpz : Work.Spaces.pz ψ x.1 x.2 = 0 :=
    ((hzslice x.1 hxU x.2 hxV).deriv_eq).symm.trans (deriv_const x.1 0)
  have hpz' : ∀ z ∈ U, ∀ θ ∈ V, Work.Spaces.pz ψ z θ = 0 := by
    intro z hz θ hθ
    exact ((hzslice z hz θ hθ).deriv_eq).symm.trans (deriv_const z 0)
  have hpth' : ∀ z ∈ U, ∀ θ ∈ V, Work.Spaces.pth ψ z θ = 0 := by
    intro z hz θ hθ
    exact ((htslice z hz θ hθ).deriv_eq).symm.trans (deriv_const θ 0)
  have hpz2 : Work.Spaces.pzIter 2 ψ x.1 x.2 = 0 := by
    have hs : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x.1] (fun z => Work.Spaces.pz ψ z x.2) := by
      filter_upwards [hUmem] with z hz
      exact (hpz' z hz x.2 hxV).symm
    exact ((hs.deriv_eq).symm.trans (deriv_const x.1 0))
  have hpth2 : Work.Spaces.pthIter 2 ψ x.1 x.2 = 0 := by
    have hs : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x.2] (fun θ => Work.Spaces.pth ψ x.1 θ) := by
      filter_upwards [hVmem] with θ hθ
      exact (hpth' x.1 hxU θ hθ).symm
    exact ((hs.deriv_eq).symm.trans (deriv_const x.2 0))
  have htan : Work.Spaces.pth (fun z θ' => Real.tan θ' * ψ z θ') x.1 x.2 = 0 := by
    have hs : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x.2] (fun θ => Real.tan θ * ψ x.1 θ) := by
      filter_upwards [hVmem] with θ hθ
      rw [hzero x.1 hxU θ hθ, mul_zero]
    exact ((hs.deriv_eq).symm.trans (deriv_const x.2 0))
  rw [Work.Elliptic.bslOp_apply]
  simp only [Work.Elliptic.Lzero]
  rw [hpz2, hpz, hpth2, htan, h0]
  ring

/-! ## Continuity of `bslOp` on the open quadrant -/

theorem continuousOn_bslOp_smoothOpen {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ContinuousOn (fun x : ℝ × ℝ => Work.Elliptic.bslOp α F x.1 x.2)
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun x : ℝ × ℝ => Work.Spaces.pzIter 2 F x.1 x.2)
      Work.FTS.EllipticEst.Q0 := (hF.pzIter 2).continuousOn
  have h2 : ContinuousOn (fun x : ℝ × ℝ => Work.Spaces.pz F x.1 x.2)
      Work.FTS.EllipticEst.Q0 := hF.pz.continuousOn
  have h3 : ContinuousOn (fun x : ℝ × ℝ => Work.Spaces.pthIter 2 F x.1 x.2)
      Work.FTS.EllipticEst.Q0 := (smoothOpen_pthIter hF 2).continuousOn
  have h4 : ContinuousOn (fun x : ℝ × ℝ => Work.Spaces.pth
      (fun z θ' => Real.tan θ' * F z θ') x.1 x.2) Work.FTS.EllipticEst.Q0 :=
    ((smoothOpen_tan_mul hF).pth).continuousOn
  have h5 : ContinuousOn (fun x : ℝ × ℝ => F x.1 x.2) Work.FTS.EllipticEst.Q0 :=
    hF.continuousOn
  have hc1 : ContinuousOn (fun x : ℝ × ℝ => -(α ^ 2 * x.1 ^ 2))
      Work.FTS.EllipticEst.Q0 := by fun_prop
  have hc2 : ContinuousOn (fun x : ℝ × ℝ => α * (5 + α) * x.1)
      Work.FTS.EllipticEst.Q0 := by fun_prop
  have hc3 : ContinuousOn (fun _ : ℝ × ℝ => (6 : ℝ)) Work.FTS.EllipticEst.Q0 :=
    continuousOn_const
  have hsum : ContinuousOn (fun x : ℝ × ℝ =>
      -(α ^ 2 * x.1 ^ 2) * Work.Spaces.pzIter 2 F x.1 x.2
        - (α * (5 + α) * x.1) * Work.Spaces.pz F x.1 x.2
        + (-(Work.Spaces.pthIter 2 F x.1 x.2)
            + Work.Spaces.pth (fun z θ' => Real.tan θ' * F z θ') x.1 x.2
            - 6 * F x.1 x.2)) Work.FTS.EllipticEst.Q0 :=
    ((hc1.mul h1).sub (hc2.mul h2)).add ((h3.neg.add h4).sub (hc3.mul h5))
  simpa only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] using hsum

theorem continuousOn_pairWeight (α : ℝ) :
    ContinuousOn (pairWeight α) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun x : ℝ × ℝ => x.1 ^ pairBeta α) Work.FTS.EllipticEst.Q0 :=
    continuous_fst.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hx).1))
  have h2 : ContinuousOn (fun x : ℝ × ℝ => Real.cos x.2) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_cos.comp continuous_snd).continuousOn
  change ContinuousOn (fun x : ℝ × ℝ => x.1 ^ pairBeta α * Real.cos x.2)
      Work.FTS.EllipticEst.Q0
  exact h1.mul h2

end Work.EllipticEst.Assembly
end
end
-- ===== merged: Submission.Work.EllipticEst.Assembly.PairAuxDiv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Assembly

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem pairDivIdentityAux {α : ℝ} (hα : 0 < α) {Φ φ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hΦz : HasDerivAt (fun z' => Φ z' θ) (Work.Spaces.pz Φ z θ) z)
    (hΦzz : HasDerivAt (fun z' => Work.Spaces.pz Φ z' θ) (Work.Spaces.pzIter 2 Φ z θ) z)
    (hφz : HasDerivAt (fun z' => φ z' θ) (Work.Spaces.pz φ z θ) z)
    (hφzz : HasDerivAt (fun z' => Work.Spaces.pz φ z' θ) (Work.Spaces.pzIter 2 φ z θ) z)
    (hΦt : HasDerivAt (fun θ' => Φ z θ') (Work.Spaces.pth Φ z θ) θ)
    (hΦtt : HasDerivAt (fun θ' => Work.Spaces.pth Φ z θ') (Work.Spaces.pthIter 2 Φ z θ) θ)
    (hφt : HasDerivAt (fun θ' => φ z θ') (Work.Spaces.pth φ z θ) θ)
    (hφtt : HasDerivAt (fun θ' => Work.Spaces.pth φ z θ') (Work.Spaces.pthIter 2 φ z θ) θ) :
    Work.EllipticEst.Assembly.pairWeight α (z, θ)
        * (Work.Elliptic.bslOp α Φ z θ * φ z θ - Φ z θ * Work.Elliptic.bslOp α φ z θ)
      = deriv (fun z' => Work.EllipticEst.Assembly.pairRad α Φ φ (z', θ)) z
        + deriv (fun θ' => Work.EllipticEst.Assembly.pairAng α Φ φ (z, θ')) θ := by
  have hcos : Real.cos θ ≠ 0 := by
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · linarith [Real.pi_pos, hθ.1]
    · linarith [Real.pi_pos, hθ.2]
  -- ### the derivative in `z`
  have hz1 : HasDerivAt (fun z' : ℝ => z' ^ (pairBeta α + 2))
      ((pairBeta α + 2) * z ^ (pairBeta α + 2 - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hz))
  have hz2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz φ z' θ * Φ z' θ
      - Work.Spaces.pz Φ z' θ * φ z' θ)
      ((Work.Spaces.pzIter 2 φ z θ * Φ z θ + Work.Spaces.pz φ z θ * Work.Spaces.pz Φ z θ)
        - (Work.Spaces.pzIter 2 Φ z θ * φ z θ
            + Work.Spaces.pz Φ z θ * Work.Spaces.pz φ z θ)) z :=
    (hφzz.mul hΦz).sub (hΦzz.mul hφz)
  have hz3 : HasDerivAt (fun z' : ℝ => Work.EllipticEst.Assembly.pairRad α Φ φ (z', θ))
      (α ^ 2 * (pairBeta α + 2) * z ^ (pairBeta α + 2 - 1) * Real.cos θ
          * (Work.Spaces.pz φ z θ * Φ z θ - Work.Spaces.pz Φ z θ * φ z θ)
        + (α ^ 2 * z ^ (pairBeta α + 2) * Real.cos θ)
          * ((Work.Spaces.pzIter 2 φ z θ * Φ z θ
                + Work.Spaces.pz φ z θ * Work.Spaces.pz Φ z θ)
            - (Work.Spaces.pzIter 2 Φ z θ * φ z θ
                + Work.Spaces.pz Φ z θ * Work.Spaces.pz φ z θ))) z :=
    (((hz1.const_mul (α ^ 2)).mul (hasDerivAt_const z (Real.cos θ))).mul hz2).congr_deriv (by
      simp only [Pi.mul_apply]
      ring)
  -- ### the derivative in `θ`
  have ht1 : HasDerivAt (fun θ' : ℝ => Real.cos θ') (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have ht2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.pth φ z θ' * Φ z θ'
      - Work.Spaces.pth Φ z θ' * φ z θ')
      ((Work.Spaces.pthIter 2 φ z θ * Φ z θ + Work.Spaces.pth φ z θ * Work.Spaces.pth Φ z θ)
        - (Work.Spaces.pthIter 2 Φ z θ * φ z θ
            + Work.Spaces.pth Φ z θ * Work.Spaces.pth φ z θ)) θ :=
    (hφtt.mul hΦt).sub (hΦtt.mul hφt)
  have ht3 : HasDerivAt (fun θ' : ℝ => Work.EllipticEst.Assembly.pairAng α Φ φ (z, θ'))
      (z ^ pairBeta α * (-Real.sin θ)
          * (Work.Spaces.pth φ z θ * Φ z θ - Work.Spaces.pth Φ z θ * φ z θ)
        + (z ^ pairBeta α * Real.cos θ)
          * ((Work.Spaces.pthIter 2 φ z θ * Φ z θ
                + Work.Spaces.pth φ z θ * Work.Spaces.pth Φ z θ)
            - (Work.Spaces.pthIter 2 Φ z θ * φ z θ
                + Work.Spaces.pth Φ z θ * Work.Spaces.pth φ z θ))) θ :=
    (((hasDerivAt_const θ (z ^ pairBeta α)).mul ht1).mul ht2).congr_deriv (by
      simp only [Pi.mul_apply]
      ring)
  -- ### the two `pth (tan · ·)` terms
  have htanΦ : Work.Spaces.pth (fun z θ' => Real.tan θ' * Φ z θ') z θ
      = (1 / Real.cos θ ^ 2) * Φ z θ + Real.tan θ * Work.Spaces.pth Φ z θ := by
    have h5 : HasDerivAt (fun θ' : ℝ => Real.tan θ' * Φ z θ')
        ((1 / Real.cos θ ^ 2) * Φ z θ + Real.tan θ * Work.Spaces.pth Φ z θ) θ :=
      ((Real.hasDerivAt_tan hcos).mul hΦt).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun θ' => rfl))
    simpa only [Work.Spaces.pth] using h5.deriv
  have htanφ : Work.Spaces.pth (fun z θ' => Real.tan θ' * φ z θ') z θ
      = (1 / Real.cos θ ^ 2) * φ z θ + Real.tan θ * Work.Spaces.pth φ z θ := by
    have h5 : HasDerivAt (fun θ' : ℝ => Real.tan θ' * φ z θ')
        ((1 / Real.cos θ ^ 2) * φ z θ + Real.tan θ * Work.Spaces.pth φ z θ) θ :=
      ((Real.hasDerivAt_tan hcos).mul hφt).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun θ' => rfl))
    simpa only [Work.Spaces.pth] using h5.deriv
  have hLΦ : Work.Elliptic.bslOp α Φ z θ
      = -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Φ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz Φ z θ
        + (-(Work.Spaces.pthIter 2 Φ z θ)
            + ((1 / Real.cos θ ^ 2) * Φ z θ + Real.tan θ * Work.Spaces.pth Φ z θ)
            - 6 * Φ z θ) := by
    simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, htanΦ]
  have hLφ : Work.Elliptic.bslOp α φ z θ
      = -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 φ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz φ z θ
        + (-(Work.Spaces.pthIter 2 φ z θ)
            + ((1 / Real.cos θ ^ 2) * φ z θ + Real.tan θ * Work.Spaces.pth φ z θ)
            - 6 * φ z θ) := by
    simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, htanφ]
  have hzA : z ^ (pairBeta α + 2) = z ^ pairBeta α * z ^ 2 := by
    rw [Real.rpow_add hz, Real.rpow_two]
  have hzB : z ^ (pairBeta α + 2 - 1) = z ^ pairBeta α * z := by
    rw [show pairBeta α + 2 - 1 = pairBeta α + 1 from by ring, Real.rpow_add hz, Real.rpow_one]
  rw [hz3.deriv, ht3.deriv, hLΦ, hLφ]
  simp only [Work.EllipticEst.Assembly.pairWeight_apply]
  rw [hzA, hzB, sq_mul_pairBeta_add_two (ne_of_gt hα), Real.tan_eq_sin_div_cos θ]
  field_simp
  ring

end Work.EllipticEst.Assembly
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.Honest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux

set_option autoImplicit false

/-! ## Auxiliary facts -/

/-- The slice integrand `(D_z^m g)² w² σ_η` is continuous on the open quadrant. -/
theorem continuousOn_dzIter_weight {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter m g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2) (Work.FTS.EllipticEst.Q0) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter m g p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    ((hg.DzIter m).continuousOn).pow 2
  have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have h1 : ContinuousOn (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) := by
      refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
      · exact (((continuous_const (y := (1 : ℝ))).add
          (continuous_id : Continuous (fun z : ℝ => z))).pow 2).continuousOn
      · exact (((continuous_id : Continuous (fun z : ℝ => z)).pow 2)).continuousOn
      · intro z hz
        exact pow_ne_zero 2 (ne_of_gt hz)
    refine h1.congr ?_
    intro z _
    simp only [Work.Spaces.w]
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    hw.comp (continuous_fst.continuousOn) (fun p hp => hp.1)
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
      Work.FTS.EllipticEst.Q0 := by
    simp only [Work.FTS.EllipticEst.thEta]
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    · intro p hp
      exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos])))
  exact (h1.mul h2).mul h3

/-- `σ_η = sin(2θ)^{-η}` is nonnegative on `Iθ`. -/
theorem thEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.thEta θ := by
  rcases eq_or_lt_of_le (Work.FTS.EllipticEst.sin_two_nonneg hθ) with h | h
  · simp only [Work.FTS.EllipticEst.thEta]
    rw [← h, Real.zero_rpow (neg_ne_zero.mpr Work.Spaces.eta_pos.ne')]
  · exact (Real.rpow_pos_of_pos h _).le

/-- The integrand `D² w² σ_η` is nonnegative on `Iθ`. -/
theorem slice_nonneg (D wz : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ D ^ 2 * wz ^ 2 * Work.FTS.EllipticEst.thEta θ :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (thEta_nonneg_Iθ hθ)

/-- For a.e. `z ∈ Iz` one has `0 < z`. -/
theorem ae_pos_Iz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
    ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-! ## The slice identities for `dIntS` and `ddIntS` -/

/-- `dIntS (D_z^r V) z` is the weighted `L²`-square of `D_z^{r+1}V` on the angular slice. -/
theorem dIntS_slice_eq {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    (z : ℝ) :
    dIntS (Work.Spaces.DzIter r V) z
      = ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.thEta θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hfun : ∀ θ : ℝ, Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ
      = Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ := by
    intro θ
    have h2 : Work.Spaces.DzIter (r + 1) V = Work.Spaces.DzIter r (Work.Spaces.Dz V) :=
      Work.Spaces.DzIter_add_right r 1 V
    exact congrFun (congrFun h2 z) θ
  rw [dIntS, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
    rw [hfun θ]; ring)

/-- `dIntS (D_z^r V) z`, written with the weighted quantity of `HkIntegrand`. -/
theorem dIntS_slice_eq' {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    (z : ℝ) :
    dIntS (Work.Spaces.DzIter r V) z
      = ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [dIntS_slice_eq hV r z]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  simp only [Work.FTS.EllipticEst.thEta]
  rw [mul_div_rpow_sq_eq (Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ) (Work.Spaces.w z)
      (Real.sin (2 * θ)) (Work.FTS.EllipticEst.sin_two_nonneg hθ) Work.Spaces.eta_pos.ne']

/-- `ddIntS (D_z^r V) z` is the weighted `L²`-square of `D_z^{r+2}V` on the angular slice. -/
theorem ddIntS_slice_eq {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    (z : ℝ) :
    ddIntS (Work.Spaces.DzIter r V) z
      = ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.thEta θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hfun : ∀ θ : ℝ, Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V)) z θ
      = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ := by
    intro θ
    have h2 : Work.Spaces.DzIter (r + 2) V = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) :=
      Work.Spaces.DzIter_add_right r 2 V
    exact congrFun (congrFun h2 z) θ
  rw [ddIntS, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
    rw [hfun θ]; ring)

/-- `ddIntS (D_z^r V) z`, written with the weighted quantity of `HkIntegrand`. -/
theorem ddIntS_slice_eq' {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    (z : ℝ) :
    ddIntS (Work.Spaces.DzIter r V) z
      = ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [ddIntS_slice_eq hV r z]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  simp only [Work.FTS.EllipticEst.thEta]
  rw [mul_div_rpow_sq_eq (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ) (Work.Spaces.w z)
      (Real.sin (2 * θ)) (Work.FTS.EllipticEst.sin_two_nonneg hθ) Work.Spaces.eta_pos.ne']

/-- `ttIntS (D_z^r V) z` is the weighted `L²`-square of `D_z^r ∂_θ²V` on the angular slice
(for `z > 0`). -/
theorem ttIntS_slice_eq {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    {z : ℝ} (hz : 0 < z) :
    ttIntS (Work.Spaces.DzIter r V) z
      = ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.thEta θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [ttIntS, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
    ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2))]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [show Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ
      = Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ from
        pthIter2_DzIter_comm hV hz hθ.1 hθ.2 r]
  ring

/-- `ttIntS (D_z^r V) z`, written with the weighted quantity of `HkIntegrand` (for `z > 0`). -/
theorem ttIntS_slice_eq' {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    {z : ℝ} (hz : 0 < z) :
    ttIntS (Work.Spaces.DzIter r V) z
      = ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [ttIntS_slice_eq hV r hz]
  refine MeasureTheory.integral_congr_ae ?_
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
    ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2))]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  show (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      * Work.FTS.EllipticEst.thEta θ
    = (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
  simp only [Work.FTS.EllipticEst.thEta]
  rw [mul_div_rpow_sq_eq (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ) (Work.Spaces.w z)
      (Real.sin (2 * θ)) hpos.le Work.Spaces.eta_pos.ne']

/-! ## The three integrability statements -/

/-- A generic honesty step: a nonnegative slice functional dominated by the `ℋ^k`-integrand of
`g` is integrable over `Iz`. -/
theorem integrableOn_of_slice_le {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ} {G : ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k g) (hGnn : ∀ z : ℝ, 0 ≤ G z)
    (haesm : MeasureTheory.AEStronglyMeasurable G
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      G z ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) :
    MeasureTheory.IntegrableOn G Work.Spaces.Iz := by
  refine MeasureTheory.Integrable.mono' hmem.2 haesm ?_
  filter_upwards [hbound] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (hGnn z)]
  exact hz

/-- `dIntS (D_z^r V)` is integrable on `Iz`. -/
theorem dIntS_integrableOn {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.Dz V)) (hr : r ≤ k) :
    MeasureTheory.IntegrableOn (fun z : ℝ => dIntS (Work.Spaces.DzIter r V) z)
      Work.Spaces.Iz := by
  refine integrableOn_of_slice_le hmem ?_ ?_ ?_
  · intro z
    rw [dIntS_slice_eq' hV r z]
    exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  · have h1 : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (Work.Spaces.aesm_of_continuousOn_Qd _
        (continuousOn_dzIter_weight (g := Work.Spaces.Dz V) hV.Dz r)).integral_prod_right'
    refine h1.congr ?_
    filter_upwards with z
    exact (dIntS_slice_eq hV r z).symm
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [dIntS_slice_eq' hV r z]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hmem.1 z hz)
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.Dz V) z θ r hr)

/-- `ddIntS (D_z^r V)` is integrable on `Iz`. -/
theorem ddIntS_integrableOn {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V)) (hr : r ≤ k) :
    MeasureTheory.IntegrableOn (fun z : ℝ => ddIntS (Work.Spaces.DzIter r V) z)
      Work.Spaces.Iz := by
  refine integrableOn_of_slice_le hmem ?_ ?_ ?_
  · intro z
    rw [ddIntS_slice_eq' hV r z]
    exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  · have h1 : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (Work.Spaces.aesm_of_continuousOn_Qd _
        (continuousOn_dzIter_weight (g := Work.Spaces.DzIter 2 V) (hV.DzIter 2) r)).integral_prod_right'
    refine h1.congr ?_
    filter_upwards with z
    exact (ddIntS_slice_eq hV r z).symm
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [ddIntS_slice_eq' hV r z]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hmem.1 z hz)
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.DzIter 2 V) z θ r hr)

/-- `ttIntS (D_z^r V)` is integrable on `Iz`. -/
theorem ttIntS_integrableOn {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V)) (hr : r ≤ k) :
    MeasureTheory.IntegrableOn (fun z : ℝ => ttIntS (Work.Spaces.DzIter r V) z)
      Work.Spaces.Iz := by
  refine integrableOn_of_slice_le hmem ?_ ?_ ?_
  · intro z
    by_cases hz : 0 < z
    · rw [ttIntS_slice_eq' hV r hz]
      exact MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => sq_nonneg _))
    · rw [ttIntS]
      exact mul_nonneg (sq_nonneg _)
        (MeasureTheory.integral_nonneg_of_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => mul_nonneg (sq_nonneg _) (thEta_nonneg_Iθ hθ))))
  · have h1 : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (Work.Spaces.aesm_of_continuousOn_Qd _
        (continuousOn_dzIter_weight (g := Work.Spaces.pthIter 2 V) hV.pth.pth r)).integral_prod_right'
    refine h1.congr ?_
    filter_upwards [ae_pos_Iz] with z hz
    exact (ttIntS_slice_eq hV r hz).symm
  · filter_upwards [ae_pos_Iz] with z hz
    rw [ttIntS_slice_eq' hV r hz]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hmem.1 z (le_of_lt hz))
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 V) z θ r hr)


/-! ## Slicewise honesty of a single `HkIntegrand` summand -/

/-- A single `D_z`-summand of `HkIntegrand α k g`, written with the unweighted angular weight,
is integrable on the angular slice for every `z > 0` as soon as the whole integrand is. -/
theorem integrableOn_slice_summand {k i : ℕ} {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α k g) (hi : i ≤ k) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter i g z θ) ^ 2
      * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.DzIter i g z θ) ^ 2
      * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.aesm_slice_of_continuousOn_Qd _
      (continuousOn_dzIter_weight (g := g) hg i) hz)
  refine MeasureTheory.Integrable.mono' (hmem.1 z (le_of_lt hz)) haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (thEta_nonneg_Iθ hθ))]
  have h := Work.Spaces.sq_le_HkIntegrand_z α k g z θ i hi
  have h2 : (Work.Spaces.DzIter i g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ := by
    rw [mul_div_rpow_sq_eq _ _ _ (Work.FTS.EllipticEst.sin_two_nonneg hθ)
      Work.Spaces.eta_pos.ne']
    simp only [Work.FTS.EllipticEst.thEta]
  rwa [h2] at h

/-! ## Slicewise honesty of the three functionals of `u_r = D_z^r V` -/

/-- **The slicewise honesty hypothesis of `InterpOpen` for `u_r = D_z^r V`**, derived from the
`ℋ^k`-membership of `D_zV`, `D_z²V` and `∂_θ²V`. -/
theorem sliceHonestOpen_dzIter {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hdd : Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V))
    (htt : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V))
    (hd : Work.Spaces.HkMem α k (Work.Spaces.Dz V)) (hr : r ≤ k) :
    SliceHonestOpen (Work.Spaces.DzIter r V) := by
  have hfunD : ∀ z θ : ℝ, Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ
      = Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ := by
    intro z θ
    have h2 : Work.Spaces.DzIter (r + 1) V = Work.Spaces.DzIter r (Work.Spaces.Dz V) :=
      Work.Spaces.DzIter_add_right r 1 V
    exact congrFun (congrFun h2 z) θ
  have hfunDD : ∀ z θ : ℝ, Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V)) z θ
      = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ := by
    intro z θ
    have h2 : Work.Spaces.DzIter (r + 2) V = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) :=
      Work.Spaces.DzIter_add_right r 2 V
    exact congrFun (congrFun h2 z) θ
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have h1 := integrableOn_slice_summand (g := Work.Spaces.pthIter 2 V) hV.pth.pth htt hr hz
    refine h1.congr ?_
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
      ← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
          (b := Real.pi / 2))]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [show Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ
        = Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ from
          pthIter2_DzIter_comm hV hz hθ.1 hθ.2 r]
  · intro z hz
    have h1 := integrableOn_slice_summand (g := Work.Spaces.DzIter 2 V) (hV.DzIter 2) hdd hr hz
    refine h1.congr ?_
    filter_upwards with θ
    rw [hfunDD z θ]
  · intro z hz
    have h1 := integrableOn_slice_summand (g := Work.Spaces.Dz V) hV.Dz hd hr hz
    refine h1.congr ?_
    filter_upwards with θ
    rw [hfunD z θ]

end Work.EllipticEst.Core.i0Aux
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.RRDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The half-strip `ℝ × (0,π/2)` of the `(σ,θ)`-coordinates. -/
def stripRR : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- The transported weight `α exp (5σ) cos θ`
(= the Jacobian `α exp (ασ)` times the weight `z^((5-α)/α) cos θ` at `z = exp (ασ)`). -/
def wtRR (α : ℝ) (σ θ : ℝ) : ℝ := α * Real.exp (5 * σ) * Real.cos θ

/-- The transported unknown, zero off the half-strip. -/
def VRR (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun σ θ => if θ ∈ Set.Ioo 0 (Real.pi / 2) then wtRR α σ θ * Ψ (Real.exp (α * σ)) θ else 0

/-- The transported source, zero off the half-strip. -/
def GRR (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun σ θ => if θ ∈ Set.Ioo 0 (Real.pi / 2) then wtRR α σ θ * F (Real.exp (α * σ)) θ else 0

/-- The operator `bslOp` in the `(σ,θ)`-coordinates (the `deriv`-level version of `Strip.Kop`). -/
def kopD (ψ : ℝ → ℝ → ℂ) (σ θ : ℝ) : ℂ :=
  - deriv (fun σ' => deriv (fun σ'' => ψ σ'' θ) σ') σ
    - deriv (fun θ' => deriv (fun θ'' => ψ σ θ'') θ') θ
    - 5 * deriv (fun σ' => ψ σ' θ) σ
    + (Real.tan θ : ℂ) * deriv (fun θ' => ψ σ θ') θ
    + ((Real.tan θ) ^ 2 - 5 : ℝ) * ψ σ θ


/-- The weak identity in the `(σ,θ)`-coordinates. -/
def StripWeakRR (U G : ℝ → ℝ → ℂ) : Prop :=
  ∀ ψ : ℝ → ℝ → ℂ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ)) →
    HasCompactSupport (Function.uncurry ψ) → tsupport (Function.uncurry ψ) ⊆ stripRR →
    ∫ q : ℝ × ℝ, U q.1 q.2 * kopD ψ q.1 q.2 = ∫ q : ℝ × ℝ, G q.1 q.2 * ψ q.1 q.2

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.exists_tan_extension =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter Metric

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The strip `{0 < θ < π/2}` is open. -/
theorem isOpen_stripE_fts : IsOpen Work.EllipticEst.InteriorRegularity.stripE := by
  rw [Work.EllipticEst.InteriorRegularity.stripE]
  refine isOpen_Ioo.preimage ?_
  fun_prop


end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.FTS.ClassC.PzSinCos2Box =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## A continuity helper -/


/-! ## The statement

The proof is the AM–GM domination of `∂_z f · sinθcos²θ` by the first `D_z`-slot of the
`ℋ¹`-integrand.  On the box `(s,z] × Iθ` we have `r ≥ s > 0`, so

* `pzSqSeta_le_Dz1_mul` gives `(∂_z f)² sin(2θ)^{-η} ≤ C·(D_z f · w/sin(2θ)^{η/2})²` with the
  box constant `C = z²/(1+s)⁴`, and `sin(2θ)^{-η} ≥ 1` away from the degenerate angles;
* `|sinθcos²θ| ≤ 1`, so `|∂_z f·sinθcos²θ| ≤ |∂_z f| ≤ ½(∂_z f)² + ½`;
* the `D_z`-slot is integrable on the box by `integrable_prod_sq_restrict_open` (the `i = 1`
  slot, valid at level `1` because `HkMem α 1 f`), the constant `½` is integrable because the
  box has finite measure, and a.e. strong measurability is
  `aesm_uncurry_restrict_open` (continuity on the open quadrant from `SmoothOpen.pz`). -/

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.aslotAux.bslOpPth.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.aslotAux.BslOpPth

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary measure-theoretic helpers -/

/-- The half-line `Iz = [0,∞)` and `(0,∞)` agree almost everywhere. -/
theorem lintegral_Iz_congr (f : ℝ → ℝ≥0∞) :
    (∫⁻ z in Work.Spaces.Iz, f z) = ∫⁻ z in Set.Ioi 0, f z := by
  rw [Work.Spaces.Iz]
  exact congrArg (fun μ : Measure ℝ => ∫⁻ z, f z ∂μ)
    (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm


/-- The product of the restricted measures is the restricted planar measure. -/
theorem prod_restrict_eq_restrict :
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  have hIz : (volume.restrict Work.Spaces.Iz : Measure ℝ) = volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm
  rw [hIz, MeasureTheory.Measure.volume_eq_prod]
  exact MeasureTheory.Measure.prod_restrict (μ := volume) (ν := volume)
    (Set.Ioi (0 : ℝ)) Work.Spaces.Iθ

/-- The two restricted rectangular measures agree. -/
theorem restrict_rect_eq :
    (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  have hIz : (volume.restrict Work.Spaces.Iz : Measure ℝ) = volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm
  have hL : (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict (μ := volume) (ν := volume)
      Work.Spaces.Iz Work.Spaces.Iθ).symm
  have hR : (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
      = (volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict (μ := volume) (ν := volume)
      (Set.Ioi (0 : ℝ)) Work.Spaces.Iθ).symm
  rw [hL, hR, hIz]

/-- The restricted planar measure on `(0,∞) × Iθ` is the one on the open quadrant. -/
theorem restrict_prod_eq_restrict_Q0 :
    (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
      = volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h1 : (volume.restrict Work.Spaces.Iθ : Measure ℝ)
      = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ))
        (b := Real.pi / 2))).symm
  have hL : (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
      = (volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict (μ := volume) (ν := volume) (Set.Ioi (0 : ℝ))
      Work.Spaces.Iθ).symm
  have hR : (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
      = (volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict (μ := volume) (ν := volume) (Set.Ioi (0 : ℝ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2))).symm
  rw [hL, hR, h1]



/-- The squared radial weight is continuous on the open quadrant. -/
theorem continuousOn_w_sq_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [show (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 from rfl]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  exact h1.pow 2

/-- The angular weight `sin(2θ)^{2-γ}` is continuous on the open quadrant. -/
theorem continuousOn_sigma_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hsin : Continuous (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_snd)
  exact hsin.continuousOn.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))




/-! ## The iterated-to-product transfer, and the level-`0` slots -/

/-- Measurability of a `σ`-weighted slot integrand, from smoothness of the uncurried factor
on the open quadrant. -/
theorem aesm_slot_of {α : ℝ} {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (g p ^ 2 * (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)))
      (volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) := by
  have hA : AEStronglyMeasurable (fun p : ℝ × ℝ => g p ^ 2 * (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (((Work.Spaces.aesm_of_continuousOn_Qd g hg).pow 2).mul
      (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        continuousOn_w_sq_Q0)).mul
      (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
        (continuousOn_sigma_Q0 α))
  have hA' : AEStronglyMeasurable (fun p : ℝ × ℝ => g p ^ 2 * (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
      (volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) := by
    rw [← prod_restrict_eq_restrict]
    exact hA
  exact hA'.aemeasurable.ennreal_ofReal

/-- **The transfer**: an iterated `∫⁻_z ∫⁻_θ`-bound for a `σ`-weighted slot gives the
corresponding product-measure bound. -/
theorem piece_slot {α : ℝ} {h : ℝ → ℝ → ℝ} {K : ℝ}
    (hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((h p.1 p.2) ^ 2
      * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)))
      (volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)))
    (hinner : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((h z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) ≤ ENNReal.ofReal K) :
    (∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ,
        ENNReal.ofReal ((h p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))) ≤ ENNReal.ofReal K := by
  have hmeas' : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((h p.1 p.2) ^ 2
      * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [prod_restrict_eq_restrict]
    exact hmeas
  have hM : (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) : Measure (ℝ × ℝ))
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict (μ := volume) (ν := volume)
      Work.Spaces.Iz Work.Spaces.Iθ).symm
  calc (∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ, ENNReal.ofReal ((h p.1 p.2) ^ 2
        * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)))
      = ∫⁻ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, ENNReal.ofReal ((h p.1 p.2) ^ 2
          * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)) := by
        rw [← restrict_rect_eq]
    _ = ∫⁻ p, ENNReal.ofReal ((h p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        rw [hM]
    _ = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((h z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
        MeasureTheory.lintegral_prod _ hmeas'
    _ = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((h z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
        rw [lintegral_Iz_congr (f := fun z => ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((h z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))]
    _ ≤ ENNReal.ofReal K := hinner




end Work.FTS.ClassC.aslotAux.BslOpPth
end
-- ===== merged: Submission.Work.FTS.ClassCHon.CmpSupp.source_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.CmpSupp

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts about the angular weight `σ` -/

/-- `sin (2θ) ≥ 0` on the angular interval `Iθ = [0,π/2]`. -/
theorem sf_sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩


/-- `(a ^ p) ^ 2 = a ^ (p * 2)` for `a ≥ 0`: the natural-number power on the left is converted
into a real one by `Real.rpow_natCast` before `Real.rpow_mul` is applied. -/
theorem sf_sq_rpow_mul_two {a : ℝ} (ha : 0 ≤ a) (p : ℝ) : (a ^ p) ^ 2 = a ^ (p * 2) := by
  rw [← Real.rpow_natCast (a ^ p) 2]
  exact (Real.rpow_mul ha p 2).symm

/-- **The square of the `i = 0` angular weight on `Iθ`**: `(w(z)/sin(2θ)^{η/2})² = w(z)²·σ(θ)`.
The only use of `θ ∈ Iθ` is the non-negativity of the base `sin(2θ)`; at the endpoints both sides
are `0` by Lean's totalised `rpow` and division. -/
theorem sf_Whz_sq_Iθ {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have ha : 0 ≤ Real.sin (2 * θ) := sf_sin_two_nonneg_Iθ hθ
  have h1 : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg ha (Work.Spaces.eta / 2)]
  rw [h1, mul_pow, sf_sq_rpow_mul_two ha (-(Work.Spaces.eta / 2)),
    show (-(Work.Spaces.eta / 2)) * 2 = -Work.Spaces.eta by ring]
  rfl

/-- **The `ℋ⁰`-integrand collapses to a single square**: at level `k = 0` the mixed double sum of
`HkIntegrand` is empty (`1 ≤ 0` is false) and only the `i = 0` term of the `D_z`-sum survives. -/
theorem sf_HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand]
  norm_num

/-! ## The separable majorant of the `ℋ⁰`-integrand

`srcMajorant a b Mc` is the constant `Mc` on the strip `[a,b]` (in `z`) times the angular weight
`σ`, and `0` off the strip.  It is the majorant used in `source_facts`: the `ℋ⁰`-integrand of a
source supported in `[a,b]` is below it (with `Mc` the bound of `F z θ ² w(z)²` on the box), its
`θ`-slices are integrable because `σ` is, and its slice integrals are the indicator of `[a,b]`
times a constant, hence integrable on `[0,∞)`. -/





/-! ## The main theorem -/


end Work.FTS.ClassCHon.CmpSupp
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.SliceMassUpgrade =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.ClassCHon.SliceMassUpgrade




/-! ## The every-`z` finiteness -/

/-- A point of the interval `(a,b)` on which an a.e. finite function is finite (any non-degenerate
interval has positive measure). -/
lemma exists_lt_top_of_ae_lt_top {M : ℝ → ENNReal} {a b : ℝ} (hab : a < b)
    (h : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), M t < ⊤) :
    ∃ t ∈ Set.Ioo a b, M t < ⊤ := by
  by_contra hcon
  push_neg at hcon
  have hsub : Set.Ioo a b ⊆ {t : ℝ | ¬ M t < ⊤} := fun t ht => not_lt.mpr (hcon t ht)
  have h0 : (volume.restrict (Set.Ioo a b)) {t : ℝ | ¬ M t < ⊤} = 0 := MeasureTheory.ae_iff.mp h
  have hle : (volume.restrict (Set.Ioo a b)) (Set.Ioo a b)
      ≤ (volume.restrict (Set.Ioo a b)) {t : ℝ | ¬ M t < ⊤} := MeasureTheory.measure_mono hsub
  rw [h0] at hle
  have hvol : (volume.restrict (Set.Ioo a b)) (Set.Ioo a b) = ENNReal.ofReal (b - a) := by
    rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_self, Real.volume_Ioo]
  rw [hvol] at hle
  exact absurd hle (not_le.mpr (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)))


end Work.FTS.ClassCHon.SliceMassUpgrade
end
-- ===== merged: Submission.Work.FTS.ClassCHon.SliceMassUpgrade.ofReal_sliceMass_pointwise_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory

namespace Work.FTS.ClassCHon.SliceMassUpgrade

/-- The `τ`-weighted (`τ ≥ 0` arbitrary) pointwise slice-mass comparison: for a source `F`
smooth on the open quadrant, `z₁ ≤ z₂`, `z₁ > 0` and interior `θ`,

  `τ θ · F(z₂,θ)² ≤ 2 τ θ · F(z₁,θ)² + 2 τ θ · (z₂ - z₁) ∫_{z₁}^{z₂} (∂_z F(s,θ))²`.

This is the general form of `ofReal_sliceMass_pointwise` (which is the case `τ = sEta`), with
the angular weight left abstract; the proof is the FTC + Cauchy–Schwarz argument on the
`z`-slice, with no positivity or measurability needed of `τ` beyond `τ ≥ 0` on `Iθ`. -/
theorem ofReal_sliceMass_pointwise_gen {F : ℝ → ℝ → ℝ} {τ : ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hτ : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ τ θ)
    {z₁ z₂ θ : ℝ} (hz₁ : 0 < z₁) (hz₁₂ : z₁ ≤ z₂) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ENNReal.ofReal (τ θ * (F z₂ θ) ^ 2)
      ≤ ENNReal.ofReal 2 * ENNReal.ofReal (τ θ * (F z₁ θ) ^ 2)
        + ENNReal.ofReal 2 * (ENNReal.ofReal (τ θ)
            * ENNReal.ofReal (z₂ - z₁)
            * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)) := by
  set A : ℝ := τ θ with hAdef
  set I : ℝ := ∫ s in z₁..z₂, Work.Spaces.pz F s θ with hIdef
  set J : ℝ := ∫ s in z₁..z₂, (Work.Spaces.pz F s θ) ^ 2 with hJdef
  -- nonnegativity of the angular weight
  have hA : 0 ≤ A := by
    rw [hAdef]
    exact hτ θ hθ
  have hz2 : 0 ≤ z₂ - z₁ := sub_nonneg.mpr hz₁₂
  -- the slices are smooth on the open half-line, hence on `[z₁,z₂]`
  have hsub : Set.Icc z₁ z₂ ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le hz₁ hs.1
  have hcontf : ContinuousOn (fun s : ℝ => Work.Spaces.pz F s θ) (Set.Icc z₁ z₂) :=
    ((hF.pz.curry_z hθ).continuousOn).mono hsub
  -- fundamental theorem of calculus for the slice
  have hderiv : ∀ s ∈ Set.uIcc z₁ z₂,
      HasDerivAt (fun s' : ℝ => F s' θ) (Work.Spaces.pz F s θ) s := by
    intro s hs
    rw [Set.uIcc_of_le hz₁₂] at hs
    exact hF.hasDerivAt_slice hθ (lt_of_lt_of_le hz₁ hs.1)
  have hint : IntervalIntegrable (fun s : ℝ => Work.Spaces.pz F s θ) volume z₁ z₂ := by
    have hc : ContinuousOn (fun s : ℝ => Work.Spaces.pz F s θ) (Set.uIcc z₁ z₂) := by
      rw [Set.uIcc_of_le hz₁₂]; exact hcontf
    exact hc.intervalIntegrable
  have hftc : F z₂ θ - F z₁ θ = I := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [hIdef]
    exact h.symm
  -- nonnegativity of the squared-gradient slice integral
  have hJ : 0 ≤ J := by
    rw [hJdef]
    exact intervalIntegral.integral_nonneg hz₁₂ (fun u _ => sq_nonneg _)
  -- Cauchy–Schwarz: `I² ≤ (z₂ - z₁) J`
  have hI2 : I ^ 2 ≤ (z₂ - z₁) * J := by
    have h := interval_integral_sq_le_measure_mul hz₁₂ hcontf (g := fun s => Work.Spaces.pz F s θ)
    rw [hIdef, hJdef]
    exact h
  -- the elementary pointwise bound
  have hmain : A * (F z₂ θ) ^ 2 ≤ 2 * (A * (F z₁ θ) ^ 2) + 2 * (A * (z₂ - z₁) * J) := by
    have hb2 : (F z₂ θ) ^ 2 ≤ 2 * (F z₁ θ) ^ 2 + 2 * I ^ 2 := by
      have hb : F z₂ θ = F z₁ θ + I := by linarith [hftc]
      rw [hb]
      nlinarith [sq_nonneg (F z₁ θ - I)]
    have h1 : A * (F z₂ θ) ^ 2 ≤ A * (2 * (F z₁ θ) ^ 2 + 2 * I ^ 2) :=
      mul_le_mul_of_nonneg_left hb2 hA
    have h2 : A * I ^ 2 ≤ A * ((z₂ - z₁) * J) := mul_le_mul_of_nonneg_left hI2 hA
    nlinarith [h1, h2]
  -- convert the angular lintegral into `ofReal J`
  have hcont2 : ContinuousOn (fun s : ℝ => (Work.Spaces.pz F s θ) ^ 2) (Set.Icc z₁ z₂) :=
    hcontf.pow 2
  have hL : (∫⁻ s in Set.Ioo z₁ z₂,
      ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)) = ENNReal.ofReal J := by
    rw [hJdef]
    exact (Work.FTS.EllipticEst.AngSecond.ofReal_intervalIntegral_eq_lintegral hz₁₂ hcont2
      (fun x _ => sq_nonneg _)).symm
  rw [hL]
  have h1 : 0 ≤ 2 * (A * (F z₁ θ) ^ 2) :=
    mul_nonneg (by norm_num) (mul_nonneg hA (sq_nonneg _))
  have h2 : 0 ≤ 2 * (A * (z₂ - z₁) * J) :=
    mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hA hz2) hJ)
  have hEqMul : ENNReal.ofReal (A * (z₂ - z₁) * J)
      = ENNReal.ofReal A * ENNReal.ofReal (z₂ - z₁) * ENNReal.ofReal J := by
    rw [ENNReal.ofReal_mul (mul_nonneg hA hz2), ENNReal.ofReal_mul hA]
  refine le_trans (ENNReal.ofReal_le_ofReal hmain) ?_
  rw [ENNReal.ofReal_add h1 h2, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), hEqMul]

end Work.FTS.ClassCHon.SliceMassUpgrade
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Zpz.Auxiliary.integrable_and_swap_abs_pzIter2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.Zpz.Aux

set_option autoImplicit false

/-!
# `integrable_and_swap_abs_pzIter2`

Box integrability and Fubini for the radial second derivative `∂_z²F` of a source which is
`C^∞` on the open quadrant and honest in `ℋ²`, at the level of the *weighted* `θ`-slices.

The pointwise input is the second-order slice bound

  `|∂_z²F(τ,θ)| ≤ (2/τ²)·√(HkIntegrand α 2 F τ θ)`   (`hpt`),

valid for `τ > 0` and `θ ∈ (0,π/2)`; the two integrability hypotheses `hsl`, `hout` say that
the right-hand side is an honest object: every `θ`-slice `√(HkIntegrand α 2 F τ ·)` is
integrable on `Iθ` for `τ ≥ 0`, and its `θ`-integral is integrable in `τ` on every `[a,b]`
with `a > 0`.

On the box `(z₀, x]` (with `z₀, x > 0`, so `τ ≥ min z₀ x > 0`) the bound `2/τ² ≤ 2/a²`,
`a := min z₀ x`, therefore turns the target into a constant multiple of `√(HkIntegrand)`,
which is integrable on the product box: this is Tonelli for a nonnegative integrand
(`Work.Spaces.integrable_prod_of_iterated`), the a.e. strong measurability coming from the
`C^∞`-smoothness of `F` on the open quadrant (`SmoothOpen`).  Fubini's theorem for interval
integrals (`MeasureTheory.intervalIntegral_integral_swap`) then gives the swap.

Every declaration in this file is fully proved and rests only on the axioms
`[propext, Classical.choice, Quot.sound]`.
-/



end Work.FTS.ClassCHon.Zpz.Aux
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Zpz.Auxiliary.slice_mul_phiW_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz.Aux

open MeasureTheory Set Filter
open scoped Real Topology



end Work.FTS.ClassCHon.Zpz.Aux
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Zpz.Auxiliary.sqrtHk_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz.Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## Elementary helpers -/





/-! ## The main statement -/


end

end Work.FTS.ClassCHon.Zpz.Aux
end
-- ===== merged: Submission.Work.FTS.EllExist.Shift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Inverting the shift -/


/-! ## The operator identity -/

/-- **The paper's identity `L(G(R) sin 2θ) = (α²R²G'' + α(5+α)RG') sin 2θ`.**

Adding the radial multiple `G(z) sin 2θ` to `Ψ` changes `bslOp α Ψ` only by
`-(α²z²G'' + α(5+α)zG') sin 2θ`: the `sin 2θ`-direction of `bslOp` is purely radial.  This is
`Work.Elliptic.bslOp_sinG` in the notation of the area. -/
theorem bslOp_shiftSing (α : ℝ) (g Ψ : Fn) (z θ : ℝ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hG : ContDiffAt ℝ 2 (Work.Elliptic.Gsing α g) z)
    (hcos : Real.cos θ ≠ 0) :
    Work.Elliptic.bslOp α (shiftSing α g Ψ) z θ
      = Work.Elliptic.bslOp α Ψ z θ
        - (α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α g) z') z
            + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α g) z) * Real.sin (2 * θ) := by
  rw [shiftSing_eq]
  exact Work.Elliptic.bslOp_sinG α Ψ (Work.Elliptic.Gsing α g) z θ hΨ hG hcos

/-- **The shift orthogonalises the source.**  If `Gsing α g` satisfies the singular-term ODE
`α²z²G'' + α(5+α)zG' = (15/4) F_*(g)`, then shifting by `Gsin 2θ` replaces the source `g` by
`orthSource g = g - (15/4) sin 2θ · F_*(g)`, i.e. by a source whose angular moment vanishes
(`Work.Elliptic.Fstar_orthSource`). -/
theorem bslOp_shiftSing_of_ode (α : ℝ) (g Ψ : Fn) (z θ : ℝ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hG : ContDiffAt ℝ 2 (Work.Elliptic.Gsing α g) z)
    (hcos : Real.cos θ ≠ 0)
    (hode : α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α g) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α g) z
      = (15 / 4) * Work.Elliptic.Fstar g z) :
    Work.Elliptic.bslOp α (shiftSing α g Ψ) z θ
      = Work.Elliptic.bslOp α Ψ z θ - (15 / 4) * Work.Elliptic.Fstar g z * Real.sin (2 * θ) := by
  rw [bslOp_shiftSing α g Ψ z θ hΨ hG hcos, hode]

/-- The converse direction: if the shifted unknown solves the orthogonalised equation, then the
unshifted one solves the original equation.  This is the step that turns the existence theorem
for the orthogonalised source `orthSource g` (which is what the elliptic theory provides) into
`IsBslSol α g Ψ`. -/
theorem bslOp_eq_of_shiftSing_of_ode (α : ℝ) (g Ψ : Fn) (z θ : ℝ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hG : ContDiffAt ℝ 2 (Work.Elliptic.Gsing α g) z)
    (hcos : Real.cos θ ≠ 0)
    (hode : α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α g) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α g) z
      = (15 / 4) * Work.Elliptic.Fstar g z)
    (hsol : Work.Elliptic.bslOp α (shiftSing α g Ψ) z θ = Work.Elliptic.orthSource g z θ) :
    Work.Elliptic.bslOp α Ψ z θ = g z θ := by
  have h := bslOp_shiftSing_of_ode α g Ψ z θ hΨ hG hcos hode
  rw [hsol, Work.Elliptic.orthSource] at h
  have h2 : Work.Elliptic.bslOp α Ψ z θ
      = (g z θ - 15 / 4 * Work.Elliptic.Fstar g z * Real.sin (2 * θ))
        + 15 / 4 * Work.Elliptic.Fstar g z * Real.sin (2 * θ) := by linarith [h]
  linarith [h2]

/-! ## The Dirichlet values -/



/-! ## The angular moment of the shift -/

/-- `∫_θ sin 2θ · sinθcos²θ dθ = 4/15`, the normalisation constant of §'The singular term'. -/
theorem integral_sin_two_mul_sinCos2 :
    (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) = 4 / 15 :=
  Work.Elliptic.integral_sin_two_mul_sinCos2


/-! ## Smoothness of the shift -/




/-! ## Decay of the shift -/


/-- **The orthogonality of `orthSource F`, unconditionally.**

`F_*(orthSource F)(z) = 0` for every `z`, with no hypothesis at all: if the slice
`θ ↦ F z θ · sinθcos²θ` is not integrable both sides of the identity are the junk value `0`,
and otherwise the integral splits and `∫_θ sin 2θ · sinθcos²θ dθ = 4/15` cancels the `15/4`.

(Proved here to keep the area self-contained: the version in
`Submission/Work/Elliptic/Fstar_orthSource.lean` asks for continuity of the angular slice.) -/
theorem Fstar_orthSource_zero (F : Fn) (z : ℝ) :
    Work.Elliptic.Fstar (Work.Elliptic.orthSource F) z = 0 := by
  set u : ℝ → ℝ := fun θ => (F z θ - (15 / 4) * Real.sin (2 * θ) * Work.Elliptic.Fstar F z)
    * Work.Elliptic.sinCos2 θ with hu
  have hval : Work.Elliptic.Fstar (Work.Elliptic.orthSource F) z
      = ∫ θ in Work.Spaces.Iθ, u θ := by
    rw [Work.Elliptic.Fstar]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    simp only [hu, Work.Elliptic.orthSource]
  rw [hval]
  by_cases hint : MeasureTheory.Integrable u (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  · have hpt : ∀ θ, u θ = F z θ * Work.Elliptic.sinCos2 θ
        - ((15 / 4) * Work.Elliptic.Fstar F z)
          * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
      intro θ; simp only [hu]; ring
    have h2int : MeasureTheory.Integrable
        (fun θ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hc : Continuous fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ := by
        simp only [Work.Elliptic.sinCos2]; fun_prop
      exact hc.continuousOn.integrableOn_compact isCompact_Icc
    have h1int : MeasureTheory.Integrable (fun θ => F z θ * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hsub : MeasureTheory.Integrable
          (fun θ => u θ + ((15 / 4) * Work.Elliptic.Fstar F z)
            * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        hint.add (h2int.const_mul _)
      refine hsub.congr ?_
      filter_upwards with θ
      rw [hpt θ]; ring
    have hcongr : (∫ θ in Work.Spaces.Iθ, u θ)
        = ∫ θ in Work.Spaces.Iθ, (F z θ * Work.Elliptic.sinCos2 θ
            - ((15 / 4) * Work.Elliptic.Fstar F z)
              * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => hpt θ
    rw [hcongr, MeasureTheory.integral_sub h1int (h2int.const_mul _),
      MeasureTheory.integral_const_mul, integral_sin_two_mul_sinCos2]
    simp only [Work.Elliptic.Fstar]
    ring
  · exact MeasureTheory.integral_undef hint

end Work.FTS.EllExist
end
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- The light angular weight `σ_a = sin(2θ)^{2-γ(α)}` of the left-hand side. -/
def wA (α : ℝ) : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)

/-- The heavy angular weight `σ_η = sin(2θ)^{-η}`. -/
def wE : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

@[simp] theorem wA_def (α θ : ℝ) : wA α θ = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := rfl
@[simp] theorem wE_def (θ : ℝ) : wE θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl

theorem wE_eq_sEta (θ : ℝ) : wE θ = Work.FTS.EllipticEst.sEta θ := rfl

/-- `σ_a ≤ σ_η` on `Iθ` (for `α ≤ 1`). -/
theorem wA_le_wE {α θ : ℝ} (hα : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ) : wA α θ ≤ wE θ :=
  Work.FTS.EllipticEst.TT.sigA_le_sEta (α := α) (θ := θ) hα hθ

theorem wA_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ wA α θ :=
  Work.FTS.EllipticEst.TT.sigA_nonneg α θ hθ

theorem wE_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ wE θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.TT.sin_two_nonneg_of_mem_Iθ hθ) _

/-- The "nice" class of data for which the Plancherel derivation is performed directly: `g` is
`C²` on the open strip, vanishes at the two endpoints for every `t`, and has **uniformly
compact support** in `t` (i.e. `g t θ = 0` for `|t| > N`, uniformly in `θ`). -/
def NiceFlat (g : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 (Function.uncurry g) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) ∧
    (∀ t : ℝ, g t 0 = 0) ∧ (∀ t : ℝ, g t (Real.pi / 2) = 0) ∧
    ∃ N : ℝ, ∀ t θ : ℝ, N < |t| → g t θ = 0

/-- The explicit `t`-Fourier transform (Mathlib's `Real.fourier` convention) of a
complex-valued function of one real variable. -/
def slice1 (h : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ t : ℝ, h t * Complex.exp (-(2 * Real.pi * Complex.I * ξ * t))

/-- The `t`-Fourier slice `Φ_ξ(θ) = ∫_t g(t,θ) e^{-2πiξt} dt` (as a complex-valued function of
`θ`).  For `NiceFlat g` this is an absolutely convergent integral. -/
def slice (g : ℝ → ℝ → ℝ) (ξ θ : ℝ) : ℂ :=
  ∫ t : ℝ, (g t θ : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * ξ * t))


/-- `Xint`: the left-hand side `∫∫ (∂_t∂_θg)² σ_a` (iterated integral form). -/
def Xint (α : ℝ) (g : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t in Set.univ, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pz (Work.Spaces.pth g) t θ) ^ 2 * wA α θ






/-- The per-`ξ` angular energy of the second `θ`-derivative of the slice. -/
def sliceQ (g : ℝ → ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, ‖deriv (fun θ' => deriv (fun θ'' => slice g ξ θ'') θ') θ‖ ^ 2 * wE θ

end

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.TraceShift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.TraceEngine

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The positivity-free Agmon cut chain -/

/-- The `m`-level Agmon chain of `InterpTraceCore`, without the positivity hypothesis on `m`:
the degenerate case is removed by applying the positive version to `m + δ·sin²(2θ)` and letting
`δ → 0⁺`. -/
theorem agmonChainShift
    (hAgmon : ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      (1 / 200) * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
          + 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ))
    {m P A B : ℝ → ℝ}
    (hm : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt m (2 * P θ) θ)
    (hP : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt P (A θ + B θ) θ)
    (hAB : ContinuousOn (fun θ : ℝ => A θ + B θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hmnn : ∀ θ : ℝ, 0 ≤ m θ)
    (hAnn : ∀ θ : ℝ, 0 ≤ A θ)
    (hCS : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), P θ ^ 2 ≤ m θ * A θ)
    (htr0 : Filter.Tendsto m (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htr1 : Filter.Tendsto m (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hA : MeasureTheory.IntegrableOn (fun θ : ℝ => A θ
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hmI : MeasureTheory.IntegrableOn (fun θ : ℝ => m θ
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn (fun θ : ℝ => B θ
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (1 / 200) * (∫ θ in Work.Spaces.Iθ, A θ * Work.FTS.EllipticEst.thEta θ)
      ≤ 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, m θ * Work.FTS.EllipticEst.thEta θ)
        - ∫ θ in Work.Spaces.Iθ, B θ * Work.FTS.EllipticEst.thEta θ := by
  -- the σ-integrable bounded angular factors
  have hσint : MeasureTheory.IntegrableOn Work.FTS.EllipticEst.thEta Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableOn_thEta.1
  have hsint0 : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
      * (Real.sin (2 * θ)) ^ 2) Work.Spaces.Iθ :=
    hσint.mul_continuousOn
      (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2).continuousOn)
      isCompact_Icc
  have hsint : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    hsint0.congr (Filter.Eventually.of_forall (fun θ => by ring))
  have hcint0 : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
      * (4 * (Real.cos (2 * θ)) ^ 2)) Work.Spaces.Iθ :=
    hσint.mul_continuousOn
      ((continuous_const.mul
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2)).continuousOn)
      isCompact_Icc
  have hcint : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    hcint0.congr (Filter.Eventually.of_forall (fun θ => by ring))
  have h4int0 : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
      * (4 * Real.cos (4 * θ))) Work.Spaces.Iθ :=
    hσint.mul_continuousOn
      ((continuous_const.mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).continuousOn)
      isCompact_Icc
  have h4int : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (4 * Real.cos (4 * θ)) * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    h4int0.congr (Filter.Eventually.of_forall (fun θ => by ring))
  -- the slack constant and the target value
  set Λ : ℝ := 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      - (∫ θ in Work.Spaces.Iθ, (4 * Real.cos (4 * θ)) * Work.FTS.EllipticEst.thEta θ)
      + (199 / 200) * (∫ θ in Work.Spaces.Iθ,
        (4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ) with hΛ
  set M0 : ℝ := 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ,
        m θ * Work.FTS.EllipticEst.thEta θ)
      - ∫ θ in Work.Spaces.Iθ, B θ * Work.FTS.EllipticEst.thEta θ with hM0
  have hlim : Filter.Tendsto (fun δ : ℝ => M0 + δ * Λ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds M0) := by
    have h0 : Filter.Tendsto (fun δ : ℝ => δ * Λ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (0 * Λ)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds
    have h1 : Filter.Tendsto (fun δ : ℝ => M0 + δ * Λ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (M0 + 0 * Λ)) := tendsto_const_nhds.add h0
    simpa using h1
  -- the per-δ bound
  have key : ∀ δ : ℝ, 0 < δ → (1 / 200) * (∫ θ in Work.Spaces.Iθ,
        A θ * Work.FTS.EllipticEst.thEta θ) ≤ M0 + δ * Λ := by
    intro δ hδ
    -- the regularised data
    set mm : ℝ → ℝ := fun θ => m θ + δ * (Real.sin (2 * θ)) ^ 2 with hmm
    set PP : ℝ → ℝ := fun θ => P θ + δ * Real.sin (4 * θ) with hPP
    set AA : ℝ → ℝ := fun θ => A θ + δ * (4 * (Real.cos (2 * θ)) ^ 2) with hAA
    set BB : ℝ → ℝ := fun θ => B θ
      + δ * (4 * Real.cos (4 * θ) - 4 * (Real.cos (2 * θ)) ^ 2) with hBB
    -- σ-integrability of the shifted summands
    have hmmI : MeasureTheory.IntegrableOn (fun θ : ℝ => mm θ
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
      rw [hmm]
      have h' : (fun θ : ℝ => (m θ + δ * (Real.sin (2 * θ)) ^ 2)
          * Work.FTS.EllipticEst.thEta θ)
          = fun θ : ℝ => m θ * Work.FTS.EllipticEst.thEta θ
            + δ * ((Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
        funext θ; ring
      rw [h']
      exact hmI.add (hsint.const_mul δ)
    have hAAI : MeasureTheory.IntegrableOn (fun θ : ℝ => AA θ
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
      rw [hAA]
      have h' : (fun θ : ℝ => (A θ + δ * (4 * (Real.cos (2 * θ)) ^ 2))
          * Work.FTS.EllipticEst.thEta θ)
          = fun θ : ℝ => A θ * Work.FTS.EllipticEst.thEta θ
            + δ * ((4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ) := by
        funext θ; ring
      rw [h']
      exact hA.add (hcint.const_mul δ)
    have hBBI : MeasureTheory.IntegrableOn (fun θ : ℝ => BB θ
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
      rw [hBB]
      have h' : (fun θ : ℝ => (B θ + δ * (4 * Real.cos (4 * θ)
          - 4 * (Real.cos (2 * θ)) ^ 2)) * Work.FTS.EllipticEst.thEta θ)
          = fun θ : ℝ => B θ * Work.FTS.EllipticEst.thEta θ
            + δ * ((4 * Real.cos (4 * θ)) * Work.FTS.EllipticEst.thEta θ)
            - δ * ((4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ) := by
        funext θ; ring
      rw [h']
      exact (hB.add (h4int.const_mul δ)).sub (hcint.const_mul δ)
    -- the derivative facts
    have hmm' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt mm (2 * PP θ) θ := by
      intro θ hθ
      have h := (hm θ hθ).add ((hasDerivAt_sinSq θ).const_mul δ)
      have hs4 : Real.sin (4 * θ) = 2 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
        rw [show (4 : ℝ) * θ = 2 * (2 * θ) by ring, Real.sin_two_mul]
      have hv : 2 * P θ + δ * (4 * Real.sin (2 * θ) * Real.cos (2 * θ))
          = 2 * (P θ + δ * Real.sin (4 * θ)) := by
        rw [hs4]; ring
      rw [hv] at h
      exact h
    have hPP' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt PP (AA θ + BB θ) θ := by
      intro θ hθ
      have h := (hP θ hθ).add ((hasDerivAt_sinFour θ).const_mul δ)
      have hv : A θ + B θ + δ * (4 * Real.cos (4 * θ))
          = (A θ + δ * (4 * (Real.cos (2 * θ)) ^ 2))
            + (B θ + δ * (4 * Real.cos (4 * θ) - 4 * (Real.cos (2 * θ)) ^ 2)) := by ring
      rw [hv] at h
      exact h
    have hAB' : ContinuousOn (fun θ : ℝ => AA θ + BB θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have hc : Continuous (fun θ : ℝ => 4 * Real.cos (4 * θ)) :=
        continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      have hcont : ContinuousOn (fun θ : ℝ => (A θ + B θ) + δ * (4 * Real.cos (4 * θ)))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hAB.add (hc.const_mul δ).continuousOn
      refine hcont.congr (fun θ _ => ?_)
      rw [hAA, hBB]; ring
    have hmpos' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < mm θ := by
      intro θ hθ
      rw [hmm]
      have hs : 0 < (Real.sin (2 * θ)) ^ 2 :=
        pow_pos (Work.FTS.EllipticEst.sin_two_pos hθ) 2
      nlinarith [hmnn θ, hδ, hs]
    have hCS' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), PP θ ^ 2 ≤ mm θ * AA θ := by
      intro θ hθ
      rw [hmm, hPP, hAA]
      have hm0 : 0 ≤ m θ := hmnn θ
      have hA0 : 0 ≤ A θ := hAnn θ
      have hPbd : |P θ| ≤ Real.sqrt (m θ) * Real.sqrt (A θ) := by
        have h1 : P θ ^ 2 ≤ (Real.sqrt (m θ) * Real.sqrt (A θ)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hm0, Real.sq_sqrt hA0]
          exact hCS θ hθ
        calc |P θ| = Real.sqrt (P θ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt ((Real.sqrt (m θ) * Real.sqrt (A θ)) ^ 2) := Real.sqrt_le_sqrt h1
          _ = |Real.sqrt (m θ) * Real.sqrt (A θ)| := Real.sqrt_sq_eq_abs _
          _ = Real.sqrt (m θ) * Real.sqrt (A θ) :=
              abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      have hw : 0 ≤ Real.sin (2 * θ) := (Work.FTS.EllipticEst.sin_two_pos hθ).le
      have hs4 : Real.sin (4 * θ) = 2 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
        rw [show (4 : ℝ) * θ = 2 * (2 * θ) by ring, Real.sin_two_mul]
      have hstep1 : |P θ + δ * Real.sin (4 * θ)|
          ≤ |P θ| + δ * (2 * Real.sin (2 * θ) * |Real.cos (2 * θ)|) := by
        calc |P θ + δ * Real.sin (4 * θ)|
            ≤ |P θ| + |δ * Real.sin (4 * θ)| := abs_add_le _ _
          _ = |P θ| + δ * |Real.sin (4 * θ)| := by rw [abs_mul, abs_of_pos hδ]
          _ = |P θ| + δ * (2 * Real.sin (2 * θ) * |Real.cos (2 * θ)|) := by
              rw [hs4, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
                abs_of_nonneg hw]
      have hstep2 : (P θ + δ * Real.sin (4 * θ)) ^ 2
          ≤ (Real.sqrt (m θ) * Real.sqrt (A θ)
            + δ * (2 * Real.sin (2 * θ) * |Real.cos (2 * θ)|)) ^ 2 := by
        have hb : 0 ≤ Real.sqrt (m θ) * Real.sqrt (A θ)
            + δ * (2 * Real.sin (2 * θ) * |Real.cos (2 * θ)|) := by positivity
        have h1 : |P θ + δ * Real.sin (4 * θ)| ≤ Real.sqrt (m θ) * Real.sqrt (A θ)
            + δ * (2 * Real.sin (2 * θ) * |Real.cos (2 * θ)|) := by linarith [hstep1, hPbd]
        calc (P θ + δ * Real.sin (4 * θ)) ^ 2
            = |P θ + δ * Real.sin (4 * θ)| ^ 2 := (sq_abs _).symm
          _ ≤ (Real.sqrt (m θ) * Real.sqrt (A θ)
                + δ * (2 * Real.sin (2 * θ) * |Real.cos (2 * θ)|)) ^ 2 := by
              rw [pow_two, pow_two]
              exact mul_self_le_mul_self (abs_nonneg _) h1
      have hstep3 : (Real.sqrt (m θ) * Real.sqrt (A θ)
            + δ * (2 * Real.sin (2 * θ) * |Real.cos (2 * θ)|)) ^ 2
          ≤ (m θ + δ * (Real.sin (2 * θ)) ^ 2)
            * (A θ + δ * (4 * (Real.cos (2 * θ)) ^ 2)) := by
        have h1 : Real.sqrt (m θ) ^ 2 = m θ := Real.sq_sqrt hm0
        have h2 : Real.sqrt (A θ) ^ 2 = A θ := Real.sq_sqrt hA0
        have h3 : |Real.cos (2 * θ)| ^ 2 = (Real.cos (2 * θ)) ^ 2 := sq_abs _
        have hgen : ∀ u v w c e : ℝ, (u * v + e * (2 * w * c)) ^ 2
            = (u ^ 2 + e * w ^ 2) * (v ^ 2 + 4 * e * c ^ 2)
              - e * (2 * c * u - w * v) ^ 2 := by
          intro u v w c e; ring
        have hgen' := hgen (Real.sqrt (m θ)) (Real.sqrt (A θ)) (Real.sin (2 * θ))
          |Real.cos (2 * θ)| δ
        rw [h1, h2, h3] at hgen'
        rw [hgen']
        have hnn : 0 ≤ δ * (2 * |Real.cos (2 * θ)| * Real.sqrt (m θ)
            - Real.sin (2 * θ) * Real.sqrt (A θ)) ^ 2 :=
          mul_nonneg hδ.le (sq_nonneg _)
        linarith
      exact le_trans hstep2 hstep3
    -- the chain applied to the regularised data
    have htr0' : Filter.Tendsto mm (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hc : Continuous (fun θ : ℝ => δ * (Real.sin (2 * θ)) ^ 2) :=
        continuous_const.mul
          ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2)
      have h1 : Filter.Tendsto (fun θ : ℝ => δ * (Real.sin (2 * θ)) ^ 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa [hmm] using htr0.add h1
    have htr1' : Filter.Tendsto mm (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds 0) := by
      have hc : Continuous (fun θ : ℝ => δ * (Real.sin (2 * θ)) ^ 2) :=
        continuous_const.mul
          ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2)
      have h1 : Filter.Tendsto (fun θ : ℝ => δ * (Real.sin (2 * θ)) ^ 2)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        have h0 : (Real.sin (2 * (Real.pi / 2))) ^ 2 = 0 := by
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]; norm_num
        have hgoal : Filter.Tendsto (fun θ : ℝ => δ * (Real.sin (2 * θ)) ^ 2)
            (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
            (nhds (δ * (Real.sin (2 * (Real.pi / 2))) ^ 2)) :=
          (hc.tendsto (Real.pi / 2)).mono_left
            (nhdsWithin_le_nhds : 𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2) ≤ 𝓝 (Real.pi / 2))
        simpa [h0] using hgoal
      simpa [hmm] using htr1.add h1
    have hshift := agmonCutChainPos hAgmon (m := mm) (P := PP) (A := AA) (B := BB)
      hmm' hPP' hAB' hmpos' hCS' htr0' htr1' hAAI hmmI hBBI
    -- the three integral identities
    have eAA : (∫ θ in Work.Spaces.Iθ, AA θ * Work.FTS.EllipticEst.thEta θ)
        = (∫ θ in Work.Spaces.Iθ, A θ * Work.FTS.EllipticEst.thEta θ)
          + δ * (∫ θ in Work.Spaces.Iθ,
              (4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ) := by
      rw [hAA]
      rw [show (fun θ : ℝ => (A θ + δ * (4 * (Real.cos (2 * θ)) ^ 2))
            * Work.FTS.EllipticEst.thEta θ)
          = fun θ : ℝ => A θ * Work.FTS.EllipticEst.thEta θ
            + δ * ((4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ) from by
        funext θ; ring]
      rw [MeasureTheory.integral_add hA (hcint.const_mul δ), MeasureTheory.integral_const_mul]
    have emm : (∫ θ in Work.Spaces.Iθ, mm θ * Work.FTS.EllipticEst.thEta θ)
        = (∫ θ in Work.Spaces.Iθ, m θ * Work.FTS.EllipticEst.thEta θ)
          + δ * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
      rw [hmm]
      rw [show (fun θ : ℝ => (m θ + δ * (Real.sin (2 * θ)) ^ 2)
            * Work.FTS.EllipticEst.thEta θ)
          = fun θ : ℝ => m θ * Work.FTS.EllipticEst.thEta θ
            + δ * ((Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) from by
        funext θ; ring]
      rw [MeasureTheory.integral_add hmI (hsint.const_mul δ), MeasureTheory.integral_const_mul]
    have eBB : (∫ θ in Work.Spaces.Iθ, BB θ * Work.FTS.EllipticEst.thEta θ)
        = (∫ θ in Work.Spaces.Iθ, B θ * Work.FTS.EllipticEst.thEta θ)
          + δ * (∫ θ in Work.Spaces.Iθ,
              (4 * Real.cos (4 * θ)) * Work.FTS.EllipticEst.thEta θ)
          - δ * (∫ θ in Work.Spaces.Iθ,
              (4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ) := by
      have hI2 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
          δ * ((4 * Real.cos (4 * θ)) * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iθ :=
        h4int.const_mul δ
      have hI3 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
          -(δ * ((4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ)))
          Work.Spaces.Iθ := (hcint.const_mul δ).neg
      have hI23 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
          δ * ((4 * Real.cos (4 * θ)) * Work.FTS.EllipticEst.thEta θ)
            + (-(δ * ((4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ))))
          Work.Spaces.Iθ := hI2.add hI3
      rw [hBB]
      rw [show (fun θ : ℝ => (B θ + δ * (4 * Real.cos (4 * θ)
            - 4 * (Real.cos (2 * θ)) ^ 2)) * Work.FTS.EllipticEst.thEta θ)
          = fun θ : ℝ => B θ * Work.FTS.EllipticEst.thEta θ
            + (δ * ((4 * Real.cos (4 * θ)) * Work.FTS.EllipticEst.thEta θ)
              + (-(δ * ((4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ)))) from by
        funext θ; ring]
      rw [MeasureTheory.integral_add hB hI23]
      rw [MeasureTheory.integral_add hI2 hI3]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_neg,
        MeasureTheory.integral_const_mul]
      ring
    rw [eAA, emm, eBB] at hshift
    rw [hM0, hΛ]
    linarith [hshift]
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact key δ hδ)

end Work.FTS.EllSol.PkgK5.TraceEngine
end
end
-- ===== merged: Submission.Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

/-
# The `j`-th slice group of the `ℋ^k`-integrand, rewritten through a single slice

`Work.FTS.EllipticEst.sliceGroup α k j f z θ` is the `j`-th group of
`Work.Spaces.HkIntegrand α k f z θ`: its radial summand `(D_z^j f z θ · w z/sin(2θ)^{η/2})²` plus
the mixed summands `(mixed j i f z θ · Wt α z θ)²` for `1 ≤ i ≤ k-j`; the integrand is the sum of
the groups over `j ≤ k` (`Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum`).
Claim: for `z > 0`, `θ ∈ (0,π/2)` and `f` of class `C^∞` on the open quadrant,

  `sliceGroup α k j f z θ = (w z)² · sliceW (k-j) α (fun θ' => D_z^j f z θ') θ`,

where `sliceW K α u θ = (u θ)²·thEta θ + ∑_{1≤i≤K}(L^i u θ)²·thGam α θ` is the single-slice
functional of `Submission/Work/FTS/EllSol/VopAux/SliceTraceDefs.lean` and `L^i = LopIter i` is the
iterate of `D_θ = sin(2θ)∂_θ`.

ROUTE: unfold `sliceGroup`, rewrite the two weight squares with
`Work.FTS.EllipticEst.w_div_sin_sq` and `Work.FTS.EllipticEst.Wt_sq` (both in
`Submission/Work/FTS/EllipticEst/SliceAux.lean`), and identify
`mixed j i f z θ = LopIter i (fun θ' => D_z^j f z θ') θ` for `θ ∈ (0,π/2)`, which is
`Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open` (open-quadrant commutation, in
`Submission/Work/FTS/EllipticEst/SliceDecompDefs.lean`) combined with
`Work.FTS.EllipticEst.LopIter_slice` (which identifies the `D_θ`-iterate of a `z`-slice with the
`L`-iterate of the one-variable slice). The hypothesis `0 < z` is needed exactly because the
commutation is available on the open quadrant only. The mixed indices of the group run over
`Finset.Icc 1 (k-j)`, matching `sliceW (k-j)`.
-/
theorem sliceGroup_eq_sliceW (α : ℝ) (k j : ℕ) (f : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.sliceGroup α k j f z θ
        = (Work.Spaces.w z) ^ 2
            * Work.FTS.EllSol.VopAux.sliceW (k - j) α
                (fun θ' => Work.Spaces.DzIter j f z θ') θ := by
  intro θ hθ
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- the `L`-iterate of the `z`-slice is the mixed derivative
  have hmixed : ∀ i : ℕ,
      Work.FTS.EllipticEst.LopIter i (fun θ' => Work.Spaces.DzIter j f z θ') θ
        = Work.Spaces.mixed j i f z θ := by
    intro i
    have hLS := congrFun (Work.FTS.EllipticEst.LopIter_slice i (Work.Spaces.DzIter j f) z) θ
    rw [hLS]
    exact Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open hf j i hz hθ
  rw [Work.FTS.EllipticEst.sliceGroup, Work.FTS.EllSol.VopAux.sliceW]
  -- the radial summand, rewritten with the weight identity
  have hrad := Work.FTS.EllipticEst.rad_term_eq hθIθ z (Work.Spaces.DzIter j f z θ)
  -- the mixed summands, rewritten with the weight identity and the `L`-iterate
  have hsum : (∑ i ∈ Finset.Icc 1 (k - j),
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = (Work.Spaces.w z) ^ 2 * ∑ i ∈ Finset.Icc 1 (k - j),
          (Work.FTS.EllipticEst.LopIter i (fun θ' => Work.Spaces.DzIter j f z θ') θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Work.FTS.EllipticEst.mix_term_eq hθIθ α z (Work.Spaces.mixed j i f z θ),
      ← hmixed i, Work.FTS.EllipticEst.sGam_eq_thGam]
  rw [hrad, hsum, Work.FTS.EllipticEst.sEta_eq_thEta, mul_add]

end Work.FTS.EllSol.VopAux
end
-- ===== merged: Submission.Work.FTS.EllSol.hkMem_slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol

open MeasureTheory Set Filter
open scoped Real Topology

/-- For `z > 0` the squared radial weight `w(z)²` does not vanish, so that the weighted
summands of the `ℋ^k`-integrand (which carry a factor `w(z)²` relative to the honest
`η`- resp. `γ`-weighted squares) can be un-weighted by multiplying with its inverse. -/
private theorem w_sq_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : (Work.Spaces.w z) ^ 2 ≠ 0 := by
  rw [Work.Spaces.w]
  exact pow_ne_zero 2
    (div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz)))

theorem hkMem_slots (α : ℝ) (k : ℕ) {Φ : ℝ → ℝ → ℝ}
    (hSO : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pth Φ))
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) (hzpos : 0 < z) (hα : 0 < α) :
    (∀ i : ℕ, i ≤ k → MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ)
    ∧ (∀ i j : ℕ, 1 ≤ i → i + j ≤ k → MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)) Work.Spaces.Iθ) := by
  have hf : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth Φ) := hSO.pth
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := w_sq_ne_zero_of_pos hzpos
  -- un-weighting by the nonvanishing constant `(w z)²`
  have hstrip : ∀ (u : ℝ → ℝ),
      IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2 * u θ) Work.Spaces.Iθ →
      IntegrableOn u Work.Spaces.Iθ := by
    intro u hu
    refine MeasureTheory.IntegrableOn.congr_fun (hu.const_mul (((Work.Spaces.w z) ^ 2)⁻¹))
      (fun θ _ => ?_) hmeasIθ
    rw [← mul_assoc, inv_mul_cancel₀ hwne, one_mul]
  constructor
  · intro i hi
    -- `(D_z^i ∂_θΦ · w/sin^{η/2})²` is `θ`-integrable by the open-quadrant `ℋ^k`-membership
    have h1 : IntegrableOn (fun θ => (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.integrableOn_zSummand α k hf hmem i hi hz
    -- which is `w(z)²` times the `η`-weighted square of `D_z^i ∂_θΦ`
    have h2 : IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2
        * ((Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iθ :=
      MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ =>
        Work.FTS.EllipticEst.rad_term_eq hθ z (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ))
        hmeasIθ
    simpa only [Work.FTS.EllipticEst.sEta] using
      hstrip (fun θ => (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) h2
  · intro i j hi hij
    -- the mixed summand `(D_z^j D_θ^i ∂_θΦ · Wt)²` is `θ`-integrable as well
    have h1 : IntegrableOn (fun θ => (Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ
        * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.integrableOn_mixedSummand α k hf hmem i j hi hij hz
    -- and it is `w(z)²` times the `γ`-weighted square of the mixed derivative
    have h2 : IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2
        * ((Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ) ^ 2
          * Work.FTS.EllipticEst.sGam α θ)) Work.Spaces.Iθ :=
      MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ => Work.FTS.EllipticEst.mix_term_eq hθ α z
        (Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ)) hmeasIθ
    simpa only [Work.FTS.EllipticEst.sGam] using
      hstrip (fun θ => (Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ) ^ 2
        * Work.FTS.EllipticEst.sGam α θ) h2

end Work.FTS.EllSol
end
-- ===== merged: Submission.Work.FTS.EllSol.shiftReduceDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol

open MeasureTheory Set
open scoped Real

noncomputable section

set_option autoImplicit false

/-- The `Ω`-weight of the target, `Ω(t) = (1 + e^t)^4 e^{-3t}` (the paper's `Wt`). -/
def omegaAux (t : ℝ) : ℝ := (1 + Real.exp t) ^ 4 * Real.exp (-(3 * t))





end

end Work.FTS.EllSol
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Asm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

set_option autoImplicit false

theorem integral_nonneg_of_ae' {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict s), 0 ≤ f x) :
    0 ≤ ∫ x in s, f x := by
  by_cases h : Integrable f (volume.restrict s)
  · exact integral_nonneg_of_ae hf
  · rw [integral_undef h]

/-- **The truncated identity** — the radial IBP of `truncZIbp2` combined with the sliced
`θ`-identity of `truncThetaIbpSep_split`:

`D_χψ = −Tr_χψ + 2η·A_χψ + κ·P_χψ + (2η/(1+η))·Def_χψ − ½·W_χψ`. -/
theorem truncIdentity (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Set.Ioi (0:ℝ))
    (hχsupp' : Function.support χ ⊆ Set.Ioi (0:ℝ))
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hψsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ tsupport ψ ⊆ Set.Ioo a b)
    (hψsep1 : tsupport ψ ⊆ Set.Ioo 0 (Real.pi / 2))
    (ho1 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (z * Work.Spaces.pz u z θ)^2))
      (Set.Ioi 0))
    (ho2 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2))
      (Set.Ioi 0))
    (ho3 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
              - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2))
      (Set.Ioi 0))
    (ho4 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
          * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2))
      (Set.Ioi 0)) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), χ z * (Work.Spaces.w z)^2
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z^2 * Work.Spaces.pzIter 2 u z θ) * (Work.Spaces.pthIter 2 u z θ))
      = - (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
            (deriv (fun z' => χ z' * (Work.Spaces.w z')^2 * z'^2) z / z)
              * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
              * (z * Work.Spaces.pz u z θ) * (Work.Spaces.pthIter 2 u z θ))
        + 2 * Work.Spaces.eta * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                * (z * Work.Spaces.pz u z θ)^2))
        + ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2))
        + (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
                    - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                      * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2))
        - (1/2) * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
                * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2)) := by
  have h1 := truncZIbp2 u χ ψ hu hχ hχc hχsupp (hψ.of_le (by norm_num)) hψsep1
  have h4 := truncThetaIbpSep_split u χ ψ hu hχ hχc hχsupp' hψ hψc hψsep ho1 ho2 ho3 ho4
  linarith [h1, h4]


/-- The `θ`-inner integral of a nonnegative integrand is nonnegative (on `Ioo 0 (π/2)`). -/
theorem inner_nonneg {f : ℝ → ℝ} (hf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ f θ) :
    0 ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), f θ := by
  refine integral_nonneg_of_ae' ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Eventually.of_forall fun θ hθ => hf θ hθ








/-- `|cw z| ≤ 2` for `z ≥ 0`. -/
theorem abs_cw_le_two {z : ℝ} (hz : 0 ≤ z) : |2*(z-1)/(1+z)| ≤ 2 := by
  have h1 : 0 < 1 + z := by linarith
  rw [abs_div, abs_mul, abs_of_pos h1, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [div_le_iff₀ h1]
  have : |z - 1| ≤ z + 1 := by
    rw [abs_le]; constructor <;> linarith
  linarith

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.InterpBrickAux.hkDensity_prod_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.InterpBrickAux

/-- **The `ℋ⁰`-density of a function of `SmoothOpen` is the unweighted density.**
For `θ ∈ Iθ = [0,π/2]` the `k = 0` integrand reduces to
`(F z θ)² · w(z)² · sin(2θ)^{-η}`: the plain `D_z^0 = id` term is the only one occurring
(no mixed derivative appears at level `0`), and the `θ`-weight square
`(sin(2θ)^{η/2})² = sin(2θ)^{η}` is converted using `sin(2θ) ≥ 0`. -/
private theorem hkDensity_pointwise (α : ℝ) (F : ℝ → ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) ?_
    have := Real.pi_pos
    linarith [hθ.2]
  -- `(sin(2θ)^{η/2})² = sin(2θ)^{η}`
  have hpow : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Real.sin (2 * θ) ^ Work.Spaces.eta := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    congr 1
    ring
  -- `sin(2θ)^{-η} = (sin(2θ)^{η})⁻¹`
  have hneg : Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
      = (Real.sin (2 * θ) ^ Work.Spaces.eta)⁻¹ :=
    Real.rpow_neg hs Work.Spaces.eta
  simp only [Work.Spaces.HkIntegrand]
  norm_num [Finset.sum_range_one]
  rw [mul_pow, div_pow, hpow, div_eq_mul_inv, hneg]
  ring

theorem hkDensity_prod_integrable {α : ℝ} {F : ℝ → ℝ → ℝ} (hF : Work.Spaces.HkMem α 0 F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- The `ℋ⁰`-integrand is integrable on the product: nonnegative, continuous on the open
  -- quadrant (so a.e. strongly measurable), with integrable slices and integrable iterated
  -- integral by `HkMem α 0 F`.  This is `integrable_prod_of_iterated`.
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 0 F z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 0 F z θ
  have hAE : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α 0 F z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (hsm.continuousOn_HkIntegrand α 0)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 0 F z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hF.1 z hz
  have houter : MeasureTheory.Integrable
      (fun z => ∫ θ, Work.Spaces.HkIntegrand α 0 F z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hF.2
  obtain ⟨hint, -⟩ := Work.Spaces.integrable_prod_of_iterated hnn hAE hslice houter
  -- On `Iz ×ˢ Iθ` the two densities agree pointwise.
  refine hint.congr ?_
  rw [MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) fun p hp => ?_
  exact hkDensity_pointwise α F hp.2 p.1

end Work.FTS.EllipticEst.Cores.InterpBrickAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.SigABasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. The weight `σ_a` and elementary exponent facts -/

/-- The light angular weight `σ_a α θ = sin(2θ)^{2-γ(α)}` (the abbreviation `TT.sigA`). -/
def sigA (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)

/-- `2 - γ(α) > 0` for `α ≤ 1`: the weight vanishes at both endpoints. -/
lemma sub_gam_pos {α : ℝ} (hα1 : α ≤ 1) : 0 < 2 - Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

/-- `2 - γ(α) < 1` for `α > 0`. -/
lemma sub_gam_lt_one {α : ℝ} (hα : 0 < α) : 2 - Work.Spaces.gam α < 1 := by
  rw [Work.Spaces.gam]; linarith

lemma sigA_pos' {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < sigA α θ :=
  Work.FTS.EllipticEst.TT.sigA_pos α θ hθ

/-- `σ_a` is continuous on `ℝ` (the exponent `2-γ` is positive). -/
lemma sigA_continuous (α : ℝ) (hα1 : α ≤ 1) : Continuous (fun t : ℝ => sigA α t) := by
  change Continuous (fun t : ℝ => (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α))
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
    (fun t => Or.inr (le_of_lt (sub_gam_pos hα1)))

/-- **`σ_a` is invariant under `θ ↦ π/2 - θ`.** -/
lemma sigA_reflect {α y : ℝ} : sigA α (Real.pi / 2 - y) = sigA α y := by
  change (Real.sin (2 * (Real.pi / 2 - y))) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * y)) ^ (2 - Work.Spaces.gam α)
  rw [show 2 * (Real.pi / 2 - y) = Real.pi - 2 * y by ring, Real.sin_pi_sub]

/-- `σ_a θ^{-1} = sin(2θ)^{-(2-γ)}` on the open interval. -/
lemma sigA_inv_eq_partial {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (sigA α θ)⁻¹ = (Real.sin (2 * θ)) ^ (-(2 - Work.Spaces.gam α)) := by
  have hpos : 0 < Real.sin (2 * θ) := Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hθ
  change ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))⁻¹ = _
  exact (Real.rpow_neg hpos.le (2 - Work.Spaces.gam α)).symm

/-- **Integrability of `σ_a^{-1}`** on `[0,π/2]`, by domination with the Jordan majorant
`(π/4)^p (θ^{-p} + (π/2-θ)^{-p})`. -/
lemma integrableOn_sigA_inv {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun t : ℝ => (sigA α t)⁻¹) (Set.Icc 0 (Real.pi / 2)) := by
  have hp0 : 0 < 2 - Work.Spaces.gam α := sub_gam_pos hα1
  have hp1 : 2 - Work.Spaces.gam α < 1 := sub_gam_lt_one hα
  refine MeasureTheory.Integrable.mono'
    (Work.Spaces.integrableOn_majorant_rpow (2 - Work.Spaces.gam α) hp0 hp1) ?_ ?_
  · exact (sigA_continuous α hα1).measurable.inv.aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ?_)
    have hsin : 0 ≤ Real.sin (2 * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
    have hmaj := Work.Spaces.sin_rpow_le_majorant (2 - Work.Spaces.gam α) t hp0 ht
    rcases eq_or_lt_of_le hsin with h0 | hpos
    · have hz : sigA α t = 0 := by
        change (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α) = 0
        rw [← h0, Real.zero_rpow (ne_of_gt hp0)]
      rw [hz, inv_zero, norm_zero]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (add_nonneg (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (by linarith [ht.2]) _))
    · have hval : (sigA α t)⁻¹ = (Real.sin (2 * t)) ^ (-(2 - Work.Spaces.gam α)) := by
        change ((Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α))⁻¹ = _
        exact (Real.rpow_neg hpos.le (2 - Work.Spaces.gam α)).symm
      rw [hval, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)]
      exact hmaj

/-! ## 2. The pointwise AM–GM bound and integrability of `Φ'` -/

/-- `2|x| ≤ x²σ + σ^{-1}` for `σ > 0` (`(x√σ - 1/√σ)² ≥ 0`). -/
lemma two_abs_le_sq_mul_add_inv {σ x : ℝ} (hσ : 0 < σ) : 2 * |x| ≤ x ^ 2 * σ + σ⁻¹ := by
  have hu2 : (Real.sqrt σ) ^ 2 = σ := Real.sq_sqrt hσ.le
  have hu0 : 0 < Real.sqrt σ := Real.sqrt_pos_of_pos hσ
  have h1 : (|x| * Real.sqrt σ) ^ 2 = x ^ 2 * σ := by rw [mul_pow, sq_abs, hu2]
  have h2 : ((Real.sqrt σ)⁻¹) ^ 2 = σ⁻¹ := by rw [inv_pow, hu2]
  have h3 : (|x| * Real.sqrt σ) * (Real.sqrt σ)⁻¹ = |x| := by
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hu0), mul_one]
  have h4 := two_mul_le_add_sq (|x| * Real.sqrt σ) ((Real.sqrt σ)⁻¹)
  rw [h1, h2] at h4
  rw [mul_assoc, h3] at h4
  exact h4

/-- **Integrability of `Φ'`** on any `s ⊆ (0,π/2)` where both `(Φ')²σ_a` and `σ_a^{-1}` are
integrable (AM–GM). -/
lemma integrableOn_deriv {α : ℝ} {Φ : ℝ → ℝ} {s : Set ℝ}
    (hsm : MeasurableSet s) (hs : s ⊆ Set.Ioo 0 (Real.pi / 2))
    (hA : IntegrableOn (fun t => (deriv Φ t) ^ 2 * sigA α t) s)
    (hB : IntegrableOn (fun t => (sigA α t)⁻¹) s) :
    IntegrableOn (deriv Φ) s := by
  have hdom : Integrable (fun t => (deriv Φ t) ^ 2 * sigA α t + (sigA α t)⁻¹)
      (volume.restrict s) := hA.add hB
  refine MeasureTheory.Integrable.mono' hdom (measurable_deriv Φ).aestronglyMeasurable ?_
  refine MeasureTheory.ae_restrict_of_forall_mem hsm (fun t ht => ?_)
  have hσ : 0 < sigA α t := sigA_pos' (hs ht)
  have h := two_abs_le_sq_mul_add_inv (σ := sigA α t) (x := deriv Φ t) hσ
  rw [Real.norm_eq_abs]
  linarith [h, abs_nonneg (deriv Φ t)]

/-- **Cauchy–Schwarz for the slice**: `(∫_s Φ')² ≤ (∫_s (Φ')²σ_a)(∫_s σ_a^{-1})`. -/
lemma cs_step {α : ℝ} (hα1 : α ≤ 1) {Φ : ℝ → ℝ} {s : Set ℝ}
    (hsm : MeasurableSet s) (hs : s ⊆ Set.Ioo 0 (Real.pi / 2))
    (hA : IntegrableOn (fun t => (deriv Φ t) ^ 2 * sigA α t) s)
    (hB : IntegrableOn (fun t => (sigA α t)⁻¹) s) :
    (∫ t in s, deriv Φ t) ^ 2
      ≤ (∫ t in s, (deriv Φ t) ^ 2 * sigA α t) * (∫ t in s, (sigA α t)⁻¹) := by
  set u : ℝ → ℝ := fun t => deriv Φ t * Real.sqrt (sigA α t) with hu
  set v : ℝ → ℝ := fun t => (Real.sqrt (sigA α t))⁻¹ with hv
  have hsig : ∀ t ∈ s, 0 < sigA α t := fun t ht => sigA_pos' (hs ht)
  have haesm_u : AEStronglyMeasurable u (volume.restrict s) := by
    rw [hu]
    exact (measurable_deriv Φ).aestronglyMeasurable.mul
      ((sigA_continuous α hα1).sqrt.aestronglyMeasurable)
  have haesm_v : AEStronglyMeasurable v (volume.restrict s) := by
    rw [hv]
    exact ((Continuous.sqrt (sigA_continuous α hα1)).continuousOn.inv₀
      (fun t ht => ne_of_gt (Real.sqrt_pos_of_pos (hsig t ht)))).aestronglyMeasurable hsm
  have huM : MemLp u 2 (volume.restrict s) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq haesm_u]
    refine hA.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem hsm (fun t ht => ?_)
    rw [hu]; simp only []
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hsig t ht))]
  have hvM : MemLp v 2 (volume.restrict s) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq haesm_v]
    refine hB.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem hsm (fun t ht => ?_)
    rw [hv]; simp only []
    rw [inv_pow, Real.sq_sqrt (le_of_lt (hsig t ht))]
  have hcs := Work.Spaces.cs_integral huM hvM
  have h1 : ∫ x in s, u x * v x = ∫ x in s, deriv Φ x := by
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem hsm (fun t ht => ?_)
    rw [hu, hv]; simp only []
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos_of_pos (hsig t ht))), mul_one]
  have h2 : ∫ x in s, u x ^ 2 = ∫ x in s, (deriv Φ x) ^ 2 * sigA α x := by
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem hsm (fun t ht => ?_)
    rw [hu]; simp only []
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hsig t ht))]
  have h3 : ∫ x in s, v x ^ 2 = ∫ x in s, (sigA α x)⁻¹ := by
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem hsm (fun t ht => ?_)
    rw [hv]; simp only []
    rw [inv_pow, Real.sq_sqrt (le_of_lt (hsig t ht))]
  rw [h1, h2, h3] at hcs
  exact hcs

/-! ## 3. The weight bound `∫_0^θ σ_a^{-1} ≤ K θ^{γ-1}` -/

/-- `(π/2 - t)^{-p} ≤ (4/π)^p` for `t ∈ (0,θ)`, `θ ≤ π/4` (`p > 0`). -/
lemma shift_le_const {p t θ : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) θ) (hsmall : θ ≤ Real.pi / 4)
    (hp0 : 0 < p) : (Real.pi / 2 - t) ^ (-p) ≤ (4 / Real.pi) ^ p := by
  have hge : Real.pi / 4 ≤ Real.pi / 2 - t := by linarith [ht.2, hsmall]
  have h1 : (Real.pi / 2 - t) ^ (-p) ≤ (Real.pi / 4) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by linarith [Real.pi_pos]) hge (by linarith)
  have h2 : (Real.pi / 4) ^ (-p) = (4 / Real.pi) ^ p := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ Real.pi / 4) p,
      show (4 : ℝ) / Real.pi = (Real.pi / 4)⁻¹ from by rw [inv_div π 4],
      Real.inv_rpow (by positivity : (0 : ℝ) ≤ Real.pi / 4) p]
  rw [← h2]
  exact h1

/-- Continuity on `(0,θ)` of `t ↦ (π/2-t)^{-p}`, for `θ ≤ π/4`. -/
lemma shift_cont {p θ : ℝ} (hsmall : θ ≤ Real.pi / 4) :
    ContinuousOn (fun t : ℝ => (Real.pi / 2 - t) ^ (-p)) (Set.Ioo (0 : ℝ) θ) :=
  ((continuous_const.sub continuous_id).continuousOn).rpow_const
    (fun t ht => Or.inl (show Real.pi / 2 - t ≠ 0 from by linarith [ht.2, hsmall, Real.pi_pos]))

/-- **The partial weight bound for the singular power weight**: for `0 < p < 1` and
`0 < θ ≤ π/2`,
`∫_{(0,θ)} sin(2t)^{-p} ≤ ((π/4)^p/(1-p) + 1 + (100/(1-p))(π/4)^{p-1}) θ^{1-p}`.

For `θ ≤ π/4` this is the Jordan majorant `sin(2t) ≥ 4t/π` integrated against the power
`t^{-p}`; for `θ ≥ π/4` it is the global bound `∫_0^{π/2} sin(2t)^{-p} ≤ 100/(1-p)`
scaled by `θ^{1-p} ≥ (π/4)^{1-p}`. -/
lemma integral_sin_rpow_neg_partial {p θ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hθ0 : 0 < θ) (hθ : θ ≤ Real.pi / 2) :
    ∫ t in Set.Ioo 0 θ, (Real.sin (2 * t)) ^ (-p)
      ≤ ((Real.pi / 4) ^ p / (1 - p) + 1 + (100 / (1 - p)) * (Real.pi / 4) ^ (p - 1))
          * θ ^ (1 - p) := by
  have hIntIcc : MeasureTheory.IntegrableOn (fun t : ℝ => (Real.sin (2 * t)) ^ (-p))
      (Set.Icc 0 (Real.pi / 2)) :=
    (Work.Spaces.sin_two_rpow (-p) (by linarith) (by linarith)).1
  have hTotal : ∫ t in Set.Icc 0 (Real.pi / 2), (Real.sin (2 * t)) ^ (-p) ≤ 100 / (1 - p) := by
    have h := (Work.Spaces.sin_two_rpow (-p) (by linarith) (by linarith)).2
    have he : (-p : ℝ) + 1 = 1 - p := by ring
    rwa [he] at h
  have hsub : Set.Ioo (0 : ℝ) θ ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun t ht => ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) hθ⟩
  rcases le_or_gt θ (Real.pi / 4) with hsmall | hbig
  · -- ===== Case `θ ≤ π/4` =====
    have hθle1 : θ ≤ 1 := by linarith [hsmall, Real.pi_lt_four]
    have hmajInt : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Real.pi / 4) ^ p * (t ^ (-p) + (Real.pi / 2 - t) ^ (-p)))
        (Set.Ioo 0 θ) :=
      (Work.Spaces.integrableOn_majorant_rpow p hp0 hp1).mono_set hsub
    have hIntθ : MeasureTheory.IntegrableOn (fun t : ℝ => (Real.sin (2 * t)) ^ (-p))
        (Set.Ioo 0 θ) := hIntIcc.mono_set hsub
    have hmono : ∫ t in Set.Ioo 0 θ, (Real.sin (2 * t)) ^ (-p)
        ≤ ∫ t in Set.Ioo 0 θ, (Real.pi / 4) ^ p * (t ^ (-p) + (Real.pi / 2 - t) ^ (-p)) := by
      refine MeasureTheory.integral_mono_ae hIntθ hmajInt ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun t ht => Work.Spaces.sin_rpow_le_majorant p t hp0 (hsub ht))
    have hpowInt : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-p)) (Set.Ioo 0 θ) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hθ0).mpr (by linarith)
    have hshiftInt : MeasureTheory.IntegrableOn (fun t : ℝ => (Real.pi / 2 - t) ^ (-p))
        (Set.Ioo 0 θ) := by
      have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (4 / Real.pi) ^ p) (Set.Ioo 0 θ) :=
        MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      refine MeasureTheory.Integrable.mono' hconst ?_ ?_
      · exact (shift_cont hsmall).aestronglyMeasurable measurableSet_Ioo
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => ?_)
        rw [Real.norm_of_nonneg (Real.rpow_nonneg
          (by linarith [ht.2, hsmall, Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - t) _)]
        exact shift_le_const ht hsmall hp0
    have hsplit : ∫ t in Set.Ioo 0 θ, ((Real.pi / 4) ^ p * (t ^ (-p) + (Real.pi / 2 - t) ^ (-p)))
        = (Real.pi / 4) ^ p * ((∫ t in Set.Ioo 0 θ, t ^ (-p))
            + ∫ t in Set.Ioo 0 θ, (Real.pi / 2 - t) ^ (-p)) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hpowInt hshiftInt]
    have hI1 : ∫ t in Set.Ioo 0 θ, t ^ (-p) = θ ^ (1 - p) / (1 - p) := by
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hθ0.le]
      rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -p))]
      rw [show (-p + 1 : ℝ) = 1 - p by ring, Real.zero_rpow (by linarith : (1 - p) ≠ 0)]
      ring
    have hI2 : ∫ t in Set.Ioo 0 θ, (Real.pi / 2 - t) ^ (-p) ≤ θ * (4 / Real.pi) ^ p := by
      have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (4 / Real.pi) ^ p) (Set.Ioo 0 θ) :=
        MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      have hcmp : ∫ t in Set.Ioo 0 θ, (Real.pi / 2 - t) ^ (-p)
          ≤ ∫ t in Set.Ioo 0 θ, ((4 / Real.pi) ^ p) := by
        refine MeasureTheory.integral_mono_ae hshiftInt hconst ?_
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun t ht => shift_le_const ht hsmall hp0)
      have hval : ∫ t in Set.Ioo 0 θ, ((4 / Real.pi) ^ p) = θ * (4 / Real.pi) ^ p := by
        rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hθ0.le,
          intervalIntegral.integral_const, sub_zero]
        simp [smul_eq_mul]
      linarith [hcmp, hval.le, hval.ge]
    have hcancel : (Real.pi / 4) ^ p * (4 / Real.pi) ^ p = 1 := by
      rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ Real.pi / 4)
          (by positivity : (0 : ℝ) ≤ 4 / Real.pi),
        show Real.pi / 4 * (4 / Real.pi) = 1 from by field_simp, Real.one_rpow]
    have hθpow : θ ≤ θ ^ (1 - p) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hθ0 hθle1 (show (1 : ℝ) - p ≤ 1 by linarith)
      simpa using h
    have hcoef1 : (0 : ℝ) ≤ (Real.pi / 4) ^ p / (1 - p) :=
      div_nonneg (Real.rpow_nonneg (by positivity) _) (by linarith)
    have hstep : (Real.pi / 4) ^ p * (θ ^ (1 - p) / (1 - p) + θ * (4 / Real.pi) ^ p)
        ≤ ((Real.pi / 4) ^ p / (1 - p) + 1) * θ ^ (1 - p) := by
      have h1 : (Real.pi / 4) ^ p * (θ * (4 / Real.pi) ^ p) = θ := by
        rw [mul_comm θ (((4 : ℝ) / Real.pi) ^ p), ← mul_assoc, hcancel, one_mul]
      have hkey : (Real.pi / 4) ^ p * (θ ^ (1 - p) / (1 - p))
          = ((Real.pi / 4) ^ p / (1 - p)) * θ ^ (1 - p) := by ring
      rw [mul_add, h1, hkey]
      have hB : (0 : ℝ) ≤ θ ^ (1 - p) := Real.rpow_nonneg hθ0.le _
      nlinarith [hcoef1, hθpow, hB]
    have hfin : ((Real.pi / 4) ^ p / (1 - p) + 1) * θ ^ (1 - p)
        ≤ ((Real.pi / 4) ^ p / (1 - p) + 1 + (100 / (1 - p)) * (Real.pi / 4) ^ (p - 1))
            * θ ^ (1 - p) := by
      have hnn : (0 : ℝ) ≤ (100 / (1 - p)) * (Real.pi / 4) ^ (p - 1) :=
        mul_nonneg (div_nonneg (by norm_num) (by linarith)) (Real.rpow_nonneg (by positivity) _)
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hθ0.le _)
    calc ∫ t in Set.Ioo 0 θ, (Real.sin (2 * t)) ^ (-p)
        ≤ ∫ t in Set.Ioo 0 θ, (Real.pi / 4) ^ p
            * (t ^ (-p) + (Real.pi / 2 - t) ^ (-p)) := hmono
      _ = (Real.pi / 4) ^ p * ((∫ t in Set.Ioo 0 θ, t ^ (-p))
            + ∫ t in Set.Ioo 0 θ, (Real.pi / 2 - t) ^ (-p)) := hsplit
      _ ≤ (Real.pi / 4) ^ p * (θ ^ (1 - p) / (1 - p) + θ * (4 / Real.pi) ^ p) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
          exact add_le_add hI1.le hI2
      _ ≤ ((Real.pi / 4) ^ p / (1 - p) + 1) * θ ^ (1 - p) := hstep
      _ ≤ _ := hfin
  · -- ===== Case `θ ≥ π/4` =====
    have hmono : ∫ t in Set.Ioo 0 θ, (Real.sin (2 * t)) ^ (-p)
        ≤ ∫ t in Set.Icc 0 (Real.pi / 2), (Real.sin (2 * t)) ^ (-p) := by
      refine MeasureTheory.setIntegral_mono_set hIntIcc ?_ ?_
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun t ht => Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
            (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])) _)
      · exact MeasureTheory.ae_le_set.mpr (by rw [Set.sdiff_eq_empty.mpr hsub, measure_empty])
    have h1 : (Real.pi / 4) ^ (p - 1) * θ ^ (1 - p) = (θ / (Real.pi / 4)) ^ (1 - p) := by
      rw [Real.div_rpow hθ0.le (by positivity : (0 : ℝ) ≤ Real.pi / 4) (1 - p)]
      have hL : (Real.pi / 4) ^ (p - 1) = ((Real.pi / 4) ^ (1 - p))⁻¹ := by
        rw [show p - 1 = -(1 - p) by ring,
          Real.rpow_neg (by positivity : (0 : ℝ) ≤ Real.pi / 4) (1 - p)]
      rw [hL]
      ring
    have hge1 : (1 : ℝ) ≤ (θ / (Real.pi / 4)) ^ (1 - p) :=
      Real.one_le_rpow (by rw [le_div_iff₀ (by linarith [Real.pi_pos])]; linarith) (by linarith)
    have hmain : 100 / (1 - p) ≤ (100 / (1 - p)) * (Real.pi / 4) ^ (p - 1) * θ ^ (1 - p) := by
      rw [mul_assoc, h1]
      exact le_mul_of_one_le_right (div_nonneg (by norm_num) (by linarith)) hge1
    have hbig2 : (100 / (1 - p)) * (Real.pi / 4) ^ (p - 1)
        ≤ (Real.pi / 4) ^ p / (1 - p) + 1 + (100 / (1 - p)) * (Real.pi / 4) ^ (p - 1) := by
      have h2 : (0 : ℝ) ≤ (Real.pi / 4) ^ p / (1 - p) + 1 := by
        have h3 := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) p
        have h4 := div_nonneg h3 (by linarith : (0 : ℝ) ≤ 1 - p)
        linarith
      linarith
    have h2 : 100 / (1 - p) ≤ ((Real.pi / 4) ^ p / (1 - p) + 1
        + (100 / (1 - p)) * (Real.pi / 4) ^ (p - 1)) * θ ^ (1 - p) :=
      hmain.trans (mul_le_mul_of_nonneg_right hbig2 (Real.rpow_nonneg hθ0.le _))
    linarith [hmono, hTotal, h2]

/-- **The weight bound in the form needed downstream**: for `α ∈ (0,1]` and `θ ∈ (0,π/2)`,
`∫_{(0,θ)} σ_a^{-1} ≤ K θ^{γ-1}`. -/
lemma integral_sigA_inv_le_partial (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∫ t in Set.Ioo 0 θ, (sigA α t)⁻¹
      ≤ ((Real.pi / 4) ^ (2 - Work.Spaces.gam α) / (1 - (2 - Work.Spaces.gam α)) + 1
          + (100 / (1 - (2 - Work.Spaces.gam α)))
              * (Real.pi / 4) ^ ((2 - Work.Spaces.gam α) - 1))
        * θ ^ (Work.Spaces.gam α - 1) := by
  have hp0 : 0 < 2 - Work.Spaces.gam α := sub_gam_pos hα1
  have hp1 : 2 - Work.Spaces.gam α < 1 := sub_gam_lt_one hα
  have hcongr : ∫ t in Set.Ioo 0 θ, (sigA α t)⁻¹
      = ∫ t in Set.Ioo 0 θ, (Real.sin (2 * t)) ^ (-(2 - Work.Spaces.gam α)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun t ht => sigA_inv_eq_partial ⟨ht.1, by linarith [ht.2, hθ.2]⟩)
  rw [hcongr]
  have h := integral_sin_rpow_neg_partial (p := 2 - Work.Spaces.gam α) hp0 hp1 hθ.1 hθ.2.le
  have hgam : Work.Spaces.gam α - 1 = 1 - (2 - Work.Spaces.gam α) := by ring
  rwa [hgam]

/-- The same with an existential constant, for a compact statement. -/
lemma integral_sigA_inv_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ KW : ℝ, 0 < KW ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ∫ t in Set.Ioo 0 θ, (sigA α t)⁻¹ ≤ KW * θ ^ (Work.Spaces.gam α - 1) := by
  refine ⟨_, ?_, fun θ hθ => integral_sigA_inv_le_partial α hα hα1 hθ⟩
  have hp0 : 0 < 2 - Work.Spaces.gam α := sub_gam_pos hα1
  have hp1 : 2 - Work.Spaces.gam α < 1 := sub_gam_lt_one hα
  have h1 : (0 : ℝ) < (Real.pi / 4) ^ (2 - Work.Spaces.gam α) / (1 - (2 - Work.Spaces.gam α)) :=
    div_pos (Real.rpow_pos_of_pos (by linarith [Real.pi_pos]) _) (by linarith)
  have h2 : (0 : ℝ) < (100 / (1 - (2 - Work.Spaces.gam α)))
      * (Real.pi / 4) ^ ((2 - Work.Spaces.gam α) - 1) :=
    mul_pos (div_pos (by norm_num) (by linarith))
      (Real.rpow_pos_of_pos (by linarith [Real.pi_pos]) _)
  linarith

/-! ## 4. The reflection `θ ↦ π/2 - θ` -/

/-- **Change of variables** `y ↦ π/2 - y` on the intervals `(0,t)` and `(π/2-t, π/2)`. -/
lemma integral_reflect {g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    ∫ y in Set.Ioo 0 t, g (Real.pi / 2 - y)
      = ∫ x in Set.Ioo (Real.pi / 2 - t) (Real.pi / 2), g x := by
  calc ∫ y in Set.Ioo 0 t, g (Real.pi / 2 - y)
      = ∫ y in (0 : ℝ)..t, g (Real.pi / 2 - y) := by
        rw [intervalIntegral.integral_of_le ht, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    _ = ∫ x in (Real.pi / 2 - t)..(Real.pi / 2), g x := by
        rw [intervalIntegral.integral_comp_sub_left g (Real.pi / 2)]
        simp
    _ = ∫ x in Set.Ioo (Real.pi / 2 - t) (Real.pi / 2), g x := by
        rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
          MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **The mirror weight bound**: `∫_{(θ,π/2)} σ_a^{-1} ≤ K (π/2-θ)^{γ-1}`. -/
lemma integral_sigA_inv_le_right (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ KW : ℝ, 0 < KW ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ∫ t in Set.Ioo θ (Real.pi / 2), (sigA α t)⁻¹
        ≤ KW * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) := by
  obtain ⟨KW, hKW, hKWb⟩ := integral_sigA_inv_le α hα hα1
  refine ⟨KW, hKW, fun θ hθ => ?_⟩
  have h1 : ∫ y in Set.Ioo 0 (Real.pi / 2 - θ), (sigA α (Real.pi / 2 - y))⁻¹
      = ∫ y in Set.Ioo 0 (Real.pi / 2 - θ), (sigA α y)⁻¹ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun y _ => by rw [sigA_reflect])
  have h2 := integral_reflect (g := fun t => (sigA α t)⁻¹) (t := Real.pi / 2 - θ)
    (by linarith [hθ.2])
  rw [show Real.pi / 2 - (Real.pi / 2 - θ) = θ from by ring] at h2
  rw [← h2, h1]
  exact hKWb (Real.pi / 2 - θ) ⟨by linarith [hθ.2], by linarith [hθ.1, Real.pi_pos]⟩

/-- The reflection of the filters: `y ↦ π/2 - y` maps `0⁺` to `(π/2)⁻`. -/
lemma tendsto_reflect_iff {Φ : ℝ → ℝ} {c : ℝ} :
    Tendsto (fun y => Φ (Real.pi / 2 - y)) (nhdsWithin 0 (Set.Ioi 0)) (nhds c)
      ↔ Tendsto Φ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) := by
  have hbase : Continuous (fun y : ℝ => Real.pi / 2 - y) := continuous_const.sub continuous_id
  constructor
  · intro h
    have hmap : Tendsto (fun x : ℝ => Real.pi / 2 - x)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h1 := (hbase.continuousAt (x := Real.pi / 2)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2)) (a := Real.pi / 2))
        simpa using h1
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [Set.mem_Iio] at hx
        simp only [Set.mem_Ioi]
        linarith
    have h2 := h.comp hmap
    have hcomp : ((fun y : ℝ => Φ (Real.pi / 2 - y)) ∘ (fun x : ℝ => Real.pi / 2 - x)) = Φ := by
      funext x
      simp only [Function.comp_apply]
      congr 1
      ring
    rwa [hcomp] at h2
  · intro h
    have hmap : Tendsto (fun y : ℝ => Real.pi / 2 - y) (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h1 := (hbase.continuousAt (x := 0)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi 0) (a := 0))
        simpa using h1
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [Set.mem_Ioi] at hx
        simp only [Set.mem_Iio]
        linarith
    have h2 := h.comp hmap
    have hcomp : (Φ ∘ (fun y : ℝ => Real.pi / 2 - y)) = fun y => Φ (Real.pi / 2 - y) := rfl
    rwa [hcomp] at h2

/-- `A y^e → 0` as `y → 0⁺` (for `e > 0`). -/
lemma tendsto_const_mul_rpow_zero {A e : ℝ} (he : 0 < e) :
    Tendsto (fun y : ℝ => A * y ^ e) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h : ContinuousAt (fun y : ℝ => A * y ^ e) 0 :=
    continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr he.le))
  have h0 : (0 : ℝ) ^ e = 0 := Real.zero_rpow (ne_of_gt he)
  simpa [h0] using h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0) (a := 0))

/-- Squeeze: a function dominated by `A y^e` off `0` tends to `0` at `0⁺`. -/
lemma tendsto_zero_of_abs_le {F : ℝ → ℝ} {A e : ℝ} (he : 0 < e)
    (h : ∀ y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |F y| ≤ A * y ^ e) :
    Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (f := fun y => ‖F y‖) (g := fun y => A * y ^ e) ?_ ?_
      (tendsto_const_mul_rpow_zero (A := A) he))
  · filter_upwards with y
    exact norm_nonneg (F y)
  · filter_upwards [Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)] with y hy
    simpa [Real.norm_eq_abs] using h y hy

/-! ## 5. The fundamental theorem of calculus in the interior -/

/-- **Interior FTC.**  For `u < v` both in `(0,π/2)` and `Φ` of class `C¹` there,
`Φ v - Φ u = ∫_{(u,v)} Φ'`. -/
lemma ftc_interior {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ 1 Φ (Set.Ioo 0 (Real.pi / 2)))
    {u v : ℝ} (hu : u ∈ Set.Ioo 0 (Real.pi / 2)) (hv : v ∈ Set.Ioo 0 (Real.pi / 2)) (huv : u < v)
    (hint : IntervalIntegrable (deriv Φ) volume u v) :
    Φ v - Φ u = ∫ t in Set.Ioo u v, deriv Φ t := by
  have hderiv : ∀ x ∈ Set.Ioo u v, HasDerivAt Φ (deriv Φ x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hu.1, hx.1], by linarith [hv.2, hx.2]⟩
    exact ((hΦ.differentiableOn_one.differentiableAt (Ioo_mem_nhds hx'.1 hx'.2))).hasDerivAt
  have hcu : Tendsto Φ (nhdsWithin u (Set.Ioi u)) (nhds (Φ u)) :=
    (hΦ.continuousOn.continuousAt (Ioo_mem_nhds hu.1 hu.2)).tendsto.mono_left nhdsWithin_le_nhds
  have hcv : Tendsto Φ (nhdsWithin v (Set.Iio v)) (nhds (Φ v)) :=
    (hΦ.continuousOn.continuousAt (Ioo_mem_nhds hv.1 hv.2)).tendsto.mono_left nhdsWithin_le_nhds
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto huv hderiv hint hcu hcv
  rw [← h, intervalIntegral.integral_of_le huv.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **Additivity of the slice integral at an interior point** (a single point is negligible, so
this is the interval-integral splitting rule). -/
lemma setIntegral_Ioo_add_adjacent {a b c : ℝ} {f : ℝ → ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : IntegrableOn f (Set.Ioo a b)) (h2 : IntegrableOn f (Set.Ioo b c)) :
    (∫ t in Set.Ioo a b, f t) + (∫ t in Set.Ioo b c, f t) = ∫ t in Set.Ioo a c, f t := by
  have h1' : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab (by simp) (by simp)).mpr h1
  have h2' : IntervalIntegrable f volume b c :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hbc (by simp) (by simp)).mpr h2
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hbc,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (le_trans hab hbc)]
  exact intervalIntegral.integral_add_adjacent_intervals h1' h2'

/-! ## 6. The FTC normalised at `θ₀ = π/4`, and the squeeze for the endpoint limits -/

/-- **The FTC identity at the left endpoint.**  With the normalisation
`c := Φ(π/4) - ∫_0^{π/4} Φ'` one has `Φ θ - c = ∫_0^θ Φ'` for every `θ ∈ (0,π/2)`.
(The splitting of the integral at `π/4` is `setIntegral_Ioo_add_adjacent`; the missing point
`π/4` is irrelevant.) -/
lemma ftc_at_quarter {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ 1 Φ (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (deriv Φ) (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Φ θ - (Φ (Real.pi / 4) - ∫ t in Set.Ioo 0 (Real.pi / 4), deriv Φ t)
        = ∫ t in Set.Ioo 0 θ, deriv Φ t := by
  intro θ hθ
  have hπ4 : (Real.pi / 4) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hfour : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hintm : IntegrableOn (deriv Φ) (Set.Ioo 0 (Real.pi / 4)) :=
    hint.mono_set (fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)
  rcases lt_trichotomy θ (Real.pi / 4) with hlt | heq | hgt
  · have hIntθ : IntegrableOn (deriv Φ) (Set.Ioo 0 θ) :=
      hint.mono_set (fun x hx => ⟨hx.1, by linarith [hx.2, hlt, Real.pi_pos]⟩)
    have hIntmid : IntegrableOn (deriv Φ) (Set.Ioo θ (Real.pi / 4)) :=
      hint.mono_set (fun x hx => ⟨by linarith [hθ.1, hx.1], by linarith [hx.2, Real.pi_pos]⟩)
    have hftc : Φ (Real.pi / 4) - Φ θ = ∫ t in Set.Ioo θ (Real.pi / 4), deriv Φ t :=
      ftc_interior hΦ hθ hπ4 hlt
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le hlt.le (by simp) (by simp)).mpr hIntmid)
    have hsplit := setIntegral_Ioo_add_adjacent hθ.1.le hlt.le hIntθ hIntmid
    linarith [hftc, hsplit]
  · subst heq
    ring
  · have hIntmid : IntegrableOn (deriv Φ) (Set.Ioo (Real.pi / 4) θ) :=
      hint.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩)
    have hftc : Φ θ - Φ (Real.pi / 4) = ∫ t in Set.Ioo (Real.pi / 4) θ, deriv Φ t :=
      ftc_interior hΦ hπ4 hθ hgt
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le hgt.le (by simp) (by simp)).mpr hIntmid)
    have hsplit := setIntegral_Ioo_add_adjacent hfour.le hgt.le hintm hIntmid
    linarith [hftc, hsplit]

/-- **The FTC identity at the right endpoint.**  With the normalisation
`c := Φ(π/4) + ∫_{π/4}^{π/2} Φ'` one has `Φ θ - c = -∫_θ^{π/2} Φ'` for every `θ ∈ (0,π/2)`. -/
lemma ftc_at_quarter_right {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ 1 Φ (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (deriv Φ) (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Φ θ - (Φ (Real.pi / 4) + ∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), deriv Φ t)
        = -(∫ t in Set.Ioo θ (Real.pi / 2), deriv Φ t) := by
  intro θ hθ
  have hπ4 : (Real.pi / 4) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hfour : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hintm : IntegrableOn (deriv Φ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    hint.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
  rcases lt_trichotomy θ (Real.pi / 4) with hlt | heq | hgt
  · have hIntθ : IntegrableOn (deriv Φ) (Set.Ioo θ (Real.pi / 4)) :=
      hint.mono_set (fun x hx => ⟨by linarith [hθ.1, hx.1], by linarith [hx.2, Real.pi_pos]⟩)
    have hftc : Φ (Real.pi / 4) - Φ θ = ∫ t in Set.Ioo θ (Real.pi / 4), deriv Φ t :=
      ftc_interior hΦ hθ hπ4 hlt
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le hlt.le (by simp) (by simp)).mpr hIntθ)
    have hsplit := setIntegral_Ioo_add_adjacent hlt.le
      (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi / 2) hIntθ hintm
    linarith [hftc, hsplit]
  · subst heq
    ring
  · have hIntmid : IntegrableOn (deriv Φ) (Set.Ioo (Real.pi / 4) θ) :=
      hint.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩)
    have hIntθ2 : IntegrableOn (deriv Φ) (Set.Ioo θ (Real.pi / 2)) :=
      hint.mono_set (fun x hx => ⟨by linarith [hgt.le, hx.1], hx.2⟩)
    have hftc : Φ θ - Φ (Real.pi / 4) = ∫ t in Set.Ioo (Real.pi / 4) θ, deriv Φ t :=
      ftc_interior hΦ hπ4 hθ hgt
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le hgt.le (by simp) (by simp)).mpr hIntmid)
    have hsplit := setIntegral_Ioo_add_adjacent hgt.le hθ.2.le hIntmid hIntθ2
    linarith [hftc, hsplit]

/-- From a bound on the square, the corresponding bound on the absolute value with the
`e/2`-power. -/
lemma abs_le_sqrt_mul_rpow {x K M e θ : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hθ : 0 ≤ θ)
    (h : x ^ 2 ≤ K * M * θ ^ e) :
    |x| ≤ Real.sqrt (K * M) * θ ^ (e / 2) := by
  have h2 : (θ ^ (e / 2)) ^ 2 = θ ^ e := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hθ]
    congr 1
    push_cast
    ring
  have hsq : (Real.sqrt (K * M) * θ ^ (e / 2)) ^ 2 = K * M * θ ^ e := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hK hM), h2]
  have h1 : Real.sqrt (x ^ 2) ≤ Real.sqrt ((Real.sqrt (K * M) * θ ^ (e / 2)) ^ 2) :=
    Real.sqrt_le_sqrt (by rw [hsq]; exact h)
  rw [Real.sqrt_sq_eq_abs,
    Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hθ _))] at h1
  exact h1

/-- The reflected squeeze: a function whose reflected version is dominated by `A y^e` at `0⁺`
has limit `0` at `(π/2)⁻`. -/
lemma tendsto_zero_of_abs_le_reflect {F : ℝ → ℝ} {A e : ℝ} (he : 0 < e)
    (h : ∀ y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |F (Real.pi / 2 - y)| ≤ A * y ^ e) :
    Tendsto F (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
  (tendsto_reflect_iff (Φ := F)).mp (tendsto_zero_of_abs_le he h)

/-! ## 7. Elementary nonnegativity helpers -/

lemma sigA_nonneg' {α θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) : 0 ≤ sigA α θ :=
  Work.FTS.EllipticEst.TT.sigA_nonneg α θ hθ


lemma sq_mul_sigA_nonneg {α x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (y : ℝ) :
    0 ≤ y ^ 2 * sigA α x :=
  mul_nonneg (sq_nonneg y) (sigA_nonneg' ⟨hx.1.le, hx.2.le⟩)

/-- Monotonicity of the slice integral in the right endpoint (nonnegative integrand). -/
lemma setIntegral_mono_Ioo {f : ℝ → ℝ} {a b c : ℝ} (hbc : b ≤ c)
    (hint : IntegrableOn f (Set.Ioo a c)) (hnn : ∀ x ∈ Set.Ioo a c, 0 ≤ f x) :
    ∫ x in Set.Ioo a b, f x ≤ ∫ x in Set.Ioo a c, f x := by
  have hsub : Set.Ioo a b ⊆ Set.Ioo a c := fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hbc⟩
  have hae : (Set.Ioo a b : Set ℝ) ≤ᵐ[volume] (Set.Ioo a c : Set ℝ) := by
    rw [MeasureTheory.ae_le_set, Set.sdiff_eq_empty.mpr hsub, measure_empty]
  exact MeasureTheory.setIntegral_mono_set hint
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hnn) hae

/-- Monotonicity of the slice integral in the left endpoint (nonnegative integrand). -/
lemma setIntegral_mono_Ioo_left {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hint : IntegrableOn f (Set.Ioo a c)) (hnn : ∀ x ∈ Set.Ioo a c, 0 ≤ f x) :
    ∫ x in Set.Ioo b c, f x ≤ ∫ x in Set.Ioo a c, f x := by
  have hsub : Set.Ioo b c ⊆ Set.Ioo a c := fun x hx => ⟨lt_of_le_of_lt hab hx.1, hx.2⟩
  have hae : (Set.Ioo b c : Set ℝ) ≤ᵐ[volume] (Set.Ioo a c : Set ℝ) := by
    rw [MeasureTheory.ae_le_set, Set.sdiff_eq_empty.mpr hsub, measure_empty]
  exact MeasureTheory.setIntegral_mono_set hint
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hnn) hae

end Work.FTS.EllipticEst.Cores
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.sliceInterpVanishing =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# The vanishing-boundary slice interpolation for the light weight `σ_A = sin(2θ)^{2-γ}`

This file proves `sliceInterpVanishing`.  With `a := 2 - γ(α) = 1 - α/10 ∈ (0,1)` and
`σ_A = sigA α = sigR a`, the *double angular integration by parts for the light weight*
(`TT.slice_ibp_light`) gives, whenever the four boundary products of `Φ` vanish,

  `∫ (Φ')²σ_A = -∫ Φ Φ'' σ_A - 2a ∫ Φ² σ_A - 2a(1-a) ∫ Φ² cos²(2θ) sin(2θ)^{a-2}`,

and the last two terms are `≤ 0` because their integrands are nonnegative and `0 < a < 1`.
Hence `∫ (Φ')²σ_A ≤ -∫ ΦΦ''σ_A ≤ |∫ ΦΦ''σ_A|`, and the Cauchy–Schwarz inequality for the
weighted pairing `(Φ, Φ'') ↦ ∫ Φ Φ'' σ_A` bounds this by `√(∫Φ²σ_A · ∫(Φ'')²σ_A)`.
The constant is therefore `C = 1`.

The weighted Cauchy–Schwarz is applied with the two half-weighted functions
`Φ·√σ_A` and `Φ''·√σ_A` in `L²(Iθ)`.
-/

/-- `Iθ` and the open interval `(0, π/2)` differ only by the two endpoints, so they carry the
same restricted Lebesgue measure. -/
theorem restrict_Iθ_eq_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  apply MeasureTheory.Measure.restrict_congr_set
  change ∀ᵐ x ∂volume, (x ∈ Work.Spaces.Iθ) = (x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
  rw [MeasureTheory.ae_iff]
  have hsub : {a : ℝ | ¬((a ∈ Work.Spaces.Iθ) = (a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)))}
      ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro x hx
    by_contra hx2
    refine hx (propext ⟨?_, ?_⟩)
    · intro h1
      simp only [Work.Spaces.Iθ, Set.mem_Icc] at h1
      have h0 : x ≠ 0 := by intro h; exact hx2 (by simp [h])
      have hp : x ≠ Real.pi / 2 := by intro h; exact hx2 (by simp [h])
      exact ⟨lt_of_le_of_ne h1.1 (Ne.symm h0), lt_of_le_of_ne h1.2 hp⟩
    · intro h1
      simp only [Work.Spaces.Iθ, Set.mem_Icc]
      exact ⟨le_of_lt h1.1, le_of_lt h1.2⟩
  have h2 : volume ({0, Real.pi / 2} : Set ℝ) = 0 := by
    rw [show ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
    exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
      (MeasureTheory.measure_singleton (Real.pi / 2))
  exact MeasureTheory.measure_mono_null hsub h2

/-- A function continuous on the open interval is a.e.-strongly-measurable on `Iθ`. -/
theorem aesm_of_continuousOn_Ioo (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq_Ioo]
  exact hf.aestronglyMeasurable measurableSet_Ioo


end Work.FTS.EllipticEst.Cores
end
-- ===== merged: Submission.Work.FTS.EllipticEst.EllTwoAsm.SliceRateLightAsm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.EllTwoAsm

set_option autoImplicit false
set_option maxHeartbeats 1000000



end Work.FTS.EllipticEst.EllTwoAsm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Ae.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false

/-- **Step 1** (paper: `(radialweightonlyL2)` with the `σ`-upgrade): in the class `AeData` the
functions `u` and `z ∂_z u` are honest in `ℋ⁰`, and `‖u‖_ρ ≤ C‖G‖_ρ`,
`α‖z∂_z u‖_ρ ≤ C‖G‖_ρ`. -/
def Step1 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      Work.Spaces.HkMem α 0 u ∧
      Work.Spaces.HkMem α 0 (grad u) ∧
      nrm α u ≤ C * nrm α G ∧
      α * nrm α (grad u) ≤ C * nrm α G

/-- **Step 2** (paper: `(radialandangularweightL2)`, angular half):
`‖∂_θθ u‖_ρ ≤ C(‖G‖_ρ + α‖z∂_z u‖_ρ)`. -/
def Step2 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      nrm α (ang2 u) ≤ C * (nrm α G + α * nrm α (grad u))

/-- **Step 3** (the radial second-order term recovered from the equation):
`α²‖z²∂_zz u‖_ρ ≤ C(‖G‖_ρ + α‖z∂_z u‖_ρ + ‖∂_θθ u‖_ρ + ‖u‖_ρ)`. -/
def Step3 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
        ≤ C * (nrm α G + α * nrm α (grad u) + nrm α (ang2 u) + nrm α u)

/-- **The assembly.**  Steps 1–3 imply the level-`0` `η`-weighted estimate. -/
theorem level0Ae_of (h1 : Step1) (h2 : Step2) (h3 : Step3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
        α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)
        ≤ C * Work.Spaces.HkSq α 0 G := by
  obtain ⟨C₁, hC₁, h1'⟩ := h1
  obtain ⟨C₂, hC₂, h2'⟩ := h2
  obtain ⟨C₃, hC₃, h3'⟩ := h3
  have hC₁0 : (0 : ℝ) ≤ C₁ := le_of_lt hC₁
  have hC₂0 : (0 : ℝ) ≤ C₂ := le_of_lt hC₂
  have hC₃0 : (0 : ℝ) ≤ C₃ := le_of_lt hC₃
  -- the coefficient of the final estimate
  have hp1 : 0 ≤ C₂ * (1 + C₁) := mul_nonneg hC₂0 (by linarith)
  have hp2 : 0 ≤ C₃ * (1 + C₁ + C₂ * (1 + C₁) + C₁) := mul_nonneg hC₃0 (by linarith)
  set K : ℝ := C₃ * (1 + C₁ + C₂ * (1 + C₁) + C₁) + C₂ * (1 + C₁) with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  refine ⟨max (K ^ 2) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro α u G hA
  obtain ⟨hmemU, hmemGu, huB, hgB⟩ := h1' α u G hA
  have hX' := h2' α u G hA
  have hA2' := h3' α u G hA
  obtain ⟨hα, hα4, heq, hdir0, hdirpi, hsmooth, hmemG, hmemA, hmemB, hmomU, hmomG⟩ := hA
  have hα0 : (0 : ℝ) ≤ α := le_of_lt hα
  have hf0 : 0 ≤ nrm α G := Real.sqrt_nonneg _
  have hb0 : 0 ≤ nrm α (grad u) := Real.sqrt_nonneg _
  have hm0 : 0 ≤ nrm α u := Real.sqrt_nonneg _
  have hX0 : 0 ≤ nrm α (ang2 u) := Real.sqrt_nonneg _
  have ha0 : 0 ≤ nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)) :=
    Real.sqrt_nonneg _
  -- Step 2, with Step 1's absorption of `α ‖z∂_z u‖_ρ`
  have hprod1 : C₂ * (α * nrm α (grad u)) ≤ C₂ * (C₁ * nrm α G) :=
    mul_le_mul_of_nonneg_left hgB hC₂0
  have hXf : nrm α (ang2 u) ≤ C₂ * (1 + C₁) * nrm α G := by
    nlinarith [hX', hprod1, hf0, hC₂0, hC₁0]
  -- Step 3, with the same absorption and with `X` bounded
  have hsum33 : nrm α G + α * nrm α (grad u) + nrm α (ang2 u) + nrm α u
      ≤ (1 + C₁ + C₂ * (1 + C₁) + C₁) * nrm α G := by
    nlinarith [hgB, huB, hXf, hf0, hb0, hm0, hC₁0, hC₂0]
  have haf : nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
      ≤ K * nrm α G := by
    have hmult : C₃ * (nrm α G + α * nrm α (grad u) + nrm α (ang2 u) + nrm α u)
        ≤ C₃ * ((1 + C₁ + C₂ * (1 + C₁) + C₁) * nrm α G) :=
      mul_le_mul_of_nonneg_left hsum33 hC₃0
    have hre : C₃ * ((1 + C₁ + C₂ * (1 + C₁) + C₁) * nrm α G)
        = (C₃ * (1 + C₁ + C₂ * (1 + C₁) + C₁)) * nrm α G := by ring
    rw [hK]
    linarith [hA2', hmult, hre]
  -- the sum of the two quantities
  have hsum : nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
      + nrm α (ang2 u) ≤ K * nrm α G := by
    nlinarith [haf, hXf, hK0, hf0, hC₂0, hC₁0]
  -- square everything
  have hsq : (nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
      + nrm α (ang2 u)) ^ 2 ≤ (K * nrm α G) ^ 2 := by
    nlinarith [hsum, ha0, hX0, hf0, hK0]
  have hexp : (nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
      + nrm α (ang2 u)) ^ 2
      = (nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))) ^ 2
        + (nrm α (ang2 u)) ^ 2
        + 2 * (nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)))
          * (nrm α (ang2 u)) := by ring
  have hcross : 0 ≤ 2 * (nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)))
      * (nrm α (ang2 u)) := by
    have := mul_nonneg ha0 hX0
    linarith
  have ha2 : (nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))) ^ 2
      = α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) := by
    rw [nrm, Work.FTS.EllipticEst.Honest.hksq_sqrt_sq,
      Work.FTS.EllipticEst.Honest.HkSq_zero_const_mul]
    ring
  have hX2 : (nrm α (ang2 u)) ^ 2 = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u) := by
    rw [nrm, Work.FTS.EllipticEst.Honest.hksq_sqrt_sq]
    rfl
  have hK2 : (K * nrm α G) ^ 2 = K ^ 2 * Work.Spaces.HkSq α 0 G := by
    rw [mul_pow, nrm, Work.FTS.EllipticEst.Honest.hksq_sqrt_sq]
  rw [hexp, ha2, hX2] at hsq
  rw [hK2] at hsq
  calc α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)
      ≤ K ^ 2 * Work.Spaces.HkSq α 0 G := by linarith [hsq, hcross]
    _ ≤ max (K ^ 2) 1 * Work.Spaces.HkSq α 0 G :=
        mul_le_mul_of_nonneg_right (le_max_left (K ^ 2) 1)
          (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α G)

end Work.FTS.EllipticEst.H2W.Ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.eigenFTCAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `WeakPureAux/eigenFTCAux` — the `(Dfun, Rfun)` FTC system for `Lzero1 u = mu * u`

Stage 1 (and the first half of stage 2) of the plan in
`WeakPureAux/NOTES_eigenSlicePoleBound.md`: the two exact integral identities carried by

* `Dfun u θ = cos θ · (u θ · (sin 2θ)' - u' θ · sin 2θ)`, with `Dfun u' = 2·Lzero1 u·sinθcos²θ`,
* `Rfun u θ = u θ / sin 2θ`, with `Rfun u' = -Dfun u θ/(cos θ · sin(2θ)²)`,

and the *running* bound for `Dfun` obtained from them under the eigenrelation
`Lzero1 u = mu * u`.  The bounds are deliberately stated with the running weight
`Gd u θ = ∫_{π/4}^{θ} |Rfun u s|·w s ds` (`w = sin(2θ)·sinθcos²θ`) instead of the total
`Mfun u = ∫_{Iθ} sinθcos²θ·|Lzero1 u|`, which is *not* known to be finite before the theorem is
proved.  All ingredients come from the already-proved `C²`-level lemmas of
`Submission/Work/FTS/EllipticEst/H2W/lzero1SliceGrowth.lean`.
-/

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section


/-- The kernel `k θ = 1/(cos θ · sin(2θ)²)` of the `Rfun` equation. -/
def ek (θ : ℝ) : ℝ := 1 / (Real.cos θ * Real.sin (2 * θ) ^ 2)



/-- `sinθcos²θ` is continuous. -/
theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop


/-- `sinθcos²θ ≥ 0` on the open angular interval. -/
theorem sinCos2_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])).le (sq_nonneg _)

















end

end Work.FTS.EllipticEst.H2W.WeakPureAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.lzeroSlicePoleBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.WeakPureAux


end Work.FTS.EllipticEst.H2W.WeakPureAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.poleBoundOfSourcePointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

/-! ## Elementary bounds for the weight `sin θ cos²θ` -/



/-- `sin θ cos²θ ≤ 1`. -/
theorem sinCos2_le_one (θ : ℝ) : Work.Elliptic.sinCos2 θ ≤ 1 := by
  rw [Work.Elliptic.sinCos2]
  simpa using mul_le_mul (Real.sin_le_one θ) (Real.cos_sq_le_one θ) (sq_nonneg _)
    (by norm_num : (0:ℝ) ≤ 1)

/-! ## The two mass bounds for the source

With `sin θ cos²θ` the angular weight of the `i = 0` slot, the pointwise source bound
`|g θ| ≤ C (θ⁻² + (π/2 - θ)⁻²)` gives the folded estimates below.  Both constants are
`C (π/4 + 4/π)`: at `θ = 0` the weight `sin s cos² s ≈ s` cancels one power of `s`, leaving
the integrable `s⁻¹` on the *relative* interval `[θ, π/4]` (giving `θ⁻¹`), and at `θ = π/2`
the weight `≈ (π/2 - s)²` cancels the second-order pole exactly. -/


/-! ## The Wronskian functional and the reduction-of-order identities -/

/-- The mass of the source on the *left* half `[θ, π/4]`. -/
def Ml (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ s in θ..(Real.pi/4), Work.Elliptic.sinCos2 s * |g s|











/-! ## The two half-bounds -/




end Work.FTS.EllipticEst.H2W.WeakPureAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.truncBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `truncBounds`: the truncated (interval) growth bounds for `Dfun` and `Rfun`

The Wronskian-type functionals of `H2W.LzeroGrowth`,

  `Dfun u θ = cos θ · (u θ · 2cos 2θ − u' θ · sin 2θ)`,      `Rfun u θ = u θ / sin 2θ`,

satisfy the two exact identities (`H2W.Lzero1Growth`)

  `(Dfun u)' θ = 2 · Lzero1 u θ · sinθcos²θ`,   `(Rfun u)' θ = − Dfun u θ / (cos θ · sin²2θ)`.

Integrating both against the *absolute values* of the right-hand sides over the interval
between `θ` and the reference point `π/4` (where `sin 2θ = 1`), and using only
`|A − B| ≤ |A| + |B|`, gives the four truncated bounds stated in `truncBounds`: the pointwise
value at `θ` is controlled by the value at `π/4` plus the accumulated growth of the source
`Lzero1 u` resp. of `Dfun u`.

Everything is `C²`: only `Dfun_hasDerivAt`/`Rfun_hasDerivAt` at `ContDiffOn ℝ 2` are used, plus
the fundamental theorem of calculus on a compact subinterval of the *open* interval
`(0, π/2)` (so the endpoints `0`, `π/2`, where the coefficients degenerate, are never touched).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

set_option autoImplicit false







end Work.FTS.EllipticEst.H2W.WeakPureAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HkNorm_add_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Auxiliary lemmas -/

/-- A property of angles which holds on the open interval `(0, π/2)` holds almost everywhere on
the closed interval `Iθ`: the two endpoints form a null set and are exactly the complement of
`(0, π/2)` inside `Iθ`. -/
private lemma ae_restrict_Iθ_of_Ioo {p : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo 0 (π / 2), p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  refine (MeasureTheory.ae_restrict_congr_set hIoo).mp ?_
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => h θ hθ

/-- **Pointwise subadditivity of the `ℋ^k`-integrand on the open quadrant.**  The `D`-operators
are additive on `(0,∞) × (0,π/2)` for `C^∞` data, and `(a+b)² ≤ 2a² + 2b²` termwise.

(This is the same statement as `Work.FTS.EllipticEst.HkIntegrand_add_le_open`; it is reproduced
here — with a proof — so that this module depends only on `Spaces.Defs`, `SmoothOpenAdd` and
`LocData.HkMem_of_majorant`.) -/
private lemma HkIntegrand_add_le_Q0 {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * (Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k g z θ) := by
  have hDz : ∀ i : ℕ, Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ := fun i =>
    SmoothOpen.DzIter_add hf hg i z θ hz hθ.1 hθ.2
  have hMixed : ∀ j i : ℕ, Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ := fun j i =>
    SmoothOpen.mixed_add hf hg j i z θ hz hθ.1 hθ.2
  simp only [Work.Spaces.HkIntegrand]
  have hZ : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + 2 * (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    calc (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ i ∈ Finset.range (k + 1),
            (2 * (Work.Spaces.DzIter i f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              + 2 * (Work.Spaces.DzIter i g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          rw [hDz i, add_mul]
          nlinarith [sq_nonneg (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            - Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
      _ = 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (2 * (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
              + 2 * (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [ite_eq_left hc, ite_eq_left hc, ite_eq_left hc, hMixed j i, add_mul]
            nlinarith [sq_nonneg (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ
              - Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ)]
          · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right hc]
            norm_num
      _ = 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
  linarith [hZ, hM]

/-- **The angular slice estimate.**  For every `z ∈ Iz`, the `θ`-integral of the `ℋ^k`-integrand
of `f + g` is at most twice the sum of the `θ`-integrals of the integrands of `f` and of `g`.
The integrability input is only for `f` and `g` (`HkMem`). -/
private lemma HkIntegrand_add_slice_le {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
      ≤ 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)) := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · -- at `z = 0` the radial weight vanishes, so all three integrands are identically zero
    subst h0
    simp [Work.FTS.LocData.HkIntegrand_zero_fst]
  · have hle : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ,
            2 * (Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k g z θ) :=
      MeasureTheory.integral_mono_of_nonneg
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k (fun z θ => f z θ + g z θ) z θ))
        (((hmf.1 z hz).add (hmg.1 z hz)).const_mul 2)
        (ae_restrict_Iθ_of_Ioo fun θ hθ => HkIntegrand_add_le_Q0 hf hg hz0 hθ)
    rwa [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hmf.1 z hz) (hmg.1 z hz)] at hle

/-- **Additivity of the squared `H^k`-norm up to the factor `2`.** -/
private lemma HkSq_add_le {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkSq α k (fun z θ => f z θ + g z θ)
      ≤ 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g := by
  have hmono : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
      ≤ ∫ z in Work.Spaces.Iz,
          2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)) :=
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k (fun z θ => f z θ + g z θ) z θ)
      ((hmf.2.add hmg.2).const_mul 2)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        fun z hz => HkIntegrand_add_slice_le hf hg hmf hmg hz)
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine le_trans hmono ?_
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hmf.2 hmg.2]
  linarith

/-! ## The main statement -/

theorem HkNorm_add_fts (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g) := by
  have hfS : SmoothOpen f := smoothOpen_of_forall (by simpa [Q0] using hf)
  have hgS : SmoothOpen g := smoothOpen_of_forall (by simpa [Q0] using hg)
  have hsq := HkSq_add_le hfS hgS hmf hmg
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
  refine le_trans (Real.sqrt_le_sqrt hsq) ?_
  have ha0 : 0 ≤ Work.Spaces.HkSq α k f := Work.Spaces.HkSq_nonneg α k f
  have hb0 : 0 ≤ Work.Spaces.HkSq α k g := Work.Spaces.HkSq_nonneg α k g
  have h2 : 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g
      ≤ (Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α k f)
          + Real.sqrt (Work.Spaces.HkSq α k g))) ^ 2 := by
    have h2s : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hfs : (Real.sqrt (Work.Spaces.HkSq α k f)) ^ 2 = Work.Spaces.HkSq α k f :=
      Real.sq_sqrt ha0
    have hgs : (Real.sqrt (Work.Spaces.HkSq α k g)) ^ 2 = Work.Spaces.HkSq α k g :=
      Real.sq_sqrt hb0
    have hnn : 0 ≤ Real.sqrt (Work.Spaces.HkSq α k f) * Real.sqrt (Work.Spaces.HkSq α k g) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [h2s, hfs, hgs, hnn]
  refine le_trans (Real.sqrt_le_sqrt h2) ?_
  rw [Real.sqrt_sq (by positivity)]

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HonGaps.mixedInterpDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.HonGaps

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The angular cut-off `ψ_ε`: smooth, `= 0` off `(ε, π/2-ε)`, `= 1` on `[2ε, π/2-2ε]`,
valued in `[0,1]`. -/
def psiCut (ε θ : ℝ) : ℝ :=
  Real.smoothTransition (θ / ε - 1) * Real.smoothTransition ((Real.pi / 2 - θ) / ε - 1)









/-- The `A`-term `z²∂²_zzΨ` of the target. -/
def qTerm (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ








end Work.FTS.EllipticEst.HonGaps
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SliceMain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- Local abbreviation for the angular weight `σ θ = sin(2θ)^{-η}`
(`Work.FTS.EllipticEst.AngSecond.sig`). -/
local notation "sg" => Work.FTS.EllipticEst.AngSecond.sig

/-- Local abbreviation for the coefficient `A(θ) = ((1-η)/2) cos 2θ + 2 sin²θ`
(`Work.FTS.EllipticEst.AngSecond.acoef`). -/
local notation "acf" => Work.FTS.EllipticEst.AngSecond.acoef

/-! ## Elementary pointwise facts -/

/-- `2 |a b| ≤ a² + b²`. -/
theorem two_mul_abs_mul_le (a b : ℝ) : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-- `√(a² σ) = |a| √σ` for `σ ≥ 0`. -/
theorem sqrt_sq_mul_sqrt (a σ : ℝ) (hσ : 0 ≤ σ) :
    Real.sqrt (a ^ 2 * σ) = |a| * Real.sqrt σ := by
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

/-- `√σ · √σ = σ` for `σ ≥ 0`. -/
theorem sqrt_mul_sqrt_eq (σ : ℝ) (hσ : 0 ≤ σ) : Real.sqrt σ * Real.sqrt σ = σ := by
  rw [← pow_two, Real.sq_sqrt hσ]

/-- `(sin(2θ))^{-η} = (sin(θ * 2))^{-η}`. -/
theorem sin_two_rpow_comm (θ : ℝ) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = (Real.sin (θ * 2)) ^ (-(Work.Spaces.eta)) := by
  rw [mul_comm]

/-- The coefficient `A` dominates `sin²θ`. -/
theorem sin_sq_le_acoef (θ : ℝ) : (Real.sin θ) ^ 2 ≤ acf θ := by
  rw [Work.FTS.EllipticEst.AngSecond.acoef_eq]
  have h1 := Work.Spaces.eta_nonneg
  have h2 := Work.FTS.EllipticEst.AngSecond.one_sub_eta_pos
  nlinarith [sq_nonneg (Real.sin θ)]

/-- On the open quadrant, `cos 2θ · (a / cos θ)² ≤ 2a²`.  (Where `cos 2θ > 0` one has
`cos 2θ ≤ 2 cos²θ`; where `cos 2θ < 0` the left-hand side is negative.) -/
theorem cos2_mul_div_cos_sq_le {a θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos (2 * θ) * (a / Real.cos θ) ^ 2 ≤ 2 * a ^ 2 := by
  have hcpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc2 : 0 < Real.cos θ ^ 2 := sq_pos_of_pos hcpos
  have hkey : (2 * Real.cos θ ^ 2 - 1) * (a ^ 2 / Real.cos θ ^ 2)
      = 2 * a ^ 2 - a ^ 2 / Real.cos θ ^ 2 := by
    field_simp
  rw [div_pow, Real.cos_two_mul, hkey]
  have hnn : 0 ≤ a ^ 2 / Real.cos θ ^ 2 := div_nonneg (sq_nonneg a) (le_of_lt hc2)
  linarith

/-! ## Continuity of the slice integrands on the open quadrant -/

/-- `σ` is continuous on the open quadrant. -/
theorem continuousOn_sig : ContinuousOn sg (Set.Ioo 0 (Real.pi / 2)) := by
  show ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (Set.Ioo 0 (Real.pi / 2))
  refine ContinuousOn.rpow_const ?_ ?_
  · exact Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2)
  · intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])))

/-- `(u/cos)'` is continuous on the open quadrant for `u ∈ C²` there. -/
theorem continuousOn_deriv_div_cos {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv (fun θ => u θ / Real.cos θ)) (Set.Ioo 0 (Real.pi / 2)) := by
  have hcd : ContDiffOn ℝ 2 (fun θ => u θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn fun θ hθ =>
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  exact hcd.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)

/-- `u''` is continuous on the open quadrant for `u ∈ C²` there. -/
theorem continuousOn_deriv_deriv {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) := by
  have hcd : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  exact hcd.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)

/-! ## From `HkMem` to the slicewise `σ`-weighted integrability -/

/-- **The slicewise integrability of `g² σ` for an honest `g`.**  `Work.Spaces.HkMem 0 0 g`
says that for every `z ∈ Iz` the function `θ ↦ (g z θ · w z / σ θ ^{η/2})²` is integrable on
`Iθ`; since that function equals `(g z θ)² · (w z)² · σ θ` and `w z ≠ 0` for `z > 0`, the
slice `θ ↦ (g z θ)² σ θ` is integrable. -/
theorem integrableOn_sq_mul_sig_of_hkMem {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.HkMem 0 0 g)
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (g z θ) ^ 2 * sg θ) Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have h1 : IntegrableOn (fun θ => Work.Spaces.HkIntegrand 0 0 g z θ) Work.Spaces.Iθ :=
    hg.1 z hzI
  have hw : Work.Spaces.w z ^ 2 ≠ 0 := by
    have hpos : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
    positivity
  have heq : EqOn (fun θ => Work.Spaces.HkIntegrand 0 0 g z θ)
      (fun θ => Work.Spaces.w z ^ 2 * ((g z θ) ^ 2 * sg θ)) Work.Spaces.Iθ := by
    intro θ hθ
    show Work.Spaces.HkIntegrand 0 0 g z θ = Work.Spaces.w z ^ 2 * ((g z θ) ^ 2 * sg θ)
    rw [HkIntegrand_zero_eq, sq_profile_eq g z θ (sin_two_nonneg_of_mem_Iθ hθ)]
    simp only [Work.FTS.EllipticEst.AngSecond.sig, sin_two_rpow_comm]
    ring
  have h2 : IntegrableOn (fun θ => Work.Spaces.w z ^ 2 * ((g z θ) ^ 2 * sg θ))
      Work.Spaces.Iθ := h1.congr_fun heq measurableSet_Icc
  have h3 : Integrable (fun θ => (g z θ) ^ 2 * sg θ)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
    (integrable_const_mul_iff (IsUnit.mk0 (Work.Spaces.w z ^ 2) hw)
      (fun θ => (g z θ) ^ 2 * sg θ)).mp h2
  exact h3

/-! ## The level-`0` `HkSq` as the `z`-integral of the slice integrals -/

/-- At a fixed `z ∈ Iz`, the `θ`-integral of the level-`0` `HkIntegrand` is `w z²` times the
`σ`-weighted `L²`-mass of the slice. -/
theorem hkIntegrand_zero_integral_eq {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.HkMem 0 0 g)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand 0 0 g z θ)
      = (Work.Spaces.w z) ^ 2
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), (g z θ) ^ 2 * sg θ) := by
  have hz' : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz' with h | h
  · subst h
    have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
    have hz0 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand 0 0 g 0 θ) = 0 := by
      have hpt : ∀ θ : ℝ, Work.Spaces.HkIntegrand 0 0 g 0 θ = 0 := by
        intro θ
        rw [HkIntegrand_zero_eq, hw0]
        simp
      rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand 0 0 g 0 θ)
          = ∫ θ in Work.Spaces.Iθ, (0 : ℝ) from
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpt θ)]
      simp
    rw [hw0, hz0]
    ring
  · have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand 0 0 g z θ)
        = ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sg θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
      rw [HkIntegrand_zero_eq, sq_profile_eq g z θ (sin_two_nonneg_of_mem_Iθ hθ)]
      simp only [Work.FTS.EllipticEst.AngSecond.sig, sin_two_rpow_comm]
    rw [h1]
    rw [show (fun θ => (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sg θ)
        = (fun θ => (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * sg θ)) from by
      funext θ; ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2))).symm

/-- **`HkSq 0 0 g` as the `w²`-weighted integral of the slicewise `σ`-weighted `L²`-masses.** -/
theorem hkSq_zero_eq_sliceW {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.HkMem 0 0 g) :
    Work.Spaces.HkSq 0 0 g
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), (g z θ) ^ 2 * sg θ) := by
  rw [Work.Spaces.HkSq]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z hz =>
    hkIntegrand_zero_integral_eq hg hz

/-! ## Slices of a function smooth on the open quadrant -/

/-- The `θ`-slice of a function smooth on the open quadrant is smooth on `(0, π/2)`. -/
theorem contDiffOn_slice_of_hsm {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z : ℝ} (hz : 0 < z) (n : ℕ) :
    ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hcomp : ContDiffOn ℝ n (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have h := (hsm n).comp hcomp (fun θ hθ => ⟨hz, hθ⟩)
  simpa [Function.comp_def, Function.uncurry] using h

/-- The iterated angular derivative `∂_θ²` of a fixed slice is the second derivative of the
slice. -/
theorem pthIter_two_apply (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 Ψ z θ = deriv (deriv (fun θ' => Ψ z θ')) θ := rfl

/-- The `θ`-derivative of `Ψ/cos θ` at `(z,θ)` is the derivative of the slice. -/
theorem pth_div_apply (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
      = deriv (fun θ' => Ψ z θ' / Real.cos θ') θ := rfl

/-! ## The quadratic solve: the `I₄`-identity implies the slice estimate -/

/-- **The slicewise estimate, from the `I₄`-identity.**

Given the honest integrability facts on a slice `u` (with `ψ = u/cos`), the identity
`∫ sin θ ψ' u'' σ = ((1-η)/2) ∫ cos 2θ ψ² σ - ∫ A (ψ')² σ` yields
`∫ sin²θ (ψ')² σ ≤ ∫ (u'')² σ + 2 ∫ u² σ`
on that slice, by `A ≥ sin²θ`, the pointwise bound `cos 2θ (u/cos θ)² ≤ 2 u²`, and
Cauchy--Schwarz `-∫ sin θ ψ' u'' σ ≤ √(∫ sin²θ (ψ')² σ) √(∫ (u'')² σ)`. -/
theorem slice_sq_le_of_ident (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hA : IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)))
    (hA' : IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hB : IntegrableOn (fun θ => (u θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * sg θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hY : IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)))
    (hident : (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.sin θ
          * deriv (fun θ => u θ / Real.cos θ) θ * deriv (deriv u) θ * sg θ)
      = ((1 - Work.Spaces.eta) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * sg θ)
        - ∫ θ in Set.Ioo 0 (Real.pi / 2), acf θ
            * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
        * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
      ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv u) θ) ^ 2 * sg θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (u θ) ^ 2 * sg θ) := by
  set ys : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ with hys
  set xs : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv u) θ) ^ 2 * sg θ with hxs
  set bs : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), (u θ) ^ 2 * sg θ with hbs
  set em : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), acf θ
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ with hem
  set c2 : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), Real.cos (2 * θ)
      * (u θ / Real.cos θ) ^ 2 * sg θ with hc2
  set mm : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), Real.sin θ
      * deriv (fun θ => u θ / Real.cos θ) θ * deriv (deriv u) θ * sg θ with hmm
  have hs : MeasurableSet (Set.Ioo 0 (Real.pi / 2)) := measurableSet_Ioo
  have hsub : Set.Ioo 0 (Real.pi / 2) ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun _ hθ => ⟨hθ.1.le, hθ.2.le⟩
  have hsig_nn : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ sg θ := fun θ hθ =>
    Work.FTS.EllipticEst.AngSecond.sig_nonneg ⟨hθ.1.le, hθ.2.le⟩
  have hψ'c : ContinuousOn (deriv (fun θ => u θ / Real.cos θ))
      (Set.Ioo 0 (Real.pi / 2)) := continuousOn_deriv_div_cos hu
  have hu''c : ContinuousOn (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_deriv_deriv hu
  have hsg_c : ContinuousOn sg (Set.Ioo 0 (Real.pi / 2)) := continuousOn_sig
  have hCcont : ContinuousOn (fun θ => Real.sin θ
      * deriv (fun θ => u θ / Real.cos θ) θ * deriv (deriv u) θ * sg θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun θ : ℝ => Real.sin θ) (Set.Ioo 0 (Real.pi / 2)) := by
      fun_prop
    exact ((h1.mul hψ'c).mul hu''c).mul hsg_c
  -- nonnegativity of the three integrals
  have hys_nn : 0 ≤ ys := by
    rw [hys]
    exact MeasureTheory.setIntegral_nonneg hs fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hsig_nn θ hθ)
  have hxs_nn : 0 ≤ xs := by
    rw [hxs]
    exact MeasureTheory.setIntegral_nonneg hs fun θ hθ =>
      mul_nonneg (sq_nonneg _) (hsig_nn θ hθ)
  have hbs_nn : 0 ≤ bs := by
    rw [hbs]
    exact MeasureTheory.setIntegral_nonneg hs fun θ hθ =>
      mul_nonneg (sq_nonneg _) (hsig_nn θ hθ)
  -- (a) `Y ≤ E`
  have hEY : ys ≤ em := by
    rw [hys, hem]
    refine MeasureTheory.setIntegral_mono_on hY ?_ hs fun θ hθ => ?_
    · have hc : ContinuousOn acf (Set.Icc 0 (Real.pi / 2)) := by
        change ContinuousOn (fun θ : ℝ => ((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ)
          + 2 * (Real.sin θ) ^ 2) (Set.Icc 0 (Real.pi / 2))
        fun_prop
      have h := hA'.mul_continuousOn_of_subset hc hs isCompact_Icc hsub
      refine h.congr_fun (fun θ _ => ?_) hs
      ring
    · have hcoef : (Real.sin θ) ^ 2 ≤ acf θ := sin_sq_le_acoef θ
      calc (Real.sin θ) ^ 2 * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ
          = (Real.sin θ) ^ 2 * ((deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ) := by
            ring
        _ ≤ acf θ * ((deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ) :=
            mul_le_mul_of_nonneg_right hcoef (mul_nonneg (sq_nonneg _) (hsig_nn θ hθ))
        _ = acf θ * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ := by ring
  -- (b) `-M ≤ √Y √X`
  have hMY : -mm ≤ Real.sqrt ys * Real.sqrt xs := by
    have hCint : IntegrableOn (fun θ => Real.sin θ
        * deriv (fun θ => u θ / Real.cos θ) θ * deriv (deriv u) θ * sg θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
      refine MeasureTheory.Integrable.mono'
        (μ := (volume : Measure ℝ).restrict (Set.Ioo 0 (Real.pi / 2))) (hY.add hX)
        (hCcont.aestronglyMeasurable hs) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hs] with θ hθ
      have hsig : 0 ≤ sg θ := hsig_nn θ hθ
      have h2 := two_mul_abs_mul_le (Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ)
        (deriv (deriv u) θ)
      rw [mul_pow] at h2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsig]
      calc |Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ * deriv (deriv u) θ| * sg θ
          ≤ ((Real.sin θ) ^ 2 * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
              + (deriv (deriv u) θ) ^ 2) * sg θ := by
            have hle : |Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ
                * deriv (deriv u) θ|
                ≤ (Real.sin θ) ^ 2 * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
                  + (deriv (deriv u) θ) ^ 2 := by
              linarith [abs_nonneg (Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ
                * deriv (deriv u) θ)]
            exact mul_le_mul_of_nonneg_right hle hsig
        _ = (Real.sin θ) ^ 2 * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ
              + (deriv (deriv u) θ) ^ 2 * sg θ := by ring
    have hdom : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |Real.sin θ
        * deriv (fun θ => u θ / Real.cos θ) θ * deriv (deriv u) θ * sg θ|
        ≤ Real.sqrt ((Real.sin θ) ^ 2 * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
          * Real.sqrt ((deriv (deriv u) θ) ^ 2 * sg θ) := by
      intro θ hθ
      have hsig : 0 ≤ sg θ := hsig_nn θ hθ
      have h1 : Real.sqrt ((Real.sin θ) ^ 2
            * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
          = |Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ| * Real.sqrt (sg θ) := by
        rw [show (Real.sin θ) ^ 2 * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ
            = (Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ by ring]
        exact sqrt_sq_mul_sqrt _ _ hsig
      have h2 : Real.sqrt ((deriv (deriv u) θ) ^ 2 * sg θ)
          = |deriv (deriv u) θ| * Real.sqrt (sg θ) := sqrt_sq_mul_sqrt _ _ hsig
      have h3 : |Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ
            * deriv (deriv u) θ * sg θ|
          = (|Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ| * |deriv (deriv u) θ|)
            * sg θ := by
        rw [abs_mul, abs_of_nonneg hsig, abs_mul]
      rw [h1, h2, h3]
      have key : (|Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ| * Real.sqrt (sg θ))
            * (|deriv (deriv u) θ| * Real.sqrt (sg θ))
          = (|Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ| * |deriv (deriv u) θ|)
            * sg θ := by
        conv_rhs => rw [← sqrt_mul_sqrt_eq (sg θ) hsig]
        ring
      rw [key]
    have hCS := Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
      (s := Set.Ioo 0 (Real.pi / 2))
      (A := fun θ => (Real.sin θ) ^ 2 * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
      (B := fun θ => (deriv (deriv u) θ) ^ 2 * sg θ)
      (C := fun θ => Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ
        * deriv (deriv u) θ * sg θ)
      hY hX hCint
      (fun θ hθ => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hsig_nn θ hθ))
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hsig_nn θ hθ))
      hdom
    rw [← hmm, ← hys, ← hxs] at hCS
    exact le_trans (neg_le_abs _) hCS
  -- (c) `C ≤ 2 B`
  have hCB : c2 ≤ 2 * bs := by
    rw [hc2, hbs, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ hs fun θ hθ => ?_
    · have hc : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Icc 0 (Real.pi / 2)) := by
        fun_prop
      have h := hA.mul_continuousOn_of_subset hc hs isCompact_Icc hsub
      refine h.congr_fun (fun θ _ => ?_) hs
      ring
    · exact hB.const_mul 2
    · have h1 := cos2_mul_div_cos_sq_le (a := u θ) hθ
      have h2 := mul_le_mul_of_nonneg_right h1 (hsig_nn θ hθ)
      calc Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * sg θ ≤ 2 * (u θ) ^ 2 * sg θ := h2
        _ = 2 * ((u θ) ^ 2 * sg θ) := by ring
  -- the identity, in the abbreviations
  have hident' : mm = ((1 - Work.Spaces.eta) / 2) * c2 - em := by
    first
      | exact hident
      | (rw [← hmm, ← hc2, ← hem] at hident; exact hident)
  -- combine
  have hstep : ys ≤ ((1 - Work.Spaces.eta) / 2) * (2 * bs)
      + Real.sqrt ys * Real.sqrt xs := by
    have hcoef : ((1 - Work.Spaces.eta) / 2) * c2 ≤ ((1 - Work.Spaces.eta) / 2) * (2 * bs) :=
      mul_le_mul_of_nonneg_left hCB (by linarith [Work.Spaces.eta_lt_one])
    have hEM : ys ≤ ((1 - Work.Spaces.eta) / 2) * c2 - mm := by linarith [hEY, hident']
    linarith [hEM, hcoef, hMY]
  -- arithmetic
  have hamgm : 2 * (Real.sqrt ys * Real.sqrt xs) ≤ ys + xs := by
    have h1 := Real.sq_sqrt hys_nn
    have h2 := Real.sq_sqrt hxs_nn
    nlinarith [sq_nonneg (Real.sqrt ys - Real.sqrt xs)]
  have hcoef2 : ((1 - Work.Spaces.eta) / 2) * (2 * bs) ≤ bs := by
    have h1 : (1 : ℝ) - Work.Spaces.eta ≤ 1 := by linarith [Work.Spaces.eta_nonneg]
    have h2 : ((1 - Work.Spaces.eta) / 2) * (2 * bs) = (1 - Work.Spaces.eta) * bs := by ring
    rw [h2]
    exact mul_le_of_le_one_left hbs_nn h1
  linarith [hstep, hamgm, hcoef2]

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.step3Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The angular term `u = ∂_θ(tan θ · Ψ)` of Step 3. -/
def uOf (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)

/-- The `I₄`-quantity `P = sin θ · ∂_θ(Ψ/cos θ)` whose norm the positivity `I_{4,2}` controls. -/
def POf (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ

/-- The first-order radial quantity `G = z ∂_z Ψ`. -/
def GOf (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Ψ z θ

/-- The second-order radial quantity `A = z² ∂_zzΨ`. -/
def AOf (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-! ## The pointwise identity `u = Ψ + P` on the open quadrant -/

/-- **The pointwise identity.**  If the `θ`-slice of `Ψ` at `z` is differentiable at `θ` and
`cos θ ≠ 0`, then

  `∂_θ(tan θ · Ψ) = Ψ + sin θ · ∂_θ(Ψ/cos θ)`,

because `tan θ · Ψ = sin θ · (Ψ / cos θ)` and `∂_θ(sin θ · Ψ̄) = cos θ · Ψ̄ + sin θ · Ψ̄'`
with `cos θ · (Ψ/cos θ) = Ψ`. -/
theorem pth_tan_mul_eq_of_diff {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hc : Real.cos θ ≠ 0)
    (hdΨ : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ) :
    Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
      = Ψ z θ + Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ := by
  have htan : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hc
  have hmul := htan.mul hdΨ.hasDerivAt
  have hdiv := hdΨ.hasDerivAt.div (Real.hasDerivAt_cos θ) hc
  have hfuneq : (Real.tan * fun θ' => Ψ z θ') = (fun θ' => Real.tan θ' * Ψ z θ') := rfl
  have hdmul : deriv (fun θ' => Real.tan θ' * Ψ z θ') θ
      = 1 / Real.cos θ ^ 2 * Ψ z θ + Real.tan θ * deriv (fun θ' => Ψ z θ') θ := by
    rw [← hfuneq]; exact hmul.deriv
  have hddiv : deriv (fun θ' => Ψ z θ' / Real.cos θ') θ
      = (deriv (fun θ' => Ψ z θ') θ * Real.cos θ - Ψ z θ * (-Real.sin θ))
        / Real.cos θ ^ 2 := hdiv.deriv
  simp only [Work.Spaces.pth]
  rw [hdmul, hddiv, Real.tan_eq_sin_div_cos]
  have hs : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  field_simp
  ring_nf
  linear_combination (-(Ψ z θ)) * hs

/-- The same identity for a function `C^∞` on the open quadrant, in the hypothesis shape of
`Hon`. -/
theorem pth_tan_mul_eq_open {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
      = Ψ z θ + Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ := by
  have hmem : (z, θ) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) := ⟨hz, hθ0, hθ1⟩
  have hopen : IsOpen (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hdiff : DifferentiableAt ℝ (Function.uncurry Ψ) (z, θ) :=
    ((hsm 1).contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by norm_num)
  refine pth_tan_mul_eq_of_diff ?_ ?_
  · exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  · exact Work.Spaces.differentiableAt_curry_right hdiff

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.MixedFamilyAlpha1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The mixed-derivative family, uniform for `0 < α ≤ 1`

The sibling `Work.EllipticEst.Core.mixedFamily_le` proves the mixed-derivative family
estimate of the interpolation for `0 < α ≤ 1/4`.  Its whole proof, however, only ever uses
`α ≤ 1` (the `α² ≤ 1` that caps the prefactor, and the hypothesis `hα1 : α ≤ 1` of the
per-slot estimate `mixedIntS_integral_le`).  The present file re-runs that assembly with the
exact hypothesis `α ≤ 1` requested by the consumer, so that the estimate holds uniformly on
the full range `(0,1]` of the singular exponent.

Nothing new is proved: the mathematical content is `mixedIntS_integral_le` (the slot
estimate, whose only `α`-hypothesis is `α ≤ 1`), and the rest is the arithmetic of the
assembly.
-/

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false


end Work.FTS.EllipticEst.RPFresh
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.OpIdentDz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open Filter

namespace Work.FTS.EllipticEst.RPFresh

/-- **`∂_θ` commutes with the `D_z`-iterates, pointwise on the open quadrant.**  This is the
Clairaut identity `∂_z∂_θ = ∂_θ∂_z` in the coordinates adapted to `D_z = z ∂_z`, packaged at a
single point: on the open quadrant `pth (DzIter i V) = DzIter i (pth V)` (`Blocks.pth_DzIter_eqOn_Q0`),
and `D_z` only sees the values of its argument on an angular slice, so the congruence can be
evaluated pointwise. -/
theorem pth_DzIter_apply {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (i : ℕ)
    {z θ : ℝ} (hz : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.pth (Work.Spaces.DzIter i V) z θ
      = Work.Spaces.DzIter i (Work.Spaces.pth V) z θ :=
  Work.Blocks.pth_DzIter_eqOn_Q0 hV i hz

theorem OpIdentDz {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (i : ℕ) {z θ : ℝ}
    (hz : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ
      = Work.Spaces.DzIter (i + 1) (Work.Spaces.pth V) z θ := by
  obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hz
  -- `Dz` is computed by a `deriv` along the angular slice, so it only depends on the values of
  -- its argument on a neighbourhood of that slice inside `Q0`.
  have hcongr : Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ
      = Work.Spaces.Dz (Work.Spaces.DzIter i (Work.Spaces.pth V)) z θ := by
    have hev : (fun z' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter i V) z' θ)
        =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.DzIter i (Work.Spaces.pth V) z' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
      exact pth_DzIter_apply hV i (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ0, hθ1⟩)
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [hev.deriv_eq]
  rw [hcongr, Work.Spaces.DzIter_succ]

end Work.FTS.EllipticEst.RPFresh
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ESW.TkChainIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT.ESW

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary facts about the angular weight -/

/-- `sin(2θ) > 0` on the open quadrant. -/
private theorem sin_two_pos_Q0 {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    0 < Real.sin (2 * p.2) := by
  obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- `θ ↦ sin(2θ)^c` is continuous on the open quadrant. -/
private theorem continuousOn_sin_rpow_Q0 (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.EllipticEst.Q0 :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_Q0 hp)))

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private theorem sin_two_nonneg_Iθ_prv {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- A pointwise statement on `Iθ` is an a.e. statement for `volume.restrict Iθ`. -/
private theorem ae_Iθ_of_forall {p : ℝ → Prop} (h : ∀ θ ∈ Work.Spaces.Iθ, p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), p θ :=
  MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc h

/-! ## The pointwise `D_θ`-chain, with no positivity hypothesis on `α`

This is the statement of `remov.selfdth.slot_pointwise_HkIntegrand` with the (vestigial)
hypothesis `0 < α` removed; the proof is the same, since neither the chain of `dthChain_core`
nor the weight identity `slot_sq_eq_Wt_sq` (whose only hypothesis is `sin(2θ) > 0`) refers to
the sign of `α`. -/
theorem slot_pointwise_HkIntegrand_allAlpha (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (v : ℝ → ℝ → ℝ) (K : ℕ), m ≤ K →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m v z θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))
          ≤ C * Work.Spaces.HkIntegrand α K v z θ := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FTS.EllipticEst.remov.selfdth.dthChain_core m hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine ⟨C0 * m, mul_pos hC0pos hmpos, ?_⟩
  intro α v K hmK hsm z hz
  have hz0 : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz0 with hzeq | hzpos
  · -- `z = 0`: the radial weight vanishes, and the right-hand side is nonnegative.
    have hw0 : (Work.Spaces.w z) ^ 2 = 0 := by rw [hzeq.symm]; norm_num [Work.Spaces.w]
    refine Eventually.of_forall (fun θ => ?_)
    rw [hw0, zero_mul]
    exact mul_nonneg (mul_pos hC0pos hmpos).le
      (Work.Spaces.HkIntegrand_nonneg α K v z θ)
  · -- `z > 0`: the genuine pointwise chain.
    refine Work.FTS.EllipticEst.remov.selfdth.ae_mem_Ioo_of_Iθ.mono (fun θ hθ => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    have hcd : ∀ k : ℕ, ContDiffAt ℝ k (Function.uncurry v) (z, θ) := fun k =>
      (hsm k).contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hzpos, hθ⟩)
    rw [Work.FTS.EllipticEst.remov.selfdth.slot_sq_eq_Wt_sq m α z θ v hs]
    have hsum : (∑ r ∈ Finset.Icc 1 m,
          (Work.Spaces.DthIter r v z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2)
        ≤ (m : ℝ) * Work.Spaces.HkIntegrand α K v z θ := by
      have hbd : ∀ r ∈ Finset.Icc 1 m,
          (Work.Spaces.DthIter r v z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α K v z θ := by
        intro r hr
        obtain ⟨hr1, _⟩ := Finset.mem_Icc.mp hr
        simpa only [Work.Spaces.mixed_zero_left, mul_pow] using
          (Work.Spaces.sq_le_HkIntegrand_mixed α K v z θ r 0 hr1 (by omega))
      calc (∑ r ∈ Finset.Icc 1 m,
            (Work.Spaces.DthIter r v z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2)
          ≤ ∑ _r ∈ Finset.Icc 1 m, Work.Spaces.HkIntegrand α K v z θ :=
            Finset.sum_le_sum hbd
        _ = (m : ℝ) * Work.Spaces.HkIntegrand α K v z θ := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    calc ((Real.sin (2 * θ)) ^ m * Work.Spaces.pthIter m v z θ) ^ 2
            * (Work.Spaces.Wt α z θ) ^ 2
        ≤ (C0 * ∑ r ∈ Finset.Icc 1 m, (Work.Spaces.DthIter r v z θ) ^ 2)
            * (Work.Spaces.Wt α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (hC0 v z θ hθ hcd) (sq_nonneg _)
      _ = C0 * ((∑ r ∈ Finset.Icc 1 m, (Work.Spaces.DthIter r v z θ) ^ 2)
            * (Work.Spaces.Wt α z θ) ^ 2) := by ring
      _ = C0 * ∑ r ∈ Finset.Icc 1 m,
            (Work.Spaces.DthIter r v z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 := by
          rw [Finset.sum_mul]
      _ ≤ C0 * ((m : ℝ) * Work.Spaces.HkIntegrand α K v z θ) :=
          mul_le_mul_of_nonneg_left hsum hC0pos.le
      _ = (C0 * m) * Work.Spaces.HkIntegrand α K v z θ := by ring

/-! ## The target -/

theorem TkChainIntegrable {α : ℝ} {K : ℕ} {v : ℝ → ℝ → ℝ} {m : ℕ} (hm : 1 ≤ m) (hmK : m ≤ K)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : Work.Spaces.HkMem α K v) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
        Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
        Work.Spaces.Iz := by
  classical
  obtain ⟨C, hCpos, hC⟩ := slot_pointwise_HkIntegrand_allAlpha m hm
  -- the two intervals are measurable
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  -- the a.e. strong measurability of the slice integrand and of its `z`-integral
  have hv : Work.FTS.EllipticEst.SmoothOpen v := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hσc : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 * (m : ℝ) - Work.Spaces.gam α))
      Work.FTS.EllipticEst.Q0 := continuousOn_sin_rpow_Q0 _
  obtain ⟨hAESM_slice, hAESM_int⟩ := Work.FTS.EllipticEst.SrcBnd.SlotAESM (n := m)
    (σ := fun θ => (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) hv hσc
  -- the same, in the shape of the statement (the constant `w z ^ 2` pulled out of the integral)
  have hAESM_int' : MeasureTheory.AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hAESM_int.congr (Filter.Eventually.of_forall (fun z =>
      MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        ((Work.Spaces.w z) ^ 2)
        (fun θ => (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))))
  -- nonnegativity of a single angular integrand, on `Iθ`
  have hslot_nn : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      0 ≤ (Work.Spaces.pthIter m v z θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α) :=
    fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_prv hθ) _)
  constructor
  · -- first conjunct: the angular slot is integrable on `Iθ` for every `z ∈ Iz`
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
    · -- `z = 0`: the integrand vanishes identically
      subst h0
      have hzero : (fun θ : ℝ => (Work.Spaces.w 0) ^ 2 * ((Work.Spaces.pthIter m v 0 θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
            = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        simp [Work.Spaces.w]
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · -- `z > 0`: dominate by the integrable `HkIntegrand`
      refine ((hmem.1 z hz).const_mul C).mono' (hAESM_slice z hz) ?_
      filter_upwards [hC α v K hmK hsm z hz, MeasureTheory.ae_restrict_mem hIθ] with θ hθ hθmem
      have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)) :=
        mul_nonneg (sq_nonneg _) (hslot_nn z θ hθmem)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hθ
  · -- second conjunct: the angular integral is integrable on `Iz`
    have hmaj : MeasureTheory.IntegrableOn
        (fun z => C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α K v z θ)
        Work.Spaces.Iz := hmem.2.const_mul C
    refine hmaj.mono' hAESM_int' ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIz] with z hzmem
    -- the pointwise (in `z`) bound, by monotonicity of the angular integral
    have hkey : (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α K v z θ) := by
      rw [(MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
            ((Work.Spaces.w z) ^ 2)
            (fun θ => (Work.Spaces.pthIter m v z θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))).symm,
        (MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) C
            (fun θ => Work.Spaces.HkIntegrand α K v z θ)).symm]
      exact MeasureTheory.integral_mono_of_nonneg
        (ae_Iθ_of_forall (fun θ hθ => mul_nonneg (sq_nonneg _) (hslot_nn z θ hθ)))
        ((hmem.1 z hzmem).const_mul C)
        (hC α v K hmK hsm z hzmem)
    have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
        (ae_Iθ_of_forall (fun θ hθ => hslot_nn z θ hθ)))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hkey

end

end Work.FTS.EllipticEst.TT.ESW
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.integrableOn_mixedSummand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- The uncurried mixed summand `(z,θ) ↦ D_z^j D_θ^i F z θ · W(α,z,θ)` is continuous on the
open quadrant, being the product of the continuous uncurried derivative (`SmoothOpen`) and the
continuous weight. -/
private theorem continuousOn_mixedSummand_Q0 {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (α : ℝ) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
  ((hF.mixed j i).continuousOn).mul (Work.FTS.EllipticEst.continuousOn_Wt_Q0 α)

/-- For `z > 0` the angular slice `θ ↦ D_z^j D_θ^i F z θ · W(α,z,θ)` is a.e. strongly
measurable w.r.t. `volume.restrict Iθ`: it is the slice of a function continuous on the open
quadrant (the endpoints of `Iθ` being null). -/
private theorem aesm_slice_mixedSummand {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (α : ℝ) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ)
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2)
    (continuousOn_mixedSummand_Q0 hF α j i) hz

theorem integrableOn_mixedSummand (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ k) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- at `z = 0` the radial factor of the weight vanishes, so the summand is `0`
    subst hz0
    have hzero : (fun θ : ℝ => (Work.Spaces.mixed j i F 0 θ * Work.Spaces.Wt α 0 θ) ^ 2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [Work.Spaces.Wt, Work.Spaces.w]
      norm_num
    rw [hzero]
    exact integrableOn_zero
  · -- at `z > 0` the summand is dominated by the honest integrand `HkIntegrand α k F`
    refine Integrable.mono' (hmem.1 z hz)
      ((aesm_slice_mixedSummand hF α j i hzpos).pow 2) ?_
    refine Eventually.of_forall fun θ => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ i j hi hij

end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.interpGamma_slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# `TT.interpGamma_slots`

The two *slot* comparisons consumed by the assembly `TT.interpGamma_of_core`:

* `TTint α G ≤ HkSq α 0 (pthIter 2 G)`,
* `DDint α G ≤ 2 HkSq α 0 (DzIter 2 G) + 18 HkSq α 0 (DzIter 1 G)`,

where `TTint = ∫∫(∂_θ²G)²w²σ_a`, `DDint = ∫∫(D_z²G + b D_zG)²w²σ_a` with
`σ_a = sin(2θ)^{2-γ(α)}`, `b z = (z-3)/(1+z)`, and the right-hand sides are the *heavy*
`ℋ⁰`-slots against `σ_η = sin(2θ)^{-η}`.

Both follow from the single weight comparison `σ_a ≤ σ_η` on `Iθ` (valid because
`α ≤ 1` gives `2 - γ ≥ 1 - 1/10 > -η`) and the estimate `|b z| ≤ 3`; the `HkMem`
hypotheses make the heavy slots honest, so that the elementary monotonicity lemma for
integrals of nonnegative functions can be applied.
-/

/-! ## The heavy `ℋ⁰`-slot is honest -/



/-! ## The light slot is dominated by the heavy one -/



/-! ## The radial slot `DDint` -/




end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.interp_amgm_rect =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-!
# `TT.interp_amgm_rect`

The weighted Cauchy–Schwarz ("AM–GM") inequality for two functions `P`, `Q` supported in a
rectangle `[A,B] × [c,d] ⊂ (0,∞) × (0,π/2)`:

```
∫_z∫_θ P Q w² σ_a  ≤  √( (∫_z∫_θ P² w² σ_a) (∫_z∫_θ Q² w² σ_a) )
```

with `w z = (1+z)²/z²` the radial weight and `σ_a(θ) = sin(2θ)^{2-γ(α)}` the angular weight
(`γ(α) = 1 + α/10`).

Because the two factors of the square root are nonnegative, this is Cauchy–Schwarz in `L²` for
the measure `dz dθ` restricted to the rectangle, applied to the two functions
`P · w · sin(2θ)^{(2-γ)/2}` and `Q · w · sin(2θ)^{(2-γ)/2}`, whose product is the left-hand
integrand and whose squares are the two right-hand integrands.  The iterated integrals over
`Iz = [0,∞)`, `Iθ = [0,π/2]` are converted into integrals over the product measure on the
rectangle by Fubini (`MeasureTheory.setIntegral_prod`), using the support hypothesis; both
continuity and hence integrability come from `ContinuousOn.integrableOn_compact`.
-/




end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.radial_ibp_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open MeasureTheory


end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.sliceRate_light =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The light-weight slice rate estimate `TT.sliceRate_light`

For `0 < a < 1` and a function `f` of class `C¹` on `(0, π/2)` whose weighted energy

`E(θ) = ∫_{θ' ∈ (0,θ)} (∂f)² sin(2θ')^a`

is finite on the whole interval, the two one-sided limits `lim_{θ→0⁺} f` and
`lim_{θ→π/2⁻} f` exist and the deviation from each of them is controlled by the local energy:

`(f θ - c)² ≤ K θ^{1-a} E(θ)`, resp. `(f θ - c)² ≤ K (π/2 - θ)^{1-a} E'(θ)`,

with a constant `K` depending only on `a`.

## Proof

The weight `w θ = sin(2θ)^a` is positive on `(0, π/2)` and its reciprocal is integrable there
(the exponent `-a` lies in `(-1, 0)` because `a < 1`), with the endpoint bound
`∫_{(0,θ)} w⁻¹ ≤ C θ^{1-a}` (`lightInvBounds`).  Since (`sliceFtcKey`) the difference from the
endpoint value is the integral `f θ - c = ∫_{(0,θ)} ∂f`, Cauchy–Schwarz in the weighted form
`weightedCS` with the split `∂f = (∂f · w^{1/2}) · w^{-1/2}` gives

`(f θ - c)² ≤ (∫_{(0,θ)} (∂f)² w) · (∫_{(0,θ)} w⁻¹) ≤ C θ^{1-a} ∫_{(0,θ)} (∂f)² w`.

Bounding the partial energy by the total energy and letting `θ → 0⁺` (here `θ^{1-a} → 0`
because `a < 1`, `sqBoundTendstoPos`) yields both the existence of the limit and the stated
rate; the right endpoint is the mirror image.  The integrability of `∂f` needed for the
fundamental theorem of calculus is `lightDerivIntegrable`.
-/


end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.slice_ibp_sigA_compact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT


end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EpsEngine.aesm_uncurry_restricted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open MeasureTheory Set

/-- Indicator to a measurable set of an a.e. strongly measurable function (the a.e. statement
being relative to the restriction of the measure to that set) is a.e. strongly measurable for
the unrestricted measure. -/
private lemma aesm_indicator_of_aesm_restrict {A : Set ℝ} (hA : MeasurableSet A) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict A)) :
    AEStronglyMeasurable (A.indicator f) volume := by
  obtain ⟨h, hh, heq⟩ := hf
  refine ⟨A.indicator h, hh.indicator hA, ?_⟩
  have hnull : (volume.restrict A) {x : ℝ | f x ≠ h x} = 0 := ae_iff.mp heq
  rw [Filter.EventuallyEq, ae_iff]
  have hsub : {x : ℝ | ¬ (A.indicator f x = A.indicator h x)}
      ⊆ {x : ℝ | f x ≠ h x} ∩ A := by
    intro x hx
    change ¬ (A.indicator f x = A.indicator h x) at hx
    change f x ≠ h x ∧ x ∈ A
    by_cases hxA : x ∈ A
    · refine ⟨?_, hxA⟩
      intro hfh
      exact hx (by rw [Set.indicator_of_mem hxA f, Set.indicator_of_mem hxA h, hfh])
    · exact absurd (by rw [Set.indicator_of_notMem hxA f, Set.indicator_of_notMem hxA h]) hx
  exact measure_mono_null hsub (by rw [← Measure.restrict_apply' hA]; exact hnull)

/-- **Carathéodory measurability relative to a measurable `s`-set.**  If `g : ℝ → ℝ → ℝ → ℝ` is,
for every `s ∈ A`, continuous on the open quadrant and zero off it, and if for every `(z,θ)` the
map `s ↦ g s z θ` is a.e. strongly measurable for `volume.restrict A`, then `(s,z,θ) ↦ g s z θ`
is a.e. strongly measurable for `(volume.restrict A).prod volume`.  The proof truncates `g` to
`A` (which is Carathéodory on all of `ℝ`) and applies the unrestricted lemma
`aesm_uncurry_of_continuousOn_of_zero`, then uses that the restricted product measure is the
product measure of a measure supported on `A`. -/
theorem aesm_uncurry_restricted {A : Set ℝ} (hA : MeasurableSet A) {g : ℝ → ℝ → ℝ → ℝ}
    (hcont : ∀ s ∈ A, ContinuousOn (fun q : ℝ × ℝ => g s q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzero : ∀ s ∈ A, ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → g s q.1 q.2 = 0)
    (hmeas : ∀ q : ℝ × ℝ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ => g s q.1 q.2)
      (MeasureTheory.volume.restrict A)) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict A).prod MeasureTheory.volume) := by
  classical
  -- truncate `g` to `A`: the resulting `g₁` is Carathéodory on all of `ℝ`
  set g₁ : ℝ → ℝ → ℝ → ℝ := fun s z θ => if s ∈ A then g s z θ else 0 with hg₁
  have hcont₁ : ∀ s : ℝ, ContinuousOn (fun q : ℝ × ℝ => g₁ s q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro s
    by_cases hs : s ∈ A
    · refine (hcont s hs).congr ?_
      intro q _
      simp only [hg₁]
      rw [if_pos hs]
    · have hz : (fun q : ℝ × ℝ => g₁ s q.1 q.2) = fun _ => (0 : ℝ) := by
        funext q
        simp only [hg₁]
        rw [if_neg hs]
      rw [hz]
      exact continuousOn_const
  have hzero₁ : ∀ s : ℝ, ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → g₁ s q.1 q.2 = 0 := by
    intro s q hq
    by_cases hs : s ∈ A
    · have hs' := hzero s hs q hq
      simp only [hg₁]
      rw [if_pos hs, hs']
    · simp only [hg₁]
      rw [if_neg hs]
  have hmeas₁ : ∀ q : ℝ × ℝ, AEStronglyMeasurable (fun s : ℝ => g₁ s q.1 q.2) volume := by
    intro q
    refine (aesm_indicator_of_aesm_restrict hA (hmeas q)).congr ?_
    filter_upwards with s
    simp only [hg₁, Set.indicator_apply]
  have hbig := aesm_uncurry_of_continuousOn_of_zero (g := g₁) hcont₁ hzero₁ hmeas₁
  -- the restricted product measure is supported on `A ×ˢ univ`
  have haeA : ∀ᵐ p ∂((volume.restrict A).prod (volume : Measure (ℝ × ℝ))), p.1 ∈ A := by
    rw [ae_iff]
    have hset : {p : ℝ × (ℝ × ℝ) | ¬ p.1 ∈ A} = Prod.fst ⁻¹' Aᶜ := by
      ext p; simp
    rw [hset]
    have hmap : Measure.map (Prod.fst : ℝ × (ℝ × ℝ) → ℝ)
          (((volume.restrict A).prod (volume : Measure (ℝ × ℝ))))
        = (volume Set.univ) • (volume.restrict A) :=
      Measure.map_fst_prod (μ := volume.restrict A) (ν := (volume : Measure (ℝ × ℝ)))
    have h := Measure.map_apply (μ := (volume.restrict A).prod (volume : Measure (ℝ × ℝ)))
      (f := (Prod.fst : ℝ × (ℝ × ℝ) → ℝ))
      (measurable_fst : Measurable (Prod.fst : ℝ × (ℝ × ℝ) → ℝ)) hA.compl
    rw [hmap, Measure.smul_apply, Measure.restrict_apply' hA] at h
    simp only [Set.compl_inter_self, measure_empty, smul_zero] at h
    exact h.symm
  have hle : ((volume.restrict A).prod (volume : Measure (ℝ × ℝ)))
      ≤ (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  refine (hbig.mono_measure hle).congr ?_
  filter_upwards [haeA] with p hp
  simp only [hg₁]
  rw [if_pos hp]

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.LNA.IntegrableOn_mixed_sq_sGamma =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc.Subcut.LNA

set_option autoImplicit false

/-- The weight `W = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant
(the two endpoints `θ = 0`, `θ = π/2` are excluded there, so `sin(2θ) > 0`). -/
private lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2)
      (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- The squared weighted mixed slice `(D_z^j D_θ^i f z · · W(α,z,·))²` is a.e. strongly
measurable on `Iθ`, for `z > 0`, as soon as `f` is `C^∞` on the *open* quadrant. -/
private lemma aesm_slice_mixed_Wt_sq {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (α : ℝ) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  (Work.Spaces.aesm_slice_of_continuousOn_Qd _
    (((hsm.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)) hz).pow 2

/-- On the open interval the squared weighted mixed slot is `w² · (D_z^b D_θ f)² · sin(2θ)^{-γ}`. -/
private lemma wt_sq_mixed {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ} {z θ : ℝ}
    (hs : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed b 1 f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow,
    Work.FTS.GalBasis.cc.sq_rpow_neg_half (γ := Work.Spaces.gam α) hs]
  ring

/-- Almost every point of `Iθ` is an interior point of the interval. -/
private theorem ae_Ioo_of_restrict_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h := MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
    (b := Real.pi / 2)
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set h]
  exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo


end Work.FTS.GalBasis.cc.Subcut.LNA
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.wwEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary rewritings of the weights -/

/-- `Wt α z θ ^ 2 = w z ^ 2 * sin(2θ)^{-γ}` on the open quadrant. -/
lemma Wt_sq_eq (α : ℝ) {z θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ0 hθ1
  have h : (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
    congr 1
    ring
  rw [h]

/-- The `D_z^b`-summand of `HkIntegrand`, rewritten with the `η`-weight:
`(D_z^b f · w / sin(2θ)^{η/2})^2 = w z ^ 2 * (D_z^b f)^2 * sin(2θ)^{-η}`. -/
lemma slot_eq (b : ℕ) {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (Work.Spaces.DzIter b f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ0 hθ1
  have hT : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
    congr 1
    ring
  rw [div_eq_mul_inv, mul_pow]
  rw [show ((Work.Spaces.w z) * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))⁻¹) ^ 2
      = (Work.Spaces.w z) ^ 2 * (((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2)⁻¹ from by
    rw [mul_pow, inv_pow]]
  rw [hT, ← Real.rpow_neg (le_of_lt hs)]
  ring



/-! ## The pointwise bound on the layer -/


/-! ## The `γ ≤ η` layer bound -/


/-! ## The sequence form of the `γ ≤ η` bound -/




end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.wwLayers =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option maxHeartbeats 1600000



end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.SourcePrep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

/-- The slice energy `z ↦ ∫_θ F z θ ^ 2 cos θ` of an `L²` source is integrable in `z` (its
integral is the double integral of `F ^ 2 cos θ` over the quadrant, which is finite). -/
theorem sigma_integrable {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hL2' : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    show MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      ((MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    rw [Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0]
    exact hL2
  have hprod : (((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)).prod
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ))
      = (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  have hF2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ)) := by
    rw [hprod]; exact hL2'
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2)
      (((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ)) := by
    have h1 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
        (((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)).prod
          ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ)) := by
      rw [hprod, Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0]
      exact hsm.continuousOn.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    exact (h1.pow 2).mul (Real.continuous_cos.comp continuous_snd).aestronglyMeasurable
  have hbound : ∀ᵐ p ∂(((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ)),
      ‖F p.1 p.2 ^ 2 * Real.cos p.2‖ ≤ F p.1 p.2 ^ 2 := by
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc F p.1 p.2 ^ 2 * |Real.cos p.2| ≤ F p.1 p.2 ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one p.2) (sq_nonneg _)
      _ = F p.1 p.2 ^ 2 := by ring
  have hF2cos : MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2)
      (((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ)) :=
    MeasureTheory.Integrable.mono' hF2 hmeas hbound
  simpa only using hF2cos.integral_prod_left

/-- For almost every `z > 0` the angular slice `θ ↦ F z θ` of an `L²` source is a.e. strongly
measurable and its square is integrable against `cos θ` on `Iθ`. -/
theorem ae_slice_facts {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.AEStronglyMeasurable (fun θ => F z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ := by
  have h1 : MeasureTheory.AEStronglyMeasurable (Function.uncurry F)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) := by
    rw [Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0]
    exact hsm.continuousOn.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  have hL2' : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    show MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      ((MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    rw [Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0]
    exact hL2
  have h2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hL2' ?_ ?_
    · exact ((h1.pow 2).mul (Real.continuous_cos.comp continuous_snd).aestronglyMeasurable)
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      calc F p.1 p.2 ^ 2 * |Real.cos p.2| ≤ F p.1 p.2 ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one p.2) (sq_nonneg _)
        _ = F p.1 p.2 ^ 2 := by ring
  exact (Work.FTS.EllipticEst.LevelOneAsm.sliceSM_of_hyp h1).and
    (Work.FTS.EllipticEst.LevelOneAsm.sliceSqInt_of_hyp h2)

end Work.FTS.H2.ModalSolR
end
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.SourceSide.joint_aesm_partialSum_residual =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `π` is *not* pre-bound as `Real.pi` here (`autoImplicit = false`); the `Real` scope is what
-- makes the notation in the statement below resolve to `Real.pi`.
open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR.SourceSide

/-- **The residual of the truncation of the mode series is a.e. strongly measurable on the
closed quadrant.**  The point is that the target measure `volume.restrict (Ioi 0 ×ˢ Icc 0 (π/2))`
agrees with `volume.restrict Q0` (they differ by the null set `Ioi 0 ×ˢ {0, π/2}`), where:

* `F` itself is continuous, hence a.e. strongly measurable (`SmoothOpen F`);
* each mode coefficient `z ↦ cmode m F z` is a.e. strongly measurable in `z` (the
  parameter-dependent-integral lemma `aesm_cmode` of `cmode_memLp`), and pulling it back along
  the projection `Prod.fst` preserves a.e. strong measurability because that projection is
  quasi-measure-preserving for the product measure;
* each `θ ↦ eFam m θ` is continuous.

Only finitely many mode functions enter, so the partial sum, and then the difference with `F`,
are a.e. strongly measurable. -/
theorem joint_aesm_partialSum_residual {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (N : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        - F p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Icc 0 (π / 2))) := by
  -- Replace the closed domain by the `Iθ`-form used throughout the API.
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) := rfl
  rw [← hIθ]
  -- The two domains differ only by the null set `Ioi 0 ×ˢ {0, π/2}`.
  rw [Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0]
  -- `volume.restrict Q0` is a product measure, so `Prod.fst` is quasi-measure-preserving.
  have hQ0prod : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        Work.FTS.EllipticEst.Q0
      = ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi 0)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
    rw [Work.FTS.EllipticEst.Q0, MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact (MeasureTheory.Measure.prod_restrict (Set.Ioi 0) (Set.Ioo 0 (π / 2))).symm
  -- The source datum itself.
  have hF : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        Work.FTS.EllipticEst.Q0) :=
    hsm.continuousOn.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- The truncated mode sum.
  have hS : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        Work.FTS.EllipticEst.Q0) := by
    have hsum : MeasureTheory.AEStronglyMeasurable
        (∑ m ∈ Finset.range (N + 1), fun p : ℝ × ℝ =>
          Work.FTS.PhiStar.Series.cmode m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          Work.FTS.EllipticEst.Q0) :=
      Finset.aestronglyMeasurable_sum (Finset.range (N + 1)) (fun m _ => by
        -- The `z`-dependent factor, pulled back along the first projection.
        have hcm : MeasureTheory.AEStronglyMeasurable
            (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z)
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi 0)) :=
          Work.EllipticEst.ModalSolution.aesm_cmode hsm m
        have hcm1 : MeasureTheory.AEStronglyMeasurable
            (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.cmode m F p.1)
            ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
              Work.FTS.EllipticEst.Q0) := by
          rw [hQ0prod]
          exact hcm.comp_quasiMeasurePreserving
            MeasureTheory.Measure.quasiMeasurePreserving_fst
        -- The angular factor is continuous, hence a.e. strongly measurable.
        have he : MeasureTheory.AEStronglyMeasurable
            (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
            ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
              Work.FTS.EllipticEst.Q0) :=
          ((Work.EllipticEst.ModalSolution.continuous_eFam m).measurable.comp
            measurable_snd).aestronglyMeasurable
        exact hcm1.mul he)
    refine hsum.congr ?_
    filter_upwards with p
    simp only [Finset.sum_apply]
  exact hS.sub hF

end Work.FTS.H2.ModalSolR.SourceSide
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Bridge.Pieces.moment_relation_of_contDiffOn_four =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.MeridianDyn.Bridge.Pieces

set_option maxHeartbeats 1000000

/-! ## The finite-order calculus of the open quadrant

The next three lemmas extract exactly the two properties of the datum that the moment
relation uses.  They are the order-`4` instances of the `C^∞`-statements
`Work.FTS.LocData.contDiffOn_pz` and `Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice`, and
avoid importing the `C^∞` vocabulary altogether. -/

/-- **`∂_z` costs one order.**  `pz` is the first partial of `fderiv ℝ (uncurry ·)` in the
direction `(1,0)`, and `fderiv` of a `C^4` function is `C^3` on an open set. -/
private theorem contDiffOn_pz_three {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 4 (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.Spaces.pz G)) Work.FTS.EllipticEst.Q0 := by
  have hchain : ∀ p ∈ Work.FTS.EllipticEst.Q0, Function.uncurry (Work.Spaces.pz G) p
      = (fderiv ℝ (Function.uncurry G) p) (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp))
  have hfd : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p)
      Work.FTS.EllipticEst.Q0 := by
    have h' := h.fderivWithin (m := 3) Work.FTS.EllipticEst.isOpen_Q0.uniqueDiffOn
      (by norm_num : (3 : WithTop ℕ∞) + 1 ≤ 4)
    refine h'.congr (fun p hp => ?_)
    rw [fderivWithin_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hp]
  have hcomp : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0))
      Work.FTS.EllipticEst.Q0 :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- **The radial slice is differentiable at interior points**, with derivative `∂_z u`. -/
private theorem hasDerivAt_slice_of_four {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 4 (Function.uncurry G) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun z' : ℝ => G z' θ) (Work.Spaces.pz G z θ) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (z, θ) :=
    (h.differentiableOn (by norm_num)).differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))
  have h1 : HasDerivAt (fun z' : ℝ => G z' θ) (deriv (fun z' : ℝ => G z' θ) z) z :=
    (Work.Spaces.differentiableAt_curry_left hd).hasDerivAt
  simpa only [Work.Spaces.pz] using h1

/-- Continuity of `r ↦ ∂_z u r θ` on `(0,∞)`, at an interior angle. -/
private theorem continuousOn_pz_slice_of_four {u : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousOn (fun r : ℝ => Work.Spaces.pz u r θ) (Set.Ioi 0) := by
  have hpc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_pz_three h).continuousOn
  have hcurve : ContinuousOn (fun r : ℝ => (r, θ)) (Set.Ioi 0) :=
    (continuous_id.prodMk continuous_const).continuousOn
  exact hpc.comp hcurve (fun r hr =>
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hr, hθ.1, hθ.2⟩)

/-! ## The radial fundamental rule of calculus on a slice -/

/-- **The `z`-slice moment.**  For `u` of class `C^4` on the open quadrant, an interior angle
`θ ∈ (0,π/2)` and `0 < a < b`, the integral over `[a,b]` of `∂_z u(·,θ) · sinθcos²θ` is
`(u b θ - u a θ) · sinθcos²θ`. -/
private theorem integral_Icc_pz_mul_sinCos2_of_four (u : ℝ → ℝ → ℝ)
    (h : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    {a b θ : ℝ} (ha : 0 < a) (hab : a < b) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ
      = (u b θ - u a θ) * Work.Elliptic.sinCos2 θ := by
  have hcont : ContinuousOn (fun r : ℝ => Work.Spaces.pz u r θ) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]
    exact (continuousOn_pz_slice_of_four h hθ).mono
      (fun r hr => lt_of_lt_of_le ha hr.1)
  have hderiv : ∀ r ∈ Set.uIcc a b,
      HasDerivAt (fun r' : ℝ => u r' θ) (Work.Spaces.pz u r θ) r := by
    intro r hr
    rw [Set.uIcc_of_le hab.le] at hr
    exact hasDerivAt_slice_of_four h (lt_of_lt_of_le ha hr.1) hθ
  have hFTC : ∫ s in Set.Icc a b, Work.Spaces.pz u s θ = u b θ - u a θ := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [← hFTC]
  exact MeasureTheory.integral_mul_const _ _

/-! ## Joint integrability of the moment integrand on the box -/

/-- **Joint integrability of `∂_z u · sinθcos²θ` on a radial box.**  From the weighted
`L²`-integrability of `∂_z u` (`hbox`, weight `sin(2θ)^{-η}`) and the joint continuity of
`∂_z u` on `Q0` (which order `4` gives), the product `∂_z u · sinθcos²θ` is jointly integrable
on `[a,b] × Iθ`.

The bound is AM–GM applied to `∂_z u · sinθcos²θ = (∂_z u · sin(2θ)^{-η/2}) ·
(sinθcos²θ · sin(2θ)^{η/2})`; since `|sinθcos²θ| ≤ 1` and `0 ≤ sin(2θ) ≤ 1` on `Iθ`, the
second factor is bounded by `1` and the square of the first is `(∂_z u)² sin(2θ)^{-η}`,
whence `|∂_z u · sinθcos²θ| ≤ ½ (∂_z u)² sin(2θ)^{-η} + ½`. -/
private theorem integrableOn_box_pz_mul_sinCos2_of_four (u : ℝ → ℝ → ℝ)
    (h : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  have hηne : -(Work.Spaces.eta) ≠ 0 := by norm_num [Work.Spaces.eta]
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_pz_three h).continuousOn).mul
      (((by unfold Work.Elliptic.sinCos2; fun_prop :
        Continuous Work.Elliptic.sinCos2).comp continuous_snd).continuousOn)
  have hvolFin : volume (Set.Icc a b ×ˢ Work.Spaces.Iθ) < ⊤ :=
    (isCompact_Icc.prod (by rw [Work.Spaces.Iθ]; exact isCompact_Icc)).measure_lt_top
  have hfin : IsFiniteMeasure (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :=
    isFiniteMeasure_restrict.mpr hvolFin.ne
  have hbase : Integrable (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) := hbox a b ha hab
  have hdom : Integrable (fun p : ℝ × ℝ => (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2)
      (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :=
    (hbase.const_mul (1 / 2)).add (integrable_const (1 / 2))
  have hsub : Set.Icc a b ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
    Set.prod_mono (fun x hx => le_trans (le_of_lt ha) hx.1) subset_rfl
  have hmono : volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)
      ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono hsub le_rfl
  have haesm : AEStronglyMeasurable
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      hcont).mono_measure hmono
  have hpt : ∀ᵐ p ∂(volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)),
      ‖Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) p‖
        ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2 := by
    rw [MeasureTheory.ae_restrict_iff' (s := Set.Icc a b ×ˢ Work.Spaces.Iθ)
      (measurableSet_Icc.prod measurableSet_Icc)]
    refine Filter.Eventually.of_forall fun p hp => ?_
    have hθ : p.2 ∈ Work.Spaces.Iθ := hp.2
    have hx0 : 0 ≤ Real.sin (2 * p.2) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
    have hx1 : Real.sin (2 * p.2) ≤ 1 := Real.sin_le_one _
    -- `|sinθcos²θ| ≤ 1`
    have hC : |Work.Elliptic.sinCos2 p.2| ≤ 1 := by
      rw [Work.Elliptic.sinCos2, abs_mul]
      have h1 : |Real.sin p.2| ≤ 1 := Real.abs_sin_le_one p.2
      have h2 : |Real.cos p.2 ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (sq_nonneg (Real.cos p.2))]
        nlinarith [Real.abs_cos_le_one p.2, abs_nonneg (Real.cos p.2), sq_abs (Real.cos p.2)]
      calc |Real.sin p.2| * |Real.cos p.2 ^ 2| ≤ 1 * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    show ‖Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
        ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2
    -- AM–GM for the radial factor
    have hAF : |Work.Spaces.pz u p.1 p.2|
        ≤ (1 / 2) * (Work.Spaces.pz u p.1 p.2) ^ 2 + 1 / 2 := by
      nlinarith [sq_abs (Work.Spaces.pz u p.1 p.2),
        sq_nonneg (|Work.Spaces.pz u p.1 p.2| - 1)]
    by_cases hx : Real.sin (2 * p.2) = 0
    · -- at the degenerate angles `sinθcos²θ` vanishes and the weight kills the other term
      have hC0 : Work.Elliptic.sinCos2 p.2 = 0 := by
        have h2 : Real.sin p.2 * Real.cos p.2 = 0 := by
          have h3 := Real.sin_two_mul p.2
          rw [hx] at h3
          linarith
        rw [Work.Elliptic.sinCos2]
        rcases mul_eq_zero.mp h2 with hh | hh
        · rw [hh, zero_mul]
        · rw [pow_two, hh, mul_zero, mul_zero]
      rw [hC0, hx, Real.zero_rpow hηne]
      simp only [mul_zero, norm_zero]
      norm_num
    · have hxpos : 0 < Real.sin (2 * p.2) := lt_of_le_of_ne hx0 (Ne.symm hx)
      -- the weight `sin(2θ)^{-η}` is at least `1`
      have hxle : 1 ≤ (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
        have h1 : (Real.sin (2 * p.2)) ^ (Work.Spaces.eta) ≤ 1 :=
          Real.rpow_le_one hx0 hx1 (by norm_num [Work.Spaces.eta])
        have h2 : 0 < (Real.sin (2 * p.2)) ^ (Work.Spaces.eta) := Real.rpow_pos_of_pos hxpos _
        rw [Real.rpow_neg hxpos.le]
        exact (one_le_inv₀ h2).mpr h1
      have hstep : ‖Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
          ≤ |Work.Spaces.pz u p.1 p.2| := by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) hC
      have hle2 : (1 / 2) * (Work.Spaces.pz u p.1 p.2) ^ 2 + 1 / 2
          ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2 := by
        have h4 := mul_le_mul_of_nonneg_left hxle (sq_nonneg (Work.Spaces.pz u p.1 p.2))
        nlinarith
      linarith
  exact Integrable.mono' hdom haesm hpt

/-! ## The target -/

/-- **The angular moment is an antiderivative of its `z`-derivative**, at smoothness order `4`.

For `u` of class `C^4` on the open quadrant `(0,∞) × (0,π/2)` whose `θ`-slices against
`sinθcos²θ` are integrable (`hsl`) and whose weighted square `(∂_z u)² sin(2θ)^{-η}` is
integrable on every box `[a,b] × Iθ` with `0 < a < b` (`hbox`):

`F_*(u)(b) = F_*(u)(a) + ∫_a^b (∫_θ ∂_z u(s,θ) sinθcos²θ dθ) ds`,
i.e. `d/dz F_*(u)(z) = ∫_θ ∂_z u(z,θ) sinθcos²θ dθ`, with
`F_*(u)(z) = ∫_θ u(z,θ) sinθcos²θ dθ` (`Work.Elliptic.Fstar`). -/
theorem moment_relation_of_contDiffOn_four (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    (hsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Work.Elliptic.Fstar u b = Work.Elliptic.Fstar u a
      + ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) := by
  have hb : 0 < b := lt_trans ha hab
  -- joint integrability of the moment integrand on the box
  have hjoint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) :=
    integrableOn_box_pz_mul_sinCos2_of_four u hu hbox ha hab
  -- the slice identity holds for a.e. angle
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
        = (u b θ - u a θ) * Work.Elliptic.sinCos2 θ := by
    have hst : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
    rw [MeasureTheory.Measure.restrict_congr_set hst]
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Set.Ioo 0 (Real.pi / 2))
      measurableSet_Ioo] with θ hθ
    exact integral_Icc_pz_mul_sinCos2_of_four u hu ha hab hθ
  -- Fubini, then the `θ`-integral of the difference
  have hkey : ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
      = Work.Elliptic.Fstar u b - Work.Elliptic.Fstar u a := by
    rw [Work.FTS.EllipticEst.Blocks.integral_Icc_integral_Itheta_swap hjoint]
    calc ∫ θ in Work.Spaces.Iθ,
          (∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ, (u b θ - u a θ) * Work.Elliptic.sinCos2 θ :=
          MeasureTheory.integral_congr_ae hae
      _ = ∫ θ in Work.Spaces.Iθ,
            (u b θ * Work.Elliptic.sinCos2 θ - u a θ * Work.Elliptic.sinCos2 θ) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
          ring
      _ = (∫ θ in Work.Spaces.Iθ, u b θ * Work.Elliptic.sinCos2 θ)
            - (∫ θ in Work.Spaces.Iθ, u a θ * Work.Elliptic.sinCos2 θ) :=
          MeasureTheory.integral_sub (hsl b hb) (hsl a ha)
      _ = Work.Elliptic.Fstar u b - Work.Elliptic.Fstar u a := rfl
  linarith [hkey]

end Work.FTS.MeridianDyn.Bridge.Pieces
end
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Bridge.Pieces.pzMoment_le_sqrt_of_contDiffOn_four =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Bridge.Pieces

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.CoercivityFix.Coer1T.Hardy (slU slV slU_mul_slV slV_sq_le
  abs_setIntegral_mul_le_sqrt w_pos_of_pos one_le_mul_w sin_two_pos_of_mem_Ioo continuousOn_slV)

/-! ## Continuity of the first Cauchy–Schwarz factor from `C⁴`-smoothness -/

/-- The angular slice `θ ↦ D_z f(z,θ)·w(z)/sin(2θ)^{η/2}` is continuous on the open
interval, for `f` of class `C⁴` on the open quadrant and `z > 0`.

This is the only place where the smoothness hypothesis of `pzMoment_le_sqrt` is used: the
slice continuity there follows from `SmoothQuad`, and here from `ContDiffOn ℝ 4 … Q0`
through `Work.Spaces.uncurry_partial_c1` applied to the `C²`-reduction of `hC`. -/
theorem continuousOn_slU_of_contDiffOn_four {f : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    {s : ℝ} (hs : 0 < s) :
    ContinuousOn (slU f s) (Set.Ioo 0 (Real.pi / 2)) := by
  -- `f` is `C²`, hence `∂_z f` is `C¹` on the open quadrant
  have h2 : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    hC.of_le (by norm_num)
  have hpz : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz f))
      Work.FTS.EllipticEst.Q0 :=
    (Work.Spaces.uncurry_partial_c1 Work.FTS.EllipticEst.isOpen_Q0 h2).1
  -- the angular slice of `∂_z f` at `s > 0`
  have hslice : ContinuousOn (fun θ : ℝ => Work.Spaces.pz f s θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hcomp : ContinuousOn
        ((Function.uncurry (Work.Spaces.pz f)) ∘ (fun θ : ℝ => (s, θ)))
        (Set.Ioo 0 (Real.pi / 2)) :=
      ContinuousOn.comp' (g := Function.uncurry (Work.Spaces.pz f))
        (f := fun θ : ℝ => (s, θ)) hpz.continuousOn
        ((continuous_const.prodMk continuous_id).continuousOn)
        (fun θ hθ => ⟨hs, hθ⟩)
    have hslice_eq : (fun θ : ℝ => Work.Spaces.pz f s θ)
        = (Function.uncurry (Work.Spaces.pz f)) ∘ (fun θ : ℝ => (s, θ)) := rfl
    rwa [hslice_eq]
  -- `D_z f = z ∂_z f`
  have hDz1 : Work.Spaces.DzIter 1 f = Work.Spaces.Dz f := by
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  have hDz : ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter 1 f s θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hDz1]
    exact continuousOn_const.mul hslice
  -- the angular weight `w(s)/sin(2θ)^{η/2}`
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hrpow : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hθ)))
  have hdiv : ContinuousOn (fun θ : ℝ => Work.Spaces.w s
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_const.div hrpow (fun θ hθ =>
      ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo hθ) _))
  exact hDz.mul hdiv

/-! ## The moment bound -/

theorem pzMoment_le_sqrt_of_contDiffOn_four (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ s : ℝ, 0 < s →
      |∫ θ in Work.Spaces.Iθ, Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ|
        ≤ Real.sqrt (Real.pi / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ) := by
  intro s hs
  -- ## The open interval carries all the measure
  have hIoo_sub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hIoo_meas : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hms : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    apply Measure.restrict_congr_set
    rw [ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [show (Work.Spaces.Iθ : Set ℝ) = Set.Icc 0 (Real.pi / 2) from rfl,
        Set.Icc_sdiff_Ioo_same (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
      rw [Set.insert_eq]
      exact measure_union_null (measure_singleton 0) (measure_singleton _)
    · rw [show (Work.Spaces.Iθ : Set ℝ) = Set.Icc 0 (Real.pi / 2) from rfl,
        Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, measure_empty]
  -- ## Integrability of the `ℋ⁴`-integrand
  have hHmem : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f s θ) Work.Spaces.Iθ :=
    hmem.1 s (le_of_lt hs)
  have hHmem_oo : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f s θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hHmem.mono_set hIoo_sub
  -- ## The two `L²` factors
  have hcontU : ContinuousOn (slU f s) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_slU_of_contDiffOn_four hC hs
  have hcontV : ContinuousOn (slV f s) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_slV f s
  have hUaesm : AEStronglyMeasurable (slU f s)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hcontU.aestronglyMeasurable hIoo_meas
  have hVaesm : AEStronglyMeasurable (slV f s)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hcontV.aestronglyMeasurable hIoo_meas
  -- the square of `slU` is the `i = 1` summand of `HkIntegrand`
  have hU2int : Integrable (fun θ => (slU f s θ) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    Integrable.mono' hHmem_oo ((hcontU.pow 2).aestronglyMeasurable hIoo_meas)
      (Eventually.of_forall fun θ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ 1 (by norm_num))
  have hUm : MemLp (slU f s) 2 (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (memLp_two_iff_integrable_sq hUaesm).mpr hU2int
  -- the square of `slV` is bounded by the constant `(1/w(s))²`
  have hV2int : Integrable (fun θ => (slV f s θ) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    Integrable.mono' (integrable_const ((1 / Work.Spaces.w s) ^ 2))
      ((hcontV.pow 2).aestronglyMeasurable hIoo_meas)
      (by
        filter_upwards [ae_restrict_mem hIoo_meas] with θ hθ
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact slV_sq_le hs hθ)
  have hVm : MemLp (slV f s) 2 (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (memLp_two_iff_integrable_sq hVaesm).mpr hV2int
  -- ## Cauchy–Schwarz
  have hcs : |∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), slU f s θ * slV f s θ|
      ≤ Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (slU f s θ) ^ 2)
        * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (slV f s θ) ^ 2) :=
    abs_setIntegral_mul_le_sqrt hUm hVm
  have hUV : ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), slU f s θ * slV f s θ
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          Work.Spaces.DzIter 1 f s θ * Work.Elliptic.sinCos2 θ :=
    setIntegral_congr_fun hIoo_meas fun θ hθ => slU_mul_slV hs hθ
  -- ## The key identity: the moment is `1/s` times the Cauchy–Schwarz integral
  have h1 : ∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter 1 f s θ * Work.Elliptic.sinCos2 θ
      = s * ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun hIθ_meas (fun θ _ => ?_)
    show s * Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ
      = s * (Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ)
    ring
  have h2 : ∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter 1 f s θ * Work.Elliptic.sinCos2 θ
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), slU f s θ * slV f s θ := by
    rw [hms]
    exact setIntegral_congr_fun hIoo_meas fun θ hθ => (slU_mul_slV hs hθ).symm
  have hkey : ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ
      = (1 / s) * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), slU f s θ * slV f s θ := by
    have h3 : s * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), slU f s θ * slV f s θ := by
      rw [← h1, h2]
    rw [← h3, ← mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hs), one_mul]
  -- ## Abbreviations for the four scalar quantities of the final estimate
  set AU := ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (slU f s θ) ^ 2 with hAU
  set AV := ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (slV f s θ) ^ 2 with hAV
  set HH := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ with hHH
  set W := Work.Spaces.w s with hW
  set A := Real.sqrt AU with hA
  set VV := Real.sqrt AV with hVV
  set B := Real.sqrt (Real.pi / 2) with hB
  set H := Real.sqrt HH with hH
  -- ## The two square-root bounds
  have hU2sqrt : A ≤ H := by
    apply Real.sqrt_le_sqrt
    rw [hHH, hms]
    exact integral_mono hU2int hHmem_oo.integrable
      (fun θ => Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ 1 (by norm_num))
  have hV2_le : AV ≤ (1 / W) ^ 2 * (Real.pi / 2) := by
    rw [hAV, hW]
    have hvol : volume (Set.Ioo (0 : ℝ) (Real.pi / 2)) < ⊤ := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    have h := norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Ioo (0 : ℝ) (Real.pi / 2))
      (f := fun θ => (slV f s θ) ^ 2) (C := (1 / Work.Spaces.w s) ^ 2) hvol
      (fun θ hθ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact slV_sq_le hs hθ)
    rwa [Measure.real_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0), sub_zero,
      Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => sq_nonneg _)] at h
  have hV2sqrt : VV ≤ B * (1 / W) := by
    have hstep : Real.sqrt AV ≤ Real.sqrt ((1 / W) ^ 2 * (Real.pi / 2)) :=
      Real.sqrt_le_sqrt hV2_le
    have hrew : Real.sqrt ((1 / W) ^ 2 * (Real.pi / 2)) = B * (1 / W) := by
      rw [hB, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (le_of_lt (one_div_pos.mpr (w_pos_of_pos hs))), mul_comm]
    rw [hrew] at hstep
    exact hstep
  -- ## The numerical core
  have hH0 : 0 ≤ H := Real.sqrt_nonneg _
  have hWpos : 0 < W := w_pos_of_pos hs
  have hSW : 1 ≤ s * W := one_le_mul_w hs
  have hSWpos : 0 < s * W := lt_of_lt_of_le zero_lt_one hSW
  have hfin : (1 / s) * (A * (B * (1 / W))) ≤ B * H := by
    have hB1W : 0 ≤ B * (1 / W) :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt (one_div_pos.mpr hWpos))
    have hmul : A * (B * (1 / W)) ≤ H * (B * (1 / W)) :=
      mul_le_mul_of_nonneg_right hU2sqrt hB1W
    have hmain : (1 / s) * (H * (B * (1 / W))) = (H * B) / (s * W) := by
      field_simp
    have h2le : (H * B) / (s * W) ≤ B * H := by
      rw [div_le_iff₀ hSWpos]
      calc H * B ≤ H * B * (s * W) :=
            le_mul_of_one_le_right (mul_nonneg hH0 (Real.sqrt_nonneg _)) hSW
        _ = (B * H) * (s * W) := by ring
    calc (1 / s) * (A * (B * (1 / W))) ≤ (1 / s) * (H * (B * (1 / W))) :=
          mul_le_mul_of_nonneg_left hmul (le_of_lt (one_div_pos.mpr hs))
      _ = (H * B) / (s * W) := hmain
      _ ≤ B * H := h2le
  -- ## Assembly
  calc |∫ θ in Work.Spaces.Iθ, Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ|
      = (1 / s) * |∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), slU f s θ * slV f s θ| := by
        rw [hkey, abs_mul, abs_of_pos (one_div_pos.mpr hs)]
    _ ≤ (1 / s) * (A * VV) :=
        mul_le_mul_of_nonneg_left hcs (le_of_lt (one_div_pos.mpr hs))
    _ ≤ (1 / s) * (A * (B * (1 / W))) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (one_div_pos.mpr hs))
        exact mul_le_mul_of_nonneg_left hV2sqrt (Real.sqrt_nonneg _)
    _ ≤ B * H := hfin

end Work.FTS.MeridianDyn.Bridge.Pieces
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Bridge.Pieces.pzSqSeta_box_integrable_of_contDiffOn_four =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Bridge.Pieces

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Continuity on the open quadrant, from four continuous derivatives -/

/-- **The plain `z`-derivative of a `C⁴` datum on the open quadrant is continuous.**
`pz f` is the directional derivative of `Function.uncurry f` in the direction `(1,0)`, which on
the open quadrant `Q0` is `fderiv ℝ (Function.uncurry f) p (1,0)`.  Four continuous derivatives
give that `fderiv ℝ (Function.uncurry f)` is `C³` on `Q0` (via `ContDiffOn.fderivWithin` plus
`fderivWithin_of_isOpen`), hence continuous, and evaluation at the fixed vector `(1,0)`
preserves continuity. -/
private theorem continuousOn_pz_of_contDiffOn_four {f : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hfd : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry f) p)
      Work.FTS.EllipticEst.Q0 := by
    have h' := hC.fderivWithin Work.FTS.EllipticEst.isOpen_Q0.uniqueDiffOn (m := 3)
      (by norm_num)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hp]
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) p) ((1 : ℝ), (0 : ℝ)))
      Work.FTS.EllipticEst.Q0 :=
    hfd.continuousOn.clm_apply
      (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ))) _)
  refine hcont.congr ?_
  intro p hp
  exact Work.Spaces.pz_eq_fderiv ((hC.differentiableOn (by norm_num)).differentiableAt
    (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp))

/-- `θ ↦ sin(2θ)^c` is continuous on the open quadrant, where `sin(2θ) > 0`. -/
private theorem continuousOn_sin_rpow_Q0 (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      Work.FTS.EllipticEst.Q0 := by
  have hpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    rw [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hpos p hp)))

/-- The `D_z`-slot integrand `(D_z f · w/sin(2θ)^{η/2})²` of the `ℋ¹`-integrand is continuous
on the open quadrant, as soon as `pz f` is. -/
private theorem continuousOn_Dz1slot_Q0 {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz f p.1 p.2)
      Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.FTS.EllipticEst.Q0 := by
  have hDz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter 1 f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.DzIter 1 f p.1 p.2)
        = fun p : ℝ × ℝ => p.1 * Work.Spaces.pz f p.1 p.2 := by
      funext p
      simp [Work.Spaces.DzIter, Work.Spaces.Dz]
    rw [hfun]
    exact continuousOn_fst.mul hcont
  exact (hDz.mul Work.FTS.EllipticEst.continuousOn_wdivsin_Q0).pow 2

/-- The target integrand `(∂_z f)² · sin(2θ)^{-η}` is continuous on the open quadrant, as soon
as `pz f` is. -/
private theorem continuousOn_pzSqSeta_Q0 {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz f p.1 p.2)
      Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pz f p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) Work.FTS.EllipticEst.Q0 :=
  (hcont.pow 2).mul (continuousOn_sin_rpow_Q0 _)

/-! ## Integrability of the `D_z`-slot on the product measure -/

/-- The first `D_z`-slot of the `ℋ⁴`-integrand is integrable for the product of the two
restricted Lebesgue measures `(volume|_[0,∞)) × (volume|_Iθ)`.

`Work.Spaces.integrable_prod_of_iterated` (Tonelli) reduces this to the angular slices and the
iterated integral: both are obtained from `hmem` by the pointwise bound
`Work.Spaces.sq_le_HkIntegrand_z`, and the a.e. strong measurability of the uncurried slot
comes from its continuity on the open quadrant (`hcont`).  The value at `z = 0` is irrelevant
(the radial weight vanishes there), but it costs nothing to handle it. -/
private theorem integrable_Dz1slot_prod (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter 1 f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hcont := continuousOn_Dz1slot_Q0 (continuousOn_pz_of_contDiffOn_four hC)
  have hAESM : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  refine (Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ : ℝ => (Work.Spaces.DzIter 1 f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (fun z θ => sq_nonneg _) hAESM ?_ ?_).1
  · -- the angular slices are integrable, with the `ℋ⁴`-integrand as dominating function
    refine MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) fun z hz => ?_
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · -- at `z = 0` the radial weight vanishes, so the slice is identically zero
      rw [← hz0]
      rw [show (fun θ : ℝ => (Work.Spaces.DzIter 1 f 0 θ
          * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          = fun _ : ℝ => (0 : ℝ) from by
        funext θ
        rw [Work.Spaces.w]
        norm_num]
      exact integrableOn_zero
    · refine MeasureTheory.Integrable.mono' (hmem.1 z hz) ?_ ?_
      · simpa only [Function.uncurry_apply_pair] using
          (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos)
      · rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
          rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
        exact Eventually.of_forall fun θ _ => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ 1 (by norm_num)
  · -- the iterated integral is dominated by the iterated integral of `HkIntegrand`
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 1 f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      hAESM.integral_prod_right'
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    refine hmem.2.mono' haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with s hs
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
    exact MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => sq_nonneg _)
      (hmem.1 s hs)
      (MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from by
          rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
        (fun θ _ => Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ 1 (by norm_num)))

/-! ## The statement -/

theorem pzSqSeta_box_integrable_of_contDiffOn_four (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn
        (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz f s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  have hpzcont := continuousOn_pz_of_contDiffOn_four hC
  intro a b ha hab
  set K : ℝ := b ^ 2 / (1 + a) ^ 4 with hKdef
  -- the `D_z`-slot integrand, integrable on the whole domain
  have hGint := integrable_Dz1slot_prod α hC hmem
  -- the box is contained in the domain `Iz ×ˢ Iθ`
  have hsub : Set.Icc a b ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    intro p hp
    rw [Set.mem_prod] at hp
    exact ⟨le_trans (le_of_lt ha) hp.1.1, hp.2⟩
  -- hence the `D_z`-slot integrand is integrable on the box
  have hGbox : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter 1 f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict] at hGint
    exact hGint.mono_measure (MeasureTheory.Measure.restrict_mono hsub le_rfl)
  refine MeasureTheory.Integrable.mono' (hGbox.const_mul K) ?_ ?_
  · -- a.e. strong measurability of the target on the box
    have hA := Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_pzSqSeta_Q0 hpzcont)
    rw [MeasureTheory.Measure.prod_restrict] at hA
    exact hA.mono_measure (MeasureTheory.Measure.restrict_mono hsub le_rfl)
  · -- the pointwise box bound
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hp
    obtain ⟨z, θ⟩ := p
    have hsin : 0 ≤ Real.sin (2 * θ) := by
      refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
      · linarith [hθ.1]
      · linarith [hθ.2, Real.pi_pos]
    have hnn : 0 ≤ (Work.Spaces.pz f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _)
    show ‖(Work.Spaces.pz f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))‖
      ≤ K * (Work.Spaces.DzIter 1 f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
    rw [Real.norm_of_nonneg hnn, hKdef]
    exact Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces.pzSqSeta_le_Dz1_mul
      (f := f) ha hab z hz θ hθ

end

end Work.FTS.MeridianDyn.Bridge.Pieces
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Bridge.Pieces.slice_sinCos2_integrable_of_contDiffOn_four =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.MeridianDyn.Bridge.Pieces

set_option autoImplicit false

/-! ## Elementary auxiliary facts -/

/-- The angular profile `sinθcos²θ` is continuous. -/
private theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop

/-- The angular factor `θ ↦ w z / sin(2θ)^{η/2}` is measurable. -/
private theorem measurable_angularWeight (z : ℝ) :
    Measurable (fun θ : ℝ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  exact measurable_const.div (hsin.pow_const _)

/-- The angular interval `Iθ = [0,π/2]` has finite Lebesgue measure. -/
private theorem volume_Iθ_lt_top : (volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-! ## The main statement -/

theorem slice_sinCos2_integrable_of_contDiffOn_four {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => f z θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ := by
  intro z hz
  -- `C⁴` on the open quadrant gives continuity there
  have hu : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hC.continuousOn
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- almost everywhere strong measurability of the angular slice of `f`
  have haesm_f : AEStronglyMeasurable (fun θ : ℝ => f z θ) (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f) hu hz
  -- the weighted square `(f z θ · w z / sin(2θ)^{η/2})²` is the `i = 0` summand of the
  -- `ℋ⁴`-integrand at `z`, hence integrable
  have hterm : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ := by
    refine (hmem.1 z hzIz).mono' ?_ ?_
    · exact (haesm_f.mul (measurable_angularWeight z).aestronglyMeasurable).pow 2
    · refine Eventually.of_forall fun θ => ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ 0 (by norm_num)
  -- the dominating function of the AM–GM bound: the weighted square plus the constant `1`
  have hdom : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1) Work.Spaces.Iθ :=
    hterm.add (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ)
      (ne_of_lt volume_Iθ_lt_top))
  refine hdom.mono' ?_ ?_
  · exact haesm_f.mul continuous_sinCos2.measurable.aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_forall_mem hIθ fun θ hθ => ?_
    rw [Real.norm_eq_abs]
    exact Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted hz hθ

end Work.FTS.MeridianDyn.Bridge.Pieces
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow10aux.phiSelfFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.NRow10aux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Smoothness of `φ` on the open quadrant -/

theorem phiSelf_smoothOpen :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => Work.FTS.NonlinRows.NRow10aux.phiF z) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 / (1 + p.1))
    Work.FTS.EllipticEst.Q0
  refine contDiffOn_fst.div (contDiffOn_const.add contDiffOn_fst) ?_
  intro p hp
  have hp1 : (0 : ℝ) < 1 + p.1 := by
    have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    linarith
  positivity

/-! ## The explicit values of the iterated derivatives

The denominators are written as iterated products (never as powers) so that the
`deriv`-computations match the stated function forms syntactically. -/

/-- The explicit rational forms of `DzdIter b φ`, `b ≤ 4`.  (The last arm is the `b = 4`
form, which is also what the default arm of the pattern match returns for `b > 4`; only
`b ≤ 4` is ever used.) -/
def phiQ : ℕ → ℝ → ℝ
  | 0 => fun z => z / (1 + z)
  | 1 => fun z => z / ((1 + z) * (1 + z))
  | 2 => fun z => z * (1 - z) / (((1 + z) * (1 + z)) * (1 + z))
  | 3 => fun z => z * (1 - 4 * z + z * z) / ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z))
  | _ => fun z => z * (1 - 11 * z + 11 * (z * z) - z * z * z)
      / (((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) * (1 + z))

/-! ### The one-variable derivative facts -/

private theorem dPhi_id (z : ℝ) : deriv (fun z : ℝ => z) z = 1 := by
  simpa using congrFun deriv_id'' z

private theorem dPhi_1add (z : ℝ) : deriv (fun z : ℝ => 1 + z) z = 1 := by
  have h : deriv (fun z : ℝ => 1 + z) z = deriv (fun z : ℝ => z) z :=
    deriv_const_add (x := z) (f := fun z : ℝ => z) (1 : ℝ)
  rw [h]; exact dPhi_id z

private theorem dPhi_1sub (z : ℝ) : deriv (fun z : ℝ => 1 - z) z = -1 := by
  have h : deriv (fun z : ℝ => 1 - z) z = - deriv (fun z : ℝ => z) z :=
    deriv_const_sub (x := z) (f := fun z : ℝ => z) (1 : ℝ)
  rw [h, dPhi_id]

private theorem dPhi_4z (z : ℝ) : deriv (fun z : ℝ => 4 * z) z = 4 := by
  have h : deriv (fun z : ℝ => 4 * z) z = 4 * deriv (fun z : ℝ => z) z :=
    deriv_const_mul (x := z) (d := fun z : ℝ => z) (4 : ℝ) (by fun_prop)
  rw [h, dPhi_id]; ring

private theorem dPhi_1sub4z (z : ℝ) : deriv (fun z : ℝ => 1 - 4 * z) z = -4 := by
  have h : deriv (fun z : ℝ => 1 - 4 * z) z = - deriv (fun z : ℝ => 4 * z) z :=
    deriv_const_sub (x := z) (f := fun z : ℝ => 4 * z) (1 : ℝ)
  rw [h, dPhi_4z]

private theorem dPhi_zz (z : ℝ) : deriv (fun z : ℝ => z * z) z = 2 * z := by
  have h : deriv (fun z : ℝ => z * z) z
      = deriv (fun z : ℝ => z) z * z + z * deriv (fun z : ℝ => z) z :=
    deriv_mul (x := z) (c := fun z : ℝ => z) (d := fun z : ℝ => z) (by fun_prop) (by fun_prop)
  rw [h, dPhi_id]; ring

private theorem dPhi_quad (z : ℝ) : deriv (fun z : ℝ => 1 - 4 * z + z * z) z = -4 + 2 * z := by
  have h : deriv (fun z : ℝ => 1 - 4 * z + z * z) z
      = deriv (fun z : ℝ => 1 - 4 * z) z + deriv (fun z : ℝ => z * z) z :=
    deriv_add (x := z) (f := fun z : ℝ => 1 - 4 * z) (g := fun z : ℝ => z * z)
      (by fun_prop) (by fun_prop)
  rw [h, dPhi_1sub4z, dPhi_zz]

private theorem dPhi_shift2 (z : ℝ) : deriv (fun z : ℝ => (1 + z) * (1 + z)) z = 2 * (1 + z) := by
  have h : deriv (fun z : ℝ => (1 + z) * (1 + z)) z
      = deriv (fun z : ℝ => 1 + z) z * (1 + z) + (1 + z) * deriv (fun z : ℝ => 1 + z) z :=
    deriv_mul (x := z) (c := fun z : ℝ => 1 + z) (d := fun z : ℝ => 1 + z)
      (by fun_prop) (by fun_prop)
  rw [h, dPhi_1add]; ring

private theorem dPhi_shift3 (z : ℝ) :
    deriv (fun z : ℝ => ((1 + z) * (1 + z)) * (1 + z)) z = 3 * ((1 + z) * (1 + z)) := by
  have h : deriv (fun z : ℝ => ((1 + z) * (1 + z)) * (1 + z)) z
      = deriv (fun z : ℝ => (1 + z) * (1 + z)) z * (1 + z)
        + ((1 + z) * (1 + z)) * deriv (fun z : ℝ => 1 + z) z :=
    deriv_mul (x := z) (c := fun z : ℝ => (1 + z) * (1 + z)) (d := fun z : ℝ => 1 + z)
      (by fun_prop) (by fun_prop)
  rw [h, dPhi_shift2, dPhi_1add]; ring

private theorem dPhi_shift4 (z : ℝ) :
    deriv (fun z : ℝ => (((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) z
      = 4 * (((1 + z) * (1 + z)) * (1 + z)) := by
  have h : deriv (fun z : ℝ => (((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) z
      = deriv (fun z : ℝ => ((1 + z) * (1 + z)) * (1 + z)) z * (1 + z)
        + (((1 + z) * (1 + z)) * (1 + z)) * deriv (fun z : ℝ => 1 + z) z :=
    deriv_mul (x := z) (c := fun z : ℝ => ((1 + z) * (1 + z)) * (1 + z))
      (d := fun z : ℝ => 1 + z) (by fun_prop) (by fun_prop)
  rw [h, dPhi_shift3, dPhi_1add]; ring

private theorem dPhi_z_1subz (z : ℝ) : deriv (fun z : ℝ => z * (1 - z)) z = 1 - 2 * z := by
  have h : deriv (fun z : ℝ => z * (1 - z)) z
      = deriv (fun z : ℝ => z) z * (1 - z) + z * deriv (fun z : ℝ => 1 - z) z :=
    deriv_mul (x := z) (c := fun z : ℝ => z) (d := fun z : ℝ => 1 - z)
      (by fun_prop) (by fun_prop)
  rw [h, dPhi_id, dPhi_1sub]; ring

private theorem dPhi_num3 (z : ℝ) :
    deriv (fun z : ℝ => z * (1 - 4 * z + z * z)) z = 1 - 8 * z + 3 * (z * z) := by
  have h : deriv (fun z : ℝ => z * (1 - 4 * z + z * z)) z
      = deriv (fun z : ℝ => z) z * (1 - 4 * z + z * z)
        + z * deriv (fun z : ℝ => 1 - 4 * z + z * z) z :=
    deriv_mul (x := z) (c := fun z : ℝ => z) (d := fun z : ℝ => 1 - 4 * z + z * z)
      (by fun_prop) (by fun_prop)
  rw [h, dPhi_id, dPhi_quad]; ring








/-! ### The recursion `z ∂_z (φQ b) = φQ (b+1)` -/

theorem phiQ_step0 (z : ℝ) (hz : (1 + z) ≠ 0) :
    z * deriv (fun z : ℝ => z / (1 + z)) z = z / ((1 + z) * (1 + z)) := by
  have h : deriv (fun z : ℝ => z / (1 + z)) z = 1 / ((1 + z) * (1 + z)) := by
    change deriv ((fun z : ℝ => z) / fun z : ℝ => 1 + z) z = 1 / ((1 + z) * (1 + z))
    have hdiv := deriv_div (x := z) (c := fun z : ℝ => z) (d := fun z : ℝ => 1 + z)
      (by fun_prop) (by fun_prop) hz
    rw [hdiv, dPhi_id, dPhi_1add]
    simp
    field_simp
  rw [h]; ring

theorem phiQ_step1 (z : ℝ) (hz : (1 + z) ≠ 0) :
    z * deriv (fun z : ℝ => z / ((1 + z) * (1 + z))) z
      = z * (1 - z) / (((1 + z) * (1 + z)) * (1 + z)) := by
  have h : deriv (fun z : ℝ => z / ((1 + z) * (1 + z))) z
      = (1 - z) / (((1 + z) * (1 + z)) * (1 + z)) := by
    change deriv ((fun z : ℝ => z) / fun z : ℝ => (1 + z) * (1 + z)) z
      = (1 - z) / (((1 + z) * (1 + z)) * (1 + z))
    have hdiv := deriv_div (x := z) (c := fun z : ℝ => z) (d := fun z : ℝ => (1 + z) * (1 + z))
      (by fun_prop) (by fun_prop) (by positivity)
    rw [hdiv, dPhi_id, dPhi_shift2]
    simp
    field_simp
    ring
  rw [h]; ring

theorem phiQ_step2 (z : ℝ) (hz : (1 + z) ≠ 0) :
    z * deriv (fun z : ℝ => z * (1 - z) / (((1 + z) * (1 + z)) * (1 + z))) z
      = z * (1 - 4 * z + z * z) / ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) := by
  have h : deriv (fun z : ℝ => z * (1 - z) / (((1 + z) * (1 + z)) * (1 + z))) z
      = (1 - 4 * z + z * z) / ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) := by
    change deriv ((fun z : ℝ => z * (1 - z)) / fun z : ℝ => ((1 + z) * (1 + z)) * (1 + z)) z
      = (1 - 4 * z + z * z) / ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z))
    have hdiv := deriv_div (x := z) (c := fun z : ℝ => z * (1 - z))
      (d := fun z : ℝ => ((1 + z) * (1 + z)) * (1 + z))
      (by fun_prop) (by fun_prop) (by positivity)
    rw [hdiv, dPhi_z_1subz, dPhi_shift3]
    field_simp
    ring
  rw [h]; ring

theorem phiQ_step3 (z : ℝ) (hz : (1 + z) ≠ 0) :
    z * deriv (fun z : ℝ =>
        z * (1 - 4 * z + z * z) / ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z))) z
      = z * (1 - 11 * z + 11 * (z * z) - z * z * z)
          / (((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) * (1 + z)) := by
  have h : deriv (fun z : ℝ =>
        z * (1 - 4 * z + z * z) / ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z))) z
      = (1 - 11 * z + 11 * (z * z) - z * z * z)
          / (((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) * (1 + z)) := by
    change deriv ((fun z : ℝ => z * (1 - 4 * z + z * z))
        / fun z : ℝ => (((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) z
      = (1 - 11 * z + 11 * (z * z) - z * z * z)
          / (((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) * (1 + z))
    have hdiv := deriv_div (x := z) (c := fun z : ℝ => z * (1 - 4 * z + z * z))
      (d := fun z : ℝ => (((1 + z) * (1 + z)) * (1 + z)) * (1 + z))
      (by fun_prop) (by fun_prop) (by positivity)
    rw [hdiv, dPhi_num3, dPhi_shift4]
    field_simp
    ring
  rw [h]; ring

/-! ### The bounds `|φQ b z| ≤ 1` on `z ≥ 0` -/

theorem phiQ_bound0 (z : ℝ) (hz : 0 ≤ z) : |z / (1 + z)| ≤ 1 := by
  rw [abs_div, abs_of_nonneg hz, abs_of_pos (by linarith : (0 : ℝ) < 1 + z)]
  rw [div_le_one (by linarith)]
  linarith

theorem phiQ_bound1 (z : ℝ) (hz : 0 ≤ z) : |z / ((1 + z) * (1 + z))| ≤ 1 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_nonneg hz, abs_of_pos (by positivity : (0 : ℝ) < (1 + z) * (1 + z))]
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg z]

theorem phiQ_bound2 (z : ℝ) (hz : 0 ≤ z) :
    |z * (1 - z) / (((1 + z) * (1 + z)) * (1 + z))| ≤ 1 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_mul, abs_of_nonneg hz,
    abs_of_pos (by positivity : (0 : ℝ) < ((1 + z) * (1 + z)) * (1 + z))]
  rw [div_le_one (by positivity)]
  have h : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
  nlinarith [mul_le_mul_of_nonneg_left h hz, sq_nonneg (1 + z)]

theorem phiQ_bound3 (z : ℝ) (hz : 0 ≤ z) :
    |z * (1 - 4 * z + z * z) / ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z))| ≤ 1 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_mul, abs_of_nonneg hz,
    abs_of_pos (by positivity : (0 : ℝ) < (((1 + z) * (1 + z)) * (1 + z)) * (1 + z))]
  rw [div_le_one (by positivity)]
  have h : |1 - 4 * z + z * z| ≤ 1 + 4 * z + z * z := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg z, hz]
  nlinarith [mul_le_mul_of_nonneg_left h hz, sq_nonneg (1 + z), hz]

theorem phiQ_bound4 (z : ℝ) (hz : 0 ≤ z) :
    |z * (1 - 11 * z + 11 * (z * z) - z * z * z)
      / (((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) * (1 + z))| ≤ 1 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_mul, abs_of_nonneg hz,
    abs_of_pos (by positivity :
      (0 : ℝ) < ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) * (1 + z))]
  rw [div_le_one (by positivity)]
  have h : |1 - 11 * z + 11 * (z * z) - z * z * z|
      ≤ 1 + 11 * z + 11 * (z * z) + z * z * z := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg z, hz]
  have h2 : z * (1 + 11 * z + 11 * (z * z) + z * z * z)
      ≤ ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) * (1 + z) := by
    by_cases hz1 : z ≤ 1
    · have h4 : z * z + z * z * z ≤ 4 * z := by nlinarith [sq_nonneg z, hz, hz1]
      nlinarith [h4, hz, pow_nonneg hz 4]
    · have hz1' : 1 ≤ z := le_of_lt (not_le.mp hz1)
      have h4 : z * z + z * z * z ≤ 4 * (z * z * z * z) := by
        nlinarith [sq_nonneg (z - 1), hz, hz1']
      nlinarith [h4, hz, hz1', pow_nonneg hz 5]
  nlinarith [mul_le_mul_of_nonneg_left h hz, h2]

/-! ### The identification `DzdIter b φ = φQ b` and the bound -/

/-- `DzdIter b φ` is the explicit rational form `φQ b`, for `z > -1` (where all the
expressions are differentiable). -/
theorem phiQ_DzdIter_eq : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, -1 < z →
    Work.Elliptic.DzdIter b (fun z : ℝ => z / (1 + z)) z = phiQ b z := by
  intro b
  induction b with
  | zero => intro _ z _; rfl
  | succ n ih =>
      intro hb z hz
      have hn : n ≤ 3 := by omega
      rw [Work.Elliptic.DzdIter_succ]
      show z * deriv (Work.Elliptic.DzdIter n (fun z : ℝ => z / (1 + z))) z = phiQ (n + 1) z
      have hderiv : deriv (Work.Elliptic.DzdIter n (fun z : ℝ => z / (1 + z))) z
          = deriv (phiQ n) z := by
        have hev : (fun w : ℝ => Work.Elliptic.DzdIter n (fun z : ℝ => z / (1 + z)) w)
            =ᶠ[𝓝 z] phiQ n :=
          Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) (fun w hw => ih (by omega) w hw)
        exact hev.deriv.eq_of_nhds
      rw [hderiv]
      have hz' : (1 + z) ≠ 0 := by linarith
      interval_cases n
      · exact phiQ_step0 z hz'
      · exact phiQ_step1 z hz'
      · exact phiQ_step2 z hz'
      · exact phiQ_step3 z hz'

/-- **The bound used by `mul_phi_Hk`**: every `z∂_z`-iterate of `z/(1+z)` of order `≤ 4` is
bounded by `1` on `[0,∞)`. -/
theorem phiSelf_DzdIter_bound (b : ℕ) (hb : b ≤ 4) (z : ℝ) (hz : 0 ≤ z) :
    |Work.Elliptic.DzdIter b (fun z : ℝ => z / (1 + z)) z| ≤ 1 := by
  rw [phiQ_DzdIter_eq b hb z (by linarith)]
  interval_cases b
  · exact phiQ_bound0 z hz
  · exact phiQ_bound1 z hz
  · exact phiQ_bound2 z hz
  · exact phiQ_bound3 z hz
  · exact phiQ_bound4 z hz

/-- The same bound for the two-variable lift `fun z _ => φ z`. -/
theorem phiSelf_DzdIter_bound_phiF (b : ℕ) (hb : b ≤ 4) (z : ℝ) (hz : 0 ≤ z) :
    |Work.Elliptic.DzdIter b (fun z : ℝ => Work.FTS.NonlinRows.NRow10aux.phiF z) z| ≤ 1 :=
  phiSelf_DzdIter_bound b hb z hz

end

end Work.FTS.NonlinRows.NRow10aux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.C0_le_lintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The level-`0` `ℋ⁰`-bound for the `cos θ`-weighted angular mass

The `ℋ⁰`-norm of a datum `F` on the open quadrant `Q0 = (0,∞) × (0,π/2)` is

    `∫⁻ p in Q0, ENNReal.ofReal (F p.1 p.2 ^ 2)`

and the *angular mass* of the slice at radius `z` is `∫ θ in Iθ, F z θ ^ 2 * cos θ`.  This file
proves that the `lintegral` over `z > 0` of the `ofReal` of the angular mass is bounded by the
`ℋ⁰`-norm: the weight `cos θ ≤ 1` (and `cos θ ≥ 0` on `Iθ`) bounds the `cos θ`-weighted slice
integral by the unweighted one, the two endpoints `θ = 0, π/2` are null for Lebesgue measure,
and Tonelli's theorem for `ℝ≥0∞`-valued functions (`MeasureTheory.setLIntegral_prod`) identifies
the iterated `lintegral` over the two half-lines with the `lintegral` over the product `Q0`.

The statement is `Work.FTS.PhiStar.Honesty.C0_le_lintegral`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty


end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false

/-- The smooth step: `0` for `t ≤ 0`, `1` for `1 ≤ t`. -/
def cut01 (t : ℝ) : ℝ := Real.smoothTransition t

/-- The radial cutoff at scale `n`: `1` on `[2/n, n]`, `0` outside `(1/n, 2n)`. -/
def chiR (n : ℕ) (z : ℝ) : ℝ := cut01 ((n : ℝ) * z - 1) * cut01 (2 - z / (n : ℝ))

/-- The angular cutoff at scale `n`: `1` on `[2/n, π/2 - 2/n]`, `0` outside
`(1/n, π/2 - 1/n)`. -/
def zetaR (n : ℕ) (θ : ℝ) : ℝ :=
  cut01 ((n : ℝ) * θ - 1) * cut01 ((n : ℝ) * (Real.pi / 2 - θ) - 1)

/-- A fixed smooth profile supported in `(1, 3/2) ⊂ (0, π/2)`. -/
def rhoAux (θ : ℝ) : ℝ := cut01 (2 * θ - 2) * cut01 (3 - 2 * θ)

/-- The normalisation of the moment profile. -/
def crho : ℝ := ∫ θ in Work.Spaces.Iθ, rhoAux θ * Work.Elliptic.sinCos2 θ

/-- The normalised moment profile with `∫_0^{π/2} rho θ sinθcos²θ dθ = 1`. -/
def rho (θ : ℝ) : ℝ := (crho)⁻¹ * rhoAux θ

/-- The `z`-dependent moment of the truncated source:
`lam n F z = ∫_θ zetaR n θ · F z θ · sinθcos²θ dθ`. -/
def lam (n : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ

/-- The moment of the truncated source, put inside the radial cutoff. -/
def mu (n : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := chiR n z * lam n F z

/-- **The approximation of `F` at scale `n`.** -/
def approx (n : ℕ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => chiR n z * (zetaR n θ * F z θ - lam n F z * rho θ)

/-- The error of the approximation at scale `n`. -/
def err (n : ℕ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => approx n F z θ - F z θ

/-- The shrinking region where the two cutoffs are not simultaneously equal to `1`:
`Ω_n = {z < 2/n} ∪ {n < z} ∪ {θ < 2/n} ∪ {π/2 - 2/n < θ}`. -/
def Omega (n : ℕ) : Set (ℝ × ℝ) :=
  {p | p.1 < 2 / (n : ℝ) ∨ (n : ℝ) < p.1 ∨ p.2 < 2 / (n : ℝ)
    ∨ Real.pi / 2 - 2 / (n : ℝ) < p.2}

theorem Omega_measurable (n : ℕ) : MeasurableSet (Omega n) := by
  refine MeasurableSet.union ?_ ?_
  · exact measurableSet_lt measurable_fst measurable_const
  · refine MeasurableSet.union ?_ ?_
    · exact measurableSet_lt measurable_const measurable_fst
    · refine MeasurableSet.union ?_ ?_
      · exact measurableSet_lt measurable_snd measurable_const
      · exact measurableSet_lt measurable_const measurable_snd

end Work.FTS.PhiStar.Honesty.CptApp
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.DiffGreen.cmode_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty.DiffGreen

/-- The elementary AM–GM estimate `|a·b·c| ≤ (a²c + b²c)/2` for a nonnegative weight `c`
applied to the split `a·b·c = (a√c)·(b√c)`.  It is the pointwise bound by which the slice
integrand `F z θ · e_m θ · cos θ` is dominated by the sum of the two integrable squares
`(F z θ)² cos θ` and `e_m θ² cos θ`. -/
lemma cmode_abs_mul_mul_le (a b c : ℝ) (hc : 0 ≤ c) :
    |a * b * c| ≤ (a ^ 2 * c + b ^ 2 * c) / 2 := by
  have h1 : |a * b * c| = |a| * |b| * c := by rw [abs_mul, abs_mul, abs_of_nonneg hc]
  rw [h1]
  have h2 : 2 * |a| * |b| ≤ |a| ^ 2 + |b| ^ 2 := two_mul_le_add_sq |a| |b|
  have h3 : (2 * |a| * |b|) * c ≤ (|a| ^ 2 + |b| ^ 2) * c :=
    mul_le_mul_of_nonneg_right h2 hc
  rw [sq_abs, sq_abs] at h3
  linarith [h3]

/-- **The slice integrand is integrable on `Iθ`.**  For `F` smooth on the open quadrant and
`F ∈ ℋ^0` (`Work.Spaces.HkMem α 0 F`), every mode-weighted slice `θ ↦ F z θ · e_m θ · cos θ`
(`z > 0`) is integrable over `Iθ`.

`Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem` gives the integrability of
`θ ↦ (F z θ)² cos θ`; the second square `θ ↦ e_m θ² cos θ` is continuous on the compact `Iθ`,
hence integrable; the pointwise AM–GM bound `cmode_abs_mul_mul_le` (legitimate on `Iθ`, where
`cos θ ≥ 0`) transfers integrability, using that the product is a.e. strongly measurable since
its uncurried form is continuous on the open quadrant
(`Work.Spaces.aesm_slice_of_continuousOn_Qd`). -/
lemma cmode_integrableOn_mul_eFam_cos {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 0 F)
    (m : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      Work.Spaces.Iθ := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- the two squares `(F z ·)² cos` and `e_m² cos` are integrable on `Iθ`
  have hA : IntegrableOn (fun θ : ℝ => (F z θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem hmem hz
  have hB : IntegrableOn
      (fun θ : ℝ => (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
      Work.Spaces.Iθ := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    exact (((Work.EllipticEst.ModalSolution.continuous_eFam m).pow 2).mul
      Real.continuous_cos).continuousOn
  -- their half-sum dominates the integrand pointwise
  have hdom : IntegrableOn (fun θ : ℝ => ((F z θ) ^ 2 * Real.cos θ
      + (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ) / 2) Work.Spaces.Iθ := by
    have h := (hA.add hB).div_const 2
    show Integrable (fun θ : ℝ => ((F z θ) ^ 2 * Real.cos θ
      + (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ) / 2)
      (volume.restrict Work.Spaces.Iθ)
    simpa only [Pi.add_apply, div_eq_mul_inv] using h
  -- a.e. strong measurability: the uncurried integrand is continuous on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2
      * Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * Real.cos p.2) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (Function.uncurry F) Work.FTS.EllipticEst.Q0 :=
      (hF.forall 0).continuousOn
    have h2 : Continuous (fun p : ℝ × ℝ =>
        Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * Real.cos p.2) :=
      ((Work.EllipticEst.ModalSolution.continuous_eFam m).comp continuous_snd).mul
        (Real.continuous_cos.comp continuous_snd)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2
        * (Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * Real.cos p.2)) Work.FTS.EllipticEst.Q0 :=
      h1.mul h2.continuousOn
    convert h3 using 1
    funext p
    ring
  have haesm : AEStronglyMeasurable
      (fun θ : ℝ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
  refine hdom.mono' haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem hIθ] with θ hθ
  have hc : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  rw [Real.norm_eq_abs]
  exact cmode_abs_mul_mul_le _ _ _ hc

/-- The interval-integral form (`0` to `π/2`) of `cmode_integrableOn_mul_eFam_cos`: the slice
integrand of the mode coefficient is interval integrable. -/
lemma cmode_intervalIntegrable_mul_eFam_cos {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 0 F)
    (m : ℕ) {z : ℝ} (hz : 0 < z) :
    IntervalIntegrable (fun θ : ℝ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Real.cos θ) volume 0 (Real.pi / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  exact cmode_integrableOn_mul_eFam_cos hF hmem m hz

/-- **The mode coefficients are additive in the source** (at `z > 0`, where the slice integral
is taken over `θ ∈ Iθ = [0, π/2]` against the continuous weight `eFam m θ · cos θ`).

The only analytic input is the `θ`-integrability of `X z θ · eFam m θ · cos θ` and of
`Y z θ · eFam m θ · cos θ` on `Iθ`: it follows from `Work.Spaces.HkMem α 0 X` via
`Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem` together with the pointwise bound
`|f · e_m cos| ≤ (f² · cos + e_m² · cos)/2` and `∫_θ eFam m θ² cos θ = eNorm m < ∞`
(`Work.EllipticEst.ModalSolution.eNorm_pos`).  The denominator `∫_θ eFam m θ² cos θ` is nonzero
(`eNorm_pos`), so plain subtraction of the two `intervalIntegral`s closes the identity. -/
theorem cmode_sub {α : ℝ} {X Y : ℝ → ℝ → ℝ}
    (hX : Work.FTS.EllipticEst.SmoothOpen X) (hY : Work.FTS.EllipticEst.SmoothOpen Y)
    (hmX : Work.Spaces.HkMem α 0 X) (hmY : Work.Spaces.HkMem α 0 Y)
    (m : ℕ) {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Series.cmode m (fun z θ => X z θ - Y z θ) z
      = Work.FTS.PhiStar.Series.cmode m X z - Work.FTS.PhiStar.Series.cmode m Y z := by
  -- the two slice integrands are interval integrable
  have hXint := cmode_intervalIntegrable_mul_eFam_cos hX hmX m hz
  have hYint := cmode_intervalIntegrable_mul_eFam_cos hY hmY m hz
  -- hence the numerator of the `X - Y` mode is the difference of the numerators
  have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        (X z θ - Y z θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = (∫ θ in (0 : ℝ)..(Real.pi / 2),
          X z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
        - ∫ θ in (0 : ℝ)..(Real.pi / 2),
            Y z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
    rw [show (fun θ : ℝ => (X z θ - Y z θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * Real.cos θ)
        = fun θ : ℝ => X z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ
            - Y z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ from
      funext fun θ => by ring]
    exact intervalIntegral.integral_sub hXint hYint
  -- the three `cmode`s share the same denominator `∫ e_m² cos`
  simp only [Work.FTS.PhiStar.Series.cmode]
  rw [hnum, sub_div]

end Work.FTS.PhiStar.Honesty.DiffGreen
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.Slots.Wt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## 1. Elementary integrability of the angular `rpow` weight -/

/-- `sin(2θ)^e` is integrable on `Iθ` for every `e > -1`. -/
theorem sin_rpow_integrableOn_Iθ {e : ℝ} (he : -1 < e) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Real.sin (2 * θ) ^ e) Work.Spaces.Iθ := by
  by_cases h : e ≤ 0
  · exact (Work.Spaces.sin_two_rpow e he h).1
  · have hcont : Continuous (fun θ : ℝ => Real.sin (2 * θ) ^ e) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
        (fun x => Or.inr (le_of_lt (not_le.mp h)))
    have hIcc : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
    rw [hIcc]
    refine MeasureTheory.Integrable.mono'
      (g := fun _ : ℝ => (1 : ℝ)) (integrableOn_const ?_) ?_ ?_
    · rw [Real.volume_Icc]; simp
    · exact hcont.continuousOn.aestronglyMeasurable measurableSet_Icc
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have h0 : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 e)]
      exact Real.rpow_le_one h0 (Real.sin_le_one _) (le_of_lt (not_le.mp h))

/-! ## 2. The weight profile `Φ z = z^{2/α}/(1+z)^{7/α}` and the integrability of `(Φ w)²` -/

/-- The weight profile singled out by the radial mode bounds. -/
noncomputable def phiWt (α : ℝ) (z : ℝ) : ℝ := z ^ (2 / α) / (1 + z) ^ (7 / α)

theorem phiWt_nonneg {α z : ℝ} (hz : 0 ≤ z) : 0 ≤ phiWt α z :=
  div_nonneg (Real.rpow_nonneg hz _) (Real.rpow_nonneg (by linarith) _)

/-- The pointwise identity `(Φ z · w z)² = z^{4/α-4}·(1+z)^{4-14/α}` for `z > 0`. -/
theorem phiWt_mul_w_sq {α : ℝ} (_hα : 0 < α) {z : ℝ} (hz : 0 < z) :
    (phiWt α z * Work.Spaces.w z) ^ 2 = z ^ (4 / α - 4) * (1 + z) ^ (4 - 14 / α) := by
  have h1 : 0 < 1 + z := by linarith
  have hwr : z ^ (2:ℝ) = z ^ 2 := Real.rpow_natCast z 2
  have h1r : (1 + z) ^ (2:ℝ) = (1 + z) ^ 2 := Real.rpow_natCast (1 + z) 2
  have hw1 : (z ^ 2)⁻¹ = z ^ (-(2 : ℝ)) := by rw [← hwr, ← Real.rpow_neg hz.le (2 : ℝ)]
  have hw2 : Work.Spaces.w z = (1 + z) ^ (2:ℝ) * z ^ (-(2 : ℝ)) := by
    rw [Work.Spaces.w, div_eq_mul_inv, hw1, h1r.symm]
  have hphi : phiWt α z = z ^ (2 / α) * (1 + z) ^ (-(7 / α)) := by
    rw [phiWt, div_eq_mul_inv, ← Real.rpow_neg h1.le (7 / α)]
  have hlin : phiWt α z * Work.Spaces.w z
      = z ^ (2 / α - 2) * (1 + z) ^ (2 - 7 / α) := by
    rw [hw2, hphi]
    rw [show z ^ (2 / α) * (1 + z) ^ (-(7 / α))
          * ((1 + z) ^ (2:ℝ) * z ^ (-(2 : ℝ)))
        = (z ^ (2 / α) * z ^ (-(2 : ℝ)))
          * ((1 + z) ^ (2:ℝ) * (1 + z) ^ (-(7 / α))) by ring]
    rw [← Real.rpow_add hz (2 / α) (-(2:ℝ)), ← Real.rpow_add h1 (2:ℝ) (-(7/α))]
    ring_nf
  rw [hlin, mul_pow, sq, sq,
    (Real.rpow_add hz (2 / α - 2) (2 / α - 2)).symm,
    (Real.rpow_add h1 (2 - 7 / α) (2 - 7 / α)).symm]
  ring_nf

theorem integrableOn_phiWt_mul_w_sq {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (phiWt α z * Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := by
  have hα16 : (16 : ℝ) ≤ 4 / α := by
    rw [le_div_iff₀ hα]; nlinarith
  have hα56 : (56 : ℝ) ≤ 14 / α := by
    rw [le_div_iff₀ hα]; nlinarith
  have hexp1 : -1 < 4 / α - 4 := by linarith
  have hexp2 : -10 / α < -1 := by
    rw [div_lt_iff₀ hα]
    nlinarith [hα4, hα]
  have hexp3 : 4 - 14 / α ≤ 0 := by linarith
  -- the two dominating functions
  have hg1 : MeasureTheory.IntegrableOn (fun z : ℝ => z ^ (4 / α - 4)) (Set.Ioo 0 1) := by
    have hIcc : MeasureTheory.IntegrableOn (fun z : ℝ => z ^ (4 / α - 4)) (Set.Icc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
        (intervalIntegral.intervalIntegrable_rpow' hexp1)
    exact hIcc.mono_set Set.Ioo_subset_Icc_self
  have hg2 : MeasureTheory.IntegrableOn (fun z : ℝ => z ^ (-10 / α)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_iff (show (0:ℝ) < 1 by norm_num)).mpr hexp2
  have hca : ContinuousOn (fun z : ℝ => z ^ (4 / α - 4) * (1 + z) ^ (4 - 14 / α))
      (Set.Ioi 0) := by
    have h2 : ContinuousOn (fun z : ℝ => 1 + z) (Set.Ioi 0) :=
      continuousOn_const.add continuousOn_id
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))).mul
      (h2.rpow_const (fun x hx => Or.inl (ne_of_gt (by linarith [show (0:ℝ) < x from hx]))))
  -- the small part
  have hsmall : MeasureTheory.IntegrableOn (fun z : ℝ => (phiWt α z * Work.Spaces.w z) ^ 2)
      (Set.Ioo 0 1) := by
    refine MeasureTheory.Integrable.mono' hg1 ?_ ?_
    · have haesm : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => z ^ (4 / α - 4) * (1 + z) ^ (4 - 14 / α))
          (MeasureTheory.volume.restrict (Set.Ioo 0 1)) :=
        (hca.mono (fun x hx => hx.1)).aestronglyMeasurable measurableSet_Ioo
      refine haesm.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
      exact (phiWt_mul_w_sq hα hz.1).symm
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), phiWt_mul_w_sq hα hz.1]
      exact mul_le_of_le_one_right (Real.rpow_nonneg (le_of_lt hz.1) _)
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hz.1]) hexp3)
  -- the large part
  have hbig : MeasureTheory.IntegrableOn (fun z : ℝ => (phiWt α z * Work.Spaces.w z) ^ 2)
      (Set.Ioi 1) := by
    refine MeasureTheory.Integrable.mono' hg2 ?_ ?_
    · have haesm : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => z ^ (4 / α - 4) * (1 + z) ^ (4 - 14 / α))
          (MeasureTheory.volume.restrict (Set.Ioi 1)) :=
        (hca.mono (fun x hx => lt_trans zero_lt_one (show (1:ℝ) < x from hx))).aestronglyMeasurable
          measurableSet_Ioi
      refine haesm.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      exact (phiWt_mul_w_sq hα (lt_trans zero_lt_one (show (1:ℝ) < z from hz))).symm
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hz1 : (1:ℝ) < z := hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), phiWt_mul_w_sq hα (by linarith)]
      have h2z : (1 + z) ^ (4 - 14 / α) ≤ z ^ (4 - 14 / α) :=
        Real.rpow_le_rpow_of_nonpos (x := z) (y := 1 + z) (z := 4 - 14 / α)
          (by linarith [hz1]) (by linarith) hexp3
      calc z ^ (4 / α - 4) * (1 + z) ^ (4 - 14 / α)
          ≤ z ^ (4 / α - 4) * z ^ (4 - 14 / α) :=
            mul_le_mul_of_nonneg_left h2z (Real.rpow_nonneg (by linarith) _)
        _ = z ^ (-10 / α) := by
            rw [← Real.rpow_add (by linarith : (0:ℝ) < z),
              show 4 / α - 4 + (4 - 14 / α) = -10 / α by ring]
  -- combine
  have hIcc : MeasureTheory.IntegrableOn (fun z : ℝ => (phiWt α z * Work.Spaces.w z) ^ 2)
      (Set.Icc 0 1) := hsmall.congr_set_ae MeasureTheory.Ioo_ae_eq_Icc.symm
  have hcomb := hIcc.union hbig
  rwa [Set.Icc_union_Ioi_eq_Ici (show (0:ℝ) ≤ 1 by norm_num)] at hcomb

/-! ## 3. Weighted-square integrability from a separable pointwise bound -/

/-- **Integrability of `θ ↦ (F z θ · w z)² sin(2θ)^e` and of its `θ`-integral.**
`F` is continuous on the open quadrant and bounded there by `K · φ(z)`, `φ` is nonnegative on
`Iz` with `(φ · w)²` integrable, and `e > -1` so that the angular weight is integrable. -/
theorem integrableOn_sq_mul_sin_rpow_of_bound {F : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {K e : ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)))
    (hK : 0 ≤ K) (hφnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ φ z)
    (hbdd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π/2) → |F z θ| ≤ K * φ z)
    (hφ : MeasureTheory.IntegrableOn (fun z : ℝ => (φ z * Work.Spaces.w z) ^ 2) Work.Spaces.Iz)
    (he : -1 < e) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ : ℝ => (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e) Work.Spaces.Iz := by
  have hsinIoo : MeasureTheory.IntegrableOn (fun θ : ℝ => Real.sin (2 * θ) ^ e)
      (Set.Ioo 0 (π/2)) :=
    (sin_rpow_integrableOn_Iθ he).mono_set (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  -- the angular weight is nonnegative on the open interval
  have hsin0 : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π/2) → 0 ≤ Real.sin (2 * θ) ^ e := fun θ hθ =>
    Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) e
  -- the pointwise domination (on the open quadrant)
  have hpt : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π/2) →
      (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e
        ≤ (K * φ z * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e := by
    intro z hz θ hθ
    have hKphi : 0 ≤ K * φ z := mul_nonneg hK (hφnn z (le_of_lt hz))
    have hF2 : (F z θ) ^ 2 ≤ (K * φ z) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hKphi]; exact hbdd z hz θ hθ
    have h1 : (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ (K * φ z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_le_mul_of_nonneg_right hF2 (sq_nonneg _)
    have h2 := mul_le_mul_of_nonneg_right h1 (hsin0 θ hθ)
    nlinarith [h2, sq_nonneg (Work.Spaces.w z), hsin0 θ hθ]
  -- continuity of the uncurried integrand on the open quadrant
  have hwq : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) := by
    unfold Work.Spaces.w
    exact ((continuousOn_const.add continuousOn_fst).pow 2).div (continuousOn_fst.pow 2)
      (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinc : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2) ^ e)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) := by
    refine (Real.continuous_sin.comp_continuousOn
      (continuousOn_const.mul continuousOn_snd)).rpow_const ?_
    intro p hp
    refine Or.inl (ne_of_gt (Real.sin_pos_of_mem_Ioo ?_))
    exact ⟨by show (0:ℝ) < 2 * p.2; linarith [hp.2.1],
      by show 2 * p.2 < Real.pi; linarith [hp.2.2]⟩
  have hGcont : ContinuousOn
      (fun p : ℝ × ℝ => (F p.1 p.2 * Work.Spaces.w p.1) ^ 2 * Real.sin (2 * p.2) ^ e)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) := ((hF.mul hwq).pow 2).mul hsinc
  -- the angular slices
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ : ℝ => (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with rfl | hz0
    · have hzero : (fun θ : ℝ => (F 0 θ * Work.Spaces.w 0) ^ 2 * Real.sin (2 * θ) ^ e)
          = fun _ => (0:ℝ) := by
        funext θ; simp [Work.Spaces.w]
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · have hsl : ContinuousOn
          (fun θ : ℝ => (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e)
          (Set.Ioo 0 (π/2)) := by
        refine ((hF.comp (continuousOn_const.prodMk continuousOn_id)
          (fun p hp => ⟨hz0, hp⟩)).mul continuousOn_const).pow 2 |>.mul ?_
        refine (Real.continuous_sin.comp_continuousOn
          (continuousOn_const.mul continuousOn_id)).rpow_const ?_
        intro θ hθ
        refine Or.inl (ne_of_gt (Real.sin_pos_of_mem_Ioo ?_))
        exact ⟨by show (0:ℝ) < 2 * θ; linarith [hθ.1],
          by show 2 * θ < Real.pi; linarith [hθ.2]⟩
      have hIoo : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e)
          (Set.Ioo 0 (π/2)) := by
        refine MeasureTheory.Integrable.mono'
          (hsinIoo.const_mul ((K * φ z * Work.Spaces.w z) ^ 2)) ?_ ?_
        · exact hsl.aestronglyMeasurable measurableSet_Ioo
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hsin0 θ hθ))]
          exact hpt z hz0 θ hθ
      exact hIoo.congr_set_ae MeasureTheory.Ioo_ae_eq_Icc.symm
  refine ⟨hslice, ?_⟩
  -- the outer integral
  set S : ℝ := ∫ θ in Set.Ioo (0:ℝ) (π/2), Real.sin (2 * θ) ^ e with hS
  have hdom : MeasureTheory.IntegrableOn
      (fun z : ℝ => (K * φ z * Work.Spaces.w z) ^ 2 * S) Work.Spaces.Iz := by
    have h := hφ.const_mul (K ^ 2 * S)
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    ring
  have hGae : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ : ℝ =>
        (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 (π/2)))) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact hGcont.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have haesm1 : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Set.Ioo (0:ℝ) (π/2),
        (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hGae.integral_prod_right'
  have haesm2 : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Set.Ioo (0:ℝ) (π/2),
        (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0:ℝ))]
    exact haesm1
  have haesm3 : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine haesm2.congr ?_
    filter_upwards with z
    exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc)
  refine MeasureTheory.Integrable.mono' hdom haesm3 ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) e)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with rfl | hz0
  · have hzero : (fun θ : ℝ => (F 0 θ * Work.Spaces.w 0) ^ 2 * Real.sin (2 * θ) ^ e)
        = fun _ => (0:ℝ) := by
      funext θ; simp [Work.Spaces.w]
    rw [hzero]
    simp [Work.Spaces.w]
  · rw [show (∫ θ in Work.Spaces.Iθ, (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e)
        = ∫ θ in Set.Ioo (0:ℝ) (π/2),
            (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e from
      MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc.symm)]
    calc ∫ θ in Set.Ioo (0:ℝ) (π/2),
          (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e
        ≤ ∫ θ in Set.Ioo (0:ℝ) (π/2),
            (K * φ z * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e :=
          MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ =>
              mul_nonneg (sq_nonneg _) (hsin0 θ hθ))
            (hsinIoo.const_mul ((K * φ z * Work.Spaces.w z) ^ 2))
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => hpt z hz0 θ hθ)
      _ = (K * φ z * Work.Spaces.w z) ^ 2 * S := by
          rw [hS, ← MeasureTheory.integral_const_mul]

/-! ## Angular smoothness facts -/

/-- The Gegenbauer polynomials are `C^∞`. -/
theorem contDiff_gC_all : ∀ k : ℕ, ∀ n : ℕ,
    ContDiff ℝ n (Work.FTS.PhiStar.Gegenbauer.gC k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro n
      rw [show Work.FTS.PhiStar.Gegenbauer.gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
      exact contDiff_const
  | one =>
      intro n
      rw [show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
      exact contDiff_const.mul contDiff_id
  | more n ih1 ih2 =>
      intro m
      rw [show Work.FTS.PhiStar.Gegenbauer.gC (n + 2) = (fun x => (2 * ((n : ℝ) + 5 / 2) * x
        * Work.FTS.PhiStar.Gegenbauer.gC (n + 1) x
        - ((n : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC n x) / ((n : ℝ) + 2)) from rfl]
      exact (((contDiff_const.mul contDiff_id).mul (ih2 m)).sub
        (contDiff_const.mul (ih1 m))).div_const _

/-- The angular modes `eFam j` are `C^∞`. -/
theorem contDiff_eFam_all (j : ℕ) : ∀ n : ℕ,
    ContDiff ℝ n (Work.FTS.PhiStar.Gegenbauer.eFam j) := by
  intro n
  have h2 : ContDiff ℝ n (Work.FTS.PhiStar.Gegenbauer.gC (2 * j + 1)) :=
    contDiff_gC_all (2 * j + 1) n
  exact Real.contDiff_cos.mul (h2.comp Real.contDiff_sin)

/-- Every iterated derivative of an angular mode is continuous. -/
theorem continuous_iteratedDeriv_eFam (m j : ℕ) :
    Continuous (iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j)) :=
  (contDiff_infty.mpr (contDiff_eFam_all j)).continuous_iteratedDeriv m
    (by show ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact_mod_cast le_top)

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.HkActivePairs_spec =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

/-! ## Membership in the rectangular index block

`HkActivePairs k` is by definition the filter of the rectangle `range (k+1) × range (k+1)` by the
predicate `p.2 = 0 ∧ p.1 ≤ k ∨ 1 ≤ p.2 ∧ p.2 + p.1 ≤ k`.  On the rectangle the bound `p.1 ≤ k` of
the first disjunct is automatic, which is the content of the two membership lemmas below: the
first one records the rectangle membership (used on the definitional `.product` form), the second
its `×ˢ`-notation twin (used for `Finset.sum_product`). -/

/-- Membership in the index rectangle `range (k+1) × range (k+1)`, in the `.product` shape in
which `HkActivePairs` is defined. -/
theorem mem_range_prod_range (k : ℕ) (p : ℕ × ℕ) :
    p ∈ (Finset.range (k + 1)).product (Finset.range (k + 1)) ↔ p.1 ≤ k ∧ p.2 ≤ k := by
  constructor
  · intro hp
    change p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)) at hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    omega
  · rintro ⟨h1, h2⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩

/-- Membership in the index rectangle `range (k+1) × range (k+1)`, in the `×ˢ` shape that
`Finset.sum_product` produces. -/
theorem mem_range_sprod_range (k : ℕ) (p : ℕ × ℕ) :
    p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)) ↔ p.1 ≤ k ∧ p.2 ≤ k := by
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
  omega

/-- **The index set of the terms of `HkIntegrand`.**  `HkActivePairs k` consists exactly of the
pure pairs `(j, 0)` with `j ≤ k` and the mixed pairs `(j, i)` with `1 ≤ i` and `i + j ≤ k`. -/
theorem HkActivePairs_mem (k : ℕ) (p : ℕ × ℕ) :
    p ∈ HkActivePairs k ↔ p.2 = 0 ∧ p.1 ≤ k ∨ 1 ≤ p.2 ∧ p.2 + p.1 ≤ k := by
  rw [HkActivePairs, Finset.mem_filter, mem_range_prod_range]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro (h | h)
    · exact ⟨⟨by omega, by omega⟩, Or.inl h⟩
    · exact ⟨⟨by omega, by omega⟩, Or.inr h⟩

/-! ## The sum over `HkActivePairs k` -/

/-- **The sum over `HkActivePairs k` splits into its pure and mixed parts**: the pure terms
`(i, 0)`, `i ≤ k`, of the first sum of `HkIntegrand`, and the mixed terms `(j, i)`, `1 ≤ i`,
`i + j ≤ k`, of the double sum. -/
theorem HkActivePairs_sum (k : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ p ∈ HkActivePairs k, F p
      = (∑ i ∈ Finset.range (k + 1), F (i, 0))
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then F (j, i) else 0) := by
  -- rewrite the two disjuncts of the filter predicate separately, in the `×ˢ` shape
  have hfilter : HkActivePairs k
      = ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
          (fun p : ℕ × ℕ => p.2 = 0 ∨ (1 ≤ p.2 ∧ p.2 + p.1 ≤ k)) := by
    ext p
    rw [HkActivePairs, Finset.mem_filter, Finset.mem_filter, mem_range_prod_range,
      mem_range_sprod_range]
    tauto
  rw [hfilter, Finset.filter_or]
  have hdisj : Disjoint
      (((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
        (fun p : ℕ × ℕ => p.2 = 0))
      (((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
        (fun p : ℕ × ℕ => 1 ≤ p.2 ∧ p.2 + p.1 ≤ k)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_filter] at ha hb
    omega
  rw [Finset.sum_union hdisj, Finset.sum_filter, Finset.sum_filter]
  congr 1
  · -- the pure part: `∑ p, if p.2 = 0 then F p else 0 = ∑ i, F (i,0)`
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_ite_eq']
    simp
  · -- the mixed part: swap the two sums, using that the bound `p.1 ≤ k` is automatic
    rw [Finset.sum_product]
    conv_lhs => rw [Finset.sum_comm]

/-- **The index set of the terms of `HkIntegrand`.**  `HkActivePairs k` enumerates exactly the pairs `(j,i)` of `HkIntegrand α k`: the pure terms `(j,0)`, `j ≤ k`, of the first sum and the mixed terms `(j,i)`, `1 ≤ i`, `i + j ≤ k`, of the double sum (with `mixed j 0 = D_z^j` and the weight `termWeight α i` equal to `w/√sin^η` for `i = 0` and `Wt` for `i ≥ 1`). -/
theorem HkActivePairs_spec (k : ℕ) :
    (∀ p : ℕ × ℕ, p ∈ HkActivePairs k
        ↔ p.2 = 0 ∧ p.1 ≤ k ∨ 1 ≤ p.2 ∧ p.2 + p.1 ≤ k)
      ∧ (∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ),
          Work.Spaces.HkIntegrand α k f z θ
            = ∑ p ∈ HkActivePairs k,
                (Work.Spaces.mixed p.1 p.2 f z θ * termWeight α p.2 z θ) ^ 2) := by
  constructor
  · intro p
    exact HkActivePairs_mem k p
  · intro α f z θ
    -- expand the sum over `HkActivePairs` and compare the two halves with `HkIntegrand`
    rw [HkActivePairs_sum k
      (fun p => (Work.Spaces.mixed p.1 p.2 f z θ * termWeight α p.2 z θ) ^ 2)]
    rw [Work.Spaces.HkIntegrand]
    -- The pure radial halves are *definitionally* equal (`mixed i 0 = D_z^i` and
    -- `termWeight α 0 = w/√sin^η`), so `congr` discharges them and only the mixed comparison
    -- remains: `termWeight α i = Wt α` for `i ≥ 1`.
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left h, ite_eq_left h]
      simp only [termWeight, ite_eq_right (show ¬ i = 0 from by omega)]
    · rw [ite_eq_right h, ite_eq_right h]

end Work.FTS.PhiStar.Honesty.SlotsLimit
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.IBPsub.Closure =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ## 0. Closure of the class of test functions -/

/-- The plain `z`-derivative of a test function on the open quadrant is again a test function:
globally `C^∞`, compactly supported, and the support only shrinks. -/
theorem testQ0_pz {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : TestQ0 (Work.Spaces.pz φ) := by
  have hF : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry φ) := h.1
  have hdiff : Differentiable ℝ (Function.uncurry φ) :=
    hF.differentiable (by rw [Work.Stability.smoothOrder]; simp)
  have hchain : Function.uncurry (Work.Spaces.pz φ)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry φ) p) (1, 0) := by
    funext p
    exact Work.Spaces.pz_eq_fderiv (hdiff p)
  have hfd : ContDiff ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry φ) p) :=
    ContDiff.fderiv_right hF (by rw [Work.Stability.smoothOrder]; simp)
  have hsmooth : ContDiff ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz φ)) := by
    rw [hchain]
    exact hfd.clm_apply contDiff_const
  have hcpt : HasCompactSupport (Function.uncurry (Work.Spaces.pz φ)) := by
    rw [hchain]
    exact h.2.1.fderiv_apply ℝ (1, 0)
  have hsub : tsupport (Function.uncurry (Work.Spaces.pz φ))
      ⊆ tsupport (Function.uncurry φ) := by
    rw [hchain]
    exact tsupport_fderiv_apply_subset ℝ (1, 0)
  exact ⟨hsmooth, hcpt, hsub.trans h.2.2⟩

/-- The plain `θ`-derivative of a test function on the open quadrant is again a test function. -/
theorem testQ0_pth {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : TestQ0 (Work.Spaces.pth φ) := by
  have hF : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry φ) := h.1
  have hdiff : Differentiable ℝ (Function.uncurry φ) :=
    hF.differentiable (by rw [Work.Stability.smoothOrder]; simp)
  have hchain : Function.uncurry (Work.Spaces.pth φ)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry φ) p) (0, 1) := by
    funext p
    exact Work.Spaces.pth_eq_fderiv (hdiff p)
  have hfd : ContDiff ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry φ) p) :=
    ContDiff.fderiv_right hF (by rw [Work.Stability.smoothOrder]; simp)
  have hsmooth : ContDiff ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth φ)) := by
    rw [hchain]
    exact hfd.clm_apply contDiff_const
  have hcpt : HasCompactSupport (Function.uncurry (Work.Spaces.pth φ)) := by
    rw [hchain]
    exact h.2.1.fderiv_apply ℝ (0, 1)
  have hsub : tsupport (Function.uncurry (Work.Spaces.pth φ))
      ⊆ tsupport (Function.uncurry φ) := by
    rw [hchain]
    exact tsupport_fderiv_apply_subset ℝ (0, 1)
  exact ⟨hsmooth, hcpt, hsub.trans h.2.2⟩

/-- The uncurried pointwise product is the pointwise product of the uncurried factors. -/
theorem uncurry_mul_eq (ψ φ : ℝ → ℝ → ℝ) :
    Function.uncurry (fun z θ => ψ z θ * φ z θ)
      = Function.uncurry ψ * Function.uncurry φ := by
  funext p
  obtain ⟨z, θ⟩ := p
  rfl

/-- A test function multiplied on the left by a globally `C^∞` function is again a test function
(the support of a product is contained in the support of the right factor). -/
theorem testQ0_mul_left {ψ φ : ℝ → ℝ → ℝ}
    (hψ : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry ψ)) (hφ : TestQ0 φ) :
    TestQ0 (fun z θ => ψ z θ * φ z θ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [uncurry_mul_eq ψ φ]
    exact hψ.mul hφ.1
  · rw [uncurry_mul_eq ψ φ]
    exact hφ.2.1.mul_left
  · rw [uncurry_mul_eq ψ φ]
    exact (tsupport_mul_subset_right (f := Function.uncurry ψ)
      (g := Function.uncurry φ)).trans hφ.2.2

/-- A test function multiplied by a constant is again a test function. -/
theorem testQ0_const_mul (c : ℝ) {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    TestQ0 (fun z θ => c * φ z θ) := by
  refine testQ0_mul_left ?_ h
  have hconst : Function.uncurry (fun _z _θ : ℝ => c) = fun _ : ℝ × ℝ => c := rfl
  rw [hconst]
  exact contDiff_const

/-- A test function multiplied by a power of the `z`-coordinate is again a test function. -/
theorem testQ0_zpow_mul (k : ℕ) {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    TestQ0 (fun z θ => z ^ k * φ z θ) := by
  refine testQ0_mul_left ?_ h
  have hz : Function.uncurry (fun z _θ : ℝ => z ^ k) = fun p : ℝ × ℝ => p.1 ^ k := rfl
  rw [hz]
  exact contDiff_fst.pow k

/-- A test function multiplied by `sin (2θ)` is again a test function. -/
theorem testQ0_sin_mul {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    TestQ0 (fun z θ => Real.sin (2 * θ) * φ z θ) := by
  refine testQ0_mul_left ?_ h
  have hs : Function.uncurry (fun _z θ : ℝ => Real.sin (2 * θ))
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) := rfl
  rw [hs]
  exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)

/-- The closed support of `∂_z φ` is contained in that of `φ`. -/
theorem tsupport_pz_subset {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    tsupport (Function.uncurry (Work.Spaces.pz φ)) ⊆ tsupport (Function.uncurry φ) := by
  have hF : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry φ) := h.1
  have hdiff : Differentiable ℝ (Function.uncurry φ) :=
    hF.differentiable (by rw [Work.Stability.smoothOrder]; simp)
  have hchain : Function.uncurry (Work.Spaces.pz φ)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry φ) p) (1, 0) := by
    funext p
    exact Work.Spaces.pz_eq_fderiv (hdiff p)
  rw [hchain]
  exact tsupport_fderiv_apply_subset ℝ (1, 0)

/-- The closed support of `∂_θ φ` is contained in that of `φ`. -/
theorem tsupport_pth_subset {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    tsupport (Function.uncurry (Work.Spaces.pth φ)) ⊆ tsupport (Function.uncurry φ) := by
  have hF : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry φ) := h.1
  have hdiff : Differentiable ℝ (Function.uncurry φ) :=
    hF.differentiable (by rw [Work.Stability.smoothOrder]; simp)
  have hchain : Function.uncurry (Work.Spaces.pth φ)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry φ) p) (0, 1) := by
    funext p
    exact Work.Spaces.pth_eq_fderiv (hdiff p)
  rw [hchain]
  exact tsupport_fderiv_apply_subset ℝ (0, 1)

/-- Iterated `∂_z` of a test function is a test function. -/
theorem testQ0_pzIter {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : ∀ k : ℕ,
    TestQ0 (Work.Spaces.pzIter k φ)
  | 0 => by simpa using h
  | (k + 1) => by
      show TestQ0 (Work.Spaces.pz (Work.Spaces.pzIter k φ))
      exact testQ0_pz (testQ0_pzIter h k)

/-- Iterated `∂_θ` preserves smoothness on the open quadrant. -/
theorem smoothOpen_pthIter {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) (i : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i g) := by
  induction i with
  | zero => simpa using hg
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact Work.FTS.EllipticEst.SmoothOpen.pth ih

/-- Iterated `∂_θ` of a test function is a test function. -/
theorem testQ0_pthIter {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : ∀ k : ℕ,
    TestQ0 (Work.Spaces.pthIter k φ)
  | 0 => by simpa using h
  | (k + 1) => by
      show TestQ0 (Work.Spaces.pth (Work.Spaces.pthIter k φ))
      exact testQ0_pth (testQ0_pthIter h k)

/-- The transpose of `D_z` preserves the class of test functions. -/
theorem testQ0_DzStar {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : TestQ0 (DzStar φ) := by
  have hpzs : ContDiff ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz φ)) := (testQ0_pz h).1
  have hchain : Function.uncurry (DzStar φ) = fun p : ℝ × ℝ =>
      -(p.1 * Function.uncurry (Work.Spaces.pz φ) p + Function.uncurry φ p) := by
    funext p
    obtain ⟨z, θ⟩ := p
    rfl
  have hsum : Function.support (fun p : ℝ × ℝ =>
      p.1 * Function.uncurry (Work.Spaces.pz φ) p + Function.uncurry φ p)
      ⊆ tsupport (Function.uncurry φ) := by
    intro p hp
    rw [Function.mem_support] at hp
    by_cases h0 : Function.uncurry φ p = 0
    · refine tsupport_pz_subset h (subset_closure (Function.mem_support.mpr ?_))
      intro h1
      exact hp (by rw [h1, h0]; ring)
    · exact subset_closure (Function.mem_support.mpr h0)
  have hsupp : Function.support (fun p : ℝ × ℝ =>
      -(p.1 * Function.uncurry (Work.Spaces.pz φ) p + Function.uncurry φ p))
      ⊆ tsupport (Function.uncurry φ) := by
    refine Set.Subset.trans ?_ hsum
    intro p hp
    rw [Function.mem_support] at hp ⊢
    intro hzero
    exact hp (by rw [hzero, neg_zero])
  refine ⟨?_, ?_, ?_⟩
  · rw [hchain]
    exact (((contDiff_fst.mul hpzs).add h.1)).neg
  · rw [hchain]
    exact (((HasCompactSupport.mul_left (f := fun p : ℝ × ℝ => p.1)
      (testQ0_pz h).2.1)).add h.2.1).neg
  · rw [hchain]
    refine (closure_mono hsupp).trans ?_
    rw [(isClosed_tsupport (Function.uncurry φ)).closure_eq]
    exact h.2.2

/-- The transpose of `D_θ` preserves the class of test functions. -/
theorem testQ0_DthStar {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : TestQ0 (DthStar φ) := by
  have hpths : ContDiff ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth φ)) := (testQ0_pth h).1
  have hsin : ContDiff ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)
  have hcos : ContDiff ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.cos (2 * p.2)) :=
    contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd))
  have hchain : Function.uncurry (DthStar φ) = fun p : ℝ × ℝ =>
      -(Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth φ) p
        + (2 * Real.cos (2 * p.2)) * Function.uncurry φ p) := by
    funext p
    obtain ⟨z, θ⟩ := p
    rfl
  have hsum : Function.support (fun p : ℝ × ℝ =>
      Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth φ) p
        + (2 * Real.cos (2 * p.2)) * Function.uncurry φ p)
      ⊆ tsupport (Function.uncurry φ) := by
    intro p hp
    rw [Function.mem_support] at hp
    by_cases h0 : Function.uncurry φ p = 0
    · refine tsupport_pth_subset h (subset_closure (Function.mem_support.mpr ?_))
      intro h1
      exact hp (by rw [h1, h0]; ring)
    · exact subset_closure (Function.mem_support.mpr h0)
  have hsupp : Function.support (fun p : ℝ × ℝ =>
      -(Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth φ) p
        + (2 * Real.cos (2 * p.2)) * Function.uncurry φ p))
      ⊆ tsupport (Function.uncurry φ) := by
    refine Set.Subset.trans ?_ hsum
    intro p hp
    rw [Function.mem_support] at hp ⊢
    intro hzero
    exact hp (by rw [hzero, neg_zero])
  refine ⟨?_, ?_, ?_⟩
  · rw [hchain]
    exact ((hsin.mul hpths).add (hcos.mul h.1)).neg
  · rw [hchain]
    exact (((testQ0_pth h).2.1.mul_left (f := fun p : ℝ × ℝ => Real.sin (2 * p.2))).add
      (h.2.1.mul_left (f := fun p : ℝ × ℝ => 2 * Real.cos (2 * p.2)))).neg
  · rw [hchain]
    refine (closure_mono hsupp).trans ?_
    rw [(isClosed_tsupport (Function.uncurry φ)).closure_eq]
    exact h.2.2

/-- Iterated `D_z`-transpose preserves the class of test functions. -/
theorem testQ0_DzIterStar {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : ∀ j : ℕ,
    TestQ0 (DzIterStar j φ)
  | 0 => by show TestQ0 φ; exact h
  | (j + 1) => by
      show TestQ0 (DzIterStar j (DzStar φ))
      exact testQ0_DzIterStar (testQ0_DzStar h) j

/-- Iterated `D_θ`-transpose preserves the class of test functions. -/
theorem testQ0_DthIterStar {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : ∀ i : ℕ,
    TestQ0 (DthIterStar i φ)
  | 0 => by show TestQ0 φ; exact h
  | (i + 1) => by
      show TestQ0 (DthIterStar i (DthStar φ))
      exact testQ0_DthIterStar (testQ0_DthStar h) i

/-- The transpose of any mixed operator preserves the class of test functions. -/
theorem testQ0_mixedStar {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) (j i : ℕ) :
    TestQ0 (mixedStar j i φ) :=
  testQ0_DthIterStar (testQ0_DzIterStar h j) i

/-- The transpose of `∂_z^j` preserves the class of test functions. -/
theorem testQ0_pzIterStar {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) (j : ℕ) :
    TestQ0 (pzIterStar j φ) := by
  have h1 : TestQ0 (Work.Spaces.pzIter j φ) := testQ0_pzIter h j
  have h2 : pzIterStar j φ = fun z θ => (-1 : ℝ) ^ j * Work.Spaces.pzIter j φ z θ := rfl
  rw [h2]
  exact testQ0_const_mul _ h1

/-- The transpose of `∂_θ^i` preserves the class of test functions. -/
theorem testQ0_pthIterStar {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) (i : ℕ) :
    TestQ0 (pthIterStar i φ) := by
  have h1 : TestQ0 (Work.Spaces.pthIter i φ) := testQ0_pthIter h i
  have h2 : pthIterStar i φ = fun z θ => (-1 : ℝ) ^ i * Work.Spaces.pthIter i φ z θ := rfl
  rw [h2]
  exact testQ0_const_mul _ h1


end Work.FTS.PhiStar.Honesty.SlotsLimit
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Joint.termWeight_pos_and_continuousOn_Q0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slot weight `termWeight α i` is positive on the open quadrant and continuous there

The weight of the `(j,i)`-term of `HkIntegrand` is

* `w(z)/sin(2θ)^{η/2}` for the pure `D_z`-slots (`i = 0`), and
* `Wt α z θ = w(z)·sin(2θ)^{-γ/2}` for the mixed slots (`i ≥ 1`),

where `w(z) = (1+z)²/z²` is strictly positive for `z > 0` and `sin(2θ) > 0` for
`0 < θ < π/2`.  Hence `termWeight α i` is strictly positive on the open quadrant `Q0`, and it
is continuous there: the two building blocks
`Work.FTS.EllipticEst.continuousOn_wdivsin_Q0` (`i = 0`) and `continuousOn_Wt_Q0` (`i ≥ 1`)
are already the `ContinuousOn` statements of exactly these functions, and `Function.uncurry`
of the (constant) `if`-clause defining `termWeight` reduces to each of them.
-/

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.Joint

open scoped Real Topology
open MeasureTheory Set Filter

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-- **The mixed weight `Wt α = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant.** -/
theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hth : ContinuousOn (fun p : ℝ × ℝ =>
      (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) Q0 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact hw.mul hth

/-- **`termWeight α i` is strictly positive on the open quadrant.** -/
theorem termWeight_pos (α : ℝ) (i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      0 < termWeight α i z θ := by
  intro z θ hz hθ0 hθ1
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]
    exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)
  rcases eq_or_ne i 0 with rfl | hne
  · have h0 : termWeight α 0
        = fun z θ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := rfl
    rw [h0]
    exact div_pos hw (Real.rpow_pos_of_pos hs _)
  · simp only [termWeight]
    rw [ite_eq_right hne, Work.Spaces.Wt, Work.Spaces.wTheta]
    exact mul_pos hw (Real.rpow_pos_of_pos hs _)

/-- **`termWeight α i` is continuous on the open quadrant.** -/
theorem termWeight_continuousOn_Q0 (α : ℝ) (i : ℕ) :
    ContinuousOn (Function.uncurry (termWeight α i)) Q0 := by
  rcases eq_or_ne i 0 with rfl | hne
  · have h : Function.uncurry (termWeight α 0)
        = fun p : ℝ × ℝ => Work.Spaces.w p.1
            / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) := by
      funext p; simp [Function.uncurry, termWeight]
    rw [h]
    exact Work.FTS.EllipticEst.continuousOn_wdivsin_Q0
  · have h : Function.uncurry (termWeight α i)
        = fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2 := by
      funext p
      simp only [Function.uncurry, termWeight]
      rw [ite_eq_right hne]
    rw [h]
    exact continuousOn_Wt_Q0 α

theorem termWeight_pos_and_continuousOn_Q0 (α : ℝ) (i : ℕ) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        0 < Work.FTS.PhiStar.Honesty.SlotsLimit.termWeight α i z θ) ∧
      ContinuousOn (Function.uncurry (Work.FTS.PhiStar.Honesty.SlotsLimit.termWeight α i))
        Work.FTS.EllipticEst.Q0 :=
  ⟨termWeight_pos α i, termWeight_continuousOn_Q0 α i⟩

end Work.FTS.PhiStar.Honesty.SlotsLimit.Joint
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux.test_mul_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux

open scoped MeasureTheory ENNReal Topology
open MeasureTheory Set Filter

/-- A continuous function on the open quadrant is bounded on the (compact) topological support of
a test function, since that support is a compact subset of the quadrant.  Multiplying the test
function by it therefore gives an integrable function on the quadrant: the product is supported
in that compact set, so its integral over `Q0` is a fortiori finite. -/
theorem test_mul_continuousOn {φ V : ℝ → ℝ → ℝ}
    (hφ : Work.FTS.PhiStar.Honesty.SlotsLimit.TestQ0 φ)
    (hV : ContinuousOn (Function.uncurry V) Work.FTS.EllipticEst.Q0) :
    IntegrableOn (fun p : ℝ × ℝ => V p.1 p.2 * φ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  set f : ℝ × ℝ → ℝ := fun p : ℝ × ℝ => V p.1 p.2 * φ p.1 p.2 with hf_def
  change IntegrableOn f Work.FTS.EllipticEst.Q0
  set K : Set (ℝ × ℝ) := tsupport (Function.uncurry φ) with hK_def
  have hKcpt : IsCompact K := hφ.cpt
  have hKsub : K ⊆ Work.FTS.EllipticEst.Q0 := hφ.tsupp
  have hKfin : volume K < ∞ := hKcpt.measure_lt_top
  have hKmeas : MeasurableSet K := hKcpt.isClosed.measurableSet
  -- a global bound for the test function
  obtain ⟨N, hN⟩ := hφ.cpt.exists_bound_of_continuous hφ.continuous
  -- a bound for `V` on the compact support of `φ`
  obtain ⟨M, hM⟩ := hKcpt.exists_bound_of_continuousOn (hV.mono hKsub)
  have hcont : ContinuousOn f K := by
    rw [hf_def]
    exact (hV.mono hKsub).mul (hφ.continuous.continuousOn.mono hKsub)
  have hAESM : AEStronglyMeasurable f (volume.restrict K) :=
    ContinuousOn.aestronglyMeasurable hcont hKmeas
  have hbnd : ∀ᵐ p ∂(volume.restrict K), ‖f p‖ ≤ |M| * |N| := by
    filter_upwards [ae_restrict_mem hKmeas] with p hp
    have h1 : ‖V p.1 p.2‖ ≤ |M| := le_trans (hM p hp) (le_abs_self M)
    have h2 : ‖φ p.1 p.2‖ ≤ |N| := le_trans (hN p) (le_abs_self N)
    rw [hf_def, norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) (abs_nonneg _)
  have hKint : IntegrableOn f K volume :=
    IntegrableOn.of_bound hKfin hAESM (|M| * |N|) hbnd
  -- `f` is supported on the compact set `K`
  have hsub : Work.FTS.EllipticEst.Q0 ∩ Function.support f ⊆ K := by
    intro p hp
    obtain ⟨-, hpsup⟩ := hp
    rw [Function.mem_support] at hpsup
    refine subset_tsupport (Function.uncurry φ) ?_
    rw [Function.mem_support]
    intro hcon
    have hcon' : φ p.1 p.2 = 0 := hcon
    exact hpsup (by
      change V p.1 p.2 * φ p.1 p.2 = 0
      rw [hcon', mul_zero])
  refine IntegrableOn.of_inter_support (Work.FTS.EllipticEst.isOpen_Q0.measurableSet) ?_
  exact hKint.mono_set hsub

end Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux.test_weight_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux

open scoped MeasureTheory ENNReal Topology
open MeasureTheory Set Filter

/-- A function which is bounded on a compact set `K` and vanishes off `K` is globally
integrable. -/
private lemma integrable_of_isCompact_bdd {g : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hcont : ContinuousOn g K) (C : ℝ) (hbdd : ∀ x ∈ K, ‖g x‖ ≤ C)
    (hext : ∀ x, x ∉ K → g x = 0) : Integrable g volume := by
  classical
  have hmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hsm : AEStronglyMeasurable g (volume.restrict K) :=
    hcont.aestronglyMeasurable_of_isCompact hK hmeas
  have hae : ∀ᵐ x ∂(volume.restrict K), ‖g x‖ ≤ C := by
    filter_upwards [self_mem_ae_restrict hmeas] with x hx using hbdd x hx
  exact (IntegrableOn.of_bound hK.measure_lt_top hsm C hae).integrable_of_forall_notMem_eq_zero
    hext

theorem test_weight_facts {ρ : ℝ → ℝ → ℝ}
    (hρpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < ρ p.1 p.2)
    (hρcont : ContinuousOn (Function.uncurry ρ) Work.FTS.EllipticEst.Q0)
    {φ : ℝ → ℝ → ℝ} (hφ : Work.FTS.PhiStar.Honesty.SlotsLimit.TestQ0 φ) :
    IntegrableOn (fun p : ℝ × ℝ => (φ p.1 p.2 / ρ p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 ∧
    AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.1 p.2 / ρ p.1 p.2)
      (volume.restrict Work.FTS.EllipticEst.Q0) ∧
    IntegrableOn (fun p : ℝ × ℝ => (φ p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 ∧
    AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.1 p.2)
      (volume.restrict Work.FTS.EllipticEst.Q0) ∧
    (∃ M : ℝ, ∀ p : ℝ × ℝ, |φ p.1 p.2| ≤ M) ∧
    MeasureTheory.Measure.restrict volume Work.FTS.EllipticEst.Q0
        (tsupport (fun p : ℝ × ℝ => φ p.1 p.2)) < ∞ := by
  classical
  -- `K` is the (compact) support of the test function, strictly inside the quadrant.
  set K : Set (ℝ × ℝ) := tsupport (Function.uncurry φ) with hKdef
  have hKsub : K ⊆ Work.FTS.EllipticEst.Q0 := hφ.tsupp
  have hKcpt : IsCompact K := hφ.cpt
  have hφcont : ContinuousOn (Function.uncurry φ) Work.FTS.EllipticEst.Q0 :=
    hφ.continuous.continuousOn
  have hcontK : ContinuousOn (Function.uncurry φ) K := hφcont.mono hKsub
  -- `φ` and `1/ρ` are bounded on `K`.
  obtain ⟨Mφ, hMφ⟩ := hKcpt.exists_bound_of_continuousOn hcontK
  have hρne : ∀ p ∈ K, Function.uncurry ρ p ≠ 0 :=
    fun p hp => ne_of_gt (hρpos p (hKsub hp))
  obtain ⟨Mρ, hMρ⟩ := hKcpt.exists_bound_of_continuousOn ((hρcont.mono hKsub).inv₀ hρne)
  set A : ℝ := max Mφ 0 with hAdef
  set B : ℝ := max Mρ 0 with hBdef
  have hA0 : 0 ≤ A := le_max_right _ _
  have hB0 : 0 ≤ B := le_max_right _ _
  -- Pointwise bounds on `K`.
  have hbd : ∀ p ∈ K, ‖φ p.1 p.2 / ρ p.1 p.2‖ ≤ A * B := by
    intro p hp
    have h1' : ‖φ p.1 p.2‖ ≤ A := le_trans (hMφ p hp) (le_max_left _ _)
    have h2' : ‖(ρ p.1 p.2)⁻¹‖ ≤ B := le_trans (hMρ p hp) (le_max_left _ _)
    rw [div_eq_mul_inv, norm_mul]
    exact mul_le_mul h1' h2' (norm_nonneg _) hA0
  have hbd_div : ∀ p ∈ K, ‖(φ p.1 p.2 / ρ p.1 p.2) ^ 2‖ ≤ (A * B) ^ 2 := by
    intro p hp
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd p hp) 2
  have hbd_phi : ∀ p ∈ K, ‖(φ p.1 p.2) ^ 2‖ ≤ A ^ 2 := by
    intro p hp
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (le_trans (hMφ p hp) (le_max_left _ _)) 2
  -- Vanishing off `K`.
  have hzero : ∀ p ∉ K, φ p.1 p.2 = 0 := by
    intro p hp
    by_contra h
    exact hp (subset_tsupport (Function.uncurry φ) (Function.mem_support.2 h))
  -- Continuity on `K`.
  have hcont_div : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2 / ρ p.1 p.2) K :=
    hcontK.div (hρcont.mono hKsub) hρne
  -- Integrability on `K` and hence globally.
  have hInt1 : Integrable (fun p : ℝ × ℝ => (φ p.1 p.2 / ρ p.1 p.2) ^ 2) volume :=
    integrable_of_isCompact_bdd hKcpt (hcont_div.pow 2) _ hbd_div
      (fun p hp => by simp [hzero p hp])
  have hInt3 : Integrable (fun p : ℝ × ℝ => (φ p.1 p.2) ^ 2) volume :=
    integrable_of_isCompact_bdd hKcpt (hcontK.pow 2) _ hbd_phi
      (fun p hp => by simp [hzero p hp])
  -- Measurability on the quadrant.
  have hdivQ : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2 / ρ p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    ContinuousOn.div hφcont hρcont (fun p hp => ne_of_gt (hρpos p hp))
  refine ⟨hInt1.integrableOn, ?_, hInt3.integrableOn, ?_, ?_, ?_⟩
  · exact hdivQ.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  · exact hφcont.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  · obtain ⟨Cφ, hCφ⟩ := hφ.cpt.exists_bound_of_continuous hφ.continuous
    exact ⟨max Cφ 0, fun p => by
      have h := hCφ p
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_left _ _)⟩
  · refine lt_of_le_of_lt (Measure.restrict_apply_le (μ := volume) Work.FTS.EllipticEst.Q0
      (tsupport (fun p : ℝ × ℝ => φ p.1 p.2))) ?_
    exact hKcpt.measure_lt_top

end Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.term_integral_le_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

/-- **Every term of the level-`k` integrand is bounded by the level-`k` norm.**  For `h` smooth on the open quadrant and `h ∈ ℋ^k`, the `(j,i)`-sub-slot of `h` (with the guard `i = 0 ∧ j ≤ k` for the pure terms and `1 ≤ i ∧ i + j ≤ k` for the mixed ones) is bounded in weighted `L²` by the whole `ℋ^k`-norm; the weight is `termWeight α i` (the pure `w/√sin^η` for `i = 0`, `Wt` otherwise), and the integral is the set integral over the open quadrant `Q0`, which agrees with the iterated integral because the integrand vanishes on the boundary and is jointly a.e. strongly measurable (smoothness on `Q0`). -/
theorem term_integral_le_HkSq (α : ℝ) (k : ℕ) {h : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h) (hmem : Work.Spaces.HkMem α k h)
    (j i : ℕ) (hij : (i = 0 ∧ j ≤ k) ∨ (1 ≤ i ∧ i + j ≤ k)) :
    (∫ p in Work.FTS.EllipticEst.Q0,
        (Work.Spaces.mixed j i h p.1 p.2 * termWeight α i p.1 p.2) ^ 2)
      ≤ Work.Spaces.HkSq α k h := by
  -- The open quadrant is contained in the closed one, and the weights vanish on the boundary,
  -- so it suffices to bound the single summand of `HkIntegrand` and integrate over `Iz ×ˢ Iθ`.
  have hsub : Work.FTS.EllipticEst.Q0 ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    intro p hp
    simp only [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
    exact ⟨le_of_lt hp.1, le_of_lt hp.2.1, le_of_lt hp.2.2⟩
  -- **The pointwise bound**: the `(j,i)`-term of `HkIntegrand` dominates the slot.
  have hFsq : ∀ z θ : ℝ, (Work.Spaces.mixed j i h z θ
      * termWeight α i z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k h z θ := by
    intro z θ
    rcases hij with ⟨rfl, hjk⟩ | ⟨hi1, hijk⟩
    · have htw : termWeight α 0 z θ
          = Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
        simp [termWeight]
      rw [Work.Spaces.mixed_zero_right, htw]
      exact Work.Spaces.sq_le_HkIntegrand_z α k h z θ j hjk
    · have hne : i ≠ 0 := by omega
      have htw : termWeight α i z θ = Work.Spaces.Wt α z θ := by
        simp [termWeight, hne]
      rw [htw]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α k h z θ i j hi1 hijk
  have hHnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α k h z θ := by
    intro z θ
    rw [Work.Spaces.HkIntegrand]
    exact add_nonneg (Work.Spaces.hkZSum_nonneg α k h z θ)
      (Work.Spaces.hkMixedSum_nonneg α k h z θ)
  -- **Joint integrability** of the integrand over `Iz ×ˢ Iθ`, by one-sided Tonelli: the
  -- a.e. strong measurability comes from continuity on the open quadrant (`hsm`), and the
  -- two iterated integrability conditions are exactly `HkMem`.
  have hAE : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.HkIntegrand α k h z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      (Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand hsm α k)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α k h z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  obtain ⟨hInt, hEq⟩ := Work.Spaces.integrable_prod_of_iterated
    (G := fun z θ : ℝ => Work.Spaces.HkIntegrand α k h z θ) hHnn hAE hslice hmem.2
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      = MeasureTheory.volume.prod (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    MeasureTheory.Measure.volume_eq_prod ℝ ℝ
  have hmeas : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  have hIntOn : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    show MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    rw [hvol, ← MeasureTheory.Measure.prod_restrict (Work.Spaces.Iz) (Work.Spaces.Iθ)]
    exact hInt
  have hIntIndicator : MeasureTheory.Integrable
      ((Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2))
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) :=
    (MeasureTheory.integrable_indicator_iff hmeas).mpr hIntOn
  -- The product integral of the integrand is exactly the iterated integral defining `HkSq`.
  have hEqOn : (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k h p.1 p.2) = Work.Spaces.HkSq α k h := by
    have hstep : (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k h p.1 p.2)
        = ∫ p, Work.Spaces.HkIntegrand α k h p.1 p.2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      show (∫ p, Work.Spaces.HkIntegrand α k h p.1 p.2
            ∂((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
              (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))) = _
      rw [hvol, ← MeasureTheory.Measure.prod_restrict (Work.Spaces.Iz) (Work.Spaces.Iθ)]
    rw [hstep, hEq]
    rfl
  -- The indicator of `Q0` is dominated by the indicator of `Iz ×ˢ Iθ`.
  have hpoint : ∀ p : ℝ × ℝ, Work.FTS.EllipticEst.Q0.indicator
        (fun p : ℝ × ℝ => (Work.Spaces.mixed j i h p.1 p.2
          * termWeight α i p.1 p.2) ^ 2) p
      ≤ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2) p := by
    intro p
    by_cases hp : p ∈ Work.FTS.EllipticEst.Q0
    · have hp' : p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := hsub hp
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp']
      exact hFsq p.1 p.2
    · rw [Set.indicator_of_notMem hp]
      by_cases hp' : p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ
      · rw [Set.indicator_of_mem hp']
        exact hHnn p.1 p.2
      · rw [Set.indicator_of_notMem hp']
  calc (∫ p in Work.FTS.EllipticEst.Q0,
        (Work.Spaces.mixed j i h p.1 p.2 * termWeight α i p.1 p.2) ^ 2)
      = ∫ p, Work.FTS.EllipticEst.Q0.indicator
          (fun p : ℝ × ℝ => (Work.Spaces.mixed j i h p.1 p.2
            * termWeight α i p.1 p.2) ^ 2) p :=
        (MeasureTheory.integral_indicator Work.FTS.EllipticEst.isOpen_Q0.measurableSet).symm
    _ ≤ ∫ p, (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2) p :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun p => Set.indicator_nonneg (fun _ _ => sq_nonneg _) p)
          hIntIndicator
          (Filter.Eventually.of_forall hpoint)
    _ = (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k h p.1 p.2) :=
        MeasureTheory.integral_indicator hmeas
    _ = Work.Spaces.HkSq α k h := hEqOn

end Work.FTS.PhiStar.Honesty.SlotsLimit
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.aemeasurable_cmode_clamp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty

/-- The clamped mode coefficient is a.e. measurable: it agrees with `cmode m F` on the open
half-line `(0,∞)`, where the latter is a.e. strongly measurable
(`Work.EllipticEst.ModalSolution.aesm_cmode`), and it vanishes off `(0,∞)`.

Formally, the clamp is the indicator of `(0,∞)` applied to `cmode m F`, and
`aemeasurable_indicator_iff` converts a.e. measurability of an indicator into a.e. measurability
of the function for the restricted measure on the set. -/
theorem aemeasurable_cmode_clamp {α : ℝ} {F : ℝ → ℝ → ℝ} (m : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) :
    AEMeasurable (fun z : ℝ => if 0 < z then Work.FTS.PhiStar.Series.cmode m F z else 0) := by
  have haesm : AEStronglyMeasurable (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Work.EllipticEst.ModalSolution.aesm_cmode hsm m
  have hc : AEMeasurable (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    aestronglyMeasurable_iff_aemeasurable.mp haesm
  have hkey : AEMeasurable (Set.indicator (Set.Ioi (0 : ℝ))
      (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z)) (volume : Measure ℝ) :=
    (aemeasurable_indicator_iff measurableSet_Ioi).mpr hc
  have hpt : ∀ z : ℝ, Set.indicator (Set.Ioi (0 : ℝ))
      (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z) z
        = (fun z : ℝ => if 0 < z then Work.FTS.PhiStar.Series.cmode m F z else 0) z := by
    intro z
    by_cases hz : 0 < z
    · simp [Set.indicator_of_mem, Set.mem_Ioi, hz]
    · simp [Set.indicator_of_notMem, Set.mem_Ioi, hz]
  exact (aemeasurable_congr (μ := (volume : Measure ℝ))
    (Filter.Eventually.of_forall hpt)).mp hkey

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.pz_abs_slice_le_sqrt_Hk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular slice of `∂_zF` is bounded by the square root of the `H^1` integrand

For a source `F` which is `C^∞` on the open quadrant `(0,∞) × (0,π/2)` and honest in the
weighted space `ℋ^1` (`Work.Spaces.HkMem α 1 F`), the angular slice of the radial derivative
at radius `t > 0` satisfies

  `∫_{Iθ} |∂_zF(t,θ)| dθ ≤ √(π/2) · t/(1+t)² · √(∫_{Iθ} HkIntegrand α 1 F t θ dθ)`.

**Route.**  The `i = 1` summand of the `ℋ^1`-integrand is

  `(D_z ∂_zF · w(t)/sin(2θ)^{η/2})² = (t·∂_zF(t,θ)·w(t)/sin(2θ)^{η/2})²`,

and `t·w(t) = (1+t)²/t`, so on the interior of `Iθ` (where `sin(2θ) > 0` and hence
`sin(2θ)^{η/2} ≤ 1`) that summand dominates `((1+t)²/t · ∂_zF)²`.  Inverting the factor
`(1+t)²/t = 1/c` with `c = t/(1+t)²` gives the *pointwise* bound

  `|∂_zF(t,θ)|² ≤ c² · HkIntegrand α 1 F t θ`,

hence `|∂_zF(t,θ)| ≤ c · √(HkIntegrand α 1 F t θ)`.  The two endpoints `0, π/2` are null.
Integrating this a.e. inequality (both sides are integrable: the left one by
`slice_abs_integrable`, the right one since `√x ≤ x + 1`) and applying Cauchy–Schwarz
(`sq_integral_sqrt_mul_le` with the constant function `1`, whose integral over `Iθ` is
`π/2`) gives the claim.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- **Pointwise bound.**  On the interior of the angular interval the square of the radial
derivative of the slice is dominated by the `ℋ^1`-integrand, with the constant
`(t/(1+t)²)²` coming from the radial weight `w(t) = (1+t)²/t²` and the `t` of `D_z`. -/
private lemma pz_sq_le_HkIntegrand {α : ℝ} {F : ℝ → ℝ → ℝ} {t θ : ℝ} (ht : 0 < t)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.pz F t θ) ^ 2
      ≤ (t / (1 + t) ^ 2) ^ 2 * Work.Spaces.HkIntegrand α 1 F t θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hse : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs _
  have hse1 : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hs.le (Real.sin_le_one _) (by rw [Work.Spaces.eta]; norm_num)
  -- the `i = 1` summand of the integrand
  have hterm := Work.Spaces.sq_le_HkIntegrand_z α 1 F t θ 1 le_rfl
  have hDz : Work.Spaces.DzIter 1 F t θ = t * Work.Spaces.pz F t θ := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  rw [hDz] at hterm
  set A : ℝ := t * (Work.Spaces.w t / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) with hA
  have hterm' : (Work.Spaces.pz F t θ * A) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 F t θ := by
    have heq : Work.Spaces.pz F t θ * A
        = t * Work.Spaces.pz F t θ
          * (Work.Spaces.w t / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) := by
      rw [hA]; ring
    rwa [heq]
  have hpz_sq : (Work.Spaces.pz F t θ) ^ 2 * A ^ 2 ≤ Work.Spaces.HkIntegrand α 1 F t θ := by
    have : (Work.Spaces.pz F t θ * A) ^ 2 = (Work.Spaces.pz F t θ) ^ 2 * A ^ 2 := mul_pow _ _ 2
    rwa [this] at hterm'
  -- `A = u/sin(2θ)^{η/2}` with `u = (1+t)²/t ≥ 4`, and `sin(2θ)^{η/2} ≤ 1`, so `A ≥ u`
  set u : ℝ := (1 + t) ^ 2 / t with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hAw : A = u / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
    rw [hA, hu, Work.Spaces.w]
    field_simp
  have hAge : u ≤ A := by
    rw [hAw, le_div_iff₀ hse]
    exact mul_le_of_le_one_right hu0.le hse1
  have hAge2 : u ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hu0.le hAge 2
  have hpu : (Work.Spaces.pz F t θ) ^ 2 * u ^ 2 ≤ Work.Spaces.HkIntegrand α 1 F t θ :=
    le_trans (mul_le_mul_of_nonneg_left hAge2 (sq_nonneg _)) hpz_sq
  have h1 : (Work.Spaces.pz F t θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 F t θ / u ^ 2 :=
    (le_div_iff₀ (pow_pos hu0 2)).mpr hpu
  -- `t/(1+t)² = 1/u`
  have hcu : t / (1 + t) ^ 2 = 1 / u := by rw [hu]; field_simp
  calc (Work.Spaces.pz F t θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 1 F t θ / u ^ 2 := h1
    _ = (t / (1 + t) ^ 2) ^ 2 * Work.Spaces.HkIntegrand α 1 F t θ := by
        rw [hcu, one_div, inv_pow, div_eq_mul_inv]
        ring

/-- **Pointwise square-root bound**: the absolute value of the radial derivative of the slice
is dominated by `t/(1+t)²` times the square root of the `ℋ^1`-integrand. -/
private lemma pz_abs_le_sqrt_HkIntegrand {α : ℝ} {F : ℝ → ℝ → ℝ} {t θ : ℝ} (ht : 0 < t)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    |Work.Spaces.pz F t θ|
      ≤ (t / (1 + t) ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ) := by
  have hsq := pz_sq_le_HkIntegrand (α := α) (F := F) ht hθ
  rw [← sq_abs (Work.Spaces.pz F t θ)] at hsq
  have hc : 0 ≤ t / (1 + t) ^ 2 := by positivity
  have h1 : Real.sqrt ((|Work.Spaces.pz F t θ|) ^ 2) = |Work.Spaces.pz F t θ| := by
    rw [Real.sqrt_sq_eq_abs, abs_abs]
  have h2 : Real.sqrt ((t / (1 + t) ^ 2) ^ 2 * Work.Spaces.HkIntegrand α 1 F t θ)
      = (t / (1 + t) ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]
  have := Real.sqrt_le_sqrt hsq
  rwa [h1, h2] at this

theorem pz_abs_slice_le_sqrt_Hk {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 1 F)
    {t : ℝ} (ht : 0 < t) :
    (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|)
      ≤ Real.sqrt (Real.pi / 2) * (t / (1 + t) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) := by
  have hcpos : 0 < t / (1 + t) ^ 2 := by positivity
  have hHk : IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ) Work.Spaces.Iθ :=
    hF.1 t (Set.mem_Ici.mpr ht.le)
  have hcone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (C := (1 : ℝ)) (s := Work.Spaces.Iθ)
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  -- `√(HkIntegrand)` is integrable on the slice, by `√x ≤ x + 1`
  have hsqrt_int : IntegrableOn (fun θ : ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ))
      Work.Spaces.Iθ := by
    have hdom : IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ + 1)
        Work.Spaces.Iθ := hHk.add hcone
    refine Integrable.mono' hdom ?_ ?_
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable hHk.aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun θ => ?_)
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have hnn := Work.Spaces.HkIntegrand_nonneg α 1 F t θ
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith⟩
  -- the two endpoints of `Iθ` are null
  have hmeq : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))).symm
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.pz F t θ|
        ≤ (t / (1 + t) ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ) := by
    rw [hmeq]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => pz_abs_le_sqrt_HkIntegrand (α := α) (F := F) ht hθ)
  have hint1 : IntegrableOn (fun θ : ℝ => |Work.Spaces.pz F t θ|) Work.Spaces.Iθ :=
    (Work.FTS.PhiStar.Honesty.slice_abs_integrable hsm hF ht).2
  have hint2 : IntegrableOn
      (fun θ : ℝ => (t / (1 + t) ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ))
      Work.Spaces.Iθ := hsqrt_int.const_mul _
  have hmono : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (t / (1 + t) ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ) :=
    integral_mono_ae hint1 hint2 hpt
  -- Cauchy–Schwarz with the constant function `1`
  have hcs := Work.PhiStar.Honesty.sq_integral_sqrt_mul_le (s := Work.Spaces.Iθ) measurableSet_Icc
    (A := fun _ : ℝ => (1 : ℝ))
    (B := fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ)
    hcone hHk (fun _ _ => zero_le_one) (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 1 F t θ)
  have hvol : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Work.Spaces.Iθ]
    simp only [Measure.real, Real.volume_Icc, sub_zero]
    exact ENNReal.toReal_ofReal (by positivity)
  have hsqrt_cs : (∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ))
      ≤ Real.sqrt (Real.pi / 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) := by
    have hsq_le : (∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ)) ^ 2
        ≤ (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) := by
      have h := hcs
      simp only [Real.sqrt_one, one_mul] at h
      rwa [hvol] at h
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ) :=
      integral_nonneg (fun θ => Real.sqrt_nonneg _)
    have hstep := Real.sqrt_le_sqrt hsq_le
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hstep
    exact hstep
  calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (t / (1 + t) ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ) := hmono
    _ = (t / (1 + t) ^ 2)
          * ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ (t / (1 + t) ^ 2) * (Real.sqrt (Real.pi / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ)) :=
        mul_le_mul_of_nonneg_left hsqrt_cs hcpos.le
    _ = Real.sqrt (Real.pi / 2) * (t / (1 + t) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) := by ring

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.slice_abs_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `L¹`-norms of the two first-order angular slices are dominated by the `ℋ¹` integrand

For a source `F` which is `C^∞` on the open quadrant and honest in the weighted space `ℋ¹`
(`Work.Spaces.HkMem α 1 F`), and for radii `0 < a ≤ t`,

  `∫_θ |F t θ| ≤ ∫_θ HkIntegrand α 1 F t θ + π/4`,
  `∫_θ |∂_zF t θ| ≤ (∫_θ HkIntegrand α 1 F t θ)/a² + π/4`.

The pointwise input (proved in `Honesty.slice_pointwise_le`) is that on the *open* angular
interval `(0,π/2)` the two slices are dominated by the `ℋ¹` integrand:

  `|F t θ| ≤ HkIntegrand α 1 F t θ + 1/2`,
  `|∂_zF t θ| ≤ HkIntegrand α 1 F t θ / a² + 1/2`,

which follows from the two summands `i = 0`, `i = 1` of `HkIntegrand α 1 F` (for `θ ∈ (0,π/2)`
the weight factor `w t / sin(2θ)^{η/2}` is `≥ 1`, so `(F t θ)² ≤ HkIntegrand α 1 F t θ` and
`t²(∂_zF t θ)² ≤ HkIntegrand α 1 F t θ`, and `t ≥ a > 0` converts the second into
`(∂_zF t θ)² ≤ HkIntegrand α 1 F t θ / a²`) together with `|x| ≤ x² + 1/2`.

The two exceptional points `θ = 0, π/2` (where `sin(2θ) = 0` collapses the weight and the bound
need not hold) form a null set, so the bounds hold a.e. on `Iθ = [0,π/2]`.  The functions
`θ ↦ |F t θ|` and `θ ↦ |∂_zF t θ|` are integrable on the slice (this is `slice_abs_integrable`),
as is `θ ↦ HkIntegrand α 1 F t θ` (this is the first conjunct of `HkMem α 1 F`, at any `t ∈ Iz`),
so `integral_mono_ae` over the finite measure space `Iθ` (of measure `π/2`) gives the two claims,
the additive constant being `(1/2)·(π/2) = π/4`.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-- The integral of the constant `1/2` over the angular interval `Iθ = [0,π/2]` is `π/4`. -/
private lemma integral_Iθ_half : (∫ θ in Work.Spaces.Iθ, ((1 : ℝ) / 2)) = Real.pi / 4 := by
  rw [MeasureTheory.setIntegral_const, Work.Spaces.Iθ, MeasureTheory.Measure.real,
    Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0)]
  ring

/-! ## The main lemma -/

theorem slice_abs_integral_le {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 1 F)
    {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    (∫ θ in Work.Spaces.Iθ, |F t θ|)
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) + Real.pi / 4 ∧
      (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|)
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) / a ^ 2
          + Real.pi / 4 := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have htIz : t ∈ Work.Spaces.Iz := Set.mem_Ici.mpr ht.le
  have hHk : IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ)
      Work.Spaces.Iθ := hF.1 t htIz
  obtain ⟨hFint, hPint⟩ := slice_abs_integrable hsm hF ht
  -- `Iθ` and the open interval `(0,π/2)` differ by the null set `{0, π/2}`
  have hmeq : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ) / 2) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (C := (1 / 2 : ℝ)) (s := Work.Spaces.Iθ)
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |F t θ| ≤ Work.Spaces.HkIntegrand α 1 F t θ + 1 / 2 ∧
        |Work.Spaces.pz F t θ| ≤ Work.Spaces.HkIntegrand α 1 F t θ / a ^ 2 + 1 / 2 :=
    fun θ hθ => slice_pointwise_le ha hat hθ
  constructor
  · have hg : IntegrableOn
        (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ + 1 / 2) Work.Spaces.Iθ :=
      hHk.add hconst
    have hle : (fun θ : ℝ => |F t θ|)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ + 1 / 2) := by
      rw [hmeq]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => (hpt θ hθ).1)
    calc (∫ θ in Work.Spaces.Iθ, |F t θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α 1 F t θ + 1 / 2) :=
          integral_mono_ae hFint hg hle
      _ = (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) + Real.pi / 4 := by
          rw [integral_add hHk hconst, integral_Iθ_half]
  · have hHk2 : IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ / a ^ 2)
        Work.Spaces.Iθ := hHk.div_const _
    have hg : IntegrableOn
        (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ / a ^ 2 + 1 / 2) Work.Spaces.Iθ :=
      hHk2.add hconst
    have hle : (fun θ : ℝ => |Work.Spaces.pz F t θ|)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ / a ^ 2 + 1 / 2) := by
      rw [hmeq]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => (hpt θ hθ).2)
    calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α 1 F t θ / a ^ 2 + 1 / 2) :=
          integral_mono_ae hPint hg hle
      _ = (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) / a ^ 2 + Real.pi / 4 := by
          rw [integral_add hHk2 hconst, MeasureTheory.integral_div, integral_Iθ_half]

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.thetaTraces_orthSource =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PhiStar.thetaTraces_orthSource` — θ-traces of the orthogonalised source (R6(4), 2026-10-11)

`orthSource g = g - (15/4)·sin 2θ·F_*(g)(z)`.  On the open quadrant
`D_z^s (orthSource g) = D_z^s g + A(z)·sin 2θ` with `A(z) = D_z^s(-(15/4)F_*(g))(z)`, and
`sin(2θ)^{1-γ}·sin(2θ)² = sin(2θ)^{3-γ} → 0` at both angular ends (`γ = 1 + α/10 ≤ 11/10`).
-/

noncomputable section
open scoped Real Topology
open Filter

namespace Work.FTS.PhiStar

/-- `D_z`-iterates of a radial function do not depend on the angle. -/
theorem DzIter_radial_indep (f : ℝ → ℝ) (n : ℕ) (z θ θ' : ℝ) :
    Work.Spaces.DzIter n (fun z _ => f z) z θ = Work.Spaces.DzIter n (fun z _ => f z) z θ' := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    rw [show (fun z' => Work.Spaces.DzIter n (fun z _ => f z) z' θ)
        = fun z' => Work.Spaces.DzIter n (fun z _ => f z) z' θ' from funext fun z' => ih z']

/-- `sin(2θ)^{1-γ}·sin(2θ)² → 0` along any filter that tends to a zero of `sin 2θ` and on which
`sin 2θ ≥ 0` eventually. -/
theorem sin_rpow_mul_sq_tendsto {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {l : Filter ℝ} {θ₀ : ℝ}
    (hl : l ≤ 𝓝 θ₀) (h0 : Real.sin (2 * θ₀) = 0) (hpos : ∀ᶠ θ in l, 0 ≤ Real.sin (2 * θ)) :
    Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * Real.sin (2 * θ) ^ 2)
      l (𝓝 0) := by
  have hq : 0 < 3 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hsin : Tendsto (fun θ => Real.sin (2 * θ)) l (𝓝 0) := by
    have h1 : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝 θ₀) (𝓝 (Real.sin (2 * θ₀))) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).tendsto θ₀)
    rw [h0] at h1
    exact h1.mono_left hl
  have hc : Tendsto (fun θ => Real.sin (2 * θ) ^ (3 - Work.Spaces.gam α)) l (𝓝 0) := by
    have hr := (Real.continuousAt_rpow_const 0 (3 - Work.Spaces.gam α) (Or.inr hq.le)).tendsto
    rw [Real.zero_rpow hq.ne'] at hr
    exact hr.comp hsin
  refine hc.congr' ?_
  filter_upwards [hpos] with θ hθ
  have hne : (1 - Work.Spaces.gam α) + 2 ≠ 0 := by intro h; linarith
  rw [show (3 - Work.Spaces.gam α) = (1 - Work.Spaces.gam α) + 2 by ring,
    Real.rpow_add' hθ hne, Real.rpow_two]

/-- Transfer of a θ-trace through `n = m + A·sin 2θ`. -/
theorem trace_add_sin {α A : ℝ} {m n : ℝ → ℝ} {l : Filter ℝ}
    (hl : ∀ᶠ θ in l, θ ∈ Set.Ioo 0 (π / 2))
    (heq : ∀ θ, 0 < θ → θ < π / 2 → n θ = m θ + A * Real.sin (2 * θ))
    (hm : Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (m θ) ^ 2) l (𝓝 0))
    (hs : Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * Real.sin (2 * θ) ^ 2)
      l (𝓝 0)) :
    Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (n θ) ^ 2) l (𝓝 0) := by
  have hlim : Tendsto (fun θ => 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (m θ) ^ 2)
      + 2 * A ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * Real.sin (2 * θ) ^ 2))
      l (𝓝 0) := by
    simpa using (hm.const_mul 2).add (hs.const_mul (2 * A ^ 2))
  have hp : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) → 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
    fun θ hθ => Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2])) _
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hl] with θ hθ
    exact mul_nonneg (hp θ hθ) (sq_nonneg _)
  · filter_upwards [hl] with θ hθ
    rw [heq θ hθ.1 hθ.2]
    have hsq : (m θ + A * Real.sin (2 * θ)) ^ 2
        ≤ 2 * (m θ) ^ 2 + 2 * A ^ 2 * Real.sin (2 * θ) ^ 2 := by
      nlinarith [sq_nonneg (m θ - A * Real.sin (2 * θ))]
    calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (m θ + A * Real.sin (2 * θ)) ^ 2
        ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (2 * (m θ) ^ 2 + 2 * A ^ 2 * Real.sin (2 * θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (hp θ hθ)
      _ = 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (m θ) ^ 2)
            + 2 * A ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * Real.sin (2 * θ) ^ 2) := by ring

/-- **R6(4) — the θ-traces of the orthogonalised source.** -/
theorem thetaTraces_orthSource {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hF : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Elliptic.Fstar g) (Set.Ioi 0))
    (h : ThetaTraces α k g) : ThetaTraces α k (Work.Elliptic.orthSource g) := by
  set f : ℝ → ℝ := fun z => (-(15 / 4)) * Work.Elliptic.Fstar g z with hfdef
  have hfsm : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) f (Set.Ioi 0) :=
    fun m => (contDiffOn_const (c := (-(15 / 4) : ℝ))).mul (hF m)
  have hsin : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hSsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z * Real.sin (2 * θ)) :=
    Work.FTS.EllExist.sep_mul_open (g := f) (χ := fun θ : ℝ => Real.sin (2 * θ)) hfsm hsin
  have horth : Work.Elliptic.orthSource g = fun z θ => g z θ + f z * Real.sin (2 * θ) := by
    funext z θ
    simp only [Work.Elliptic.orthSource, hfdef]
    ring
  intro s hs z hz
  have hz0 : 0 < z := hz
  obtain ⟨h0, h1⟩ := h s hs z hz
  set A : ℝ := Work.Spaces.DzIter s (fun z _ => f z) z 0 with hA
  have hmix : ∀ θ, 0 < θ → θ < π / 2 →
      Work.Spaces.mixed s 0 (Work.Elliptic.orthSource g) z θ
        = Work.Spaces.mixed s 0 g z θ + A * Real.sin (2 * θ) := by
    intro θ hθ0 hθ1
    rw [horth, Work.FTS.EllipticEst.SmoothOpen.mixed_add hsm hSsm s 0 z θ hz0 hθ0 hθ1,
      Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.mixed_sep_product s 0 f
        (fun θ => Real.sin (2 * θ)) z θ,
      DzIter_radial_indep f s z θ 0]
    rfl
  have hIoo0 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Set.Ioo 0 (π / 2) :=
    Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by positivity)
  have hIoo1 : ∀ᶠ θ in 𝓝[<] (π / 2), θ ∈ Set.Ioo 0 (π / 2) :=
    Ioo_mem_nhdsLT (show (0 : ℝ) < π / 2 by positivity)
  have hnn : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) → 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  refine ⟨?_, ?_⟩
  · refine trace_add_sin (m := fun θ => Work.Spaces.mixed s 0 g z θ) hIoo0 hmix h0 ?_
    exact sin_rpow_mul_sq_tendsto hα hα1 nhdsWithin_le_nhds (by simp)
      (hIoo0.mono fun θ hθ => hnn θ hθ)
  · refine trace_add_sin (m := fun θ => Work.Spaces.mixed s 0 g z θ) hIoo1 hmix h1 ?_
    exact sin_rpow_mul_sq_tendsto hα hα1 nhdsWithin_le_nhds
      (by rw [show 2 * (π / 2) = π by ring]; exact Real.sin_pi)
      (hIoo1.mono fun θ hθ => hnn θ hθ)

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.contDiffOn_zero_mixed_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Filter Set

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false

/-- `D_θ^i` costs `i` orders of differentiability: the `i`-fold `θ`-iterate of a function
of class `C^m` on `Q0` is of class `C^{m-i}` (with the natural-valued order `m - i`). -/
theorem contDiffOn_DthIter_sub {m : ℕ} {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ (m : ℕ∞ω) (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    ∀ i : ℕ, i ≤ m →
      ContDiffOn ℝ ((m - i : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.DthIter i G))
        Work.FTS.EllipticEst.Q0 := by
  intro i
  induction i with
  | zero => intro _; simpa using h
  | succ i ih =>
      intro hi
      have hih : ContDiffOn ℝ ((m - i : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.DthIter i G)) Work.FTS.EllipticEst.Q0 :=
        ih (by omega)
      have hsub : m - i = (m - (i + 1)) + 1 := by omega
      rw [Work.Spaces.DthIter_succ]
      exact contDiffOn_uncurry_Dth_succ
        (n := ((m - (i + 1) : ℕ) : ℕ∞ω)) Work.FTS.EllipticEst.isOpen_Q0
        (by simpa [hsub, Nat.cast_add, Nat.cast_one] using hih)

/-- `D_z^j` costs `j` orders of differentiability: the `j`-fold `z`-iterate of a function
of class `C^m` on `Q0` is of class `C^{m-j}` (with the natural-valued order `m - j`). -/
theorem contDiffOn_DzIter_sub {m : ℕ} {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ (m : ℕ∞ω) (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    ∀ j : ℕ, j ≤ m →
      ContDiffOn ℝ ((m - j : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.DzIter j G))
        Work.FTS.EllipticEst.Q0 := by
  intro j
  induction j with
  | zero => intro _; simpa using h
  | succ j ih =>
      intro hj
      have hih : ContDiffOn ℝ ((m - j : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.DzIter j G)) Work.FTS.EllipticEst.Q0 :=
        ih (by omega)
      have hsub : m - j = (m - (j + 1)) + 1 := by omega
      rw [Work.Spaces.DzIter_succ]
      exact contDiffOn_uncurry_Dz_succ
        (n := ((m - (j + 1) : ℕ) : ℕ∞ω)) Work.FTS.EllipticEst.isOpen_Q0
        (by simpa [hsub, Nat.cast_add, Nat.cast_one] using hih)

/-- Every slot `D_z^j D_θ^i` with `j + i ≤ n` of a function of class `C^n` on `Q0` is
continuous there (the finite-order counterpart of `contDiffOn_zero_mixed`). -/
theorem contDiffOn_zero_mixed_le {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry G) Work.FTS.EllipticEst.Q0) {j i : ℕ}
    (hji : j + i ≤ n) :
    ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.mixed j i G)) Work.FTS.EllipticEst.Q0 := by
  have hDth : ContDiffOn ℝ ((n - i : ℕ) : ℕ∞ω)
      (Function.uncurry (Work.Spaces.DthIter i G)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_DthIter_sub (m := n) h i (by omega)
  have hjn : j ≤ n - i := by omega
  have hDz := contDiffOn_DzIter_sub (m := n - i) hDth j hjn
  have hmi : (n - i) - j = n - (j + i) := by omega
  rw [show ((((n - i) - j : ℕ)) : ℕ∞ω) = ((n - (j + i) : ℕ) : ℕ∞ω) from by rw [hmi]] at hDz
  have h0 : (0 : ℕ∞ω) ≤ ((n - (j + i) : ℕ) : ℕ∞ω) := by positivity
  simpa [Work.Spaces.mixed] using hDz.of_le h0

end Work.FTS.StrongEps.E5Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G5.HkIntegrand_intervalIntegral_le_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G5

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

/-!
# `HkIntegrand` versus the interval integral in `s`, for arbitrary `k`

This is the general-`k` version of
`Work.FTS.StrongEps.E5G.HkIntegrand_intervalIntegral_le` (which is the case `k = 4`).
If every slot `D_z^j D_θ^i (H s) z θ` of the family `s ↦ H s` is measurable and bounded
by `C` on `uIoc a b`, and if the slots of the primitive `∫_s H s` are the integrals of the
slots (the exchange identity `hid`), then

`HkIntegrand α k (∫_s H s) z θ ≤ (b - a) · ∫_s HkIntegrand α k (H s) z θ`.

The proof is slotwise Cauchy–Schwarz in `s`: each slot of `HkIntegrand α k (∫_s H s)` is
`W · ∫_s (slot of H s)`, and `(∫_s φ)² ≤ (b - a) ∫_s φ²`; summing over the finitely many
slots (the ranges `Finset.range (k+1)`) and using that the sum over the slots of `H s` is
exactly `HkIntegrand α k (H s) z θ` gives the claim.  Nothing depends on `k = 4` beyond
the index range, so the argument transcribes verbatim.
-/

/-- The main estimate, for arbitrary `k`. -/
theorem HkIntegrand_intervalIntegral_le_gen {α a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    {H : ℝ → ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {k : ℕ}
    (hmeas : ∀ (j i : ℕ), j + i ≤ k →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (hbdd : ∀ (j i : ℕ), j + i ≤ k → ∀ s ∈ Set.uIoc a b,
      |Work.Spaces.mixed j i (H s) z θ| ≤ C)
    (hid : ∀ j i : ℕ, j + i ≤ k →
      Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ) :
    Work.Spaces.HkIntegrand α k (fun z θ => ∫ s in a..b, H s z θ) z θ
      ≤ (b - a) * ∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) z θ := by
  set G : ℝ → ℝ → ℝ := fun z θ => ∫ s in a..b, H s z θ
  set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hW
  have hvol : volume (Set.uIoc a b) < ⊤ := by
    rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
  -- slot integrability, from measurability and the uniform bound on `uIoc a b`
  have hslot : ∀ (j i : ℕ), j + i ≤ k →
      IntervalIntegrable (fun s => Work.Spaces.mixed j i (H s) z θ) volume a b := by
    intro j i hji
    refine intervalIntegrable_iff.mpr ?_
    refine MeasureTheory.IntegrableOn.of_bound hvol (hmeas j i hji) C ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs
    simpa [Real.norm_eq_abs] using hbdd j i hji s hs
  have hslot2 : ∀ (j i : ℕ), j + i ≤ k → ∀ c : ℝ,
      IntervalIntegrable (fun s => (Work.Spaces.mixed j i (H s) z θ * c) ^ 2) volume a b := by
    intro j i hji c
    refine intervalIntegrable_iff.mpr ?_
    refine MeasureTheory.IntegrableOn.of_bound hvol
      (((hmeas j i hji).mul_const c).pow 2) ((C * |c|) ^ 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs
    have hb1 := hbdd j i hji s hs
    have hb2 : |Work.Spaces.mixed j i (H s) z θ * c| ≤ C * |c| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb1 (abs_nonneg c)
    rw [Real.norm_eq_abs, abs_sq]
    calc (Work.Spaces.mixed j i (H s) z θ * c) ^ 2
        = |Work.Spaces.mixed j i (H s) z θ * c| ^ 2 := (sq_abs _).symm
      _ ≤ (C * |c|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb2 2
  -- unfolding `HkIntegrand α k G z θ` into its two blocks
  have hId : Work.Spaces.HkIntegrand α k G z θ
      = (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i G z θ * W) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    rw [Work.Spaces.HkIntegrand, hW]
  -- the `D_z`-block
  have hPart1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i G z θ * W) ^ 2)
      ≤ (b - a) * ∫ s in a..b, ∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2 := by
    refine le_of_eq_of_le ?_ (Work.FTS.StrongEps.E5G.finset_sum_sq_intervalIntegral_le
      (Finset.range (k + 1)) (fun i s => Work.Spaces.mixed i 0 (H s) z θ * W) hab ?_ ?_)
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i + 0 ≤ k := by have := Finset.mem_range.mp hi; omega
      rw [show Work.Spaces.DzIter i G z θ = ∫ s in a..b, Work.Spaces.mixed i 0 (H s) z θ
        from hid i 0 hik]
      rw [intervalIntegral.integral_mul_const]
    · intro i hi
      have hik : i + 0 ≤ k := by have := Finset.mem_range.mp hi; omega
      exact (hslot i 0 hik).mul_const W
    · intro i hi
      have hik : i + 0 ≤ k := by have := Finset.mem_range.mp hi; omega
      exact hslot2 i 0 hik W
  -- integrability of the mixed slots, in the "`if` inside the square" form
  have hF5 : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
      IntervalIntegrable (fun s => if 1 ≤ i ∧ i + j ≤ k then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) volume a b := by
    intro i hi j hj
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · have hfe : (fun s => if 1 ≤ i ∧ i + j ≤ k then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0)
          = fun s => Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ :=
        funext fun s => ite_eq_left h
      rw [hfe]
      have hij : j + i ≤ k := by omega
      exact (hslot j i hij).mul_const _
    · have hfe : (fun s => if 1 ≤ i ∧ i + j ≤ k then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) = fun _ => 0 :=
        funext fun s => ite_eq_right h
      rw [hfe]; exact intervalIntegrable_const
  have hF5sq : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
      IntervalIntegrable (fun s => (if 1 ≤ i ∧ i + j ≤ k then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2) volume a b := by
    intro i hi j hj
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · have hfe : (fun s => (if 1 ≤ i ∧ i + j ≤ k then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
          = fun s => (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2 :=
        funext fun s => by rw [ite_eq_left h]
      rw [hfe]
      have hij : j + i ≤ k := by omega
      exact hslot2 j i hij _
    · have hfe : (fun s => (if 1 ≤ i ∧ i + j ≤ k then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2) = fun _ => 0 :=
        funext fun s => by rw [ite_eq_right h]; ring
      rw [hfe]; exact intervalIntegrable_const
  -- the mixed block
  have hPart2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (b - a) * ∫ s in a..b, ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2 := by
    have hmain := Work.FTS.StrongEps.E5G.double_sum_sq_intervalIntegral_le
      (Finset.range (k + 1)) (Finset.range (k + 1))
      (fun i j s => if 1 ≤ i ∧ i + j ≤ k then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) hab hF5 hF5sq
    have hL : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (∫ s in a..b, if 1 ≤ i ∧ i + j ≤ k then
              Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2 := by
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
      by_cases h : 1 ≤ i ∧ i + j ≤ k
      · have hij : j + i ≤ k := by omega
        simp only [ite_eq_left h]
        rw [intervalIntegral.integral_mul_const, ← hid j i hij]
      · simp only [ite_eq_right h]
        simp
    rw [hL]
    exact hmain
  -- the slots of the family `H s` recombine into `HkIntegrand α k (H s) z θ`
  have hT : ∀ s : ℝ,
      (∑ i ∈ Finset.range (k + 1), (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2
      = Work.Spaces.HkIntegrand α k (H s) z θ := by
    intro s
    have h1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
        = ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (H s) z θ * W) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by simp only [Work.Spaces.mixed_zero_right]
    have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
        = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases h : 1 ≤ i ∧ i + j ≤ k
      · rw [ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h]; ring
    rw [h1, h2, Work.Spaces.HkIntegrand, hW]
  have hT1int : IntervalIntegrable (fun s => ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2) volume a b :=
    Work.FTS.StrongEps.E5G.intervalIntegrable_finsetSum (Finset.range (k + 1))
      (fun i s => (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
      (fun i hi => by
        have hik : i + 0 ≤ k := by have := Finset.mem_range.mp hi; omega
        exact hslot2 i 0 hik W)
  have hT2int : IntervalIntegrable (fun s => ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2) volume a b :=
    Work.FTS.StrongEps.E5G.intervalIntegrable_finsetSum (Finset.range (k + 1))
      (fun i s => ∑ j ∈ Finset.range (k + 1), (if 1 ≤ i ∧ i + j ≤ k then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
      (fun i hi => Work.FTS.StrongEps.E5G.intervalIntegrable_finsetSum (Finset.range (k + 1))
        (fun j s => (if 1 ≤ i ∧ i + j ≤ k then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
        (fun j hj => hF5sq i hi j hj))
  have hTint : (∫ s in a..b, ∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
      + (∫ s in a..b, ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
      = ∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) z θ := by
    rw [← intervalIntegral.integral_add hT1int hT2int]
    exact intervalIntegral.integral_congr (fun s _ => hT s)
  rw [hId]
  refine le_trans (add_le_add hPart1 hPart2) ?_
  rw [← hTint]
  exact le_of_eq (by ring)

end

end Work.FTS.StrongEps.E5G5
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.OpenLeibniz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2hatOAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `φ(z) = z/(1+z)²` is `C^∞` on the positive half-line. -/
lemma phiZ_contDiffOn : ∀ m : ℕ,
    ContDiffOn ℝ m (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi 0) := by
  intro m
  refine ContDiffOn.div (by fun_prop) (by fun_prop) ?_
  intro z hz
  exact pow_ne_zero 2 (by have hz' : (0 : ℝ) < z := hz; linarith)

/-- A function of `z` alone, `C^∞` on `(0,∞)`, is `SmoothOpen` as a function of `(z,θ)`. -/
lemma smoothOpen_zOnly {ψ : ℝ → ℝ}
    (hψ : ∀ m : ℕ, ContDiffOn ℝ m ψ (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => ψ z) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have hfun : Function.uncurry (fun z _ : ℝ => ψ z) = fun p : ℝ × ℝ => ψ p.1 := rfl
  rw [hfun]
  exact (hψ n).comp contDiffOn_fst (fun p hp => (Set.mem_prod.mp hp).1)

/-- `SmoothOpen` is closed under multiplication. -/
lemma smoothOpen_mul {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => f z θ * g z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [hfun]
  exact hf.mul hg

/-- `SmoothOpen` is closed under multiplication by a constant. -/
lemma smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => c * f z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ : ℝ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := rfl
  rw [hfun]
  exact ContDiffOn.mul (contDiffOn_const (c := c)) hf

/-- **Mixed Leibniz expansion (open quadrant) of a product with a `z`-only factor.**  For
`ψ : ℝ → ℝ` of class `C^∞` on `(0,∞)` and `x` of class `SmoothOpen` (`C^∞` on the open
quadrant `(0,∞) × (0,π/2)`), and for `z > 0`, `θ ∈ (0,π/2)`,
`D_z^j D_θ^i (ψ·x) = ∑_{b ≤ j} C(j,b)·(Zop^b ψ)(z)·(D_z^{j-b}D_θ^i x)(z,θ)`.

`D_θ^i` commutes with the `z`-only factor `ψ` (`GalFields.Norm.DthIter_zmul_rad`, which needs
no smoothness), reducing the claim to the graded `Zop`-Leibniz rule on the `z`-slice
(`GalFields.Norm.Zop_iter_mul_contDiffOn`), where both factors are `C^{j+1}` on `(0,∞)`. -/
theorem mixed_zmul_SO (j i : ℕ) (ψ : ℝ → ℝ) (x : ℝ → ℝ → ℝ)
    (hψ : ∀ m : ℕ, ContDiffOn ℝ m ψ (Set.Ioi 0))
    (hx : Work.FTS.EllipticEst.SmoothOpen x)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.mixed j i (fun z θ : ℝ => ψ z * x z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
          (Work.Spaces.Zop^[b] ψ z * Work.Spaces.mixed (j - b) i x z θ) := by
  have hψj : ContDiffOn ℝ (((j + 1 : ℕ)) : WithTop ℕ∞) ψ (Set.Ioi (0 : ℝ)) := hψ (j + 1)
  have hgj : ContDiffOn ℝ (((j + 1 : ℕ)) : WithTop ℕ∞)
      (fun z : ℝ => Work.Spaces.DthIter i x z θ) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.GalFields.Norm.curry_z_nat_of_smoothOpen (hx.DthIter i) hθ (j + 1)
  have hL : Work.Spaces.mixed j i (fun z θ : ℝ => ψ z * x z θ) z θ
      = Work.Spaces.Zop^[j] (ψ * fun z : ℝ => Work.Spaces.DthIter i x z θ) z := by
    show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ : ℝ => ψ z * x z θ)) z θ
      = Work.Spaces.Zop^[j] (ψ * fun z : ℝ => Work.Spaces.DthIter i x z θ) z
    rw [Work.FTS.GalFields.Norm.DthIter_zmul_rad i ψ x]
    exact congrFun (Work.FTS.LocData.Zop_iterate_slice j
      (fun z θ => ψ z * Work.Spaces.DthIter i x z θ) θ) z
  rw [hL, Work.FTS.GalFields.Norm.Zop_iter_mul_contDiffOn isOpen_Ioi hψj hgj z hz]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hstep : Work.Spaces.Zop^[j - b] (fun z : ℝ => Work.Spaces.DthIter i x z θ) z
      = Work.Spaces.mixed (j - b) i x z θ :=
    (congrFun (Work.FTS.LocData.Zop_iterate_slice (j - b) (Work.Spaces.DthIter i x) θ) z).symm
  rw [hstep]

/-- The `D_z`-only instance of `mixed_zmul_SO`. -/
theorem DzIter_zmul_SO (j : ℕ) (ψ : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hψ : ∀ m : ℕ, ContDiffOn ℝ m ψ (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.DzIter j (fun z θ => ψ z * f z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
          (Work.Spaces.Zop^[b] ψ z * Work.Spaces.DzIter (j - b) f z θ) := by
  simpa only [Work.Spaces.mixed_zero_right] using mixed_zmul_SO j 0 ψ f hψ hf hz hθ

end Work.FTS.StrongEps.EpsE4Thr.E2hatOAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsWp.LGammaT_abs_le_explicit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsWp

/-- `|a / b| ≤ |a|` as soon as `1 ≤ b`. -/
private lemma abs_div_le_abs_of_one_le {a b : ℝ} (hb : 1 ≤ b) : |a / b| ≤ |a| := by
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le one_pos hb
  rw [abs_div, abs_of_nonneg hb0.le, div_le_iff₀ hb0]
  exact le_mul_of_one_le_right (abs_nonneg a) hb

/-- `|a - b| ≤ |a| + |b|`. -/
private lemma abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg] using abs_add_le a (-b)

/-- **`𝓛_Γ^T` is bounded pointwise in terms of the data bound `B`.**  Unfolding
`𝓛_Γ^T = 𝓛 - (2zΓ/(c(1+z)²))L₁₂ - 𝕡(3D_θ/(1+z))` leaves five terms, each bounded by `B`
(the two `1/(1+z)` factors by `B` and `1 + z ≥ 1` on `z ≥ 0`, the two `L₁₂`-coefficients by
`hcoef`/`hcoef2` against `hL12f`/`hL12T`).  This is the pointwise form of
`Work.FTS.StrongEps.LGammaT_abs_le_on_compact`. -/
theorem LGammaT_abs_le_explicit {α B : ℝ} (hB : 0 ≤ B)
    {f : Work.FTS.Galerkin.Fn} {z θ : ℝ} (hz : 0 ≤ z)
    (hbnd : |f z θ| + |Work.Spaces.Dz f z θ| + |Work.Spaces.Dth f z θ| ≤ B)
    (hcoef : |2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2)| ≤ B)
    (hcoef2 : |Work.Spaces.Gam α θ / Work.Spaces.c α * (2 * z ^ 2 / (1 + z) ^ 3)| ≤ B)
    (hL12f : |Work.Coercivity.L12f f z| ≤ B)
    (hL12T : |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0| ≤ B) :
    |Work.Coercivity.LGammaT α f z θ| ≤ 7 * B + 2 * (B * B) := by
  have hz1 : (1 : ℝ) ≤ 1 + z := by linarith
  have hfB : |f z θ| ≤ B := by
    nlinarith [abs_nonneg (Work.Spaces.Dz f z θ), abs_nonneg (Work.Spaces.Dth f z θ)]
  have hDzB : |Work.Spaces.Dz f z θ| ≤ B := by
    nlinarith [abs_nonneg (f z θ), abs_nonneg (Work.Spaces.Dth f z θ)]
  have hDthB : |Work.Spaces.Dth f z θ| ≤ B := by
    nlinarith [abs_nonneg (f z θ), abs_nonneg (Work.Spaces.Dz f z θ)]
  -- unfold `𝓛_Γ^T` once and for all into its five summands
  have hsplit : Work.Coercivity.LGammaT α f z θ
      = (Work.Coercivity.L f z θ
          - (2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
            * Work.Coercivity.L12f f z)
        - (Work.Coercivity.Transport f z θ
          - (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) := rfl
  rw [hsplit]
  -- `𝓛 f = f + D_z f - 2f/(1+z)`, bounded by `2B + 2B`
  have hA : |Work.Coercivity.L f z θ| ≤ 4 * B := by
    have hLf : Work.Coercivity.L f z θ
        = f z θ + Work.Spaces.Dz f z θ - 2 * f z θ / (1 + z) := rfl
    rw [hLf]
    have h1 : |f z θ + Work.Spaces.Dz f z θ - 2 * f z θ / (1 + z)| ≤
        |f z θ + Work.Spaces.Dz f z θ| + |2 * f z θ / (1 + z)| := by
      simpa [sub_eq_add_neg] using
        abs_add_le (f z θ + Work.Spaces.Dz f z θ) (-(2 * f z θ / (1 + z)))
    have h2 : |f z θ + Work.Spaces.Dz f z θ| ≤ |f z θ| + |Work.Spaces.Dz f z θ| :=
      abs_add_le _ _
    have h3 : |2 * f z θ / (1 + z)| ≤ 2 * B := by
      have h4 : |2 * f z θ| ≤ 2 * B := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith
      exact le_trans (abs_div_le_abs_of_one_le (a := 2 * f z θ) hz1) h4
    linarith
  have hCL : |(2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
      * Work.Coercivity.L12f f z| ≤ B * B := by
    rw [abs_mul]
    exact mul_le_mul hcoef hL12f (abs_nonneg _) hB
  -- `Transport f = 3 D_θ f/(1+z)`, bounded by `3B`
  have hB2 : |Work.Coercivity.Transport f z θ| ≤ 3 * B := by
    have hTe : Work.Coercivity.Transport f z θ
        = 3 * Work.Spaces.Dth f z θ / (1 + z) := rfl
    rw [hTe]
    have h5 : |3 * Work.Spaces.Dth f z θ| ≤ 3 * B := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      linarith
    exact le_trans (abs_div_le_abs_of_one_le (a := 3 * Work.Spaces.Dth f z θ) hz1) h5
  have hCT : |(Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
      * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0| ≤ B * B := by
    rw [abs_mul]
    exact mul_le_mul hcoef2 hL12T (abs_nonneg _) hB
  -- assemble: `|X₁| ≤ 4B + B²`, `|X₂| ≤ 3B + B²`, `|X₁ - X₂| ≤ |X₁| + |X₂|`
  have hX1 : |Work.Coercivity.L f z θ
      - (2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
        * Work.Coercivity.L12f f z| ≤ 4 * B + B * B := by
    have h := abs_sub_le_abs_add_abs (Work.Coercivity.L f z θ)
      ((2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
        * Work.Coercivity.L12f f z)
    linarith [h, hA, hCL]
  have hX2 : |Work.Coercivity.Transport f z θ
      - (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0| ≤ 3 * B + B * B := by
    have h := abs_sub_le_abs_add_abs (Work.Coercivity.Transport f z θ)
      ((Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
    linarith [h, hB2, hCT]
  have hfin := abs_sub_le_abs_add_abs
    (Work.Coercivity.L f z θ
      - (2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
        * Work.Coercivity.L12f f z)
    (Work.Coercivity.Transport f z θ
      - (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
  linarith [hfin, hX1, hX2]

end Work.FTS.StrongEps.EpsWp
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.WProd5.Pointwise5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.WProd5

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The Bell numbers of the rows `0 ≤ n ≤ 5` are `1, 1, 2, 5, 15, 52`, all below `100`. -/
theorem bell_le_five (n : ℕ) (hn : n ≤ 5) : Work.Spaces.bell n ≤ 100 := by
  interval_cases n <;> decide

/-- `|z^j ∂_z^j f| ≤ |f|_{𝒲^{5,∞}}` for `j ≤ 5`, on the domain. -/
theorem zpz_le_WlInf5 {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : WlInfMem α 5 f)
    {j : ℕ} (hj : j ≤ 5) {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |z ^ j * pzIter j f z θ| ≤ WlInf α 5 f := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have h := pz_sup_bound α 5 f hmem j hj z θ hz hθ
  have hW := WlInf_nonneg α 5 f hmem
  rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 j)]
  calc z ^ j * |pzIter j f z θ| ≤ z ^ j * (WlInf α 5 f / (z + 1) ^ j) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hz0 j)
    _ = WlInf α 5 f * (z / (z + 1)) ^ j := by rw [div_pow]; ring
    _ ≤ WlInf α 5 f * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hW
        exact pow_le_one₀ (div_nonneg hz0 (by linarith)) (by rw [div_le_one hz1]; linarith)
    _ = WlInf α 5 f := mul_one _

/-- `|z^j ∂_z^j (D_θ^a f)| ≤ |f|_{𝒲^{5,∞}} (α+sin 2θ) sin(2θ)^{α/5}` for `1 ≤ a`,
`j + a ≤ 5`, on the domain. -/
theorem zpz_Dth_le_WlInf5 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (hmem : WlInfMem α 5 f)
    {a : ℕ} (ha : 1 ≤ a) {j : ℕ} (hja : j + a ≤ 5) {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |z ^ j * pzIter j (DthIter a f) z θ| ≤
      WlInf α 5 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have h := pz_Dth_sup_bound α hα 5 f hmem a j ha hja z θ hz hθ
  have hW := WlInf_nonneg α 5 f hmem
  have hnn : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith [sin_two_nonneg' hθ]) (Real.rpow_nonneg (sin_two_nonneg' hθ) _)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 j)]
  have hle1 : (z / (z + 1)) ^ j ≤ 1 :=
    pow_le_one₀ (div_nonneg hz0 (by linarith)) (by rw [div_le_one hz1]; linarith)
  calc z ^ j * |pzIter j (DthIter a f) z θ|
      ≤ z ^ j * (WlInf α 5 f / (z + 1) ^ j
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hz0 j)
    _ = WlInf α 5 f * ((z / (z + 1)) ^ j
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
        rw [div_pow]; ring
    _ ≤ WlInf α 5 f * (1 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle1 hnn) hW
    _ = WlInf α 5 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring

/-- `|D_z^b f| ≤ 100 |f|_{𝒲^{5,∞}}` on the open quadrant, for `b ≤ 5`. -/
theorem dzIter_le_WlInf5 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : WlInfMem α 5 f)
    {b : ℕ} (hb : b ≤ 5) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |DzIter b f z θ| ≤ 100 * WlInf α 5 f := by
  have hzI : z ∈ Iz := le_of_lt hz
  have hθI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hz' : z ∈ Set.Ioi (0 : ℝ) := hz
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => f z' θ) (Set.Ioi 0) :=
    Work.FTS.OpenPkg.smoothOpen_slice_z hf hθ
  have hDz : DzIter b f z θ
      = ∑ k ∈ Finset.range (b + 1),
          (scoef b k : ℝ) * (z ^ k * pzIter k f z θ) :=
    Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open hslice b z hz'
  have hsum := abs_sum_scoef_mul_le b (WlInf α 5 f)
    (fun k => z ^ k * pzIter k f z θ)
    (fun k hk => zpz_le_WlInf5 hfm (le_trans hk hb) hzI hθI)
  have hbell : (bell b : ℝ) ≤ 100 := by exact_mod_cast bell_le_five b hb
  have hW := WlInf_nonneg α 5 f hfm
  calc |DzIter b f z θ|
      = |∑ k ∈ Finset.range (b + 1),
          (scoef b k : ℝ) * (z ^ k * pzIter k f z θ)| := by rw [hDz]
    _ ≤ (bell b : ℝ) * WlInf α 5 f := hsum
    _ ≤ 100 * WlInf α 5 f := mul_le_mul_of_nonneg_right hbell hW

/-- `|D_z^b D_θ^a f| ≤ 100 |f|_{𝒲^{5,∞}} (α+sin 2θ) sin(2θ)^{α/5}` on the open quadrant,
for `1 ≤ a`, `a + b ≤ 5`. -/
theorem mixed_le_WlInf5 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : WlInfMem α 5 f)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 5) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |mixed b a f z θ| ≤ 100 * (WlInf α 5 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  have hzI : z ∈ Iz := le_of_lt hz
  have hθI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hb5 : b ≤ 5 := by omega
  have hsin0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hY : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
  have hW := WlInf_nonneg α 5 f hfm
  have hM : 0 ≤ WlInf α 5 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := mul_nonneg hW hY
  have hbound : ∀ k ≤ b, |z ^ k * pzIter k (DthIter a f) z θ|
      ≤ WlInf α 5 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    fun k hk => zpz_Dth_le_WlInf5 hα hfm ha (by omega) hzI hθI
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => DthIter a f z' θ) (Set.Ioi 0) :=
    Work.FTS.OpenPkg.smoothOpen_DthIter_slice_z hf a hθ
  rw [mixed,
    Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open (h := DthIter a f) hsmooth b z hz]
  have hsum := abs_sum_scoef_mul_le b
    (WlInf α 5 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
    (fun k => z ^ k * pzIter k (DthIter a f) z θ) hbound
  refine le_trans hsum ?_
  calc (bell b : ℝ) * (WlInf α 5 f
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
      ≤ 100 * (WlInf α 5 f
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast bell_le_five b hb5) hM

end Work.FTS.StrongEps.H5.WProd5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12.DensSplit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Two elementary helpers -/




end Work.FTS.StrongEps.L12
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12.HkMemZeroSub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The level-`0` integrand is the square of the weighted datum

At level `0` both `Finset.range (0 + 1)`-sums of `HkIntegrand` collapse: the first one has the
single summand `i = 0`, and the second one is empty because its condition `1 ≤ i` fails there.
Hence `HkIntegrand α 0 f z θ = (Gaz f z θ)²`, with `Gaz` the weighted datum
`h z θ · w z / sin(2θ)^{η/2}` of `Work.FTS.GalBasis.cc`. -/


/-! ## The pointwise domination -/


/-! ## Continuity on the open quadrant -/



end Work.FTS.StrongEps.L12
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12AbsLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-! ## The pointwise bound on the density -/

/-- The `L₁₂`-density at order `0`: angular Cauchy–Schwarz
(`Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le_gen` with `k = 0`) combined with the
factorisation `L12dens f s = Wlam s · ∫_θ K·Sw·Gaz f s ·` of
`Work.FTS.GalBasis.cc.L12dens_eq_weighted`. -/
lemma abs_L12dens_le_zero (α : ℝ) (f : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s)
    (hint : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 f s θ)
      Work.Spaces.Iθ) :
    |Work.Construction.L12dens f s|
      ≤ Work.FTS.GalBasis.cc.Wlam s
        * (Work.FTS.GalBasis.cc.BK * Real.sqrt
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f s θ)) := by
  rw [Work.FTS.GalBasis.cc.L12dens_eq_weighted f hs, abs_mul,
    abs_of_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg hs.le)]
  exact mul_le_mul_of_nonneg_left
    (Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le_gen α 0 f hint)
    (Work.FTS.GalBasis.cc.Wlam_nonneg hs.le)

/-! ## The sharp radial Cauchy–Schwarz bound -/

/-- The pointwise comparison behind the sharp radial weight bound:
`Wlam s² = s²/(1+s)⁴ ≤ s^{-2}` for `s > 0`. -/
lemma Wlam_sq_le_rpow (s : ℝ) (hs : 0 < s) :
    Work.FTS.GalBasis.cc.Wlam s ^ 2 ≤ s ^ (-2 : ℝ) := by
  have h4 : s ^ 4 ≤ (1 + s) ^ 4 := pow_le_pow_left₀ hs.le (by linarith) 4
  have hid : ((1 + s) ^ 2) ^ 2 = (1 + s) ^ 4 := by ring
  have hmain : s ^ 2 / ((1 + s) ^ 2) ^ 2 ≤ 1 / s ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), hid]
    nlinarith [h4]
  have hred : s ^ (-2 : ℝ) = 1 / s ^ 2 := by
    rw [Real.rpow_neg hs.le, Real.rpow_two, inv_eq_one_div]
  rw [Work.FTS.GalBasis.cc.Wlam, div_pow, hred]
  exact hmain

/-- Cauchy–Schwarz in the radial variable, with the sharp weight bound
`∫_{s>z} Wlam² ≤ 1/z`.  No measurability of `A` is assumed: the argument uses the
measurable surrogate `B = √(A²)`, which agrees with `A` on `(z,∞)` because `A ≥ 0` there. -/
lemma Wlam_mul_le_sqrt {A : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hnn : ∀ s ∈ Set.Ioi z, 0 ≤ A s)
    (hint : MeasureTheory.IntegrableOn (fun s => A s ^ 2) (Set.Ioi z)) :
    ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      ≤ Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) := by
  -- the measurable surrogate `B = √(A²)`, equal to `A` on `(z,∞)`
  set B : ℝ → ℝ := fun s => Real.sqrt (A s ^ 2) with hB
  have hBnn : ∀ s, 0 ≤ B s := fun s => Real.sqrt_nonneg _
  have hBeq : B =ᵐ[volume.restrict (Set.Ioi z)] A := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [hB]
    exact Real.sqrt_sq (hnn s hs)
  have hBsq : ∀ s, B s ^ 2 = A s ^ 2 := fun s => by
    change Real.sqrt (A s ^ 2) ^ 2 = A s ^ 2
    exact Real.sq_sqrt (sq_nonneg (A s))
  have hB_aesm : AEStronglyMeasurable B (volume.restrict (Set.Ioi z)) := by
    change AEStronglyMeasurable (fun s => Real.sqrt (A s ^ 2)) (volume.restrict (Set.Ioi z))
    exact (hint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hB_int : MeasureTheory.IntegrableOn (fun s => B s ^ 2) (Set.Ioi z) :=
    hint.congr_fun (fun s _ => (hBsq s).symm) measurableSet_Ioi
  have hB_memLp : MemLp B 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hB_aesm).mpr hB_int
  -- the radial weight
  have hWlam_aesm : AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam
      (volume.restrict (Set.Ioi z)) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi z))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_)
      measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  have hWlam_sq_int : MeasureTheory.IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi z) := by
    simpa only [Work.FTS.GalBasis.cc.Wlam] using
      Work.Elliptic.psi_sq_integrable_aux.mono_set (fun x hx => by
        simp only [Set.mem_Ioi] at hx ⊢
        linarith)
  have hWlam_memLp : MemLp Work.FTS.GalBasis.cc.Wlam 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hWlam_aesm).mpr hWlam_sq_int
  -- the sharp weight bound
  have hWlam_sq_le : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2 ≤ 1 / z := by
    have h1 : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2
        ≤ ∫ s in Set.Ioi z, s ^ (-2 : ℝ) :=
      MeasureTheory.setIntegral_mono_of_nonneg (fun s _ => sq_nonneg _)
        (fun s hs => Wlam_sq_le_rpow s (lt_trans hz hs))
        (integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hz)
    have h2 : ∫ s in Set.Ioi z, s ^ (-2 : ℝ) = 1 / z := by
      rw [integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hz,
        show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      ring
    linarith
  -- Cauchy–Schwarz for the two measurable factors
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
    (u := Work.FTS.GalBasis.cc.Wlam) (v := B) (s := Set.Ioi z) hWlam_memLp hB_memLp
  have hprod : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * B s
      = |∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * B s| := by
    rw [abs_of_nonneg]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt (lt_trans hz hs))) (hBnn s)
  calc ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      = ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * B s := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hBeq] with s hs
        rw [hs]
    _ = |∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * B s| := hprod
    _ ≤ Real.sqrt (∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2)
          * Real.sqrt (∫ s in Set.Ioi z, B s ^ 2) := hcs
    _ = Real.sqrt (∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2)
          * Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) := by
        rw [MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun s => hBsq s)]
    _ ≤ Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hWlam_sq_le) (Real.sqrt_nonneg _)

/-! ## The integrated bound on the tail `(z,∞)` -/

/-- **The main estimate.**  For `f` with `HkMem α 0 f` and `z > 0`,
`∫_{s>z} |L₁₂-density f s| ds ≤ BK · √(1/z) · √(HkSq α 0 f)`. -/
lemma tail_abs_L12dens_le (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 0 f)
    {z : ℝ} (hz : 0 < z) :
    ∫ s in Set.Ioi z, |Work.Construction.L12dens f s|
      ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / z)
        * Real.sqrt (Work.Spaces.HkSq α 0 f) := by
  -- the angular marginal `H` and its square root `A`
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 f s θ
  have hAnn : ∀ s, 0 ≤ A s := fun s => Real.sqrt_nonneg _
  -- integrability of `H` on `[0,∞)` and hence on `(z,∞)`
  have hH_int_Iz : MeasureTheory.IntegrableOn H Work.Spaces.Iz := by
    simpa only [hH] using hmem.2
  have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := by
    intro x hx
    simp only [Work.Spaces.Iz, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith
  have hH_int : MeasureTheory.IntegrableOn H (Set.Ioi z) := hH_int_Iz.mono_set hsub
  have hA2_int : MeasureTheory.IntegrableOn (fun s => A s ^ 2) (Set.Ioi z) := by
    refine hH_int.congr_fun (fun s _ => ?_) measurableSet_Ioi
    rw [hA]
    exact (Real.sq_sqrt (hHnn s)).symm
  -- `∫_{s>z} A² ≤ HkSq α 0 f`
  have hA2_le : ∫ s in Set.Ioi z, A s ^ 2 ≤ Work.Spaces.HkSq α 0 f := by
    have h1 : ∫ s in Set.Ioi z, A s ^ 2 = ∫ s in Set.Ioi z, H s :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s _ => by
        rw [hA]
        exact Real.sq_sqrt (hHnn s)
    have h2 : ∫ s in Set.Ioi z, H s ≤ ∫ s in Work.Spaces.Iz, H s :=
      MeasureTheory.setIntegral_mono_set hH_int_Iz (Filter.Eventually.of_forall hHnn)
        (Filter.Eventually.of_forall fun x hx => hsub hx)
    have h3 : ∫ s in Work.Spaces.Iz, H s = Work.Spaces.HkSq α 0 f := by
      rw [hH]
      rfl
    linarith
  -- Cauchy–Schwarz in the radial variable
  have hCS : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      ≤ Real.sqrt (1 / z) * Real.sqrt (Work.Spaces.HkSq α 0 f) :=
    le_trans (Wlam_mul_le_sqrt hz (fun s _ => hAnn s) hA2_int)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hA2_le) (Real.sqrt_nonneg _))
  -- the pointwise bound on the density
  have hbd : ∀ s ∈ Set.Ioi z, |Work.Construction.L12dens f s|
      ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * A s) := by
    intro s hs
    have hs0 : 0 < s := lt_trans hz hs
    have hb := abs_L12dens_le_zero α f hs0 (hmem.1 s (hsub hs))
    simpa only [hA, hH] using hb
  -- the majorant is integrable (AM–GM) and the bound passes to the integral
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi z)) := by
    rw [hA]
    exact (hH_int.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hWlam_aesm : AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam
      (volume.restrict (Set.Ioi z)) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi z))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_)
      measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  have hWlam_sq_int : MeasureTheory.IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi z) := by
    simpa only [Work.FTS.GalBasis.cc.Wlam] using
      Work.Elliptic.psi_sq_integrable_aux.mono_set (fun x hx => by
        simp only [Set.mem_Ioi] at hx ⊢
        linarith)
  have hAMGM : ∀ s ∈ Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      ≤ Work.FTS.GalBasis.cc.Wlam s ^ 2 + A s ^ 2 := by
    intro s _
    nlinarith [sq_nonneg (Work.FTS.GalBasis.cc.Wlam s - A s)]
  have hsum_int : MeasureTheory.IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2 + A s ^ 2) (Set.Ioi z) :=
    hWlam_sq_int.add hA2_int
  have hdom_int : MeasureTheory.IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s))
      (Set.Ioi z) := by
    refine MeasureTheory.Integrable.mono' (hsum_int.const_mul Work.FTS.GalBasis.cc.BK) ?_ ?_
    · exact (hWlam_aesm.mul hA_aesm).const_mul Work.FTS.GalBasis.cc.BK
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hnn : 0 ≤ Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) :=
        mul_nonneg Work.FTS.GalBasis.cc.BK_nonneg
          (mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt (lt_trans hz hs)))
            (hAnn s))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (hAMGM s hs) Work.FTS.GalBasis.cc.BK_nonneg
  have h2 : ∫ s in Set.Ioi z, |Work.Construction.L12dens f s|
      ≤ ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun s => abs_nonneg _) hdom_int ?_
    show ∀ᵐ s ∂(volume.restrict (Set.Ioi z)),
      |Work.Construction.L12dens f s|
        ≤ Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun s hs => ?_
    calc |Work.Construction.L12dens f s|
        ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * A s) := hbd s hs
      _ = Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := by ring
  have h3 : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s)
      = Work.FTS.GalBasis.cc.BK * ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s :=
    MeasureTheory.integral_const_mul Work.FTS.GalBasis.cc.BK _
  calc ∫ s in Set.Ioi z, |Work.Construction.L12dens f s|
      ≤ ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := h2
    _ = Work.FTS.GalBasis.cc.BK * ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s := h3
    _ ≤ Work.FTS.GalBasis.cc.BK * (Real.sqrt (1 / z) * Real.sqrt (Work.Spaces.HkSq α 0 f)) :=
        mul_le_mul_of_nonneg_left hCS Work.FTS.GalBasis.cc.BK_nonneg
    _ = Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / z) * Real.sqrt (Work.Spaces.HkSq α 0 f) := by
        ring

/-! ## The theorem -/


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.rect_deriv_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Splitting the integral of a sum of four functions over a set of `ℝ × ℝ`. -/
lemma integral_rect_add4 {s : Set (ℝ × ℝ)} {f₁ f₂ f₃ f₄ : ℝ × ℝ → ℝ}
    (h₁ : IntegrableOn f₁ s) (h₂ : IntegrableOn f₂ s) (h₃ : IntegrableOn f₃ s)
    (h₄ : IntegrableOn f₄ s) :
    (∫ x in s, (f₁ x + f₂ x + f₃ x + f₄ x))
      = (∫ x in s, f₁ x) + (∫ x in s, f₂ x) + (∫ x in s, f₃ x) + (∫ x in s, f₄ x) := by
  rw [show (∫ x in s, (f₁ x + f₂ x + f₃ x + f₄ x))
      = ∫ x in s, ((f₁ + f₂ + f₃) x + f₄ x) from rfl]
  rw [integral_add ((h₁.add h₂).add h₃) h₄]
  rw [show (∫ x in s, (f₁ + f₂ + f₃) x) = ∫ x in s, ((f₁ + f₂) x + f₃ x) from rfl]
  rw [integral_add (h₁.add h₂) h₃]
  rw [show (∫ x in s, (f₁ + f₂) x) = ∫ x in s, (f₁ x + f₂ x) from rfl]
  rw [integral_add h₁ h₂]

/-- **The derivative bounds of `rect_deriv_bounds`, for an arbitrary datum.**

If `G` is `C^∞` on the open quadrant and its six second-order quantities
`∂_zG, ∂_θG, ∂_z²G, ∂_z∂_θG, ∂_θ∂_zG, ∂_θ²G` have `L²`-norms bounded by `C * M` on a
rectangle `[a',b'] × [c',d'] ⊆ Q0`, then the `L²`-norms on that rectangle of the first and
second Fréchet derivatives of `uncurry G` are bounded by `4 * C * M` and `16 * C * M`.

This is purely a `2 × 2` operator-norm computation (`eqc_opNorm_le_basis_sum₂` and
Cauchy–Schwarz `(a+b+c+d)² ≤ 4(a²+b²+c²+d²)`) followed by Fubini
(`eqc_setIntegral_rect_eq`): on `ℝ × ℝ` the operator norm of a linear functional is dominated
by the sum of its two basis values, and that of a bilinear form by the sum of the absolute
values of its four matrix entries (`norm_fderiv_fderiv_le_basis`), which are
`∂_z²G, ∂_z∂_θG, ∂_θ∂_zG, ∂_θ²G`. -/
theorem rect_deriv_bounds_aux {G : ℝ → ℝ → ℝ} {C M a' b' c' d' : ℝ}
    (hsub : Set.Icc a' b' ×ˢ Set.Icc c' d' ⊆ Work.FTS.EllipticEst.Q0)
    (hG : Work.FTS.EllipticEst.SmoothOpen G)
    (h1 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pz G z θ) ^ 2 ≤ C * M)
    (h2 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pth G z θ) ^ 2 ≤ C * M)
    (h3 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pz (Work.Spaces.pz G) z θ) ^ 2 ≤ C * M)
    (h4 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pz (Work.Spaces.pth G) z θ) ^ 2 ≤ C * M)
    (h5 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pth (Work.Spaces.pz G) z θ) ^ 2 ≤ C * M)
    (h6 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 ≤ C * M) :
    (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        ‖fderiv ℝ (Function.uncurry G) x‖ ^ 2 ≤ 4 * C * M)
      ∧ (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        ‖fderiv ℝ (fderiv ℝ (Function.uncurry G)) x‖ ^ 2 ≤ 16 * C * M) := by
  classical
  have hR2m : MeasurableSet (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
    measurableSet_Icc.prod measurableSet_Icc
  have hR2k : IsCompact (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
    isCompact_Icc.prod isCompact_Icc
  have hG2 : ContDiffOn ℝ 2 (Function.uncurry G) Work.FTS.EllipticEst.Q0 :=
    hG.of_le two_le_smoothOrder
  constructor
  · -- ## first derivative
    have hpt1 : ∀ x ∈ Set.Icc a' b' ×ˢ Set.Icc c' d',
        ‖fderiv ℝ (Function.uncurry G) x‖ ^ 2
          ≤ 2 * (Work.Spaces.pz G x.1 x.2) ^ 2
            + 2 * (Work.Spaces.pth G x.1 x.2) ^ 2 := by
      rintro ⟨z, θ⟩ hx
      have hd : DifferentiableAt ℝ (Function.uncurry G) (z, θ) :=
        (hG2.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds (hsub hx))).differentiableAt
          (by norm_num)
      have hb := Work.FTS.StrongLWP.Sobolev.eqc_opNorm_le_basis_sum
        (fderiv ℝ (Function.uncurry G) (z, θ))
      calc ‖fderiv ℝ (Function.uncurry G) (z, θ)‖ ^ 2
          ≤ (‖(fderiv ℝ (Function.uncurry G) (z, θ)) (1, 0)‖
              + ‖(fderiv ℝ (Function.uncurry G) (z, θ)) (0, 1)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ ≤ 2 * (((fderiv ℝ (Function.uncurry G) (z, θ)) (1, 0)) ^ 2
              + ((fderiv ℝ (Function.uncurry G) (z, θ)) (0, 1)) ^ 2) := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs]
            simpa only [sq_abs] using Work.FTS.StrongLWP.Sobolev.eqc_sq_add2_le
              |(fderiv ℝ (Function.uncurry G) (z, θ)) (1, 0)|
              |(fderiv ℝ (Function.uncurry G) (z, θ)) (0, 1)|
        _ = 2 * (Work.Spaces.pz G z θ) ^ 2 + 2 * (Work.Spaces.pth G z θ) ^ 2 := by
            rw [← Work.Spaces.pz_eq_fderiv hd, ← Work.Spaces.pth_eq_fderiv hd]
            ring
    have hpzint : IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pz G x.1 x.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      ContinuousOn.integrableOn_compact hR2k (((hG.pz).continuousOn.mono hsub).pow 2)
    have hpthint : IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pth G x.1 x.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      ContinuousOn.integrableOn_compact hR2k (((hG.pth).continuousOn.mono hsub).pow 2)
    have hInt : IntegrableOn (fun x : ℝ × ℝ =>
        2 * (Work.Spaces.pz G x.1 x.2) ^ 2 + 2 * (Work.Spaces.pth G x.1 x.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      (hpzint.const_mul 2).add (hpthint.const_mul 2)
    have hI1 : ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        (Work.Spaces.pz G x.1 x.2) ^ 2 ≤ C * M := by
      rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq hpzint]
      exact h1
    have hI2 : ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        (Work.Spaces.pth G x.1 x.2) ^ 2 ≤ C * M := by
      rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq hpthint]
      exact h2
    calc ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d', ‖fderiv ℝ (Function.uncurry G) x‖ ^ 2
        ≤ ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
            (2 * (Work.Spaces.pz G x.1 x.2) ^ 2 + 2 * (Work.Spaces.pth G x.1 x.2) ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) hInt
            (ae_restrict_of_forall_mem hR2m hpt1)
      _ = 2 * (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d', (Work.Spaces.pz G x.1 x.2) ^ 2)
            + 2 * (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d', (Work.Spaces.pth G x.1 x.2) ^ 2) := by
          rw [integral_add (hpzint.const_mul 2) (hpthint.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 4 * C * M := by nlinarith [hI1, hI2]
  · -- ## second derivative
    have hpt2 : ∀ x ∈ Set.Icc a' b' ×ˢ Set.Icc c' d',
        ‖fderiv ℝ (fderiv ℝ (Function.uncurry G)) x‖ ^ 2
          ≤ 4 * ((Work.Spaces.pz (Work.Spaces.pz G) x.1 x.2) ^ 2
              + (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pth G) x.1 x.2) ^ 2) := by
      rintro ⟨z, θ⟩ hx
      have hb : ‖fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)‖ ≤
          |Work.Spaces.pz (Work.Spaces.pz G) z θ| + |Work.Spaces.pz (Work.Spaces.pth G) z θ|
            + |Work.Spaces.pth (Work.Spaces.pz G) z θ|
            + |Work.Spaces.pth (Work.Spaces.pth G) z θ| := by
        simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pthIter_succ,
          Work.Spaces.pthIter_zero] using
          norm_fderiv_fderiv_le_basis (G := G) Work.FTS.EllipticEst.isOpen_Q0 hG2 (hsub hx)
      calc ‖fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)‖ ^ 2
          ≤ (|Work.Spaces.pz (Work.Spaces.pz G) z θ|
              + |Work.Spaces.pz (Work.Spaces.pth G) z θ|
              + |Work.Spaces.pth (Work.Spaces.pz G) z θ|
              + |Work.Spaces.pth (Work.Spaces.pth G) z θ|) ^ 2 :=
            pow_le_pow_left₀
              (norm_nonneg (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ))) hb 2
        _ ≤ 4 * ((Work.Spaces.pz (Work.Spaces.pz G) z θ) ^ 2
              + (Work.Spaces.pz (Work.Spaces.pth G) z θ) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pz G) z θ) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2) := by
            simpa only [sq_abs] using Work.FTS.StrongLWP.Sobolev.eqc_sq_add4_le
              |Work.Spaces.pz (Work.Spaces.pz G) z θ| |Work.Spaces.pz (Work.Spaces.pth G) z θ|
              |Work.Spaces.pth (Work.Spaces.pz G) z θ| |Work.Spaces.pth (Work.Spaces.pth G) z θ|
    have he1 : IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz G) x.1 x.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      ContinuousOn.integrableOn_compact hR2k ((((hG.pz).pz).continuousOn.mono hsub).pow 2)
    have he2 : IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      ContinuousOn.integrableOn_compact hR2k ((((hG.pth).pz).continuousOn.mono hsub).pow 2)
    have he3 : IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      ContinuousOn.integrableOn_compact hR2k ((((hG.pz).pth).continuousOn.mono hsub).pow 2)
    have he4 : IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth G) x.1 x.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      ContinuousOn.integrableOn_compact hR2k ((((hG.pth).pth).continuousOn.mono hsub).pow 2)
    have hInt2 : IntegrableOn (fun x : ℝ × ℝ =>
        4 * ((Work.Spaces.pz (Work.Spaces.pz G) x.1 x.2) ^ 2
              + (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pth G) x.1 x.2) ^ 2))
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      (((he1.add he2).add he3).add he4).const_mul 4
    have hg1 : ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        (Work.Spaces.pz (Work.Spaces.pz G) x.1 x.2) ^ 2 ≤ C * M := by
      rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq he1]
      exact h3
    have hg2 : ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2 ≤ C * M := by
      rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq he2]
      exact h4
    have hg3 : ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2 ≤ C * M := by
      rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq he3]
      exact h5
    have hg4 : ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        (Work.Spaces.pth (Work.Spaces.pth G) x.1 x.2) ^ 2 ≤ C * M := by
      rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq he4]
      exact h6
    calc ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
            ‖fderiv ℝ (fderiv ℝ (Function.uncurry G)) x‖ ^ 2
        ≤ ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
            4 * ((Work.Spaces.pz (Work.Spaces.pz G) x.1 x.2) ^ 2
              + (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pth G) x.1 x.2) ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) hInt2
            (ae_restrict_of_forall_mem hR2m hpt2)
      _ = 4 * ((∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
              (Work.Spaces.pz (Work.Spaces.pz G) x.1 x.2) ^ 2)
            + (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
              (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2)
            + (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
              (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2)
            + (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
              (Work.Spaces.pth (Work.Spaces.pth G) x.1 x.2) ^ 2)) := by
          rw [integral_const_mul, integral_rect_add4 he1 he2 he3 he4]
      _ ≤ 16 * C * M := by nlinarith [hg1, hg2, hg3, hg4]

theorem rect_deriv_bounds {F : ℝ → ℝ → ℝ} {α C : ℝ} {a' b' c' d' : ℝ} (j i : ℕ)
    (hsub : Set.Icc a' b' ×ˢ Set.Icc c' d' ⊆ Work.FTS.EllipticEst.Q0)
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (h1 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F)
    (h2 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F)
    (h3 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F)
    (h4 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F)
    (h5 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F)
    (h6 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) :
    (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed j i F)) x‖ ^ 2
          ≤ 4 * C * Work.Spaces.HkSq α 6 F)
      ∧ (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        ‖fderiv ℝ (fderiv ℝ (Function.uncurry (Work.Spaces.mixed j i F))) x‖ ^ 2
          ≤ 16 * C * Work.Spaces.HkSq α 6 F) :=
  rect_deriv_bounds_aux (G := Work.Spaces.mixed j i F) (M := Work.Spaces.HkSq α 6 F)
    hsub (hFsm.mixed j i) h1 h2 h3 h4 h5 h6

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.R.WipLSelf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `⟨𝓛u, u⟩_{w²σ} = ½ ⟨u,u⟩_{w²σ}` from the `D_z`-IBP hypotheses

The paper's identity `𝓛u · u · w² = (u w)² + ½ z ∂_z((u w)²)` integrates (against the
angular weight `σ`) to

  `wip (w²σ) (𝓛u) u = ½ ∫∫ u² w² σ`,

i.e. `𝓛` is self-adjoint for the weighted `L²` pairing.  The file
`Submission/Work/Coercivity/wip_L_self.lean` proves this from the *analytic* hypothesis
package `IBP u` (boundary limits assumed), and
`Submission/Work/FTS/CoercivityFix/Coer1/zIBP.lean` from `SmoothQuad` plus the boundary
limits.  Here the hypotheses are the three *integrability* assumptions
(`u²w²σ`, `(D_z u)·u·w²σ` and `u²·∂_z(z w²)·σ`) together with `SmoothOpen u`; the
boundary terms of the `z`-integration by parts are then *derived* from integrability by
`Work.FTS.StrongPersist.H6Aux.wip_Dz_ibp`.

The proof is pure algebra once the IBP is available.  Writing `ρ = w²σ` and `Φ = w²`:

* `𝓛u · u · ρ = u²ρ + (D_z u)·u·ρ - 2u²ρ/(1+z)` (pointwise, the definition of `𝓛`),
* `∫∫ (D_z u)·u·ρ = -(1/2) ∫∫ u² ∂_z(zΦ) σ` (`wip_Dz_ibp`),
* `∂_z(z Φ) = ((z-3)/(1+z)) Φ` for `z > 0`
  (`Work.FTS.EllipticEst.weight_algebra_fts`), hence *pointwise*

  `u²ρ + (1/2)(u² ∂_z(zΦ) σ - u²ρ) = u²ρ - 2u²ρ/(1+z)`,

so the three pieces combine to `(1/2)∫∫ u²ρ`.

The whole computation is lifted to the product measure `μ ⊗ ν`
(`μ = volume.restrict I_z`, `ν = volume.restrict I_θ`), where the linearity of the
integral is available unconditionally; the bridge is
`Work.Coercivity.wip_eq_integral_prod`.
-/

namespace Work.FTS.StrongPersist.H6Aux.R

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Product-measure bookkeeping -/

/-- The restriction of the plane Lebesgue measure to `I_z ×ˢ I_θ` is the product of the two
restricted measures. -/
private theorem volume_restrict_prod_loc :
    volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact (MeasureTheory.Measure.prod_restrict _ _).symm

/-- `IntegrableOn` on the quadrant is `Integrable` against the product of the two restricted
measures. -/
private theorem integrableOn_prod_iff_loc {g : ℝ → ℝ → ℝ} :
    MeasureTheory.IntegrableOn (Function.uncurry g) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ↔ MeasureTheory.Integrable (fun p : ℝ × ℝ => g p.1 p.2)
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  rw [MeasureTheory.IntegrableOn, volume_restrict_prod_loc]
  rfl

/-- Almost every point of the product measure has positive first coordinate. -/
private theorem ae_prod_pos_loc :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod
      (volume.restrict Work.Spaces.Iθ)), 0 < p.1 := by
  rw [MeasureTheory.ae_iff]
  have hset : {p : ℝ × ℝ | ¬ (0 < p.1)} = Set.Iic (0 : ℝ) ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_setOf_eq, not_lt, Set.mem_prod, Set.mem_Iic, Set.mem_univ, and_true]
  have hIz : (volume.restrict Work.Spaces.Iz) (Set.Iic (0 : ℝ)) = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iic]
    have hI : Work.Spaces.Iz ∩ Set.Iic (0 : ℝ) = {0} := by
      ext z
      simp only [Work.Spaces.Iz, Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
      · rintro rfl; exact ⟨le_refl 0, le_refl 0⟩
    rw [Set.inter_comm, hI, Real.volume_singleton]
  rw [hset, MeasureTheory.Measure.prod_prod, hIz, zero_mul]

/-- The derivative of the derived weight `z ↦ z·w z²`, in the factored form used to match the
weight `w²` itself: `∂_z(z w²) = ((z-3)/(1+z))·w²` for `z > 0`. -/
private theorem deriv_zw2 {z : ℝ} (hz : 0 < z) :
    deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z
      = (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) := by
  rw [Work.FTS.EllipticEst.weight_algebra_fts.2.2.2.1 z (ne_of_gt hz)]
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.Spaces.w]
  field_simp

/-! ## The four integrands, on the product -/

/-- `u·u·w²σ`. -/
private def pAF (u : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2)

/-- `(D_z u)·u·w²σ`. -/
private def pBF (u : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Work.Spaces.Dz u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2)

/-- `u·u·∂_z(z·w²)·σ`. -/
private def pDF (u : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  u p.1 p.2 * u p.1 p.2
    * (deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) p.1 * σ p.2)

/-- `(𝓛u)·u·w²σ`. -/
private def pLF (u : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Work.Coercivity.L u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2)

theorem WipLSelf {u : ℝ → ℝ → ℝ} {σ : ℝ → ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen u)
    (h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * (Work.Spaces.w z) ^ 2 * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ * (Work.Spaces.w z) ^ 2 * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h3 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z
        * σ θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ) (Work.Coercivity.L u) u
      = (1 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * σ θ)) := by
  set m : MeasureTheory.Measure (ℝ × ℝ) :=
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) with hm
  -- ## 0.  The weight `Φ = w²` is `C¹` on `(0,∞)`
  have hΦ : ContDiffOn ℝ 1 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have hw1 : ContDiffOn ℝ 1 (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
      show ContDiffOn ℝ 1 (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
      exact ContDiffOn.div (by fun_prop) (by fun_prop)
        (fun z hz => pow_ne_zero 2 (ne_of_gt (show (0 : ℝ) < z from hz)))
    exact hw1.pow 2
  -- ## 1.  The three integrands in `wip`-shape
  have h1w : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * ((Work.Spaces.w z) ^ 2 * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h1.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have h2w : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * σ θ))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h2.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have h3w : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * (deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h3.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  -- ## 2.  The `z`-integration by parts, from `wip_Dz_ibp`
  have hDz : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ)
        (Work.Spaces.Dz u) u
      = -(1 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ) :=
    Work.FTS.StrongPersist.H6Aux.wip_Dz_ibp (h := u)
      (Φ := fun z : ℝ => (Work.Spaces.w z) ^ 2) (σ := σ) hs hΦ h1 h2 h3
  -- ## 3.  Integrability of the four product integrands
  have hAFint : MeasureTheory.Integrable (pAF u σ) m := by
    rw [hm]
    exact integrableOn_prod_iff_loc.mp h1w
  have hBFint : MeasureTheory.Integrable (pBF u σ) m := by
    rw [hm]
    exact integrableOn_prod_iff_loc.mp h2w
  have hDFint : MeasureTheory.Integrable (pDF u σ) m := by
    rw [hm]
    exact integrableOn_prod_iff_loc.mp h3w
  -- the `2u²ρ/(1+z)` piece, dominated by `2u²ρ` because `1+z ≥ 1` on `Iz`
  have hCint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ =>
        2 * (u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2)) / (1 + p.1)) m := by
    have hbase : MeasureTheory.Integrable
        (fun p : ℝ × ℝ =>
          2 * (u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2))) m :=
      hAFint.const_mul 2
    have hg : AEStronglyMeasurable (fun p : ℝ × ℝ => (1 : ℝ) / (1 + p.1)) m :=
      ((((measurable_const : Measurable fun _ : ℝ => (1 : ℝ)).div
          (measurable_const.add measurable_id))).comp measurable_fst).aestronglyMeasurable
    have hbdd : ∀ᵐ p ∂m, ‖(1 : ℝ) / (1 + p.1)‖ ≤ (1 : ℝ) := by
      filter_upwards [ae_prod_pos_loc] with p hp
      have hz : (0 : ℝ) ≤ p.1 := le_of_lt hp
      have h1p : (0 : ℝ) < 1 + p.1 := by linarith
      rw [Real.norm_eq_abs, abs_div, abs_of_pos h1p, abs_one, div_le_one h1p]
      linarith
    refine (hbase.mul_bdd hg hbdd).congr ?_
    filter_upwards with p
    rw [div_eq_mul_inv]
    ring
  -- `𝓛u·u·ρ` is integrable: it is `u²ρ + (D_z u)uρ - 2u²ρ/(1+z)`
  have hLFint : MeasureTheory.Integrable (pLF u σ) m := by
    have hsum : MeasureTheory.Integrable
        (fun p : ℝ × ℝ =>
          u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2)
            + Work.Spaces.Dz u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2)
            - 2 * (u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2))
                / (1 + p.1)) m :=
      (hAFint.add hBFint).sub hCint
    refine hsum.congr ?_
    filter_upwards with p
    simp only [pLF, Work.Coercivity.L, Work.Spaces.Dz]
    ring
  have hHalfint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (1 / 2) * (pDF u σ p - pAF u σ p)) m :=
    (hDFint.sub hAFint).const_mul (1 / 2)
  -- ## 4.  The `wip`-to-product conversions
  have hwipA : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ) u u
      = ∫ p, pAF u σ p ∂m := by
    rw [Work.Coercivity.wip_eq_integral_prod (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ) u u h1w]
    rw [hm]
    simp only [pAF]
  have hwipB : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ)
        (Work.Spaces.Dz u) u = ∫ p, pBF u σ p ∂m := by
    rw [Work.Coercivity.wip_eq_integral_prod (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ)
      (Work.Spaces.Dz u) u h2w]
    rw [hm]
    simp only [pBF]
  have hDconv : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        u z θ ^ 2 * deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ)
      = ∫ p, pDF u σ p ∂m := by
    have hstep1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ)
        = Work.Coercivity.wip
            (fun z θ => deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ) u u := by
      simp only [Work.Coercivity.wip]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      ring
    have hstep2 : Work.Coercivity.wip
          (fun z θ => deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ) u u
        = ∫ p, pDF u σ p ∂m := by
      rw [Work.Coercivity.wip_eq_integral_prod
        (fun z θ => deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ) u u h3w]
      rw [hm]
      simp only [pDF]
    exact hstep1.trans hstep2
  have hwipL : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ)
        (Work.Coercivity.L u) u = ∫ p, pLF u σ p ∂m := by
    rw [Work.Coercivity.wip_eq_integral_prod (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ)
      (Work.Coercivity.L u) u
      ((integrableOn_prod_iff_loc
        (g := fun z θ => Work.Coercivity.L u z θ * u z θ * ((Work.Spaces.w z) ^ 2 * σ θ))).mpr
        hLFint)]
    rw [hm]
    simp only [pLF]
  -- ## 5.  The `D_z`-pairing, in product form
  have hBF_eq : ∫ p, pBF u σ p ∂m = -(1 / 2) * ∫ p, pDF u σ p ∂m := by
    rw [← hwipB, hDz, hDconv]
  -- ## 6.  The pointwise identity and the split of the integral
  have hid : pLF u σ =ᵐ[m] (fun p : ℝ × ℝ =>
      pAF u σ p + pBF u σ p + (1 / 2) * (pDF u σ p - pAF u σ p)) := by
    filter_upwards [ae_prod_pos_loc] with p hp
    have hder := deriv_zw2 hp
    have h1z : (1 : ℝ) + p.1 ≠ 0 := by linarith
    simp only [pLF, pAF, pBF, pDF, Work.Coercivity.L, Work.Spaces.Dz]
    rw [hder]
    field_simp
    ring
  have hstep : ∫ p, pLF u σ p ∂m
      = (∫ p, pAF u σ p ∂m) + (∫ p, pBF u σ p ∂m)
        + (1 / 2) * ((∫ p, pDF u σ p ∂m) - (∫ p, pAF u σ p ∂m)) := by
    have e0 : ∫ p, pLF u σ p ∂m
        = ∫ p, pAF u σ p + pBF u σ p + (1 / 2) * (pDF u σ p - pAF u σ p) ∂m :=
      MeasureTheory.integral_congr_ae hid
    have e1 : ∫ p, pAF u σ p + pBF u σ p + (1 / 2) * (pDF u σ p - pAF u σ p) ∂m
        = (∫ p, pAF u σ p + pBF u σ p ∂m)
          + (∫ p, (1 / 2) * (pDF u σ p - pAF u σ p) ∂m) :=
      MeasureTheory.integral_add (hAFint.add hBFint) hHalfint
    have e2 : ∫ p, pAF u σ p + pBF u σ p ∂m
        = (∫ p, pAF u σ p ∂m) + (∫ p, pBF u σ p ∂m) :=
      MeasureTheory.integral_add hAFint hBFint
    have e3 : ∫ p, (1 / 2) * (pDF u σ p - pAF u σ p) ∂m
        = (1 / 2) * ∫ p, pDF u σ p - pAF u σ p ∂m :=
      MeasureTheory.integral_const_mul (1 / 2) _
    have e4 : ∫ p, pDF u σ p - pAF u σ p ∂m
        = (∫ p, pDF u σ p ∂m) - (∫ p, pAF u σ p ∂m) :=
      MeasureTheory.integral_sub hDFint hAFint
    rw [e0, e1, e2, e3, e4]
  -- ## 7.  Assembly
  have hkey : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ)
        (Work.Coercivity.L u) u
      = (1 / 2) * Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ) u u := by
    rw [hwipL, hstep, hBF_eq, ← hwipA]
    ring
  have hR : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ) u u
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * σ θ) := by
    simp only [Work.Coercivity.wip]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    ring
  rw [hkey, hR]

end

end Work.FTS.StrongPersist.H6Aux.R
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.thetaAngIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Gen

open scoped Real Topology
open MeasureTheory Set Filter

theorem thetaAngIntegrable (α : ℝ) (hα : α ∈ Set.Ioc 0 1) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f)
    (j : ℕ) (hj : j ≤ 5) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter j f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  have hαpos : 0 < α := hα.1
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- (1) the weighted mixed slot `(D_z^j D_θ f · W)²` is integrable on `Iθ`
  have hmix : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableOn_mixedSummand α 6 hsm hmem 1 j le_rfl
      (by omega) hzI
  -- (2) divide by `(w z)² ≠ 0`; the weight identity is valid on all of `Iθ`
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    rw [Work.Spaces.w]; positivity
  have hB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.mixed j 1 f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
    (hmix.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr
      (MeasureTheory.ae_restrict_of_forall_mem hIθ (fun θ hθ => by
        beta_reduce
        have hsq := (Work.FTS.H2.Whz_Wm_sq α hαpos z θ hθ).2
        rw [Work.FTS.H2.Wm_eq] at hsq
        rw [mul_pow, hsq]
        rw [show (((Work.Spaces.w z) ^ 2)⁻¹) * ((Work.Spaces.mixed j 1 f z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
            = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2)
                * ((Work.Spaces.mixed j 1 f z θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) from by ring,
          inv_mul_cancel₀ hw2, one_mul]))
  -- (3) on the interior, `sin(2θ) · ∂_θ(D_z^j f) = D_z^j D_θ f`
  refine hB.congr ?_
  rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  beta_reduce
  have hcomm := Work.FTS.EllipticEst.SmoothOpen.DthIter_DzIter_eq_mixed hsm j 1 hz hθ
  have hsin : Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter j f) z θ
      = Work.Spaces.mixed j 1 f z θ := by
    have h := hcomm
    rw [show Work.Spaces.DthIter 1 (Work.Spaces.DzIter j f)
        = Work.Spaces.Dth (Work.Spaces.DzIter j f) from rfl] at h
    simpa only [Work.Spaces.Dth] using h
  rw [hsin]

end Work.FTS.StrongPersist.H6Pair6Aux.T6Gen
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.pure_slice_agmon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

set_option linter.unusedVariables false

/-! ## The radial restricted measure -/

/-- `volume.restrict Iz = volume.restrict (0,∞)`: the two restricted measures differ only at
the null point `0`.  (`Iz = [0,∞)`.) -/
theorem restrict_Iz_eq_Ioi :
    (volume.restrict Work.Spaces.Iz : Measure ℝ) = volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm

/-! ## Extracting a single radial slot from the level-7 integrability hypothesis -/

/-- **A single radial slot of `HkIntegrand`.**  If the level-`7` weighted integrand based at a
fixed interior angle `θ` is integrable on `Iz`, then so is every plain radial slot
`(D_z^i f · θ)² w²` with `i ≤ 7`.  (The integrand being a finite sum of squares, each
summand is dominated by the sum; the only point to be careful about is that the angular
normalisation `sin(2θ)^{η/2}` is a *nonzero* constant, and that the slot is measurable —
the total is integrable, so it is a.e. strongly measurable, but the slot itself only needs
continuity on the open half line, the difference at `z = 0` being null.) -/
theorem integrableOn_dzIter_sq_w_sq {α : ℝ} {f : ℝ → ℝ → ℝ} {θ : ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hInt : IntegrableOn (fun s => Work.Spaces.HkIntegrand α 7 f s θ) Work.Spaces.Iz)
    (i : ℕ) (hi : i ≤ 7) :
    IntegrableOn (fun s => (Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iz := by
  -- the angular normalisation `c = sin(2θ)^{η/2}` is a positive (hence nonzero) constant
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  set c : ℝ := Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) with hcdef
  have hcpos : 0 < c := Real.rpow_pos_of_pos hsin _
  have hcne : c ≠ 0 := ne_of_gt hcpos
  -- the angular weight `w · c⁻¹` is continuous on the open half line
  have hwcont : ContinuousOn (fun s : ℝ => Work.Spaces.w s / c) (Set.Ioi 0) := by
    refine ContinuousOn.div_const ?_ c
    change ContinuousOn (fun s : ℝ => (1 + s) ^ 2 / s ^ 2) (Set.Ioi 0)
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun s hs => pow_ne_zero 2 (ne_of_gt hs))
  -- the `i`-th summand of the first (plain radial) family is a.e. strongly measurable
  have haesm : AEStronglyMeasurable
      (fun s : ℝ => (Work.Spaces.DzIter i f s θ * (Work.Spaces.w s / c)) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    rw [restrict_Iz_eq_Ioi]
    exact ((((hF.DzIter i).curry_z hθ).continuousOn).mul hwcont).pow 2 |>.aestronglyMeasurable
      measurableSet_Ioi
  -- it is dominated by the (integrable) level-7 integrand
  have hIntSlot : IntegrableOn
      (fun s : ℝ => (Work.Spaces.DzIter i f s θ * (Work.Spaces.w s / c)) ^ 2)
      Work.Spaces.Iz :=
    hInt.mono' haesm (Eventually.of_forall fun s => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_z α 7 f s θ i hi)
  -- multiply by the nonzero constant `c²` to obtain the slot with weight `w²`
  have h1 : IntegrableOn
      (fun s : ℝ => c ^ 2 * (Work.Spaces.DzIter i f s θ * (Work.Spaces.w s / c)) ^ 2)
      Work.Spaces.Iz := hIntSlot.const_mul (c ^ 2)
  exact IntegrableOn.congr_fun h1 (fun x _ => by
    show c ^ 2 * (Work.Spaces.DzIter i f x θ * (Work.Spaces.w x / c)) ^ 2
        = (Work.Spaces.DzIter i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2
    field_simp) measurableSet_Ici

/-! ## The target -/

theorem pure_slice_agmon : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (θ : ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → θ ∈ Set.Ioo 0 (Real.pi / 2) →
    MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 7 f s θ) Work.Spaces.Iz →
    ∀ (j : ℕ), j ≤ 6 → ∀ z : ℝ, 0 < z →
      (Work.Spaces.DzIter j f z θ) ^ 2
        ≤ 2 * ∫ s in Work.Spaces.Iz, (Work.Spaces.DzIter (j + 1) f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
  intro α f θ hα hα1 hF hθ hInt j hj z hz
  -- the two window integrals of `zslice6_hardy` agree with the two plain radial slots
  have hid : (fun x : ℝ => (x * Work.Spaces.pz (Work.Spaces.DzIter j f) x θ * Work.Spaces.w x) ^ 2)
      = fun x : ℝ => (Work.Spaces.DzIter (j + 1) f x θ) ^ 2 * (Work.Spaces.w x) ^ 2 := by
    funext x
    rw [show x * Work.Spaces.pz (Work.Spaces.DzIter j f) x θ
        = Work.Spaces.DzIter (j + 1) f x θ from rfl, mul_pow]
  -- the windowed radial Hardy inequality at the fixed angle `θ`
  have hmain := Work.FTS.StrongPersist.N6Trans.SixAux.zslice6_hardy
    (h := fun x => Work.Spaces.DzIter j f x θ)
    (h' := fun x => Work.Spaces.pz (Work.Spaces.DzIter j f) x θ)
    hz (fun x hx => hF.hasDerivAt_slice_DzIter j hθ hx)
    (((hF.DzIter j).curry_z hθ).continuousOn)
    ((((hF.DzIter j).pz).curry_z hθ).continuousOn)
    (integrableOn_dzIter_sq_w_sq hF hθ hInt j (by omega))
    (by rw [hid]; exact integrableOn_dzIter_sq_w_sq hF hθ hInt (j + 1) (by omega))
  rw [hid] at hmain
  simpa using hmain

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_sep_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Aux

theorem HkIntegrand_sep_le {α : ℝ} {C : ℝ → ℝ} {B : ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 3 (fun z' θ' => C θ' * B z') z θ
      ≤ ((C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + ∑ i ∈ Finset.range 4,
              (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
        * (∑ q ∈ Finset.range 4,
            (Work.Spaces.DzIter q (fun z' _ => B z') z 0) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  -- ### Separation of variables for the pure `D_z`- and the mixed derivatives
  have hDz : ∀ i : ℕ, Work.Spaces.DzIter i (fun z' θ' => C θ' * B z') z θ
      = C θ * (Work.Spaces.OpZ^[i] B) z := by
    intro i
    have h := Work.FTS.Nonlinear.Pieces.RNP.row15aux.mixedSepDecomp i 0 C B z θ
    rw [Work.Spaces.mixed_zero_right] at h
    simpa using h
  have hMx : ∀ j i : ℕ, Work.Spaces.mixed j i (fun z' θ' => C θ' * B z') z θ
      = (Work.Spaces.dthU^[i] C) θ * (Work.Spaces.OpZ^[j] B) z := by
    intro j i
    simpa using Work.FTS.Nonlinear.Pieces.RNP.row15aux.mixedSepDecomp j i C B z θ
  -- the radial factor of the right-hand side is `OpZ^[q] B z`, independently of `θ`
  have hDzB : ∀ q : ℕ, Work.Spaces.DzIter q (fun z' _ => B z') z 0
      = (Work.Spaces.OpZ^[q] B) z := by
    intro q
    rw [← congrFun (Work.Spaces.sliceZ_DzIter q (fun z' _ => B z') 0) z]
  -- ### Unfold the integrand and normalise `range (3+1) = range 4`
  rw [Work.Spaces.HkIntegrand]
  simp only [hDz, hMx, hDzB]
  rw [show (3:ℕ) + 1 = 4 from rfl]
  -- ### The angular variable and the two weight identities
  set s : ℝ := Real.sin (2 * θ) with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Work.FTS.LocData.sin_two_nonneg hθ
  have hWt : Work.Spaces.Wt α z θ = Work.Spaces.w z * s ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, ← hsdef]
  have hgamma : ∀ i : ℕ, 0 ≤ (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
      * s ^ (-(Work.Spaces.gam α)) else 0) := by
    intro i
    split_ifs with h
    · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    · exact le_refl 0
  have hbq : ∀ q : ℕ, 0 ≤ ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    fun q => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- ### The pure `D_z`-summands reproduce the first term of the right-hand side exactly
  have hP : (∑ i ∈ Finset.range 4,
        (C θ * (Work.Spaces.OpZ^[i] B) z * (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2))) ^ 2)
      = C θ ^ 2 * s ^ (-(Work.Spaces.eta))
        * (∑ q ∈ Finset.range 4, ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show C θ * (Work.Spaces.OpZ^[i] B) z * (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2))
        = (Work.Spaces.OpZ^[i] B) z * C θ * (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2))
        by ring,
      Work.FTS.LocData.sep_sq1 ((Work.Spaces.OpZ^[i] B) z) (C θ) (Work.Spaces.w z) s
        (Work.Spaces.eta) hs0]
    ring
  rw [hP]
  -- ### The mixed summands are dominated by the product of the two sums
  have hQ : (∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
        (if 1 ≤ i ∧ i + j ≤ 3
          then (Work.Spaces.dthU^[i] C θ * (Work.Spaces.OpZ^[j] B) z
            * Work.Spaces.Wt α z θ) ^ 2
          else 0))
      ≤ (∑ i ∈ Finset.range 4, (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
            * s ^ (-(Work.Spaces.gam α)) else 0))
        * (∑ q ∈ Finset.range 4, ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    have hQ1 : (∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
          (if 1 ≤ i ∧ i + j ≤ 3
            then (Work.Spaces.dthU^[i] C θ * (Work.Spaces.OpZ^[j] B) z
              * Work.Spaces.Wt α z θ) ^ 2
            else 0))
        = ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
            (if 1 ≤ i ∧ i + j ≤ 3
              then (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
                  * s ^ (-(Work.Spaces.gam α)) else 0)
                * (((Work.Spaces.OpZ^[j] B) z) ^ 2 * (Work.Spaces.w z) ^ 2)
              else 0) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      by_cases h : 1 ≤ i ∧ i + j ≤ 3
      · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h.1, hWt]
        rw [show Work.Spaces.dthU^[i] C θ * (Work.Spaces.OpZ^[j] B) z
              * (Work.Spaces.w z * s ^ (-(Work.Spaces.gam α / 2)))
            = (Work.Spaces.OpZ^[j] B) z * (Work.Spaces.dthU^[i] C θ)
              * (Work.Spaces.w z * s ^ (-(Work.Spaces.gam α / 2))) by ring,
          Work.FTS.LocData.sep_sq2 ((Work.Spaces.OpZ^[j] B) z) (Work.Spaces.dthU^[i] C θ)
            (Work.Spaces.w z) s (Work.Spaces.gam α) hs0]
        ring
      · rw [ite_eq_right h, ite_eq_right h]
    calc (∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
          (if 1 ≤ i ∧ i + j ≤ 3
            then (Work.Spaces.dthU^[i] C θ * (Work.Spaces.OpZ^[j] B) z
              * Work.Spaces.Wt α z θ) ^ 2
            else 0))
        = _ := hQ1
      _ ≤ ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
            ((if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
                * s ^ (-(Work.Spaces.gam α)) else 0)
              * (((Work.Spaces.OpZ^[j] B) z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
          by_cases h : 1 ≤ i ∧ i + j ≤ 3
          · rw [ite_eq_left h]
          · rw [ite_eq_right h]
            exact mul_nonneg (hgamma i) (hbq j)
      _ = (∑ i ∈ Finset.range 4, (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
              * s ^ (-(Work.Spaces.gam α)) else 0))
            * (∑ q ∈ Finset.range 4,
                ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
  -- ### Assemble
  have hR : (C θ ^ 2 * s ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range 4, (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
            * s ^ (-(Work.Spaces.gam α)) else 0))
      * (∑ q ∈ Finset.range 4, ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = C θ ^ 2 * s ^ (-(Work.Spaces.eta))
          * (∑ q ∈ Finset.range 4, ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (∑ i ∈ Finset.range 4, (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
            * s ^ (-(Work.Spaces.gam α)) else 0))
          * (∑ q ∈ Finset.range 4, ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [add_mul]
  rw [hR]
  exact add_le_add (le_refl _) hQ

end Work.FTS.StrongPersist.L3Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The angular profile and the radial weight of the transport density -/

/-- `SwG α θ = sin(2θ)^{γ/2}`, the angular half of the `ℋ⁴`-weight on the `D_θ`-slot. -/
def SwG (α : ℝ) (θ : ℝ) : ℝ := Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2)

/-- `KG α θ = 3 K(θ) sin(2θ)^{γ/2}`, the angular profile of the transport density. -/
def KG (α : ℝ) (θ : ℝ) : ℝ := 3 * Work.Spaces.K θ * SwG α θ

/-- `Wlam3 s = s/(1+s)³ = 1/(s(1+s)w(s))`, the radial weight of the transport density. -/
def Wlam3 (s : ℝ) : ℝ := s / (1 + s) ^ 3

lemma tl12_gam_half_nonneg {α : ℝ} (hα : 0 < α) : 0 ≤ Work.Spaces.gam α / 2 := by
  rw [Work.Spaces.gam]; linarith

lemma tl12_sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Work.FTS.GalBasis.cc.sin_two_nonneg_of_mem_Iθ hθ

lemma tl12_continuous_SwG (α : ℝ) (h : 0 ≤ Work.Spaces.gam α / 2) : Continuous (SwG α) :=
  (Real.continuous_rpow_const h).comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))

lemma tl12_continuous_K : Continuous fun θ : ℝ => Work.Spaces.K θ := by
  change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
  fun_prop

lemma tl12_continuous_KG (α : ℝ) (hγ : 0 ≤ Work.Spaces.gam α / 2) : Continuous (KG α) :=
  (continuous_const.mul tl12_continuous_K).mul (tl12_continuous_SwG α hγ)

lemma tl12_SwG_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ SwG α θ :=
  Real.rpow_nonneg (tl12_sin_two_nonneg hθ) _

lemma tl12_KG_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ KG α θ :=
  mul_nonneg (mul_nonneg (by norm_num) (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθ))
    (tl12_SwG_nonneg α hθ)

lemma tl12_KG_le_nine (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hγ : 0 ≤ Work.Spaces.gam α / 2) : KG α θ ≤ 9 := by
  have hK := Work.FTS.GalBasis.cc.K_le_three_of_mem_Iθ hθ
  have hS := Real.rpow_le_one (tl12_sin_two_nonneg hθ) (Real.sin_le_one (2 * θ)) hγ
  have hK0 := Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθ
  have hS0 : 0 ≤ Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) :=
    Real.rpow_nonneg (tl12_sin_two_nonneg hθ) _
  rw [KG, SwG]
  nlinarith

lemma tl12_KG_sq_le (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hγ : 0 ≤ Work.Spaces.gam α / 2) : (KG α θ) ^ 2 ≤ 81 := by
  have h1 := tl12_KG_le_nine α hθ hγ
  have h2 := tl12_KG_nonneg α hθ
  nlinarith

lemma tl12_Wlam3_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ Wlam3 s := by
  rw [Wlam3]; exact div_nonneg hs (by positivity)

lemma tl12_Wlam3_le_Wlam {s : ℝ} (hs : 0 ≤ s) : Wlam3 s ≤ Work.FTS.GalBasis.cc.Wlam s := by
  rw [Wlam3, Work.FTS.GalBasis.cc.Wlam]
  rcases eq_or_lt_of_le hs with h | h
  · subst h; simp
  · have h1 : 0 < (1 + s) ^ 2 := by positivity
    have h2 : (1 + s) ^ 2 ≤ (1 + s) ^ 3 := by
      nlinarith [show (1 : ℝ) ≤ 1 + s by linarith]
    exact div_le_div_of_nonneg_left hs h1 h2

/-- `√(∫_θ KG²) ≤ 13` uniformly for `α > 0` (so the Cauchy–Schwarz constants below are
independent of `α`). -/
lemma tl12_sqrt_KG_sq_le (α : ℝ) (hα : 0 < α) :
    Real.sqrt (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2) ≤ 13 := by
  have hγ := tl12_gam_half_nonneg hα
  have hcont : Continuous (KG α) := tl12_continuous_KG α hγ
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hInt : IntegrableOn (fun θ => (KG α θ) ^ 2) Work.Spaces.Iθ :=
    (hcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have h81 : IntegrableOn (fun _ : ℝ => (81 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; simp)
  have hmono : ∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, (81 : ℝ) :=
    integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) h81
      (MeasureTheory.ae_restrict_of_forall_mem hIθ fun θ hθ => tl12_KG_sq_le α hθ hγ)
  have hval : ∫ _θ in Work.Spaces.Iθ, (81 : ℝ) ≤ 162 := by
    have h : ∫ θ in Work.Spaces.Iθ, (81 : ℝ) ≤ 162 := by
      rw [Work.Spaces.Iθ, MeasureTheory.setIntegral_const]
      simp
      rw [max_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
      nlinarith [Real.pi_lt_four]
    exact h
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2 :=
    integral_nonneg fun θ => sq_nonneg _
  have hsquare : (Real.sqrt (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2)) ^ 2 ≤ 162 := by
    rw [Real.sq_sqrt hnn]
    exact le_trans hmono hval
  nlinarith [Real.sqrt_nonneg (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2)]

/-! ## The pointwise identity for the transport density -/

/-- **The factorisation of the transport density** (for `s > 0` and `θ ∈ Iθ`): the
`L₁₂`-density of `Transport g` is the radial weight `Wlam3 s` times the angular pairing of
the profile `KG α` with the weighted `D_θ`-derivative of `g`. -/
lemma tl12_Transport_integrand_eq (α : ℝ) (g : ℝ → ℝ → ℝ) {s θ : ℝ} (hs : 0 < s)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.K θ * Work.Coercivity.Transport g s θ / s
      = Wlam3 s * (KG α θ * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ)) := by
  have ht0 : 0 ≤ Real.sin (2 * θ) := tl12_sin_two_nonneg hθ
  rw [Work.Coercivity.Transport, Work.Spaces.Dth, Work.Spaces.mixed_zero_left,
    Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth]
  rcases eq_or_lt_of_le ht0 with hzero | hpos
  · have hsin0 : Real.sin (2 * θ) = 0 := hzero.symm
    rw [hsin0]
    simp
  · have hsin : 0 < Real.sin (2 * θ) := hpos
    have hsum : Work.Spaces.gam α / 2 + -(Work.Spaces.gam α / 2) = 0 := by ring
    have hSW : SwG α θ * Work.Spaces.wTheta α θ = 1 := by
      rw [SwG, Work.Spaces.wTheta, ← Real.rpow_add hsin, hsum, Real.rpow_zero]
    have hW3 : Wlam3 s * Work.Spaces.w s = 1 / (s * (1 + s)) := by
      rw [Wlam3, Work.Spaces.w]
      field_simp
    have hre : Wlam3 s * (3 * Work.Spaces.K θ * SwG α θ *
          ((Real.sin (2 * θ) * Work.Spaces.pth g s θ) *
            (Work.Spaces.w s * Work.Spaces.wTheta α θ)))
        = (Wlam3 s * Work.Spaces.w s) * (SwG α θ * Work.Spaces.wTheta α θ)
            * (3 * Work.Spaces.K θ * (Real.sin (2 * θ) * Work.Spaces.pth g s θ)) := by
      ring
    rw [KG, Work.Spaces.Wt, hre, hW3, hSW]
    field_simp

/-- The `L₁₂`-density of the transport term as a constant times an angular integral. -/
lemma tl12_L12dens_Transport_eq (α : ℝ) (g : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    Work.Construction.L12dens (Work.Coercivity.Transport g) s
      = Wlam3 s * ∫ θ in Work.Spaces.Iθ,
          KG α θ * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ) := by
  have hI : Work.Spaces.Iθ = Set.Icc 0 (π / 2) := rfl
  rw [Work.Construction.L12dens, Work.FM.L12dens, hI]
  calc ∫ θ in Set.Icc 0 (π / 2), Work.Spaces.K θ * Work.Coercivity.Transport g s θ / s
      = ∫ θ in Set.Icc 0 (π / 2),
          Wlam3 s * (KG α θ * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ)) := by
        refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
        exact tl12_Transport_integrand_eq α g hs (by simpa only [hI] using hθ)
    _ = Wlam3 s * ∫ θ in Set.Icc 0 (π / 2),
          KG α θ * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ) :=
        integral_const_mul _ _

/-! ## The angular Cauchy–Schwarz step -/

lemma tl12_abs_integral_KG_le (α : ℝ) (hα : 0 < α) (g : ℝ → ℝ → ℝ) {s : ℝ}
    (hint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g s θ) Work.Spaces.Iθ) :
    |∫ θ in Work.Spaces.Iθ, KG α θ * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ)|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
  have hγ : 0 ≤ Work.Spaces.gam α / 2 := tl12_gam_half_nonneg hα
  set u : ℝ → ℝ := fun θ => KG α θ with hu
  set v : ℝ → ℝ := fun θ => Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ with hv
  set w : ℝ → ℝ := fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) with hw
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hHk_nn : ∀ θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 g s θ :=
    fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ
  have hw_nn : ∀ θ : ℝ, 0 ≤ w θ := by intro θ; rw [hw]; exact Real.sqrt_nonneg _
  have hvw : ∀ θ : ℝ, |v θ| ≤ w θ := by
    intro θ
    have h1 : (v θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
      rw [hv]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g s θ 1 0 (by norm_num) (by norm_num)
    rw [hw, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h1
  have hcont_u : Continuous u := by rw [hu]; exact tl12_continuous_KG α hγ
  have hw_aesm : AEStronglyMeasurable w (volume.restrict Work.Spaces.Iθ) := by
    rw [hw]
    exact (hint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hu2_int : IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
    (hcont_u.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hw2_int : IntegrableOn (fun θ => (w θ) ^ 2) Work.Spaces.Iθ := by
    refine hint.congr_fun (fun θ _ => ?_) hIθ
    rw [hw]; exact (Real.sq_sqrt (hHk_nn θ)).symm
  have huw_int : IntegrableOn (fun θ => |u θ| * w θ) Work.Spaces.Iθ := by
    have hmaj : IntegrableOn (fun θ => ((u θ) ^ 2 + (w θ) ^ 2) / 2) Work.Spaces.Iθ :=
      (hu2_int.add hw2_int).div_const 2
    refine hmaj.mono' ((hcont_u.abs.aestronglyMeasurable).mul hw_aesm) ?_
    filter_upwards with θ
    have h1 : 0 ≤ |u θ| := abs_nonneg _
    have h2 : 0 ≤ w θ := hw_nn θ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1]
    have key : |u θ| * w θ ≤ (|u θ| ^ 2 + (w θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|u θ| - w θ), sq_nonneg (|u θ| + w θ)]
    rw [sq_abs (u θ)] at key
    exact key
  have hMemLp_u : MemLp (fun θ => |u θ|) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => |u θ|) hcont_u.abs.aestronglyMeasurable).mpr
      (hu2_int.congr (Eventually.of_forall fun θ => (sq_abs (u θ)).symm))
  have hMemLp_w : MemLp w 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ) hw_aesm).mpr hw2_int
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt (u := fun θ => |u θ|)
    (v := w) hMemLp_u hMemLp_w
  have hsqrt_u : Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2) := by
    congr 1
    simp only [hu]
    exact integral_congr_ae (Eventually.of_forall fun θ => sq_abs (KG α θ))
  have hsqrt_w : Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    rw [hw]; exact Real.sq_sqrt (hHk_nn θ)
  have h1 : |∫ θ in Work.Spaces.Iθ, u θ * v θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
        (f := fun θ => u θ * v θ))
  have h2 : ∫ θ in Work.Spaces.Iθ, |u θ * v θ| ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _) huw_int
      (Eventually.of_forall fun θ => ?_)
    show |u θ * v θ| ≤ |u θ| * w θ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hvw θ) (abs_nonneg _)
  have h3 : ∫ θ in Work.Spaces.Iθ, |u θ| * w θ
      = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := by
    rw [abs_of_nonneg]
    exact integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (hw_nn θ)
  calc |∫ θ in Work.Spaces.Iθ, KG α θ * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ)|
      = |∫ θ in Work.Spaces.Iθ, u θ * v θ| := by simp only [hu, hv]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := h1
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := h2
    _ = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := h3
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2) := hcs
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
        rw [hsqrt_u, hsqrt_w]

/-! ## The radial Cauchy–Schwarz step -/

lemma tl12_integral_abs_L12dens_Transport_le (α : ℝ) (hα : 0 < α) (g : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α 4 g) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ s ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.L12dens (Work.Coercivity.Transport g) s|
        ≤ Wlam3 s * (B * Real.sqrt
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ))) :
    ∫ s in Set.Ioi (0 : ℝ), |Work.Construction.L12dens (Work.Coercivity.Transport g) s|
      ≤ B * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (Work.Spaces.HkSq α 4 g) := by
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ
  have hAnn : ∀ s, 0 ≤ A s := fun s => Real.sqrt_nonneg _
  -- the marginal `H` is integrable on `(0,∞)`
  have hH_int : IntegrableOn H (Set.Ioi 0) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hH_aesm : AEStronglyMeasurable H (volume.restrict (Set.Ioi 0)) :=
    hH_int.aestronglyMeasurable
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi 0)) := by
    rw [hA]; exact (hH_aesm.aemeasurable.sqrt).aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi 0) := by
    refine hH_int.congr ?_
    filter_upwards with s
    rw [hA]
    exact (Real.sq_sqrt (hHnn s)).symm
  have hA_memLp : MemLp A 2 (volume.restrict (Set.Ioi 0)) :=
    (memLp_two_iff_integrable_sq hA_aesm).mpr hA2_int
  -- the radial weight `Wlam3` is square-integrable, dominated by `Wlam`
  have hcont3 : ContinuousOn Wlam3 (Set.Ioi 0) := by
    change ContinuousOn (fun s : ℝ => s / (1 + s) ^ 3) (Set.Ioi 0)
    refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 3)
      (fun s hs => ?_)
    have hs' : (0 : ℝ) < s := hs
    have h1 : 0 < 1 + s := by linarith
    positivity
  have hWlam3_aesm : AEStronglyMeasurable Wlam3 (volume.restrict (Set.Ioi 0)) :=
    hcont3.aestronglyMeasurable measurableSet_Ioi
  have hWlam3_sq_int : IntegrableOn (fun s => Wlam3 s ^ 2) (Set.Ioi 0) := by
    refine Work.Elliptic.psi_sq_integrable_aux.mono' ((hcont3.pow 2).aestronglyMeasurable
      measurableSet_Ioi) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Wlam3 s))]
    exact pow_le_pow_left₀ (tl12_Wlam3_nonneg (le_of_lt hs)) (tl12_Wlam3_le_Wlam (le_of_lt hs)) 2
  have hWlam3_memLp : MemLp Wlam3 2 (volume.restrict (Set.Ioi 0)) :=
    (memLp_two_iff_integrable_sq hWlam3_aesm).mpr hWlam3_sq_int
  have hW2le : ∫ s in Set.Ioi 0, Wlam3 s ^ 2 ≤ Work.FTS.GalBasis.cc.W2 := by
    rw [Work.FTS.GalBasis.cc.W2]
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => sq_nonneg _)
      Work.Elliptic.psi_sq_integrable_aux ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact pow_le_pow_left₀ (tl12_Wlam3_nonneg (le_of_lt hs)) (tl12_Wlam3_le_Wlam (le_of_lt hs)) 2
  -- `∫_{(0,∞)} A² = HkSq α 4 g`, up to the null set `{0}`
  have hIz_eq : ∫ s in Work.Spaces.Iz, H s = Work.Spaces.HkSq α 4 g := by rw [hH]; rfl
  have hA2sq : ∫ s in Set.Ioi 0, A s ^ 2 = Work.Spaces.HkSq α 4 g := by
    have h1 : ∫ s in Set.Ioi 0, A s ^ 2 = ∫ s in Set.Ioi 0, H s :=
      setIntegral_congr_fun measurableSet_Ioi fun s _ => by
        rw [hA]; exact Real.sq_sqrt (hHnn s)
    have h2 : ∫ s in Set.Ioi 0, H s = ∫ s in Work.Spaces.Iz, H s :=
      MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici' (MeasureTheory.measure_singleton 0))
    rw [h1, h2, hIz_eq]
  -- Cauchy–Schwarz in the radial variable
  have hCS : ∫ s in Set.Ioi 0, Wlam3 s * A s
      ≤ Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (Work.Spaces.HkSq α 4 g) := by
    have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
      (u := Wlam3) (v := A) (s := Set.Ioi 0) hWlam3_memLp hA_memLp
    rw [hA2sq] at hcs
    have hnn : 0 ≤ ∫ s in Set.Ioi 0, Wlam3 s * A s := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      show ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))), (0 : ℝ) ≤ Wlam3 s * A s
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun s hs =>
        mul_nonneg (tl12_Wlam3_nonneg (le_of_lt hs)) (hAnn s)
    rw [abs_of_nonneg hnn] at hcs
    exact le_trans hcs (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hW2le)
      (Real.sqrt_nonneg _))
  -- AM–GM, giving integrability of the majorant
  have hAMGM : ∀ s ∈ Set.Ioi (0 : ℝ), Wlam3 s * A s ≤ Wlam3 s ^ 2 + A s ^ 2 := by
    intro s _
    nlinarith [sq_nonneg (Wlam3 s - A s)]
  have hsum_int : IntegrableOn (fun s => Wlam3 s ^ 2 + A s ^ 2) (Set.Ioi 0) :=
    hWlam3_sq_int.add hA2_int
  have hdom_int : IntegrableOn (fun s => B * (Wlam3 s * A s)) (Set.Ioi 0) := by
    refine Integrable.mono' (hsum_int.const_mul B) ?_ ?_
    · exact (hWlam3_aesm.mul hA_aesm).const_mul B
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hnn : 0 ≤ B * (Wlam3 s * A s) :=
        mul_nonneg hB (mul_nonneg (tl12_Wlam3_nonneg (le_of_lt hs)) (hAnn s))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (hAMGM s hs) hB
  have h2 : ∫ s in Set.Ioi 0, |Work.Construction.L12dens (Work.Coercivity.Transport g) s|
      ≤ ∫ s in Set.Ioi 0, B * (Wlam3 s * A s) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg _) hdom_int ?_
    show ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      |Work.Construction.L12dens (Work.Coercivity.Transport g) s| ≤ B * (Wlam3 s * A s)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hb := hbd s hs
    have hbA : |Work.Construction.L12dens (Work.Coercivity.Transport g) s|
        ≤ Wlam3 s * (B * A s) := by simpa only [hA, hH] using hb
    calc |Work.Construction.L12dens (Work.Coercivity.Transport g) s|
        ≤ Wlam3 s * (B * A s) := hbA
      _ = B * (Wlam3 s * A s) := by ring
  calc ∫ s in Set.Ioi 0, |Work.Construction.L12dens (Work.Coercivity.Transport g) s|
      ≤ ∫ s in Set.Ioi 0, B * (Wlam3 s * A s) := h2
    _ = B * ∫ s in Set.Ioi 0, Wlam3 s * A s := integral_const_mul B _
    _ ≤ B * (Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (Work.Spaces.HkSq α 4 g)) :=
        mul_le_mul_of_nonneg_left hCS hB
    _ = B * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (Work.Spaces.HkSq α 4 g) := by ring

/-! ## The final estimate -/

theorem Transport_L12_zero_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.Spaces.HkMem α 4 g →
    |Work.Coercivity.L12f (Work.Coercivity.Transport g) 0|
      ≤ C * Work.Spaces.HkNorm α 4 g := by
  refine ⟨1 + 13 * Real.sqrt Work.FTS.GalBasis.cc.W2, by positivity, ?_⟩
  intro α g hα hα1 hmem
  have hBK : Real.sqrt (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2) ≤ 13 := tl12_sqrt_KG_sq_le α hα
  -- the pointwise (in `s`) bound
  have hbd : ∀ s ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.L12dens (Work.Coercivity.Transport g) s|
        ≤ Wlam3 s * (13 * Real.sqrt
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)) := by
    intro s hs
    have hslice : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g s θ) Work.Spaces.Iθ :=
      hmem.1 s (by simpa [Work.Spaces.Iz] using le_of_lt hs)
    have hW3nn : 0 ≤ Wlam3 s := tl12_Wlam3_nonneg (le_of_lt hs)
    rw [tl12_L12dens_Transport_eq α g hs, abs_mul, abs_of_nonneg hW3nn]
    refine mul_le_mul_of_nonneg_left ?_ hW3nn
    calc |∫ θ in Work.Spaces.Iθ,
            KG α θ * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ)|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) :=
          tl12_abs_integral_KG_le α hα g hslice
      _ ≤ 13 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) :=
          mul_le_mul_of_nonneg_right hBK (Real.sqrt_nonneg _)
  have hrad := tl12_integral_abs_L12dens_Transport_le α hα g hmem 13 (by norm_num) hbd
  calc |Work.Coercivity.L12f (Work.Coercivity.Transport g) 0|
      = |∫ s in Set.Ioi (0 : ℝ),
          Work.Construction.L12dens (Work.Coercivity.Transport g) s| := by
        simp only [Work.Coercivity.L12f, Work.FM.L12, Work.FM.L12dens,
          Work.Construction.L12dens]
    _ ≤ ∫ s in Set.Ioi (0 : ℝ),
          |Work.Construction.L12dens (Work.Coercivity.Transport g) s| := by
        simpa only [Real.norm_eq_abs] using
          (MeasureTheory.norm_integral_le_integral_norm
            (μ := volume.restrict (Set.Ioi (0 : ℝ)))
            (f := fun s => Work.Construction.L12dens (Work.Coercivity.Transport g) s))
    _ ≤ 13 * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (Work.Spaces.HkSq α 4 g) := hrad
    _ = 13 * Real.sqrt Work.FTS.GalBasis.cc.W2 * Work.Spaces.HkNorm α 4 g := by
        rw [Work.Spaces.HkNorm]
    _ ≤ (1 + 13 * Real.sqrt Work.FTS.GalBasis.cc.W2) * Work.Spaces.HkNorm α 4 g := by
        have h1 := Work.Spaces.HkNorm_nonneg α 4 g
        have h2 := Real.sqrt_nonneg Work.FTS.GalBasis.cc.W2
        nlinarith

end Work.FTS.StrongPersist.L3Aux
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Decay.local_energy_lower_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.Decay

set_option autoImplicit false

theorem local_energy_lower_bound {α C : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hbox : Work.FTS_EllLimOK.BoxReg Ψ)
    (hHk : Work.Spaces.HkMem α 0 Ψ)
    (hDz : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed 1 0 Ψ z θ| ≤ C)
    (hDth : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed 0 1 Ψ z θ| ≤ C)
    (hC : 0 < C) {ε : ℝ} (hε : 0 < ε) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℝ, max 1 (4 * C / ε) ≤ z → ε ≤ |Ψ z θ₀| →
      ∀ z' ∈ Set.Icc z (z + 1),
        c ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z' θ := by
  /- ### Step 1: the geometric data attached to `θ₀` -/
  have hθ₀0 : 0 < θ₀ := hθ₀.1
  have hθ₀lt : θ₀ < Real.pi / 2 := hθ₀.2
  have hS2pos : 0 < Real.sin (2 * θ₀) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  -- the base half-width `u` of the `θ`-window and the resulting lower bound `s` for `sin 2θ`
  set u : ℝ := min (θ₀ / 2) (min ((Real.pi / 2 - θ₀) / 2) (Real.sin (2 * θ₀) / 8)) with hu
  have hu_le1 : u ≤ θ₀ / 2 := hu.le.trans (min_le_left _ _)
  have hu_le2 : u ≤ min ((Real.pi / 2 - θ₀) / 2) (Real.sin (2 * θ₀) / 8) :=
    hu.le.trans (min_le_right _ _)
  have hu_le3 : u ≤ (Real.pi / 2 - θ₀) / 2 := hu_le2.trans (min_le_left _ _)
  have hu_le4 : u ≤ Real.sin (2 * θ₀) / 8 := hu_le2.trans (min_le_right _ _)
  have hu_pos : 0 < u := by
    rw [hu]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  set s : ℝ := 3 * Real.sin (2 * θ₀) / 4 with hs
  have hs_pos : 0 < s := by rw [hs]; linarith
  have hsne : s ≠ 0 := ne_of_gt hs_pos
  have hCne : C ≠ 0 := ne_of_gt hC
  -- `sin 2θ ≥ s` on the window `[θ₀ - u, θ₀ + u]`
  have hsin_ge : ∀ θ ∈ Set.Icc (θ₀ - u) (θ₀ + u), s ≤ Real.sin (2 * θ) := by
    intro θ hθ
    have h1 : |θ - θ₀| ≤ u := abs_le.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have h2 : |2 * θ - 2 * θ₀| ≤ 2 * u := by
      have hθ2 : 2 * θ - 2 * θ₀ = 2 * (θ - θ₀) := by ring
      rw [hθ2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have h3 : |Real.sin (2 * θ) - Real.sin (2 * θ₀)| ≤ 2 * u :=
      le_trans (Real.abs_sin_sub_sin_le _ _) h2
    have h4 : 2 * u ≤ Real.sin (2 * θ₀) / 4 := by linarith [hu_le4]
    have h5 := (abs_le.mp h3).1
    rw [hs]
    linarith
  /- ### Step 2: the final window, shrunk so that the value at `θ₀` survives -/
  set δ : ℝ := min u (ε * s / (8 * C)) with hδ
  have hδ_le_u : δ ≤ u := hδ.le.trans (min_le_left _ _)
  have hδ_le_eps : δ ≤ ε * s / (8 * C) := hδ.le.trans (min_le_right _ _)
  have hδ_pos : 0 < δ := by
    rw [hδ]
    exact lt_min hu_pos (div_pos (mul_pos hε hs_pos) (by linarith))
  have ha_pos : 0 < θ₀ - δ := by linarith [hu_le1, hδ_le_u, hθ₀0]
  have hb_lt : θ₀ + δ < Real.pi / 2 := by linarith [hu_le3, hδ_le_u, hθ₀lt]
  have hab : θ₀ - δ ≤ θ₀ + δ := by linarith [hδ_pos]
  have hsub : Set.Ioc (θ₀ - δ) (θ₀ + δ) ⊆ Work.Spaces.Iθ := by
    intro θ hθ
    exact ⟨by linarith [ha_pos, hθ.1], by linarith [hθ.2, hb_lt]⟩
  have hwin : ∀ θ ∈ Set.Icc (θ₀ - δ) (θ₀ + δ), θ ∈ Set.Icc (θ₀ - u) (θ₀ + u) :=
    fun θ hθ => ⟨by linarith [hδ_le_u, hθ.1], by linarith [hδ_le_u, hθ.2]⟩
  have hθ₀mem : θ₀ ∈ Set.Icc (θ₀ - δ) (θ₀ + δ) :=
    ⟨by linarith [hδ_pos], by linarith [hδ_pos]⟩
  refine ⟨(5 * ε / 8) ^ 2 * (2 * δ),
    mul_pos (pow_pos (by linarith : 0 < 5 * ε / 8) 2) (by linarith), ?_⟩
  /- ### Step 3: the local energy bound on `[z, z+1]` -/
  intro z hz hΨz z' hz'
  have hz1 : 1 ≤ z := le_trans (le_max_left _ _) hz
  have hzC : 4 * C / ε ≤ z := le_trans (le_max_right _ _) hz
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hz'1 : z ≤ z' := hz'.1
  have hz'le : z' ≤ z + 1 := hz'.2
  have hz'ge1 : 1 ≤ z' := le_trans hz1 hz'1
  have hz'pos : 0 < z' := lt_of_lt_of_le zero_lt_one hz'ge1
  have hz'mem : z' ∈ Work.Spaces.Iz := hz'pos.le
  have h4C : 4 * C ≤ ε * z := by
    have h := hzC
    rw [div_le_iff₀ hε] at h
    linarith
  have hCz : C / z ≤ ε / 4 := by
    rw [div_le_iff₀ hzpos]
    linarith
  have hint : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 Ψ z' θ)
      Work.Spaces.Iθ := hHk.1 z' hz'mem
  have hlow : ∀ θ ∈ Set.Icc (θ₀ - δ) (θ₀ + δ),
      (5 * ε / 8) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 Ψ z' θ := by
    intro θ hθmem
    have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [ha_pos, hθmem.1], by linarith [hθmem.2, hb_lt]⟩
    -- the value at `θ₀` propagates to the window at the same `z`
    have hthZ : |Ψ z θ - Ψ z θ₀| ≤ C / s * |θ - θ₀| :=
      abs_slice_th_sub_le (a := θ₀ - δ) (b := θ₀ + δ) (z := z) (s := s)
        hbox hDth hC hzpos ha_pos hb_lt (fun t ht => hsin_ge t (hwin t ht)) hs_pos
        hθ₀mem hθmem
    have hθδ : |θ - θ₀| ≤ δ := abs_le.mpr ⟨by linarith [hθmem.1], by linarith [hθmem.2]⟩
    have hCs : 0 ≤ C / s := (div_pos hC hs_pos).le
    have hbound1 : C / s * |θ - θ₀| ≤ ε / 8 := by
      have h1 : C / s * |θ - θ₀| ≤ C / s * δ := mul_le_mul_of_nonneg_left hθδ hCs
      have h2 : C / s * δ ≤ C / s * (ε * s / (8 * C)) :=
        mul_le_mul_of_nonneg_left hδ_le_eps hCs
      have h3 : C / s * (ε * s / (8 * C)) = ε / 8 := by
        field_simp
      linarith
    have hΨzθ : 7 * ε / 8 ≤ |Ψ z θ| := by
      have hup : |Ψ z θ| - |Ψ z θ₀| ≤ ε / 8 :=
        le_trans (abs_sub_abs_le_abs_sub (Ψ z θ) (Ψ z θ₀)) (le_trans hthZ hbound1)
      have hdown : |Ψ z θ₀| - |Ψ z θ| ≤ ε / 8 := by
        have h3 : |Ψ z θ₀ - Ψ z θ| ≤ ε / 8 := by
          rw [abs_sub_comm]
          exact le_trans hthZ hbound1
        exact le_trans (abs_sub_abs_le_abs_sub (Ψ z θ₀) (Ψ z θ)) h3
      linarith
    -- and then across the window `[z, z+1]`
    have hzZ : |Ψ z' θ - Ψ z θ| ≤ ε / 4 := by
      have h1 : |Ψ z' θ - Ψ z θ| ≤ C / z * (z' - z) :=
        abs_slice_z_sub_le hbox hDz hC hzpos hz'1 hθIoo
      have h2 : C / z * (z' - z) ≤ C / z * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (div_pos hC hzpos).le
      have h3 : C / z * 1 ≤ ε / 4 := by rw [mul_one]; exact hCz
      linarith
    have hΨz'θ : 5 * ε / 8 ≤ |Ψ z' θ| := by
      have hup : |Ψ z' θ| - |Ψ z θ| ≤ ε / 4 :=
        le_trans (abs_sub_abs_le_abs_sub (Ψ z' θ) (Ψ z θ)) hzZ
      have hdown : |Ψ z θ| - |Ψ z' θ| ≤ ε / 4 := by
        have h3 : |Ψ z θ - Ψ z' θ| ≤ ε / 4 := by
          rw [abs_sub_comm]
          exact hzZ
        exact le_trans (abs_sub_abs_le_abs_sub (Ψ z θ) (Ψ z' θ)) h3
      linarith
    -- the integrand is a square with weight factor `≥ 1`
    rw [HkIntegrand_zero_eq]
    have hw : 1 ≤ Work.Spaces.w z' / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
      one_le_w_div_sin hz'ge1 hθIoo
    have hwpos : 0 < Work.Spaces.w z' / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
      lt_of_lt_of_le zero_lt_one hw
    have habs : |Ψ z' θ * (Work.Spaces.w z' / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
        = |Ψ z' θ| * (Work.Spaces.w z' / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
      rw [abs_mul, abs_of_pos hwpos]
    have hge : 5 * ε / 8 ≤
        |Ψ z' θ * (Work.Spaces.w z' / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
      rw [habs]
      have := mul_le_mul hΨz'θ hw zero_le_one (abs_nonneg (Ψ z' θ))
      linarith
    rw [sq_le_sq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 5 * ε / 8)]
    exact hge
  have hfin := thetaIntegral_ge_of_lower_bound
    (f := fun θ => Work.Spaces.HkIntegrand α 0 Ψ z' θ)
    (a := θ₀ - δ) (b := θ₀ + δ) (c := (5 * ε / 8) ^ 2)
    hab hsub hint (fun θ => by rw [HkIntegrand_zero_eq]; exact sq_nonneg _) hlow
  have hlen : θ₀ + δ - (θ₀ - δ) = 2 * δ := by ring
  rw [hlen] at hfin
  exact hfin

end Work.FTS_EllLimOK.Decay
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.LimTower_c2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The Fréchet derivative from continuous slice derivatives -/

/-- The continuous linear map `ℝ × ℝ →L[ℝ] ℝ` which is the Fréchet derivative of a function
whose slice derivatives are `x` (in the first variable) and `y` (in the second). -/
def cop (x y : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ x).coprod (ContinuousLinearMap.toSpanSingleton ℝ y)

theorem cop_apply (x y : ℝ) (v : ℝ × ℝ) : cop x y v = v.1 * x + v.2 * y := by
  simp [cop, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]

/-- The map `c ↦ x ↦ x • c` is continuous. -/
theorem continuous_toSpanSingleton :
    Continuous (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c : ℝ → (ℝ →L[ℝ] ℝ)) := by
  have h : (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c : ℝ → (ℝ →L[ℝ] ℝ))
      = ⇑(ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)) := by
    funext c
    simp [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  rw [h]
  exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous

/-- **Slice derivatives give the Fréchet derivative.**  If the two one-variable slices of `φ`
have derivative `a z θ` resp. `b z θ` at every point of the open set `U`, and these slice
derivative functions are continuous on `U`, then `Function.uncurry φ` is differentiable on `U`
with `fderivWithin ℝ (Function.uncurry φ) U p = cop (a p.1 p.2) (b p.1 p.2)`. -/
theorem diffOn_uncurry_of_slices {φ : ℝ → ℝ → ℝ} {a b : ℝ → ℝ → ℝ}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (ha : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun z' => φ z' θ) (a z θ) z)
    (hb : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun θ' => φ z θ') (b z θ) θ)
    (hca : ContinuousOn (Function.uncurry a) U) (hcb : ContinuousOn (Function.uncurry b) U) :
    DifferentiableOn ℝ (Function.uncurry φ) U ∧
      EqOn (fderivWithin ℝ (Function.uncurry φ) U)
        (fun p => cop (a p.1 p.2) (b p.1 p.2)) U := by
  have key : ∀ p ∈ U, HasFDerivAt (Function.uncurry φ) (cop (a p.1 p.2) (b p.1 p.2)) p := by
    intro p hp
    have hmem : U ∈ 𝓝 p := hU.mem_nhds hp
    have h1 : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun x => φ x v.2)
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (a z θ)) v) v.1 := by
      filter_upwards [hmem] with v hv
      exact (ha v.1 v.2 hv).hasFDerivAt
    have h2 : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun x => φ v.1 x)
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (b z θ)) v) v.2 := by
      filter_upwards [hmem] with v hv
      exact (hb v.1 v.2 hv).hasFDerivAt
    have c1 : ContinuousAt
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (a z θ))) p :=
      continuous_toSpanSingleton.continuousAt.comp (hca.continuousAt hmem)
    have c2 : ContinuousAt
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (b z θ))) p :=
      continuous_toSpanSingleton.continuousAt.comp (hcb.continuousAt hmem)
    have h := hasStrictFDerivAt_uncurry_coprod (u := p) (f := φ)
      (f₁ := fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (a z θ))
      (f₂ := fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (b z θ)) h1 h2 c1 c2
    exact h.hasFDerivAt
  constructor
  · intro p hp; exact (key p hp).differentiableAt.differentiableWithinAt
  · intro p hp
    exact ((key p hp).hasFDerivWithinAt).fderivWithin (hU.uniqueDiffOn p hp)

/-- **Continuous slice derivatives give `C¹`.** -/
theorem contDiffOn_one_of_slices {φ : ℝ → ℝ → ℝ} {a b : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U)
    (ha : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun z' => φ z' θ) (a z θ) z)
    (hb : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun θ' => φ z θ') (b z θ) θ)
    (hca : ContinuousOn (Function.uncurry a) U) (hcb : ContinuousOn (Function.uncurry b) U) :
    ContDiffOn ℝ 1 (Function.uncurry φ) U := by
  have h := diffOn_uncurry_of_slices hU ha hb hca hcb
  refine contDiffOn_succ_of_fderiv_apply (n := 0) h.1 (fun hω => absurd hω (by simp))
    (fun y => ?_)
  rw [contDiffOn_zero]
  have hcontfun : ContinuousOn
      (fun x : ℝ × ℝ => y.1 * a x.1 x.2 + y.2 * b x.1 x.2) U :=
    (continuousOn_const.mul hca).add (continuousOn_const.mul hcb)
  exact hcontfun.congr fun x hx => by rw [h.2 hx, cop_apply]

/-- **The derivative function `p ↦ cop (a p) (b p)` of two `C^n` functions is `C^n`.** -/
theorem contDiffOn_cop {n : WithTop ℕ∞} {U : Set (ℝ × ℝ)} {a b : ℝ × ℝ → ℝ}
    (ha : ContDiffOn ℝ n a U) (hb : ContDiffOn ℝ n b U) :
    ContDiffOn ℝ n (fun p => cop (a p) (b p)) U := by
  have heq : (fun q : ℝ × ℝ => cop q.1 q.2)
      = fun q : ℝ × ℝ =>
        q.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + q.2 • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    funext q
    apply ContinuousLinearMap.ext
    intro v
    rw [show cop q.1 q.2 v = v.1 * q.1 + v.2 * q.2 from by
      simp [cop, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul]]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [show (ContinuousLinearMap.fst ℝ ℝ ℝ) v = v.1 from rfl,
        show (ContinuousLinearMap.snd ℝ ℝ ℝ) v = v.2 from rfl]
    ring
  have hc : ContDiff ℝ n (fun q : ℝ × ℝ => cop q.1 q.2) := by
    rw [heq]
    exact ((contDiff_fst (𝕜 := ℝ)).smul_const _).add ((contDiff_snd (𝕜 := ℝ)).smul_const _)
  have h := hc.comp_contDiffOn (ha.prodMk hb)
  simpa [Function.comp_def] using h

/-! ## The second-order partial tower on an open subset of `ℝ²` -/

/-- **`C²` from a continuous second-order partial tower.**  If `D : ℕ → ℕ → ℝ → ℝ → ℝ` is a
partial-derivative tower on the open set `U` — all `D a b` with `a + b ≤ 2` continuous on `U`
and the slices of `D a b` differentiating to `D (a+1) b` resp. `D a (b+1)` for `a + b ≤ 1` —
then the first entry `D 0 0` is `C²` on `U`. -/
theorem contDiffOn_two_of_partial_tower {φ : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hφ : ∀ z θ, φ z θ = D 0 0 z θ)
    (hcont : ∀ a b : ℕ, a + b ≤ 2 → ContinuousOn (fun p : ℝ × ℝ => D a b p.1 p.2) U)
    (hsz : ∀ a b : ℕ, a + b ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ U →
      HasDerivAt (fun z' => D a b z' θ) (D (a + 1) b z θ) z)
    (hth : ∀ a b : ℕ, a + b ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ U →
      HasDerivAt (fun θ' => D a b z θ') (D a (b + 1) z θ) θ) :
    ContDiffOn ℝ 2 (Function.uncurry φ) U := by
  have hC1_10 : ContDiffOn ℝ 1 (Function.uncurry (D 1 0)) U :=
    contDiffOn_one_of_slices hU (hsz 1 0 (by norm_num)) (hth 1 0 (by norm_num))
      (hcont 2 0 (by norm_num)) (hcont 1 1 (by norm_num))
  have hC1_01 : ContDiffOn ℝ 1 (Function.uncurry (D 0 1)) U :=
    contDiffOn_one_of_slices hU (hsz 0 1 (by norm_num)) (hth 0 1 (by norm_num))
      (hcont 1 1 (by norm_num)) (hcont 0 2 (by norm_num))
  have hcop : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => cop (D 1 0 p.1 p.2) (D 0 1 p.1 p.2)) U :=
    contDiffOn_cop hC1_10 hC1_01
  have hdiff := diffOn_uncurry_of_slices hU (hsz 0 0 (by norm_num)) (hth 0 0 (by norm_num))
    (hcont 1 0 (by norm_num)) (hcont 0 1 (by norm_num))
  have hstep : ContDiffOn ℝ (1 + 1) (Function.uncurry (D 0 0)) U := by
    refine contDiffOn_succ_of_fderiv_apply (n := 1) hdiff.1 (fun hω => absurd hω (by simp))
      (fun y => ?_)
    refine (hcop.clm_apply (contDiffOn_const (c := y))).congr fun x hx => ?_
    rw [hdiff.2 hx]
  have hφD : Function.uncurry φ = Function.uncurry (D 0 0) := by
    funext p; exact hφ p.1 p.2
  rw [hφD]
  exact hstep

/-! ## The tower in the coordinates `u = log z`, `v = log tan θ` -/

/-- In the coordinates `u = log z`, `v = log tan θ` the operator `D_z` becomes `∂_u` and
`D_θ` becomes `2 ∂_v`; the extra factor `2^{-d}` below turns the `d`-fold `θ`-derivative into
the honest `∂_v^d`. -/
def T (F : ℕ → ℕ → ℝ → ℝ → ℝ) (c d : ℕ) (u v : ℝ) : ℝ :=
  F c d (Real.exp u) (Real.arctan (Real.exp v)) / 2 ^ d

/-- The transfer back to the original coordinates: on the open quadrant the tower entry
`T F 0 0` composed with `(z,θ) ↦ (log z, log tan θ)` is `F 0 0`. -/
theorem comp_logLog_T00 (F : ℕ → ℕ → ℝ → ℝ → ℝ) {p : ℝ × ℝ}
    (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    Function.uncurry (F 0 0) p
      = ((Function.uncurry (fun u v => T F 0 0 u v)) ∘
          (fun p : ℝ × ℝ => (Real.log p.1, Real.log (Real.tan p.2)))) p := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have htanpos : 0 < Real.tan p.2 := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1
  have hθπ : p.2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith⟩
  simp only [Function.comp_apply, Function.uncurry, T]
  rw [Real.exp_log hz, Real.exp_log htanpos, Real.arctan_tan hθπ.1 hθπ.2, pow_zero, div_one]

/-! ## The target lemma -/

theorem LimTower_c2 {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hcont : ∀ (c d : ℕ), c + d ≤ 2 → ContinuousOn (fun p : ℝ × ℝ => F c d p.1 p.2)
      Work.FTS.EllipticEst.Q0)
    (hdz : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z)
    (hdth : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) :
    ContDiffOn ℝ 2 (Function.uncurry (F 0 0)) Work.FTS.EllipticEst.Q0 := by
  -- the map `(u,v) ↦ (exp u, arctan (exp v))` lands in the open quadrant
  have hmemQ : ∀ p : ℝ × ℝ,
      (Real.exp p.1, Real.arctan (Real.exp p.2)) ∈ Work.FTS.EllipticEst.Q0 := by
    intro p
    refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos p.1, ?_, ?_⟩
    · rw [Real.arctan_pos]; exact Real.exp_pos p.2
    · exact Real.arctan_lt_pi_div_two _
  have hΦcont : Continuous fun p : ℝ × ℝ => (Real.exp p.1, Real.arctan (Real.exp p.2)) := by
    fun_prop
  -- continuity of every tower entry in the `(u,v)`-coordinates
  have hcontT : ∀ a b : ℕ, a + b ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ => T F a b p.1 p.2) Set.univ := by
    intro a b hab
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        F a b (Real.exp p.1) (Real.arctan (Real.exp p.2))) Set.univ :=
      (hcont a b hab).comp hΦcont.continuousOn (fun p _ => hmemQ p)
    simpa only [T] using h1.div_const (2 ^ b)
  -- the `u`-derivative relation
  have hszT : ∀ a b : ℕ, a + b ≤ 1 → ∀ u v : ℝ,
      HasDerivAt (fun u' : ℝ => T F a b u' v) (T F (a + 1) b u v) u := by
    intro a b hab u v
    have hθ : Real.arctan (Real.exp v) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨by rw [Real.arctan_pos]; exact Real.exp_pos v, Real.arctan_lt_pi_div_two _⟩
    have hzQ : (Real.exp u, Real.arctan (Real.exp v)) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos u, hθ⟩
    have hd := hdz a b hab (Real.exp u) (Real.arctan (Real.exp v)) hzQ
    have hcomp := hd.comp u (Real.hasDerivAt_exp u)
    have hval : F (a + 1) b (Real.exp u) (Real.arctan (Real.exp v)) / Real.exp u
        * Real.exp u = F (a + 1) b (Real.exp u) (Real.arctan (Real.exp v)) := by
      field_simp
    rw [hval] at hcomp
    have h2 := hcomp.div_const (2 ^ b)
    simpa only [T, Function.comp_apply] using h2
  -- the `v`-derivative relation
  have hthT : ∀ a b : ℕ, a + b ≤ 1 → ∀ u v : ℝ,
      HasDerivAt (fun v' : ℝ => T F a b u v') (T F a (b + 1) u v) v := by
    intro a b hab u v
    have hθ : Real.arctan (Real.exp v) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨by rw [Real.arctan_pos]; exact Real.exp_pos v, Real.arctan_lt_pi_div_two _⟩
    have hzQ : (Real.exp u, Real.arctan (Real.exp v)) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos u, hθ⟩
    have hd := hdth a b hab (Real.exp u) (Real.arctan (Real.exp v)) hzQ
    have hcomp := hd.comp v (Work.FTS.StrongEps.LocUnif.hasDerivAt_arctan_exp v)
    have hsin : Real.sin (2 * Real.arctan (Real.exp v)) ≠ 0 := by
      rw [show Real.sin (2 * Real.arctan (Real.exp v))
            = 2 * Real.exp v / (1 + (Real.exp v) ^ 2) from by
        have hS : (0 : ℝ) < 1 + (Real.exp v) ^ 2 := by positivity
        rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
        rw [show (2 : ℝ) * (Real.exp v / √(1 + (Real.exp v) ^ 2))
              * (1 / √(1 + (Real.exp v) ^ 2))
            = 2 * Real.exp v / (√(1 + (Real.exp v) ^ 2)) ^ 2 from by ring]
        rw [Real.sq_sqrt hS.le]]
      positivity
    have hval : F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v))
          / Real.sin (2 * Real.arctan (Real.exp v))
          * (Real.sin (2 * Real.arctan (Real.exp v)) / 2)
        = F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 := by
      field_simp
    rw [hval] at hcomp
    have h2 := hcomp.div_const (2 ^ b)
    have hval2 : F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 / 2 ^ b
        = F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 ^ (b + 1) := by
      rw [pow_succ]; ring
    rw [hval2] at h2
    simpa only [T, Function.comp_apply] using h2
  -- the partial tower on `ℝ²` and the transfer back through the smooth coordinate change
  have h2 := contDiffOn_two_of_partial_tower (φ := fun u v => T F 0 0 u v) (D := T F)
    isOpen_univ (fun u v => rfl) hcontT (fun a b hab z θ _ => hszT a b hab z θ)
    (fun a b hab z θ _ => hthT a b hab z θ)
  have hcomp := h2.comp (Work.FTS.StrongEps.LocUnif.contDiffOn_logLog_Q0 2)
    (fun p _ => Set.mem_univ _)
  exact hcomp.congr fun p hp => comp_logLog_T00 F hp

end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.Pieces.L12_sup_six =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets.Pieces

open MeasureTheory Set Filter
open scoped Real Topology

/-
**The uniform-in-`z` sup bound on `L₁₂` at order `6`.**

`L₁₂(f)(z) = ∫_{s>z} ∫_θ K(θ) f(s,θ)/s dθ ds` is the tail integral of the density
`L₁₂dens f`.  For `z ≥ 0` the absolute value of the tail is dominated by the integral of the
absolute density over the *fixed* half-line `(0,∞)`:

  `|L₁₂ f z| ≤ ∫_{s>z} |L₁₂dens f s| ds ≤ ∫_{s>0} |L₁₂dens f s| ds`,

and the last quantity is estimated by Cauchy–Schwarz (in the angular variable against the
profile `K·sin(2θ)^{η/2}`, and radially against the weight `Wlam s = s/(1+s)²`) by
`BK·√W2·√(HkSq α 6 f)`.  This is the general-order (`k = 6`) form, uniform in `z ≥ 0`, of the
`z = 0` bound of `Work.FTS.GalBasis.cc.abs_L12_le_HkNorm`; the constants `BK`, `W2` are `α`-
and `k`-independent.

The decomposition is
* `abs_integral_K_S_Gaz_le_gen` — the angular Cauchy–Schwarz step at order `6`;
* `integral_abs_L12dens_le_Ioi` — the radial Cauchy–Schwarz step on the tail `(z,∞)`;
* `norm_integral_le_integral_norm` — the (hypothesis-free) domination of the integral by the
  integral of the absolute value.
-/
theorem L12_sup_six : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ),
    Work.Spaces.HkMem α 6 f → ∀ z : ℝ, 0 ≤ z →
      |Work.Construction.L12 f z| ≤ C * Work.Spaces.HkNorm α 6 f := by
  refine ⟨Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2 + 1, ?_, ?_⟩
  · have h1 : 0 ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2 :=
      mul_nonneg Work.FTS.GalBasis.cc.BK_nonneg (Real.sqrt_nonneg _)
    linarith
  · intro α f hmem z hz
    -- the pointwise (in `s > z`) bound on the density
    have hbd : ∀ s ∈ Set.Ioi z, |Work.Construction.L12dens f s|
        ≤ Work.FTS.GalBasis.cc.Wlam s
          * (Work.FTS.GalBasis.cc.BK * Real.sqrt
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f s θ)) := by
      intro s hs
      have hs0 : 0 < s := lt_of_le_of_lt hz hs
      rw [Work.FTS.GalBasis.cc.L12dens_eq_weighted f hs0, abs_mul,
        abs_of_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg hs0.le)]
      exact mul_le_mul_of_nonneg_left
        (Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le_gen α 6 f
          (hmem.1 s (Set.mem_Ici.mpr hs0.le)))
        (Work.FTS.GalBasis.cc.Wlam_nonneg hs0.le)
    have hL12 : Work.Construction.L12 f z
        = ∫ s in Set.Ioi z, Work.Construction.L12dens f s := rfl
    calc |Work.Construction.L12 f z|
        = |∫ s in Set.Ioi z, Work.Construction.L12dens f s| := by rw [hL12]
      _ ≤ ∫ s in Set.Ioi z, |Work.Construction.L12dens f s| := by
          simpa only [Real.norm_eq_abs] using
            (MeasureTheory.norm_integral_le_integral_norm
              (μ := volume.restrict (Set.Ioi z))
              (f := fun s => Work.Construction.L12dens f s))
      _ ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2
            * Real.sqrt (Work.Spaces.HkSq α 6 f) :=
          Work.FTS.GalBasis.cc.integral_abs_L12dens_le_Ioi α 6 f hmem hz hbd
      _ = (Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2)
            * Work.Spaces.HkNorm α 6 f := by rw [Work.Spaces.HkNorm]
      _ ≤ (Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2 + 1)
            * Work.Spaces.HkNorm α 6 f := by
          have hx := Work.Spaces.HkNorm_nonneg α 6 f
          have hnn : 0 ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2 :=
            mul_nonneg Work.FTS.GalBasis.cc.BK_nonneg (Real.sqrt_nonneg _)
          nlinarith [hx]

end Work.FTS_EllLimOK.PkgJets.Pieces
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.Support.pzIter_three_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2.Support

/-- **The Stirling expansion of `D_z = z ∂_z` in the small case `n = 3`.**

`D_z^3 Ψ = z ∂_zΨ + 3 z² ∂_z²Ψ + z³ ∂_z³Ψ` on the open quadrant; the small
numerical form of `Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open`. -/
private theorem DzIter_three_eq {Ψ : ℝ → ℝ → ℝ} {θ z : ℝ}
    (hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => Ψ z' θ) (Set.Ioi 0))
    (hz : 0 < z) :
    Work.Spaces.DzIter 3 Ψ z θ
      = z * Work.Spaces.pzIter 1 Ψ z θ + 3 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ := by
  rw [Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open hslice 3 z hz]
  norm_num [Finset.sum_range_succ, Work.Spaces.scoef]

theorem pzIter_three_bound
    {Ψ : ℝ → ℝ → ℝ} {a b z θ M1 M2 M3 : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) (ha : 0 < a) (hzb : z ∈ Set.Icc a b)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (h1 : |Work.Spaces.mixed 3 0 Ψ z θ| ≤ M1)
    (h2 : |Work.Spaces.pz Ψ z θ| ≤ M2)
    (h3 : |Work.Spaces.pz (Work.Spaces.pz Ψ) z θ| ≤ M3) :
    |Work.Spaces.pzIter 3 Ψ z θ| ≤ (M1 + b * M2 + 3 * b ^ 2 * M3) / a ^ 3 := by
  have haz : a ≤ z := hzb.1
  have hbz : z ≤ b := hzb.2
  have hz0 : 0 < z := lt_of_lt_of_le ha haz
  have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
  have hz3 : 0 ≤ z ^ 3 := pow_nonneg hz0.le 3
  -- the three input bounds, in the `pzIter`-spelling
  have h1' : |Work.Spaces.DzIter 3 Ψ z θ| ≤ M1 := by simpa using h1
  have h2' : |Work.Spaces.pzIter 1 Ψ z θ| ≤ M2 := by simpa using h2
  have h3' : |Work.Spaces.pzIter 2 Ψ z θ| ≤ M3 := by simpa using h3
  have hM2 : 0 ≤ M2 := le_trans (abs_nonneg _) h2'
  have hM3 : 0 ≤ M3 := le_trans (abs_nonneg _) h3'
  have hsum := DzIter_three_eq (hsm.curry_z hθ) hz0
  -- the elementary absolute-value bounds of the three terms
  have hb1 : |z * Work.Spaces.pzIter 1 Ψ z θ| ≤ z * M2 := by
    rw [abs_mul, abs_of_pos hz0]
    exact mul_le_mul_of_nonneg_left h2' hz0.le
  have hb2 : |3 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)| ≤ 3 * (z ^ 2 * M3) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_mul, abs_of_nonneg hz2]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3' hz2) (by norm_num)
  -- solve for `z³ ∂_z³Ψ` and bound it
  have hkey : z ^ 3 * |Work.Spaces.pzIter 3 Ψ z θ| ≤ M1 + b * M2 + 3 * b ^ 2 * M3 := by
    have hxz : z ^ 3 * |Work.Spaces.pzIter 3 Ψ z θ| = |z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ| := by
      rw [abs_mul, abs_of_nonneg hz3]
    rw [hxz]
    have hinner : |z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ| ≤ M1 + z * M2 + 3 * (z ^ 2 * M3) := by
      have hrew : z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ
          = Work.Spaces.DzIter 3 Ψ z θ - z * Work.Spaces.pzIter 1 Ψ z θ
            - 3 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
        rw [hsum]; ring
      rw [hrew, abs_le]
      obtain ⟨hA1, hA2⟩ := abs_le.mp h1'
      obtain ⟨hB1, hB2⟩ := abs_le.mp hb1
      obtain ⟨hC1, hC2⟩ := abs_le.mp hb2
      constructor <;> linarith
    have hzM2 : z * M2 ≤ b * M2 := mul_le_mul_of_nonneg_right hbz hM2
    have hz2M3 : z ^ 2 * M3 ≤ b ^ 2 * M3 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0.le hbz 2) hM3
    linarith
  rw [le_div_iff₀ (pow_pos ha 3)]
  have hlow : |Work.Spaces.pzIter 3 Ψ z θ| * a ^ 3 ≤ |Work.Spaces.pzIter 3 Ψ z θ| * z ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le haz 3) (abs_nonneg _)
  have hcomm : |Work.Spaces.pzIter 3 Ψ z θ| * z ^ 3 = z ^ 3 * |Work.Spaces.pzIter 3 Ψ z θ| := by
    ring
  linarith

end Work.FTS_EllLimOK.ProducerH.H2.Support
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.tendsto_EJet =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Slots.JetCalc

open Filter

/-- **Convergence of one Leibniz sum.**  If every mixed jet `D_z^b D_θ^a X` of order
`a + b ≤ 3` of a sequence `Ξ n` converges pointwise to the corresponding jet of `Ξlim`,
then so does every finite Leibniz sum `coefJetS d j i s` whose highest occurring jet
`D_z^j D_θ^{i+s} X` has order at most `3`.

The `θ`-dependent coefficients `D_θ^k d` are fixed, hence convergent as constant
sequences. -/
theorem tendsto_coefJetS {Ξ : ℕ → ℝ → ℝ → ℝ} {Ξlim : ℝ → ℝ → ℝ}
    (hconv : ∀ (b a : ℕ), a + b ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (Ξ n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed b a Ξlim z θ)))
    (d : ℝ → ℝ) {j i s : ℕ} (hord : j + (i + s) ≤ 3) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => coefJetS d j i s (Ξ n) z θ) Filter.atTop
        (nhds (coefJetS d j i s Ξlim z θ)) := by
  intro z θ hz hθ hθlt
  unfold coefJetS
  refine tendsto_finsetSum (Finset.range (i + 1)) ?_
  intro k hk
  have hk_le : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hle : (i - k + s) + j ≤ 3 := by omega
  have hterm := hconv j (i - k + s) hle z θ hz hθ hθlt
  have hconst : Filter.Tendsto
      (fun _ : ℕ => (i.choose k : ℝ)
        * Work.Spaces.DthIter k (fun _ (θ' : ℝ) => d θ') z θ) Filter.atTop
      (nhds ((i.choose k : ℝ)
        * Work.Spaces.DthIter k (fun _ (θ' : ℝ) => d θ') z θ)) :=
    tendsto_const_nhds
  simpa only [mul_assoc] using hconst.mul hterm

theorem tendsto_EJet {Ξ : ℕ → ℝ → ℝ → ℝ} {Ξlim : ℝ → ℝ → ℝ}
    (hconv : ∀ (b a : ℕ), a + b ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (Ξ n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed b a Ξlim z θ)))
    (a b c : ℝ → ℝ) {j i : ℕ} (hji : j + i ≤ 2) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.FTS_RegExport.RXT.Slots.JetCalc.EJet a b c j i (Ξ n) z θ)
        Filter.atTop
        (nhds (Work.FTS_RegExport.RXT.Slots.JetCalc.EJet a b c j i Ξlim z θ)) := by
  intro z θ hz hθ hθlt
  have h1 := tendsto_coefJetS hconv a (j := j) (i := i) (s := 0) (by omega) z θ hz hθ hθlt
  have h2 := tendsto_coefJetS hconv b (j := j + 1) (i := i) (s := 0) (by omega) z θ hz hθ hθlt
  have h3 := tendsto_coefJetS hconv (fun θ' : ℝ => c θ' / Real.sin (2 * θ'))
    (j := j) (i := i) (s := 1) (by omega) z θ hz hθ hθlt
  unfold EJet
  exact (h1.add h2).add h3

end Work.FTS_RegExport.RXT.Slots.JetCalc
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary facts about the weight `K` and about `∂_z` -/

/-- `|K(θ)| = |3 sinθ cos²θ| ≤ 3` on all of `ℝ` (in particular on `Iθ`). -/
private theorem abs_K_le_three_prv (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    have h := Real.abs_cos_le_one θ
    nlinarith [abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  have hcs : |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 :=
    calc |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 * 1 :=
          mul_le_mul hs hc (sq_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hK : |Work.Spaces.K θ| = 3 * (|Real.sin θ| * Real.cos θ ^ 2) := by
    rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
      abs_of_nonneg (sq_nonneg (Real.cos θ))]
    ring
  rw [hK]
  linarith [hcs]

/-- `K` is continuous. -/
private theorem continuous_K : Continuous Work.Spaces.K := by
  unfold Work.Spaces.K
  exact ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2))

/-- `∂_z` costs one order of differentiability: the uncurried `∂_z f` of a datum that is
jointly `C²` on the open quadrant is jointly continuous there. -/
private theorem continuousOn_pz_of_two {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz f)) Work.FTS.EllipticEst.Q0 := by
  have hchain : ∀ p ∈ Work.FTS.EllipticEst.Q0, Function.uncurry (Work.Spaces.pz f) p
      = (fderiv ℝ (Function.uncurry f) p) (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp))
  have hfd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry f) p)
      Work.FTS.EllipticEst.Q0 := by
    have h' := h.fderivWithin (m := 1) Work.FTS.EllipticEst.isOpen_Q0.uniqueDiffOn
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    refine h'.congr (fun p hp => ?_)
    rw [fderivWithin_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hp]
  have hcomp : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) p) (1, 0))
      Work.FTS.EllipticEst.Q0 :=
    hfd.clm_apply contDiffOn_const
  exact (hcomp.congr hchain).continuousOn

/-! ## The main statement -/

theorem hasDerivAt_integral_Itheta_K {f : ℝ → ℝ → ℝ} {z C : ℝ}
    (h2 : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hz : 0 < z) (hC : 0 ≤ C)
    (hb : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.pz f x θ| ≤ C)
    (hb0 : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f x θ| ≤ C) :
    HasDerivAt (fun x => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f x θ)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f z θ) z := by
  -- `C ≥ 0` is what makes `3 * C` an admissible dominating constant in the two a.e. bounds
  -- below; it is recorded here (the bounds themselves come from `hb`/`hb0` and `|K| ≤ 3`).
  have _hC : (0 : ℝ) ≤ C := hC
  have hV : IsOpen (Set.Ioo (z / 2) (2 * z)) := isOpen_Ioo
  have hzV : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  have hVpos : ∀ x ∈ Set.Ioo (z / 2) (2 * z), 0 < x := fun x hx => by linarith [hx.1, hz]
  -- joint continuity of the angular factor `θ ↦ K θ` on the open quadrant
  have hKc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      Work.FTS.EllipticEst.Q0 := continuous_K.comp_continuousOn continuousOn_snd
  -- joint continuity of the integrand `(x,θ) ↦ K θ · f x θ` on the open quadrant
  have hg : ContinuousOn (Function.uncurry (fun x θ => Work.Spaces.K θ * f x θ))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun x θ => Work.Spaces.K θ * f x θ)
        = fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry f p := by
      funext p; rcases p with ⟨x, θ⟩; rfl
    rw [hfun]
    exact hKc.mul h2.continuousOn
  -- joint continuity of the candidate derivative `(x,θ) ↦ K θ · ∂_z f x θ`
  have hpc : ContinuousOn (Function.uncurry (Work.Spaces.pz f)) Work.FTS.EllipticEst.Q0 :=
    continuousOn_pz_of_two h2
  have hg' : ContinuousOn
      (Function.uncurry (fun x θ => Work.Spaces.K θ * Work.Spaces.pz f x θ))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun x θ => Work.Spaces.K θ * Work.Spaces.pz f x θ)
        = fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry (Work.Spaces.pz f) p := by
      funext p; rcases p with ⟨x, θ⟩; rfl
    rw [hfun]
    exact hKc.mul hpc
  -- the a.e. bound on the base integrand `θ ↦ K θ · f z θ`
  have hbnd0 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K θ * f z θ‖ ≤ 3 * C := by
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_K_le_three_prv θ) (hb0 z hzV θ hθ) (abs_nonneg _) (by norm_num)
  -- integrability of the base integrand on the finite measure space `Iθ`
  have hint : Integrable (fun θ => Work.Spaces.K θ * f z θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Integrable.of_bound (Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0 hg hz) (3 * C) hbnd0
  -- the uniform a.e. bound on the candidate derivative on the strip
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      ‖Work.Spaces.K θ * Work.Spaces.pz f x θ‖ ≤ 3 * C := by
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_K_le_three_prv θ) (hb x hx θ hθ) (abs_nonneg _) (by norm_num)
  -- the pointwise `x`-derivative, at every interior angle and every `x` in the strip
  have hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (fun y => Work.Spaces.K θ * f y θ)
        (Work.Spaces.K θ * Work.Spaces.pz f x θ) x := by
    intro θ hθ x hx
    have hx0 : 0 < x := hVpos x hx
    have hd : DifferentiableAt ℝ (Function.uncurry f) (x, θ) :=
      (h2.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hx0, hθ.1, hθ.2⟩))
    have h1 : HasDerivAt (fun y : ℝ => f y θ) (deriv (fun y : ℝ => f y θ) x) x :=
      (Work.Spaces.differentiableAt_curry_left hd).hasDerivAt
    simpa only [Work.Spaces.pz] using h1.const_mul (Work.Spaces.K θ)
  exact Work.FTS_RegExport.RXT.Slots.hasDerivAt_integral_Itheta_Q0
    (g := fun x θ => Work.Spaces.K θ * f x θ)
    (g' := fun x θ => Work.Spaces.K θ * Work.Spaces.pz f x θ)
    hV hzV hVpos hg hg' hint hbound hdiff

end Work.FTS_RegExport.RXT.Sys.L12FKaux
end
end
