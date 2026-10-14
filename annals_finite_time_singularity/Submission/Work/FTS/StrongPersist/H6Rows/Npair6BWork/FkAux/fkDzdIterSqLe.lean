import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.StepFacts.HkMemJepsStepAux
import Submission.Work.FTS.StrongEps.StepFacts.StepPointwise
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.L3Rhs.CoupledVf
import Submission.Work.FTS.StrongPersist.L3Rhs.CoupledVfs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkJets
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Aux
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.ClassC.level0_psiSeries =====
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

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "w" => Work.Spaces.w
local notation "sEta" => Work.FTS.EllipticEst.sEta


end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.smoothOpen_atoms_of_gal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.RHS

set_option maxHeartbeats 1600000

open Work.FTS.EllipticEst (SmoothOpen)

/-- `N_*` is a linear combination of `g` and `D_z g`, hence `C^∞` on the open quadrant
whenever `g` is. -/
theorem smoothOpen_Nstar_of {μ lam : ℝ} {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    SmoothOpen (Work.Construction.Nstar μ lam g) := by
  have h1 : SmoothOpen (fun z θ : ℝ => -μ * g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (-μ) hg
  have h2 : SmoothOpen (fun z θ : ℝ => (μ + lam + μ * lam) * Work.Spaces.Dz g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (μ + lam + μ * lam) hg.Dz
  have h3 : SmoothOpen (fun z θ : ℝ => -μ * g z θ
      - (μ + lam + μ * lam) * Work.Spaces.Dz g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_sub h1 h2
  refine ContDiffOn.congr (f₁ := Function.uncurry (fun z θ : ℝ => -μ * g z θ
      - (μ + lam + μ * lam) * Work.Spaces.Dz g z θ)) h3 ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry, Work.Construction.Nstar]


end Work.FTS.GalFields.RHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Maj4Slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- `b.choose k ≤ 2^b ≤ 16` for `b ≤ 4`, hence `((b.choose k : ℝ))² ≤ 256`. -/
private theorem choose_sq_le_256 (b k : ℕ) (_hk : k ≤ b) (hb : b ≤ 4) :
    ((b.choose k : ℕ) : ℝ) ^ 2 ≤ 256 := by
  have h1 : b.choose k ≤ 2 ^ b := Nat.choose_le_two_pow b k
  have h2 : 2 ^ b ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hb
  have h3 : ((b.choose k : ℕ) : ℝ) ≤ 16 := by
    have h : b.choose k ≤ 16 := by omega
    exact_mod_cast h
  nlinarith [h3, Nat.cast_nonneg (α := ℝ) (b.choose k)]

theorem HkIntegrand_zero4 (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
  simp

/-- The universal constant of the level-`4` majorant. -/
def Maj4C : ℝ := 1000000

theorem Maj4C_pos : 0 < Maj4C := by norm_num [Maj4C]

/-- A single pure `D_z`-slot of the `ℋ⁴`-integrand of the radial product `X · f`. -/
theorem zslot4 {α B : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hB : 0 ≤ B) (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hR : ∀ j : ℕ, j ≤ 4 → |Work.Elliptic.DzdIter j X z| ≤ B)
    (i : ℕ) (hi : i ≤ 4) :
    (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hlei :=
    Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf i 0 (by omega) z θ hz hθ0 hθ1
  have hmm : Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
      = Work.Spaces.mixed i 0 (fun z θ => X z * f z θ) z θ := rfl
  have hsum : Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range (i + 1),
          (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) := by
    rw [hmm, hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by
      rw [Work.Spaces.mixed_zero_right]
      ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (i + 1),
      ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro b hbmem
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 256 := choose_sq_le_256 i b hbi hi
    have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B ^ 2 := by
      have hx := hR b (by omega)
      rw [← sq_abs]
      nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hB]
    have hG : (Work.Spaces.DzIter (i - b) f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ (i - b) (by omega)
    calc ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        = (((i.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          ring
      _ ≤ 256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
          have hc : (0 : ℝ) ≤ 256 * B ^ 2 := mul_nonneg (by norm_num) (sq_nonneg B)
          exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) hc
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) ≤ 5 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : i + 1 ≤ 5)
  have hMnn : 0 ≤ 256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg B)) hHk
  have hsum2 : (∑ b ∈ Finset.range (i + 1),
        ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
      ≤ 5 * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
    calc (∑ b ∈ Finset.range (i + 1),
          ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
        ≤ ∑ _b ∈ Finset.range (i + 1),
            (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := Finset.sum_le_sum hper
      _ = ((i + 1 : ℕ) : ℝ) * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 5 * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : i + 1 ≤ 5)) hMnn
  refine hcs.trans ?_
  calc (((Finset.range (i + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.DzIter (i - b) f z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 5 * (5 * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by ring

/-- A single mixed slot (`1 ≤ i`) of the `ℋ⁴`-integrand of the radial product `X · f`. -/
theorem mslot4 {α B : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hB : 0 ≤ B) (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hR : ∀ j : ℕ, j ≤ 4 → |Work.Elliptic.DzdIter j X z| ≤ B)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hj4 : j ≤ 4 := by omega
  have hlei :=
    Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf j i (by omega) z θ hz hθ0 hθ1
  have hsum : Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ
      = ∑ b ∈ Finset.range (j + 1),
          (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) := by
    rw [hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (j + 1),
      ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro b hbmem
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 256 := choose_sq_le_256 j b hbj hj4
    have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B ^ 2 := by
      have hx := hR b (by omega)
      rw [← sq_abs]
      nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hB]
    have hG : (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i (j - b) hi (by omega)
    calc ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2
        = (((j.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          ring
      _ ≤ 256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
          have hc : (0 : ℝ) ≤ 256 * B ^ 2 := mul_nonneg (by norm_num) (sq_nonneg B)
          exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) hc
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
    (f := fun b => (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))))
  have hcard : (((Finset.range (j + 1)).card : ℕ) : ℝ) ≤ 5 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : j + 1 ≤ 5)
  have hMnn : 0 ≤ 256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg B)) hHk
  have hsum2 : (∑ b ∈ Finset.range (j + 1),
        ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
      ≤ 5 * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
    calc (∑ b ∈ Finset.range (j + 1),
          ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
        ≤ ∑ _b ∈ Finset.range (j + 1),
            (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := Finset.sum_le_sum hper
      _ = ((j + 1 : ℕ) : ℝ) * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 5 * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : j + 1 ≤ 5)) hMnn
  refine hcs.trans ?_
  calc (((Finset.range (j + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (j + 1),
              ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 5 * (5 * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Maj6SplitSlots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Elementary bounds -/

/-- `b.choose k ≤ 2^b ≤ 64` for `b ≤ 6`, hence `((b.choose k : ℝ))² ≤ 4096`. -/
theorem choose_sq_le_4096 (b k : ℕ) (_hk : k ≤ b) (hb : b ≤ 6) :
    ((b.choose k : ℕ) : ℝ) ^ 2 ≤ 4096 := by
  have h1 : b.choose k ≤ 2 ^ b := Nat.choose_le_two_pow b k
  have h2 : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hb
  have h3 : ((b.choose k : ℕ) : ℝ) ≤ 64 := by
    have h : b.choose k ≤ 64 := by omega
    exact_mod_cast h
  nlinarith [h3, Nat.cast_nonneg (α := ℝ) (b.choose k)]

/-- At `z = 0` the weight vanishes, so every term of the weighted integrand vanishes there. -/
theorem HkIntegrand_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
  simp

/-- The value of the universal constant of the pointwise majorant. -/
def MajC : ℝ := 20000000

theorem MajC_pos : 0 < MajC := by norm_num [MajC]

/-! ## A single pure `D_z`-slot -/

theorem zslot6_split {α Blo Bhi : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hBlo : 0 ≤ Blo) (hBhi : 0 ≤ Bhi)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0)) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hLo : ∀ j : ℕ, j ≤ 4 → |Work.Elliptic.DzdIter j X z| ≤ Blo)
    (hHi : ∀ j : ℕ, j ≤ 6 → |Work.Elliptic.DzdIter j X z| ≤ Bhi)
    (i : ℕ) (hi : i ≤ 6) :
    (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
  have hHk6 : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hHk2 : 0 ≤ Work.Spaces.HkIntegrand α 2 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 2 f z θ
  have hlei :=
    Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf i 0 (by omega) z θ hz hθ0 hθ1
  have hmm : Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
      = Work.Spaces.mixed i 0 (fun z θ => X z * f z θ) z θ := rfl
  have hsum : Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range (i + 1),
          (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) := by
    rw [hmm, hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by
      rw [Work.Spaces.mixed_zero_right]
      ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (i + 1),
      ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    intro b hbmem
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 := choose_sq_le_4096 i b hbi hi
    by_cases hb4 : b ≤ 4
    · have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ Blo ^ 2 := by
        have hx := hLo b hb4
        rw [← sq_abs]
        nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hBlo]
      have hG : (Work.Spaces.DzIter (i - b) f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ (i - b) (by omega)
      calc ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
          = (((i.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
            ring
        _ ≤ 4096 * Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
            have hc : (0 : ℝ) ≤ 4096 * Blo ^ 2 :=
              mul_nonneg (by norm_num) (sq_nonneg Blo)
            exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
              (sq_nonneg _) hc
        _ ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
            have h1 : 0 ≤ Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ :=
              mul_nonneg (sq_nonneg Bhi) hHk2
            nlinarith [h1, hHk6, sq_nonneg Blo]
    · have hb5 : 5 ≤ b := by omega
      have hib : i - b ≤ 1 := by omega
      have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ Bhi ^ 2 := by
        have hx := hHi b (by omega)
        rw [← sq_abs]
        nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hBhi]
      have hG : (Work.Spaces.DzIter (i - b) f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Work.Spaces.HkIntegrand α 2 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 2 f z θ (i - b) (by omega)
      calc ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
          = (((i.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
            ring
        _ ≤ 4096 * Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ := by
            have hc : (0 : ℝ) ≤ 4096 * Bhi ^ 2 :=
              mul_nonneg (by norm_num) (sq_nonneg Bhi)
            exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
              (sq_nonneg _) hc
        _ ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
            have h1 : 0 ≤ Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ :=
              mul_nonneg (sq_nonneg Blo) hHk6
            nlinarith [h1, hHk2, sq_nonneg Bhi]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) ≤ 7 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : i + 1 ≤ 7)
  have hMnn : 0 ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
      + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    have h : 0 ≤ Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
        + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ :=
      add_nonneg (mul_nonneg (sq_nonneg Blo) hHk6) (mul_nonneg (sq_nonneg Bhi) hHk2)
    linarith
  have hsum2 : (∑ b ∈ Finset.range (i + 1),
        ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
      ≤ 7 * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
    calc (∑ b ∈ Finset.range (i + 1),
          ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
        ≤ ∑ _b ∈ Finset.range (i + 1),
            (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := Finset.sum_le_sum hper
      _ = ((i + 1 : ℕ) : ℝ) * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 7 * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : i + 1 ≤ 7)) hMnn
  refine hcs.trans ?_
  calc (((Finset.range (i + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.DzIter (i - b) f z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 7 * (7 * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ))) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by ring

/-! ## A single mixed slot -/

theorem mslot6_split {α Blo Bhi : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hBlo : 0 ≤ Blo) (hBhi : 0 ≤ Bhi)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0)) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hLo : ∀ j : ℕ, j ≤ 4 → |Work.Elliptic.DzdIter j X z| ≤ Blo)
    (hHi : ∀ j : ℕ, j ≤ 6 → |Work.Elliptic.DzdIter j X z| ≤ Bhi)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
  have hHk6 : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hHk2 : 0 ≤ Work.Spaces.HkIntegrand α 2 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 2 f z θ
  have hj6 : j ≤ 6 := by omega
  have hlei :=
    Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf j i hj6 z θ hz hθ0 hθ1
  have hsum : Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ
      = ∑ b ∈ Finset.range (j + 1),
          (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) := by
    rw [hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (j + 1),
      ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    intro b hbmem
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 := choose_sq_le_4096 j b hbj hj6
    by_cases hb4 : b ≤ 4
    · have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ Blo ^ 2 := by
        have hx := hLo b hb4
        rw [← sq_abs]
        nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hBlo]
      have hG : (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ i (j - b) hi (by omega)
      calc ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
              * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2
          = (((j.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
              * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
            ring
        _ ≤ 4096 * Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
            have hc : (0 : ℝ) ≤ 4096 * Blo ^ 2 :=
              mul_nonneg (by norm_num) (sq_nonneg Blo)
            exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
              (sq_nonneg _) hc
        _ ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
            have h1 : 0 ≤ Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ :=
              mul_nonneg (sq_nonneg Bhi) hHk2
            nlinarith [h1, hHk6, sq_nonneg Blo]
    · have hb5 : 5 ≤ b := by omega
      have hji : i + (j - b) ≤ 2 := by omega
      have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ Bhi ^ 2 := by
        have hx := hHi b (by omega)
        rw [← sq_abs]
        nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hBhi]
      have hG : (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 2 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 2 f z θ i (j - b) hi hji
      calc ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
              * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2
          = (((j.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
              * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
            ring
        _ ≤ 4096 * Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ := by
            have hc : (0 : ℝ) ≤ 4096 * Bhi ^ 2 :=
              mul_nonneg (by norm_num) (sq_nonneg Bhi)
            exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
              (sq_nonneg _) hc
        _ ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
            have h1 : 0 ≤ Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ :=
              mul_nonneg (sq_nonneg Blo) hHk6
            nlinarith [h1, hHk2, sq_nonneg Bhi]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
    (f := fun b => (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))))
  have hcard : (((Finset.range (j + 1)).card : ℕ) : ℝ) ≤ 7 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : j + 1 ≤ 7)
  have hMnn : 0 ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
      + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    have h : 0 ≤ Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
        + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ :=
      add_nonneg (mul_nonneg (sq_nonneg Blo) hHk6) (mul_nonneg (sq_nonneg Bhi) hHk2)
    linarith
  have hsum2 : (∑ b ∈ Finset.range (j + 1),
        ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
      ≤ 7 * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
    calc (∑ b ∈ Finset.range (j + 1),
          ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
        ≤ ∑ _b ∈ Finset.range (j + 1),
            (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := Finset.sum_le_sum hper
      _ = ((j + 1 : ℕ) : ℝ) * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 7 * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : j + 1 ≤ 7)) hMnn
  refine hcs.trans ?_
  calc (((Finset.range (j + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (j + 1),
              ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 7 * (7 * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ))) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by ring


end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.vfs4_VfsA2_jet =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- NOTE: the statement uses the notation `π` for `Real.pi`, so the locale `Real` has to be
-- opened (as in the sibling `VfsA2JetBound`).
open scoped Real

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

open Work.FTS.StrongPersist.L3Rhs (VfsA2 VfsGc)

/-- The order-4 version of `Work.FTS.StrongPersist.L3Rhs.VfsA2JetBound`: the `dthU`-jets of
`VfsA2 α = -α·c₂·(Γ/c)` up to order `4` are dominated by `α·B` times the jets `0 ≤ m ≤ 4` of
`Γ/c = VfsGc α`.

The hypothesis on `c₂` is exactly the order-4 jet bound `|dthU^[j] c₂| ≤ B` (`j ≤ 4`), so the
only change with respect to `VfsA2JetBound` is that the binomial sum
`Σ_{a ≤ i} C(i,a)` is now bounded by `2^i ≤ 2^4 = 16`; the constant is `16`.

Route: `dthU^[i](VfsA2 α) θ = -α Σ_{a≤i} C(i,a)·dthU^[a](c₂) θ·dthU^[i-a](VfsGc α) θ`
(iterated Leibniz rule on the open set `(0,π/2)`, plus linearity for the constant factor `-α`);
every term is at most `C(i,a)·B·inner` with
`inner = |VfsGc α θ| + Σ_{1≤m≤4}|dthU^[m](VfsGc α) θ|`. -/
theorem vfs4_VfsA2_jet :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℝ), 0 < B →
        (∀ j ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
          |Work.Spaces.dthU^[j] Work.Construction.c2m θ| ≤ B) →
        ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
        ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          |Work.Spaces.dthU^[i]
              (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ|
            ≤ C * B * α
              * (|Work.FTS.StrongPersist.L3Rhs.VfsGc α θ|
                + ∑ m ∈ Finset.Icc 1 4,
                    |Work.Spaces.dthU^[m]
                      (Work.FTS.StrongPersist.L3Rhs.VfsGc α) θ|) := by
  refine ⟨16, by norm_num, ?_⟩
  intro B hB hc2 α hα hα1 i hi1 hi4 θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (π / 2)) := isOpen_Ioo
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- ## Smoothness of the two angular factors on `U = (0, π/2)`
  have hc2sm : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) Work.Construction.c2m
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    have h : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
        (fun t : ℝ => Real.cos (2 * t) - Real.sin t ^ 2) := by fun_prop
    refine h.contDiffOn.congr (fun t _ => ?_)
    rw [Work.Construction.c2m_eq]
  have hgcsm : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (VfsGc α)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Work.FTS.PhiStar.contDiffOn_Gam α).div_const _
  have hprodsm : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (Work.Construction.c2m * VfsGc α) (Set.Ioo (0 : ℝ) (π / 2)) := hc2sm.mul hgcsm
  -- ## The inner bound: every jet of order `≤ 4` of `VfsGc α` is dominated by `inner`
  set inner : ℝ := |VfsGc α θ|
      + ∑ m ∈ Finset.Icc 1 4, |Work.Spaces.dthU^[m] (VfsGc α) θ| with hinner
  have hinner_nonneg : 0 ≤ inner := by
    rw [hinner]
    exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun m _ => abs_nonneg _))
  have hgc_le : ∀ m : ℕ, m ≤ 4 → |Work.Spaces.dthU^[m] (VfsGc α) θ| ≤ inner := by
    intro m hm4
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      rw [hinner]
      simp only [Function.iterate_zero, id_eq]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun m _ => abs_nonneg _))
    · have hmem : m ∈ Finset.Icc 1 4 := Finset.mem_Icc.mpr ⟨hmpos, hm4⟩
      rw [hinner]
      exact le_trans
        (Finset.single_le_sum (s := Finset.Icc 1 4)
          (f := fun x => |Work.Spaces.dthU^[x] (VfsGc α) θ|)
          (fun x _ => abs_nonneg _) hmem)
        (le_add_of_nonneg_left (abs_nonneg _))
  -- ## The Leibniz expansion of the jets of `VfsA2 α = -α · (c₂ · VfsGc α)`
  have hfe : VfsA2 α = fun t : ℝ => -α * ((Work.Construction.c2m * VfsGc α) t) := by
    funext t; rw [VfsA2, Pi.mul_apply]; ring
  have hexp : Work.Spaces.dthU^[i] (VfsA2 α) θ
      = -α * ∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ) *
          (Work.Spaces.dthU^[a] Work.Construction.c2m θ
            * Work.Spaces.dthU^[i - a] (VfsGc α) θ) := by
    rw [hfe]
    rw [show Work.Spaces.dthU^[i]
          (fun t : ℝ => -α * ((Work.Construction.c2m * VfsGc α) t)) θ
        = -α * Work.Spaces.dthU^[i] (Work.Construction.c2m * VfsGc α) θ from by
      simpa using Work.FTS.PhiStar.Psi0Est.dthU_iter_const_mul_eqOn hU (-α) hprodsm i hθ]
    congr 1
    simpa using Work.FTS.PhiStar.Psi0Est.dthU_iter_mul_eqOn hU hc2sm hgcsm i hθ
  rw [hexp]
  set S : ℝ := ∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ) *
      (Work.Spaces.dthU^[a] Work.Construction.c2m θ
        * Work.Spaces.dthU^[i - a] (VfsGc α) θ) with hSdef
  -- ## Termwise bound of the binomial sum
  have hterm : ∀ a ∈ Finset.range (i + 1),
      |((i.choose a : ℕ) : ℝ) *
        (Work.Spaces.dthU^[a] Work.Construction.c2m θ
          * Work.Spaces.dthU^[i - a] (VfsGc α) θ)|
        ≤ ((i.choose a : ℕ) : ℝ) * (B * inner) := by
    intro a ha
    have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hchoose : (0 : ℝ) ≤ ((i.choose a : ℕ) : ℝ) := by positivity
    have hc2a : |Work.Spaces.dthU^[a] Work.Construction.c2m θ| ≤ B :=
      hc2 a (by omega) θ hθI
    have hgca : |Work.Spaces.dthU^[i - a] (VfsGc α) θ| ≤ inner := hgc_le (i - a) (by omega)
    have hprod : |Work.Spaces.dthU^[a] Work.Construction.c2m θ|
        * |Work.Spaces.dthU^[i - a] (VfsGc α) θ| ≤ B * inner :=
      mul_le_mul hc2a hgca (abs_nonneg _) (le_of_lt hB)
    rw [abs_mul, abs_of_nonneg hchoose, abs_mul]
    exact mul_le_mul_of_nonneg_left hprod hchoose
  have hS : |S| ≤ ∑ a ∈ Finset.range (i + 1),
      ((i.choose a : ℕ) : ℝ) * (B * inner) := by
    rw [hSdef]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  have hsum_eq : (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ) * (B * inner))
      = (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ)) * (B * inner) := by
    rw [Finset.sum_mul]
  -- ## The binomial sum is at most `2 ^ i ≤ 16`
  have hbin : (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ)) ≤ 16 := by
    have hN : (∑ a ∈ Finset.range (i + 1), i.choose a) ≤ 16 := by
      have h2 : (∑ a ∈ Finset.range (i + 1), i.choose a) = 2 ^ i := Nat.sum_range_choose i
      rw [h2]
      calc 2 ^ i ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hi4
        _ = 16 := by norm_num
    exact_mod_cast hN
  -- ## Assembly
  calc |-α * S| = α * |S| := by rw [abs_mul, abs_neg, abs_of_pos hα]
    _ ≤ α * (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ) * (B * inner)) :=
        mul_le_mul_of_nonneg_left hS hα.le
    _ = α * ((∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ)) * (B * inner)) := by
        rw [hsum_eq]
    _ ≤ α * (16 * (B * inner)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hbin (by positivity)) hα.le
    _ = 16 * B * α * inner := by ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces

/-! ## The budget -/

/-- The pointwise budget of the level-`6` product bound for `A · D_θ f`.  Its four summands are
the two terms of the target estimate that are not of the form `K · (·)²` of a single slot, split
into the pairs (price, kept slot) that occur in the Leibniz expansion. -/
def ptdBud (α : ℝ) (A f : ℝ → ℝ → ℝ) (MA : ℝ) (z θ : ℝ) : ℝ :=
  MA ^ 2 * HkIntegrand α 7 f z θ
    + (gam α - 1)⁻¹ * HkSq α 6 A * HkIntegrand α 6 f z θ
    + (gam α - 1)⁻¹ * HkSq α 6 f * HkIntegrand α 6 A z θ
    + (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2

theorem ptdBud_nonneg {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA : ℝ) (z θ : ℝ) :
    0 ≤ ptdBud α A f MA z θ := by
  have hγ : 0 ≤ (gam α - 1)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (by rw [gam_sub_one]; linarith))
  have h1 := HkIntegrand_nonneg α 7 f z θ
  have h2 := HkSq_nonneg α 6 A
  have h3 := HkSq_nonneg α 6 f
  have h4 := HkIntegrand_nonneg α 6 A z θ
  have h5 := HkIntegrand_nonneg α 6 f z θ
  rw [ptdBud]
  positivity

/-- The `MA²`-component of the budget. -/
theorem MAsq_mul_Hk7_le_ptdBud {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    MA ^ 2 * HkIntegrand α 7 f z θ ≤ ptdBud α A f MA z θ := by
  have hγ : 0 ≤ (gam α - 1)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (by rw [gam_sub_one]; linarith))
  have h2 := HkSq_nonneg α 6 A
  have h3 := HkSq_nonneg α 6 f
  have h4 := HkIntegrand_nonneg α 6 A z θ
  have h5 := HkIntegrand_nonneg α 6 f z θ
  have h6 : 0 ≤ MA ^ 2 := sq_nonneg MA
  rw [ptdBud]
  nlinarith [mul_nonneg hγ (mul_nonneg h2 h5), mul_nonneg hγ (mul_nonneg h3 h4),
    sq_nonneg (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ)]

/-- The `(γ-1)⁻¹ HkSq 6 A · HkIntegrand 6 f`-component of the budget. -/
theorem inv_hA_mul_Hk6f_le_ptdBud {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    (gam α - 1)⁻¹ * HkSq α 6 A * HkIntegrand α 6 f z θ ≤ ptdBud α A f MA z θ := by
  have hγ : 0 ≤ (gam α - 1)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (by rw [gam_sub_one]; linarith))
  have h3 := HkSq_nonneg α 6 f
  have h4 := HkIntegrand_nonneg α 6 A z θ
  have h6 : 0 ≤ MA ^ 2 := sq_nonneg MA
  have h1 := HkIntegrand_nonneg α 7 f z θ
  rw [ptdBud]
  nlinarith [mul_nonneg h6 h1, mul_nonneg hγ (mul_nonneg h3 h4),
    sq_nonneg (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ)]

/-- The `(γ-1)⁻¹ HkSq 6 f · HkIntegrand 6 A`-component of the budget. -/
theorem inv_hf_mul_Hk6A_le_ptdBud {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    (gam α - 1)⁻¹ * HkSq α 6 f * HkIntegrand α 6 A z θ ≤ ptdBud α A f MA z θ := by
  have hγ : 0 ≤ (gam α - 1)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (by rw [gam_sub_one]; linarith))
  have h2 := HkSq_nonneg α 6 A
  have h5 := HkIntegrand_nonneg α 6 f z θ
  have h6 : 0 ≤ MA ^ 2 := sq_nonneg MA
  have h1 := HkIntegrand_nonneg α 7 f z θ
  rw [ptdBud]
  nlinarith [mul_nonneg h6 h1, mul_nonneg hγ (mul_nonneg h2 h5),
    sq_nonneg (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ)]

/-- The exceptional squared slot `(D_z⁵A · D_θ²f · W)²` is a summand of the budget. -/
theorem exc_le_ptdBud {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2 ≤ ptdBud α A f MA z θ := by
  have hγ : 0 ≤ (gam α - 1)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (by rw [gam_sub_one]; linarith))
  have h2 := HkSq_nonneg α 6 A
  have h3 := HkSq_nonneg α 6 f
  have h1 := HkIntegrand_nonneg α 7 f z θ
  have h4 := HkIntegrand_nonneg α 6 A z θ
  have h5 := HkIntegrand_nonneg α 6 f z θ
  have h6 : 0 ≤ MA ^ 2 := sq_nonneg MA
  rw [ptdBud]
  nlinarith [mul_nonneg h6 h1, mul_nonneg hγ (mul_nonneg h2 h5),
    mul_nonneg hγ (mul_nonneg h3 h4)]

/-! ## The universal pricing constant -/

/-- The universal constant of the level-six pointwise price `PwAny6`. -/
def CP : ℝ := Classical.choose Work.FTS.StrongPersist.N6.PwAny6

theorem CP_pos : 0 < CP := (Classical.choose_spec Work.FTS.StrongPersist.N6.PwAny6).1

/-- The pointwise price: every slot `D_z^bD_θ^a g` with `a + b ≤ 4` of a `C^∞`-on-the-quadrant
datum `g ∈ ℋ⁶` is bounded by `CP (γ-1)⁻¹ |g|²_{ℋ⁶}` (with `CP` the universal constant above). -/
theorem CP_price (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : HkMem α 6 f) (hab : a + b ≤ 4)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (mixed b a f z θ) ^ 2 ≤ CP / (gam α - 1) * HkSq α 6 f :=
  (Classical.choose_spec Work.FTS.StrongPersist.N6.PwAny6).2 α f b a hα hα1 hf hmem hab z hz θ hθ

/-- The constant of the per-summand estimates. -/
def ptdK2 : ℝ := 4096 * (CP + 1)

theorem ptdK2_pos : 0 < ptdK2 := by
  have := CP_pos
  rw [ptdK2]; positivity

theorem one_le_ptdK2 : 1 ≤ ptdK2 := by
  have := CP_pos
  rw [ptdK2]; nlinarith

theorem CP_le_ptdK2 : CP ≤ ptdK2 := by
  have := CP_pos
  rw [ptdK2]; nlinarith


/-! ## The weight comparison `w/sin(2θ)^{η/2} ≤ W` -/

theorem div_rpow_le_wTheta {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) : (Real.sin (2 * θ) ^ (eta / 2))⁻¹ ≤ wTheta α θ := by
  have hs0 : 0 < Real.sin (2 * θ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos ⟨hθ0, hθ1⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hexp : eta / 2 ≤ gam α / 2 := by
    have : eta ≤ gam α := by rw [eta, gam]; linarith
    linarith
  have hle : Real.sin (2 * θ) ^ (gam α / 2) ≤ Real.sin (2 * θ) ^ (eta / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hs0 hs1 hexp
  rw [wTheta, Real.rpow_neg hs0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hs0 _) hle

theorem wTheta_pos {α θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) : 0 < wTheta α θ := by
  have hs0 : 0 < Real.sin (2 * θ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos ⟨hθ0, hθ1⟩
  rw [wTheta, Real.rpow_neg hs0.le]
  exact inv_pos.mpr (Real.rpow_pos_of_pos hs0 _)

/-- `w/sin(2θ)^{η/2} ≤ W` on the open quadrant, because `η < γ`. -/
theorem abs_light_le_abs_Wt {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    |w z / Real.sin (2 * θ) ^ (eta / 2)| ≤ |Wt α z θ| := by
  have hs0 : 0 < Real.sin (2 * θ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos ⟨hθ0, hθ1⟩
  have hw : 0 < w z := Work.FTS.TransportS.w_pos_of_pos hz
  have h1 := div_rpow_le_wTheta hα hα1 hθ0 hθ1
  have h2 : 0 < w z / Real.sin (2 * θ) ^ (eta / 2) :=
    div_pos hw (Real.rpow_pos_of_pos hs0 _)
  have h3 : 0 < wTheta α θ := wTheta_pos hθ0 hθ1
  rw [abs_of_pos h2, Wt, abs_of_pos (mul_pos hw h3), div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left h1 hw.le

/-- The `L²`-form of the weight comparison: a light-weighted slot is dominated by the
`W`-weighted one. -/
theorem sq_light_le_sq_Wt {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (Y : ℝ) :
    (Y * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2 ≤ (Y * (Wt α z θ)) ^ 2 := by
  have h := abs_light_le_abs_Wt hα hα1 hz hθ0 hθ1
  refine sq_le_sq.mpr ?_
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg Y)

/-! ## Cauchy–Schwarz bookkeeping -/

/-- `(∑ x ∈ s, f x)² ≤ s.card · ∑ x ∈ s, (f x)²`. -/
theorem sq_sum_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s f (fun _ => (1 : ℝ))
  have h2 : (∑ i ∈ s, f i ^ 2) * (s.card : ℝ) = (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 :=
    mul_comm _ _
  rw [← h2]
  simpa using h

end Work.FTS.StrongEps.E4R3.Nblock6.Tools
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsApprox.HkNorm_Jeps_sub_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsApprox

open Work.FTS.StrongEps.DiffAux
open Work.FTS.StrongEps (Quad zShift thShift Jker Jeps IsMollKernel sin_two_pos
  Jker_continuous zShift_pos thShift_mem)

set_option maxHeartbeats 4000000

/-! ## The quantitative estimate in square (`HkSq`) form

This is the `ℝ≥0∞`-integration of the pointwise bound `HkIntegrand_sub_le`: after Tonelli,
the log-coordinate shift invariance replaces the shifted shadow by `e^{δ(|p₁|+|p₂|)}` times the
unshifted one, the kernel mass contributes `e^{2δε}`, and the combinatorial bound
`shadow_le` identifies the result with `2 · HkSq α (k+1) f`. -/
theorem HkSq_sub_est_aux {ρ : ℝ × ℝ → ℝ} {α : ℝ} (hα : α ∈ Set.Ioc 0 1) (hρ : IsMollKernel ρ)
    {k : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hF : Work.Spaces.HkMem α (k + 1) f)
    {c δ : ℝ} (hc : 0 ≤ c) (hδ0 : 0 ≤ δ)
    (hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ q : ℝ × ℝ,
      wE z θ ≤ Real.exp (c * (|q.1| + |q.2|)) * wE (zShift z q.1) (thShift θ q.2))
    (hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ q : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (c * (|q.1| + |q.2|))
        * Work.Spaces.Wt α (zShift z q.1) (thShift θ q.2))
    (hJac : ∀ s ζ p₁ p₂ : ℝ, HkSqAux.logJac s ζ
      ≤ Real.exp (δ * (|p₁| + |p₂|)) * HkSqAux.logJac (s - p₁) (ζ - p₂)) :
    Work.Spaces.HkSq α k (fun z θ => Jeps ρ ε f z θ - f z θ)
      ≤ 4 * Real.exp (4 * c + 2 * δ) * ε ^ 2 * Work.Spaces.HkSq α (k + 1) f := by
  have hfQ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad := hf
  have hmeasure : μX = (volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Measure.prod_restrict (μ := volume) (ν := volume) (s := Work.Spaces.Iz)
      (t := Work.Spaces.Iθ)
  have hmeasureY : μY = (volume.prod volume).restrict (Set.univ ×ˢ Set.Icc (0:ℝ) 1) := by
    show volume.prod (volume.restrict (Set.Icc (0:ℝ) 1)) = _
    rw [← Measure.prod_restrict (μ := volume) (ν := volume) (s := Set.univ)
      (t := Set.Icc (0:ℝ) 1), Measure.restrict_univ]
  have h2ne : (2 : ℝ≥0∞) ≠ ⊤ := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm]
    exact ENNReal.ofReal_ne_top
  -- the joint measurability of the four-variable integrand
  have hF4 : AEMeasurable (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) => ENNReal.ofReal (Jker ρ ε q.2.1)
      * ENNReal.ofReal (shadow α k f (zShift q.1.1 (q.2.2 * q.2.1.1))
          (thShift q.1.2 (q.2.2 * q.2.1.2)))) (μX.prod μY) :=
    aemeasurable_pair_comp hρ hε (continuousOn_shadow (k := k) hfQ)
  -- the reference value: `ofReal (HkSq α (k+1) f)` as an iterated `lintegral`
  have hHkSq : ENNReal.ofReal (Work.Spaces.HkSq α (k + 1) f)
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) f z θ) := by
    rw [Work.Spaces.HkSq]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF.2
      (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α (k + 1) f z θ)]
    exact MeasureTheory.setLIntegral_congr_fun measurableSet_Ici
      (fun z hz => MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hF.1 z hz)
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α (k + 1) f z θ))
  -- (A) the left-hand side as an iterated `lintegral`
  have hA : ENNReal.ofReal (Work.Spaces.HkSq α k (fun z θ => Jeps ρ ε f z θ - f z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (fun z θ => Jeps ρ ε f z θ - f z θ)
            z θ) := by
    rw [Work.Spaces.HkSq]
    refine (ofReal_integral_le_lintegral (volume.restrict Work.Spaces.Iz) ?_).trans ?_
    · intro z
      exact integral_nonneg fun θ' =>
        Work.Spaces.HkIntegrand_nonneg α k (fun z θ => Jeps ρ ε f z θ - f z θ) z θ'
    · refine lintegral_mono fun z => ?_
      exact ofReal_integral_le_lintegral (volume.restrict Work.Spaces.Iθ)
        fun θ' => Work.Spaces.HkIntegrand_nonneg α k (fun z θ => Jeps ρ ε f z θ - f z θ) z θ'
  -- (B) the pointwise bound, integrated
  have hB : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (fun z θ => Jeps ρ ε f z θ - f z θ)
            z θ))
      ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
        * ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, lintegral μY (fun y =>
            ENNReal.ofReal (Jker ρ ε y.1)
              * ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
                  (thShift θ (y.2 * y.1.2)))) := by
    rw [← MeasureTheory.lintegral_const_mul' (μ := volume.restrict Work.Spaces.Iz)
      (ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε)))
      (fun z => ∫⁻ θ in Work.Spaces.Iθ, lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
          * ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2)))))
      ENNReal.ofReal_ne_top]
    refine MeasureTheory.setLIntegral_mono' measurableSet_Ici fun z hz => ?_
    rw [← MeasureTheory.lintegral_const_mul' (μ := volume.restrict Work.Spaces.Iθ)
      (ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε)))
      (fun θ => lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
          * ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))))) ENNReal.ofReal_ne_top]
    refine MeasureTheory.setLIntegral_mono' measurableSet_Icc fun θ hθ => ?_
    exact HkIntegrand_sub_le (ε := ε) hα hρ hε hfQ hc hWη hWγ hz hθ
  -- (C) the shift variables as a product measure
  have hCK : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, lintegral μY (fun y =>
        ENNReal.ofReal (Jker ρ ε y.1)
          * ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2)))))
      = lintegral μX (fun x => lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
          * ENNReal.ofReal (shadow α k f (zShift x.1 (y.2 * y.1.1))
              (thShift x.2 (y.2 * y.1.2))))) := by
    have hG : AEMeasurable (fun x : ℝ × ℝ => lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
        * ENNReal.ofReal (shadow α k f (zShift x.1 (y.2 * y.1.1))
            (thShift x.2 (y.2 * y.1.2)))))
        ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
      rw [← hmeasure]
      exact hF4.lintegral_prod_right'
    rw [lintegral_μX_eq hG]
  -- (D) Tonelli
  have hCD : lintegral μX (fun x => lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
        * ENNReal.ofReal (shadow α k f (zShift x.1 (y.2 * y.1.1))
            (thShift x.2 (y.2 * y.1.2)))))
      = lintegral μY (fun y => lintegral μX (fun x => ENNReal.ofReal (Jker ρ ε y.1)
          * ENNReal.ofReal (shadow α k f (zShift x.1 (y.2 * y.1.1))
              (thShift x.2 (y.2 * y.1.2))))) :=
    lintegral_swap4 hF4
  -- (E) the shift step: pull out the kernel, shift the shadow, and spend the kernel mass
  have hDE : lintegral μY (fun y => lintegral μX (fun x => ENNReal.ofReal (Jker ρ ε y.1)
          * ENNReal.ofReal (shadow α k f (zShift x.1 (y.2 * y.1.1))
              (thShift x.2 (y.2 * y.1.2)))))
      ≤ ENNReal.ofReal (Real.exp (2 * δ * ε))
        * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (shadow α k f z θ)) := by
    -- the joint measurability of the `(p,t)`-integrand
    have hmeas : AEMeasurable (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)
        * ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))) μY := by
      have hJk : Continuous (Jker ρ ε) := Jker_continuous hρ ε
      have h1 : AEMeasurable (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)) μY :=
        (ENNReal.continuous_ofReal.comp (hJk.comp continuous_fst)).aemeasurable
      have h2 : AEMeasurable (fun y : (ℝ × ℝ) × ℝ =>
          ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))) μY :=
        (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul
          ((continuous_abs.comp (continuous_snd.mul continuous_fst.fst)).add
            (continuous_abs.comp (continuous_snd.mul continuous_fst.snd)))))).aemeasurable
      exact h1.mul h2
    have hmeasY : AEMeasurable (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)
        * ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|))))
        ((volume.prod volume).restrict (Set.univ ×ˢ Set.Icc (0:ℝ) 1)) := by
      rw [← hmeasureY]
      exact hmeas
    have hstep : ∀ y : (ℝ × ℝ) × ℝ,
        lintegral μX (fun x => ENNReal.ofReal (Jker ρ ε y.1)
            * ENNReal.ofReal (shadow α k f (zShift x.1 (y.2 * y.1.1))
                (thShift x.2 (y.2 * y.1.2))))
        = ENNReal.ofReal (Jker ρ ε y.1)
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
                (thShift θ (y.2 * y.1.2)))) := by
      intro y
      rw [MeasureTheory.lintegral_const_mul' (μ := μX) (ENNReal.ofReal (Jker ρ ε y.1)) _
        ENNReal.ofReal_ne_top]
      congr 1
      exact lintegral_μX_eq (by
        rw [← hmeasure]
        exact aemeasurable_μX_comp (continuousOn_shadow (k := k) hfQ) y)
    rw [lintegral_congr hstep]
    have hshift : ∀ y ∈ (Set.univ : Set ((ℝ × ℝ) × ℝ)),
        (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))))
          ≤ ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))
            * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (shadow α k f z θ)) := by
      intro y _
      exact lintegral_shift_le_gen (V := fun u v => shadow α k f u v) hJac
        (y.2 * y.1.1, y.2 * y.1.2)
    have hmass : lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
        * ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|))))
        ≤ ENNReal.ofReal (Real.exp (2 * δ * ε)) := by
      rw [lintegral_μY_eq hmeasY]
      have hstep1 : ∀ p : ℝ × ℝ, (∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal (Real.exp (δ * (|t * p.1| + |t * p.2|))))
          ≤ ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) := by
        intro p
        have hexp : ∀ t ∈ Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal (Real.exp (δ * (|t * p.1| + |t * p.2|)))
            ≤ ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) := by
          intro t ht
          refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) zero_le
          rw [Real.exp_le_exp]
          have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
          have h1 : |t * p.1| ≤ |p.1| := by
            rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ht1
          have h2 : |t * p.2| ≤ |p.2| := by
            rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ht1
          nlinarith [h1, h2, hδ0]
        calc (∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal (Real.exp (δ * (|t * p.1| + |t * p.2|))))
            ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) :=
              MeasureTheory.setLIntegral_mono' measurableSet_Icc hexp
          _ = ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) := by
              rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
              simp
      refine (lintegral_mono hstep1).trans ?_
      have hker := HkSqAux.Jker_exp_integral_le hρ hε (c := 0) (δ := δ)
        (by norm_num) hδ0
      simpa only [mul_zero, zero_add] using hker
    calc lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
                (thShift θ (y.2 * y.1.2)))))
        ≤ lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
            * (ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))
              * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                  ENNReal.ofReal (shadow α k f z θ)))) := by
          refine lintegral_mono fun y => ?_
          exact mul_le_mul_of_nonneg_left (hshift y (Set.mem_univ y)) zero_le
      _ = (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (shadow α k f z θ))
            * lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
                * ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))) := by
          calc lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
                * (ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))
                  * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal (shadow α k f z θ))))
              = lintegral μY (fun y => (ENNReal.ofReal (Jker ρ ε y.1)
                  * ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|))))
                  * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal (shadow α k f z θ))) :=
                lintegral_congr fun y => by ring
            _ = (lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
                  * ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))))
                  * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal (shadow α k f z θ)) :=
                MeasureTheory.lintegral_mul_const''
                  (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal (shadow α k f z θ)) hmeas
            _ = (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal (shadow α k f z θ))
                  * lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
                      * ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))) := by
                rw [mul_comm]
      _ ≤ (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (shadow α k f z θ)) * ENNReal.ofReal (Real.exp (2 * δ * ε)) :=
          mul_le_mul_of_nonneg_left hmass zero_le
      _ = ENNReal.ofReal (Real.exp (2 * δ * ε))
            * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (shadow α k f z θ)) := by rw [mul_comm]
  -- (F) the shadow bound
  have hEF : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (shadow α k f z θ))
      ≤ 2 * ENNReal.ofReal (Work.Spaces.HkSq α (k + 1) f) := by
    rw [hHkSq]
    calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (shadow α k f z θ))
        ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (2 * Work.Spaces.HkIntegrand α (k + 1) f z θ) := by
          refine MeasureTheory.setLIntegral_mono' measurableSet_Ici fun z _ => ?_
          refine MeasureTheory.setLIntegral_mono' measurableSet_Icc fun θ _ => ?_
          exact ENNReal.ofReal_le_ofReal (shadow_le α k f z θ)
      _ = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            2 * ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) f z θ) := by
          refine lintegral_congr fun z => lintegral_congr fun θ => ?_
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
          norm_num
      _ = 2 * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) f z θ)) := by
          have hinner : ∀ z : ℝ, (∫⁻ θ in Work.Spaces.Iθ,
                2 * ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) f z θ))
              = 2 * ∫⁻ θ in Work.Spaces.Iθ,
                  ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) f z θ) :=
            fun z => MeasureTheory.lintegral_const_mul'
              (μ := volume.restrict Work.Spaces.Iθ) 2 _ h2ne
          rw [lintegral_congr hinner]
          rw [MeasureTheory.lintegral_const_mul' (μ := volume.restrict Work.Spaces.Iz)
            2 _ h2ne]
  -- assembling
  have hchain : ENNReal.ofReal (Work.Spaces.HkSq α k (fun z θ => Jeps ρ ε f z θ - f z θ))
      ≤ 2 * ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
        * ENNReal.ofReal (Real.exp (2 * δ * ε))
        * ENNReal.ofReal (Work.Spaces.HkSq α (k + 1) f) := by
    refine (hA.trans (hB.trans ?_))
    rw [hCK, hCD]
    calc ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * lintegral μY (fun y => lintegral μX (fun x => ENNReal.ofReal (Jker ρ ε y.1)
              * ENNReal.ofReal (shadow α k f (zShift x.1 (y.2 * y.1.1))
                  (thShift x.2 (y.2 * y.1.2)))))
        ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * (ENNReal.ofReal (Real.exp (2 * δ * ε))
            * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (shadow α k f z θ))) :=
          mul_le_mul_of_nonneg_left hDE zero_le
      _ ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * (ENNReal.ofReal (Real.exp (2 * δ * ε))
            * (2 * ENNReal.ofReal (Work.Spaces.HkSq α (k + 1) f))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEF zero_le) zero_le
      _ = 2 * ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * ENNReal.ofReal (Real.exp (2 * δ * ε))
          * ENNReal.ofReal (Work.Spaces.HkSq α (k + 1) f) := by ring
  -- merge the `ofReal`s into a single one
  have hmerge : 2 * ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
        * ENNReal.ofReal (Real.exp (2 * δ * ε))
        * ENNReal.ofReal (Work.Spaces.HkSq α (k + 1) f)
      = ENNReal.ofReal (2 * (2 * ε ^ 2 * Real.exp (4 * c * ε)) * Real.exp (2 * δ * ε)
          * Work.Spaces.HkSq α (k + 1) f) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * (2 * ε ^ 2 * Real.exp (4 * c * ε))),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * Real.exp (2 * δ * ε))]
  rw [hmerge] at hchain
  have hY : (0:ℝ) ≤ Work.Spaces.HkSq α (k + 1) f := Work.Spaces.HkSq_nonneg α (k + 1) f
  have hgoal : Work.Spaces.HkSq α k (fun z θ => Jeps ρ ε f z θ - f z θ)
      ≤ 2 * (2 * ε ^ 2 * Real.exp (4 * c * ε)) * Real.exp (2 * δ * ε)
          * Work.Spaces.HkSq α (k + 1) f := by
    refine (ENNReal.ofReal_le_ofReal_iff ?_).mp hchain
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      (Real.exp_pos _).le) hY
  have hexp : Real.exp (4 * c * ε) * Real.exp (2 * δ * ε) ≤ Real.exp (4 * c + 2 * δ) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [hε.le, hε1, hc, hδ0])
  calc Work.Spaces.HkSq α k (fun z θ => Jeps ρ ε f z θ - f z θ)
      ≤ 2 * (2 * ε ^ 2 * Real.exp (4 * c * ε)) * Real.exp (2 * δ * ε)
          * Work.Spaces.HkSq α (k + 1) f := hgoal
    _ = 4 * ε ^ 2 * (Real.exp (4 * c * ε) * Real.exp (2 * δ * ε))
          * Work.Spaces.HkSq α (k + 1) f := by ring
    _ ≤ 4 * ε ^ 2 * Real.exp (4 * c + 2 * δ) * Work.Spaces.HkSq α (k + 1) f := by
        have hfac : (0:ℝ) ≤ 4 * ε ^ 2 * Work.Spaces.HkSq α (k + 1) f :=
          mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg ε)) hY
        calc 4 * ε ^ 2 * (Real.exp (4 * c * ε) * Real.exp (2 * δ * ε))
              * Work.Spaces.HkSq α (k + 1) f
            = (Real.exp (4 * c * ε) * Real.exp (2 * δ * ε))
                * (4 * ε ^ 2 * Work.Spaces.HkSq α (k + 1) f) := by ring
          _ ≤ Real.exp (4 * c + 2 * δ)
                * (4 * ε ^ 2 * Work.Spaces.HkSq α (k + 1) f) :=
              mul_le_mul_of_nonneg_right hexp hfac
          _ = 4 * ε ^ 2 * Real.exp (4 * c + 2 * δ)
                * Work.Spaces.HkSq α (k + 1) f := by ring
    _ = 4 * Real.exp (4 * c + 2 * δ) * ε ^ 2 * Work.Spaces.HkSq α (k + 1) f := by ring

/-! ## The norm form -/

/-- **The mollifier-approximation estimate in the weighted `ℋ^k` norm**: for every admissible
mollifier kernel `ρ` there is a constant `C` with
`‖J_ε f - f‖_{ℋ^k} ≤ C ε ‖f‖_{ℋ^{k+1}}` for all `α ∈ (0,1]`, `k`, `ε ∈ (0,1]` and all
`f` which are `C^∞` on the open quadrant with `HkMem α (k+1) f`.

It is the square root of `HkSq_sub_est_aux`, since `HkNorm = √HkSq`. -/
theorem HkNorm_Jeps_sub_le (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ k : ℕ, ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 →
      ∀ f : ℝ → ℝ → ℝ,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0) →
        Work.Spaces.HkMem α (k + 1) f →
        Work.Spaces.HkMem α k (Work.FTS.StrongEps.Jeps ρ ε f) →
        Work.Spaces.HkNorm α k (fun z θ => Work.FTS.StrongEps.Jeps ρ ε f z θ - f z θ)
          ≤ C * ε * Work.Spaces.HkNorm α (k + 1) f := by
  obtain ⟨cη, hcη, hWη0⟩ := HkSqAux.wdiv_shift_le
  obtain ⟨cγ, hcγ, hWγ0⟩ := HkSqAux.Wt_shift_le
  obtain ⟨δ, hδ, hJac⟩ := HkSqAux.logJac_shift_le
  refine ⟨Real.sqrt (4 * Real.exp (4 * max cη cγ + 2 * δ)), Real.sqrt_pos.2 (by positivity), ?_⟩
  intro α hα k ε hε f hf hF _
  have hc : 0 ≤ max cη cγ := le_of_lt (lt_of_lt_of_le hcη (le_max_left _ _))
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ q : ℝ × ℝ,
      wE z θ ≤ Real.exp (max cη cγ * (|q.1| + |q.2|)) * wE (zShift z q.1) (thShift θ q.2) := by
    intro z θ hz hθ q
    refine (hWη0 z θ q.1 q.2 hz hθ).trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · exact wE_nonneg (thShift_mem hθ)
  have hWt_nn : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p₁ p₂ : ℝ,
      0 ≤ Work.Spaces.Wt α (zShift z p₁) (thShift θ p₂) := fun z θ hz hθ p₁ p₂ =>
    Wt_nonneg ⟨le_of_lt (thShift_mem hθ).1, le_of_lt (thShift_mem hθ).2⟩
  have hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ q : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (max cη cγ * (|q.1| + |q.2|))
        * Work.Spaces.Wt α (zShift z q.1) (thShift θ q.2) := by
    intro z θ hz hθ q
    refine (hWγ0 α hα z θ q.1 q.2 hz hθ).trans
      (mul_le_mul_of_nonneg_right ?_ (hWt_nn z θ hz hθ q.1 q.2))
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hmain := HkSq_sub_est_aux hα hρ hε.1 hε.2 hf hF hc hδ0 hWη hWγ hJac
  have hY : (0:ℝ) ≤ Work.Spaces.HkSq α (k + 1) f := Work.Spaces.HkSq_nonneg α (k + 1) f
  have hstep : Work.Spaces.HkSq α k (fun z θ => Jeps ρ ε f z θ - f z θ)
      ≤ (Real.sqrt (4 * Real.exp (4 * max cη cγ + 2 * δ)) * ε
          * Work.Spaces.HkNorm α (k + 1) f) ^ 2 := by
    have hsq : (Real.sqrt (4 * Real.exp (4 * max cη cγ + 2 * δ)) * ε
          * Work.Spaces.HkNorm α (k + 1) f) ^ 2
        = 4 * Real.exp (4 * max cη cγ + 2 * δ) * ε ^ 2 * Work.Spaces.HkSq α (k + 1) f := by
      rw [mul_pow, mul_pow,
        Real.sq_sqrt (by positivity : (0:ℝ) ≤ 4 * Real.exp (4 * max cη cγ + 2 * δ)),
        Work.Spaces.HkNorm, Real.sq_sqrt hY]
    rw [hsq]
    exact hmain
  have hle := Real.sqrt_le_sqrt hstep
  have hnn : (0:ℝ) ≤ Real.sqrt (4 * Real.exp (4 * max cη cγ + 2 * δ)) * ε
      * Work.Spaces.HkNorm α (k + 1) f :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hε.1.le) (Real.sqrt_nonneg _)
  rw [Real.sqrt_sq hnn] at hle
  simpa only [Work.Spaces.HkNorm] using hle

end Work.FTS.StrongEps.EpsApprox
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Comm2_succ_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

theorem Comm2_succ_O (α : ℝ) (hα : 0 < α) (n : ℕ)
    {IP : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ} {c₁ c₂ : ℝ}
    (hc : Work.FTS.StrongEps.EpsE4Thr.Comm2O α n IP) :
    Work.FTS.StrongEps.EpsE4Thr.Comm2O α (n + 1)
      (Work.Coercivity.HkIPStep c₁ c₂ IP) := by
  -- The two commutator clauses mention neither `n` nor `IP`: they are inherited verbatim.
  refine ⟨?congr, ?add, hc.dthC, hc.dzC⟩
  case congr =>
    -- Congruence: the derivative is local and the open quadrant is open, so agreement on
    -- `Qd` propagates to `D_θ` and `D_z`, and the three `congr` clauses of `IP` apply.
    intro f f' g hfg
    have e0 := hc.congr f f' g hfg
    have e1 := hc.congr (Work.Spaces.Dth f) (Work.Spaces.Dth f') (Work.Spaces.Dth g)
      (Work.FTS.IPGen.Dth_congr_Qd hfg)
    have e2 := hc.congr (Work.Spaces.Dz f) (Work.Spaces.Dz f') (Work.Spaces.Dz g)
      (Work.FTS.IPGen.Dz_congr_Qd hfg)
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
  case add =>
    intro f₁ f₂ g hf₁ hf₂ hg
    -- descent of the class from level `n+1` to level `n`
    have h₁ : RegQo α n f₁ := regQo_mono (Nat.le_succ n) hf₁
    have h₂ : RegQo α n f₂ := regQo_mono (Nat.le_succ n) hf₂
    have h₃ : RegQo α n g := regQo_mono (Nat.le_succ n) hg
    have e0 := hc.add f₁ f₂ g h₁ h₂ h₃
    have h1n : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have hbadd : Work.FTS.CoercivityFix.Assembly.BlocksAdd (n + 1) f₁ f₂ :=
      Work.FTS.IPGen.BlocksAdd_of_smoothOpen (k := n + 1) hf₁.1 hf₂.1
    have e1 : IP (Work.Spaces.Dth (f₁ + f₂)) (Work.Spaces.Dth g)
        = IP (Work.Spaces.Dth f₁) (Work.Spaces.Dth g)
          + IP (Work.Spaces.Dth f₂) (Work.Spaces.Dth g) := by
      rw [hc.congr (Work.Spaces.Dth (f₁ + f₂))
        (Work.Spaces.Dth f₁ + Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        (Work.FTS.IPGen.Dth_add_of_blocksAdd hbadd h1n)]
      exact hc.add (Work.Spaces.Dth f₁) (Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        (regQo_dth_dz hα hf₁).1 (regQo_dth_dz hα hf₂).1 (regQo_dth_dz hα hg).1
    have e2 : IP (Work.Spaces.Dz (f₁ + f₂)) (Work.Spaces.Dz g)
        = IP (Work.Spaces.Dz f₁) (Work.Spaces.Dz g)
          + IP (Work.Spaces.Dz f₂) (Work.Spaces.Dz g) := by
      rw [hc.congr (Work.Spaces.Dz (f₁ + f₂))
        (Work.Spaces.Dz f₁ + Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        (Work.FTS.IPGen.Dz_add_of_blocksAdd hbadd h1n)]
      exact hc.add (Work.Spaces.Dz f₁) (Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        (regQo_dth_dz hα hf₁).2 (regQo_dth_dz hα hf₂).2 (regQo_dth_dz hα hg).2
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
    ring

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.DiagCross =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace Work.FTS.StrongEps.EpsE4Thr

set_option linter.unusedVariables false







end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.StepMembership =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.StrongEps.StepFacts (Kd Fd Psi Psi_nonneg Psi_mass Psi_moment_integrable Dmass
  hjstep_Psi_comp_zShift_lt_top hjstep_aemeasurable_pair_slice_Psi aemeasurable_Psi_shift)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000


end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.StepTO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongEps.EpsE4Thr (CoerAdmO CoerData2O CoerDataTO RegQo StepReg2O)
open Work.FTS.StrongEps.EpsE4Thr.TransO (cs_clause_succ_O)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- Young's inequality in the form used by the step: for `0 < lam` and `x, y ≥ 0`,
`p·√x·√y ≤ lam·x + (p²/(4·lam))·y`. -/
private lemma young_absorb_T {lam p x y : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    p * (Real.sqrt x * Real.sqrt y) ≤ lam * x + (p ^ 2 / (4 * lam)) * y := by
  have h4 : 0 < 4 * lam := by linarith
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hsy : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  have h1 : 0 ≤ (2 * lam * Real.sqrt x - p * Real.sqrt y) ^ 2 := sq_nonneg _
  have h3 : 4 * lam * (p * (Real.sqrt x * Real.sqrt y)) ≤ 4 * lam ^ 2 * x + p ^ 2 * y := by
    nlinarith [h1, hsx, hsy]
  have h2 : (4 * lam) * ((p ^ 2 / (4 * lam)) * y) = p ^ 2 * y := by
    field_simp
  have hkey : 4 * lam * (p * (Real.sqrt x * Real.sqrt y))
      ≤ 4 * lam * (lam * x + (p ^ 2 / (4 * lam)) * y) := by
    have h4' : 4 * lam * (lam * x + (p ^ 2 / (4 * lam)) * y)
        = 4 * lam ^ 2 * x + 4 * lam * ((p ^ 2 / (4 * lam)) * y) := by ring
    rw [h4', h2]
    linarith [h3]
  exact le_of_mul_le_mul_left hkey h4

/-- **The transfer step, on the open class.** -/
theorem stepT_O (α : ℝ) (n : ℕ) (hα : 0 < α) (hn3 : n ≤ 3)
    {IP : Fn → Fn → ℝ} {cc CC ccL CCL κ₁ κ₂ c₁ c₂ D : ℝ}
    (ht : CoerDataTO α n IP cc CC)
    (hcl : CoerData2O α n IP ccL CCL)
    (hc : Work.FTS.CoercivityFix.Transfer.CommSm α n IP)
    (hcs1 : ∀ f : Fn, CoerAdmO α f →
      |IP (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f)|
        ≤ CCL * Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dth f))
    (hcs2 : ∀ f : Fn, CoerAdmO α f →
      |IP (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f)|
        ≤ CCL * Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dz f))
    (hreg : StepReg2O α n)
    (hid1 : ∀ f : Fn, CoerAdmO α f → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ
          + Work.FTS.CoercivityFix.Transfer.E1 α f z θ)
    (hid2 : ∀ f : Fn, CoerAdmO α f → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
          + Work.FTS.CoercivityFix.Transfer.E2 α f z θ)
    (hbk1 : ∀ f : Fn, CoerAdmO α f →
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f))
        (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f))
    (hbk2 : ∀ f : Fn, CoerAdmO α f →
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
        (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f))
    (hn1 : ∀ f : Fn, CoerAdmO α f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
        ≤ α * κ₁ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hn2 : ∀ f : Fn, CoerAdmO α f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
        ≤ κ₂ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hD : 0 < D)
    (hs1 : c₁ * (16 * (CCL * α * κ₁) ^ 2) ≤ cc * ccL)
    (hs2 : CCL * α * κ₁ ≤ ccL / 8)
    (hs3 : c₂ * (16 * (CCL * κ₂) ^ 2) ≤ cc * ccL)
    (hs4 : c₂ * (16 * (CCL * κ₂) ^ 2) ≤ c₁ * ccL ^ 2)
    (hnormD : ∀ f : Fn, CoerAdmO α f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ D * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f))) :
    CoerDataTO α (n + 1) (Work.Coercivity.HkIPStep c₁ c₂ IP)
      (min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) / D)
      (3 * max 1 (max c₁ c₂) * CC) := by
  have hα'' : 0 < α := hα
  have hccL : 0 < ccL := hcl.hcc
  have hCCL : 0 < CCL := hcl.hCC
  have hm₀ : 0 < min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) :=
    lt_min (by linarith [ht.hcc]) (lt_min (by positivity) (by positivity))
  have hcc' : 0 < min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) / D :=
    div_pos hm₀ hD
  have hCC' : 0 < 3 * max 1 (max c₁ c₂) * CC := by
    have h1 : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
    nlinarith [ht.hCC]
  refine ⟨hcc', hCC', ?_, ?_⟩
  · -- the Cauchy–Schwarz clause
    intro f g hf hg
    exact cs_clause_succ_O α hα'' n ht.cs (le_of_lt ht.hCC) hc₁ hc₂ f g hf hg
  · -- the coercivity clause
    intro f hf
    set X0 : ℝ := Work.Spaces.HkSq α n f with hX0def
    set X1 : ℝ := Work.Spaces.HkSq α n (Work.Spaces.Dth f) with hX1def
    set X2 : ℝ := Work.Spaces.HkSq α n (Work.Spaces.Dz f) with hX2def
    set Y : ℝ := Work.Spaces.HkSq α (n + 1) f with hYdef
    have hX0 : 0 ≤ X0 := by rw [hX0def]; exact Work.Spaces.HkSq_nonneg α n f
    have hX1 : 0 ≤ X1 := by rw [hX1def]; exact Work.Spaces.HkSq_nonneg α n _
    have hX2 : 0 ≤ X2 := by rw [hX2def]; exact Work.Spaces.HkSq_nonneg α n _
    have hf2 : RegQo α (n + 2) f := regQo_mono (k := n + 2) (l := 5) (by omega) hf.1
    have hf1 : RegQo α (n + 1) (Work.Spaces.Dth f) := hreg.dth1 f hf2
    have hf2n : RegQo α (n + 1) (Work.Spaces.Dz f) := hreg.dz1 f hf2
    obtain ⟨hq1a, hq1b, hq1c, hm1a, hm1b, hm1c⟩ := hbk1 f hf
    obtain ⟨hq2a, hq2b, hq2c, hm2a, hm2b, hm2c⟩ := hbk2 f hf
    have e₁ : IP (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)
        = IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f)
          + IP (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f) := by
      rw [hc.congr (Work.Spaces.Dth (Work.Coercivity.LGammaT α f))
            (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)
              + Work.FTS.CoercivityFix.Transfer.E1 α f)
            (Work.Spaces.Dth f) (fun z θ h => hid1 f hf z θ h)]
      exact hc.add _ _ _ ⟨hq1a, hq1b, hq1c, hm1a, hm1b, hm1c⟩
    have e₂ : IP (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f)
        = IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
          + IP (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f) := by
      rw [hc.congr (Work.Spaces.Dz (Work.Coercivity.LGammaT α f))
            (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)
              + Work.FTS.CoercivityFix.Transfer.E2 α f)
            (Work.Spaces.Dz f) (fun z θ h => hid2 f hf z θ h)]
      exact hc.add _ _ _ ⟨hq2a, hq2b, hq2c, hm2a, hm2b, hm2c⟩
    -- the three coercivities
    have hA : cc * X0 ≤ IP (Work.Coercivity.LGammaT α f) f := ht.coer f hf
    have hB1 : ccL * X1
        ≤ IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f) :=
      hcl.coer _ hf1
    have hB2 : ccL * X2
        ≤ IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f) :=
      hcl.coer _ hf2n
    -- the two Cauchy–Schwarz bounds on the error pairings
    have hS1 : |IP (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f)|
        ≤ CCL * Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f))
            * Real.sqrt X1 := by
      have h := hcs1 f hf
      rw [show Work.Spaces.HkNorm α n (Work.Spaces.Dth f) = Real.sqrt X1 from by
        rw [Work.Spaces.HkNorm, hX1def]] at h
      rwa [show Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
        = Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f))
          from rfl] at h
    have hS2 : |IP (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f)|
        ≤ CCL * Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f))
            * Real.sqrt X2 := by
      have h := hcs2 f hf
      rw [show Work.Spaces.HkNorm α n (Work.Spaces.Dz f) = Real.sqrt X2 from by
        rw [Work.Spaces.HkNorm, hX2def]] at h
      rwa [show Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
        = Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f))
          from rfl] at h
    -- the two defect norms
    have hν1 : Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f)) * CCL
        ≤ (α * κ₁ * CCL) * (Real.sqrt X0 + Real.sqrt X1) := by
      have h := hn1 f hf
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkNorm, ← hX0def, ← hX1def] at h
      nlinarith [h, le_of_lt hCCL]
    have hν2 : Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f)) * CCL
        ≤ (κ₂ * CCL) * (Real.sqrt X0 + Real.sqrt X1) := by
      have h := hn2 f hf
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkNorm, ← hX0def, ← hX1def] at h
      nlinarith [h, le_of_lt hCCL]
    have hn1' : CCL * Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f))
          * Real.sqrt X1
        ≤ (α * κ₁ * CCL) * (Real.sqrt X0 * Real.sqrt X1) + (α * κ₁ * CCL) * X1 := by
      have h := mul_le_mul_of_nonneg_right hν1 (Real.sqrt_nonneg X1)
      have hsq : (Real.sqrt X1) ^ 2 = X1 := Real.sq_sqrt hX1
      nlinarith [h, hsq]
    have hn2' : CCL * Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f))
          * Real.sqrt X2
        ≤ (κ₂ * CCL) * (Real.sqrt X0 * Real.sqrt X2)
          + (κ₂ * CCL) * (Real.sqrt X1 * Real.sqrt X2) := by
      have h := mul_le_mul_of_nonneg_right hν2 (Real.sqrt_nonneg X2)
      have hsq : (Real.sqrt X2) ^ 2 = X2 := Real.sq_sqrt hX2
      nlinarith [h, hsq]
    -- Young
    have hp1 : (c₁ * (α * κ₁ * CCL)) * (Real.sqrt X0 * Real.sqrt X1)
        ≤ (cc / 8) * X0 + (2 * (c₁ * (α * κ₁ * CCL)) ^ 2 / cc) * X1 := by
      have h := young_absorb_T (lam := cc / 8) (p := c₁ * (α * κ₁ * CCL)) (x := X0) (y := X1)
        (div_pos ht.hcc (by norm_num)) hX0 hX1
      have heq : (c₁ * (α * κ₁ * CCL)) ^ 2 / (4 * (cc / 8))
          = 2 * (c₁ * (α * κ₁ * CCL)) ^ 2 / cc := by field_simp; ring
      rwa [heq] at h
    have hp2 : (c₂ * (κ₂ * CCL)) * (Real.sqrt X0 * Real.sqrt X2)
        ≤ (cc / 8) * X0 + (2 * (c₂ * (κ₂ * CCL)) ^ 2 / cc) * X2 := by
      have h := young_absorb_T (lam := cc / 8) (p := c₂ * (κ₂ * CCL)) (x := X0) (y := X2)
        (div_pos ht.hcc (by norm_num)) hX0 hX2
      have heq : (c₂ * (κ₂ * CCL)) ^ 2 / (4 * (cc / 8))
          = 2 * (c₂ * (κ₂ * CCL)) ^ 2 / cc := by field_simp; ring
      rwa [heq] at h
    have hp3 : (c₂ * (κ₂ * CCL)) * (Real.sqrt X1 * Real.sqrt X2)
        ≤ (c₁ * ccL / 8) * X1 + (2 * (c₂ * (κ₂ * CCL)) ^ 2 / (c₁ * ccL)) * X2 := by
      have h := young_absorb_T (lam := c₁ * ccL / 8) (p := c₂ * (κ₂ * CCL)) (x := X1) (y := X2)
        (by positivity) hX1 hX2
      have heq : (c₂ * (κ₂ * CCL)) ^ 2 / (4 * (c₁ * ccL / 8))
          = 2 * (c₂ * (κ₂ * CCL)) ^ 2 / (c₁ * ccL) := by field_simp; ring
      rwa [heq] at h
    -- the Young tails fit in the budgets
    have hd1 : 2 * (c₁ * (α * κ₁ * CCL)) ^ 2 / cc ≤ c₁ * ccL / 8 := by
      rw [div_le_iff₀ ht.hcc]
      have h := mul_le_mul_of_nonneg_left hs1 hc₁.le
      nlinarith [h]
    have hd2 : 2 * (c₂ * (κ₂ * CCL)) ^ 2 / cc ≤ c₂ * ccL / 8 := by
      rw [div_le_iff₀ ht.hcc]
      have h := mul_le_mul_of_nonneg_left hs3 hc₂.le
      nlinarith [h]
    have hd3 : 2 * (c₂ * (κ₂ * CCL)) ^ 2 / (c₁ * ccL) ≤ c₂ * ccL / 8 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < c₁ * ccL)]
      have h := mul_le_mul_of_nonneg_left hs4 hc₂.le
      nlinarith [h]
    have hd4 : c₁ * (α * κ₁ * CCL) * X1 ≤ (c₁ * ccL / 8) * X1 := by
      have h : α * κ₁ * CCL ≤ ccL / 8 := by linarith [hs2]
      have h' : c₁ * (α * κ₁ * CCL) ≤ c₁ * ccL / 8 := by
        have := mul_le_mul_of_nonneg_left h hc₁.le
        linarith [this]
      exact mul_le_mul_of_nonneg_right h' hX1
    -- the two error terms, fully estimated
    have herr1 : c₁ * (CCL * Real.sqrt (Work.Spaces.HkSq α n
          (Work.FTS.CoercivityFix.Transfer.E1 α f)) * Real.sqrt X1)
        ≤ (cc / 8) * X0 + (c₁ * ccL / 4) * X1 := by
      have h4 : c₁ * (c₁ * (α * κ₁ * CCL) * X1) ≤ c₁ * ((c₁ * ccL / 8) * X1) :=
        mul_le_mul_of_nonneg_left hd4 hc₁.le
      calc c₁ * (CCL * Real.sqrt (Work.Spaces.HkSq α n
              (Work.FTS.CoercivityFix.Transfer.E1 α f)) * Real.sqrt X1)
          ≤ c₁ * ((α * κ₁ * CCL) * (Real.sqrt X0 * Real.sqrt X1) + (α * κ₁ * CCL) * X1) :=
            mul_le_mul_of_nonneg_left hn1' hc₁.le
        _ = (c₁ * (α * κ₁ * CCL)) * (Real.sqrt X0 * Real.sqrt X1)
              + c₁ * (α * κ₁ * CCL) * X1 := by ring
        _ ≤ ((cc / 8) * X0 + (2 * (c₁ * (α * κ₁ * CCL)) ^ 2 / cc) * X1)
              + (c₁ * ccL / 8) * X1 := add_le_add hp1 hd4
        _ ≤ ((cc / 8) * X0 + (c₁ * ccL / 8) * X1) + (c₁ * ccL / 8) * X1 := by
            have h3 := mul_le_mul_of_nonneg_right hd1 hX1
            linarith [h3]
        _ = (cc / 8) * X0 + (c₁ * ccL / 4) * X1 := by ring
    have herr2 : c₂ * (CCL * Real.sqrt (Work.Spaces.HkSq α n
          (Work.FTS.CoercivityFix.Transfer.E2 α f)) * Real.sqrt X2)
        ≤ (cc / 8) * X0 + (c₁ * ccL / 8) * X1 + (c₂ * ccL / 4) * X2 := by
      have h4 : (2 * (c₂ * (κ₂ * CCL)) ^ 2 / cc) * X2 ≤ (c₂ * ccL / 8) * X2 :=
        mul_le_mul_of_nonneg_right hd2 hX2
      have h5 : (2 * (c₂ * (κ₂ * CCL)) ^ 2 / (c₁ * ccL)) * X2 ≤ (c₂ * ccL / 8) * X2 :=
        mul_le_mul_of_nonneg_right hd3 hX2
      calc c₂ * (CCL * Real.sqrt (Work.Spaces.HkSq α n
              (Work.FTS.CoercivityFix.Transfer.E2 α f)) * Real.sqrt X2)
          ≤ c₂ * ((κ₂ * CCL) * (Real.sqrt X0 * Real.sqrt X2)
              + (κ₂ * CCL) * (Real.sqrt X1 * Real.sqrt X2)) :=
            mul_le_mul_of_nonneg_left hn2' hc₂.le
        _ = (c₂ * (κ₂ * CCL)) * (Real.sqrt X0 * Real.sqrt X2)
              + (c₂ * (κ₂ * CCL)) * (Real.sqrt X1 * Real.sqrt X2) := by ring
        _ ≤ ((cc / 8) * X0 + (2 * (c₂ * (κ₂ * CCL)) ^ 2 / cc) * X2)
              + ((c₁ * ccL / 8) * X1 + (2 * (c₂ * (κ₂ * CCL)) ^ 2 / (c₁ * ccL)) * X2) :=
            add_le_add hp2 hp3
        _ ≤ ((cc / 8) * X0 + (c₂ * ccL / 8) * X2)
              + ((c₁ * ccL / 8) * X1 + (c₂ * ccL / 8) * X2) := add_le_add
            (add_le_add le_rfl h4) (add_le_add le_rfl h5)
        _ = (cc / 8) * X0 + (c₁ * ccL / 8) * X1 + (c₂ * ccL / 4) * X2 := by ring
    -- the two lower bounds on the differentiated slots
    have hN1 : -(IP (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f))
        ≤ CCL * Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f))
            * Real.sqrt X1 :=
      le_trans (neg_le_abs _) hS1
    have hN2 : -(IP (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f))
        ≤ CCL * Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f))
            * Real.sqrt X2 :=
      le_trans (neg_le_abs _) hS2
    have hstep1 : c₁ * IP (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)
        ≥ c₁ * (ccL * X1)
          - c₁ * (CCL * Real.sqrt (Work.Spaces.HkSq α n
              (Work.FTS.CoercivityFix.Transfer.E1 α f)) * Real.sqrt X1) := by
      rw [e₁]
      have h1 : c₁ * (ccL * X1)
          ≤ c₁ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f))
              (Work.Spaces.Dth f) :=
        mul_le_mul_of_nonneg_left hB1 hc₁.le
      have h2 : -(c₁ * (CCL * Real.sqrt (Work.Spaces.HkSq α n
              (Work.FTS.CoercivityFix.Transfer.E1 α f)) * Real.sqrt X1))
          ≤ c₁ * IP (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f) := by
        have := mul_le_mul_of_nonneg_left hN1 hc₁.le
        linarith
      linarith
    have hstep2 : c₂ * IP (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f)
        ≥ c₂ * (ccL * X2)
          - c₂ * (CCL * Real.sqrt (Work.Spaces.HkSq α n
              (Work.FTS.CoercivityFix.Transfer.E2 α f)) * Real.sqrt X2) := by
      rw [e₂]
      have h1 : c₂ * (ccL * X2)
          ≤ c₂ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
              (Work.Spaces.Dz f) :=
        mul_le_mul_of_nonneg_left hB2 hc₂.le
      have h2 : -(c₂ * (CCL * Real.sqrt (Work.Spaces.HkSq α n
              (Work.FTS.CoercivityFix.Transfer.E2 α f)) * Real.sqrt X2))
          ≤ c₂ * IP (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f) := by
        have := mul_le_mul_of_nonneg_left hN2 hc₂.le
        linarith
      linarith
    have hIP : IP (Work.Coercivity.LGammaT α f) f
          + c₁ * IP (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)
          + c₂ * IP (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f)
        ≥ cc * X0 + c₁ * ccL * X1 + c₂ * ccL * X2
          - (c₁ * (CCL * Real.sqrt (Work.Spaces.HkSq α n
                (Work.FTS.CoercivityFix.Transfer.E1 α f)) * Real.sqrt X1)
              + c₂ * (CCL * Real.sqrt (Work.Spaces.HkSq α n
                (Work.FTS.CoercivityFix.Transfer.E2 α f)) * Real.sqrt X2)) := by
      linarith [hA, hstep1, hstep2]
    have hsurv : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4))
          * (X0 + X1 + X2)
        ≤ cc * X0 + c₁ * ccL * X1 + c₂ * ccL * X2
          - (c₁ * (CCL * Real.sqrt (Work.Spaces.HkSq α n
                (Work.FTS.CoercivityFix.Transfer.E1 α f)) * Real.sqrt X1)
              + c₂ * (CCL * Real.sqrt (Work.Spaces.HkSq α n
                (Work.FTS.CoercivityFix.Transfer.E2 α f)) * Real.sqrt X2)) := by
      have h0 : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) ≤ 3 * cc / 4 :=
        min_le_left _ _
      have h1 : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4))
          ≤ 5 * c₁ * ccL / 8 := le_trans (min_le_right _ _) (min_le_left _ _)
      have h2 : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4))
          ≤ 3 * c₂ * ccL / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
      have e0 : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) * X0
          ≤ (3 * cc / 4) * X0 := mul_le_mul_of_nonneg_right h0 hX0
      have e1' : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) * X1
          ≤ (5 * c₁ * ccL / 8) * X1 := mul_le_mul_of_nonneg_right h1 hX1
      have e2' : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) * X2
          ≤ (3 * c₂ * ccL / 4) * X2 := mul_le_mul_of_nonneg_right h2 hX2
      have hexp : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4))
            * (X0 + X1 + X2)
          = min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) * X0
            + min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) * X1
            + min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) * X2 := by ring
      rw [hexp]
      linarith [e0, e1', e2', herr1, herr2]
    have hYD : Y ≤ D * (X0 + X1 + X2) := by
      have h := hnormD f hf
      rw [hYdef, hX0def, hX1def, hX2def]
      exact h
    have hscale : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) / D * Y
        ≤ min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4))
            * (X0 + X1 + X2) := by
      have hc0 : 0 ≤ min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) / D :=
        le_of_lt hcc'
      calc min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) / D * Y
          ≤ min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) / D
              * (D * (X0 + X1 + X2)) := mul_le_mul_of_nonneg_left hYD hc0
        _ = min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4))
              * (X0 + X1 + X2) := by field_simp
    rw [Work.Coercivity.HkIPStep]
    exact le_trans hscale (le_trans hsurv hIP)

end Work.FTS.StrongEps.EpsE4Thr.TransO
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.step_pointwise_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.StrongEps.StepFacts

set_option maxHeartbeats 2000000




end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.up_four_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `up_four_open` — the `up` clause of the level-four coercivity, on the **open** class

`Work.FTS.StrongEps.EpsE4Thr.RegQo α k f = SmoothOpen f ∧ HkMem α k f ∧ BdryTraces α k f`
is the open-quadrant version of the frozen `Work.FTS.Nonlin.RegQ`: it asks for `C^∞` of `f`
on the open quadrant `(0,∞) × (0,π/2)` instead of the *strip* `(-1,∞) × (0,π/2)` of
`LocData.SmoothQuad`.  The weaker class is the one the level-four barrier can actually be run
against (`OpenBarrier.coerAdmO_slice_JfamP`), and it is exactly what the interior
integrations by parts of the coercivity consume.

This file supplies the upper comparison of the level-four inner product

  `IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α = HkIPStep c₁'' c₂'' (HkIPStep c₁' c₂'
      (HkIPStep c₁ c₂ (H1IP α)))`

on `RegQo α 5`, i.e. the open-class analogue of `Assembly.V_bounds.up_four` (which is stated
on `RegQ α 5`).  It is one of the four analytic clauses from which
`UnifIPOIP4.unifIPO_IP4_of_open_clauses` assembles the open coercivity interface `UnifIPO`.

## The proof

The recursion is the frozen one, transcribed onto the open class.  One step of the recursion
(`up_step_SO`) trades one level of the class for one level of the norm: if `IP ≼ Cst·|·|²_{ℋⁿ}`
on `{SmoothOpen} ∩ ℋ^{n+1}`, then

  `HkIPStep c₁ c₂ IP ≼ (3·Cst·max 1 (max c₁ c₂))·|·|²_{ℋ^{n+1}}`

on `{SmoothOpen} ∩ ℋ^{n+2}`, because each of the three slots of `HkIPStep` is one order lower
(`normSub_SO`), and the class of the slots is preserved by `D_θ` (`SmoothOpen.Dth`, and
`ℋ^{n+2} ↦ ℋ^{n+1}` by `IPGen.HkMem_descent`) and by `D_z` (`SmoothOpen.Dz`,
`IPGen.HkMem_descent`).  The base of the recursion is the level-`1` comparison

  `H1IP α f f ≤ 10^22·|f|²_{ℋ¹}`  (`H1IP_upper_open`),

which needs the open `ℋ¹`-identity `HkSq_one_eq_SO` and the comparison
`Ef f ≤ EfEta f` on the open honest class (`ef_le_efEta_open`).

Three steps of the recursion (`n = 1, 2, 3`) therefore give the conclusion on
`{SmoothOpen} ∩ ℋ⁵`, and `RegQo α 5` supplies exactly those two clauses.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "IP2" => Work.FTS.CoercivityFix.Assembly.IP2
local notation "IP3" => Work.FTS.CoercivityFix.Assembly.IP3
local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-- **One step of the upper comparison, on the open class.**  If the level-`n` pairing is
dominated by `Cst·|v|²_{ℋⁿ}` on `SmoothOpen ∩ ℋ^{n+1}`, then `HkIPStep c₁ c₂ IP` is dominated
by `(3·Cst·max 1 (max c₁ c₂))·|v|²_{ℋ^{n+1}}` on `SmoothOpen ∩ ℋ^{n+2}`.

The three summands of `HkIPStep` are handled by the one-sided `ℋⁿ`-vs-`ℋ^{n+1}` comparison
`hnorm` of the three slots (`normSub_SO` in the applications), the regularity of the slots
coming from `SmoothOpen.Dth`/`SmoothOpen.Dz` and the descent `IPGen.HkMem_descent`.  With
positive coefficients the loss of the step is `3·max 1 (max c₁ c₂)`. -/
theorem up_step_SO {α : ℝ} (hα : 0 < α) {n : ℕ}
    {IP : Fn → Fn → ℝ} {c₁ c₂ Cst : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hCst : 0 < Cst)
    (hnorm : ∀ v : Fn, Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α (n + 1) v →
      Work.Spaces.HkSq α n v ≤ Work.Spaces.HkSq α (n + 1) v ∧
        Work.Spaces.HkSq α n (Work.Spaces.Dth v) ≤ Work.Spaces.HkSq α (n + 1) v ∧
        Work.Spaces.HkSq α n (Work.Spaces.Dz v) ≤ Work.Spaces.HkSq α (n + 1) v)
    (h : ∀ v : Fn, Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α (n + 1) v →
      IP v v ≤ Cst * Work.Spaces.HkSq α n v) :
    ∀ v : Fn, Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α (n + 2) v →
      Work.Coercivity.HkIPStep c₁ c₂ IP v v
        ≤ (3 * Cst * max 1 (max c₁ c₂)) * Work.Spaces.HkSq α (n + 1) v := by
  intro v hs hm
  have hmv : Work.Spaces.HkMem α (n + 1) v :=
    Work.FTS.OpenPkg.HkMem_mono_open hs (n + 1) (by omega) hm
  obtain ⟨-, hmd, hmz⟩ :=
    Work.FTS.IPGen.HkMem_descent (α := α) (k := n + 1) (by linarith) hs hm
  have h0 := h v hs hmv
  have h1 := h (Work.Spaces.Dth v) hs.Dth hmd
  have h2 := h (Work.Spaces.Dz v) hs.Dz hmz
  obtain ⟨hn0, hn1, hn2⟩ := hnorm v hs hmv
  have hT : 0 ≤ Work.Spaces.HkSq α (n + 1) v := Work.Spaces.HkSq_nonneg α (n + 1) v
  have e0 : IP v v ≤ Cst * Work.Spaces.HkSq α (n + 1) v :=
    le_trans h0 (mul_le_mul_of_nonneg_left hn0 hCst.le)
  have e1 : IP (Work.Spaces.Dth v) (Work.Spaces.Dth v)
      ≤ Cst * Work.Spaces.HkSq α (n + 1) v :=
    le_trans h1 (mul_le_mul_of_nonneg_left hn1 hCst.le)
  have e2 : IP (Work.Spaces.Dz v) (Work.Spaces.Dz v)
      ≤ Cst * Work.Spaces.HkSq α (n + 1) v :=
    le_trans h2 (mul_le_mul_of_nonneg_left hn2 hCst.le)
  have hm1 : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
  have hm2 : c₁ ≤ max 1 (max c₁ c₂) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hm3 : c₂ ≤ max 1 (max c₁ c₂) := le_trans (le_max_right _ _) (le_max_right _ _)
  rw [Work.Coercivity.HkIPStep]
  have hcomb : IP v v + c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v)
      + c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v)
      ≤ (Cst * (1 + c₁ + c₂)) * Work.Spaces.HkSq α (n + 1) v := by
    have hc1 : c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v)
        ≤ c₁ * (Cst * Work.Spaces.HkSq α (n + 1) v) :=
      mul_le_mul_of_nonneg_left e1 hc₁.le
    have hc2 : c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v)
        ≤ c₂ * (Cst * Work.Spaces.HkSq α (n + 1) v) :=
      mul_le_mul_of_nonneg_left e2 hc₂.le
    nlinarith [e0, hc1, hc2, hT, hCst, hc₁, hc₂]
  refine le_trans hcomb ?_
  have hcoef : Cst * (1 + c₁ + c₂) ≤ 3 * Cst * max 1 (max c₁ c₂) := by
    nlinarith [hCst, hm1, hm2, hm3]
  exact mul_le_mul_of_nonneg_right hcoef hT

/-- **The upper comparison of the level-four inner product on the open coercivity class** —
the open-class analogue of `Assembly.up_four`.  The constant is explicit:
`3·(3·(3·10^22·max 1 (max c₁ c₂))·max 1 (max c₁' c₂'))·max 1 (max c₁'' c₂'')`, the three
factors being the losses of the three steps of the recursion. -/
theorem up_four_open {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₁' : 0 < c₁') (h₂' : 0 < c₂')
    (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ Cup : ℝ, 0 < Cup ∧ ∀ (α : ℝ), 0 < α → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.EpsE4Thr.RegQo α 5 f →
        Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f
          ≤ Cup * Work.Spaces.HkSq α 4 f := by
  set D₁ : ℝ := 3 * (10 : ℝ) ^ 22 * max 1 (max c₁ c₂) with hD₁
  set D₂ : ℝ := 3 * D₁ * max 1 (max c₁' c₂') with hD₂
  set D₃ : ℝ := 3 * D₂ * max 1 (max c₁'' c₂'') with hD₃
  have hm₁ : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
  have hm₂ : (1 : ℝ) ≤ max 1 (max c₁' c₂') := le_max_left _ _
  have hm₃ : (1 : ℝ) ≤ max 1 (max c₁'' c₂'') := le_max_left _ _
  have hD₁pos : 0 < D₁ := by rw [hD₁]; nlinarith [hm₁]
  have hD₂pos : 0 < D₂ := by rw [hD₂]; nlinarith [hD₁pos, hm₂]
  have hD₃pos : 0 < D₃ := by rw [hD₃]; nlinarith [hD₂pos, hm₃]
  refine ⟨D₃, hD₃pos, ?_⟩
  intro α hα f hf
  -- the base of the recursion: the level-`1` upper comparison on `SmoothOpen ∩ ℋ¹`
  have hbase : ∀ v : Fn, Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α 1 v →
      Work.Coercivity.H1IP α v v ≤ (10 : ℝ) ^ 22 * Work.Spaces.HkSq α 1 v :=
    fun v hs hm => H1IP_upper_open (α := α) hα hs hm (ef_le_efEta_open hs hm)
  -- three steps of the recursion, `n = 1, 2, 3`
  have u2 := up_step_SO (α := α) hα (n := 1)
    (IP := Work.Coercivity.H1IP α) h₁ h₂ (by norm_num : (0 : ℝ) < 10 ^ 22)
    (fun v hs hm => normSub_SO hα hs hm)
    (fun v hs hm => hbase v hs (Work.FTS.OpenPkg.HkMem_mono_open hs 1 (by norm_num) hm))
  have u3 := up_step_SO (α := α) hα (n := 2)
    (IP := IP2 c₁ c₂ α) h₁' h₂' hD₁pos
    (fun v hs hm => normSub_SO hα hs hm)
    (fun v hs hm => by rw [hD₁]; exact u2 v hs hm)
  have u4 := up_step_SO (α := α) hα (n := 3)
    (IP := IP3 c₁ c₂ c₁' c₂' α) h₁'' h₂'' hD₂pos
    (fun v hs hm => normSub_SO hα hs hm)
    (fun v hs hm => by rw [hD₂]; exact u3 v hs hm)
  exact u4 f hf.1 hf.2.1

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.GlueParts.RegGlue =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.StrongGlobal (P3 uncurry3 concat concat_apply_of_le concat_apply_of_gt)

/-! ## The slabs of the fake-time quadrant -/

/-- The closed slab `(0,∞) × (0,π/2) × [a,b]` of the fake-time quadrant. -/
private def Qslab (a b : ℝ) : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc a b

private theorem mem_Qslab {a b : ℝ} {q : P3} :
    q ∈ Qslab a b ↔ 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi / 2 ∧ a ≤ q.2.2 ∧ q.2.2 ≤ b := by
  simp only [Qslab, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
  tauto

/-! ## The shift of a one-sided derivative -/

private theorem hasDerivWithinAt_comp_sub_Icc_prv {f : ℝ → ℝ} {f' x a c : ℝ}
    (h : HasDerivWithinAt f f' (Set.Icc 0 c) (x - a)) :
    HasDerivWithinAt (fun y : ℝ => f (y - a)) f' (Set.Icc a (a + c)) x := by
  have hg : HasDerivWithinAt (fun y : ℝ => y - a) 1 (Set.Icc a (a + c)) x :=
    ((hasDerivAt_id (x := x)).sub_const a).hasDerivWithinAt
  have hst : MapsTo (fun y : ℝ => y - a) (Set.Icc a (a + c)) (Set.Icc 0 c) :=
    fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcomp := h.comp x hg hst
  rw [show (f ∘ fun y : ℝ => y - a) = (fun y : ℝ => f (y - a)) from rfl, mul_one] at hcomp
  exact hcomp

/-! ## The joint `C¹`-regularity of the concatenation -/

/-- The joint `C¹`-regularity clause of `EpsReg` for the concatenated family: the pieces are `C¹`
on the closed slabs `[0,t]` and `[0,δ]`, agree at the junction as functions of `(z,θ)` and have
the same one-sided fake-time derivative `R` there. -/
private theorem contDiffOn_concat_shiftFam {G H : Fam} {t δ : ℝ} {R : Fn} (hδ : 0 < δ)
    (hG : ContDiffOn ℝ 1 (uncurry3 G) (Qslab 0 t))
    (hH : ContDiffOn ℝ 1 (uncurry3 H) (Qslab 0 δ))
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ 0)
    (hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t)
    (hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc 0 δ) 0) :
    ContDiffOn ℝ 1 (uncurry3 (concat G (shiftFam H t) t)) (Qslab 0 (t + δ)) := by
  have hHt : ContDiffOn ℝ 1 (uncurry3 (shiftFam H t)) (Qslab t (t + δ)) :=
    contDiffOn_shiftFam (H := H) (t := t) (δ := δ) hH
  intro q hq
  obtain ⟨hz, hθ0, hθ1, hτ0, hτ1⟩ := mem_Qslab.mp hq
  rcases lt_trichotomy q.2.2 t with hlt | heq | hgt
  · -- strictly before the junction: the concatenation agrees with `G`
    have hqUG : q ∈ Qslab 0 t := mem_Qslab.mpr ⟨hz, hθ0, hθ1, hτ0, le_of_lt hlt⟩
    have hUG : Qslab 0 t ∈ 𝓝[Qslab 0 (t + δ)] q := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨{y : P3 | y.2.2 < t}, ?_, ?_⟩
      · exact (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const).mem_nhds hlt
      · rintro y ⟨hylt, hyU⟩
        obtain ⟨h1, h2, h3, h4, -⟩ := mem_Qslab.mp hyU
        exact mem_Qslab.mpr ⟨h1, h2, h3, h4, le_of_lt hylt⟩
    refine ContDiffWithinAt.congr_of_eventuallyEq
      (f₁ := uncurry3 (concat G (shiftFam H t) t))
      ((hG.contDiffWithinAt hqUG).mono_of_mem_nhdsWithin hUG) ?_ ?_
    · show uncurry3 (concat G (shiftFam H t) t) =ᶠ[𝓝[Qslab 0 (t + δ)] q] uncurry3 G
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ y in 𝓝 (q : P3), y.2.2 < t from
          (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const).mem_nhds hlt)]
        with y hy
      exact concat_apply_of_le (le_of_lt hy)
    · exact concat_apply_of_le (le_of_lt hlt)
  · -- at the junction: the one-sided junction glue
    exact contDiffWithinAt_concat_halfslab (G := G) (H := shiftFam H t) (R := R) (q := q)
      hδ hG hHt (fun z θ hz' hθ0' hθ1' => by
        rw [Work.FTS.StrongEps.shiftFam_apply, sub_self]
        exact hval z θ hz' hθ0' hθ1') hderG
      (fun z θ hz' hθ0' hθ1' => hasDerivWithinAt_comp_sub_Icc_prv (f := fun s => H z θ s)
        (a := t) (c := δ) (x := t) (by simpa using hderH z θ hz' hθ0' hθ1')) hq heq
  · -- strictly after the junction: the concatenation agrees with the shifted `H`
    have hqUH : q ∈ Qslab t (t + δ) := mem_Qslab.mpr ⟨hz, hθ0, hθ1, le_of_lt hgt, hτ1⟩
    have hmemUH : Qslab t (t + δ) ∈ 𝓝[Qslab 0 (t + δ)] q := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨{y : P3 | t < y.2.2}, ?_, ?_⟩
      · exact (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).mem_nhds hgt
      · rintro y ⟨hygt, hyU⟩
        obtain ⟨h1, h2, h3, -, h5⟩ := mem_Qslab.mp hyU
        exact mem_Qslab.mpr ⟨h1, h2, h3, le_of_lt hygt, h5⟩
    refine ContDiffWithinAt.congr_of_eventuallyEq
      (f₁ := uncurry3 (concat G (shiftFam H t) t))
      ((hHt.contDiffWithinAt hqUH).mono_of_mem_nhdsWithin hmemUH) ?_ ?_
    · show uncurry3 (concat G (shiftFam H t) t) =ᶠ[𝓝[Qslab 0 (t + δ)] q]
        uncurry3 (shiftFam H t)
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ y in 𝓝 (q : P3), t < y.2.2 from
          (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).mem_nhds hgt)]
        with y hy
      exact concat_apply_of_gt hy
    · exact concat_apply_of_gt hgt


end Work.FTS.StrongEps.GlueParts
end
-- ===== merged: Submission.Work.FTS.StrongEps.StrongEpsP.RegGlueP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StrongEpsP

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.StrongGlobal (P3 uncurry3 concat concat_apply_of_le concat_apply_of_gt)

/-! ## The slabs of the fake-time quadrant -/

/-- The closed slab `(0,∞) × (0,π/2) × [a,b]` of the fake-time quadrant (the domain of the joint
`C¹`-clause of `EpsRegP`). -/
def Qslab (a b : ℝ) : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc a b

theorem mem_Qslab {a b : ℝ} {q : P3} :
    q ∈ Qslab a b ↔ 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi / 2 ∧ a ≤ q.2.2 ∧ q.2.2 ≤ b := by
  simp only [Qslab, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
  tauto

/-! ## The shift of a one-sided derivative -/

/-! ## The joint `C¹`-regularity of the concatenation -/

/-- The joint `C¹`-regularity clause of `EpsRegP` for the concatenated family: the pieces are `C¹`
on the closed slabs `[0,t]` and `[0,δ]`, agree at the junction as functions of `(z,θ)` and have
the same one-sided fake-time derivative `R` there, hence `uncurry3 (concat G (shiftFam H t) t)` is
`C¹` on `(0,∞) × (0,π/2) × [0,t+δ]`.  The junction `t` is a *common boundary* of the two slabs, so
this is `GlueParts.contDiffWithinAt_concat_halfslab` (at the junction) combined with the two
off-junction reductions to `hG` resp. `contDiffOn_shiftFam hH`. -/
theorem contDiffOn_concat_shiftFam {G H : Fam} {t δ : ℝ} {R : Fn} (hδ : 0 < δ)
    (hG : ContDiffOn ℝ 1 (uncurry3 G) (Qslab 0 t))
    (hH : ContDiffOn ℝ 1 (uncurry3 H) (Qslab 0 δ))
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ 0)
    (hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t)
    (hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc 0 δ) 0) :
    ContDiffOn ℝ 1 (uncurry3 (concat G (shiftFam H t) t)) (Qslab 0 (t + δ)) := by
  have hHt : ContDiffOn ℝ 1 (uncurry3 (shiftFam H t)) (Qslab t (t + δ)) :=
    Work.FTS.StrongEps.GlueParts.contDiffOn_shiftFam (H := H) (t := t) (δ := δ) hH
  intro q hq
  obtain ⟨hz, hθ0, hθ1, hτ0, hτ1⟩ := mem_Qslab.mp hq
  rcases lt_trichotomy q.2.2 t with hlt | heq | hgt
  · -- strictly before the junction: the concatenation agrees with `G`
    have hqUG : q ∈ Qslab 0 t := mem_Qslab.mpr ⟨hz, hθ0, hθ1, hτ0, le_of_lt hlt⟩
    have hUG : Qslab 0 t ∈ 𝓝[Qslab 0 (t + δ)] q := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨{y : P3 | y.2.2 < t}, ?_, ?_⟩
      · exact (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const).mem_nhds hlt
      · rintro y ⟨hylt, hyU⟩
        obtain ⟨h1, h2, h3, h4, -⟩ := mem_Qslab.mp hyU
        exact mem_Qslab.mpr ⟨h1, h2, h3, h4, le_of_lt hylt⟩
    refine ContDiffWithinAt.congr_of_eventuallyEq
      (f₁ := uncurry3 (concat G (shiftFam H t) t))
      ((hG.contDiffWithinAt hqUG).mono_of_mem_nhdsWithin hUG) ?_ ?_
    · show uncurry3 (concat G (shiftFam H t) t) =ᶠ[𝓝[Qslab 0 (t + δ)] q] uncurry3 G
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ y in 𝓝 (q : P3), y.2.2 < t from
          (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const).mem_nhds hlt)]
        with y hy
      exact concat_apply_of_le (le_of_lt hy)
    · exact concat_apply_of_le (le_of_lt hlt)
  · -- at the junction: the one-sided junction glue
    exact Work.FTS.StrongEps.GlueParts.contDiffWithinAt_concat_halfslab (G := G)
      (H := shiftFam H t) (R := R) (q := q)
      hδ hG hHt (fun z θ hz' hθ0' hθ1' => by
        rw [Work.FTS.StrongEps.shiftFam_apply, sub_self]
        exact hval z θ hz' hθ0' hθ1') hderG
      (fun z θ hz' hθ0' hθ1' => hasDerivWithinAt_comp_sub_Icc (f := fun s => H z θ s)
        (a := t) (c := δ) (x := t) (by simpa using hderH z θ hz' hθ0' hθ1')) hq heq
  · -- strictly after the junction: the concatenation agrees with the shifted `H`
    have hqUH : q ∈ Qslab t (t + δ) := mem_Qslab.mpr ⟨hz, hθ0, hθ1, le_of_lt hgt, hτ1⟩
    have hmemUH : Qslab t (t + δ) ∈ 𝓝[Qslab 0 (t + δ)] q := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨{y : P3 | t < y.2.2}, ?_, ?_⟩
      · exact (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).mem_nhds hgt
      · rintro y ⟨hygt, hyU⟩
        obtain ⟨h1, h2, h3, -, h5⟩ := mem_Qslab.mp hyU
        exact mem_Qslab.mpr ⟨h1, h2, h3, le_of_lt hygt, h5⟩
    refine ContDiffWithinAt.congr_of_eventuallyEq
      (f₁ := uncurry3 (concat G (shiftFam H t) t))
      ((hHt.contDiffWithinAt hqUH).mono_of_mem_nhdsWithin hmemUH) ?_ ?_
    · show uncurry3 (concat G (shiftFam H t) t) =ᶠ[𝓝[Qslab 0 (t + δ)] q]
        uncurry3 (shiftFam H t)
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ y in 𝓝 (q : P3), t < y.2.2 from
          (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).mem_nhds hgt)]
        with y hy
      exact concat_apply_of_gt hy
    · exact concat_apply_of_gt hgt

/-! ## The regularity glue of the `P₀`-scheme -/

theorem RegGlueP {α ε t δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {G H : Work.FTS.Galerkin.Fam}
    {R : Work.FTS.Galerkin.Fn} (ht : 0 ≤ t) (hδ : 0 < δ)
    (hG : Work.FTS.StrongEps.EpsRegP α ρ ε t G) (hH : Work.FTS.StrongEps.EpsRegP α ρ ε δ H)
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ 0)
    (hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t)
    (hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc 0 δ) 0) :
    Work.FTS.StrongEps.EpsRegP α ρ ε (t + δ)
      (Work.FTS.StrongGlobal.concat G (Work.FTS.StrongEps.shiftFam H t) t) := by
  refine ⟨?_, ?_⟩
  · -- the joint `C¹`-regularity of the concatenation
    exact contDiffOn_concat_shiftFam (G := G) (H := H) (t := t) (δ := δ) (R := R) hδ
      hG.1 hH.1 hval hderG hderH
  · -- the datum bookkeeping: the slices are those of the two pieces
    intro τ hτ
    rcases le_or_gt τ t with hle | hlt
    · rw [Work.FTS.StrongGlobal.slice_concat_of_le (G := G) (H := shiftFam H t) (τ₀ := t)
        (τ := τ) hle]
      exact hG.2 τ ⟨hτ.1, hle⟩
    · rw [Work.FTS.StrongGlobal.slice_concat_of_gt (G := G) (H := shiftFam H t) (τ₀ := t)
        (τ := τ) hlt, Work.FTS.StrongEps.slice_shiftFam]
      exact hH.2 (τ - t) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩

end Work.FTS.StrongEps.StrongEpsP
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.Mth6_integral_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

open MeasureTheory Set
open scoped Real Topology

/-- The pointwise comparison behind `Mth6_integral_bound`, stated in the `Mth6` vocabulary:
the integrand of `Mth6 α` is dominated by `K · radAngInt α θ` with a single `K` for all
`α ∈ (0,1]`.  (`L3Aux.radAngInt α θ = sin(2θ)^{-η} + α²Γ(θ)²sin(2θ)^{-γ}`.) -/
theorem Mth6_le_radAngInt : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc 0 1, ∀ θ ∈ Work.Spaces.Iθ,
    Work.FTS.StrongPersist.Mth6 α θ
      ≤ K * Work.FTS.StrongPersist.L3Aux.radAngInt α θ := by
  obtain ⟨K, hKpos, hang⟩ := Work.FTS.StrongPersist.L6Aux.gamCoef_angBlk6
  exact ⟨K, hKpos, fun α hα θ hθ => hang α hα.1 hα.2 θ hθ⟩

theorem Mth6_integral_bound : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ) ≤ C := by
  obtain ⟨K, hKpos, hpoint⟩ := Mth6_le_radAngInt
  obtain ⟨M, _hMpos, hbound⟩ := Work.FTS.StrongPersist.L3Aux.radAngInt_bound
  refine ⟨max 1 (K * M), lt_max_of_lt_left one_pos, fun α hα => ?_⟩
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hintM : IntegrableOn (Work.FTS.StrongPersist.Mth6 α) Work.Spaces.Iθ :=
    Work.FTS.StrongPersist.Mth6_integrable hα0 hα1
  obtain ⟨hintR, hRbd⟩ := hbound α hα0 hα1
  have hintKR : IntegrableOn (fun θ => K * Work.FTS.StrongPersist.L3Aux.radAngInt α θ)
      Work.Spaces.Iθ := hintR.const_mul K
  calc (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ)
      ≤ ∫ θ in Work.Spaces.Iθ, K * Work.FTS.StrongPersist.L3Aux.radAngInt α θ :=
        integral_mono_ae hintM hintKR
          (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpoint α hα θ hθ))
    _ = K * ∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.radAngInt α θ :=
        integral_const_mul K _
    _ ≤ K * M := mul_le_mul_of_nonneg_left hRbd hKpos.le
    _ ≤ max 1 (K * M) := le_max_right _ _

end Work.FTS.StrongPersist.H6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.radBlk_le7 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `radBlk_le7` — the level-six weighted `L²`-bound for the radial block `ρ · L₁₂(f)`

`L₁₂(f)` is a function of the radial variable `z` alone.  For a radial multiplier
`ρ : ℝ → ℝ` that is `C⁶` on `(0,∞)` with bounded `Zop`-jets of order `≤ 6` (`Zop u = z u'`),
this module bounds the full level-six weighted energy of the radial product
`z ↦ ρ(z) · L₁₂(f)(z)`:

  `∑_{q ≤ 6} (D_z^q (ρ · L₁₂f)(z) · w(z))²` is integrable on `Iz = [0,∞)` and its integral is
  at most `C · (1 + Kρ)² · |f|²_{ℋ⁶}`.

## Route

The level-six analogue of `Work.FTS.StrongPersist.L3Rhs.VfsRadSlotBound` (the same statement
at level four).  Since the product is independent of `θ`, `Zop_slice` identifies the slot
`D_z^q (ρ · L₁₂f)(z)` with the one-dimensional `Zop^[q]` applied to the radial profile, and
the one-variable Leibniz rule `DzIter_mul_of_contDiffOn` expands

  `D_z^q (ρ · L₁₂f)(z) = ∑_{b ≤ q} C(q,b) · (Zop^[b] ρ)(z) · (Zop^[q-b] L₁₂f)(z)`;

Cauchy–Schwarz in `b` (the multiplier coefficients against the `L₁₂ f`-slots; the index shift
`b ↦ q - b` is avoided by bounding each `(Zop^[q-b] L₁₂f)²` by the whole slot sum) gives

  `(D_z^q (ρ · L₁₂f)(z))² ≤ 7 · 7 · 4⁶ · Kρ² · ∑_{b ≤ 6} (Zop^[b] L₁₂f)(z)²`,

and each of the seven slots of `L₁₂f` is the weighted `L²`-bound
`Work.FTS.StrongPersist.H6Pair6Aux.L12slotLe7`
(`∫ (D_z^b L₁₂f · w)² ≤ C₁ · |f|²_{ℋ⁶}`, `b ≤ 7`; this is where the hypothesis `HkMem α 7 f`
is used, the `q = 0` slot using `L₁₂ f 0 = 0`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## One-variable facts about `Zop u = z u'` on the open half-line -/

/-- A `C^{n+1}` function on `(0,∞)` has `C^n` derivative there. -/
private theorem contDiffOn_deriv_of_succ {n : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (n + 1) u (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ n (deriv u) (Set.Ioi (0 : ℝ)) := by
  have hfd : ContDiffOn ℝ n (fderiv ℝ u) (Set.Ioi (0 : ℝ)) :=
    hu.fderiv_of_isOpen isOpen_Ioi (by simp)
  have hev : ContDiffOn ℝ n (fun z : ℝ => (fderiv ℝ u z) 1) (Set.Ioi (0 : ℝ)) :=
    hfd.clm_apply contDiffOn_const
  refine hev.congr (fun z _ => ?_)
  rw [fderiv_apply_one_eq_deriv]

/-- A `C^{b+k}` function on `(0,∞)` has `C^k` `Zop`-iterates of order `b`. -/
private theorem contDiffOn_Zop_iter {u : ℝ → ℝ} (b k : ℕ)
    (hu : ContDiffOn ℝ (b + k) u (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ k (Work.Spaces.Zop^[b] u) (Set.Ioi (0 : ℝ)) := by
  induction b generalizing k with
  | zero => simpa using hu
  | succ b ih =>
      have hu' : ContDiffOn ℝ (b + (k + 1)) u (Set.Ioi (0 : ℝ)) :=
        hu.of_le (by exact_mod_cast (by omega : b + (k + 1) ≤ (b + 1) + k))
      have h1 : ContDiffOn ℝ (k + 1) (Work.Spaces.Zop^[b] u) (Set.Ioi (0 : ℝ)) :=
        ih (k + 1) hu'
      have h2 : ContDiffOn ℝ k (deriv (Work.Spaces.Zop^[b] u)) (Set.Ioi (0 : ℝ)) :=
        contDiffOn_deriv_of_succ h1
      have h3 : ContDiffOn ℝ k (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z)
          (Set.Ioi (0 : ℝ)) := (contDiff_id.contDiffOn).mul h2
      rw [Function.iterate_succ_apply']
      exact h3

/-- A `C^m` function on `(0,∞)` has a `C^{m-q}` `Zop`-iterate of order `q ≤ m`. -/
private theorem contDiffOn_Zop_iter_le {u : ℝ → ℝ} {m q : ℕ}
    (hu : ContDiffOn ℝ m u (Set.Ioi (0 : ℝ))) (hq : q ≤ m) :
    ContDiffOn ℝ (m - q) (Work.Spaces.Zop^[q] u) (Set.Ioi (0 : ℝ)) := by
  refine contDiffOn_Zop_iter q (m - q) ?_
  refine hu.of_le ?_
  exact_mod_cast (by omega : q + (m - q) ≤ m)

/-- The weighted slot sum `∑_{q ≤ m} (Zop^[q] G · w)²` of a `C^m` radial profile `G` is
a.e. strongly measurable for the restricted Lebesgue measure on `Iz = [0,∞)`. -/
private theorem aestronglyMeasurable_Zop_slotSum (m : ℕ) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ m G (Set.Ioi (0 : ℝ))) :
    MeasureTheory.AEStronglyMeasurable (fun z => ∑ q ∈ Finset.range (m + 1),
        (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hw : Measurable (Work.Spaces.w) := by
    unfold Work.Spaces.w
    fun_prop
  have hZcont : ∀ q ≤ m, ContinuousOn (Work.Spaces.Zop^[q] G) (Set.Ioi (0 : ℝ)) :=
    fun q hq => (contDiffOn_Zop_iter_le (u := G) (m := m) hG hq).continuousOn
  have haesmZop : MeasureTheory.AEStronglyMeasurable (fun z => ∑ q ∈ Finset.range (m + 1),
        (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h' : MeasureTheory.AEStronglyMeasurable (∑ q ∈ Finset.range (m + 1),
        fun z : ℝ => (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Finset.aestronglyMeasurable_sum (Finset.range (m + 1))
        (f := fun q z => (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (fun q hq => by
          have hqm : q ≤ m := by
            have := Finset.mem_range.mp hq
            omega
          exact (((hZcont q hqm).aestronglyMeasurable measurableSet_Ioi).pow 2).mul
            (hw.aestronglyMeasurable.pow 2))
    refine h'.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Finset.sum_apply]
  have hIoi : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    show MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))
    exact Measure.restrict_congr_set Ioi_ae_eq_Ici
  rw [← hIoi]
  exact haesmZop

/-! ## The binomial Cauchy–Schwarz bound -/

/-- Cauchy–Schwarz for the Leibniz expansion in the order produced by the rule, i.e.
`∑_{b ≤ q} C(q,b) Y_b X_{q-b}`: with `|Y j| ≤ K` for `j ≤ n` and `q ≤ n`,

  `(∑_{b ≤ q} C(q,b) Y_b X_{q-b})² ≤ ((n+1)² 4^n K²) · ∑_{b ≤ n} X_b²`.

The multiplier coefficients `C(q,b) Y_b` contribute `(q+1) 4^q K²` and the shifted slot
sequence is dominated termwise by the full slot sum, contributing a further `q + 1 ≤ n + 1`. -/
private theorem sum_sq_binom_le_gen (n : ℕ) (Y X : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hY : ∀ j ≤ n, |Y j| ≤ K) {q : ℕ} (hq : q ≤ n) :
    (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (Y b * X (q - b))) ^ 2
      ≤ (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * 4 ^ n * K ^ 2)
          * ∑ b ∈ Finset.range (n + 1), (X b) ^ 2 := by
  have hsum_eq : (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (Y b * X (q - b)))
      = ∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y b) * X (q - b) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hsum_eq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (q + 1))
      (fun b => (q.choose b : ℝ) * Y b) (fun b => X (q - b))
  have hf2 : ∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y b) ^ 2
      ≤ ((n + 1 : ℕ) : ℝ) * 4 ^ n * K ^ 2 := by
    have hterm : ∀ b ∈ Finset.range (q + 1),
        ((q.choose b : ℝ) * Y b) ^ 2 ≤ 4 ^ n * K ^ 2 := by
      intro b hb
      have hbq : b ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hc0 : (0 : ℝ) ≤ (q.choose b : ℝ) := by positivity
      have hcoef : ((q.choose b : ℝ)) ^ 2 ≤ 4 ^ n := by
        have h1 : q.choose b ≤ 2 ^ q := Nat.choose_le_two_pow q b
        have h2 : 2 ^ q ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hq
        have h3 : ((q.choose b : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
          calc ((q.choose b : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
                exact_mod_cast le_trans h1 h2
            _ = (2 : ℝ) ^ n := by push_cast; ring
        have h4 : (2 : ℝ) ^ n * (2 : ℝ) ^ n = 4 ^ n := by
          rw [← mul_pow]
          norm_num
        calc ((q.choose b : ℝ)) ^ 2 = (q.choose b : ℝ) * (q.choose b : ℝ) := by ring
          _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n := mul_self_le_mul_self hc0 h3
          _ = 4 ^ n := h4
      have hy : (Y b) ^ 2 ≤ K ^ 2 := by
        have h := hY b (by omega)
        exact sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
      calc ((q.choose b : ℝ) * Y b) ^ 2
          = ((q.choose b : ℝ)) ^ 2 * (Y b) ^ 2 := by ring
        _ ≤ 4 ^ n * K ^ 2 := mul_le_mul hcoef hy (sq_nonneg _) (by positivity)
    calc ∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y b) ^ 2
        ≤ (Finset.range (q + 1)).card • (4 ^ n * K ^ 2) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = ((q + 1 : ℕ) : ℝ) * (4 ^ n * K ^ 2) := by
          simp [Finset.card_range, nsmul_eq_mul]
      _ ≤ ((n + 1 : ℕ) : ℝ) * (4 ^ n * K ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast (by omega : q + 1 ≤ n + 1)
      _ = ((n + 1 : ℕ) : ℝ) * 4 ^ n * K ^ 2 := by ring
  have hg2 : ∑ b ∈ Finset.range (q + 1), (X (q - b)) ^ 2
      ≤ ((n + 1 : ℕ) : ℝ) * ∑ b ∈ Finset.range (n + 1), (X b) ^ 2 := by
    have hterm : ∀ b ∈ Finset.range (q + 1),
        (X (q - b)) ^ 2 ≤ ∑ i ∈ Finset.range (n + 1), (X i) ^ 2 := by
      intro b hb
      have hbq : b ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      refine Finset.single_le_sum (fun i _ => sq_nonneg _) ?_
      simp only [Finset.mem_range]
      omega
    calc ∑ b ∈ Finset.range (q + 1), (X (q - b)) ^ 2
        ≤ (Finset.range (q + 1)).card • (∑ i ∈ Finset.range (n + 1), (X i) ^ 2) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = ((q + 1 : ℕ) : ℝ) * (∑ i ∈ Finset.range (n + 1), (X i) ^ 2) := by
          simp [Finset.card_range, nsmul_eq_mul]
      _ ≤ ((n + 1 : ℕ) : ℝ) * (∑ i ∈ Finset.range (n + 1), (X i) ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun i _ => sq_nonneg _)
          exact_mod_cast (by omega : q + 1 ≤ n + 1)
  calc (∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y b) * X (q - b)) ^ 2
      ≤ (∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y b) ^ 2)
          * ∑ b ∈ Finset.range (q + 1), (X (q - b)) ^ 2 := hcs
    _ ≤ (((n + 1 : ℕ) : ℝ) * 4 ^ n * K ^ 2)
          * (((n + 1 : ℕ) : ℝ) * ∑ b ∈ Finset.range (n + 1), (X b) ^ 2) :=
        mul_le_mul hf2 hg2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by positivity)
    _ = (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * 4 ^ n * K ^ 2)
          * ∑ b ∈ Finset.range (n + 1), (X b) ^ 2 := by ring

theorem radBlk_le7 : ∃ Cr : ℝ, 0 < Cr ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (ρ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (Kρ : ℝ),
    0 ≤ Kρ → ContDiffOn ℝ 6 ρ (Set.Ioi 0) →
    (∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] ρ z| ≤ Kρ) →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
    Work.Construction.L12 f 0 = 0 →
    MeasureTheory.IntegrableOn (fun z => ∑ q ∈ Finset.range 7,
        (Work.Spaces.DzIter q (fun z' _ => ρ z' * Work.Construction.L12 f z') z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
          (Work.Spaces.DzIter q (fun z' _ => ρ z' * Work.Construction.L12 f z') z 0) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ Cr * (1 + Kρ) ^ 2 * Work.Spaces.HkSq α 6 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12slotLe7
  refine ⟨1404928 * (7 * C₁) + 1, by positivity, ?_⟩
  intro α hαIoc ρ f Kρ hKρ hρ6 hρbound hsm hmem6 hmem7 h0
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  -- `L₁₂ f` is `C⁶` on `(0,∞)`
  have hL6 : ContDiffOn ℝ 6 (Work.Construction.L12 f) (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 6 f hα hα1 hsm hmem6
      (by norm_num)
    exact h.congr (fun x _ =>
      (congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 f) x).symm)
  -- the seven weighted slots of `L₁₂ f`
  have hslot := hC₁ α f hα hα1 hsm hmem6 hmem7 h0
  -- ## the Leibniz expansion of the slots of the product
  have hexp : ∀ q ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0
        = ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
            * (Work.Spaces.Zop^[b] ρ z
                * Work.Spaces.Zop^[q - b] (fun z => Work.Construction.L12 f z) z) := by
    intro q hq z hz
    have hρq : ContDiffOn ℝ q ρ (Set.Ioi (0 : ℝ)) := hρ6.of_le (by exact_mod_cast hq)
    have hLq : ContDiffOn ℝ q (fun z' => Work.Construction.L12 f z') (Set.Ioi (0 : ℝ)) :=
      hL6.of_le (by exact_mod_cast hq)
    have h1 := Work.FTS.FinalClock.DzIter_mul_of_contDiffOn q ρ
      (fun z _ => Work.Construction.L12 f z) isOpen_Ioi (θ := 0) hρq hLq z hz
    rw [h1]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [congrFun (Work.Spaces.Zop_slice (q - b) (fun z _ => Work.Construction.L12 f z) 0) z]
  -- ## the pointwise Cauchy–Schwarz bound
  have hpt : ∀ (X Y : ℕ → ℝ) (z : ℝ), z ∈ Set.Ioi (0 : ℝ) → (∀ j ≤ 6, |Y j| ≤ Kρ) →
      (∀ q ≤ 6, Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0
        = ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (Y b * X (q - b))) →
      (∑ q ∈ Finset.range 7,
          (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ 1404928 * Kρ ^ 2 * ∑ b ∈ Finset.range 7, (X b) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro X Y z _ hY hex
    have hsq : ∀ q ≤ 6,
        (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2
          ≤ 200704 * Kρ ^ 2 * ∑ b ∈ Finset.range 7, (X b) ^ 2 := by
      intro q hq
      have hgen := sum_sq_binom_le_gen 6 Y X hKρ hY hq
      have hconst : (((6 + 1 : ℕ) : ℝ) * ((6 + 1 : ℕ) : ℝ) * 4 ^ 6 * Kρ ^ 2)
            * ∑ b ∈ Finset.range (6 + 1), (X b) ^ 2
          = 200704 * Kρ ^ 2 * ∑ b ∈ Finset.range 7, (X b) ^ 2 := by
        rw [show (((6 + 1 : ℕ) : ℝ) * ((6 + 1 : ℕ) : ℝ) * 4 ^ 6 * Kρ ^ 2)
            = 200704 * Kρ ^ 2 from by norm_num]
      calc (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2
          = (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (Y b * X (q - b))) ^ 2 := by
            rw [hex q hq]
        _ ≤ (((6 + 1 : ℕ) : ℝ) * ((6 + 1 : ℕ) : ℝ) * 4 ^ 6 * Kρ ^ 2)
              * ∑ b ∈ Finset.range (6 + 1), (X b) ^ 2 := hgen
        _ = 200704 * Kρ ^ 2 * ∑ b ∈ Finset.range 7, (X b) ^ 2 := hconst
    have hsum : (∑ q ∈ Finset.range 7,
        (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2)
        ≤ 1404928 * Kρ ^ 2 * ∑ b ∈ Finset.range 7, (X b) ^ 2 := by
      calc (∑ q ∈ Finset.range 7,
            (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2)
          ≤ ∑ _q ∈ Finset.range 7,
              (200704 * Kρ ^ 2 * ∑ b ∈ Finset.range 7, (X b) ^ 2) :=
            Finset.sum_le_sum
              (fun q hq => hsq q (by rw [Finset.mem_range] at hq; omega))
        _ = 7 * (200704 * Kρ ^ 2 * ∑ b ∈ Finset.range 7, (X b) ^ 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
        _ = 1404928 * Kρ ^ 2 * ∑ b ∈ Finset.range 7, (X b) ^ 2 := by ring
    calc (∑ q ∈ Finset.range 7,
            (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2)
        = (∑ q ∈ Finset.range 7,
            (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2)
              * (Work.Spaces.w z) ^ 2 := by rw [Finset.sum_mul]
      _ ≤ (1404928 * Kρ ^ 2 * ∑ b ∈ Finset.range 7, (X b) ^ 2) * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
      _ = 1404928 * Kρ ^ 2 * ∑ b ∈ Finset.range 7, (X b) ^ 2 * (Work.Spaces.w z) ^ 2 := by
          rw [← Finset.sum_mul]
          ring
  -- ## abbreviations for the majorant and the slot sum
  let X : ℕ → ℝ → ℝ := fun b z => Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z
  let Y : ℕ → ℝ → ℝ := fun j z => Work.Spaces.Zop^[j] ρ z
  let G : ℝ → ℝ := fun z => ∑ b ∈ Finset.range 7, (X b z) ^ 2 * (Work.Spaces.w z) ^ 2
  let A : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7,
      (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2
        * (Work.Spaces.w z) ^ 2
  have hAnn : ∀ z, 0 ≤ A z := fun z =>
    Finset.sum_nonneg (fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hApt : ∀ z ∈ Set.Ioi (0 : ℝ), A z ≤ 1404928 * Kρ ^ 2 * G z := by
    intro z hz
    exact hpt (fun b => X b z) (fun j => Y j z) z hz
      (fun j hj => hρbound j hj z hz)
      (fun q hq => hexp q hq z hz)
  -- ## integrability of the majorant `G`
  have hGint : MeasureTheory.IntegrableOn G Work.Spaces.Iz := by
    refine MeasureTheory.integrable_finsetSum (Finset.range 7)
      (f := fun b z => (X b z) ^ 2 * (Work.Spaces.w z) ^ 2) (fun b hb => ?_)
    have hb7 : b ≤ 6 := by rw [Finset.mem_range] at hb; omega
    refine MeasureTheory.IntegrableOn.congr_fun (hslot b (by omega)).1 (fun z _ => ?_)
      measurableSet_Ici
    show (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        = (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2
    rw [Work.FTS.StrongPersist.H6Pair6Aux.Zop_iter_eq_DzdIter]
  -- ## the value of the majorant integral
  have hGval : (∫ z in Work.Spaces.Iz, G z) ≤ 7 * (C₁ * Work.Spaces.HkSq α 6 f) := by
    have hfun : G = fun z => ∑ b ∈ Finset.range 7,
        (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2 := by
      funext z
      show (∑ b ∈ Finset.range 7, (Work.Spaces.Zop^[b]
              (fun z => Work.Construction.L12 f z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
          = ∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b
              (fun z => Work.Construction.L12 f z) z) ^ 2 * (Work.Spaces.w z) ^ 2
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Work.FTS.StrongPersist.H6Pair6Aux.Zop_iter_eq_DzdIter]
    rw [hfun]
    calc (∫ z in Work.Spaces.Iz, ∑ b ∈ Finset.range 7,
            (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 f z) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
        = ∑ b ∈ Finset.range 7,
            (∫ z in Work.Spaces.Iz,
              (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 f z) z) ^ 2
                * (Work.Spaces.w z) ^ 2) :=
          MeasureTheory.integral_finsetSum (Finset.range 7)
            (fun b hb => (hslot b (by rw [Finset.mem_range] at hb; omega)).1)
      _ ≤ ∑ _b ∈ Finset.range 7, (C₁ * Work.Spaces.HkSq α 6 f) :=
          Finset.sum_le_sum
            (fun b hb => (hslot b (by rw [Finset.mem_range] at hb; omega)).2)
      _ = 7 * (C₁ * Work.Spaces.HkSq α 6 f) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- ## the a.e. statements and integrability of the slot sum
  have hIzcongr : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).symm
  have hae_le : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      A z ≤ 1404928 * Kρ ^ 2 * G z := by
    rw [hIzcongr]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => hApt z hz)
  have hae_norm : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ‖A z‖ ≤ 1404928 * Kρ ^ 2 * G z := by
    rw [hIzcongr]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hAnn z)]
    exact hApt z hz
  have hAesm : MeasureTheory.AEStronglyMeasurable A
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hProdc6 : ContDiffOn ℝ 6 (fun z => ρ z * Work.Construction.L12 f z)
        (Set.Ioi (0 : ℝ)) := hρ6.mul hL6
    have hbase := aestronglyMeasurable_Zop_slotSum 6
      (G := fun z => ρ z * Work.Construction.L12 f z) hProdc6
    have hptZ : ∀ q : ℕ, ∀ z : ℝ,
        Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0
          = Work.Spaces.Zop^[q] (fun z => ρ z * Work.Construction.L12 f z) z := by
      intro q z
      exact congrFun
        (Work.Spaces.Zop_slice q (fun z _ => ρ z * Work.Construction.L12 f z) 0) z
    refine hbase.congr (Filter.Eventually.of_forall (fun z => ?_))
    have hAz : A z = ∑ q ∈ Finset.range 7,
        (Work.Spaces.Zop^[q] (fun z => ρ z * Work.Construction.L12 f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2 := by
      show (∑ q ∈ Finset.range 7,
            (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2) = _
      exact Finset.sum_congr rfl (fun q _ => by rw [hptZ q z])
    rw [hAz]
  have hAint : MeasureTheory.IntegrableOn A Work.Spaces.Iz :=
    MeasureTheory.Integrable.mono' (hGint.const_mul (1404928 * Kρ ^ 2)) hAesm hae_norm
  have hAle : (∫ z in Work.Spaces.Iz, A z)
      ≤ 1404928 * Kρ ^ 2 * (∫ z in Work.Spaces.Iz, G z) := by
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (g := fun z => 1404928 * Kρ ^ 2 * G z)
      (Filter.Eventually.of_forall hAnn) (hGint.const_mul (1404928 * Kρ ^ 2)) hae_le
    rwa [MeasureTheory.integral_const_mul] at hmono
  refine ⟨hAint, ?_⟩
  have hS := Work.Spaces.HkSq_nonneg α 6 f
  have hA2 : 0 ≤ 1404928 * (7 * C₁) := by positivity
  have hK2 : Kρ ^ 2 ≤ (1 + Kρ) ^ 2 := by nlinarith [hKρ]
  have hstep1 : 1404928 * (7 * C₁) * Kρ ^ 2 * Work.Spaces.HkSq α 6 f
      ≤ 1404928 * (7 * C₁) * ((1 + Kρ) ^ 2 * Work.Spaces.HkSq α 6 f) := by
    rw [show 1404928 * (7 * C₁) * Kρ ^ 2 * Work.Spaces.HkSq α 6 f
        = 1404928 * (7 * C₁) * (Kρ ^ 2 * Work.Spaces.HkSq α 6 f) from by ring]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK2 hS) hA2
  have hstep2 : 1404928 * (7 * C₁) * ((1 + Kρ) ^ 2 * Work.Spaces.HkSq α 6 f)
      ≤ (1404928 * (7 * C₁) + 1) * ((1 + Kρ) ^ 2 * Work.Spaces.HkSq α 6 f) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (sq_nonneg _) hS)
  calc (∫ z in Work.Spaces.Iz, A z)
      ≤ 1404928 * Kρ ^ 2 * (∫ z in Work.Spaces.Iz, G z) := hAle
    _ ≤ 1404928 * Kρ ^ 2 * (7 * (C₁ * Work.Spaces.HkSq α 6 f)) :=
        mul_le_mul_of_nonneg_left hGval (by positivity)
    _ = 1404928 * (7 * C₁) * Kρ ^ 2 * Work.Spaces.HkSq α 6 f := by ring
    _ ≤ 1404928 * (7 * C₁) * ((1 + Kρ) ^ 2 * Work.Spaces.HkSq α 6 f) := hstep1
    _ ≤ (1404928 * (7 * C₁) + 1) * ((1 + Kρ) ^ 2 * Work.Spaces.HkSq α 6 f) := hstep2
    _ = (1404928 * (7 * C₁) + 1) * (1 + Kρ) ^ 2 * Work.Spaces.HkSq α 6 f := by ring

end Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-- **The a.e. pointwise bound on the `D_z`-iterates of the angular moment `FK f`.**

For a datum `f` of class `C^∞` on the open quadrant whose weighted `ℋ⁶`- and `ℋ⁷`-energy is
finite, and for `b ≤ 6`, the `b`-th `D_z`-iterate of the radial function `z ↦ FK f z`
(`FK f z = ∫_θ f z θ K θ dθ`, the angular moment) is bounded almost everywhere in `z` by
`C·HkSq α (b+1) f`, with a universal constant `C`.

The proof is the two-step reduction `D_z^b (FK f) = FK (D_z^b f)` a.e. (`DzIter_FK_eq_ae`),
the angular Cauchy–Schwarz `(FK g z)² ≤ 16 ∫_θ g z θ ² dθ` (`n5_FK_abs_le`), and the
uniform-in-`z` angular-average bound `∫_θ (D_z^b f z θ)² dθ ≤ C·HkSq α (b+1) f`
(`supDzAvgLevel`, the level-`k` form of the radial Hardy/window inequality). -/
theorem fkDzdIterSqLe : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {f : Work.FTS.Galerkin.Fn},
    0 < α → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.Spaces.HkMem α 7 f → ∀ b : ℕ, b ≤ 6 →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
        ≤ C * Work.Spaces.HkSq α (b + 1) f := by
  obtain ⟨C₁, _hC₁pos, hC₁⟩ := supDzAvgLevel
  refine ⟨16 * C₁, by positivity, ?_⟩
  intro α f hα hsm hm6 hm7 b hb
  -- `ℋ^{b+1}`-membership, descending from `ℋ⁷`
  have hbmem : Work.Spaces.HkMem α (b + 1) f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm (b + 1) (by omega) hm7
  -- `D_z^b (FK f) = FK (D_z^b f)` a.e. in `z`
  have hae := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae hsm hm6 b hb
  have hae' := (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici).mp hae
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
  filter_upwards [hae', MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with z hid hne
  intro hzI
  have hzpos : 0 < z := lt_of_le_of_ne (Set.mem_Ici.mp hzI) (Ne.symm hne)
  -- angular Cauchy–Schwarz for the moment of the `b`-th derivative
  have hsq : (Work.Construction.FK (Work.Spaces.DzIter b f) z) ^ 2
      ≤ 16 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2 :=
    FKdzIter_sq_le hsm hbmem b (Nat.le_succ b) hzpos
  -- the uniform angular-average bound at level `b+1`
  have havg : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
      ≤ C₁ * Work.Spaces.HkSq α (b + 1) f :=
    hC₁ α f (b + 1) b hα hsm hbmem (le_refl (b + 1)) z hzpos
  rw [hid hzI 0]
  calc (Work.Construction.FK (Work.Spaces.DzIter b f) z) ^ 2
      ≤ 16 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2 := hsq
    _ ≤ 16 * (C₁ * Work.Spaces.HkSq α (b + 1) f) :=
        mul_le_mul_of_nonneg_left havg (by norm_num)
    _ = (16 * C₁) * Work.Spaces.HkSq α (b + 1) f := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
end
