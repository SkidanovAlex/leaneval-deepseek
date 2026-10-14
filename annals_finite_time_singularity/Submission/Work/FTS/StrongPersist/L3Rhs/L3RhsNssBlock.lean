import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.L3Rhs.CoupledVfs
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.PieceSmooth
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SmainHon
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_MuLamOK.Conversion
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.SolutionDelivery.DatumOdd
-- ===== merged: Submission.Work.FTS.StrongEps.TenOfEight.GainPtAll =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

open Work.FTS.StrongEps.EpsE4Thr

namespace Work.FTS.StrongEps.TenOfEight

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem HkIntegrand_Jeps_gain_pt_all {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε α c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c) {M k : ℕ} (hk : 1 ≤ k)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hWη : ∀ p : ℝ × ℝ, Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      ≤ Real.exp (c * (|p.1| + |p.2|))
        * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    (hWγ : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
      * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :
    ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
      ≤ ENNReal.ofReal (Cgain ρ ε M)
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (LamAll ρ ε c M p)
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
  set J : ℝ≥0∞ := ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (LamAll ρ ε c M p)
      * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
          (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) with hJdef
  set Kg : ℝ≥0∞ := ENNReal.ofReal (KgainBig ρ ε M) with hKgdef
  set A : ℝ := ∑ a ∈ Finset.range (M + 1),
    (Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 with hAdef
  set B : ℝ := ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (M + 1),
    (if 1 ≤ i ∧ i + j ≤ M then
      (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0) with hBdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact Finset.sum_nonneg fun a _ => sq_nonneg _
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs with h <;> simp [sq_nonneg]
  have hsplit : Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ = A + B := by
    simp only [Work.Spaces.HkIntegrand]
    rw [← hAdef, ← hBdef]
  -- the per-slot bounds, and the two finite sums
  have hslotA : ∀ a ∈ Finset.range (M + 1),
      ENNReal.ofReal ((Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) ≤ Kg * J := by
    intro a ha
    have haM : a ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    simpa only [hJdef, hKgdef] using
      zslot_le_gain_all hρ hε hc hf hz hθ hWη haM
  have hslotB : ∀ i ∈ Finset.range (M + 1), ∀ j ∈ Finset.range (M + 1),
      ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ M then
        (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0) ≤ Kg * J := by
    intro i _ j _
    by_cases hc' : 1 ≤ i ∧ i + j ≤ M
    · rw [if_pos hc']
      simpa only [hJdef, hKgdef] using
        mslot_le_gain_all hρ hε hc hk hf hz hθ hWγ hc'.1 hc'.2
    · rw [if_neg hc']
      simp only [ENNReal.ofReal_zero]
      exact zero_le
  have hA_le : (∑ a ∈ Finset.range (M + 1),
      ENNReal.ofReal ((Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ≤ ((M + 1 : ℕ) : ℝ≥0∞) * (Kg * J) := by
    refine (Finset.sum_le_card_nsmul (Finset.range (M + 1)) _ (Kg * J) hslotA).trans ?_
    rw [Finset.card_range]
    exact Work.FTS.StrongEps.StepFacts.nsmul_le_natCast_mul (M + 1) (Kg * J)
  have hB_le : (∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (M + 1),
      ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ M then
        (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) ≤ (((M + 1) * (M + 1) : ℕ) : ℝ≥0∞) * (Kg * J) := by
    have hinner : ∀ i ∈ Finset.range (M + 1),
        (∑ j ∈ Finset.range (M + 1), ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ M then
          (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ((M + 1 : ℕ) : ℝ≥0∞) * (Kg * J) := fun i hi =>
      (Finset.sum_le_card_nsmul (Finset.range (M + 1)) _ (Kg * J)
        (fun j hj => hslotB i hi j hj)).trans (by
          rw [Finset.card_range]
          exact Work.FTS.StrongEps.StepFacts.nsmul_le_natCast_mul (M + 1) (Kg * J))
    refine (Finset.sum_le_card_nsmul (Finset.range (M + 1)) _ _ hinner).trans ?_
    rw [Finset.card_range, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
  -- the `ofReal` split and the numerical bookkeeping
  have hpt : ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
      = ENNReal.ofReal A + ENNReal.ofReal B := by
    rw [hsplit, ENNReal.ofReal_add hA0 hB0]
  have h1 : ENNReal.ofReal A = ∑ a ∈ Finset.range (M + 1),
      ENNReal.ofReal ((Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    rw [hAdef, ENNReal.ofReal_sum_of_nonneg]
    exact fun a _ => sq_nonneg _
  have h2 : ENNReal.ofReal B = ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (M + 1),
      ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ M then
        (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
          * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    rw [hBdef, ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg]
      exact fun j _ => by split_ifs with h <;> simp [sq_nonneg]
    · exact fun i _ => Finset.sum_nonneg fun j _ => by
        split_ifs with h <;> simp [sq_nonneg]
  have hAB : ENNReal.ofReal A + ENNReal.ofReal B
      ≤ ((((M + 1) + (M + 1) * (M + 1) : ℕ)) : ℝ≥0∞) * (Kg * J) := by
    rw [h1, h2]
    refine (add_le_add hA_le hB_le).trans (le_of_eq ?_)
    rw [← add_mul, ← Nat.cast_add]
  have hC : ENNReal.ofReal (Cgain ρ ε M) * J
      = ((((M + 1) + (M + 1) * (M + 1) : ℕ)) : ℝ≥0∞) * (Kg * J) := by
    rw [Cgain, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ← hKgdef]
    rw [pow_two, mul_assoc]
  rw [hpt]
  exact hAB.trans (le_of_eq hC.symm)

end Work.FTS.StrongEps.TenOfEight
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNssBlock =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

theorem L3RhsNssBlock : ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.StrongPersist.L3Rhs.NSsSum α Φs)) Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem α 3 (Work.FTS.StrongPersist.L3Rhs.NSsSum α Φs) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.StrongPersist.L3Rhs.NSsSum α Φs)
        ≤ C * (1 + |Cs|) ^ 4 * α ^ (-Cpow) := by
  obtain ⟨C1, hC1pos, hbody1⟩ := N1ssPriced
  obtain ⟨C2, hC2pos, hbody2⟩ := N2ssPriced
  obtain ⟨C3, hC3pos, hbody3⟩ := N3ssPriced
  obtain ⟨C4, hC4pos, hbody4⟩ := N4ssPriced
  obtain ⟨C5, hC5pos, hbody5⟩ := N5ssPriced
  refine ⟨16 * (C1 + C2 + C3 + C4 + C5) + 1, 0, 1 / 2, ?_, le_refl 0, by norm_num, ?_⟩
  · have h1' : (0 : ℝ) < 16 * (C1 + C2 + C3 + C4 + C5) := by linarith
    linarith
  intro α hαmem Cs Φs hstar
  obtain ⟨hα0, hαhalf⟩ := hαmem
  have hα : 0 < α := hα0
  have hα1 : α ≤ 1 := by linarith
  have hαIoc : α ∈ Set.Ioc 0 1 := ⟨hα, hα1⟩
  -- the five pieces, and the four partial sums
  set S1 : Fn := Work.FTS.Nonlin.N1ss α Φs with hS1
  set S2 : Fn := Work.FTS.Nonlin.N2ss α Φs with hS2
  set S3 : Fn := Work.FTS.Nonlin.N3ss α Φs with hS3
  set S4 : Fn := Work.FTS.Nonlin.N4ss α with hS4
  set S5 : Fn := Work.FTS.Nonlin.N5ss α with hS5
  set P12 : Fn := fun z θ => S1 z θ + S2 z θ with hP12
  set P123 : Fn := fun z θ => P12 z θ + S3 z θ with hP123
  set P1234 : Fn := fun z θ => P123 z θ + S4 z θ with hP1234
  set Pall : Fn := fun z θ => P1234 z θ + S5 z θ with hPall
  have hsum : NSsSum α Φs = Pall := by
    rw [hPall, hP1234, hP123, hP12, hS1, hS2, hS3, hS4, hS5]
    rfl
  -- the six delegated inputs, instantiated (the `set`-definitions `Sᵢ` are definitionally the
  -- pieces, so the statements transfer without rewriting)
  have hmem4_1 : Work.Spaces.HkMem α 4 S1 := (hbody1 α hαIoc Cs Φs hstar).1
  have hmem4_2 : Work.Spaces.HkMem α 4 S2 := (hbody2 α hαIoc Cs Φs hstar).1
  have hmem4_3 : Work.Spaces.HkMem α 4 S3 := (hbody3 α hαIoc Cs Φs hstar).1
  have hmem4_4 : Work.Spaces.HkMem α 4 S4 := (hbody4 α hαIoc).1
  have hmem4_5 : Work.Spaces.HkMem α 4 S5 := (hbody5 α hαIoc).1
  have hbnd1 : Work.Spaces.HkNorm α 4 S1 ≤ C1 * (1 + |Cs|) * α ^ 2 :=
    (hbody1 α hαIoc Cs Φs hstar).2
  have hbnd2 : Work.Spaces.HkNorm α 4 S2 ≤ C2 * (1 + |Cs|) * α ^ 2 :=
    (hbody2 α hαIoc Cs Φs hstar).2
  have hbnd3 : Work.Spaces.HkNorm α 4 S3 ≤ C3 * (1 + |Cs|) * α ^ 3 :=
    (hbody3 α hαIoc Cs Φs hstar).2
  have hbnd4 : Work.Spaces.HkNorm α 4 S4 ≤ C4 * α ^ 3 := (hbody4 α hαIoc).2
  have hbnd5 : Work.Spaces.HkNorm α 4 S5 ≤ C5 * α ^ 2 := (hbody5 α hαIoc).2
  obtain ⟨hSO1, hSO2, hSO3, hSO4, hSO5⟩ := PieceSmooth α hαIoc Cs Φs hstar
  -- level-3 honesty of the pieces
  have hmem3_1 : Work.Spaces.HkMem α 3 S1 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO1 3 (by norm_num) hmem4_1
  have hmem3_2 : Work.Spaces.HkMem α 3 S2 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO2 3 (by norm_num) hmem4_2
  have hmem3_3 : Work.Spaces.HkMem α 3 S3 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO3 3 (by norm_num) hmem4_3
  have hmem3_4 : Work.Spaces.HkMem α 3 S4 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO4 3 (by norm_num) hmem4_4
  have hmem3_5 : Work.Spaces.HkMem α 3 S5 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO5 3 (by norm_num) hmem4_5
  -- level-4 honesty of the partial sums
  have hmem4_12 : Work.Spaces.HkMem α 4 P12 := by
    rw [hP12]
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four (f := S1) (g := S2)
      (hSO1.forall 4) (hSO2.forall 4) hmem4_1 hmem4_2
  have hmem4_123 : Work.Spaces.HkMem α 4 P123 := by
    rw [hP123]
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four (f := P12) (g := S3)
      ((Work.FTS.EllipticEst.smoothOpen_add hSO1 hSO2).forall 4) (hSO3.forall 4)
      hmem4_12 hmem4_3
  have hSO12 : Work.FTS.EllipticEst.SmoothOpen P12 := by
    rw [hP12]; exact Work.FTS.EllipticEst.smoothOpen_add hSO1 hSO2
  have hSO123 : Work.FTS.EllipticEst.SmoothOpen P123 := by
    rw [hP123]; exact Work.FTS.EllipticEst.smoothOpen_add hSO12 hSO3
  have hmem4_1234 : Work.Spaces.HkMem α 4 P1234 := by
    rw [hP1234]
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four (f := P123) (g := S4)
      (hSO123.forall 4) (hSO4.forall 4) hmem4_123 hmem4_4
  have hSO1234 : Work.FTS.EllipticEst.SmoothOpen P1234 := by
    rw [hP1234]; exact Work.FTS.EllipticEst.smoothOpen_add hSO123 hSO4
  have hmem4_Pall : Work.Spaces.HkMem α 4 Pall := by
    rw [hPall]
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four (f := P1234) (g := S5)
      (hSO1234.forall 4) (hSO5.forall 4) hmem4_1234 hmem4_5
  have hSO_Pall : Work.FTS.EllipticEst.SmoothOpen Pall := by
    rw [hPall]; exact Work.FTS.EllipticEst.smoothOpen_add hSO1234 hSO5
  have hmem3_12 : Work.Spaces.HkMem α 3 P12 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO12 3 (by norm_num) hmem4_12
  have hmem3_123 : Work.Spaces.HkMem α 3 P123 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO123 3 (by norm_num) hmem4_123
  have hmem3_1234 : Work.Spaces.HkMem α 3 P1234 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO1234 3 (by norm_num) hmem4_1234
  -- the triangle inequalities for the norm at level 3
  have hs2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have htri12 : Work.Spaces.HkNorm α 3 P12
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 3 S1 + Work.Spaces.HkNorm α 3 S2) := by
    rw [hP12]
    exact Work.FTS.EllipticEst.HkNorm_add_le α 3 (hSO1.forall) (hSO2.forall) hmem3_1 hmem3_2
  have htri123 : Work.Spaces.HkNorm α 3 P123
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 3 P12 + Work.Spaces.HkNorm α 3 S3) := by
    rw [hP123]
    exact Work.FTS.EllipticEst.HkNorm_add_le α 3 (hSO12.forall) (hSO3.forall) hmem3_12 hmem3_3
  have htri1234 : Work.Spaces.HkNorm α 3 P1234
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 3 P123 + Work.Spaces.HkNorm α 3 S4) := by
    rw [hP1234]
    exact Work.FTS.EllipticEst.HkNorm_add_le α 3 (hSO123.forall) (hSO4.forall) hmem3_123 hmem3_4
  have htriPall : Work.Spaces.HkNorm α 3 Pall
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 3 P1234 + Work.Spaces.HkNorm α 3 S5) := by
    rw [hPall]
    exact Work.FTS.EllipticEst.HkNorm_add_le α 3 (hSO1234.forall) (hSO5.forall) hmem3_1234 hmem3_5
  -- the monotonicity `3 ≤ 4`
  have hmono1 : Work.Spaces.HkNorm α 3 S1 ≤ Work.Spaces.HkNorm α 4 S1 :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 4) (k' := 3) (by norm_num) hmem4_1
  have hmono2 : Work.Spaces.HkNorm α 3 S2 ≤ Work.Spaces.HkNorm α 4 S2 :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 4) (k' := 3) (by norm_num) hmem4_2
  have hmono3 : Work.Spaces.HkNorm α 3 S3 ≤ Work.Spaces.HkNorm α 4 S3 :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 4) (k' := 3) (by norm_num) hmem4_3
  have hmono4 : Work.Spaces.HkNorm α 3 S4 ≤ Work.Spaces.HkNorm α 4 S4 :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 4) (k' := 3) (by norm_num) hmem4_4
  have hmono5 : Work.Spaces.HkNorm α 3 S5 ≤ Work.Spaces.HkNorm α 4 S5 :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 4) (k' := 3) (by norm_num) hmem4_5
  -- arithmetic
  have hX1 : (0 : ℝ) ≤ (1 : ℝ) + |Cs| := by positivity
  have hX1ge : (1 : ℝ) ≤ 1 + |Cs| := by linarith [abs_nonneg Cs]
  have hX4 : (1 : ℝ) + |Cs| ≤ (1 + |Cs|) ^ 4 := by
    calc (1 : ℝ) + |Cs| = (1 + |Cs|) ^ 1 := (pow_one _).symm
      _ ≤ (1 + |Cs|) ^ 4 := pow_le_pow_right₀ hX1ge (by norm_num)
  have hp2 : α ^ 2 ≤ 1 := pow_le_one₀ hα.le hα1
  have hp3 : α ^ 3 ≤ 1 := pow_le_one₀ hα.le hα1
  -- the five pieces, in the final shape
  have hF1 : Work.Spaces.HkNorm α 3 S1 ≤ C1 * (1 + |Cs|) ^ 4 := by
    refine hmono1.trans (hbnd1.trans ?_)
    calc C1 * (1 + |Cs|) * α ^ 2 ≤ C1 * (1 + |Cs|) * 1 :=
          mul_le_mul_of_nonneg_left hp2 (by positivity)
      _ = C1 * (1 + |Cs|) := by ring
      _ ≤ C1 * (1 + |Cs|) ^ 4 := mul_le_mul_of_nonneg_left hX4 hC1pos.le
  have hF2 : Work.Spaces.HkNorm α 3 S2 ≤ C2 * (1 + |Cs|) ^ 4 := by
    refine hmono2.trans (hbnd2.trans ?_)
    calc C2 * (1 + |Cs|) * α ^ 2 ≤ C2 * (1 + |Cs|) * 1 :=
          mul_le_mul_of_nonneg_left hp2 (by positivity)
      _ = C2 * (1 + |Cs|) := by ring
      _ ≤ C2 * (1 + |Cs|) ^ 4 := mul_le_mul_of_nonneg_left hX4 hC2pos.le
  have hF3 : Work.Spaces.HkNorm α 3 S3 ≤ C3 * (1 + |Cs|) ^ 4 := by
    refine hmono3.trans (hbnd3.trans ?_)
    calc C3 * (1 + |Cs|) * α ^ 3 ≤ C3 * (1 + |Cs|) * 1 :=
          mul_le_mul_of_nonneg_left hp3 (by positivity)
      _ = C3 * (1 + |Cs|) := by ring
      _ ≤ C3 * (1 + |Cs|) ^ 4 := mul_le_mul_of_nonneg_left hX4 hC3pos.le
  have hF4 : Work.Spaces.HkNorm α 3 S4 ≤ C4 * (1 + |Cs|) ^ 4 := by
    refine hmono4.trans (hbnd4.trans ?_)
    calc C4 * α ^ 3 ≤ C4 * 1 := mul_le_mul_of_nonneg_left hp3 hC4pos.le
      _ = C4 * 1 := by ring
      _ ≤ C4 * (1 + |Cs|) ^ 4 := by
          refine mul_le_mul_of_nonneg_left ?_ hC4pos.le
          have h1 : (1 : ℝ) ≤ (1 + |Cs|) ^ 4 := one_le_pow₀ hX1ge
          linarith
  have hF5 : Work.Spaces.HkNorm α 3 S5 ≤ C5 * (1 + |Cs|) ^ 4 := by
    refine hmono5.trans (hbnd5.trans ?_)
    calc C5 * α ^ 2 ≤ C5 * 1 := mul_le_mul_of_nonneg_left hp2 hC5pos.le
      _ = C5 * 1 := by ring
      _ ≤ C5 * (1 + |Cs|) ^ 4 := by
          refine mul_le_mul_of_nonneg_left ?_ hC5pos.le
          have h1 : (1 : ℝ) ≤ (1 + |Cs|) ^ 4 := one_le_pow₀ hX1ge
          linarith
  -- the four triangle steps, with `√2 ≤ 2`
  have step1 : Work.Spaces.HkNorm α 3 Pall
      ≤ 2 * (Work.Spaces.HkNorm α 3 P1234 + Work.Spaces.HkNorm α 3 S5) := by
    refine htriPall.trans ?_
    exact mul_le_mul_of_nonneg_right hs2
      (by linarith [Work.Spaces.HkNorm_nonneg α 3 P1234, Work.Spaces.HkNorm_nonneg α 3 S5])
  have step2 : Work.Spaces.HkNorm α 3 P1234
      ≤ 2 * (Work.Spaces.HkNorm α 3 P123 + Work.Spaces.HkNorm α 3 S4) := by
    refine htri1234.trans ?_
    exact mul_le_mul_of_nonneg_right hs2
      (by linarith [Work.Spaces.HkNorm_nonneg α 3 P123, Work.Spaces.HkNorm_nonneg α 3 S4])
  have step3 : Work.Spaces.HkNorm α 3 P123
      ≤ 2 * (Work.Spaces.HkNorm α 3 P12 + Work.Spaces.HkNorm α 3 S3) := by
    refine htri123.trans ?_
    exact mul_le_mul_of_nonneg_right hs2
      (by linarith [Work.Spaces.HkNorm_nonneg α 3 P12, Work.Spaces.HkNorm_nonneg α 3 S3])
  have step4 : Work.Spaces.HkNorm α 3 P12
      ≤ 2 * (Work.Spaces.HkNorm α 3 S1 + Work.Spaces.HkNorm α 3 S2) := by
    refine htri12.trans ?_
    exact mul_le_mul_of_nonneg_right hs2
      (by linarith [Work.Spaces.HkNorm_nonneg α 3 S1, Work.Spaces.HkNorm_nonneg α 3 S2])
  have hchain : Work.Spaces.HkNorm α 3 Pall
      ≤ 16 * (Work.Spaces.HkNorm α 3 S1 + Work.Spaces.HkNorm α 3 S2
          + Work.Spaces.HkNorm α 3 S3 + Work.Spaces.HkNorm α 3 S4
          + Work.Spaces.HkNorm α 3 S5) := by
    linarith [step1, step2, step3, step4, Work.Spaces.HkNorm_nonneg α 3 S1,
      Work.Spaces.HkNorm_nonneg α 3 S2, Work.Spaces.HkNorm_nonneg α 3 S3,
      Work.Spaces.HkNorm_nonneg α 3 S4, Work.Spaces.HkNorm_nonneg α 3 S5]
  have hfin : Work.Spaces.HkNorm α 3 Pall
      ≤ 16 * (C1 + C2 + C3 + C4 + C5) * (1 + |Cs|) ^ 4 := by
    refine hchain.trans ?_
    have hsum5 : Work.Spaces.HkNorm α 3 S1 + Work.Spaces.HkNorm α 3 S2
        + Work.Spaces.HkNorm α 3 S3 + Work.Spaces.HkNorm α 3 S4
        + Work.Spaces.HkNorm α 3 S5
        ≤ C1 * (1 + |Cs|) ^ 4 + C2 * (1 + |Cs|) ^ 4 + C3 * (1 + |Cs|) ^ 4
          + C4 * (1 + |Cs|) ^ 4 + C5 * (1 + |Cs|) ^ 4 := by
      linarith [hF1, hF2, hF3, hF4, hF5]
    calc 16 * (Work.Spaces.HkNorm α 3 S1 + Work.Spaces.HkNorm α 3 S2
            + Work.Spaces.HkNorm α 3 S3 + Work.Spaces.HkNorm α 3 S4
            + Work.Spaces.HkNorm α 3 S5)
        ≤ 16 * (C1 * (1 + |Cs|) ^ 4 + C2 * (1 + |Cs|) ^ 4 + C3 * (1 + |Cs|) ^ 4
            + C4 * (1 + |Cs|) ^ 4 + C5 * (1 + |Cs|) ^ 4) := by linarith
      _ = 16 * (C1 + C2 + C3 + C4 + C5) * (1 + |Cs|) ^ 4 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum]
    exact hSO_Pall.forall 3
  · rw [hsum]
    exact Work.FTS.OpenPkg.HkMem_mono_open hSO_Pall 3 (by norm_num) hmem4_Pall
  · rw [hsum]
    refine hfin.trans ?_
    rw [show (-(0 : ℝ)) = 0 by norm_num, Real.rpow_zero, mul_one]
    have hquad : (0 : ℝ) ≤ (1 + |Cs|) ^ 4 := by positivity
    nlinarith [hquad]

end Work.FTS.StrongPersist.L3Rhs
end
end
