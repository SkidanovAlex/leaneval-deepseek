import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.I1WMSliceB =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! Split out of `AeI1Fts/I1PaperWeakMixed.lean` (the file was 45 KB, above the project's
per-file build guard): the `θ`-truncated slice bounds.  Names and namespace are unchanged. -/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)






end

end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.GalFields.Norm.HkSq_Lhat_le_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The pointwise integrand bound, uniform in `α` -/

/-- **The `ℋ^m`-integrand of `𝓛̂g` is dominated by the `ℋ^{m+1}`-integrand of `g`, with a
constant independent of `α`.**  This is `Lhat_integrand_le` with the quantifier over `α`
moved inside the existential: the proof is verbatim the same, because every ingredient of it
carries a constant that does not mention `α`. -/
theorem Lhat_integrand_le_uniform (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ g : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen g →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α m (Work.FTS.CoercivityFix.Lhat g) z θ
          ≤ C * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
  obtain ⟨K, hKpos, hKb⟩ := Work.FTS.StrongPersist.H6Aux.three_div_zop_bound m
  have hK : (0 : ℝ) ≤ K := hKpos.le
  refine ⟨8 * (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2) + 9, ?_, ?_⟩
  · have h1 : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 :=
      mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos m).le (sq_nonneg _)
    linarith
  · intro α hα g hg z hz θ hθ
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hZnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 :=
      mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos m).le (sq_nonneg _)
    have hRnn : 0 ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ :=
      Work.Spaces.HkIntegrand_nonneg α (m + 1) g z θ
    have hφsm : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 3 / (1 + z))
        (Set.Ioi (-1)) :=
      contDiffOn_iff_forall_nat_le.mpr (fun k _ => Work.FTS.FinalClock.contDiffOn_phiThree k)
    -- the multiplier estimate for `φ(z) = 3/(1+z)`, for an arbitrary `SmoothOpen` factor
    have hmul (X : ℝ → ℝ → ℝ) (hX : Work.FTS.EllipticEst.SmoothOpen X) :
        Work.Spaces.HkIntegrand α m (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * X z θ) z θ
          ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α m X z θ :=
      Work.FTS.StrongPersist.L3Aux.zmul_open α m (fun z : ℝ => 3 / (1 + z)) X hK hKb hφsm hX
        z hz θ hθ
    -- the index shifts
    have hshiftZ : Work.Spaces.HkIntegrand α m (Work.Spaces.Dz g) z θ
        ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      have h := Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα m 0 1 hg z hzIz θ hθI
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
        Nat.reduceAdd] using h
    have hshiftT : Work.Spaces.HkIntegrand α m (Work.Spaces.Dth g) z θ
        ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      have h := Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα m 1 0 hg z hzIz θ hθI
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
        Nat.reduceAdd, Nat.add_zero] using h
    have hmono : Work.Spaces.HkIntegrand α m g z θ ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ :=
      Work.FTS.StrongPersist.HkIntegrand_le_of_le α (Nat.le_succ m) g z θ
    -- smoothness of the three new summands of the decomposition
    have hφopen : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => (fun z : ℝ => 3 / (1 + z)) z) :=
      Work.FTS.StrongPersist.linMem_radial hφsm
    have hBsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)) :=
      Work.FTS.StrongPersist.linMem_const_mul (-(2 / 3))
        (Work.FTS.StrongPersist.linMem_mul hφopen hg)
    have hDsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) :=
      Work.FTS.StrongPersist.linMem_const_mul (-1)
        (Work.FTS.StrongPersist.linMem_mul hφopen hg.Dth)
    -- the bound for each of the three summands
    have hA : Work.Spaces.HkIntegrand α m (fun z θ => g z θ + Work.Spaces.Dz g z θ) z θ
        ≤ 4 * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      have h := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α m
        (f := g) (g := Work.Spaces.Dz g) (hg.forall m) ((hg.Dz).forall m) z hzIz θ hθI
      linarith [h, hmono, hshiftZ]
    have hB : Work.Spaces.HkIntegrand α m
        (fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)) z θ
        ≤ (4 / 9) * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
            * Work.Spaces.HkIntegrand α (m + 1) g z θ) := by
      rw [Work.FTS.LocData.HkIntegrand_const_mul]
      have hsq : (-(2 / 3) : ℝ) ^ 2 = 4 / 9 := by norm_num
      rw [hsq]
      have h2 : Work.Spaces.HkIntegrand α m
            (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * g z θ) z θ
          ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ :=
        le_trans (hmul g hg) (mul_le_mul_of_nonneg_left hmono hZnn)
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have hD : Work.Spaces.HkIntegrand α m
        (fun z θ => (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) z θ
        ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
            * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      rw [Work.FTS.LocData.HkIntegrand_const_mul]
      have h2 : Work.Spaces.HkIntegrand α m
            (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ) z θ
          ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ :=
        le_trans (hmul (Work.Spaces.Dth g) hg.Dth)
          (mul_le_mul_of_nonneg_left hshiftT hZnn)
      norm_num
      exact h2
    have hBD : Work.Spaces.HkIntegrand α m
        (fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)
          + (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) z θ
        ≤ 2 * ((4 / 9) * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ))
          + 2 * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ) := by
      have h := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α m
        (f := fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ))
        (g := fun z θ => (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ))
        (hBsm.forall m) (hDsm.forall m) z hzIz θ hθI
      linarith [h, hB, hD]
    -- assemble along `𝓛̂g = (g + D_z g) + [(−2/3)·(φ g) + (−1)·(φ D_θ g)]`
    have hLhat : Work.FTS.CoercivityFix.Lhat g
        = fun z θ => (g z θ + Work.Spaces.Dz g z θ)
            + ((-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)
               + (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) := by
      funext z θ
      rw [Work.FTS.CoercivityFix.Lhat_eq]
      ring
    rw [hLhat]
    have hfinal := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α m
      (f := fun z θ => g z θ + Work.Spaces.Dz g z θ)
      (g := fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)
        + (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ))
      ((hg.forall m).add ((hg.Dz).forall m)) ((hBsm.forall m).add (hDsm.forall m)) z hzIz θ hθI
    have hkey : 2 * (4 * Work.Spaces.HkIntegrand α (m + 1) g z θ)
        + 2 * (2 * ((4 / 9) * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
                * Work.Spaces.HkIntegrand α (m + 1) g z θ))
          + 2 * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ))
        ≤ (8 * (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2) + 9)
            * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      nlinarith [hRnn, hZnn]
    linarith [hfinal, hA, hBD, hkey]

/-! ## The closed-quadrant form -/

/-- The closed-quadrant form of `Lhat_integrand_le_uniform`, with the same constant: the two
boundary lines `z = 0` and `sin(2θ) = 0` are trivial because both integrands vanish there. -/
theorem Lhat_HkIntegrand_le_uniform (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ g : Fn,
      Work.FTS.EllipticEst.SmoothOpen g →
        ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α m (Work.FTS.CoercivityFix.Lhat g) z θ
            ≤ C * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
  obtain ⟨C, hC, h⟩ := Lhat_integrand_le_uniform m
  exact ⟨C, hC, fun α hα g hs => Work.FTS.StrongPersist.H6Aux.HkIntegrand_le_Izθ_of_Ioo
    (α := α) (m := m) (l := m + 1) (X := Work.FTS.CoercivityFix.Lhat g) (Y := g) (C := C)
    hα hC.le (h α hα g hs)⟩

/-! ## The integrated bound -/

/-- **The `α`-uniform `ℋᵐ`-bound for `𝓛̂`.**  One constant works for every `α > 0`:

  `HkSq α m (Lhat g) ≤ C · HkSq α (m+1) g`. -/
theorem HkSq_Lhat_le_uniform_aux (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ g : Fn,
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α (m + 1) g →
        Work.Spaces.HkSq α m (Work.FTS.CoercivityFix.Lhat g)
          ≤ C * Work.Spaces.HkSq α (m + 1) g := by
  obtain ⟨C, hC, h⟩ := Lhat_HkIntegrand_le_uniform m
  refine ⟨C, hC, fun α hα g hs hm => ?_⟩
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have hout : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m
          (Work.FTS.CoercivityFix.Lhat g) z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) g z θ) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    have hinner : (∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α (m + 1) g z θ)
        = C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) g z θ) :=
      MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) C _
    rw [← hinner]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α m
        (Work.FTS.CoercivityFix.Lhat g) z θ) ((hm.1 z hz).const_mul C) ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
      h α hα g hs z hz θ hθ
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α m (Work.FTS.CoercivityFix.Lhat g) z θ)
    (hm.2.const_mul C) hout) ?_
  exact le_of_eq (MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iz) C
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) g z θ))

/-! ## The requested theorem -/

/-- **`HkSq_Lhat_le_uniform`**: the `ℋ⁴`-norm of `𝓛̂g` is bounded by a *single* constant
times the `ℋ⁵`-norm of `g`, uniformly over all `α > 0`. -/
theorem HkSq_Lhat_le_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 5 g →
        Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat g)
          ≤ C * Work.Spaces.HkSq α 5 g := by
  obtain ⟨C, hC, h⟩ := HkSq_Lhat_le_uniform_aux 4
  exact ⟨C, hC, fun α hα g hs hm => h α hα g hs (by simpa using hm)⟩

end Work.FTS.GalFields.Norm
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0Rows =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- Negation as a lambda (for rewriting under `Xn`/`HkMem`). -/
private theorem neg_apply_eq (f : ℝ → ℝ → ℝ) : (fun z θ => -f z θ) = -f := rfl

private theorem mem_neg_apply {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k (fun z θ => -f z θ) := by
  rw [neg_apply_eq f]
  exact mem_neg h

private theorem Xn_neg_apply {α : ℝ} (f : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.Xn α (fun z θ => -f z θ) = Work.FTS.Nonlin.Xn α f := by
  rw [neg_apply_eq f]
  exact Xn_neg f

/-- The standard nonnegativity of `3/(2α)`. -/
private theorem three_div_two_pos {α : ℝ} (hα : 0 < α) : (0 : ℝ) < 3 / (2 * α) := by positivity

/-! ## The six product rows of the `N₀`-block

Each lemma below proves the `ℋ⁴`-honesty, smoothness and `ℋ⁴`-size of one product piece
`N03g`, `N04aF`, `N04bF`, `N05aF`, `N05bF`, `N06F` of the split, in terms of the universal
product rules (`prod_field`, `wprod_field_winf`) supplied as hypotheses, and of the size bounds
of the factors. -/

/-- **Row 2 of the `N₀`-table**: `N₀₃ᵍ = (1/α)·L₁₂(w)·w`. -/
theorem row_N03g {α Cp C1 : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hsmw : Work.FTS.EllipticEst.SmoothOpen w) (hmem4 : Work.Spaces.HkMem α 4 w)
    (hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 w z))
    (hL12mem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 w z))
    (hCp : 0 < Cp) (hC1 : 0 < C1)
    (hL12le : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 w z)
      ≤ C1 * Work.FTS.Nonlin.Xn α w)
    (hprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N03g α w) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N03g α w) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N03g α w)
        ≤ (1 / α) * (((Cp * α ^ (-(1 / 2 : ℝ))) * (C1 * Work.FTS.Nonlin.Xn α w))
            * Work.FTS.Nonlin.Xn α w) := by
  have h1α : (0 : ℝ) < 1 / α := by positivity
  have hpα : 0 ≤ Cp * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCp.le (Real.rpow_nonneg hα.le _)
  have hXw0 : 0 ≤ Work.FTS.Nonlin.Xn α w := Work.Spaces.HkNorm_nonneg α 4 w
  have h1eq : Work.FTS.Nonlin.N03g α w
      = fun z θ => (1 / α) * (Work.Construction.L12 w z * w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
    ring
  have hrow := hprod
    (fun z θ => Work.Construction.L12 w z) w ⟨hL12sm, hL12mem⟩ ⟨hsmw, hmem4⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h1eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (1 / α)
      (Work.FTS.NonlinRows.smoothOpen_mul hL12sm hsmw)
  · rw [h1eq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (1 / α) hrow.1
  · rw [h1eq, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, abs_of_nonneg h1α.le]
    refine mul_le_mul_of_nonneg_left ?_ h1α.le
    exact le_trans hrow.2
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL12le hpα) hXw0)

/-- **Row 3 of the `N₀`-table**: `N₀₄ᵃ = D_θF_* · ((3/(2α))·L₁₂(w))`. -/
theorem row_N04aF {α Cw C1 CF : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 w z))
    (hL12mem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 w z))
    (hCw : 0 < Cw) (hC1 : 0 < C1) (hCF : 0 < CF)
    (hL12le : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 w z)
      ≤ C1 * Work.FTS.Nonlin.Xn α w)
    (hDthFWmem : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)))
    (hDthFWle : Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
      ≤ CF * α ^ 2)
    (hWprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04aF α w) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04aF α w) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N04aF α w)
        ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (CF * α ^ 2))
          * ((3 / (2 * α)) * (C1 * Work.FTS.Nonlin.Xn α w)) := by
  have h32 : (0 : ℝ) < 3 / (2 * α) := three_div_two_pos hα
  have hα2nn : 0 ≤ α ^ 2 := sq_nonneg α
  have hwα : 0 ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCw.le (Real.rpow_nonneg hα.le _)
  have hDthFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
    (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dth
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hL12sm
  have hAmem : Work.Spaces.HkMem α 4 (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hL12mem
  have hAle : Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z)
      ≤ (3 / (2 * α)) * (C1 * Work.FTS.Nonlin.Xn α w) := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, abs_of_nonneg h32.le]
    exact mul_le_mul_of_nonneg_left hL12le h32.le
  have h3eq : Work.FTS.Nonlin.N04aF α w
      = fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * ((3 / (2 * α)) * Work.Construction.L12 w z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a, Work.Construction.s2,
      Work.Spaces.Dth]
    ring
  have hrow := hWprod (Work.Spaces.Dth (Work.Construction.Fstar α))
    (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) hDthFsm hDthFWmem ⟨hAsm, hAmem⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h3eq]
    exact Work.FTS.NonlinRows.smoothOpen_mul hDthFsm hAsm
  · rw [h3eq]; exact hrow.1
  · rw [h3eq]
    refine le_trans hrow.2 ?_
    have hpos : 0 ≤ (Cw * α ^ (-(1 / 2 : ℝ))) * (CF * α ^ 2) :=
      mul_nonneg hwα (mul_nonneg hCF.le hα2nn)
    calc ((Cw * α ^ (-(1 / 2 : ℝ)))
            * Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)))
          * Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z)
        ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (CF * α ^ 2))
            * Work.FTS.Nonlin.Xn α
              (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDthFWle hwα)
            (Work.Spaces.HkNorm_nonneg α 4 _)
      _ ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (CF * α ^ 2))
            * ((3 / (2 * α)) * (C1 * Work.FTS.Nonlin.Xn α w)) :=
          mul_le_mul_of_nonneg_left hAle hpos

/-- **Row 4 of the `N₀`-table**: `N₀₄ᵇ = D_θw · ((3/(2α))·L₁₂(w))`. -/
theorem row_N04bF {α Cp C1 Bd : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hsmw : Work.FTS.EllipticEst.SmoothOpen w)
    (hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 w z))
    (hL12mem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 w z))
    (hCp : 0 < Cp) (hC1 : 0 < C1)
    (hL12le : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 w z)
      ≤ C1 * Work.FTS.Nonlin.Xn α w)
    (hDthw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth w))
    (hDthw_le : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth w) ≤ Bd) (hBd : 0 ≤ Bd)
    (hprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04bF α w) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α w) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N04bF α w)
        ≤ ((Cp * α ^ (-(1 / 2 : ℝ))) * Bd)
          * ((3 / (2 * α)) * (C1 * Work.FTS.Nonlin.Xn α w)) := by
  have h32 : (0 : ℝ) < 3 / (2 * α) := three_div_two_pos hα
  have hpα : 0 ≤ Cp * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCp.le (Real.rpow_nonneg hα.le _)
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hL12sm
  have hAmem : Work.Spaces.HkMem α 4 (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hL12mem
  have hAle : Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z)
      ≤ (3 / (2 * α)) * (C1 * Work.FTS.Nonlin.Xn α w) := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, abs_of_nonneg h32.le]
    exact mul_le_mul_of_nonneg_left hL12le h32.le
  have h4eq : Work.FTS.Nonlin.N04bF α w
      = fun z θ => Work.Spaces.Dth w z θ * ((3 / (2 * α)) * Work.Construction.L12 w z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.s2,
      Work.Spaces.Dth]
    ring
  have hrow := hprod (Work.Spaces.Dth w) (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z)
    ⟨hsmw.Dth, hDthw_mem⟩ ⟨hAsm, hAmem⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h4eq]
    exact Work.FTS.NonlinRows.smoothOpen_mul hsmw.Dth hAsm
  · rw [h4eq]; exact hrow.1
  · rw [h4eq]
    refine le_trans hrow.2 ?_
    have hpos : 0 ≤ (Cp * α ^ (-(1 / 2 : ℝ))) * Bd := mul_nonneg hpα hBd
    calc ((Cp * α ^ (-(1 / 2 : ℝ))) * Work.FTS.Nonlin.Xn α (Work.Spaces.Dth w))
          * Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z)
        ≤ ((Cp * α ^ (-(1 / 2 : ℝ))) * Bd)
            * Work.FTS.Nonlin.Xn α
              (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDthw_le hpα)
            (Work.Spaces.HkNorm_nonneg α 4 _)
      _ ≤ ((Cp * α ^ (-(1 / 2 : ℝ))) * Bd)
            * ((3 / (2 * α)) * (C1 * Work.FTS.Nonlin.Xn α w)) :=
          mul_le_mul_of_nonneg_left hAle hpos

/-- **Row 5 of the `N₀`-table**: `N₀₅ᵃ = D_zF_* · (-(c2m·L₁₂(w)))`. -/
theorem row_N05aF {α Cw Cdz CB : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hBsmt : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z))
    (hBmem : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z))
    (hBle : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) ≤ CB) (hCB : 0 ≤ CB)
    (hCw : 0 < Cw) (hCdz : 0 < Cdz)
    (hDzFWmem : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)))
    (hDzFWle : Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α))
      ≤ Cdz * α)
    (hWprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05aF α w) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05aF α w) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N05aF α w)
        ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (Cdz * α)) * CB := by
  have hαnn : 0 ≤ α := hα.le
  have hwα : 0 ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCw.le (Real.rpow_nonneg hα.le _)
  have hDzFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
    (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dz
  have h5sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(Work.Construction.c2m θ * Work.Construction.L12 w z)) := by
    refine (Work.FTS.NonlinRows.smoothOpen_const_mul (-1) hBsmt).congr ?_
    intro z θ _ _ _
    ring
  have h5memg : Work.Spaces.HkMem α 4
      (fun z θ => -(Work.Construction.c2m θ * Work.Construction.L12 w z)) :=
    mem_neg_apply hBmem
  have h5leg : Work.FTS.Nonlin.Xn α
      (fun z θ => -(Work.Construction.c2m θ * Work.Construction.L12 w z)) ≤ CB := by
    rw [Xn_neg_apply]
    exact hBle
  have h5eq : Work.FTS.Nonlin.N05aF α w
      = fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * (-(Work.Construction.c2m θ * Work.Construction.L12 w z)) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a]
    ring
  have hrow := hWprod (Work.Spaces.Dz (Work.Construction.Fstar α))
    (fun z θ => -(Work.Construction.c2m θ * Work.Construction.L12 w z))
    hDzFsm hDzFWmem ⟨h5sm, h5memg⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h5eq]
    exact Work.FTS.NonlinRows.smoothOpen_mul hDzFsm h5sm
  · rw [h5eq]; exact hrow.1
  · rw [h5eq]
    refine le_trans hrow.2 ?_
    have hpos : 0 ≤ (Cw * α ^ (-(1 / 2 : ℝ))) * (Cdz * α) :=
      mul_nonneg hwα (mul_nonneg hCdz.le hαnn)
    calc ((Cw * α ^ (-(1 / 2 : ℝ)))
            * Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)))
          * Work.FTS.Nonlin.Xn α
            (fun z θ => -(Work.Construction.c2m θ * Work.Construction.L12 w z))
        ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (Cdz * α))
            * Work.FTS.Nonlin.Xn α
              (fun z θ => -(Work.Construction.c2m θ * Work.Construction.L12 w z)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDzFWle hwα)
            (Work.Spaces.HkNorm_nonneg α 4 _)
      _ ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (Cdz * α)) * CB :=
          mul_le_mul_of_nonneg_left h5leg hpos

/-- **Row 6 of the `N₀`-table**: `N₀₅ᵇ = -((c2m·L₁₂(w)) · D_zw)`. -/
theorem row_N05bF {α Cp CB Bd : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hsmw : Work.FTS.EllipticEst.SmoothOpen w)
    (hBsmt : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z))
    (hBmem : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z))
    (hBle : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) ≤ CB)
    (hCB : 0 ≤ CB) (hCp : 0 < Cp)
    (hDzw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w))
    (hDzw_le : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ Bd) (hBd : 0 ≤ Bd)
    (hprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05bF α w) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05bF α w) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N05bF α w)
        ≤ ((Cp * α ^ (-(1 / 2 : ℝ))) * CB) * Bd := by
  have hpα : 0 ≤ Cp * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCp.le (Real.rpow_nonneg hα.le _)
  have h6eq : Work.FTS.Nonlin.N05bF α w
      = fun z θ => -((Work.Construction.c2m θ * Work.Construction.L12 w z)
          * Work.Spaces.Dz w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b]
    ring
  have h6eq' : Work.FTS.Nonlin.N05bF α w
      = fun z θ => (-(Work.Construction.c2m θ * Work.Construction.L12 w z))
          * Work.Spaces.Dz w z θ := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b]
    ring
  have hrow := hprod (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z)
    (Work.Spaces.Dz w) ⟨hBsmt, hBmem⟩ ⟨hsmw.Dz, hDzw_mem⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h6eq']
    exact Work.FTS.NonlinRows.smoothOpen_mul
      ((Work.FTS.NonlinRows.smoothOpen_const_mul (-1) hBsmt).congr (by
        intro z θ _ _ _; ring)) hsmw.Dz
  · rw [h6eq]
    exact mem_neg_apply hrow.1
  · rw [h6eq, Xn_neg_apply]
    refine le_trans hrow.2 ?_
    have hpos : 0 ≤ (Cp * α ^ (-(1 / 2 : ℝ))) * CB := mul_nonneg hpα hCB
    calc ((Cp * α ^ (-(1 / 2 : ℝ))) * Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z))
          * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w)
        ≤ ((Cp * α ^ (-(1 / 2 : ℝ))) * CB) * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBle hpα)
            (Work.Spaces.HkNorm_nonneg α 4 _)
      _ ≤ ((Cp * α ^ (-(1 / 2 : ℝ))) * CB) * Bd :=
          mul_le_mul_of_nonneg_left hDzw_le hpos

/-- **Row 7 of the `N₀`-table**: `N₀₆ = -((c2m·L₁₂(F_*)) · D_zw)`. -/
theorem row_N06F {α Cw Cw0 Bd : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hsmw : Work.FTS.EllipticEst.SmoothOpen w)
    (hDzw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w))
    (hDzw_le : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ Bd) (hBd : 0 ≤ Bd)
    (hc2mL12Fsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z))
    (hc2mL12FWmem : Work.Spaces.WlInfMem α 4
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z))
    (hc2mL12FWle : Work.Spaces.WlInf α 4
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z)
      ≤ Cw0 * α)
    (hCw : 0 < Cw) (hCw0 : 0 < Cw0)
    (hWprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N06F α w) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N06F α w) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N06F α w)
        ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (Cw0 * α)) * Bd := by
  have hαnn : 0 ≤ α := hα.le
  have hwα : 0 ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCw.le (Real.rpow_nonneg hα.le _)
  have h7eq : Work.FTS.Nonlin.N06F α w
      = fun z θ => -((Work.Construction.c2m θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z)
          * Work.Spaces.Dz w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06]
    ring
  have h7eq' : Work.FTS.Nonlin.N06F α w
      = fun z θ => (-(Work.Construction.c2m θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z))
          * Work.Spaces.Dz w z θ := by
    funext z θ
    simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06]
    ring
  have hrow := hWprod
    (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z)
    (Work.Spaces.Dz w) hc2mL12Fsm hc2mL12FWmem ⟨hsmw.Dz, hDzw_mem⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h7eq']
    exact Work.FTS.NonlinRows.smoothOpen_mul
      ((Work.FTS.NonlinRows.smoothOpen_const_mul (-1) hc2mL12Fsm).congr (by
        intro z θ _ _ _; ring)) hsmw.Dz
  · rw [h7eq]
    exact mem_neg_apply hrow.1
  · rw [h7eq, Xn_neg_apply]
    refine le_trans hrow.2 ?_
    have hpos : 0 ≤ (Cw * α ^ (-(1 / 2 : ℝ))) * (Cw0 * α) :=
      mul_nonneg hwα (mul_nonneg hCw0.le hαnn)
    calc ((Cw * α ^ (-(1 / 2 : ℝ))) * Work.Spaces.WlInf α 4
            (fun z θ => Work.Construction.c2m θ
              * Work.Construction.L12 (Work.Construction.Fstar α) z))
          * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w)
        ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (Cw0 * α)) * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc2mL12FWle hwα)
            (Work.Spaces.HkNorm_nonneg α 4 _)
      _ ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (Cw0 * α)) * Bd :=
          mul_le_mul_of_nonneg_left hDzw_le hpos

end Work.FTS.StrongEps.ClassCRHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.N0SubEqRsum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The telescoping identity of the `N₀`-difference.**

On the open quadrant `Qd`, the difference `N₀ α (F_*+W₁) W₁ − N₀ α (F_*+W₂) W₂` telescopes
exactly into the right-nested sum `Rsum α W₁ W₂ (W₁ − W₂) = P1 + (P2 + (P3 + (P4 + (P5 + (P6 +
(P7 + (P8 + P9)))))))` of the nine difference pieces `Work.FTS.GalFields.RHS.P1 … P9`
(`Submission/Work/FTS/GalFields/RHS/sharpN0_defs.lean`), where with `h := W₁ − W₂`:
`P1 = (1/α)·(L₁₂ W₁·h)`, `P2 = (1/α)·(L₁₂ h·W₂)`, `P3 = (3/2α)·(D_θF_*·L₁₂ h)`,
`P4 = (3/2α)·(L₁₂ W₁·D_θh)`, `P5 = (3/2α)·(L₁₂ h·D_θW₂)`, `P6 = -c2m·(D_zF_*·L₁₂ h)`,
`P7 = -c2m·(L₁₂ W₁·D_zh)`, `P8 = -c2m·(L₁₂ h·D_zW₂)`, `P9 = -(c2m·L₁₂F_*)·D_zh`.

Route (this is a pure algebraic identity; no estimates are needed):
* split each `N₀` with `Work.FTS.StrongEps.ClassCRHS.N0_split_open_aux hα hsm z θ hzθ` into
  `N0fix + (N03g + (N04aF + (N04bF + (N05aF + (N05bF + N06F)))))`;
* the six telescoping identities, all on `Qd`,
  `N03g α W₁ = N03g α W₂ + (P1 α W₁ h + P2 α W₂ h)`, `N04aF α W₁ = N04aF α W₂ + P3 α h`,
  `N04bF α W₁ = N04bF α W₂ + (P4 α W₁ h + P5 α W₂ h)`, `N05aF α W₁ = N05aF α W₂ + P6 α h`,
  `N05bF α W₁ = N05bF α W₂ + (P7 α W₁ h + P8 α W₂ h)`, `N06F α W₁ = N06F α W₂ + P9 α h`
  (copy the proofs from `Submission/Work/FTS/GalFields/RHS/sharp_N0_diff.lean`, `h3`, `h4a`,
  `h4b`, `h5a`, `h5b`, `h6`, or the same block in `SharpMod/N0_L12_diff.lean`; they only use
  `unfold`, `simp only`, `rw` and `ring`);
* the linearity inputs: `Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen` (needs `SmoothOpen`
  and `HkMem α 4` of both, and `z ≥ 0`), `pz_add_of_smoothOpen`, `pth_add_of_smoothOpen`
  (need only `SmoothOpen` and the pointwise decomposition `W₁ = W₂ + h`);
* finish with `simp only [Rsum, Pi.add_apply]` and `ring`. -/
theorem N0SubEqRsum {α : ℝ} (hα : 0 < α) {W₁ W₂ : Work.FTS.Galerkin.Fn}
    (hsm₁ : Work.FTS.EllipticEst.SmoothOpen W₁)
    (hsm₂ : Work.FTS.EllipticEst.SmoothOpen W₂)
    (hm₁ : Work.Spaces.HkMem α 4 W₁) (hm₂ : Work.Spaces.HkMem α 4 W₂) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
        - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ
      = Work.FTS.GalFields.RHS.Rsum α W₁ W₂ (fun z θ => W₁ z θ - W₂ z θ) z θ := by
  intro z θ hzθ
  have hz : 0 < z := hzθ.1
  have hθ0 : 0 < θ := hzθ.2.1
  have hθ1 : θ < π / 2 := hzθ.2.2
  set h : ℝ → ℝ → ℝ := fun z θ => W₁ z θ - W₂ z θ with hhdef
  have hsmh : Work.FTS.EllipticEst.SmoothOpen h := by
    rw [hhdef]
    exact Work.FTS.EllipticEst.smoothOpen_sub hsm₁ hsm₂
  have hgh : ∀ z' θ' : ℝ, W₁ z' θ' = W₂ z' θ' + h z' θ' := by
    intro z' θ'
    rw [hhdef]
    ring
  have hLadd : Work.Construction.L12 W₁ z
      = Work.Construction.L12 W₂ z + Work.Construction.L12 h z := by
    have hhfun : (fun z θ => W₁ z θ - W₂ z θ) = h := by rw [hhdef]
    have hsub := Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen hsm₁ hsm₂ hm₁ hm₂ z
      (le_of_lt hz)
    rw [hhfun] at hsub
    linarith
  have hpzadd : Work.Spaces.pz W₁ z θ
      = Work.Spaces.pz W₂ z θ + Work.Spaces.pz h z θ :=
    Work.FTS.GalFields.RHS.pz_add_of_smoothOpen hsm₂ hsmh hgh z θ hz hθ0 hθ1
  have hpthadd : Work.Spaces.pth W₁ z θ
      = Work.Spaces.pth W₂ z θ + Work.Spaces.pth h z θ :=
    Work.FTS.GalFields.RHS.pth_add_of_smoothOpen hsm₂ hsmh hgh z θ hz hθ0 hθ1
  have h3 : Work.FTS.Nonlin.N03g α W₁ z θ
      = Work.FTS.Nonlin.N03g α W₂ z θ
        + (Work.FTS.GalFields.RHS.P1 α W₁ h z θ + Work.FTS.GalFields.RHS.P2 α W₂ h z θ) := by
    unfold Work.FTS.GalFields.RHS.P1 Work.FTS.GalFields.RHS.P2
    simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
    rw [hgh z θ, hLadd]
    ring
  have h4a : Work.FTS.Nonlin.N04aF α W₁ z θ
      = Work.FTS.Nonlin.N04aF α W₂ z θ + Work.FTS.GalFields.RHS.P3 α h z θ := by
    unfold Work.FTS.GalFields.RHS.P3
    simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a, Work.Construction.s2,
      Work.Spaces.Dth]
    rw [hLadd]
    ring
  have h4b : Work.FTS.Nonlin.N04bF α W₁ z θ
      = Work.FTS.Nonlin.N04bF α W₂ z θ
        + (Work.FTS.GalFields.RHS.P4 α W₁ h z θ + Work.FTS.GalFields.RHS.P5 α W₂ h z θ) := by
    unfold Work.FTS.GalFields.RHS.P4 Work.FTS.GalFields.RHS.P5
    simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.s2,
      Work.Spaces.Dth]
    rw [hpthadd, hLadd]
    ring
  have h5a : Work.FTS.Nonlin.N05aF α W₁ z θ
      = Work.FTS.Nonlin.N05aF α W₂ z θ + Work.FTS.GalFields.RHS.P6 α h z θ := by
    unfold Work.FTS.GalFields.RHS.P6
    simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a]
    rw [hLadd]
    ring
  have h5b : Work.FTS.Nonlin.N05bF α W₁ z θ
      = Work.FTS.Nonlin.N05bF α W₂ z θ
        + (Work.FTS.GalFields.RHS.P7 α W₁ h z θ + Work.FTS.GalFields.RHS.P8 α W₂ h z θ) := by
    unfold Work.FTS.GalFields.RHS.P7 Work.FTS.GalFields.RHS.P8
    simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b, Work.Spaces.Dz]
    rw [hLadd, hpzadd]
    ring
  have h6 : Work.FTS.Nonlin.N06F α W₁ z θ
      = Work.FTS.Nonlin.N06F α W₂ z θ + Work.FTS.GalFields.RHS.P9 α h z θ := by
    unfold Work.FTS.GalFields.RHS.P9
    simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06, Work.Spaces.Dz]
    rw [hpzadd]
    ring
  rw [Work.FTS.StrongEps.ClassCRHS.N0_split_open_aux hα hsm₁ z θ hzθ,
    Work.FTS.StrongEps.ClassCRHS.N0_split_open_aux hα hsm₂ z θ hzθ]
  rw [h3, h4a, h4b, h5a, h5b, h6]
  simp only [Work.FTS.GalFields.RHS.Rsum, Pi.add_apply]
  ring

end Work.FTS.StrongEps.EpsRLX
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.slotT2Six =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

open MeasureTheory Set Filter
open scoped Real Topology


end Work.FTS.StrongPersist.N6Trans
end
