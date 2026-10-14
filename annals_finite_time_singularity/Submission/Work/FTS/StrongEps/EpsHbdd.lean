import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.StrongEps.EpsE4Thr.integrable_cross_slot_rpow
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Components2
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux
import Submission.Work.FTS.StrongEps.H5.Asm
import Submission.Work.FTS.StrongEps.H5.HAtoms5
import Submission.Work.FTS.StrongEps.H5.HkMemXnLGammaT5
import Submission.Work.FTS.StrongEps.H5.HkMemXnN5
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumGamSin
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.StarPkg6OfCore
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.RXVP.thLip
import Submission.Work.FTS_RegExport.THL.cs7_rop_split
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.L12Add
-- ===== merged: Submission.Work.FTS.EpsEngine.EpsRHSP_slotSup_of_val =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The slot sup bounds of the scheme's right-hand side, from value bounds of `epsWP`.** -/
theorem EpsRHSP_slotSup_of_val {α C₀ Ce Cs T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g : Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 0 ≤ T)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E)
    (hC : ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) s))
    (hb4 : ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ ε g) s) ≤ Ce)
    (hreg : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ ε Φs E g s))
    (hnorm : ∃ KW : ℝ, 0 ≤ KW ∧ ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 4 (epsWP α ρ ε Φs E g s) ∧
        Work.Spaces.HkNorm α 4 (epsWP α ρ ε Φs E g s) ≤ KW)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K,
      |Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C := by
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα.1 hα.2
  obtain ⟨CL, hCL0, hCL⟩ := abs_L12_Jeps_le (ρ := ρ) hρ
  obtain ⟨Cb, hCb0, hbump⟩ := exists_bound_mixed_bump K hK
  obtain ⟨KW, hKW0, hnorm'⟩ := hnorm
  have hc0 : 0 < pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  -- ### one bound per slot
  have key : ∀ j i : ℕ, j + i ≤ 4 → ∃ Cji : ℝ, 0 ≤ Cji ∧ ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K,
      |Work.Spaces.mixed j i (Pz (Jeps ρ ε (epsWP α ρ ε Φs E g s))) p.1 p.2| ≤ Cji := by
    intro j i hji
    obtain ⟨K', hK'c, hK'Q, hKK', Csl, hCsl0, hsl⟩ :=
      abs_mixed_Jeps_le_sup (ρ := ρ) hρ (ε := ε) hε j i K hK hKQ
    obtain ⟨B, hBpos, hBval⟩ :=
      epsWP_sup_le_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T)
        (ρ := ρ) (Φs := Φs) (E := E) (G := fun _ => g) (ε := fun _ => ε)
        hα hρ (fun _ => ⟨hε, hε1⟩) hT hc1 hc2 hEll hstar hml
        (fun _ _ hs => hC _ hs) (fun _ _ hs => hb4 _ hs) (fun _ _ hs => hb6 _ hs) hK'c hK'Q
    refine ⟨Csl * B + (CL * KW / pzNorm) * Cb, by positivity, ?_⟩
    intro s hs p hp
    have hXsm : Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ ε Φs E g s) := hreg s hs
    obtain ⟨hmem, hnb⟩ := hnorm' s hs
    -- the slot of the mollified profile, from the *value* bound of `epsWP`
    have h1 : |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2| ≤ Csl * B :=
      hsl (epsWP α ρ ε Φs E g s) hXsm B hBpos.le (fun q hq => hBval 0 s hs q hq) p hp
    -- the coefficient of the rank-one correction
    have h2 : |Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0| ≤ CL * KW :=
      hCL hα hε hε1 hKW0 ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hXsm) hmem hnb
    -- the slots of the correction profile
    have h3 : |Work.Spaces.mixed j i bump p.1 p.2| ≤ Cb := hbump j i hji p hp
    -- the slot identity of the projection
    have hJsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Jeps ρ ε (epsWP α ρ ε Φs E g s)))
        Quad := (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
          (smoothOpen_Jeps ρ hρ hε ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hXsm))
    have hsplit := Work.FTS.StrongEps.EpsE4Thr.mixed_Pz_eq (n := 4) (a := j) (b := i)
      (w := Jeps ρ ε (epsWP α ρ ε Φs E g s)) (hJsm 4) (by omega) (hKQ hp)
    rw [hsplit]
    calc |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2
          - (Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
            * Work.Spaces.mixed j i bump p.1 p.2|
        ≤ |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2|
          + |(Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
            * Work.Spaces.mixed j i bump p.1 p.2| := by
          calc |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2
                - (Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
                  * Work.Spaces.mixed j i bump p.1 p.2|
              = |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2
                  + -((Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
                    * Work.Spaces.mixed j i bump p.1 p.2)| := by rw [sub_eq_add_neg]
            _ ≤ |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2|
                  + |-((Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
                    * Work.Spaces.mixed j i bump p.1 p.2)| := abs_add_le _ _
            _ = |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2|
                  + |(Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
                    * Work.Spaces.mixed j i bump p.1 p.2| := by rw [abs_neg]
      _ ≤ Csl * B + (CL * KW / pzNorm) * Cb := by
          refine add_le_add h1 ?_
          rw [abs_mul]
          have hfac : |Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm|
              ≤ CL * KW / pzNorm := by
            rw [abs_div, abs_of_pos hc0]
            exact div_le_div_of_nonneg_right h2 hc0.le
          exact mul_le_mul hfac h3 (abs_nonneg _) (div_nonneg (mul_nonneg hCL0 hKW0) hc0.le)
  have key2 : ∀ j i : ℕ, ∃ Cji : ℝ, 0 ≤ Cji ∧ (j + i ≤ 4 → ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K,
      |Work.Spaces.mixed j i (Pz (Jeps ρ ε (epsWP α ρ ε Φs E g s))) p.1 p.2| ≤ Cji) := by
    intro j i
    by_cases h : j + i ≤ 4
    · obtain ⟨C, hC0, hC⟩ := key j i h
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' h⟩
  choose Csl hCsl using key2
  refine ⟨∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 5, Csl j i, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => (hCsl j i).1
  · intro j i hji s hs p hp
    have hmem : j ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
    have hmem2 : i ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
    have hsingle : Csl j i ≤ ∑ j' ∈ Finset.range 5, ∑ i' ∈ Finset.range 5, Csl j' i' := by
      refine le_trans (Finset.single_le_sum (f := fun i' => Csl j i')
        (fun i' _ => (hCsl j i').1) hmem2) ?_
      exact Finset.single_le_sum (f := fun j' => ∑ i' ∈ Finset.range 5, Csl j' i')
        (fun j' _ => Finset.sum_nonneg fun i' _ => (hCsl j' i').1) hmem
    exact le_trans ((hCsl j i).2 hji s hs p hp) hsingle

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.EpsRHSP_slotSup_of_val_six =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The slot sup bounds of the scheme's right-hand side, from value bounds of `epsWP`.** -/
theorem EpsRHSP_slotSup_of_val_six {α C₀ Ce Cs T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g : Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 0 ≤ T)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E)
    (hC : ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) s))
    (hb4 : ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ ε g) s) ≤ Ce)
    (hreg : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ ε Φs E g s))
    (hnorm : ∃ KW : ℝ, 0 ≤ KW ∧ ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 4 (epsWP α ρ ε Φs E g s) ∧
        Work.Spaces.HkNorm α 4 (epsWP α ρ ε Φs E g s) ≤ KW)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j i : ℕ), j + i ≤ 6 → ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K,
      |Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C := by
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα.1 hα.2
  obtain ⟨CL, hCL0, hCL⟩ := abs_L12_Jeps_le (ρ := ρ) hρ
  have hbump6 : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (j i : ℕ), j + i ≤ 6 → ∀ p ∈ K,
      |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| ≤ Cb := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => ∑ j ∈ Finset.range 7, ∑ i ∈ Finset.range 7,
        |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|) K := by
      refine continuousOn_finsetSum _ (fun j _ => continuousOn_finsetSum _ (fun i _ => ?_))
      exact ((Work.FTS.StrongEps.smoothOpen_bump.mixed j i).continuousOn.mono hKQ).abs
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
    refine ⟨max M 0, le_max_right _ _, ?_⟩
    intro j i hji p hp
    have hj : j ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
    have hi : i ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
    calc |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
        ≤ ∑ i' ∈ Finset.range 7, |Work.Spaces.mixed j i' Work.FTS.StrongEps.bump p.1 p.2| :=
          Finset.single_le_sum (f := fun i' => |Work.Spaces.mixed j i' Work.FTS.StrongEps.bump p.1 p.2|)
            (fun i' _ => abs_nonneg _) hi
      _ ≤ ∑ j' ∈ Finset.range 7, ∑ i' ∈ Finset.range 7,
            |Work.Spaces.mixed j' i' Work.FTS.StrongEps.bump p.1 p.2| :=
          Finset.single_le_sum (f := fun j' => ∑ i' ∈ Finset.range 7,
            |Work.Spaces.mixed j' i' Work.FTS.StrongEps.bump p.1 p.2|)
            (fun j' _ => Finset.sum_nonneg fun i' _ => abs_nonneg _) hj
      _ ≤ max M 0 := by
          have h1 : ‖(∑ j ∈ Finset.range 7, ∑ i ∈ Finset.range 7,
              |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|)‖
              = (∑ j ∈ Finset.range 7, ∑ i ∈ Finset.range 7,
                |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          calc (∑ j ∈ Finset.range 7, ∑ i ∈ Finset.range 7,
                |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|)
              = ‖(∑ j ∈ Finset.range 7, ∑ i ∈ Finset.range 7,
                  |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|)‖ := h1.symm
            _ ≤ M := hM p hp
            _ ≤ max M 0 := le_max_left _ _
  obtain ⟨Cb, hCb0, hbump⟩ := hbump6
  obtain ⟨KW, hKW0, hnorm'⟩ := hnorm
  have hc0 : 0 < pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  -- ### one bound per slot
  have key : ∀ j i : ℕ, j + i ≤ 6 → ∃ Cji : ℝ, 0 ≤ Cji ∧ ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K,
      |Work.Spaces.mixed j i (Pz (Jeps ρ ε (epsWP α ρ ε Φs E g s))) p.1 p.2| ≤ Cji := by
    intro j i hji
    obtain ⟨K', hK'c, hK'Q, hKK', Csl, hCsl0, hsl⟩ :=
      abs_mixed_Jeps_le_sup (ρ := ρ) hρ (ε := ε) hε j i K hK hKQ
    obtain ⟨B, hBpos, hBval⟩ :=
      epsWP_sup_le_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T)
        (ρ := ρ) (Φs := Φs) (E := E) (G := fun _ => g) (ε := fun _ => ε)
        hα hρ (fun _ => ⟨hε, hε1⟩) hT hc1 hc2 hEll hstar hml
        (fun _ _ hs => hC _ hs) (fun _ _ hs => hb4 _ hs) (fun _ _ hs => hb6 _ hs) hK'c hK'Q
    refine ⟨Csl * B + (CL * KW / pzNorm) * Cb, by positivity, ?_⟩
    intro s hs p hp
    have hXsm : Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ ε Φs E g s) := hreg s hs
    obtain ⟨hmem, hnb⟩ := hnorm' s hs
    -- the slot of the mollified profile, from the *value* bound of `epsWP`
    have h1 : |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2| ≤ Csl * B :=
      hsl (epsWP α ρ ε Φs E g s) hXsm B hBpos.le (fun q hq => hBval 0 s hs q hq) p hp
    -- the coefficient of the rank-one correction
    have h2 : |Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0| ≤ CL * KW :=
      hCL hα hε hε1 hKW0 ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hXsm) hmem hnb
    -- the slots of the correction profile
    have h3 : |Work.Spaces.mixed j i bump p.1 p.2| ≤ Cb := hbump j i hji p hp
    -- the slot identity of the projection
    have hJsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Jeps ρ ε (epsWP α ρ ε Φs E g s)))
        Quad := (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
          (smoothOpen_Jeps ρ hρ hε ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hXsm))
    have hsplit := Work.FTS.StrongEps.EpsE4Thr.mixed_Pz_eq (n := 6) (a := j) (b := i)
      (w := Jeps ρ ε (epsWP α ρ ε Φs E g s)) (hJsm 6) (by omega) (hKQ hp)
    rw [hsplit]
    calc |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2
          - (Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
            * Work.Spaces.mixed j i bump p.1 p.2|
        ≤ |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2|
          + |(Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
            * Work.Spaces.mixed j i bump p.1 p.2| := by
          calc |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2
                - (Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
                  * Work.Spaces.mixed j i bump p.1 p.2|
              = |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2
                  + -((Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
                    * Work.Spaces.mixed j i bump p.1 p.2)| := by rw [sub_eq_add_neg]
            _ ≤ |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2|
                  + |-((Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
                    * Work.Spaces.mixed j i bump p.1 p.2)| := abs_add_le _ _
            _ = |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2|
                  + |(Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
                    * Work.Spaces.mixed j i bump p.1 p.2| := by rw [abs_neg]
      _ ≤ Csl * B + (CL * KW / pzNorm) * Cb := by
          refine add_le_add h1 ?_
          rw [abs_mul]
          have hfac : |Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm|
              ≤ CL * KW / pzNorm := by
            rw [abs_div, abs_of_pos hc0]
            exact div_le_div_of_nonneg_right h2 hc0.le
          exact mul_le_mul hfac h3 (abs_nonneg _) (div_nonneg (mul_nonneg hCL0 hKW0) hc0.le)
  have key2 : ∀ j i : ℕ, ∃ Cji : ℝ, 0 ≤ Cji ∧ (j + i ≤ 6 → ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K,
      |Work.Spaces.mixed j i (Pz (Jeps ρ ε (epsWP α ρ ε Φs E g s))) p.1 p.2| ≤ Cji) := by
    intro j i
    by_cases h : j + i ≤ 6
    · obtain ⟨C, hC0, hC⟩ := key j i h
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' h⟩
  choose Csl hCsl using key2
  refine ⟨∑ j ∈ Finset.range 7, ∑ i ∈ Finset.range 7, Csl j i, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => (hCsl j i).1
  · intro j i hji s hs p hp
    have hmem : j ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
    have hmem2 : i ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
    have hsingle : Csl j i ≤ ∑ j' ∈ Finset.range 7, ∑ i' ∈ Finset.range 7, Csl j' i' := by
      refine le_trans (Finset.single_le_sum (f := fun i' => Csl j i')
        (fun i' _ => (hCsl j i').1) hmem2) ?_
      exact Finset.single_le_sum (f := fun j' => ∑ i' ∈ Finset.range 7, Csl j' i')
        (fun j' _ => Finset.sum_nonneg fun i' _ => (hCsl j' i').1) hmem
    exact le_trans ((hCsl j i).2 hji s hs p hp) hsingle

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.L12FtauAux.L12dens_add_Fstar_of_majorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2.L12FtauAux

/-- **The angular slice of a majorised continuous profile is integrable on `Iθ`.**

If `h` is continuous on the open quadrant `Q0 = (0,∞) × (0,π/2)` and is dominated
pointwise by `Maj σ` on every angular interval `(0,π/2)`, then for every `σ > 0` the
integrand `θ ↦ K θ · h σ θ / σ` of the `L₁₂`-density is integrable on the compact
interval `Iθ = [0,π/2]`: it is continuous on the co-null open interval `(0,π/2)` (hence
a.e.-strongly measurable on `Iθ`) and bounded there by `3·Maj σ / σ` (using `|K| ≤ 3`),
and `Iθ` has finite Lebesgue measure. -/
private lemma integrableOn_slice_of_majorant {h : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ}
    (hh : ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |h σ θ| ≤ Maj σ)
    {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * h σ θ / σ) Work.Spaces.Iθ := by
  have hK : ContinuousOn (fun θ => Work.Spaces.K θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    unfold Work.Spaces.K; fun_prop
  have hsl : ContinuousOn (fun θ => h σ θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hh.comp (continuous_const.prodMk continuous_id).continuousOn (fun θ hθ => ⟨hσ, hθ⟩)
  have hcont : ContinuousOn (fun θ => Work.Spaces.K θ * h σ θ / σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hK.mul hsl).div_const σ
  have hmeas1 : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.K θ * h σ θ / σ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  have hIoo : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := Real.pi / 2))
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.K θ * h σ θ / σ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [← hIoo]; exact hmeas1
  have hbdd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K θ * h σ θ / σ‖ ≤ 3 * Maj σ / σ := by
    rw [← hIoo]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    have hKb : |Work.Spaces.K θ| ≤ 3 := by
      unfold Work.Spaces.K
      rw [show |3 * Real.sin θ * Real.cos θ ^ 2| = 3 * |Real.sin θ| * |Real.cos θ| ^ 2 by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_pow]]
      nlinarith [Real.abs_sin_le_one θ, Real.abs_cos_le_one θ,
        abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ)]
    have hhb : |h σ θ| ≤ Maj σ := hbd σ (Set.mem_Ioi.mpr hσ) θ hθ
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hσ, abs_mul]
    have h1 : |Work.Spaces.K θ| * |h σ θ| ≤ 3 * Maj σ := by
      nlinarith [abs_nonneg (h σ θ)]
    rw [div_le_div_iff_of_pos_right hσ]
    exact h1
  exact MeasureTheory.IntegrableOn.of_bound (s := Work.Spaces.Iθ)
    (by rw [Work.Spaces.Iθ]; exact measure_Icc_lt_top) hmeas _ hbdd

theorem L12dens_add_Fstar_of_majorant {α : ℝ} (hα : 0 < α) {h : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ}
    (hh : ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |h σ θ| ≤ Maj σ)
    {σ : ℝ} (hσ : 0 < σ) :
    Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.Fstar α z θ + h z θ) σ
      = Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) σ
        + Work.FM.L12dens Work.Spaces.K h σ :=
  Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
    (Work.Stability.integrableOn_slice_Fstar α hα σ)
    (integrableOn_slice_of_majorant hh hbd hσ)

end Work.FTS.StrongEps.E5Aux2.L12FtauAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.L12FtauAux.L12dens_continuousAt_of_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2.L12FtauAux

set_option linter.unusedVariables false

open scoped Real
open MeasureTheory

/-- The `L₁₂`-density is the angular moment `∫ θ in Iθ, K θ * Y s θ` divided by `s`.

This is the definitional unfolding of `Work.FM.L12dens` together with the fact that the
division by the *constant* `s` may be pulled out of the integral. -/
theorem L12dens_eq_thetaIntegral_div (Y : ℝ → ℝ → ℝ) (s : ℝ) :
    Work.FM.L12dens Work.Spaces.K Y s
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Y s θ) / s := by
  rw [Work.FM.L12dens, MeasureTheory.integral_div, Work.Spaces.Iθ]

theorem L12dens_continuousAt_of_bound {Y : ℝ → ℝ → ℝ} {M z : ℝ}
    (hM : 0 ≤ M)
    (hY : ContinuousOn (Function.uncurry Y) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Y σ θ| ≤ M)
    (hz : 0 < z) :
    ContinuousAt (Work.FM.L12dens Work.Spaces.K Y) z := by
  -- The angular moment `s ↦ ∫ θ in Iθ, K θ * Y s θ` is continuous at `z`.
  have hQang : ContinuousAt
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Y s θ) z := by
    have h := Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds (f := Y)
      (s₀ := z) (A := M) hz (by simpa only [Work.FTS.EllipticEst.Q0] using hY)
      (fun s θ hs h0 h1 => hbd s (by simp only [Set.mem_Ioi]; linarith [hz, hs.1]) θ ⟨h0, h1⟩)
    simpa only [← Work.Elliptic.Ktheta_eq_K] using h
  -- Rewrite the density as `(angular moment) / s` and divide by the continuous, nonvanishing `s`.
  have hfun : (fun s => (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Y s θ) / s)
      = Work.FM.L12dens Work.Spaces.K Y :=
    funext fun s => (L12dens_eq_thetaIntegral_div Y s).symm
  rw [← hfun]
  exact hQang.div continuousAt_id (ne_of_gt hz)

end Work.FTS.StrongEps.E5Aux2.L12FtauAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.L12FtauAux.integrableOn_L12dens_of_majorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the `L₁₂`-density from a radial majorant

`Work.FM.L12dens K h s = ∫_{θ ∈ [0,π/2]} K θ · h s θ / s` with `K θ = 3 sin θ cos²θ`.  Since
`K ≥ 0` on `[0,π/2]` and `∫_{[0,π/2]} K = 1`, the elementary bound

`|L12dens K h s| ≤ (∫_θ |K θ|) · Maj s / s = Maj s / s`   (`s > 0`)

holds as soon as `|h s θ| ≤ Maj s` on the *open* interval `(0,π/2)` — the endpoints `θ = 0`,
`θ = π/2` are harmless because `K` vanishes there.  Hence, if `Maj s / s` is integrable on
`(0,∞)` and `h` is continuous on the open quadrant (which gives a.e. strong measurability of
the density, `Work.FTS.StrongEps.E5Aux2.aesm_L12dens_of_contOn`), then so is `L12dens K h`.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.E5Aux2.L12FtauAux

/-! ## Elementary angular facts about `K θ = 3 sin θ cos²θ` -/

/-- The angular weight `K` is continuous. -/
theorem continuous_K : Continuous Work.Spaces.K := by
  rw [show Work.Spaces.K = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 from by
    funext θ; rw [Work.Spaces.K]]
  exact (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)

/-- `K ≥ 0` on `Iθ = [0,π/2]`. -/
theorem K_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  exact mul_nonneg (mul_nonneg (by norm_num)
    (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])))
    (sq_nonneg _)

/-- `K` vanishes at the endpoints of `Iθ`: if `θ ∈ Iθ` but `θ ∉ (0,π/2)` then `θ` is `0` or
`π/2`, and `K` vanishes there. -/
theorem K_eq_zero_of_mem_Iθ_of_not_mem_Ioo {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (h : θ ∉ Set.Ioo (0 : ℝ) (Real.pi / 2)) : Work.Spaces.K θ = 0 := by
  have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
    rw [Set.mem_Ioo, not_and_or] at h
    rcases h with h | h
    · left; exact le_antisymm (not_lt.mp h) hθ.1
    · right; exact le_antisymm hθ.2 (not_lt.mp h)
  rcases hcases with rfl | rfl
  · rw [Work.Spaces.K, Real.sin_zero]; ring
  · rw [Work.Spaces.K, Real.cos_pi_div_two]; ring

/-- `-cos³` is a primitive of `K`. -/
theorem hasDerivAt_neg_cos_cube (x : ℝ) :
    HasDerivAt (fun t : ℝ => -(Real.cos t) ^ 3) (Work.Spaces.K x) x := by
  have h1 : HasDerivAt (fun t : ℝ => Real.cos t ^ 3)
      (3 * Real.cos x ^ 2 * -Real.sin x) x :=
    (Real.hasDerivAt_cos x).pow 3
  convert h1.neg using 1
  rw [Work.Spaces.K]; ring

/-- `∫_{Iθ} K θ = 1` (fundamental theorem of calculus with primitive `-cos³`). -/
theorem integral_K_Iθ : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ) = 1 := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
  have hInt : (∫ θ in (0 : ℝ)..(Real.pi / 2), Work.Spaces.K θ)
      = (fun t : ℝ => -(Real.cos t) ^ 3) (Real.pi / 2)
        - (fun t : ℝ => -(Real.cos t) ^ 3) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => -(Real.cos t) ^ 3)
      (fun x _ => hasDerivAt_neg_cos_cube x) (continuous_K.intervalIntegrable _ _)
  rw [hInt]
  norm_num [Real.cos_pi_div_two, Real.cos_zero]

/-- `∫_{Iθ} |K θ| = 1`. -/
theorem integral_abs_K_Iθ : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ|) = 1 := by
  have hms : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  rw [MeasureTheory.setIntegral_congr_fun hms
    (fun θ hθ => abs_of_nonneg (K_nonneg_of_mem_Iθ hθ)), integral_K_Iθ]

/-! ## The main theorem -/

theorem integrableOn_L12dens_of_majorant {h : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ}
    (hh : ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hMaj : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hbd : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |h σ θ| ≤ Maj σ) :
    MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K h) (Set.Ioi 0) := by
  -- the angular comparison function is integrable on the compact interval `Iθ`
  have hIntMaj : ∀ s ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Work.Spaces.K θ| * Maj s / s) Work.Spaces.Iθ := by
    intro s _
    have hc : Continuous fun θ : ℝ => |Work.Spaces.K θ| * Maj s / s :=
      (continuous_K.abs.mul continuous_const).div_const s
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  -- the pointwise domination `|L12dens K h s| ≤ Maj s / s` for `s > 0`
  have hle : ∀ s ∈ Set.Ioi (0 : ℝ),
      |Work.FM.L12dens Work.Spaces.K h s| ≤ Maj s / s := by
    intro s hs
    have hs0 : 0 < s := hs
    show |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h s θ / s| ≤ Maj s / s
    calc |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h s θ / s|
        = ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h s θ / s‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Spaces.K θ * h s θ / s‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ| * Maj s / s := by
          refine MeasureTheory.setIntegral_mono_of_nonneg (fun θ _ => norm_nonneg _)
            (fun θ hθ => ?_) (hIntMaj s hs)
          rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hs0]
          by_cases hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
          · exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hbd s hs θ hmem) (abs_nonneg _)) hs0.le
          · rw [K_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hmem]; simp
      _ = (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ|) * (Maj s / s) := by
          rw [show (fun θ => |Work.Spaces.K θ| * Maj s / s)
              = (fun θ => |Work.Spaces.K θ| * (Maj s / s)) from by funext θ; ring]
          exact MeasureTheory.integral_mul_const _ _
      _ = Maj s / s := by rw [integral_abs_K_Iθ, one_mul]
  refine MeasureTheory.Integrable.mono' hMaj
    (Work.FTS.StrongEps.E5Aux2.aesm_L12dens_of_contOn hh) ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall (fun s hs => ?_)
  rw [Real.norm_eq_abs]
  exact hle s hs

end Work.FTS.StrongEps.E5Aux2.L12FtauAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.MuHDens =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `MuHDens` — the angular dominated-convergence step for the `L₁₂`-density

`l12dens_tendsto_of_slot`: a pointwise domination of a family of profiles by `C/sin(2θ)` on the
open quadrant, together with the pointwise convergence of the profiles there and the a.e.
measurability of the angular slices, gives the convergence of the `L₁₂`-densities at every
`s > 0`.

This is `dens_tendsto_of_slot_tendsto` (`E5Aux.dens_tendsto_of_slot_tendsto`) with the two
hypotheses about the *limit* (`hmeasl`, `hdoml`) removed: the dominated-convergence theorem for
the `θ`-integral needs measurability and domination only for the *sequence*.

(The earlier draft of this file contained its own `K_nonneg_of_mem_Iθ` and `K_eq`; the first is
already in `E5Aux2.AbsL12densLe` under exactly that name, and the second is renamed here to
`K_eq_sin_two_mul`.)
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false

/-- `K θ = (3/2)·sin(2θ)·cos θ`. -/
theorem K_eq_sin_two_mul (θ : ℝ) : Work.Spaces.K θ = 3 / 2 * Real.sin (2 * θ) * Real.cos θ := by
  rw [Work.Spaces.K, Real.sin_two_mul]; ring

/-- `K θ = 0` at both endpoints of `Iθ`. -/
theorem K_at_endpoints : Work.Spaces.K 0 = 0 ∧ Work.Spaces.K (Real.pi / 2) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [Work.Spaces.K]; simp
  · rw [Work.Spaces.K, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring

/-- The angular density of the family converges, from a domination by `C/sin(2θ)` on the open
quadrant and the pointwise convergence of the profiles there.  Only the *sequence* needs to be
measurable and dominated. -/
theorem l12dens_tendsto_of_slot {Yk : ℕ → ℝ → ℝ → ℝ} {Y : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmeas : ∀ k : ℕ, ∀ s ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.K θ * Yk k s θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hdom : ∀ k : ℕ, ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      |Yk k z θ| ≤ C / Real.sin (2 * θ))
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun k : ℕ => Yk k z θ) Filter.atTop (nhds (Y z θ))) :
    ∀ s ∈ Set.Ioi (0 : ℝ), Filter.Tendsto (fun k : ℕ => Work.FM.L12dens Work.Spaces.K (Yk k) s)
      Filter.atTop (nhds (Work.FM.L12dens Work.Spaces.K Y s)) := by
  intro s hs
  -- the dominating function `(3C/2)·cos θ`
  have hb : MeasureTheory.Integrable (fun θ : ℝ => 3 * C / 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (continuous_const.mul Real.continuous_cos).continuousOn.integrableOn_compact isCompact_Icc
  -- the pointwise domination of every slice
  have hbound : ∀ k : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K θ * Yk k s θ‖ ≤ 3 * C / 2 * Real.cos θ := by
    intro k
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall fun θ hθ => ?_)
    rcases lt_or_eq_of_le hθ.1 with h0 | h0
    · rcases lt_or_eq_of_le hθ.2 with h2 | h2
      · have hKnn : 0 ≤ Work.Spaces.K θ := K_nonneg_of_mem_Iθ hθ
        have hs2 : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
        have hkey : Work.Spaces.K θ * (C / Real.sin (2 * θ)) = 3 * C / 2 * Real.cos θ := by
          rw [K_eq_sin_two_mul]; field_simp
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hKnn]
        calc Work.Spaces.K θ * |Yk k s θ|
            ≤ Work.Spaces.K θ * (C / Real.sin (2 * θ)) :=
              mul_le_mul_of_nonneg_left (hdom k s θ ⟨hs, h0, h2⟩) hKnn
          _ = 3 * C / 2 * Real.cos θ := hkey
      · subst h2
        rw [Real.norm_eq_abs, K_at_endpoints.2, zero_mul, abs_zero, Real.cos_pi_div_two, mul_zero]
    · subst h0
      rw [Real.norm_eq_abs, K_at_endpoints.1, zero_mul, abs_zero, Real.cos_zero, mul_one]
      linarith [hC]
  -- the a.e. convergence of the slices
  have hlim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun k : ℕ => Work.Spaces.K θ * Yk k s θ) Filter.atTop
        (nhds (Work.Spaces.K θ * Y s θ)) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall fun θ hθ => ?_)
    rcases lt_or_eq_of_le hθ.1 with h0 | h0
    · rcases lt_or_eq_of_le hθ.2 with h2 | h2
      · exact (hconv s θ ⟨hs, h0, h2⟩).const_mul _
      · subst h2
        have h1 : (fun k : ℕ => Work.Spaces.K (Real.pi / 2) * Yk k s (Real.pi / 2))
            = fun _ : ℕ => (0 : ℝ) := by
          funext k; rw [K_at_endpoints.2, zero_mul]
        have h2' : Work.Spaces.K (Real.pi / 2) * Y s (Real.pi / 2) = 0 := by
          rw [K_at_endpoints.2, zero_mul]
        rw [h1, h2']; exact tendsto_const_nhds
    · subst h0
      have h1 : (fun k : ℕ => Work.Spaces.K 0 * Yk k s 0) = fun _ : ℕ => (0 : ℝ) := by
        funext k; rw [K_at_endpoints.1, zero_mul]
      have h2' : Work.Spaces.K 0 * Y s 0 = 0 := by rw [K_at_endpoints.1, zero_mul]
      rw [h1, h2']; exact tendsto_const_nhds
  have h := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (F := fun (k : ℕ) (θ : ℝ) => Work.Spaces.K θ * Yk k s θ)
    (f := fun θ : ℝ => Work.Spaces.K θ * Y s θ)
    (bound := fun θ : ℝ => 3 * C / 2 * Real.cos θ)
    (fun k => hmeas k s hs) hb hbound hlim
  simpa only [Work.FM.L12dens, Work.Spaces.Iθ, MeasureTheory.integral_div] using h.div_const s

end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.PT.L12densFstar_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2.PT

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# Convergence of the angular `L₁₂`-density of `F_* + wₙ`

The density of the model operator is the angular integral

`L12dens f x = ∫_θ K(θ) f(x,θ) / x`   (`θ` over `Iθ = [0,π/2]`),

with `K(θ) = 3 sin θ cos²θ`.  Here `f = F_* + wₙ`, where `F_* = Construction.Fstar α` is the
fixed profile — whose angular slice `θ ↦ F_*(x,θ)` is *continuous on the closed* interval
`Iθ` because the exponent `α/3` of `Γ(θ) = (sin θ cos²θ)^{α/3}` is positive — and `wₙ` is a
sequence dominated by the constant `C` on the open quadrant, converging pointwise there.

Since the complement of the open quadrant inside `Iθ` is the two-point null set
`{0,π/2}`, the pointwise convergence and the domination hold a.e.; the dominating function
`θ ↦ |K θ| (|F_*(x,θ)| + C)/x` is continuous on the compact `Iθ` (as `x ≠ 0`), hence
integrable, and the dominated convergence theorem gives the density limit at every `x > 0`.

Axioms: `[propext, Classical.choice, Quot.sound]`.
-/

/-- **Convergence of the `L₁₂`-density of `F_* + wₙ`.**  If the profiles `wₙ` are uniformly
bounded on the open quadrant `Qd = (0,∞) × (0,π/2)` and converge pointwise there to `W`, then
at every `x > 0` the angular densities of `F_* + wₙ` converge to that of `F_* + W`, by
dominated convergence in `θ` (the angular slices `θ ↦ wₙ x θ` being a.e.-strongly
measurable). -/
theorem L12densFstar_tendsto {α C : ℝ} (hα : α ∈ Set.Ioc 0 1) {w : ℕ → ℝ → ℝ → ℝ} {W : ℝ → ℝ → ℝ}
    (hbd : ∀ (n : ℕ) (z θ : ℝ), (z, θ) ∈ Work.Construction.Qd → |w n z θ| ≤ C)
    (hconv : ∀ (z θ : ℝ), (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => w n z θ) Filter.atTop (nhds (W z θ)))
    {x : ℝ} (hx : 0 < x)
    (hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (fun θ => w n x θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x) Filter.atTop
      (nhds (Work.Construction.L12dens (fun z θ => Work.Construction.Fstar α z θ + W z θ) x)) := by
  have hαpos : 0 < α := hα.1
  have hα3 : (0 : ℝ) ≤ α / 3 := div_nonneg hαpos.le (by norm_num)
  -- The angular slice of the reference profile `F_*` is continuous on the *closed* interval.
  have hGam : ContinuousOn (fun θ : ℝ => Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
    have hbase : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ := by
      fun_prop
    exact hbase.rpow_const (fun _ _ => Or.inr hα3)
  have hcontF : ContinuousOn (fun θ : ℝ => Work.Construction.Fstar α x θ) Work.Spaces.Iθ := by
    simp only [Work.Construction.Fstar]
    exact (continuousOn_const.mul (hGam.div_const (Work.Spaces.c α))).mul continuousOn_const
  have hKcont : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
    unfold Work.Spaces.K
    fun_prop
  -- A.e. the angle lies in the open interval, where the hypotheses on `w` apply.
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ))
      (b := Real.pi / 2)] with θ h
    exact fun hmem => h.mpr hmem
  -- Measurability of the integrand, from the a.e.-measurability of the slice of `wₙ`.
  have hmeas' : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.K θ * (Work.Construction.Fstar α x θ + w n x θ) / x)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro n
    have hKae : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.K θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hKcont.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self
    have hFae : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.Construction.Fstar α x θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hcontF.aestronglyMeasurable measurableSet_Icc
    have hsum : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.Construction.Fstar α x θ + w n x θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hFae.add (hmeas n)
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.Spaces.K θ * (Work.Construction.Fstar α x θ + w n x θ) * x⁻¹)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hKae.mul hsum).mul_const x⁻¹
    simpa only [div_eq_mul_inv] using h1
  -- Integrability of the dominating function: continuous on the compact `Iθ`.
  have hboundcont : ContinuousOn
      (fun θ : ℝ => |Work.Spaces.K θ| * (|Work.Construction.Fstar α x θ| + C) / x)
      Work.Spaces.Iθ :=
    ((hKcont.continuousOn.abs).mul ((hcontF.abs).add continuousOn_const)).div_const x
  have hboundInt : MeasureTheory.Integrable
      (fun θ : ℝ => |Work.Spaces.K θ| * (|Work.Construction.Fstar α x θ| + C) / x)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ContinuousOn.integrableOn_compact isCompact_Icc hboundcont
  -- The domination, a.e. in `θ`.
  have hbound : ∀ n : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K θ * (Work.Construction.Fstar α x θ + w n x θ) / x‖
        ≤ |Work.Spaces.K θ| * (|Work.Construction.Fstar α x θ| + C) / x := by
    intro n
    filter_upwards [haeθ] with θ hθ
    have hw : |w n x θ| ≤ C := hbd n x θ ⟨hx, hθ⟩
    have h1 : |Work.Construction.Fstar α x θ + w n x θ|
        ≤ |Work.Construction.Fstar α x θ| + C :=
      le_trans (abs_add_le _ _) (add_le_add le_rfl hw)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hx]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) hx.le
  -- The pointwise convergence, a.e. in `θ`.
  have hlim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto
        (fun n : ℕ => Work.Spaces.K θ * (Work.Construction.Fstar α x θ + w n x θ) / x)
        Filter.atTop
        (nhds (Work.Spaces.K θ * (Work.Construction.Fstar α x θ + W x θ) / x)) := by
    filter_upwards [haeθ] with θ hθ
    have h2 : Filter.Tendsto (fun n : ℕ => Work.Construction.Fstar α x θ + w n x θ)
        Filter.atTop (nhds (Work.Construction.Fstar α x θ + W x θ)) :=
      tendsto_const_nhds.add (hconv x θ ⟨hx, hθ⟩)
    have h3 := h2.div_const x
    have h4 : Filter.Tendsto
        (fun n : ℕ => Work.Spaces.K θ * ((Work.Construction.Fstar α x θ + w n x θ) / x))
        Filter.atTop
        (nhds (Work.Spaces.K θ * ((Work.Construction.Fstar α x θ + W x θ) / x))) :=
      tendsto_const_nhds.mul h3
    simpa only [mul_div_assoc] using h4
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (F := fun (n : ℕ) (θ : ℝ) =>
      Work.Spaces.K θ * (Work.Construction.Fstar α x θ + w n x θ) / x)
    (f := fun θ : ℝ => Work.Spaces.K θ * (Work.Construction.Fstar α x θ + W x θ) / x)
    (fun θ : ℝ => |Work.Spaces.K θ| * (|Work.Construction.Fstar α x θ| + C) / x)
    hmeas' hboundInt hbound hlim
  simpa only [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ] using hmain

end Work.FTS.StrongEps.E5Aux2.PT
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.l12dens_transport_tendsto_at =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pointwise convergence of the `L₁₂`-density of the transport block

Along the `ε`-scheme (`ε n → 0`), the angular density of the *transport* block of the projected
`J_ε`-slices converges at every `z > 0`:

  `L12dens K (Transport (slice (JfamP ρ (ε n) (G n)) s)) z ⟶ L12dens K (Transport (slice g s)) z`.

The mathematics is a single dominated-convergence theorem in the angular variable:

* the `θ`-integrand is `θ ↦ K θ · Transport f z θ / z = K θ · 3 D_θ f z θ/((1+z)z)`, and
  `D_θ f = mixed 0 1 f` definitionally, so the *slot* convergence
  `mixed 0 1 (JfamP-slice) z θ → mixed 0 1 g z θ` on the open quadrant (`mixed_JfamP_tendsto`, at
  `(j,i) = (0,1)`) gives the pointwise convergence of the integrand at every interior `θ`; at the
  two endpoints `θ = 0, π/2` the factor `K θ` vanishes, so there is nothing to prove;
* the domination is supplied by the `SlotMaj 1` clause of `EpsDecay`, which bounds
  `|D_θ (slice (JfamP ρ (ε n) (G n)) s) z θ|` by `Maj z` for *every* `θ`, whence
  `|K θ · Transport · / z| ≤ K θ · (3 Maj z/(1+z))/z` (the slot-to-transport step is the shared
  lemma `E5Aux2.abs_Transport_slotMaj_le`), a continuous (hence integrable) function
  of `θ` on the compact `Iθ`;
* the a.e. strong measurability of the integrands is the joint continuity hypothesis `hcont`,
  through `MuHGlue.aesm_slice_K_of_contOn` (which only needs continuity on the open quadrant,
  because the two angular endpoints are null in `Iθ`).

This is the `θ`-step feeding the `z`-dominated convergence of the radial functional
`L₁₂(Transport ·)(0)` (`E5Aux2.l12Transport_JfamP_tendsto`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

/-- The transport block in *slot* form: `Transport f z θ = 3 D_θ f z θ/(1+z)` with
`D_θ f = mixed 0 1 f` holds definitionally; the right-hand side is written in the `mixed`-form
used by the slot bounds of `EpsDecay`. -/
private theorem Transport_eq_slot (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Coercivity.Transport f z θ = 3 * Work.Spaces.mixed 0 1 f z θ / (1 + z) := rfl

theorem l12dens_transport_tendsto_at {α B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {s : ℝ} {Maj : ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) s)) Work.FTS.StrongEps.Quad)
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) s)
      (Work.FTS.Galerkin.slice g s))
    (hcont : ∀ n : ℕ, ContinuousOn (Function.uncurry (Work.Coercivity.Transport
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)))
      Work.FTS.EllipticEst.Q0)
    (hDec : ∀ n : ℕ, Work.FTS.StrongEps.EpsDecay α ρ Φs E (ε n) s (G n) Maj)
    (hl12 : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) s)) 0)
      Filter.atTop (nhds 0))
    {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun n : ℕ => Work.FM.L12dens Work.Spaces.K
        (Work.Coercivity.Transport
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z)
      Filter.atTop
      (nhds (Work.FM.L12dens Work.Spaces.K
        (Work.Coercivity.Transport (Work.FTS.Galerkin.slice g s)) z)) := by
  -- the hypothesis `hsm` in the shape demanded by `mixed_JfamP_tendsto`
  have hsm' : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k
      (Function.uncurry (Work.FTS.Galerkin.slice (G n) s))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n k => by simpa only [Work.FTS.StrongEps.Quad] using hsm n k
  -- **The dominated convergence theorem for the angular integral.**
  have hmain : Filter.Tendsto (fun n : ℕ => ∫ θ,
      Work.Spaces.K θ * Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ / z
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      Filter.atTop (nhds (∫ θ,
        Work.Spaces.K θ * Work.Coercivity.Transport (Work.FTS.Galerkin.slice g s) z θ / z
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (F := fun (n : ℕ) (θ : ℝ) => Work.Spaces.K θ * Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ / z)
      (f := fun θ : ℝ => Work.Spaces.K θ * Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice g s) z θ / z)
      (bound := fun θ : ℝ => Work.Spaces.K θ * (3 * Maj z / (1 + z)) / z)
      ?_ ?_ ?_ ?_
    · -- a.e. strong measurability of the integrands, from joint continuity on the open quadrant
      intro n
      have h1 := aesm_slice_K_of_contOn (hcont n) hz
      have h2 : MeasureTheory.AEStronglyMeasurable
          (fun θ => (1 / z) * (Work.Spaces.K θ * Work.Coercivity.Transport
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := h1.const_mul (1 / z)
      exact h2.congr (Filter.Eventually.of_forall fun θ => by ring)
    · -- integrability of the majorant (`K` is continuous and `Iθ` is compact)
      exact (((Work.FTS.StrongEps.E5Aux2.continuous_K.mul continuous_const).div_const z)
        |>.continuousOn).integrableOn_compact isCompact_Icc
    · -- the pointwise domination, from the `SlotMaj 1` clause of `EpsDecay`
      intro n
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
      have hKnn : 0 ≤ Work.Spaces.K θ := K_nonneg_of_mem_Iθ hθ
      have hb : |Work.Coercivity.Transport (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ| ≤ 3 * Maj z / (1 + z) :=
        abs_Transport_slotMaj_le hz
          (fun θ' => (hDec n).2.2.2.1 z hz θ' 0 1 (by norm_num)) θ
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hKnn, abs_of_pos hz]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hKnn) hz.le
    · -- a.e. convergence of the integrands (`K` vanishes at the two angular endpoints)
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · have hθ0 : θ = 0 := h0.symm
        rw [hθ0]
        have hK0 : Work.Spaces.K 0 = 0 := by simp [Work.Spaces.K]
        simp only [hK0, zero_mul, zero_div]
        exact tendsto_const_nhds
      · rcases eq_or_lt_of_le hθ.2 with h2 | h2
        · have hθ2 : θ = Real.pi / 2 := h2
          rw [hθ2]
          have hKp : Work.Spaces.K (Real.pi / 2) = 0 := by
            simp [Work.Spaces.K, Real.cos_pi_div_two]
          simp only [hKp, zero_mul, zero_div]
          exact tendsto_const_nhds
        · -- interior: the slot convergence at `(j,i) = (0,1)`
          have hp : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨hz, h0, h2⟩
          have hX := Work.FTS.StrongEps.mixed_JfamP_tendsto hρ hsm' hconv
            (fun n => (hε n).1) hε0 hl12 hp (j := 0) (i := 1) (by norm_num)
          have hT : Filter.Tendsto (fun n : ℕ => Work.Coercivity.Transport
              (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)
              Filter.atTop (nhds (Work.Coercivity.Transport
                (Work.FTS.Galerkin.slice g s) z θ)) := by
            simpa only [Transport_eq_slot] using (hX.const_mul 3).div_const (1 + z)
          simpa only [mul_assoc, mul_div_assoc] using
            ((hT.const_mul (Work.Spaces.K θ)).div_const z)
  simpa only [Work.FM.L12dens, Work.Spaces.Iθ] using hmain

end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.prof_cont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Continuity of the elliptic-correction block `N` from `C¹` data

`N α F Φ` is an algebraic combination of the profile `F = F_* + w`, of its two moments
`z ↦ L₁₂(F)(z)` and `z ↦ FK(F)(z)`, and of the three transported coefficients
`ℛ(Φ̃)`, `𝒰(Φ̃)`, `𝒱(Φ̃)` of the residual stream function `Φ̃ = Φ - (1/(4α)) sin(2θ) L₁₂(F)`.

The contrast with `smoothOpen_N_gen` (`FTS/StrongEps/smoothOpen_dynRHS.lean`) is that the
stream function `Φ` is only *`C¹`* on the open quadrant — the case of the `ε`-scheme's limit
object — so the three coefficients are only continuous, not smooth.  Everything else is
smooth, and the only `Φ`-input is that `Φ̃` is `C¹` on the open quadrant (a `C¹` difference),
whose continuity feeds the coefficient lemma `prof_cont_ops`. -/

/-- **`N α F Φ` is continuous on the open quadrant from `C¹` data on `Φ`.** -/
theorem continuousOn_N_gen {α : ℝ} {F Φ : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hL12F : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 F z))
    (hFK : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK F z))
    (hΦ : ContDiffOn ℝ 1 (Function.uncurry Φ) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Function.uncurry (Work.Construction.N α F Φ))
      Work.FTS.EllipticEst.Q0 := by
  -- the singular part `Θ = (1/(4α)) sin(2θ) L₁₂(F)` is smooth
  have hTheta : ContDiffOn ℝ 1
      (Function.uncurry (Work.Construction.Theta α F)) Work.FTS.EllipticEst.Q0 := by
    have hs2 : Work.FTS.EllipticEst.SmoothOpen
        (fun _ (θ : ℝ) => Real.sin (2 * θ)) := Work.FTS.GalFields.RHS.smoothOpen_sin_two
    have h := (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul hs2 hL12F)).forall 1
    refine h.congr ?_
    intro p hp
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.Construction.Theta, Work.Construction.s2]
    ring
  -- the residual `Φ̃ = Φ - Θ` is `C¹`, hence continuous
  have hPsi_c1 : ContDiffOn ℝ 1
      (Function.uncurry (Work.Construction.PhiTil α F Φ)) Work.FTS.EllipticEst.Q0 := by
    refine (hΦ.sub hTheta).congr ?_
    intro p hp
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.Construction.PhiTil]
  -- the three transported coefficients
  obtain ⟨hR, hU, hV⟩ := prof_cont_ops (α := α) hPsi_c1
  have hFc : ContinuousOn (Function.uncurry F) Work.FTS.EllipticEst.Q0 := hF.continuousOn
  have hpthF : ContinuousOn (Function.uncurry (Work.Spaces.pth F))
      Work.FTS.EllipticEst.Q0 := hF.pth.continuousOn
  have hDzF : ContinuousOn (Function.uncurry (Work.Spaces.Dz F))
      Work.FTS.EllipticEst.Q0 := hF.Dz.continuousOn
  have hFKc : ContinuousOn (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK F z))
      Work.FTS.EllipticEst.Q0 := hFK.continuousOn
  have hs2c : ContinuousOn (Function.uncurry (fun _ (θ : ℝ) => Work.Construction.s2 θ))
      Work.FTS.EllipticEst.Q0 := Work.FTS.GalFields.RHS.smoothOpen_sin_two.continuousOn
  have hsin2c : ContinuousOn (Function.uncurry (fun _ (θ : ℝ) => Real.sin θ ^ 2))
      Work.FTS.EllipticEst.Q0 := Work.FTS.GalFields.RHS.smoothOpen_sin_sq.continuousOn
  have t1 : ContinuousOn (fun p : ℝ × ℝ => 2 * Work.Construction.Rop α
      (Work.Construction.PhiTil α F Φ) p.1 p.2 * F p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (continuousOn_const.mul hR).mul hFc
  have t2 : ContinuousOn (fun p : ℝ × ℝ => 2 * Work.Construction.Uop α
      (Work.Construction.PhiTil α F Φ) p.1 p.2 * Work.Spaces.pth F p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (continuousOn_const.mul hU).mul hpthF
  have t3 : ContinuousOn (fun p : ℝ × ℝ => 2 * α * Work.Construction.Vop
      (Work.Construction.PhiTil α F Φ) p.1 p.2 * Work.Spaces.Dz F p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    ((continuousOn_const (c := (2 : ℝ) * α)).mul hV).mul hDzF
  have t4 : ContinuousOn (fun p : ℝ × ℝ => (1 / 2) * Work.Construction.s2 p.2
      * Work.Construction.FK F p.1 * Work.Spaces.pth F p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    ((continuousOn_const.mul hs2c).mul hFKc).mul hpthF
  have t5 : ContinuousOn (fun p : ℝ × ℝ => Real.sin p.2 ^ 2 * Work.Construction.FK F p.1
      * F p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (hsin2c.mul hFKc).mul hFc
  have key : ContinuousOn (fun p : ℝ × ℝ =>
      2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) p.1 p.2 * F p.1 p.2
        - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) p.1 p.2
          * Work.Spaces.pth F p.1 p.2
        - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Φ) p.1 p.2
          * Work.Spaces.Dz F p.1 p.2
        - (1 / 2) * Work.Construction.s2 p.2 * Work.Construction.FK F p.1
          * Work.Spaces.pth F p.1 p.2
        - Real.sin p.2 ^ 2 * Work.Construction.FK F p.1 * F p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (((t1.sub t2).sub t3).sub t4).sub t5
  refine key.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry_apply_pair, Work.Construction.N]

/-! ## The target -/

/-- **The three right-hand-side blocks of the `ε`-scheme are jointly continuous on the open
quadrant**, for a profile `w` of the class `ClassC α` and a stream function `Φ` which is only
`C¹` on the open quadrant.

* `N₀ α (F_* + w) w` is smooth: `SmoothN0` with the `C^∞`-radial moment
  `z ↦ L₁₂(w)(z)` supplied by the class alone (`smoothOpen_L12_radial_classC`);
* `N α (F_* + w) Φ` is only continuous, because `Φ` is: `continuousOn_N_gen`, whose
  `Φ`-input is the `C¹`-difference `Φ̃ = Φ - (1/(4α)) sin(2θ) L₁₂(F_* + w)`;
* `Transport w = 3 D_θw/(1+z)` is continuous: `continuousOn_uncurry_transport`. -/
theorem prof_cont {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {w Φ : ℝ → ℝ → ℝ}
    (hw : Work.FTS.ClassC.ClassC α w)
    (hΦ : ContDiffOn ℝ 1 (Function.uncurry Φ) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Function.uncurry
        (Work.Construction.N0 α (Work.Construction.Ftot α w) w)) Work.FTS.EllipticEst.Q0 ∧
    ContinuousOn (Function.uncurry
        (Work.Construction.N α (Work.Construction.Ftot α w) Φ)) Work.FTS.EllipticEst.Q0 ∧
    ContinuousOn (Function.uncurry (Work.Coercivity.Transport w)) Work.FTS.EllipticEst.Q0 := by
  obtain ⟨hL12w, hFKw⟩ := prof_cont_moments hα hα1 hw
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Ftot α w) :=
    Work.FTS.NonlinRows.smoothOpen_add
      (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)) hw.reg
  refine ⟨?_, ?_, ?_⟩
  · exact (Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hα hw.reg
      (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw)).continuousOn
  · exact continuousOn_N_gen hF hL12w hFKw hΦ
  · exact continuousOn_uncurry_transport hw.reg

end

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.epsWP_hkMem5_bnd_fam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

theorem epsWP_hkMem5_bnd_fam {α C₀ Ce Cs Cs6 T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {G : ℕ → Work.FTS.Galerkin.Fam}
    {ε : ℕ → ℝ}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ Ce) :
    ∃ KW : ℝ, 0 < KW ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) ∧
        Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) ≤ KW := by
  -- ### the three block estimates at level `5`
  obtain ⟨Kl, hKl, hLGT⟩ :=
    Work.FTS.StrongEps.H5.HkMemXnLGammaT5 (α := α) hα (C₀ := C₀) (B := Ce)
  obtain ⟨K0, hK0, hN0⟩ :=
    Work.FTS.StrongEps.H5.HkMemXnN05 (α := α) hα (C₀ := C₀) (B := Ce)
  obtain ⟨KN, hKN, hNb⟩ :=
    Work.FTS.StrongEps.H5.HkMemXnN5 (α := α) hα (C₀ := C₀) (B := Ce) (Ce := Ce) (Cs6 := Cs6)
      (Φs := Φs)
  -- ### the assembly
  obtain ⟨KW, hKW, hkey⟩ :=
    Work.FTS.StrongEps.H5.epsWP_hkMem5_bnd_unif_of_blocks (α := α) (C₀ := C₀) (Ce := Ce)
      (Cs6 := Cs6) (T := T) (ρ := ρ) (Φs := Φs) (E := E) hα hρ hEll hstar6 hml hKl hK0 hKN
      hLGT hN0 hNb
  -- ### the family form
  exact ⟨KW, hKW, fun n s hs => hkey (G n) (ε n) (fun s hs => hC n s hs)
    (fun s hs => hb4 n s hs) (fun s hs => hb6 n s hs) s hs⟩

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsHbdd =====
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

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000


/-- **The compact form of `hbdd`.**  The same assembly as `hbdd_of_mem_all`, but for a compact
`K ⊆ Q0` (which is the shape `EpsProfileLip` consumes), using `exists_shift_window_compact` on `K`
itself. -/
theorem hbdd_of_mem_compact {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {G : ℕ → Fam} {ε : ℕ → ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    (hT : 0 ≤ T) (hc1 : 1 / 10 ≤ Work.Spaces.c α) (hc2 : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (ε n) (G n)) s) ≤ Ce)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K,
      |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C := by
  obtain ⟨K', hK'c, hK'Q, hKK', hshift1⟩ :=
    Work.FTS.StrongEps.exists_shift_window_compact one_pos le_rfl hK hKQ
  obtain ⟨B, hB0, hwp⟩ :=
    Work.FTS.StrongEps.epsWP_sup_le_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T)
      (ρ := ρ) (Φs := Φs) (E := E) (G := G) (ε := ε) hα hρ hε hT hc1 hc2 hEll hstar hml
      hC hb4 hb6 hK'c hK'Q
  obtain ⟨KW, hKW0, hKWb⟩ :=
    Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T)
      (ρ := ρ) (Φs := Φs) (E := E) (G := G) (ε := ε) hα hEll hstar hml hC hb4 hb6
  have hsm : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ (ε n) Φs E (G n) s) :=
    fun n => Work.FTS.StrongEps.smoothOpen_epsWP (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (T := T) (ρ := ρ) (Φs := Φs) (E := E) (g := G n) (ε := ε n) hα hEll hstar (hC n)
  obtain ⟨Cc, hCc0, hcorr⟩ :=
    Work.FTS.StrongEps.epsWP_corr_le_fam (α := α) (T := T) (KW := KW) (ρ := ρ) (Φs := Φs)
      (E := E) (G := G) (ε := ε) hρ hα hε hsm hKWb
  obtain ⟨B', hB'0, hbd⟩ := Work.FTS.StrongEps.epsRHSP_sup_le_fam (α := α) (C₀ := C₀) (Ce := Ce)
    (Cs := Cs) (T := T) (B := B) (Cc := Cc) hρ hε hK hKQ hKK'
    (fun n p hp q hq1 hq2 => hshift1 p hp q (le_trans hq1 (hε n).2) (le_trans hq2 (hε n).2))
    hB0.le hwp hCc0 hcorr
  exact ⟨B', hB'0.le, fun n s hs p hp => hbd n s hs p hp⟩


end Work.FTS.StrongEps
end
end
