import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN
import Submission.Work.FTS.GalFields.RHS.sharp_N_diff
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS_RegExport.RXT.Slots.v2_hkMem_pointwise_min
import Submission.Work.FTS.StrongEps.EComparison.E_slots_diff_le
import Submission.Work.FTS.OpenPkg.N4NormExists
import Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.Base
import Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.IdentityC
import Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.WlInfTermsBoundC
import Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.HonestTermsBoundC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- `SmoothOpen` only depends on the values on the open quadrant. -/
theorem smoothOpen_of_eqOn_Qd_cc {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.FTS.EllipticEst.SmoothOpen g := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mpr (fun n => ?_)
  refine ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf n).congr (fun p hp => ?_)
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact (h p.1 p.2 hz hθ0 hθ1).symm

theorem NDiffClassC {α Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ) z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ) z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ) z θ)
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  obtain ⟨Ci, -, hN⟩ :=
    Work.FTS.OpenPkg.N4Norm'_exists_of_all_fields (α₂ := (1 : ℝ)) one_pos le_rfl
  have hEG : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) := fun u hu => (hEll u hu).1
  obtain ⟨KW, hKW, hWb⟩ := CCSharp.WlInfTermsBoundC (α := α) (α₂ := (1 : ℝ))
    (Ci := Ci) (Ce := Ce) (Cs := Cs) hN hstar hEG hα0 hα1
  obtain ⟨KH, hKH, hHb⟩ := CCSharp.HonestTermsBoundC (α := α) (α₂ := (1 : ℝ))
    (Ci := Ci) (Ce := Ce) (Cs := Cs) hN hstar hEG hα0 hα1
  set K₀ : ℝ := max KW KH + 1 with hK₀
  have hK₀pos : 0 < K₀ := by rw [hK₀]; linarith [hKW, le_max_left KW KH]
  have hKW₀ : KW ≤ K₀ := by rw [hK₀]; linarith [le_max_left KW KH]
  have hKH₀ : KH ≤ K₀ := by rw [hK₀]; linarith [le_max_right KW KH]
  refine ⟨2 ^ (20 : ℕ) * 20 * K₀ + 1, by positivity, ?_⟩
  intro W₁ W₂ hW₁ hW₂
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10⟩ := hWb hW₁ hW₂ hα1
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := hHb hW₁ hW₂ hα1
  have hBIG : (0 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂ :=
    add_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hSMALL : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
    Real.sqrt_nonneg _
  have upW : ∀ {A : ℝ}, A ≤ KW * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) →
      A ≤ K₀ * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := fun hle =>
    le_trans hle (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKW₀ hBIG) hSMALL)
  have upH : ∀ {A : ℝ}, A ≤ KH * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) →
      A ≤ K₀ * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := fun hle =>
    le_trans hle (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKH₀ hBIG) hSMALL)
  have bTRA := upW w1.2.2
  have bTRB := upH v1.2.2
  have bTRC := upW w4.2.2
  have bTRD := upH v6.2.2
  have bTUA := upW w2.2.2
  have bTUB := upH v2.2.2
  have bTUC := upW w5.2.2
  have bTUD := upH v7.2.2
  have bTVA := upW w3.2.2
  have bTVB := upH v3.2.2
  have bTVC := upW w6.2.2
  have bTVD := upH v8.2.2
  have bTDA := upW w7.2.2
  have bTDB := upH v4.2.2
  have bTDC := upW w8.2.2
  have bTDD := upH v9.2.2
  have bTEA := upW w9.2.2
  have bTEB := upH v5.2.2
  have bTEC := upW w10.2.2
  have bTED := upH v10.2.2
  have hSlist : ∀ f ∈ Work.FTS.GalFields.RHS.Sharp.termList α Φs E W₁ W₂
      (fun z θ => W₁ z θ - W₂ z θ), Work.FTS.EllipticEst.SmoothOpen f := by
    intro f hf
    simp only [Work.FTS.GalFields.RHS.Sharp.termList, List.mem_cons, List.not_mem_nil,
      or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact w1.1
    · exact v1.1
    · exact w4.1
    · exact v6.1
    · exact w2.1
    · exact v2.1
    · exact w5.1
    · exact v7.1
    · exact w3.1
    · exact v3.1
    · exact w6.1
    · exact v8.1
    · exact w7.1
    · exact v4.1
    · exact w8.1
    · exact v9.1
    · exact w9.1
    · exact v5.1
    · exact w10.1
    · exact v10.1
  have hMlist : ∀ f ∈ Work.FTS.GalFields.RHS.Sharp.termList α Φs E W₁ W₂
      (fun z θ => W₁ z θ - W₂ z θ), Work.Spaces.HkMem α 4 f := by
    intro f hf
    simp only [Work.FTS.GalFields.RHS.Sharp.termList, List.mem_cons, List.not_mem_nil,
      or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact w1.2.1
    · exact v1.2.1
    · exact w4.2.1
    · exact v6.2.1
    · exact w2.2.1
    · exact v2.2.1
    · exact w5.2.1
    · exact v7.2.1
    · exact w3.2.1
    · exact v3.2.1
    · exact w6.2.1
    · exact v8.2.1
    · exact w7.2.1
    · exact v4.2.1
    · exact w8.2.1
    · exact v9.2.1
    · exact w9.2.1
    · exact v5.2.1
    · exact w10.2.1
    · exact v10.2.1
  have hsumle : List.foldr (fun f acc => Work.FTS.Nonlin.Xn α f + acc) 0
      (Work.FTS.GalFields.RHS.Sharp.termList α Φs E W₁ W₂ (fun z θ => W₁ z θ - W₂ z θ))
      ≤ 20 * (K₀ * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) := by
    simp only [Work.FTS.GalFields.RHS.Sharp.termList, List.foldr_cons, List.foldr_nil]
    linarith [bTRA, bTRB, bTRC, bTRD, bTUA, bTUB, bTUC, bTUD, bTVA, bTVB,
      bTVC, bTVD, bTDA, bTDB, bTDC, bTDD, bTEA, bTEB, bTEC, bTED]
  have hfoldle := Work.FTS.GalFields.RHS.Sharp.HkNorm_listFoldr_le hα0
    (Work.FTS.GalFields.RHS.Sharp.termList α Φs E W₁ W₂ (fun z θ => W₁ z θ - W₂ z θ))
    hSlist hMlist
  rw [Work.FTS.GalFields.RHS.Sharp.termList_length] at hfoldle
  have hId := CCSharp.NDiffIdC hα0 hα1 hstar hEll hW₁ hW₂
    (CCSharp.sub_classC hW₁ hW₂) (fun z θ => rfl)
  have hagree : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ) z θ) z θ
      = (List.foldr (fun f acc => f + acc) (0 : Work.FTS.Galerkin.Fn)
        (Work.FTS.GalFields.RHS.Sharp.termList α Φs E W₁ W₂
          (fun z θ => W₁ z θ - W₂ z θ))) z θ := by
    intro z θ hz hθ0 hθ1
    exact hId z θ ⟨hz, hθ0, hθ1⟩
  have hXnD : Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ) z θ)
      ≤ 2 ^ (20 : ℕ) * (20 * (K₀ * (1 + Work.FTS.GalFields.Xn5 α W₁
          + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ))) := by
    have heq : Work.FTS.Nonlin.Xn α (fun z θ =>
            Work.Construction.N α (Work.Construction.Ftot α W₁)
                (fun z θ => Φs z θ + E W₁ z θ) z θ
              - Work.Construction.N α (Work.Construction.Ftot α W₂)
                (fun z θ => Φs z θ + E W₂ z θ) z θ)
        = Work.FTS.Nonlin.Xn α (List.foldr (fun f acc => f + acc)
            (0 : Work.FTS.Galerkin.Fn)
            (Work.FTS.GalFields.RHS.Sharp.termList α Φs E W₁ W₂
              (fun z θ => W₁ z θ - W₂ z θ))) :=
      Work.FTS.StrongEps.EComparison.HkNorm_congr_open α 4 hagree
    rw [heq]
    exact le_trans hfoldle (mul_le_mul_of_nonneg_left hsumle (by positivity))
  have hfinal : Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ) z θ)
      ≤ (2 ^ (20 : ℕ) * 20 * K₀ + 1)
          * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
    refine le_trans hXnD ?_
    have h2 : 2 ^ (20 : ℕ) * (20 * (K₀ * (1 + Work.FTS.GalFields.Xn5 α W₁
          + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α
            (fun z θ => W₁ z θ - W₂ z θ)))
        = (2 ^ (20 : ℕ) * 20 * K₀) * ((1 + Work.FTS.GalFields.Xn5 α W₁
            + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α
              (fun z θ => W₁ z θ - W₂ z θ)) := by ring
    rw [h2]
    have h3 : (0 : ℝ) ≤ 2 ^ (20 : ℕ) * 20 * K₀ := by positivity
    calc (2 ^ (20 : ℕ) * 20 * K₀) * ((1 + Work.FTS.GalFields.Xn5 α W₁
            + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ))
        ≤ (2 ^ (20 : ℕ) * 20 * K₀ + 1) * ((1 + Work.FTS.GalFields.Xn5 α W₁
            + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hBIG hSMALL)
      _ = (2 ^ (20 : ℕ) * 20 * K₀ + 1) * (1 + Work.FTS.GalFields.Xn5 α W₁
            + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by ring
  exact ⟨smoothOpen_of_eqOn_Qd_cc
      (Work.FTS.GalFields.RHS.Sharp.smoothOpen_listFoldr _ hSlist)
      (fun z θ hz hθ0 hθ1 => (hagree z θ hz hθ0 hθ1).symm),
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
      (Work.FTS.GalFields.RHS.Sharp.HkMem_listFoldr _
        (fun f hf => hSlist f hf) (fun f hf => hMlist f hf))
      (fun z hz θ hθ0 => (hagree z θ hz hθ0.1 hθ0.2).symm),
    hfinal⟩

end Work.FTS.StrongEps.EpsRLX
