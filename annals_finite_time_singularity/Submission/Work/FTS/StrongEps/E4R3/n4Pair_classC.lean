import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.CoerTransferO
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.HnegCore
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.IPGen.Assembly
import Submission.Work.FTS.StrongEps.E4R3.N4C.ExtraH
import Submission.Work.FTS.StrongEps.E4R3.N4C.rowsN0T
import Submission.Work.FTS.StrongEps.E4R3.N4C.rowsNT
import Submission.Work.FTS.StrongEps.E4R3.N4C.rowsAuxT
import Submission.Work.FTS.StrongEps.E4R3.N4C.rowsHkT
import Submission.Work.FTS.StrongEps.E4R3.N4C.rowsSplitsT
import Submission.Work.FTS.StrongEps.E4R3.N4C.pairingBoundT
import Submission.Work.FTS.OpenPkg.N4NormExists

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3

set_option autoImplicit false

/-- **`UnifIPO` is monotone in the range `α₂`**: the clauses are quantified over
`α ∈ (0, α₂]`, so a witness on the larger range restricts to the smaller one. -/
theorem UnifIPO_mono {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {α₂ α₂' cc clo Cup Ccs : ℝ} (hα₂' : α₂' ≤ α₂) (hα₂'pos : 0 < α₂')
    (h : Work.FTS.StrongEps.EpsE4Thr.UnifIPO IP α₂ cc clo Cup Ccs) :
    Work.FTS.StrongEps.EpsE4Thr.UnifIPO IP α₂' cc clo Cup Ccs :=
  ⟨⟨hα₂'pos, h.pos.2.1, h.pos.2.2.1, h.pos.2.2.2.1, h.pos.2.2.2.2⟩,
   fun α f g => h.symm α f g,
   fun α hα f₁ f₂ g h₁ h₂ h₃ => h.add_fst α ⟨hα.1, le_trans hα.2 hα₂'⟩ f₁ f₂ g h₁ h₂ h₃,
   fun α hα c f g h₁ h₂ => h.smul_fst α ⟨hα.1, le_trans hα.2 hα₂'⟩ c f g h₁ h₂,
   fun α hα f f' g h₁ h₂ hh => h.congr_qd α ⟨hα.1, le_trans hα.2 hα₂'⟩ f f' g h₁ h₂ hh,
   fun α hα f hf => h.nonneg α ⟨hα.1, le_trans hα.2 hα₂'⟩ f hf,
   fun α hα f g h₁ h₂ => h.cs α ⟨hα.1, le_trans hα.2 hα₂'⟩ f g h₁ h₂,
   fun α hα f hf => h.lo α ⟨hα.1, le_trans hα.2 hα₂'⟩ f hf,
   fun α hα f hf => h.up α ⟨hα.1, le_trans hα.2 hα₂'⟩ f hf,
   fun α hα f hf => h.coer α ⟨hα.1, le_trans hα.2 hα₂'⟩ f hf,
   fun α hα f hf => h.Dz_self α ⟨hα.1, le_trans hα.2 hα₂'⟩ f hf⟩

theorem n4Pair_classC {Ce Cs : ℝ} (hCe : 0 < Ce) (hCs : 0 < Cs) :
    ∃ (c₁ c₂ c₁' c₂' c₁'' c₂'' α₂ cc clo Cup Ccs CcN : ℝ),
      0 < c₁ ∧ 0 < c₂ ∧ 0 < c₁' ∧ 0 < c₂' ∧ 0 < c₁'' ∧ 0 < c₂'' ∧
      0 < α₂ ∧ 0 < cc ∧ 0 < clo ∧ 0 < Cup ∧ 0 < Ccs ∧ 0 < CcN ∧
      Work.FTS.StrongEps.EpsE4Thr.UnifIPO
          (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ cc clo Cup Ccs ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ {g Φs Φg : Work.FTS.Galerkin.Fn},
        Work.FTS.ClassC.ClassC α g → Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g →
        Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
        Work.FTS.Nonlin.Xn α g ≤ α ^ (7 / 4 : ℝ) →
        |Work.FTS.Apriori.rhsPair
            (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
            α g (fun z θ => Φs z θ + Φg z θ)|
          ≤ CcN * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g) := by
  -- ## the coercivity witness for the concrete `IP4`
  obtain ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', h₁, h₂, h₁', h₂', h₁'', h₂'', α₂U, cc, clo, Cup, Ccs,
    hα₂U, hcc, hclo, hCup, hCcs, hU⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.TransO.unifIPO_IP4_of_transfer
  -- ## the honest clause bundle for those coefficients
  obtain ⟨Ct, α₂E, hCtpos, hα₂Epos, hE⟩ :=
    Work.FTS.StrongEps.E4R3.N4C.n4ExtraH_IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' h₁ h₂ h₁' h₂' h₁'' h₂''
  -- ## a common range
  set α₂ : ℝ := min α₂E (min α₂U 1) with hα₂def
  have hα₂pos : 0 < α₂ := by
    rw [hα₂def]; exact lt_min hα₂Epos (lt_min hα₂U one_pos)
  have hα₂one : α₂ ≤ 1 := by
    rw [hα₂def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hα₂E' : α₂ ≤ α₂E := by rw [hα₂def]; exact min_le_left _ _
  have hα₂U' : α₂ ≤ α₂U := by
    rw [hα₂def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hE' : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ Ct :=
    hE.mono hα₂E' hα₂pos
  -- ## the norm interface and the honest row table
  obtain ⟨Ci, _hCi, hN⟩ :=
    Work.FTS.OpenPkg.N4Norm'_exists_of_all_fields (α₂ := α₂) hα₂pos hα₂one
  obtain ⟨K₁, hK₁, hrowN0⟩ := Work.FTS.StrongEps.E4R3.N4C.rowsN0T
    (IP := Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') hN hE'
  obtain ⟨K₂, hK₂, hrowN⟩ := Work.FTS.StrongEps.E4R3.N4C.rowsNT
    (IP := Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
    (Ce := Ce) (Cs := Cs) hN hE'
  obtain ⟨K₃, hK₃, hrowAux⟩ := Work.FTS.StrongEps.E4R3.N4C.rowsAuxT
    (IP := Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
    (Ce := Ce) (Cs := Cs) hN hE'
  have hhk : ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.OpenPkg.PiecesHk α g Φs Φg :=
    Work.FTS.StrongEps.E4R3.N4C.rowsHkT
      (IP := Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
      (Ce := Ce) (Cs := Cs) hN hE'
  have hsp : ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.NonlinRows.SplitsData α g Φs Φg :=
    Work.FTS.StrongEps.E4R3.N4C.rowsSplitsT (Cs := Cs) (Ce := Ce) (α₂ := α₂)
  have hR : Work.FTS.StrongEps.E4R3.N4C.RowsT
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ Ce Cs :=
    ⟨K₁, K₂, K₃, hK₁, hK₂, hK₃, fun hc => hrowN0 hc, fun hc => hrowN hc,
      fun hc => hrowAux hc, fun hc => hhk hc, fun hc => hsp hc⟩
  -- ## the pairing estimate
  obtain ⟨CcN, α₄, hCcN, hα₄pos, _hα₄α₂, hbound⟩ :=
    Work.FTS.StrongEps.E4R3.N4C.pairingBoundT
      (IP := Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') hCs hCe hE' hR
  -- ## the final constants
  have hfinpos : 0 < min α₄ α₂ := lt_min hα₄pos hα₂pos
  refine ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', min α₄ α₂, cc, clo, Cup, Ccs, CcN, h₁, h₂, h₁', h₂',
    h₁'', h₂'', hfinpos, hcc, hclo, hCup, hCcs, hCcN, ?_, ?_⟩
  · exact UnifIPO_mono (le_trans (min_le_right _ _) hα₂U') hfinpos hU
  · intro α hα g Φs Φg hclassC hco hstar hell hX
    have hα₄ : α ≤ α₄ := le_trans hα.2 (min_le_left _ _)
    have hα₂' : α ≤ α₂ := le_trans hα.2 (min_le_right _ _)
    have hα1 : α ≤ 1 := le_trans hα₂' hα₂one
    exact hbound α ⟨hα.1, hα₄⟩ (g := g) (Φs := Φs) (Φg := Φg)
      ⟨hα.1, hα1, hα₂', hclassC, hco, hstar, hell⟩ hX

end Work.FTS.StrongEps.E4R3
