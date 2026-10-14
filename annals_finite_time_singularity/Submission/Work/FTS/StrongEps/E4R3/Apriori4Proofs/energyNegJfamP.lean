import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.slot_transfer_deriv
import Submission.Work.FTS.StrongEps.E4R3.n4Pair_classC
import Submission.Work.FTS.StrongEps.E5G.epsRHSP_hkMem5_bnd_fam
import Submission.Work.FTS.StrongEps.EpsE4Thr.HnegCore
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.WpUniformBound
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs


theorem energyNegJfamP {ρ : ℝ × ℝ → ℝ} (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α₂ cc clo Cup Ccs CcN : ℝ}
    (hU : Work.FTS.StrongEps.EpsE4Thr.UnifIPO
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ cc clo Cup Ccs)
    {Ce Cs : ℝ}
    (hN4 : ∀ α ∈ Set.Ioc 0 α₂, ∀ {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α g → Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.FTS.Nonlin.Xn α g ≤ α ^ (7 / 4 : ℝ) →
      |Work.FTS.Apriori.rhsPair (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
        α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g))
    {α C₀ M : ℝ} (hα : α ∈ Set.Ioc 0 α₂) (hα1 : α ≤ 1) (hC₀ : 0 < C₀) (hM : 0 ≤ M)
    (hsmall : C₀ * α ^ (1 / 4 : ℝ) ≤ 1)
    (hclose : CcN * Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2)
      < Work.FTS.Apriori.kappa cc clo Cup * C₀ ^ 2 * α ^ 4) :
    ∃ ε₅ : ℝ, 0 < ε₅ ∧ ε₅ ≤ 1 ∧
      ∀ {T τ ε : ℝ} {Φs : Work.FTS.Galerkin.Fn}
        {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
        {g : Work.FTS.Galerkin.Fam},
        0 < T → τ ∈ Set.Ioo 0 T → ε ∈ Set.Ioc 0 ε₅ →
        Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g →
        Work.FTS.StrongEps.EpsRegP α ρ ε T g →
        (∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
          Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
        Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.StrongEps.MuLamOK α C₀ Φs E →
        (∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g s) ≤ M) →
        (∀ t ∈ Set.Icc 0 τ, Work.FTS.Nonlin.Xn α
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) t) ≤ C₀ * α ^ 2) →
        Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) = clo * (C₀ * α ^ 2) ^ 2 →
        2 * Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
              (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ)))
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) < 0 := by
  -- ### the two building blocks (proved in the `TransferDeriv` chapter)
  obtain ⟨Kc, hKc0, hKc⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.jfamP_defect_bound
      c₁ c₂ c₁' c₂' c₁'' c₂'' hρ hU hN4 hα hα1 hC₀ hM hsmall
  -- ### the margin of the barrier inequality
  have hδpos : 0 < cc * ((clo * (C₀ * α ^ 2) ^ 2) / Cup)
      - CcN * Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2) := by
    have hk : cc * ((clo * (C₀ * α ^ 2) ^ 2) / Cup)
        = Work.FTS.Apriori.kappa cc clo Cup * C₀ ^ 2 * α ^ 4 := by
      unfold Work.FTS.Apriori.kappa
      ring_nf
    linarith [hclose]
  refine ⟨min 1 ((cc * ((clo * (C₀ * α ^ 2) ^ 2) / Cup)
      - CcN * Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2)) / (2 * (Kc + 1))),
    lt_min one_pos (div_pos hδpos (by linarith)), min_le_left _ _, ?_⟩
  intro T τ ε Φs E g₀ g hT hτ hε hsol hreg hEll hstar hml hM6 hball hY
  have hε1 : ε ≤ 1 := le_trans hε.2 (min_le_left _ _)
  have hεδ : ε ≤ (cc * ((clo * (C₀ * α ^ 2) ^ 2) / Cup)
      - CcN * Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2)) / (2 * (Kc + 1)) :=
    le_trans hε.2 (min_le_right _ _)
  -- ### the defect bound and the core inequality at this instance
  have hdef := hKc hT hτ ⟨hε.1, hε1⟩ hsol hreg hEll hstar hml hM6 hball
  have hc : Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε g) τ
          + Work.FTS.Galerkin.dynRHS α
              (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
              (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
      ≤ -(cc * ((clo * (C₀ * α ^ 2) ^ 2) / Cup)
          - CcN * Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2)) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.jfamP_core_le
      c₁ c₂ c₁' c₂' c₁'' c₂'' hρ hU hN4 hα hα1 hC₀ hM hsmall
      (T := T) (τ := τ) (ε₀ := ε) (Φs := Φs) (E := E) (g₀ := g₀) (g := g)
      hτ hreg hM6 hEll hstar hml hball hY
  -- ### the arithmetic: the margin beats the defect
  have hmarg : Kc * ε < cc * ((clo * (C₀ * α ^ 2) ^ 2) / Cup)
      - CcN * Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2) := by
    have h1 : Kc * ε ≤ (Kc + 1) * ε := by nlinarith [hKc0, hε.1.le]
    have h2 : (Kc + 1) * ε ≤ (Kc + 1)
        * ((cc * ((clo * (C₀ * α ^ 2) ^ 2) / Cup)
          - CcN * Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2)) / (2 * (Kc + 1))) :=
      mul_le_mul_of_nonneg_left hεδ (by linarith)
    have h3 : (Kc + 1) * ((cc * ((clo * (C₀ * α ^ 2) ^ 2) / Cup)
          - CcN * Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2)) / (2 * (Kc + 1)))
        = (cc * ((clo * (C₀ * α ^ 2) ^ 2) / Cup)
          - CcN * Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2)) / 2 := by
      field_simp
    linarith
  have hle : Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
          (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ)))
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
      ≤ Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
          (Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε g) τ
            + Work.FTS.Galerkin.dynRHS α
                (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
                (Work.FTS.StrongEps.JfamP ρ ε g) τ)
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) + Kc * ε := by
    have h := (abs_le.mp hdef).2
    linarith
  have hneg : Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
          (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ)))
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) < 0 := by
    linarith
  linarith

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
