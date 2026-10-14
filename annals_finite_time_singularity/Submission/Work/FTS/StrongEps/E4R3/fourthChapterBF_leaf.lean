import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.energyNegJfamP
import Submission.Work.FTS.StrongEps.E4R3.Flow5Leaves.IP4_JfamP_hasDerivWithinAt_of_flow
import Submission.Work.FTS.StrongEps.E4R3.n4Pair_classC
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenBarrierHlim
import Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.CoerTransferO
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_EllLimOK.PkgJets.L12jets_classC
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgMid
import Submission.Work.FTS_RegExport.THL.L.DzDthG_tau_mod
import Submission.Work.FTS_StreamBdry.Inputs.residual_slot_jetsB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsE4Thr
open Work.FTS.StrongEps.E4R3.Flow5Leaves

set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedVariables false

local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-- `StarPkgo2` is monotone in the constant `Cs` (for `Cs ≥ 0`). -/
theorem StarPkgo2_mono {α Cs Cs' : ℝ} {Φs : Fn} (hα : 0 ≤ α)
    (h : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hle : Cs ≤ Cs') :
    Work.FTS.VocabO2.StarPkgo2 α Cs' Φs := by
  have hCα : Cs * α ≤ Cs' * α := mul_le_mul_of_nonneg_right hle hα
  have hpar : Work.FTS.VocabO.StarPkgo α Cs' Φs :=
    ⟨h.toStarPkgo.sol, h.toStarPkgo.smooth, ⟨h.toStarPkgo.R.1, le_trans h.toStarPkgo.R.2 hCα⟩,
      ⟨h.toStarPkgo.dU.1, le_trans h.toStarPkgo.dU.2 hCα⟩,
      ⟨h.toStarPkgo.V.1, le_trans h.toStarPkgo.V.2 hCα⟩, h.toStarPkgo.vanishU,
      ⟨h.toStarPkgo.Vth.1, le_trans h.toStarPkgo.Vth.2 hCα⟩⟩
  exact ⟨hpar, ⟨h.RW.1, le_trans h.RW.2 hCα⟩, ⟨h.VW.1, le_trans h.VW.2 hCα⟩,
    ⟨h.VzW.1, le_trans h.VzW.2 hCα⟩, ⟨h.UsW.1, le_trans h.UsW.2 hCα⟩,
    ⟨h.UszW.1, le_trans h.UszW.2 hCα⟩⟩

/-- The closing inequality of the barrier at a general level `C₀ ≥ C0 CcN cc clo Cup Ccs`. -/
theorem closing_at {CcN cc clo Cup Ccs C₀ α : ℝ} (hCcN : 0 < CcN) (hcc : 0 < cc)
    (hclo : 0 < clo) (hCup : 0 < Cup) (hCcs : 0 < Ccs) (hC₀ : 0 < C₀)
    (hC₀ge : Work.FTS.Apriori.C0 CcN cc clo Cup Ccs ≤ C₀) (hα : 0 < α)
    (hαCl : α ≤ Work.FTS.Apriori.alphaCl C₀) :
    CcN * Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2)
      < Work.FTS.Apriori.kappa cc clo Cup * C₀ ^ 2 * α ^ 4 := by
  have hkey : (C₀ + C₀ ^ 2) * Real.sqrt α + C₀ ^ 3 * α ^ (3 / 2 : ℝ) < 1 :=
    Work.FTS.Apriori.alphaCl_key hC₀ hα hαCl
  have hbracket : C₀ + (C₀ ^ 2 + C₀ ^ 3) * Real.sqrt α + C₀ ^ 4 * α ^ (3 / 2 : ℝ) < 2 * C₀ := by
    nlinarith [hkey, hC₀, Real.sqrt_nonneg α, Real.rpow_nonneg hα.le (3 / 2 : ℝ)]
  have h2CcN : 2 * CcN ≤ Work.FTS.Apriori.kappa cc clo Cup * C₀ := by
    have h := Work.FTS.Apriori.C0_ge (CcN := CcN) (Ccs := Ccs) hcc hclo hCup
    have hk : 0 ≤ Work.FTS.Apriori.kappa cc clo Cup :=
      (Work.FTS.Apriori.kappa_pos hcc hclo hCup).le
    nlinarith [h, hC₀ge, hk]
  have h4 : 0 < α ^ 4 := by positivity
  rw [Work.FTS.Apriori.Pbd_at hα]
  calc CcN * (α ^ 4 * (C₀ + (C₀ ^ 2 + C₀ ^ 3) * Real.sqrt α + C₀ ^ 4 * α ^ (3 / 2 : ℝ)))
      = (CcN * (C₀ + (C₀ ^ 2 + C₀ ^ 3) * Real.sqrt α + C₀ ^ 4 * α ^ (3 / 2 : ℝ))) * α ^ 4 := by
        ring
    _ < (CcN * (2 * C₀)) * α ^ 4 := by
        have := mul_lt_mul_of_pos_left hbracket hCcN
        nlinarith [this, h4]
    _ = (2 * CcN * C₀) * α ^ 4 := by ring
    _ ≤ (Work.FTS.Apriori.kappa cc clo Cup * C₀ * C₀) * α ^ 4 := by
        have : 2 * CcN * C₀ ≤ Work.FTS.Apriori.kappa cc clo Cup * C₀ * C₀ := by
          nlinarith [h2CcN, hC₀]
        exact mul_le_mul_of_nonneg_right this h4.le
    _ = Work.FTS.Apriori.kappa cc clo Cup * C₀ ^ 2 * α ^ 4 := by ring

/-- `C₀ α^{1/4} ≤ 1` from `α ≤ C₀^{-4}`. -/
theorem small_at {C₀ α : ℝ} (hC₀ : 0 < C₀) (hα : 0 < α) (h : α ≤ C₀ ^ (-(4 : ℝ))) :
    C₀ * α ^ (1 / 4 : ℝ) ≤ 1 := by
  have h1 : α ^ (1 / 4 : ℝ) ≤ C₀ ^ (-(1 : ℝ)) := by
    have h2 := Real.rpow_le_rpow hα.le h (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [← Real.rpow_mul hC₀.le, show -(4 : ℝ) * (1 / 4) = -(1 : ℝ) by norm_num] at h2
  calc C₀ * α ^ (1 / 4 : ℝ) ≤ C₀ * C₀ ^ (-(1 : ℝ)) := mul_le_mul_of_nonneg_left h1 hC₀.le
    _ = 1 := by
        rw [Real.rpow_neg hC₀.le, Real.rpow_one, mul_inv_cancel₀ (ne_of_gt hC₀)]

/-- The level-four a-priori chapter over the flow class, given the `ClassC` N4 pairing bound. -/
theorem fourthChapterBF_leaf_of_n4 {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hρ : IsSmoothKernel ρ)
    (hN4 : ∃ (c₁ c₂ c₁' c₂' c₁'' c₂'' α₂ cc clo Cup Ccs CcN : ℝ),
      0 < c₁ ∧ 0 < c₂ ∧ 0 < c₁' ∧ 0 < c₂' ∧ 0 < c₁'' ∧ 0 < c₂'' ∧
      0 < α₂ ∧ 0 < cc ∧ 0 < clo ∧ 0 < Cup ∧ 0 < Ccs ∧ 0 < CcN ∧
      Work.FTS.StrongEps.EpsE4Thr.UnifIPO (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ cc clo Cup Ccs ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ {g Φs Φg : Fn},
        Work.FTS.ClassC.ClassC α g → CoerAdmO α g →
        Work.FTS.VocabO2.StarPkgo2 α (max Cs 1) Φs →
        Work.FTS.VocabO.EllPkgGo α (max Ce 1) g Φg →
        Work.FTS.Nonlin.Xn α g ≤ α ^ (7 / 4 : ℝ) →
        |Work.FTS.Apriori.rhsPair (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α g
            (fun z θ => Φs z θ + Φg z θ)|
          ≤ CcN * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g)) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ →
      Work.FTS.StrongEps.EpsE4Thr.E4R5.FourthChapterBF Ce Cs C₀ ρ := by
  classical
  obtain ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', α₂, cc, clo, Cup, Ccs, CcN,
    hc₁, hc₂, hc₁', hc₂', hc₁'', hc₂'', hα₂, hcc, hclo, hCup, hCcs, hCcN, hU, hN4b⟩ := hN4
  set Cstar : ℝ := max (Work.FTS.Apriori.C0 CcN cc clo Cup Ccs) (2 * Real.sqrt (Cup / clo)) + 1
    with hCstardef
  have hC0 := Work.FTS.Apriori.C0_pos hCcN hcc hclo hCup hCcs
  have hCsqr : 2 * Real.sqrt (Cup / clo) ≤ Cstar := by
    rw [hCstardef]
    linarith [le_max_right (Work.FTS.Apriori.C0 CcN cc clo Cup Ccs) (2 * Real.sqrt (Cup / clo))]
  have hC0le : Work.FTS.Apriori.C0 CcN cc clo Cup Ccs ≤ Cstar := by
    rw [hCstardef]
    linarith [le_max_left (Work.FTS.Apriori.C0 CcN cc clo Cup Ccs) (2 * Real.sqrt (Cup / clo))]
  refine ⟨Cstar, fun C₀ hC₀ => ?_⟩
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (by linarith [hC0, Real.sqrt_nonneg (Cup / clo)]) hC₀
  have hC₀ge : Work.FTS.Apriori.C0 CcN cc clo Cup Ccs ≤ C₀ := le_trans hC0le hC₀
  have hratio : 1 < Real.sqrt (clo / Cup) * C₀ := by
    have hcloCup : 0 < clo / Cup := div_pos hclo hCup
    have hsq : Real.sqrt (clo / Cup) * Real.sqrt (Cup / clo) = 1 := by
      rw [← Real.sqrt_mul (le_of_lt hcloCup), Real.sqrt_eq_one]
      field_simp
    have h2 : Real.sqrt (Cup / clo) < C₀ := by
      have := hCsqr
      linarith [Real.sqrt_nonneg (Cup / clo)]
    calc (1 : ℝ) = Real.sqrt (clo / Cup) * Real.sqrt (Cup / clo) := hsq.symm
      _ < Real.sqrt (clo / Cup) * C₀ :=
          mul_lt_mul_of_pos_left h2 (Real.sqrt_pos_of_pos hcloCup)
  -- the chapter threshold
  refine ⟨min (min (1 / 4) α₂) (min (Work.FTS.Apriori.alphaCl C₀) (C₀ ^ (-(4 : ℝ)))), ?_, ?_, ?_⟩
  · exact lt_min (lt_min (by norm_num) hα₂)
      (lt_min (Work.FTS.Apriori.alphaCl_pos hC₀pos) (Real.rpow_pos_of_pos hC₀pos _))
  · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (by norm_num))
  · intro α hα
    have hα0 : 0 < α := hα.1
    have hα1 : α ≤ 1 := by
      have := hα.2
      linarith [min_le_left (min (1 / 4) α₂) (min (Work.FTS.Apriori.alphaCl C₀) (C₀ ^ (-(4 : ℝ)))),
        min_le_left (1 / 4 : ℝ) α₂]
    have hαα₂ : α ≤ α₂ := by
      have := hα.2
      linarith [min_le_left (min (1 / 4) α₂) (min (Work.FTS.Apriori.alphaCl C₀) (C₀ ^ (-(4 : ℝ)))),
        min_le_right (1 / 4 : ℝ) α₂]
    have hαCl : α ≤ Work.FTS.Apriori.alphaCl C₀ := by
      have := hα.2
      linarith [min_le_right (min (1 / 4) α₂) (min (Work.FTS.Apriori.alphaCl C₀) (C₀ ^ (-(4 : ℝ)))),
        min_le_left (Work.FTS.Apriori.alphaCl C₀) (C₀ ^ (-(4 : ℝ)))]
    have hαpow : α ≤ C₀ ^ (-(4 : ℝ)) := by
      have := hα.2
      linarith [min_le_right (min (1 / 4) α₂) (min (Work.FTS.Apriori.alphaCl C₀) (C₀ ^ (-(4 : ℝ)))),
        min_le_right (Work.FTS.Apriori.alphaCl C₀) (C₀ ^ (-(4 : ℝ)))]
    have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα0, hαα₂⟩
    have hsmall : C₀ * α ^ (1 / 4 : ℝ) ≤ 1 := small_at hC₀pos hα0 hαpow
    have hclose := closing_at hCcN hcc hclo hCup hCcs hC₀pos hC₀ge hα0 hαCl
    intro K Φs E g₀ hDat T M hT
    have hCsle : Cs ≤ max Cs 1 := le_max_left Cs 1
    have hCele : Ce ≤ max Ce 1 := le_max_left Ce 1
    have hstar' : Work.FTS.VocabO2.StarPkgo2 α (max Cs 1) Φs :=
      StarPkgo2_mono hα0.le hDat.2.2.2.1 hCsle
    have hEll' : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α (max Ce 1) u (E u) ∧
          Work.FTS.ClassC.EllPkgK α 6 (max Ce 1) u (E u) := by
      intro u hu
      exact ⟨Work.FTS.ClassC.EllPkgGo_mono hα0 (hDat.2.2.1 u hu).1 hCele,
        Work.FTS.ClassC.EllPkgK_mono (hDat.2.2.1 u hu).2 hCele⟩
    by_cases hM : 0 ≤ M
    · obtain ⟨ε₅, hε₅pos, hε₅1, hNeg⟩ :=
        Work.FTS.StrongEps.E4R3.Apriori4Proofs.energyNegJfamP (α := α) (ρ := ρ)
          (C₀ := C₀) (M := M) (Ce := max Ce 1) (Cs := max Cs 1)
          c₁ c₂ c₁' c₂' c₁'' c₂'' hρ hU hN4b
          hαIoc hα1 hC₀pos hM hsmall hclose
      obtain ⟨ε₁, hε₁pos, hε₁⟩ :=
        Work.FTS.StrongEps.EpsE4Thr.Pz_Jeps_lt_ratio (α := α) (C₀ := C₀) (ρ := ρ)
          (g₀ := g₀) hρ hα0 hα1 hclo hCup hC₀pos hratio hDat.2.2.2.2.2.1 hDat.2.2.2.2.2.2.1
      refine ⟨min ε₅ ε₁, lt_min hε₅pos hε₁pos, le_trans (min_le_left _ _) hε₅1,
        fun ε hε => ?_⟩
      have hε₅ : ε ∈ Set.Ioc 0 ε₅ := ⟨hε.1, le_trans hε.2 (min_le_left _ _)⟩
      have hε₁' : ε ∈ Set.Ioc 0 ε₁ := ⟨hε.1, le_trans hε.2 (min_le_right _ _)⟩
      have hε1 : ε ≤ 1 := le_trans hε₅.2 hε₅1
      intro _hball T' hT' _hT'le g _hsol hreg hflow h6M
      set Y : ℝ := clo * (C₀ * α ^ 2) ^ 2 with hYdef
      have hY0 : 0 < Y := by rw [hYdef]; positivity
      have hcoer : ∀ τ ∈ Set.Icc 0 T', CoerAdmO α (slice (JfamP ρ ε g) τ) :=
        fun τ hτ => coerAdmO_slice_JfamP hreg τ hτ
      -- LEAF-C: the derivative of the level-four energy along the flow
      have hderivAll : ∀ τ ∈ Set.Icc 0 T',
          HasDerivWithinAt
            (fun s => IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
              (slice (JfamP ρ ε g) s) (slice (JfamP ρ ε g) s))
            (2 * IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
              (Pz (Jeps ρ ε (epsRHSP α ρ ε Φs E g τ))) (slice (JfamP ρ ε g) τ))
            (Set.Icc 0 T') τ := by
        intro τ hτ
        exact IP4_JfamP_hasDerivWithinAt_of_flow (α := α) (ε := ε) (T := T') (ρ := ρ)
          (Φs := Φs) (E := E) (g := g) c₁ c₂ c₁' c₂' c₁'' c₂''
          hc₁.le hc₂.le hc₁'.le hc₂'.le hc₁''.le hc₂''.le hρ ⟨hα0, hα1⟩ hε.1 hε1 hreg hflow hτ
      -- the ball at a point from the level bound
      have ball_at : ∀ τ ∈ Set.Icc 0 T',
          IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (slice (JfamP ρ ε g) τ) (slice (JfamP ρ ε g) τ) ≤ Y →
          Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 := by
        intro τ hτ hEτ
        have hlo := hU.lo α hαIoc (slice (JfamP ρ ε g) τ) (hcoer τ hτ)
        have hSq : Work.Spaces.HkSq α 4 (slice (JfamP ρ ε g) τ) ≤ (C₀ * α ^ 2) ^ 2 := by
          have h2 : Work.Spaces.HkSq α 4 (slice (JfamP ρ ε g) τ) ≤ Y / clo := by
            rw [le_div_iff₀ hclo, mul_comm]
            exact le_trans hlo hEτ
          have h3 : Y / clo ≤ (C₀ * α ^ 2) ^ 2 := by
            rw [hYdef, div_le_iff₀ hclo]
            ring_nf
            rw [mul_comm]
          linarith
        have hZnn : 0 ≤ C₀ * α ^ 2 := by positivity
        have hnorm : Real.sqrt (Work.Spaces.HkSq α 4 (slice (JfamP ρ ε g) τ)) ≤ C₀ * α ^ 2 := by
          have h1 := Real.sqrt_le_sqrt hSq
          rwa [Real.sqrt_sq hZnn] at h1
        simpa [Work.Spaces.HkNorm, Work.FTS.Nonlin.Xn] using hnorm
      -- the strict start condition
      have h0 : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
          (slice (JfamP ρ ε g) 0) (slice (JfamP ρ ε g) 0) < Y := by
        have hg0 : slice g 0 = g₀ := by
          funext z θ
          exact _hsol.1 z θ
        have hx0 : slice (JfamP ρ ε g) 0 = Pz (Jeps ρ ε g₀) := by
          have h1 : slice (JfamP ρ ε g) 0 = Pz (Jeps ρ ε (slice g 0)) := rfl
          rw [h1, hg0]
        have hx := hε₁ ε hε₁'
        have hx' : Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) 0)
            < Real.sqrt (clo / Cup) * (C₀ * α ^ 2) := by
          rw [hx0]
          exact hx
        simpa only [hYdef] using
          h0_of_datum_ratio_open (IP := IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') (x := slice (JfamP ρ ε g) 0)
            hU hαIoc (hcoer 0 ⟨le_rfl, hT'.le⟩) hx'
      -- the level bound on the half-open interval
      have hlevel : ∀ τ ∈ Set.Ico 0 T',
          IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (slice (JfamP ρ ε g) τ) (slice (JfamP ρ ε g) τ) ≤ Y := by
        refine barrier_within_level_left (E := fun s => IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (slice (JfamP ρ ε g) s) (slice (JfamP ρ ε g) s))
          (E' := fun s => 2 * IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (Pz (Jeps ρ ε (epsRHSP α ρ ε Φs E g s))) (slice (JfamP ρ ε g) s))
          hT' ?_ h0 ?_
        · intro τ hτ
          exact ((hderivAll τ ⟨hτ.1, hτ.2.le⟩).continuousWithinAt).mono Set.Ico_subset_Icc_self
        · intro τ hτ hlev hτY
          have hb : ∀ t ∈ Set.Icc 0 τ,
              Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) t) ≤ C₀ * α ^ 2 := by
            intro t ht
            refine ball_at t ⟨ht.1, ht.2.trans hτ.2.le⟩ ?_
            rcases lt_or_eq_of_le ht.2 with h | h
            · exact hlev t ⟨ht.1, h⟩
            · rw [h]; exact le_of_eq hτY
          have hdn : (2 : ℝ) * IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
              (Pz (Jeps ρ ε (epsRHSP α ρ ε Φs E g τ))) (slice (JfamP ρ ε g) τ) < 0 :=
            hNeg hT' hτ hε₅ _hsol hreg hEll' hstar' hDat.2.2.2.2.1 h6M hb hτY
          exact ⟨(hderivAll τ ⟨hτ.1.le, hτ.2.le⟩).mono (Set.Icc_subset_Icc_right hτ.2.le), hdn⟩
      -- the endpoint from the one-sided continuity
      have hend : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
          (slice (JfamP ρ ε g) T') (slice (JfamP ρ ε g) T') ≤ Y := by
        have hcontT : ContinuousWithinAt
            (fun s => IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
              (slice (JfamP ρ ε g) s) (slice (JfamP ρ ε g) s)) (Set.Icc 0 T') T' :=
          (hderivAll T' ⟨hT'.le, le_rfl⟩).continuousWithinAt
        refine le_of_forall_pos_le_add fun ε₀ hε₀ => ?_
        obtain ⟨δ, hδ0, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds).mp hcontT ε₀ hε₀
        set m : ℝ := min (δ / 2) (T' / 2) with hmdef
        have hm0 : 0 < m := by
          rw [hmdef]
          exact lt_min (by linarith) (by linarith)
        have hmδ : m ≤ δ / 2 := by rw [hmdef]; exact min_le_left _ _
        have hmT : m ≤ T' / 2 := by rw [hmdef]; exact min_le_right _ _
        have hmem : T' - m ∈ Set.Icc 0 T' := ⟨by linarith, by linarith⟩
        have hdist : dist (T' - m) T' < δ := by
          rw [Real.dist_eq, show T' - m - T' = -m by ring, abs_neg, abs_of_pos hm0]
          linarith
        have hb := hδ hmem hdist
        have hb' : |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
              (slice (JfamP ρ ε g) (T' - m)) (slice (JfamP ρ ε g) (T' - m))
            - IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (slice (JfamP ρ ε g) T') (slice (JfamP ρ ε g) T')|
            < ε₀ := by
          simpa only [Real.dist_eq] using hb
        have hl : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (slice (JfamP ρ ε g) (T' - m)) (slice (JfamP ρ ε g) (T' - m)) ≤ Y :=
          hlevel _ ⟨hmem.1, by linarith⟩
        linarith [(abs_lt.mp hb').1]
      intro τ hτ
      rcases lt_or_eq_of_le hτ.2 with h | h
      · exact ball_at τ hτ (hlevel τ ⟨hτ.1, h⟩)
      · rw [h] at hτ ⊢
        exact ball_at T' hτ hend
    · -- the vacuous case `M < 0`
      push_neg at hM
      refine ⟨1, one_pos, le_rfl, fun ε _hε => ?_⟩
      intro _hball T' hT' _hT'le g hsol _hreg _hflow h6M
      exfalso
      have h2 : Work.FTS.StrongGlobal.Xn6 α g₀ ≤ M := by
        have h1 : Work.FTS.StrongGlobal.Xn6 α (slice g 0) ≤ M := h6M 0 ⟨le_rfl, hT'.le⟩
        rwa [show slice g 0 = g₀ from funext (fun z => funext (fun θ => hsol.1 z θ))] at h1
      have h3 : (0 : ℝ) ≤ Work.FTS.StrongGlobal.Xn6 α g₀ := Work.Spaces.HkNorm_nonneg α 6 g₀
      linarith

/-- **The level-four chapter over the flow class** (the H4 leaf), from the `ClassC` N4 pairing
bound.  The chapter constant is chosen from the constants of the pairing bound, and the mollifier
constant `Ce`/`Cs` of the data are replaced by `max · 1` (the packages are monotone in them). -/
theorem fourthChapterBF_leaf {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ →
      Work.FTS.StrongEps.EpsE4Thr.E4R5.FourthChapterBF Ce Cs C₀ ρ := by
  obtain ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', α₂, cc, clo, Cup, Ccs, CcN,
    hc₁, hc₂, hc₁', hc₂', hc₁'', hc₂'', hα₂, hcc, hclo, hCup, hCcs, hCcN, hU, hN4b⟩ :=
    Work.FTS.StrongEps.E4R3.n4Pair_classC (Ce := max Ce 1) (Cs := max Cs 1)
      (lt_of_lt_of_le one_pos (le_max_right Ce 1)) (lt_of_lt_of_le one_pos (le_max_right Cs 1))
  exact fourthChapterBF_leaf_of_n4 (Ce := Ce) (Cs := Cs) hρ
    ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', α₂, cc, clo, Cup, Ccs, CcN,
      hc₁, hc₂, hc₁', hc₂', hc₁'', hc₂'', hα₂, hcc, hclo, hCup, hCcs, hCcN, hU, hN4b⟩

end Work.FTS.StrongEps.E4R3
