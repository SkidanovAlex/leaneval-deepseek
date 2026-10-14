import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonTerms.Base
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongEps.LocUnif.D5.rounds
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem
import Submission.Work.FTS_EllLimOK.Pinning.tendsto_cos_mul_of_hkMem_cosDiv
import Submission.Work.FTS_EllLimOK.PkgJets.L12jets_classC
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgBasic
import Submission.Work.FTS_EllLimOK.SlotSup.slot_jets_sup_le
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXA1.abs_mixed_le_HkNorm_C4_proved
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXR1.pzIter_bound_weighted
import Submission.Work.FTS_RegExport.RXR1.slice_deriv_equi
import Submission.Work.FTS_RegExport.RXR5.R5PiecesF
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.FTS_StreamBdry.SB4.lim_mixed_plainE
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.fstarDzIterFourAe
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.DensNPointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem DensNPointwise :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε τ C₀ B : ℝ} {g : Fam} {Maj : ℝ → ℝ},
      Work.FTS.StrongEps.EpsDecay α ρ Φs E ε τ g Maj →
      Work.FTS.ClassC.ClassC α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
      Work.FTS.StrongGlobal.Xn6 α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ B →
      ∀ s ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.K θ * |Work.Construction.N α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ) s θ|
          ≤ C * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) * Real.cos θ := by
  obtain ⟨CFs, hCFspos, hCFs⟩ := FstarSlotBounds
  have hCFs0 : 0 ≤ CFs := hCFspos.le
  refine ⟨200 * (CFs + 1) ^ 2 + 400, ?_, ?_⟩
  · nlinarith only [hCFspos]
  intro α hαIoc ρ Φs E ε τ C₀ B g Maj hDec hClass hXn hXn6 s hs θ hθ
  have hα0 : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hs0 : (0 : ℝ) < s := hs
  obtain ⟨hMaj0, hMaj1, -, hSlot1, hBlk⟩ := hDec
  have hC₀0 : 0 ≤ C₀ := by
    have hX : 0 ≤ Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    nlinarith only [hX, hXn, pow_pos hα0 2]
  have hB0 : 0 ≤ B := by
    have hX : 0 ≤ Work.FTS.StrongGlobal.Xn6 α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 6 _
    linarith
  have hA1 : 1 ≤ (1 + C₀) * (1 + B) := by nlinarith
  have h1C : 0 ≤ 1 + C₀ := by linarith
  have h1B : 0 ≤ 1 + B := by linarith
  obtain ⟨hKnn, hKcos, hcos0, -, -, -, -, -⟩ := AngFacts
  -- ## the names
  set W : ℝ → ℝ → ℝ := slice (Work.FTS.StrongEps.JfamP ρ ε g) τ with hWdef
  set Φg : ℝ → ℝ → ℝ :=
    slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ with hΦgdef
  set F : ℝ → ℝ → ℝ := Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ with hFdef
  have hFdec : F = fun z θ => Work.Construction.Fstar α z θ + W z θ := by
    rw [hFdef, hWdef]; funext z θ; rfl
  set Ψ₀ : ℝ → ℝ → ℝ := Work.Construction.PhiTil α W Φg with hΨ₀def
  set Ψ : ℝ → ℝ → ℝ := Work.Construction.PhiTil α F Φg with hΨdef
  set H : ℝ := s / (1 + s) ^ 2 with hHdef
  have hH0 : 0 ≤ H := by rw [hHdef]; exact div_nonneg hs0.le (sq_nonneg _)
  set Q : ℝ := Maj s + H with hQdef
  have hQ0 : 0 ≤ Q := by rw [hQdef]; exact add_nonneg (hMaj0 s) hH0
  have hMQ : Maj s ≤ Q := by rw [hQdef]; linarith only [hH0]
  have hHQ : H ≤ Q := by rw [hQdef]; linarith only [hMaj0 s]
  have hQfac : 0 ≤ (CFs + 1) * Q := mul_nonneg (by linarith) hQ0
  have hQ2 : Q ≤ 2 := by
    have h1 : Maj s ≤ 1 := hMaj1 s
    have h2 : H ≤ 1 := by
      rw [hHdef]
      rw [div_le_one (by positivity)]
      nlinarith
    rw [hQdef]; linarith
  -- ## the slot bounds of the interface (as functions of `Maj`)
  have hSlotR : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Construction.Rop α Ψ₀ z θ| ≤ 3 := by
    intro z hz θ hθ
    exact (hBlk z θ hz hθ).1
  have hSlotU : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Construction.Uop α Ψ₀ z θ / Work.Construction.s2 θ| ≤ 3 := by
    intro z hz θ hθ
    exact (hBlk z θ hz hθ).2.1
  have hSlotV : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Construction.Vop Ψ₀ z θ| ≤ 3 := by
    intro z hz θ hθ
    exact (hBlk z θ hz hθ).2.2
  -- ## the same slots for `PhiTil α (F_* + W) Φg` (with the `+10` of `Psivar0_slots_sub`)
  have hΘ : ∀ z θ : ℝ, 0 < z →
      Work.Construction.Theta α W z θ
        - Work.Construction.Theta α (fun z θ => Work.Construction.Fstar α z θ + W z θ) z θ
        = -Real.sin (2 * θ) / (2 * (1 + z)) :=
    fun z θ hz => ThetaDiff hα0 hα1 hClass z θ hz
  have hΞid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg z θ
        = Work.Construction.PhiTil α W Φg z θ - Real.sin (2 * θ) / (2 * (1 + z)) := by
    intro z θ hz h1 h2
    have h := hΘ z θ hz
    simp only [Work.Construction.PhiTil] at h ⊢
    ring_nf at h ⊢
    linarith
  have hlocR : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Rop α Ψ z θ
        = Work.Construction.Rop α
            (fun z θ => Ψ₀ z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ := by
    intro z θ hz h1 h2
    rw [hΨdef, hΨ₀def, hFdec]
    exact Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0
      (fun z θ hz' h1' h2' => hΞid z θ hz' h1' h2') z θ hz h1 h2
  have hlocU : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Uop α Ψ z θ
        = Work.Construction.Uop α
            (fun z θ => Ψ₀ z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ := by
    intro z θ hz h1 h2
    rw [hΨdef, hΨ₀def, hFdec]
    exact Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0
      (fun z θ hz' h1' h2' => hΞid z θ hz' h1' h2') z θ hz h1 h2
  have hlocV : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Vop Ψ z θ
        = Work.Construction.Vop
            (fun z θ => Ψ₀ z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ := by
    intro z θ hz h1 h2
    rw [hΨdef, hΨ₀def, hFdec]
    exact Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0
      (fun z θ hz' h1' h2' => hΞid z θ hz' h1' h2') z θ hz h1 h2
  -- ## the F-slot bounds
  have hFstar : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Construction.Fstar α s θ'| ≤ CFs * H := by
    intro θ' hθ'
    have h := (hCFs (α := α) (z := s) (θ := θ') hαIoc hs0 hθ').1
    rw [hHdef]; exact h
  have hWval : ∀ θ', |W s θ'| ≤ Maj s := by
    intro θ'
    have h := hSlot1 s hs θ' 0 0 (by norm_num)
    simpa using h
  have hFval : ∀ θ' ∈ Work.Spaces.Iθ, |F s θ'| ≤ (CFs + 1) * Q := by
    intro θ' hθ'
    have h1 : |F s θ'| ≤ CFs * H + Maj s := by
      rw [hFdec]
      have h2 := abs_add_le (Work.Construction.Fstar α s θ') (W s θ')
      linarith only [h2, hFstar θ' hθ', hWval θ']
    have h3 : CFs * H + Maj s ≤ (CFs + 1) * Q := by
      have ha : CFs * H ≤ CFs * Q := mul_le_mul_of_nonneg_left hHQ hCFs0
      have hb : CFs * Q + Maj s ≤ CFs * Q + Q := add_le_add_right hMQ (CFs * Q)
      have hc : (CFs + 1) * Q = CFs * Q + Q := by ring
      linarith only [ha, hb, hc]
    linarith only [h1, h3]
  -- ## the endpoint cases
  rcases eq_or_lt_of_le hθ.1 with hθz | hθz
  · subst hθz
    have hKz : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
    rw [hKz, zero_mul, Real.cos_zero, mul_one]
    have hCpos : 0 < 200 * (CFs + 1) ^ 2 + 400 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hCpos.le (by linarith)) (by linarith)) hQ0
  · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
    · subst hθp
      have hKp : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      rw [hKp, zero_mul, Real.cos_pi_div_two, mul_zero]
    · -- ## the interior
      have hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθz, hθp⟩
      have hK0 : 0 ≤ Work.Spaces.K θ := hKnn θ hθ
      have hKle : Work.Spaces.K θ ≤ 2 * Real.cos θ := hKcos θ hθ
      have hc0 : 0 ≤ Real.cos θ := hcos0 θ hθ
      have hs2pos : 0 < Work.Construction.s2 θ := by
        rw [Work.Construction.s2]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith only [hθi.1]) (by linarith only [hθi.2])
      have hΞR : |Work.Construction.Rop α Ψ s θ| ≤ 13 := by
        rw [hlocR s θ hs0 hθi.1 hθi.2]
        have h := (Psivar0_slots_sub hαIoc hs0 hθi (Ψ1 := Ψ₀)).1
        have h2 := hSlotR s hs0 θ hθi
        rw [hΨ₀def] at h2
        linarith only [h, h2]
      have hΞU : |Work.Construction.Uop α Ψ s θ / Work.Construction.s2 θ| ≤ 13 := by
        rw [hlocU s θ hs0 hθi.1 hθi.2]
        have h := (Psivar0_slots_sub hαIoc hs0 hθi (Ψ1 := Ψ₀)).2.1
        have h2 := hSlotU s hs0 θ hθi
        rw [hΨ₀def] at h2
        linarith only [h, h2]
      have hΞV : |Work.Construction.Vop Ψ s θ| ≤ 13 := by
        rw [hlocV s θ hs0 hθi.1 hθi.2]
        have h := (Psivar0_slots_sub hαIoc hs0 hθi (Ψ1 := Ψ₀)).2.2
        have h2 := hSlotV s hs0 θ hθi
        rw [hΨ₀def] at h2
        linarith only [h, h2]
      have hUopLe : |Work.Construction.Uop α Ψ s θ| ≤ (13 : ℝ) * Work.Construction.s2 θ := by
        rw [abs_div, abs_of_pos hs2pos] at hΞU
        rw [div_le_iff₀ hs2pos] at hΞU
        linarith only [hΞU]
      -- ## the remaining `F`-slots
      have hFS : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
        Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
      have hpth_add : Work.Spaces.pth F s θ
          = Work.Spaces.pth (Work.Construction.Fstar α) s θ + Work.Spaces.pth W s θ := by
        have hpt : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
            F z' θ' = Work.Construction.Fstar α z' θ' + W z' θ' := by
          intro z' θ' _ _ _; rw [hFdec]
        rw [Work.FTS.PhiStar.CoreAux.pth_congr_Q0 hpt s θ hs0 hθi.1 hθi.2]
        exact Work.FTS.GalFields.RHS.Sharp.pth_add_Q0 hFS hClass.reg s θ hs0 hθi.1 hθi.2
      have hpz_add : Work.Spaces.pz F s θ
          = Work.Spaces.pz (Work.Construction.Fstar α) s θ + Work.Spaces.pz W s θ := by
        have hpt : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
            F z' θ' = Work.Construction.Fstar α z' θ' + W z' θ' := by
          intro z' θ' _ _ _; rw [hFdec]
        rw [Work.FTS.GalFields.RHS.Sharp.pz_congr_Q0 hpt s θ hs0 hθi.1 hθi.2]
        exact Work.FTS.GalFields.RHS.Sharp.pz_add_Q0 hFS hClass.reg s θ hs0 hθi.1 hθi.2
      have hFstarDz : |Work.Spaces.Dz (Work.Construction.Fstar α) s θ| ≤ CFs * H := by
        have h := (hCFs (α := α) (z := s) (θ := θ) hαIoc hs0 hθ).2.2.1
        rw [hHdef]; exact h
      have hFstarDth : |Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) s θ|
          ≤ CFs * H := by
        have h := (hCFs (α := α) (z := s) (θ := θ) hαIoc hs0 hθ).2.1
        rw [hHdef]; simpa only [Work.Construction.s2] using h
      have hWDz : |Work.Spaces.Dz W s θ| ≤ Maj s := by
        have h := hSlot1 s hs θ 1 0 (by norm_num); simpa using h
      have hWDth : |Work.Construction.s2 θ * Work.Spaces.pth W s θ| ≤ Maj s := by
        have h := hSlot1 s hs θ 0 1 (by norm_num)
        simpa [Work.Construction.s2, Work.Spaces.Dth] using h
      have hQadd : CFs * H + Maj s ≤ (CFs + 1) * Q := by
        have ha : CFs * H ≤ CFs * Q := mul_le_mul_of_nonneg_left hHQ hCFs0
        have hb : CFs * Q + Maj s ≤ CFs * Q + Q := add_le_add_right hMQ (CFs * Q)
        have hc : (CFs + 1) * Q = CFs * Q + Q := by ring
        linarith only [ha, hb, hc]
      have hDzF : |Work.Spaces.Dz F s θ| ≤ (CFs + 1) * Q := by
        have h2' : Work.Spaces.Dz F s θ
            = Work.Spaces.Dz (Work.Construction.Fstar α) s θ + Work.Spaces.Dz W s θ := by
          rw [Work.Spaces.Dz, hpz_add, Work.Spaces.Dz, Work.Spaces.Dz]; ring
        rw [h2']
        have h1 := abs_add_le (Work.Spaces.Dz (Work.Construction.Fstar α) s θ)
          (Work.Spaces.Dz W s θ)
        linarith only [h1, hFstarDz, hWDz, hQadd]
      have hs2pthF : |Work.Construction.s2 θ * Work.Spaces.pth F s θ| ≤ (CFs + 1) * Q := by
        have hdist : Work.Construction.s2 θ
            * (Work.Spaces.pth (Work.Construction.Fstar α) s θ + Work.Spaces.pth W s θ)
            = Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) s θ
              + Work.Construction.s2 θ * Work.Spaces.pth W s θ := by ring
        rw [hpth_add, hdist]
        have h1 := abs_add_le
          (Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) s θ)
          (Work.Construction.s2 θ * Work.Spaces.pth W s θ)
        linarith only [h1, hFstarDth, hWDth, hQadd]
      -- ## the angular moment of `F`
      have hFKF : |Work.Construction.FK F s| ≤ (CFs + 1) * Q := by
        have hFKdef : Work.Construction.FK F s
            = ∫ θ' in Work.Spaces.Iθ, F s θ' * Work.Spaces.K θ' := rfl
        have hK3 : ∀ θ' ∈ Work.Spaces.Iθ, Work.Spaces.K θ' ≤ 3 := by
          intro θ' hθ'
          have hs1 : Real.sin θ' ≤ 1 := Real.sin_le_one θ'
          have hs0' : 0 ≤ Real.sin θ' :=
            Real.sin_nonneg_of_mem_Icc ⟨hθ'.1, by linarith only [hθ'.2, Real.pi_pos]⟩
          have hc2 : Real.cos θ' ^ 2 ≤ 1 := by
            nlinarith only [Real.neg_one_le_cos θ', Real.cos_le_one θ', sq_nonneg (Real.cos θ')]
          rw [Work.Spaces.K]
          nlinarith
        have hmaj : ∀ θ' ∈ Work.Spaces.Iθ,
            |F s θ' * Work.Spaces.K θ'| ≤ ((CFs + 1) * Q) * Work.Spaces.K θ' := by
          intro θ' hθ'
          rw [abs_mul, abs_of_nonneg (hKnn θ' hθ')]
          exact mul_le_mul_of_nonneg_right (hFval θ' hθ') (hKnn θ' hθ')
        have hInt : Integrable ((fun θ' : ℝ => ((CFs + 1) * Q) * Work.Spaces.K θ'))
            (volume.restrict Work.Spaces.Iθ) :=
          (continuous_K.const_mul ((CFs + 1) * Q)).continuousOn.integrableOn_compact
            isCompact_Icc
        calc |Work.Construction.FK F s|
            ≤ ∫ θ' in Work.Spaces.Iθ, |F s θ' * Work.Spaces.K θ'| := by
              rw [hFKdef]
              simpa only [Real.norm_eq_abs] using
                (MeasureTheory.norm_integral_le_integral_norm
                  (μ := volume.restrict Work.Spaces.Iθ)
                  (f := fun θ' => F s θ' * Work.Spaces.K θ'))
          _ ≤ ∫ θ' in Work.Spaces.Iθ, ((CFs + 1) * Q) * Work.Spaces.K θ' :=
              MeasureTheory.setIntegral_mono_of_nonneg (fun θ' _ => abs_nonneg _) hmaj hInt
          _ = ((CFs + 1) * Q) * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.K θ') := by
              rw [MeasureTheory.integral_const_mul]
          _ = (CFs + 1) * Q := by rw [AngIntK, mul_one]
      -- ## the five summands of `N`
      have h11 : (13 : ℝ) ≤ 13 := le_rfl
      have hU1 : |2 * Work.Construction.Rop α Ψ s θ * F s θ| ≤ 26 * ((CFs + 1) * Q) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        have h1 : |Work.Construction.Rop α Ψ s θ| ≤ 13 := le_trans hΞR h11
        calc 2 * |Work.Construction.Rop α Ψ s θ| * |F s θ|
            ≤ 2 * 13 * ((CFs + 1) * Q) :=
              mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) (hFval θ hθ)
                (abs_nonneg _) (by norm_num)
          _ = 26 * ((CFs + 1) * Q) := by ring
      have hU2 : |2 * Work.Construction.Uop α Ψ s θ * Work.Spaces.pth F s θ|
          ≤ 26 * ((CFs + 1) * Q) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        have h1 : 2 * |Work.Construction.Uop α Ψ s θ|
            ≤ 2 * ((13 : ℝ) * Work.Construction.s2 θ) :=
          mul_le_mul_of_nonneg_left hUopLe (by norm_num)
        have h2 : Work.Construction.s2 θ * |Work.Spaces.pth F s θ| ≤ (CFs + 1) * Q := by
          simpa only [abs_mul, abs_of_pos hs2pos] using hs2pthF
        have h3 : 2 * |Work.Construction.Uop α Ψ s θ| * |Work.Spaces.pth F s θ|
            ≤ 2 * ((13 : ℝ) * Work.Construction.s2 θ) * |Work.Spaces.pth F s θ| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hUopLe (by norm_num)) (abs_nonneg _)
        have h4 : 2 * ((13 : ℝ) * Work.Construction.s2 θ) * |Work.Spaces.pth F s θ|
            = 2 * (13 : ℝ) * (Work.Construction.s2 θ * |Work.Spaces.pth F s θ|) := by ring
        have h5 : 2 * (13 : ℝ) * (Work.Construction.s2 θ * |Work.Spaces.pth F s θ|)
            ≤ 2 * 13 * ((CFs + 1) * Q) :=
          mul_le_mul (by linarith only [h11] : 2 * (13 : ℝ) ≤ 2 * 13) h2
            (mul_nonneg hs2pos.le (abs_nonneg _)) (by norm_num)
        calc 2 * |Work.Construction.Uop α Ψ s θ| * |Work.Spaces.pth F s θ|
            ≤ 2 * 13 * ((CFs + 1) * Q) := le_trans h3 (le_trans (le_of_eq h4) h5)
          _ = 26 * ((CFs + 1) * Q) := by ring
      have hU3 : |2 * α * Work.Construction.Vop Ψ s θ * Work.Spaces.Dz F s θ|
          ≤ 26 * ((CFs + 1) * Q) := by
        rw [abs_mul, abs_mul]
        have h1 : |2 * α| ≤ 2 := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_pos hα0]
          linarith
        have h2 : |Work.Construction.Vop Ψ s θ| ≤ 13 := le_trans hΞV h11
        calc |2 * α| * |Work.Construction.Vop Ψ s θ| * |Work.Spaces.Dz F s θ|
            ≤ 2 * 13 * ((CFs + 1) * Q) :=
              mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) hDzF
                (abs_nonneg _) (by norm_num)
          _ = 26 * ((CFs + 1) * Q) := by ring
      have hQQ : Q * Q ≤ 2 * Q := by
        have h := mul_le_mul_of_nonneg_left hQ2 hQ0
        exact le_trans h (le_of_eq (by ring))
      have hU4 : |(1/2) * Work.Construction.s2 θ * Work.Construction.FK F s
          * Work.Spaces.pth F s θ| ≤ (CFs + 1) ^ 2 * Q := by
        rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2), abs_of_pos hs2pos]
        have h2 : Work.Construction.s2 θ * |Work.Spaces.pth F s θ| ≤ (CFs + 1) * Q := by
          simpa only [abs_mul, abs_of_pos hs2pos] using hs2pthF
        have h3 : (1/2) * (Work.Construction.s2 θ * |Work.Spaces.pth F s θ|)
              * |Work.Construction.FK F s|
            ≤ (1/2) * ((CFs + 1) * Q) * ((CFs + 1) * Q) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) hFKF (abs_nonneg _)
            (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hQfac)
        have h4 : (1/2) * ((CFs + 1) * Q) * ((CFs + 1) * Q) ≤ (CFs + 1) ^ 2 * Q := by
          have hnn : 0 ≤ (CFs + 1) ^ 2 := by positivity
          have h5 : (1/2) * ((CFs + 1) * Q) * ((CFs + 1) * Q)
              = (1/2) * ((CFs + 1) ^ 2 * (Q * Q)) := by ring
          have h6 : (1/2) * ((CFs + 1) ^ 2 * (Q * Q)) ≤ (CFs + 1) ^ 2 * Q := by
            nlinarith only [hnn, hQ0, hQQ]
          rw [h5]; exact h6
        have h7 : ((1/2) * Work.Construction.s2 θ) * |Work.Construction.FK F s|
              * |Work.Spaces.pth F s θ|
            = (1/2) * (Work.Construction.s2 θ * |Work.Spaces.pth F s θ|)
              * |Work.Construction.FK F s| := by ring
        rw [h7]
        exact le_trans h3 h4
      have hU5 : |(Real.sin θ) ^ 2 * Work.Construction.FK F s * F s θ|
          ≤ 2 * (CFs + 1) ^ 2 * Q := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin θ))]
        have hs0' : 0 ≤ Real.sin θ :=
          Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith only [hθ.2, Real.pi_pos]⟩
        have h1 : (Real.sin θ) ^ 2 ≤ 1 := by
          nlinarith only [Real.sin_le_one θ, Real.neg_one_le_sin θ, sq_nonneg (Real.sin θ)]
        have h2 : (Real.sin θ) ^ 2 * |Work.Construction.FK F s| * |F s θ|
            ≤ 1 * ((CFs + 1) * Q) * ((CFs + 1) * Q) :=
          mul_le_mul (mul_le_mul h1 hFKF (abs_nonneg _) (by norm_num)) (hFval θ hθ)
            (abs_nonneg _) (mul_nonneg (by norm_num : (0:ℝ) ≤ 1) hQfac)
        have h3 : 1 * ((CFs + 1) * Q) * ((CFs + 1) * Q) ≤ 2 * (CFs + 1) ^ 2 * Q := by
          have hnn : 0 ≤ (CFs + 1) ^ 2 := by positivity
          calc 1 * ((CFs + 1) * Q) * ((CFs + 1) * Q)
              = (CFs + 1) ^ 2 * (Q * Q) := by ring
            _ ≤ (CFs + 1) ^ 2 * (2 * Q) := mul_le_mul_of_nonneg_left hQQ hnn
            _ ≤ 2 * (CFs + 1) ^ 2 * Q := by nlinarith only [hnn, hQ0]
        exact le_trans h2 h3
      -- ## the whole block
      have hexp : Work.Construction.N α F Φg s θ
          = (2 * Work.Construction.Rop α Ψ s θ * F s θ)
            + (-(2 * Work.Construction.Uop α Ψ s θ * Work.Spaces.pth F s θ))
            + (-(2 * α * Work.Construction.Vop Ψ s θ * Work.Spaces.Dz F s θ))
            + (-((1/2) * Work.Construction.s2 θ * Work.Construction.FK F s
                * Work.Spaces.pth F s θ))
            + (-((Real.sin θ) ^ 2 * Work.Construction.FK F s * F s θ)) := by
        rw [hΨdef, hFdef]
        simp only [Work.Construction.N, Work.Construction.s2]
        ring
      have hNbd : |Work.Construction.N α F Φg s θ| ≤ 100 * (CFs + 1) ^ 2 * Q := by
        rw [hexp]
        have h := abs_five_le (2 * Work.Construction.Rop α Ψ s θ * F s θ)
          (-(2 * Work.Construction.Uop α Ψ s θ * Work.Spaces.pth F s θ))
          (-(2 * α * Work.Construction.Vop Ψ s θ * Work.Spaces.Dz F s θ))
          (-((1/2) * Work.Construction.s2 θ * Work.Construction.FK F s
              * Work.Spaces.pth F s θ))
          (-((Real.sin θ) ^ 2 * Work.Construction.FK F s * F s θ))
        simp only [abs_neg] at h
        have hsum : 26 * ((CFs + 1) * Q) + 26 * ((CFs + 1) * Q) + 26 * ((CFs + 1) * Q)
            + (CFs + 1) ^ 2 * Q + 2 * (CFs + 1) ^ 2 * Q ≤ 100 * (CFs + 1) ^ 2 * Q := by
          have h2 : (CFs + 1) ≤ (CFs + 1) ^ 2 := by nlinarith only [hCFs0]
          nlinarith only [h2, hQ0]
        linarith only [h, hU1, hU2, hU3, hU4, hU5, hsum]
      have hfin : Work.Spaces.K θ * |Work.Construction.N α F Φg s θ|
          ≤ 200 * (CFs + 1) ^ 2 * (1 + C₀) * (1 + B) * Q * Real.cos θ := by
        have h1 : Work.Spaces.K θ * |Work.Construction.N α F Φg s θ|
            ≤ Work.Spaces.K θ * (100 * (CFs + 1) ^ 2 * Q) :=
          mul_le_mul_of_nonneg_left hNbd hK0
        have h2 : Work.Spaces.K θ * (100 * (CFs + 1) ^ 2 * Q)
            ≤ (2 * Real.cos θ) * (100 * (CFs + 1) ^ 2 * Q) :=
          mul_le_mul_of_nonneg_right hKle (by positivity)
        have h3 : (2 * Real.cos θ) * (100 * (CFs + 1) ^ 2 * Q)
            = 200 * (CFs + 1) ^ 2 * Q * Real.cos θ := by ring
        have h4 : 200 * (CFs + 1) ^ 2 * Q * Real.cos θ
            ≤ 200 * (CFs + 1) ^ 2 * (1 + C₀) * (1 + B) * Q * Real.cos θ := by
          have hA0 : 0 ≤ 200 * (CFs + 1) ^ 2 := by positivity
          have hcos0' : 0 ≤ Q * Real.cos θ := mul_nonneg hQ0 hc0
          have h5 : 200 * (CFs + 1) ^ 2 * 1 ≤ 200 * (CFs + 1) ^ 2 * ((1 + C₀) * (1 + B)) :=
            mul_le_mul_of_nonneg_left hA1 hA0
          have h6 : (200 * (CFs + 1) ^ 2 * 1) * (Q * Real.cos θ)
              ≤ (200 * (CFs + 1) ^ 2 * ((1 + C₀) * (1 + B))) * (Q * Real.cos θ) :=
            mul_le_mul_of_nonneg_right h5 hcos0'
          have h7 : (200 * (CFs + 1) ^ 2 * 1) * (Q * Real.cos θ)
              = 200 * (CFs + 1) ^ 2 * Q * Real.cos θ := by ring
          have h8 : (200 * (CFs + 1) ^ 2 * ((1 + C₀) * (1 + B))) * (Q * Real.cos θ)
              = 200 * (CFs + 1) ^ 2 * (1 + C₀) * (1 + B) * Q * Real.cos θ := by ring
          linarith only [h6, h7, h8]
        linarith only [h1, h2, h3, h4]
      have hCb : 200 * (CFs + 1) ^ 2
          ≤ 200 * (CFs + 1) ^ 2 + 400 := by linarith
      calc Work.Spaces.K θ * |Work.Construction.N α
              (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
              (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ) s θ|
          = Work.Spaces.K θ * |Work.Construction.N α F Φg s θ| := by
            rw [hFdef, hΦgdef]
        _ ≤ 200 * (CFs + 1) ^ 2 * (1 + C₀) * (1 + B) * Q * Real.cos θ := hfin
        _ = 200 * (CFs + 1) ^ 2 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) * Real.cos θ := by
            rw [hQdef, hHdef]
        _ ≤ (200 * (CFs + 1) ^ 2 + 400) * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2)
              * Real.cos θ := by
            have h0 : 0 ≤ (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) * Real.cos θ := by
              rw [← hQdef]
              exact mul_nonneg (mul_nonneg (mul_nonneg h1C h1B) hQ0) hc0
            nlinarith only [hCb, h0]

end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.PTgadgets =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- Triangle inequality for six signed terms. -/
theorem pt_abs_six_le (a b c d e f : ℝ) :
    |a - b + c + d - e - f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  rw [abs_le]
  constructor <;>
    linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b, le_abs_self c,
      neg_abs_le c, le_abs_self d, neg_abs_le d, le_abs_self e, neg_abs_le e, le_abs_self f,
      neg_abs_le f]

/-- Triangle inequality for five signed terms. -/
theorem pt_abs_five_le (a b c d e : ℝ) :
    |a - b - c - d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
  rw [abs_le]
  constructor <;>
    linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b, le_abs_self c,
      neg_abs_le c, le_abs_self d, neg_abs_le d, le_abs_self e, neg_abs_le e]

/-- The angular coefficient `c2m θ = cos 2θ - sin²θ` is bounded by `2` in absolute value. -/
theorem pt_abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m_eq]
  have h1 := Real.abs_cos_le_one (2 * θ)
  have h2 := Real.sin_sq_le_one θ
  have h3 : |Real.sin θ ^ 2| = Real.sin θ ^ 2 := abs_of_nonneg (sq_nonneg _)
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := abs_sub _ _
    _ = |Real.cos (2 * θ)| + Real.sin θ ^ 2 := by rw [h3]
    _ ≤ 1 + 1 := by linarith
    _ = 2 := by norm_num

/-- `z/(1+z)² ≤ 1` for `z ≥ 0`. -/
theorem pt_z_div_sq_le_one {z : ℝ} (hz : 0 ≤ z) : z / (1 + z) ^ 2 ≤ 1 := by
  have h1 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  rw [div_le_one h1]
  nlinarith [sq_nonneg z]

/-- The sharp pointwise data of the reference profile `F_*` on the open quadrant: all five
quantities are `O(α)`, because the radial factor `z/(1+z)²` is `≤ 1`. -/
theorem pt_Fstar_pt_data {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    |Work.Construction.Fstar α z θ| ≤ 100 * α ∧
      |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 100 * α ∧
      |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| ≤ 100 * α ∧
      |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ 2 * α ∧
      |Work.Construction.FK (Work.Construction.Fstar α) z| ≤ 2 * α := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hfrac : z / (1 + z) ^ 2 ≤ 1 := pt_z_div_sq_le_one hz.le
  have hα2 : α ^ 2 ≤ α := by nlinarith [hα.le, hα1]
  have hL : Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
    Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 (by linarith)
  have hFK : Work.Construction.FK (Work.Construction.Fstar α) z = α * (2 * z / (1 + z) ^ 2) :=
    Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans (Work.FTS.NonlinRows.Rl1.Fstar_pt hα hα1 hz hθI) ?_
    have h2 : 20 * α * (z / (1 + z) ^ 2) ≤ 20 * α := by
      have := mul_le_mul_of_nonneg_left hfrac (by positivity : (0 : ℝ) ≤ 20 * α)
      linarith [this]
    have h3 : 20 * α * z / (1 + z) ^ 2 = 20 * α * (z / (1 + z) ^ 2) := by ring
    linarith [h2]
  · refine le_trans (Work.FTS.NonlinRows.Rl1.DzFstar_pt hα hα1 hz hθI) ?_
    have h2 : 20 * α * (z / (1 + z) ^ 2) ≤ 20 * α := by
      have := mul_le_mul_of_nonneg_left hfrac (by positivity : (0 : ℝ) ≤ 20 * α)
      linarith [this]
    have h3 : 20 * α * z / (1 + z) ^ 2 = 20 * α * (z / (1 + z) ^ 2) := by ring
    linarith [h2]
  · refine le_trans (Work.FTS.NonlinRows.Rl1.DthFstar_pt hα hα1 hz hθ.1 hθ.2) ?_
    have h2 : 80 / 3 * α ^ 2 * (z / (1 + z) ^ 2) ≤ 80 / 3 * α ^ 2 := by
      have := mul_le_mul_of_nonneg_left hfrac (by positivity : (0 : ℝ) ≤ 80 / 3 * α ^ 2)
      linarith [this]
    have h3 : 80 / 3 * α ^ 2 * z / (1 + z) ^ 2 = 80 / 3 * α ^ 2 * (z / (1 + z) ^ 2) := by ring
    linarith [h2, hα2]
  · rw [hL, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + z),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * α)]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + z)]
    nlinarith [hα.le]
  · rw [hFK, abs_mul, abs_of_nonneg hα.le]
    have h2 : |2 * z / (1 + z) ^ 2| ≤ 2 := by
      have h1 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
      rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hz.le,
        abs_of_pos h1, div_le_iff₀ h1]
      nlinarith [sq_nonneg z]
    calc α * |2 * z / (1 + z) ^ 2| ≤ α * 2 := mul_le_mul_of_nonneg_left h2 hα.le
      _ ≤ 2 * α := by linarith

/-! ## The slot bounds of the interface -/

/-- The seven slot bounds of the interface `EpsDecay`, normalised to `≤ 1` (the majorant is
bounded by `1`, and `SlotMaj 0` is the case `j = i = 0` of a slot bound). -/
theorem pt_EpsDecay_slots {α : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε τ : ℝ}
    {g : Work.FTS.Galerkin.Fam} {Maj : ℝ → ℝ}
    (hDec : Work.FTS.StrongEps.EpsDecay α ρ Φs E ε τ g Maj) :
    (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, ∀ j i : ℕ, j + i ≤ 1 →
        |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            z θ| ≤ 1) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ,
        |Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ z θ| ≤ 1) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ,
        |Work.Spaces.Dz (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) z θ| ≤ 1) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ,
        |Work.Spaces.Dth (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) z θ| ≤ 1) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ ε g)) τ)) z θ| ≤ 3) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ ε g)) τ)) z θ
          / Work.Construction.s2 θ| ≤ 3) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ ε g)) τ)) z θ| ≤ 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz θ j i hji
    exact le_trans (hDec.2.2.2.1 z hz θ j i hji) (hDec.2.1 z)
  · intro z hz θ
    have h := le_trans (hDec.2.2.2.1 z hz θ 0 0 (by norm_num)) (hDec.2.1 z)
    simpa [Work.Spaces.mixed, Work.Spaces.DzIter, Work.Spaces.DthIter] using h
  · intro z hz θ
    have h := le_trans (hDec.2.2.2.1 z hz θ 1 0 (by norm_num)) (hDec.2.1 z)
    simpa [Work.Spaces.mixed, Work.Spaces.DzIter, Work.Spaces.DthIter] using h
  · intro z hz θ
    have h := le_trans (hDec.2.2.2.1 z hz θ 0 1 (by norm_num)) (hDec.2.1 z)
    simpa [Work.Spaces.mixed, Work.Spaces.DzIter, Work.Spaces.DthIter] using h
  · intro z hz θ hθ
    exact (hDec.2.2.2.2 z θ hz hθ).1
  · intro z hz θ hθ
    exact (hDec.2.2.2.2 z θ hz hθ).2.1
  · intro z hz θ hθ
    exact (hDec.2.2.2.2 z θ hz hθ).2.2

/-! ## The slots of the full profile `F = F_* + W` -/

/-- The value of `F = F_* + W`, and the two combinations `sin 2θ·∂_θF`, `D_zF` occurring in
`N₀` and `N`. -/
theorem pt_F_slots {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {W F : ℝ → ℝ → ℝ}
    (hWS : Work.FTS.EllipticEst.SmoothOpen W)
    (hFeq : F = fun z θ => Work.Construction.Fstar α z θ + W z θ)
    (hWval : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |W z θ| ≤ 1)
    (hWDz : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |Work.Spaces.Dz W z θ| ≤ 1)
    (hWDth : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |Work.Spaces.Dth W z θ| ≤ 1) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |F z θ| ≤ 101 ∧
        |Work.Construction.s2 θ * Work.Spaces.pth F z θ| ≤ 101 ∧
        |Work.Spaces.Dz F z θ| ≤ 101 := by
  have hFS : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hpth : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pth F z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth W z θ := by
    intro z θ hz h1 h2
    have hpt : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
        F z' θ' = Work.Construction.Fstar α z' θ' + W z' θ' := by
      intro z' θ' hz' h1' h2'
      rw [hFeq]
    rw [Work.FTS.PhiStar.CoreAux.pth_congr_Q0 hpt z θ hz h1 h2]
    exact Work.FTS.GalFields.RHS.Sharp.pth_add_Q0 hFS hWS z θ hz h1 h2
  have hpz : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pz F z θ
        = Work.Spaces.pz (Work.Construction.Fstar α) z θ + Work.Spaces.pz W z θ := by
    intro z θ hz h1 h2
    have hpt : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
        F z' θ' = Work.Construction.Fstar α z' θ' + W z' θ' := by
      intro z' θ' hz' h1' h2'
      rw [hFeq]
    rw [Work.FTS.GalFields.RHS.Sharp.pz_congr_Q0 hpt z θ hz h1 h2]
    exact Work.FTS.GalFields.RHS.Sharp.pz_add_Q0 hFS hWS z θ hz h1 h2
  intro z hz θ hθ
  obtain ⟨hFstar, hDzFstar, hDthFstar, -, -⟩ := pt_Fstar_pt_data hα hα1 hz hθ
  have h2 : Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      = Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ := rfl
  have h3 : Work.Spaces.Dth W z θ = Work.Construction.s2 θ * Work.Spaces.pth W z θ := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hFeq]
    have h1 := abs_add_le (Work.Construction.Fstar α z θ) (W z θ)
    nlinarith [h1, hFstar, hWval z hz θ, hα.le, hα1]
  · have hdist : Work.Construction.s2 θ
        * (Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth W z θ)
        = Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth W z θ := by
      simp only [Work.Construction.s2, Work.Spaces.Dth]
      ring_nf
    rw [hpth z θ hz hθ.1 hθ.2, hdist]
    have h1 := abs_add_le (Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
      (Work.Spaces.Dth W z θ)
    nlinarith [h1, hDthFstar, hWDth z hz θ, hα.le, hα1]
  · have h1 := abs_add_le (Work.Spaces.Dz (Work.Construction.Fstar α) z θ) (Work.Spaces.Dz W z θ)
    have h2' : Work.Spaces.Dz F z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz W z θ := by
      rw [Work.Spaces.Dz, hpz z θ hz hθ.1 hθ.2, Work.Spaces.Dz, Work.Spaces.Dz]
      ring
    rw [h2']
    nlinarith [h1, hDzFstar, hWDz z hz θ, hα.le, hα1]

/-! ## The slots of the residual stream function -/

/-- The three slots of `PhiTil α (F_* + W) Φg`, from the slots of `PhiTil α W Φg` (the
profile whose slots the interface bounds) and the explicit `Theta`-difference
`sin 2θ/(2(1+z))`. -/
theorem pt_Xi_slots {α : ℝ} (hαι : α ∈ Set.Ioc 0 1) {W Φg : ℝ → ℝ → ℝ}
    (hWS : Work.FTS.EllipticEst.SmoothOpen W)
    (hWC4 : Work.Spaces.HkMem α 4 W)
    (hSlotR : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.Rop α (Work.Construction.PhiTil α W Φg) z θ| ≤ 3)
    (hSlotU : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.Uop α (Work.Construction.PhiTil α W Φg) z θ
        / Work.Construction.s2 θ| ≤ 3)
    (hSlotV : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.Vop (Work.Construction.PhiTil α W Φg) z θ| ≤ 3) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.Rop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg)
          z θ| ≤ 13 ∧
        |Work.Construction.Uop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg)
          z θ / Work.Construction.s2 θ| ≤ 13 ∧
        |Work.Construction.Vop
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg)
          z θ| ≤ 13 := by
  have hα0 : 0 < α := hαι.1
  have hα1 : α ≤ 1 := hαι.2
  -- the explicit difference of the two `Theta`-parts
  have hΘ : ∀ z θ : ℝ, 0 < z →
      Work.Construction.Theta α W z θ
        - Work.Construction.Theta α (fun z θ => Work.Construction.Fstar α z θ + W z θ) z θ
        = -Real.sin (2 * θ) / (2 * (1 + z)) := by
    intro z θ hz
    have hLadd : Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + W z θ) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 W z :=
      Work.FTS.StrongEps.blocks.L12_Fstar_add_open hα0 hα1 hWS hWC4 hz.le
    have hLstar : Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
      Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα0 hα1 (by linarith)
    simp only [Work.Construction.Theta, Work.Construction.s2]
    rw [hLadd, hLstar]
    have hαne : α ≠ 0 := ne_of_gt hα0
    have h1z : (1 : ℝ) + z ≠ 0 := by linarith
    field_simp
    ring
  have hΞid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg z θ
        = Work.Construction.PhiTil α W Φg z θ - Real.sin (2 * θ) / (2 * (1 + z)) := by
    intro z θ hz h1 h2
    have h := hΘ z θ hz
    simp only [Work.Construction.PhiTil] at h ⊢
    ring_nf at h ⊢
    linarith
  have hlocR : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Construction.Rop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg)
          z θ
        = Work.Construction.Rop α (fun z θ =>
            Work.Construction.PhiTil α W Φg z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ :=
    fun z θ hz h1 h2 =>
      Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0 (fun z θ hz' h1' h2' => hΞid z θ hz' h1' h2')
        z θ hz h1 h2
  have hlocU : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Construction.Uop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg)
          z θ
        = Work.Construction.Uop α (fun z θ =>
            Work.Construction.PhiTil α W Φg z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ :=
    fun z θ hz h1 h2 =>
      Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0 (fun z θ hz' h1' h2' => hΞid z θ hz' h1' h2')
        z θ hz h1 h2
  have hlocV : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Construction.Vop
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg)
          z θ
        = Work.Construction.Vop (fun z θ =>
            Work.Construction.PhiTil α W Φg z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ :=
    fun z θ hz h1 h2 =>
      Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0 (fun z θ hz' h1' h2' => hΞid z θ hz' h1' h2')
        z θ hz h1 h2
  intro z hz θ hθ
  refine ⟨?_, ?_, ?_⟩
  · rw [hlocR z θ hz hθ.1 hθ.2]
    have h := (Psivar0_slots_sub hαι hz hθ (Ψ1 := Work.Construction.PhiTil α W Φg)).1
    linarith [hSlotR z hz θ hθ]
  · rw [hlocU z θ hz hθ.1 hθ.2]
    have h := (Psivar0_slots_sub hαι hz hθ (Ψ1 := Work.Construction.PhiTil α W Φg)).2.1
    linarith [hSlotU z hz θ hθ]
  · rw [hlocV z θ hz hθ.1 hθ.2]
    have h := (Psivar0_slots_sub hαι hz hθ (Ψ1 := Work.Construction.PhiTil α W Φg)).2.2
    linarith [hSlotV z hz θ hθ]

/-! ## The angular moment of `F = F_* + W` -/

/-- `FK (F_* + W) = FK F_* + FK W` and the resulting bound. -/
theorem pt_FK_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {W F : ℝ → ℝ → ℝ}
    (hWS : Work.FTS.EllipticEst.SmoothOpen W)
    (hWC4 : Work.Spaces.HkMem α 4 W)
    (hFeq : F = fun z θ => Work.Construction.Fstar α z θ + W z θ)
    {C7 B : ℝ} (hC7nn : 0 ≤ C7) (hB0 : 0 ≤ B)
    (hFKW : ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Construction.FK W z| ≤ C7 * B) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.FK F z| ≤ (100 + C7) * (1 + B) := by
  intro z hz
  obtain ⟨-, -, -, -, hFKstar⟩ :=
    pt_Fstar_pt_data (θ := 1) hα hα1 hz ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hadd : Work.Construction.FK F z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK W z := by
    rw [hFeq]
    exact Work.FTS.GalFields.RHS.FK_add_of_slices hz0
      (Work.Stability.integrableOn_slice_Fstar α hα z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hWS hWC4 hz)
  rw [hadd]
  have h1 := abs_add_le (Work.Construction.FK (Work.Construction.Fstar α) z)
    (Work.Construction.FK W z)
  have h2 := hFKW z hz
  have h3 : |Work.Construction.FK (Work.Construction.Fstar α) z| ≤ 100 := by
    nlinarith [hFKstar, hα.le, hα1]
  have h4 : |Work.Construction.FK W z| ≤ C7 * (1 + B) := by
    nlinarith [h2, hC7nn, hB0]
  nlinarith [h1, h3, h4, hB0, hC7nn]

end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.epsWP_blocks_bnd =====
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

namespace Work.FTS.StrongEps

set_option maxHeartbeats 2000000


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Pinning.hpin_of_hasPkgD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `hpin_of_hasPkgD` — the pinning lemma of the repaired elliptic package

This is the module behind obligation 1 of `FTS_EllLimOK`: from the repaired package
`HasPkgD α Ce E = HasPkg α Ce E ∧ PkgCos α E ∧ PkgDecay α E` one derives the *pinning*

`cos s · Φ̃(z,s) → 0`  (`s → π/2⁻`),  `Φ̃ = PhiTil α g (E g)`,

for every class-`C` source `g` and every `z > 0` (`REPLY_LEAD2.md` §2, §9).

## The argument

Fix `g` (class `C`) and `z > 0`, write `Ψ = PhiTil α g (E g)` and `φ(θ) = cos θ · Ψ z θ`.
Three inputs are used:

* `smoothOpen_PhiTil` (`EllPkgGo`'s regularity of the solution) gives `Ψ` of class `C^∞` on
  the open quadrant, hence `φ` is `C¹` on `(0,π/2)`;
* `EllPkgGo.V` gives `Vop Ψ ∈ ℋ⁴`, hence (extraction of the `D_z⁰`-term of the `ℋ⁰`-integrand,
  `integrableOn_sq_rpow_of_HkMem`) the weighted square `(Vop Ψ z ·)²·sin(2θ)^{-η}` is
  integrable; by `integrableOn_deriv_cos_mul_sq_rpow` — the pointwise identity
  `deriv (cos·θΨ z ·) = cos θ·Vop Ψ z θ` (`cos_mul_Vop_eq`) — this is the weighted square of
  `φ'`, which controls the *oscillation* of `φ` near `π/2`;
* `PkgCos` gives `Ψ/cos ∈ ℋ⁰`, hence `(Ψ z ·/cos ·)²·sin(2θ)^{-η}` is integrable; since
  `sin θ ≥ 1/2` on `(π/6, π/2)`, `integrableOn_cos_sq_rpow_tail` turns this into the
  weighted square `φ²·sin(2θ)^{-(η+4)}` on the tail `(π/6, π/2)`, whose weight is *not*
  integrable at `π/2`: that forces a point `τ` close to `π/2` with `|φ(τ)|` small.

Combining the small value at `τ` with the oscillation bound over a short enough tail gives
`|φ| ≤ ε` on a one-sided neighbourhood of `π/2`, i.e. `φ → 0`: this is
`SliceTrace.tendsto_zero_of_deriv_sq_integrable` (the `C¹` form of
`SliceTrace.deriv_tendsto_zero_at_pi_div_two`), applied with `η = Work.Spaces.eta = 99/100`
and `γ = η + 4 > 1`.

Note that *no* pointwise bound on `Vop Ψ` is needed: only the weighted `L²`-bounds of the
package enter.
-/

namespace Work.FTS_EllLimOK.Pinning

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The `θ`-slice `θ ↦ cos θ · Ψ z θ` of a quadrant-smooth `Ψ` is `C¹` on `(0, π/2)`. -/
theorem contDiffOn_one_cos_mul_slice {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 1 (fun s => Real.cos s * Ψ z s) (Set.Ioo 0 (π / 2)) := by
  have hs : ContDiffOn ℝ 1 (fun s => Ψ z s) (Set.Ioo 0 (π / 2)) :=
    (hsm.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  exact ((Real.contDiff_cos (n := 1)).contDiffOn).mul hs



end Work.FTS_EllLimOK.Pinning
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.pkg_pointwise_jets =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## §1  the mixed jets of a separable product `A(z)·B(θ)` -/

private lemma sep_DthIter (i : ℕ) (A B : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => A z * B θ)
      = fun z θ => A z * (Work.Spaces.Lop^[i] B) θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => A z * (Work.Spaces.Lop^[i] B) θ') θ
          = A z * (Work.Spaces.Lop^[i + 1] B) θ
      rw [deriv_const_mul_field (x := θ) (v := Work.Spaces.Lop^[i] B) (A z)]
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      ring

private lemma sep_DzIter (j : ℕ) (A C : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => A z * C θ)
      = fun z θ => (Work.Spaces.Zop^[j] A z) * C θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      show z * deriv (fun z' => Work.Spaces.Zop^[j] A z' * C θ) z
          = (Work.Spaces.Zop^[j + 1] A z) * C θ
      rw [deriv_mul_const_field (v := C θ) (u := Work.Spaces.Zop^[j] A) (x := z)]
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Zop]
      ring

private lemma zop_eq_dziter (j : ℕ) (A : ℝ → ℝ) (z : ℝ) :
    Work.Spaces.Zop^[j] A z = Work.Spaces.DzIter j (fun z _ => A z) z 0 := by
  have h := congrFun (Work.Spaces.Zop_slice j (fun z _ => A z) 0) z
  exact h.symm

/-- The mixed jet of a separable product is the product of the `θ`-jet of `B` with the
`z`-jet of `A`. -/
private lemma mixed_sep (j i : ℕ) (A B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => A z * B θ) z θ
      = (Work.Spaces.Lop^[i] B) θ * Work.Spaces.DzIter j (fun z _ => A z) z 0 := by
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => A z * B θ)) z θ = _
  rw [sep_DthIter i A B, sep_DzIter j A (Work.Spaces.Lop^[i] B)]
  show Work.Spaces.Zop^[j] A z * (Work.Spaces.Lop^[i] B) θ = _
  rw [zop_eq_dziter j A z]
  ring

/-- `D_θ^i` of a `(z,θ)`-function that only depends on `θ` is `Lop^i` of its `θ`-slice. -/
private lemma DthIter_sep_const (i : ℕ) (B : ℝ → ℝ) :
    ∀ z θ : ℝ, Work.Spaces.DthIter i (fun _ θ => B θ) z θ = (Work.Spaces.Lop^[i] B) θ := by
  induction i with
  | zero => intro z θ; rfl
  | succ i ih =>
      intro z θ
      rw [Work.Spaces.DthIter_succ]
      have hstep : Work.Spaces.DthIter i (fun _ θ => B θ) = fun _ θ => (Work.Spaces.Lop^[i] B) θ := by
        funext z θ
        exact ih z θ
      rw [hstep]
      show Real.sin (2 * θ) * deriv (fun θ' => (Work.Spaces.Lop^[i] B) θ') θ
          = (Work.Spaces.Lop^[i + 1] B) θ
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      try ring

private lemma DthIter_Sfun_eq (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i Work.FTS.H2.Sfun z θ
      = (Work.Spaces.Lop^[i] (fun θ : ℝ => Real.sin (2 * θ))) θ :=
  DthIter_sep_const i (fun θ : ℝ => Real.sin (2 * θ)) z θ

/-! ## §2  the angular factors of `Θ` -/

/-- `Lop` commutes with multiplication by a constant. -/
private lemma Lop_const_mul (c : ℝ) : ∀ i : ℕ, ∀ B : ℝ → ℝ,
    Work.Spaces.Lop^[i] (fun θ => c * B θ) = fun θ => c * (Work.Spaces.Lop^[i] B) θ := by
  intro i
  induction i with
  | zero => intro B; rfl
  | succ i ih =>
      intro B
      rw [Function.iterate_succ_apply']
      rw [show Work.Spaces.Lop^[i] (fun θ => c * B θ) = fun θ => c * (Work.Spaces.Lop^[i] B) θ
        from ih B]
      funext θ
      show Real.sin (2 * θ) * deriv (fun θ' => c * (Work.Spaces.Lop^[i] B) θ') θ
          = c * (Work.Spaces.Lop^[i + 1] B) θ
      rw [deriv_const_mul_field (x := θ) (v := Work.Spaces.Lop^[i] B) c]
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      ring

/-- `|D_θ^i (sin 2·)| ≤ Asin i` on the closed angular interval. -/
private lemma LopSin_bound (i : ℕ) (hi : i ≤ 4) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |(Work.Spaces.Lop^[i] (fun θ : ℝ => Real.sin (2 * θ))) θ| ≤ Work.FTS.H2.Asin i := by
  have h := Work.FTS.H2.abs_DthIter_Sfun_le i hi z hθ
  rw [DthIter_Sfun_eq i z θ] at h
  calc |(Work.Spaces.Lop^[i] (fun θ : ℝ => Real.sin (2 * θ))) θ|
      ≤ Work.FTS.H2.Asin i * Real.sin (2 * θ) := h
    _ ≤ Work.FTS.H2.Asin i * 1 :=
        mul_le_mul_of_nonneg_left (Real.sin_le_one _) (Work.FTS.H2.Asin_pos i).le
    _ = Work.FTS.H2.Asin i := mul_one _

private lemma Asin_le_384 (i : ℕ) (hi : i ≤ 4) : Work.FTS.H2.Asin i ≤ 384 := by
  interval_cases i <;> norm_num [Work.FTS.H2.Asin]

private lemma LopScaled_bound {α : ℝ} (hα : 0 < α) (i : ℕ) (hi : i ≤ 4) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |(Work.Spaces.Lop^[i] (fun θ : ℝ => (1 / (4 * α)) * Real.sin (2 * θ))) θ|
      ≤ (1 / (4 * α)) * Work.FTS.H2.Asin i := by
  rw [Lop_const_mul (1 / (4 * α)) i (fun θ : ℝ => Real.sin (2 * θ))]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (4 * α))]
  exact mul_le_mul_of_nonneg_left (LopSin_bound i hi (0 : ℝ) hθ) (by positivity)

/-! ## §3  the mixed jets of `Θ α g` -/

/-- `Θ α g` is the separable product `B(θ)·A(z)`, `B θ = (1/(4α)) sin 2θ`,
`A z = L₁₂ g z`, so its mixed jets factor. -/
private lemma Theta_mixed_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (Work.Construction.Theta α g) z θ
      = (Work.Spaces.Lop^[i] (fun θ => (1 / (4 * α)) * Real.sin (2 * θ))) θ
        * Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0 := by
  have hfun : Work.Construction.Theta α g
      = (fun z θ => Work.Construction.L12 g z * ((1 / (4 * α)) * Real.sin (2 * θ))) := by
    funext z θ
    simp only [Work.Construction.Theta, Work.Construction.s2]
    ring
  rw [hfun]
  exact mixed_sep j i (fun z => Work.Construction.L12 g z)
    (fun θ => (1 / (4 * α)) * Real.sin (2 * θ)) z θ

/-- **The mixed jets of `Θ α g` are bounded by the `D_z`-jets of `L₁₂ g`.** -/
private lemma Theta_jets_aux {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} {CL : ℝ} (hCL0 : 0 ≤ CL)
    (hL12 : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
        ≤ CL * Work.FTS.StrongGlobal.Xn6 α g) :
    ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i (Work.Construction.Theta α g) z θ|
        ≤ ((1 / (4 * α)) * 384) * (CL * Work.FTS.StrongGlobal.Xn6 α g) := by
  intro j i hji z θ hz hθ0 hθ2
  have hj4 : j ≤ 4 := by omega
  have hi4 : i ≤ 4 := by omega
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ2.le⟩
  have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  rw [Theta_mixed_eq α g j i z θ]
  have hLop := LopScaled_bound hα i hi4 hθIθ
  have hDz := hL12 j hj4 z hz
  calc |(Work.Spaces.Lop^[i] (fun θ => (1 / (4 * α)) * Real.sin (2 * θ))) θ
          * Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
      = |(Work.Spaces.Lop^[i] (fun θ => (1 / (4 * α)) * Real.sin (2 * θ))) θ|
        * |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0| := abs_mul _ _
    _ ≤ ((1 / (4 * α)) * Work.FTS.H2.Asin i) * (CL * Work.FTS.StrongGlobal.Xn6 α g) :=
        mul_le_mul hLop hDz (abs_nonneg _)
          (mul_nonneg (by positivity) (Work.FTS.H2.Asin_pos i).le)
    _ ≤ ((1 / (4 * α)) * 384) * (CL * Work.FTS.StrongGlobal.Xn6 α g) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hCL0 hXnn)
        exact mul_le_mul_of_nonneg_left (Asin_le_384 i hi4) (by positivity)

/-- `Θ α g` is `C^∞` on the open quadrant for a Galerkin-elliptic package. -/
private lemma Theta_smoothOpen {α Ce : ℝ} (hα : 0 < α) {g Φg : ℝ → ℝ → ℝ}
    (hGo : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Theta α g) := by
  have hEq : Work.Construction.Theta α g
      = (fun z θ => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 g z) := by
    funext z θ
    simp only [Work.Construction.Theta, Work.Construction.s2]
  rw [hEq]
  exact Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul
    (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
      Work.FTS.GalFields.RHS.smoothOpen_sin_two)
    (Work.FTS.GalFields.RHS.Sharp.smoothOpen_L12_gal hα hGo)

/-! ## §4  the assembly -/

/-- **The assembly**, parameterised by the `D_z`-jet bound for `L₁₂ g` on the class `C`. -/
private theorem pkg_pointwise_jets_aux {α Ce CL : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCL0 : 0 ≤ CL)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : HasPkg α Ce E) {fn : ℕ → Work.FTS.Galerkin.Fn} {f : Work.FTS.Galerkin.Fn}
    (hL : LimSeq4 α fn f)
    (hpin : ∀ n : ℕ, ∀ z ∈ Set.Ioi (0 : ℝ),
      Filter.Tendsto (fun s => Real.cos s
        * Work.Construction.PhiTil α (fn n) (E (fn n)) z s) (𝓝[<] (π / 2)) (𝓝 0))
    (hL12j : ∀ (g : Work.FTS.Galerkin.Fn), Work.FTS.ClassC.ClassC α g →
      ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
        |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
          ≤ CL * Work.FTS.StrongGlobal.Xn6 α g) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ C := by
  obtain ⟨CS, hCS0, hCS⟩ := Work.FTS_EllLimOK.SlotSup.slot_jets_sup_le α hα hα1
  obtain ⟨CV, hCV0, hCV⟩ := Work.FTS_EllLimOK.VopTransfer.mixed_le_of_Vop_jets
  obtain ⟨B, hB⟩ := hL.bound
  have hB0 : (0 : ℝ) ≤ B := le_trans (Work.Spaces.HkNorm_nonneg α 6 (fn 0)) (hB 0)
  refine ⟨CV * (CS * (|Ce| * B)) + ((1 / (4 * α)) * 384) * (CL * B) + 1, by positivity, ?_⟩
  intro n j i hji z θ hzθ
  have hz : 0 < z := hzθ.1
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hzθ.2
  have hθ0 : 0 < θ := hzθ.2.1
  have hθ2 : θ < π / 2 := hzθ.2.2
  -- the two packages at `fn n`
  have hPkg := hE (fn n) (hL.classC n)
  have hGo : Work.FTS.VocabO.EllPkgGo α Ce (fn n) (E (fn n)) := hPkg.1
  have hK : Work.FTS.ClassC.EllPkgK α 6 Ce (fn n) (E (fn n)) := hPkg.2
  -- smoothness of `Φ̃` and of `Θ`
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α (fn n) (E (fn n))) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hGo
  have hΘsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Theta α (fn n)) :=
    Theta_smoothOpen hα hGo
  have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α (fn n) :=
    Work.Spaces.HkNorm_nonneg α 6 (fn n)
  have hφnn : 0 ≤ |Ce| * B := mul_nonneg (abs_nonneg Ce) hB0
  -- ## the jets of `Vop Φ̃`, from the package and the `ℋ⁶`-slot bound
  have hVjets : ∀ j l : ℕ, j + l ≤ 4 → ∀ z' θ' : ℝ, 0 < z' → θ' ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed j l (Work.Construction.Vop
        (Work.Construction.PhiTil α (fn n) (E (fn n)))) z' θ'| ≤ CS * (|Ce| * B) := by
    intro j l hjl z' θ' hz' hθ'
    refine le_trans (hCS _ hK.V.1.1 hK.V.1.2 j l (by omega) z' θ' hz' hθ'.1 hθ'.2) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCS0.le
    calc Work.Spaces.HkNorm α 6 (Work.Construction.Vop
            (Work.Construction.PhiTil α (fn n) (E (fn n))))
        ≤ Ce * Work.Spaces.HkNorm α 6 (fn n) := hK.V.2
      _ ≤ |Ce| * Work.Spaces.HkNorm α 6 (fn n) :=
          mul_le_mul_of_nonneg_right (le_abs_self Ce)
            (Work.Spaces.HkNorm_nonneg α 6 (fn n))
      _ ≤ |Ce| * B := mul_le_mul_of_nonneg_left (hB n) (abs_nonneg Ce)
  -- ## the jets of `Φ̃`
  have hΦjets : ∀ j i : ℕ, j + i ≤ 4 → ∀ z' θ' : ℝ, 0 < z' → θ' ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed j i (Work.Construction.PhiTil α (fn n) (E (fn n))) z' θ'|
        ≤ CV * (CS * (|Ce| * B)) :=
    hCV (CS * (|Ce| * B)) (mul_nonneg hCS0.le hφnn) _
      hΦsm (hpin n) hVjets
  -- ## the jets of `Θ α (fn n)`
  have hΘjets : ∀ j i : ℕ, j + i ≤ 4 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      |Work.Spaces.mixed j i (Work.Construction.Theta α (fn n)) z' θ'|
        ≤ ((1 / (4 * α)) * 384) * (CL * Work.FTS.StrongGlobal.Xn6 α (fn n)) :=
    Theta_jets_aux hα hCL0 (hL12j (fn n) (hL.classC n))
  -- ## the decomposition `E (fn n) = Φ̃ + Θ`
  have hdec : E (fn n) = fun z θ => Work.Construction.PhiTil α (fn n) (E (fn n)) z θ
      + Work.Construction.Theta α (fn n) z θ := by
    funext z' θ'
    simp only [Work.Construction.PhiTil]
    ring
  rw [hdec, Work.FTS.EllipticEst.SmoothOpen.mixed_add hΦsm hΘsm j i z θ hz hθ0 hθ2]
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (hΦjets j i hji z θ hz hθI)
    (hΘjets j i hji z θ hz hθ0 hθ2)) ?_
  have hle : ((1 / (4 * α)) * 384) * (CL * Work.FTS.StrongGlobal.Xn6 α (fn n))
      ≤ ((1 / (4 * α)) * 384) * (CL * B) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB n) hCL0) (by positivity)
  linarith

theorem pkg_pointwise_jets {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.HasPkg α Ce E) {fn : ℕ → Work.FTS.Galerkin.Fn}
    {f : Work.FTS.Galerkin.Fn} (hL : Work.FTS_EllLimOK.LimSeq4 α fn f)
    (hpin : ∀ n : ℕ, ∀ z ∈ Set.Ioi (0 : ℝ),
      Filter.Tendsto (fun s => Real.cos s
        * Work.Construction.PhiTil α (fn n) (E (fn n)) z s) (𝓝[<] (π / 2)) (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ C := by
  obtain ⟨CL, hCL0, hCL⟩ := L12jets_classC hα hα1
  exact pkg_pointwise_jets_aux hα hα1 hCL0.le hE hL hpin hCL

end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowT.diffRow2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowT

set_option autoImplicit false

/-! ## Two elementary facts about the transport field on the domain of `L₁₂` -/

/-- **`L₁₂` only sees the values on `(0,∞) × [0,π/2]`**: at `z ≥ 0` its iterated integral runs
over `Ioi z ⊆ Ioi 0` in the radial variable and over `Iθ` in the angular one, so a pointwise
equality of the two profiles there gives equality of the zero-modes. -/
theorem L12_congr_Ioi_Iθ {a b : ℝ → ℝ → ℝ}
    (h : ∀ s θ : ℝ, 0 < s → θ ∈ Work.Spaces.Iθ → a s θ = b s θ) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 a z = Work.Construction.L12 b z := by
  simp only [Work.Construction.L12, Work.FM.L12, Work.FM.L12dens]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  rw [h s θ (lt_of_le_of_lt hz (Set.mem_Ioi.mp hs)) hθ]

/-- `sin(2θ) = 0` at the two endpoints of `Iθ`: the angular weight of `D_θ` kills the (possibly
junk) values of the derivative there. -/
theorem sin_two_eq_zero_of_mem_Iθ_of_not_mem_Ioo {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (h : θ ∉ Set.Ioo 0 (π / 2)) : Real.sin (2 * θ) = 0 := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0]; simp
  · have h1 : θ = π / 2 :=
      le_antisymm hθ.2 (le_of_not_gt fun hlt => h ⟨h0, hlt⟩)
    rw [h1]
    have h2 : 2 * (π / 2) = π := by ring
    rw [h2, Real.sin_pi]

/-- **The transport field is additive on two profiles `C^∞` on the open quadrant.**  In the
interior of `Iθ` this is the additivity of `∂_θ` on `SmoothOpen` data
(`Work.FTS.GalFields.RHS.Sharp.pth_add_Q0`), and at the two endpoints `sin(2θ)` kills both
sides.  (Only the *quadrant* values matter: `L₁₂` integrates over `z > 0`, `θ ∈ Iθ`.) -/
theorem Tf_add_open {g d : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hd : Work.FTS.EllipticEst.SmoothOpen d) :
    ∀ s θ : ℝ, 0 < s → θ ∈ Work.Spaces.Iθ →
      Work.FTS_MuLipC.Tf (fun z θ => g z θ + d z θ) s θ
        = Work.FTS_MuLipC.Tf g s θ + Work.FTS_MuLipC.Tf d s θ := by
  intro s θ hs hθ
  have hDth : Work.Spaces.Dth (fun z θ => g z θ + d z θ) s θ
      = Work.Spaces.Dth g s θ + Work.Spaces.Dth d s θ := by
    by_cases hIoo : θ ∈ Set.Ioo 0 (π / 2)
    · have hpth := Work.FTS.GalFields.RHS.Sharp.pth_add_Q0 hg hd s θ hs hIoo.1 hIoo.2
      simp only [Work.Spaces.Dth]
      rw [hpth]; ring
    · have hzero := sin_two_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hIoo
      simp only [Work.Spaces.Dth, hzero, zero_mul, add_zero]
  simp only [Work.FTS_MuLipC.Tf]
  rw [hDth]; ring

/-! ## Additivity of the transport zero-mode over a difference -/

/-- **The transport zero-mode is additive over a difference of profiles**, in the conditional form
in which the four integrability certificates required by `Work.FTS.LocData.L12_add_mul` are
hypotheses (they are supplied, for `C^∞`-on-the-quadrant `ℋ⁴`-profiles, by
`Work.FTS_MuLipC.RowT.Tf_slice_integrable` and `Work.FTS_MuLipC.RowT.Tf_dens_integrable`).

`Tf` is additive on `SmoothOpen` data (`Tf_add_open`), so on `(0,∞) × Iθ` the field `Tf f` agrees
with `Tf f' + Tf (f - f')`; `L₁₂` of the sum splits by `L12_add_mul` (the integrals), and the
congruence of `L₁₂` on the domain of integration moves the identity to `Tf f`. -/
theorem L12_Tf_sub_of {f f' : ℝ → ℝ → ℝ}
    (hf' : Work.FTS.EllipticEst.SmoothOpen f')
    (hdS : Work.FTS.EllipticEst.SmoothOpen (f - f'))
    (hslice' : ∀ s ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS_MuLipC.Tf f' s θ / s) Work.Spaces.Iθ)
    (hsliceD : ∀ s ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS_MuLipC.Tf (f - f') s θ / s) Work.Spaces.Iθ)
    (hdens' : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.FTS_MuLipC.Tf f')) (Set.Ioi (0 : ℝ)))
    (hdensD : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.FTS_MuLipC.Tf (f - f'))) (Set.Ioi (0 : ℝ))) :
    Work.Construction.L12 (Work.FTS_MuLipC.Tf f) 0
      = Work.Construction.L12 (Work.FTS_MuLipC.Tf f') 0
        + Work.Construction.L12 (Work.FTS_MuLipC.Tf (f - f')) 0 := by
  have hadd := (Work.FTS.LocData.L12_add_mul (c := 0) (a := Work.FTS_MuLipC.Tf f')
    (b := Work.FTS_MuLipC.Tf (f - f')) (z := 0) hslice' hsliceD hdens' hdensD).1
  refine (L12_congr_Ioi_Iθ (a := Work.FTS_MuLipC.Tf f)
    (b := fun z θ => Work.FTS_MuLipC.Tf f' z θ + Work.FTS_MuLipC.Tf (f - f') z θ) ?_
    le_rfl).trans hadd
  intro s θ hs hθ
  conv_lhs =>
    rw [show (f : ℝ → ℝ → ℝ) = fun z θ => f' z θ + (f - f') z θ from by
      funext z θ
      simp]
  exact Tf_add_open hf' hdS s θ hs hθ

/-- **The transport zero-mode is additive over a difference of `ℋ⁴`-honest profiles**: the
`Tf g`-form of `L12_Tf_sub_of`, with the four integrability certificates supplied by
`Work.FTS_MuLipC.RowT.Tf_slice_integrable` and `Work.FTS_MuLipC.RowT.Tf_dens_integrable`. -/
theorem L12_Tf_sub {α : ℝ} (hα : 0 < α) {f f' : ℝ → ℝ → ℝ}
    (hf' : Work.FTS.EllipticEst.SmoothOpen f')
    (hdS : Work.FTS.EllipticEst.SmoothOpen (f - f'))
    (hmem' : Work.Spaces.HkMem α 4 f')
    (hmemd : Work.Spaces.HkMem α 4 (f - f')) :
    Work.Construction.L12 (Work.FTS_MuLipC.Tf f) 0
      = Work.Construction.L12 (Work.FTS_MuLipC.Tf f') 0
        + Work.Construction.L12 (Work.FTS_MuLipC.Tf (f - f')) 0 :=
  L12_Tf_sub_of hf' hdS
    (fun s hs => Tf_slice_integrable hα hf' hmem' s hs)
    (fun s hs => Tf_slice_integrable hα hdS hmemd s hs)
    (Tf_dens_integrable hα hf' hmem')
    (Tf_dens_integrable hα hdS hmemd)

/-- **The difference row of the transport term** (`DiffRow2 α C₀`,
`Submission/Work/FTS_MuLipC/Defs.lean`): for `ClassC α` profiles of `ℋ⁴`-size `≤ C₀α²`, the
`L₁₂`-zero-mode of the *linear* transport field `Tf g = 3·D_θg/(1+z)` is Lipschitz in the profile.
The transport functional is `L₁₂` of a linear image of the profile, so this row is the
single-profile row `KMu2_row` (`|L₁₂(3 D_θg/(1+z))(0)| ≤ 9·|g|_{ℋ⁴}`) transported to the
difference `f − f'` by the additivity of `L₁₂` on the class (`KMu2_row` is
`Work.FTS_MuLamOK.KMu2_row`; the linearity of `L₁₂` on honest fields is available as
`Work.FTS.LocData.L12_add_mul`, `Work.FTS.GalFields.RHS.Sharp.L12_sub_ge0`,
`Work.FTS.GalBasis.cc.L12_add_of_HkMem`). -/
theorem diffRow2 {α C₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS_MuLipC.DiffRow2 α C₀ := by
  refine ⟨Work.FTS_MuLamOK.KMu2, Work.FTS_MuLamOK.KMu2_pos, ?_⟩
  intro f f' hf hf' _hXf _hXf'
  have hd : Work.FTS.ClassC.ClassC α (f - f') :=
    Work.FTS.StrongEps.EComparison.classC_sub hf hf'
  have hmem' : Work.Spaces.HkMem α 4 f' := Work.FTS.ClassC.classC_hkMem_four hf'
  have hmemd : Work.Spaces.HkMem α 4 (f - f') := Work.FTS.ClassC.classC_hkMem_four hd
  have hsub := L12_Tf_sub hα hf'.reg hd.reg hmem' hmemd
  have hrow := Work.FTS_MuLamOK.KMu2_row hα hα1 hd.reg hmemd
  have hdiff : Work.Construction.L12 (Work.FTS_MuLipC.Tf f) 0
      - Work.Construction.L12 (Work.FTS_MuLipC.Tf f') 0
      = Work.Construction.L12 (Work.FTS_MuLipC.Tf (f - f')) 0 := by linarith
  rw [hdiff]
  exact hrow

end Work.FTS_MuLipC.RowT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.MubarAssemblyAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS_RegExport.RXR5L

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp gSlice)

set_option autoImplicit false

/-- `Env` is monotone in the second (nonnegative) argument. -/
theorem Env_mono {β : ℝ} (hβ : 0 ≤ β) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Work.FTS_MuLipC.Env β a ≤ Work.FTS_MuLipC.Env β b := by
  have h1 : Real.sqrt β * a ≤ Real.sqrt β * b :=
    mul_le_mul_of_nonneg_left hab (Real.sqrt_nonneg β)
  have h2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
  have h3 : β ^ (-(3 / 2 : ℝ)) * a ^ 2 ≤ β ^ (-(3 / 2 : ℝ)) * b ^ 2 :=
    mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hβ _)
  simp only [Work.FTS_MuLipC.Env]
  linarith

/-- `SG α g` agrees with the raw family `g` on the open quadrant, for `τ ≥ 0`. -/
theorem SG_agree_g {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    Work.FTS_RegExport.RXR5.AgreeOnQ (gSlice (Work.FTS_RegExport.RXR5.SG α g) τ)
      (gSlice g τ) := by
  intro z θ hz hθ hθ2
  change Work.FTS_RegExport.RXR5.SG α g z θ τ = g z θ τ
  rw [show Work.FTS_RegExport.RXR5.SG α g z θ τ
      = Work.FTS.FinalV2.tauExt g z θ τ from
    Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.le hθ2.le,
    Work.FTS.FinalV2.tauExt_of_nonneg g hτ]

/-- `SΨ α Φs E g` agrees with `PsiCan Φs E g` on the open quadrant, for `τ ≥ 0`. -/
theorem SY_agree_PsiCan {α : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ}
    (hτ : 0 ≤ τ) :
    Work.FTS_RegExport.RXR5.AgreeOnQ (gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ)
      (gSlice (Work.FTS.Nonlin.PsiCan Φs E g) τ) := by
  intro z θ hz hθ hθ2
  have h1 := Work.FTS_RegExport.RXR5.SΨ_slice_agreeOnQ α Φs E g τ z θ hz hθ hθ2
  have h2 : Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.FinalV2.tauExt g)) τ z θ
      = Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ := by
    have hfun : Work.FTS.Galerkin.slice (Work.FTS.FinalV2.tauExt g) τ
        = Work.FTS.Galerkin.slice g τ := by
      funext z' θ'
      exact Work.FTS.FinalV2.tauExt_of_nonneg g hτ
    simp only [Work.FTS.Nonlin.PsiCan, Work.FTS.Galerkin.slice]
    rw [hfun]
  exact h1.trans h2

/-- The `F`-profile `F_* + slice (SG α g) τ` agrees with `F_* + slice g τ` on the quadrant. -/
theorem Ftau_SG_agree {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    Work.FTS_RegExport.RXR5.AgreeOnQ
      (Work.Construction.Ftau (pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ)
      (Work.Construction.Ftau (pExp α) g τ) :=
  Work.FTS_RegExport.RXR5.Ftau_congr_of_agreeOnQ (SG_agree_g (α := α) hτ)

/-- **The `mubar` of the sanitised family is the reference `mubar`.** -/
theorem mubar_sanitized_eq {α : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ}
    (hτ : 0 ≤ τ) :
    Work.Construction.mubar
        (Work.Construction.N0 (pExp α)
          (Work.Construction.Ftau (pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ)
          (gSlice (Work.FTS_RegExport.RXR5.SG α g) τ))
        (Work.Construction.N (pExp α)
          (Work.Construction.Ftau (pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ)
          (gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ))
      = Work.Construction.mubar
        (Work.Construction.N0 (pExp α)
          (Work.Construction.Ftau (pExp α) g τ) (gSlice g τ))
        (Work.Construction.N (pExp α)
          (Work.Construction.Ftau (pExp α) g τ)
          (gSlice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) :=
  Work.FTS_RegExport.RXR5.mubar_congr_of_agreeOnQ (α := pExp α)
    (Ftau_SG_agree (α := α) hτ) (SG_agree_g (α := α) hτ) (SY_agree_PsiCan (α := α) hτ)

/-- **The modulation identity.**  The reference `mubar` is `2·pExp α·μ(τ)` minus the transport
zero-mode `L₁₂(3 D_θ g(τ)/(1+z))(0)`. -/
theorem mubar_ref_eq {α : ℝ} (hα : 0 < α) {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ} :
    Work.Construction.mubar
        (Work.Construction.N0 (pExp α)
          (Work.Construction.Ftau (pExp α) g τ) (gSlice g τ))
        (Work.Construction.N (pExp α)
          (Work.Construction.Ftau (pExp α) g τ)
          (gSlice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
      = 2 * (pExp α) * Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g τ
        - Work.Construction.L12
            (fun z θ => 3 * Work.Spaces.Dth (gSlice g τ) z θ / (1 + z)) 0 := by
  have hβ : (pExp α) ≠ 0 := ne_of_gt (Work.FTS.Regularity.pExp_pos hα)
  have hmu : Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g τ
      = Work.FTS.Galerkin.muDyn (pExp α)
          (Work.FTS.Nonlin.PsiCan Φs (⇑E) (Work.FTS.FinalV2.cst (gSlice g τ)))
          (Work.FTS.FinalV2.cst (gSlice g τ)) 0 := rfl
  rw [hmu, Work.FTS_MuLipC.muDyn_const_eq]
  simp only [Work.FTS_MuLipC.Sn0, Work.FTS_MuLipC.Sn]
  rw [show Work.Construction.Ftau (pExp α) g τ
        = Work.Construction.Ftot (pExp α) (gSlice g τ) from rfl,
      show gSlice (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) τ
        = fun z θ => Φs z θ + E (gSlice g τ) z θ from rfl,
      Work.FTS.GalBasis.L12_congr_all (z := (0 : ℝ)) (a := Work.FTS_MuLipC.Tf (gSlice g τ))
        (b := fun z θ => Work.Spaces.Dth (gSlice g τ) z θ * (1 + z)⁻¹ * 3)
        (fun z θ => by simp only [Work.FTS_MuLipC.Tf]; ring),
      Work.Construction.mubar]
  field_simp
  ring_nf

end Work.FTS_RegExport.RXR5L
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.SG_C1Jet =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 Elementary helpers -/

/-- Monotonicity of `Jet` in its constant. -/
theorem Jet_mono {α S N N' : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Work.FTS.Regularity.Jet α S N h)
    (hN : N ≤ N') : Work.FTS.Regularity.Jet α S N' h := by
  refine ⟨le_trans H.1 hN, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    exact le_trans (H.2.1 z θ τ hz hθ hτ) hN
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := H.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have hd : (0 : ℝ) ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_nonneg (by positivity) α
    exact le_trans h1 (mul_le_mul_of_nonneg_right hN hd)

/-- On the box `z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]` the extension `extG` of the sanitised family is the
family itself (they differ only in the `τ < 0` jet and for `z < 0`). -/
theorem SG_extG_eq {α S z θ τ : ℝ} {g : Work.FTS.Galerkin.Fam} (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc 0 S) :
    Work.FTS.RegPkgGal.extG (Work.FTS_RegExport.RXR5.SG α g) z θ τ
      = Work.FTS_RegExport.RXR5.SG α g z θ τ := by
  rcases eq_or_lt_of_le hz with h | h
  · rw [← h, Work.FTS.RegPkgGal.extG_of_nonpos le_rfl,
      Work.FTS_RegExport.RXR5.SG_apply_of_nonpos le_rfl]
  · rw [Work.FTS.RegPkgGal.extG_of_pos h hτ.1,
      Work.FTS_RegExport.RXR5.SG_apply_of_pos h hθ.1 hθ.2]

/-- `C₀ ≥ 0`: the `ℋ⁴`-smallness clause of `DynOK` bounds the nonnegative `Xn` by
`C₀ (pExp α)²`. -/
theorem C0_nonneg {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    0 ≤ C₀ := by
  have h1 : Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice g 0)
      ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 :=
    Work.FTS.Final.DynOK.Xn_le hOK.1 0 le_rfl
  have h2 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
      (Work.FTS.Galerkin.slice g 0) := Real.sqrt_nonneg _
  have h3 : 0 < (Work.FTS.Regularity.pExp α) ^ 2 := by
    have := Work.FTS.Regularity.pExp_pos hα; positivity
  nlinarith [h1, h2, h3]

/-- `SG α g · θ ·` vanishes identically when `θ` is one of the two angular endpoints (for
`τ ≥ 0`), and also for `z ≤ 0`. -/
theorem SG_eq_zero_of_endpoint {α S z θ τ : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hvanish : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0)
    (hτ : τ ∈ Set.Icc 0 S) (hz : 0 ≤ z) (hθ : θ = 0 ∨ θ = π / 2) :
    Work.FTS_RegExport.RXR5.SG α g z θ τ = 0 := by
  rcases eq_or_lt_of_le hz with h | h
  · rw [← h]; exact Work.FTS_RegExport.RXR5.SG_apply_of_nonpos le_rfl
  · rcases hθ with rfl | rfl
    · rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos h le_rfl (by linarith [Real.pi_pos]),
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
      exact (hvanish τ hτ.1 z h.le).1
    · rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos h (by linarith [Real.pi_pos]) le_rfl,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
      exact (hvanish τ hτ.1 z h.le).2

/-- The weight `z^{3/2}/(1+z)²` is bounded by `1`. -/
theorem z_rpow_three_halves_div_sq_le_one {z : ℝ} (hz : 0 < z) :
    z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ 1 := by
  have h1 : 0 < (1 + z) ^ 2 := by positivity
  rw [div_le_iff₀ h1, one_mul]
  have hA : z ^ ((3 : ℝ) / 2) ≤ (1 + z) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hz.le (by linarith) (by norm_num)
  have hB : (1 + z) ^ ((3 : ℝ) / 2) ≤ (1 + z) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [Real.rpow_two] at hB
  linarith

/-- On a horizon `[0,S]` the Lipschitz modulus `L|τ - τ'|` upgrades to the `α`-modulus
`L · max S 1 · |τ - τ'|^α`. -/
theorem abs_sub_le_max_mul_rpow {S α τ τ' : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hτ : τ ∈ Set.Icc 0 S) (hτ' : τ' ∈ Set.Icc 0 S) :
    |τ - τ'| ≤ max S 1 * |τ - τ'| ^ α := by
  have ht0 : 0 ≤ |τ - τ'| := abs_nonneg _
  have htS : |τ - τ'| ≤ S := by
    rw [abs_le]
    exact ⟨by linarith [hτ.1, hτ'.2], by linarith [hτ.2, hτ'.1]⟩
  have hmax1 : 1 ≤ max S 1 := le_max_right _ _
  have hle : |τ - τ'| ≤ max S 1 := le_trans htS (le_max_left _ _)
  rcases eq_or_lt_of_le ht0 with h | ht
  · rw [← h, Real.zero_rpow hα0.ne', mul_zero]
  · rcases lt_or_ge |τ - τ'| 1 with h1 | h1
    · have h3 : |τ - τ'| ^ (1 : ℝ) ≤ |τ - τ'| ^ α :=
        Real.rpow_le_rpow_of_exponent_ge ht h1.le hα1
      rw [Real.rpow_one] at h3
      calc |τ - τ'| ≤ |τ - τ'| ^ α := h3
        _ = 1 * |τ - τ'| ^ α := (one_mul _).symm
        _ ≤ max S 1 * |τ - τ'| ^ α :=
            mul_le_mul_of_nonneg_right hmax1 (Real.rpow_nonneg ht0 α)
    · have h2 : 1 ≤ |τ - τ'| ^ α := Real.one_le_rpow h1 hα0.le
      calc |τ - τ'| ≤ max S 1 := hle
        _ = max S 1 * 1 := (mul_one _).symm
        _ ≤ max S 1 * |τ - τ'| ^ α :=
            mul_le_mul_of_nonneg_left h2 (by linarith)

/-! ## §2 The `θ`-modulus and the continuity at `z = 0` -/

/-- The `θ`-modulus of `SG α g`: on the box it is `St1Class.hhθ`. -/
theorem SG_theta_mod {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S (Work.FTS_RegExport.RXR5.SG α g)) :
    ∃ Lθ : ℝ, 0 ≤ Lθ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
        |Work.FTS_RegExport.RXR5.SG α g z θ τ - Work.FTS_RegExport.RXR5.SG α g z θ' τ|
          ≤ Lθ * |θ - θ'| ^ α := by
  obtain ⟨Lθ, hLθ, hh⟩ := hSt1.hhθ
  refine ⟨Lθ, hLθ, ?_⟩
  intro τ hτ z hz θ hθ θ' hθ'
  rw [← SG_extG_eq hz hθ hτ, ← SG_extG_eq hz hθ' hτ]
  exact hh τ hτ z hz θ hθ θ' hθ'

/-- Continuity of the `z`-slices of `SG α g` at `z = 0`, from the quadratic vanishing of the
`St1`-class data at the origin. -/
theorem SG_cont0 {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S (Work.FTS_RegExport.RXR5.SG α g)) :
    ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousAt (fun z' => Work.FTS_RegExport.RXR5.SG α g z' θ τ) 0 := by
  obtain ⟨K, Q, hK, hQ, hquad⟩ := hSt1.quad
  intro τ hτ θ hθ
  have hquad' : ∀ z' : ℝ, 0 ≤ z' → z' ≤ 2 →
      |Work.FTS_RegExport.RXR5.SG α g z' θ τ| ≤ K * z' ^ 2 := by
    intro z' hz' hz'2
    have h1 := (hquad τ hτ θ hθ).1 z' hz' hz'2
    rwa [SG_extG_eq hz' hθ hτ] at h1
  have h0 : Work.FTS_RegExport.RXR5.SG α g 0 θ τ = 0 :=
    Work.FTS_RegExport.RXR5.SG_apply_of_nonpos le_rfl
  have hnorm : Filter.Tendsto (fun z' => ‖Work.FTS_RegExport.RXR5.SG α g z' θ τ‖)
      (𝓝 0) (𝓝 0) := by
    refine squeeze_zero' (f := fun z' : ℝ => ‖Work.FTS_RegExport.RXR5.SG α g z' θ τ‖)
      (g := fun z' : ℝ => K * z' ^ 2) ?_ ?_ ?_
    · filter_upwards with z' using norm_nonneg _
    · filter_upwards [Iic_mem_nhds (show (0 : ℝ) < 2 by norm_num)] with z' hz'2
      rcases lt_or_ge z' 0 with h | h
      · rw [Work.FTS_RegExport.RXR5.SG_apply_of_nonpos h.le, norm_zero]
        exact mul_nonneg hK (sq_nonneg z')
      · rw [Real.norm_eq_abs]
        exact hquad' z' h hz'2
    · have hcont : ContinuousAt (fun z' : ℝ => K * z' ^ 2) 0 :=
        continuousAt_const.mul (continuousAt_id.pow 2)
      have hv : (fun z' : ℝ => K * z' ^ 2) 0 = 0 := by ring
      simpa only [hv] using hcont.tendsto
  have htend : Filter.Tendsto (fun z' => Work.FTS_RegExport.RXR5.SG α g z' θ τ) (𝓝 0) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  show Filter.Tendsto (fun z' => Work.FTS_RegExport.RXR5.SG α g z' θ τ) (𝓝 0)
    (𝓝 (Work.FTS_RegExport.RXR5.SG α g 0 θ τ))
  rw [h0]
  exact htend

/-! ## §3 The sup bound -/

/-- The uniform sup bound of the sanitised family on the box: the `(b,a) = (0,0)` slot of the
interior `L^∞`–`ℋ⁴` trade-off, with the angular endpoints and `z = 0` from the exact vanishing. -/
theorem SG_sup_le_aux {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS_RegExport.RXR5.SG α g z θ τ| ≤
        10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
          * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) := by
  obtain ⟨Lτ, hLτ0, hb⟩ := Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved
    (hα := Work.FTS.Regularity.pExp_pos hα) (hα1 := Work.FTS.Regularity.pExp_le_one hα13)
    (hA := hOK.2) S hS
  have hK0 : 0 ≤ 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
      * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) :=
    mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg (C0_nonneg hα hOK) (sq_nonneg _))
  intro τ hτ z hz θ hθ
  have hvanish := hOK.1.1.vanish τ hτ.1
  rcases eq_or_lt_of_le hz with h | hz'
  · rw [← h, Work.FTS_RegExport.RXR5.SG_apply_of_nonpos le_rfl, abs_zero]
    exact hK0
  · rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz' hθ.1 hθ.2,
      Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
    by_cases hθ0 : θ = 0
    · rw [hθ0, (hvanish z hz).1, abs_zero]; exact hK0
    · by_cases hθ2 : θ = π / 2
      · rw [hθ2, (hvanish z hz).2, abs_zero]; exact hK0
      · have hθp : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
        have hθl : θ < π / 2 := lt_of_le_of_ne hθ.2 hθ2
        simpa using (hb τ hτ τ hτ 0 0 (by norm_num) z θ hz' hθp hθl).1

/-! ## §4 The `τ`-modulus -/

/-- The `τ`-modulus of `SG α g`, from the weighted `τ`-Lipschitz bound of
`Pieces.mixed_slice_tau_modulus` at the slot `(0,0)`. -/
theorem SG_tau_mod_aux {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∃ Lt : ℝ, 0 ≤ Lt ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.FTS_RegExport.RXR5.SG α g z θ τ - Work.FTS_RegExport.RXR5.SG α g z θ τ'|
          ≤ Lt * |τ - τ'| ^ α := by
  obtain ⟨L, hL, hb⟩ := Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus
    (hA := hOK.2) (hαG := Work.FTS.Regularity.pExp_pos hα)
    (hαG1 := Work.FTS.Regularity.pExp_le_one hα13) S hS
  have hmax1 : (1 : ℝ) ≤ max S 1 := le_max_right _ _
  refine ⟨L * max S 1, mul_nonneg hL (le_trans zero_le_one hmax1), ?_⟩
  intro τ hτ τ' hτ' z hz θ hθ
  have hRnn : 0 ≤ L * max S 1 * |τ - τ'| ^ α :=
    mul_nonneg (mul_nonneg hL (le_trans zero_le_one hmax1))
      (Real.rpow_nonneg (abs_nonneg _) α)
  have hvanish : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ z hz => hOK.1.1.vanish τ hτ z hz
  by_cases hθe : θ = 0 ∨ θ = π / 2
  · rw [SG_eq_zero_of_endpoint hvanish hτ hz hθe, SG_eq_zero_of_endpoint hvanish hτ' hz hθe,
      sub_self, abs_zero]
    exact hRnn
  · push Not at hθe
    obtain ⟨hθne0, hθne2⟩ := hθe
    have hθp : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθne0)
    have hθl : θ < π / 2 := lt_of_le_of_ne hθ.2 hθne2
    rcases eq_or_lt_of_le hz with h | hz'
    · rw [← h, Work.FTS_RegExport.RXR5.SG_apply_of_nonpos (le_refl (0 : ℝ)),
        Work.FTS_RegExport.RXR5.SG_apply_of_nonpos (le_refl (0 : ℝ)), sub_self, abs_zero]
      exact hRnn
    · have hSG : ∀ τ ∈ Set.Icc 0 S,
          Work.FTS_RegExport.RXR5.SG α g z θ τ = Work.FTS.Galerkin.slice g τ z θ := by
        intro τ hτ
        rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz' hθ.1 hθ.2,
          Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
        rfl
      rw [hSG τ hτ, hSG τ' hτ']
      have hb' := hb τ hτ τ' hτ' 0 0 (by norm_num) z θ hz' hθp hθl
      have hw := z_rpow_three_halves_div_sq_le_one hz'
      have hkey := abs_sub_le_max_mul_rpow (S := S) hα (by linarith) hτ hτ'
      calc |Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ|
          ≤ L * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'| := hb'
        _ ≤ L * 1 * |τ - τ'| := by
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left hw hL
        _ = L * |τ - τ'| := by ring
        _ ≤ L * (max S 1 * |τ - τ'| ^ α) := mul_le_mul_of_nonneg_left hkey hL
        _ = L * max S 1 * |τ - τ'| ^ α := by ring

/-! ## §5 The bounded `z`-derivative -/

/-- Every slice of `SG α g` has a `z`-derivative at every `z > 0`, with a uniform bound:
for `z ≥ 1` the `(b,a) = (1,0)` slot of the interior trade-off, for `z ≤ 1` the near-origin class
datum `St1Class.quad`. -/
theorem SG_zderiv_aux {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S (Work.FTS_RegExport.RXR5.SG α g)) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.FTS_RegExport.RXR5.SG α g z' θ τ) d z ∧
        |d| ≤ N := by
  obtain ⟨Lτ, hLτ0, hb⟩ := Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved
    (hα := Work.FTS.Regularity.pExp_pos hα) (hα1 := Work.FTS.Regularity.pExp_le_one hα13)
    (hA := hOK.2) S hS
  obtain ⟨K, Q, hK, hQ, hquad⟩ := hSt1.quad
  set Cw : ℝ := 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
      * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) with hCwdef
  have hCw0 : 0 ≤ Cw := by
    rw [hCwdef]
    exact mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg (C0_nonneg hα hOK) (sq_nonneg _))
  have hN0 : 0 ≤ max Cw Q := le_trans hCw0 (le_max_left _ _)
  refine ⟨max Cw Q, hN0, ?_⟩
  intro τ hτ θ hθ z hz
  have hvanish : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ z hz => hOK.1.1.vanish τ hτ z hz
  by_cases hθe : θ = 0 ∨ θ = π / 2
  · have hv : (fun z' : ℝ => Work.FTS_RegExport.RXR5.SG α g z' θ τ)
        =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact SG_eq_zero_of_endpoint hvanish hτ hz'.le hθe
    exact ⟨0, (hasDerivAt_const z 0).congr_of_eventuallyEq hv, by rw [abs_zero]; exact hN0⟩
  · push Not at hθe
    obtain ⟨hθne0, hθne2⟩ := hθe
    have hθp : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθne0)
    have hθl : θ < π / 2 := lt_of_le_of_ne hθ.2 hθne2
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
      rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθp, hθl⟩
    have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
        Work.FTS.EllipticEst.Q0 := (hOK.1.1.c4 τ hτ.1).of_le (by norm_num)
    have hd : HasDerivAt (fun z' => Work.FTS.Galerkin.slice g τ z' θ)
        (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ) z :=
      Work.FTS_RegExport.RXT.hasDerivAt_slice_fst_of_contDiffOn
        Work.FTS.EllipticEst.isOpen_Q0 h1 hmem
    have hcongr : (fun z' : ℝ => Work.FTS_RegExport.RXR5.SG α g z' θ τ)
        =ᶠ[𝓝 z] (fun z' => Work.FTS.Galerkin.slice g τ z' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz' hθ.1 hθ.2,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
      rfl
    refine ⟨Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ,
      hd.congr_of_eventuallyEq hcongr, ?_⟩
    rcases lt_or_ge z 1 with hz1 | hz1
    · -- near the origin: the quadratic class datum
      have hpz : Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ
          = Work.Spaces.pz (Work.FTS.Regularity.gSlice
              (Work.FTS.RegPkgGal.extG (Work.FTS_RegExport.RXR5.SG α g)) τ) z θ := by
        show deriv (fun z' => Work.FTS.Galerkin.slice g τ z' θ) z
          = deriv (fun z' => Work.FTS.RegPkgGal.extG (Work.FTS_RegExport.RXR5.SG α g) z' θ τ) z
        refine Filter.EventuallyEq.deriv_eq ?_
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        rw [SG_extG_eq hz'.le hθ hτ]
        rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz' hθ.1 hθ.2,
          Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
        rfl
      rw [hpz]
      calc |Work.Spaces.pz (Work.FTS.Regularity.gSlice
              (Work.FTS.RegPkgGal.extG (Work.FTS_RegExport.RXR5.SG α g)) τ) z θ|
          ≤ Q * z := (hquad τ hτ θ hθ).2 z hz.le (by linarith)
        _ ≤ Q := by nlinarith [hz, hQ]
        _ ≤ max Cw Q := le_max_right _ _
    · -- far from the origin: the `D_z g = z ∂_z g` slot
      have hmix := (hb τ hτ τ hτ 1 0 (by norm_num) z θ hz hθp hθl).1
      have hpzm : Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ
          = z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ := rfl
      have hzabs : |z| = z := abs_of_pos hz
      have heq : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
          = |Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ| / z := by
        rw [hpzm, abs_mul, hzabs]
        exact (eq_div_iff hz.ne').mpr (by ring)
      calc |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
          = |Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ| / z := heq
        _ ≤ Cw / z := div_le_div_of_nonneg_right hmix hz.le
        _ ≤ max Cw Q := by
            rw [div_le_iff₀ hz]
            calc Cw = Cw * 1 := (mul_one _).symm
              _ ≤ max Cw Q * z :=
                  mul_le_mul (le_max_left _ _) hz1 zero_le_one hN0

/-! ## §6 The `z`-modulus -/

/-- The `z`-modulus of `SG α g`: the interpolation `RXR5.zhmod_of` between the `z`-Lipschitz
bound supplied by the derivative bound `M` and the sup bound `B`. -/
theorem SG_zmod {α : ℝ} {g : Work.FTS.Galerkin.Fam} (hα : 0 < α) (hα1 : α ≤ 1)
    {S M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hderiv : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.FTS_RegExport.RXR5.SG α g z' θ τ) d z ∧ |d| ≤ M)
    (hcont0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousAt (fun z' => Work.FTS_RegExport.RXR5.SG α g z' θ τ) 0)
    (hsup : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS_RegExport.RXR5.SG α g z θ τ| ≤ B) :
    ∃ Lz : ℝ, 0 ≤ Lz ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.FTS_RegExport.RXR5.SG α g z θ τ - Work.FTS_RegExport.RXR5.SG α g z' θ τ|
          ≤ Lz * |z - z'| ^ α := by
  have hmod := Work.FTS_RegExport.RXR5.zhmod_of (α := α) (S := S) (M := M) (B := B)
    (h := fun z θ τ => Work.FTS_RegExport.RXR5.SG α g z θ τ) hα hα1 hM hB
    (fun τ hτ θ hθ x hx => (hderiv τ hτ θ hθ x hx).choose_spec.1.differentiableAt)
    (fun τ hτ θ hθ x hx => by
      obtain ⟨d, hd, hbd⟩ := hderiv τ hτ θ hθ x hx
      rw [hd.deriv]; exact hbd)
    hcont0 (fun τ hτ θ hθ z hz => hsup τ hτ z θ hz hθ)
  exact ⟨max M (2 * B), le_trans hM (le_max_left _ _),
    fun τ hτ z z' hz hz' θ hθ => hmod τ hτ θ hθ z z' hz hz'⟩

/-! ## §7 The assembly -/

theorem SG_C1Jet {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) :
    ∃ N₁ : ℝ, 0 ≤ N₁ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₁ (Work.FTS_RegExport.RXR5.SG α g) := by
  have hα1 : α ≤ 1 := by linarith
  have hSt1' : Work.FTS.RegPkgGal.St1Class α S (Work.FTS_RegExport.RXR5.SG α g) := hSt1
  set Mval : ℝ := 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
      * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) with hMvaldef
  have hMval0 : 0 ≤ Mval := by
    rw [hMvaldef]
    exact mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg (C0_nonneg hα hOK) (sq_nonneg _))
  have hsup : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS_RegExport.RXR5.SG α g z θ τ| ≤ Mval := by
    intro τ hτ z θ hz hθ
    rw [hMvaldef]
    exact SG_sup_le_aux hα hα13 hOK hS τ hτ z hz θ hθ
  obtain ⟨Md, hMd0, hderiv⟩ := SG_zderiv_aux hα hα13 hOK hS hSt1'
  have hcont0 := SG_cont0 hα hα13 hOK hS hSt1'
  obtain ⟨Lθ, hLθ0, hth⟩ := SG_theta_mod hα hα13 hOK hS hSt1'
  obtain ⟨Lt, hLt0, htau⟩ := SG_tau_mod_aux hα hα13 hOK hS
  obtain ⟨Lz, hLz0, hzmod⟩ := SG_zmod hα hα1 hMd0 hMval0 hderiv hcont0 hsup
  obtain ⟨Njet, hJet⟩ := Work.FTS.RegPkgGal.R3d.jet_of_bounded_holder
    (hα := hα) (hM := hMval0) (hLz := hLz0) (hLθ := hLθ0) (hLt := hLt0)
    (h := fun z θ τ => Work.FTS_RegExport.RXR5.SG α g z θ τ)
    hsup hzmod hth htau
  refine ⟨max Njet Md, le_trans hJet.1 (le_max_left _ _), ?_, ?_⟩
  · exact Jet_mono hJet (le_max_left _ _)
  · intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hbd⟩ := hderiv τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hbd (le_max_right _ _)⟩

end Work.FTS_RegExport.RXR5L
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.slice_contDiffOn_four =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

theorem slice_contDiffOn_four {α B : ℝ} (hα : 0 < α)
    {G : ℕ → Work.FTS.Galerkin.Fn} {f : Work.FTS.Galerkin.Fn}
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) →
      Filter.Tendsto (fun n : ℕ => G n z θ) Filter.atTop (nhds (f z θ))) :
    ContDiffOn ℝ 4 (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  classical
  -- The extraction theorem produces a subsequence converging locally uniformly, together with
  -- its `C⁴`-limit `F` on the open quadrant.
  obtain ⟨φ, hφ, F, hunif, hcdF, -⟩ :=
    Work.FTS.StrongEps.LocUnif.exists_subseq_deriv4_of_uniform_H6 (α := α) (B := B)
      hα hsm hmem hb
  -- Because the *whole* sequence converges pointwise to `f`, the limit of any subsequence is `f`.
  have hFeq : Set.EqOn (Function.uncurry f) (Function.uncurry F)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rintro ⟨z, θ⟩ hp
    simp only [Function.uncurry]
    have hsub : ({(z, θ)} : Set (ℝ × ℝ)) ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
      simpa [Set.singleton_subset_iff] using hp
    have h1 : Filter.Tendsto (fun n : ℕ => G (φ n) z θ) Filter.atTop (nhds (F z θ)) :=
      (hunif {(z, θ)} isCompact_singleton hsub).tendsto_at (Set.mem_singleton (z, θ))
    have h2 : Filter.Tendsto (fun n : ℕ => G (φ n) z θ) Filter.atTop (nhds (f z θ)) :=
      (hconv z θ hp).comp hφ.tendsto_atTop
    exact (tendsto_nhds_unique h1 h2).symm
  exact hcdF.congr hFeq

end Work.FTS_RegExport.RXT.Sys
end
