import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixedMul_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixed_le_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_le_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbAux.SlotPriceAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.summand_le_easy
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.qDzLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowMulSupAux.basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowMulSupAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
/-- The `σ`-algebra of the mismatch summand: the flat-norm gain
`σ^{-γ}(α+σ)σ^{α/5} = α σ^{-(1-α/10)} + σ^{α/10}` together with the two AM–GM bounds. -/
private lemma weight_amgm {α σ Y Z : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    σ ^ (-(Work.Spaces.gam α)) * ((α + σ) * σ ^ (α / 5)) * |Y| * |Z|
      ≤ (α ^ 2) * σ ^ (-(1 - α / 10)) * Y ^ 2 + σ ^ (-(1 - α / 10)) * Z ^ 2
        + σ ^ (-(Work.Spaces.eta)) * Y ^ 2 + σ ^ (-(Work.Spaces.gam α)) * Z ^ 2 := by
  have hgam : Work.Spaces.gam α = 1 + α / 10 := rfl
  have hgam0 : 0 < Work.Spaces.gam α := by rw [hgam]; linarith
  -- ## the multiplicative identity
  have h1 : σ ^ (-(Work.Spaces.gam α)) * σ ^ (α / 5) = σ ^ (-(1 - α / 10)) := by
    rw [← Real.rpow_add hσ0]
    congr 1
    rw [hgam]
    ring
  have h2 : σ ^ (-(1 - α / 10)) * σ = σ ^ (α / 10) := by
    calc σ ^ (-(1 - α / 10)) * σ = σ ^ (-(1 - α / 10)) * σ ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ = σ ^ (-(1 - α / 10) + 1) := (Real.rpow_add hσ0 _ _).symm
      _ = σ ^ (α / 10) := by
          congr 1
          ring
  have hid : σ ^ (-(Work.Spaces.gam α)) * ((α + σ) * σ ^ (α / 5))
      = α * σ ^ (-(1 - α / 10)) + σ ^ (α / 10) := by
    calc σ ^ (-(Work.Spaces.gam α)) * ((α + σ) * σ ^ (α / 5))
        = (σ ^ (-(Work.Spaces.gam α)) * σ ^ (α / 5)) * (α + σ) := by ring
      _ = σ ^ (-(1 - α / 10)) * (α + σ) := by rw [h1]
      _ = α * σ ^ (-(1 - α / 10)) + σ ^ (-(1 - α / 10)) * σ := by ring
      _ = α * σ ^ (-(1 - α / 10)) + σ ^ (α / 10) := by rw [h2]
  -- ## the first AM–GM
  have hb1 : α * σ ^ (-(1 - α / 10)) * |Y| * |Z|
      ≤ (α ^ 2) * σ ^ (-(1 - α / 10)) * Y ^ 2 + σ ^ (-(1 - α / 10)) * Z ^ 2 := by
    have hsos : α * |Y| * |Z| ≤ α ^ 2 * Y ^ 2 + Z ^ 2 := by
      have h := sq_nonneg (α * |Y| - |Z|)
      have hY : Y ^ 2 = |Y| ^ 2 := (sq_abs Y).symm
      have hZ : Z ^ 2 = |Z| ^ 2 := (sq_abs Z).symm
      nlinarith [h, abs_nonneg Y, abs_nonneg Z]
    have hp : 0 ≤ σ ^ (-(1 - α / 10)) := Real.rpow_nonneg hσ0.le _
    have h3 : σ ^ (-(1 - α / 10)) * (α * |Y| * |Z|)
        ≤ σ ^ (-(1 - α / 10)) * (α ^ 2 * Y ^ 2 + Z ^ 2) := mul_le_mul_of_nonneg_left hsos hp
    have e : α * σ ^ (-(1 - α / 10)) * |Y| * |Z|
        = σ ^ (-(1 - α / 10)) * (α * |Y| * |Z|) := by ring
    have e' : σ ^ (-(1 - α / 10)) * (α ^ 2 * Y ^ 2 + Z ^ 2)
        = (α ^ 2) * σ ^ (-(1 - α / 10)) * Y ^ 2 + σ ^ (-(1 - α / 10)) * Z ^ 2 := by ring
    rw [e]
    exact h3.trans (le_of_eq e')
  -- ## the second AM–GM
  have hsq1 : (σ ^ (-(Work.Spaces.eta / 2))) ^ 2 = σ ^ (-(Work.Spaces.eta)) := by
    rw [sq, ← Real.rpow_add hσ0]
    congr 1
    ring
  have hsq2 : (σ ^ (-(Work.Spaces.gam α / 2))) ^ 2 = σ ^ (-(Work.Spaces.gam α)) := by
    rw [sq, ← Real.rpow_add hσ0]
    congr 1
    ring
  have hmul : σ ^ (-(Work.Spaces.eta / 2)) * σ ^ (-(Work.Spaces.gam α / 2))
      = σ ^ (-(Work.Spaces.eta + Work.Spaces.gam α) / 2) := by
    rw [← Real.rpow_add hσ0]
    congr 1
    ring
  have hSOS : 2 * ((σ ^ (-(Work.Spaces.eta / 2)) * |Y|)
        * (σ ^ (-(Work.Spaces.gam α / 2)) * |Z|))
      ≤ (σ ^ (-(Work.Spaces.eta / 2)) * |Y|) ^ 2
        + (σ ^ (-(Work.Spaces.gam α / 2)) * |Z|) ^ 2 := by
    nlinarith [sq_nonneg (σ ^ (-(Work.Spaces.eta / 2)) * |Y|
      - σ ^ (-(Work.Spaces.gam α / 2)) * |Z|)]
  have e1 : (σ ^ (-(Work.Spaces.eta / 2)) * |Y|) ^ 2 = σ ^ (-(Work.Spaces.eta)) * Y ^ 2 := by
    rw [mul_pow, sq_abs, hsq1]
  have e2 : (σ ^ (-(Work.Spaces.gam α / 2)) * |Z|) ^ 2
      = σ ^ (-(Work.Spaces.gam α)) * Z ^ 2 := by
    rw [mul_pow, sq_abs, hsq2]
  have e3 : 2 * ((σ ^ (-(Work.Spaces.eta / 2)) * |Y|)
        * (σ ^ (-(Work.Spaces.gam α / 2)) * |Z|))
      = 2 * (σ ^ (-(Work.Spaces.eta + Work.Spaces.gam α) / 2) * (|Y| * |Z|)) := by
    rw [← hmul]
    ring
  have hmain : 2 * (σ ^ (-(Work.Spaces.eta + Work.Spaces.gam α) / 2) * (|Y| * |Z|))
      ≤ σ ^ (-(Work.Spaces.eta)) * Y ^ 2 + σ ^ (-(Work.Spaces.gam α)) * Z ^ 2 := by
    rw [← e3, ← e1, ← e2]
    exact hSOS
  have hE : 0 ≤ (Work.Spaces.eta + Work.Spaces.gam α) / 2 := by
    linarith [Work.Spaces.eta_pos, hgam0]
  have hpos : 0 < σ ^ ((Work.Spaces.eta + Work.Spaces.gam α) / 2) :=
    Real.rpow_pos_of_pos hσ0 _
  have hle1 : σ ^ ((Work.Spaces.eta + Work.Spaces.gam α) / 2) ≤ 1 :=
    Real.rpow_le_one hσ0.le hσ1 hE
  have hone : 1 ≤ σ ^ (-(Work.Spaces.eta + Work.Spaces.gam α) / 2) := by
    rw [show -(Work.Spaces.eta + Work.Spaces.gam α) / 2
        = -((Work.Spaces.eta + Work.Spaces.gam α) / 2) by ring, Real.rpow_neg hσ0.le]
    exact (one_le_inv₀ hpos).mpr hle1
  have hle : σ ^ (α / 10) ≤ σ ^ (-(Work.Spaces.eta + Work.Spaces.gam α) / 2) := by
    have ha : σ ^ (α / 10) ≤ 1 := Real.rpow_le_one hσ0.le hσ1 (by linarith)
    linarith [hone]
  have hYZ : 0 ≤ |Y| * |Z| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hstep : σ ^ (α / 10) * (|Y| * |Z|)
      ≤ σ ^ (-(Work.Spaces.eta + Work.Spaces.gam α) / 2) * (|Y| * |Z|) :=
    mul_le_mul_of_nonneg_right hle hYZ
  have hA0 : 0 ≤ σ ^ (α / 10) * (|Y| * |Z|) :=
    mul_nonneg (Real.rpow_nonneg hσ0.le _) hYZ
  have hb2 : σ ^ (α / 10) * |Y| * |Z|
      ≤ σ ^ (-(Work.Spaces.eta)) * Y ^ 2 + σ ^ (-(Work.Spaces.gam α)) * Z ^ 2 := by
    have e : σ ^ (α / 10) * |Y| * |Z| = σ ^ (α / 10) * (|Y| * |Z|) := by ring
    rw [e]
    linarith [hmain, hstep, hA0]
  -- ## assembly
  rw [hid]
  have e3' : (α * σ ^ (-(1 - α / 10)) + σ ^ (α / 10)) * |Y| * |Z|
      = α * σ ^ (-(1 - α / 10)) * |Y| * |Z| + σ ^ (α / 10) * |Y| * |Z| := by ring
  rw [e3']
  linarith [hb1, hb2]

/-- **The mismatch Leibniz summand.**  All angular derivatives on the coefficient slot
(`j = a ≥ 1`) with `ρ = leafGam α`: the flat-norm gain `(α+σ)σ^{α/5}` turns the `γ`-weight into
`α σ^{-(1-α/10)} + σ^{α/10}`; the first piece is paid by the two-weight angular Hardy `qDzLe`
(whose `α^{-2}` is cancelled by the `α^2` of the AM–GM) and the second by the level-six slots
of `f`. -/
lemma mismatchSummand' : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : ℝ → ℝ → ℝ) (KA : ℝ) (i a b : ℕ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ KA →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      1 ≤ a → i ≤ b → a + b ≤ 6 →
      Integrable (fun p : ℝ × ℝ =>
          Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed i a A p.1 p.2
            * Work.Spaces.DzIter (b - i) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2) mu ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed i a A p.1 p.2
            * Work.Spaces.DzIter (b - i) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2 ∂mu|
        ≤ C * KA * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨Cq, hCqpos, hqdz⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.qDzLe
  refine ⟨1000 * (Cq + 3) + 1, by positivity, ?_⟩
  intro α hα A f KA i a b hA hAm hAb hfsm hfm ha1 hib hab
  obtain ⟨hα0, hα1⟩ := hα
  have hαmem : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
  have hA6 : ContDiffOn ℝ 6 (Function.uncurry A) Work.FTS.EllipticEst.Q0 := hA.forall 6
  have hKA0 : 0 ≤ KA := le_trans (Work.Spaces.WlInf_nonneg α 6 A hAm) hAb
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hb5 : b - i ≤ 5 := by omega
  -- ## the four majorant pieces
  set F : ℝ × ℝ → ℝ := fun p => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed i a A p.1 p.2 * Work.Spaces.DzIter (b - i) f p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2 with hFdef
  set M1 : ℝ × ℝ → ℝ := fun p => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(1 - α / 10))
      * (Work.Spaces.DzIter (b - i) f p.1 p.2) ^ 2 with hM1def
  set M2 : ℝ × ℝ → ℝ := fun p => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(1 - α / 10))
      * (Work.Spaces.mixed b a f p.1 p.2) ^ 2 with hM2def
  set M3 : ℝ × ℝ → ℝ := fun p => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))
      * (Work.Spaces.DzIter (b - i) f p.1 p.2) ^ 2 with hM3def
  set M4 : ℝ × ℝ → ℝ := fun p => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed b a f p.1 p.2) ^ 2 with hM4def
  -- ## integrability and bounds of the four pieces
  obtain ⟨hM1int, hM1bd⟩ := hqdz α hαmem f (b - i) hfsm hfm hb5
  have hM1i : Integrable M1 mu := by
    rw [hM1def]; exact hM1int
  have hM1b : ∫ p, M1 p ∂mu ≤ Cq * α ^ (-(2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f) := by
    simpa only [hM1def] using hM1bd
  have hcontS : ∀ (q : ℝ) (g : ℝ × ℝ → ℝ),
      ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-q) * g p) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro q g hg
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-q)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have h := Work.FTS.TransportS.SlotT2.continuousOn_canonW q
      simpa only [Work.FTS.TransportS.SlotT2.canonW] using h
    exact h1.mul hg
  have hM2c : ContinuousOn M2 (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h := hcontS (1 - α / 10)
      (fun p : ℝ × ℝ => (Work.Spaces.mixed b a f p.1 p.2) ^ 2)
      ((hfsm.mixed b a).continuousOn.pow 2)
    simpa only [hM2def] using h
  have hM2p : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ‖M2 (z, θ)‖ ≤ (1 : ℝ) * Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hz hθ1 hθ2
    have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ1, hθ2⟩
    have h1 := Work.FTS.TransportS.T2Sup.canonW_mixed_slot_le_gen hα0 6
      (q := 1 - α / 10) (by linarith) (by rw [Work.Spaces.gam]; linarith) f (z := z) hθ b a
      ha1 (by omega)
    have h2 : M2 (z, θ) = Work.FTS.TransportS.SlotT2.canonW (1 - α / 10) z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2 := by
      simp only [hM2def, Work.FTS.TransportS.SlotT2.canonW]
    have hsin₀ : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.pi_pos])
    have hnn : 0 ≤ M2 (z, θ) := by
      rw [hM2def]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin₀ _)) (sq_nonneg _)
    rw [Real.norm_of_nonneg hnn, h2, one_mul]
    exact h1
  have hM2i : Integrable M2 mu :=
    (Work.FTS.StrongPersist.N6TP.summand_ae_package hfsm hfm hM2c hM2p).1
  have hM2b : ∫ p, M2 p ∂mu ≤ Work.Spaces.HkSq α 6 f := by
    obtain ⟨hHkint, hHkval⟩ := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (k := 6) hfsm hfm
    have hmono : ∫ p, M2 p ∂mu ≤ ∫ p, Work.Spaces.HkIntegrand α 6 f p.1 p.2 ∂mu := by
      refine integral_mono_ae hM2i hHkint ?_
      refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ1 hθ2 => ?_)
      have h := hM2p z θ hz hθ1 hθ2
      have hle := le_trans (le_abs_self (M2 (z, θ))) h
      simpa using hle
    rw [hHkval] at hmono
    exact hmono
  have hM3c : ContinuousOn M3 (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h := hcontS Work.Spaces.eta
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter (b - i) f p.1 p.2) ^ 2)
      ((hfsm.DzIter (b - i)).continuousOn.pow 2)
    simpa only [hM3def] using h
  have hM3p : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ‖M3 (z, θ)‖ ≤ (1 : ℝ) * Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hz hθ1 hθ2
    have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ1, hθ2⟩
    have h1 := Work.FTS.TransportS.T2Sup.canonW_z_slot_le_gen (α := α) 6
      (q := Work.Spaces.eta) Work.Spaces.eta_pos.le le_rfl f (z := z) hθ (b - i) (by omega)
    have h2 : M3 (z, θ) = Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.DzIter (b - i) f z θ) ^ 2 := by
      simp only [hM3def, Work.FTS.TransportS.SlotT2.canonW]
    have hsin₀ : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.pi_pos])
    have hnn : 0 ≤ M3 (z, θ) := by
      rw [hM3def]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin₀ _)) (sq_nonneg _)
    rw [Real.norm_of_nonneg hnn, h2, one_mul]
    exact h1
  have hM3i : Integrable M3 mu :=
    (Work.FTS.StrongPersist.N6TP.summand_ae_package hfsm hfm hM3c hM3p).1
  have hM3b : ∫ p, M3 p ∂mu ≤ Work.Spaces.HkSq α 6 f := by
    obtain ⟨hHkint, hHkval⟩ := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (k := 6) hfsm hfm
    have hmono : ∫ p, M3 p ∂mu ≤ ∫ p, Work.Spaces.HkIntegrand α 6 f p.1 p.2 ∂mu := by
      refine integral_mono_ae hM3i hHkint ?_
      refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ1 hθ2 => ?_)
      have h := hM3p z θ hz hθ1 hθ2
      have hle := le_trans (le_abs_self (M3 (z, θ))) h
      simpa using hle
    rw [hHkval] at hmono
    exact hmono
  have hM4c : ContinuousOn M4 (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h := hcontS (Work.Spaces.gam α)
      (fun p : ℝ × ℝ => (Work.Spaces.mixed b a f p.1 p.2) ^ 2)
      ((hfsm.mixed b a).continuousOn.pow 2)
    simpa only [hM4def] using h
  have hM4p : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ‖M4 (z, θ)‖ ≤ (1 : ℝ) * Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hz hθ1 hθ2
    have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ1, hθ2⟩
    have hgam0 : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
    have h1 := Work.FTS.TransportS.T2Sup.canonW_mixed_slot_le_gen hα0 6
      (q := Work.Spaces.gam α) hgam0 le_rfl f (z := z) hθ b a ha1 (by omega)
    have h2 : M4 (z, θ) = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2 := by
      simp only [hM4def, Work.FTS.TransportS.SlotT2.canonW]
    have hsin₀ : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.pi_pos])
    have hnn : 0 ≤ M4 (z, θ) := by
      rw [hM4def]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin₀ _)) (sq_nonneg _)
    rw [Real.norm_of_nonneg hnn, h2, one_mul]
    exact h1
  have hM4i : Integrable M4 mu :=
    (Work.FTS.StrongPersist.N6TP.summand_ae_package hfsm hfm hM4c hM4p).1
  have hM4b : ∫ p, M4 p ∂mu ≤ Work.Spaces.HkSq α 6 f := by
    obtain ⟨hHkint, hHkval⟩ := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (k := 6) hfsm hfm
    have hmono : ∫ p, M4 p ∂mu ≤ ∫ p, Work.Spaces.HkIntegrand α 6 f p.1 p.2 ∂mu := by
      refine integral_mono_ae hM4i hHkint ?_
      refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ1 hθ2 => ?_)
      have h := hM4p z θ hz hθ1 hθ2
      have hle := le_trans (le_abs_self (M4 (z, θ))) h
      simpa using hle
    rw [hHkval] at hmono
    exact hmono
  -- ## the pointwise bound of `F`
  have hFbd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ‖F (z, θ)‖ ≤ 1000 * KA * ((α ^ 2) * M1 (z, θ) + M2 (z, θ) + M3 (z, θ) + M4 (z, θ)) := by
    intro z θ hz hθ1 hθ2
    have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ1, hθ2⟩
    have hσ0 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hgain : (0 : ℝ) ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hσ0.le _)
    have hAslot := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixed_le_WlInf6_cd6
      (α := α) hα0 (f := A) hA6 hAm (a := a) (b := i) ha1 (by omega) (z := z) hz hθ
    have hAslotBd : |Work.Spaces.mixed i a A z θ|
        ≤ 1000 * KA * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      calc |Work.Spaces.mixed i a A z θ|
          ≤ 1000 * (Work.Spaces.WlInf α 6 A
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := hAslot
        _ ≤ 1000 * (KA * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAb hgain) (by norm_num)
        _ = 1000 * KA * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
    have ham := weight_amgm (α := α) (σ := Real.sin (2 * θ))
      (Y := Work.Spaces.DzIter (b - i) f z θ) (Z := Work.Spaces.mixed b a f z θ)
      hα0 hα1 hσ0 hσ1
    have hFval : F (z, θ) = Work.FTS.TransportS.leafGam α z θ
        * Work.Spaces.mixed i a A z θ * Work.Spaces.DzIter (b - i) f z θ
        * Work.Spaces.mixed b a f z θ := by simp only [hFdef]
    rw [hFval, Real.norm_eq_abs]
    have hsig0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hσ0.le _
    have hw2 : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hY0 : (0 : ℝ) ≤ |Work.Spaces.DzIter (b - i) f z θ| := abs_nonneg _
    have hZ0 : (0 : ℝ) ≤ |Work.Spaces.mixed b a f z θ| := abs_nonneg _
    have hleaf : Work.FTS.TransportS.leafGam α z θ
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := rfl
    rw [hleaf, abs_mul, abs_mul, abs_mul, abs_of_nonneg (mul_nonneg hw2 hsig0)]
    have step1 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.mixed i a A z θ| * |Work.Spaces.DzIter (b - i) f z θ|
          * |Work.Spaces.mixed b a f z θ|
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (1000 * KA * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
          * |Work.Spaces.DzIter (b - i) f z θ| * |Work.Spaces.mixed b a f z θ| := by
      have h1 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * |Work.Spaces.mixed i a A z θ|
          ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (1000 * KA * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_left hAslotBd (mul_nonneg hw2 hsig0)
      calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * |Work.Spaces.mixed i a A z θ| * |Work.Spaces.DzIter (b - i) f z θ|
            * |Work.Spaces.mixed b a f z θ|
          = ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * |Work.Spaces.mixed i a A z θ|) * |Work.Spaces.DzIter (b - i) f z θ|
              * |Work.Spaces.mixed b a f z θ| := by ring
        _ ≤ ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (1000 * KA * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
              * |Work.Spaces.DzIter (b - i) f z θ| * |Work.Spaces.mixed b a f z θ| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hY0) hZ0
    refine step1.trans ?_
    have step2 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (1000 * KA * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
          * |Work.Spaces.DzIter (b - i) f z θ| * |Work.Spaces.mixed b a f z θ|
        = 1000 * KA * ((Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            * |Work.Spaces.DzIter (b - i) f z θ| * |Work.Spaces.mixed b a f z θ|)) := by ring
    rw [step2]
    have h20 : (0 : ℝ) ≤ 1000 * KA := by positivity
    refine mul_le_mul_of_nonneg_left ?_ h20
    have hcore : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
          * |Work.Spaces.DzIter (b - i) f z θ| * |Work.Spaces.mixed b a f z θ|
        ≤ (α ^ 2) * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
            * (Work.Spaces.DzIter (b - i) f z θ) ^ 2
          + (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.mixed b a f z θ) ^ 2
          + (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.DzIter (b - i) f z θ) ^ 2
          + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed b a f z θ) ^ 2 := ham
    calc (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            * |Work.Spaces.DzIter (b - i) f z θ| * |Work.Spaces.mixed b a f z θ|)
        ≤ (Work.Spaces.w z) ^ 2 * ((α ^ 2) * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
              * (Work.Spaces.DzIter (b - i) f z θ) ^ 2
            + (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.mixed b a f z θ) ^ 2
            + (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              * (Work.Spaces.DzIter (b - i) f z θ) ^ 2
            + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed b a f z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hcore hw2
      _ = (α ^ 2) * M1 (z, θ) + M2 (z, θ) + M3 (z, θ) + M4 (z, θ) := by
          simp only [hM1def, hM2def, hM3def, hM4def]
          ring
  -- ## integrability of the majorant and of `F`
  have ha : Integrable (fun p : ℝ × ℝ => (α ^ 2) * M1 p) mu := hM1i.const_mul _
  have hb : Integrable (fun p : ℝ × ℝ => (α ^ 2) * M1 p + M2 p) mu := ha.add hM2i
  have hc : Integrable (fun p : ℝ × ℝ => (α ^ 2) * M1 p + M2 p + M3 p) mu := hb.add hM3i
  have hMsum : Integrable (fun p : ℝ × ℝ => (α ^ 2) * M1 p + M2 p + M3 p + M4 p) mu :=
    hc.add hM4i
  have hcontF : ContinuousOn F (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have h := Work.FTS.TransportS.SlotT2.continuousOn_canonW (Work.Spaces.gam α)
      simpa only [Work.FTS.TransportS.leafGam, Work.FTS.TransportS.SlotT2.canonW] using h
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed i a A p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hA.mixed i a).continuousOn
    have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter (b - i) f p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hfsm.DzIter (b - i)).continuousOn
    have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hfsm.mixed b a).continuousOn
    have h := ((h1.mul h2).mul h3).mul h4
    have hFfun : F = ((fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
        * (fun p : ℝ × ℝ => Work.Spaces.mixed i a A p.1 p.2)
        * (fun p : ℝ × ℝ => Work.Spaces.DzIter (b - i) f p.1 p.2)
        * (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2)) := by
      funext p
      simp only [hFdef, Pi.mul_apply]
    rw [hFfun]
    exact h
  have haesm : AEStronglyMeasurable F mu := Work.Spaces.aesm_of_continuousOn_Qd F hcontF
  have hdom : ∀ᵐ p ∂mu, ‖F p‖ ≤ 1000 * KA * ((α ^ 2) * M1 p + M2 p + M3 p + M4 p) :=
    Work.FTS.TransportS.ae_of_forall_Qd hFbd
  have hMaj : Integrable (fun p : ℝ × ℝ =>
      1000 * KA * ((α ^ 2) * M1 p + M2 p + M3 p + M4 p)) mu := hMsum.const_mul _
  have hFint : Integrable F mu := hMaj.mono' haesm hdom
  -- ## the value of the majorant integral
  have e1 : ∫ p, ((α ^ 2) * M1 p + M2 p + M3 p + M4 p) ∂mu
      = ∫ p, ((α ^ 2) * M1 p + M2 p + M3 p) ∂mu + ∫ p, M4 p ∂mu :=
    integral_add (f := fun p : ℝ × ℝ => (α ^ 2) * M1 p + M2 p + M3 p)
      (g := fun p : ℝ × ℝ => M4 p) hc hM4i
  have e2 : ∫ p, ((α ^ 2) * M1 p + M2 p + M3 p) ∂mu
      = ∫ p, ((α ^ 2) * M1 p + M2 p) ∂mu + ∫ p, M3 p ∂mu :=
    integral_add (f := fun p : ℝ × ℝ => (α ^ 2) * M1 p + M2 p)
      (g := fun p : ℝ × ℝ => M3 p) hb hM3i
  have e3 : ∫ p, ((α ^ 2) * M1 p + M2 p) ∂mu
      = ∫ p, ((α ^ 2) * M1 p) ∂mu + ∫ p, M2 p ∂mu :=
    integral_add (f := fun p : ℝ × ℝ => (α ^ 2) * M1 p) (g := fun p : ℝ × ℝ => M2 p) ha hM2i
  have e4 : ∫ p, ((α ^ 2) * M1 p) ∂mu = (α ^ 2) * ∫ p, M1 p ∂mu :=
    integral_const_mul _ _
  have hval : ∫ p, ((α ^ 2) * M1 p + M2 p + M3 p + M4 p) ∂mu
      = (α ^ 2) * (∫ p, M1 p ∂mu) + (∫ p, M2 p ∂mu) + (∫ p, M3 p ∂mu)
        + (∫ p, M4 p ∂mu) := by
    rw [e1, e2, e3, e4]
  -- ## the arithmetic
  have hαinv : α ^ 2 * α ^ (-(2 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast α 2, ← Real.rpow_add hα0,
      show ((2 : ℕ) : ℝ) + -(2 : ℝ) = 0 by norm_num, Real.rpow_zero]
  have hfin : (α ^ 2) * (∫ p, M1 p ∂mu) + (∫ p, M2 p ∂mu) + (∫ p, M3 p ∂mu)
        + (∫ p, M4 p ∂mu) ≤ (Cq + 3) * (1 + Work.Spaces.HkSq α 6 f) := by
    have h1 : (α ^ 2) * (∫ p, M1 p ∂mu)
        ≤ (α ^ 2) * (Cq * α ^ (-(2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f)) :=
      mul_le_mul_of_nonneg_left hM1b (by positivity)
    have h1' : (α ^ 2) * (Cq * α ^ (-(2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f))
        = Cq * (1 + Work.Spaces.HkSq α 6 f) := by
      rw [show (α ^ 2) * (Cq * α ^ (-(2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f))
          = (α ^ 2 * α ^ (-(2 : ℝ))) * (Cq * (1 + Work.Spaces.HkSq α 6 f)) by ring, hαinv,
        one_mul]
    have h2 : ∫ p, M2 p ∂mu ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith [hM2b]
    have h3 : ∫ p, M3 p ∂mu ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith [hM3b]
    have h4 : ∫ p, M4 p ∂mu ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith [hM4b]
    linarith [h1, h1', h2, h3, h4]
  refine ⟨?_, ?_⟩
  · simpa only [hFdef] using hFint
  · calc |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed i a A p.1 p.2
            * Work.Spaces.DzIter (b - i) f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2 ∂mu|
        = |∫ p, F p ∂mu| := by rw [hFdef]
      _ ≤ ∫ p, ‖F p‖ ∂mu := abs_integral_le_integral_abs
      _ ≤ ∫ p, 1000 * KA * ((α ^ 2) * M1 p + M2 p + M3 p + M4 p) ∂mu :=
          integral_mono_ae hFint.norm hMaj hdom
      _ = 1000 * KA * (∫ p, ((α ^ 2) * M1 p + M2 p + M3 p + M4 p) ∂mu) :=
          integral_const_mul _ _
      _ = 1000 * KA * ((α ^ 2) * (∫ p, M1 p ∂mu) + (∫ p, M2 p ∂mu) + (∫ p, M3 p ∂mu)
            + (∫ p, M4 p ∂mu)) := by rw [hval]
      _ ≤ 1000 * KA * ((Cq + 3) * (1 + Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul_of_nonneg_left hfin (by positivity)
      _ ≤ (1000 * (Cq + 3) + 1) * KA * (1 + Work.Spaces.HkSq α 6 f) := by
          nlinarith [hKA0, hSq0]


end Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowMulSupAux
