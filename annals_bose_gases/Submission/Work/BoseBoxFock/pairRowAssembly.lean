import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.pairRowNice_le_wordParts
import Submission.Work.BoseBoxFock.pinCond_real
import Submission.Work.BoseBoxFock.q2wordGeWordParts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowAssembly` — the assembly of the `Q₂` row node

`PotPairRows_exists` from the three pieces

* `pairRowS2Bound` (**PROVED**): `K1exp → K1lim` in blocks I/II,
* `stripImages_cost_le` (**PROVED**): `K1lim → pairRowNice` (the lattice images),
* `pairRowS3Bound` (**the open crux**): the limit-kernel comparison with `q2word`,

plus `cIPn_potPairRows_eq` (the exact row identity) and `pairRow_errKafz_add` (linearity of
`errKafz` in `C`).  The three `½·errKafz` slots are combined pointwise via
`C := C₂ + C₄ + C₃`, `ε₀ := min ε₀₂ (min ε₀₃ ε₀₄)`, `Nmin := max Nmin₂ Nmin₃`.

**Assembly arithmetic** (`(re a) ≤ (re b) + ‖a − b‖`, `Complex.re_le_norm`):

    (R1 + B3).re ≤ (R2 + B3).re + ½err(C₂)‖Φ‖²        (pairRowS2Bound)
                 ≤ (R3 + B3).re + ½err(C₂)‖Φ‖² + ½err(C₄)‖Φ‖²   (stripImages_cost_le)
                 ≤ q2word + ½err(C₂+C₄+C₃)‖Φ‖²      (pairRowS3Bound, pairRow_errKafz_add)

with `R1` the row at `K1exp`, `R2` at `K1lim`, `R3` at `pairRowNice`, `B3 = pairRowB3`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- `(re a) ≤ (re b) + ‖a − b‖` for complex numbers. -/
private lemma re_le_re_add_norm_sub (a b : ℂ) : a.re ≤ b.re + ‖a - b‖ := by
  have h : (a - b).re ≤ ‖a - b‖ := Complex.re_le_norm _
  rw [Complex.sub_re] at h
  linarith

theorem PotPairRows_exists_assembly (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.PotPairRows v h fc fu R J Nmin ε₀ C := by
  obtain ⟨Nmin₂, ε₀₂, C₂, hε₀₂, hC₂, hS2⟩ :=
    pairRowS2Bound v h hv hv1 hvrad hR hv_supp hav fc fu J hB3
  obtain ⟨ε₀₄, C₄, hε₀₄, hC₄, hS4⟩ :=
    stripImages_cost_le v h hv hv1 hvrad hR hv_supp hav fc fu J hB3
  obtain ⟨NminA, ε₀A, CA, hε₀A, hCA, hSA⟩ :=
    pairRowNice_le_wordParts v h hv hv1 hvrad hR hv_supp hav fc fu J hB3
  obtain ⟨ε₀B, CB, hε₀B, hCB, hSB⟩ :=
    q2wordGeWordParts v h hv hv1 hvrad hR hv_supp hav fc fu J hB3
  refine ⟨fun μ => max (Nmin₂ μ) (NminA μ), min ε₀₂ (min ε₀₄ (min ε₀A ε₀B)),
    C₂ + C₄ + (CA + CB), lt_min hε₀₂ (lt_min hε₀₄ (lt_min hε₀A hε₀B)), by linarith, ?_⟩
  intro HM hN μ hAdm hJ n Φ hn hnorm hlow hspec e hemeas hebdd hesupp heorth heint hemem
    hpin hKp hLp hθp T_NH hTNH
  have hμ : 0 < μ := hAdm.1
  have hℓ : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) :=
    pairRow_ellH_eq_sideAt (Work.BoseBox.sideAt_pos hμ hav)
  have hN₂ : ∀ μ' : ℝ, Nmin₂ μ' ≤ (HM μ').N := fun μ' => le_trans (le_max_left _ _) (hN μ')
  have hNA : NminA μ ≤ (HM μ).N := le_trans (le_max_right _ _) (hN μ)
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₀₂ μ :=
    ⟨hμ, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hAdm₄ : Work.BoseBoxFix.Adm v ε₀₄ μ :=
    ⟨hμ, le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_left _ _)), hAdm.2.2⟩
  have hAdm_A : Work.BoseBoxFix.Adm v ε₀A μ :=
    ⟨hμ, le_trans hAdm.2.1 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_left _ _))), hAdm.2.2⟩
  have hAdm_B : Work.BoseBoxFix.Adm v ε₀B μ :=
    ⟨hμ, le_trans hAdm.2.1 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_right _ _))), hAdm.2.2⟩
  -- the state, the condensate pin and the mode data at `ellH v μ`
  obtain ⟨c, hcc, hun⟩ := hpin
  have hcc' : (starRingEnd ℂ) c * c = ((ellH v μ) ^ 3)⁻¹ := by rw [hℓ]; exact hcc
  have hun' : e 0 =ᵐ[MeasureTheory.volume]
      fun x => c * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x := by
    simpa only [hℓ] using hun
  -- the θ-pin at the box side `ellH v μ`, and the **reality of `c`** it forces
  have hθp' : (∫ z : E3, (starRingEnd ℂ) (e 0 z)
        * Work.BoseK15.corpusBox.thetaFun (ellH v μ) z)
      = (((ellH v μ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [hℓ]; exact hθp
  have hcreal : (starRingEnd ℂ) c = c :=
    pinCond_conj_real (m := (HM μ).m) (ℓ := ellH v μ) (ellH_pos v μ) hcc' hun' hθp'
  have hpin0 : e 0 =ᵐ[MeasureTheory.volume] pinCond v μ c := by
    filter_upwards [hun'] with x hx
    rw [hx]; rfl
  have hesupp' : ∀ l, Function.support (e l) ⊆ boxL (ellH v μ) :=
    fun l => by simpa only [hℓ] using hesupp l
  have hpairF : ∀ (k : Lab (HM μ).N) (l : Fin (HM μ).m),
      (∫ z : E3, star (e l z) * Work.BoseK15.corpusBox.qVec (ellH v μ)
          (kmomLab (ellH v μ) (HM μ).N k) z)
        = (((ellH v μ) ^ (3 / 2 : ℝ) * (HM μ).f k l : ℝ) : ℂ) :=
    fun k l => by simpa only [hℓ] using hKp k l
  set Θ : Xn n → ℂ := boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ with hΘdef
  obtain ⟨hΘm, hΘb, hΘs, hΘperm, hΘmass⟩ :=
    boxRestrictState (Work.BoseBox.sideAt_pos hμ hav) Φ
  have hΘside : boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ = Θ := hΘdef.symm
  have hΘell : boxRestrictC (ellH v μ) Φ = Θ := by rw [hℓ]
  have hΘsell : Function.support Θ ⊆ Work.MB.boxPow n (ellH v μ) := by rw [hℓ]; exact hΘs
  -- ### the exact row identity
  have hrow := cIPn_potPairRows_eq (v := v) (μ := μ) (HM μ) hemeas hebdd hesupp' heorth
    hemem c hpin0 hpairF (HonestBoxFam v h fc fu HM μ).E Θ hΘm hΘb hΘsell
  -- ### the coefficient identifications
  have hW1 : (fun k : Lab (HM μ).N => (HonestBoxFam v h fc fu HM μ).E.W1 k)
      = k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ)) 0 (ellH v μ) (HM μ).N :=
    pairRow_W1_eq_k1cfun (fc := fc) (fu := fu) (HM := HM) hμ hav
  have hW1b : (fun k : Lab (HM μ).N =>
        (HonestBoxFam v h fc fu HM μ).E.W1 k + (HonestBoxFam v h fc fu HM μ).E.W1omega k)
      = k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ))
          (Work.BoseFixR.W1omegaFun v h (ellH v μ)) (ellH v μ) (HM μ).N :=
    pairRow_W1_add_W1omega_eq_k1cfun (fc := fc) (fu := fu) (HM := HM) hμ hav
  have hKI : K1exp v μ (HM μ).N (fun k : Lab (HM μ).N =>
        (HonestBoxFam v h fc fu HM μ).E.W1 k + (HonestBoxFam v h fc fu HM μ).E.W1omega k)
      = K1exp v μ (HM μ).N (k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ))
          (Work.BoseFixR.W1omegaFun v h (ellH v μ)) (ellH v μ) (HM μ).N) :=
    congrArg (K1exp v μ (HM μ).N) hW1b
  have hKII : K1exp v μ (HM μ).N (fun k : Lab (HM μ).N => (HonestBoxFam v h fc fu HM μ).E.W1 k)
      = K1exp v μ (HM μ).N (k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ)) 0
          (ellH v μ) (HM μ).N) :=
    congrArg (K1exp v μ (HM μ).N) hW1
  have hEell : (HonestBoxFam v h fc fu HM μ).E.ell = ellH v μ := hℓ.symm
  have hEpow : (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ)) = ((ellH v μ) ^ 3)⁻¹ := by
    rw [hEell, show (-(3 : ℝ)) = -(↑(3 : ℕ) : ℝ) from by norm_num,
      Real.rpow_neg (le_of_lt (ellH_pos v μ)), Real.rpow_natCast]
  have hEmu : (HonestBoxFam v h fc fu HM μ).E.mu = μ := rfl
  have hW1zero : (HonestBoxFam v h fc fu HM μ).E.W1 (0 : Lab (HM μ).N)
      = Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ)) 0 :=
    pairRow_E_W1_zero (v := v) (h := h) (fc := fc) (fu := fu) (HM := HM) hμ hav
  have hW1wzero : (HonestBoxFam v h fc fu HM μ).E.W1omega0
      = Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (ellH v μ)) 0 :=
    pairRow_E_W1omega_zero (v := v) (h := h) (fc := fc) (fu := fu) (HM := HM) hμ hav
  -- ### the three readings of the row
  set R1 := rowPairSubC (((ellH v μ) ^ 3)⁻¹) Θ (pinCond v μ c)
      (K1exp v μ (HM μ).N (k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ))
        (Work.BoseFixR.W1omegaFun v h (ellH v μ)) (ellH v μ) (HM μ).N))
      (K1exp v μ (HM μ).N (k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ)) 0
        (ellH v μ) (HM μ).N)) with hR1def
  set R2 := rowPairSubC (((ellH v μ) ^ 3)⁻¹) Θ (pinCond v μ c)
      (K1lim (ellH v μ) (fun x => Work.BoseFixR.W1fun v h (ellH v μ) x
        + Work.BoseFixR.W1omegaFun v h (ellH v μ) x))
      (K1lim (ellH v μ) (Work.BoseFixR.W1fun v h (ellH v μ))) with hR2def
  set R3 := rowPairSubC (((ellH v μ) ^ 3)⁻¹) Θ (pinCond v μ c)
      (pairRowNice (ellH v μ) (fun x => Work.BoseFixR.W1fun v h (ellH v μ) x
        + Work.BoseFixR.W1omegaFun v h (ellH v μ) x))
      (pairRowNice (ellH v μ) (Work.BoseFixR.W1fun v h (ellH v μ))) with hR3def
  set B3 : ℂ := pairRowB3 v h μ (HM μ).N c Θ with hB3def
  -- ### the row identity in the `(R1, B3)` shape
  have hcoef1 : ((HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
          * (HonestBoxFam v h fc fu HM μ).E.W1 (0 : Lab (HM μ).N)
        + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
          * (HonestBoxFam v h fc fu HM μ).E.W1omega0)
      = (((ellH v μ) ^ 3)⁻¹ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ)) 0
        + ((ellH v μ) ^ 3)⁻¹ * Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (ellH v μ)) 0) := by
    rw [hEpow, hW1zero, hW1wzero]
  have hcoef2 : ((HonestBoxFam v h fc fu HM μ).E.mu
        * (HonestBoxFam v h fc fu HM μ).E.W1 (0 : Lab (HM μ).N))
      = (μ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ)) 0) := by
    rw [hEmu, hW1zero]
  have hrowB : Work.BoseDict.cIPn n Θ
      (potPairRows (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f
        (HonestBoxFam v h fc fu HM μ).E Θ) = R1 + B3 :=
    hrow.trans (by
      rw [hB3def, pairRowB3, hcoef1, hcoef2, hEpow, hKI, hKII, ← hR1def]
      abel)
  -- ### the goal's left-hand side
  have hLHS : (∫ x : Xn n, star (Θ x)
        * potPairRows (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f
            (HonestBoxFam v h fc fu HM μ).E Θ x)
      = Work.BoseDict.cIPn n Θ
          (potPairRows (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f
            (HonestBoxFam v h fc fu HM μ).E Θ) := by
    rw [Work.BoseDict.cIPn]
    simp only [starRingEnd_apply]
  -- ### the four error bounds
  have hS2' := hS2 HM hN₂ μ hAdm₂ hJ n Φ hn hnorm hlow hspec c hcc'
  have hS4' := hS4 μ hAdm₄ hJ n Φ hn hnorm hlow hspec c hcc'
  have hSA' := hSA μ hAdm_A hJ n Φ hn hnorm hlow hspec (HM μ).N hNA c hcc' hcreal
  have hSB' := hSB μ hAdm_B hJ n Φ hn hnorm hlow hspec
  rw [hΘell] at hS2' hS4' hSA'
  rw [← hR1def, ← hR2def] at hS2'
  rw [← hR2def, ← hR3def] at hS4'
  rw [← hR3def, ← hB3def] at hSA'
  simp only [hℓ] at hSA' hSB'
  -- ### the arithmetic
  have hstep1 : (R1 + B3).re ≤ (R2 + B3).re
      + (1 / 2) * Work.BoseFixR.errKafz v R μ C₂ * Work.BoseBoxFix.normB v μ n Φ := by
    have h1 := re_le_re_add_norm_sub R1 R2
    rw [Complex.add_re, Complex.add_re]
    linarith [h1, hS2']
  have hstep2 : (R2 + B3).re ≤ (R3 + B3).re
      + (1 / 2) * Work.BoseFixR.errKafz v R μ C₄ * Work.BoseBoxFix.normB v μ n Φ := by
    have h1 := re_le_re_add_norm_sub R2 R3
    rw [Complex.add_re, Complex.add_re]
    linarith [h1, hS4']
  have herr3 : (1 / 2) * Work.BoseFixR.errKafz v R μ C₂ * Work.BoseBoxFix.normB v μ n Φ
      + (1 / 2) * Work.BoseFixR.errKafz v R μ C₄ * Work.BoseBoxFix.normB v μ n Φ
      + (1 / 2) * Work.BoseFixR.errKafz v R μ CA * Work.BoseBoxFix.normB v μ n Φ
      + (1 / 2) * Work.BoseFixR.errKafz v R μ CB * Work.BoseBoxFix.normB v μ n Φ
      = (1 / 2) * Work.BoseFixR.errKafz v R μ (C₂ + C₄ + (CA + CB))
          * Work.BoseBoxFix.normB v μ n Φ := by
    rw [pairRow_errKafz_add, pairRow_errKafz_add, pairRow_errKafz_add]
    ring
  rw [hLHS]
  refine le_trans (le_of_eq (congrArg Complex.re hrowB)) ?_
  linarith [hstep1, hstep2, hSA', hSB', herr3]

end Work.BoseBoxFock
