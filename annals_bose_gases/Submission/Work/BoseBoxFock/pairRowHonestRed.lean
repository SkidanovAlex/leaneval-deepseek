import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.K1exp_sub_K1lim_pairing_dirB
import Submission.Work.BoseBoxFock.potPairRows_kernelExpanded
import Submission.Work.BoseBoxFock.rowSum_roots_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowHonestRed` — the `(S2)` reduction of the `Q₂` row, step 1

The honest instantiation of the row identity `potPairRows_kernelExpanded`: the row's quadratic form
at the honest data is the block-`I/II` part `rowPairSubC` (with the truncated `K1exp` kernels) plus
the `block III` part, and the honest weights are the `k1cfun` data of the pairing bound.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- `ellH v μ = sideAt μ (a v)` at admissible `μ`. -/
theorem pairRow_ellH_eq_sideAt {v : ℝ³ → ℝ} {μ : ℝ}
    (h : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) :
    ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
  unfold ellH
  rw [if_pos h]

theorem pairRow_W1_eq_k1cfun {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    (fun k : Lab (HM μ).N => (HonestBoxFam v h fc fu HM μ).E.W1 k)
      = k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ)) 0 (ellH v μ) (HM μ).N := by
  have hℓ : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) :=
    pairRow_ellH_eq_sideAt (Work.BoseBox.sideAt_pos hμ hav)
  funext k
  simp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs, k1cfun]
  rw [← hℓ]
  simp only [Work.BoseB4.boxFockData, Work.BoseB4.b7FockDataBox, Work.BoseFixR.chat]
  simp [Submission.BoseGases.kinFT]

theorem pairRow_W1_add_W1omega_eq_k1cfun {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    (fun k : Lab (HM μ).N =>
        (HonestBoxFam v h fc fu HM μ).E.W1 k + (HonestBoxFam v h fc fu HM μ).E.W1omega k)
      = k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ))
          (Work.BoseFixR.W1omegaFun v h (ellH v μ)) (ellH v μ) (HM μ).N := by
  have hℓ : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) :=
    pairRow_ellH_eq_sideAt (Work.BoseBox.sideAt_pos hμ hav)
  funext k
  simp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs, k1cfun]
  rw [← hℓ]
  simp only [Work.BoseB4.boxFockData, Work.BoseB4.b7FockDataBox, Work.BoseFixR.chat]

/-- Pointwise form of `pairRow_W1_eq_k1cfun`. -/
theorem pairRow_W1_apply {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    (k : Lab (HM μ).N) :
    (HonestBoxFam v h fc fu HM μ).E.W1 k
      = k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ)) 0 (ellH v μ) (HM μ).N k :=
  congrFun (pairRow_W1_eq_k1cfun (v := v) (h := h) (fc := fc) (fu := fu) (HM := HM)
    hμ hav) k

/-- `E.W1 0 = Ŵ₁(0)`. -/
theorem pairRow_E_W1_zero {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    (HonestBoxFam v h fc fu HM μ).E.W1 0
      = Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ)) 0 := by
  refine (pairRow_W1_apply (v := v) (h := h) (fc := fc) (fu := fu) (HM := HM) hμ hav
    (0 : Lab (HM μ).N)).trans ?_
  simp only [k1cfun, kmomLab_zero, uvCut, norm_zero, zero_div, fu.one 0 zero_le_one, one_mul]
  simp [Work.BoseFixR.chat, Submission.BoseGases.kinFT]

/-- `E.W1omega 0 = Ŵ₁ω(0)`. -/
theorem pairRow_E_W1omega_zero {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    (HonestBoxFam v h fc fu HM μ).E.W1omega0
      = Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (ellH v μ)) 0 := by
  have hℓ : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) :=
    pairRow_ellH_eq_sideAt (Work.BoseBox.sideAt_pos hμ hav)
  simp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs]
  rw [← hℓ]

/-! ## 2. The row identity at the honest data

`potPairRows_kernelExpanded` writes the row as the block-`I/II` part `rowPairSubC` (with the
truncated `K1exp` kernels) plus the two `block III` sums; the identity below is definitional. -/

/-- **The `Q₂` row is `rowPairSubC` plus its `block III`.** -/
theorem cIPn_potPairRows_eq {n : ℕ} {v : E3 → ℝ} {μ : ℝ} (HM : HonestModes v μ)
    {e : Fin HM.m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l)
      ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ))
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (c : ℂ) (hpin0 : e 0 =ᵐ[MeasureTheory.volume] pinCond v μ c)
    (hpairF : ∀ (k : Lab HM.N) (l : Fin HM.m),
      (∫ z : E3, star (e l z) * Work.BoseK15.corpusBox.qVec (ellH v μ)
          (kmomLab (ellH v μ) HM.N k) z)
        = (((ellH v μ) ^ (3 / 2 : ℝ) * HM.f k l : ℝ) : ℂ))
    (E : Work.BoseB7.Q3Env (Lab HM.N)) (Theta : Xn n → ℂ)
    (hΘm : Measurable Theta) (hΘb : ∃ C : ℝ, ∀ x, ‖Theta x‖ ≤ C)
    (hΘs : Function.support Theta ⊆ Work.MB.boxPow n (ellH v μ)) :
    Work.BoseDict.cIPn n Theta
        (potPairRows (fun T => Work.BoseDict.boxSlotSum e T) HM.f E Theta)
      = rowPairSubC (E.ell ^ (-(3 : ℝ))) Theta (pinCond v μ c)
          (K1exp v μ HM.N (fun k => E.W1 k + E.W1omega k))
          (K1exp v μ HM.N E.W1)
        + (E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
              (∑ p ∈ Submission.BoseGases.pairSet n,
                ∫ x : Xn n, ∫ y : E3, ∫ u : E3,
                  star (Theta x) * pinCond v μ c (x p.1)
                    * star (pinCond v μ c y)
                    * K1exp v μ HM.N (fun _ : Lab HM.N => (1 : ℝ)) (x p.2) u
                    * Theta (Function.update (Function.update x p.1 y) p.2 u))
          - (E.mu * E.W1 0) •
              (∑ j : Fin n,
                ∫ x : Xn n, ∫ y : E3,
                  star (Theta x)
                    * K1exp v μ HM.N (fun _ : Lab HM.N => (1 : ℝ)) (x j) y
                    * Theta (Function.update x j y)) := by
  rw [potPairRows_kernelExpanded HM hmeas hbdd hsupp horth hMemLp c hpin0 hpairF E Theta
    hΘm hΘb hΘs]
  simp only [rowPairSubC, rowSum13, rowShape13, rowSum21, rowShape21, rowSum23, rowShape23,
    starRingEnd_apply]
  abel

end Work.BoseBoxFock
