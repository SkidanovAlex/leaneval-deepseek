import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PCFU.lhs_kernelForm
import Submission.Work.BoseBoxFock.PCFU.pairSum_MiddleV_star_MiddleU
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.lowBandCondSumAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.PCFU.LhsTwoRe` — the `Re I₂ = Re I₁` reduction at the honest data

The node's left-hand side is the cubic row `cIPn Θ (potCubic … Θ)` at the honest environment and at
`Θ = boxRestrictC ℓ Φ` (`ℓ = sideAt μ (a v)`).  `PCFU.lhs_kernelForm` (PROVED) identifies it with
`ℓ⁻³(Σ_p (I₁(p) + I₂(p))).re`, where `I₁` is the `MiddleU` (annihilation-slot) pair integral and
`I₂` the `MiddleV` (creation-slot) pair integral.  `PCFU.pairSum_MiddleV_star_MiddleU` (PROVED)
gives `Σ_p I₂(p) = star (Σ_p I₁(p))`, since the two atoms of `potCubic` are conjugate as `cIPn`
pairings.  Hence

    LHS = 2·ℓ⁻³·(Σ_{p∈pairSet n} I₁(p)).re ,

which is the **interface** of the whole cubic dictionary: only the four `Ch`-channels of `MiddleU`
(already in canonical form) have to be matched against `q3lowWord`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Work.BoseB4 Work.BoseBoxFock

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

theorem lhs_eq_two_re_pairSum (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ)
    (hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (c : ℂ) (e : Fin (HM μ).m → E3 → ℂ)
    (hemeas : ∀ l, Measurable (e l))
    (hebdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hesupp : ∀ l, Function.support (e l)
      ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (heorth : ∀ l l', (∫ z : E3, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hemem : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hpin0 : e 0 =ᵐ[MeasureTheory.volume] fun x =>
      c * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x)
    (hpairF : ∀ (k : Lab (HM μ).N) (l : Fin (HM μ).m),
      (∫ z : E3, star (e l z)
          * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (kmomLab (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N k) z)
        = (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ (3 / 2 : ℝ)
            * (HM μ).f k l : ℝ) : ℂ))
    (hpairG : ∀ (s : Lab (HM μ).N) (l : Fin (HM μ).m), s ≠ 0 →
      (∫ z : E3, star (e l z)
          * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (kmomLab (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N s) z)
        = (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ (3 / 2 : ℝ)
            * (HM μ).g s l : ℝ) : ℂ))
    (T_NH : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ))
    (hTNH : (HonestBoxFam v h fc fu HM μ).T.NH = Work.BoseB4.dGamma (HM μ).m T_NH) :
    (∫ x : Submission.BoseGases.X n,
        star (boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ x)
          * potCubic (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f (HM μ).g
              (Finset.univ : Finset (Lab (HM μ).N))
              (HonestBoxFam v h fc fu HM μ).E
              (boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ) x).re
      = 2 * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ (-3 : ℤ))
        * (∑ p ∈ Submission.BoseGases.pairSet n,
            (∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
                (starRingEnd ℂ) (boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ x)
                  * pinCond v μ c (x p.1)
                  * MiddleU v h fc fu μ (HM μ).N (x p.2) y u
                  * boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ
                      (Function.update (Function.update x p.1 y) p.2 u))).re := by
  classical
  -- the box side and `ellH` agree
  have hℓeq : ellH v μ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rw [ellH, if_pos hside]
  have hℓpos : 0 < ellH v μ := by rw [hℓeq]; exact hside
  -- the three regularity facts for `Θ = boxRestrictC ℓ Φ`
  have hθc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hΘm : Measurable (boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ) :=
    boxRestrictC_measurable _ hθc
  have hΘb : ∃ C : ℝ, ∀ x, ‖boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ x‖ ≤ C :=
    (boxRestrictC_norm_bound hside hθc).imp (fun C hC => hC.2)
  have hΘs : Function.support (boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ)
      ⊆ Work.MB.boxPow n (ellH v μ) := by
    rw [Work.BoseBoxFock.PotCubicLowBandAux.boxPow_eq_abox (n := n) hℓpos, hℓeq]
    exact boxRestrictC_support_subset _ _
  -- the `Re I₂ = Re I₁` identity
  have hconj := pairSum_MiddleV_star_MiddleU (v := v) (h := h) (fc := fc) (fu := fu)
    (μ := μ) (N := (HM μ).N) (c := c)
    (Θ := boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ) hΘm hΘb hΘs
  -- the kernel-form reduction
  have hk := lhs_kernelForm v h fc fu HM μ hside n Φ c e hemeas hebdd hesupp heorth hemem hpin0
    hpairF hpairG T_NH hTNH
  rw [hk]
  simp only [starRingEnd_apply] at hconj ⊢
  rw [← Complex.re_sum, Finset.sum_add_distrib, Complex.add_re, hconj, Complex.star_def,
    Complex.conj_re]
  ring

end Work.BoseBoxFock.PCFU
