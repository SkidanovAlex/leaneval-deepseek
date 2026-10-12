import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PCFU.HonFields
import Submission.Work.BoseBoxFock.boxRestrict_state_facts
import Submission.Work.BoseBoxFock.cIPn_potCubic_kernelForm
import Submission.Work.BoseBoxFock.chiRow_muEvalAux
import Submission.Work.BoseBoxFock.kmomLab_sub_of_support
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-!
## LAYER 3 of `PotCubicFreeU_exists` — the `ℓ`-only (no positivity of `μ` or `a v`) helpers

The node's left-hand side is the cubic row `cIPn Θ (potCubic …)` at the honest environment
`E = (HonestBoxFam v h fc fu HM μ).E` and at `Θ = boxRestrictC ℓ Φ`, `ℓ = sideAt μ (a v)`, and the
target's right-hand side is the same object in the `MiddleU`/`MiddleV` kernel form.  The bridge is
`cIPn_potCubic_kernelForm` (PROVED) together with the identification of the honest environment's
`E.fL`/`E.W1` fields with the chapter's `fLh`/`W1h`.

`PCFU/HonFields.lean` performs that identification **at `0 < μ` and `0 < a v`**.  The node carries
only `0 < sideAt μ (a v)`, so this file redoes it at that (weaker, and in fact enough) hypothesis:

* `0 < sideAt μ (a v)` forces `0 ≤ μ * a v` (at `μ * a v < 0` the factor `(μ a)^{-1/2}` of the box
  side vanishes, because `Real.rpow` of a negative base uses `cos` of the exponent times `π`, and
  `cos (-π/2) = 0`);
* with `0 ≤ μ * a v` the algebra lemma `honKap v μ = ((paramsAt μ (a v)).d ^ 2 * ellH v μ)⁻¹` is
  proved verbatim as in `PCFU/honKap_eq.lean`, replacing `sideAt_pos hμ hav` by the node's own
  `hside` and `0 < μ * a v` by `0 ≤ μ * a v`.

Everything here is `sorry`-free.
-/

set_option maxHeartbeats 1000000

/-- **`0 < sideAt μ (a v)` forces `0 ≤ μ · a v`.**  If `μ · a v < 0` then `(μ · a v) ^ (-(1/2)) = 0`
(the `rpow` of a negative base is `exp (log x * y) * cos (y * π)` and `cos (-π/2) = 0`), so the box
side `Kl · (μ a)^{-1/2}` collapses to `0`. -/
private lemma sideAt_pos_imp_mul_a_nonneg {v : Ω → ℝ} {μ : ℝ}
    (hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :
    0 ≤ μ * _root_.BoseGases.a v := by
  by_contra hcon
  have hlt : μ * _root_.BoseGases.a v < 0 := lt_of_not_ge hcon
  have hz : (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) = 0 := by
    rw [Real.rpow_def_of_neg hlt]
    rw [show -(1 / 2 : ℝ) * Real.pi = -(Real.pi / 2) from by ring, Real.cos_neg,
      Real.cos_pi_div_two, mul_zero]
  have hzero : Work.BoseBox.sideAt μ (_root_.BoseGases.a v) = 0 := by
    show Work.BoseBox.boxSide (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) μ
      (_root_.BoseGases.a v) = 0
    simp only [Work.BoseBox.boxSide]
    rw [hz, mul_zero]
  linarith

/-- `honKap_eq` at the node's `0 < sideAt μ (a v)` (instead of `0 < μ`, `0 < a v`). -/
private lemma honKap_eq_of_sideAt_pos (v : Ω → ℝ) (h : Work.UBB.ScatSol v) {μ : ℝ}
    (hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :
    Work.BoseRowQ2.RowGchiMaskRowAux.honKap v μ
      = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2
          * Work.BoseBoxFock.ellH v μ)⁻¹ := by
  have hμa : 0 ≤ μ * _root_.BoseGases.a v := sideAt_pos_imp_mul_a_nonneg hside
  have key : ∀ a b s : ℝ, (a * b)⁻¹ * s = (b * (a * s⁻¹))⁻¹ := by
    intro a b s
    simp only [mul_inv_rev, inv_inv]
    ring
  unfold Work.BoseRowQ2.RowGchiMaskRowAux.honKap Work.BoseBoxFock.ellH
  rw [if_pos hside]
  unfold Work.BoseBox.sideAt Work.BoseBox.boxSide
  rw [Real.rpow_neg_one, Real.sqrt_eq_rpow]
  rw [Real.rpow_neg hμa]
  exact key _ _ _

/-- The honest environment's `f_L` is the chapter's `fLh`, at the node's hypothesis. -/
private lemma honE_fL_eq_fLh' (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (s : Lab (HM μ).N) :
    (HonestBoxFam v h fc fu HM μ).E.fL s = fLh v fc μ (HM μ).N s := by
  have hℓ : ellH v μ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rw [ellH, if_pos hside]
  have hkap := honKap_eq_of_sideAt_pos v h hside
  rw [Work.BoseRowQ2.RowGchiMaskRowAux.honE_fL_eq HM μ s,
    Work.BoseRowsFS.honF_kmom v h fc fu HM μ, hkap]
  unfold Work.BoseBoxFock.fLh
  rw [show ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2
        * Work.BoseBoxFock.ellH v μ)⁻¹
      = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹ from by rw [hℓ]]

/-- The honest environment's `W₁` is the chapter's `W1h` (definitionally — no positivity needed). -/
private lemma honE_W1_eq_W1h' (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (k : Lab (HM μ).N) :
    (HonestBoxFam v h fc fu HM μ).E.W1 k = W1h v h μ fu (HM μ).N k := rfl

/-- The honest env's **atom-1 (annihilation-slot) kernel** is the chapter's `MiddleU`
(unconditional version of `HonFields.honE_chOne_eq_MiddleU`). -/
private lemma honE_chOne_eq_MiddleU' (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (x y u : Ω) :
    (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N), ∑ k : Lab (HM μ).N,
        (((HonestBoxFam v h fc fu HM μ).E.fL s
            * (HonestBoxFam v h fc fu HM μ).E.W1 k : ℝ) : ℂ)
          * star (pinQ v μ (HM μ).N (s - k) y) * pinTheta v μ (HM μ).N s x
          * star (pinQ v μ (HM μ).N k u))
      = MiddleU v h fc fu μ (HM μ).N x y u := by
  simp only [MiddleU]
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [honE_fL_eq_fLh' v h fc fu HM μ hside s, honE_W1_eq_W1h' v h fc fu HM μ k]

/-- The honest env's **atom-2 (creation-slot) kernel** is the chapter's `MiddleV`
(unconditional version of `HonFields.honE_chTwo_eq_MiddleV`). -/
private lemma honE_chTwo_eq_MiddleV' (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (c : ℂ) (xi y xj u : Ω) :
    (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N), ∑ k : Lab (HM μ).N,
        (((HonestBoxFam v h fc fu HM μ).E.fL s
            * (HonestBoxFam v h fc fu HM μ).E.W1 k : ℝ) : ℂ)
          * pinQ v μ (HM μ).N k xi * star (pinTheta v μ (HM μ).N s y)
          * pinQ v μ (HM μ).N (s - k) xj * star (pinCond v μ c u))
      = MiddleV v h fc fu μ (HM μ).N c xi y xj u := by
  simp only [MiddleV]
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [honE_fL_eq_fLh' v h fc fu HM μ hside s, honE_W1_eq_W1h' v h fc fu HM μ k]

theorem lhs_kernelForm (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ)
    (hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (c : ℂ) (e : Fin (HM μ).m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hemeas : ∀ l, Measurable (e l))
    (hebdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hesupp : ∀ l, Function.support (e l)
      ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (heorth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hemem : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hpin0 : e 0 =ᵐ[MeasureTheory.volume] fun x =>
      c * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x)
    (hpairF : ∀ (k : Work.BoseBoxFock.Lab (HM μ).N) (l : Fin (HM μ).m),
      (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z)
          * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBoxFock.kmomLab (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N k) z)
        = (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ (3 / 2 : ℝ)
            * (HM μ).f k l : ℝ) : ℂ))
    (hpairG : ∀ (s : Work.BoseBoxFock.Lab (HM μ).N) (l : Fin (HM μ).m), s ≠ 0 →
      (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z)
          * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBoxFock.kmomLab (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N s) z)
        = (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ (3 / 2 : ℝ)
            * (HM μ).g s l : ℝ) : ℂ))
    (T_NH : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ))
    (hTNH : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH = Work.BoseB4.dGamma (HM μ).m T_NH) :
    (∫ x : Submission.BoseGases.X n,
        star (Work.BoseBoxFock.boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ x)
          * Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f (HM μ).g
              (Finset.univ : Finset (Work.BoseBoxFock.Lab (HM μ).N))
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
              (Work.BoseBoxFock.boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ) x).re
      = ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ (-3 : ℤ))
        * (∑ p ∈ Submission.BoseGases.pairSet n,
            ((∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3), ∫ u : EuclideanSpace ℝ (Fin 3),
                (starRingEnd ℂ) (Work.BoseBoxFock.boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ x)
                  * Work.BoseBoxFock.pinCond v μ c (x p.1)
                  * Work.BoseBoxFock.PCFU.MiddleU v h fc fu μ (HM μ).N (x p.2) y u
                  * Work.BoseBoxFock.boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ
                      (Function.update (Function.update x p.1 y) p.2 u))
              + (∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3), ∫ u : EuclideanSpace ℝ (Fin 3),
                (starRingEnd ℂ) (Work.BoseBoxFock.boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ x)
                  * Work.BoseBoxFock.PCFU.MiddleV v h fc fu μ (HM μ).N c (x p.1) y (x p.2) u
                  * Work.BoseBoxFock.boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ
                      (Function.update (Function.update x p.1 y) p.2 u))).re) := by
  classical
  -- ## 1. the two box sides agree
  have hℓ : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rw [Work.BoseBoxFock.ellH, if_pos hside]
  -- ## 2. the mode hypotheses in the `ellH` normalisation of the kernel-form lemma
  have hsuppE : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
    intro l
    rw [hℓ]
    exact hesupp l
  have hpin0E : e 0 =ᵐ[MeasureTheory.volume] Work.BoseBoxFock.pinCond v μ c := by
    have hfun : (fun x => c * Work.BoseK15.corpusBox.thetaFun
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x) = Work.BoseBoxFock.pinCond v μ c := by
      funext x
      show c * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x
        = c * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
      rw [hℓ]
    rwa [hfun] at hpin0
  have hpairFE : ∀ (k : Lab (HM μ).N) (l : Fin (HM μ).m),
      (∫ z : Ω, star (e l z)
          * Work.BoseK15.corpusBox.qVec (ellH v μ)
              (kmomLab (ellH v μ) (HM μ).N k) z)
        = (((ellH v μ) ^ (3 / 2 : ℝ) * (HM μ).f k l : ℝ) : ℂ) := by
    intro k l
    simpa only [hℓ] using hpairF k l
  have hpairGE : ∀ (s : Lab (HM μ).N) (l : Fin (HM μ).m), s ≠ 0 →
      (∫ z : Ω, star (e l z)
          * Work.BoseK15.corpusBox.thetaExp (ellH v μ)
              (kmomLab (ellH v μ) (HM μ).N s) z)
        = (((ellH v μ) ^ (3 / 2 : ℝ) * (HM μ).g s l : ℝ) : ℂ) := by
    intro s l hs
    simpa only [hℓ] using hpairG s l hs
  -- ## 3. the state facts about `Θ = boxRestrictC ℓ Φ`
  obtain ⟨hΘm, hΘb, hΘs, _⟩ := Work.BoseBoxFock.boxRestrict_state_facts Φ
  have hΘsE : Function.support
      (Work.BoseBoxFock.boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ)
      ⊆ Work.MB.boxPow n (ellH v μ) := by
    rw [hℓ]
    exact hΘs
  -- ## 4. the kernel form
  have hK := Work.BoseBoxFock.cIPn_potCubic_kernelForm (n := n) (v := v) (μ := μ) (HM := HM μ)
    (e := e) hemeas hebdd hsuppE heorth hemem c hpin0E hpairFE hpairGE
    (Finset.univ : Finset (Lab (HM μ).N)) (HonestBoxFam v h fc fu HM μ).E
    (Work.BoseBoxFock.boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ)
    hΘm hΘb hΘsE
  -- ## 5. the left-hand side in `cIPn` form
  --
  -- (`rw [hK]` cannot be used here: the `potCubic` of the node's left-hand side and the one of
  -- `cIPn_potCubic_kernelForm`'s conclusion carry *syntactically different* (but definitionally
  -- equal) `AddCommGroup (Lab (HM μ).N)` instances, and `rw`'s keyed matching does not see through
  -- them.  `Eq.trans` with `congrArg` uses the default transparency, where they agree.)
  simp only [Work.BoseDict.cIPn] at hK
  simp only [starRingEnd_apply] at hK
  refine Eq.trans ?_ (Eq.trans (congrArg Complex.re hK) ?_)
  · rfl
  -- ## 6. the two channels in the `MiddleU`/`MiddleV` vocabulary
  simp only [MiddleU, MiddleV, starRingEnd_apply, mul_assoc, Complex.ofReal_mul]
  simp only [honE_fL_eq_fLh' v h fc fu HM μ hside, honE_W1_eq_W1h' v h fc fu HM μ]
  -- ## 7. the box side and the exponent
  rw [show (HonestBoxFam v h fc fu HM μ).E.ell
      = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) from rfl]
  rw [show (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ (-(3 : ℝ))
      = (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ (-3 : ℤ) from by
    rw [show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) from by norm_num, Real.rpow_intCast]]
  rw [Complex.smul_re, smul_eq_mul]
  congr 1
  rw [Complex.re_sum]

end Work.BoseBoxFock.PCFU
