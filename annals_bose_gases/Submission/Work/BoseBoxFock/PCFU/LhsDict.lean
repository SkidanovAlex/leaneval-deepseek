import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PCFU.LhsTwoRe
import Submission.Work.BoseBoxFock.PCFU.pairI1_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.PCFU.LhsDict` — the cubic dictionary theorem (glue (G3)+(G4))

This module assembles the PROVED ingredients

* `PCFU.pairI1_eq` — the per-pair identity
  `I₁(p) = ℓ³·chWord(p) + chSlotAB(p) + ℓ⁻³·chSlotCD(p)` (per ordered pair `p`), and
* `PCFU.sum_chWord_eq_half_q3lowWord` — `Σ_p chWord(p) = ½·q3lowWord`,
* `PCFU.lhs_eq_two_re_pairSum` — `LHS = 2ℓ⁻³·Re(Σ_p I₁(p))`,

into the **dictionary theorem**

    LHS.re = q3lowWord + 2·ℓ⁻³·Re(chSlotSum) ,

where `chSlotSum` is the total slot of the dictionary (the `(A,B)` alias pair plus `ℓ⁻³` times the
`(C,D)` alias pair, summed over the ordered pairs).  Consequently the target `PotCubicFreeU` is
*exactly* the single bound `2ℓ⁻³·Re(chSlotSum) ≤ ½·errKafz·normB` on the slot.

Nothing here is new mathematics: it is `Finset.sum_congr` plus `Complex.re`-algebra.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Work.BoseB4 Work.BoseBoxFock

set_option maxHeartbeats 3000000
set_option linter.unusedVariables false

/-- **Transport of a `BoxState` across an equality of box sides.**  The fields of `BoxState` do
not mention the side, so the same data is a state at either side.  (`abbrev`, so that the coercion
to the underlying function is definitionally the identity — this is what lets `ellH`-spelled
statements be used at the `sideAt` side without any rewriting.) -/
abbrev boxStateCast {n : ℕ} {ℓ ℓ' : ℝ} (_h : ℓ = ℓ') (Φ : Work.BoseKinLoc.BoxState n ℓ) :
    Work.BoseKinLoc.BoxState n ℓ' :=
  { toFun := Φ.toFun, contDiff := Φ.contDiff, symm := Φ.symm, nezero := Φ.nezero }

/-- The real arithmetic of the dictionary assembly: with `x` the `½·q3lowWord` column and `B` the
`(C,D)` slot, the bookkeeping cancels the `ℓ³` against the `2ℓ⁻³`. -/
private lemma arith_final {s Q A B : ℝ} (hs : s ≠ 0) :
    2 * s ^ (-3 : ℤ) * (s ^ 3 * ((1 / 2) * Q) + A + s ^ (-3 : ℤ) * B)
      = Q + 2 * s ^ (-3 : ℤ) * (A + s ^ (-3 : ℤ) * B) := by
  have h2 : s ^ (-3 : ℤ) * s ^ (3 : ℕ) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hs]
    norm_num
  have h3 : s ^ (-3 : ℤ) * (s ^ (3 : ℕ) * ((1 / 2) * Q)) = (1 / 2) * Q := by
    rw [← mul_assoc, h2, one_mul]
  have h4 : 2 * s ^ (-3 : ℤ) * (s ^ 3 * ((1 / 2) * Q) + A + s ^ (-3 : ℤ) * B)
      = 2 * (s ^ (-3 : ℤ) * (s ^ 3 * ((1 / 2) * Q)) + s ^ (-3 : ℤ) * A
          + s ^ (-3 : ℤ) * (s ^ (-3 : ℤ) * B)) := by ring
  rw [h4, h3]
  ring

/-- **The total slot of the cubic dictionary** at the state `Θ` (already box-restricted):
the `(A,B)`-alias pair plus `ℓ⁻³` times the `(C,D)`-alias pair, summed over the *ordered* pairs.
This is exactly the object whose smallness is the remaining obligation of the node. -/
noncomputable def chSlotSum {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  (∑ p ∈ Submission.BoseGases.pairSet n, chSlotAB v h fc fu μ N p.1 p.2 Θ)
    + ((ellH v μ : ℂ)) ^ (-3 : ℤ)
      * (∑ p ∈ Submission.BoseGases.pairSet n, chSlotCD v h fc fu μ N p.1 p.2 Θ)

/-- **The cubic dictionary theorem.**  The honest cubic row (`Finset.univ` over the `k`-labels,
at the honest environment and the pinned condensate) equals the frozen word `q3lowWord` plus the
total slot.  This is the `(G3)+(G4)` assembly of the session-13 plan. -/
theorem lhs_re_eq_q3lowWord_add_slot {n : ℕ}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (hvrad : _root_.BoseGases.IsRadial v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hsub : ∀ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
        fLh v fc μ (HM μ).N s ≠ 0 →
        ∀ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
          W1h v h μ fu (HM μ).N k ≠ 0 →
        kmomLab (ellH v μ) (HM μ).N (s - k)
          = kmomLab (ellH v μ) (HM μ).N s - kmomLab (ellH v μ) (HM μ).N k)
    (hκ : 0 < chKappa v μ)
    (hN : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ ((HM μ).N : ℝ))
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
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
    (hTNH : (HonestBoxFam v h fc fu HM μ).T.NH = Work.BoseB4.dGamma (HM μ).m T_NH)
    (hc : c = (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) :
    (∫ x : Submission.BoseGases.X n,
        star (boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ x)
          * potCubic (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f (HM μ).g
              (Finset.univ : Finset (Lab (HM μ).N))
              (HonestBoxFam v h fc fu HM μ).E
              (boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ) x).re
      = Work.BoseBoxFix.q3lowWord fc (chKappa v μ) (ellH v μ)
          (Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0)
          (Φ : Submission.BoseGases.X n → ℝ)
        + 2 * (ellH v μ) ^ (-3 : ℤ)
          * (chSlotSum v h fc fu μ (HM μ).N
              (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))).re := by
  classical
  have hℓeq : ellH v μ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rw [ellH, if_pos hside]
  have hℓpos : 0 < ellH v μ := ellH_pos v μ
  -- the interface `LHS = 2ℓ⁻³·Re(Σ_p I₁(p))`
  have h2 := lhs_eq_two_re_pairSum v h fc fu HM μ hside n Φ c e hemeas hebdd hesupp heorth
    hemem hpin0 hpairF hpairG T_NH hTNH
  -- the per-pair identity, in the `sideAt` spelling the goal uses
  have hterm : ∀ p ∈ Submission.BoseGases.pairSet n,
      (∫ x : Submission.BoseGases.X n, ∫ y : E3, ∫ u : E3,
          (starRingEnd ℂ) (boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ x)
            * pinCond v μ c (x p.1)
            * MiddleU v h fc fu μ (HM μ).N (x p.2) y u
            * boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ
                (Function.update (Function.update x p.1 y) p.2 u))
        = ((ellH v μ : ℂ)) ^ 3 * chWord v h fc fu μ (HM μ).N p.1 p.2
              (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
          + chSlotAB v h fc fu μ (HM μ).N p.1 p.2
              (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
          + ((ellH v μ : ℂ)) ^ (-3 : ℤ) * chSlotCD v h fc fu μ (HM μ).N p.1 p.2
              (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)) := by
    intro p hp
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hpe := pairI1_eq hij v h hvrad fc fu μ (HM μ).N hsub hℓpos hκ hN
      (boxStateCast hℓeq.symm Φ) c hc
    simpa only [boxStateCast, hℓeq, starRingEnd_apply] using hpe
  have hsum : (∑ p ∈ Submission.BoseGases.pairSet n,
        (∫ x : Submission.BoseGases.X n, ∫ y : E3, ∫ u : E3,
          (starRingEnd ℂ) (boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ x)
            * pinCond v μ c (x p.1)
            * MiddleU v h fc fu μ (HM μ).N (x p.2) y u
            * boxRestrictC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Φ
                (Function.update (Function.update x p.1 y) p.2 u)))
      = (∑ p ∈ Submission.BoseGases.pairSet n,
          (((ellH v μ : ℂ)) ^ 3 * chWord v h fc fu μ (HM μ).N p.1 p.2
                (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
            + chSlotAB v h fc fu μ (HM μ).N p.1 p.2
                (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
            + ((ellH v μ : ℂ)) ^ (-3 : ℤ) * chSlotCD v h fc fu μ (HM μ).N p.1 p.2
                (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)))) :=
    Finset.sum_congr rfl hterm
  -- `Σ_p chWord = ½·q3lowWord`
  have hword : (∑ p ∈ Submission.BoseGases.pairSet n,
        chWord v h fc fu μ (HM μ).N p.1 p.2
          (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)))
      = (((1 / 2) * Work.BoseBoxFix.q3lowWord fc (chKappa v μ) (ellH v μ)
            (Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0)
            (Φ : Submission.BoseGases.X n → ℝ) : ℝ) : ℂ) := by
    have hh := sum_chWord_eq_half_q3lowWord v h fc fu μ (HM μ).N (boxStateCast hℓeq.symm Φ)
      hℓpos hκ
    simpa only [boxStateCast] using hh
  have hsplit : (∑ p ∈ Submission.BoseGases.pairSet n,
        (((ellH v μ : ℂ)) ^ 3 * chWord v h fc fu μ (HM μ).N p.1 p.2
              (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
          + chSlotAB v h fc fu μ (HM μ).N p.1 p.2
              (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
          + ((ellH v μ : ℂ)) ^ (-3 : ℤ) * chSlotCD v h fc fu μ (HM μ).N p.1 p.2
              (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))))
      = ((ellH v μ : ℂ)) ^ 3 * (∑ p ∈ Submission.BoseGases.pairSet n,
            chWord v h fc fu μ (HM μ).N p.1 p.2
              (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)))
          + (∑ p ∈ Submission.BoseGases.pairSet n,
              chSlotAB v h fc fu μ (HM μ).N p.1 p.2
                (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)))
          + ((ellH v μ : ℂ)) ^ (-3 : ℤ) * (∑ p ∈ Submission.BoseGases.pairSet n,
              chSlotCD v h fc fu μ (HM μ).N p.1 p.2
                (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [h2, hsum, hsplit, hword, chSlotSum, hℓeq]
  -- pure arithmetic
  have hsne : Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ≠ 0 := ne_of_gt hside
  have hre1 : (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v) : ℂ) ^ 3
      * (((1 / 2) * Work.BoseBoxFix.q3lowWord fc (chKappa v μ)
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.g0 v h) 0)
            (Φ : Submission.BoseGases.X n → ℝ) : ℝ) : ℂ))).re
      = (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ (3 : ℕ)
        * ((1 / 2) * Work.BoseBoxFix.q3lowWord fc (chKappa v μ)
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.g0 v h) 0)
            (Φ : Submission.BoseGases.X n → ℝ)) := by
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

  have hre2 : (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v) : ℂ) ^ (-3 : ℤ))
      * (∑ p ∈ Submission.BoseGases.pairSet n, chSlotCD v h fc fu μ (HM μ).N p.1 p.2
          (boxRestrictR (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Φ : Submission.BoseGases.X n → ℝ))) ).re
      = (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ (-3 : ℤ)
        * (∑ p ∈ Submission.BoseGases.pairSet n, chSlotCD v h fc fu μ (HM μ).N p.1 p.2
            (boxRestrictR (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Φ : Submission.BoseGases.X n → ℝ))).re := by
    simp only [← Complex.ofReal_zpow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  simp only [Complex.add_re, hre1, hre2]
  exact arith_final (s := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Q := Work.BoseBoxFix.q3lowWord fc (chKappa v μ)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Submission.BoseGases.g0 v h) 0) (Φ : Submission.BoseGases.X n → ℝ))
    (A := (∑ p ∈ Submission.BoseGases.pairSet n, chSlotAB v h fc fu μ (HM μ).N p.1 p.2
      (boxRestrictR (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Φ : Submission.BoseGases.X n → ℝ))).re)
    (B := (∑ p ∈ Submission.BoseGases.pairSet n, chSlotCD v h fc fu μ (HM μ).N p.1 p.2
      (boxRestrictR (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Φ : Submission.BoseGases.X n → ℝ))).re) hsne

end Work.BoseBoxFock.PCFU
