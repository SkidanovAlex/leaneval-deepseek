/-
  Area E7 / the `CoreLT_succ` endgame, node **E2S** (module `Work.WilE7.Endgame.Bv2.Aux2`).

  Bookkeeping lemmas used by the per-instance construction `e2s_build`:
  * monotonicity of `Polynomial.eval` on `ℕ`;
  * the format bounds of the pair sets `absPairSet`, `absLevelPairSet` of a stratum (these feed the
    `absPairSet`/`absLevelPairSet` hypotheses of the `Σ`/`E1` boxes);
  * the format bound of a `SemiPf.pad` to a common fibre dimension `M2 ≤ SC`.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.Bv2.Env
import Submission.Work.WilE7.Endgame.PairSet2Bounds
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.WilE7.levelAgree_semiPf
import Submission.Work.WilE7.pad_proj
import Submission.Work.WilE7.pad_deg

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7.Endgame.Bv2

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

/-! ## §1. The format bounds of the pair sets -/

/-- The format of the pair set of a stratum, in the form used by the `Σ`-box. -/
theorem absPairSet_fmt_le {n m F : ℕ} (T : Stratum 0 (n + (m + 1)))
    (hT : (n + (m + 1)) + T.X.r ≤ F) : (absPairSet T).fmt ≤ 2 * F := by
  have hT' : (absReindex T).fmt ≤ F := by
    show (n + (m + 1)) + (absReindex T).r ≤ F
    rw [show (absReindex T).r = T.X.r from rfl]
    exact hT
  have h := Work.WilE7.fiberProdZ_fmt (p := n) (q := m + 1) (absReindex T) (absReindex T) hT' hT'
  have h1 : (absPairSet T).fmt =
      (Work.WilE7.fiberProdZ (absReindex T) (absReindex T)).fmt := by
    show (0 + pPair n m) + (Work.WilE7.fiberProdZ (absReindex T) (absReindex T)).r
      = pPair n m + (Work.WilE7.fiberProdZ (absReindex T) (absReindex T)).r
    omega
  rw [h1]
  exact h

/-- The format of the level-agreement pair set of two strata. -/
theorem absLevelPairSet_fmt_le {n m F : ℕ} (R T : Stratum 0 (n + (m + 1)))
    (hR : (n + (m + 1)) + R.X.r ≤ F) (hT : (n + (m + 1)) + T.X.r ≤ F) :
    (absLevelPairSet R T).fmt ≤ 2 * F := by
  have hR' : (absReindex R).fmt ≤ F := hR
  have hT' : (absReindex T).fmt ≤ F := hT
  have h := Work.WilE7.levelGlue_fmt (absReindex R) (absReindex T) hR' hT'
  have h1 : (absLevelPairSet R T).fmt =
      (Work.WilE7.levelGlue (absReindex R) (absReindex T)).fmt := by
    show (0 + pPair n m) + (Work.WilE7.levelGlue (absReindex R) (absReindex T)).r
      = pPair n m + (Work.WilE7.levelGlue (absReindex R) (absReindex T)).r
    omega
  rw [h1]
  exact h

/-! ## §1'. Monotonicity of `MvPolynomial.eval` in several variables -/

/-- Evaluation of a two-variable polynomial with `ℕ` coefficients is monotone in the arguments. -/
theorem mvpoly_eval_mono2 (b : MvPolynomial (Fin 2) ℕ) {v w : Fin 2 → ℕ} (h : ∀ i, v i ≤ w i) :
    MvPolynomial.eval v b ≤ MvPolynomial.eval w b := by
  induction b using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add]; exact Nat.add_le_add hp hq
  | mul_X p i hp =>
      rw [map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]
      exact Nat.mul_le_mul hp (h i)

/-- Evaluation of a three-variable polynomial with `ℕ` coefficients is monotone in the
arguments. -/
theorem mvpoly_eval_mono3 (b : MvPolynomial (Fin 3) ℕ) {v w : Fin 3 → ℕ} (h : ∀ i, v i ≤ w i) :
    MvPolynomial.eval v b ≤ MvPolynomial.eval w b := by
  induction b using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add]; exact Nat.add_le_add hp hq
  | mul_X p i hp =>
      rw [map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]
      exact Nat.mul_le_mul hp (h i)

/-! ## §2. Padding to a common fibre dimension -/

/-- The format of a `SemiPf.pad` to a dimension `M2`: it is `M2 + X.r`. -/
theorem semipf_pad_fmt_eq {k K : ℕ} (hm : k ≤ K) (X : SemiPf k) :
    (Work.WilE7.SemiPf.pad hm X).fmt = K + X.r := rfl

/-- **The padding format bound.**  A set in `ℝ^{n+s}` of format at most `2 * SC`, padded to a
common *full* dimension `M2 ≤ SC`, has format at most `F'` (the padding adds `M2` to the chain
length). -/
theorem semipf_pad_fmt_le_F' {hFC : HypFC} {hE2 : HypE2} {hE5 : HypE5} {hE6 : HypE6}
    {h0 : FrontierRestrat} {h1 : SigmaVPairs} {hV : GCaseVertical} {n K F : ℕ}
    (E : E2Env hFC hE2 hE5 hE6 h0 h1 hV n K F) {s M2 : ℕ} (hM2 : M2 ≤ E.SC)
    {Z : SemiPf (n + s)} (hZ : Z.fmt ≤ 2 * E.SC) (hm : n + s ≤ M2) :
    (Work.WilE7.SemiPf.pad hm Z).fmt ≤ E.F' := by
  rw [semipf_pad_fmt_eq]
  have hr : Z.r ≤ Z.fmt := by
    show Z.r ≤ (n + s) + Z.r
    omega
  have h1 : M2 + Z.r ≤ E.SC + 2 * E.SC := by omega
  have h2 : 3 * E.SC ≤ E.F' := by have := E.hF'pad; omega
  omega

end Work.WilE7.Endgame.Bv2
