import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.PhiStar.LinvFlat.LinvLopAux
import Submission.Work.FTS.PhiStar.LinvFlat.Linv_contDiffOn_hasDerivAt
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff Interval
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.PhiStar.LinvFlat

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The first-order equation satisfied by `Linv h` -/

lemma LI_lop_Linv_eq {h : ℝ → ℝ}
    (hcd : ContDiffOn ℝ 9 h (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ) :
    Set.EqOn (Work.Spaces.Lop (Work.FTS.PhiStar.Linv h))
      (fun θ : ℝ => -(h θ + LI_L2fun θ * Work.FTS.PhiStar.Linv h θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
  obtain ⟨-, hderiv⟩ :=
    Linv_contDiffOn_hasDerivAt (h := h) (n := 9) (by norm_num) hcd hint
  intro θ hθ
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hcoef : 2 * (2 * Real.cos θ ^ 2 - 3 * Real.sin θ ^ 2) = LI_L2fun θ := by
    rw [LI_L2fun_eq]
  show Real.sin (2 * θ) * deriv (Work.FTS.PhiStar.Linv h) θ
    = -(h θ + LI_L2fun θ * Work.FTS.PhiStar.Linv h θ)
  rw [(hderiv θ hθ).deriv, hcoef]
  field_simp [hsin]

/-- Expansion of `Lop^[k]` applied to the source function `-(h + L₂ Linv h)`. -/
lemma LI_lop_iter_Xfun_eqOn {h : ℝ → ℝ}
    (hcd9 : ContDiffOn ℝ 9 h (Set.Ioo 0 (Real.pi / 2)))
    (hg9 : ContDiffOn ℝ 9 (Work.FTS.PhiStar.Linv h) (Set.Ioo 0 (Real.pi / 2)))
    {k : ℕ} (hk : k ≤ 8) :
    Set.EqOn
      (Work.Spaces.Lop^[k]
        (fun θ : ℝ => -(h θ + LI_L2fun θ * Work.FTS.PhiStar.Linv h θ)))
      (fun θ : ℝ => -(Work.Spaces.Lop^[k] h θ)
        - ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) *
            ((Work.Spaces.Lop^[a]) LI_L2fun θ * (Work.Spaces.Lop^[k - a])
              (Work.FTS.PhiStar.Linv h) θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hU : IsOpen (Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioo
  have hh : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) h (Set.Ioo 0 (Real.pi / 2)) :=
    hcd9.of_le (by exact_mod_cast (by omega : k ≤ 9))
  have hg : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) (Work.FTS.PhiStar.Linv h)
      (Set.Ioo 0 (Real.pi / 2)) := hg9.of_le (by exact_mod_cast (by omega : k ≤ 9))
  have hL2 : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) LI_L2fun (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_LI_L2fun k
  have hA0 : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω)
      (fun θ : ℝ => h θ + LI_L2fun θ * Work.FTS.PhiStar.Linv h θ)
      (Set.Ioo 0 (Real.pi / 2)) := hh.add (hL2.mul hg)
  have hB : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω)
      (LI_L2fun * Work.FTS.PhiStar.Linv h) (Set.Ioo 0 (Real.pi / 2)) := hL2.mul hg
  have hneg := LI_Lop_iter_neg_eqOn hU k
    (A := (fun θ : ℝ => h θ + LI_L2fun θ * Work.FTS.PhiStar.Linv h θ)) hA0
  have hadd := LI_Lop_iter_add_eqOn hU k hh hB
  have hleib := LI_Lop_iter_mul_eqOn_9 hU (contDiffOn_LI_L2fun 9) hg9 k hk
  refine hneg.trans ?_
  have hmid : Set.EqOn
      (fun θ : ℝ => -(Work.Spaces.Lop^[k]
        (fun θ' : ℝ => h θ' + LI_L2fun θ' * Work.FTS.PhiStar.Linv h θ') θ))
      (fun θ : ℝ => -(Work.Spaces.Lop^[k] h θ
        + Work.Spaces.Lop^[k] (LI_L2fun * Work.FTS.PhiStar.Linv h) θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro θ hθ
    exact congrArg Neg.neg (hadd hθ)
  refine hmid.trans ?_
  intro θ hθ
  show -(Work.Spaces.Lop^[k] h θ + Work.Spaces.Lop^[k] (LI_L2fun * Work.FTS.PhiStar.Linv h) θ)
    = -(Work.Spaces.Lop^[k] h θ)
      - ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) *
          ((Work.Spaces.Lop^[a]) LI_L2fun θ
            * (Work.Spaces.Lop^[k - a]) (Work.FTS.PhiStar.Linv h) θ)
  rw [hleib hθ]
  ring

/-! ## The growth sequence -/

/-- `LI_Cfun M n = 4 (10⁶ (M+1))ⁿ`. -/
def LI_Cfun (M : ℝ) (n : ℕ) : ℝ := 4 * (1000000 * (M + 1)) ^ n

lemma LI_Cfun_nonneg {M : ℝ} (hM : 0 ≤ M) (n : ℕ) : 0 ≤ LI_Cfun M n := by
  show 0 ≤ 4 * (1000000 * (M + 1)) ^ n
  have h : (0 : ℝ) ≤ 1000000 * (M + 1) := by nlinarith
  exact mul_nonneg (by norm_num) (pow_nonneg h n)

lemma LI_Cfun_one_le {M : ℝ} (hM : 0 ≤ M) (n : ℕ) : (1 : ℝ) ≤ LI_Cfun M n := by
  show (1 : ℝ) ≤ 4 * (1000000 * (M + 1)) ^ n
  have hR : (1 : ℝ) ≤ 1000000 * (M + 1) := by nlinarith
  have h2 : (1 : ℝ) ≤ (1000000 * (M + 1)) ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; nlinarith [ih, hR]
  nlinarith

lemma LI_Cfun_mono {M : ℝ} (hM : 0 ≤ M) {m n : ℕ} (hmn : m ≤ n) :
    LI_Cfun M m ≤ LI_Cfun M n := by
  show 4 * (1000000 * (M + 1)) ^ m ≤ 4 * (1000000 * (M + 1)) ^ n
  have hR : (1 : ℝ) ≤ 1000000 * (M + 1) := by nlinarith
  have hpow : ∀ k : ℕ, (1 : ℝ) ≤ (1000000 * (M + 1)) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; nlinarith [ih, hR]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add]
  have h2 : (0 : ℝ) ≤ (1000000 * (M + 1)) ^ m := pow_nonneg (by linarith) m
  nlinarith [hpow k, h2]


end Work.FTS.PhiStar.LinvFlat
