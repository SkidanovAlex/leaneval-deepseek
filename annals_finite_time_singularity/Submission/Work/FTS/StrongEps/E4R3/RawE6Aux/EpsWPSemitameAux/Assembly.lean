/-
# `semitame_of_bdata` — the assembly of the five blocks
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.EpsWPSemitameAux.Common

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.RawE6Aux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The assembly of the five blocks -/

/-- **The assembly**: the five `BData`s of the blocks of `epsWBlk` give the three conjuncts of
the semi-tame estimate with the single constant `√(16·(KL+KM+K0+KN+KS+1)) + 1`.  (The proof is
the arithmetic core of `Apriori4Proofs.semitame_blk_of_blocks`, with the `μ̄`-bound of the
`blkMu`-block supplied as an explicit hypothesis instead of being extracted from the elliptic
packages.) -/
theorem semitame_of_bdata {C₀ Ce Cs α : ℝ} (hα : α ∈ Set.Ioc 0 1)
    {KL KM K0 KN KS : ℝ} (hKL : 0 < KL) (hKM : 0 < KM) (hK0 : 0 < K0) (hKN : 0 < KN)
    (hKS : 0 < KS)
    (hL : ∀ {w : Fn}, Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → w z θ = 0) →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KL
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkLin α w))
    (hM : ∀ {Φs w Φg : Fn}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      |Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w Φg| ≤ 1 / 2 →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KM
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkMu α Φs w Φg))
    (h0 : ∀ {w : Fn}, Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → w z θ = 0) →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w K0
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w))
    (hN : ∀ {Φs w Φg : Fn}, Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KN
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN α Φs w Φg))
    (hS : ∀ {w : Fn} (μ lam : ℝ), Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → |μ| ≤ 1 / 2 → |lam| ≤ 1 →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KS
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkNstar w μ lam)) :
    ∀ {Φs w Φg : Fn} {μ lam : ℝ}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → |μ| ≤ 1 / 2 → |lam| ≤ 1 →
      |Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w Φg| ≤ 1 / 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      Work.FTS.VocabO.HQo α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam)
          ≤ (Real.sqrt (16 * (KL + KM + K0 + KN + KS + 1)) + 1)
            * (1 + Work.Spaces.HkNorm α 5 w) ∧
      Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam)
          ≤ (Real.sqrt (16 * (KL + KM + K0 + KN + KS + 1)) + 1)
              * (1 + Work.Spaces.HkNorm α 7 w)
            + (Real.sqrt (16 * (KL + KM + K0 + KN + KS + 1)) + 1)
              * (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by
  set Ktot : ℝ := KL + KM + K0 + KN + KS + 1 with hKtot
  have hKtot0 : 0 < Ktot := by rw [hKtot]; linarith
  set C : ℝ := Real.sqrt (16 * Ktot) + 1 with hC
  have hCsq : Real.sqrt (16 * Ktot) ≤ C := by rw [hC]; linarith [Real.sqrt_nonneg (16 * Ktot)]
  intro Φs w Φg μ lam hcls hXw hμ hlam hμblk hzero hgo hK hstar
  have hα0 : 0 < α := hα.1
  set A1 : Fn := fun z θ => - Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkLin α w z θ with hA1
  set A2 : Fn := fun z θ => - Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkMu α Φs w Φg z θ with hA2
  set A3 : Fn := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w with hA3
  set A4 : Fn := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN α Φs w Φg with hA4
  set A5 : Fn := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkNstar w μ lam with hA5
  have hsum : Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam
      = Work.FTS.StrongEps.E4R3.Apriori4Proofs.sum5 A1 A2 A3 A4 A5 := by
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk_eq_sum5, ← hA1, ← hA2, ← hA3, ← hA4, ← hA5]
  have eL : Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KL A1 := by
    rw [hA1]; exact (hL hcls hXw hzero).neg
  have eM : Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KM A2 := by
    rw [hA2]
    exact (hM hcls hXw hμblk).neg
  have e0 : Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w K0 A3 := by
    rw [hA3]; exact h0 hcls hXw hzero
  have eN : Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KN A4 := by
    rw [hA4]; exact hN hcls hXw hzero hgo hK hstar
  have eS : Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KS A5 := by
    rw [hA5]; exact hS μ lam hcls hXw hμ hlam
  have hm6 : Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam) := by
    rw [hsum]
    exact Work.FTS.StrongEps.E4R3.Apriori4Proofs.hkMem_sum5 eL.sm eM.sm e0.sm eN.sm eS.sm
      eL.hm eM.hm e0.hm eN.hm eS.hm
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam) := by
    rw [hsum]
    exact Work.FTS.StrongEps.E4R3.Apriori4Proofs.smoothOpen_sum5 eL.sm eM.sm e0.sm eN.sm eS.sm
  have m4 : ∀ {B : Fn}, Work.FTS.EllipticEst.SmoothOpen B → Work.Spaces.HkMem α 6 B →
      Work.Spaces.HkMem α 4 B := fun hs hm =>
    Work.FTS.OpenPkg.HkMem_mono_open hs 4 (by norm_num) hm
  have hsq4 : Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam)
      ≤ 16 * Ktot * (1 + Work.Spaces.HkSq α 5 w) := by
    rw [hsum]
    have hs := Work.FTS.StrongEps.E4R3.Apriori4Proofs.hkSq_sum5 hα0 eL.sm eM.sm e0.sm eN.sm eS.sm
      (m4 eL.sm eL.hm) (m4 eM.sm eM.hm) (m4 e0.sm e0.hm) (m4 eN.sm eN.hm) (m4 eS.sm eS.hm)
    have hS5 := Work.Spaces.HkSq_nonneg α 5 w
    have hbound : Work.Spaces.HkSq α 4 A1 + Work.Spaces.HkSq α 4 A2 + Work.Spaces.HkSq α 4 A3
        + Work.Spaces.HkSq α 4 A4 + Work.Spaces.HkSq α 4 A5
        ≤ Ktot * (1 + Work.Spaces.HkSq α 5 w) := by
      rw [hKtot]
      nlinarith [eL.b4, eM.b4, e0.b4, eN.b4, eS.b4, hS5, hKL, hKM, hK0, hKN, hKS]
    calc Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.sum5 A1 A2 A3 A4 A5)
        ≤ 16 * (Work.Spaces.HkSq α 4 A1 + Work.Spaces.HkSq α 4 A2 + Work.Spaces.HkSq α 4 A3
            + Work.Spaces.HkSq α 4 A4 + Work.Spaces.HkSq α 4 A5) := hs
      _ ≤ 16 * (Ktot * (1 + Work.Spaces.HkSq α 5 w)) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = 16 * Ktot * (1 + Work.Spaces.HkSq α 5 w) := by ring
  have hsq6 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam)
      ≤ 16 * Ktot * ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by
    rw [hsum]
    have hs := Work.FTS.StrongEps.E4R3.Apriori4Proofs.hkSq_sum5 hα0 eL.sm eM.sm e0.sm eN.sm eS.sm
      eL.hm eM.hm e0.hm eN.hm eS.hm
    have hS7 := Work.Spaces.HkSq_nonneg α 7 w
    have hS6 := Work.Spaces.HkSq_nonneg α 6 w
    have hbound : Work.Spaces.HkSq α 6 A1 + Work.Spaces.HkSq α 6 A2 + Work.Spaces.HkSq α 6 A3
        + Work.Spaces.HkSq α 6 A4 + Work.Spaces.HkSq α 6 A5
        ≤ Ktot * ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by
      rw [hKtot]
      nlinarith [eL.b6, eM.b6, e0.b6, eN.b6, eS.b6, hS7, hS6,
        sq_nonneg (1 + Work.Spaces.HkSq α 6 w), hKL, hKM, hK0, hKN, hKS]
    calc Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.sum5 A1 A2 A3 A4 A5)
        ≤ 16 * (Work.Spaces.HkSq α 6 A1 + Work.Spaces.HkSq α 6 A2 + Work.Spaces.HkSq α 6 A3
            + Work.Spaces.HkSq α 6 A4 + Work.Spaces.HkSq α 6 A5) := hs
      _ ≤ 16 * (Ktot * ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2)) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = 16 * Ktot * ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by ring
  have hHQ : Work.FTS.VocabO.HQo α 6
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam) := ⟨hsm, hm6⟩
  have hN5 : Work.Spaces.HkNorm α 5 w = Real.sqrt (Work.Spaces.HkSq α 5 w) := rfl
  have hN6 : Work.Spaces.HkNorm α 6 w = Real.sqrt (Work.Spaces.HkSq α 6 w) := rfl
  have hN7 : Work.Spaces.HkNorm α 7 w = Real.sqrt (Work.Spaces.HkSq α 7 w) := rfl
  have sqrt_one_add_le : ∀ {x : ℝ}, 0 ≤ x → Real.sqrt (1 + x) ≤ 1 + Real.sqrt x := by
    intro x hx
    have hnn : 0 ≤ 1 + Real.sqrt x := by linarith [Real.sqrt_nonneg x]
    rw [← Real.sqrt_sq hnn]
    refine Real.sqrt_le_sqrt ?_
    have hsq : (1 + Real.sqrt x) ^ 2 = 1 + 2 * Real.sqrt x + x := by
      rw [add_sq, one_pow, Real.sq_sqrt hx]; ring
    rw [hsq]; linarith [Real.sqrt_nonneg x]
  have sqrt_add_le' : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b →
      Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    have hnn : 0 ≤ Real.sqrt a + Real.sqrt b := by
      linarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
    rw [← Real.sqrt_sq hnn]
    refine Real.sqrt_le_sqrt ?_
    have hsq : (Real.sqrt a + Real.sqrt b) ^ 2 = a + 2 * (Real.sqrt a * Real.sqrt b) + b := by
      rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
    rw [hsq]
    have h2 : 0 ≤ 2 * (Real.sqrt a * Real.sqrt b) := by positivity
    linarith
  refine ⟨hHQ, ?_, ?_⟩
  · rw [Work.Spaces.HkNorm]
    have hS5 := Work.Spaces.HkSq_nonneg α 5 w
    calc Real.sqrt (Work.Spaces.HkSq α 4
            (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam))
        ≤ Real.sqrt (16 * Ktot * (1 + Work.Spaces.HkSq α 5 w)) := Real.sqrt_le_sqrt hsq4
      _ = Real.sqrt (16 * Ktot) * Real.sqrt (1 + Work.Spaces.HkSq α 5 w) := by
          rw [Real.sqrt_mul (by positivity)]
      _ ≤ Real.sqrt (16 * Ktot) * (1 + Real.sqrt (Work.Spaces.HkSq α 5 w)) :=
          mul_le_mul_of_nonneg_left (sqrt_one_add_le hS5) (Real.sqrt_nonneg _)
      _ = Real.sqrt (16 * Ktot) * (1 + Work.Spaces.HkNorm α 5 w) := by rw [hN5]
      _ ≤ C * (1 + Work.Spaces.HkNorm α 5 w) :=
          mul_le_mul_of_nonneg_right hCsq (by linarith [Work.Spaces.HkNorm_nonneg α 5 w])
  · rw [Work.Spaces.HkNorm]
    have hS6 := Work.Spaces.HkSq_nonneg α 6 w
    have hS7 := Work.Spaces.HkSq_nonneg α 7 w
    have hsq : Real.sqrt ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2)
        ≤ (1 + Work.Spaces.HkNorm α 7 w) + (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by
      have h1 : Real.sqrt (1 + Work.Spaces.HkSq α 7 w) ≤ 1 + Work.Spaces.HkNorm α 7 w := by
        refine le_trans (sqrt_one_add_le hS7) (le_of_eq ?_)
        rw [hN7]
      have h2 : Real.sqrt ((1 + Work.Spaces.HkSq α 6 w) ^ 2)
          = 1 + Work.Spaces.HkSq α 6 w := Real.sqrt_sq (by linarith)
      have h3 : 1 + Work.Spaces.HkSq α 6 w ≤ (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by
        rw [hN6]
        nlinarith [Real.sq_sqrt hS6, Real.sqrt_nonneg (Work.Spaces.HkSq α 6 w)]
      calc Real.sqrt ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2)
          ≤ Real.sqrt (1 + Work.Spaces.HkSq α 7 w)
              + Real.sqrt ((1 + Work.Spaces.HkSq α 6 w) ^ 2) :=
            sqrt_add_le' (by linarith) (by positivity)
        _ = Real.sqrt (1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) := by rw [h2]
        _ ≤ (1 + Work.Spaces.HkNorm α 7 w) + (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by
            linarith [h1, h3]
    calc Real.sqrt (Work.Spaces.HkSq α 6
            (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam))
        ≤ Real.sqrt (16 * Ktot * ((1 + Work.Spaces.HkSq α 7 w)
            + (1 + Work.Spaces.HkSq α 6 w) ^ 2)) := Real.sqrt_le_sqrt hsq6
      _ = Real.sqrt (16 * Ktot) * Real.sqrt ((1 + Work.Spaces.HkSq α 7 w)
            + (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by rw [Real.sqrt_mul (by positivity)]
      _ ≤ Real.sqrt (16 * Ktot) * ((1 + Work.Spaces.HkNorm α 7 w)
            + (1 + Work.Spaces.HkNorm α 6 w) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
      _ ≤ C * ((1 + Work.Spaces.HkNorm α 7 w) + (1 + Work.Spaces.HkNorm α 6 w) ^ 2) :=
          mul_le_mul_of_nonneg_right hCsq (by
            have h7 := Work.Spaces.HkNorm_nonneg α 7 w
            have h6 := Work.Spaces.HkNorm_nonneg α 6 w
            positivity)
      _ = C * (1 + Work.Spaces.HkNorm α 7 w) + C * (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by ring


end Work.FTS.StrongEps.E4R3.RawE6Aux
