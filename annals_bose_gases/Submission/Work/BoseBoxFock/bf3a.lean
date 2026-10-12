import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.bf3a_kin_reserve
import Submission.Work.BoseBoxFock.bf3a_pot
import Submission.Work.BoseFixB3.Defs
import Submission.Work.BoseKinLoc.Word.boxFormB_eq_parts_of_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.bf3a` — FS `prop:Hamilton2ndQuant`, first quantised

The node **BF3a** of the box ↔ Fock bridge (`BOSE_BOXFOCK_LEAD.md` §4.2, design
`BOX_TO_MODEL_ROUTE.md`): the first-quantised comparison of FS's box word `H_Λ(μ)`
(`Work.BoseBoxFix.wordB`) with the first-quantised `H_Λ^{2nd}` word `W₂`
(`Work.BoseBoxFock.W2B = W2kinB + W2potB`):

    `W₂ ≤ wordB + C·μ²aℓ³·(d^{2(M−1)} + R²/ℓ²)·‖Φ‖²`

on the admissible class `Adm v ε₀ μ` with `n ≤ 2μℓ³`.

## The assembly

`W₂` is the *sum* of its kinetic and potential rows, so the two already-proved halves add up:

* kinetic — `bf3a_kin_reserve`:
  `W2kinB + (b/2ℓ²)·cnPlus + (ε_Tb/2d²ℓ²)·nPlusHB ≤ kinFormB`
  (the kinetic rows at the **full** gap strength `bℓ⁻²cnPlus + bε_T(dℓ)⁻²nPlusHB`);
* potential — `bf3a_pot`:
  `W2potB − C·errB·‖Φ‖² ≤ chemPartB + pairPartB + (b/100)(ℓ⁻²cnPlus + ε_T(dℓ)⁻²nPlusHB)`
  (FS `lem:potsplit` + `NodeB3B` + `Q₄ ≥ 0`).

What remains is bookkeeping:

1. **`wordB = kinFormB + chemPartB + pairPartB`**
   (`Work.BoseKinLoc.Word.boxFormB_eq_parts_of_integrable`, with the integrability of the
   two pieces of the multiplicative potential word `potWordU` at the honest kernels — this is
   the *same* integrability data that `bf3a_pot` produces internally, so it is re-derived here
   from `Band.integrableOn_potOnePiece` and `Pot.potWordU_integrable`);
2. **the reserve of `bf3a_pot` is absorbed by the excess of the full gaps over the halves**
   (`reserve_absorb`, using `cnPlus ≥ 0`, `nPlusHB ≥ 0`, `b = 1/16 > 0`, `ε_T ≥ 0`).

Both halves are stated at the parameters `P = paramsAt μ (a v)`, `ℓ = sideAt μ (a v)` of FS
`sec:params`; the positivity of `P.d`, `P.eT`, `P.b` is read off `fsParams`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. Absorbing the `bf3a_pot` reserve into the `bf3a_kin_reserve` gaps -/

/-- **The reserve halves fit inside the two full gaps.**  `1/100 ≤ 1/2` in both slots and
the two gap expressions are nonnegative. -/
lemma reserve_absorb {b eT ℓ d W V : ℝ} (hb : 0 ≤ b) (heT : 0 ≤ eT) (hℓ : 0 < ℓ)
    (hd : 0 < d) (hW : 0 ≤ W) (hV : 0 ≤ V) :
    b / 100 * (ℓ ^ (-2 : ℤ) * W + eT * (d * ℓ) ^ (-2 : ℤ) * V)
      ≤ b / 2 * ℓ ^ (-2 : ℤ) * W + eT * b / (2 * d ^ 2 * ℓ ^ 2) * V := by
  have h1 : ℓ ^ (-2 : ℤ) = (ℓ ^ 2)⁻¹ := by simp [zpow_neg]
  have h2 : (d * ℓ) ^ (-2 : ℤ) = (d ^ 2 * ℓ ^ 2)⁻¹ := by simp [zpow_neg, mul_pow]
  have h3 : eT * b / (2 * d ^ 2 * ℓ ^ 2) = eT * b * (d ^ 2 * ℓ ^ 2)⁻¹ / 2 := by
    field_simp
  rw [h1, h2, h3]
  have hW' : 0 ≤ (ℓ ^ 2)⁻¹ * W := mul_nonneg (inv_nonneg.mpr (by positivity)) hW
  have hV' : 0 ≤ eT * (d ^ 2 * ℓ ^ 2)⁻¹ * V :=
    mul_nonneg (mul_nonneg heT (inv_nonneg.mpr (by positivity))) hV
  nlinarith [hb, heT, hW', hV']

/-! ## 2. `wordB` splits into its kinetic, chemical and pair parts

The integrability of the two pieces of the potential word is the same as in `bf3a_pot`:
the one-body `μ`-line is `Band.integrableOn_potOnePiece`, and the pair line follows from the
integrability of the whole word `Pot.potWordU_integrable` minus the one-body piece. -/

/-- **`wordB = kinFormB + chemPartB + pairPartB`** at the honest kernels
`wLoc ℓ v 0` (`= wPairC ℓ v`) and `wLoc ℓ (g₀ v h) 0` (`= wPairC ℓ (g₀ v h)`). -/
theorem wordB_eq_kin_add_chemPair (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Φ) :
    Work.BoseBoxFix.wordB v h μ n Φ
      = Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).b Φ
        + Work.BoseKinLoc.chemPartB n (Submission.BoseGases.g0 v h)
            (Work.BoseBox.sideAt μ (BoseGases.a v)) μ Φ
        + Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ := by
  have hg0 : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  let ℓ : ℝ := Work.BoseBox.sideAt μ (BoseGases.a v)
  have hℓ : 0 < ℓ := Work.BoseBox.sideAt_pos hμ hav
  -- the one-body piece of the potential word
  have hone : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        (∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y))
      (Submission.BoseGases.abox n ℓ) :=
    fun i => integrableOn_sq_mul hℓ hΦc
      (Work.BoseFixB2.Band.integrableOn_potOnePiece (N := n) hℓ hg0 i)
  have hA : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        (-μ * (∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)))
      (Submission.BoseGases.abox n ℓ) := by
    have hsum : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X n => ∑ i : Fin n, (Φ x) ^ 2 *
          (∫ y : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y))
        (Submission.BoseGases.abox n ℓ) :=
      MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hone i)
    refine (hsum.const_mul (-μ)).congr ?_
    filter_upwards with x
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hAB : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x)
      (Submission.BoseGases.abox n ℓ) :=
    integrableOn_sq_mul hℓ hΦc
      (Work.BoseFixB2.Pot.potWordU_integrable (v := v) h (R := R) hR hv_supp hv1
        (μ := μ) (n := n) ℓ)
  -- the pair piece, as `potWordU − (one-body piece)`
  have hB : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
          Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2)))
      (Submission.BoseGases.abox n ℓ) := by
    refine (hAB.sub hA).congr ?_
    filter_upwards with x
    simp only [Pi.sub_apply]
    unfold Work.BoseKinLoc.potWordU
    ring
  -- the box form splits
  have hbox := Work.BoseKinLoc.Word.boxFormB_eq_parts_of_integrable
    (m := n) (v := v) (g := Submission.BoseGases.g0 v h) (ℓ := ℓ) (μ := μ)
    (d := (Work.BoseBox.paramsAt μ (BoseGases.a v)).d)
    (s := (Work.BoseBox.paramsAt μ (BoseGases.a v)).s)
    (εT := (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT)
    (b := (Work.BoseBox.paramsAt μ (BoseGases.a v)).b)
    Φ hA hB
  show Work.BoseKinLoc.boxFormB n v (Submission.BoseGases.g0 v h) ℓ μ
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).b Φ
      = Work.BoseKinLoc.kinFormB n ℓ
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).b Φ
        + Work.BoseKinLoc.chemPartB n (Submission.BoseGases.g0 v h) ℓ μ Φ
        + Work.BoseKinLoc.pairPartB n v ℓ Φ
  exact hbox

/-! ## 3. The node -/

theorem bf3a (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc : Work.BoseBoxFix.LowCut)
    (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
          (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
          Work.BoseBoxFock.W2B v h μ n fc (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseBoxFix.wordB v h μ n Φ
              + C * Work.BoseBoxFock.errB v R μ * Work.BoseBoxFix.normB v μ n Φ := by
  obtain ⟨C₁, ε₁, hC₁, hε₁, hpot⟩ :=
    bf3a_pot v h hv hv1 hvrad hR hv_supp hav fc hB3
  obtain ⟨ε₂, hε₂, hkin⟩ := bf3a_kin_reserve v h hav
  refine ⟨C₁, min ε₁ ε₂, hC₁, lt_min hε₁ hε₂, ?_⟩
  intro μ hAdm n Φ hnc
  have hμ : 0 < μ := hAdm.1
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_right _ _), hAdm.2.2⟩
  have hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  -- the parameters of FS `sec:params`
  have hμa : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have hpar : Work.BoseBox.paramsAt μ (BoseGases.a v)
      = Work.BoseBox.fsParams (μ * (BoseGases.a v) ^ 3) := rfl
  have heT : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT := by
    rw [hpar]
    exact le_of_lt (Work.BoseBox.fsXp_pos hμa)
  have hb : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).b := by
    rw [hpar]
    simp only [Work.BoseBox.fsParams, Work.BoseBox.bValue]
    norm_num
  have hd : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d := by
    rw [hpar]
    exact Work.BoseBox.fsXp_pos hμa
  -- the three inequalities
  have hsplit := wordB_eq_kin_add_chemPair v h hv1 hvrad hR hv_supp hμ hav
    (Φ : Submission.BoseGases.X n → ℝ) hΦc
  have hres := reserve_absorb (W := Submission.BoseGases.cnPlus
        (Work.BoseBox.sideAt μ (BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ))
    (V := Work.BoseBoxFix.nPlusHB (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).d (Φ : Submission.BoseGases.X n → ℝ))
    hb heT hℓ hd Submission.BoseGases.cnPlus_nonneg
    (Work.BoseFixB3.nPlusHB_nonneg hℓ (Φ : Submission.BoseGases.X n → ℝ))
  have hK := hkin μ hAdm₂ n Φ hnc
  have hP := hpot μ hAdm₁ n Φ hnc
  rw [W2B, hsplit]
  linarith

end Work.BoseBoxFock
