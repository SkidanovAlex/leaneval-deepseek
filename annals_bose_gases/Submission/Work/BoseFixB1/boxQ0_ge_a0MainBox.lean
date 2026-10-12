import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxQ0Value
import Submission.Work.BoseFixB1.q0word_localised_value
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxQ0_ge_a0MainBox` — the box-projected `Q₀ ≥ A₀`-main estimate

The box-projected analogue of `Work.BoseFixB1.q0word_ge_a0_main`: at FS's own box projections
`P_{B(u),i}` (with the box volume `volA` of `A ⊆ acube ℓ` in place of `ℓ³`),

    a0MainLocBox volA μ (∬_{A×A}w₁) (Σᵢ∫(PᵢΦ)²) ≤ boxQ0 volA ℓ μ A w₁ w₂ Φ .

The proof is the same three-ingredient chain as in the localised cube case:

1. the exact value of the box-projected word (`boxQ0_value`, proved in `BoxQ0Value.lean`),
   `boxQ0 = ½(M₂/volA²)·Pc − μ(M₁/volA)·S` with `M₁ = ∬_{A×A}w₁`, `M₂ = ∬_{A×A}w₂`;
2. the pure-real `A₀` algebra `Submission.BoseGases.a0_form_ge_fs_main` at `V = volA`,
   `a = M₁/(8π volA)`, `D = 0`, giving
   `a0MainLocBox volA μ M₁ S ≤ ½(M₁/volA²)(S²−S) − μ(M₁/volA)S`;
3. the condensate-pair comparison `S² − S ≤ Pc` and the mass hierarchy `M₁ ≤ M₂`
   (with `0 ≤ Pc`, `0 ≤ M₁`), giving `½(M₁/volA²)(S²−S) ≤ ½(M₂/volA²)Pc`.

Steps 2 and 3 are pure real arithmetic and are recorded as the helper lemma
`a0MainLocBox_le_counts` below.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-- **The pure-real core of the box-projected `A₀` step.**  For `V > 0`, `μ ≥ 0`, `M₁,M₂ ≥ 0`
with `M₁ ≤ M₂`, `Pc ≥ 0` and the condensate-pair comparison `S² − S ≤ Pc`,

    a0MainLocBox V μ M₁ S ≤ ½(M₂/V²)·Pc − μ(M₁/V)·S .

This is `Submission.BoseGases.a0_form_ge_fs_main` (at `a = M₁/(8πV)`, `D = 0`) followed by the
pair count `S² − S ≤ Pc` and the mass hierarchy `M₁ ≤ M₂`. -/
lemma a0MainLocBox_le_counts {V μ M1 M2 S Pc : ℝ} (hV : 0 < V) (hμ : 0 ≤ μ) (hM1 : 0 ≤ M1)
    (hM2 : M1 ≤ M2) (hPc : 0 ≤ Pc) (hcS2 : S ^ 2 - S ≤ Pc) :
    a0MainLocBox V μ M1 S ≤ (1 / 2) * (M2 / V ^ 2) * Pc - μ * (M1 / V) * S := by
  have hinv : 0 ≤ V⁻¹ := inv_nonneg.mpr hV.le
  set a : ℝ := M1 / (8 * π * V) with hadef
  have ha : 0 ≤ a := by rw [hadef]; exact div_nonneg hM1 (by positivity)
  -- the `A₀`-algebra floor at the box density
  have hA := Submission.BoseGases.a0_form_ge_fs_main V S μ a 0 hV hμ ha
  have h8 : 8 * π * a * V = M1 := by rw [hadef]; field_simp
  have h8' : 8 * π * a = M1 / V := by rw [hadef]; field_simp
  have h4 : 4 * π * a = M1 / (2 * V) := by rw [hadef] <;> field_simp <;> ring
  have h2 : 2 * π * a * V⁻¹ = M1 / (4 * V ^ 2) := by rw [hadef] <;> field_simp <;> ring
  -- `a0MainLocBox` is *exactly* the left-hand side of `hA`
  have hAid : a0MainLocBox V μ M1 S
      = (1 / 4) * (S * V⁻¹ - μ) ^ 2 * (8 * π * a * V)
        - (1 / 2) * μ ^ 2 * (8 * π * a * V)
        - 4 * π * a * (2 * (S * V⁻¹) + μ)
        - 2 * π * a * V⁻¹
        + (1 / 2) * V⁻¹ * 0 * (S ^ 2 - S) := by
    unfold a0MainLocBox
    rw [h8, h4, h2]
    field_simp
    ring
  -- drop the nonnegative CS-slack `−¼(μ−S/V−1/V)²M₁`
  have hdrop : 0 ≤ (1 / 4) * (μ - S * V⁻¹ - V⁻¹) ^ 2 * M1 :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hM1
  have hAbase : a0MainLocBox V μ M1 S
      ≤ (1 / 2) * V⁻¹ * V⁻¹ * M1 * (S ^ 2 - S) - μ * V⁻¹ * M1 * S := by
    have h1 : (1 / 2) * V⁻¹ * (8 * π * a) * (S ^ 2 - S)
        = (1 / 2) * V⁻¹ * V⁻¹ * M1 * (S ^ 2 - S) := by
      rw [h8'] <;> field_simp <;> ring
    have h2' : 8 * π * a * μ * S = μ * V⁻¹ * M1 * S := by
      rw [h8'] <;> field_simp <;> ring
    have h3 : (1 / 4) * (μ - S * V⁻¹ - V⁻¹) ^ 2 * (8 * π * a * V)
        = (1 / 4) * (μ - S * V⁻¹ - V⁻¹) ^ 2 * M1 := by rw [h8]
    have h0 : (1 / 2) * V⁻¹ * 0 * (S ^ 2 - S) = 0 := by ring
    linarith [hA, hAid, hdrop, h1.le, h1.ge, h2'.le, h2'.ge, h3.le, h3.ge, h0.le, h0.ge]
  -- the pair count and the mass hierarchy
  have hcoef2 : 0 ≤ (1 / 2) * V⁻¹ * V⁻¹ :=
    mul_nonneg (mul_nonneg (by norm_num) hinv) hinv
  have hcoef : 0 ≤ (1 / 2) * V⁻¹ * V⁻¹ * M1 := mul_nonneg hcoef2 hM1
  have hpair : (1 / 2) * V⁻¹ * V⁻¹ * M1 * (S ^ 2 - S) ≤ (1 / 2) * V⁻¹ * V⁻¹ * M1 * Pc :=
    mul_le_mul_of_nonneg_left hcS2 hcoef
  have h12 : (1 / 2) * V⁻¹ * V⁻¹ * M1 ≤ (1 / 2) * V⁻¹ * V⁻¹ * M2 :=
    mul_le_mul_of_nonneg_left hM2 hcoef2
  have hpair2 : (1 / 2) * V⁻¹ * V⁻¹ * M1 * Pc ≤ (1 / 2) * V⁻¹ * V⁻¹ * M2 * Pc :=
    mul_le_mul_of_nonneg_right h12 hPc
  have hshape : (1 / 2) * V⁻¹ * V⁻¹ * M2 * Pc = (1 / 2) * (M2 / V ^ 2) * Pc := by
    field_simp <;> ring
  have hshape2 : μ * V⁻¹ * M1 * S = μ * (M1 / V) * S := by field_simp <;> ring
  linarith [hAbase, hpair, hpair2, hshape.le, hshape.ge, hshape2.le, hshape2.ge]

theorem boxQ0_ge_a0MainBox {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw2i : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        w2 p.1 p.2) ((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))).restrict (A ×ˢ A)))
    (hfib : MeasureTheory.IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre ℓ w1 z) A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hμ : 0 ≤ μ)
    (hM1nn : 0 ≤ Work.BoseFixB1S.boxM1 ℓ A w1)
    (hM2 : Work.BoseFixB1S.boxM1 ℓ A w1 ≤ Work.BoseFixB1S.boxM2 volA A w2)
    (hPcnn : 0 ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ)
    (hcS2 : Work.BoseFixB1S.boxFlatCount volA ℓ A Φ * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ) :
    Work.BoseFixB1.a0MainLocBox volA μ (Work.BoseFixB1S.boxM1 ℓ A w1)
        (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ)
      ≤ Work.BoseFixB1S.boxQ0 volA ℓ μ A w1 w2 Φ := by
  -- the exact value of the box-projected condensate word
  have hQ0 := boxQ0_value (N := N) (ℓ := ℓ) (volA := volA) (μ := μ) (A := A)
    (w1 := w1) (w2 := w2) (Φ := Φ) hℓ hvol hA hvolA hAc hw2i hfib hΦc
  -- the condensate-pair comparison in the `S ^ 2` shape
  have hcS2' : Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ^ 2
      - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
    simpa only [sq] using hcS2
  -- the pure-real `A₀` core at the box parameters
  have hcore := a0MainLocBox_le_counts (V := volA) (μ := μ)
    (M1 := Work.BoseFixB1S.boxM1 ℓ A w1) (M2 := Work.BoseFixB1S.boxM2 volA A w2)
    (S := Work.BoseFixB1S.boxFlatCount volA ℓ A Φ)
    (Pc := Work.BoseFixB1S.boxPairCount volA ℓ A Φ) hvol hμ hM1nn hM2 hPcnn hcS2'
  linarith [hcore, hQ0]

end Work.BoseFixB1
