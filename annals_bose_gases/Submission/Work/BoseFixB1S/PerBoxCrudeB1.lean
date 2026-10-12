import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

/-- **The localised pair kernel is nonnegative.**

`wSmallPair M ℓ d u v x y = χ_{B(u)}(x) · (v(x−y) / ((χ_M ⋆ χ_M)((x−y)/(ℓd)) · (χ ⋆ χ)((x−y)/ℓ)))
· χ_{B(u)}(y)`, each factor of which is `≥ 0`: the two cut-offs (`chiSmallB_nonneg`), the numerator
(`0 ≤ v`), and the two convolution denominators (`conv3Small` and `convScale` are integrals of
non-negative integrands).  Lean's `x / 0 = 0` convention covers vanishing-denominator points. -/
lemma wSmallPair_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v) (M : ℕ) (ℓ d : ℝ)
    (u x y : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Submission.BoseGases.wSmallPair M ℓ d u v x y := by
  rw [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled,
    Submission.BoseGases.convScaleSmall]
  refine mul_nonneg
    (mul_nonneg (Submission.BoseGases.chiSmallB_nonneg M ℓ d u x) ?_)
    (Submission.BoseGases.chiSmallB_nonneg M ℓ d u y)
  refine div_nonneg (div_nonneg (hv _) ?_) (Submission.BoseGases.convScale_nonneg ℓ _)
  rw [Submission.BoseGases.conv3Small]
  exact integral_nonneg fun w =>
    mul_nonneg (Submission.BoseGases.chiSmall_nonneg M w)
      (Submission.BoseGases.chiSmall_nonneg M (_ - w))

/-- The same, in the `∀`-form the pair term consumes. -/
lemma wSmallPair_nonneg_apply {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v) (M : ℕ) (ℓ d : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∀ x y : EuclideanSpace ℝ (Fin 3), 0 ≤ Submission.BoseGases.wSmallPair M ℓ d u v x y :=
  fun x y => wSmallPair_nonneg hv M ℓ d u x y

/-- **The pair part of the localised potential word is non-negative** (P1, consumed form). -/
lemma pairTerm_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v) {M : ℕ} {ℓ d : ℝ}
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ ∑ p ∈ Submission.BoseGases.pairSet n,
        ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2) := by
  refine Finset.sum_nonneg fun p _ => integral_nonneg fun x => ?_
  exact mul_nonneg (sq_nonneg _) (wSmallPair_nonneg hv M ℓ d u (x p.1) (x p.2))

/-- **The arithmetic core of the reduction** (machine-checked, sorry-free).

At the numbers attached to a fixed `(μ, n, Φ, u)` (`t` is the *actual fibre loss*
`Σ_i ∫Φ²·(∫_y wSmall1Pair(x_i,y)dy)/μ`-scaled, i.e. the loss is `μ t`; `pair` is the *pair term*
`Σ_{i<j}∫Φ²w(x_i,x_j)`; `kin` is the spectral kinetic `tBwordKinInd`; `nps` is the excited count
`cnPlusBoxInd`; `gap` is the sliding gap coefficient `tbGapCoeff (ℓd) ε_T`):

* `hword` — `sbWord ≥ gap·n₊ + kin + ½·pair − μ·t` (the word's decomposition, using the localised
  potential word's split `qLHSwordB = −(the loss) + (the pair term)`);
* `hpay` — (PAY): `μ t ≤ ½·pair + kin + K μ (a v) n₊ + C(μ²(a v)V + μ(a v))‖Φ‖²`
  — the *same* coefficients `½` and `1` as in `hword`, and the *free* `K` only in the `n₊`-slot;
* `hgap` — the gap absorption `K μ (a v) ≤ gap` (i.e. `ε₀` small enough that the sliding gap
  coefficient `tbGapCoeff (ℓd) ε_T = ½ε_T(1+π⁻²)⁻¹(ℓd)⁻²` beats the *fixed* `K μ (a v)`; the ratio
  `tbGapCoeff/(μ(a v)) = ε_T/(2(1+π⁻²)(ℓd)²μ(a v)) = t^{−13/1292}/(2(1+π⁻²)) → ∞`, `t = μ(a v)³`).

Conclusion: the crude bound `−(C (μ²(a v)V + μ (a v)))‖Φ‖² ≤ sbWord` — exactly the target. -/
lemma perBoxCrudeB1_arith {sw pair kin gap nps t μ a V M K C : ℝ}
    (hnps : 0 ≤ nps)
    (hword : gap * nps + kin + (1 / 2) * pair - μ * t ≤ sw)
    (hpay : μ * t ≤ (1 / 2) * pair + kin + K * (μ * a) * nps
      + C * (μ ^ 2 * a * V + μ * a) * M)
    (hgap : K * (μ * a) ≤ gap) :
    -(C * (μ ^ 2 * a * V + μ * a)) * M ≤ sw := by
  have hkey : (gap - K * (μ * a)) * nps - C * (μ ^ 2 * a * V + μ * a) * M ≤ sw := by
    nlinarith [hword, hpay]
  have hnn : 0 ≤ (gap - K * (μ * a)) * nps := mul_nonneg (by linarith) hnps
  linarith [hkey, hnn]

/-- **The localised fibre loss** at FS's parameters:
`Σ_i ∫_{abox n ℓ} Φ² · (∫_y wSmall1Pair h M ℓ d u (x i) y dy)` — the `μ`-linear part of the localised
potential word, whose absolute value the fibre bound dominates by `K (a v) Σ_i ∫Φ²χ_{B(u)}(x_i)`. -/
noncomputable def fibLoss {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ i : Fin n,
    ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ x) ^ 2 *
        (∫ y in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          Submission.BoseGases.wSmall1Pair h
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (x i) y)

/-- **The localised pair term** at FS's parameters:
`Σ_{i<j} ∫_{abox n ℓ} Φ² wSmallPair M ℓ d u v (x i) (x j)` — the two-body part of the localised
potential word (non-negative by `pairTerm_nonneg`). -/
noncomputable def pairTermB {v : EuclideanSpace ℝ (Fin 3) → ℝ} (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n,
    ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ x) ^ 2 * Submission.BoseGases.wSmallPair
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v (x p.1) (x p.2)

theorem PerBoxCrudeB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          -(C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                + μ * (_root_.BoseGases.a v)))
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by sorry

end Work.BoseFixB1S
