import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.w2_sub_w1_pointwise
import Submission.Work.BoseFixB1S.csBoxMeasBdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.bandPairLe` — `w₂ ≤ w` pointwise (first piece of the pair half)

FS's splitting `w = w₁ + ω w` (`eq:potsplit`, `ω ∈ [0,1]`) has the pointwise consequence
`w₂ = w(1 − ω²) ≤ w`, i.e. for the corpus's localised kernels

    w₂ := wSmallPair M ℓ d u (g₂ v h) ≤ wSmallPair M ℓ d u v =: w     (pointwise in `(x,y)`),

whenever `0 ≤ v`.  This is what lets the *flat pair credit* be read off the manifest pair term:
with `Pᵢ = boxPInd volA A i`,

    Σ_{i<j}∫(PᵢPⱼΦ)²w₂ ≤ Σ_{i<j}∫(PᵢPⱼΦ)²w ,

and the left side is the corpus's `(∬w₂/V²)·Pc` (`boxPIndPairFactor`), i.e. the credit
`½(M₂/V²)·boxPairCount` used in step (H5) of `FINDING_bandCondensedArm.md`.

The proof is the unfolding `wSmallPair_eq_chi_mul` (which exhibits both kernels as
`χ_B(x)·(h(x−y)/D)·χ_B(y)` with the *same* positive denominator `D = convScaleSmall·convScale`),
the pointwise `g₂ ≤ v` (`g₂ = v(1−ω₀)(1+ω₀) = v(1−ω₀²) ≤ v` for `v ≥ 0`), and monotonicity of
multiplication by the nonnegative factors `χ_B(x)`, `χ_B(y)`.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1B

/-- **`g₂ ≤ v` pointwise** for `v ≥ 0`: `g₂ = v(1−ω₀)(1+ω₀) = v(1−ω₀²) ≤ v`. -/
theorem g2_le_self {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.g2 v h z ≤ v z := by
  have hvz : 0 ≤ v z := hv z
  have hsq : 0 ≤ (Classical.choose h z) ^ 2 := sq_nonneg _
  have hfac : Submission.BoseGases.g2 v h z
      = v z * (1 - (Classical.choose h z) ^ 2) := by
    simp only [Submission.BoseGases.g2, Submission.BoseGases.g0]
    ring
  rw [hfac]
  nlinarith [hvz, hsq]

/-- **`w₂ ≤ w` pointwise.**  The two localised kernels share the denominator
`D = convScaleSmall M (ℓd)(x−y) · convScale ℓ (x−y) ≥ 0` and the χ-factors, so the comparison is
the pointwise numerator comparison `g₂ ≤ v` of `g2_le_self`. -/
theorem wSmallPair_g2_le_v {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (M : ℕ) (ℓ d : ℝ)
    (u x y : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) x y
      ≤ Submission.BoseGases.wSmallPair M ℓ d u v x y := by
  rw [Work.BoseFixB1.wSmallPair_eq_chi_mul M ℓ d u x y (Submission.BoseGases.g2 v h),
    Work.BoseFixB1.wSmallPair_eq_chi_mul M ℓ d u x y v]
  have hχx : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hχy : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u y :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u y
  have hD : 0 ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
      * Submission.BoseGases.convScale ℓ (x - y) :=
    mul_nonneg (Work.SmallBoxSliding.convScaleSmall_nonneg M (ℓ * d) (x - y))
      (Submission.BoseGases.convScale_nonneg ℓ (x - y))
  have hdiv : Submission.BoseGases.g2 v h (x - y)
        / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
            * Submission.BoseGases.convScale ℓ (x - y))
      ≤ v (x - y)
        / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
            * Submission.BoseGases.convScale ℓ (x - y)) :=
    div_le_div_of_nonneg_right (g2_le_self h hv (x - y)) hD
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdiv hχx) hχy

/-! ## The per-pair arithmetic of the pair-half Cauchy–Schwarz

For one ordered pair `p`, write `A = ∫(PₚΦ)²w`, `B = ∫(PₚΦ)((1−Pₚ)Φ)w`, `C = ∫((1−Pₚ)Φ)²w`
(so that `∫Φ²w = A + 2B + C` by the pointwise expansion of `Φ²`).  The single per-pair
Cauchy–Schwarz `B² ≤ A·C` (with `A, C ≥ 0`) then gives `∫Φ²w ≥ A/2 − 2C`, and summing over the
pairs turns the flat pair credit `Cr = Σ_p A_p` against the excited pair mass `Ex = Σ_p C_p`:

    pairSum ≥ Cr/2 − 2·Ex .

This lemma is that arithmetic step, isolated (no measure theory). -/
theorem pairSplit_arith {A B C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hcs : B ^ 2 ≤ A * C) :
    A / 2 - 2 * C ≤ A + 2 * B + C := by
  nlinarith [hA, hC, hcs, sq_nonneg (B + A / 2), sq_nonneg (B - 2 * C),
    mul_nonneg hA hC]

/-! ## The exact pair bookkeeping `∫(P + Q)²w = A + 2B + C`

The second measure-theoretic input of the pair half: for a state written as
`Φ = P + Q` (in the application `P = P_{p.1}P_{p.2}Φ` and `Q = Φ − P_{p.1}P_{p.2}Φ`) and a kernel
weight `w ≥ 0`,

    A := ∫ P²w ,   B := ∫ P·Q·w ,   C := ∫ Q²w ,
    ∫ (P + Q)²w = A + 2B + C .

This is the pointwise expansion `(P+Q)²w = P²w + 2PQw + Q²w` plus linearity of the integral; the
only care needed is integrability: `B`'s integrand is *not* assumed, it is derived from the
`L¹`-hypotheses on `P²w` and `Q²w` by the AM–GM bound `|PQ| ≤ (P² + Q²)/2` (with `w ≥ 0`) and
`MeasureTheory.Integrable.mono'`, exactly as in the corpus's `Work.BoseFixB1S.csBoxMeasBdd`
style.  Linearists should note that the `rw`-matching of the applied `integral_add` /
`integral_const_mul` lemmas against the unfolded integrand is unreliable (the lemmas carry
lambda-forms), so the steps are taken with `calc` and `congrArg` — the same trap recorded in
`Submission/Work/BoseFixB1B/FINDING_bandCondensedArm.md`. -/
theorem integral_sq_mul_eq {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {P Q w : α → ℝ} (hPm : MeasureTheory.AEStronglyMeasurable P μ)
    (hQm : MeasureTheory.AEStronglyMeasurable Q μ)
    (hwm : MeasureTheory.AEStronglyMeasurable w μ)
    (hw : 0 ≤ w)
    (hP : MeasureTheory.Integrable (fun x => (P x) ^ 2 * w x) μ)
    (hQ : MeasureTheory.Integrable (fun x => (Q x) ^ 2 * w x) μ) :
    (∫ x, (P x + Q x) ^ 2 * w x ∂μ)
      = (∫ x, (P x) ^ 2 * w x ∂μ) + 2 * (∫ x, P x * Q x * w x ∂μ)
        + (∫ x, (Q x) ^ 2 * w x ∂μ) := by
  have hPQ : MeasureTheory.Integrable (fun x => P x * Q x * w x) μ := by
    refine MeasureTheory.Integrable.mono' ((hP.add hQ).const_mul (1 / 2)) ?_ ?_
    · exact (hPm.mul hQm).mul hwm
    · filter_upwards with x
      have h1 : |P x| * |Q x| ≤ ((P x) ^ 2 + (Q x) ^ 2) / 2 := by
        nlinarith [sq_nonneg (|P x| - |Q x|), sq_abs (P x), sq_abs (Q x)]
      calc ‖P x * Q x * w x‖ = |P x * Q x| * w x := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw x)]
        _ = |P x| * |Q x| * w x := by rw [abs_mul]
        _ ≤ (((P x) ^ 2 + (Q x) ^ 2) / 2) * w x := mul_le_mul_of_nonneg_right h1 (hw x)
        _ = (1 / 2) * ((P x) ^ 2 * w x + (Q x) ^ 2 * w x) := by ring
  have h2 : MeasureTheory.Integrable (fun x => 2 * (P x * Q x * w x)) μ := hPQ.const_mul 2
  have hsum : MeasureTheory.Integrable
      (fun x => (P x) ^ 2 * w x + 2 * (P x * Q x * w x)) μ := hP.add h2
  have hpt : (fun x => (P x + Q x) ^ 2 * w x)
      = fun x => (P x) ^ 2 * w x + 2 * (P x * Q x * w x) + (Q x) ^ 2 * w x := by
    funext x; ring
  calc (∫ x, (P x + Q x) ^ 2 * w x ∂μ)
      = ∫ x, (P x) ^ 2 * w x + 2 * (P x * Q x * w x) + (Q x) ^ 2 * w x ∂μ := by rw [hpt]
    _ = (∫ x, (P x) ^ 2 * w x + 2 * (P x * Q x * w x) ∂μ) + (∫ x, (Q x) ^ 2 * w x ∂μ) :=
        MeasureTheory.integral_add hsum hQ
    _ = ((∫ x, (P x) ^ 2 * w x ∂μ) + (∫ x, 2 * (P x * Q x * w x) ∂μ))
          + (∫ x, (Q x) ^ 2 * w x ∂μ) :=
        congrArg (fun t => t + (∫ x, (Q x) ^ 2 * w x ∂μ)) (MeasureTheory.integral_add hP h2)
    _ = ((∫ x, (P x) ^ 2 * w x ∂μ) + 2 * (∫ x, P x * Q x * w x ∂μ))
          + (∫ x, (Q x) ^ 2 * w x ∂μ) :=
        congrArg (fun t => ((∫ x, (P x) ^ 2 * w x ∂μ) + t) + (∫ x, (Q x) ^ 2 * w x ∂μ))
          (MeasureTheory.integral_const_mul (2 : ℝ) (fun x => P x * Q x * w x))
    _ = (∫ x, (P x) ^ 2 * w x ∂μ) + 2 * (∫ x, P x * Q x * w x ∂μ)
          + (∫ x, (Q x) ^ 2 * w x ∂μ) := by ring

/-! ## The per-pair weighted Cauchy–Schwarz on the box

The third measure-theoretic input of the pair half: for functions `P`, `Q` and a nonnegative weight
`w` on the centred box, all bounded there,

    (∫_{abox} P·Q·w)² ≤ (∫_{abox} P²w)·(∫_{abox} Q²w) .

It is the corpus's box Cauchy–Schwarz `Work.BoseFixB1S.csBoxMeasBdd` applied to the two functions
`P·√w` and `Q·√w` (so that the two "norms" are `∫P²w`, `∫Q²w`), with the weight's square root
removed by `Real.sq_sqrt`.  In the application `P = boxPInd volA A p.1 (boxPInd volA A p.2 Φ)`,
`Q = Φ − P`, `w = wSmallPair M ℓ d u v` (bounded on `abox` by the band sup bound
`bandS²·sup|W^s|`), this is the `B² ≤ A·C` that `pairSplit_arith` consumes. -/
theorem weighted_cs_abox {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {P Q w : Submission.BoseGases.X N → ℝ}
    (hPm : Measurable P) (hQm : Measurable Q) (hwm : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x)
    {CP CQ Cw : ℝ} (hCP : 0 ≤ CP) (hCQ : 0 ≤ CQ)
    (hPb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |P x| ≤ CP)
    (hQb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Q x| ≤ CQ)
    (hwb : ∀ x ∈ Submission.BoseGases.abox N ℓ, w x ≤ Cw) :
    (∫ x in Submission.BoseGases.abox N ℓ, P x * Q x * w x) ^ 2
      ≤ (∫ x in Submission.BoseGases.abox N ℓ, (P x) ^ 2 * w x)
        * (∫ x in Submission.BoseGases.abox N ℓ, (Q x) ^ 2 * w x) := by
  have hfm : Measurable (fun x : Submission.BoseGases.X N => P x * Real.sqrt (w x)) :=
    hPm.mul hwm.sqrt
  have hgm : Measurable (fun x : Submission.BoseGases.X N => Q x * Real.sqrt (w x)) :=
    hQm.mul hwm.sqrt
  have hfb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |P x * Real.sqrt (w x)| ≤ CP * Real.sqrt Cw := by
    intro x hx
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul (hPb x hx) (Real.sqrt_le_sqrt (hwb x hx)) (Real.sqrt_nonneg _) hCP
  have hgb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Q x * Real.sqrt (w x)| ≤ CQ * Real.sqrt Cw := by
    intro x hx
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul (hQb x hx) (Real.sqrt_le_sqrt (hwb x hx)) (Real.sqrt_nonneg _) hCQ
  have hcs := Work.BoseFixB1S.csBoxMeasBdd (N := N) (ℓ := ℓ) hℓ hfm hgm hfb hgb
  have h1 : (∫ x in Submission.BoseGases.abox N ℓ, P x * Q x * w x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (P x * Real.sqrt (w x)) * (Q x * Real.sqrt (w x)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show P x * Q x * w x = P x * Real.sqrt (w x) * (Q x * Real.sqrt (w x))
    conv_lhs => rw [← Real.sq_sqrt (hw0 x)]
    ring
  have h2 : (∫ x in Submission.BoseGases.abox N ℓ, (P x * Real.sqrt (w x)) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ, (P x) ^ 2 * w x := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (P x * Real.sqrt (w x)) ^ 2 = (P x) ^ 2 * w x
    rw [mul_pow, Real.sq_sqrt (hw0 x)]
  have h3 : (∫ x in Submission.BoseGases.abox N ℓ, (Q x * Real.sqrt (w x)) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ, (Q x) ^ 2 * w x := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (Q x * Real.sqrt (w x)) ^ 2 = (Q x) ^ 2 * w x
    rw [mul_pow, Real.sq_sqrt (hw0 x)]
  calc (∫ x in Submission.BoseGases.abox N ℓ, P x * Q x * w x) ^ 2
      = (∫ x in Submission.BoseGases.abox N ℓ,
          (P x * Real.sqrt (w x)) * (Q x * Real.sqrt (w x))) ^ 2 := by rw [h1]
    _ ≤ (∫ x in Submission.BoseGases.abox N ℓ, (P x * Real.sqrt (w x)) ^ 2)
          * (∫ x in Submission.BoseGases.abox N ℓ, (Q x * Real.sqrt (w x)) ^ 2) := hcs
    _ = (∫ x in Submission.BoseGases.abox N ℓ, (P x) ^ 2 * w x)
          * (∫ x in Submission.BoseGases.abox N ℓ, (Q x) ^ 2 * w x) := by rw [h2, h3]

end Work.BoseFixB1B
