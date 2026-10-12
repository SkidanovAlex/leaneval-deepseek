import ChallengeDeps
import Submission.Work.BoseFixB1S.mfRows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal
open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-!
# `Work.BoseFixB1S.mfPairBoxWBoundB1` — the uniform pointwise bound on the localised pair kernel

The sliding pair kernel is
`boxW h μ u x y = w_{B(u)}(v)(x,y) = χ_{B(u)}(x)·W(x−y)·χ_{B(u)}(y)` with
`W = v/((χ_M⋆χ_M)(·/(ℓd))·(χ⋆χ)(·/ℓ))` (`Submission.BoseGases.wSmallPair`).  Under the
regime `R ≤ ℓd/16` (the numerator `v` vanishes outside `ball 0 R`, and
`smallConvLower M ≤ (χ_M⋆χ_M)(·/(ℓd))` on the polydisc `|z_j| ≤ 1/16`) and
`R ≤ ℓ·chiR0` (which gives `|(χ⋆χ)(·/ℓ)⁻¹| ≤ 2` on `ball 0 R`), the kernel admits the
`μ`-independent bound

    |boxW h μ u x y| ≤ chiSupAbs² · chiSmallDecay M² · 2·Bv/smallConvLower M ,

with `M = (paramsAt μ (a v)).M = mValue = 48` a *fixed* integer, so the right-hand side is an
absolute constant (in particular independent of `μ`, `u`, `x`, `y`).  This is the `v`-numerator
analogue of `Work.SmallBoxSliding.abs_wSmall1Pair_le` (which is the `g₀ = v(1−ω)` numerator);
the only new input is that the topological-support hypothesis on `v` makes the numerator vanish
outside `ball 0 R`.

The proof is the pointwise chain: bound both cutoff factors by `chiSupAbs·chiSmallDecay M`
(`abs_chiSmallB_le` + `chiSmall_decay_coord_le_decay`), and the renormalised fibre quotient by
`2·(Bv/smallConvLower M)` (`abs_wSmallScaled_le` for the `(χ_M⋆χ_M)` denominator, which is
legitimate on the support of the numerator because `R ≤ ℓd/16`, and
`abs_inv_convScale_le_two` for the `(χ⋆χ)` denominator).
-/

/-- A function whose topological support lies in `ball 0 R` vanishes at every point of norm
`≥ R`. -/
theorem mfPair_eq_zero_of_R_le_norm {f : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hfsupp : tsupport f ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {z : EuclideanSpace ℝ (Fin 3)} (hz : R ≤ ‖z‖) : f z = 0 := by
  by_contra hne
  have hzmem : z ∈ tsupport f := subset_closure (by simpa [Function.mem_support] using hne)
  have hball := hfsupp hzmem
  rw [Metric.mem_ball, dist_zero_right] at hball
  exact absurd hball (not_lt.mpr hz)

/-- **Uniform pointwise bound on the localised pair kernel** with an arbitrary numerator `f`
supported in `ball 0 R`: in the regime `R ≤ ℓd/16`, `R ≤ ℓ·chiR0` one has

    |wSmallPair M ℓ d u f x y| ≤
      (chiSupAbs·chiSmallDecay M)·(2·(Bv/smallConvLower M))·(chiSupAbs·chiSmallDecay M)

for every `u`, `x`, `y`. -/
theorem abs_wSmallPair_le_const {M : ℕ} (hM : 1 ≤ M) {ℓ d R Bv : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → f z = 0)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hfb : ∀ z : EuclideanSpace ℝ (Fin 3), |f z| ≤ Bv) (hBv : 0 ≤ Bv)
    (u x y : EuclideanSpace ℝ (Fin 3)) :
    |Submission.BoseGases.wSmallPair M ℓ d u f x y| ≤
      (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        * (2 * (Bv / Work.SmallBoxSliding.smallConvLower M))
        * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) := by
  have hcpos : 0 < ℓ * d := mul_pos hℓ hd
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hSnn : 0 ≤ Work.SmallBoxSliding.smallConvLower M := le_of_lt hSpos
  have hCSnn : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
  have hCDnn : 0 ≤ Submission.BoseGases.chiSmallDecay M :=
    Submission.BoseGases.chiSmallDecay_nonneg M
  -- the two cutoff factors
  have hx : |Submission.BoseGases.chiSmallB M ℓ d u x| ≤
      Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
    refine le_trans (Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u x) ?_
    have hb : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
        ≤ Submission.BoseGases.chiSmallDecay M := by
      have h' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • x - u)
      rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at h'
    exact mul_le_mul_of_nonneg_left hb Submission.BoseGases.chiSupAbs_nonneg
  have hy : |Submission.BoseGases.chiSmallB M ℓ d u y| ≤
      Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
    refine le_trans (Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u y) ?_
    have hb : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)
        ≤ Submission.BoseGases.chiSmallDecay M := by
      have h' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • y - u)
      rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at h'
    exact mul_le_mul_of_nonneg_left hb Submission.BoseGases.chiSupAbs_nonneg
  -- the renormalised fibre quotient
  have hmid : |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)
        / Submission.BoseGases.convScale ℓ (x - y)| ≤
      2 * (Bv / Work.SmallBoxSliding.smallConvLower M) := by
    by_cases hnorm : ‖x - y‖ ≤ R
    · have h1 : |(Submission.BoseGases.convScale ℓ (x - y))⁻¹| ≤ 2 :=
        Submission.BoseGases.abs_inv_convScale_le_two hℓ hRχ hnorm
      have h2 : |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)| ≤
          Bv / Work.SmallBoxSliding.smallConvLower M := by
        refine le_trans (Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R)
          hM hcpos hfsupp hR (x - y)) ?_
        exact div_le_div_of_nonneg_right (hfb (x - y)) hSnn
      rw [div_eq_mul_inv, abs_mul]
      calc |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)|
              * |(Submission.BoseGases.convScale ℓ (x - y))⁻¹|
          ≤ (Bv / Work.SmallBoxSliding.smallConvLower M) * 2 :=
            mul_le_mul h2 h1 (abs_nonneg _) (div_nonneg hBv hSnn)
        _ = 2 * (Bv / Work.SmallBoxSliding.smallConvLower M) := by ring
    · have hz0 : f (x - y) = 0 := hfsupp (x - y) (le_of_lt (lt_of_not_ge hnorm))
      have hw0 : Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y) = 0 := by
        dsimp [Submission.BoseGases.wSmallScaled]
        rw [hz0]
        ring
      rw [hw0, zero_div, abs_zero]
      exact mul_nonneg (by norm_num) (div_nonneg hBv hSnn)
  have hA0 : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg hCSnn hCDnn
  have hm0 : 0 ≤ 2 * (Bv / Work.SmallBoxSliding.smallConvLower M) :=
    mul_nonneg (by norm_num) (div_nonneg hBv hSnn)
  calc |Submission.BoseGases.wSmallPair M ℓ d u f x y|
      = |Submission.BoseGases.chiSmallB M ℓ d u x|
          * |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)
              / Submission.BoseGases.convScale ℓ (x - y)|
          * |Submission.BoseGases.chiSmallB M ℓ d u y| := by
        unfold Submission.BoseGases.wSmallPair
        rw [abs_mul, abs_mul]
    _ ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * (2 * (Bv / Work.SmallBoxSliding.smallConvLower M))
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) :=
        mul_le_mul (mul_le_mul hx hmid (abs_nonneg _) hA0) hy (abs_nonneg _) (mul_nonneg hA0 hm0)

theorem mfPairBoxWBoundB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {Bv : ℝ}
    (hvb : ∀ y : EuclideanSpace ℝ (Fin 3), |v y| ≤ Bv) (hBv : 0 ≤ Bv) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧
      ∀ (μ : ℝ) (_hμ : 0 ≤ μ)
        (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
        (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
        (u x y : EuclideanSpace ℝ (Fin 3)),
        |Work.BoseFixB1S.boxW h μ u x y| ≤ Cw := by
  refine ⟨(Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue)
      * (2 * (Bv / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue))
      * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue),
    ?_, ?_⟩
  · have h1 : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay
        Work.BoseBox.mValue :=
      mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
        (Submission.BoseGases.chiSmallDecay_nonneg Work.BoseBox.mValue)
    have h2 : 0 ≤ 2 * (Bv / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue) :=
      mul_nonneg (by norm_num)
        (div_nonneg hBv (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos Work.BoseBox.mValue)))
    exact mul_nonneg (mul_nonneg h1 h2) h1
  · intro μ _hμ hℓ hd hR16 hRχ u x y
    have hvsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → v z = 0 :=
      fun z hz => mfPair_eq_zero_of_R_le_norm hv_supp hz
    have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
      norm_num [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
    have hMain := abs_wSmallPair_le_const (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
      hM hℓ hd hvsupp hR16 hRχ hvb hBv u x y
    have hMv : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M = Work.BoseBox.mValue := rfl
    simp only [Work.BoseFixB1S.boxW]
    rw [hMv] at hMain ⊢
    exact hMain

end

end Work.BoseFixB1S
