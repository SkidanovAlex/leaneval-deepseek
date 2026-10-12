import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.twoSlotWeightedCS`

The two-slot weighted estimate (the `n = 2` case of the `CS` step of the `BoseFixB3`
block); the statement is the one requested in
`Submission/Work/BoseFixB3/CS/Pieces/DESIGN_ppMass_le_q4mass_cnPlus.md`, §7.0, where the
pointwise identity (★) below is identified as the key tool.

## Mathematics

Everything rests on one pointwise identity.  For reals `w ≥ 0`, `λ > 0` and reals `ω, m, g`:

    (ω m + g)² w + 2λ g² − 2λ m² · ω² w/(w + 2λ)
        = (w + 2λ) · (g + w ω m/(w + 2λ))²                                (★)

The right-hand side is `(w + 2λ) > 0` times a square, hence `≥ 0`; the identity itself is
just `2λ w²/(w + 2λ) = w²(w + 2λ − 2λ)/(w + 2λ) = w² − w·w²/(w + 2λ)` expanded.

Integrating (★) against `μ` — all terms are integrable under the hypotheses, `ω²w/(w+2λ)`
being `(1/2λ)(ω²w − ω²w²/(w+2λ))` — gives, for every `m`,

    2λ m² · ∫ ω²w/(w + 2λ)  ≤  ∫ (ωm + g)² w + 2λ ∫ g²                    (†)

(that is `twoSlotIntegral`).  The hypothesis `hscale` of the target says
`1 ≤ K (∫ω²w − ∫ω²w²/(w+2λ))`, and

    ∫ ω²w − ∫ ω²w²/(w+2λ) = ∫ ω²w (1 − w/(w+2λ)) = 2λ ∫ ω²w/(w+2λ)          (‡)

holds because `w + 2λ > 0` (that is `twoSlotMassIdentity`).  Writing
`E := ∫ ω²w/(w+2λ)`, (‡) and `hscale` give `1 ≤ K·(2λE)` with `2λE > 0`, so
`1/(2λE) ≤ K`; dividing (†) by `2λE` and multiplying the resulting upper bound by
`K ≥ 1/(2λE) ≥ 0` produces the claim

    m² ≤ K (∫ (ωm+g)²w + 2λ∫g²)        for all `m`.

Notably `0 ≤ ω` and `ω ≤ 1` are **not** used: only `0 ≤ w`, `0 < λ` and the four
integrability hypotheses enter.  There is also no measurability or boundedness assumption on
`w`, and no sign condition on `g`.

The three reusable ingredients are stated separately (`twoSlotPointwise` (★),
`twoSlotIntegral` (†), `twoSlotMassIdentity` (‡)); the requested theorem is then a short
assembly.
-/

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory

/-- **The pointwise two-slot identity (★).**  For `w ≥ 0` and `λ > 0`,

`(ω m + g)² w + 2λ g² − 2λ m² ω²w/(w+2λ) = (w + 2λ)·(g + w ω m/(w + 2λ))²`,

so in particular the left-hand side is pointwise non-negative. -/
theorem twoSlotPointwise (ω w g m lam : ℝ) (hw : 0 ≤ w) (hlam : 0 < lam) :
    (ω * m + g) ^ 2 * w + 2 * lam * g ^ 2 - 2 * lam * m ^ 2 * (ω ^ 2 * w / (w + 2 * lam))
      = (w + 2 * lam) * (g + w * (ω * m) / (w + 2 * lam)) ^ 2 := by
  have hne : w + 2 * lam ≠ 0 := by linarith
  field_simp
  ring

/-- **The integrated form (†) of `twoSlotPointwise`:** for every `m : ℝ`,

`2λ m² ∫ ω²w/(w+2λ) ≤ ∫ (ωm + g)² w + 2λ ∫ g²`.

Only `0 ≤ w`, `0 < λ` and the integrability hypotheses are used. -/
theorem twoSlotIntegral {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {ω w g : α → ℝ} {lam : ℝ} (hw0 : ∀ x, 0 ≤ w x) (hlam : 0 < lam)
    (hI1 : MeasureTheory.Integrable (fun x => ω x ^ 2 * w x) μ)
    (hI2 : MeasureTheory.Integrable (fun x => ω x ^ 2 * w x ^ 2 / (w x + 2 * lam)) μ)
    (hI3 : MeasureTheory.Integrable (fun x => g x ^ 2 * (w x + 2 * lam)) μ)
    (hI4 : ∀ m : ℝ, MeasureTheory.Integrable (fun x => (ω x * m + g x) ^ 2 * w x) μ)
    (m : ℝ) :
    2 * lam * m ^ 2 * (∫ x, ω x ^ 2 * w x / (w x + 2 * lam) ∂μ)
      ≤ (∫ x, (ω x * m + g x) ^ 2 * w x ∂μ) + 2 * lam * (∫ x, g x ^ 2 ∂μ) := by
  have hwlam : ∀ x, 0 < w x + 2 * lam := fun x => by linarith [hw0 x, hlam]
  have hIgw : MeasureTheory.Integrable (fun x => g x ^ 2 * w x) μ := by
    simpa using hI4 0
  have hIg2 : MeasureTheory.Integrable (fun x => g x ^ 2) μ := by
    have h2 : MeasureTheory.Integrable
        (fun x => 1 / (2 * lam) * (g x ^ 2 * (w x + 2 * lam) - g x ^ 2 * w x)) μ := by
      simpa only [Pi.sub_apply] using (hI3.sub hIgw).const_mul (1 / (2 * lam))
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    have h' : w x + 2 * lam ≠ 0 := ne_of_gt (hwlam x)
    field_simp
    ring
  have hIdiv : MeasureTheory.Integrable (fun x => ω x ^ 2 * w x / (w x + 2 * lam)) μ := by
    have h2 : MeasureTheory.Integrable
        (fun x => 1 / (2 * lam) * (ω x ^ 2 * w x - ω x ^ 2 * w x ^ 2 / (w x + 2 * lam))) μ := by
      simpa only [Pi.sub_apply] using (hI1.sub hI2).const_mul (1 / (2 * lam))
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    have h' : w x + 2 * lam ≠ 0 := ne_of_gt (hwlam x)
    field_simp
    ring
  have hpt : ∀ x, 0 ≤ (ω x * m + g x) ^ 2 * w x + 2 * lam * g x ^ 2
      - 2 * lam * m ^ 2 * (ω x ^ 2 * w x / (w x + 2 * lam)) := by
    intro x
    rw [twoSlotPointwise (ω x) (w x) (g x) m lam (hw0 x) hlam]
    exact mul_nonneg (le_of_lt (hwlam x)) (sq_nonneg _)
  have hnn : 0 ≤ ∫ x, ((ω x * m + g x) ^ 2 * w x + 2 * lam * g x ^ 2
      - 2 * lam * m ^ 2 * (ω x ^ 2 * w x / (w x + 2 * lam))) ∂μ :=
    integral_nonneg (f := fun x => (ω x * m + g x) ^ 2 * w x + 2 * lam * g x ^ 2
      - 2 * lam * m ^ 2 * (ω x ^ 2 * w x / (w x + 2 * lam))) hpt
  have hF : MeasureTheory.Integrable
      (fun x => (ω x * m + g x) ^ 2 * w x + 2 * lam * g x ^ 2) μ :=
    (hI4 m).add (hIg2.const_mul (2 * lam))
  have hG : MeasureTheory.Integrable
      (fun x => 2 * lam * m ^ 2 * (ω x ^ 2 * w x / (w x + 2 * lam))) μ :=
    hIdiv.const_mul (2 * lam * m ^ 2)
  have hsub : ∫ x, ((ω x * m + g x) ^ 2 * w x + 2 * lam * g x ^ 2
        - 2 * lam * m ^ 2 * (ω x ^ 2 * w x / (w x + 2 * lam))) ∂μ
      = (∫ x, (ω x * m + g x) ^ 2 * w x + 2 * lam * g x ^ 2 ∂μ)
        - (∫ x, 2 * lam * m ^ 2 * (ω x ^ 2 * w x / (w x + 2 * lam)) ∂μ) :=
    integral_sub hF hG
  have e1 : (∫ x, (ω x * m + g x) ^ 2 * w x ∂μ) + 2 * lam * (∫ x, g x ^ 2 ∂μ)
      = ∫ x, ((ω x * m + g x) ^ 2 * w x + 2 * lam * g x ^ 2) ∂μ := by
    rw [← integral_const_mul, ← integral_add (hI4 m) (hIg2.const_mul (2 * lam))]
  have e2 : 2 * lam * m ^ 2 * (∫ x, ω x ^ 2 * w x / (w x + 2 * lam) ∂μ)
      = ∫ x, 2 * lam * m ^ 2 * (ω x ^ 2 * w x / (w x + 2 * lam)) ∂μ := by
    rw [← integral_const_mul]
  have hlin : ∫ x, ((ω x * m + g x) ^ 2 * w x + 2 * lam * g x ^ 2
        - 2 * lam * m ^ 2 * (ω x ^ 2 * w x / (w x + 2 * lam))) ∂μ
      = ((∫ x, (ω x * m + g x) ^ 2 * w x ∂μ) + 2 * lam * (∫ x, g x ^ 2 ∂μ))
        - 2 * lam * m ^ 2 * (∫ x, ω x ^ 2 * w x / (w x + 2 * lam) ∂μ) := by
    rw [hsub, ← e1, ← e2]
  linarith

/-- **The algebraic mass identity (‡):** the `hscale` difference is `2λ` times the screened
mass, `∫ω²w − ∫ω²w²/(w+2λ) = 2λ ∫ ω²w/(w+2λ)`. -/
theorem twoSlotMassIdentity {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {ω w : α → ℝ} {lam : ℝ} (hw0 : ∀ x, 0 ≤ w x) (hlam : 0 < lam)
    (hI1 : MeasureTheory.Integrable (fun x => ω x ^ 2 * w x) μ)
    (hI2 : MeasureTheory.Integrable (fun x => ω x ^ 2 * w x ^ 2 / (w x + 2 * lam)) μ) :
    (∫ x, ω x ^ 2 * w x ∂μ) - (∫ x, ω x ^ 2 * w x ^ 2 / (w x + 2 * lam) ∂μ)
      = 2 * lam * (∫ x, ω x ^ 2 * w x / (w x + 2 * lam) ∂μ) := by
  have hwlam : ∀ x, 0 < w x + 2 * lam := fun x => by linarith [hw0 x, hlam]
  have h1 : (∫ x, ω x ^ 2 * w x - ω x ^ 2 * w x ^ 2 / (w x + 2 * lam) ∂μ)
      = ∫ x, 2 * lam * (ω x ^ 2 * w x / (w x + 2 * lam)) ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    have h' : w x + 2 * lam ≠ 0 := ne_of_gt (hwlam x)
    field_simp
    ring
  rwa [integral_sub hI1 hI2, integral_const_mul] at h1

/-- **The requested two-slot weighted estimate.**  With
`a := ∫ω²w`, `d := ∫ω²w²/(w+2λ)`, `E := ∫ω²w/(w+2λ)` and `B(m) := ∫(ωm+g)²w + 2λ∫g²`:
`twoSlotMassIdentity` gives `a − d = 2λE`, so `hscale` reads `1 ≤ K·(2λE)`; since `2λE > 0`
this gives `1/(2λE) ≤ K`, while `twoSlotIntegral` gives `m² ≤ B(m)/(2λE)`; multiplying by
`K ≥ 1/(2λE) ≥ 0` yields `m² ≤ K·B(m)`. -/
theorem twoSlotWeightedCS {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {ω w g : α → ℝ} {lam K : ℝ}
    (hω0 : ∀ x, 0 ≤ ω x) (hω1 : ∀ x, ω x ≤ 1) (hw0 : ∀ x, 0 ≤ w x)
    (hlam : 0 < lam) (hK : 0 ≤ K)
    (hI1 : MeasureTheory.Integrable (fun x => ω x ^ 2 * w x) μ)
    (hI2 : MeasureTheory.Integrable (fun x => ω x ^ 2 * w x ^ 2 / (w x + 2 * lam)) μ)
    (hI3 : MeasureTheory.Integrable (fun x => g x ^ 2 * (w x + 2 * lam)) μ)
    (hI4 : ∀ m : ℝ, MeasureTheory.Integrable (fun x => (ω x * m + g x) ^ 2 * w x) μ)
    (hscale : 1 ≤ K * ((∫ x, ω x ^ 2 * w x ∂μ)
      - (∫ x, ω x ^ 2 * w x ^ 2 / (w x + 2 * lam) ∂μ))) :
    ∀ m : ℝ,
      m ^ 2 ≤ K * ((∫ x, (ω x * m + g x) ^ 2 * w x ∂μ) + 2 * lam * (∫ x, g x ^ 2 ∂μ)) := by
  intro m
  -- `hscale`, rewritten with (‡)
  have hKe : 1 ≤ K * (2 * lam * (∫ x, ω x ^ 2 * w x / (w x + 2 * lam) ∂μ)) := by
    rw [← twoSlotMassIdentity μ hw0 hlam hI1 hI2]
    exact hscale
  -- the screened mass is positive (else `K·(2λE) ≤ 0 < 1`)
  have hepos : 0 < 2 * lam * (∫ x, ω x ^ 2 * w x / (w x + 2 * lam) ∂μ) := by
    by_contra h
    have h' : 2 * lam * (∫ x, ω x ^ 2 * w x / (w x + 2 * lam) ∂μ) ≤ 0 := not_lt.mp h
    have hh := mul_nonpos_of_nonneg_of_nonpos hK h'
    linarith
  have hB : 0 ≤ (∫ x, (ω x * m + g x) ^ 2 * w x ∂μ) + 2 * lam * (∫ x, g x ^ 2 ∂μ) := by
    refine add_nonneg ?_ ?_
    · exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw0 x))
    · exact mul_nonneg (by positivity) (integral_nonneg (fun x => sq_nonneg _))
  -- (†), in the form `m²·(2λE) ≤ B`
  have hslot := twoSlotIntegral μ hw0 hlam hI1 hI2 hI3 hI4 m
  have hstep : m ^ 2 * (2 * lam * (∫ x, ω x ^ 2 * w x / (w x + 2 * lam) ∂μ))
      ≤ (∫ x, (ω x * m + g x) ^ 2 * w x ∂μ) + 2 * lam * (∫ x, g x ^ 2 ∂μ) := by
    linarith
  -- `m² ≤ m²·(K·2λE) ≤ K·B`
  nlinarith [mul_le_mul_of_nonneg_right hstep hK, mul_le_mul_of_nonneg_left hKe (sq_nonneg m)]

end Work.BoseFixB3.CS.Pieces
