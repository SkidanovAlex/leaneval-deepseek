import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.ae_wSmall1Pair_le_wSmallPair_g2` — FS `lm:w2>w1`, pointwise form

The localised small-box one-body kernel is dominated pointwise (a.e. in the pair
`(x,y)`) by the localised two-body kernel with FS's numerator
`g₂ = v(1−ω₀)(1+ω₀)` (`ω₀ := Classical.choose h`).

The two kernels share the (everywhere nonnegative) cutoffs and the
(everywhere nonnegative) renormalisation denominators, so the comparison
reduces to the numerator comparison `g₀ ≤ g₂`.  That comparison is FS's
`0 ≤ ω₀ ≤ 1` (`eq:omegabounds`) together with `v ≥ 0`: the excess is

    g₂ − g₀ = g₀·ω₀  ≥ 0     a.e.

(Multiplication of the numerator by the common factor `1/(χ_M⋆χ_M)((x−y)/(ℓd))`
and then by `1/(χ⋆χ)((x−y)/ℓ)` preserves the inequality *because those two
factors are pointwise `≥ 0` — this is why the hypothesis `ψ ≥ 0` of FS's
comparison is not needed and why the statement carries no diluteness
hypothesis on `ℓ, d`.)

Contents (all `sorry`-free):
* `conv3Small_nonneg`, `convScaleSmall_nonneg` — the two `dℓ`-scale
  renormalisation denominators are nonnegative everywhere.
* `ae_g0_le_g2` — `g₀ ≤ g₂` a.e. (`g0_nonneg_ae` + `scattering_bounds_ae`).
* `wSmallPair_mono_of_le` — the pointwise kernel comparison, for an arbitrary
  pair of numerators `f ≤ g`.
* `ae_wSmall1Pair_le_wSmallPair_g2` — the a.e. statement, obtained from
  `ae_g0_le_g2` by taking a measurable null superset of the (not known to be
  measurable) bad set and pulling it back through `(x,y) ↦ x − y`, whose
  `y`-sections are translates.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real BigOperators ENNReal Topology

namespace Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The cosine-`M` self-convolution `(χ_M ⋆ χ_M)` is nonnegative everywhere
(its integrand is a product of two nonnegative factors). -/
lemma conv3Small_nonneg (M : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Submission.BoseGases.conv3Small M x := by
  show 0 ≤ ∫ y : EuclideanSpace ℝ (Fin 3),
    Submission.BoseGases.chiSmall M y * Submission.BoseGases.chiSmall M (x - y)
  exact MeasureTheory.integral_nonneg fun y =>
    mul_nonneg (Submission.BoseGases.chiSmall_nonneg M y)
      (Submission.BoseGases.chiSmall_nonneg M (x - y))

/-- The `dℓ`-scale renormalisation denominator `convScaleSmall M c` is
nonnegative everywhere. -/
lemma convScaleSmall_nonneg (M : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Submission.BoseGases.convScaleSmall M c x := by
  show 0 ≤ ∫ y : EuclideanSpace ℝ (Fin 3),
    Submission.BoseGases.chiSmall M y * Submission.BoseGases.chiSmall M ((c⁻¹ • x) - y)
  exact MeasureTheory.integral_nonneg fun y =>
    mul_nonneg (Submission.BoseGases.chiSmall_nonneg M y)
      (Submission.BoseGases.chiSmall_nonneg M _)

/-- **FS `lm:w2>w1` at the numerator level**: `g₀ ≤ g₂` almost everywhere.

`g₂ − g₀ = g₀·ω₀`: `g₀ ≥ 0` a.e. (`ScatKernelChosen.g0_nonneg_ae`) and
`ω₀ ≥ 0` a.e. (`ScatT3.scattering_bounds_ae`). -/
lemma ae_g0_le_g2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v) :
    ∀ᵐ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.g0 v h z ≤ Submission.BoseGases.g2 v h z := by
  obtain ⟨hrad, hscat⟩ := Classical.choose_spec h
  have hb := Submission.BoseGases.scattering_bounds_ae (w := Classical.choose h)
    hR0 hv hvrad hv_supp hrad hscat
  have hg0 := Submission.BoseGases.g0_nonneg_ae (R := R0) hR0 hv hvrad hv_supp h
  filter_upwards [hg0, hb.1] with z h0 hw
  have heq : Submission.BoseGases.g2 v h z
      = Submission.BoseGases.g0 v h z
        + Submission.BoseGases.g0 v h z * Classical.choose h z := by
    rw [Submission.BoseGases.g2, Submission.BoseGases.g0]
    ring
  rw [heq]
  exact le_add_of_nonneg_right (mul_nonneg h0 hw)

/-- **Pointwise comparison of the localised kernels** at a fixed pair `(x,y)`:
if the two numerators satisfy `f (x−y) ≤ g (x−y)`, then
`w_{B(u)}[f](x,y) ≤ w_{B(u)}[g](x,y)`.

Both kernels factor as
`χ_{B(u)}(x)·(f(x−y)/(χ_M⋆χ_M)((x−y)/(ℓd)))/(χ⋆χ)((x−y)/ℓ)·χ_{B(u)}(y)`;
all four factors `χ_{B(u)}(x)`, `χ_{B(u)}(y)`, `convScaleSmall M (ℓd) (x−y)`,
`convScale ℓ (x−y)` are nonnegative everywhere, so the two divisions
(`div_le_div_of_nonneg_right`, which is valid for a nonnegative denominator
because `_/0 = 0`) preserve the inequality. -/
lemma wSmallPair_mono_of_le {M : ℕ} {ℓ d : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (x y : EuclideanSpace ℝ (Fin 3)) (hxy : f (x - y) ≤ g (x - y)) :
    Submission.BoseGases.wSmallPair M ℓ d u f x y
      ≤ Submission.BoseGases.wSmallPair M ℓ d u g x y := by
  have hD : 0 ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) :=
    convScaleSmall_nonneg M (ℓ * d) (x - y)
  have hC : 0 ≤ Submission.BoseGases.convScale ℓ (x - y) :=
    Submission.BoseGases.convScale_nonneg ℓ (x - y)
  have hA : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hB : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u y :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u y
  have h1 : Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)
      ≤ Submission.BoseGases.wSmallScaled M (ℓ * d) g (x - y) := by
    rw [Submission.BoseGases.wSmallScaled, Submission.BoseGases.wSmallScaled]
    exact div_le_div_of_nonneg_right hxy hD
  have h2 := div_le_div_of_nonneg_right h1 hC
  have h3 := mul_le_mul_of_nonneg_left h2 hA
  have h4 := mul_le_mul_of_nonneg_right h3 hB
  simpa only [Submission.BoseGases.wSmallPair] using h4

theorem ae_wSmall1Pair_le_wSmallPair_g2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) :
    ∀ᵐ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)
      ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))),
      Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2
        ≤ Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2 := by
  -- `g₀ ≤ g₂` a.e. in `z = x − y`
  have hle_ae := ae_g0_le_g2 (R0 := R0) hv_supp hR0 hv hvrad h
  -- at every pair whose difference is a `g₀ ≤ g₂` point, the kernels compare
  have key : ∀ x y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.g0 v h (x - y) ≤ Submission.BoseGases.g2 v h (x - y) →
      Submission.BoseGases.wSmall1Pair h M ℓ d u x y
        ≤ Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) x y := by
    intro x y hxy
    have hxy' : Submission.BoseGases.g0 v h (x - y)
        ≤ Submission.BoseGases.g2 v h (x - y) := hxy
    have h := wSmallPair_mono_of_le (M := M) (ℓ := ℓ) (d := d) (u := u)
      (f := Submission.BoseGases.g0 v h) (g := Submission.BoseGases.g2 v h) x y hxy'
    simpa only [Submission.BoseGases.wSmall1Pair] using h
  rw [MeasureTheory.ae_iff]
  -- a measurable null superset of the (possibly non-measurable) bad set in `z`
  obtain ⟨t, hNt, htmeas, ht0⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp hle_ae)
  -- the bad pairs have `x − y ∈ t`
  have hsub : {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
        ¬ (Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2
          ≤ Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)}
      ⊆ {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) | p.1 - p.2 ∈ t} := by
    intro p hp
    by_contra hpt
    have hz : Submission.BoseGases.g0 v h (p.1 - p.2)
        ≤ Submission.BoseGases.g2 v h (p.1 - p.2) := by
      by_contra hc
      exact hpt (hNt hc)
    exact hp (key p.1 p.2 hz)
  -- and that set is null: its `y`-sections are translates of the null set `t`
  have hS0 : (volume.prod volume) {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
      p.1 - p.2 ∈ t} = 0 := by
    have hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
        p.1 - p.2 ∈ t} := htmeas.preimage (measurable_fst.sub measurable_snd)
    refine (MeasureTheory.Measure.measure_prod_null hmeas).2 ?_
    filter_upwards with x
    have hmp : MeasureTheory.MeasurePreserving
        (fun y : EuclideanSpace ℝ (Fin 3) => x - y) volume volume := by
      have hh := (MeasureTheory.measurePreserving_add_left volume x).comp
        (MeasureTheory.Measure.measurePreserving_neg volume)
      simpa [Function.comp_def, sub_eq_add_neg] using hh
    have hsec : Prod.mk x ⁻¹' {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
          p.1 - p.2 ∈ t} = (fun y : EuclideanSpace ℝ (Fin 3) => x - y) ⁻¹' t := rfl
    rw [hsec, hmp.measure_preimage htmeas.nullMeasurableSet, ht0]
    simp
  exact MeasureTheory.measure_mono_null hsub hS0

end Work.BoseFixB1
