import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SboxEB
import Submission.Work.SmallBoxA0.Final
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Infrastructure for `Work.SmallBoxA0.w1_L2_sq_le`

Shared helpers for the bound `‖w₁‖²_{L²(abox 2 s)} ≤ 4·chiSup⁴·s³·∫g₀²`:

* `abox2_measurePreserving` — the measurable equivalence `X 2 ≃ᵐ ℝ³ × ℝ³`,
  `x ↦ (x 0, x 1)` pushes `volume.restrict (abox 2 s)` to the product of the
  cube measures;
* `wPairC_sq_le` — the pointwise bound
  `wPairC ℓ f x y ^ 2 ≤ 4·chiSup⁴·(f (x-y))^2` (chi-renormalisation makes the
  kernel at most `2·chiSup²·|f(x-y)|`);
* `volume_prod_sub_preimage_null` / `prod_restrict_sub_preimage_null` /
  `abox_sub_preimage_null` — the difference map `(x,y) ↦ x - y` pulls a null
  set of `ℝ³` back to a null set of `abox 2 s` (Fubini + translation
  invariance of Lebesgue measure).
-/

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators
open Submission BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- The measurable equivalence `X 2 ≃ᵐ ℝ³ × ℝ³`, `x ↦ (x 0, x 1)`, pushes the
measure on the two-particle box `abox 2 s` to the product of the cube measures. -/
lemma abox2_measurePreserving (s : ℝ) :
    MeasurePreserving (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ³))
      (volume.restrict (abox 2 s))
      (((volume : Measure ℝ³).restrict (acube s)).prod
        ((volume : Measure ℝ³).restrict (acube s))) := by
  have h := measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure ℝ³).restrict (acube s))
  rw [← restrict_abox_eq_pi 2 s] at h
  exact h

/-- Pointwise bound for the chi-renormalised pair kernel: `wPairC` is at most
`2·chiSup²` times the numerator on the diagonal difference. -/
lemma wPairC_sq_le {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hRℓ : R ≤ ℓ * chiR0)
    {f : ℝ³ → ℝ} (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → f z = 0) (x y : ℝ³) :
    (wPairC ℓ f x y) ^ 2 ≤ 4 * chiSup ^ 4 * (f (x - y)) ^ 2 := by
  have hchi : ∀ z : ℝ³, |chiScale ℓ z| ≤ chiSup := abs_chiScale_le_chiSup ℓ
  have h1 : |wPairC ℓ f x y| ≤ 2 * chiSup ^ 2 * |f (x - y)| := by
    have hxy : wPairC ℓ f x y = chiScale ℓ x * wScaled ℓ f (x - y) * chiScale ℓ y := rfl
    rw [hxy, abs_mul, abs_mul]
    have h2 : |wScaled ℓ f (x - y)| ≤ 2 * |f (x - y)| :=
      wScaled_abs_le_two hℓ hR hRℓ hsupp (x - y)
    calc |chiScale ℓ x| * |wScaled ℓ f (x - y)| * |chiScale ℓ y|
        ≤ chiSup * (2 * |f (x - y)|) * chiSup := by
          apply mul_le_mul
          · exact mul_le_mul (hchi x) h2 (abs_nonneg _) (le_of_lt chiSup_pos)
          · exact hchi y
          · exact abs_nonneg _
          · exact mul_nonneg (le_of_lt chiSup_pos) (by positivity)
      _ = 2 * chiSup ^ 2 * |f (x - y)| := by ring
  calc (wPairC ℓ f x y) ^ 2 = |wPairC ℓ f x y| ^ 2 := by rw [sq_abs]
    _ ≤ (2 * chiSup ^ 2 * |f (x - y)|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = 4 * chiSup ^ 4 * (f (x - y)) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring

/-- The difference map `(x,y) ↦ x - y` pulls a measurable null set of `ℝ³`
back to a null set of the full product measure on `ℝ³ × ℝ³`. -/
lemma volume_prod_sub_preimage_null {G : Set ℝ³} (hGm : MeasurableSet G)
    (hG : (volume : Measure ℝ³) G = 0) :
    (volume : Measure (ℝ³ × ℝ³)) {q : ℝ³ × ℝ³ | q.1 - q.2 ∈ G} = 0 := by
  set S : Set (ℝ³ × ℝ³) := {q | q.1 - q.2 ∈ G} with hS
  have hSm : MeasurableSet S := (measurable_fst.sub measurable_snd) hGm
  rw [MeasureTheory.Measure.volume_eq_prod ℝ³ ℝ³]
  rw [Measure.prod_apply hSm]
  have hzero : ∀ x : ℝ³, (volume : Measure ℝ³) (Prod.mk x ⁻¹' S) = 0 := by
    intro x
    have hpre : Prod.mk x ⁻¹' S = (fun y : ℝ³ => x - y) ⁻¹' G := by
      ext y; simp [S]
    rw [hpre]
    have hmp := km_measurePreserving_sub_left x
    exact (hmp.measure_preimage hGm.nullMeasurableSet).trans hG
  simp [hzero]

/-- The same pullback statement for the product of the two cube measures. -/
lemma prod_restrict_sub_preimage_null (s : ℝ) {G : Set ℝ³} (hGm : MeasurableSet G)
    (hG : (volume : Measure ℝ³) G = 0) :
    (((volume : Measure ℝ³).restrict (acube s)).prod
        ((volume : Measure ℝ³).restrict (acube s)))
      {q : ℝ³ × ℝ³ | q.1 - q.2 ∈ G} = 0 := by
  set S : Set (ℝ³ × ℝ³) := {q | q.1 - q.2 ∈ G} with hS
  have hSm : MeasurableSet S := (measurable_fst.sub measurable_snd) hGm
  have hprod : (((volume : Measure ℝ³).restrict (acube s)).prod
        ((volume : Measure ℝ³).restrict (acube s)))
      = (volume : Measure (ℝ³ × ℝ³)).restrict (acube s ×ˢ acube s) := by
    rw [Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ³ ℝ³]
  rw [hprod]
  have h1 : (volume : Measure (ℝ³ × ℝ³)).restrict (acube s ×ˢ acube s) S
      ≤ (volume : Measure (ℝ³ × ℝ³)) S := Measure.restrict_apply_le _ _
  rw [volume_prod_sub_preimage_null hGm hG] at h1
  exact le_antisymm h1 zero_le

/-- The difference map `p ↦ p 0 - p 1` on `X 2` pulls a measurable null set of
`ℝ³` back to a null set of the restricted measure on the box `abox 2 s`. -/
lemma abox_sub_preimage_null {s : ℝ} {G : Set ℝ³} (hGm : MeasurableSet G)
    (hG : (volume : Measure ℝ³) G = 0) :
    (volume.restrict (abox 2 s)) {p : X 2 | p 0 - p 1 ∈ G} = 0 := by
  have he := abox2_measurePreserving s
  have hpre : (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ³)) ⁻¹'
      {q : ℝ³ × ℝ³ | q.1 - q.2 ∈ G} = {p : X 2 | p 0 - p 1 ∈ G} := by
    ext p
    simp [MeasurableEquiv.piFinTwo_apply]
  rw [← hpre, he.measure_preimage_emb (MeasurableEquiv.piFinTwo _).measurableEmbedding]
  exact prod_restrict_sub_preimage_null s hGm hG

end Work.SmallBoxA0
