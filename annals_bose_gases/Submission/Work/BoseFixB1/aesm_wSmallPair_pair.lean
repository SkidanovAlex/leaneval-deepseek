import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxSliding.abs_wSmall1Pair_le
import Submission.Work.SmallBoxSliding.chiSmallB_continuous_joint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.aesm_wSmallPair_pair`

A.e.-strong measurability of the localised two-body kernel

    x ↦ wSmallPair M ℓ d u f (x i) (x j)

on the `N`-particle box `abox N ℓ ⊆ X N`, for a numerator `f` which is only
a.e.-measurable w.r.t. Lebesgue measure (the situation in the corpus, where `f` is one of
the scattering kernels `v`, `g₀`, `g₂`, known only a.e.).

The kernel unfolds (`Submission.BoseGases.wSmallPair`, `wSmallScaled`) as

    wSmallPair M ℓ d u f x y
      = χ_{B(u)}(x) · (f(x−y)/C_{ℓd}(x−y)) / (χ⋆χ)((x−y)/ℓ) · χ_{B(u)}(y)

with `χ_{B(u)}` the two-factor small-box cutoff and `C_{ℓd} = χ_M⋆χ_M` the scaled cosine
self-convolution.  The proof is in two steps.

**Step 1 (the two-variable kernel on `volume ⊗ volume`).**

* `(x,y) ↦ f (x−y)`: the difference map is quasi-measure-preserving for Lebesgue measure
  (`quasiMeasurePreserving_sub_of_right_invariant`), so a.e.-measurability of `f` transfers;
* `(x,y) ↦ C_{ℓd}(x−y)`: the scaled self-convolution is measurable *for every* `M` — for
  `M ≥ 1` it is continuous, and the general case is proved here by writing it as a
  parametric integral of a **continuous** integrand and applying
  `AEStronglyMeasurable.integral_prod_right'` (this avoids the `M = 0` pathology, where the
  cosine bump degenerates);
* `(x,y) ↦ (χ⋆χ)((x−y)/ℓ)` and the two cutoff factors: compositions of continuous functions.

**Step 2 (transfer to the box).**  For distinct labels `i ≠ j` the two-coordinate projection
`x ↦ (x i, x j)` on `X N = Fin N → ℝ³` is quasi-measure-preserving for the product Lebesgue
measure (`qmp_pair_proj_XN`, transported from Mathlib's `piEquivPiSubtypeProd`), so Step 1
composes with it; the restriction to `abox N ℓ` then only makes the measure smaller
(`AEStronglyMeasurable.mono_measure`).  For `i = j` the relative coordinate vanishes and the
kernel is continuous in `x i`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Continuity of the cutoff and of the scaled self-convolution -/

/-- The small-box cutoff `χ_{B(u)}(x) = χ(x/ℓ)·χ_M(x/(ℓd) − u)` is continuous in its spatial
variable, for **every** `M` (`χ_M` is continuous for all `M`: at `M = 0` it is the zero
function). -/
lemma continuous_chiSmallB (M : ℕ) (ℓ d : ℝ) (u : ℝ³) :
    Continuous (fun x : ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u x) := by
  have hchi : Continuous (fun z : ℝ³ => Submission.BoseGases.chiSmall M z) :=
    Work.SmallBoxSliding.chiSmall_continuous_all M
  have heq : (fun x : ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u x) =
      fun x => Submission.BoseGases.chiScale ℓ x *
        Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) := by
    funext x; rfl
  rw [heq]
  exact (Submission.BoseGases.chiScale_continuous ℓ).mul
    (hchi.comp ((continuous_id.const_smul ((ℓ * d)⁻¹)).sub continuous_const))

/-- **The scaled cosine self-convolution along the relative coordinate is a.e.-strongly
measurable.**  For every `M : ℕ` and every real `c`, the function
`p ↦ (χ_M ⋆ χ_M)(c⁻¹ • (p₁ − p₂))` is a.e.-strongly measurable on `volume ⊗ volume`.

The proof avoids any continuity hypothesis on `conv3Small M` (the corpus lemma
`conv3Small_continuous` needs `1 ≤ M`): the self-convolution is written as the parametric
integral `p ↦ ∫_y χ_M(y)·χ_M(c⁻¹•(p₁−p₂) − y)`, whose integrand is continuous on
`(ℝ³ × ℝ³) × ℝ³` because `χ_M` is continuous for *all* `M`
(`Work.SmallBoxSliding.chiSmall_continuous_all`); then
`AEStronglyMeasurable.integral_prod_right'` (no integrability needed) gives the claim. -/
lemma aesm_convScaleSmall_sub {M : ℕ} {c : ℝ} :
    AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.convScaleSmall M c (p.1 - p.2))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
  have hchi : Continuous (fun z : ℝ³ => Submission.BoseGases.chiSmall M z) :=
    Work.SmallBoxSliding.chiSmall_continuous_all M
  have hcont : Continuous (fun z : (ℝ³ × ℝ³) × ℝ³ =>
      Submission.BoseGases.chiSmall M z.2 *
        Submission.BoseGases.chiSmall M (c⁻¹ • (z.1.1 - z.1.2) - z.2)) :=
    (hchi.comp continuous_snd).mul (hchi.comp (by fun_prop))
  have hint : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => ∫ y : ℝ³, Submission.BoseGases.chiSmall M y *
        Submission.BoseGases.chiSmall M (c⁻¹ • (p.1 - p.2) - y))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    AEStronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ³))
      hcont.aestronglyMeasurable
  have heq : (fun p : ℝ³ × ℝ³ => ∫ y : ℝ³, Submission.BoseGases.chiSmall M y *
        Submission.BoseGases.chiSmall M (c⁻¹ • (p.1 - p.2) - y))
      = fun p : ℝ³ × ℝ³ => Submission.BoseGases.convScaleSmall M c (p.1 - p.2) := by
    funext p
    rw [Submission.BoseGases.convScaleSmall, Submission.BoseGases.conv3Small]
  rwa [heq] at hint

/-! ## 2. The two-variable kernel on the product space -/

/-- **A.e.-strong measurability of the localised pair kernel `wSmallPair` on
`volume ⊗ volume`.**  The numerator `f` need only be a.e.-measurable. -/
lemma aesm_wSmallPair_prod_full {M : ℕ} {ℓ d : ℝ} (u : ℝ³) {f : ℝ³ → ℝ}
    (hf : AEMeasurable f (volume : Measure ℝ³)) :
    AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.wSmallPair M ℓ d u f p.1 p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
  have hnum : AEMeasurable (fun p : ℝ³ × ℝ³ => f (p.1 - p.2))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    hf.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure ℝ³) (volume : Measure ℝ³))
  have hden1 : AEMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    (aesm_convScaleSmall_sub (M := M) (c := ℓ * d)).aemeasurable
  have hden2 : AEMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.convScale ℓ (p.1 - p.2))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    ((Submission.BoseGases.convScale_continuous ℓ).comp
      (by fun_prop : Continuous fun p : ℝ³ × ℝ³ => p.1 - p.2)).aemeasurable
  have hchi1 : AEMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u p.1)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    ((continuous_chiSmallB M ℓ d u).comp continuous_fst).aemeasurable
  have hchi2 : AEMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    ((continuous_chiSmallB M ℓ d u).comp continuous_snd).aemeasurable
  have hmain : AEMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u p.1 *
        ((f (p.1 - p.2) / Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2)) /
          Submission.BoseGases.convScale ℓ (p.1 - p.2)) *
        Submission.BoseGases.chiSmallB M ℓ d u p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    (hchi1.mul ((hnum.div hden1).div hden2)).mul hchi2
  have hgoal : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u p.1 *
        ((f (p.1 - p.2) / Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2)) /
          Submission.BoseGases.convScale ℓ (p.1 - p.2)) *
        Submission.BoseGases.chiSmallB M ℓ d u p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := hmain.aestronglyMeasurable
  simpa only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled] using hgoal

/-- The kernel is **continuous on the diagonal** `x = y`: the relative coordinate `a − a`
vanishes, so only the cutoff and the constant `f 0 / (C_{ℓd}(0)·(χ⋆χ)(0))` remain. -/
lemma continuous_wSmallPair_diag (M : ℕ) (ℓ d : ℝ) (u : ℝ³) (f : ℝ³ → ℝ) :
    Continuous (fun a : ℝ³ => Submission.BoseGases.wSmallPair M ℓ d u f a a) := by
  have heq : (fun a : ℝ³ => Submission.BoseGases.wSmallPair M ℓ d u f a a) =
      fun a => Submission.BoseGases.chiSmallB M ℓ d u a *
        ((f 0 / Submission.BoseGases.convScaleSmall M (ℓ * d) 0) /
          Submission.BoseGases.convScale ℓ 0) *
        Submission.BoseGases.chiSmallB M ℓ d u a := by
    funext a
    simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled, sub_self]
  rw [heq]
  exact ((continuous_chiSmallB M ℓ d u).mul continuous_const).mul
    (continuous_chiSmallB M ℓ d u)

/-! ## 3. The two-coordinate projection of `X N` is quasi-measure-preserving -/

/-- **The two-coordinate projection `x ↦ (x i, x j)` is quasi-measure-preserving** (for
distinct labels `i ≠ j`): the configuration space splits as
`({k // k ≠ j} → ℝ³) × ℝ³`, this identification is measure-preserving
(`volume_preserving_piEquivPiSubtypeProd`), and on the two factors the evaluations at `i`,
resp. `j`, are quasi-measure-preserving (`Measure.quasiMeasurePreserving_eval`). -/
lemma qmp_pair_proj_XN {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Measure.QuasiMeasurePreserving (fun x : Submission.BoseGases.X N => (x i, x j))
      (volume : Measure (Submission.BoseGases.X N))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
  have h : Measure.QuasiMeasurePreserving (fun x : Fin N → ℝ³ => (x i, x j))
      (Measure.pi (fun _ : Fin N => (volume : Measure ℝ³)))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
    classical
    have hA := Measure.quasiMeasurePreserving_eval
      (μ := fun _ : {k : Fin N // k ≠ j} => (volume : Measure ℝ³)) ⟨i, hij⟩
    have hB := Measure.quasiMeasurePreserving_eval
      (μ := fun _ : {k : Fin N // ¬(k ≠ j)} => (volume : Measure ℝ³)) ⟨j, fun h => h rfl⟩
    have hmap := QuasiMeasurePreserving.prodMap hA hB
    have he := (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N => ℝ³)
      (fun k : Fin N => k ≠ j)).quasiMeasurePreserving
    refine (hmap.comp he).congr (by fun_prop) ?_
    filter_upwards with x
    apply Prod.ext
    · simp only [Function.comp_apply, Prod.map_fst, Function.eval,
        MeasurableEquiv.piEquivPiSubtypeProd_apply]
    · simp only [Function.comp_apply, Prod.map_snd, Function.eval,
        MeasurableEquiv.piEquivPiSubtypeProd_apply]
  rwa [← MeasureTheory.volume_pi] at h

/-! ## 4. The theorem -/

theorem aesm_wSmallPair_pair {N : ℕ} {ℓ d : ℝ} (M : ℕ) (u : EuclideanSpace ℝ (Fin 3))
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : AEMeasurable f (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (i j : Fin N) :
    MeasureTheory.AEStronglyMeasurable (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.wSmallPair M ℓ d u f (x i) (x j))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
  by_cases hij : i = j
  · -- equal labels: the relative coordinate vanishes, the kernel is continuous in `x i`
    have heq : (fun x : Submission.BoseGases.X N =>
          Submission.BoseGases.wSmallPair M ℓ d u f (x i) (x j))
        = (fun x : Submission.BoseGases.X N =>
            Submission.BoseGases.wSmallPair M ℓ d u f (x j) (x j)) := by
      funext x
      rw [hij]
    rw [heq]
    have hcont : Continuous (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.wSmallPair M ℓ d u f (x j) (x j)) :=
      (continuous_wSmallPair_diag M ℓ d u f).comp (continuous_apply j)
    exact hcont.aestronglyMeasurable
  · -- distinct labels: compose with the quasi-measure-preserving pair projection
    have hK := aesm_wSmallPair_prod_full (M := M) (ℓ := ℓ) (d := d) u hf
    have hq := qmp_pair_proj_XN (N := N) i j hij
    exact (hK.comp_quasiMeasurePreserving hq).mono_measure Measure.restrict_le_self

end Work.BoseFixB1
