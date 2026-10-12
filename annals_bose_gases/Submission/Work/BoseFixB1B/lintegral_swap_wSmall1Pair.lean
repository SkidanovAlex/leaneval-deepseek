import ChallengeDeps
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Tonelli swap for the localised one-body kernel `wSmall1Pair`

This file proves `Work.BoseFixB1B.lintegral_swap_wSmall1Pair`: the triple
iterated Lebesgue integral of `ENNReal.ofReal (wSmall1Pair h M ℓ d u x y)` may
be taken in any variable order.  Nothing about the *value* of the integral is
needed (and therefore the geometric hypotheses `0 < R`, `tsupport v ⊆ B(0,R)`
do not enter the argument), so the only mathematical input is a.e. measurability
of the integrand on the relevant product spaces.

Writing `F u x y = ENNReal.ofReal (wSmall1Pair h M ℓ d u x y)`, the kernel
factors as

`F u x y = ofReal (χ_{B(u)}(x) · W(x−y)/convScale ℓ (x−y) · χ_{B(u)}(y))`,

and the ingredients are:

* `g₀ = v(1−ω₀)` is locally integrable by the scattering equation
  (`IsScatteringSolution.rhs_integrable`), hence a.e. strongly measurable;
* the one-variable slicings `x ↦ x − y` and `x ↦ y − x` preserve Lebesgue
  measure, so the numerators `x ↦ g₀(±(x−y))` (fixed `y`) are a.e. measurable;
  the denominators `(χ_M⋆χ_M)(·/(ℓd))` and `(χ⋆χ)(·/ℓ)` are continuous;
* over the triple product `((u,x),y)` the numerator `q ↦ g₀(q.1.2 − q.2)` is
  a.e. measurable: the subtraction map is quasi-measure-preserving by
  translation invariance of Lebesgue measure;
* the two-factor small-box cutoff `χ_{B(u)}(x) = χ(x/ℓ)·χ_M(x/(ℓd)−u)` is
  *jointly continuous* in `(u,x)`.

With `F` a.e. measurable in the `((u,x),y)`-ordering and, for every fixed
middle variable, in the `(u,y)`-ordering, two applications of Tonelli's theorem
(`lintegral_lintegral_swap`) move `(u,x,y) ↦ (x,y,u)`.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Work.BoseFixB1B

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Transport of a.e. measurability along a pointwise equality -/

private lemma aemeasurable_of_eq_real {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (h : AEMeasurable f μ) (heq : f = g) : AEMeasurable g μ := by
  rw [heq] at h; exact h

private lemma aemeasurable_of_eq_nnreal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ENNReal} (h : AEMeasurable f μ) (heq : f = g) : AEMeasurable g μ := by
  rw [heq] at h; exact h

/-! ## Measurability of the factors -/

/-- `g₀ = v(1−ω₀)` is a.e. measurable: it is the locally integrable function
`v(1−ω₀)` of the scattering data. -/
private lemma aemeasurable_g0 {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) :
    AEMeasurable (g0 v h) volume :=
  (w0_spec h).2.rhs_integrable.aestronglyMeasurable.aemeasurable

/-- Joint measurability (indeed plain continuity) of the two-factor small-box
cutoff `χ_{B(u)}(x) = χ(x/ℓ)·χ_M(x/(ℓd)−u)` in the pair `(u,x)`. -/
private lemma measurable_chiSmallB_joint {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) :
    Measurable (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2) := by
  have h1 : Continuous (fun p : ℝ³ × ℝ³ => chiScale ℓ p.2) :=
    (chiScale_continuous ℓ).comp continuous_snd
  have h2 : Continuous (fun p : ℝ³ × ℝ³ => chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) :=
    (chiSmall_continuous hM).comp ((continuous_snd.const_smul ((ℓ * d)⁻¹)).sub continuous_fst)
  have heq : (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2)
      = fun p => chiScale ℓ p.2 * chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1) := by
    funext p; rfl
  rw [heq]; exact (h1.mul h2).measurable

/-- A.e. measurability of `x ↦ W(x−y)/convScale ℓ (x−y)` at fixed `y`: the
numerator `x ↦ g₀(x−y)` is a.e. measurable because `x ↦ x − y` (i.e.
`x ↦ x + (−y)`) preserves Lebesgue measure, and the two denominators are
continuous. -/
private lemma aemeasurable_wSmallScaled_sub_fixed {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (y : ℝ³) :
    AEMeasurable (fun x : ℝ³ => wSmallScaled M (ℓ * d) (g0 v h) (x - y)
      / convScale ℓ (x - y)) volume := by
  have hg0 : AEMeasurable (g0 v h) volume := aemeasurable_g0 h
  have hfun : (fun x : ℝ³ => x + (-y)) = fun x : ℝ³ => x - y := by
    funext x; simp only [sub_eq_add_neg]
  have hq : Measure.QuasiMeasurePreserving (fun x : ℝ³ => x - y) volume volume := by
    rw [← hfun]; exact quasiMeasurePreserving_add_right volume (-y)
  have hnum : AEMeasurable (fun x : ℝ³ => g0 v h (x - y)) volume :=
    AEMeasurable.comp_quasiMeasurePreserving hg0 hq
  have hden1 : Measurable (fun x : ℝ³ => convScaleSmall M (ℓ * d) (x - y)) := by
    have hc : Continuous (fun x : ℝ³ => (ℓ * d)⁻¹ • (x - y)) :=
      (continuous_id.sub continuous_const).const_smul ((ℓ * d)⁻¹)
    exact ((conv3Small_continuous hM).comp hc).measurable
  have hden2 : Measurable (fun x : ℝ³ => convScale ℓ (x - y)) :=
    ((convScale_continuous ℓ).comp (continuous_id.sub continuous_const)).measurable
  refine aemeasurable_of_eq_real ((hnum.div hden1.aemeasurable).div hden2.aemeasurable) ?_
  funext x; simp only [wSmallScaled, Pi.div_apply]

/-- A.e. measurability of `x ↦ W(y−x)/convScale ℓ (y−x)` at fixed `y` (the
mirror image of `aemeasurable_wSmallScaled_sub_fixed`); here `x ↦ y − x`
preserves Lebesgue measure directly. -/
private lemma aemeasurable_wSmallScaled_sub_fixed_left {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (y : ℝ³) :
    AEMeasurable (fun x : ℝ³ => wSmallScaled M (ℓ * d) (g0 v h) (y - x)
      / convScale ℓ (y - x)) volume := by
  have hg0 : AEMeasurable (g0 v h) volume := aemeasurable_g0 h
  have hq : Measure.QuasiMeasurePreserving (fun x : ℝ³ => y - x) volume volume :=
    quasiMeasurePreserving_sub_left_of_right_invariant volume y
  have hnum : AEMeasurable (fun x : ℝ³ => g0 v h (y - x)) volume :=
    AEMeasurable.comp_quasiMeasurePreserving hg0 hq
  have hden1 : Measurable (fun x : ℝ³ => convScaleSmall M (ℓ * d) (y - x)) := by
    have hc : Continuous (fun x : ℝ³ => (ℓ * d)⁻¹ • (y - x)) :=
      (continuous_const.sub continuous_id).const_smul ((ℓ * d)⁻¹)
    exact ((conv3Small_continuous hM).comp hc).measurable
  have hden2 : Measurable (fun x : ℝ³ => convScale ℓ (y - x)) :=
    ((convScale_continuous ℓ).comp (continuous_const.sub continuous_id)).measurable
  refine aemeasurable_of_eq_real ((hnum.div hden1.aemeasurable).div hden2.aemeasurable) ?_
  funext x; simp only [wSmallScaled, Pi.div_apply]

/-- Joint a.e. measurability of the numerator `g₀(q.1.2 − q.2)` over the triple
product `((u,x),y)`: the subtraction map is quasi-measure-preserving by
translation invariance of Lebesgue measure. -/
private lemma aemeasurable_g0_sub_triple {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) :
    AEMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ => g0 v h (q.1.2 - q.2))
      ((volume.prod volume).prod volume) := by
  have hg0 : AEMeasurable (g0 v h) volume := aemeasurable_g0 h
  have hsub : Measurable (fun q : (ℝ³ × ℝ³) × ℝ³ => q.1.2 - q.2) :=
    measurable_fst.snd.sub measurable_snd
  have hq : Measure.QuasiMeasurePreserving (fun q : (ℝ³ × ℝ³) × ℝ³ => q.1.2 - q.2)
      ((volume.prod volume).prod volume) volume :=
    QuasiMeasurePreserving.prod_of_right hsub
      (Eventually.of_forall fun p =>
        quasiMeasurePreserving_sub_left_of_right_invariant volume p.2)
  exact AEMeasurable.comp_quasiMeasurePreserving hg0 hq

/-- The middle factor `W(x−y)/convScale ℓ (x−y)` over the triple product
`((u,x),y)`. -/
private lemma aemeasurable_B_triple {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) :
    AEMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ =>
      wSmallScaled M (ℓ * d) (g0 v h) (q.1.2 - q.2) / convScale ℓ (q.1.2 - q.2))
      ((volume.prod volume).prod volume) := by
  have hnum : AEMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ => g0 v h (q.1.2 - q.2))
      ((volume.prod volume).prod volume) := aemeasurable_g0_sub_triple h
  have hden1 : Measurable (fun q : (ℝ³ × ℝ³) × ℝ³ => convScaleSmall M (ℓ * d) (q.1.2 - q.2)) := by
    have hc : Continuous (fun q : (ℝ³ × ℝ³) × ℝ³ => (ℓ * d)⁻¹ • (q.1.2 - q.2)) :=
      (((continuous_fst.snd).sub continuous_snd).const_smul ((ℓ * d)⁻¹))
    exact ((conv3Small_continuous hM).comp hc).measurable
  have hden2 : Measurable (fun q : (ℝ³ × ℝ³) × ℝ³ => convScale ℓ (q.1.2 - q.2)) :=
    ((convScale_continuous ℓ).comp ((continuous_fst.snd).sub continuous_snd)).measurable
  refine aemeasurable_of_eq_real ((hnum.div hden1.aemeasurable).div hden2.aemeasurable) ?_
  funext q; simp only [wSmallScaled, Pi.div_apply]

/-! ## The two orderings of the integrand

`F u x y = ofReal (χ_{B(u)}(x) · W(x−y)/convScale ℓ (x−y) · χ_{B(u)}(y))` is a.e.
measurable in the `((u,x),y)`-ordering (`aemeasurable_w1_triple`) and, for every
fixed middle variable, in the `(u,y)`-ordering (`aemeasurable_w1_mid`).
-/

private lemma aemeasurable_w1_triple {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) :
    AEMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ =>
      ENNReal.ofReal (wSmall1Pair h M ℓ d q.1.1 q.1.2 q.2)) ((volume.prod volume).prod volume) := by
  have hJ : Measurable (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2) :=
    measurable_chiSmallB_joint hM ℓ d
  have hA : AEMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ => chiSmallB M ℓ d q.1.1 q.1.2)
      ((volume.prod volume).prod volume) := (hJ.comp measurable_fst).aemeasurable
  have hB : AEMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ =>
      wSmallScaled M (ℓ * d) (g0 v h) (q.1.2 - q.2) / convScale ℓ (q.1.2 - q.2))
      ((volume.prod volume).prod volume) := aemeasurable_B_triple h hM ℓ d
  have hC : AEMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ => chiSmallB M ℓ d q.1.1 q.2)
      ((volume.prod volume).prod volume) :=
    (hJ.comp (((continuous_fst.fst).prodMk continuous_snd).measurable)).aemeasurable
  have hgoal := ((hA.mul hB).mul hC).ennreal_ofReal
  refine aemeasurable_of_eq_nnreal hgoal ?_
  funext q; simp only [wSmall1Pair, wSmallPair, Pi.mul_apply]

private lemma aemeasurable_w1_mid {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (x : ℝ³) :
    AEMeasurable (fun p : ℝ³ × ℝ³ => ENNReal.ofReal (wSmall1Pair h M ℓ d p.1 x p.2))
      (volume.prod volume) := by
  have hJ : Measurable (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2) :=
    measurable_chiSmallB_joint hM ℓ d
  have hA : AEMeasurable (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 x) (volume.prod volume) :=
    (hJ.comp ((continuous_fst.prodMk continuous_const).measurable)).aemeasurable
  have hB : AEMeasurable (fun p : ℝ³ × ℝ³ =>
      wSmallScaled M (ℓ * d) (g0 v h) (x - p.2) / convScale ℓ (x - p.2))
      (volume.prod volume) := (aemeasurable_wSmallScaled_sub_fixed_left h hM ℓ d x).comp_snd
  have hC : AEMeasurable (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2) (volume.prod volume) :=
    hJ.aemeasurable
  have hgoal := ((hA.mul hB).mul hC).ennreal_ofReal
  refine aemeasurable_of_eq_nnreal hgoal ?_
  funext p; simp only [wSmall1Pair, wSmallPair, Pi.mul_apply]

/-! ## The swap -/

/-- The triple Tonelli swap for a nonnegative integrand on `α×α×α`: from
`((a,b),c)`-a.e.-measurability of the integrand and, for every fixed middle
variable, `(a,c)`-a.e.-measurability, the iterated integral may be cycled to the
`(b,c,a)` order. -/
private lemma lintegral_swap3 {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {f : α → α → α → ENNReal}
    (h1 : AEMeasurable (fun q : (α × α) × α => f q.1.1 q.1.2 q.2) ((μ.prod μ).prod μ))
    (h2 : ∀ b, AEMeasurable (Function.uncurry (fun a c => f a b c)) (μ.prod μ)) :
    ∫⁻ a, ∫⁻ b, ∫⁻ c, f a b c ∂μ ∂μ ∂μ = ∫⁻ b, ∫⁻ c, ∫⁻ a, f a b c ∂μ ∂μ ∂μ := by
  have h1' : AEMeasurable (Function.uncurry (fun a b => ∫⁻ c, f a b c ∂μ)) (μ.prod μ) :=
    AEMeasurable.lintegral_prod_right (μ := μ.prod μ) (ν := μ)
      (f := fun p c => f p.1 p.2 c) h1
  have step1 : (∫⁻ a, ∫⁻ b, ∫⁻ c, f a b c ∂μ ∂μ ∂μ)
      = ∫⁻ b, ∫⁻ a, ∫⁻ c, f a b c ∂μ ∂μ ∂μ :=
    lintegral_lintegral_swap (f := fun a b => ∫⁻ c, f a b c ∂μ) h1'
  have step2 : (∫⁻ b, ∫⁻ a, ∫⁻ c, f a b c ∂μ ∂μ ∂μ)
      = ∫⁻ b, ∫⁻ c, ∫⁻ a, f a b c ∂μ ∂μ ∂μ := by
    apply lintegral_congr
    intro b
    exact lintegral_lintegral_swap (f := fun a c => f a b c) (h2 b)
  exact step1.trans step2

theorem lintegral_swap_wSmall1Pair {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    (∫⁻ u : EuclideanSpace ℝ (Fin 3), ∫⁻ x : EuclideanSpace ℝ (Fin 3),
        ∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (Submission.BoseGases.wSmall1Pair h M ℓ d u x y))
      = ∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
          ∫⁻ u : EuclideanSpace ℝ (Fin 3),
            ENNReal.ofReal (Submission.BoseGases.wSmall1Pair h M ℓ d u x y) := by
  refine lintegral_swap3 (α := ℝ³) (μ := volume)
    (f := fun u x y => ENNReal.ofReal (Submission.BoseGases.wSmall1Pair h M ℓ d u x y)) ?_ ?_
  · exact aemeasurable_w1_triple h hM ℓ d
  · intro x
    exact aemeasurable_w1_mid h hM ℓ d x

end Work.BoseFixB1B
