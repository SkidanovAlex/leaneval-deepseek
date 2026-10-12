import ChallengeDeps
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseB1Cube.fibSumOffCube
import Submission.Work.BoseB1Cube.fibSumUniformBound
import Submission.Work.BoseFixB1B.matchedWindowDefs
import Submission.Work.BoseFixB1B.sbWordMuShift
import Submission.Work.BoseFixB1S.FlatFib.fibMeasurableRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory
open scoped Real BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Measurability of the sliding fibre sum in the centre `u`

`Work.BoseFixB1.fibSum h M ℓ d u Φ = ∫_{abox n ℓ} Φ x² · Σ_i ∫_{acube ℓ} wSmall1Pair h M ℓ d u (x i) y`
depends on `u` only through the two cutoff factors
`χ_{B(u)}(z) = χ(z/ℓ)·χ_M((ℓd)⁻¹•z − u)`.  The only non-continuous ingredient of the kernel is the
numerator `g₀ v h = v(1−w₀)`, which is only `a.e.` strongly measurable
(`Submission.BoseGases.g0_integrable`), so — exactly as in
`Work.BoseFixB1S.FlatFib.fibMeasurableRep` and `Work.BoseFixR.w1FibreSlotIntegrableOfSupport` — we
replace it by its measurable representative `AEMeasurable.mk (g₀ v h) ·`; the two fibres agree
*everywhere* because `g₀` enters the kernel only as `g₀ (z − y)` and `y ↦ z − y` is measure
preserving.  The two parametric-integral lemmas
(`StronglyMeasurable.integral_prod_right`, once in `y` and once in `x`) then give strong
measurability of `u ↦ fibSum h M ℓ d u Φ`. -/

/-- Joint measurability of the localised kernel with a *measurable* numerator, as a function of the
sliding centre `u`, the particle position `z` and the integration variable `y`.  All the
`u`-dependence sits in the two cutoff factors `χ_{B(u)}(z) = χ(z/ℓ)·χ_M((ℓd)⁻¹z − u)` and
`χ_{B(u)}(y)`, which are jointly continuous in `(u,z)` (resp. `(u,y)`). -/
private lemma measurable_kernel_sliding {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    {g : E3 → ℝ} (hg : Measurable g) :
    Measurable fun p : (E3 × E3) × E3 =>
      Submission.BoseGases.wSmallPair M ℓ d p.1.1 g p.1.2 p.2 := by
  have hchi1 : Measurable fun p : (E3 × E3) × E3 =>
      Submission.BoseGases.chiSmallB M ℓ d p.1.1 p.1.2 := by
    have hc : Continuous fun p : (E3 × E3) × E3 =>
        Submission.BoseGases.chiSmallB M ℓ d p.1.1 p.1.2 := by
      show Continuous fun p : (E3 × E3) × E3 => Submission.BoseGases.chiScale ℓ p.1.2 *
        Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.1.2 - p.1.1)
      exact (Submission.BoseGases.chiScale_continuous ℓ).comp (by fun_prop) |>.mul
        ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
    exact hc.measurable
  have hchi2 : Measurable fun p : (E3 × E3) × E3 =>
      Submission.BoseGases.chiSmallB M ℓ d p.1.1 p.2 := by
    have hc : Continuous fun p : (E3 × E3) × E3 =>
        Submission.BoseGases.chiSmallB M ℓ d p.1.1 p.2 := by
      show Continuous fun p : (E3 × E3) × E3 => Submission.BoseGases.chiScale ℓ p.2 *
        Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1.1)
      exact (Submission.BoseGases.chiScale_continuous ℓ).comp (by fun_prop) |>.mul
        ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
    exact hc.measurable
  have hnum : Measurable fun p : (E3 × E3) × E3 => g (p.1.2 - p.2) := hg.comp (by fun_prop)
  have hden1 : Measurable fun p : (E3 × E3) × E3 =>
      Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1.2 - p.2) := by
    have hc : Continuous fun p : (E3 × E3) × E3 =>
        Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1.2 - p.2) := by
      show Continuous fun p : (E3 × E3) × E3 =>
        Submission.BoseGases.conv3Small M ((ℓ * d)⁻¹ • (p.1.2 - p.2))
      exact (Submission.BoseGases.conv3Small_continuous hM).comp (by fun_prop)
    exact hc.measurable
  have hden2 : Measurable fun p : (E3 × E3) × E3 =>
      Submission.BoseGases.convScale ℓ (p.1.2 - p.2) :=
    ((Submission.BoseGases.convScale_continuous ℓ).comp (by fun_prop)).measurable
  have hmain : Measurable fun p : (E3 × E3) × E3 =>
      Submission.BoseGases.chiSmallB M ℓ d p.1.1 p.1.2 *
        ((g (p.1.2 - p.2) / Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1.2 - p.2))
          / Submission.BoseGases.convScale ℓ (p.1.2 - p.2)) *
        Submission.BoseGases.chiSmallB M ℓ d p.1.1 p.2 :=
    (hchi1.mul ((hnum.div hden1).div hden2)).mul hchi2
  simpa only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled] using hmain

/-- **Measurability of the joint fibre** `(u,z) ↦ ∫_{acube ℓ} wSmallPair M ℓ d u g z y` for a
*measurable* numerator `g`: the parametric-integral lemma
`StronglyMeasurable.integral_prod_right` applied to `measurable_kernel_sliding`. -/
private lemma measurable_fibre_sliding {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} {g : E3 → ℝ}
    (hg : Measurable g) :
    Measurable fun p : E3 × E3 =>
      ∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmallPair M ℓ d p.1 g p.2 y := by
  have hjoint := measurable_kernel_sliding (ℓ := ℓ) (d := d) hM hg
  have hsm : StronglyMeasurable (Function.uncurry fun (p : E3 × E3) (y : E3) =>
      Submission.BoseGases.wSmallPair M ℓ d p.1 g p.2 y) := hjoint.stronglyMeasurable
  have h := StronglyMeasurable.integral_prod_right
    (ν := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict
      (Submission.BoseGases.acube ℓ))
    (f := fun (p : E3 × E3) (y : E3) =>
      Submission.BoseGases.wSmallPair M ℓ d p.1 g p.2 y) hsm
  exact h.measurable

/-- Joint measurability of the localised kernel at the `i`-th particle position, as a function of
the pair `(u, x) ∈ E3 × 𝕏ⁿ` and of the integration variable `y`. -/
private lemma measurable_kernel_sliding_i {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    {g : E3 → ℝ} (hg : Measurable g) {n : ℕ} (i : Fin n) :
    Measurable fun p : (E3 × Submission.BoseGases.X n) × E3 =>
      Submission.BoseGases.wSmallPair M ℓ d p.1.1 g (p.1.2 i) p.2 := by
  have hchi1 : Measurable fun p : (E3 × Submission.BoseGases.X n) × E3 =>
      Submission.BoseGases.chiSmallB M ℓ d p.1.1 (p.1.2 i) := by
    have hc : Continuous fun p : (E3 × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.chiSmallB M ℓ d p.1.1 (p.1.2 i) := by
      show Continuous fun p : (E3 × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.chiScale ℓ (p.1.2 i) *
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (p.1.2 i) - p.1.1)
      exact (Submission.BoseGases.chiScale_continuous ℓ).comp (by fun_prop) |>.mul
        ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
    exact hc.measurable
  have hchi2 : Measurable fun p : (E3 × Submission.BoseGases.X n) × E3 =>
      Submission.BoseGases.chiSmallB M ℓ d p.1.1 p.2 := by
    have hc : Continuous fun p : (E3 × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.chiSmallB M ℓ d p.1.1 p.2 := by
      show Continuous fun p : (E3 × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.chiScale ℓ p.2 *
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1.1)
      exact (Submission.BoseGases.chiScale_continuous ℓ).comp (by fun_prop) |>.mul
        ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
    exact hc.measurable
  have hnum : Measurable fun p : (E3 × Submission.BoseGases.X n) × E3 =>
      g (p.1.2 i - p.2) := hg.comp (by fun_prop)
  have hden1 : Measurable fun p : (E3 × Submission.BoseGases.X n) × E3 =>
      Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1.2 i - p.2) := by
    have hc : Continuous fun p : (E3 × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1.2 i - p.2) := by
      show Continuous fun p : (E3 × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.conv3Small M ((ℓ * d)⁻¹ • (p.1.2 i - p.2))
      exact (Submission.BoseGases.conv3Small_continuous hM).comp (by fun_prop)
    exact hc.measurable
  have hden2 : Measurable fun p : (E3 × Submission.BoseGases.X n) × E3 =>
      Submission.BoseGases.convScale ℓ (p.1.2 i - p.2) :=
    ((Submission.BoseGases.convScale_continuous ℓ).comp (by fun_prop)).measurable
  have hmain : Measurable fun p : (E3 × Submission.BoseGases.X n) × E3 =>
      Submission.BoseGases.chiSmallB M ℓ d p.1.1 (p.1.2 i) *
        ((g (p.1.2 i - p.2) / Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1.2 i - p.2))
          / Submission.BoseGases.convScale ℓ (p.1.2 i - p.2)) *
        Submission.BoseGases.chiSmallB M ℓ d p.1.1 p.2 :=
    (hchi1.mul ((hnum.div hden1).div hden2)).mul hchi2
  simpa only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled] using hmain

/-- **Measurability of the `i`-th fibre slot** in the sliding centre `u` and the configuration
`x`, with a *measurable* numerator `g`. -/
private lemma measurable_fibre_sliding_i {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} {g : E3 → ℝ}
    (hg : Measurable g) {n : ℕ} (i : Fin n) :
    Measurable fun q : E3 × Submission.BoseGases.X n =>
      ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d q.1 g (q.2 i) y := by
  have hjoint := measurable_kernel_sliding_i (ℓ := ℓ) (d := d) hM hg i
  have hsm : StronglyMeasurable (Function.uncurry fun (q : E3 × Submission.BoseGases.X n) (y : E3) =>
      Submission.BoseGases.wSmallPair M ℓ d q.1 g (q.2 i) y) := hjoint.stronglyMeasurable
  have h := StronglyMeasurable.integral_prod_right
    (ν := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict
      (Submission.BoseGases.acube ℓ))
    (f := fun (q : E3 × Submission.BoseGases.X n) (y : E3) =>
      Submission.BoseGases.wSmallPair M ℓ d q.1 g (q.2 i) y) hsm
  exact h.measurable

/-- **The sliding fibre sum is a.e. strongly measurable in `u`.** -/
theorem aestronglyMeasurable_fibSumB {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (hΦ : Continuous Φ) :
    MeasureTheory.AEStronglyMeasurable
      (fun u : E3 => Work.BoseFixB1.fibSum h M ℓ d u Φ)
      (MeasureTheory.volume : MeasureTheory.Measure E3) := by
  classical
  -- a measurable representative of the numerator `g₀ = v(1−w₀)`
  have hg0 : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  set f' : E3 → ℝ := AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0.aemeasurable with hf'def
  have hf'meas : Measurable f' := by
    rw [hf'def]; exact hg0.aemeasurable.measurable_mk
  have hf'eq : Submission.BoseGases.g0 v h =ᵐ[MeasureTheory.volume] f' := by
    rw [hf'def]; exact hg0.aemeasurable.ae_eq_mk
  -- the `g₀`- and `f'`-fibres agree *everywhere* (the reflection `y ↦ z − y` is measure preserving)
  have hpairEq : ∀ (u z : E3),
      (∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmall1Pair h M ℓ d u z y)
        = (∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmallPair M ℓ d u f' z y) := by
    intro u z
    rw [show Submission.BoseGases.wSmall1Pair h M ℓ d u
        = Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) from rfl]
    refine MeasureTheory.integral_congr_ae ?_
    have hmp : MeasureTheory.MeasurePreserving (fun t : E3 => z - t)
        (MeasureTheory.volume : MeasureTheory.Measure E3)
        (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      MeasureTheory.Measure.measurePreserving_sub_left MeasureTheory.volume z
    have hae : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
        Submission.BoseGases.g0 v h (z - y) = f' (z - y) :=
      hmp.quasiMeasurePreserving.tendsto_ae.eventually hf'eq
    filter_upwards [MeasureTheory.ae_restrict_of_ae hae] with y hy
    simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
    rw [hy]
  -- joint measurability of the `x`-integrand
  have hIntegrand : Measurable fun q : E3 × Submission.BoseGases.X n =>
      (Φ q.2) ^ 2 * ∑ i : Fin n,
        ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d q.1 f' (q.2 i) y := by
    refine (Measurable.mul ?_ ?_)
    · exact (hΦ.measurable.comp measurable_snd).pow_const 2
    · exact Finset.measurable_sum _ fun i _ => measurable_fibre_sliding_i (ℓ := ℓ) (d := d) hM hf'meas i
  have hsm : StronglyMeasurable (Function.uncurry fun (u : E3)
      (x : Submission.BoseGases.X n) =>
      (Φ x) ^ 2 * ∑ i : Fin n,
        ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u f' (x i) y) :=
    hIntegrand.stronglyMeasurable
  have hmeasF : StronglyMeasurable fun u : E3 =>
      ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * ∑ i : Fin n,
        ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u f' (x i) y :=
    StronglyMeasurable.integral_prod_right
      (ν := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ))
      (f := fun (u : E3) (x : Submission.BoseGases.X n) =>
        (Φ x) ^ 2 * ∑ i : Fin n,
          ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmallPair M ℓ d u f' (x i) y) hsm
  have hfibEq : (fun u : E3 => Work.BoseFixB1.fibSum h M ℓ d u Φ)
      = fun u : E3 => ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * ∑ i : Fin n,
          ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmallPair M ℓ d u f' (x i) y := by
    funext u
    rw [Work.BoseFixB1.fibSum]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [show (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
        = (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmallPair M ℓ d u f' (x i) y) from
      Finset.sum_congr rfl (fun i _ => hpairEq u (x i))]
  rw [hfibEq]
  exact hmeasF.aestronglyMeasurable

/-- **`u`-integrability of the sliding fibre sum** (the object `Work.BoseFixB1.fibSum` of
`Submission/Work/BoseFixB1/perBoxF_localised.lean`:
`fibSum h M ℓ d u Φ = ∫ x in abox n ℓ, Φ x ^ 2 * ∑ i, ∫ y in acube ℓ, wSmall1Pair h M ℓ d u (x i) y`).

Needed for the `u`-integral bookkeeping of the good-set localisation (`∫` over `goodSet`,
`interiorSet` and their complements).  Import `Submission.Work.BoseB1Cube.goodCubeDefs` (re-exports
`matchedWindowDefs` + `perBoxF_localised` + `SmallBoxSliding.Defs`).

**Spelling note:** the smoothness hypothesis is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ`, i.e. the
*smooth* order `∞ = (↑⊤ : WithTop ℕ∞)` — **not** `ContDiff ℝ (⊤ : WithTop ℕ∞)`, which in this
Mathlib denotes the *analytic* order (`ContDiff.of_le : ContDiff 𝕜 n f → m ≤ n → ContDiff 𝕜 m f`,
and `∞ < ⊤` in `WithTop ℕ∞`).  `Work.BoseKinLoc.BoxState.contDiff` is exactly the smooth one.

PROOF RECIPE: the same pattern as `Work.BoseFixB1S.sbWordCubeIntegrable`'s private
`integrable_of_support_bound` (`Submission/Work/BoseFixB1S/sbWordCubeIntegrable.lean:33`):
`fibSum h M ℓ d u Φ` vanishes for `u` outside the fixed cube `acube (2ν)` with
`ν = (1+d)/(2d)` (the `u`-support of `χ_{B(u)}(z)` for `z ∈ acube ℓ` is `{|u_j| ≤ 1/(2d) + 1/2}`),
that cube has finite measure, and the function is uniformly bounded in `u`: `Φ` is continuous hence
bounded on the compact `abox n ℓ`, and `|∫ y in acube ℓ, wSmall1Pair h M ℓ d u z y|` is bounded
uniformly in `u` and `z` by `Work.BoseFixB1.wSmall1Pair_fibre_abs_le`.  (A sibling agent's
`Submission/Work/BoseB1Cube/fibSumOffCube.lean` and `fibSumUniformBound.lean` already contain the
vanishing and the uniform bound, and `aestronglyMeasurable_fibSum` the a.e. measurability — import
and glue them if they are green.) -/
theorem fibSumIntegrableB {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hRd : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.fibSum h M ℓ d u Φ) := by
  -- (1) a.e. strong measurability in `u`
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun u : E3 => Work.BoseFixB1.fibSum h M ℓ d u Φ)
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    aestronglyMeasurable_fibSumB h hR hv_supp hM (ℓ := ℓ) (d := d) Φ hΦ.continuous
  -- (2) a uniform bound in `u`
  obtain ⟨B, hB0, hB⟩ := fibSumUniformBound h hv hvrad hR hv_supp hM hℓ hd hRd hRχ Φ hΦ.continuous
  -- (3) vanishing off the fixed `u`-cube, which has finite volume
  set K : Set E3 := Submission.BoseGases.acube ((1 + d) / d) with hKdef
  have hKmeas : MeasurableSet K := Submission.BoseGases.acube_measurable _
  have hKfin : (MeasureTheory.volume : MeasureTheory.Measure E3) K ≠ ⊤ :=
    ne_of_lt (Submission.BoseGases.acube_lt_top _ (by positivity))
  have hg : MeasureTheory.Integrable (K.indicator fun _ : E3 => B)
      (MeasureTheory.volume : MeasureTheory.Measure E3) := by
    rw [MeasureTheory.integrable_indicator_iff hKmeas]
    exact MeasureTheory.integrableOn_const hKfin (by simp)
  refine MeasureTheory.Integrable.mono' hg hmeas ?_
  filter_upwards with u
  by_cases hu : u ∈ K
  · rw [Set.indicator_of_mem hu, Real.norm_eq_abs]
    exact hB u
  · rw [Set.indicator_of_notMem hu, Real.norm_eq_abs,
      fibSumOffCube h hM hℓ hd hu Φ, abs_zero]

end Work.BoseB1Cube
