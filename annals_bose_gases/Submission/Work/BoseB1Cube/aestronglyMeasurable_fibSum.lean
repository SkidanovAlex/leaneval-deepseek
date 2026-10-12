import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.WB.sig_eq
import Submission.Work.BoseFixB1.perBoxF_localised
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.aestronglyMeasurable_fibSum`

A.e. strong measurability in the sliding parameter `u ∈ ℝ³` of the one-body fibre sum

    `fibSum h M ℓ d u Φ = ∫ x in abox n ℓ, Φ x ^ 2 * Σᵢ ∫_{y ∈ acube ℓ} wSmall1Pair h M ℓ d u (xᵢ) y`

(`Submission/Work/BoseFixB1/perBoxF_localised.lean`).  This is the measurability input needed to
integrate the per-box demand against `u` (over `goodSet`, `interiorSet` and their complements).

The proof never unfolds the kernel `wSmall1Pair`: the corpus lemma
`Work.BoseFixB1.WB.aesm_uncurry_wSmall1Pair` already gives its a.e. strong measurability as a
function of the *uncurried* triple `((u,z),y)`, and the slot-`i` joint integrand is that function
composed with the coordinate map `((u,x),y) ↦ ((u,xᵢ),y)`, which is quasi-measure-preserving
(`qmp_triple`, from `Measure.quasiMeasurePreserving_eval` and `volume_pi`).  Then

* `AEStronglyMeasurable.integral_prod_right'` integrates out `y` over `volume.restrict (acube ℓ)`
  (the space `X n` being restricted to `abox n ℓ`, which only *shrinks* the measure, so the joint
  a.e. strong measurability transports by `mono_measure` — no quasi-measure-preservation is needed
  for the restrictions);
* `Finset.aestronglyMeasurable_sum` adds the `n` slots, `Measurable.mul` brings in `Φ²`;
* `AEStronglyMeasurable.integral_prod_right'` integrates out `x` over `volume.restrict (abox n ℓ)`.

Only `hM : 1 ≤ M` and the measurability of `Φ` are used; `hR` and `hv_supp` are carried because the
colleagues' downstream statements carry them.
-/

namespace Work.BoseB1Cube

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **Quasi-measure-preservation of the slot coordinate map** `((u,x),y) ↦ ((u,xᵢ),y)`:
both factors are Lebesgue measure, and a single coordinate of `X n` is Lebesgue. -/
private lemma qmp_triple (n : ℕ) (i : Fin n) :
    Measure.QuasiMeasurePreserving
      (fun z : (E3 × Submission.BoseGases.X n) × E3 => ((z.1.1, z.1.2 i), z.2))
      (((volume : Measure E3).prod (volume : Measure (Submission.BoseGases.X n))).prod
        (volume : Measure E3))
      (((volume : Measure E3).prod (volume : Measure E3)).prod (volume : Measure E3)) := by
  have hE : Measure.QuasiMeasurePreserving (fun x : Submission.BoseGases.X n => x i)
      (volume : Measure (Submission.BoseGases.X n)) (volume : Measure E3) := by
    have h := Measure.quasiMeasurePreserving_eval
        (fun _ : Fin n => (volume : Measure E3)) i
    rwa [← MeasureTheory.volume_pi] at h
  exact MeasureTheory.QuasiMeasurePreserving.prodMap
    (MeasureTheory.QuasiMeasurePreserving.prodMap (Measure.QuasiMeasurePreserving.id _) hE)
    (Measure.QuasiMeasurePreserving.id _)

/-- The joint function `((u,x),y) ↦ wSmall1Pair h M ℓ d u (xᵢ) y` (the `i`-th slot of the fibre
integrand).  Introduced as a `def` so that the (large) implicit arguments of `wSmall1Pair` are
never unfolded during unification. -/
private def kernFun {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ) {n : ℕ}
    (i : Fin n) : (E3 × Submission.BoseGases.X n) × E3 → ℝ :=
  fun z => Submission.BoseGases.wSmall1Pair h M ℓ d z.1.1 (z.1.2 i) z.2

/-- A.e. strong measurability of the slot-`i` joint integrand, from the corpus's uncurried form
`Work.BoseFixB1.WB.aesm_uncurry_wSmall1Pair` composed with `qmp_triple`. -/
private lemma aesm_kernFun {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} {n : ℕ} (i : Fin n) :
    MeasureTheory.AEStronglyMeasurable (kernFun h M ℓ d i)
      (((volume : Measure E3).prod (volume : Measure (Submission.BoseGases.X n))).prod
        (volume : Measure E3)) :=
  (Work.BoseFixB1.WB.aesm_uncurry_wSmall1Pair (v := v) (h := h) hM ℓ d).comp_quasiMeasurePreserving
    (f := fun z : (E3 × Submission.BoseGases.X n) × E3 => ((z.1.1, z.1.2 i), z.2))
    (qmp_triple n i)

/-- A.e. strong measurability of the fibre integral at the slot `i`, as a function of `(u,x)`. -/
private lemma aesm_fibre_integral {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} {n : ℕ} (i : Fin n) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : E3 × Submission.BoseGases.X n =>
        ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d q.1 (q.2 i) y)
      ((volume : Measure E3).prod
        ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))) := by
  have hle : ((volume : Measure E3).prod
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))).prod
        ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      ≤ ((volume : Measure E3).prod (volume : Measure (Submission.BoseGases.X n))).prod
        (volume : Measure E3) :=
    Measure.prod_mono (Measure.prod_mono le_rfl Measure.restrict_le_self)
      Measure.restrict_le_self
  have hJ : MeasureTheory.AEStronglyMeasurable (kernFun h M ℓ d i)
      (((volume : Measure E3).prod
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))).prod
        ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    (aesm_kernFun (v := v) h hM i).mono_measure hle
  have h2 := MeasureTheory.AEStronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) hJ
  simpa only [kernFun] using h2

/-- A.e. strong measurability of the `Fin n`-sum of the fibre integrals, as a function of `(u,x)`. -/
private lemma aesm_sum_fibre {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} {n : ℕ} :
    MeasureTheory.AEStronglyMeasurable
      (fun q : E3 × Submission.BoseGases.X n =>
        ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d q.1 (q.2 i) y)
      ((volume : Measure E3).prod
        ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))) := by
  have hsum := Finset.aestronglyMeasurable_sum (s := Finset.univ)
    (f := fun i (q : E3 × Submission.BoseGases.X n) =>
      ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d q.1 (q.2 i) y)
    (fun i _ => aesm_fibre_integral (v := v) h hM (ℓ := ℓ) (d := d) i)
  refine hsum.congr ?_
  filter_upwards with q
  simp only [Finset.sum_apply]

theorem aestronglyMeasurable_fibSum {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (hΦ : Measurable Φ) :
    MeasureTheory.AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.fibSum h M ℓ d u Φ)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  have hsum := aesm_sum_fibre (v := v) h hM (ℓ := ℓ) (d := d) (n := n)
  have hΦ2 : Measurable fun q : E3 × Submission.BoseGases.X n => (Φ q.2) ^ 2 :=
    (hΦ.pow_const 2).comp measurable_snd
  have h3 : MeasureTheory.AEStronglyMeasurable
      (fun q : E3 × Submission.BoseGases.X n =>
        (Φ q.2) ^ 2 * ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d q.1 (q.2 i) y)
      ((volume : Measure E3).prod
        ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))) :=
    hΦ2.aestronglyMeasurable.mul hsum
  have h4 := MeasureTheory.AEStronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) h3
  simpa only [Work.BoseFixB1.fibSum] using h4

end

end Work.BoseB1Cube
