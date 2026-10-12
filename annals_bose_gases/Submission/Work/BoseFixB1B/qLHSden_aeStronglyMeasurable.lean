import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseFixB1.aesm_wSmallPair_pair
import Submission.Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre
import Submission.Work.BoseFixB1B.sectorCountBoxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.qLHSden_aeStronglyMeasurable`

The diagonal density `qLHSden` of the localised `qLHSword` at the `B1B` parameters,

    qLHSden n ℓ μ w w₁ x = −μ·Σᵢ w1Fibre ℓ w₁ (xᵢ) + ½·Σ_{p ∈ pairSet n} w (x_{p.1}) (x_{p.2}),

is **a.e.-strongly-measurable** on the big box `abox n ℓ`, for the localised kernels
`w = wSmallPair … v` (numerator the bare potential `v`, only `MemLp v 1`) and
`w₁ = wSmall1Pair h …` (numerator `g₀ v h`, only *a.e.* measurable).

Neither kernel is `Measurable` (their numerators are only a.e.-measurable), so the proof goes
through a.e.-measurability:

* **the one-body fibre.**  `aestronglyMeasurable_w1Fibre_wSmallPair` shows that
  `z ↦ w1Fibre ℓ (wSmallPair M ℓ d u f) z = ∫_{acube ℓ} wSmallPair M ℓ d u f z y` is
  a.e.-strongly-measurable on `ℝ³` from `AEMeasurable f`: the joint kernel is a.e.-strongly
  measurable on `volume ⊗ volume` (`Work.BoseFixB1.aesm_wSmallPair_prod_full`, whose content is
  the quasi-measure-preservation of the difference map `(x,y) ↦ x − y` for Lebesgue measure), the
  measure is restricted to the cube, and `AEStronglyMeasurable.integral_prod_right'` integrates.
  Then `qmp_eval_X` (the coordinate projection is quasi-measure-preserving, since `volume` on
  `X n = Fin n → ℝ³` is the product measure) transports it to the coordinate `xᵢ`.
* **the pair atoms.**  `Work.BoseFixB1.aesm_wSmallPair_pair` gives
  `x ↦ wSmallPair M ℓ d u v (x p.1) (x p.2)` directly, once more by composing with the
  quasi-measure-preserving two-coordinate projection.
* **the assembly.**  Finite sums and scalar multiples of a.e.-strongly-measurable `ℝ`-valued
  functions (`Finset.aestronglyMeasurable_sum`, `AEStronglyMeasurable.add`/`const_mul`) reassemble
  the density; the two functions agree definitionally after unfolding `qLHSden`.

No use is made of the extra hypotheses (`0 ≤ v`, radiality, `0 < a v`, `Adm`, `goodSet`): only
`MemLp v 1` (for `AEMeasurable v`) and `0 < R` + support (for the integrability of `g₀ v h`) enter.
-/

namespace Work.BoseFixB1B

open MeasureTheory

set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The coordinate projection is quasi-measure-preserving.**  On `X n = Fin n → ℝ³` the volume
is the product measure (`volume_pi`), and the evaluation map of a product measure onto a factor is
quasi-measure-preserving (`Measure.quasiMeasurePreserving_eval`). -/
lemma qmp_eval_X {n : ℕ} (i : Fin n) :
    Measure.QuasiMeasurePreserving (fun x : Submission.BoseGases.X n => x i)
      (volume : Measure (Submission.BoseGases.X n)) (volume : Measure E3) := by
  have h := Measure.quasiMeasurePreserving_eval
    (μ := fun _ : Fin n => (volume : Measure E3)) i
  simpa [volume_pi] using h

/-- **The one-body fibre of the localised kernel is a.e.-strongly-measurable.**  For an
a.e.-measurable numerator `f`, the function `z ↦ ∫_{acube ℓ} wSmallPair M ℓ d u f z y` is
a.e.-strongly-measurable on `ℝ³`.

The joint kernel is a.e.-strongly measurable for `volume ⊗ volume`
(`Work.BoseFixB1.aesm_wSmallPair_prod_full`), hence also for `volume ⊗ (volume ∣ acube ℓ)`; the
parametric-integral lemma `AEStronglyMeasurable.integral_prod_right'` then integrates out `y`. -/
lemma aestronglyMeasurable_w1Fibre_wSmallPair {M : ℕ} {ℓ d : ℝ} (u : E3) {f : E3 → ℝ}
    (hf : AEMeasurable f (volume : Measure E3)) :
    AEStronglyMeasurable
      (fun z : E3 => Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wSmallPair M ℓ d u f) z)
      (volume : Measure E3) := by
  have hjoint := Work.BoseFixB1.aesm_wSmallPair_prod_full (M := M) (ℓ := ℓ) (d := d) u hf
  have hjoint' : AEStronglyMeasurable
      (fun p : E3 × E3 => Submission.BoseGases.wSmallPair M ℓ d u f p.1 p.2)
      ((volume : Measure E3).prod
        ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    hjoint.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hint := AEStronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) hjoint'
  simpa only [Submission.BoseGases.w1Fibre] using hint

theorem qLHSden_aeStronglyMeasurable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    {ε₀ c C : ℝ} (hε₀ : 0 < ε₀) {μ : ℝ} (hμ : Work.BoseBoxFix.Adm v ε₀ μ)
    {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ)
    {n : ℕ} :
    MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.qLHSden n (Work.BoseFixB1B.PBℓ v μ) μ
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u v)
          (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u) x)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ))) := by
  -- the two numerators are a.e. measurable (`MemLp v 1`, and `g₀ v h` is integrable)
  have hva : AEMeasurable v (volume : Measure E3) := hv1.aestronglyMeasurable.aemeasurable
  have hg0 : AEMeasurable (Submission.BoseGases.g0 v h) (volume : Measure E3) :=
    (Submission.BoseGases.g0_integrable hR hv_supp h).aestronglyMeasurable.aemeasurable
  -- the one-body fibre at the fixed localisation centre `u`, transported to the `i`-th coordinate
  have hfib := aestronglyMeasurable_w1Fibre_wSmallPair (M := PBM v μ) (ℓ := PBℓ v μ)
    (d := PBd v μ) u (f := Submission.BoseGases.g0 v h) hg0
  have hsum1 : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n =>
        ∑ i : Fin n, Submission.BoseGases.w1Fibre (PBℓ v μ)
          (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) (x i))
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n (PBℓ v μ))) := by
    have h' : AEStronglyMeasurable
        (∑ i : Fin n, fun x : Submission.BoseGases.X n => Submission.BoseGases.w1Fibre (PBℓ v μ)
          (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) (x i))
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n (PBℓ v μ))) := by
      refine Finset.aestronglyMeasurable_sum (s := Finset.univ)
        (f := fun (i : Fin n) (x : Submission.BoseGases.X n) =>
          Submission.BoseGases.w1Fibre (PBℓ v μ)
            (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) (x i))
        (fun i _ => ?_)
      have h1 : AEStronglyMeasurable
          (fun x : Submission.BoseGases.X n => Submission.BoseGases.w1Fibre (PBℓ v μ)
            (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
              (Submission.BoseGases.g0 v h)) (x i))
          ((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n (PBℓ v μ))) :=
        (hfib.comp_quasiMeasurePreserving (qmp_eval_X i)).mono_measure
          Measure.restrict_le_self
      exact h1
    refine h'.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Finset.sum_apply]
  -- the pair atoms, with the bare potential as numerator
  have hsum2 : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n =>
        ∑ p ∈ Submission.BoseGases.pairSet n,
          Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v (x p.1) (x p.2))
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n (PBℓ v μ))) := by
    have h' : AEStronglyMeasurable
        (∑ p ∈ Submission.BoseGases.pairSet n, fun x : Submission.BoseGases.X n =>
          Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v (x p.1) (x p.2))
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n (PBℓ v μ))) := by
      refine Finset.aestronglyMeasurable_sum (s := Submission.BoseGases.pairSet n)
        (f := fun (p : Fin n × Fin n) (x : Submission.BoseGases.X n) =>
          Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v (x p.1) (x p.2))
        (fun p _ => ?_)
      exact Work.BoseFixB1.aesm_wSmallPair_pair (M := PBM v μ) (ℓ := PBℓ v μ) (d := PBd v μ)
        u hva p.1 p.2
    refine h'.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Finset.sum_apply]
  -- assemble `qLHSden = −μ·(fibre sum) + ½·(pair sum)`
  have hfin := (hsum1.const_mul (-μ)).add (hsum2.const_mul (1 / 2 : ℝ))
  refine hfin.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [Submission.BoseGases.qLHSden, Pi.add_apply]

end Work.BoseFixB1B
