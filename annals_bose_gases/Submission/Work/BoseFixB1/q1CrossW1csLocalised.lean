import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.amgmSlotSum
import Submission.Work.BoseFixB1.perSectorBoundG_holds
import Submission.Work.BoseFixB1.sumAPsqMulFibre
import Submission.Work.BoseFixB1S.boxM1Info
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.q1CrossW1csLocalised`

FS's per-slot AM–GM for the `w₁`-line of the localised small-box word, at the *localised*
kernels `w_{1,B(u)} = wSmall1Pair h M ℓ d u` (FS §SmallBoxes, the `Q₁`-cross term of
`thm:smallbox`).

The statement is the localised port of the proved global `Work.Q3Q4Peel.q1_cross_w1_cs_fs`:
with `f z = ∫_{acube ℓ} w_{1,B(u)}(z,y) dy` the fibre of the localised one-body kernel, the
completion of squares

    (√A·Qᵢ + t/√A·Pᵢ)² · f(xᵢ) ≥ 0 ,   A := 4·cS1/ℓ³

summed over the slots and integrated gives

    2t·Σᵢ∫ (QᵢΦ)(PᵢΦ) f(xᵢ) ≥ −(t²/4)·∬w_{1,B(u)} − A·Σᵢ∫ (QᵢΦ)² f(xᵢ),

the `P`-weighted mass being supplied by the localised mass identity

    Σᵢ∫ (PᵢΦ)² f(xᵢ) = (cS1/ℓ³)·∬w_{1,B(u)}          (`integralAcubeFibreW1MassB` + `sumAPsqMulFibre`)

(peel the `i`-th slot, then use that the fibre vanishes off the sliding box).

The constant `C` of the existential is a dummy: it does not occur in the bound.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Auxiliary facts about the localised fibre `z ↦ ∫_{acube ℓ} w_{1,B(u)}(z,y) dy` -/

/-- The localised fibre is nonnegative (`g₀ ≥ 0` a.e., all cutoff/renormalisation factors
nonnegative). -/
lemma q1cw1_w1Fibre_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) :
    ∀ z : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z := by
  intro z
  have h1 := wSmall1Pair_fibre_nonneg (v := v) (M := M) (ℓ := ℓ) (d := d)
    hR0 hv hvrad hv_supp h u z
  simpa only [Submission.BoseGases.w1Fibre] using h1

/-- The localised fibre is uniformly bounded by `Kfib M`. -/
lemma q1cw1_w1Fibre_abs_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∀ z : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z|
        ≤ Kfib (v := v) M := by
  intro z
  have h1 := w1Fibre_wSmall1Pair_abs_le (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u z
  simpa only [Submission.BoseGases.w1Fibre] using h1

/-- `0 ≤ Kfib M`, from `∫|g₀| = 8π a v`. -/
lemma q1cw1_Kfib_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Kfib (v := v) M := by
  have hg0 := Submission.BoseGases.g0_abs_integral (R := R0) hR0 hv hvrad hv_supp h
  have h0 : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h x| :=
    integral_nonneg (fun x => abs_nonneg _)
  have hav8 : 0 ≤ 8 * π * _root_.BoseGases.a v := by
    rw [← hg0]; exact h0
  have hD : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg (Submission.BoseGases.chiSmallDecay_nonneg M)
  unfold Kfib
  refine mul_nonneg hD (mul_nonneg ?_ hav8)
  refine div_nonneg (mul_nonneg (by norm_num) hD) ?_
  exact le_of_lt (Work.SmallBoxSliding.smallConvLower_pos M)

/-- **The localised mass identity**: the `acube ℓ`-integral of the localised fibre is the full
space mass `∬ w_{1,B(u)}` (both integrals see only the sliding box, where the kernel is
supported). -/
lemma q1cw1_integral_acube_w1Fibre {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    (∫ z in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      = w1MassB h M ℓ d u := by
  have hvan : ∀ x y : EuclideanSpace ℝ (Fin 3),
      (x ∉ Submission.BoseGases.dlBox ℓ d u ∨ y ∉ Submission.BoseGases.dlBox ℓ d u) →
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y = 0 :=
    fun x y hxy => Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u hxy
  have hInt : IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) :=
    integrableOn_wSmallPair_cube
      (f := Submission.BoseGases.g0 v h)
      (Submission.BoseGases.g0_integrable hR0 hv_supp h)
      (fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h) hM hℓ hd hR hRχ u
  have hnested := Work.BoseFixB1S.acubePair_eq_nested (ℓ := ℓ) (d := d) u hvan hInt
  have hprod := MeasureTheory.setIntegral_prod (μ := volume) (ν := volume)
      (s := Submission.BoseGases.acube ℓ) (t := Submission.BoseGases.acube ℓ)
      (f := fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2) hInt
  calc (∫ z in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      = (∫ z in Submission.BoseGases.acube ℓ,
        ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u z y) := rfl
    _ = (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2) := hprod.symm
    _ = (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmall1Pair h M ℓ d u x y) := hnested
    _ = w1MassB h M ℓ d u := rfl

/-! ## Temporary stubs for the two delegated lemmas (replaced by imports) -/

/-! ## The target -/

theorem q1CrossW1csLocalised {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
        (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
        (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
        (hΦc : Continuous Φ) (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1)
        (hS : 0 < Submission.BoseGases.cS1 ℓ Φ) (t : ℝ),
        2 * t * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x)
              * (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)))
          ≥ - (1 / 4) * t ^ 2 * (Work.BoseFixB1.w1MassB h M ℓ d u)
            - (4 * (Submission.BoseGases.cS1 ℓ Φ) / ℓ ^ 3)
              * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                  (Submission.BoseGases.aQ ℓ i Φ x) ^ 2
                    * (Submission.BoseGases.w1Fibre ℓ
                        (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))) := by
  classical
  refine ⟨0, le_refl 0, ?_⟩
  intro ℓ d μ hℓ hd hR hRχ u N Φ hΦc hnorm hS t
  set f : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun z => Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z with hfdef
  have hfnn : ∀ z, 0 ≤ f z := fun z => q1cw1_w1Fibre_nonneg hv_supp hR0 hv hvrad h u z
  have hfm : AEStronglyMeasurable f (volume.restrict (Submission.BoseGases.acube ℓ)) := by
    have h1 := aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
      (Submission.BoseGases.g0_integrable hR0 hv_supp h).aemeasurable
    simpa only [hfdef, Submission.BoseGases.w1Fibre, Submission.BoseGases.wSmall1Pair] using h1
  have hfb : ∀ z ∈ Submission.BoseGases.acube ℓ, |f z| ≤ Kfib (v := v) M := by
    intro z _
    have h1 := q1cw1_w1Fibre_abs_le hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u z
    simpa only [hfdef] using h1
  have hB0 : 0 ≤ Kfib (v := v) M := q1cw1_Kfib_nonneg hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u
  have hmassid : (∫ z in Submission.BoseGases.acube ℓ, f z) = w1MassB h M ℓ d u := by
    have h1 := q1cw1_integral_acube_w1Fibre hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u
    simpa only [hfdef] using h1
  have hpel : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ i Φ x) ^ 2 * f (x i))
      = (Submission.BoseGases.cS1 ℓ Φ / ℓ ^ 3) * (∫ z in Submission.BoseGases.acube ℓ, f z) :=
    sumAPsqMulFibre hℓ hΦc hfm hB0 hfb
  have hmass : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ i Φ x) ^ 2 * f (x i))
      = ((4 * Submission.BoseGases.cS1 ℓ Φ / ℓ ^ 3) / 4) * (w1MassB h M ℓ d u) := by
    rw [hpel, hmassid]
    ring
  have hApos : 0 < 4 * Submission.BoseGases.cS1 ℓ Φ / ℓ ^ 3 :=
    div_pos (mul_pos (by norm_num) hS) (pow_pos hℓ 3)
  have hW0 : 0 ≤ w1MassB h M ℓ d u :=
    w1MassB_nonneg (v := v) h hv hvrad hR0 hv_supp hℓ hd u
  have hchild := amgmSlotSum (N := N) (ℓ := ℓ) hℓ
    (P := fun i => Submission.BoseGases.aP ℓ i Φ)
    (Q := fun i => Submission.BoseGases.aQ ℓ i Φ)
    (fun i => Submission.BoseGases.aP_continuous hℓ i hΦc)
    (fun i => Submission.BoseGases.aQ_continuous hℓ i hΦc)
    hfnn hfm hB0 hfb (A := 4 * Submission.BoseGases.cS1 ℓ Φ / ℓ ^ 3)
    (t := t) (W := w1MassB h M ℓ d u) hApos hW0 hmass
  exact hchild

end Work.BoseFixB1
