import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre
import Submission.Work.BoseFixB1.wSmall1Pair_fibre_abs_le
import Submission.Work.BoseFixB1S.BoxPIndFlat
import Submission.Work.BoseFixB1S.BoxQIndCore
import Submission.Work.SlotWord.chiSmallB_support_mem_dlBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory
open Submission.BoseGases

set_option maxHeartbeats 1600000

/-!
# `Work.BoseFixB1.boxMuAgreeB1` — the `μ`-line agrees with the flat-branch form

The two `μ`-lines of the FS-faithful box-projection potential word at the sliding box
`A = B(u) = dlBox ℓ d u` (`volA = boxMass ℓ d u = |A|`) agree with the flat-branch
expression `μ·(M₁/|A|)·S − μ·Σᵢ∫(1_A(xᵢ)Φ)²w₁(xᵢ)`:

    `−2μ Σᵢ∫ (QᵢΦ)(PᵢΦ) w₁(xᵢ) − μ Σᵢ∫ (QᵢΦ)² w₁(xᵢ)`
      `= μ·(M₁/|A|)·S − μ Σᵢ∫ (1_A(xᵢ)Φ)² w₁(xᵢ)` ,

`S = boxFlatCount = Σᵢ∫(PᵢΦ)²`, `M₁ = boxM1 = ∫_A w₁(·,·)`.

The proof is the two structural facts

* **the flat slot identity** (`slotPInd_fibre_eq`): since `PᵢΦ = 1_A(xᵢ)·cᵢ(x_{≠i})` factors
  through the box indicator and a *slot-independent* mean `cᵢ`,
  `∫ (PᵢΦ)²·g(xᵢ) = (∫_A g)·|A|⁻¹·∫ (PᵢΦ)²` for every fibre `g` (here `g = w₁`);
* **the pointwise square identity**: `Pᵢ + Qᵢ = 1_A(xᵢ)Φ`, hence
  `2(QᵢΦ)(PᵢΦ) + (QᵢΦ)² = (1_A(xᵢ)Φ)² − (PᵢΦ)²`.

## The flat slot identity

`PᵢΦ = 1_A(xᵢ)·cᵢ(x_{≠i})`: this is `boxPInd_kcInsN`, and it is *exactly* where the box
indicator matters — the corpus's centred projection would be slot-independent but carry no
indicator.  Peeling the `i`-th coordinate (`Submission.BoseGases.abox_integral_peel`) and
using `∫_{acube ℓ} 1_A·h = ∫_A h` (`setIntegral_indicator_one_mul`) gives both sides of the
identity with the same `∫_{abox n ℓ}(∫_A Φ(·|i↦z)dz)²`, whence the ratio `(∫_A g)/|A|`.
-/

/-- **Slot integrability.**  A bounded a.e.-strongly-measurable slot factor `S` against a
fibre `F` evaluated in one coordinate is integrable over the box.  (The corpus's
`Submission.BoseGases.integrableOn_slot_fibre` is the special case of *continuous* `S`; the box
projections here are only measurable.) -/
theorem integrableOn_abox_slot_mul {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {F : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hFm : AEStronglyMeasurable F (volume.restrict (Submission.BoseGases.acube ℓ)))
    {C : ℝ} (hC : ∀ z ∈ Submission.BoseGases.acube ℓ, |F z| ≤ C)
    {S : Submission.BoseGases.X N → ℝ}
    (hSm : AEStronglyMeasurable S (volume.restrict (Submission.BoseGases.abox N ℓ)))
    {B : ℝ} (hB : ∀ x ∈ Submission.BoseGases.abox N ℓ, |S x| ≤ B) :
    IntegrableOn (fun x : Submission.BoseGases.X N => S x * F (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
  have hAm : AEStronglyMeasurable (fun x : Submission.BoseGases.X N => S x * F (x i))
      (volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    hSm.mul (Submission.BoseGases.aem_comp_coord' i hFm)
  refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N ℓ hℓ.le) hAm (|B| * |C|) ?_
  rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
  refine ae_of_all _ (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_trans (hB x hx) (le_abs_self B))
    (le_trans (hC (x i) (hx i)) (le_abs_self C)) (abs_nonneg _) (abs_nonneg _)

/-- **The peeled slot integral of a box projection.**  For the FS-faithful box projection
`Pᵢ = boxPInd volA A i` (carrying the box indicator `1_A`) and *any* fibre `g`,

    `∫_{abox (n+1) ℓ} (PᵢΦ)²·g(xᵢ) = (∫_A g)·volA⁻²·∫_{abox n ℓ} (∫_A Φ(·|i↦z)dz)²` .

The `i`-th coordinate is peeled (`abox_integral_peel`); in the peeled variables the integrand
is `1_A(y)·cᵢ(r)²·g(y)` with `cᵢ(r) = volA⁻¹∫_A Φ(·|i↦z)dz` *independent of* `y`, so the
`y`-integral is `cᵢ(r)²∫_{acube ℓ}1_A·g = cᵢ(r)²∫_A g`. -/
theorem slotPInd_mul_integral {n : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin (n + 1))
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hInt : IntegrableOn
      (fun x : Submission.BoseGases.X (n + 1) =>
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * g (x i))
      (Submission.BoseGases.abox (n + 1) ℓ) volume) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * g (x i))
      = (∫ z in A, g z) * (1 / volA) ^ 2
        * (∫ r in Submission.BoseGases.abox n ℓ,
            (∫ z in A, Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2) := by
  have hpeel := Submission.BoseGases.abox_integral_peel (n := n) (ℓ := ℓ) i
    (fun x : Submission.BoseGases.X (n + 1) =>
      (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * g (x i)) hInt
  simp only [Submission.BoseGases.kc_insN_apply_same] at hpeel
  have hinner : ∀ r : Submission.BoseGases.X n,
      (∫ y in Submission.BoseGases.acube ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2
            * g y)
        = (∫ z in A, g z)
          * ((1 / volA) * ∫ z in A, Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2 := by
    intro r
    have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
        (Work.UBBInputs8.boxPInd volA A i Φ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2 * g y
          = ((1 / volA) * ∫ z in A, Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2
              * (A.indicator (fun _ => (1 : ℝ)) y * g y) := by
      intro y
      rw [Work.BoseFixB1S.boxPInd_kcInsN]
      have hs : A.indicator (fun _ => (1 : ℝ)) y ^ 2 = A.indicator (fun _ => (1 : ℝ)) y := by
        by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
      rw [mul_pow, hs]
      ring
    rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
          (Work.UBBInputs8.boxPInd volA A i Φ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2
            * g y)
        = (fun y : EuclideanSpace ℝ (Fin 3) =>
            ((1 / volA) * ∫ z in A, Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2
              * (A.indicator (fun _ => (1 : ℝ)) y * g y)) from funext hpt]
    rw [MeasureTheory.integral_const_mul, Work.BoseFixB1S.setIntegral_indicator_one_mul hA hAc g]
    ring
  have houter : (∫ r in Submission.BoseGases.abox n ℓ,
        ∫ y in Submission.BoseGases.acube ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2
            * g y)
      = (∫ z in A, g z) * (1 / volA) ^ 2
        * (∫ r in Submission.BoseGases.abox n ℓ,
            (∫ z in A, Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2) := by
    rw [show (fun r : Submission.BoseGases.X n =>
          ∫ y in Submission.BoseGases.acube ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2
              * g y)
        = (fun r : Submission.BoseGases.X n =>
            (∫ z in A, g z)
              * ((1 / volA) * ∫ z in A, Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2)
        from funext hinner]
    rw [MeasureTheory.integral_const_mul]
    have h2 : (∫ r in Submission.BoseGases.abox n ℓ,
          ((1 / volA) * ∫ z in A, Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2)
        = (1 / volA) ^ 2 * (∫ r in Submission.BoseGases.abox n ℓ,
            (∫ z in A, Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2) := by
      rw [show (fun r : Submission.BoseGases.X n =>
            ((1 / volA) * ∫ z in A, Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2)
          = (fun r : Submission.BoseGases.X n =>
              (1 / volA) ^ 2 * (∫ z in A, Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2)
          from funext (fun r => by ring)]
      rw [MeasureTheory.integral_const_mul]
    rw [h2]
    ring
  rw [hpeel, houter]

/-- **The flat slot identity.**  For the fibre `fib` on the box `A ⊆ acube ℓ` of volume `volA`,

    `∫_{abox (n+1) ℓ} (PᵢΦ)²·fib(xᵢ) = ((∫_A fib)/volA)·∫_{abox (n+1) ℓ} (PᵢΦ)²` .

This is the `g := fib` instance of `slotPInd_mul_integral` compared with its `g := 1`
instance, using `∫_A 1 = volA`. -/
theorem slotPInd_fibre_eq {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin (n + 1)) {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦm : Measurable Φ)
    {C : ℝ} (hΦb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, |Φ x| ≤ C)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hFm : AEStronglyMeasurable fib (volume.restrict (Submission.BoseGases.acube ℓ)))
    {D : ℝ} (hFb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ D) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i))
      = ((∫ z in A, fib z) / volA)
        * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
  have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA i hΦm
  have hPb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
      |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb
  have hIntFib : IntegrableOn
      (fun x : Submission.BoseGases.X (n + 1) =>
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i))
      (Submission.BoseGases.abox (n + 1) ℓ) volume :=
    integrableOn_abox_slot_mul hℓ i hFm hFb (hPm.pow_const 2).aestronglyMeasurable
      (B := C ^ 2) (fun x hx => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hPb x hx) 2)
  have hIntOne : IntegrableOn
      (fun x : Submission.BoseGases.X (n + 1) =>
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) (x i))
      (Submission.BoseGases.abox (n + 1) ℓ) volume :=
    integrableOn_abox_slot_mul hℓ i aestronglyMeasurable_const (C := 1)
      (fun z _ => by simp) (hPm.pow_const 2).aestronglyMeasurable
      (B := C ^ 2) (fun x hx => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hPb x hx) 2)
  have hA1 := slotPInd_mul_integral (n := n) (ℓ := ℓ) (volA := volA) hA hAc i Φ fib hIntFib
  have hA2 := slotPInd_mul_integral (n := n) (ℓ := ℓ) (volA := volA) hA hAc i Φ
    (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) hIntOne
  have hIntA : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      = volA * (1 / volA) ^ 2
        * (∫ r in Submission.BoseGases.abox n ℓ,
            (∫ z in A, Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2) := by
    have h1 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
            * (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) (x i))
        = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      simp
    rw [← h1, hA2, MeasureTheory.setIntegral_const]
    rw [smul_eq_mul, mul_one, MeasureTheory.Measure.real_def, hvolA]
  rw [hA1, hIntA]
  have hvol' : volA ≠ 0 := ne_of_gt hvol
  field_simp

theorem boxMuAgreeB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    - 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x)
          * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x)
          * (Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)))
      - μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
            * (Submission.BoseGases.w1Fibre ℓ
                (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)))
      = μ * ((Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u))
            / Work.SmallBoxSliding.boxMass ℓ d u)
          * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ
        - μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2
              * (Submission.BoseGases.w1Fibre ℓ
                  (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))) := by
  classical
  cases N with
  | zero => simp [Work.BoseFixB1S.boxFlatCount]
  | succ n =>
    set A : Set (EuclideanSpace ℝ (Fin 3)) := Submission.BoseGases.dlBox ℓ d u with hAdef
    set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvolAdef
    set W : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ :=
      Submission.BoseGases.wSmall1Pair h M ℓ d u with hWdef
    set fib : (EuclideanSpace ℝ (Fin 3)) → ℝ := Submission.BoseGases.w1Fibre ℓ W with hfibdef
    have hAmeas : MeasurableSet A := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
    have hAc : A ⊆ Submission.BoseGases.acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
    have hvolA_eq : volA = (volume A).toReal := by
      rw [hvolAdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal,
        MeasureTheory.Measure.real_def]
    have hvolpos : 0 < volA := by rw [hvolAdef]; exact hvol
    -- the localised fibre: a.e. strong measurability and a uniform (global) bound
    have hFm : AEStronglyMeasurable fib (volume.restrict (Submission.BoseGases.acube ℓ)) := by
      have hint : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) volume :=
        Submission.BoseGases.g0_integrable hR0 hv_supp h
      have hm := Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
        (f := Submission.BoseGases.g0 v h) hint.aestronglyMeasurable.aemeasurable
      exact hm
    have hFb : ∀ z ∈ Submission.BoseGases.acube ℓ,
        |fib z| ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M *
          (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) /
            Work.SmallBoxSliding.smallConvLower M * (8 * Real.pi * BoseGases.a v)) := by
      intro z _
      exact Work.BoseFixB1.wSmall1Pair_fibre_abs_le (v := v) (R0 := R0) hv_supp hR0 hv hvrad h
          hM hℓ hd hR hRχ u z
    obtain ⟨C₀, hC₀⟩ := (Submission.BoseGases.abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
      hΦc.continuousOn
    set C : ℝ := max C₀ 0 with hCdef
    have hC0 : 0 ≤ C := le_max_right _ _
    have hΦb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, |Φ x| ≤ C := by
      intro x hx
      have hh := hC₀ x hx
      rw [Real.norm_eq_abs] at hh
      exact le_trans hh (le_max_left _ _)
    -- the per-slot flat identity
    have hkey : ∀ i : Fin (n + 1),
        (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i))
          = ((∫ z in A, fib z) / volA)
            * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) :=
      fun i => slotPInd_fibre_eq hℓ hvolpos hAmeas hvolA_eq hAc i hΦc.measurable hΦb hFm hFb
    -- the per-slot square identity
    have hquad : ∀ i : Fin (n + 1),
        2 * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
                * fib (x i))
          + (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * fib (x i))
        = (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 * fib (x i))
          - (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i)) := by
      intro i
      have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
        Work.BoseFixB1S.measurable_boxPInd volA A hAmeas i hΦc.measurable
      have hPb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
          |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C :=
        Work.BoseFixB1S.abs_boxPInd_le hℓ hvolpos hAmeas hvolA_eq hAc i hΦb
      have hQeq : ∀ x : Submission.BoseGases.X (n + 1),
          Work.UBBInputs8.boxQInd volA A i Φ x
            = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
              - Work.UBBInputs8.boxPInd volA A i Φ x := fun x => rfl
      have hQm : Measurable
          (fun x : Submission.BoseGases.X (n + 1) => Work.UBBInputs8.boxQInd volA A i Φ x) := by
        have hfun : (fun x : Submission.BoseGases.X (n + 1) =>
              Work.UBBInputs8.boxQInd volA A i Φ x)
            = fun x => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
                - Work.UBBInputs8.boxPInd volA A i Φ x := by
          funext x
          rfl
        rw [hfun]
        exact (((measurable_const.indicator hAmeas).comp (measurable_pi_apply i)).mul
          hΦc.measurable).sub hPm
      have hQb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
          |Work.UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * C := by
        intro x hx
        rw [hQeq x]
        have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
          by_cases hxi : x i ∈ A <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
        calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
              - Work.UBBInputs8.boxPInd volA A i Φ x|
            ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
              + |Work.UBBInputs8.boxPInd volA A i Φ x| := abs_sub _ _
          _ ≤ 1 * |Φ x| + C := by
              refine add_le_add ?_ (hPb x hx)
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_right hind (abs_nonneg _)
          _ ≤ 2 * C := by
              have h1 := hΦb x hx
              linarith
      have hindb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
          |(A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2| ≤ C ^ 2 := by
        intro x hx
        have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
          by_cases hxi : x i ∈ A <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
        rw [abs_pow]
        calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ^ 2
            = (|A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x|) ^ 2 := by rw [abs_mul]
          _ ≤ (1 * C) ^ 2 := by
              refine pow_le_pow_left₀ (by positivity) ?_ 2
              exact mul_le_mul hind (hΦb x hx) (abs_nonneg _) (by norm_num)
          _ = C ^ 2 := by ring
      have hIntQP : IntegrableOn
          (fun x : Submission.BoseGases.X (n + 1) =>
            (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
              * fib (x i))
          (Submission.BoseGases.abox (n + 1) ℓ) volume :=
        integrableOn_abox_slot_mul hℓ i hFm hFb ((hQm.mul hPm).aestronglyMeasurable)
          (B := (2 * C) * C) (fun x hx => by
            rw [abs_mul]
            exact mul_le_mul (hQb x hx) (hPb x hx) (abs_nonneg _)
              (le_trans (abs_nonneg _) (hQb x hx)))
      have hIntQ : IntegrableOn
          (fun x : Submission.BoseGases.X (n + 1) =>
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * fib (x i))
          (Submission.BoseGases.abox (n + 1) ℓ) volume :=
        integrableOn_abox_slot_mul hℓ i hFm hFb ((hQm.pow_const 2).aestronglyMeasurable)
          (B := (2 * C) ^ 2) (fun x hx => by
            rw [abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) (hQb x hx) 2)
      have hIntP : IntegrableOn
          (fun x : Submission.BoseGases.X (n + 1) =>
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i))
          (Submission.BoseGases.abox (n + 1) ℓ) volume :=
        integrableOn_abox_slot_mul hℓ i hFm hFb ((hPm.pow_const 2).aestronglyMeasurable)
          (B := C ^ 2) (fun x hx => by
            rw [abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) (hPb x hx) 2)
      have hIntD : IntegrableOn
          (fun x : Submission.BoseGases.X (n + 1) =>
            (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 * fib (x i))
          (Submission.BoseGases.abox (n + 1) ℓ) volume :=
        integrableOn_abox_slot_mul hℓ i hFm hFb
          ((((measurable_const.indicator hAmeas).comp (measurable_pi_apply i)).mul
            hΦc.measurable).pow_const 2).aestronglyMeasurable (B := C ^ 2) hindb
      have hIntQP2 : IntegrableOn
          (fun x : Submission.BoseGases.X (n + 1) =>
            2 * ((Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
              * fib (x i)))
          (Submission.BoseGases.abox (n + 1) ℓ) volume := hIntQP.const_mul 2
      have hpt : ∀ x : Submission.BoseGases.X (n + 1),
          2 * ((Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
              * fib (x i))
            + (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * fib (x i)
          = (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 * fib (x i)
            - (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i) := by
        intro x
        rw [hQeq x]
        ring
      have h1 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            2 * ((Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
                * fib (x i))
              + (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * fib (x i))
          = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 * fib (x i)
                - (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i)) := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpt x
      have h2 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 * fib (x i)
                - (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i)))
          = (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 * fib (x i))
            - (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i)) :=
        MeasureTheory.integral_sub hIntD hIntP
      have h3 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            2 * ((Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
                * fib (x i))
              + (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * fib (x i))
          = (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              2 * ((Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
                * fib (x i)))
            + (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * fib (x i)) :=
        MeasureTheory.integral_add hIntQP2 hIntQ
      have h4 : 2 * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
              * fib (x i))
          = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              2 * ((Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
                * fib (x i)) :=
        (MeasureTheory.integral_const_mul 2
          (fun x : Submission.BoseGases.X (n + 1) =>
            (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
              * fib (x i))).symm
      linarith [h1, h2, h3, h4]
    -- the sums
    have hsumM : (∑ i : Fin (n + 1),
          (2 * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
                * fib (x i))
            + (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * fib (x i))))
        = (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 * fib (x i))
          - (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hquad i)
    have hsumP : (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i))
        = ((∫ z in A, fib z) / volA)
          * (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => hkey i)
    have hsumT : (∑ i : Fin (n + 1),
          (2 * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
                * fib (x i))
            + (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * fib (x i))))
        = 2 * (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
                * fib (x i))
          + (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * fib (x i)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hLHS : -2 * μ * (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
              * fib (x i))
          - μ * (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * fib (x i))
        = -μ * (∑ i : Fin (n + 1),
            (2 * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
                  * fib (x i))
              + (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * fib (x i)))) := by
      rw [hsumT]
      ring
    have hRHS : μ * ((Work.BoseFixB1S.boxM1 ℓ A W) / volA)
          * (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ)
          - μ * (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 * fib (x i))
        = μ * (((∫ z in A, fib z) / volA))
              * (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                  (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
          - μ * (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 * fib (x i)) := by
      simp only [Work.BoseFixB1S.boxM1, Work.BoseFixB1S.boxFlatCount, hfibdef]
    rw [hLHS, hsumM, hsumP, hRHS]
    ring

end Work.BoseFixB1
