import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotOper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped Real BigOperators ENNReal
open Submission.BoseGases

set_option maxHeartbeats 1000000

/-!
# `Work.BoseFixB1S.slotPIndFlatMul` — the flat-slot identity for a product of fixed slots

The `slotPInd_fibre_eq` (`BoseFixB1/boxMuAgreeB1`) argument, generalised from `(PᵢΦ)²` to an
arbitrary product `Ψ·Θ` of two `Pᵢ`-fixed measurable slots.

The structural input is `flatSlotPInd_fixed_eq`: `Pᵢ`-fixedness of `Ψ` says exactly that, at a
configuration with the `i`-th slot set to `t`, `Ψ` is `1_A(t)` times the slot-`i`-independent box
mean of `Ψ` (this is `boxPInd_kcInsN` plus the fixed-point equation `hΨfix`).  Hence on the peeled
configuration

  `Ψ(kcIns(y,r))·Θ(kcIns(y,r))·g(y) = ((1/volA)∫_A Ψ(kcIns(z,r))dz)·((1/volA)∫_A Θ(kcIns(z,r))dz)
                                        · 1_A(y)·g(y)`

(`1_A(y)² = 1_A(y)`), and the `y`-integral collapses through
`∫_{acube ℓ} 1_A·g = ∫_A g` (`setIntegral_indicator_one_mul`).  Comparing the fibre `g := fib`
with `g := 1` produces the factor `(∫_A fib)/volA`.

Everything is packaged as `flatSlotMul_integral` (general fibre `g`, own integrability side
condition) and the two integrability facts come from `integrableOn_slotMul_of_bound`.
-/

/-- **A `Pᵢ`-fixed slot, evaluated at an inserted configuration.**  If `Ψ` is fixed by
`Pᵢ = boxPInd volA A i`, then at every configuration whose `i`-th slot is `y` and whose remaining
slots are `r`, the value of `Ψ` is the box indicator at `y` times the (`i`-slot-independent) box
mean of `Ψ`. -/
theorem flatSlotPInd_fixed_eq {n : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (i : Fin (n + 1)) {Ψ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΨfix : UBBInputs8.boxPInd volA A i Ψ = Ψ)
    (y : EuclideanSpace ℝ (Fin 3)) (r : Submission.BoseGases.X n) :
    Ψ (Submission.BoseGases.kcInsN n i (y, r))
      = A.indicator (fun _ => (1 : ℝ)) y
        * ((1 / volA) * ∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r))) := by
  have h := boxPInd_kcInsN volA A i Ψ y r
  rw [hΨfix] at h
  exact h

/-- **Slot integrability, bounded form.**  A bounded a.e.-strongly-measurable slot factor `S`
against a fibre `F` evaluated in one coordinate is integrable over the box.  (This is the
`N`-general bounded form of `Work.BoseFixB1.integrableOn_abox_slot_mul`.) -/
theorem integrableOn_slotMul_of_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {F : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hFm : AEStronglyMeasurable F (volume.restrict (Submission.BoseGases.acube ℓ)))
    {CF : ℝ} (hFb : ∀ z ∈ Submission.BoseGases.acube ℓ, |F z| ≤ CF)
    {S : Submission.BoseGases.X N → ℝ}
    (hSm : AEStronglyMeasurable S (volume.restrict (Submission.BoseGases.abox N ℓ)))
    {CS : ℝ} (hSb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |S x| ≤ CS) :
    IntegrableOn (fun x : Submission.BoseGases.X N => S x * F (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
  refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N ℓ hℓ.le)
    (hSm.mul (Submission.BoseGases.aem_comp_coord' i hFm)) (|CS| * |CF|) ?_
  rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
  refine ae_of_all _ (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_trans (hSb x hx) (le_abs_self CS))
    (le_trans (hFb (x i) (hx i)) (le_abs_self CF)) (abs_nonneg _) (abs_nonneg _)

/-- **The flat-slot product identity with a general fibre.**  For two `Pᵢ`-fixed slots `Ψ`, `Θ`
and an integrable fibre product,

    `∫_{abox (n+1) ℓ} Ψ·Θ·g(xᵢ)
       = (∫_A g)·volA⁻²·∫_{abox n ℓ} (∫_A Ψ(kcIns(z,r))dz)·(∫_A Θ(kcIns(z,r))dz)` .

The fibre `g := 1` instance turns this into `∫ Ψ·Θ` and yields the target ratio. -/
theorem flatSlotMul_integral {n : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin (n + 1))
    {Ψ Θ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΨfix : UBBInputs8.boxPInd volA A i Ψ = Ψ)
    (hΘfix : UBBInputs8.boxPInd volA A i Θ = Θ)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hInt : IntegrableOn (fun x : Submission.BoseGases.X (n + 1) => Ψ x * Θ x * g (x i))
      (Submission.BoseGases.abox (n + 1) ℓ) volume) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ, Ψ x * Θ x * g (x i))
      = (∫ z in A, g z) * (1 / volA) ^ 2
        * (∫ r in Submission.BoseGases.abox n ℓ,
            (∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r)))
              * (∫ z in A, Θ (Submission.BoseGases.kcInsN n i (z, r)))) := by
  have hpeel := Submission.BoseGases.abox_integral_peel (n := n) (ℓ := ℓ) i
    (fun x : Submission.BoseGases.X (n + 1) => Ψ x * Θ x * g (x i)) hInt
  simp only [Submission.BoseGases.kc_insN_apply_same] at hpeel
  have hinner : ∀ r : Submission.BoseGases.X n,
      (∫ y in Submission.BoseGases.acube ℓ,
          Ψ (Submission.BoseGases.kcInsN n i (y, r))
            * Θ (Submission.BoseGases.kcInsN n i (y, r)) * g y)
        = (∫ z in A, g z)
          * (((1 / volA) * ∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r)))
              * ((1 / volA) * ∫ z in A, Θ (Submission.BoseGases.kcInsN n i (z, r)))) := by
    intro r
    have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
        Ψ (Submission.BoseGases.kcInsN n i (y, r))
          * Θ (Submission.BoseGases.kcInsN n i (y, r)) * g y
          = ((1 / volA) * (∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r))))
            * ((1 / volA) * (∫ z in A, Θ (Submission.BoseGases.kcInsN n i (z, r))))
            * (A.indicator (fun _ => (1 : ℝ)) y * g y) := by
      intro y
      rw [flatSlotPInd_fixed_eq volA A i hΨfix y r,
        flatSlotPInd_fixed_eq volA A i hΘfix y r]
      by_cases hy : y ∈ A
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy]
    rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
          Ψ (Submission.BoseGases.kcInsN n i (y, r))
            * Θ (Submission.BoseGases.kcInsN n i (y, r)) * g y)
        = (fun y : EuclideanSpace ℝ (Fin 3) =>
            ((1 / volA) * (∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r))))
              * ((1 / volA) * (∫ z in A, Θ (Submission.BoseGases.kcInsN n i (z, r))))
              * (A.indicator (fun _ => (1 : ℝ)) y * g y)) from funext hpt]
    rw [MeasureTheory.integral_const_mul, setIntegral_indicator_one_mul hA hAc g]
    ring
  have houter : (∫ r in Submission.BoseGases.abox n ℓ, ∫ y in Submission.BoseGases.acube ℓ,
        Ψ (Submission.BoseGases.kcInsN n i (y, r))
          * Θ (Submission.BoseGases.kcInsN n i (y, r)) * g y)
      = (∫ z in A, g z) * (1 / volA) ^ 2
        * (∫ r in Submission.BoseGases.abox n ℓ,
            (∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r)))
              * (∫ z in A, Θ (Submission.BoseGases.kcInsN n i (z, r)))) := by
    rw [show (fun r : Submission.BoseGases.X n => ∫ y in Submission.BoseGases.acube ℓ,
          Ψ (Submission.BoseGases.kcInsN n i (y, r))
            * Θ (Submission.BoseGases.kcInsN n i (y, r)) * g y)
        = (fun r : Submission.BoseGases.X n => (∫ z in A, g z)
            * (((1 / volA) * ∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r)))
                * ((1 / volA) * ∫ z in A, Θ (Submission.BoseGases.kcInsN n i (z, r)))))
        from funext hinner]
    rw [MeasureTheory.integral_const_mul]
    have h2 : (∫ r in Submission.BoseGases.abox n ℓ,
          ((1 / volA) * ∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r)))
            * ((1 / volA) * ∫ z in A, Θ (Submission.BoseGases.kcInsN n i (z, r))))
        = (1 / volA) ^ 2 * (∫ r in Submission.BoseGases.abox n ℓ,
            (∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r)))
              * (∫ z in A, Θ (Submission.BoseGases.kcInsN n i (z, r)))) := by
      rw [show (fun r : Submission.BoseGases.X n =>
            ((1 / volA) * ∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r)))
              * ((1 / volA) * ∫ z in A, Θ (Submission.BoseGases.kcInsN n i (z, r))))
          = (fun r : Submission.BoseGases.X n => (1 / volA) ^ 2
              * ((∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r)))
                * (∫ z in A, Θ (Submission.BoseGases.kcInsN n i (z, r)))))
          from funext (fun r => by ring)]
      rw [MeasureTheory.integral_const_mul]
    rw [h2]
    ring
  rw [hpeel, houter]

/-- **The generalised flat-slot identity.**  If `Ψ` and `Θ` are both fixed by the box projection
`Pᵢ = boxPInd volA A i` (so each equals `1_A(xᵢ)·(a function of the remaining slots)`), then for
*any* fibre `fib` (bounded and a.e. strongly measurable on the analysis cube),

    ∫_{abox (n+1) ℓ} fib(xᵢ)·Ψ·Θ = ((∫_A fib)/volA)·∫_{abox (n+1) ℓ} Ψ·Θ .

This generalises the PROVED `Work.BoseFixB1.slotPInd_fibre_eq` (the case `Ψ = Θ = PᵢΦ`, fibre
`w₁`) to an arbitrary product `ΨΘ` of `Pᵢ`-fixed measurable slots; it is the key step of the
`δ²`-bounds of the rung-4 crux of `Work.BoseFixB1S.interEstB1` (`fib := (w1Fibre ℓ w₁ − M₁/volA)²`
applied to `Xᵢ² = ((n₀ − 1 − μV)PᵢΦ)²`, whose factors are all `Pᵢ`-fixed).  Both slot hypotheses
are needed: `Ψ = Θ = Φ` is a counterexample as soon as `fib` is not constant on `A`.
Proof recipe: unfold `boxPInd`, use `hΨfix`/`hΘfix` to write `Ψ x = 1_A(xᵢ)·c(x_{≠i})`,
`Θ x = 1_A(xᵢ)·d(x_{≠i})` (the box mean is slot-`i`-independent and `1_A² = 1_A`), peel slot `i`
with `Submission.BoseGases.abox_integral_peel`, and use
`∫_{acube ℓ} 1_A·h = ∫_A h` — exactly the `slotPInd_fibre_eq` (`boxMuAgreeB1`) argument with
`(PᵢΦ)²` replaced by `ΨΘ`. -/
theorem slotPIndFlatMul {n : ℕ} {ℓ volA C D : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin (n + 1)) {Ψ Θ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΨm : Measurable Ψ) (hΘm : Measurable Θ)
    (hΨfix : Work.UBBInputs8.boxPInd volA A i Ψ = Ψ)
    (hΘfix : Work.UBBInputs8.boxPInd volA A i Θ = Θ)
    (hΨb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, |Ψ x| ≤ C)
    (hΘb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, |Θ x| ≤ C)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hFm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    (hFb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ D) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ, fib (x i) * (Ψ x * Θ x))
      = ((∫ z in A, fib z) / volA)
        * (∫ x in Submission.BoseGases.abox (n + 1) ℓ, Ψ x * Θ x) := by
  have hSmeas : AEStronglyMeasurable (fun x : Submission.BoseGases.X (n + 1) => Ψ x * Θ x)
      (volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) :=
    (hΨm.mul hΘm).aestronglyMeasurable
  have hSb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, |Ψ x * Θ x| ≤ C * C := by
    intro x hx
    rw [abs_mul]
    exact mul_le_mul (hΨb x hx) (hΘb x hx) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hΨb x hx))
  have hIntFib : IntegrableOn
      (fun x : Submission.BoseGases.X (n + 1) => (Ψ x * Θ x) * fib (x i))
      (Submission.BoseGases.abox (n + 1) ℓ) volume :=
    integrableOn_slotMul_of_bound hℓ i hFm hFb hSmeas hSb
  have hIntOne : IntegrableOn
      (fun x : Submission.BoseGases.X (n + 1) =>
        (Ψ x * Θ x) * (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) (x i))
      (Submission.BoseGases.abox (n + 1) ℓ) volume :=
    integrableOn_slotMul_of_bound hℓ i aestronglyMeasurable_const (fun z _ => by simp)
      (CF := 1) hSmeas hSb
  have hG := flatSlotMul_integral hA hAc i hΨfix hΘfix fib hIntFib
  have hG1 := flatSlotMul_integral hA hAc i hΨfix hΘfix
    (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) hIntOne
  set J : ℝ := ∫ r in Submission.BoseGases.abox n ℓ,
      (∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r)))
        * (∫ z in A, Θ (Submission.BoseGases.kcInsN n i (z, r))) with hJdef
  have hfib_comm : (∫ x in Submission.BoseGases.abox (n + 1) ℓ, fib (x i) * (Ψ x * Θ x))
      = ∫ x in Submission.BoseGases.abox (n + 1) ℓ, Ψ x * Θ x * fib (x i) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hmass : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        Ψ x * Θ x * (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) (x i))
      = ∫ x in Submission.BoseGases.abox (n + 1) ℓ, Ψ x * Θ x := by
    apply integral_congr_ae
    filter_upwards with x
    simp
  have hA1 : (∫ z in A, (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) z) = volA := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one,
      MeasureTheory.Measure.real_def, hvolA]
  have hmassJ : (∫ x in Submission.BoseGases.abox (n + 1) ℓ, Ψ x * Θ x)
      = volA * (1 / volA) ^ 2 * J := by
    rw [← hmass, hG1, hA1]
  have hvol' : volA ≠ 0 := ne_of_gt hvol
  rw [hfib_comm, hG, hmassJ]
  field_simp

end Work.BoseFixB1S
