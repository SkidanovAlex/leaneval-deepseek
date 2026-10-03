/-
# The Fourier coefficients of the symbol of a composed kernel

`Work.KMTAreas.A7.kernComp K κ κ'` is the kernel of the composition of the bilinear convolution
operator with kernel `K` with the two linear convolutions with kernels `κ`, `κ'`; its symbol is
the product of the symbols, i.e. `symSeq2 K x y * symSeq κ x * symSeq κ' y`.  This module proves
the resulting Fourier-coefficient identity

  `coeff2 (fun x y => symSeq2 K x y * symSeq κ x * symSeq κ' y) p₁ p₂ = kernComp K κ κ' p₁ p₂`

for a summable kernel `K : ℤ → ℤ → ℂ` (summability of `fun p => ‖K p.1 p.2‖`) and summable
`κ, κ' : ℤ → ℂ`.  This is the "kernel ↔ symbol" dictionary of §6 of Krause--Mirek--Tao in the
general (non finite-supported) case: the composition of the bilinear operator `bilinOp K` with
the two linear convolutions has symbol the product of the symbols.

The proof is the direct computation.  The product of the three absolutely convergent series
(`SymSeq2_mul_symSeq_eeC_tsum`) is the fourfold absolutely convergent series over
`(ℤ × ℤ) × (ℤ × ℤ)` whose `(x,y)`-modulus is the *constant* `‖K a b‖ ‖κ c‖ ‖κ' d‖`; that
constant modulus is what makes both interchanges of `tsum` with the iterated integral legal
(`MeasureTheory.integral_tsum`, applied in `y` for fixed `x` and then in `x`).  The remaining
iterated integral of each single term is evaluated by the orthogonality of the characters
(`integral_integral_kernelTerm`):
`∫₀¹∫₀¹ (K a b e(ax+by)) (κ c e(cx)) (κ' d e(dy)) e(-p₁x-p₂y) = K a b κ c κ' d [a+c=p₁] [b+d=p₂]`.
Summing over `w = ((a,b),(c,d))` and reindexing by the bijection
`((a,b),(c,d)) ↦ ((a+c,b+d),(c,d))` lands on the iterated sum defining `kernComp`:
`∑' c, ∑' d, K (p₁-c) (p₂-d) κ c κ' d = kernComp K κ κ' p₁ p₂`
(`tsum_kernelTerm_eq_kernComp`, via `A7.ModelApproxCore_aux.kernComp_eq_tsum`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SymSeq2_mul_symSeq_eeC_tsum
import Submission.Work.KMTPlan.A6.integral_integral_kernelTerm
import Submission.Work.KMTPlan.A6.tsum_kernelTerm_eq_kernComp
import Submission.Work.KMTPlan.A6.enorm_prod_tsum_ne_top
import Submission.Work.KMTPlan.A6.lintegral_enorm_kernelTerm

namespace Work.KMTPlan.A6

open MeasureTheory intervalIntegral
open scoped BigOperators ENNReal

noncomputable section

/-- Interchange of a `tsum` over an arbitrary countable index type with the interval integral
`∫₀¹`, the countable-index version of `SymSeq_coeff1.intervalIntegral_tsum`. -/
lemma intervalIntegral_tsum_countable {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ}
    (hmeas : ∀ i, AEStronglyMeasurable (F i) (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hsum : (∑' i, ∫⁻ x, ‖F i x‖ₑ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ≠ ∞) :
    ∫ x in (0 : ℝ)..1, (∑' i, F i x) = ∑' i, ∫ x in (0 : ℝ)..1, F i x := by
  simp only [intervalIntegral.integral_of_le zero_le_one]
  exact MeasureTheory.integral_tsum hmeas hsum

/-- The total mass of the measure of integration: `volume (Ioc 0 1) = 1`. -/
lemma volume_univ_Ioc : (volume.restrict (Set.Ioc (0 : ℝ) 1)) Set.univ = 1 := by
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
  norm_num

theorem SymSeq2_kernComp_coeff (K : ℤ → ℤ → ℂ) (κ κ' : ℤ → ℂ)
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (hκ : Summable κ) (hκ' : Summable κ') (p₁ p₂ : ℤ) :
    Work.KMTPlan.A6.coeff2 (fun x y => Work.KMTPlan.A6.symSeq2 K x y
        * Work.KMTPlan.A6.symSeq κ x * Work.KMTPlan.A6.symSeq κ' y) p₁ p₂
      = Work.KMTAreas.A7.kernComp K κ κ' p₁ p₂ := by
  -- the single term of the fourfold series, and the five computational pieces it is made of
  have pA : ∀ (x y : ℝ), symSeq2 K x y * symSeq κ x * symSeq κ' y
        * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)
      = ∑' w : (ℤ × ℤ) × (ℤ × ℤ), ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y) := fun x y =>
    SymSeq2_mul_symSeq_eeC_tsum K κ κ' hK hκ hκ' p₁ p₂ x y
  have pF : ∀ (x : ℝ) (w : (ℤ × ℤ) × (ℤ × ℤ)), ∫⁻ y, ‖((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)‖ₑ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = enorm (K w.1.1 w.1.2) * enorm (κ w.2.1) * enorm (κ' w.2.2) := fun x w =>
    lintegral_enorm_kernelTerm K κ κ' p₁ p₂ x w
  have pD : (∑' w : (ℤ × ℤ) × (ℤ × ℤ), enorm (K w.1.1 w.1.2) * enorm (κ w.2.1) * enorm (κ' w.2.2)) ≠ ⊤ :=
    enorm_prod_tsum_ne_top K κ κ' hK hκ hκ'
  have pB : ∀ w : (ℤ × ℤ) × (ℤ × ℤ), ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y) = K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2 * (if w.1.1 + w.2.1 = p₁ then 1 else 0) * (if w.1.2 + w.2.2 = p₂ then 1 else 0) := fun w =>
    integral_integral_kernelTerm K κ κ' p₁ p₂ w
  have pC : (∑' w : (ℤ × ℤ) × (ℤ × ℤ), K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2 * (if w.1.1 + w.2.1 = p₁ then 1 else 0) * (if w.1.2 + w.2.2 = p₂ then 1 else 0)) = Work.KMTAreas.A7.kernComp K κ κ' p₁ p₂ :=
    tsum_kernelTerm_eq_kernComp K κ κ' hK hκ hκ' p₁ p₂
  -- the two interchanges of the (absolutely convergent) series with the integrals
  have hswap1 : ∀ x : ℝ, ∫ y in (0 : ℝ)..1, (∑' w : (ℤ × ℤ) × (ℤ × ℤ), ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y))
      = ∑' w : (ℤ × ℤ) × (ℤ × ℤ), ∫ y in (0 : ℝ)..1, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y) := by
    intro x
    refine intervalIntegral_tsum_countable (F := fun (w : (ℤ × ℤ) × (ℤ × ℤ)) (y : ℝ) => ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)) ?_ ?_
    · intro w
      exact (by unfold eeC; fun_prop : Continuous fun y : ℝ => ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)).aestronglyMeasurable
    · rw [tsum_congr (fun w => pF x w)]
      exact pD
  have hmeas2 : ∀ w : (ℤ × ℤ) × (ℤ × ℤ), AEStronglyMeasurable (fun x : ℝ => ∫ y in (0 : ℝ)..1, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro w
    have hcont : Continuous fun p : ℝ × ℝ => ((K w.1.1 w.1.2 * eeC (w.1.1 * p.1 + w.1.2 * p.2)) * (κ w.2.1 * eeC (w.2.1 * p.1) * (κ' w.2.2 * eeC (w.2.2 * p.2)))) * eeC (-(p₁ : ℝ) * p.1 - (p₂ : ℝ) * p.2) := by unfold eeC; fun_prop
    have hsm : StronglyMeasurable (fun x : ℝ => ∫ y, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
      MeasureTheory.StronglyMeasurable.integral_prod_right
        (f := fun (x y : ℝ) => ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)) (by
          show StronglyMeasurable fun p : ℝ × ℝ => ((K w.1.1 w.1.2 * eeC (w.1.1 * p.1 + w.1.2 * p.2)) * (κ w.2.1 * eeC (w.2.1 * p.1) * (κ' w.2.2 * eeC (w.2.2 * p.2)))) * eeC (-(p₁ : ℝ) * p.1 - (p₂ : ℝ) * p.2)
          exact hcont.stronglyMeasurable)
    have hfun : (fun x : ℝ => ∫ y in (0 : ℝ)..1, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)) = fun x : ℝ => ∫ y, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      funext x
      rw [intervalIntegral.integral_of_le zero_le_one]
    rw [hfun]
    exact hsm.aestronglyMeasurable
  have hbound2 : (∑' w : (ℤ × ℤ) × (ℤ × ℤ), ∫⁻ x, ‖∫ y in (0 : ℝ)..1, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)‖ₑ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ≠ ∞ := by
    refine ne_top_of_le_ne_top pD (ENNReal.tsum_le_tsum (fun w => ?_))
    have hpt : ∀ x : ℝ, ‖∫ y in (0 : ℝ)..1, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)‖ₑ ≤ enorm (K w.1.1 w.1.2) * enorm (κ w.2.1) * enorm (κ' w.2.2) := by
      intro x
      have h1 : ‖∫ y in (0 : ℝ)..1, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)‖ₑ ≤ ∫⁻ y, ‖((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)‖ₑ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
        rw [intervalIntegral.integral_of_le zero_le_one]
        exact MeasureTheory.enorm_integral_le_lintegral_enorm _
      exact h1.trans_eq (pF x w)
    calc ∫⁻ x, ‖∫ y in (0 : ℝ)..1, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)‖ₑ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
        ≤ ∫⁻ x, (enorm (K w.1.1 w.1.2) * enorm (κ w.2.1) * enorm (κ' w.2.2)) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := lintegral_mono hpt
      _ = enorm (K w.1.1 w.1.2) * enorm (κ w.2.1) * enorm (κ' w.2.2) := by rw [MeasureTheory.lintegral_const, volume_univ_Ioc, mul_one]
  have hswap2 : ∫ x in (0 : ℝ)..1, (∑' w : (ℤ × ℤ) × (ℤ × ℤ), ∫ y in (0 : ℝ)..1, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y))
      = ∑' w : (ℤ × ℤ) × (ℤ × ℤ), ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y) :=
    intervalIntegral_tsum_countable (F := fun (w : (ℤ × ℤ) × (ℤ × ℤ)) (x : ℝ) => ∫ y in (0 : ℝ)..1, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y))
      hmeas2 hbound2
  calc coeff2 (fun x y => symSeq2 K x y * symSeq κ x * symSeq κ' y) p₁ p₂
      = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, symSeq2 K x y * symSeq κ x * symSeq κ' y
          * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y) := rfl
    _ = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, (∑' w : (ℤ × ℤ) × (ℤ × ℤ), ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)) := by
        refine intervalIntegral.integral_congr (fun x _ =>
          intervalIntegral.integral_congr (fun y _ => ?_))
        exact pA x y
    _ = ∫ x in (0 : ℝ)..1, (∑' w : (ℤ × ℤ) × (ℤ × ℤ), ∫ y in (0 : ℝ)..1, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)) := by
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        exact hswap1 x
    _ = ∑' w : (ℤ × ℤ) × (ℤ × ℤ), ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y)) * (κ w.2.1 * eeC (w.2.1 * x) * (κ' w.2.2 * eeC (w.2.2 * y)))) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y) := hswap2
    _ = ∑' w : (ℤ × ℤ) × (ℤ × ℤ), K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2 * (if w.1.1 + w.2.1 = p₁ then 1 else 0) * (if w.1.2 + w.2.2 = p₂ then 1 else 0) := tsum_congr pB
    _ = Work.KMTAreas.A7.kernComp K κ κ' p₁ p₂ := pC

end

end Work.KMTPlan.A6
