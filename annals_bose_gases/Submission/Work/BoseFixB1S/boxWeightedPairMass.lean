import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.a0A2QPaymentB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped BigOperators
open Submission.BoseGases

namespace Work.BoseFixB1S

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Degenerate dimension: the pair set is empty for `N ≤ 1` -/

private theorem pairSet_eq_empty_of_le_one {N : ℕ} (hN : N ≤ 1) :
    Submission.BoseGases.pairSet N = ∅ := by
  rw [Submission.BoseGases.pairSet, Finset.eq_empty_iff_forall_notMem]
  intro q hq
  rw [Finset.mem_filter] at hq
  exact hq.2 (Fin.ext (by have h1 := q.1.isLt; have h2 := q.2.isLt; omega))

/-! ## The `A × A`-indicator integral over the two-cube product measure -/

private theorem pairIndicatorIntegral_eq_setIntegral {ℓ : ℝ} {A : Set kcE3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) {u : kcE3 → kcE3 → ℝ} :
    (∫ q : kcE3 × kcE3,
        A.indicator (fun _ => (1 : ℝ)) q.1 * A.indicator (fun _ => (1 : ℝ)) q.2 * u q.1 q.2
      ∂(((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure kcE3).restrict (acube ℓ))))
      = ∫ q in A ×ˢ A, u q.1 q.2 := by
  have hpt : (fun q : kcE3 × kcE3 =>
        A.indicator (fun _ => (1 : ℝ)) q.1 * A.indicator (fun _ => (1 : ℝ)) q.2 * u q.1 q.2)
      = (A ×ˢ A).indicator (fun q : kcE3 × kcE3 => u q.1 q.2) := by
    funext q
    by_cases h1 : q.1 ∈ A <;> by_cases h2 : q.2 ∈ A <;>
      simp [Set.mem_prod, Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2]
  rw [hpt, MeasureTheory.integral_indicator (hA.prod hA)]
  have hmeas : ((((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure kcE3).restrict (acube ℓ))).restrict (A ×ˢ A))
      = (volume : Measure (kcE3 × kcE3)).restrict (A ×ˢ A) := by
    rw [← Measure.prod_restrict A A]
    rw [Measure.restrict_restrict_of_subset hAc]
    rw [Measure.prod_restrict A A, MeasureTheory.Measure.volume_eq_prod kcE3 kcE3]
  rw [hmeas]

/-! ## Transport of the weighted pair integrand to the product space -/

private theorem boxPairWeightedIntegrand_transport_p2 {p : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    {A : Set kcE3} {u : kcE3 → kcE3 → ℝ} {Φ : X (p + 2) → ℝ}
    (i : Fin (p + 2)) (j' : Fin (p + 1)) :
    (∫ x in abox (p + 2) ℓ,
        (Work.UBBInputs8.boxPInd volA A i
          (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) x) ^ 2
          * u (x i) (x (i.succAbove j')))
      = ∫ q : (kcE3 × kcE3) × X p,
          (A.indicator (fun _ => (1 : ℝ)) q.1.1 * A.indicator (fun _ => (1 : ℝ)) q.1.2
            * u q.1.1 q.1.2) * (Work.BoseFixB1S.Q0C.pairRest volA A i j' Φ q.2) ^ 2
          ∂((((volume : Measure kcE3).restrict (acube ℓ)).prod
              ((volume : Measure kcE3).restrict (acube ℓ))).prod
            ((volume : Measure (X p)).restrict (abox p ℓ))) := by
  rw [Work.BoseFixB1S.Q0C.abox_peel2_transport (p := p) hℓ i j'
    (fun x => (Work.UBBInputs8.boxPInd volA A i
        (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) x) ^ 2
      * u (x i) (x (i.succAbove j')))]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  rcases q with ⟨⟨y, z⟩, r2⟩
  simp only
  rw [Work.BoseFixB1S.Q0C.boxPInd_pair_ins2_sq volA A i j' Φ y z r2]
  rw [ins2_apply_i, ins2_apply_succ]
  ring

/-! ## Positivity of `ℓ` in the non-degenerate case -/

private theorem acube_pos_of_volA_pos_aux {ℓ volA : ℝ} {A : Set kcE3}
    (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ) (hvol : 0 < volA) :
    0 < ℓ := by
  have hne : (volume A : ENNReal) ≠ 0 := by
    intro h
    rw [h] at hvolA
    simp at hvolA
    linarith
  have hAne : A.Nonempty :=
    Set.nonempty_iff_ne_empty.mpr (fun h => hne (by rw [h, measure_empty]))
  obtain ⟨y, hy⟩ := hAne
  have hyc : ∀ m : Fin 3, y m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := hAc hy
  have hℓ0 : 0 ≤ ℓ := by
    have h := hyc 0
    simp only [Set.mem_Icc] at h
    linarith [h.1, h.2]
  have hle : volume A ≤ ENNReal.ofReal (ℓ ^ 3) := by
    calc volume A ≤ volume (acube ℓ) := measure_mono hAc
      _ = ENNReal.ofReal (ℓ ^ 3) := acube_volume ℓ hℓ0
  have hofz : ENNReal.ofReal (ℓ ^ 3) ≠ 0 := fun h0 => hne (le_antisymm (h0 ▸ hle) bot_le)
  have h3 : 0 < ℓ ^ 3 := ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hofz)
  have hℓne : ℓ ≠ 0 := fun h => by rw [h] at h3; norm_num at h3
  exact lt_of_le_of_ne hℓ0 (Ne.symm hℓne)

/-! ## The per-pair identity at dimension `p + 2` -/

/-- **The per-pair weighted mass identity.**  For `i ≠ j` (written `j = i.succAbove j'`), an
arbitrary kernel `u` and an arbitrary (not necessarily measurable) state `Φ`,

`∫_{abox (p+2) ℓ} (P_iP_jΦ)²·u(x i)(x j) = (∬_{A×A} u / volA²) · ∫_{abox (p+2) ℓ} (P_iP_jΦ)²`.

No integrability or support hypothesis on `u` is needed: the box indicators inside `P_i`, `P_j`
already confine the pair integral to `A × A`, and `MeasureTheory.integral_prod_mul` requires no
measurability of the remaining factor. -/
theorem pairMassValue {p : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set kcE3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (u : kcE3 → kcE3 → ℝ)
    {Φ : X (p + 2) → ℝ} (i : Fin (p + 2)) (j' : Fin (p + 1)) :
    (∫ x in abox (p + 2) ℓ,
        (Work.UBBInputs8.boxPInd volA A i
          (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) x) ^ 2
          * u (x i) (x (i.succAbove j')))
      = ((∫ q in A ×ˢ A, u q.1 q.2) / volA ^ 2)
          * ∫ x in abox (p + 2) ℓ,
              (Work.UBBInputs8.boxPInd volA A i
                (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) x) ^ 2 := by
  have hL : (∫ x in abox (p + 2) ℓ,
        (Work.UBBInputs8.boxPInd volA A i
          (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) x) ^ 2
          * u (x i) (x (i.succAbove j')))
      = ∫ q : (kcE3 × kcE3) × X p,
          (A.indicator (fun _ => (1 : ℝ)) q.1.1 * A.indicator (fun _ => (1 : ℝ)) q.1.2
            * u q.1.1 q.1.2) * (Work.BoseFixB1S.Q0C.pairRest volA A i j' Φ q.2) ^ 2
          ∂((((volume : Measure kcE3).restrict (acube ℓ)).prod
              ((volume : Measure kcE3).restrict (acube ℓ))).prod
            ((volume : Measure (X p)).restrict (abox p ℓ))) :=
    boxPairWeightedIntegrand_transport_p2 hℓ i j'
  have hR : (∫ x in abox (p + 2) ℓ,
        (Work.UBBInputs8.boxPInd volA A i
          (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) x) ^ 2)
      = ∫ q : (kcE3 × kcE3) × X p,
          (A.indicator (fun _ => (1 : ℝ)) q.1.1 * A.indicator (fun _ => (1 : ℝ)) q.1.2)
            * (Work.BoseFixB1S.Q0C.pairRest volA A i j' Φ q.2) ^ 2
          ∂((((volume : Measure kcE3).restrict (acube ℓ)).prod
              ((volume : Measure kcE3).restrict (acube ℓ))).prod
            ((volume : Measure (X p)).restrict (abox p ℓ))) := by
    simpa only [mul_one] using
      (boxPairWeightedIntegrand_transport_p2 (p := p) (ℓ := ℓ) (volA := volA) hℓ
        (A := A) (u := fun _ _ => (1 : ℝ)) (Φ := Φ) i j')
  rw [hL, hR]
  rw [MeasureTheory.integral_prod_mul
    (f := fun ξ : kcE3 × kcE3 =>
      A.indicator (fun _ => (1 : ℝ)) ξ.1 * A.indicator (fun _ => (1 : ℝ)) ξ.2 * u ξ.1 ξ.2)
    (g := fun r : X p => (Work.BoseFixB1S.Q0C.pairRest volA A i j' Φ r) ^ 2)]
  rw [MeasureTheory.integral_prod_mul
    (f := fun ξ : kcE3 × kcE3 =>
      A.indicator (fun _ => (1 : ℝ)) ξ.1 * A.indicator (fun _ => (1 : ℝ)) ξ.2)
    (g := fun r : X p => (Work.BoseFixB1S.Q0C.pairRest volA A i j' Φ r) ^ 2)]
  rw [pairIndicatorIntegral_eq_setIntegral hA hAc (u := u)]
  have hone : (∫ q : kcE3 × kcE3,
        A.indicator (fun _ => (1 : ℝ)) q.1 * A.indicator (fun _ => (1 : ℝ)) q.2
      ∂(((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure kcE3).restrict (acube ℓ)))) = ∫ q in A ×ˢ A, (1 : ℝ) := by
    simpa only [mul_one] using
      (pairIndicatorIntegral_eq_setIntegral (ℓ := ℓ) hA hAc (u := fun _ _ => (1 : ℝ)))
  rw [hone]
  have hval : (∫ q in A ×ˢ A, (1 : ℝ)) = volA ^ 2 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, smul_eq_mul, mul_one]
    rw [show (volume : Measure (kcE3 × kcE3)) (A ×ˢ A)
        = (volume : Measure kcE3) A * (volume : Measure kcE3) A from by
      rw [MeasureTheory.Measure.volume_eq_prod kcE3 kcE3, Measure.prod_prod]]
    rw [ENNReal.toReal_mul, ← hvolA]
    ring
  rw [hval]
  have hvol2 : volA ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hvol)
  field_simp

/-! ## The main theorem -/

theorem boxWeightedPairMass {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (w₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    {Φ : Submission.BoseGases.X N → ℝ}
    (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hsupp : ∀ x y : EuclideanSpace ℝ (Fin 3), w₁ x y ≠ 0 → x ∈ A ∧ y ∈ A)
    (hint : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2
          * w₁ (x p.1) (x p.2)) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hmass : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => w₁ p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))).restrict (A ×ˢ A))) :
    (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2
            * w₁ (x p.1) (x p.2))
      = ((∫ p in A ×ˢ A, w₁ p.1 p.2) / volA ^ 2)
          * Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
  cases N with
  | zero =>
    have h0 : Submission.BoseGases.pairSet 0 = ∅ := pairSet_eq_empty_of_le_one (by norm_num)
    simp only [Work.BoseFixB1S.boxPairCount, h0, Finset.sum_empty, mul_zero]
  | succ n =>
    cases n with
    | zero =>
      have h0 : Submission.BoseGases.pairSet (Nat.succ 0) = ∅ :=
        pairSet_eq_empty_of_le_one (by norm_num)
      simp only [Work.BoseFixB1S.boxPairCount, h0, Finset.sum_empty, mul_zero]
    | succ p =>
      rw [Work.BoseFixB1S.boxPairCount]
      by_cases hvol : volA = 0
      · -- `volA = 0`: every `boxPInd` vanishes, and the right-hand side carries `1/volA² = 0`
        rw [hvol]
        have hzero : ∀ (i : Fin (Nat.succ (Nat.succ p)))
            (Ψ : Submission.BoseGases.X (Nat.succ (Nat.succ p)) → ℝ),
            Work.UBBInputs8.boxPInd 0 A i Ψ = fun _ => 0 := by
          intro i Ψ
          funext x
          simp only [Work.UBBInputs8.boxPInd]
          rw [div_zero, zero_mul, zero_mul]
        have hL : (∑ q ∈ Submission.BoseGases.pairSet (Nat.succ (Nat.succ p)),
            ∫ x in Submission.BoseGases.abox (Nat.succ (Nat.succ p)) ℓ,
              (Work.UBBInputs8.boxPInd 0 A q.1 (Work.UBBInputs8.boxPInd 0 A q.2 Φ) x) ^ 2
                * w₁ (x q.1) (x q.2)) = 0 := by
          refine Finset.sum_eq_zero (fun q hq => ?_)
          have hpt : (fun x : Submission.BoseGases.X (Nat.succ (Nat.succ p)) =>
              (Work.UBBInputs8.boxPInd 0 A q.1 (Work.UBBInputs8.boxPInd 0 A q.2 Φ) x) ^ 2
                * w₁ (x q.1) (x q.2)) = fun _ => 0 := by
            funext x
            rw [hzero q.1 (Work.UBBInputs8.boxPInd 0 A q.2 Φ)]
            simp
          rw [hpt]
          simp
        rw [hL]
        simp
      · -- the main case
        have hvolpos : 0 < volA :=
          lt_of_le_of_ne (by rw [hvolA]; exact ENNReal.toReal_nonneg) (Ne.symm hvol)
        obtain hℓ := acube_pos_of_volA_pos_aux hvolA hAc hvolpos
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        have hne : q.1 ≠ q.2 := (Finset.mem_filter.mp hq).2
        obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := q.2) (y := q.1) hne.symm
        rw [← hj']
        exact pairMassValue hℓ hvolpos hA hvolA hAc w₁ q.1 j'

end Work.BoseFixB1S
