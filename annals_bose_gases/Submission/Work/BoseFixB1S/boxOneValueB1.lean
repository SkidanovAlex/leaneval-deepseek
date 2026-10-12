import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.BoxQWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxOneValueB1`

The one-body line of the box-potential words at the FS-faithful box projection
`P_{B,i}` (`Work.UBBInputs8.boxPInd`): for a measurable `A ⊆ acube ℓ` of volume `volA`
and any continuous `Φ`,

    ∫_{abox N ℓ} (P_{B,i}Φ)² · w₁fibre(x_i)
      = (boxM1 ℓ A w1 / volA) · ∫_{abox N ℓ} (P_{B,i}Φ)².

Since `P_{B,i}Φ x = volA⁻¹ (∫_A Φ(x_{i←z}) dz) · 1_A(x_i)`, the integrand factors into a
function of the slot `i` alone and a function of the remaining slots; peeling slot `i` out of
the product box therefore reduces both sides to the same marginal, and the two constants are
`∫_{acube ℓ} 1_A = volA` and `∫_{acube ℓ} 1_A · w₁fibre = boxM1 ℓ A w1` (the latter uses
`A ⊆ acube ℓ`).  Nothing else is used: in particular the identity is unconditional, no
integrability of `w₁fibre` is needed (the hypothesis is kept for the caller).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1S

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- **Peeling one slot out of the centred box.**  If `F` does not depend on the slot `i`
(`F (update x i z) = F x`), then the box integral of `F x * h (x i)` is the product of the
one-slot integral of `h` over the cube and the `i`-free marginal of `F`. -/
theorem peel_slot_aux {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1))
    {F : Submission.BoseGases.X (n + 1) → ℝ}
    (hF : ∀ (x : Submission.BoseGases.X (n + 1)) (z : EuclideanSpace ℝ (Fin 3)),
      F (Function.update x i z) = F x)
    (h : EuclideanSpace ℝ (Fin 3) → ℝ) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x * h (x i))
      = (∫ z in Submission.BoseGases.acube ℓ, h z)
        * (∫ y in Submission.BoseGases.abox n ℓ,
            F (Fin.insertNth i (0 : EuclideanSpace ℝ (Fin 3)) y)) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin 3)) i
  have hmp : MeasurePreserving (⇑e)
      ((volume : Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ))
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) := by
    rw [show (volume : Measure (Submission.BoseGases.X (n + 1))).restrict
          (Submission.BoseGases.abox (n + 1) ℓ)
        = Measure.pi (fun _ : Fin (n + 1) =>
            (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.acube ℓ))
        from Submission.BoseGases.restrict_abox_eq_pi (n + 1) ℓ,
      show (volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)
        = Measure.pi (fun _ : Fin n =>
            (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.acube ℓ))
        from Submission.BoseGases.restrict_abox_eq_pi n ℓ]
    exact measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) =>
        (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)) i
  have hEsym : (e.symm : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n →
        Submission.BoseGases.X (n + 1))
      = fun p => Fin.insertNth i p.1 p.2 := by
    funext p j
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
  have hpt : ∀ p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n,
      F (e.symm p) * h ((e.symm p) i)
        = h p.1 * F (Fin.insertNth i (0 : EuclideanSpace ℝ (Fin 3)) p.2) := by
    intro p
    simp only [hEsym]
    rw [Fin.insertNth_apply_same]
    have hF' : F (Fin.insertNth i p.1 p.2)
        = F (Fin.insertNth i (0 : EuclideanSpace ℝ (Fin 3)) p.2) := by
      rw [← Fin.update_insertNth
        (α := fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin 3))
        i (0 : EuclideanSpace ℝ (Fin 3)) p.1 p.2]
      exact hF (Fin.insertNth i (0 : EuclideanSpace ℝ (Fin 3)) p.2) p.1
    rw [hF', mul_comm]
  calc (∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x * h (x i))
      = ∫ x, F x * h (x i)
          ∂((volume : Measure (Submission.BoseGases.X (n + 1))).restrict
            (Submission.BoseGases.abox (n + 1) ℓ)) := rfl
    _ = ∫ p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n,
          F (e.symm p) * h ((e.symm p) i)
          ∂(((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
                (Submission.BoseGases.acube ℓ)).prod
              ((volume : Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n ℓ))) := by
        have hc := hmp.integral_comp (MeasurableEquiv.measurableEmbedding e)
          (g := fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
            F (e.symm p) * h ((e.symm p) i))
        simpa using hc
    _ = ∫ p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n,
          h p.1 * F (Fin.insertNth i (0 : EuclideanSpace ℝ (Fin 3)) p.2)
          ∂(((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
                (Submission.BoseGases.acube ℓ)).prod
              ((volume : Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n ℓ))) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ z : EuclideanSpace ℝ (Fin 3), h z
          ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ)))
        * (∫ y : Submission.BoseGases.X n,
            F (Fin.insertNth i (0 : EuclideanSpace ℝ (Fin 3)) y)
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))) := by
        rw [MeasureTheory.integral_prod_mul
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ))
          (ν := (volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))
          (f := h)
          (g := fun y : Submission.BoseGases.X n =>
            F (Fin.insertNth i (0 : EuclideanSpace ℝ (Fin 3)) y))]
    _ = (∫ z in Submission.BoseGases.acube ℓ, h z)
        * (∫ y in Submission.BoseGases.abox n ℓ,
            F (Fin.insertNth i (0 : EuclideanSpace ℝ (Fin 3)) y)) := rfl

/-- The indicator mass of `A` over the cube: `∫_{acube ℓ} 1_A = volA` when
`A ⊆ acube ℓ` and `volA = volume A`. -/
theorem acube_indicator_one_aux {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) :
    (∫ z in Submission.BoseGases.acube ℓ, A.indicator (fun _ => 1) z) = volA := by
  have h1 : (∫ z in Submission.BoseGases.acube ℓ, A.indicator (fun _ => 1) z)
      = ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ)).real A :=
    MeasureTheory.integral_indicator_one hA
  rw [h1, MeasureTheory.Measure.real_def, MeasureTheory.Measure.restrict_apply hA,
    show A ∩ Submission.BoseGases.acube ℓ = A from Set.inter_eq_left.mpr hAc]
  exact hvolA.symm

/-- The `w₁`-fibre mass of the indicator over the cube: `∫_{acube ℓ} 1_A · w₁fibre = boxM1`
when `A ⊆ acube ℓ`. -/
theorem acube_indicator_w1_aux {ℓ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w1 : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ} :
    (∫ z in Submission.BoseGases.acube ℓ,
        A.indicator (fun _ => 1) z * Submission.BoseGases.w1Fibre ℓ w1 z)
      = boxM1 ℓ A w1 := by
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      A.indicator (fun _ => 1) z * Submission.BoseGases.w1Fibre ℓ w1 z
        = A.indicator (fun _ => Submission.BoseGases.w1Fibre ℓ w1 z) z := by
    intro z
    by_cases hz : z ∈ A
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  calc (∫ z in Submission.BoseGases.acube ℓ,
        A.indicator (fun _ => 1) z * Submission.BoseGases.w1Fibre ℓ w1 z)
      = ∫ z in Submission.BoseGases.acube ℓ,
          A.indicator (fun _ => Submission.BoseGases.w1Fibre ℓ w1 z) z :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ z in A, Submission.BoseGases.w1Fibre ℓ w1 z
          ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ)) :=
        MeasureTheory.integral_indicator hA
    _ = ∫ z, Submission.BoseGases.w1Fibre ℓ w1 z
          ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) := by
        rw [Measure.restrict_restrict hA, Set.inter_eq_left.mpr hAc]
    _ = boxM1 ℓ A w1 := rfl

theorem boxOneValueB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {i : Fin N}
    {w1 : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hw1 : MeasureTheory.IntegrableOn (Submission.BoseGases.w1Fibre ℓ w1) A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
          * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      = (Work.BoseFixB1S.boxM1 ℓ A w1 / volA) *
        (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ n =>
    set F : Submission.BoseGases.X (n + 1) → ℝ :=
      fun x => (∫ z in A, Φ (Function.update x i z)) ^ 2 with hFdef
    set h1 : EuclideanSpace ℝ (Fin 3) → ℝ :=
      fun z => A.indicator (fun _ => 1) z * Submission.BoseGases.w1Fibre ℓ w1 z with h1def
    set h2 : EuclideanSpace ℝ (Fin 3) → ℝ :=
      fun z => A.indicator (fun _ => 1) z with h2def
    set R : ℝ := ∫ y in Submission.BoseGases.abox n ℓ,
        F (Fin.insertNth i (0 : EuclideanSpace ℝ (Fin 3)) y) with hRdef
    have hindF : ∀ (x : Submission.BoseGases.X (n + 1))
        (z : EuclideanSpace ℝ (Fin 3)), F (Function.update x i z) = F x := by
      intro x z
      simp only [hFdef]
      have hEq : (fun z' : EuclideanSpace ℝ (Fin 3) =>
            Φ (Function.update (Function.update x i z) i z'))
          = (fun z' => Φ (Function.update x i z')) := by
        funext z'
        rw [Function.update_idem]
      simp only [hEq]
    have hpeel1 := peel_slot_aux (n := n) (ℓ := ℓ) i hindF h1
    have hpeel2 := peel_slot_aux (n := n) (ℓ := ℓ) i hindF h2
    have hmass1 : (∫ z in Submission.BoseGases.acube ℓ, h1 z) = boxM1 ℓ A w1 := by
      simp only [h1def]
      exact acube_indicator_w1_aux hA hAc
    have hmass2 : (∫ z in Submission.BoseGases.acube ℓ, h2 z) = volA := by
      simp only [h2def]
      exact acube_indicator_one_aux hA hvolA hAc
    have hpt1 : ∀ x : Submission.BoseGases.X (n + 1),
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
            * Submission.BoseGases.w1Fibre ℓ w1 (x i)
          = (1 / volA) ^ 2 * (F x * h1 (x i)) := by
      intro x
      simp only [hFdef, h1def, Work.UBBInputs8.boxPInd]
      by_cases hx : x i ∈ A
      · simp only [Set.indicator_of_mem hx]
        ring
      · simp only [Set.indicator_of_notMem hx]
        ring
    have hpt2 : ∀ x : Submission.BoseGases.X (n + 1),
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
          = (1 / volA) ^ 2 * (F x * h2 (x i)) := by
      intro x
      simp only [hFdef, h2def, Work.UBBInputs8.boxPInd]
      by_cases hx : x i ∈ A
      · simp only [Set.indicator_of_mem hx]
        ring
      · simp only [Set.indicator_of_notMem hx]
        ring
    have key1 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
            * Submission.BoseGases.w1Fibre ℓ w1 (x i))
        = (1 / volA) ^ 2 * (boxM1 ℓ A w1 * R) := by
      calc (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
              * Submission.BoseGases.w1Fibre ℓ w1 (x i))
          = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (1 / volA) ^ 2 * (F x * h1 (x i)) :=
            integral_congr_ae (Filter.Eventually.of_forall hpt1)
        _ = (1 / volA) ^ 2
              * (∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x * h1 (x i)) :=
            integral_const_mul _ _
        _ = (1 / volA) ^ 2 * ((∫ z in Submission.BoseGases.acube ℓ, h1 z) * R) := by
            rw [hpeel1, ← hRdef]
        _ = (1 / volA) ^ 2 * (boxM1 ℓ A w1 * R) := by rw [hmass1]
    have key2 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        = (1 / volA) ^ 2 * (volA * R) := by
      calc (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
          = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (1 / volA) ^ 2 * (F x * h2 (x i)) :=
            integral_congr_ae (Filter.Eventually.of_forall hpt2)
        _ = (1 / volA) ^ 2
              * (∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x * h2 (x i)) :=
            integral_const_mul _ _
        _ = (1 / volA) ^ 2 * ((∫ z in Submission.BoseGases.acube ℓ, h2 z) * R) := by
            rw [hpeel2, ← hRdef]
        _ = (1 / volA) ^ 2 * (volA * R) := by rw [hmass2]
    rw [key1, key2]
    have hv : volA ≠ 0 := ne_of_gt hvol
    field_simp

end Work.BoseFixB1S
