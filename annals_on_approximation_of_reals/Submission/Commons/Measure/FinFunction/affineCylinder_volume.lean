import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory ENNReal
open scoped ENNReal
set_option autoImplicit false

namespace Commons.Measure.FinFunction

/-- The measurable equivalence identifying `v : Fin (n+1) → ℝ` with the pair
`(v ∘ Fin.succ, v 0) : (Fin n → ℝ) × ℝ`, preserving Lebesgue measure. -/
private def cylinderEquiv (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵐ ((Fin n → ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).trans
    (MeasurableEquiv.prodComm (α := ℝ) (β := Fin n → ℝ))

private lemma cylinderEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (cylinderEquiv n : (Fin (n + 1) → ℝ) → (Fin n → ℝ) × ℝ) := by
  unfold cylinderEquiv
  have h1 : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 :
        (Fin (n + 1) → ℝ) → ℝ × (Fin n → ℝ)) := by
    simpa using (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
  have h2 : MeasurePreserving (Prod.swap : ℝ × (Fin n → ℝ) → (Fin n → ℝ) × ℝ) := by
    simpa [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap : MeasurePreserving Prod.swap
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
        ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)))
  have hcomp : MeasurePreserving
      (Prod.swap ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 :
        (Fin (n + 1) → ℝ) → ℝ × (Fin n → ℝ))) := h2.comp h1
  simpa [cylinderEquiv, MeasurableEquiv.coe_trans, MeasurableEquiv.prodComm] using hcomp

/-- The target cylinder set is the preimage under `cylinderEquiv` of a set in the product. -/
private lemma cylinder_preimage {n : ℕ} (a : Fin n → ℝ) (s ε : ℝ) :
    {v : Fin (n + 1) → ℝ |
        (∀ i : Fin n, |v (Fin.succ i)| ≤ s) ∧
        |v 0 - ∑ i : Fin n, a i * v (Fin.succ i)| ≤ ε} =
      (cylinderEquiv n) ⁻¹' {p : (Fin n → ℝ) × ℝ |
        (∀ i : Fin n, |p.1 i| ≤ s) ∧ |p.2 - ∑ i : Fin n, a i * p.1 i| ≤ ε} := by
  ext v
  constructor
  · intro hv
    change (fun i : Fin n => v (Fin.succ i), v 0) ∈
      {p : (Fin n → ℝ) × ℝ | (∀ i : Fin n, |p.1 i| ≤ s) ∧
        |p.2 - ∑ i : Fin n, a i * p.1 i| ≤ ε}
    simpa [Fin.succ] using hv
  · intro hv
    change (fun i : Fin n => v (Fin.succ i), v 0) ∈
      {p : (Fin n → ℝ) × ℝ | (∀ i : Fin n, |p.1 i| ≤ s) ∧
        |p.2 - ∑ i : Fin n, a i * p.1 i| ≤ ε} at hv
    simpa [Fin.succ] using hv

/-- Volume of the closed cube `[-s,s]^n` in `Fin n → ℝ`. -/
private lemma cube_volume {n : ℕ} (s : ℝ) (hs : 0 ≤ s) :
    (volume : Measure (Fin n → ℝ)) {x : Fin n → ℝ | ∀ i : Fin n, |x i| ≤ s} =
      ENNReal.ofReal ((2 * s) ^ n) := by
  have hB : ({x : Fin n → ℝ | ∀ i : Fin n, |x i| ≤ s} : Set (Fin n → ℝ)) =
      Set.Icc (fun _ : Fin n => -s) (fun _ : Fin n => s) := by
    ext x
    simp [Set.mem_Icc, Pi.le_def, abs_le, forall_and]
  rw [hB]
  rw [Real.volume_Icc_pi (a := fun _ : Fin n => -s) (b := fun _ : Fin n => s)]
  calc
    (∏ _i : Fin n, ENNReal.ofReal (s - (-s))) = ∏ _i : Fin n, ENNReal.ofReal (2 * s) := by
      apply Finset.prod_congr rfl
      intro i hi
      congr 1
      ring
    _ = (ENNReal.ofReal (2 * s)) ^ n := by
      simp [Fintype.card_fin]
    _ = ENNReal.ofReal ((2 * s) ^ n) := by
      rw [ENNReal.ofReal_pow (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs) n]

/-- Measurability of the cylinder set in the product coordinates. -/
private lemma cylinder_measurable {n : ℕ} (a : Fin n → ℝ) (s ε : ℝ) :
    MeasurableSet {p : (Fin n → ℝ) × ℝ |
      (∀ i : Fin n, |p.1 i| ≤ s) ∧ |p.2 - ∑ i : Fin n, a i * p.1 i| ≤ ε} := by
  have hcube_closed : IsClosed {x : Fin n → ℝ | ∀ i : Fin n, |x i| ≤ s} := by
    have hset : ({x : Fin n → ℝ | ∀ i : Fin n, |x i| ≤ s} : Set (Fin n → ℝ)) =
        ⋂ i : Fin n, {x : Fin n → ℝ | |x i| ≤ s} := by
      ext x
      simp
    rw [hset]
    refine isClosed_iInter ?_
    intro i
    exact isClosed_le (continuous_abs.comp (continuous_apply i)) continuous_const
  have hfst_closed : IsClosed {p : (Fin n → ℝ) × ℝ | p.1 ∈ {x : Fin n → ℝ | ∀ i : Fin n, |x i| ≤ s}} := by
    simpa using (hcube_closed.preimage continuous_fst)
  have hslab_closed : IsClosed {p : (Fin n → ℝ) × ℝ |
      |p.2 - ∑ i : Fin n, a i * p.1 i| ≤ ε} := by
    have hcont : Continuous (fun p : (Fin n → ℝ) × ℝ =>
        |p.2 - ∑ i : Fin n, a i * p.1 i|) := by
      fun_prop
    -- |..| ≤ ε expressed as closed set {p | |..| ≤ ε}
    simpa using (isClosed_le hcont continuous_const)
  have hclosed : IsClosed {p : (Fin n → ℝ) × ℝ |
      (∀ i : Fin n, |p.1 i| ≤ s) ∧ |p.2 - ∑ i : Fin n, a i * p.1 i| ≤ ε} := by
    convert hfst_closed.inter hslab_closed using 1
    ext p
    constructor
    · intro h
      exact ⟨h.1, h.2⟩
    · intro h
      exact ⟨h.1, h.2⟩
  exact hclosed.measurableSet

/-- Volume of the affine cylinder, by Fubini along coordinate 0. -/
theorem affineCylinder_volume {n : ℕ} (a : Fin n → ℝ) (s ε : ℝ) (hs : 0 ≤ s) (hε : 0 ≤ ε) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ))
      {v : Fin (n + 1) → ℝ |
        (∀ i : Fin n, |v (Fin.succ i)| ≤ s) ∧
        |v 0 - ∑ i : Fin n, a i * v (Fin.succ i)| ≤ ε} =
    ENNReal.ofReal ((2 * s) ^ n * (2 * ε)) := by
  let B : Set (Fin n → ℝ) := {x : Fin n → ℝ | ∀ i : Fin n, |x i| ≤ s}
  let E : Set ((Fin n → ℝ) × ℝ) :=
    {p : (Fin n → ℝ) × ℝ | (∀ i : Fin n, |p.1 i| ≤ s) ∧
      |p.2 - ∑ i : Fin n, a i * p.1 i| ≤ ε}
  have hS : ({v : Fin (n + 1) → ℝ |
        (∀ i : Fin n, |v (Fin.succ i)| ≤ s) ∧
        |v 0 - ∑ i : Fin n, a i * v (Fin.succ i)| ≤ ε} : Set (Fin (n + 1) → ℝ)) =
      (cylinderEquiv n) ⁻¹' E := by
    simpa [E] using (cylinder_preimage (n := n) a s ε)
  have hEmeas : MeasurableSet E := by
    simpa [E] using (cylinder_measurable (n := n) a s ε)
  have hBmeas : MeasurableSet B := by
    have : IsClosed {x : Fin n → ℝ | ∀ i : Fin n, |x i| ≤ s} := by
      have hset : ({x : Fin n → ℝ | ∀ i : Fin n, |x i| ≤ s} : Set (Fin n → ℝ)) =
          ⋂ i : Fin n, {x : Fin n → ℝ | |x i| ≤ s} := by
        ext x
        simp
      rw [hset]
      refine isClosed_iInter ?_
      intro i
      exact isClosed_le (continuous_abs.comp (continuous_apply i)) continuous_const
    simpa [B] using this.measurableSet
  have hvolB : (volume : Measure (Fin n → ℝ)) B = ENNReal.ofReal ((2 * s) ^ n) := by
    simpa [B] using (cube_volume (n := n) s hs)
  -- length of each fibre {t | |t - c| ≤ ε} is 2ε
  have hslice : ∀ x : Fin n → ℝ,
      (volume : Measure ℝ) (Prod.mk x ⁻¹' E) =
        (B.indicator (fun _ : Fin n → ℝ => ENNReal.ofReal (2 * ε))) x := by
    intro x
    by_cases hx : x ∈ B
    · have hxB : ∀ i : Fin n, |x i| ≤ s := by simpa [B] using hx
      have hEq : (Prod.mk x ⁻¹' E : Set ℝ) =
          {t : ℝ | |t - ∑ i : Fin n, a i * x i| ≤ ε} := by
        ext t
        simp [E, hxB]
      rw [hEq]
      have hcl : ({t : ℝ | |t - ∑ i : Fin n, a i * x i| ≤ ε} : Set ℝ) =
          Metric.closedBall (∑ i : Fin n, a i * x i) ε := by
        ext t
        simp [Metric.mem_closedBall, dist_eq_norm]
      rw [hcl]
      simp [hx]
    · have hn : ¬ ∀ i : Fin n, |x i| ≤ s := by simpa [B] using hx
      have hEq : (Prod.mk x ⁻¹' E : Set ℝ) = ∅ := by
        ext t
        simp [E, hn]
      rw [hEq, measure_empty]
      simp [hx]
  -- measure of E in the product by Fubini
  have hE_vol : (volume : Measure ((Fin n → ℝ) × ℝ)) E =
      ENNReal.ofReal (2 * ε) * (volume : Measure (Fin n → ℝ)) B := by
    calc
      (volume : Measure ((Fin n → ℝ) × ℝ)) E
          = ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) E := by
            rw [Measure.volume_eq_prod]
      _ = ∫⁻ x : Fin n → ℝ,
            (volume : Measure ℝ) (Prod.mk x ⁻¹' E)
            ∂(volume : Measure (Fin n → ℝ)) := by
            rw [Measure.prod_apply hEmeas]
      _ = ∫⁻ x : Fin n → ℝ,
            (B.indicator (fun _ : Fin n → ℝ => ENNReal.ofReal (2 * ε))) x
            ∂(volume : Measure (Fin n → ℝ)) := by
            exact lintegral_congr fun x => hslice x
      _ = ∫⁻ x : Fin n → ℝ in B, ENNReal.ofReal (2 * ε)
            ∂(volume : Measure (Fin n → ℝ)) := by
            rw [lintegral_indicator hBmeas]
      _ = ENNReal.ofReal (2 * ε) * (volume : Measure (Fin n → ℝ)) B := by
            rw [setLIntegral_const]
  calc
    (volume : Measure (Fin (n + 1) → ℝ)) {v : Fin (n + 1) → ℝ |
        (∀ i : Fin n, |v (Fin.succ i)| ≤ s) ∧
        |v 0 - ∑ i : Fin n, a i * v (Fin.succ i)| ≤ ε}
        = (volume : Measure ((Fin n → ℝ) × ℝ)) E := by
            rw [hS]
            exact (cylinderEquiv_measurePreserving n).measure_preimage hEmeas.nullMeasurableSet
    _ = ENNReal.ofReal (2 * ε) * ENNReal.ofReal ((2 * s) ^ n) := by
            rw [hE_vol, hvolB]
    _ = ENNReal.ofReal ((2 * ε) * (2 * s) ^ n) := by
            rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε)]
    _ = ENNReal.ofReal ((2 * s) ^ n * (2 * ε)) := by
            congr 1
            ring

end Commons.Measure.FinFunction