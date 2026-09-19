import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Commons.MeasureTheory.Integral.integral_piFinSuccAbove_of_integrable

namespace Commons.MeasureTheory.Integral

open _root_.MeasureTheory Finset
open scoped BigOperators

/-- **Fubini factorisation over `Fin k → ℝ × ℝ`.**  The integral over the finite product
`Fin k → ℝ × ℝ` of a product of coordinate functions, where the `j`-th coordinate is replaced
by an indicator, factorises into the set integral of the `j`-th function times the product of
the integrals of the remaining ones. -/
lemma integral_indicator_apply_mul_prod_erase {k : ℕ} (c : Fin k → ℝ × ℝ → ℝ)
    (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) (j : Fin k) :
    ∫ p : Fin k → ℝ × ℝ,
        (s.indicator (c j) (p j) * ∏ i ∈ Finset.univ.erase j, c i (p i))
      = (∫ q in s, c j q) * ∏ i ∈ Finset.univ.erase j, ∫ q, c i q := by
  let f : Fin k → ℝ × ℝ → ℝ := Function.update c j (s.indicator (c j))
  have hfj : f j = s.indicator (c j) := Function.update_self ..
  have hfi : ∀ i, i ≠ j → f i = c i := fun i hi => Function.update_of_ne hi ..
  have hprod : ∀ p : Fin k → ℝ × ℝ,
      (s.indicator (c j) (p j) * ∏ i ∈ Finset.univ.erase j, c i (p i))
        = ∏ i, f i (p i) := by
    intro p
    rw [← Finset.mul_prod_erase Finset.univ (fun i => f i (p i)) (Finset.mem_univ j)]
    congr 1
    · rw [hfj]
    · apply Finset.prod_congr rfl
      intro i hi
      rw [hfi i (Finset.mem_erase.mp hi).1]
  simp_rw [hprod]
  rw [integral_fintype_prod_volume_eq_prod f]
  rw [← Finset.mul_prod_erase Finset.univ (fun i => ∫ q, f i q) (Finset.mem_univ j)]
  congr 1
  · rw [hfj, integral_indicator hs]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hfi i (Finset.mem_erase.mp hi).1]

/-- **Integrability for the Fubini factorisation.**  The product of coordinate functions with one
coordinate replaced by an indicator of a measurable set is integrable for the product measure. -/
lemma integrable_indicator_apply_mul_prod_erase {k : ℕ} (c : Fin k → ℝ × ℝ → ℝ)
    (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) (j : Fin k) (hc : ∀ i, Integrable (c i)) :
    Integrable (fun p : Fin k → ℝ × ℝ =>
        s.indicator (c j) (p j) * ∏ i ∈ Finset.univ.erase j, c i (p i)) volume := by
  let f : Fin k → ℝ × ℝ → ℝ := Function.update c j (s.indicator (c j))
  have hfj : f j = s.indicator (c j) := Function.update_self ..
  have hfi : ∀ i, i ≠ j → f i = c i := fun i hi => Function.update_of_ne hi ..
  have hprod : ∀ p : Fin k → ℝ × ℝ,
      (∏ i, f i (p i))
        = s.indicator (c j) (p j) * ∏ i ∈ Finset.univ.erase j, c i (p i) := by
    intro p
    rw [← Finset.mul_prod_erase Finset.univ (fun i => f i (p i)) (Finset.mem_univ j)]
    congr 1
    · rw [hfj]
    · apply Finset.prod_congr rfl
      intro i hi
      rw [hfi i (Finset.mem_erase.mp hi).1]
  have hint : Integrable (fun p : Fin k → ℝ × ℝ => ∏ i, f i (p i)) volume := by
    rw [volume_pi]
    refine Integrable.fintype_prod (f := f) (fun i => ?_)
    by_cases hi : i = j
    · subst hi
      rw [hfj]
      exact (hc i).indicator hs
    · rw [hfi i hi]
      exact hc i
  exact hint.congr (Filter.Eventually.of_forall hprod)

/-- **Union bound for a product integral outside a cube.**  For a finite family
`c : Fin k → ℝ × ℝ → ℝ` of nonnegative integrable functions and a radius `ρ`,
the integral over `Fin k → ℝ × ℝ` (product Lebesgue measure) of the product
`∏ j, c j (p j)`, restricted to the complement of the cube
`{p | ∀ j, |(p j).1| < ρ ∧ |(p j).2| < ρ}`, is bounded by the sum over the
coordinates of the corresponding one-dimensional tails multiplied by the full
integrals of the other coordinates. -/
theorem integral_prod_indicator_cube_compl_le {k : ℕ} (c : Fin k → ℝ × ℝ → ℝ) (ρ : ℝ)
    (hc : ∀ j, MeasureTheory.Integrable (c j)) (hn : ∀ j q, 0 ≤ c j q) :
    MeasureTheory.integral MeasureTheory.volume
        (fun p : Fin k → ℝ × ℝ =>
          if (∃ j, ρ ≤ |(p j).1| ∨ ρ ≤ |(p j).2|) then ∏ j, c j (p j) else 0)
      ≤ ∑ j, ((MeasureTheory.integral (MeasureTheory.volume.restrict {q : ℝ × ℝ | ρ ≤ |q.1|}) (c j)) +
              (MeasureTheory.integral (MeasureTheory.volume.restrict {q : ℝ × ℝ | ρ ≤ |q.2|}) (c j))) *
          (∏ i ∈ Finset.univ.erase j, MeasureTheory.integral MeasureTheory.volume (c i)) := by
  set s1 : Set (ℝ × ℝ) := {q : ℝ × ℝ | ρ ≤ |q.1|} with hs1def
  set s2 : Set (ℝ × ℝ) := {q : ℝ × ℝ | ρ ≤ |q.2|} with hs2def
  have hs1 : MeasurableSet s1 := by rw [hs1def]; measurability
  have hs2 : MeasurableSet s2 := by rw [hs2def]; measurability
  let T1 : Fin k → (Fin k → ℝ × ℝ) → ℝ :=
    fun j p => s1.indicator (c j) (p j) * ∏ i ∈ Finset.univ.erase j, c i (p i)
  let T2 : Fin k → (Fin k → ℝ × ℝ) → ℝ :=
    fun j p => s2.indicator (c j) (p j) * ∏ i ∈ Finset.univ.erase j, c i (p i)
  let G : (Fin k → ℝ × ℝ) → ℝ := fun p => ∑ j, (T1 j p + T2 j p)
  have hT1int : ∀ j, Integrable (T1 j) volume :=
    fun j => integrable_indicator_apply_mul_prod_erase c s1 hs1 j hc
  have hT2int : ∀ j, Integrable (T2 j) volume :=
    fun j => integrable_indicator_apply_mul_prod_erase c s2 hs2 j hc
  have hT1val : ∀ j, ∫ p, T1 j p
      = (∫ q in s1, c j q) * ∏ i ∈ Finset.univ.erase j, ∫ q, c i q :=
    fun j => integral_indicator_apply_mul_prod_erase c s1 hs1 j
  have hT2val : ∀ j, ∫ p, T2 j p
      = (∫ q in s2, c j q) * ∏ i ∈ Finset.univ.erase j, ∫ q, c i q :=
    fun j => integral_indicator_apply_mul_prod_erase c s2 hs2 j
  have hGint : Integrable G volume :=
    integrable_finsetSum Finset.univ (f := fun j p => T1 j p + T2 j p)
      (fun j _ => (hT1int j).add (hT2int j))
  -- Pointwise union bound `F ≤ G`.
  have hle : (fun p : Fin k → ℝ × ℝ =>
      if (∃ j, ρ ≤ |(p j).1| ∨ ρ ≤ |(p j).2|) then ∏ j, c j (p j) else 0) ≤ G := by
    intro p
    change (if (∃ j, ρ ≤ |(p j).1| ∨ ρ ≤ |(p j).2|) then ∏ j, c j (p j) else 0) ≤ G p
    have hprodnn : ∀ j', 0 ≤ ∏ i ∈ Finset.univ.erase j', c i (p i) :=
      fun j' => Finset.prod_nonneg (fun i _ => hn i (p i))
    have hind1 : ∀ j', 0 ≤ s1.indicator (c j') (p j') := by
      intro j'
      by_cases hh : p j' ∈ s1
      · rw [Set.indicator_of_mem hh]; exact hn j' (p j')
      · rw [Set.indicator_of_notMem hh]
    have hind2 : ∀ j', 0 ≤ s2.indicator (c j') (p j') := by
      intro j'
      by_cases hh : p j' ∈ s2
      · rw [Set.indicator_of_mem hh]; exact hn j' (p j')
      · rw [Set.indicator_of_notMem hh]
    have hterm : ∀ j', 0 ≤ T1 j' p + T2 j' p := by
      intro j'
      exact add_nonneg (mul_nonneg (hind1 j') (hprodnn j'))
        (mul_nonneg (hind2 j') (hprodnn j'))
    by_cases hcond : ∃ j, ρ ≤ |(p j).1| ∨ ρ ≤ |(p j).2|
    · rw [if_pos hcond]
      obtain ⟨j, hj | hj⟩ := hcond
      · have hmem : p j ∈ s1 := hj
        have hT1eq : T1 j p = ∏ i, c i (p i) := by
          change s1.indicator (c j) (p j) * ∏ i ∈ Finset.univ.erase j, c i (p i)
              = ∏ i, c i (p i)
          rw [Set.indicator_of_mem hmem,
            Finset.mul_prod_erase Finset.univ (fun i => c i (p i)) (Finset.mem_univ j)]
        rw [← hT1eq]
        calc T1 j p ≤ T1 j p + T2 j p :=
              le_add_of_nonneg_right (mul_nonneg (hind2 j) (hprodnn j))
          _ ≤ G p := Finset.single_le_sum (fun j' _ => hterm j') (Finset.mem_univ j)
      · have hmem : p j ∈ s2 := hj
        have hT2eq : T2 j p = ∏ i, c i (p i) := by
          change s2.indicator (c j) (p j) * ∏ i ∈ Finset.univ.erase j, c i (p i)
              = ∏ i, c i (p i)
          rw [Set.indicator_of_mem hmem,
            Finset.mul_prod_erase Finset.univ (fun i => c i (p i)) (Finset.mem_univ j)]
        rw [← hT2eq]
        calc T2 j p ≤ T1 j p + T2 j p :=
              le_add_of_nonneg_left (mul_nonneg (hind1 j) (hprodnn j))
          _ ≤ G p := Finset.single_le_sum (fun j' _ => hterm j') (Finset.mem_univ j)
    · rw [if_neg hcond]
      exact Finset.sum_nonneg (fun j _ => hterm j)
  have hpt : ∀ p : Fin k → ℝ × ℝ,
      0 ≤ (if (∃ j, ρ ≤ |(p j).1| ∨ ρ ≤ |(p j).2|) then ∏ j, c j (p j) else 0) := by
    intro p
    by_cases hcond : ∃ j, ρ ≤ |(p j).1| ∨ ρ ≤ |(p j).2|
    · rw [if_pos hcond]; exact Finset.prod_nonneg (fun i _ => hn i (p i))
    · rw [if_neg hcond]
  have hnonneg : 0 ≤ᵐ[volume] (fun p : Fin k → ℝ × ℝ =>
      if (∃ j, ρ ≤ |(p j).1| ∨ ρ ≤ |(p j).2|) then ∏ j, c j (p j) else 0) :=
    Filter.Eventually.of_forall hpt
  calc MeasureTheory.integral MeasureTheory.volume
        (fun p : Fin k → ℝ × ℝ =>
          if (∃ j, ρ ≤ |(p j).1| ∨ ρ ≤ |(p j).2|) then ∏ j, c j (p j) else 0)
      ≤ MeasureTheory.integral MeasureTheory.volume G :=
        integral_mono_of_nonneg hnonneg hGint (Filter.Eventually.of_forall hle)
    _ = ∑ j, ((∫ q in s1, c j q) + (∫ q in s2, c j q)) *
          ∏ i ∈ Finset.univ.erase j, ∫ q, c i q := by
        rw [show G = (fun p => ∑ j, (T1 j p + T2 j p)) from rfl]
        rw [integral_finsetSum Finset.univ (f := fun j p => T1 j p + T2 j p)
              (fun j _ => (hT1int j).add (hT2int j))]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [integral_add (hT1int j) (hT2int j), hT1val j, hT2val j]
        ring

end Commons.MeasureTheory.Integral