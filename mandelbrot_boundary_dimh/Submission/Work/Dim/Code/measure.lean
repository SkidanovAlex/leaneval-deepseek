import Mathlib

namespace Work.Dim.Code

open MeasureTheory

/-- The uniform Bernoulli measure on `ℕ → Fin N`: the infinite product of the uniform
measure on `Fin N`. Its value on a cylinder determined by a word `w` is `N ^ (-w.length)`. -/
theorem measure (N : ℕ) (hN : 1 ≤ N) :
    ∃ ν : MeasureTheory.Measure (ℕ → Fin N), MeasureTheory.IsProbabilityMeasure ν ∧
      ∀ w : List (Fin N),
        ν {ω : ℕ → Fin N | ∀ k : Fin w.length, ω k = w.get k} =
          (N : ENNReal)⁻¹ ^ w.length := by
  classical
  have hN0 : (N : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hNtop : (N : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  let μ : ℕ → Measure (Fin N) := fun _ => (N : ENNReal)⁻¹ • (Measure.count : Measure (Fin N))
  have hprob : ∀ i, IsProbabilityMeasure (μ i) := by
    intro i
    constructor
    change ((N : ENNReal)⁻¹ • (Measure.count : Measure (Fin N))) Set.univ = 1
    rw [Measure.smul_apply, smul_eq_mul, ← Finset.coe_univ, Measure.count_apply_finset,
      Finset.card_univ, Fintype.card_fin]
    exact ENNReal.inv_mul_cancel hN0 hNtop
  have hprob_inf : IsProbabilityMeasure (Measure.infinitePi μ) := by
    constructor
    have h := Measure.infinitePi_pi μ (hμ := hprob) (s := (∅ : Finset ℕ))
      (t := fun _ => Set.univ) (by simp)
    rw [Finset.coe_empty] at h
    have hpi : Set.pi (∅ : Set ℕ) (fun _ => (Set.univ : Set (Fin N))) = Set.univ := by
      ext f; simp [Set.pi]
    rw [hpi] at h
    simpa using h
  refine ⟨Measure.infinitePi μ, hprob_inf, ?_⟩
  intro w
  let t : ℕ → Set (Fin N) := fun i => if h : i < w.length then {w.get ⟨i, h⟩} else Set.univ
  have hset : {ω : ℕ → Fin N | ∀ k : Fin w.length, ω k = w.get k} =
      Set.pi (↑(Finset.range w.length) : Set ℕ) t := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
    constructor
    · intro h i hi
      change ω i ∈ (if h : i < w.length then {w.get ⟨i, h⟩} else Set.univ)
      rw [dite_eq_left hi]
      exact h ⟨i, hi⟩
    · intro h k
      have hk := h (k : ℕ) k.isLt
      change ω ↑k ∈ (if h : ↑k < w.length then {w.get ⟨↑k, h⟩} else Set.univ) at hk
      rw [dite_eq_left k.isLt] at hk
      simpa using hk
  have hmeas : ∀ i ∈ Finset.range w.length, MeasurableSet (t i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    change MeasurableSet (if h : i < w.length then {w.get ⟨i, h⟩} else Set.univ)
    rw [dite_eq_left hi]
    exact measurableSet_singleton _
  have hprod : ∏ i ∈ Finset.range w.length, μ i (t i) = (N : ENNReal)⁻¹ ^ w.length := by
    have hstep : ∀ i ∈ Finset.range w.length, μ i (t i) = (N : ENNReal)⁻¹ := by
      intro i hi
      rw [Finset.mem_range] at hi
      change μ i (if h : i < w.length then {w.get ⟨i, h⟩} else Set.univ) = (N : ENNReal)⁻¹
      rw [dite_eq_left hi]
      change ((N : ENNReal)⁻¹ • (Measure.count : Measure (Fin N))) {w.get ⟨i, hi⟩} =
        (N : ENNReal)⁻¹
      rw [Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one]
    rw [Finset.prod_congr rfl hstep, Finset.prod_const, Finset.card_range]
  rw [hset, Measure.infinitePi_pi μ (hμ := hprob) (s := Finset.range w.length) (t := t) hmeas,
    hprod]

end Work.Dim.Code
