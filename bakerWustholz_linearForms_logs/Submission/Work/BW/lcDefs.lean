import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set
open scoped ENNReal

namespace Work.BW

noncomputable section

/-- The layer-cake indicator of the interval `[0,c]`: as a function of `u` it is `1` on
`[0,c]` and `0` elsewhere. -/
def lcInd (c u : ℝ) : ℝ≥0∞ := Set.indicator (Set.Icc 0 c) (fun _ => (1 : ℝ≥0∞)) u

lemma lcInd_apply (c u : ℝ) : lcInd c u = if 0 ≤ u ∧ u ≤ c then 1 else 0 := by
  simp only [lcInd, Set.indicator_apply, Set.mem_Icc]

lemma measurable_lcInd_left (c : ℝ) : Measurable (lcInd c) := by
  change Measurable (Set.indicator (Set.Icc 0 c) (fun _ => (1 : ℝ≥0∞)))
  exact measurable_const.indicator measurableSet_Icc

lemma measurable_lcInd : Measurable (fun p : ℝ × ℝ => lcInd p.1 p.2) := by
  have hset : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1} := by
    have h1 : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.2} :=
      measurableSet_le measurable_const measurable_snd
    have h2 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
      measurableSet_le measurable_snd measurable_fst
    have heq : {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1} = {p | 0 ≤ p.2} ∩ {p | p.2 ≤ p.1} := by
      ext p; simp
    rw [heq]; exact h1.inter h2
  have hfun : (fun p : ℝ × ℝ => lcInd p.1 p.2)
      = Set.indicator {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1} (fun _ => (1 : ℝ≥0∞)) := by
    funext p
    rw [lcInd_apply, Set.indicator_apply]
    by_cases h : 0 ≤ p.2 ∧ p.2 ≤ p.1 <;> simp [h]
  rw [hfun]
  exact measurable_const.indicator hset

/-- The `ℝ≥0∞`-valued weight `∏ i, ofReal (h i (y i))`. -/
def lcWeight {n : ℕ} (h : Fin n → ℝ → ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (h i (y i))

/-- The joint layer-cake integrand on `(Fin n → ℝ) × (Fin n → ℝ)`. -/
def lcJoint {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1)) (h : Fin n → ℝ → ℝ)
    (s : ℝ) (y u : Fin n → ℝ) : ℝ≥0∞ :=
  (Set.indicator {x : Fin n → ℝ | Fin.insertNth k s x ∈ C} (fun _ => (1 : ℝ≥0∞)) y)
    * ∏ i, lcInd (h i (y i)) (u i)

/-- The convex, symmetric set `C ∩ {z | ∀ i, u i ≤ h i (z (k.succAbove i))}` when `u ≥ 0`
componentwise, and `∅` otherwise. -/
def bwSet {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1)) (h : Fin n → ℝ → ℝ)
    (u : Fin n → ℝ) : Set (Fin (n+1) → ℝ) :=
  if ∀ i, 0 ≤ u i then
    C ∩ ⋂ i, {z : Fin (n+1) → ℝ | u i ≤ h i (z (k.succAbove i))}
  else ∅

lemma bwSet_of_forall_nonneg {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1))
    (h : Fin n → ℝ → ℝ) {u : Fin n → ℝ} (hu : ∀ i, 0 ≤ u i) :
    bwSet C k h u = C ∩ ⋂ i, {z : Fin (n+1) → ℝ | u i ≤ h i (z (k.succAbove i))} := by
  rw [bwSet, if_pos hu]

lemma bwSet_of_not {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1))
    (h : Fin n → ℝ → ℝ) {u : Fin n → ℝ} (hu : ¬ ∀ i, 0 ≤ u i) :
    bwSet C k h u = ∅ := by rw [bwSet, if_neg hu]

/-- The `ℝ≥0∞` layer-cake integral of the weighted slice. -/
def lcFl {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1)) (h : Fin n → ℝ → ℝ)
    (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, (Set.indicator {x : Fin n → ℝ | Fin.insertNth k s x ∈ C} (fun _ => (1 : ℝ≥0∞)) y)
    * lcWeight h y

lemma continuous_insertNth {n : ℕ} (k : Fin (n+1)) (s : ℝ) :
    Continuous (fun y : Fin n → ℝ => (Fin.insertNth k s y : Fin (n+1) → ℝ)) :=
  continuous_const.finInsertNth k continuous_id

end

end Work.BW
