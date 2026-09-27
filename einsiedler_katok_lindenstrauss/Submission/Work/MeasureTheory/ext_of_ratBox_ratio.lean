import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.Topology.generateFrom_ratBox
import Submission.Work.Topology.isCompact_entryBoxSL

open MeasureTheory
open scoped ENNReal

namespace Work.MeasureTheory

/-!
# Extensionality of measures on `SL₃(ℝ)` from entrywise rational boxes

If two locally finite Borel measures `μ`, `ν` on `G = SL₃(ℝ)` are proportional with ratio `c`
on every set of the form "entrywise rational box intersected with an entrywise ball"
`{g | (∀ i j, a i j ≤ g i j ≤ b i j) ∧ ∀ i j, |g i j| ≤ N}`, then `μ = ofReal c • ν`.

The proof is the standard π–λ argument:
* the entrywise rational boxes `boxSL a b` form a π-system and generate the Borel σ-algebra
  (`Work.Topology.generateFrom_ratBox`);
* the entrywise balls `ballSL N = {g | ∀ i j, |g i j| ≤ N}` are compact (locally finite, so
  `μ (ballSL N) < ⊤`), increasing and cover `G`; each is itself a rational box, so the equality
  holds on it;
* hence `Measure.ext_of_generateFrom_of_iUnion` applies.
-/

/-- The entrywise closed box with rational bounds in `SL₃(ℝ)`. -/
private def boxSL (a b : Matrix (Fin 3) (Fin 3) ℚ) : Set Work.EKLContract.SL3 :=
  {g | ∀ i j, (a i j : ℝ) ≤ g i j ∧ g i j ≤ (b i j : ℝ)}

/-- The family of all entrywise closed boxes with rational bounds in `SL₃(ℝ)`. -/
private def ratBox : Set (Set Work.EKLContract.SL3) :=
  {s | ∃ a b : Matrix (Fin 3) (Fin 3) ℚ, s = boxSL a b}

/-- The entrywise `N`-ball in `SL₃(ℝ)`: the set of matrices with all entries bounded by `N`. -/
private def ballSL (N : ℕ) : Set Work.EKLContract.SL3 := {g | ∀ i j, |g i j| ≤ (N : ℝ)}

private theorem ratBox_eq :
    ratBox = {s : Set Work.EKLContract.SL3 |
      ∃ a b : Matrix (Fin 3) (Fin 3) ℚ,
        s = {g : Work.EKLContract.SL3 |
          ∀ i j, (a i j : ℝ) ≤ g i j ∧ g i j ≤ (b i j : ℝ)}} := rfl

/-- The family of rational boxes is a π-system. -/
private theorem isPiSystem_ratBox : IsPiSystem ratBox := by
  rintro s ⟨a, b, rfl⟩ t ⟨a', b', rfl⟩ -
  refine ⟨Matrix.of (fun i j => max (a i j) (a' i j)),
    Matrix.of (fun i j => min (b i j) (b' i j)), ?_⟩
  ext g
  simp only [boxSL, Set.mem_ofPred_eq, Set.mem_inter_iff, Matrix.of_apply, Rat.cast_max,
    Rat.cast_min]
  constructor
  · rintro ⟨h1, h2⟩ i j
    exact ⟨max_le (h1 i j).1 (h2 i j).1, le_min (h1 i j).2 (h2 i j).2⟩
  · intro h
    exact ⟨fun i j => ⟨le_trans (le_max_left _ _) (h i j).1,
              le_trans (h i j).2 (min_le_left _ _)⟩,
           fun i j => ⟨le_trans (le_max_right _ _) (h i j).1,
              le_trans (h i j).2 (min_le_right _ _)⟩⟩

/-- The entrywise balls `ballSL N` exhaust `SL₃(ℝ)`. -/
private theorem iUnion_ballSL : ⋃ n, ballSL n = Set.univ := by
  refine Set.eq_univ_of_forall (fun g => ?_)
  rw [Set.mem_iUnion]
  refine ⟨⌈∑ i : Fin 3, ∑ j : Fin 3, |g i j|⌉₊, fun i j => ?_⟩
  refine le_trans ?_ (Nat.le_ceil (∑ i : Fin 3, ∑ j : Fin 3, |g i j|))
  calc |g i j| ≤ ∑ j : Fin 3, |g i j| :=
        Finset.single_le_sum (f := fun j : Fin 3 => |g i j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |g i j| :=
        Finset.single_le_sum (f := fun i : Fin 3 => ∑ j : Fin 3, |g i j|)
          (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ i)

/-- Each entrywise ball is an entrywise rational box. -/
private theorem ballSL_mem_ratBox (n : ℕ) : ballSL n ∈ ratBox := by
  refine ⟨Matrix.of (fun _ _ => -(n : ℚ)), Matrix.of (fun _ _ => (n : ℚ)), ?_⟩
  ext g
  simp only [ballSL, boxSL, Set.mem_ofPred_eq, Matrix.of_apply, Rat.cast_neg, Rat.cast_natCast]
  constructor
  · intro h i j; exact abs_le.mp (h i j)
  · intro h i j; exact abs_le.mpr (h i j)

/-- The entrywise balls are compact. -/
private theorem isCompact_ballSL (n : ℕ) : IsCompact (ballSL n) := by
  have h := Work.Topology.isCompact_entryBoxSL (0 : Matrix (Fin 3) (Fin 3) ℝ) (n : ℝ)
  simpa [ballSL] using h

/-- Every rational box is contained in an entrywise ball. -/
private theorem exists_ballSL_superset (a b : Matrix (Fin 3) (Fin 3) ℚ) :
    ∃ N : ℕ, boxSL a b ⊆ ballSL N := by
  refine ⟨⌈∑ i : Fin 3, ∑ j : Fin 3, (|(a i j : ℝ)| + |(b i j : ℝ)|)⌉₊, fun g hg i j => ?_⟩
  have ha : (a i j : ℝ) ≤ g i j := (hg i j).1
  have hb : g i j ≤ (b i j : ℝ) := (hg i j).2
  have key : |g i j| ≤ ∑ i : Fin 3, ∑ j : Fin 3, (|(a i j : ℝ)| + |(b i j : ℝ)|) := by
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i : Fin 3 => ∑ j : Fin 3, (|(a i j : ℝ)| + |(b i j : ℝ)|))
      (fun i _ => Finset.sum_nonneg (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)))
      (Finset.mem_univ i))
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun j : Fin 3 => (|(a i j : ℝ)| + |(b i j : ℝ)|))
      (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j))
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (a i j : ℝ), neg_abs_le (b i j : ℝ), abs_nonneg (a i j : ℝ),
        abs_nonneg (b i j : ℝ), ha]
    · linarith [le_abs_self (a i j : ℝ), le_abs_self (b i j : ℝ), abs_nonneg (a i j : ℝ),
        abs_nonneg (b i j : ℝ), hb]
  exact le_trans key (Nat.le_ceil _)

set_option linter.unusedVariables false in
theorem ext_of_ratBox_ratio {μ ν : MeasureTheory.Measure Work.EKLContract.SL3} (hμ : ∀ K : Set Work.EKLContract.SL3, IsCompact K → μ K < ⊤) (hν' : ∀ K : Set Work.EKLContract.SL3, IsCompact K → ν K < ⊤) (c : ℝ) (hc : 0 < c) (h : ∀ (a b : Matrix (Fin 3) (Fin 3) ℚ) (N : ℕ), μ {g : Work.EKLContract.SL3 | (∀ i j, (a i j : ℝ) ≤ g i j ∧ g i j ≤ (b i j : ℝ)) ∧ ∀ i j, |g i j| ≤ (N : ℝ)} = ENNReal.ofReal c * ν {g : Work.EKLContract.SL3 | (∀ i j, (a i j : ℝ) ≤ g i j ∧ g i j ≤ (b i j : ℝ)) ∧ ∀ i j, |g i j| ≤ (N : ℝ)}) : μ = ENNReal.ofReal c • ν := by
  have hA : (inferInstance : MeasurableSpace Work.EKLContract.SL3) =
      MeasurableSpace.generateFrom ratBox := by
    rw [ratBox_eq]
    exact Work.Topology.generateFrom_ratBox.symm
  refine Measure.ext_of_generateFrom_of_iUnion ratBox ballSL hA isPiSystem_ratBox
    iUnion_ballSL ballSL_mem_ratBox ?_ ?_
  · intro n
    exact ne_top_of_lt (hμ (ballSL n) (isCompact_ballSL n))
  · rintro s ⟨a, b, rfl⟩
    obtain ⟨N, hN⟩ := exists_ballSL_superset a b
    have hkey := h a b N
    have hset : {g : Work.EKLContract.SL3 |
        (∀ i j, (a i j : ℝ) ≤ g i j ∧ g i j ≤ (b i j : ℝ)) ∧
          ∀ i j, |g i j| ≤ (N : ℝ)} = boxSL a b := by
      ext g; constructor
      · intro hg; exact hg.1
      · intro hg; exact ⟨hg, hN hg⟩
    rw [hset] at hkey
    rw [Measure.smul_apply, smul_eq_mul]
    exact hkey

end Work.MeasureTheory
