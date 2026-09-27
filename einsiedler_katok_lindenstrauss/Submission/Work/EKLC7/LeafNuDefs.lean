import Mathlib
import Submission.Work.EKLC7.LeafFlowerDefs
import Submission.Work.EKLC7.OrbitCoord
import Submission.Work.EKLComp.condExpKernel_atom

/-!
# `Work.EKLC7.LeafNuDefs` — the definition of the leafwise measures from a flower family

Fix a probability measure `μ` on `X₃`, a closed subgroup `U ≤ SL₃(ℝ)`, a jointly measurable
"leaf coordinate" `coord : X₃ → X₃ → SL₃(ℝ)` (so that for `x` with free orbit and
`y ∈ U • x`, `coord x y` is the unique `u ∈ U` with `u • x = y`), and a family of flowers
`F : FlowerFam U μ` (Pisa Cor. 6.15, in the uniform form needed for the patching (6.19a)).

The leafwise measure at `x` is the Radon measure `ν x` on `SL₃(ℝ)` defined by the patching
formula (Pisa 6.19a): for every bounded Borel `D ⊆ U` one chooses a flower `k` whose atom at `x`
contains the plaque `D • x` and sets

`ν x (D) = μ^{A_k}_x (D • x) / μ^{A_k}_x (B₁ᵁ • x)`.

Here we realise the measure `ν x` as a countable sum over the annuli
`Ann U n = Blk U n ∖ Blk U (n-1)` (whose union is `U`), the `n`-th term being the normalised
push-forward of the conditional measure of the flower chosen at level `n` (whose atom at `x`
contains the plaque of radius `n+2`).  The terms are the *normalised* ratios, so that the
well-definedness of the ratio (proved from Pisa 5.17, `Work.EKLComp.plaque_propor`) makes the
patching consistent.

Outside the (conull, measurable) domain `X'` the definition is replaced by the Dirac mass at `1`;
this is irrelevant for every clause of `IsLeafwise` except global measurability, where it makes
the function `x ↦ ∫ f dν x` measurable.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Classical

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract
open Work.EKLComp

/-! ## The annuli inside `U` -/

/-- The closed `U`-balls of radius `n+2`, `n ∈ ℕ`.  Their union is `U`. -/
def Blk (U : Subgroup SL3) (n : ℕ) : Set SL3 := Uball U ((n : ℝ) + 2)

/-- The annuli `Ann U n = Blk U n \ Blk U (n-1)`; they are pairwise disjoint and their union is
`U`.  `Ann U 0 = Uball U 2` contains the normalising set `Box1 U = Ucl U 1`. -/
def Ann (U : Subgroup SL3) : ℕ → Set SL3
  | 0 => Blk U 0
  | (n + 1) => Blk U (n + 1) \ Blk U n

@[simp] theorem Ann_zero (U : Subgroup SL3) : Ann U 0 = Blk U 0 := rfl

@[simp] theorem Ann_succ (U : Subgroup SL3) (n : ℕ) :
    Ann U (n + 1) = Blk U (n + 1) \ Blk U n := rfl

theorem Blk_mono (U : Subgroup SL3) {n m : ℕ} (h : n ≤ m) : Blk U n ⊆ Blk U m :=
  Uball_mono (by
    have h' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    linarith)

theorem Blk_subset_U (U : Subgroup SL3) (n : ℕ) : Blk U n ⊆ (U : Set SL3) := fun _ h => h.1

theorem Ann_subset_Blk (U : Subgroup SL3) (n : ℕ) : Ann U n ⊆ Blk U n := by
  cases n with
  | zero => rw [Ann_zero]
  | succ n => rw [Ann_succ]; exact Set.diff_subset

theorem blk_subset_Ann_iUnion (U : Subgroup SL3) (m : ℕ) : Blk U m ⊆ ⋃ n, Ann U n := by
  induction m with
  | zero => intro x hx; exact Set.mem_iUnion.mpr ⟨0, hx⟩
  | succ m ih =>
    intro x hx
    by_cases h : x ∈ Blk U m
    · exact ih h
    · exact Set.mem_iUnion.mpr ⟨m + 1, ⟨hx, h⟩⟩

theorem blk_mem_of_mem (U : Subgroup SL3) (u : SL3) (hu : u ∈ U) : ∃ n, u ∈ Blk U n := by
  have h : ∃ r : ℝ, ∀ i j : Fin 3,
      |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < r := by
    refine ⟨(∑ i, ∑ j, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|) + 1, fun i j => ?_⟩
    have hnn : ∀ i j : Fin 3, 0 ≤ |(u : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := fun i j => abs_nonneg _
    have h1 : |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ ∑ i, ∑ j, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
      calc |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          ≤ ∑ j, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
            Finset.single_le_sum (fun j _ => hnn i j) (Finset.mem_univ j)
        _ ≤ ∑ i, ∑ j, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j
              - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
            Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j))
              (Finset.mem_univ i)
    linarith
  obtain ⟨r, hr⟩ := h
  refine ⟨Nat.ceil r, hu, fun i j => ?_⟩
  have := Nat.le_ceil r
  linarith [hr i j]

theorem iUnion_Blk (U : Subgroup SL3) : (⋃ n, Blk U n) = (U : Set SL3) := by
  ext u
  constructor
  · intro h; obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h; exact hn.1
  · intro hu; exact Set.mem_iUnion.mpr (blk_mem_of_mem U u hu)

theorem iUnion_Ann (U : Subgroup SL3) : (⋃ n, Ann U n) = (U : Set SL3) := by
  refine le_antisymm ?_ ?_
  · refine Set.iUnion_subset fun n => ?_
    exact Set.Subset.trans (Ann_subset_Blk U n) (Blk_subset_U U n)
  · rw [← iUnion_Blk U]
    exact Set.iUnion_subset fun m => blk_subset_Ann_iUnion U m

theorem Ann_subset_U (U : Subgroup SL3) (n : ℕ) : Ann U n ⊆ (U : Set SL3) :=
  Set.Subset.trans (Ann_subset_Blk U n) (Blk_subset_U U n)

/-- `Ann U n` is disjoint from `Blk U m` for `m < n`. -/
theorem Ann_disjoint_Blk (U : Subgroup SL3) {n m : ℕ} (h : m < n) :
    Disjoint (Ann U n) (Blk U m) := by
  cases n with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ n =>
    have hmn : m ≤ n := Nat.lt_succ_iff.mp h
    rw [Ann_succ]
    exact Set.disjoint_left.mpr fun x hx hx' => hx.2 (Blk_mono U hmn hx')

theorem Ann_pairwise (U : Subgroup SL3) : Pairwise fun n m => Disjoint (Ann U n) (Ann U m) := by
  intro n m h
  rcases Nat.lt_or_gt_of_ne h with h' | h'
  · refine Set.disjoint_left.mpr fun x hx hx' => ?_
    exact (Set.disjoint_left.mp (Ann_disjoint_Blk U h') hx') (Ann_subset_Blk U n hx)
  · refine Set.disjoint_left.mpr fun x hx hx' => ?_
    exact (Set.disjoint_left.mp (Ann_disjoint_Blk U h') hx) ((Ann_subset_Blk U m) hx')

theorem box1_subset_Ann_zero (U : Subgroup SL3) : Box1 U ⊆ Ann U 0 := fun g hg =>
  Ucl_subset_Uball (by norm_num) hg

theorem box1_disjoint_Ann_succ (U : Subgroup SL3) (n : ℕ) :
    Disjoint (Box1 U) (Ann U (n + 1)) :=
  Set.disjoint_left.mpr fun g hg hg' => by
    rw [Ann_succ] at hg'
    exact hg'.2 (Blk_mono U (Nat.zero_le n) (Ucl_subset_Uball (by norm_num) hg))

end Work.EKLC7

/-! ## The chosen flower and its conditional measure

The definitions below take the flower family as their first argument, so they live in the
namespace `Work.EKLC7.FlowerFam` and dot notation applies. -/

namespace Work.EKLC7.FlowerFam

open MeasureTheory Filter Topology
open scoped ENNReal
open Classical
open Work.EKLC7 Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3} {μ : Measure X3}

/-- **The flower index chosen at level `n`**: the least `j` with `x` in the base of the `j`-th
flower and radius at least `n+2`.  (Junk value `0` when no such flower exists; this can only
happen outside the conull set of the cover condition.) -/
def chose (F : FlowerFam U μ) (n : ℕ) (x : X3) : ℕ :=
  if h : ∃ j, x ∈ F.E j ∧ (n : ℝ) + 2 ≤ F.R j then Nat.find h else 0

theorem chose_spec (F : FlowerFam U μ) {n : ℕ} {x : X3}
    (h : ∃ j, x ∈ F.E j ∧ (n : ℝ) + 2 ≤ F.R j) :
    x ∈ F.E (F.chose n x) ∧ (n : ℝ) + 2 ≤ F.R (F.chose n x) := by
  simp only [chose, dif_pos h]
  exact Nat.find_spec h

theorem le_chose (F : FlowerFam U μ) {n j : ℕ} {x : X3}
    (h : x ∈ F.E j ∧ (n : ℝ) + 2 ≤ F.R j) : F.chose n x ≤ j := by
  have hex : ∃ k, x ∈ F.E k ∧ (n : ℝ) + 2 ≤ F.R k := ⟨j, h⟩
  simp only [chose, dif_pos hex]
  exact Nat.find_min' hex h

theorem measE_chose (F : FlowerFam U μ) (n : ℕ) (x : X3) : MeasurableSet (F.E (F.chose n x)) :=
  F.measE _

/-- The conditional measure of the chosen flower at level `n`, at `x`. -/
def kap (F : FlowerFam U μ) [IsFiniteMeasure μ] (n : ℕ) (x : X3) : Measure X3 :=
  ProbabilityTheory.condExpKernel (μ.restrict (F.Z (F.chose n x))) (F.m (F.chose n x)) x

/-- The normalising constant: the mass of the plaque of the normalising set `Box1 U`. -/
def dd (F : FlowerFam U μ) [IsFiniteMeasure μ] (n : ℕ) (x : X3) : ℝ≥0∞ :=
  F.kap n x ((fun g : SL3 => g • x) '' (Box1 U))

/-- The push-forward of the conditional measure to the group along the leaf coordinate. -/
def prp (F : FlowerFam U μ) [IsFiniteMeasure μ] (coord : X3 → X3 → SL3) (n : ℕ) (x : X3) :
    Measure SL3 :=
  (F.kap n x).map (coord x)

/-- The `n`-th term of the patching: the normalised push-forward, restricted to the `n`-th
annulus of `U`. -/
def trm (F : FlowerFam U μ) [IsFiniteMeasure μ] (coord : X3 → X3 → SL3) (n : ℕ) (x : X3) :
    Measure SL3 :=
  (F.dd n x)⁻¹ • ((F.prp coord n x).restrict (Ann U n))

/-- The patched measure (Pisa 6.19a): the sum of the `n`-th terms over all annuli. -/
def raw (F : FlowerFam U μ) [IsFiniteMeasure μ] (coord : X3 → X3 → SL3) (x : X3) :
    Measure SL3 :=
  Measure.sum (fun n => F.trm coord n x)

/-- **The system of leafwise measures** built from a flower family: on the (conull) domain `X'`
it is the patched measure, outside it the Dirac mass at `1` (which makes the global measurability
clause of `IsLeafwise` true). -/
def nu (F : FlowerFam U μ) [IsFiniteMeasure μ] (coord : X3 → X3 → SL3) (X' : Set X3) :
    X3 → Measure SL3 :=
  fun x => if x ∈ X' then F.raw coord x else Measure.dirac 1

theorem nu_of_mem {F : FlowerFam U μ} [IsFiniteMeasure μ] {coord : X3 → X3 → SL3}
    {X' : Set X3} {x : X3} (hx : x ∈ X') : F.nu coord X' x = F.raw coord x := by
  rw [nu, if_pos hx]

theorem nu_of_notMem {F : FlowerFam U μ} [IsFiniteMeasure μ] {coord : X3 → X3 → SL3}
    {X' : Set X3} {x : X3} (hx : x ∉ X') : F.nu coord X' x = Measure.dirac 1 := by
  rw [nu, if_neg hx]

end Work.EKLC7.FlowerFam
