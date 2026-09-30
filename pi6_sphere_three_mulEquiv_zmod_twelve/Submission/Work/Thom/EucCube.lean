import Mathlib

set_option synthInstance.maxHeartbeats 400000

/-!
# The Euclidean cube model for the disc pair

This file fixes the model of the `n`-disc pair used by the induction of
`Work.Thom.subsingleton_relComplex_cube`: the unit **cube** `[-1,1]^n ⊆ ℝⁿ` together with its
boundary (the points with some coordinate `±1`).  The cube is used instead of the Euclidean ball
because its slices by a coordinate hyperplane are *products*, which makes the Mayer–Vietoris
induction of the vanishing theorem purely formal.

The ambient model space is the function type `Fin n → ℝ` (with the product topology, which is the
topology of `EuclideanSpace ℝ (Fin n)` under `PiLp.homeomorph`), so that the product structure of
the cube is visible in the types.

* `Work.Thom.euCube n` — the cube `{x : ℝⁿ | ∀ i, |x i| ≤ 1}`;
* `Work.Thom.euCubeBdry n` — its boundary `{x | x ∈ euCube n ∧ ∃ i, |x i| = 1}`;
* `Work.Thom.euCubeTop n`, `Work.Thom.euCubeBot n` — the two pieces of `euCube (n+1)` cut by the
  last coordinate (`> -1/2` and `< 1/2`), an open cover of the cube;
* `Work.Thom.euCubeSplit n` — the coordinate splitting `ℝⁿ⁺¹ ≅ ℝⁿ × ℝ` given by the last
  coordinate.
-/

namespace Work.Thom

/-- The unit cube `[-1,1]^n ⊆ ℝⁿ`. -/
def euCube (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, |x i| ≤ 1}

/-- The boundary of the unit cube: the points of the cube with some coordinate `±1`. -/
def euCubeBdry (n : ℕ) : Set (Fin n → ℝ) :=
  {x | x ∈ euCube n ∧ ∃ i, |x i| = 1}

@[simp] theorem mem_euCube {n : ℕ} {x : Fin n → ℝ} :
    x ∈ euCube n ↔ ∀ i, |x i| ≤ 1 := Iff.rfl

@[simp] theorem mem_euCubeBdry {n : ℕ} {x : Fin n → ℝ} :
    x ∈ euCubeBdry n ↔ x ∈ euCube n ∧ ∃ i, |x i| = 1 := Iff.rfl

theorem euCubeBdry_eq (n : ℕ) :
    euCubeBdry n = {x : Fin n → ℝ | ∃ i, |x i| = 1} ∩ euCube n := by
  ext x
  simp only [mem_euCubeBdry, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact and_comm

@[simp] theorem euCube_zero : euCube 0 = Set.univ := by
  ext x
  simp [mem_euCube]

@[simp] theorem euCubeBdry_zero : euCubeBdry 0 = (∅ : Set (Fin 0 → ℝ)) := by
  ext x
  simp [mem_euCubeBdry]

theorem euCubeBdry_subset (n : ℕ) : euCubeBdry n ⊆ euCube n := fun _ h => h.1

/-! ## The two pieces cutting the cube by the last coordinate -/

/-- The "upper" piece of the cube `euCube (n+1)`: its last coordinate exceeds `-1/2`. -/
def euCubeTop (n : ℕ) : Set (Fin (n+1) → ℝ) :=
  {x | x ∈ euCube (n+1) ∧ x (Fin.last n) > -1/2}

/-- The "lower" piece of the cube `euCube (n+1)`: its last coordinate is less than `1/2`. -/
def euCubeBot (n : ℕ) : Set (Fin (n+1) → ℝ) :=
  {x | x ∈ euCube (n+1) ∧ x (Fin.last n) < 1/2}

@[simp] theorem mem_euCubeTop {n : ℕ} {x : Fin (n+1) → ℝ} :
    x ∈ euCubeTop n ↔ x ∈ euCube (n+1) ∧ x (Fin.last n) > -1/2 := Iff.rfl

@[simp] theorem mem_euCubeBot {n : ℕ} {x : Fin (n+1) → ℝ} :
    x ∈ euCubeBot n ↔ x ∈ euCube (n+1) ∧ x (Fin.last n) < 1/2 := Iff.rfl

theorem euCubeTop_union_euCubeBot (n : ℕ) :
    euCubeTop n ∪ euCubeBot n = euCube (n+1) := by
  ext x
  simp only [Set.mem_union, mem_euCubeTop, mem_euCubeBot]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    rcases lt_or_ge (-1/2) (x (Fin.last n)) with hlt | hle
    · exact Or.inl ⟨h, hlt⟩
    · exact Or.inr ⟨h, by linarith⟩

theorem euCubeTop_subset (n : ℕ) : euCubeTop n ⊆ euCube (n+1) := fun _ h => h.1

theorem euCubeBot_subset (n : ℕ) : euCubeBot n ⊆ euCube (n+1) := fun _ h => h.1

/-! ## The coordinate splitting -/

/-- The coordinate splitting `ℝⁿ⁺¹ ≅ ℝⁿ × ℝ` given by the last coordinate. -/
def euCubeSplit (n : ℕ) : (Fin (n+1) → ℝ) ≃ₜ (Fin n → ℝ) × ℝ where
  toFun x := (fun i => x i.castSucc, x (Fin.last n))
  invFun p := Fin.snoc p.1 p.2
  left_inv x := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j
      simp
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext i
      simp
    · simp
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_ <;> fun_prop
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    refine Fin.lastCases ?_ ?_ i
    · simp only [Fin.snoc_last]
      exact continuous_snd
    · intro j
      simp only [Fin.snoc_castSucc]
      exact (continuous_apply j).comp continuous_fst

@[simp] theorem euCubeSplit_apply {n : ℕ} (x : Fin (n+1) → ℝ) :
    euCubeSplit n x = (fun i => x i.castSucc, x (Fin.last n)) := rfl

@[simp] theorem euCubeSplit_symm_apply {n : ℕ} (p : (Fin n → ℝ) × ℝ) :
    (euCubeSplit n).symm p = Fin.snoc p.1 p.2 := rfl

theorem euCubeSplit_mem_cube {n : ℕ} (x : Fin (n+1) → ℝ) (hx : |x (Fin.last n)| < 1/2) :
    (euCubeSplit n x).1 ∈ euCube n ↔ x ∈ euCube (n+1) := by
  have hlast : |x (Fin.last n)| ≤ 1 := le_of_lt (lt_trans hx (by norm_num))
  simp only [mem_euCube, euCubeSplit_apply]
  constructor
  · intro h1 j
    refine Fin.lastCases ?_ ?_ j
    · exact hlast
    · intro k
      exact h1 k
  · intro h i
    exact h i.castSucc

theorem euCubeSplit_mem_cubeBdry {n : ℕ} (x : Fin (n+1) → ℝ)
    (hx : |x (Fin.last n)| < 1/2) :
    (euCubeSplit n x).1 ∈ euCubeBdry n ↔ x ∈ euCubeBdry (n+1) := by
  have hlast_lt : x (Fin.last n) < 1/2 := (abs_lt.mp hx).2
  have hlast_gt : -(1/2) < x (Fin.last n) := (abs_lt.mp hx).1
  have hne : x (Fin.last n) ≠ 1 ∧ x (Fin.last n) ≠ -1 := by
    constructor <;> intro h <;> rw [h] at hx <;> norm_num at hx
  simp only [mem_euCubeBdry, mem_euCube, euCubeSplit_apply]
  constructor
  · rintro ⟨h1, i, hi⟩
    refine ⟨fun j => ?_, ⟨i.castSucc, hi⟩⟩
    refine Fin.lastCases ?_ ?_ j
    · rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    · intro k
      exact h1 k
  · rintro ⟨h1, i, hi⟩
    refine ⟨fun j => h1 j.castSucc, ?_⟩
    revert hi
    refine Fin.lastCases ?_ ?_ i
    · intro hi
      rw [hi] at hx
      norm_num at hx
    · intro k hi
      exact ⟨k, hi⟩

end Work.Thom
