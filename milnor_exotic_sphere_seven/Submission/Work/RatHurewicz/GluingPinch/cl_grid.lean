import Mathlib
import Submission.Work.RatHurewicz.GluingPinch.GridDefs
import Submission.Work.RatHurewicz.GluingPinch.CutGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `cl_grid`: the dyadic grid subdivision of a based `n`-cube

A based `n`-cube `p` which is `x₀` on every mid-hyperplane `{u i = 1/2}` (`i : Fin n`,
`m ∈ {0,1,2}` in the hypothesis `h`, i.e. on `{u i = 0}`, `{u i = 1/2}`, `{u i = 1}`) can be
subdivided along the mid-hyperplanes: the `2^n` dyadic cells `k : Fin n → Fin 2` give the affine
readings `cellCube n p k h` (`GridDefs.lean`), and the class of `p` is the product of their
classes (`Work.RatHurewicz.cl_grid`).

The proof is the `n`-fold iteration of the cut lemma `Work.RatHurewicz.cl_cut_gen`: cutting the
coordinate `i` at `1/2` rescales only the `i`-th coordinate, so after cutting all the coordinates
in a set `S` the reading on the cell `c : Fin n → Fin 2` is `partCube p h S c`
(`partCube_val`), and the additivity is the induction over the *number of coordinates cut*
(`Stmt`/`stmt_step`), the intermediate objects being full `GenLoop (Fin n)`'s.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical
open Work.Stems.Hur2

namespace Work.RatHurewicz.GluingPinch

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- The midpoint of `I = [0,1]`, written as an element of `unitInterval`. -/
def half : unitInterval := ⟨1/2, by norm_num⟩

@[simp] theorem half_coe : ((half : unitInterval) : ℝ) = 1/2 := rfl

/-- The half-chart step: `0` reads the left half `[0,1/2]`, `1` the right half `[1/2,1]`.  Written
with exactly the same `clamp` expression as `cellChart`, so that the cell charts match. -/
def step (b : Fin 2) : C(unitInterval, unitInterval) :=
  ⟨fun t => clamp ((((b : ℕ) : ℝ) + (t : ℝ)) / 2), by
    apply continuous_clamp.comp
    fun_prop⟩

theorem step_apply (b : Fin 2) (t : unitInterval) :
    step b t = clamp ((((b : ℕ) : ℝ) + (t : ℝ)) / 2) := rfl

/-- `step 0` reads the left half. -/
theorem step_zero_val (b : Fin 2) : step b 0 = 0 ∨ step b 0 = half := by
  have hb : (b : ℕ) = 0 ∨ (b : ℕ) = 1 := by omega
  rcases hb with h | h
  · left
    rw [step_apply]
    have harg : (((b : ℕ) : ℝ) + ((0 : unitInterval) : ℝ)) / 2 = 0 := by rw [h]; norm_num
    rw [harg, clamp_zero]
  · right
    rw [step_apply]
    have harg : (((b : ℕ) : ℝ) + ((0 : unitInterval) : ℝ)) / 2 = 1/2 := by rw [h]; norm_num
    rw [harg]
    apply Subtype.ext
    rw [Work.RatHurewicz.clamp_eq_of_mem (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1), half_coe]

/-- `step 1` reads the right half. -/
theorem step_one_val (b : Fin 2) : step b 1 = 1 ∨ step b 1 = half := by
  have hb : (b : ℕ) = 0 ∨ (b : ℕ) = 1 := by omega
  rcases hb with h | h
  · right
    rw [step_apply]
    have harg : (((b : ℕ) : ℝ) + ((1 : unitInterval) : ℝ)) / 2 = 1/2 := by rw [h]; norm_num
    rw [harg]
    apply Subtype.ext
    rw [Work.RatHurewicz.clamp_eq_of_mem (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1), half_coe]
  · left
    rw [step_apply]
    have harg : (((b : ℕ) : ℝ) + ((1 : unitInterval) : ℝ)) / 2 = 1 := by rw [h]; norm_num
    rw [harg, clamp_one]

/-- The reading map of the cell `c` of the grid obtained by cutting the coordinates in `S`:
coordinate `i ∈ S` is read through `step (c i)`, the others are untouched. -/
def gridMap {n : ℕ} (S : Finset (Fin n)) (c : Fin n → Fin 2) : C(IC n, IC n) :=
  ⟨fun u i => if i ∈ S then step (c i) (u i) else u i, by
    apply continuous_pi
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      exact (step (c i)).continuous.comp (continuous_apply i)
    · simp only [hi, if_false]
      exact continuous_apply i⟩

theorem gridMap_apply_of_mem {n : ℕ} (S : Finset (Fin n)) (c : Fin n → Fin 2) (u : IC n)
    {i : Fin n} (hi : i ∈ S) : gridMap S c u i = step (c i) (u i) := by
  show (if i ∈ S then step (c i) (u i) else u i) = step (c i) (u i)
  rw [if_pos hi]

theorem gridMap_apply_of_not_mem {n : ℕ} (S : Finset (Fin n)) (c : Fin n → Fin 2) (u : IC n)
    {i : Fin n} (hi : i ∉ S) : gridMap S c u i = u i := by
  show (if i ∈ S then step (c i) (u i) else u i) = u i
  rw [if_neg hi]

/-- Cutting *all* the coordinates gives the cell chart of `GridDefs.lean`. -/
theorem gridMap_univ {n : ℕ} (c : Fin n → Fin 2) :
    gridMap (Finset.univ : Finset (Fin n)) c = cellChart n c := by
  apply ContinuousMap.ext
  intro u
  funext i
  rw [gridMap_apply_of_mem (Finset.univ : Finset (Fin n)) c u (Finset.mem_univ i), step_apply,
    Work.RatHurewicz.cellChart_apply]

/-- The reading of `p` on the cell `c` of the grid obtained by cutting the coordinates in `S`.
It is a based cube: a point of `∂I^n` either has a coordinate outside `S` still at `0`/`1`, or a
coordinate of `S` whose read value is `0`, `1` or `1/2` — where `p` vanishes by `h`. -/
def partCube {n : ℕ} (p : GenLoop (Fin n) X x₀)
    (h : ∀ (i : Fin n) (m : Fin 3) (u : IC n), (u i : ℝ) = ((m : ℕ) : ℝ) / 2 → p.1 u = x₀)
    (S : Finset (Fin n)) (c : Fin n → Fin 2) : GenLoop (Fin n) X x₀ :=
  ⟨p.1.comp (gridMap S c), by
    intro u hu
    show p.1 (gridMap S c u) = x₀
    obtain ⟨j, hj | hj⟩ := hu
    · by_cases hjs : j ∈ S
      · rcases step_zero_val (c j) with h0 | h0
        · exact p.2 _ ⟨j, Or.inl (by rw [gridMap_apply_of_mem S c u hjs, hj, h0])⟩
        · refine h j 1 _ ?_
          rw [gridMap_apply_of_mem S c u hjs, hj, h0, half_coe]
          norm_num
      · exact p.2 _ ⟨j, Or.inl (by rw [gridMap_apply_of_not_mem S c u hjs, hj])⟩
    · by_cases hjs : j ∈ S
      · rcases step_one_val (c j) with h1 | h1
        · exact p.2 _ ⟨j, Or.inr (by rw [gridMap_apply_of_mem S c u hjs, hj, h1])⟩
        · refine h j 1 _ ?_
          rw [gridMap_apply_of_mem S c u hjs, hj, h1, half_coe]
          norm_num
      · exact p.2 _ ⟨j, Or.inr (by rw [gridMap_apply_of_not_mem S c u hjs, hj])⟩⟩

theorem partCube_val {n : ℕ} (p : GenLoop (Fin n) X x₀)
    (h : ∀ (i : Fin n) (m : Fin 3) (u : IC n), (u i : ℝ) = ((m : ℕ) : ℝ) / 2 → p.1 u = x₀)
    (S : Finset (Fin n)) (c : Fin n → Fin 2) (u : IC n) :
    (partCube p h S c).1 u = p.1 (gridMap S c u) := rfl

/-- No cut: the reading is `p` itself. -/
theorem partCube_empty {n : ℕ} (p : GenLoop (Fin n) X x₀)
    (h : ∀ (i : Fin n) (m : Fin 3) (u : IC n), (u i : ℝ) = ((m : ℕ) : ℝ) / 2 → p.1 u = x₀)
    (c : Fin n → Fin 2) : partCube p h ∅ c = p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  rfl

/-- All the coordinates cut: the reading is the cell cube of `GridDefs.lean`. -/
theorem partCube_univ {n : ℕ} (p : GenLoop (Fin n) X x₀)
    (h : ∀ (i : Fin n) (m : Fin 3) (u : IC n), (u i : ℝ) = ((m : ℕ) : ℝ) / 2 → p.1 u = x₀)
    (c : Fin n → Fin 2) : partCube p h Finset.univ c = cellCube n p c h := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  show p.1 (gridMap (Finset.univ : Finset (Fin n)) c u) = p.1 (cellChart n c u)
  rw [gridMap_univ]

/-- The left half of `partCube p h S c` is the cell with the coordinate `i` read at `0`. -/
theorem cutL_half {n : ℕ} (p : GenLoop (Fin n) X x₀)
    (h : ∀ (i : Fin n) (m : Fin 3) (u : IC n), (u i : ℝ) = ((m : ℕ) : ℝ) / 2 → p.1 u = x₀)
    (S : Finset (Fin n)) (c : Fin n → Fin 2) (i : Fin n) (hi : i ∉ S)
    (h' : ∀ u : IC n, u i = half → (partCube p h S c).1 u = x₀) :
    Work.RatHurewicz.cutL i half (partCube p h S c) h'
      = partCube p h (insert i S) (Function.update c i 0) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  show p.1 (gridMap S c (Function.update u i (clamp ((half : ℝ) * ((u i : unitInterval) : ℝ)))))
      = p.1 (gridMap (insert i S) (Function.update c i 0) u)
  congr 1
  funext j
  by_cases hji : j = i
  · rw [hji]
    rw [gridMap_apply_of_not_mem S c _ hi, Function.update_apply, if_pos rfl,
      gridMap_apply_of_mem (insert i S) (Function.update c i 0) u (Finset.mem_insert_self i S),
      Function.update_apply, if_pos rfl, step_apply]
    congr 1
    rw [half_coe]
    simp only [Fin.val_zero, Nat.cast_zero, zero_add]
    ring
  · by_cases hjs : j ∈ S
    · rw [gridMap_apply_of_mem S c _ hjs, Function.update_apply, if_neg hji,
        gridMap_apply_of_mem (insert i S) (Function.update c i 0) u
          (Finset.mem_insert.mpr (Or.inr hjs)),
        Function.update_apply, if_neg hji]
    · rw [gridMap_apply_of_not_mem S c _ hjs, Function.update_apply, if_neg hji,
        gridMap_apply_of_not_mem (insert i S) (Function.update c i 0) u
          (by rw [Finset.mem_insert]; exact fun h => h.elim hji hjs)]

/-- The right half of `partCube p h S c` is the cell with the coordinate `i` read at `1`. -/
theorem cutR_half {n : ℕ} (p : GenLoop (Fin n) X x₀)
    (h : ∀ (i : Fin n) (m : Fin 3) (u : IC n), (u i : ℝ) = ((m : ℕ) : ℝ) / 2 → p.1 u = x₀)
    (S : Finset (Fin n)) (c : Fin n → Fin 2) (i : Fin n) (hi : i ∉ S)
    (h' : ∀ u : IC n, u i = half → (partCube p h S c).1 u = x₀) :
    Work.RatHurewicz.cutR i half (partCube p h S c) h'
      = partCube p h (insert i S) (Function.update c i 1) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  show p.1 (gridMap S c (Function.update u i
        (clamp ((half : ℝ) + (1 - (half : ℝ)) * ((u i : unitInterval) : ℝ)))))
      = p.1 (gridMap (insert i S) (Function.update c i 1) u)
  congr 1
  funext j
  by_cases hji : j = i
  · rw [hji]
    rw [gridMap_apply_of_not_mem S c _ hi, Function.update_apply, if_pos rfl,
      gridMap_apply_of_mem (insert i S) (Function.update c i 1) u (Finset.mem_insert_self i S),
      Function.update_apply, if_pos rfl, step_apply]
    congr 1
    rw [half_coe]
    simp only [Fin.val_one, Nat.cast_one]
    ring
  · by_cases hjs : j ∈ S
    · rw [gridMap_apply_of_mem S c _ hjs, Function.update_apply, if_neg hji,
        gridMap_apply_of_mem (insert i S) (Function.update c i 1) u
          (Finset.mem_insert.mpr (Or.inr hjs)),
        Function.update_apply, if_neg hji]
    · rw [gridMap_apply_of_not_mem S c _ hjs, Function.update_apply, if_neg hji,
        gridMap_apply_of_not_mem (insert i S) (Function.update c i 1) u
          (by rw [Finset.mem_insert]; exact fun h => h.elim hji hjs)]

/-- The set of full assignments agreeing with `c` on the cut coordinates `S`. -/
def exts {n : ℕ} (S : Finset (Fin n)) (c : Fin n → Fin 2) : Finset (Fin n → Fin 2) :=
  Finset.univ.filter (fun k => ∀ i ∈ S, k i = c i)

theorem mem_exts {n : ℕ} {S : Finset (Fin n)} {c : Fin n → Fin 2} {k : Fin n → Fin 2} :
    k ∈ exts S c ↔ ∀ i ∈ S, k i = c i := by
  simp [exts]

theorem exts_empty {n : ℕ} (c : Fin n → Fin 2) : exts (∅ : Finset (Fin n)) c = Finset.univ := by
  apply Finset.ext
  intro k
  rw [mem_exts]
  simp

theorem exts_univ {n : ℕ} (c : Fin n → Fin 2) : exts (Finset.univ : Finset (Fin n)) c = {c} := by
  apply Finset.ext
  intro k
  rw [mem_exts, Finset.mem_singleton]
  constructor
  · intro hk
    funext i
    exact hk i (Finset.mem_univ i)
  · intro hk i _
    rw [hk]

/-- Splitting the agreement condition at a coordinate not yet in `S`. -/
theorem exts_insert {n : ℕ} (S : Finset (Fin n)) (c : Fin n → Fin 2) (i : Fin n) (hi : i ∉ S) :
    exts S c = exts (insert i S) (Function.update c i 0)
      ∪ exts (insert i S) (Function.update c i 1) := by
  apply Finset.ext
  intro k
  rw [mem_exts, Finset.mem_union, mem_exts, mem_exts]
  constructor
  · intro hk
    rcases (Fin.exists_fin_two (p := fun b => k i = b)).mp ⟨k i, rfl⟩ with h | h
    · left
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · rw [h, Function.update_apply, if_pos rfl]
      · have hji : j ≠ i := by rintro rfl; exact hi hjs
        rw [hk j hjs, Function.update_apply, if_neg hji]
    · right
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · rw [h, Function.update_apply, if_pos rfl]
      · have hji : j ≠ i := by rintro rfl; exact hi hjs
        rw [hk j hjs, Function.update_apply, if_neg hji]
  · intro hk
    rcases hk with hk | hk
    · intro j hjs
      have hji : j ≠ i := by rintro rfl; exact hi hjs
      have h' := hk j (Finset.mem_insert.mpr (Or.inr hjs))
      rwa [Function.update_apply, if_neg hji] at h'
    · intro j hjs
      have hji : j ≠ i := by rintro rfl; exact hi hjs
      have h' := hk j (Finset.mem_insert.mpr (Or.inr hjs))
      rwa [Function.update_apply, if_neg hji] at h'

/-- The two pieces of the splitting are disjoint (the coordinate `i` reads `0` versus `1`). -/
theorem exts_disjoint {n : ℕ} (S : Finset (Fin n)) (c : Fin n → Fin 2) (i : Fin n)
    (_hi : i ∉ S) :
    Disjoint (exts (insert i S) (Function.update c i 0))
      (exts (insert i S) (Function.update c i 1)) := by
  rw [Finset.disjoint_left]
  intro k h0
  rw [mem_exts] at h0
  intro h1
  rw [mem_exts] at h1
  have e0 := h0 i (Finset.mem_insert_self i S)
  have e1 := h1 i (Finset.mem_insert_self i S)
  rw [Function.update_apply, if_pos rfl] at e0 e1
  exact absurd (e0.symm.trans e1) (by decide : (0 : Fin 2) ≠ 1)

/-- The product over the agreeing assignments splits as the product of the two halves. -/
theorem prod_exts_split {n : ℕ} (S : Finset (Fin n)) (c : Fin n → Fin 2) (i : Fin n) (hi : i ∉ S)
    {M : Type*} [CommMonoid M] (f : (Fin n → Fin 2) → M) :
    ∏ k ∈ exts S c, f k
      = (∏ k ∈ exts (insert i S) (Function.update c i 0), f k)
        * (∏ k ∈ exts (insert i S) (Function.update c i 1), f k) := by
  rw [← Finset.prod_union (exts_disjoint S c i hi), ← exts_insert S c i hi]

/-- **The induction step of `cl_grid`** (downward in the cut set): if the additivity is known after
cutting one more coordinate, it holds before that cut, by the cut lemma `cl_cut_gen`. -/
theorem stmt_step {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (p : GenLoop (Fin n) X x₀)
    (h : ∀ (i : Fin n) (m : Fin 3) (u : IC n), (u i : ℝ) = ((m : ℕ) : ℝ) / 2 → p.1 u = x₀)
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S)
    (H : ∀ c : Fin n → Fin 2, cl n X x₀ (partCube p h (insert i S) c)
        = ∏ k ∈ exts (insert i S) c, cl n X x₀ (partCube p h Finset.univ k)) :
    ∀ c : Fin n → Fin 2, cl n X x₀ (partCube p h S c)
        = ∏ k ∈ exts S c, cl n X x₀ (partCube p h Finset.univ k) := by
  intro c
  have hL : ∀ u : IC n, u i = half → (partCube p h S c).1 u = x₀ := by
    intro u hu
    show p.1 (gridMap S c u) = x₀
    refine h i 1 (gridMap S c u) ?_
    rw [gridMap_apply_of_not_mem S c u hi, hu, half_coe]
    norm_num
  rw [Work.RatHurewicz.cl_cut_gen i (partCube p h S c) half hL,
      cutL_half p h S c i hi hL, cutR_half p h S c i hi hL,
      H (Function.update c i 0), H (Function.update c i 1)]
  exact (prod_exts_split S c i hi (fun k => cl n X x₀ (partCube p h Finset.univ k))).symm

theorem cl_grid {n : ℕ} [NeZero n] [Nontrivial (Fin n)] {X : Type} [TopologicalSpace X]
    {x₀ : X} (p : GenLoop (Fin n) X x₀)
    (h : ∀ (i : Fin n) (m : Fin 3) (u : Work.Stems.Cubical.IC n),
      (u i : ℝ) = ((m : ℕ) : ℝ) / 2 → p.1 u = x₀) :
    Work.RatHurewicz.cl n X x₀ p
      = ∏ k : Fin n → Fin 2,
          Work.RatHurewicz.cl n X x₀ (Work.RatHurewicz.cellCube n p k h) := by
  have key : ∀ T : Finset (Fin n), ∀ c : Fin n → Fin 2,
      cl n X x₀ (partCube p h (Finset.univ \ T) c)
        = ∏ k ∈ exts (Finset.univ \ T) c, cl n X x₀ (partCube p h Finset.univ k) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro c
      rw [Finset.sdiff_empty, exts_univ, Finset.prod_singleton]
    · intro i T hiT ih c
      have hmem : i ∈ Finset.univ \ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiT⟩
      have hins : insert i (Finset.univ \ insert i T) = Finset.univ \ T := by
        rw [Finset.sdiff_insert, Finset.insert_erase hmem]
      have hmemS : i ∉ Finset.univ \ insert i T := by
        simp [Finset.mem_sdiff]
      rw [← hins] at ih
      exact stmt_step p h (Finset.univ \ insert i T) i hmemS ih c
  have hfin := key Finset.univ (fun _ => (0 : Fin 2))
  rw [Finset.sdiff_self] at hfin
  rw [partCube_empty] at hfin
  rw [exts_empty] at hfin
  simp only [partCube_univ] at hfin
  exact hfin

end

end Work.RatHurewicz.GluingPinch
