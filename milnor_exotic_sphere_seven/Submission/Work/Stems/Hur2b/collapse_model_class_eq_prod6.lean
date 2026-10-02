import Mathlib
import Submission.Work.Stems.Hur2b.GluingModel
import Submission.Work.Stems.Hur2b.Assembly
import Submission.Work.Stems.Hur2b.cl_cut_vertical
import Submission.Work.Stems.Hur2b.collapseModel_class_eq_one
import Submission.Work.Stems.Hur2b.NetLayout
import Submission.Work.Stems.Hur2b.NetData
import Submission.Work.Stems.Hur2b.cl_grid8
import Submission.Work.Stems.Hur2b.cl_comp_swapMap
import Submission.Work.Stems.Hur2b.net_model

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Stems.Hur2b

open scoped unitInterval Topology

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

/-- The class of a based cube reversed in the `i`-th coordinate is the inverse of its class.  (This
is the elementary degree `-1` case used in the computation of the readings' contributions.) -/
theorem cl_symmAt {X : Type} [TopologicalSpace X] {x₀ : X} (i : Fin 2)
    (p : GenLoop (Fin 2) X x₀) :
    Work.Stems.Hur2b.cl x₀ (GenLoop.symmAt i p) = (Work.Stems.Hur2b.cl x₀ p)⁻¹ := by
  rw [Work.Stems.Hur2b.cl, Work.Stems.Hur2b.cl]
  exact (HomotopyGroup.inv_spec (N := Fin 2) (i := i) (p := p)).symm

/-! ## The readings as self-maps of the square, and the coordinate reversals -/

/-- The reading of the `k`-th T-net cell, as a self-map of the square (the face inclusion is
dropped: `netRead k = (faceIncl _ _).comp (netReadMap k)`). -/
def netReadMap : Fin 6 → C(IC 2, IC 2)
  | 0 => readMap (-8) 3 8 (-3)
  | 1 => readMap (-8) 4 8 (-3)
  | 2 => readMap 8 (-4) 8 (-3)
  | 3 => readMap 8 (-5) 8 (-3)
  | 4 => readSwap (-8) 4 (-8) 3
  | 5 => readSwap (-8) 4 8 (-4)

/-- The reversal of the `i`-th coordinate of the square (the self-map used by `GenLoop.symmAt`). -/
def revMap (i : Fin 2) : C(IC 2, IC 2) :=
  ⟨fun y => fun j => if j = i then σ (y i) else y j, by
    apply continuous_pi
    intro j
    by_cases h : j = i
    · rw [h]
      rw [show (fun a : IC 2 => if i = i then σ (a i) else a i) = fun a : IC 2 => σ (a i) from
        funext (fun a => if_pos rfl)]
      exact unitInterval.continuous_symm.comp (continuous_apply i)
    · rw [show (fun a : IC 2 => if j = i then σ (a i) else a j) = fun a : IC 2 => a j from
        funext (fun a => if_neg h)]
      exact continuous_apply j⟩

/-- The clamp of a real in `[0,1]` is the corresponding point of the unit interval. -/
theorem clamp_coe_of_mem' {r : ℝ} (h : r ∈ Set.Icc (0:ℝ) 1) : clamp r = (⟨r, h⟩ : unitInterval) :=
  clamp_coe ⟨r, h⟩

/-- `clamp` of a point of `I` is that point. -/
theorem clamp_self (s : unitInterval) : clamp (s : ℝ) = s := clamp_coe_of_mem' s.2

/-- `clamp (1 - s) = σ s`. -/
theorem clamp_one_sub (s : unitInterval) : clamp (1 - (s : ℝ)) = σ s := by
  refine (clamp_coe_of_mem' ?_).trans (Subtype.ext ?_)
  · exact ⟨by linarith [s.2.2], by linarith [s.2.1]⟩
  · rw [unitInterval.coe_symm_eq]


/-! ## The dihedral maps of the square and the readings' coordinates -/

/-- `aff α a (clamp (γ s + δ)) = s` when the affine data is the identity on the range. -/
theorem aff_comp_clamp_self {α a γ δ : ℝ} {s : unitInterval}
    (h : γ * (s:ℝ) + δ ∈ Set.Icc (0:ℝ) 1) (hα : α * (γ * (s:ℝ) + δ) + a = (s:ℝ)) :
    aff α a (clamp (γ * (s:ℝ) + δ)) = s := by
  have h1 : ((clamp (γ * (s:ℝ) + δ) : unitInterval) : ℝ) = γ * (s:ℝ) + δ :=
    congrArg Subtype.val (clamp_coe_of_mem' h)
  rw [aff]
  show clamp (α * ((clamp (γ * (s:ℝ) + δ) : unitInterval) : ℝ) + a) = s
  rw [h1, hα, clamp_self]

/-- `aff α a (clamp (γ s + δ)) = σ s` when the affine data is the reversal on the range. -/
theorem aff_comp_clamp_symm {α a γ δ : ℝ} {s : unitInterval}
    (h : γ * (s:ℝ) + δ ∈ Set.Icc (0:ℝ) 1) (hα : α * (γ * (s:ℝ) + δ) + a = 1 - (s:ℝ)) :
    aff α a (clamp (γ * (s:ℝ) + δ)) = σ s := by
  have h1 : ((clamp (γ * (s:ℝ) + δ) : unitInterval) : ℝ) = γ * (s:ℝ) + δ :=
    congrArg Subtype.val (clamp_coe_of_mem' h)
  rw [aff]
  show clamp (α * ((clamp (γ * (s:ℝ) + δ) : unitInterval) : ℝ) + a) = σ s
  rw [h1, hα, clamp_one_sub]

/-- The reversal of the first coordinate, `y ↦ (σ y₀, y₁)`. -/
def diagA : C(IC 2, IC 2) :=
  ⟨fun y => pair2 (σ (y 0)) (y 1),
    continuous_pair2 (unitInterval.continuous_symm.comp (continuous_apply 0)) (continuous_apply 1)⟩

/-- The reversal of the second coordinate, `y ↦ (y₀, σ y₁)`. -/
def diagB : C(IC 2, IC 2) :=
  ⟨fun y => pair2 (y 0) (σ (y 1)),
    continuous_pair2 (continuous_apply 0) (unitInterval.continuous_symm.comp (continuous_apply 1))⟩

/-- The anti-diagonal reflection `y ↦ (σ y₁, σ y₀)`. -/
def diagD : C(IC 2, IC 2) :=
  ⟨fun y => pair2 (σ (y 1)) (σ (y 0)),
    continuous_pair2 (unitInterval.continuous_symm.comp (continuous_apply 1))
      (unitInterval.continuous_symm.comp (continuous_apply 0))⟩

/-- The quarter turn `y ↦ (y₁, σ y₀)`. -/
def diagR : C(IC 2, IC 2) :=
  ⟨fun y => pair2 (y 1) (σ (y 0)),
    continuous_pair2 (continuous_apply 1) (unitInterval.continuous_symm.comp (continuous_apply 0))⟩

theorem revMap_zero : revMap 0 = diagA := by
  ext y j; fin_cases j <;> simp [revMap, diagA, pair2]

theorem revMap_one : revMap 1 = diagB := by
  ext y j; fin_cases j <;> simp [revMap, diagB, pair2]

theorem diagD_eq : diagD = diagB.comp (diagA.comp swapMap) := by
  ext y j; fin_cases j <;> simp [diagA, diagB, diagD, swapMap, pair2]

theorem diagR_eq : diagR = diagB.comp swapMap := by
  ext y j; fin_cases j <;> simp [diagB, diagR, swapMap, pair2]

/-! ## The readings' coordinates: each reading, restricted to its net cell, is a dihedral map -/

theorem netReadMap_comp_zero : (netReadMap 0).comp (cellRead 2 3) = diagA := by
  ext y j
  fin_cases j
  · change (((aff (-8) 3 (aff (1/8) (2/8) (y 0)) : unitInterval) : ℝ)
      = ((σ (y 0) : unitInterval) : ℝ))
    exact congrArg Subtype.val (aff_comp_clamp_symm (α := -8) (a := 3) (γ := 1/8) (δ := 2/8)
      (s := y 0) ⟨by linarith [(y 0).2.1], by linarith [(y 0).2.2]⟩ (by ring))
  · change (((aff 8 (-3) (aff (1/8) (3/8) (y 1)) : unitInterval) : ℝ)
      = ((y 1 : unitInterval) : ℝ))
    exact congrArg Subtype.val (aff_comp_clamp_self (α := 8) (a := -3) (γ := 1/8) (δ := 3/8)
      (s := y 1) ⟨by linarith [(y 1).2.1], by linarith [(y 1).2.2]⟩ (by ring))

theorem netReadMap_comp_one : (netReadMap 1).comp (cellRead 3 3) = diagA := by
  ext y j
  fin_cases j
  · change (((aff (-8) 4 (aff (1/8) (3/8) (y 0)) : unitInterval) : ℝ)
      = ((σ (y 0) : unitInterval) : ℝ))
    exact congrArg Subtype.val (aff_comp_clamp_symm (α := -8) (a := 4) (γ := 1/8) (δ := 3/8)
      (s := y 0) ⟨by linarith [(y 0).2.1], by linarith [(y 0).2.2]⟩ (by ring))
  · change (((aff 8 (-3) (aff (1/8) (3/8) (y 1)) : unitInterval) : ℝ)
      = ((y 1 : unitInterval) : ℝ))
    exact congrArg Subtype.val (aff_comp_clamp_self (α := 8) (a := -3) (γ := 1/8) (δ := 3/8)
      (s := y 1) ⟨by linarith [(y 1).2.1], by linarith [(y 1).2.2]⟩ (by ring))

theorem netReadMap_comp_two : (netReadMap 2).comp (cellRead 4 3) = ContinuousMap.id (IC 2) := by
  ext y j
  fin_cases j
  · change (((aff 8 (-4) (aff (1/8) (4/8) (y 0)) : unitInterval) : ℝ)
      = ((y 0 : unitInterval) : ℝ))
    exact congrArg Subtype.val (aff_comp_clamp_self (α := 8) (a := -4) (γ := 1/8) (δ := 4/8)
      (s := y 0) ⟨by linarith [(y 0).2.1], by linarith [(y 0).2.2]⟩ (by ring))
  · change (((aff 8 (-3) (aff (1/8) (3/8) (y 1)) : unitInterval) : ℝ)
      = ((y 1 : unitInterval) : ℝ))
    exact congrArg Subtype.val (aff_comp_clamp_self (α := 8) (a := -3) (γ := 1/8) (δ := 3/8)
      (s := y 1) ⟨by linarith [(y 1).2.1], by linarith [(y 1).2.2]⟩ (by ring))

theorem netReadMap_comp_three : (netReadMap 3).comp (cellRead 5 3) = ContinuousMap.id (IC 2) := by
  ext y j
  fin_cases j
  · change (((aff 8 (-5) (aff (1/8) (5/8) (y 0)) : unitInterval) : ℝ)
      = ((y 0 : unitInterval) : ℝ))
    exact congrArg Subtype.val (aff_comp_clamp_self (α := 8) (a := -5) (γ := 1/8) (δ := 5/8)
      (s := y 0) ⟨by linarith [(y 0).2.1], by linarith [(y 0).2.2]⟩ (by ring))
  · change (((aff 8 (-3) (aff (1/8) (3/8) (y 1)) : unitInterval) : ℝ)
      = ((y 1 : unitInterval) : ℝ))
    exact congrArg Subtype.val (aff_comp_clamp_self (α := 8) (a := -3) (γ := 1/8) (δ := 3/8)
      (s := y 1) ⟨by linarith [(y 1).2.1], by linarith [(y 1).2.2]⟩ (by ring))

theorem netReadMap_comp_four : (netReadMap 4).comp (cellRead 3 2) = diagD := by
  ext y j
  fin_cases j
  · change (((aff (-8) 3 (aff (1/8) (2/8) (y 1)) : unitInterval) : ℝ)
      = ((σ (y 1) : unitInterval) : ℝ))
    exact congrArg Subtype.val (aff_comp_clamp_symm (α := -8) (a := 3) (γ := 1/8) (δ := 2/8)
      (s := y 1) ⟨by linarith [(y 1).2.1], by linarith [(y 1).2.2]⟩ (by ring))
  · change (((aff (-8) 4 (aff (1/8) (3/8) (y 0)) : unitInterval) : ℝ)
      = ((σ (y 0) : unitInterval) : ℝ))
    exact congrArg Subtype.val (aff_comp_clamp_symm (α := -8) (a := 4) (γ := 1/8) (δ := 3/8)
      (s := y 0) ⟨by linarith [(y 0).2.1], by linarith [(y 0).2.2]⟩ (by ring))

theorem netReadMap_comp_five : (netReadMap 5).comp (cellRead 3 4) = diagR := by
  ext y j
  fin_cases j
  · change (((aff 8 (-4) (aff (1/8) (4/8) (y 1)) : unitInterval) : ℝ)
      = ((y 1 : unitInterval) : ℝ))
    exact congrArg Subtype.val (aff_comp_clamp_self (α := 8) (a := -4) (γ := 1/8) (δ := 4/8)
      (s := y 1) ⟨by linarith [(y 1).2.1], by linarith [(y 1).2.2]⟩ (by ring))
  · change (((aff (-8) 4 (aff (1/8) (3/8) (y 0)) : unitInterval) : ℝ)
      = ((σ (y 0) : unitInterval) : ℝ))
    exact congrArg Subtype.val (aff_comp_clamp_symm (α := -8) (a := 4) (γ := 1/8) (δ := 3/8)
      (s := y 0) ⟨by linarith [(y 0).2.1], by linarith [(y 0).2.2]⟩ (by ring))

/-! ## The class of a cube reparametrised by a coordinate reversal -/

/-- `revMap i` preserves the boundary of the square. -/
theorem revMap_mem_boundary (i : Fin 2) {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) :
    revMap i y ∈ Cube.boundary (Fin 2) := by
  obtain ⟨c, hc⟩ := hy
  by_cases h : c = i
  · refine ⟨i, ?_⟩
    have h1 : revMap i y i = σ (y i) := by simp [revMap]
    rw [h] at hc
    rw [h1]
    rcases hc with hc | hc
    · rw [hc, unitInterval.symm_zero]; exact Or.inr rfl
    · rw [hc, unitInterval.symm_one]; exact Or.inl rfl
  · refine ⟨c, ?_⟩
    have h1 : revMap i y c = y c := by simp [revMap, h]
    rw [h1]; exact hc

/-- `compGenLoop` along `revMap i` is `GenLoop.symmAt i`. -/
theorem compGenLoop_revMap_eq {X : Type} [TopologicalSpace X] {x₀ : X} (i : Fin 2)
    (c : GenLoop (Fin 2) X x₀) (h : ∀ y ∈ Cube.boundary (Fin 2), c.1 (revMap i y) = x₀) :
    (compGenLoop (c := c) (φ := revMap i) h : GenLoop (Fin 2) X x₀) = GenLoop.symmAt i c := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  rfl

/-- Two `compGenLoop`s along equal maps agree. -/
theorem compGenLoop_congr {X : Type} [TopologicalSpace X] {x₀ : X} {c : GenLoop (Fin 2) X x₀}
    {φ ψ : C(IC 2, IC 2)} (h : φ = ψ)
    (hφ : ∀ y ∈ Cube.boundary (Fin 2), c.1 (φ y) = x₀)
    (hψ : ∀ y ∈ Cube.boundary (Fin 2), c.1 (ψ y) = x₀) :
    (compGenLoop (c := c) (φ := φ) hφ : GenLoop (Fin 2) X x₀)
      = compGenLoop (c := c) (φ := ψ) hψ := by
  subst h; rfl

/-- **A based cube reparametrised by a coordinate reversal has inverse class.** -/
theorem cl_comp_revMap {X : Type} [TopologicalSpace X] {x₀ : X} (i : Fin 2)
    (c : GenLoop (Fin 2) X x₀) (h : ∀ y ∈ Cube.boundary (Fin 2), c.1 (revMap i y) = x₀) :
    Work.Stems.Hur2b.cl x₀ (compGenLoop (c := c) (φ := revMap i) h) = (Work.Stems.Hur2b.cl x₀ c)⁻¹ := by
  rw [compGenLoop_revMap_eq i c h]
  exact cl_symmAt i c

/-- **A based cube reparametrised by `diagA = (σ y₀, y₁)` has inverse class.** -/
theorem cl_comp_diagA {X : Type} [TopologicalSpace X] {x₀ : X} (c : GenLoop (Fin 2) X x₀)
    (h : ∀ y ∈ Cube.boundary (Fin 2), c.1 (diagA y) = x₀) :
    Work.Stems.Hur2b.cl x₀ (compGenLoop (c := c) (φ := diagA) h) = (Work.Stems.Hur2b.cl x₀ c)⁻¹ := by
  have h' : ∀ y ∈ Cube.boundary (Fin 2), c.1 (revMap 0 y) = x₀ := by
    intro y hy; rw [revMap_zero]; exact h y hy
  rw [show (compGenLoop (c := c) (φ := diagA) h : GenLoop (Fin 2) X x₀)
      = compGenLoop (c := c) (φ := revMap 0) h' from (compGenLoop_congr revMap_zero h' h).symm]
  exact cl_comp_revMap 0 c h'

/-- **A based cube reparametrised by `diagB = (y₀, σ y₁)` has inverse class.** -/
theorem cl_comp_diagB {X : Type} [TopologicalSpace X] {x₀ : X} (c : GenLoop (Fin 2) X x₀)
    (h : ∀ y ∈ Cube.boundary (Fin 2), c.1 (diagB y) = x₀) :
    Work.Stems.Hur2b.cl x₀ (compGenLoop (c := c) (φ := diagB) h) = (Work.Stems.Hur2b.cl x₀ c)⁻¹ := by
  have h' : ∀ y ∈ Cube.boundary (Fin 2), c.1 (revMap 1 y) = x₀ := by
    intro y hy; rw [revMap_one]; exact h y hy
  rw [show (compGenLoop (c := c) (φ := diagB) h : GenLoop (Fin 2) X x₀)
      = compGenLoop (c := c) (φ := revMap 1) h' from (compGenLoop_congr revMap_one h' h).symm]
  exact cl_comp_revMap 1 c h'

/-- Composing two `compGenLoop`s (both sides are `c ∘ φ ∘ ψ`). -/
theorem compGenLoop_comp {X : Type} [TopologicalSpace X] {x₀ : X} (c : GenLoop (Fin 2) X x₀)
    (φ ψ : C(IC 2, IC 2)) (hφ : ∀ y ∈ Cube.boundary (Fin 2), c.1 (φ y) = x₀)
    (hψ : ∀ y ∈ Cube.boundary (Fin 2), (compGenLoop (c := c) (φ := φ) hφ).1 (ψ y) = x₀)
    (h : ∀ y ∈ Cube.boundary (Fin 2), c.1 ((φ.comp ψ) y) = x₀) :
    (compGenLoop (c := c) (φ := φ.comp ψ) h : GenLoop (Fin 2) X x₀)
      = compGenLoop (c := compGenLoop (c := c) (φ := φ) hφ) (φ := ψ) hψ := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  rfl

-- (`cl_comp_id`, the identity case, is the trivial `rfl` and is still to be recorded; see PINCH_PLAN.md.)
/-- `diagB y = diagR (swapMap y)`. -/
theorem diagB_eq_diagR_swap (y : IC 2) : diagB y = diagR (swapMap y) := by
  funext j; fin_cases j <;> simp [diagB, diagR, swapMap, pair2]

/-- `diagR y = diagB (swapMap y)`. -/
theorem diagR_eq_diagB_swap (y : IC 2) : diagR y = diagB (swapMap y) := by
  funext j; fin_cases j <;> simp [diagB, diagR, swapMap, pair2]

/-- **A based cube reparametrised by `diagR = (y₁, σ y₀)` (the quarter turn) has the same class.** -/
theorem cl_comp_diagR {X : Type} [TopologicalSpace X] {x₀ : X} (c : GenLoop (Fin 2) X x₀)
    (h : ∀ y ∈ Cube.boundary (Fin 2), c.1 (diagR y) = x₀) :
    Work.Stems.Hur2b.cl x₀ (compGenLoop (c := c) (φ := diagR) h)
      = Work.Stems.Hur2b.cl x₀ c := by
  have hB : ∀ y ∈ Cube.boundary (Fin 2), c.1 (revMap 1 y) = x₀ := by
    intro y hy
    rw [revMap_one, diagB_eq_diagR_swap]
    exact h _ (swapMap_boundary hy)
  have h1 : Work.Stems.Hur2b.cl x₀ (compGenLoop (c := c) (φ := revMap 1) hB) = (Work.Stems.Hur2b.cl x₀ c)⁻¹ :=
    cl_comp_revMap 1 c hB
  have hlink : (compGenLoop (c := c) (φ := diagR) h : GenLoop (Fin 2) X x₀)
      = compGenLoop (c := compGenLoop (c := c) (φ := revMap 1) hB) (φ := swapMap)
          (fun y hy => c.2 _ (revMap_mem_boundary 1 (swapMap_boundary hy))) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro y
    show c.1 (diagR y) = c.1 (revMap 1 (swapMap y))
    rw [diagR_eq_diagB_swap y, revMap_one]
  rw [hlink, cl_comp_swapMap, h1, inv_inv]


/-! ## The identity and anti-diagonal cases, and composition bookkeeping -/

/-- The `(-1)`-reparametrisations preserve the boundary of the square. -/
theorem diagA_mem_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) :
    diagA y ∈ Cube.boundary (Fin 2) := by
  have h := revMap_mem_boundary 0 hy
  rwa [revMap_zero] at h

theorem diagB_mem_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) :
    diagB y ∈ Cube.boundary (Fin 2) := by
  have h := revMap_mem_boundary 1 hy
  rwa [revMap_one] at h

/-- The anti-diagonal reflection preserves the boundary of the square. -/
theorem diagD_mem_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) :
    diagD y ∈ Cube.boundary (Fin 2) := by
  rw [diagD_eq]
  simpa only [ContinuousMap.comp_apply] using
    diagB_mem_boundary (diagA_mem_boundary (swapMap_boundary hy))

/-- `diagD y = diagB (diagA (swapMap y))`. -/
theorem diagD_apply (y : IC 2) : diagD y = diagB (diagA (swapMap y)) := by
  rw [diagD_eq]; rfl

/-- Two `compGenLoop`s along the same map (with different boundary proofs) are equal. -/
theorem compGenLoop_hirrel {X : Type} [TopologicalSpace X] {x₀ : X} {c : GenLoop (Fin 2) X x₀}
    {φ : C(IC 2, IC 2)} (h h' : ∀ y ∈ Cube.boundary (Fin 2), c.1 (φ y) = x₀) :
    (compGenLoop (c := c) (φ := φ) h : GenLoop (Fin 2) X x₀)
      = compGenLoop (c := c) (φ := φ) h' :=
  GenLoop.ext _ _ fun _ => rfl

/-- **A based cube reparametrised by the identity has the same class.** -/
theorem cl_comp_id {X : Type} [TopologicalSpace X] {x₀ : X} (c : GenLoop (Fin 2) X x₀)
    (h : ∀ y ∈ Cube.boundary (Fin 2), c.1 ((ContinuousMap.id (IC 2)) y) = x₀) :
    Work.Stems.Hur2b.cl x₀ (compGenLoop (c := c) (φ := ContinuousMap.id (IC 2)) h) =
      Work.Stems.Hur2b.cl x₀ c := by
  rw [show (compGenLoop (c := c) (φ := ContinuousMap.id (IC 2)) h : GenLoop (Fin 2) X x₀) = c
      from GenLoop.ext _ _ fun _ => rfl]

/-- **A based cube reparametrised by the anti-diagonal reflection has inverse class.** -/
theorem cl_comp_diagD {X : Type} [TopologicalSpace X] {x₀ : X} (c : GenLoop (Fin 2) X x₀)
    (h : ∀ y ∈ Cube.boundary (Fin 2), c.1 (diagD y) = x₀) :
    Work.Stems.Hur2b.cl x₀ (compGenLoop (c := c) (φ := diagD) h)
      = (Work.Stems.Hur2b.cl x₀ c)⁻¹ := by
  have hD : ∀ y ∈ Cube.boundary (Fin 2), c.1 (diagD y) = x₀ :=
    fun y hy => c.2 _ (diagD_mem_boundary hy)
  have hB : ∀ y ∈ Cube.boundary (Fin 2), c.1 (diagB y) = x₀ :=
    fun y hy => c.2 _ (diagB_mem_boundary hy)
  rw [show (compGenLoop (c := c) (φ := diagD) h : GenLoop (Fin 2) X x₀)
      = compGenLoop (c := c) (φ := diagD) hD from compGenLoop_hirrel h hD]
  let Q1 : GenLoop (Fin 2) X x₀ := compGenLoop (c := c) (φ := diagB) hB
  let hA1 : ∀ y ∈ Cube.boundary (Fin 2), Q1.1 (diagA y) = x₀ :=
    fun y hy => Q1.2 _ (diagA_mem_boundary hy)
  let Q2 : GenLoop (Fin 2) X x₀ := compGenLoop (c := Q1) (φ := diagA) hA1
  let hSw : ∀ y ∈ Cube.boundary (Fin 2), Q2.1 (swapMap y) = x₀ :=
    fun y hy => Q2.2 _ (swapMap_boundary hy)
  have hφc : ∀ y ∈ Cube.boundary (Fin 2), c.1 ((diagB.comp (diagA.comp swapMap)) y) = x₀ :=
    fun y hy => by rw [← diagD_eq]; exact hD y hy
  have hψ1 : ∀ y ∈ Cube.boundary (Fin 2), Q1.1 ((diagA.comp swapMap) y) = x₀ := hφc
  have hlink : (compGenLoop (c := c) (φ := diagD) hD : GenLoop (Fin 2) X x₀)
      = compGenLoop (c := Q2) (φ := swapMap) hSw := by
    rw [show (compGenLoop (c := c) (φ := diagD) hD : GenLoop (Fin 2) X x₀)
        = compGenLoop (c := c) (φ := diagB.comp (diagA.comp swapMap)) hφc
        from compGenLoop_congr diagD_eq hD hφc]
    rw [show (compGenLoop (c := c) (φ := diagB.comp (diagA.comp swapMap)) hφc : GenLoop (Fin 2) X x₀)
        = compGenLoop (c := Q1) (φ := diagA.comp swapMap) hψ1
        from compGenLoop_comp c diagB (diagA.comp swapMap) hB hψ1 hφc]
    exact compGenLoop_comp Q1 diagA swapMap hA1 hSw hψ1
  rw [hlink]
  rw [show (compGenLoop (c := Q2) (φ := swapMap) hSw : GenLoop (Fin 2) X x₀)
      = compGenLoop (c := Q2) (φ := swapMap) (fun y hy => Q2.2 _ (swapMap_boundary hy))
      from compGenLoop_hirrel hSw _]
  rw [cl_comp_swapMap Q2]
  have h2 : Work.Stems.Hur2b.cl x₀ Q2 = (Work.Stems.Hur2b.cl x₀ Q1)⁻¹ :=
    cl_comp_diagA Q1 hA1
  have h1 : Work.Stems.Hur2b.cl x₀ Q1 = (Work.Stems.Hur2b.cl x₀ c)⁻¹ :=
    cl_comp_diagB c hB
  rw [h2, h1, inv_inv]


/-! ## The readings of points outside the open net cells

The whole computation of the six content cells rests on the following two facts:

* the `k`-th reading sends every point outside the *open* `k`-th net cell into the boundary `∂I²`
  (so that a based cube read through it is automatically based on the cell boundaries);
* every point of a closed grid cell `(i,j) ≠ (i₀,j₀)` lies outside the open cell `(i₀,j₀)`.
-/

theorem clamp_zero_of_nonpos' {r : ℝ} (h : r ≤ 0) : clamp r = 0 :=
  Set.projIcc_of_le_left zero_le_one h

theorem clamp_one_of_one_le' {r : ℝ} (h : 1 ≤ r) : clamp r = 1 :=
  Set.projIcc_of_right_le zero_le_one h

theorem clamp_coe_mem {r : ℝ} (h : r ∈ Set.Icc (0:ℝ) 1) :
    ((clamp r : unitInterval) : ℝ) = r := by rw [clamp_of_mem h]

theorem readMap_coord0 (α a β b : ℝ) (z : IC 2) :
    (readMap α a β b z) 0 = clamp (α * (z 0 : ℝ) + a) := by simp [readMap, aff, pair2]

theorem readMap_coord1 (α a β b : ℝ) (z : IC 2) :
    (readMap α a β b z) 1 = clamp (β * (z 1 : ℝ) + b) := by simp [readMap, aff, pair2]

theorem readSwap_coord0 (α a β b : ℝ) (z : IC 2) :
    (readSwap α a β b z) 0 = clamp (β * (z 1 : ℝ) + b) := by simp [readSwap, aff, pair2]

theorem readSwap_coord1 (α a β b : ℝ) (z : IC 2) :
    (readSwap α a β b z) 1 = clamp (α * (z 0 : ℝ) + a) := by simp [readSwap, aff, pair2]

/-- A point outside the open grid cell `(i,j)` is outside in one of the four coordinate ways. -/
theorem notMem_openCube {z : IC 2} {i j : Fin 8} (h : z ∉ openCube i j) :
    (z 0 : ℝ) ≤ (i : ℝ)/8 ∨ ((i : ℝ)+1)/8 ≤ (z 0 : ℝ) ∨
    (z 1 : ℝ) ≤ (j : ℝ)/8 ∨ ((j : ℝ)+1)/8 ≤ (z 1 : ℝ) := by
  have h1 : ¬ ((i : ℝ)/8 < (z 0 : ℝ) ∧ (z 0 : ℝ) < ((i : ℝ)+1)/8 ∧
      (j : ℝ)/8 < (z 1 : ℝ) ∧ (z 1 : ℝ) < ((j : ℝ)+1)/8) := by
    intro hc
    exact h (by simpa only [openCube, Set.mem_ofPred_eq] using hc)
  rcases not_and_or.mp h1 with h2 | h2
  · exact Or.inl (not_lt.mp h2)
  rcases not_and_or.mp h2 with h3 | h3
  · exact Or.inr (Or.inl (not_lt.mp h3))
  rcases not_and_or.mp h3 with h4 | h4
  · exact Or.inr (Or.inr (Or.inl (not_lt.mp h4)))
  · exact Or.inr (Or.inr (Or.inr (not_lt.mp h4)))

/-- **The `k`-th reading sends points outside the open `k`-th net cell to `∂I²`.** -/
theorem netReadMap_mem_boundary (k : Fin 6) {z : IC 2}
    (hz : z ∉ openCube (netCellIdx k).1 (netCellIdx k).2) :
    netReadMap k z ∈ Cube.boundary (Fin 2) := by
  fin_cases k
  · rcases notMem_openCube (show z ∉ openCube (2:Fin 8) (3:Fin 8) from hz) with h | h | h | h
    · refine ⟨0, Or.inr ?_⟩
      change (readMap (-8) 3 8 (-3) z) 0 = 1
      rw [readMap_coord0]; exact clamp_one_of_one_le' (by norm_num at h; linarith)
    · refine ⟨0, Or.inl ?_⟩
      change (readMap (-8) 3 8 (-3) z) 0 = 0
      rw [readMap_coord0]; exact clamp_zero_of_nonpos' (by norm_num at h; linarith)
    · refine ⟨1, Or.inl ?_⟩
      change (readMap (-8) 3 8 (-3) z) 1 = 0
      rw [readMap_coord1]; exact clamp_zero_of_nonpos' (by norm_num at h; linarith)
    · refine ⟨1, Or.inr ?_⟩
      change (readMap (-8) 3 8 (-3) z) 1 = 1
      rw [readMap_coord1]; exact clamp_one_of_one_le' (by norm_num at h; linarith)
  · rcases notMem_openCube (show z ∉ openCube (3:Fin 8) (3:Fin 8) from hz) with h | h | h | h
    · refine ⟨0, Or.inr ?_⟩
      change (readMap (-8) 4 8 (-3) z) 0 = 1
      rw [readMap_coord0]; exact clamp_one_of_one_le' (by norm_num at h; linarith)
    · refine ⟨0, Or.inl ?_⟩
      change (readMap (-8) 4 8 (-3) z) 0 = 0
      rw [readMap_coord0]; exact clamp_zero_of_nonpos' (by norm_num at h; linarith)
    · refine ⟨1, Or.inl ?_⟩
      change (readMap (-8) 4 8 (-3) z) 1 = 0
      rw [readMap_coord1]; exact clamp_zero_of_nonpos' (by norm_num at h; linarith)
    · refine ⟨1, Or.inr ?_⟩
      change (readMap (-8) 4 8 (-3) z) 1 = 1
      rw [readMap_coord1]; exact clamp_one_of_one_le' (by norm_num at h; linarith)
  · rcases notMem_openCube (show z ∉ openCube (4:Fin 8) (3:Fin 8) from hz) with h | h | h | h
    · refine ⟨0, Or.inl ?_⟩
      change (readMap 8 (-4) 8 (-3) z) 0 = 0
      rw [readMap_coord0]; exact clamp_zero_of_nonpos' (by norm_num at h; linarith)
    · refine ⟨0, Or.inr ?_⟩
      change (readMap 8 (-4) 8 (-3) z) 0 = 1
      rw [readMap_coord0]; exact clamp_one_of_one_le' (by norm_num at h; linarith)
    · refine ⟨1, Or.inl ?_⟩
      change (readMap 8 (-4) 8 (-3) z) 1 = 0
      rw [readMap_coord1]; exact clamp_zero_of_nonpos' (by norm_num at h; linarith)
    · refine ⟨1, Or.inr ?_⟩
      change (readMap 8 (-4) 8 (-3) z) 1 = 1
      rw [readMap_coord1]; exact clamp_one_of_one_le' (by norm_num at h; linarith)
  · rcases notMem_openCube (show z ∉ openCube (5:Fin 8) (3:Fin 8) from hz) with h | h | h | h
    · refine ⟨0, Or.inl ?_⟩
      change (readMap 8 (-5) 8 (-3) z) 0 = 0
      rw [readMap_coord0]; exact clamp_zero_of_nonpos' (by norm_num at h; linarith)
    · refine ⟨0, Or.inr ?_⟩
      change (readMap 8 (-5) 8 (-3) z) 0 = 1
      rw [readMap_coord0]; exact clamp_one_of_one_le' (by norm_num at h; linarith)
    · refine ⟨1, Or.inl ?_⟩
      change (readMap 8 (-5) 8 (-3) z) 1 = 0
      rw [readMap_coord1]; exact clamp_zero_of_nonpos' (by norm_num at h; linarith)
    · refine ⟨1, Or.inr ?_⟩
      change (readMap 8 (-5) 8 (-3) z) 1 = 1
      rw [readMap_coord1]; exact clamp_one_of_one_le' (by norm_num at h; linarith)
  · rcases notMem_openCube (show z ∉ openCube (3:Fin 8) (2:Fin 8) from hz) with h | h | h | h
    · refine ⟨1, Or.inr ?_⟩
      change (readSwap (-8) 4 (-8) 3 z) 1 = 1
      rw [readSwap_coord1]; exact clamp_one_of_one_le' (by norm_num at h; linarith)
    · refine ⟨1, Or.inl ?_⟩
      change (readSwap (-8) 4 (-8) 3 z) 1 = 0
      rw [readSwap_coord1]; exact clamp_zero_of_nonpos' (by norm_num at h; linarith)
    · refine ⟨0, Or.inr ?_⟩
      change (readSwap (-8) 4 (-8) 3 z) 0 = 1
      rw [readSwap_coord0]; exact clamp_one_of_one_le' (by norm_num at h; linarith)
    · refine ⟨0, Or.inl ?_⟩
      change (readSwap (-8) 4 (-8) 3 z) 0 = 0
      rw [readSwap_coord0]; exact clamp_zero_of_nonpos' (by norm_num at h; linarith)
  · rcases notMem_openCube (show z ∉ openCube (3:Fin 8) (4:Fin 8) from hz) with h | h | h | h
    · refine ⟨1, Or.inr ?_⟩
      change (readSwap (-8) 4 8 (-4) z) 1 = 1
      rw [readSwap_coord1]; exact clamp_one_of_one_le' (by norm_num at h; linarith)
    · refine ⟨1, Or.inl ?_⟩
      change (readSwap (-8) 4 8 (-4) z) 1 = 0
      rw [readSwap_coord1]; exact clamp_zero_of_nonpos' (by norm_num at h; linarith)
    · refine ⟨0, Or.inl ?_⟩
      change (readSwap (-8) 4 8 (-4) z) 0 = 0
      rw [readSwap_coord0]; exact clamp_zero_of_nonpos' (by norm_num at h; linarith)
    · refine ⟨0, Or.inr ?_⟩
      change (readSwap (-8) 4 8 (-4) z) 0 = 1
      rw [readSwap_coord0]; exact clamp_one_of_one_le' (by norm_num at h; linarith)

/-- The coordinates of a cell reading, in the ambient reals. -/
theorem cellRead_coe_zero (i j : Fin 8) (y : IC 2) :
    (((cellRead i j y) 0 : unitInterval) : ℝ) = ((y 0 : ℝ) + (i : ℝ))/8 := by
  have hmem : (1:ℝ)/8 * (y 0 : ℝ) + ((i:ℕ):ℝ)/8 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [(y 0).2.1, (show (0:ℝ) ≤ ((i:ℕ):ℝ) from Nat.cast_nonneg _)],
     by
      have h2 : (i:ℕ) ≤ 7 := by have := i.isLt; omega
      have h3 : ((i:ℕ):ℝ) ≤ 7 := by exact_mod_cast h2
      linarith [(y 0).2.2]⟩
  rw [show ((cellRead i j y) 0 : unitInterval) = clamp ((1:ℝ)/8 * (y 0 : ℝ) + ((i:ℕ):ℝ)/8)
      from readMap_coord0 (1/8) (((i:ℕ):ℝ)/8) (1/8) (((j:ℕ):ℝ)/8) y,
    clamp_coe_mem (r := (1:ℝ)/8 * (y 0 : ℝ) + ((i:ℕ):ℝ)/8) hmem]
  push_cast
  ring

theorem cellRead_coe_one (i j : Fin 8) (y : IC 2) :
    (((cellRead i j y) 1 : unitInterval) : ℝ) = ((y 1 : ℝ) + (j : ℝ))/8 := by
  have hmem : (1:ℝ)/8 * (y 1 : ℝ) + ((j:ℕ):ℝ)/8 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [(y 1).2.1, (show (0:ℝ) ≤ ((j:ℕ):ℝ) from Nat.cast_nonneg _)],
     by
      have h2 : (j:ℕ) ≤ 7 := by have := j.isLt; omega
      have h3 : ((j:ℕ):ℝ) ≤ 7 := by exact_mod_cast h2
      linarith [(y 1).2.2]⟩
  rw [show ((cellRead i j y) 1 : unitInterval) = clamp ((1:ℝ)/8 * (y 1 : ℝ) + ((j:ℕ):ℝ)/8)
      from readMap_coord1 (1/8) (((i:ℕ):ℝ)/8) (1/8) (((j:ℕ):ℝ)/8) y,
    clamp_coe_mem (r := (1:ℝ)/8 * (y 1 : ℝ) + ((j:ℕ):ℝ)/8) hmem]
  push_cast
  ring

/-- A point of the cell `(i,j)` lies outside the open cell `(i₀,j₀)` unless `(i,j) = (i₀,j₀)`. -/
theorem cellRead_notMem_openCube {i j i₀ j₀ : Fin 8} (h : (i, j) ≠ (i₀, j₀)) (y : IC 2) :
    cellRead i j y ∉ openCube i₀ j₀ := by
  intro hc
  have hc' : (i₀ : ℝ)/8 < (((cellRead i j y) 0 : unitInterval) : ℝ) ∧
      (((cellRead i j y) 0 : unitInterval) : ℝ) < ((i₀ : ℝ)+1)/8 ∧
      (j₀ : ℝ)/8 < (((cellRead i j y) 1 : unitInterval) : ℝ) ∧
      (((cellRead i j y) 1 : unitInterval) : ℝ) < ((j₀ : ℝ)+1)/8 := by
    simpa only [openCube, Set.mem_ofPred_eq] using hc
  rw [cellRead_coe_zero, cellRead_coe_one] at hc'
  obtain ⟨ha, hb, hc1, hd⟩ := hc'
  have hy0 : (0:ℝ) ≤ (y 0 : ℝ) := (y 0).2.1
  have hy0' : (y 0 : ℝ) ≤ 1 := (y 0).2.2
  have hy1 : (0:ℝ) ≤ (y 1 : ℝ) := (y 1).2.1
  have hy1' : (y 1 : ℝ) ≤ 1 := (y 1).2.2
  have hi : i = i₀ := by
    have h1 : ((i:ℕ):ℝ) < (((i₀:ℕ)+1 : ℕ) : ℝ) := by push_cast; linarith
    have h2 : ((i₀:ℕ):ℝ) < (((i:ℕ)+1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_lt.mp h1
    have := Nat.cast_lt.mp h2
    exact Fin.ext (by omega)
  have hj : j = j₀ := by
    have h1 : ((j:ℕ):ℝ) < (((j₀:ℕ)+1 : ℕ) : ℝ) := by push_cast; linarith
    have h2 : ((j₀:ℕ):ℝ) < (((j:ℕ)+1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_lt.mp h1
    have := Nat.cast_lt.mp h2
    exact Fin.ext (by omega)
  exact h (by rw [hi, hj])

/-! ## The class of a cube read through a net reading -/

/-- A point of a vertical grid line lies outside every open grid cell. -/
theorem gLine_notMem_openCube (i₀ j₀ : Fin 8) (m : Fin 9) (s : unitInterval) :
    pair2 (gLine m) s ∉ openCube i₀ j₀ := by
  intro hc
  have hc' : (i₀:ℝ)/8 < (m:ℝ)/8 ∧ (m:ℝ)/8 < ((i₀:ℝ)+1)/8 ∧
      (j₀:ℝ)/8 < (s:ℝ) ∧ (s:ℝ) < ((j₀:ℝ)+1)/8 := by
    have hcc : (i₀:ℝ)/8 < ((pair2 (gLine m) s) 0 : ℝ) ∧
        ((pair2 (gLine m) s) 0 : ℝ) < ((i₀:ℝ)+1)/8 ∧
        (j₀:ℝ)/8 < ((pair2 (gLine m) s) 1 : ℝ) ∧
        ((pair2 (gLine m) s) 1 : ℝ) < ((j₀:ℝ)+1)/8 := by
      simpa only [openCube, Set.mem_ofPred_eq] using hc
    simpa only [pair2_zero, pair2_one, gLine_coe] using hcc
  obtain ⟨ha, hb, _, _⟩ := hc'
  by_cases h : (m:ℕ) ≤ (i₀:ℕ)
  · have hm : (m:ℝ) ≤ (i₀:ℝ) := by exact_mod_cast h
    linarith
  · have h0 : (i₀:ℕ) < (m:ℕ) := not_le.mp h
    have hm : ((i₀:ℝ) + 1) ≤ (m:ℝ) := by
      have h1 : (((i₀:ℕ) + 1 : ℕ) : ℝ) ≤ ((m:ℕ):ℝ) := by exact_mod_cast h0
      push_cast at h1
      exact h1
    linarith

/-- A point of a horizontal grid line lies outside every open grid cell. -/
theorem pair2_gLine_notMem_openCube (i₀ j₀ : Fin 8) (m : Fin 9) (s : unitInterval) :
    pair2 s (gLine m) ∉ openCube i₀ j₀ := by
  intro hc
  have hc' : (i₀:ℝ)/8 < (s:ℝ) ∧ (s:ℝ) < ((i₀:ℝ)+1)/8 ∧
      (j₀:ℝ)/8 < (m:ℝ)/8 ∧ (m:ℝ)/8 < ((j₀:ℝ)+1)/8 := by
    have hcc : (i₀:ℝ)/8 < ((pair2 s (gLine m)) 0 : ℝ) ∧
        ((pair2 s (gLine m)) 0 : ℝ) < ((i₀:ℝ)+1)/8 ∧
        (j₀:ℝ)/8 < ((pair2 s (gLine m)) 1 : ℝ) ∧
        ((pair2 s (gLine m)) 1 : ℝ) < ((j₀:ℝ)+1)/8 := by
      simpa only [openCube, Set.mem_ofPred_eq] using hc
    simpa only [pair2_zero, pair2_one, gLine_coe] using hcc
  obtain ⟨_, _, ha, hb⟩ := hc'
  by_cases h : (m:ℕ) ≤ (j₀:ℕ)
  · have hm : (m:ℝ) ≤ (j₀:ℝ) := by exact_mod_cast h
    linarith
  · have h0 : (j₀:ℕ) < (m:ℕ) := not_le.mp h
    have hm : ((j₀:ℝ) + 1) ≤ (m:ℝ) := by
      have h1 : (((j₀:ℕ) + 1 : ℕ) : ℝ) ≤ ((m:ℕ):ℝ) := by exact_mod_cast h0
      push_cast at h1
      exact h1
    linarith

/-- The class of the constant cube is `1`. -/
theorem cl_const {X : Type} [TopologicalSpace X] {x₀ : X} :
    Work.Stems.Hur2b.cl x₀ (GenLoop.const : GenLoop (Fin 2) X x₀) = 1 :=
  (HomotopyGroup.one_def (N := Fin 2) (X := X) (x := x₀)).symm

/-- The dihedral map carried by the `k`-th net cell. -/
def netDiag : Fin 6 → C(IC 2, IC 2)
  | 0 => diagA
  | 1 => diagA
  | 2 => ContinuousMap.id (IC 2)
  | 3 => ContinuousMap.id (IC 2)
  | 4 => diagD
  | 5 => diagR

/-- The readings compose with the cell inclusions to the dihedral maps. -/
theorem netReadMap_comp_netDiag (k : Fin 6) :
    (netReadMap k).comp (cellRead (netCellIdx k).1 (netCellIdx k).2) = netDiag k := by
  fin_cases k
  · exact netReadMap_comp_zero
  · exact netReadMap_comp_one
  · exact netReadMap_comp_two
  · exact netReadMap_comp_three
  · exact netReadMap_comp_four
  · exact netReadMap_comp_five

/-- The quarter turn preserves the boundary of the square. -/
theorem diagR_mem_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) :
    diagR y ∈ Cube.boundary (Fin 2) := by
  rw [diagR_eq]
  simpa only [ContinuousMap.comp_apply] using diagB_mem_boundary (swapMap_boundary hy)

/-- Each dihedral map of a net cell preserves the boundary of the square. -/
theorem netDiag_mem_boundary (k : Fin 6) {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) :
    netDiag k y ∈ Cube.boundary (Fin 2) := by
  fin_cases k
  · exact diagA_mem_boundary hy
  · exact diagA_mem_boundary hy
  · exact hy
  · exact hy
  · exact diagD_mem_boundary hy
  · exact diagR_mem_boundary hy

/-- The class of a cube read through a net cell's dihedral map. -/
theorem cl_comp_netDiag {X : Type} [TopologicalSpace X] {x₀ : X} (k : Fin 6)
    (c : GenLoop (Fin 2) X x₀)
    (h : ∀ y ∈ Cube.boundary (Fin 2), c.1 (netDiag k y) = x₀) :
    Work.Stems.Hur2b.cl x₀ (compGenLoop (c := c) (φ := netDiag k) h)
      = (Work.Stems.Hur2b.cl x₀ c) ^ (netSign k) := by
  fin_cases k
  · simp only [netDiag, netSign] at h ⊢
    rw [cl_comp_diagA]; exact (zpow_neg_one _).symm
  · simp only [netDiag, netSign] at h ⊢
    rw [cl_comp_diagA]; exact (zpow_neg_one _).symm
  · simp only [netDiag, netSign] at h ⊢
    rw [cl_comp_id]; exact (zpow_one _).symm
  · simp only [netDiag, netSign] at h ⊢
    rw [cl_comp_id]; exact (zpow_one _).symm
  · simp only [netDiag, netSign] at h ⊢
    rw [cl_comp_diagD]; exact (zpow_neg_one _).symm
  · simp only [netDiag, netSign] at h ⊢
    rw [cl_comp_diagR]; exact (zpow_one _).symm

/-- **The class of a based cube read through the `k`-th net reading.** -/
theorem netRead_class {X : Type} [TopologicalSpace X] {x₀ : X} (k : Fin 6)
    (c : GenLoop (Fin 2) X x₀)
    (h : ∀ y ∈ Cube.boundary (Fin 2), c.1 (netReadMap k y) = x₀) :
    Work.Stems.Hur2b.cl x₀ (compGenLoop (c := c) (φ := netReadMap k) h)
      = (Work.Stems.Hur2b.cl x₀ c) ^ (netSign k) := by
  let p : GenLoop (Fin 2) X x₀ := compGenLoop (c := c) (φ := netReadMap k) h
  have hV : ∀ (m : Fin 9) (s : unitInterval), p.1 (pair2 (gLine m) s) = x₀ := by
    intro m s
    change c.1 ((netReadMap k) (pair2 (gLine m) s)) = x₀
    exact c.2 _ (netReadMap_mem_boundary k
      (gLine_notMem_openCube (netCellIdx k).1 (netCellIdx k).2 m s))
  have hH : ∀ (m : Fin 9) (s : unitInterval), p.1 (pair2 s (gLine m)) = x₀ := by
    intro m s
    change c.1 ((netReadMap k) (pair2 s (gLine m))) = x₀
    exact c.2 _ (netReadMap_mem_boundary k
      (pair2_gLine_notMem_openCube (netCellIdx k).1 (netCellIdx k).2 m s))
  have hbound : ∀ (c' : Fin 8 × Fin 8) (y : IC 2), y ∈ Cube.boundary (Fin 2) →
      p.1 (cellRead c'.1 c'.2 y) = x₀ := fun c' => cellRead_boundary p hV hH c'.1 c'.2
  change Work.Stems.Hur2b.cl x₀ p = (Work.Stems.Hur2b.cl x₀ c) ^ (netSign k)
  rw [cl_grid8 p hbound]
  have hsingle : (∏ c' : Fin 8 × Fin 8,
      Work.Stems.Hur2b.cl x₀ (Work.Stems.Hur2b.cellCube p c'.1 c'.2 (hbound c')))
      = Work.Stems.Hur2b.cl x₀
          (Work.Stems.Hur2b.cellCube p (netCellIdx k).1 (netCellIdx k).2 (hbound (netCellIdx k))) := by
    apply Fintype.prod_eq_single (netCellIdx k)
    intro c' hc'
    have hconst : (Work.Stems.Hur2b.cellCube p c'.1 c'.2 (hbound c') : GenLoop (Fin 2) X x₀)
        = GenLoop.const := by
      apply GenLoop.ext
      intro y
      change c.1 ((netReadMap k) ((cellRead c'.1 c'.2) y)) = x₀
      exact c.2 _ (netReadMap_mem_boundary k
        (cellRead_notMem_openCube
          (fun heq => hc' (Prod.ext (Prod.ext_iff.mp heq).1 (Prod.ext_iff.mp heq).2)) y))
    rw [hconst, cl_const]
  rw [hsingle]
  have hcube : (Work.Stems.Hur2b.cellCube p (netCellIdx k).1 (netCellIdx k).2
        (hbound (netCellIdx k)) : GenLoop (Fin 2) X x₀)
      = compGenLoop (c := c) (φ := netDiag k)
          (fun y hy => c.2 _ (netDiag_mem_boundary k hy)) := by
    apply GenLoop.ext
    intro y
    change c.1 ((netReadMap k) ((cellRead (netCellIdx k).1 (netCellIdx k).2) y)) = c.1 (netDiag k y)
    rw [← netReadMap_comp_netDiag k]
    rfl
  rw [hcube, cl_comp_netDiag]

/-! ## Auxiliary evaluations for the final assembly -/

/-- The reading of the `k`-th cell, unfolded. -/
theorem netRead_apply_eq (k : Fin 6) (y : IC 2) :
    netRead k y = (faceIncl (netFace k).1 (netFace k).2) ((netReadMap k) y) := by
  fin_cases k <;> rfl

/-- A point of `∂I²` lies outside every open grid cell. -/
theorem memBoundary_notMem_openCube {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) (i j : Fin 8) :
    y ∉ openCube i j := by
  obtain ⟨c, hc⟩ := hy
  intro hh
  have hh' : (i:ℝ)/8 < (y 0:ℝ) ∧ (y 0:ℝ) < ((i:ℝ)+1)/8 ∧
      (j:ℝ)/8 < (y 1:ℝ) ∧ (y 1:ℝ) < ((j:ℝ)+1)/8 := by
    simpa only [openCube, Set.mem_ofPred_eq] using hh
  obtain ⟨ha, hb, hc1, hd⟩ := hh'
  have hi7 : (i:ℝ) ≤ 7 := by
    have h : (i:ℕ) ≤ 7 := by have := i.isLt; omega
    exact_mod_cast h
  have hj7 : (j:ℝ) ≤ 7 := by
    have h : (j:ℕ) ≤ 7 := by have := j.isLt; omega
    exact_mod_cast h
  have hi0 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg _
  have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg _
  fin_cases c
  · have hcy : y 0 = 0 ∨ y 0 = 1 := hc
    rcases hcy with h | h
    · have hv : (y 0 : ℝ) = 0 := by rw [h]; rfl
      linarith
    · have hv : (y 0 : ℝ) = 1 := by rw [h]; rfl
      linarith
  · have hcy : y 1 = 0 ∨ y 1 = 1 := hc
    rcases hcy with h | h
    · have hv : (y 1 : ℝ) = 0 := by rw [h]; rfl
      linarith
    · have hv : (y 1 : ℝ) = 1 := by rw [h]; rfl
      linarith

theorem netCellIdx_injective : Function.Injective netCellIdx := by decide

theorem netFace_bijective : Function.Bijective netFace := by decide

/-- **The alternating product of the six face classes equals the product over the net cells.** -/
theorem prod6_reindex {G : Type*} [CommGroup G] (X : Fin 3 → Fin 2 → G) :
    (∏ k : Fin 6, X (netFace k).1 (netFace k).2 ^ (netSign k))
      = (∏ i : Fin 3, X i 0 ^ ((-1:ℤ)^(i:ℕ)) * X i 1 ^ (-((-1:ℤ)^(i:ℕ))))⁻¹ := by
  have hsign : ∀ k : Fin 6,
      netSign k = -((-1:ℤ)^(((netFace k).1:ℕ) + ((netFace k).2:ℕ))) := by
    intro k; fin_cases k <;> norm_num [netFace, netSign]
  have step1 : (∏ k : Fin 6, X (netFace k).1 (netFace k).2 ^ (netSign k))
      = ∏ k : Fin 6, X (netFace k).1 (netFace k).2 ^
          (-((-1:ℤ)^(((netFace k).1:ℕ) + ((netFace k).2:ℕ)))) := by
    apply Fintype.prod_congr; intro k; rw [hsign k]
  rw [step1]
  have step2 : (∏ k : Fin 6, X (netFace k).1 (netFace k).2 ^
        (-((-1:ℤ)^(((netFace k).1:ℕ) + ((netFace k).2:ℕ)))))
      = ∏ p : Fin 3 × Fin 2, X p.1 p.2 ^ (-((-1:ℤ)^((p.1:ℕ) + (p.2:ℕ)))) :=
    netFace_bijective.prod_comp (fun p : Fin 3 × Fin 2 => X p.1 p.2 ^
      (-((-1:ℤ)^((p.1:ℕ) + (p.2:ℕ)))))
  rw [step2]
  have step3 : (∏ p : Fin 3 × Fin 2, X p.1 p.2 ^ (-((-1:ℤ)^((p.1:ℕ) + (p.2:ℕ)))))
      = (∏ p : Fin 3 × Fin 2, X p.1 p.2 ^ (((-1:ℤ)^((p.1:ℕ) + (p.2:ℕ)))))⁻¹ := by
    rw [show (∏ p : Fin 3 × Fin 2, X p.1 p.2 ^ (-((-1:ℤ)^((p.1:ℕ) + (p.2:ℕ)))))
        = ∏ p : Fin 3 × Fin 2, (X p.1 p.2 ^ (((-1:ℤ)^((p.1:ℕ) + (p.2:ℕ)))))⁻¹ from by
      apply Fintype.prod_congr; intro p; rw [zpow_neg]]
    exact Finset.prod_inv_distrib _
  rw [step3]
  have step4 : (∏ p : Fin 3 × Fin 2, X p.1 p.2 ^ (((-1:ℤ)^((p.1:ℕ) + (p.2:ℕ)))))
      = ∏ i : Fin 3, ∏ b : Fin 2, X i b ^ (((-1:ℤ)^((i:ℕ) + (b:ℕ)))) :=
    Fintype.prod_prod_type _
  rw [step4]
  congr 1
  apply Fintype.prod_congr
  intro i
  rw [Fin.prod_univ_two]
  rw [show ((-1:ℤ)^((i:ℕ) + ((0:Fin 2):ℕ))) = ((-1:ℤ)^(i:ℕ)) from by
    rw [show ((0:Fin 2):ℕ) = 0 from rfl, Nat.add_zero]]
  rw [show ((-1:ℤ)^((i:ℕ) + ((1:Fin 2):ℕ))) = -((-1:ℤ)^(i:ℕ)) from by
    rw [show ((1:Fin 2):ℕ) = 1 from rfl, pow_succ]; ring]


end

theorem collapse_model_class_eq_prod6 {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x₀ : X) (τ : ContinuousMap (Work.Stems.Cubical.IC 3) X) :
    ∃ (ψ : ContinuousMap (Work.Stems.Cubical.IC 2) Work.Stems.Hur2b.Bdy3)
      (hψ : ∀ y ∈ Cube.boundary (Fin 2), ψ y = Work.Stems.Hur2b.vertexBdy3),
      Work.Stems.Hur2b.cl x₀ (Work.Stems.Hur2b.model x₀ τ ψ hψ)
        = (Work.Stems.Hur2b.prod6 x₀ τ)⁻¹ := by
  obtain ⟨ψ, hψ, hcell, hcol⟩ := net_model
  refine ⟨ψ, hψ, ?_⟩
  let M : GenLoop (Fin 2) X x₀ := model x₀ τ ψ hψ
  have hM : ∀ z : IC 2, M.1 z = gluingMap x₀ τ (ψ z) := fun z => rfl
  have hGskel : ∀ p : Bdy3, Skel3 p → gluingMap x₀ τ p = x₀ := by
    rintro p ⟨i, i', hii, b, b', hb, hb'⟩
    exact gluingMap_eq_x₀_of_mem_two x₀ τ hb hb' hii
  have hGN : ∀ (k : Fin 6) (z : IC 2), gluingMap x₀ τ (netRead k z)
      = PsiCube x₀ (face3 τ (netFace k).1 (netFace k).2) ((netReadMap k) z) := by
    intro k z
    have h1 := DFunLike.congr_fun
      (gluingMap_comp_faceIncl x₀ τ (netFace k).1 (netFace k).2) ((netReadMap k) z)
    simp only [ContinuousMap.comp_apply] at h1
    rw [face3_eq_comp τ (netFace k).1 (netFace k).2, ← h1, netRead_apply_eq]
  have hbound : ∀ (c' : Fin 8 × Fin 8) (y : IC 2), y ∈ Cube.boundary (Fin 2) →
      M.1 (cellRead c'.1 c'.2 y) = x₀ := by
    intro c' y hy
    rw [hM]
    by_cases hc : ∃ k : Fin 6, c' = netCellIdx k
    · obtain ⟨k, rfl⟩ := hc
      rw [hcell k y, hGN k y]
      exact PsiCube_mem_boundary
        (netReadMap_mem_boundary k (memBoundary_notMem_openCube hy _ _))
    · rw [not_exists] at hc
      exact hGskel _ (hcol _ (by
        rw [mem_Collar]
        intro k
        exact cellRead_notMem_openCube
          (fun heq => hc k (Prod.ext (Prod.ext_iff.mp heq).1 (Prod.ext_iff.mp heq).2)) y))
  change Work.Stems.Hur2b.cl x₀ M = (Work.Stems.Hur2b.prod6 x₀ τ)⁻¹
  rw [cl_grid8 M hbound]
  have hoff : ∀ c' ∈ (Finset.univ : Finset (Fin 8 × Fin 8)),
      c' ∉ (Finset.univ.image netCellIdx : Finset (Fin 8 × Fin 8)) →
      Work.Stems.Hur2b.cl x₀ (Work.Stems.Hur2b.cellCube M c'.1 c'.2 (hbound c')) = 1 := by
    intro c' _ hc'
    have hc'' : ∀ k : Fin 6, c' ≠ netCellIdx k := fun k hk =>
      hc' (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk.symm⟩)
    have hconst : (Work.Stems.Hur2b.cellCube M c'.1 c'.2 (hbound c') : GenLoop (Fin 2) X x₀)
        = GenLoop.const := by
      apply GenLoop.ext
      intro y
      change gluingMap x₀ τ (ψ ((cellRead c'.1 c'.2) y)) = x₀
      exact hGskel _ (hcol _ (by
        rw [mem_Collar]
        intro k
        exact cellRead_notMem_openCube
          (fun heq => hc'' k (Prod.ext (Prod.ext_iff.mp heq).1 (Prod.ext_iff.mp heq).2)) y))
    rw [hconst, cl_const]
  have hcells : ∀ k : Fin 6,
      Work.Stems.Hur2b.cl x₀ (Work.Stems.Hur2b.cellCube M (netCellIdx k).1 (netCellIdx k).2
          (hbound (netCellIdx k)))
        = (psiC x₀ (face3 τ (netFace k).1 (netFace k).2)) ^ (netSign k) := by
    intro k
    have hh : ∀ y ∈ Cube.boundary (Fin 2),
        (psiGenLoop x₀ (face3 τ (netFace k).1 (netFace k).2)).1 ((netReadMap k) y) = x₀ :=
      fun y hy => PsiCube_mem_boundary (netReadMap_mem_boundary k
        (memBoundary_notMem_openCube hy (netCellIdx k).1 (netCellIdx k).2))
    have hcube : (Work.Stems.Hur2b.cellCube M (netCellIdx k).1 (netCellIdx k).2
          (hbound (netCellIdx k)) : GenLoop (Fin 2) X x₀)
        = compGenLoop (c := psiGenLoop x₀ (face3 τ (netFace k).1 (netFace k).2))
            (φ := netReadMap k) hh := by
      apply GenLoop.ext
      intro y
      change gluingMap x₀ τ (ψ ((cellRead (netCellIdx k).1 (netCellIdx k).2) y))
        = PsiCube x₀ (face3 τ (netFace k).1 (netFace k).2) ((netReadMap k) y)
      rw [hcell k y, hGN k y]
    rw [hcube]
    exact netRead_class k _ hh
  have hsix : (∏ k : Fin 6, Work.Stems.Hur2b.cl x₀ (Work.Stems.Hur2b.cellCube M (netCellIdx k).1
          (netCellIdx k).2 (hbound (netCellIdx k))))
      = (∏ k : Fin 6, (psiC x₀ (face3 τ (netFace k).1 (netFace k).2)) ^ (netSign k)) :=
    Fintype.prod_congr _ _ hcells
  have himg : (∏ x ∈ (Finset.univ.image netCellIdx : Finset (Fin 8 × Fin 8)),
        Work.Stems.Hur2b.cl x₀ (Work.Stems.Hur2b.cellCube M x.1 x.2 (hbound x)))
      = ∏ k : Fin 6, Work.Stems.Hur2b.cl x₀ (Work.Stems.Hur2b.cellCube M (netCellIdx k).1
          (netCellIdx k).2 (hbound (netCellIdx k))) :=
    (Finset.prod_bij (s := (Finset.univ : Finset (Fin 6)))
      (t := Finset.univ.image netCellIdx)
      (f := fun k : Fin 6 => Work.Stems.Hur2b.cl x₀ (Work.Stems.Hur2b.cellCube M (netCellIdx k).1
        (netCellIdx k).2 (hbound (netCellIdx k))))
      (g := fun x : Fin 8 × Fin 8 => Work.Stems.Hur2b.cl x₀
        (Work.Stems.Hur2b.cellCube M x.1 x.2 (hbound x)))
      (i := fun k _ => netCellIdx k)
      (fun k _ => Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
      (fun a _ b _ h => netCellIdx_injective h)
      (fun b hb => by
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hb
        exact ⟨k, Finset.mem_univ k, hk⟩)
      (fun k _ => rfl)).symm
  have hsub : (∏ x ∈ (Finset.univ.image netCellIdx : Finset (Fin 8 × Fin 8)),
        Work.Stems.Hur2b.cl x₀ (Work.Stems.Hur2b.cellCube M x.1 x.2 (hbound x)))
      = ∏ x : Fin 8 × Fin 8, Work.Stems.Hur2b.cl x₀
          (Work.Stems.Hur2b.cellCube M x.1 x.2 (hbound x)) :=
    Finset.prod_subset (Finset.subset_univ _) (fun x _ hx => hoff x (Finset.mem_univ x) hx)
  rw [← hsub, himg, hsix, prod6_reindex (X := fun i b => psiC x₀ (face3 τ i b))]
  rfl

end Work.Stems.Hur2b
