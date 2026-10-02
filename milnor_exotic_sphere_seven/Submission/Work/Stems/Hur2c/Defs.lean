import Submission.Work.Stems.CubicalNorm
import Submission.Work.Stems.Hur2b.PsiLin_cubD_single

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Ψ` on degenerate `2`-cubes: vocabulary

This is the `Hur2c` layer of the degree-`2` Hurewicz development.  Its purpose is the statement

*`Work.Stems.Hur2c.PsiLin_eq_zero_of_degen_cycle`*: the filling `Ψ` of a **degenerate `2`-cycle**
is trivial.  This is the missing ingredient of the degree-`2` Hurewicz theorem: the naive route
through `Ψ(∂σ) = 0` needs `Ψ` to vanish on *all* degenerate `2`-cubes, which is **not provable**
for the workspace's `Ψ` (its `K₀`, `K₁` are opaque `Classical.choose` witnesses); see
`Submission/Work/Stems/PSI_DEG_NOTES.md`.  Only *cycles* are needed, and for those the vanishing
does follow from `(Y)` (`PsiLin_cubD_single`) together with the constant case.

## The vocabulary

A degenerate `2`-cube is, up to the labelling of its coordinates, of the form

`degenCube i δ : I² → X`,   `t ↦ δ (t i)`   (`i : Fin 2`, `δ : I → X`),

the pull-back of the `1`-cube `δ` along the coordinate projection `i`.  We write

`T x₀ i δ := Ψ (single (degenCube i δ) 1) ∈ π₂(X,x₀)`

for its `Ψ`-value.

## The `T`-calculus

The `T`-values satisfy, and are determined by:

* `T_loop` — `T` of a loop (in particular of a constant `1`-cube) vanishes;
* `T_coord` — `T x₀ 0 δ = T x₀ 1 δ` (the two coordinate variants agree);
* `T_rev` — reversing `δ` negates `T`;
* `T_mul` — `T` is additive in the concatenation of `1`-cubes.

Together they give `T x₀ i δ = φ (δ 1) - φ (δ 0)` with `φ v := T x₀ i (K₀ v)`, hence the vanishing
on degenerate `2`-cycles by linearity (`degenCube_boundary` computes `∂` of a degenerate cube, which
is what turns the cycle condition into the cancellation of the `φ`-values).
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2c

open Work.Stems.Cubical

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The projection `I² → I¹` onto the coordinate `i`. -/
def proj (i : Fin 2) : C(IC 2, IC 1) :=
  ⟨fun t _ => t i, continuous_pi fun _ => continuous_apply i⟩

@[simp] theorem proj_apply (i : Fin 2) (t : IC 2) (j : Fin 1) : proj i t j = t i := rfl

/-- **The degenerate `2`-cube attached to a `1`-cube `δ`**: the pull-back of `δ` along the
projection onto the coordinate `i`.  Every degenerate `2`-cube is of this form. -/
def degenCube (i : Fin 2) (δ : C(IC 1, X)) : C(IC 2, X) := δ.comp (proj i)

@[simp] theorem degenCube_apply (i : Fin 2) (δ : C(IC 1, X)) (t : IC 2) (j : Fin 1) :
    degenCube i δ t = δ (proj i t) := rfl

theorem isDegenerate_degenCube (i : Fin 2) (δ : C(IC 1, X)) :
    IsDegenerate 2 (degenCube i δ) := by
  refine ⟨⟨1 - i.val, by omega⟩, fun t t' h => ?_⟩
  have hne : i ≠ (⟨1 - i.val, by omega⟩ : Fin 2) := by
    intro hc
    have := congrArg Fin.val hc
    simp only [Fin.val_mk] at this
    omega
  show δ (proj i t) = δ (proj i t')
  congr 1
  funext j
  exact h i hne

/-- A `Path` as a `1`-cube. -/
def cubeOfPath {X : Type} [TopologicalSpace X] {a b : X} (γ : Path a b) : C(IC 1, X) :=
  ⟨fun t => γ (t 0), γ.continuous.comp (continuous_apply 0)⟩

@[simp] theorem cubeOfPath_apply {X : Type} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (t : IC 1) : cubeOfPath γ t = γ (t 0) := rfl

/-- **The `Ψ`-value of a degenerate `2`-cube**, as a function of the attached `1`-cube `δ`. -/
def T (x₀ : X) [SimplyConnectedSpace X] (i : Fin 2) (δ : C(IC 1, X)) :
    Additive (HomotopyGroup (Fin 2) X x₀) :=
  Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (degenCube i δ) 1)

/-- `T` is the `Ψ`-value of `degenCube`. -/
theorem T_def (x₀ : X) [SimplyConnectedSpace X] (i : Fin 2) (δ : C(IC 1, X)) :
    T x₀ i δ = Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (degenCube i δ) 1) := rfl

/-! ## The same vocabulary in all dimensions

The `3`-cube steps of the `T`-calculus (`STATUS.md` (0)--(3)) all use a cube of the form
`γ ∘ (a coordinate projection)`; with the general `degenCube'` and the two face lemmas below every
face identity becomes a two-line rewrite, and no `Fin.predAbove` computation is ever needed (the
inverse index is *provided* as the witness `k`).
-/

/-- **The frozen coordinate of a face.** -/
theorem faceCM_frozen {n : ℕ} (i : Fin (n + 1)) (b : unitInterval) (t : IC n) :
    (faceCM i b t) i = b := by
  rw [faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]

/-- The projection `I^{n+1} → I^n` onto the coordinate `i`. -/
def proj' (n : ℕ) (i : Fin (n + 1)) : C(IC (n + 1), IC n) :=
  ⟨fun t _ => t i, continuous_pi fun _ => continuous_apply i⟩

@[simp] theorem proj'_apply (n : ℕ) (i : Fin (n + 1)) (t : IC (n + 1)) (j : Fin n) :
    proj' n i t j = t i := rfl

/-- **The degenerate `(n+1)`-cube attached to an `n`-cube `δ`**: `δ` pulled back along the
projection onto the coordinate `i`. -/
def degenCube' (n : ℕ) (i : Fin (n + 1)) {X : Type} [TopologicalSpace X] (δ : C(IC n, X)) :
    C(IC (n + 1), X) :=
  δ.comp (proj' n i)

@[simp] theorem degenCube'_apply (n : ℕ) (i : Fin (n + 1)) {X : Type} [TopologicalSpace X]
    (δ : C(IC n, X)) (t : IC (n + 1)) : degenCube' n i δ t = δ (proj' n i t) := rfl

/-- The "diagonal" pull-back of an `n`-cube along the fold `s ↦ (fun _ => s k)`.  The faces of
`degenCube'` in the other directions are of this form. -/
def diagCube (n : ℕ) {X : Type} [TopologicalSpace X] (k : Fin n) (δ : C(IC n, X)) :
    C(IC n, X) :=
  δ.comp ⟨fun s _ => s k, continuous_pi fun _ => continuous_apply k⟩

@[simp] theorem diagCube_apply (n : ℕ) {X : Type} [TopologicalSpace X] (k : Fin n)
    (δ : C(IC n, X)) (s : IC n) : diagCube n k δ s = δ (fun _ => s k) := rfl

/-- The face of a degenerate cube in the frozen direction is constant. -/
theorem faceCube_degenCube'_frozen (n : ℕ) (i : Fin (n + 1)) (b : unitInterval)
    {X : Type} [TopologicalSpace X] (δ : C(IC n, X)) :
    faceCube i b (degenCube' n i δ) = ContinuousMap.const (IC n) (δ (fun _ => b)) := by
  ext t
  show δ (proj' n i (faceCM i b t)) = δ (fun _ => b)
  congr 1
  funext j
  rw [proj'_apply]
  exact faceCM_frozen i b t

/-- The faces of a degenerate cube in the other directions are diagonal cubes of `δ`; the inverse
index `k` of the frozen coordinate is *provided*, which is what makes this a rewrite. -/
theorem faceCube_degenCube'_other {n : ℕ} {i j : Fin (n + 1)} {k : Fin n}
    (h : i = j.succAbove k) (b : unitInterval) {X : Type} [TopologicalSpace X]
    (δ : C(IC n, X)) :
    faceCube j b (degenCube' n i δ) = diagCube n k δ := by
  ext s
  show δ (proj' n i (faceCM j b s)) = δ (fun _ => s k)
  congr 1
  funext l
  rw [proj'_apply]
  show (faceCM j b s) i = s k
  rw [h, faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth,
    Fin.insertNth_apply_succAbove]


end

end Work.Stems.Hur2c
