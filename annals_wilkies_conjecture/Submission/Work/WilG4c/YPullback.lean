/-
  WilG4c — the `y`-pullback prefix of the §5.3 reduction (`Work.WilG4c.StepLip`).

  The frozen `PY p n` (= `YBound`) bounds `iteratedFDeriv ℝ m (slice (F i l) x) y`, which is
  the *junk* value `0` wherever the slice fails to be `C^m`; it therefore does **not** imply
  that the `y`-slices are `C`-Lipschitz for any `C` (a definable slice may jump on a
  `(n-1)`-dimensional set).  Consequently no `x`-only reparametrisation of a `PY` family is
  `PYLip`, and the §5.3 route of BNZ cannot be run on `F` itself.

  The fix is to *create* the missing `y`-smoothness: apply the `n`-dimensional F-lemma
  (`ih`, a hypothesis of `StepLip`) to the family `(l,x) ↦ F i l (Fin.cons x ·)` over the
  parameter space `Λ × I_x`, obtaining a finite family of `y`-charts `φ`.  For such a chart,
  the *pullback family*

    `yPullback F φ i l z := F i l (Fin.cons (z 0) (fun j => φ j (Fin.snoc l (z 0)) (Fin.tail z)))`

  has, by construction, the `y`-slices of `F` *composed with the chart*, i.e. the composites
  whose unit `r`-norms are exactly the conclusion of `ih`.  Hence `yPullback F φ` satisfies
  `YBound` and is `1`-Lipschitz in the `y`-directions — which is what `F` itself lacks.

  This file contains the vocabulary; the properties are proved in the sibling modules
  (`YPullbackBound`, `YPullbackGraph`, `YPullbackDense`).
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.FLemAPI

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- The reparametrisation attached to a `(p+1)`-parameter chart `φ` of the `y`-family: it
sends `(l, z)` to the point whose first coordinate is `z 0` and whose remaining coordinates are
`fun j => φ j (l, z 0) (Fin.tail z)`. -/
def pullbackMap {p n : ℕ} (φ : ChartTuple (p+1) n) :
    (Fin p → ℝ) → (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) :=
  fun l z => Fin.cons (z 0) (fun j => φ j (Fin.snoc l (z 0)) (Fin.tail z))

/-- The `y`-pullback of a family along a `y`-chart: the reparametrisation changes only the
`y`-coordinates; the distinguished `x`-coordinate is kept. -/
def yPullback {k p n : ℕ} (F : Family k p (n+1)) (φ : ChartTuple (p+1) n) : Family k p (n+1) :=
  fun i l z => F i l (pullbackMap φ l z)

@[simp] theorem pullbackMap_apply {p n : ℕ} (φ : ChartTuple (p+1) n) (l : Fin p → ℝ)
    (z : Fin (n+1) → ℝ) :
    pullbackMap φ l z =
      Fin.cons (z 0) (fun j => φ j (Fin.snoc l (z 0)) (Fin.tail z)) := rfl

@[simp] theorem pullbackMap_zero {p n : ℕ} (φ : ChartTuple (p+1) n) (l : Fin p → ℝ)
    (z : Fin (n+1) → ℝ) : pullbackMap φ l z 0 = z 0 := by
  simp [pullbackMap]

@[simp] theorem pullbackMap_succ {p n : ℕ} (φ : ChartTuple (p+1) n) (l : Fin p → ℝ)
    (z : Fin (n+1) → ℝ) (j : Fin n) :
    pullbackMap φ l z j.succ = φ j (Fin.snoc l (z 0)) (Fin.tail z) := by
  simp [pullbackMap]

@[simp] theorem yPullback_apply {k p n : ℕ} (F : Family k p (n+1)) (φ : ChartTuple (p+1) n)
    (i : Fin k) (l : Fin p → ℝ) (z : Fin (n+1) → ℝ) :
    yPullback F φ i l z = F i l (pullbackMap φ l z) := rfl

/-- The first-coordinate slice of the pullback is the fibre slice of `F` composed with the
chart `φ` at the same parameter: this is the identity behind the transfer of `YBound`. -/
theorem slice_yPullback {k p n : ℕ} (F : Family k p (n+1)) (φ : ChartTuple (p+1) n)
    (i : Fin k) (l : Fin p → ℝ) (s : ℝ) :
    slice (yPullback F φ i l) s =
      fun u : Fin n → ℝ => F i l (Fin.cons s (fun j => φ j (Fin.snoc l s) u)) := by
  funext u
  simp only [slice, yPullback, pullbackMap, pt]
  rw [Fin.cons_zero, Fin.tail_cons]

/-- The pullback at `Fin.cons s u` is the composite of the `s`-slice of `F` with the chart. -/
theorem yPullback_cons {k p n : ℕ} (F : Family k p (n+1)) (φ : ChartTuple (p+1) n)
    (i : Fin k) (l : Fin p → ℝ) (s : ℝ) (u : Fin n → ℝ) :
    yPullback F φ i l (Fin.cons s u) =
      F i l (Fin.cons s (fun j => φ j (Fin.snoc l s) u)) := by
  rw [yPullback_apply, pullbackMap_apply, Fin.cons_zero, Fin.tail_cons]

/-- The image of the reparametrisation attached to a chart that maps the `y`-cube into itself
lies in the cube. -/
theorem pullbackMap_mem_openCube {p n : ℕ} {φ : ChartTuple (p+1) n} {l : Fin p → ℝ}
    (hφ : ∀ s : ℝ, ∀ t ∈ openCube n, (fun j => φ j (Fin.snoc l s) t) ∈ openCube n) :
    ∀ z ∈ openCube (n+1), pullbackMap φ l z ∈ openCube (n+1) := by
  intro z hz j
  induction j using Fin.cases with
  | zero => simpa using hz 0
  | succ k =>
    simpa using hφ (z 0) (Fin.tail z) (fun i => hz i.succ) k

/-- Values of the pullback are the values of `F` at points of the cube, so `ValuesIn01`
transfers. -/
theorem yPullback_valuesIn01 {k p n : ℕ} {F : Family k p (n+1)} {φ : ChartTuple (p+1) n}
    {Λ : Set (Fin p → ℝ)} (hval : ValuesIn01 Λ F)
    (hcube : ∀ l ∈ Λ, ∀ z ∈ openCube (n+1), pullbackMap φ l z ∈ openCube (n+1)) :
    ValuesIn01 Λ (yPullback F φ) := by
  intro i l hl z hz
  rw [yPullback_apply]
  exact hval i l hl (pullbackMap φ l z) (hcube l hl z hz)

/-- **The image of the pullback is `ε`-dense in the image of `F`.**  This is the hypothesis
`hdense` of `Work.WilG4c.ChartTransport`, read off from the cover of the `y`-family given by
`ih`: if the chart `φ` (together with some `t`) hits the `y`-value of every point of the
`(l,x)`-fibre up to `ε`, then the pullback hits the corresponding value of `F` up to `ε`. -/
theorem yPullback_dense {k p n : ℕ} {F : Family k p (n+1)} {φ : ChartTuple (p+1) n}
    {Λ : Set (Fin p → ℝ)} {ε : ℝ}
    (hcover : ∀ l ∈ Λ, ∀ x ∈ I, ∀ y ∈ openCube n, ∃ t ∈ openCube n,
      ∀ i, |F i l (Fin.cons x (fun j => φ j (Fin.snoc l x) t)) - F i l (Fin.cons x y)| < ε) :
    ∀ l ∈ Λ, ∀ z ∈ openCube (n+1), ∃ z' ∈ openCube (n+1),
      ∀ i, |yPullback F φ i l z' - F i l z| < ε := by
  intro l hl z hz
  have hz0 : z 0 ∈ I := hz 0
  have hzt : Fin.tail z ∈ openCube n := fun i => hz i.succ
  obtain ⟨t, ht, h⟩ := hcover l hl (z 0) hz0 (Fin.tail z) hzt
  refine ⟨Fin.cons (z 0) t, ?_, ?_⟩
  · intro j
    induction j using Fin.cases with
    | zero => simpa using hz 0
    | succ k => simpa using ht k
  · intro i
    rw [yPullback_cons, ← Fin.cons_self_tail z]
    exact h i

end Work.WilkG4c
