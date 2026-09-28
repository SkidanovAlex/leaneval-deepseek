import Mathlib
import Submission.Work.Serre.pathSpaceAaction
import Submission.Work.Serre.PathSpaceTorsor
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.Serre.sweepCube_bdry

/-!
# The `A`-difference of two lifts of a simplex is constant (`actRel_const`, piece (D1))

For a based space `(X, pt)`, `E = Work.StemsB.PathSpace X pt` and `p = evalOne X pt : E → X`, let
`act : A → C(E, E)` preserve `p` (`hact`).  Given two lifts `X₁`, `X₂ : Δⁿ → E` of the same simplex
`σ : Δⁿ → X` and a homotopy (relative to the endpoints) at a point `z ∈ Δⁿ` between
`act a (X₁ z)` and `X₂ z`, the *same* relative homotopy exists at every other point `z' ∈ Δⁿ`.

This is the constancy of the "`A`-difference" of the two lifts over the simplex: the difference is
a section of the `π₀`-bundle of the fibration `p` over the simply connected (indeed contractible)
base `Δⁿ`, and monodromy over a contractible base is trivial.

## Proof

It is the classical *filling of a `U`-shaped square* by the homotopy lifting property, and it uses
nothing but the fact that `p` is a Serre fibration (no connectivity or vanishing of `π₂`):

* `c : I → Δⁿ` is the straight segment from `z` to `z'` (the simplex is convex), so
  `σ ∘ c` is a path in the base;
* in the square `I_u × I_s` the base map `Hbase (u, s) = σ (c u)` (constant in `s`) has three
  prescribed lifts: on `{u = 0}` the given homotopy, seen as a path in the fibre over `σ z` from
  `act a (X₁ z)` to `X₂ z`; on `{s = 0}` the path `u ↦ act a (X₁ (c u))`; on `{s = 1}` the path
  `u ↦ X₂ (c u)`.  The corners match by `c 0 = z`;
* `Work.Serre.sweepCube_bdry` (the three-face lifting property for the cube `Z = I⁰`, a point)
  fills the square;
* the missing edge `{u = 1}` is a path in the fibre over `σ z'` from `act a (X₁ z')` to `X₂ z'`,
  which — read through `evalOne` — is the required homotopy.
-/

namespace Work.Serre

/-- The straight-line path in the standard simplex from `z` to `z'`. -/
def simplexPath {n : ℕ} (z z' : ↥(stdSimplex ℝ (Fin (n + 1)))) :
    C(unitInterval, ↥(stdSimplex ℝ (Fin (n + 1)))) where
  toFun t :=
    ⟨(1 - (t : ℝ)) • (z : Fin (n + 1) → ℝ) + (t : ℝ) • (z' : Fin (n + 1) → ℝ),
      convex_stdSimplex ℝ (Fin (n + 1)) z.2 z'.2 (by have := t.2.2; linarith) t.2.1 (by ring)⟩
  continuous_toFun := by fun_prop

@[simp] theorem simplexPath_zero {n : ℕ} (z z' : ↥(stdSimplex ℝ (Fin (n + 1)))) :
    simplexPath z z' 0 = z := by
  apply Subtype.ext
  show (1 - ((0 : unitInterval) : ℝ)) • (z : Fin (n + 1) → ℝ) +
      ((0 : unitInterval) : ℝ) • (z' : Fin (n + 1) → ℝ) = (z : Fin (n + 1) → ℝ)
  norm_num

@[simp] theorem simplexPath_one {n : ℕ} (z z' : ↥(stdSimplex ℝ (Fin (n + 1)))) :
    simplexPath z z' 1 = z' := by
  apply Subtype.ext
  show (1 - ((1 : unitInterval) : ℝ)) • (z : Fin (n + 1) → ℝ) +
      ((1 : unitInterval) : ℝ) • (z' : Fin (n + 1) → ℝ) = (z' : Fin (n + 1) → ℝ)
  norm_num

/-- The `A`-difference of two lifts of a simplex is independent of the point of the simplex: a
relative homotopy `act a (X₁ z) ≃ X₂ z` at one point propagates to every other point. -/
theorem actRel_const {X : Type} [TopologicalSpace X] (pt : X)
    (A : Type) [AddCommGroup A] [Fintype A]
    (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt))
    (hact : ∀ a, (Work.StemsB.evalOne X pt).comp (act a) = Work.StemsB.evalOne X pt)
    (n : ℕ) (σ : C(↥(stdSimplex ℝ (Fin (n + 1))), X))
    (X₁ X₂ : C(↥(stdSimplex ℝ (Fin (n + 1))), Work.StemsB.PathSpace X pt))
    (h₁ : (Work.StemsB.evalOne X pt).comp X₁ = σ)
    (h₂ : (Work.StemsB.evalOne X pt).comp X₂ = σ)
    (z z' : ↥(stdSimplex ℝ (Fin (n + 1)))) (a : A)
    (h : ∃ H : C(unitInterval × unitInterval, X),
        (∀ t : unitInterval, H (0, t) = (act a (X₁ z)).1 t) ∧
        (∀ t : unitInterval, H (1, t) = (X₂ z).1 t) ∧
        (∀ s : unitInterval, H (s, 0) = pt) ∧
        (∀ s : unitInterval, H (s, 1) = σ z)) :
    ∃ H : C(unitInterval × unitInterval, X),
        (∀ t : unitInterval, H (0, t) = (act a (X₁ z')).1 t) ∧
        (∀ t : unitInterval, H (1, t) = (X₂ z').1 t) ∧
        (∀ s : unitInterval, H (s, 0) = pt) ∧
        (∀ s : unitInterval, H (s, 1) = σ z') := by
  classical
  obtain ⟨H, hH0, hH1, hHs0, hHs1⟩ := h
  -- the two projections to the base
  have hX₁ : ∀ w : ↥(stdSimplex ℝ (Fin (n + 1))), (X₁ w).1 1 = σ w :=
    fun w => congrFun (congrArg DFunLike.coe h₁) w
  have hX₂ : ∀ w : ↥(stdSimplex ℝ (Fin (n + 1))), (X₂ w).1 1 = σ w :=
    fun w => congrFun (congrArg DFunLike.coe h₂) w
  have hact' : ∀ (b : A) (e : Work.StemsB.PathSpace X pt), (act b e).1 1 = e.1 1 :=
    fun b e => congrFun (congrArg DFunLike.coe (hact b)) e
  -- the path `c` in the simplex from `z` to `z'`
  let c : C(unitInterval, ↥(stdSimplex ℝ (Fin (n + 1)))) := simplexPath z z'
  have hc0 : c 0 = z := by rw [show c = simplexPath z z' from rfl, simplexPath_zero]
  have hc1 : c 1 = z' := by rw [show c = simplexPath z z' from rfl, simplexPath_one]
  -- the lift of the given homotopy as a path in the path space
  let Rfun : C(unitInterval, Work.StemsB.PathSpace X pt) :=
    ⟨fun u => ⟨H.curry u, by rw [ContinuousMap.curry_apply]; exact hHs0 u⟩,
      Continuous.subtype_mk H.curry.continuous
        (fun u => by rw [ContinuousMap.curry_apply]; exact hHs0 u)⟩
  have hRfun : ∀ u : unitInterval, (Rfun u).1 = H.curry u := fun u => rfl
  have hRfun_apply : ∀ (u t : unitInterval), (Rfun u).1 t = H (u, t) := by
    intro u t
    rw [hRfun u, ContinuousMap.curry_apply]
  -- the base test space of the sweep: a point
  let Z : Type := Fin 0 → unitInterval
  let z₀ : Z := fun i => i.elim0
  have hZ : Subsingleton Z := inferInstance
  -- the three faces and the base map
  let f0 : C(Z × unitInterval, Work.StemsB.PathSpace X pt) :=
    ⟨fun w => Rfun w.2, Rfun.continuous.comp continuous_snd⟩
  let f1 : C(Z × unitInterval, Work.StemsB.PathSpace X pt) :=
    ⟨fun w => act a (X₁ (c w.2)),
      (act a).continuous.comp (X₁.continuous.comp (c.continuous.comp continuous_snd))⟩
  let f2 : C(Z × unitInterval, Work.StemsB.PathSpace X pt) :=
    ⟨fun w => X₂ (c w.2), X₂.continuous.comp (c.continuous.comp continuous_snd)⟩
  let Hbase : C(Z × unitInterval × unitInterval, X) :=
    ⟨fun w => σ (c w.2.1),
      σ.continuous.comp (c.continuous.comp (continuous_fst.comp continuous_snd))⟩
  have hf0 : ∀ w : Z × unitInterval, f0 w = Rfun w.2 := fun w => rfl
  have hf1 : ∀ w : Z × unitInterval, f1 w = act a (X₁ (c w.2)) := fun w => rfl
  have hf2 : ∀ w : Z × unitInterval, f2 w = X₂ (c w.2) := fun w => rfl
  have hHbase : ∀ (y : Z) (u s : unitInterval), Hbase (y, u, s) = σ (c u) :=
    fun y u s => rfl
  -- the compatibility of the faces
  have comp0 : (Work.StemsB.evalOne X pt).comp f0 =
      Hbase.comp ⟨fun x : Z × unitInterval => (x.1, 0, x.2), by fun_prop⟩ := by
    ext w
    show (f0 w).1 1 = Hbase (w.1, 0, w.2)
    rw [hf0 w, hRfun_apply w.2 1, hHbase w.1 0 w.2, hc0]
    exact hHs1 w.2
  have comp1 : (Work.StemsB.evalOne X pt).comp f1 =
      Hbase.comp ⟨fun x : Z × unitInterval => (x.1, x.2, 0), by fun_prop⟩ := by
    ext w
    show (f1 w).1 1 = Hbase (w.1, w.2, 0)
    rw [hf1 w, hact' a (X₁ (c w.2)), hX₁ (c w.2), hHbase w.1 w.2 0]
  have comp2 : (Work.StemsB.evalOne X pt).comp f2 =
      Hbase.comp ⟨fun x : Z × unitInterval => (x.1, x.2, 1), by fun_prop⟩ := by
    ext w
    show (f2 w).1 1 = Hbase (w.1, w.2, 1)
    rw [hf2 w, hX₂ (c w.2), hHbase w.1 w.2 1]
  have corner0 : ∀ y : Z, f0 (y, 0) = f1 (y, 0) := by
    intro y
    apply Subtype.ext
    ext t
    show (f0 (y, 0)).1 t = (f1 (y, 0)).1 t
    rw [hf0 (y, 0), hRfun_apply 0 t, hf1 (y, 0), hc0]
    exact hH0 t
  have corner1 : ∀ y : Z, f0 (y, 1) = f2 (y, 0) := by
    intro y
    apply Subtype.ext
    ext t
    show (f0 (y, 1)).1 t = (f2 (y, 0)).1 t
    rw [hf0 (y, 1), hRfun_apply 1 t, hf2 (y, 0), hc0]
    exact hH1 t
  -- the sweep
  have hSweep := (Work.Serre.sweepCube_bdry (Work.StemsB.evalOne X pt)
    (Work.StemsB.isSerreFibration_evalOne X pt)).1 0
  obtain ⟨G, hG, hG0, hG1, hG2⟩ := hSweep Hbase f0 comp0 f1 comp1 f2 comp2 corner0 corner1
  -- the missing edge of the filled square gives the new homotopy
  let g : C(unitInterval, Work.StemsB.PathSpace X pt) :=
    ⟨fun t => G (z₀, 1, t), G.continuous.comp (by fun_prop)⟩
  have hg0 : g 0 = f1 (z₀, 1) := hG1 z₀ 1
  have hg1 : g 1 = f2 (z₀, 1) := hG2 z₀ 1
  have hgeval : ∀ s : unitInterval, (g s).1 1 = σ (c 1) := by
    intro s
    have := congrFun (congrArg DFunLike.coe hG) (z₀, (1 : unitInterval), s)
    exact this
  let gval : C(unitInterval, C(unitInterval, X)) :=
    ⟨fun t => (g t).1, continuous_subtype_val.comp g.continuous⟩
  have hgval : ∀ t : unitInterval, gval t = (g t).1 := fun t => rfl
  refine ⟨gval.uncurry, ?_, ?_, ?_, ?_⟩
  · intro t
    show gval 0 t = (act a (X₁ z')).1 t
    rw [hgval 0]
    have : g 0 = act a (X₁ (c 1)) := by
      rw [hg0]
      show f1 (z₀, (1 : unitInterval)) = act a (X₁ (c 1))
      rfl
    rw [this, hc1]
  · intro t
    show gval 1 t = (X₂ z').1 t
    rw [hgval 1]
    have : g 1 = X₂ (c 1) := by
      rw [hg1]
      show f2 (z₀, (1 : unitInterval)) = X₂ (c 1)
      rfl
    rw [this, hc1]
  · intro s
    show gval s 0 = pt
    rw [hgval s]
    exact (g s).2
  · intro s
    show gval s 1 = σ z'
    rw [hgval s, hgeval s, hc1]

end Work.Serre
