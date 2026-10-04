import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.L.Stmt
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.L.R4_rmFrame_initSMet_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]

/-- **Parseval in a `g`-orthonormal frame.**  The coordinate functions `i ↦ g.inner x (e i) ·` of a
`g`-orthonormal frame preserve the scalar product: for all `v, w`,
`∑ i, g.inner x (e i) v * g.inner x (e i) w = g.inner x v w`. -/
private lemma dot_coord_eq (g : SMet I M) (x : M) (hn : 0 < Module.finrank ℝ E)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (v w : TangentSpace I x) :
    (∑ i, g.inner x (e i) v * g.inner x (e i) w) = g.inner x v w := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hon : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    exact he i j
  have hsum : ∀ c : TangentSpace I x, (∑ i, g.inner x (e i) c • e i) = c :=
    fun c => Work.Diff.GE.sum_inner_smul_eq_self g x hn e he c
  have h := Orthonormal.inner_sum hon (fun i => g.inner x (e i) v)
    (fun i => g.inner x (e i) w) Finset.univ
  calc (∑ i, g.inner x (e i) v * g.inner x (e i) w)
      = ∑ i, (starRingEnd ℝ) (g.inner x (e i) v) * g.inner x (e i) w :=
        Finset.sum_congr rfl (fun i _ => by simp)
    _ = inner ℝ (∑ i, g.inner x (e i) v • e i) (∑ i, g.inner x (e i) w • e i) := h.symm
    _ = inner ℝ v w := by rw [hsum v, hsum w]
    _ = g.inner x v w := rfl

/-- **Coordinates of an orthonormal pair.**  The coordinates of a `g`-orthonormal pair of vectors
in a `g`-orthonormal frame form an orthonormal pair of coefficient vectors. -/
private lemma isONPair_coord (g : SMet I M) (x : M) (hn : 0 < Module.finrank ℝ E)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (p q : TangentSpace I x) (hp : g.inner x p p = 1) (hq : g.inner x q q = 1)
    (hpq : g.inner x p q = 0) :
    IsONPair (fun i => g.inner x (e i) p) (fun i => g.inner x (e i) q) :=
  ⟨(dot_coord_eq g x hn e he p p).trans hp, (dot_coord_eq g x hn e he q q).trans hq,
    (dot_coord_eq g x hn e he p q).trans hpq⟩

end Helpers

/-- **From frame-component bounds to pinching of the Levi-Civita connection.**  If the sectional
curvatures of the frame tensor `rmFrame g x (onFrame g x)` (in the *chosen* orthonormal frame)
satisfy the two-sided bound for every orthonormal pair of coefficient vectors, then the curvature of
the Levi-Civita connection of `g` is `(κ, (1+η)κ]`-pinched in the `g.inner` form: for all smooth
sections `X, Y` and every `x` where `g.inner x (X x) (X x) = 1`, `g.inner x (Y x) (Y x) = 1` and
`g.inner x (X x) (Y x) = 0`, the sectional curvature `g.inner x (curv (lcOf g) X Y Y x) (X x)` again
lies in `(κ, (1+η)κ]`.

Route.  With `e := onFrame g x`, `a := X x`, `b := Y x`: the coordinate vectors
`u := fun i => g.inner x (e i) a`, `v := fun i => g.inner x (e i) b` form an orthonormal pair
(Parseval, provable as in `Work.Diff.L.pinched_of_frame`'s `dot_coord_eq`/`isONPair_coord`, using
`Work.Diff.GE.sum_inner_smul_eq_self`), so the hypothesis applies to `u, v`.  Then
`secK (rmFrame g x e) u v = g.inner x (rmVec (lcOf g) x a b b) a` by the frame identity — prove it
inline by expanding `(∑ uᵢ eᵢ)` with `Work.Diff.GE.rmVec_sum_left/middle/right` and
`Work.Diff.GE.sum_inner_smul_eq_self`; do NOT import `Submission.Work.Diff.L.secK_rmFrame_eq_inner`,
that module currently does not build (a missing `T2Space` instance argument).  Finally
`g.inner x (rmVec (lcOf g) x a b b) a = g.inner x (curv (lcOf g) X Y Y x) (X x)` by
`Work.Diff.GE.rmVec_eq_curvVec` + `Submission.CurvatureVec.curvVec_eq` applied to the smooth
extensions `X, Y`, together with `curv_eq_of_apply_eq` (the curvature depends only on the values at
`x`). -/
theorem pinched_of_frameBounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [T2Space M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    {g : Submission.Diff.SMet I M} {κ η : ℝ} (hη : 0 < η) (hκ : 0 < κ)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g)
      (((⊤ : ℕ∞) : WithTop ℕ∞)))
    (h : ∀ (x : M) (u v : Fin (Module.finrank ℝ E) → ℝ), Submission.Diff.Alg.IsONPair u v →
      κ < Submission.Diff.Alg.secK
          (Submission.Diff.rmFrame g x (Submission.Diff.onFrame g x)) u v ∧
      Submission.Diff.Alg.secK
          (Submission.Diff.rmFrame g x (Submission.Diff.onFrame g x)) u v ≤ (1 + η) * κ) :
    ∀ (X Y : Π x : M, TangentSpace I x), Work.Diff.L.SmoothField X → Work.Diff.L.SmoothField Y →
      ∀ x : M, g.inner x (X x) (X x) = 1 → g.inner x (Y x) (Y x) = 1 →
        g.inner x (X x) (Y x) = 0 →
        κ < g.inner x
            (LeanEval.Geometry.SphereTheorem.curv (Submission.Diff.lcOf g) X Y Y x) (X x) ∧
        g.inner x
            (LeanEval.Geometry.SphereTheorem.curv (Submission.Diff.lcOf g) X Y Y x) (X x)
          ≤ (1 + η) * κ := by
  intro X Y hX hY x h1 h2 h3
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hn : 0 < Module.finrank ℝ E := by omega
  have he : IsONFrame g x (onFrame g x) := Work.Diff.GE.isONFrame_onFrame g x
  -- the coefficient vectors of `X x` and `Y x` in the chosen frame
  let a : Fin (Module.finrank ℝ E) → ℝ := fun i => g.inner x (onFrame g x i) (X x)
  let b : Fin (Module.finrank ℝ E) → ℝ := fun j => g.inner x (onFrame g x j) (Y x)
  have hON : IsONPair a b :=
    isONPair_coord g x hn (onFrame g x) he (X x) (Y x) h1 h2 h3
  obtain ⟨hlo, hup⟩ := h x a b hON
  -- the coefficient vectors expand back to `X x` and `Y x`
  have hA : (∑ i, a i • onFrame g x i) = X x := by
    show (∑ i, g.inner x (onFrame g x i) (X x) • onFrame g x i) = X x
    exact Work.Diff.GE.sum_inner_smul_eq_self g x hn (onFrame g x) he (X x)
  have hB : (∑ j, b j • onFrame g x j) = Y x := by
    show (∑ j, g.inner x (onFrame g x j) (Y x) • onFrame g x j) = Y x
    exact Work.Diff.GE.sum_inner_smul_eq_self g x hn (onFrame g x) he (Y x)
  -- the pointwise curvature agrees with the curvature of the smooth fields
  have hrm : rmVec (lcOf g) x (X x) (Y x) (Y x) = curv (lcOf g) X Y Y x := by
    rw [Work.Diff.GE.rmVec_eq_curvVec (lcOf g) hcov x (X x) (Y x) (Y x)]
    exact Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hX hY hY rfl rfl rfl
  -- the frame identity: frame components contracted with the coordinates are the pairing of `R`
  have hsec : secK (rmFrame g x (onFrame g x)) a b
      = g.inner x (curv (lcOf g) X Y Y x) (X x) := by
    show R4 (rmFrame g x (onFrame g x)) a b a b
      = g.inner x (curv (lcOf g) X Y Y x) (X x)
    rw [R4_rmFrame_eq_inner (I := I) (M := M) g hcov x (onFrame g x) a b a b, hA, hB, hrm]
  rw [hsec] at hlo hup
  exact ⟨hlo, hup⟩

end Work.Diff.L
