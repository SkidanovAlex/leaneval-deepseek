import Mathlib
import Submission.Work.Stems.Cubical.CubeFace
import Submission.Work.Stems.Hur2b.homotopic_const_of_boundary_const

/-!
# The cancellation half of the homotopy addition theorem (general dimension)

Let `g : I^{k+1} → X` be a cube and `ψ : I^k → I^{k+1}` a continuous map which is *constant* on the
boundary `∂I^k`, with value a point `v` where `g v = x₀`.  Then the based cube `g ∘ ψ` is
null-homotopic (relative to `∂I^k`), hence its class in `π_k(X,x₀)` is trivial.

The homotopy is the explicit *straight-line* (convex) homotopy

  `H(u,t) = g((1-t)·ψ u + t·v)`,

which is a homotopy of based cubes because `ψ` is constant on `∂I^k` with value `v`: for `u ∈ ∂I^k`
the whole segment is the single point `v`, so every slice is constant on the boundary.  Lemma
2.2(a) of Hutchings (`Work.Stems.Hur2b.homotopic_const_of_boundary_const`) then converts this into
a based null-homotopy.

This is the general-dimension form of the "cancellation" step of the proof of the homotopy
addition theorem (Hutchings 2.2(b)): the boundary sphere map of a cube that extends over the ball
(e.g. `g|_{∂I^{k+1}} = g ∘ (a collapse)`) is trivial in `π_k(X,x₀)`.  The case `k = 2` is
`Work.Stems.Hur2b.model_class_eq_one'`.
-/

open scoped unitInterval Topology

namespace Work.RatHurewicz

open Work.Stems.Cubical

noncomputable section

/-- The straight-line segment in the cube `I^n` from `a` to `b`, at parameter `s`. -/
def segPt {n : ℕ} (a b : IC n) (s : unitInterval) : IC n :=
  fun i => ⟨(1 - (s : ℝ)) * (a i : ℝ) + (s : ℝ) * (b i : ℝ), by
    have ha := (a i).2
    have hb := (b i).2
    have hs := s.2
    constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2, hs.1, hs.2]⟩

theorem continuous_segPt {n : ℕ} (a b : IC n) : Continuous (fun s => segPt a b s) := by
  refine continuous_pi (fun i => ?_)
  apply Continuous.subtype_mk
  fun_prop

@[simp] theorem segPt_zero {n : ℕ} (a b : IC n) : segPt a b 0 = a := by
  funext i
  exact Subtype.ext (by
    show (1 - ((0 : unitInterval) : ℝ)) * (a i : ℝ) + ((0 : unitInterval) : ℝ) * (b i : ℝ)
      = (a i : ℝ)
    norm_num)

@[simp] theorem segPt_one {n : ℕ} (a b : IC n) : segPt a b 1 = b := by
  funext i
  exact Subtype.ext (by
    show (1 - ((1 : unitInterval) : ℝ)) * (a i : ℝ) + ((1 : unitInterval) : ℝ) * (b i : ℝ)
      = (b i : ℝ)
    norm_num)

@[simp] theorem segPt_self {n : ℕ} (a : IC n) (s : unitInterval) : segPt a a s = a := by
  funext i
  exact Subtype.ext (by
    show (1 - (s : ℝ)) * (a i : ℝ) + (s : ℝ) * (a i : ℝ) = (a i : ℝ)
    ring)

/-- The straight-line homotopy of the cube `I^{n+1}` from `ψ` to the constant map at `v`. -/
def segHom {n : ℕ} (ψ : C(IC n, IC (n + 1))) (v : IC (n + 1)) :
    C(IC n × unitInterval, IC (n + 1)) where
  toFun p := segPt (ψ p.1) v p.2
  continuous_toFun := by
    refine continuous_pi (fun i => ?_)
    apply Continuous.subtype_mk
    fun_prop

@[simp] theorem segHom_apply {n : ℕ} (ψ : C(IC n, IC (n + 1))) (v : IC (n + 1))
    (u : IC n) (t : unitInterval) : segHom ψ v (u, t) = segPt (ψ u) v t := rfl

@[simp] theorem segHom_zero {n : ℕ} (ψ : C(IC n, IC (n + 1))) (v : IC (n + 1)) (u : IC n) :
    segHom ψ v (u, 0) = ψ u := segPt_zero _ _

@[simp] theorem segHom_one {n : ℕ} (ψ : C(IC n, IC (n + 1))) (v : IC (n + 1)) (u : IC n) :
    segHom ψ v (u, 1) = v := segPt_one _ _

theorem segHom_eq_of_eq {n : ℕ} (ψ : C(IC n, IC (n + 1))) (v : IC (n + 1)) (u : IC n)
    (h : ψ u = v) (t : unitInterval) : segHom ψ v (u, t) = v := by
  rw [segHom_apply, h, segPt_self]

/-- **The cancellation half of the homotopy addition theorem.**  If `ψ : I^k → I^{k+1}` is
continuous and constant on `∂I^k` with value `v`, and `g v = x₀`, then the based cube `g ∘ ψ` is
null-homotopic. -/
theorem homotopic_const_of_comp_eqOn_boundary (k : ℕ) [NeZero k] {X : Type} [TopologicalSpace X]
    {x₀ : X} (g : C(IC (k + 1), X)) (ψ : C(IC k, IC (k + 1))) (v : IC (k + 1))
    (hψ : ∀ u ∈ Cube.boundary (Fin k), ψ u = v) (hg : g v = x₀) :
    GenLoop.Homotopic (⟨g.comp ψ, fun u hu => by rw [ContinuousMap.comp_apply, hψ u hu, hg]⟩ :
      GenLoop (Fin k) X x₀) GenLoop.const := by
  refine Work.Stems.Hur2b.homotopic_const_of_boundary_const (n := k)
    (p := ⟨g.comp ψ, fun u hu => by rw [ContinuousMap.comp_apply, hψ u hu, hg]⟩)
    (z := x₀) (H := g.comp (segHom ψ v)) ?_ ?_ ?_
  · intro u
    rw [ContinuousMap.comp_apply, segHom_zero]
    rfl
  · intro u
    rw [ContinuousMap.comp_apply, segHom_one, hg]
  · intro y y' t hy hy'
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply,
      segHom_eq_of_eq ψ v y (hψ y hy) t, segHom_eq_of_eq ψ v y' (hψ y' hy') t]

/-- **The cancellation half, in the homotopy group.** -/
theorem cl_comp_collapse_eq_one (k : ℕ) [NeZero k] [Nontrivial (Fin k)] {X : Type}
    [TopologicalSpace X] {x₀ : X} (g : C(IC (k + 1), X)) (ψ : C(IC k, IC (k + 1)))
    (v : IC (k + 1)) (hψ : ∀ u ∈ Cube.boundary (Fin k), ψ u = v) (hg : g v = x₀) :
    (show HomotopyGroup (Fin k) X x₀ from
        Quotient.mk _ ⟨g.comp ψ, fun u hu => by rw [ContinuousMap.comp_apply, hψ u hu, hg]⟩) = 1 := by
  rw [HomotopyGroup.one_def]
  exact Quotient.sound (homotopic_const_of_comp_eqOn_boundary k g ψ v hψ hg)

end

end Work.RatHurewicz
