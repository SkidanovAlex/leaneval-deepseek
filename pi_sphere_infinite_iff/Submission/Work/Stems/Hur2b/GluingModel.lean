import Mathlib
import Submission.Work.Stems.Hur2b.Gluing3
import Submission.Work.Stems.Hur2b.GluingCancel
import Submission.Work.Stems.Hur2b.Assembly
import Submission.Work.Stems.Hur2b.homotopic_const_of_boundary_const

/-!
# Cube models of the gluing of `∂I³`, and their nullity

`gluingMap x₀ τ : Bdy3 → X` (Gluing3.lean) is `x₀` on the 1-skeleton of `∂I³`.  Any continuous
`ψ : I² → ∂I³` whose boundary is collapsed to the vertex `v = (0,0,0)` therefore gives a *based
cube* `G ∘ ψ`.

If moreover `Φ : Bdy3 × I → X` is a family with `Φ(·,0) = G` and `Φ(·,1)` constant (the
"cancellation family" of Hutchings' proof of `(2.5)`), then the cube `G ∘ ψ` is null as a *based*
cube: the family `H(y,t) := Φ(ψ y, t)` has all its slices constant on `∂I²` (because `ψ(∂I²)` is the
single point `v`), starts at `G ∘ ψ` and ends at the constant `z`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- The vertex `(0,0,0)` of `I³`, viewed as a point of the boundary `∂I³`. -/
def vertexBdy3 : Bdy3 := ⟨0, by refine ⟨0, Or.inl ?_⟩; simp⟩

/-- The gluing is `x₀` at the vertex `(0,0,0)`. -/
theorem gluingMap_vertexBdy3 (x₀ : X) (τ : C(IC 3, X)) :
    gluingMap x₀ τ vertexBdy3 = x₀ :=
  gluingMap_eq_x₀_of_mem_two x₀ τ (i := 0) (i' := 1) (b := 0) (b' := 0)
    (by show (0 : IC 3) 0 = bval 0; simp [bval])
    (by show (0 : IC 3) 1 = bval 0; simp [bval]) (by decide)

/-- **The cube model of the gluing along a `ψ` with `ψ(∂I²) = {v}`.** -/
def model (x₀ : X) (τ : C(IC 3, X)) (ψ : C(IC 2, Bdy3))
    (hψ : ∀ y ∈ Cube.boundary (Fin 2), ψ y = vertexBdy3) : GenLoop (Fin 2) X x₀ :=
  ⟨(gluingMap x₀ τ).comp ψ, fun y hy => by
    rw [ContinuousMap.comp_apply, hψ y hy, gluingMap_vertexBdy3]⟩

@[simp] theorem model_apply (x₀ : X) (τ : C(IC 3, X)) (ψ : C(IC 2, Bdy3))
    (hψ : ∀ y ∈ Cube.boundary (Fin 2), ψ y = vertexBdy3) (y : IC 2) :
    (model x₀ τ ψ hψ).1 y = gluingMap x₀ τ (ψ y) := rfl

/-- **The model is null, given a cancellation family for the gluing.** -/
theorem model_homotopic_const (x₀ : X) (τ : C(IC 3, X)) (ψ : C(IC 2, Bdy3))
    (hψ : ∀ y ∈ Cube.boundary (Fin 2), ψ y = vertexBdy3)
    (Φ : C(Bdy3 × unitInterval, X))
    (h0 : ∀ p, Φ (p, 0) = gluingMap x₀ τ p) (z : X) (h1 : ∀ p, Φ (p, 1) = z) :
    GenLoop.Homotopic (model x₀ τ ψ hψ) GenLoop.const := by
  refine homotopic_const_of_boundary_const 2 (x₀ := x₀) (p := model x₀ τ ψ hψ) z
    ⟨fun q => Φ (ψ q.1, q.2), ?_⟩ ?_ ?_ ?_
  · exact Φ.continuous.comp ((ψ.continuous.comp continuous_fst).prodMk continuous_snd)
  · intro y
    show Φ (ψ y, 0) = gluingMap x₀ τ (ψ y)
    rw [h0]
  · intro y
    show Φ (ψ y, 1) = z
    rw [h1]
  · intro y y' t hy hy'
    show Φ (ψ y, t) = Φ (ψ y', t)
    rw [hψ y hy, hψ y' hy']

/-- The class of the model. -/
theorem model_class (x₀ : X) (τ : C(IC 3, X)) (ψ : C(IC 2, Bdy3))
    (hψ : ∀ y ∈ Cube.boundary (Fin 2), ψ y = vertexBdy3) :
    cl x₀ (model x₀ τ ψ hψ) = ⟦model x₀ τ ψ hψ⟧ := rfl

/-- **The class of the model is `1`, given a cancellation family.** -/
theorem model_class_eq_one (x₀ : X) (τ : C(IC 3, X)) (ψ : C(IC 2, Bdy3))
    (hψ : ∀ y ∈ Cube.boundary (Fin 2), ψ y = vertexBdy3)
    (Φ : C(Bdy3 × unitInterval, X))
    (h0 : ∀ p, Φ (p, 0) = gluingMap x₀ τ p) (z : X) (h1 : ∀ p, Φ (p, 1) = z) :
    cl x₀ (model x₀ τ ψ hψ) = 1 :=
  Quotient.sound (model_homotopic_const x₀ τ ψ hψ Φ h0 z h1)

/-- **The model is null**, with the cancellation family `gluingCancelFamily` supplied explicitly. -/
theorem model_homotopic_const' (x₀ : X) (τ : C(IC 3, X)) (ψ : C(IC 2, Bdy3))
    (hψ : ∀ y ∈ Cube.boundary (Fin 2), ψ y = vertexBdy3) :
    GenLoop.Homotopic (model x₀ τ ψ hψ) GenLoop.const :=
  model_homotopic_const x₀ τ ψ hψ (gluingCancelFamily x₀ τ)
    (gluingCancelFamily_zero x₀ τ) (τ 0) (gluingCancelFamily_one x₀ τ)

/-- The class of the model is `1`. -/
theorem model_class_eq_one' (x₀ : X) (τ : C(IC 3, X)) (ψ : C(IC 2, Bdy3))
    (hψ : ∀ y ∈ Cube.boundary (Fin 2), ψ y = vertexBdy3) :
    cl x₀ (model x₀ τ ψ hψ) = 1 :=
  Quotient.sound (model_homotopic_const' x₀ τ ψ hψ)

end

end Work.Stems.Hur2b
