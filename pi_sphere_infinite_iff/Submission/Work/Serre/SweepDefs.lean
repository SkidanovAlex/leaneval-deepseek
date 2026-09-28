import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.exists_lift_rel

/-!
# The "three faces" lifting property (the sweep)

`Work.Serre.Sweep Z p` is the statement that for a Serre fibration `p : E → B` and a test space
`Z`, every lift of a base map `H : Z × I × I → B` which is prescribed on the union of the three
faces `{s = 0}`, `{t = 0}`, `{t = 1}` of the "prism" `Z × I_s × I_t` extends to a lift of `H`.

This is the combinatorial core of `Work.Serre.homotopicLiftsOfJoinedFibre`: the prism
`Δⁿ × I` is a cone (from a point `v` of the simplex) over `∂Δⁿ × I`, and the sweep is applied to
the test space `∂Δⁿ`.

The two instances used are `Z = Fin m → I` (the cube) and `Z = ↥(Cube.boundary (Fin m))`:
`Work.Serre.sweepCube` / `Work.Serre.sweepBdry` (in the sibling file) prove them by an induction on
`m`, using
* `Work.StemsB.exists_lift_rel` (the relative homotopy lifting property for cube prisms), and
* `Work.RatHurewicz.domePt` (the "dome" parametrisation `I^{m-1} ≅ ∂I^m ∖ int (bottom face)`).
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- **The "three faces" lifting property.**  For a Serre fibration `p : E → B` and a test space
`Z`, every lift of a base map `H : Z × I × I → B` on the union of the faces `{s = 0}`, `{t = 0}`
and `{t = 1}` (with the obvious compatibility on the corners) extends to a lift of `H`. -/
def Sweep (Z : Type) [TopologicalSpace Z] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) : Prop :=
  ∀ (H : C(Z × unitInterval × unitInterval, B))
    (f₀ : C(Z × unitInterval, E))
    (_h₀ : p.comp f₀ = H.comp ⟨fun x : Z × unitInterval => (x.1, 0, x.2), by fun_prop⟩)
    (f₁ : C(Z × unitInterval, E))
    (_h₁ : p.comp f₁ = H.comp ⟨fun x : Z × unitInterval => (x.1, x.2, 0), by fun_prop⟩)
    (f₂ : C(Z × unitInterval, E))
    (_h₂ : p.comp f₂ = H.comp ⟨fun x : Z × unitInterval => (x.1, x.2, 1), by fun_prop⟩)
    (_c₀ : ∀ z : Z, f₀ (z, 0) = f₁ (z, 0))
    (_c₁ : ∀ z : Z, f₀ (z, 1) = f₂ (z, 0)),
    ∃ G : C(Z × unitInterval × unitInterval, E), p.comp G = H ∧
      (∀ z : Z, ∀ t : unitInterval, G (z, 0, t) = f₀ (z, t)) ∧
      (∀ z : Z, ∀ s : unitInterval, G (z, s, 0) = f₁ (z, s)) ∧
      (∀ z : Z, ∀ s : unitInterval, G (z, s, 1) = f₂ (z, s))

/-- `Sweep` is invariant under homeomorphism of the test space (contravariantly). -/
theorem Sweep.of_homeomorph {Z Z' : Type} [TopologicalSpace Z] [TopologicalSpace Z']
    {E B : Type} [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)}
    (e : Z' ≃ₜ Z) (h : Sweep Z E B p) : Sweep Z' E B p := by
  intro H f₀ h₀ f₁ h₁ f₂ h₂ c₀ c₁
  let ee : C(Z × unitInterval × unitInterval, Z' × unitInterval × unitInterval) :=
    ⟨fun x => (e.symm x.1, x.2), (e.symm.continuous.comp continuous_fst).prodMk continuous_snd⟩
  let e2 : C(Z × unitInterval, Z' × unitInterval) :=
    ⟨fun y => (e.symm y.1, y.2), (e.symm.continuous.comp continuous_fst).prodMk continuous_snd⟩
  have h2 : ∀ (z : Z) (s : unitInterval), e2 (z, s) = (e.symm z, s) := fun z s => rfl
  obtain ⟨G, hG, hG₀, hG₁, hG₂⟩ := h (H.comp ee)
    (f₀.comp e2)
    (by ext y; exact congrFun (congrArg DFunLike.coe h₀) (e.symm y.1, y.2))
    (f₁.comp e2)
    (by ext y; exact congrFun (congrArg DFunLike.coe h₁) (e.symm y.1, y.2))
    (f₂.comp e2)
    (by ext y; exact congrFun (congrArg DFunLike.coe h₂) (e.symm y.1, y.2))
    (fun z => c₀ (e.symm z)) (fun z => c₁ (e.symm z))
  let G' : C(Z' × unitInterval × unitInterval, E) :=
    ⟨fun x => G (e x.1, x.2), G.continuous.comp
      ((e.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  refine ⟨G', ?_, ?_, ?_, ?_⟩
  · ext x
    show p (G (e x.1, x.2)) = H x
    have h1 : p (G (e x.1, x.2)) = (H.comp ee) (e x.1, x.2.1, x.2.2) :=
      congrFun (congrArg DFunLike.coe hG) (e x.1, x.2.1, x.2.2)
    rw [h1]
    show H (e.symm (e x.1), x.2.1, x.2.2) = H x
    rw [e.symm_apply_apply]
  · intro z t
    show G (e z, 0, t) = f₀ (z, t)
    rw [hG₀ (e z) t]
    show f₀ (e.symm (e z), t) = f₀ (z, t)
    rw [e.symm_apply_apply]
  · intro z s
    show G (e z, s, 0) = f₁ (z, s)
    rw [hG₁ (e z) s]
    show f₁ (e.symm (e z), s) = f₁ (z, s)
    rw [e.symm_apply_apply]
  · intro z s
    show G (e z, s, 1) = f₂ (z, s)
    rw [hG₂ (e z) s]
    show f₂ (e.symm (e z), s) = f₂ (z, s)
    rw [e.symm_apply_apply]

end

end Work.Serre
