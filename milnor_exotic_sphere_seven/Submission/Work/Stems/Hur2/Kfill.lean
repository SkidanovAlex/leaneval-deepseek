import Submission.Work.Stems.Hur2.SquareFaces

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chain homotopy `K`: paths to the base point, and the square filling an edge

Hutchings' construction (`_ztmp_hur/hutch.txt` §2) attaches to each `i`-cube `σ : I^i → X` with
`i < k` an `(i+1)`-cube `K(σ)` whose faces are `x₀`, `σ` and the faces of `K(∂σ)`.  In degree two
only the first two steps are needed at the chain level:

* `K₀ v` — a path from the base point `x₀` to `v`, with `K₀ x₀ = const`,
* `K₁ e` — the square filling an edge `e : I¹ → X`, with faces
  `x₀`, `K₀ (e 0)`, `e`, `K₀ (e 1)`, and **constant on the constant cube at `x₀`** (this is
  condition `(*)` of Hutchings, and it is what makes `Ψ` a section of the Hurewicz map on based
  cubes).
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The (unique) point of `I¹` with coordinate `u`. -/
def iota (u : unitInterval) : IC 1 := fun _ => u

theorem continuous_iota : Continuous (iota : unitInterval → IC 1) :=
  continuous_pi fun _ => continuous_id

/-- `iota` as a continuous map. -/
def iotaCM : C(unitInterval, IC 1) := ⟨iota, continuous_iota⟩

@[simp] theorem iotaCM_apply (u : unitInterval) : iotaCM u = iota u := rfl

@[simp] theorem iota_coe_zero : (iota (0 : unitInterval) : IC 1) = 0 := rfl

@[simp] theorem iota_coe_one : (iota (1 : unitInterval) : IC 1) = 1 := rfl

@[simp] theorem iota_eq (t : IC 1) : iota (t 0) = t := by
  funext j
  fin_cases j
  rfl

/-- **A chosen path from `x₀` to `v`**, constant when `v = x₀`. -/
def K₀ (x₀ : X) [PathConnectedSpace X] (v : X) : Path x₀ v := by
  classical
  exact if h : v = x₀ then
    { toFun := fun _ => x₀, continuous_toFun := continuous_const, source' := rfl,
      target' := h.symm }
  else PathConnectedSpace.somePath x₀ v

theorem K₀_self (x₀ : X) [PathConnectedSpace X] : K₀ x₀ x₀ = Path.refl x₀ := by
  classical
  unfold K₀
  rw [dif_pos rfl]
  ext t
  rfl

/-- The path underlying a 1-cube. -/
def edgePath (e : C(IC 1, X)) : Path (e 0) (e 1) where
  toFun := fun u => e (iota u)
  continuous_toFun := e.continuous.comp continuous_iota
  source' := rfl
  target' := rfl

@[simp] theorem edgePath_apply (e : C(IC 1, X)) (u : unitInterval) :
    edgePath e u = e (iota u) := rfl

/-- **The square filling an edge** `e`, with faces `x₀`, `K₀ (e 0)`, `e`, `K₀ (e 1)`; constant
when `e` is the constant cube at `x₀`. -/
def K₁ (x₀ : X) [SimplyConnectedSpace X] (e : C(IC 1, X)) : C(IC 2, X) := by
  classical
  exact if _h : e = ContinuousMap.const (IC 1) x₀ then ContinuousMap.const (IC 2) x₀
  else Classical.choose (square_filling (K₀ x₀ (e 0)) (edgePath e) (K₀ x₀ (e 1)))

theorem K₁_const (x₀ : X) [SimplyConnectedSpace X] :
    K₁ x₀ (ContinuousMap.const (IC 1) x₀) = ContinuousMap.const (IC 2) x₀ := by
  classical
  unfold K₁
  rw [dif_pos rfl]

/-- The four faces of `K₁ e` in the non-constant case. -/
theorem K₁_face (x₀ : X) [SimplyConnectedSpace X] (e : C(IC 1, X))
    (h : e ≠ ContinuousMap.const (IC 1) x₀) :
    (∀ t : IC 1, K₁ x₀ e (faceCM (0 : Fin 2) (0 : unitInterval) t) = x₀) ∧
    (∀ t : IC 1, K₁ x₀ e (faceCM (1 : Fin 2) (0 : unitInterval) t) = K₀ x₀ (e 0) (t 0)) ∧
    (∀ t : IC 1, K₁ x₀ e (faceCM (0 : Fin 2) (1 : unitInterval) t) = e t) ∧
    (∀ t : IC 1, K₁ x₀ e (faceCM (1 : Fin 2) (1 : unitInterval) t) = K₀ x₀ (e 1) (t 0)) := by
  classical
  unfold K₁
  rw [dif_neg h]
  obtain ⟨h1, h2, h3, h4⟩ :=
    Classical.choose_spec (square_filling (K₀ x₀ (e 0)) (edgePath e) (K₀ x₀ (e 1)))
  exact ⟨h1, h2, fun t => by simpa only [edgePath_apply, iota_eq] using h3 t, h4⟩

/-- The four faces of `K₁ e` in all cases (the constant case is absorbed by `K₁_const`). -/
theorem K₁_face_00 (x₀ : X) [SimplyConnectedSpace X] (e : C(IC 1, X)) (t : IC 1) :
    K₁ x₀ e (faceCM (0 : Fin 2) (0 : unitInterval) t) = x₀ := by
  by_cases h : e = ContinuousMap.const (IC 1) x₀
  · rw [h, K₁_const]
    rfl
  · exact (K₁_face x₀ e h).1 t

theorem K₁_face_10 (x₀ : X) [SimplyConnectedSpace X] (e : C(IC 1, X)) (t : IC 1) :
    K₁ x₀ e (faceCM (1 : Fin 2) (0 : unitInterval) t) = K₀ x₀ (e 0) (t 0) := by
  by_cases h : e = ContinuousMap.const (IC 1) x₀
  · rw [h, K₁_const]
    simp only [ContinuousMap.const_apply, K₀_self]
    exact (Path.refl_apply x₀ (t 0)).symm
  · exact (K₁_face x₀ e h).2.1 t

theorem K₁_face_01 (x₀ : X) [SimplyConnectedSpace X] (e : C(IC 1, X)) (t : IC 1) :
    K₁ x₀ e (faceCM (0 : Fin 2) (1 : unitInterval) t) = e t := by
  by_cases h : e = ContinuousMap.const (IC 1) x₀
  · rw [h, K₁_const]
    rfl
  · exact (K₁_face x₀ e h).2.2.1 t

theorem K₁_face_11 (x₀ : X) [SimplyConnectedSpace X] (e : C(IC 1, X)) (t : IC 1) :
    K₁ x₀ e (faceCM (1 : Fin 2) (1 : unitInterval) t) = K₀ x₀ (e 1) (t 0) := by
  by_cases h : e = ContinuousMap.const (IC 1) x₀
  · rw [h, K₁_const]
    simp only [ContinuousMap.const_apply, K₀_self]
    exact (Path.refl_apply x₀ (t 0)).symm
  · exact (K₁_face x₀ e h).2.2.2 t

end

end Work.Stems.Hur2
