import Mathlib
import Submission.Work.Stems.Hur2.Kfill

/-!
# The square filling an edge retracts onto its `e`-edge, relatively

Hutchings' `K₁ e` (`Submission/Work/Stems/Hur2/Kfill.lean`) is the square filling an edge `e`, with
faces `x₀`, `K₀ (e 0)`, `e`, `K₀ (e 1)`.  Here we record that the square deformation retracts onto
the `e`-face `{t₀ = 1}` *while fixing that face*.  The explicit homotopy is
`(τ, t) ↦ K₁ e ((1-τ)·t₀ + τ, t₁)`; at `τ = 1` it is the edge `e` read in the second coordinate,
and it is constant on `{t₀ = 1}`.

This is the ("cancellation") ingredient of Hutchings' proof that the filling `Ψ` of a `3`-cube has
trivial class: each fill `K₁ e` can be pushed back onto its `e`-edge, fixing that edge.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.Stems.Hur2b

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The edge `e` read in the second coordinate of the square. -/
def edgeCube (e : ContinuousMap (IC 1) X) : ContinuousMap (IC 2) X :=
  e.comp ⟨fun t => fun _ => t 1, by continuity⟩

/-- The `e`-face `{t₀ = 1}` of the square. -/
def edgeFace : Set (IC 2) := {t | t 0 = 1}

theorem edgeCube_apply (e : ContinuousMap (IC 1) X) (t : IC 2) :
    edgeCube e t = e (fun _ => t 1) := rfl

theorem coe_zero_I : ((0 : unitInterval) : ℝ) = 0 := rfl

theorem coe_one_I : ((1 : unitInterval) : ℝ) = 1 := rfl

/-- The interpolated first coordinate `(1-τ)·a + τ`. -/
def interp (τ a : unitInterval) : unitInterval :=
  Set.projIcc (0 : ℝ) 1 zero_le_one ((1 - (τ : ℝ)) * (a : ℝ) + (τ : ℝ))

theorem interp_coe {τ a : unitInterval}
    (h : (1 - (τ : ℝ)) * (a : ℝ) + (τ : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    (interp τ a : ℝ) = (1 - (τ : ℝ)) * (a : ℝ) + (τ : ℝ) := by
  rw [interp, Set.projIcc_of_mem _ h]

theorem interp_zero (a : unitInterval) : interp 0 a = a := by
  apply Subtype.ext
  have h : (1 - ((0 : unitInterval) : ℝ)) * (a : ℝ) + ((0 : unitInterval) : ℝ) ∈
      Set.Icc (0:ℝ) 1 := by
    rw [coe_zero_I]; constructor <;> nlinarith [a.2.1, a.2.2]
  rw [interp_coe h, coe_zero_I]; ring

theorem interp_one (a : unitInterval) : interp 1 a = 1 := by
  apply Subtype.ext
  have h : (1 - ((1 : unitInterval) : ℝ)) * (a : ℝ) + ((1 : unitInterval) : ℝ) ∈
      Set.Icc (0:ℝ) 1 := by
    rw [coe_one_I]; constructor <;> nlinarith [a.2.1, a.2.2]
  rw [interp_coe h, coe_one_I]; ring

theorem interp_of_eq_one {τ a : unitInterval} (ha : a = 1) : interp τ a = 1 := by
  subst ha
  apply Subtype.ext
  have h : (1 - (τ : ℝ)) * ((1 : unitInterval) : ℝ) + (τ : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
    rw [coe_one_I]; constructor <;> nlinarith [τ.2.1, τ.2.2]
  rw [interp_coe h, coe_one_I]; ring

theorem continuous_interp :
    Continuous fun z : unitInterval × IC 2 => interp z.1 (z.2 0) := by
  rw [show (fun z : unitInterval × IC 2 => interp z.1 (z.2 0)) =
      (fun z => Set.projIcc (0:ℝ) 1 zero_le_one
        ((1 - (z.1 : ℝ)) * ((z.2 0 : unitInterval) : ℝ) + (z.1 : ℝ))) from rfl]
  exact (continuous_projIcc).comp (by fun_prop)

theorem faceCM_eq_insertNth {n : ℕ} (i : Fin (n+1)) (b : unitInterval) (u : IC n) :
    faceCM i b u = (i.insertNth b u : IC (n+1)) := rfl

/-- The point `(t₀, t₁)` is `t`. -/
theorem faceCM_zero_eq (t : IC 2) :
    faceCM (0 : Fin 2) (t 0) (fun _ : Fin 1 => t 1) = t := by
  funext j
  fin_cases j <;> simp [faceCM_apply, faceFun_apply]

theorem faceCM_zero_one_eq {t : IC 2} (ht : t 0 = 1) :
    faceCM (0 : Fin 2) (1 : unitInterval) (fun _ : Fin 1 => t 1) = t := by
  rw [← ht]; exact faceCM_zero_eq t

/-- **The cancellation**: the square `K₁ e` retracts onto its `e`-edge, fixing that edge. -/
theorem K1_homotopicRel_edge (x₀ : X) [SimplyConnectedSpace X] (e : ContinuousMap (IC 1) X) :
    ContinuousMap.HomotopicRel (Work.Stems.Hur2.K₁ x₀ e) (edgeCube e) edgeFace := by
  refine ⟨⟨⟨fun z => Work.Stems.Hur2.K₁ x₀ e
      (faceCM (0 : Fin 2) (interp z.1 (z.2 0)) (fun _ : Fin 1 => (z.2) 1)), ?_⟩, ?_, ?_⟩, ?_⟩
  · have hK : Continuous fun z : unitInterval × IC 2 =>
        @Fin.insertNth 1 (fun _ => unitInterval) 0 (interp z.1 (z.2 0))
          (fun _ : Fin 1 => z.2 1) :=
      Continuous.finInsertNth (n := 1) (A := fun _ : Fin 2 => unitInterval) (0 : Fin 2)
        (f := fun z : unitInterval × IC 2 => interp z.1 (z.2 0))
        (g := fun z : unitInterval × IC 2 => fun _ : Fin 1 => z.2 1)
        continuous_interp
        (continuous_pi fun _ : Fin 1 => (continuous_apply (1 : Fin 2)).comp continuous_snd)
    have hK' : Continuous fun z : unitInterval × IC 2 =>
        faceCM (0 : Fin 2) (interp z.1 (z.2 0)) (fun _ : Fin 1 => z.2 1) :=
      hK.congr fun z =>
        (faceCM_eq_insertNth (0 : Fin 2) (interp z.1 (z.2 0)) (fun _ : Fin 1 => z.2 1)).symm
    exact (Work.Stems.Hur2.K₁ x₀ e).continuous.comp hK'
  · intro t
    change (Work.Stems.Hur2.K₁ x₀ e) (faceCM (0 : Fin 2) (interp (0 : unitInterval) (t 0))
      (fun _ : Fin 1 => t 1)) = (Work.Stems.Hur2.K₁ x₀ e) t
    rw [interp_zero (t 0), faceCM_zero_eq t]
  · intro t
    change (Work.Stems.Hur2.K₁ x₀ e) (faceCM (0 : Fin 2) (interp (1 : unitInterval) (t 0))
      (fun _ : Fin 1 => t 1)) = edgeCube e t
    rw [interp_one (t 0), edgeCube_apply]
    exact Work.Stems.Hur2.K₁_face_01 x₀ e (fun _ : Fin 1 => t 1)
  · intro τ t ht
    change (Work.Stems.Hur2.K₁ x₀ e) (faceCM (0 : Fin 2) (interp τ (t 0))
      (fun _ : Fin 1 => t 1)) = (Work.Stems.Hur2.K₁ x₀ e) t
    have h : interp τ (t 0) = (1 : unitInterval) := by
      rw [show t 0 = (1 : unitInterval) from ht]
      exact interp_of_eq_one rfl
    rw [h, faceCM_zero_one_eq ht]

end

end Work.Stems.Hur2b
