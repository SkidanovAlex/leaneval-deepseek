import Mathlib
import Submission.Work.Conn.Basic

namespace Work.Conn.HomotopyInvariance

open ContinuousMap

/-- A map homotopic to a null-homotopic map is null-homotopic. -/
theorem Nullhomotopic.of_homotopic {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f.Homotopic g) (hg : g.Nullhomotopic) : f.Nullhomotopic := by
  obtain ⟨y, hy⟩ := hg
  exact ⟨y, h.trans hy⟩

/-- Null-homotopy is invariant under homotopy of maps. -/
theorem Homotopic.nullhomotopic_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f.Homotopic g) : f.Nullhomotopic ↔ g.Nullhomotopic :=
  ⟨fun hf => Nullhomotopic.of_homotopic h.symm hf, fun hg => Nullhomotopic.of_homotopic h hg⟩

/-- Null-homotopy is a homotopy invariant: for a homotopy equivalence `e : X ≃ₕ Y` and any
space `Z`, a map `f : C(Z, X)` is null-homotopic if and only if `e ∘ f` is.

Route: if `e.toFun ∘ f` is null-homotopic then so is `e.invFun ∘ (e.toFun ∘ f)`
(`ContinuousMap.Nullhomotopic.comp_right`), and `e.invFun ∘ e.toFun` is homotopic to the identity
(`HomotopyEquiv.left_inv`), so `e.invFun ∘ (e.toFun ∘ f)` is homotopic to `f`; conversely use
`e.toFun` and `HomotopyEquiv.right_inv`. -/
theorem nullhomotopic_iff_of_homotopyEquiv {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (e : X ≃ₕ Y) (f : C(Z, X)) :
    f.Nullhomotopic ↔ (e.toFun.comp f).Nullhomotopic := by
  constructor
  · intro hf
    exact hf.comp_right e.toFun
  · intro hf
    -- `e.invFun ∘ (e.toFun ∘ f)` is null-homotopic
    have hcomp : (e.invFun.comp (e.toFun.comp f)).Nullhomotopic := hf.comp_right e.invFun
    -- and it is homotopic to `f`
    have hHom : (e.invFun.comp (e.toFun.comp f)).Homotopic f := by
      have h := e.left_inv.comp (Homotopic.refl f)
      rwa [comp_assoc, id_comp] at h
    exact (Homotopic.nullhomotopic_iff hHom).mp hcomp

end Work.Conn.HomotopyInvariance
