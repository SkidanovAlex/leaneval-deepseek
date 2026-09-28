import Mathlib
import Submission.Work.ThomBordism.TwoSet.CompressBasic
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv

/-!
# Auxiliary facts about the trace of `U` in `V`

`{v : ↥V | (v : X) ∈ U}` is canonically homeomorphic to `↥(U ∩ V)` (`traceHomeo`), and the
triviality of homotopy groups transports along a homeomorphism
(`subsingleton_of_homeomorph`).
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

/-- The homeomorphism between the trace of `U` inside `↥V` and `↥(U ∩ V)`. -/
def traceHomeo {X : Type*} [TopologicalSpace X] {U V : Set X} :
    {w : ↥V // (w : X) ∈ U} ≃ₜ ↥(U ∩ V) where
  toFun w := ⟨w.1.1, ⟨w.2, w.1.2⟩⟩
  invFun z := ⟨⟨z.1, z.2.2⟩, z.2.1⟩
  left_inv w := by ext; rfl
  right_inv z := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **Transport of the triviality of a homotopy group along a homeomorphism.**
(`N` must be nonempty; the `N = Fin 0` case is the separate statement about `π₀`.) -/
theorem subsingleton_of_homeomorph {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {a : A} {b : B} (hab : e a = b)
    (N : Type*) [DecidableEq N] [Nonempty N]
    (h : Subsingleton (HomotopyGroup N B b)) : Subsingleton (HomotopyGroup N A a) := by
  obtain ⟨me⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := N) (X := A) (Y := B)
    e.toHomotopyEquiv a
  have h' : Subsingleton (HomotopyGroup N B (e.toHomotopyEquiv a)) := by
    have : e.toHomotopyEquiv a = b := by
      rw [Homeomorph.coe_toHomotopyEquiv]
      exact hab
    rw [this]
    exact h
  haveI := h'
  exact ⟨fun x y => me.injective (Subsingleton.elim (me x) (me y))⟩

end Work.ThomBordism.TwoSet
