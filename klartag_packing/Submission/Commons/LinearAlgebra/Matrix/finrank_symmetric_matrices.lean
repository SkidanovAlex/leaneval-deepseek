import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Symmetric

namespace Commons.LinearAlgebra.Matrix

/-- The submodule of symmetric matrices over `ℝ`. -/
noncomputable def symmSubmodule (d : ℕ) : Submodule ℝ (_root_.Matrix (Fin d) (Fin d) ℝ) where
  carrier := {A | A.IsSymm}
  zero_mem' := _root_.Matrix.isSymm_zero
  add_mem' := fun {_ _} hA hB => hA.add hB
  smul_mem' := fun c _ hA => hA.smul c

/-- Evaluation of a function on unordered pairs as a symmetric matrix. -/
noncomputable def symmToFun (d : ℕ) :
    (Sym2 (Fin d) → ℝ) →ₗ[ℝ] _root_.Matrix (Fin d) (Fin d) ℝ where
  toFun f := fun i j => f (Sym2.mk i j)
  map_add' f g := by ext i j; rfl
  map_smul' c f := by ext i j; rfl

lemma range_symmToFun (d : ℕ) :
    LinearMap.range (symmToFun d) = symmSubmodule d := by
  apply le_antisymm
  · rintro A ⟨f, rfl⟩
    show ((symmToFun d) f).IsSymm
    rw [_root_.Matrix.IsSymm.ext_iff]
    intro i j
    exact congr_arg f (Sym2.eq_swap (a := j) (b := i))
  · intro A hA
    refine ⟨Sym2.lift ⟨fun i j => A i j, ?_⟩, ?_⟩
    · intro a b
      exact (hA.apply a b).symm
    · ext i j
      change Sym2.lift ⟨fun i j => A i j, fun a b => (hA.apply a b).symm⟩ (Sym2.mk i j) = A i j
      rw [Sym2.lift_mk]

lemma span_eq_symmSubmodule (d : ℕ) :
    Submodule.span ℝ {A : _root_.Matrix (Fin d) (Fin d) ℝ | A.IsSymm} = symmSubmodule d := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro A hA
    exact hA
  · intro A hA
    exact Submodule.subset_span hA

theorem finrank_symmetric_matrices (d : ℕ) :
    Module.finrank ℝ (Submodule.span ℝ {A : Matrix (Fin d) (Fin d) ℝ | A.IsSymm})
      = d * (d + 1) / 2 := by
  rw [span_eq_symmSubmodule, ← range_symmToFun]
  rw [LinearMap.finrank_range_of_inj (f := symmToFun d) ?_]
  · rw [Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin,
        Nat.choose_two_right, Nat.add_sub_cancel]
    rw [Nat.mul_comm (d + 1) d]
  · intro f g hfg
    funext s
    induction s using Sym2.ind with
    | h i j => exact congrFun (congrFun hfg i) j

end Commons.LinearAlgebra.Matrix