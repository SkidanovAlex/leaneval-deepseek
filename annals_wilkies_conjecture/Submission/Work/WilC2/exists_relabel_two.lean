import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.definable_fin_params
import Submission.Work.WilC2.meetsDefinable_dcl
import Submission.Work.WilC2.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

/-- **Separating the parameter `b` into a variable.**  If the singleton `{a}` is definable over the
parameter set `insert b T`, then there is an `LRc`-formula `Ψ` in the variables `Fin n ⊕ Fin 2`
(`n` parameters, one free variable `y` standing for the parameter `b`, and one free variable `x`
for the point) whose parameters `c` all lie in `T`, such that the fibre at `y = b` is exactly
`{a}`. -/
theorem exists_relabel_two {M : Type} [WilkiesDesign.CG.LRc.Structure M] {T : Set M} {a b : M}
    (h : (insert b T).Definable WilkiesDesign.CG.LRc {v : Fin 1 → M | v 0 ∈ ({a} : Set M)}) :
    ∃ (n : ℕ) (Ψ : WilkiesDesign.CG.LRc.Formula (Fin n ⊕ Fin 2)) (c : Fin n → M),
      (∀ i, c i ∈ T) ∧ ∀ x : M, Ψ.Realize (Sum.elim c ![b, x]) ↔ x = a := by
  classical
  -- Express the definability of `{a}` over `insert b T` by an explicit formula with parameters.
  obtain ⟨φ, hφ⟩ := (Set.definable_iff_exists_formula_sum (A := insert b T)
    (L := LRc) (α := Fin 1) (s := {v : Fin 1 → M | v 0 ∈ ({a} : Set M)})).mp h
  have hφ' : ∀ x : M, φ.Realize (Sum.elim (Subtype.val : ↥(insert b T) → M) ![x]) ↔ x = a := by
    intro x
    have hx := Set.ext_iff.mp hφ ![x]
    exact hx.symm
  -- Split the parameter block: the element `b` of `insert b T` is sent to a fresh variable,
  -- the remaining parameters (which all lie in `T`) to a block indexed by `↥T`.
  let f : (↥(insert b T) ⊕ Fin 1) → (↥T ⊕ Fin 2) :=
    Sum.elim (fun p => if hp : (p : M) = b then Sum.inr 0
        else Sum.inl (⟨(p : M), by
          rcases Set.mem_insert_iff.mp p.property with hb | hT
          · exact absurd hb hp
          · exact hT⟩ : ↥T))
      (fun _ : Fin 1 => Sum.inr 1)
  -- The relabelled assignment carries the value `b` on the new `y`-variable and `x` on `x`.
  have hcomp : ∀ x : M, Sum.elim (Subtype.val : ↥(insert b T) → M) ![x]
      = (Sum.elim (fun t : ↥T => (t : M)) ![b, x]) ∘ f := by
    intro x
    funext y
    rcases y with p | i
    · by_cases hp : (p : M) = b
      · simp [f, hp]
      · simp [f, hp]
    · fin_cases i
      simp [f, Function.comp_apply]
  have h2 : ∀ x : M,
      (φ.relabel f).Realize (Sum.elim (fun t : ↥T => (t : M)) ![b, x]) ↔ x = a := by
    intro x
    rw [Formula.realize_relabel, ← hcomp x]
    exact hφ' x
  -- Only finitely many elements of `T` are actually used: compress the parameter block.
  obtain ⟨n, σ, ψ, hψ⟩ := exists_fin_relabel_elim (L := LRc) (M := M) (k := 2)
    (φ := φ.relabel f)
  refine ⟨n, ψ, fun i => (σ i : M), fun i => (σ i).property, fun x => ?_⟩
  exact (hψ (fun t : ↥T => (t : M)) ![b, x]).trans (h2 x)

end Work.WilC2
