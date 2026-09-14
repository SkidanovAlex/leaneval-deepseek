import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.DFinsupp

open BigOperators
open scoped BigOperators

set_option autoImplicit false

namespace Commons.Lattice.Counting

/-- If multiplying a finitely-supported function by a nonzero integer keeps its support inside
a set, then the original support is already inside that set (since `ℤ` is a domain). -/
lemma support_subset_of_smul_support_subset {α : Type*} (f : α →₀ ℤ) (a : ℤ) (ha : a ≠ 0)
    {s : Set α} (hs : ↑(a • f).support ⊆ s) : ↑f.support ⊆ s := by
  intro i hi
  have hfi : f i ≠ 0 := by
    change i ∈ f.support at hi
    rwa [Finsupp.mem_support_iff] at hi
  have hmem : i ∈ ((a • f).support : Set α) := by
    have hsmul : (a • f) i ≠ 0 := by
      change a * f i ≠ 0
      exact mul_ne_zero ha hfi
    change i ∈ (a • f).support
    exact Finsupp.mem_support_iff.mpr hsmul
  exact hs hmem

/-- Membership in the span of a subfamily of a basis is equivalent to the basis coordinates
being supported on the subfamily's index set. -/
lemma mem_span_subfamily {n o r : ℕ} (eO : Module.Basis (Fin o) ℤ (Fin n → ℤ))
    (emb : Fin r ↪ Fin o) (x : Fin n → ℤ) :
    x ∈ Submodule.span ℤ (Set.range (fun k : Fin r => (eO (emb k) : Fin n → ℤ))) ↔
      ↑(eO.repr x).support ⊆ Set.range emb := by
  rw [show (Submodule.span ℤ (Set.range (fun k : Fin r => (eO (emb k) : Fin n → ℤ)))) =
        Submodule.span ℤ (⇑eO '' (Set.range emb)) by
    congr 1
    rw [← Set.range_comp]
    exact congrArg Set.range (funext (fun k : Fin r => rfl))]
  exact Module.Basis.mem_span_image eO

/-- The submodule spanned by a subfamily of a `ℤ`-basis is pure: if a nonzero integer multiple
of `x` lies in it, then `x` itself lies in it. -/
theorem pure_span_subfamily {n o r : ℕ} (eO : Module.Basis (Fin o) ℤ (Fin n → ℤ))
    (emb : Fin r ↪ Fin o) :
    ∀ x : Fin n → ℤ,
      (∃ a : ℤ, a ≠ 0 ∧ a • x ∈ Submodule.span ℤ (Set.range (fun k : Fin r => (eO (emb k) : Fin n → ℤ)))) →
      x ∈ Submodule.span ℤ (Set.range (fun k : Fin r => (eO (emb k) : Fin n → ℤ))) := by
  intro x hax
  rcases hax with ⟨a, ha, hax⟩
  have hrep : ↑(eO.repr (a • x)).support ⊆ Set.range emb :=
    (mem_span_subfamily eO emb (a • x)).mp hax
  have hlin : eO.repr (a • x) = a • eO.repr x := by
    exact map_smul eO.repr a x
  rw [hlin] at hrep
  have hrep' : ↑(eO.repr x).support ⊆ Set.range emb :=
    support_subset_of_smul_support_subset (eO.repr x) a ha hrep
  exact (mem_span_subfamily eO emb x).mpr hrep'

end Commons.Lattice.Counting