import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.Wilkies.Defs

namespace Work.WilG4cR

open WilkiesDesign WilkiesConjecture

/-- Reindexing an intersection family along an equivalence: the intersection of `f ∘ e.symm` over
`β` is the intersection of `f` over `α`. -/
theorem iInter_equiv {α β γ : Type*} (e : α ≃ β) (f : α → Set γ) :
    (⋂ j : β, f (e.symm j)) = ⋂ i : α, f i := by
  ext z
  simp only [Set.mem_iInter]
  exact ⟨fun h i => by have := h (e i); simpa using this, fun h j => h (e.symm j)⟩

/-- `Ω`-bookkeeping for an intersection over an arbitrary finite index type at a *common* format
`a` and a *common* degree `D`: the intersection lies in `S.Ω (a+1) (card * D)`.  This is the
reindexed form of the `inter` axiom. -/
theorem iInter_fintype_mem {S : WilkiesDesign.SOMin} {n a D : ℕ} {α : Type*} [Fintype α]
    (A : α → Set (Fin n → ℝ)) (hA : ∀ i, A i ∈ S.Ω a D n) :
    (⋂ i, A i) ∈ S.Ω (a + 1) (Fintype.card α * D) n := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  have h := S.inter (F := a) (n := n) (k := Fintype.card α)
    (fun _ : Fin (Fintype.card α) => D) (fun j => A (e.symm j)) (fun j => hA _)
  have hsum : (∑ _ : Fin (Fintype.card α), D) = Fintype.card α * D := by
    simp [Finset.sum_const]
  rw [hsum] at h
  rwa [iInter_equiv e A] at h

/-- `Ω`-bookkeeping for a `Finset`-indexed intersection at a *common* format `a` and a common
degree `MvPolynomial.eval ![D,k] b`: the intersection lies in `S.Ω (a+1) (card * b.eval)`.  The
format grows by exactly one (the `inter` axiom), the degree by the cardinality.  The existing
`Work.WilG1.Omega.inter_mem` / `Work.WilG1.Plumb.inter_fin` do the `Fin k`-indexed case; this is
the `Finset` version (go via `Finset.equivFin` or `Finset.induction`). -/
theorem finset_inter_mem {S : WilkiesDesign.SOMin} {n : ℕ} {a : ℕ}
    {b : MvPolynomial (Fin 2) ℕ} {D k : ℕ} {ι : Type*}
    (s : Finset ι) (A : ι → Set (Fin n → ℝ))
    (hA : ∀ i ∈ s, A i ∈ S.Ω a (MvPolynomial.eval ![D, k] b) n) :
    (⋂ i ∈ s, A i) ∈ S.Ω (a + 1)
      (MvPolynomial.eval ![D, k] (MvPolynomial.C s.card * b)) n := by
  classical
  have h := iInter_fintype_mem (S := S) (a := a) (D := MvPolynomial.eval ![D, k] b)
    (α := {x : ι // x ∈ s}) (fun y => A y.1) (fun y => hA y.1 y.2)
  rw [Fintype.card_coe s] at h
  have hset : (⋂ y : {x : ι // x ∈ s}, A y.1) = ⋂ i ∈ s, A i := by
    ext z
    simp [Set.mem_iInter]
  rw [hset] at h
  rw [show MvPolynomial.eval ![D, k] (MvPolynomial.C s.card * b)
      = s.card * MvPolynomial.eval ![D, k] b from by
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]]
  exact h

end Work.WilG4cR
