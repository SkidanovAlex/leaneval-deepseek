import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Submission.Commons.NumberTheory.ZMod.norm_sum_stdAddChar_range_le

open Finset

namespace Commons.NumberTheory.ZMod

/-- An additive character turns a finite sum into a product. -/
lemma AddChar.map_sum_eq_prod {A M : Type*} [AddCommMonoid A] [CommMonoid M]
    (ψ : AddChar A M) {ι : Type*} (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, ψ.map_add_eq_mul, ih]

/-- **Fourier box atom**: for a box `{0,…,L-1}^m` and an additive character `χ`
of `ZMod p` (here the standard one, evaluated on the linear form
`v ↦ ∑ i, (v i) * a i`), the character sum factorizes over the coordinates,
so a one-dimensional bound `‖∑_{k<L} stdAddChar (k * a i)‖ ≤ K i` for each
coordinate yields `‖∑_{v} stdAddChar (∑ i, (v i) * a i)‖ ≤ ∏ i, K i`. -/
theorem norm_sum_box_stdAddChar_le (p : ℕ) [Fact p.Prime] (m L : ℕ)
    (a : Fin m → ZMod p) (K : Fin m → ℝ)
    (h : ∀ i, ‖∑ k ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod p) * a i)‖ ≤ K i) :
    ‖∑ v : Fin m → Fin L, ZMod.stdAddChar (∑ i, ((v i : ℕ) : ZMod p) * a i)‖ ≤ ∏ i, K i := by
  classical
  set G : Fin m → Fin L → ℂ := fun i k => ZMod.stdAddChar (((k : ℕ) : ZMod p) * a i) with hG
  -- Step 1: pointwise factorisation of the character of the linear form
  have hpoint : ∀ v : Fin m → Fin L,
      ZMod.stdAddChar (∑ i, ((v i : ℕ) : ZMod p) * a i) = ∏ i, G i (v i) := by
    intro v
    rw [AddChar.map_sum_eq_prod (ZMod.stdAddChar) Finset.univ
      (fun i => ((v i : ℕ) : ZMod p) * a i)]
  -- Step 2: factorise the sum over the box into a product of one-dimensional sums
  have hfactor : (∑ v : Fin m → Fin L, ∏ i, G i (v i)) = ∏ i, ∑ k : Fin L, G i k := by
    have := Finset.sum_prod_piFinset (s := (Finset.univ : Finset (Fin L))) (g := G)
    simpa using this
  -- Step 3: one-dimensional bounds
  have h4 : ∀ i, ‖∑ k : Fin L, G i k‖ ≤ K i := by
    intro i
    have hEq : (∑ k : Fin L, G i k)
        = ∑ k ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod p) * a i) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun n : ℕ => ZMod.stdAddChar (((n : ℕ) : ZMod p) * a i)) L]
    rw [hEq]
    exact h i
  calc ‖∑ v : Fin m → Fin L, ZMod.stdAddChar (∑ i, ((v i : ℕ) : ZMod p) * a i)‖
      = ‖∑ v : Fin m → Fin L, ∏ i, G i (v i)‖ := by
        rw [Finset.sum_congr rfl (fun v _ => hpoint v)]
    _ = ‖∏ i, ∑ k : Fin L, G i k‖ := by rw [hfactor]
    _ = ∏ i, ‖∑ k : Fin L, G i k‖ := by rw [norm_prod]
    _ ≤ ∏ i, K i :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => h4 i)

end Commons.NumberTheory.ZMod