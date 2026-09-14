import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace Commons.NumberTheory.ZMod

/-- An additive character sends a finite sum to the corresponding finite product. -/
private lemma addchar_sum_eq_prod {A M : Type*} [AddCommMonoid A] [CommMonoid M]
    (ψ : AddChar A M) {ι : Type*} (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem norm_sum_box_stdAddChar_le_zmod (M : ℕ) [NeZero M] (m L : ℕ)
    (a : Fin m → ZMod M) (K : Fin m → ℝ)
    (h : ∀ i, ‖∑ k ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod M) * a i)‖ ≤ K i) :
    ‖∑ v : Fin m → Fin L, ZMod.stdAddChar (∑ i, ((v i : ℕ) : ZMod M) * a i)‖ ≤ ∏ i, K i := by
  classical
  have hK : ∀ i : Fin m,
      ‖∑ k : Fin L, ZMod.stdAddChar (((k : ℕ) : ZMod M) * a i)‖ ≤ K i := by
    intro i
    rw [Fin.sum_univ_eq_sum_range (fun k => ZMod.stdAddChar ((k : ZMod M) * a i)) L]
    exact h i
  have h1 : (∑ v : Fin m → Fin L, ZMod.stdAddChar (∑ i, ((v i : ℕ) : ZMod M) * a i))
      = ∑ v : Fin m → Fin L,
          ∏ i, ZMod.stdAddChar (((v i : ℕ) : ZMod M) * a i) :=
    Finset.sum_congr rfl fun v _ => by
      rw [addchar_sum_eq_prod]
  have h2 : (∑ v : Fin m → Fin L, ∏ i, ZMod.stdAddChar (((v i : ℕ) : ZMod M) * a i))
      = ∏ i : Fin m, ∑ k : Fin L, ZMod.stdAddChar (((k : ℕ) : ZMod M) * a i) :=
    (Fintype.prod_sum (fun (i : Fin m) (k : Fin L) =>
      ZMod.stdAddChar (((k : ℕ) : ZMod M) * a i))).symm
  have h3 : ‖∏ i : Fin m, ∑ k : Fin L, ZMod.stdAddChar (((k : ℕ) : ZMod M) * a i)‖
      = ∏ i : Fin m, ‖∑ k : Fin L, ZMod.stdAddChar (((k : ℕ) : ZMod M) * a i)‖ :=
    norm_prod Finset.univ _
  calc
    ‖∑ v : Fin m → Fin L, ZMod.stdAddChar (∑ i, ((v i : ℕ) : ZMod M) * a i)‖
      = ‖∑ v : Fin m → Fin L,
            ∏ i, ZMod.stdAddChar (((v i : ℕ) : ZMod M) * a i)‖ := by rw [h1]
    _ = ‖∏ i : Fin m, ∑ k : Fin L, ZMod.stdAddChar (((k : ℕ) : ZMod M) * a i)‖ := by rw [h2]
    _ = ∏ i : Fin m, ‖∑ k : Fin L, ZMod.stdAddChar (((k : ℕ) : ZMod M) * a i)‖ := h3
    _ ≤ ∏ i : Fin m, K i :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hK i)

end Commons.NumberTheory.ZMod