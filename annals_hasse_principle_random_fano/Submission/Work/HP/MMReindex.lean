import Mathlib
import Submission.Work.HP.MMDefs

set_option autoImplicit false
noncomputable section

open Filter Finset MeasureTheory
open scoped RealInnerProductSpace

namespace Work.HP

/-! ## Finiteness of the sets that occur in `D^mix` and `D^loc` -/

section finite
variable {ι : Type*} [Fintype ι]

lemma eNorm_coord_abs_le (v : ι → ℤ) (i : ι) : |(v i : ℝ)| ≤ eNorm v := by
  have h2 : ((v i : ℝ)) ^ 2 ≤ ∑ j, ((v j : ℝ)) ^ 2 := by
    have := Finset.single_le_sum (s := Finset.univ) (f := fun j : ι => ((v j : ℝ)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    simpa using this
  calc |(v i : ℝ)| = Real.sqrt (((v i : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, ((v j : ℝ)) ^ 2) := Real.sqrt_le_sqrt h2
    _ = eNorm v := rfl

lemma coord_box_finite (N : ℕ) :
    {v : ι → ℤ | ∀ i, -(N : ℤ) ≤ v i ∧ v i ≤ (N : ℤ)}.Finite := by
  refine Set.Finite.subset
    (Set.Finite.pi (t := fun _ : ι => Set.Icc (-(N : ℤ)) (N : ℤ)) fun _ => Set.finite_Icc _ _) ?_
  intro v hv i _
  exact hv i

/-- Integer vectors satisfying `eNorm v ≤ A` form a finite set. -/
lemma finite_of_eNorm_le (A : ℝ) : {v : ι → ℤ | eNorm v ≤ A}.Finite := by
  refine Set.Finite.subset (coord_box_finite (Nat.ceil A)) ?_
  intro v hv i
  have h1 : |(v i : ℝ)| ≤ A := le_trans (eNorm_coord_abs_le v i) hv
  have h2 : A ≤ (Nat.ceil A : ℝ) := Nat.le_ceil A
  have h3 : (v i : ℝ) ≤ (Nat.ceil A : ℝ) := le_trans (le_trans (le_abs_self _) h1) h2
  have h4 : (-(Nat.ceil A : ℤ)) ≤ v i := by
    have h5 : -(v i : ℝ) ≤ (Nat.ceil A : ℝ) :=
      le_trans (neg_le_abs (v i : ℝ)) (le_trans h1 h2)
    have h6 : (-(Nat.ceil A) : ℝ) ≤ (v i : ℝ) := by linarith
    exact_mod_cast h6
  exact ⟨by simpa using h4, by exact_mod_cast h3⟩

end finite

section main
variable (d n : ℕ)

lemma primSet_finite (A : ℝ) (P : (Mon d n → ℤ) → Prop) : (primSet d n A P).Finite := by
  refine Set.Finite.subset (finite_of_eNorm_le (ι := Mon d n) A) ?_
  intro a ha
  exact ha.2.1

lemma Xi_finite (B : ℝ) : (Xi d n B).Finite := by
  refine Set.Finite.subset (finite_of_eNorm_le (ι := Fin (n + 1)) (B ^ (1 / ((n : ℝ) + 1 - d)))) ?_
  intro x hx
  exact hx.2

variable [DecidableEq (Mon d n)]

/-- The `x`-set in the definition of `N_V(B)`: rational points of `f_a` of height `≤ B`. -/
def Zx (a : Mon d n → ℤ) (B : ℝ) : Set (Fin (n + 1) → ℤ) :=
  {x | x ∈ Xi d n B ∧ formEval d n a x = 0}

/-- The `y`-set in the definition of `N_V^loc(B)`. -/
def Zy (a : Mon d n → ℤ) (B : ℝ) : Set (Fin (n + 1) → ℤ) :=
  {y | y ∈ Xi d n B ∧ ((bigW (wOf B) : ℕ) : ℤ) ∣ formEval d n a y ∧
      toR a ∈ Cgam (toR (veronese d n y)) (Real.log B)}

lemma Zx_finite (a : Mon d n → ℤ) (B : ℝ) : (Zx d n a B).Finite :=
  (Xi_finite d n B).subset fun x hx => hx.1

lemma Zy_finite (a : Mon d n → ℤ) (B : ℝ) : (Zy d n a B).Finite :=
  (Xi_finite d n B).subset fun y hy => hy.1

lemma Omega_finite (B : ℝ) : (Omega d n B).Finite :=
  ((Xi_finite d n B).prod (Xi_finite d n B)).subset fun p hp =>
    ⟨hp.1, hp.2.1⟩

end main

end Work.HP
