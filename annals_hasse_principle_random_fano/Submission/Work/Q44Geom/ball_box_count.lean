import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Q44Child.CountDefs

/-!
# `Work.Q44Geom.ball_box_count`

The number of integral zeros `x` of a polynomial `g` in `5` variables with Euclidean norm
`≤ T` is at most the number of zeros of `g` in the coordinate box `[-⌈T⌉₊, ⌈T⌉₊]^5`.

The proof is the elementary pointwise inclusion: `eNorm x ≤ T` forces `|x i| ≤ eNorm x ≤ T`,
and since `T ≤ ⌈T⌉₊` every such `x` lies in the box; the zero condition is carried along, so
the set is contained in the filtered box and `Set.ncard` is monotone on finite sets.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Q44Geom

open Work.HP.Q44Child

/-- Membership in the coordinate box, coordinatewise form. -/
lemma mem_cbox5 {s M : ℕ} {x : Fin s → ℤ} :
    x ∈ cbox s M ↔ ∀ i, -(M : ℤ) ≤ x i ∧ x i ≤ (M : ℤ) := by
  simp [cbox, Fintype.mem_piFinset, Finset.mem_Icc]

/-- Every coordinate of an integer vector is bounded in absolute value by its Euclidean norm. -/
lemma abs_coord_le_eNorm5 (v : Fin 5 → ℤ) (i : Fin 5) :
    |((v i : ℤ) : ℝ)| ≤ Work.HP.eNorm v := by
  have h1 : (((v i : ℤ) : ℝ)) ^ 2 ≤ ∑ j, (((v j : ℤ) : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (((v j : ℤ) : ℝ))) (Finset.mem_univ i)
  calc |((v i : ℤ) : ℝ)| = Real.sqrt ((((v i : ℤ) : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, (((v j : ℤ) : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Work.HP.eNorm v := rfl

theorem ball_box_count (g : MvPolynomial (Fin 5) ℤ) (T : ℝ) :
    (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ T ∧ MvPolynomial.eval x g = 0} :
        Set (Fin 5 → ℤ)).ncard : ℝ)
      ≤ (((Work.HP.Q44Child.cbox 5 ⌈T⌉₊).filter (fun x => MvPolynomial.eval x g = 0)).card : ℝ) := by
  classical
  have hsub : ({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ T ∧ MvPolynomial.eval x g = 0} :
        Set (Fin 5 → ℤ))
      ⊆ ((Work.HP.Q44Child.cbox 5 ⌈T⌉₊).filter (fun x => MvPolynomial.eval x g = 0) :
        Finset (Fin 5 → ℤ)) := by
    intro x hx
    obtain ⟨hxT, hx0⟩ := hx
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨?_, hx0⟩
    rw [mem_cbox5]
    intro i
    have h1 : |((x i : ℤ) : ℝ)| ≤ ((⌈T⌉₊ : ℕ) : ℝ) :=
      le_trans (le_trans (abs_coord_le_eNorm5 x i) hxT) (Nat.le_ceil T)
    have h2 : ((|x i| : ℤ) : ℝ) = |(x i : ℝ)| := Int.cast_abs
    have h3 : ((|x i| : ℤ) : ℝ) ≤ (((⌈T⌉₊ : ℕ) : ℤ) : ℝ) := by
      rw [h2]; push_cast; exact h1
    exact abs_le.mp (by exact_mod_cast h3)
  have hcard : (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ T ∧ MvPolynomial.eval x g = 0} :
        Set (Fin 5 → ℤ)).ncard : ℝ)
      ≤ (((Work.HP.Q44Child.cbox 5 ⌈T⌉₊).filter
          (fun x => MvPolynomial.eval x g = 0)).card : ℝ) := by
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    exact_mod_cast h1
  exact hcard

end Work.Q44Geom
