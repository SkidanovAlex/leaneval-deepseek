import Mathlib
import Submission.Work.HP.Defs

/-!
# Finiteness of the basic counting sets

`primSet d n A P`, `Xi d n B` and `Omega d n B` are all bounded sets of integer
vectors (a height ball, the set of primitive vectors of bounded norm, and its
square), hence finite.  We prove the single analytic input once: for a finite
index type `ι` and any real `A`, the set `{v : ι → ℤ | eNorm v ≤ A}` is finite,
because every coordinate satisfies `|v i| ≤ eNorm v ≤ max A 0` and therefore
runs through a finite box.
-/

set_option autoImplicit false

namespace Work.HP.MDBasic

open MvPolynomial Finset

/-- Every coordinate of an integer vector is bounded by its Euclidean norm. -/
lemma abs_apply_le_eNorm {ι : Type*} [Fintype ι] (v : ι → ℤ) (i : ι) :
    |(v i : ℝ)| ≤ eNorm v := by
  have h : ((v i : ℝ)) ^ 2 ≤ ∑ j, ((v j : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun j => ((v j : ℝ)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  simpa [eNorm] using Real.abs_le_sqrt h

/-- The set of integer vectors of Euclidean norm at most `A` is finite. -/
lemma finite_eNorm_le {ι : Type*} [Fintype ι] (A : ℝ) :
    {v : ι → ℤ | eNorm v ≤ A}.Finite := by
  have hbox :
      (Set.univ.pi fun _ : ι => Set.Icc (-(⌈max A 0⌉₊ : ℤ)) (⌈max A 0⌉₊ : ℤ)).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine hbox.subset ?_
  intro v hv
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i
  have h1 : |(v i : ℝ)| ≤ (⌈max A 0⌉₊ : ℝ) := by
    refine le_trans (abs_apply_le_eNorm v i) ?_
    refine le_trans hv ?_
    exact le_trans (le_max_left _ _) (Nat.le_ceil _)
  obtain ⟨h2, h3⟩ := abs_le.1 h1
  exact ⟨by exact_mod_cast h2, by exact_mod_cast h3⟩

theorem finite_sets (d n : ℕ) (A B : ℝ) (P : (Mon d n → ℤ) → Prop) :
    (primSet d n A P).Finite ∧ (Xi d n B).Finite ∧ (Omega d n B).Finite := by
  have hXi : (Xi d n B).Finite :=
    (finite_eNorm_le (ι := Fin (n + 1)) (B ^ (1 / ((n : ℝ) + 1 - d)))).subset
      (fun x hx => hx.2)
  refine ⟨?_, hXi, ?_⟩
  · exact (finite_eNorm_le (ι := Mon d n) A).subset (fun a ha => ha.2.1)
  · exact (hXi.prod hXi).subset (fun p hp => ⟨hp.1, hp.2.1⟩)

end Work.HP.MDBasic
