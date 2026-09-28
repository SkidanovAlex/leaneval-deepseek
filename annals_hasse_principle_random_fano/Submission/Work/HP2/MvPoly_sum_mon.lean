import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.BridgeDefs

namespace Work.HP2

set_option autoImplicit false

open MvPolynomial

/-! ## The exponent-vector/Finsupp dictionary

`Work.HP.Mon.toFinsupp` sends a degree-`d` exponent vector to the corresponding finsupp; these two
lemmas record that it is the identity on values (hence injective) and that every finsupp of total
degree `2 * d` comes from a degree-`2 * d` exponent vector. -/

lemma toFinsupp_apply {d n : ℕ} (η : Work.HP.Mon d n) (i : Fin (n + 1)) :
    Work.HP.Mon.toFinsupp η i = (η.1 i : ℕ) := by
  simp only [Work.HP.Mon.toFinsupp, Finsupp.coe_equivFunOnFinite_symm]

lemma toFinsupp_injective (d n : ℕ) :
    Function.Injective (Work.HP.Mon.toFinsupp (d := d) (n := n)) := by
  intro η η' h
  have h' : ∀ i, (η.1 i : ℕ) = (η'.1 i : ℕ) := fun i => by
    have hh := congrFun (congrArg DFunLike.coe h) i
    rw [toFinsupp_apply η i, toFinsupp_apply η' i] at hh
    exact hh
  exact Subtype.ext (funext (fun i => Fin.ext (h' i)))

lemma exists_mon_toFinsupp (d n : ℕ) (m : Fin (n + 1) →₀ ℕ)
    (hm : Finsupp.degree m = 2 * d) :
    ∃ η : Work.HP.Mon (2 * d) n, Work.HP.Mon.toFinsupp η = m := by
  have hle : ∀ i, m i ≤ 2 * d := fun i => by
    have h := Finsupp.le_degree i m
    rwa [hm] at h
  have hsum : ∑ i, m i = 2 * d := by
    rw [← Finsupp.degree_eq_sum]
    exact hm
  refine ⟨⟨fun i => ⟨m i, by have := hle i; omega⟩, ?_⟩, ?_⟩
  · simpa using hsum
  · ext i
    rw [toFinsupp_apply, Fin.val_mk]

/-- A homogeneous polynomial of degree `2 * d` in `n + 1` variables evaluates as the sum of its
monomials grouped by their exponent vector in `Mon (2 * d) n`. -/
theorem MvPoly_sum_mon (d n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℝ)
    (hP : P.IsHomogeneous (2 * d)) (x : Fin (n + 1) → ℝ) :
    MvPolynomial.eval x P
      = ∑ η : Work.HP.Mon (2 * d) n,
          P.coeff (Work.HP.Mon.toFinsupp η) * Work.HP.veronese (2 * d) n x η := by
  have hR : (∑ η : Work.HP.Mon (2 * d) n,
        P.coeff (Work.HP.Mon.toFinsupp η) * Work.HP.veronese (2 * d) n x η)
      = ∑ η : Work.HP.Mon (2 * d) n,
        P.coeff (Work.HP.Mon.toFinsupp η) *
          ∏ i : Fin (n + 1), x i ^ (Work.HP.Mon.toFinsupp η i) := by
    apply Finset.sum_congr rfl
    intro η _
    simp only [Work.HP.veronese, toFinsupp_apply]
  have hmain : (∑ η : Work.HP.Mon (2 * d) n,
        P.coeff (Work.HP.Mon.toFinsupp η) *
          ∏ i : Fin (n + 1), x i ^ (Work.HP.Mon.toFinsupp η i))
      = ∑ m ∈ P.support, P.coeff m * ∏ i : Fin (n + 1), x i ^ m i := by
    have hinj : Set.InjOn (Work.HP.Mon.toFinsupp (d := 2 * d) (n := n))
        (Finset.univ : Finset (Work.HP.Mon (2 * d) n)) :=
      fun a _ b _ h => toFinsupp_injective (2 * d) n h
    rw [← Finset.sum_image
      (f := fun m : Fin (n + 1) →₀ ℕ => P.coeff m * ∏ i : Fin (n + 1), x i ^ m i) hinj]
    refine (Finset.sum_subset
      (f := fun m : Fin (n + 1) →₀ ℕ => P.coeff m * ∏ i : Fin (n + 1), x i ^ m i)
      ?_ ?_).symm
    · intro m hm
      have hc : P.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
      have hdeg : Finsupp.degree m = 2 * d := by
        by_contra hne
        exact hc (hP.coeff_eq_zero hne)
      obtain ⟨η, hη⟩ := exists_mon_toFinsupp d n m hdeg
      exact Finset.mem_image.mpr ⟨η, Finset.mem_univ η, hη⟩
    · intro m _ hnot
      have hc : P.coeff m = 0 := by
        by_contra hc
        exact hnot (MvPolynomial.mem_support_iff.mpr hc)
      simp [hc]
  rw [MvPolynomial.eval_eq', hR, hmain]

end Work.HP2
