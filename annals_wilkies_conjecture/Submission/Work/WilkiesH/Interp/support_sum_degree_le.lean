import Mathlib
import Submission.Work.WilkiesH.Defs

namespace Work.WilkiesH.Interp

open MvPolynomial

/-- For a finitely supported exponent function `m` on `Fin n`, every value `m i` is at
most the total sum `∑ a, m a`. -/
lemma apply_le_sum {n : ℕ} (m : Fin n →₀ ℕ) (i : Fin n) : m i ≤ m.sum (fun _ e => e) := by
  rw [Finsupp.sum]
  by_cases hi : i ∈ m.support
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  · rw [Finsupp.notMem_support_iff.mp hi]
    exact Nat.zero_le _

/-- The plain finite sum `∑ i, m i` agrees with the `Finsupp.sum` of the identity. -/
lemma sum_apply_eq_finsupp_sum {n : ℕ} (m : Fin n →₀ ℕ) :
    (∑ i, m i) = m.sum (fun _ e => e) := by
  rw [Finsupp.sum]
  exact (Finset.sum_subset (Finset.subset_univ _)
    (fun i _ hi => Finsupp.notMem_support_iff.mp hi)).symm

/-- The exponent vector underlying a finitely supported exponent function of total
degree at most `d`.  Entries are bounded by `d` because the total sum is. -/
def toExpVec {n d : ℕ} (m : Fin n →₀ ℕ) (h : m.sum (fun _ e => e) ≤ d) :
    Work.WilkiesH.ExpVec n d :=
  ⟨fun i => ⟨m i, Nat.lt_succ_of_le (le_trans (apply_le_sum m i) h)⟩,
   by rw [sum_apply_eq_finsupp_sum]; exact h⟩

/-- `toExpVec` is injective: it only re-packages the entries as elements of `Fin (d+1)`. -/
lemma toExpVec_injective {n d : ℕ} {m m' : Fin n →₀ ℕ}
    (h : m.sum (fun _ e => e) ≤ d) (h' : m'.sum (fun _ e => e) ≤ d)
    (heq : toExpVec m h = toExpVec m' h') : m = m' := by
  ext i
  have h2 := congrFun (congrArg Subtype.val heq) i
  exact congrArg Fin.val h2

/-- The support of a polynomial of total degree `≤ d` in `n` variables has at most
`monoCount n d` elements: its exponent vectors inject into `ExpVec n d`. -/
lemma card_support_le {n d : ℕ} (P : MvPolynomial (Fin n) ℤ) (hdeg : P.totalDegree ≤ d) :
    P.support.card ≤ Work.WilkiesH.monoCount n d := by
  classical
  rw [Work.WilkiesH.monoCount]
  refine Finset.card_le_card_of_injective (s := P.support)
    (t := (Finset.univ : Finset (Work.WilkiesH.ExpVec n d)))
    (f := fun m => ⟨toExpVec m.1 (by
      exact (le_totalDegree m.2).trans hdeg), Finset.mem_univ _⟩) ?_
  intro a b hab
  apply Subtype.ext
  have hab' : toExpVec a.1 (by exact (le_totalDegree a.2).trans hdeg) =
      toExpVec b.1 (by exact (le_totalDegree b.2).trans hdeg) :=
    Subtype.ext_iff.mp hab
  exact toExpVec_injective _ _ hab'

/-- Every monomial appearing in `P` has total degree `≤ d`, so the sum of total degrees
over the support is at most `#support * d ≤ monoCount n d * d`. -/
theorem support_sum_degree_le {n d : ℕ} (P : MvPolynomial (Fin n) ℤ) (hdeg : P.totalDegree ≤ d) :
    ∑ m ∈ P.support, (∑ i, m i) ≤ Work.WilkiesH.monoCount n d * d := by
  have hterm : ∀ m ∈ P.support, (∑ i, m i) ≤ d := by
    intro m hm
    rw [sum_apply_eq_finsupp_sum]
    exact (le_totalDegree hm).trans hdeg
  calc ∑ m ∈ P.support, (∑ i, m i) ≤ ∑ m ∈ P.support, d := Finset.sum_le_sum hterm
    _ = P.support.card * d := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Work.WilkiesH.monoCount n d * d := Nat.mul_le_mul_right d (card_support_le P hdeg)

end Work.WilkiesH.Interp
