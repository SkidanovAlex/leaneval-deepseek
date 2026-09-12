import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.MvPolynomial

open Finsupp

/-- The number of finitely supported functions `Fin r → ℕ` summing to at most `m` is
`(m + r).choose r`. -/
theorem ncard_finsupp_sum_le (r m : ℕ) :
    ({n : Fin r →₀ ℕ | n.sum (fun _ e => e) ≤ m} : Set (Fin r →₀ ℕ)).ncard
      = (m + r).choose r := by
  classical
  have e : ↥({n : Fin r →₀ ℕ | n.sum (fun _ e => e) ≤ m} : Set (Fin r →₀ ℕ)) ≃
      ↥({N : Fin (r + 1) →₀ ℕ | N.sum (fun _ e => e) = m} : Set (Fin (r + 1) →₀ ℕ)) :=
    { toFun := fun n => ⟨Finsupp.cons (m - n.1.sum (fun _ e => e)) n.1, by
        show (Finsupp.cons (m - n.1.sum (fun _ e => e)) n.1).sum (fun _ e => e) = m
        rw [Finsupp.sum_cons, Nat.sub_add_cancel n.2]⟩
      invFun := fun N => ⟨Finsupp.tail N.1, by
        have h : (Finsupp.tail N.1).sum (fun _ e => e) ≤ N.1.sum (fun _ e => e) := by
          rw [← Finsupp.cons_tail N.1, Finsupp.sum_cons]
          exact Nat.le_add_left _ _
        exact h.trans_eq N.2⟩
      left_inv := fun n => Subtype.ext (Finsupp.tail_cons _ _)
      right_inv := fun N => Subtype.ext (by
        show Finsupp.cons (m - (Finsupp.tail N.1).sum (fun _ e => e)) (Finsupp.tail N.1) = N.1
        have hN : N.1.sum (fun _ e => e) = m := N.2
        have h := Finsupp.sum_cons r (Finsupp.tail N.1) (N.1 0)
        rw [Finsupp.cons_tail] at h
        have h' : m - (Finsupp.tail N.1).sum (fun _ e => e) = N.1 0 := by omega
        rw [h', Finsupp.cons_tail]) }
  have hB : ({N : Fin (r + 1) →₀ ℕ | N.sum (fun _ e => e) = m} : Set (Fin (r + 1) →₀ ℕ))
      = ↑((Finset.univ : Finset (Fin (r + 1))).finsuppAntidiag m) := by
    ext N
    rw [Finset.mem_coe, Finset.mem_finsuppAntidiag']
    simp [Finset.subset_univ]
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_coe_set_eq, hB, Set.ncard_coe_finset,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  have h : r + 1 + m - 1 = m + r := by omega
  rw [h, Nat.choose_symm_add]

theorem finrank_restrictTotalDegree (𝕜 : Type*) [Field 𝕜] (r m : ℕ) :
    Module.finrank 𝕜 (MvPolynomial.restrictTotalDegree (Fin r) 𝕜 m) = (m + r).choose r := by
  classical
  change Module.finrank 𝕜 (_root_.MvPolynomial.restrictSupport 𝕜
    ({n : Fin r →₀ ℕ | n.sum (fun _ e => e) ≤ m} : Set (Fin r →₀ ℕ))) = (m + r).choose r
  rw [Module.finrank_eq_nat_card_basis (_root_.MvPolynomial.basisRestrictSupport 𝕜
    ({n : Fin r →₀ ℕ | n.sum (fun _ e => e) ≤ m} : Set (Fin r →₀ ℕ)))]
  rw [Nat.card_coe_set_eq]
  exact ncard_finsupp_sum_le r m

end Commons.Algebra.MvPolynomial