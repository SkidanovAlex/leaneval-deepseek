import Mathlib
import Submission.Work.WilE4.CAD.Fibre
import Submission.Work.WilE4.CAD.sign_const_of_deriv_pos
import Submission.Work.WilE4.CAD.sign_const_of_deriv_neg

noncomputable section
open Classical
namespace Work.WilE4.CAD

open Polynomial

variable {k : ℕ}

/-- **Main lemma.**  Let a family of real polynomials be closed under differentiation (in the
weak sense that the derivative of a member is again a member, or zero).  If two points `a < b`
lie in the same strict sign-condition set, then the whole open interval between them does. -/
theorem pcell_Ioo_subset (P : Fin k → Polynomial ℝ) (v : Fin k → SignType)
    (hderiv : ∀ i, (P i).derivative = 0 ∨ ∃ j, P j = (P i).derivative)
    {a b : ℝ} (hab : a < b) (ha : a ∈ pcell P v) (hb : b ∈ pcell P v) :
    Set.Ioo a b ⊆ pcell P v := by
  intro y hy
  simp only [pcell, Set.mem_ofPred_eq] at ha hb ⊢
  have hkey : ∀ n, ∀ i : Fin k, (P i).natDegree = n →
      ∀ t ∈ Set.Ioo a b, SignType.sign ((P i).eval t) = v i := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hdeg t ht
      by_cases hn : n = 0
      · have hdeg0 : (P i).natDegree = 0 := by omega
        have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
        have hcte : (P i).eval t = (P i).eval a := by rw [hC]; simp
        rw [hcte]; exact ha i
      · have hnd : (P i).natDegree ≠ 0 := by omega
        have hdne : (P i).derivative ≠ 0 :=
          fun h => hnd (Polynomial.derivative_eq_zero.mp h)
        rcases hderiv i with h0 | ⟨j, hj⟩
        · exact absurd h0 hdne
        · have hdegj : (P j).natDegree < n := by
            rw [hj, ← hdeg]
            exact Polynomial.natDegree_derivative_lt hnd
          have ihj : ∀ s ∈ Set.Ioo a b, SignType.sign ((P j).eval s) = v j :=
            ih (P j).natDegree hdegj j rfl
          have hsign : ∀ s ∈ Set.Ioo a b,
              SignType.sign ((P i).derivative.eval s)
                = SignType.sign ((P i).derivative.eval a) := by
            intro s hs'
            have h1 := ihj s hs'
            have h2 : SignType.sign ((P j).eval a) = v j := ha j
            rw [hj] at h1 h2
            exact h1.trans h2.symm
          have hsa : SignType.sign ((P i).eval a) = v i := ha i
          have hsb : SignType.sign ((P i).eval b) = v i := hb i
          rcases lt_trichotomy ((P i).derivative.eval a) 0 with hneg | hzero | hpos
          · have hdneg : ∀ s ∈ Set.Ioo a b, (P i).derivative.eval s < 0 := by
              intro s hs'
              have hh := hsign s hs'
              rw [sign_neg hneg] at hh
              exact sign_eq_neg_one_iff.mp hh
            have key := sign_const_of_deriv_neg (f := P i) hab hdneg (by rw [hsa, hsb])
            rw [hsa] at key
            exact key t ht
          · exfalso
            have hdzero : ∀ s ∈ Set.Ioo a b, (P i).derivative.eval s = 0 := by
              intro s hs'
              have hh := hsign s hs'
              rw [hzero, sign_zero] at hh
              exact sign_eq_zero_iff.mp hh
            have hz : (P i).derivative = 0 := by
              refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
              refine (Set.Ioo_infinite hab).mono ?_
              intro s hs'
              simp only [Set.mem_ofPred_eq, Polynomial.IsRoot]
              exact hdzero s hs'
            exact hdne hz
          · have hdpos : ∀ s ∈ Set.Ioo a b, 0 < (P i).derivative.eval s := by
              intro s hs'
              have hh := hsign s hs'
              rw [sign_pos hpos] at hh
              exact sign_eq_one_iff.mp hh
            have key := sign_const_of_deriv_pos (f := P i) hab hdpos (by rw [hsa, hsb])
            rw [hsa] at key
            exact key t ht
  intro i
  exact hkey (P i).natDegree i rfl y hy

theorem pcell_ordConnected {k : ℕ} (P : Fin k → Polynomial ℝ) (v : Fin k → SignType)
    (hderiv : ∀ i, (P i).derivative = 0 ∨ ∃ j, P j = (P i).derivative) :
    Set.OrdConnected (pcell P v) := by
  refine Set.ordConnected_of_Ioo ?_
  intro a ha b hb hab
  exact pcell_Ioo_subset P v hderiv hab ha hb

end Work.WilE4.CAD
