import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.SwapCS0

open scoped BigOperators

/-- Membership in the symmetric interval `[-L, L]`, in terms of `Int.natAbs`. -/
private lemma mem_symIcc_iff_natAbs {L : ℕ} {x : ℤ} :
    x ∈ Work.Peluse.symIcc L ↔ x.natAbs ≤ L := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h : |x| ≤ (L : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · intro h
    have h' : |x| ≤ (L : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    exact abs_le.mp h'

/-- For `c c' : Fin M` one has `|(c : ℤ) - (c' : ℤ)| ≤ M`. -/
private lemma fin_sub_natAbs_le (M : ℕ) (c c' : Fin M) :
    (((c : ℤ) - (c' : ℤ))).natAbs ≤ M := by
  have h : (c : ℤ) < (M : ℤ) := by exact_mod_cast c.isLt
  have h' : (c' : ℤ) < (M : ℤ) := by exact_mod_cast c'.isLt
  have h0 : (0 : ℤ) ≤ (c' : ℤ) := Int.natCast_nonneg _
  have h1 : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg _
  omega

/-- If `f` is supported in `S₀`, then the shifted correlation
`∑_{i,c,c'} f (x + a i (c - c'))` vanishes outside the box `symIcc (sup S₀ + sup |a| · M)`:
each summand `f (x + a i (c - c'))` has its argument of absolute value `> sup S₀` there. -/
lemma acfShiftSupp {I : Type} [Fintype I] (M : ℕ) (a : I → ℤ) (f : ℤ → ℂ)
    (S₀ : Finset ℤ) (hsup : ∀ x : ℤ, x ∉ S₀ → f x = 0) :
    ∀ x : ℤ, x ∉ Work.Peluse.symIcc (S₀.sup (fun x : ℤ => x.natAbs)
        + (Finset.univ.sup (fun i : I => (a i).natAbs)) * M) →
      (∑ i : I, ∑ c : Fin M, ∑ c' : Fin M, f (x + a i * ((c : ℤ) - (c' : ℤ)))) = 0 := by
  classical
  intro x hx
  have hxlt : S₀.sup (fun x : ℤ => x.natAbs)
      + (Finset.univ.sup (fun i : I => (a i).natAbs)) * M < x.natAbs := by
    by_contra h
    exact hx (mem_symIcc_iff_natAbs.mpr (not_lt.mp h))
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine Finset.sum_eq_zero (fun c _ => ?_)
  refine Finset.sum_eq_zero (fun c' _ => ?_)
  refine hsup _ ?_
  intro hmem
  have hAi : (a i).natAbs ≤ Finset.univ.sup (fun i : I => (a i).natAbs) :=
    Finset.le_sup (f := fun i : I => (a i).natAbs) (Finset.mem_univ i)
  have hC : (((c : ℤ) - (c' : ℤ))).natAbs ≤ M := fin_sub_natAbs_le M c c'
  have hT : (a i * ((c : ℤ) - (c' : ℤ))).natAbs
      ≤ (Finset.univ.sup (fun i : I => (a i).natAbs)) * M := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul hAi hC
  have hle : (x + a i * ((c : ℤ) - (c' : ℤ))).natAbs ≤ S₀.sup (fun x : ℤ => x.natAbs) :=
    Finset.le_sup (f := fun x : ℤ => x.natAbs) hmem
  have htri : x.natAbs ≤ (x + a i * ((c : ℤ) - (c' : ℤ))).natAbs
      + (a i * ((c : ℤ) - (c' : ℤ))).natAbs := by
    have h2 :=
      Int.natAbs_add_le (x + a i * ((c : ℤ) - (c' : ℤ))) (-(a i * ((c : ℤ) - (c' : ℤ))))
    rw [show x + a i * ((c : ℤ) - (c' : ℤ)) + -(a i * ((c : ℤ) - (c' : ℤ))) = x by ring,
      Int.natAbs_neg] at h2
    exact h2
  omega

end Work.Peluse.SwapCS0
