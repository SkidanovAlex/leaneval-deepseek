import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.PET

/-! ## Auxiliary lemmas for `pet_reindex`

The change of variables in this file is a finite-sum manipulation.  It splits into two
independent facts, proved below:

* `sum_Icc_add_shift_of_support` — the analytic/arithmetic part: a sum over the wide interval
  `[-N(Cne+1), N(Cne+1)]` of a function supported in `[-N,N]` is unchanged by shifting the
  argument (`x ↦ x + c`, `|c| ≤ Cne·N`) and may be restricted to `[-N,N]`;
* `prod_identity` — the purely algebraic part: pulling the `i₀`-factor `F i₀ (x + Q i₀ y)` out of
  the product over `i` and splitting each remaining factor into its two `ε : Bool` parts.
-/

/-- Reindex a sum over `Finset.Icc a b` by the translation `x ↦ x + c`. -/
private lemma sum_Icc_add_shift (f : ℤ → ℂ) (a b c : ℤ) :
    (∑ x ∈ Finset.Icc a b, f (x + c)) = ∑ z ∈ Finset.Icc (a + c) (b + c), f z := by
  refine Finset.sum_nbij' (fun x => x + c) (fun z => z - c) ?_ ?_ ?_ ?_ ?_
  · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; constructor <;> omega
  · intro z hz; simp only [Finset.mem_Icc] at hz ⊢; constructor <;> omega
  · intro x hx; ring
  · intro z hz; ring
  · intro x hx; rfl

/-- A shifted sum over the wide interval `[-N(Cne+1), N(Cne+1)]` of a function vanishing outside
`[-N,N]` collapses onto `[-N,N]`, for any shift `c` with `|c| ≤ Cne·N`. -/
private lemma sum_Icc_add_shift_of_support {f : ℤ → ℂ} {N Cne : ℕ} {c : ℤ}
    (hf : ∀ z : ℤ, N < z.natAbs → f z = 0)
    (hc : |c| ≤ (Cne : ℤ) * (N : ℤ)) :
    (∑ x ∈ Finset.Icc (-((N:ℤ)*(Cne+1))) ((N:ℤ)*(Cne+1)), f (x + c))
      = ∑ z ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), f z := by
  rw [sum_Icc_add_shift]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro z hz
    simp only [Finset.mem_Icc] at hz ⊢
    have hAN : (N:ℤ)*(Cne+1) - (N:ℤ) = (Cne:ℤ)*(N:ℤ) := by ring
    constructor
    · have h : c ≤ (N:ℤ)*(Cne+1) - (N:ℤ) := by rw [hAN]; exact (abs_le.mp hc).2
      omega
    · have h : -c ≤ (N:ℤ)*(Cne+1) - (N:ℤ) := by
        rw [hAN]; have := (abs_le.mp hc).1; omega
      omega
  · intro z _ hznot
    simp only [Finset.mem_Icc] at hznot
    apply hf z
    rw [← Nat.cast_lt (α := ℤ), ← Int.abs_eq_natAbs, lt_abs]
    rcases not_and_or.mp hznot with h | h
    · right; omega
    · left; omega

/-- The algebraic core: pulling the `i₀`-factor out of the product and rewriting each remaining
factor as the two `ε : Bool` pieces. -/
private lemma prod_identity {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ : ι)
    (Q : ι → ℤ → ℤ) (F : ι → ℤ → ℂ) (a x y : ℤ) :
    (∏ i : ι, (star (F i (x + Q i (y + a))) * F i (x + Q i y)))
      = F i₀ (x + Q i₀ y) *
          ∏ i : ι, ∏ ε : Bool,
            (if ((i, ε) = (i₀, false)) then 1 else
              (if ε then star (F i ((x + Q i₀ y) + (Q i (y + a) - Q i₀ y)))
                      else F i ((x + Q i₀ y) + (Q i y - Q i₀ y)))) := by
  rw [Finset.prod_mul_distrib]
  have hbool : ∀ i : ι, (∏ ε : Bool,
        (if ((i, ε) = (i₀, false)) then (1:ℂ) else
          (if ε then star (F i ((x + Q i₀ y) + (Q i (y + a) - Q i₀ y)))
                  else F i ((x + Q i₀ y) + (Q i y - Q i₀ y)))))
      = (if i = i₀ then (1:ℂ) else F i (x + Q i y)) * star (F i (x + Q i (y + a))) := by
    intro i
    rw [Fintype.prod_bool]
    by_cases hi : i = i₀
    · subst hi
      simp only [Prod.mk.injEq, ite_true, ite_false, true_and,
        one_mul, mul_one, Bool.true_eq_false]
      congr 2
      ring
    · simp only [Prod.mk.injEq, and_true, reduceIte, hi, Bool.true_eq_false,
        Bool.false_eq_true, and_false]
      rw [show x + Q i₀ y + (Q i (y + a) - Q i₀ y) = x + Q i (y + a) by ring,
          show x + Q i₀ y + (Q i y - Q i₀ y) = x + Q i y by ring, mul_comm]
  simp only [hbool]
  rw [Finset.prod_mul_distrib]
  have hB : F i₀ (x + Q i₀ y) * (∏ i : ι, (if i = i₀ then (1:ℂ) else F i (x + Q i y)))
      = ∏ i : ι, F i (x + Q i y) := by
    have h1 : (∏ i : ι, (if i = i₀ then (1:ℂ) else F i (x + Q i y)))
        = ∏ i ∈ (Finset.univ : Finset ι) \ {i₀}, F i (x + Q i y) := by
      rw [Finset.prod_eq_mul_prod_sdiff_singleton i₀
        (fun i => if i = i₀ then (1:ℂ) else F i (x + Q i y))
        (fun h => absurd (Finset.mem_univ i₀) h)]
      rw [if_pos rfl, one_mul]
      exact Finset.prod_congr rfl (fun i hi =>
        by rw [if_neg (by simpa using (Finset.mem_sdiff.mp hi).2)])
    rw [h1, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i₀)
      (fun i => F i (x + Q i y))]
  rw [← mul_assoc, hB]
  ring

/-- The change of variables `x ↦ x + Q i₀ y` in the PET step: for each fixed `a`, moving the
`i₀`-factor `F i₀ (x + Q i₀ y)` out of the product and reindexing the `x`-sum.  The two ranges
`[-N(Cne+1), N(Cne+1)]` (LHS) and `[-N,N]` (RHS) are exactly the (finitely many) `x` for which the
summands can be nonzero, so this is a plain bijection argument; `a : ℤ` is arbitrary. -/
theorem pet_reindex {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ : ι) {N M Cne : ℕ}
    (Q : ι → ℤ → ℤ) (F : ι → ℤ → ℂ)
    (hFs : ∀ i, Work.Peluse.SupportIn (F i) N)
    (hQ : ∀ i, ∀ y ∈ Finset.Icc 1 M, |Q i (y : ℤ)| ≤ (Cne : ℤ) * (N : ℤ))
    (a : ℤ) :
    ∑ x ∈ Finset.Icc (-((N:ℤ)*(Cne+1))) ((N:ℤ)*(Cne+1)),
        ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, (star (F i (x + Q i ((y:ℤ) + a))) * F i (x + Q i (y:ℤ)))
      = ∑ x ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), F i₀ x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, ∏ ε : Bool,
            (if ((i, ε) = (i₀, false)) then 1 else
              (if ε then star (F i (x + (Q i ((y : ℤ) + a) - Q i₀ (y : ℤ))))
                      else F i (x + (Q i (y : ℤ) - Q i₀ (y : ℤ))))) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  have hcongr : (∑ x ∈ Finset.Icc (-((N:ℤ)*(Cne+1))) ((N:ℤ)*(Cne+1)),
        ∏ i : ι, (star (F i (x + Q i ((y:ℤ) + a))) * F i (x + Q i (y:ℤ))))
      = ∑ x ∈ Finset.Icc (-((N:ℤ)*(Cne+1))) ((N:ℤ)*(Cne+1)),
          F i₀ (x + Q i₀ (y:ℤ)) *
            ∏ i : ι, ∏ ε : Bool,
              (if ((i, ε) = (i₀, false)) then 1 else
                (if ε then star (F i ((x + Q i₀ (y:ℤ)) + (Q i ((y:ℤ) + a) - Q i₀ (y:ℤ))))
                        else F i ((x + Q i₀ (y:ℤ)) + (Q i (y:ℤ) - Q i₀ (y:ℤ))))) :=
    Finset.sum_congr rfl (fun x _ => prod_identity i₀ Q F a x (y:ℤ))
  rw [hcongr]
  refine sum_Icc_add_shift_of_support (c := Q i₀ (y:ℤ))
    (f := fun z => F i₀ z * ∏ i : ι, ∏ ε : Bool,
      (if ((i, ε) = (i₀, false)) then 1 else
        (if ε then star (F i (z + (Q i ((y:ℤ) + a) - Q i₀ (y:ℤ))))
                else F i (z + (Q i (y:ℤ) - Q i₀ (y:ℤ)))))) ?_ ?_
  · intro z hz; rw [hFs i₀ z hz, zero_mul]
  · exact hQ i₀ y hy

end Work.Peluse.PET
