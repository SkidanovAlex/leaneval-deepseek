import Mathlib
import Submission.Commons.NumberTheory.Stepanov.gpow_mod_Xq_indep

namespace Commons.NumberTheory.Stepanov

open Polynomial

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- **Non-vanishing of the Stepanov auxiliary function, general `e`.**

Let `F` be a finite field, `e ≥ 2` with `e ∣ #F - 1`, and `g ∈ F[X]` with `g(0) ≠ 0` which is
not a constant multiple of a `p`-th power for any prime `p ∣ e`.  Let `A_r ∈ F[X][Y]`
(`r : Fin e`) be such that all `X`-coefficients have degree `≤ A₀`, the `Y`-degree is `< #F`,
and `e·A₀ + e³·(deg g + 1) < #F`.  If

`∑_r A_r(X, X ^ #F) · g ^ (r · (#F-1)/e) = 0`

then all `A_r` vanish.

Proof: write `A_r(X^q) = ∑_i a_{r,i} X ^ (q i)`; grouping the relation by the power of `X^q`
gives `∑_i X^(q i) T_i = 0` with `T_i = ∑_r a_{r,i} g^(r m)`.  Reducing modulo `X^q` and
cancelling successively shows `X^q ∣ T_i` for every `i`, so `T_i = 0` by the already proven
lemma `gpow_mod_Xq_indep`, whence every coefficient `a_{r,i}` vanishes. -/
theorem gpow_main_g0 {F : Type*} [Field F] [Fintype F]
    (e : ℕ) (he : 2 ≤ e) (hdiv : e ∣ Fintype.card F - 1) (g : Polynomial F) (hg : g ≠ 0)
    (hg0 : g.eval 0 ≠ 0)
    (hnd : ∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
      g ≠ Polynomial.C a * h ^ p)
    (A₀ : ℕ) (hA₀ : (e:ℕ) * A₀ + (e:ℕ) ^ 3 * (g.natDegree + 1) < Fintype.card F)
    (A : Fin e → Polynomial (Polynomial F))
    (hAd : ∀ r i, ((A r).coeff i).natDegree ≤ A₀)
    (hAn : ∀ r, (A r).natDegree < Fintype.card F)
    (h : ∑ r : Fin e, (A r).eval ((Polynomial.X : Polynomial F) ^ Fintype.card F)
          * g ^ ((r : ℕ) * ((Fintype.card F - 1) / e)) = 0) :
    ∀ r, A r = 0 := by
  classical
  let m : ℕ := (Fintype.card F - 1) / e
  let T : ℕ → Polynomial F := fun i => ∑ r : Fin e, (A r).coeff i * g ^ ((r : ℕ) * m)
  let J : ℕ := Finset.univ.sup (fun r : Fin e => (A r).natDegree)
  have hJle : ∀ r : Fin e, (A r).natDegree ≤ J := fun r =>
    show (A r).natDegree ≤ J from
      Finset.le_sup (f := fun r : Fin e => (A r).natDegree) (Finset.mem_univ r)
  have hJ : ∀ i, J < i → ∀ r : Fin e, (A r).coeff i = 0 := fun i hi r =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hJle r) hi)
  have hTzero : ∀ i, (∀ r : Fin e, (A r).coeff i = 0) → T i = 0 := by
    intro i hi
    show (∑ r : Fin e, (A r).coeff i * g ^ ((r : ℕ) * m)) = 0
    exact Finset.sum_eq_zero (fun r _ => by rw [hi r, zero_mul])
  -- the relation, expanded along the `X ^ #F` powers
  have hExpand : (∑ i ∈ Finset.range (J + 1),
      Polynomial.X ^ (Fintype.card F * i) * T i) = 0 := by
    have h1 : (∑ i ∈ Finset.range (J + 1), Polynomial.X ^ (Fintype.card F * i) * T i)
        = ∑ r : Fin e,
            (∑ i ∈ Finset.range (J + 1),
              (A r).coeff i * Polynomial.X ^ (Fintype.card F * i))
            * g ^ ((r : ℕ) * m) := by
      calc (∑ i ∈ Finset.range (J + 1), Polynomial.X ^ (Fintype.card F * i) * T i)
          = ∑ i ∈ Finset.range (J + 1), ∑ r : Fin e,
              Polynomial.X ^ (Fintype.card F * i) * ((A r).coeff i * g ^ ((r : ℕ) * m)) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            show Polynomial.X ^ (Fintype.card F * i)
                * (∑ r : Fin e, (A r).coeff i * g ^ ((r : ℕ) * m))
              = ∑ r : Fin e,
                  Polynomial.X ^ (Fintype.card F * i) * ((A r).coeff i * g ^ ((r : ℕ) * m))
            rw [Finset.mul_sum]
        _ = ∑ r : Fin e, ∑ i ∈ Finset.range (J + 1),
              Polynomial.X ^ (Fintype.card F * i) * ((A r).coeff i * g ^ ((r : ℕ) * m)) :=
            Finset.sum_comm
        _ = ∑ r : Fin e,
              (∑ i ∈ Finset.range (J + 1),
                (A r).coeff i * Polynomial.X ^ (Fintype.card F * i))
              * g ^ ((r : ℕ) * m) := by
            refine Finset.sum_congr rfl (fun r _ => ?_)
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            ring
    rw [h1]
    have h2 : ∀ r : Fin e,
        (∑ i ∈ Finset.range (J + 1),
          (A r).coeff i * Polynomial.X ^ (Fintype.card F * i))
          = (A r).eval (Polynomial.X ^ Fintype.card F) := by
      intro r
      rw [Polynomial.eval_eq_sum_range'
        (lt_of_le_of_lt (hJle r) (Nat.lt_succ_self J))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [pow_mul]
    simp only [h2]
    exact h
  have main : ∀ k, ∀ r : Fin e, (A r).coeff k = 0 := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro r
      by_cases hk : J < k
      · exact hJ k hk r
      · have hkJ : k ≤ J := Nat.le_of_not_lt hk
        -- `X ^ #F` divides `T k`
        have hTk : Polynomial.X ^ (Fintype.card F) ∣ T k := by
          -- the terms with `i < k` of `hExpand` vanish
          have hsum_k : (∑ i ∈ Finset.range k,
              Polynomial.X ^ (Fintype.card F * i) * T i) = 0 := by
            refine Finset.sum_eq_zero (fun i hi => ?_)
            rw [hTzero i (ih i (Finset.mem_range.mp hi)), mul_zero]
          have hlen : k + (J + 1 - k) = J + 1 := by omega
          have hsplit := Finset.sum_range_add
            (fun i => Polynomial.X ^ (Fintype.card F * i) * T i) k (J + 1 - k)
          rw [hlen, hExpand, hsum_k, zero_add] at hsplit
          -- hsplit : 0 = ∑ i ∈ range (J+1-k), X^(#F*(k+i)) * T (k+i); factor out X^(#F*k)
          have hfac : (∑ i ∈ Finset.range (J + 1 - k),
                Polynomial.X ^ (Fintype.card F * (k + i)) * T (k + i))
              = Polynomial.X ^ (Fintype.card F * k)
                * (∑ i ∈ Finset.range (J + 1 - k),
                    Polynomial.X ^ (Fintype.card F * i) * T (k + i)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [← mul_assoc, ← pow_add,
              show Fintype.card F * (k + i) = Fintype.card F * k + Fintype.card F * i by ring]
          have hU : (∑ i ∈ Finset.range (J + 1 - k),
              Polynomial.X ^ (Fintype.card F * i) * T (k + i)) = 0 := by
            have h0 : Polynomial.X ^ (Fintype.card F * k)
                * (∑ i ∈ Finset.range (J + 1 - k),
                    Polynomial.X ^ (Fintype.card F * i) * T (k + i)) = 0 := by
              rw [← hfac, ← hsplit]
            exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ Polynomial.X_ne_zero)
          -- split off the first term
          have h1 := Finset.sum_range_succ'
            (fun i => Polynomial.X ^ (Fintype.card F * i) * T (k + i)) (J - k)
          have hlen2 : J - k + 1 = J + 1 - k := by omega
          rw [hlen2, hU] at h1
          have hUsplit : (∑ i ∈ Finset.range (J - k),
                Polynomial.X ^ (Fintype.card F * (i + 1)) * T (k + (i + 1))) + T k = 0 := by
            simpa using h1.symm
          refine ⟨-(∑ i ∈ Finset.range (J - k),
              Polynomial.X ^ (Fintype.card F * i) * T (k + (i + 1))), ?_⟩
          have key : Polynomial.X ^ (Fintype.card F)
                * (-(∑ i ∈ Finset.range (J - k),
                    Polynomial.X ^ (Fintype.card F * i) * T (k + (i + 1))))
              = -(∑ i ∈ Finset.range (J - k),
                    Polynomial.X ^ (Fintype.card F * (i + 1)) * T (k + (i + 1))) := by
            rw [mul_neg, Finset.mul_sum, neg_inj]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [← mul_assoc, ← pow_add,
              show Fintype.card F + Fintype.card F * i = Fintype.card F * (i + 1) by ring]
          rw [key]
          exact eq_neg_of_add_eq_zero_right hUsplit
        exact gpow_mod_Xq_indep e he hdiv g hg0 hnd A₀ hA₀
          (fun r => (A r).coeff k) (fun r => hAd r k) hTk r
  intro r
  apply Polynomial.ext
  intro i
  simp [main i r]

end Commons.NumberTheory.Stepanov
