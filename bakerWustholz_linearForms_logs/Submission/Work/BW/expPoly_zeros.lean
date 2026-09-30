import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Zero lemma for exponential polynomials

If a function of the form `t ↦ ∑ᵢ zᵢ^t · pᵢ(t)` over a finite index set `s`, where the distinct
values of `z` number `m`, the polynomials `pᵢ` have degree `≤ d`, and the function vanishes at
`t = 0, 1, …, S` with `(d+1)·m ≤ S+1`, then it vanishes for *every* `t`.

The proof is by induction on the total "weight" `∑_{a} (deg Q_a + 1)` over the distinct bases,
using the finite-difference step `f(t+1) - a₀·f(t)`, which lowers the degree of the `a₀`-component
by one and leaves the others unchanged (or lowers them too).
-/

open Polynomial

namespace Work.BW

/-- Weight of a polynomial: `deg + 1`, with the zero polynomial having weight `0`. This is exactly
the number of "basis monomials" `t ↦ z^t t^k` (`0 ≤ k ≤ deg`) attached to a nonzero polynomial. -/
noncomputable def wt (p : Polynomial ℂ) : ℕ := if p = 0 then 0 else p.natDegree + 1

/-- Total weight of a family of polynomials indexed by a finite set of complex bases. -/
noncomputable def wgt (A : Finset ℂ) (Q : ℂ → Polynomial ℂ) : ℕ := ∑ a ∈ A, wt (Q a)

/-- The finite-difference transform of a family `Q` at the base `a₀`:
`(stepPoly Q a₀) a = C a · taylor 1 (Q a) - C a₀ · Q a`. -/
noncomputable def stepPoly (Q : ℂ → Polynomial ℂ) (a0 : ℂ) : ℂ → Polynomial ℂ :=
  fun a => Polynomial.C a * Polynomial.taylor (1 : ℂ) (Q a) - Polynomial.C a0 * Q a

lemma wt_zero : wt (0 : Polynomial ℂ) = 0 := by simp [wt]

lemma wt_eq {p : Polynomial ℂ} (hp : p ≠ 0) : wt p = p.natDegree + 1 := by
  simp only [wt]; rw [ite_eq_right hp]

/-- The polynomial `q(X+1) - q(X)` drops degree by (at least) one. -/
lemma natDegree_taylor_one_sub_le (q : Polynomial ℂ) :
    (Polynomial.taylor (1 : ℂ) q - q).natDegree ≤ q.natDegree - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_sub]
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | hpos
  · have hm0 : m ≠ 0 := by omega
    have hcq : q.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have hq : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero h0
    rw [hcq, hq]
    simp [Polynomial.coeff_C, hm0]
  · have hmge : q.natDegree ≤ m := by omega
    rcases lt_or_eq_of_le hmge with hlt | heq
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_taylor]; exact hlt),
          coeff_eq_zero_of_natDegree_lt hlt, sub_zero]
    · subst heq
      have hthis : (Polynomial.taylor (1 : ℂ) q).coeff q.natDegree = q.coeff q.natDegree := by
        have e : (Polynomial.taylor (1 : ℂ) q).natDegree = q.natDegree := natDegree_taylor q 1
        conv_lhs => rw [← e]
        rw [coeff_natDegree, leadingCoeff_taylor, coeff_natDegree]
      rw [hthis, sub_self]

lemma taylor_one_ne_zero_iff (p : Polynomial ℂ) : Polynomial.taylor (1 : ℂ) p ≠ 0 ↔ p ≠ 0 := by
  constructor
  · intro h hp; exact h (by rw [hp]; simp)
  · intro hp h
    have h2 : (Polynomial.taylor (1 : ℂ) p).leadingCoeff = 0 := by rw [h]; simp
    rw [leadingCoeff_taylor] at h2
    exact (leadingCoeff_ne_zero.mpr hp) h2

lemma wt_C_mul_le (c : ℂ) (p : Polynomial ℂ) : wt (C c * p) ≤ wt p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [wt]
  · rcases eq_or_ne c 0 with rfl | hc
    · simp [wt]
    · rw [wt_eq (mul_ne_zero (C_ne_zero.mpr hc) hp), wt_eq hp, natDegree_C_mul hc]

lemma wt_taylor (p : Polynomial ℂ) : wt (Polynomial.taylor (1 : ℂ) p) = wt p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [wt]
  · rw [wt_eq hp, wt_eq ((taylor_one_ne_zero_iff p).mpr hp), natDegree_taylor]

lemma wt_sub_le (p q : Polynomial ℂ) : wt (p - q) ≤ max (wt p) (wt q) := by
  rcases eq_or_ne p 0 with rfl | hp
  · rcases eq_or_ne q 0 with rfl | hq
    · simp [wt]
    · rw [zero_sub, wt_eq (neg_ne_zero.mpr hq), natDegree_neg, wt_eq hq]
      exact le_max_right _ _
  · rcases eq_or_ne q 0 with rfl | hq
    · rw [sub_zero, wt_eq hp]
      exact le_max_left _ _
    · rcases eq_or_ne (p - q) 0 with hpq | hpq
      · rw [hpq, wt_zero]; exact Nat.zero_le _
      · rw [wt_eq hpq, wt_eq hp, wt_eq hq]
        calc (p - q).natDegree + 1 ≤ max p.natDegree q.natDegree + 1 :=
              Nat.add_le_add_right (natDegree_sub_le p q) 1
          _ = max (p.natDegree + 1) (q.natDegree + 1) := (max_add_add_right _ _ _).symm

lemma wt_taylor_sub_le (p : Polynomial ℂ) :
    wt (Polynomial.taylor (1 : ℂ) p - p) ≤ p.natDegree := by
  by_cases h : Polynomial.taylor (1 : ℂ) p - p = 0
  · rw [h, wt_zero]; exact Nat.zero_le _
  · have hp1 : 1 ≤ p.natDegree := by
      rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
      · exact absurd (by
          have hq : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero h0
          rw [hq]; simp [taylor_apply]) h
      · exact hpos
    rw [wt_eq h]
    have hd := natDegree_taylor_one_sub_le p
    omega

/-- For `a ≠ a₀` the differenced component keeps its weight. -/
lemma wt_step_off (c d : ℂ) (R : Polynomial ℂ) :
    wt (C c * Polynomial.taylor (1 : ℂ) R - C d * R) ≤ wt R := by
  have h1 : wt (C c * Polynomial.taylor (1 : ℂ) R) ≤ wt R :=
    le_trans (wt_C_mul_le c _) (le_of_eq (wt_taylor R))
  have h2 : wt (C d * R) ≤ wt R := wt_C_mul_le d R
  exact le_trans (wt_sub_le _ _) (max_le h1 h2)

/-- The weight strictly decreases under the finite-difference step at a nonzero component. -/
lemma wgt_step (A : Finset ℂ) (Q : ℂ → Polynomial ℂ) (a0 : ℂ) (ha0 : a0 ∈ A)
    (hQ : Q a0 ≠ 0) : wgt A (stepPoly Q a0) ≤ wgt A Q - 1 := by
  have hsplit1 : wgt A Q = wt (Q a0) + ∑ a ∈ A.erase a0, wt (Q a) :=
    (Finset.add_sum_erase A (fun a => wt (Q a)) ha0).symm
  have hsplit2 : wgt A (stepPoly Q a0) =
      wt (stepPoly Q a0 a0) + ∑ a ∈ A.erase a0, wt (stepPoly Q a0 a) :=
    (Finset.add_sum_erase A (fun a => wt (stepPoly Q a0 a)) ha0).symm
  rw [hsplit1, hsplit2]
  have hdiag : wt (stepPoly Q a0 a0) ≤ (Q a0).natDegree := by
    have heq : stepPoly Q a0 a0 = C a0 * (Polynomial.taylor (1 : ℂ) (Q a0) - Q a0) := by
      simp only [stepPoly]; ring
    rw [heq]
    exact le_trans (wt_C_mul_le a0 _) (wt_taylor_sub_le (Q a0))
  have hrest : ∑ a ∈ A.erase a0, wt (stepPoly Q a0 a) ≤ ∑ a ∈ A.erase a0, wt (Q a) :=
    Finset.sum_le_sum (fun a _ => wt_step_off a a0 (Q a))
  rw [wt_eq hQ]
  calc wt (stepPoly Q a0 a0) + ∑ a ∈ A.erase a0, wt (stepPoly Q a0 a)
      ≤ (Q a0).natDegree + ∑ a ∈ A.erase a0, wt (Q a) := add_le_add hdiag hrest
    _ = (Q a0).natDegree + 1 + ∑ a ∈ A.erase a0, wt (Q a) - 1 := by omega

/-- The finite-difference identity: `∑_a aᵗ (stepPoly Q a₀ a)(t) = F(t+1) - a₀·F(t)`. -/
lemma step_identity (A : Finset ℂ) (Q : ℂ → Polynomial ℂ) (a0 : ℂ) (t : ℕ) :
    (∑ a ∈ A, a ^ t * ((stepPoly Q a0 a).eval (t : ℂ)))
      = (∑ a ∈ A, a ^ (t + 1) * (Q a).eval ((t + 1 : ℕ) : ℂ))
        - a0 * (∑ a ∈ A, a ^ t * (Q a).eval (t : ℂ)) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hev : (stepPoly Q a0 a).eval (t : ℂ)
      = a * (Q a).eval ((t : ℂ) + 1) - a0 * (Q a).eval (t : ℂ) := by
    simp only [stepPoly, eval_sub, eval_mul, eval_C, taylor_apply, eval_comp, eval_add,
      eval_X]
  rw [hev, pow_succ]
  push_cast
  ring

/-- Core zero lemma: a nonzero exponential polynomial over a *set* of distinct complex bases
weighted by `wgt` cannot vanish on `wgt` consecutive values `0, …, wgt-1` unless it is zero. -/
theorem expPoly_core (A : Finset ℂ) (Q : ℂ → Polynomial ℂ)
    (h : ∀ t : ℕ, t < wgt A Q → (∑ a ∈ A, a ^ t * (Q a).eval (t : ℂ)) = 0) :
    ∀ t : ℕ, (∑ a ∈ A, a ^ t * (Q a).eval (t : ℂ)) = 0 := by
  suffices H : ∀ N, ∀ (A : Finset ℂ) (Q : ℂ → Polynomial ℂ), wgt A Q = N →
      (∀ t : ℕ, t < wgt A Q → (∑ a ∈ A, a ^ t * (Q a).eval (t : ℂ)) = 0) →
      ∀ t : ℕ, (∑ a ∈ A, a ^ t * (Q a).eval (t : ℂ)) = 0 by
    exact H _ A Q rfl h
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro A Q hN hzero
    by_cases hex : ∃ a ∈ A, Q a ≠ 0
    · obtain ⟨a0, ha0, hQa0⟩ := hex
      have hwpos : 1 ≤ wgt A Q := by
        have hle : wt (Q a0) ≤ wgt A Q := by
          rw [wgt]
          exact Finset.single_le_sum (f := fun a => wt (Q a)) (fun a _ => Nat.zero_le _) ha0
        rw [wt_eq hQa0] at hle
        omega
      have hw' : wgt A (stepPoly Q a0) ≤ wgt A Q - 1 := wgt_step A Q a0 ha0 hQa0
      have hlt : wgt A (stepPoly Q a0) < N := by rw [← hN]; omega
      have hzero' : ∀ t : ℕ, t < wgt A (stepPoly Q a0) →
          (∑ a ∈ A, a ^ t * ((stepPoly Q a0 a).eval (t : ℂ))) = 0 := by
        intro t ht
        have ht1 : t + 1 < wgt A Q := by omega
        have ht0 : t < wgt A Q := by omega
        rw [step_identity A Q a0 t, hzero (t + 1) ht1, hzero t ht0, mul_zero, sub_zero]
      have hrec : ∀ t : ℕ, (∑ a ∈ A, a ^ t * ((stepPoly Q a0 a).eval (t : ℂ))) = 0 :=
        ih (wgt A (stepPoly Q a0)) hlt A (stepPoly Q a0) rfl hzero'
      have hstep : ∀ t : ℕ, (∑ a ∈ A, a ^ (t + 1) * (Q a).eval ((t + 1 : ℕ) : ℂ))
          = a0 * (∑ a ∈ A, a ^ t * (Q a).eval (t : ℂ)) := by
        intro t
        have h1 := hrec t
        rw [step_identity A Q a0 t, sub_eq_zero] at h1
        exact h1
      have h0 : (∑ a ∈ A, a ^ 0 * (Q a).eval ((0 : ℕ) : ℂ)) = 0 := hzero 0 hwpos
      intro t
      induction t with
      | zero => simpa using h0
      | succ n ih2 => rw [hstep n, ih2, mul_zero]
    · intro t
      refine Finset.sum_eq_zero (fun a ha => ?_)
      have hqa : Q a = 0 := by
        by_contra hc
        exact hex ⟨a, ha, hc⟩
      rw [hqa]; simp

/-- **Zero lemma for exponential polynomials.** If `∑ᵢ zᵢᵗ pᵢ(t)` vanishes for `t = 0, …, S`
where `S + 1 ≥ (d+1)·#{distinct values of z}` and `deg pᵢ ≤ d`, then it vanishes for all `t`. -/
theorem expPoly_zeros {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ι → ℂ) (p : ι → Polynomial ℂ)
    (d : ℕ) (hp : ∀ i ∈ s, (p i).natDegree ≤ d) (S : ℕ)
    (hS : (d + 1) * (s.image z).card ≤ S + 1)
    (hzero : ∀ t, t ≤ S → ∑ i ∈ s, z i ^ t * (p i).eval (t : ℂ) = 0) :
    ∀ t : ℕ, ∑ i ∈ s, z i ^ t * (p i).eval (t : ℂ) = 0 := by
  classical
  set A : Finset ℂ := s.image z with hA
  set Q : ℂ → Polynomial ℂ := (fun a => ∑ i ∈ s.filter (fun i => z i = a), p i) with hQ
  -- Fiber decomposition: the grouped sum equals the original sum.
  have hfib : ∀ t : ℕ, (∑ a ∈ A, a ^ t * (Q a).eval (t : ℂ))
      = ∑ i ∈ s, z i ^ t * (p i).eval (t : ℂ) := by
    intro t
    have hmap : ∀ i ∈ s, z i ∈ A := by
      intro i hi; rw [hA]; exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmap (fun i => z i ^ t * (p i).eval (t : ℂ))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hQ]
    simp only
    rw [Polynomial.eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [(Finset.mem_filter.mp hi).2]
  -- Degree bound after grouping.
  have hQdeg : ∀ a ∈ A, (Q a).natDegree ≤ d := by
    intro a _
    rw [hQ]
    exact Polynomial.natDegree_sum_le_of_forall_le (s.filter (fun i => z i = a)) (fun i => p i)
      (fun i hi => hp i (Finset.mem_of_mem_filter i hi))
  have hwbound : wgt A Q ≤ A.card * (d + 1) := by
    rw [wgt]
    calc ∑ a ∈ A, wt (Q a) ≤ ∑ _a ∈ A, (d + 1) :=
          Finset.sum_le_sum (fun a ha => by
            rcases eq_or_ne (Q a) 0 with hq | hq
            · rw [hq, wt_zero]; exact Nat.zero_le _
            · rw [wt_eq hq]; exact Nat.add_le_add_right (hQdeg a ha) 1)
      _ = A.card * (d + 1) := by rw [Finset.sum_const, smul_eq_mul]
  have hzero' : ∀ t, t < wgt A Q → (∑ a ∈ A, a ^ t * (Q a).eval (t : ℂ)) = 0 := by
    intro t ht
    have htS : t ≤ S := by
      have hle : wgt A Q ≤ S + 1 := by
        refine le_trans hwbound ?_
        rw [hA, mul_comm]
        exact hS
      omega
    rw [hfib t]
    exact hzero t htS
  intro t
  rw [← hfib t]
  exact expPoly_core A Q hzero' t

end Work.BW
