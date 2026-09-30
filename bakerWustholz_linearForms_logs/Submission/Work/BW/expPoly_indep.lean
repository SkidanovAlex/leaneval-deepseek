import Mathlib
import Submission.Work.BW.expPoly_aux
import Submission.Work.BW.Op_one_iterate_zero
import Submission.Work.BW.Op_iterate_eq_zero
import Submission.Work.BW.sum_step_iterate
import Submission.Work.BW.div_base_vanish

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

namespace Work.BW

/-- Linear independence of the exponential monomials `t ↦ z i ^ t * (Q i).eval t`: if
`t ↦ ∑ i ∈ s, z i ^ t * (Q i).eval (t : ℂ)` vanishes for every `t : ℕ`, and the bases `z i` are
non-zero and pairwise distinct on `s`, then every `Q i` is the zero polynomial.
(Proof: strong induction on `s.card`.  Pick `i₀ ∈ s` with `Q i₀ ≠ 0` and set `z' i = z i / z i₀`, so
that `z' i₀ = 1`.  Applying the finite-difference operator
`Q ↦ C (z' i) * taylor 1 (Q i) - Q i` `((Q i₀).natDegree + 1)` times kills the `i₀`-component
(the base `1` component drops degree each time, `Polynomial.natDegree_taylor_one_sub_le`) and
leaves the other bases unchanged, giving the same vanishing identity for the resulting family on
`s.erase i₀`; the induction hypothesis makes each remaining component zero, i.e.
`z' i * Q i (t+1) = Q i t`, which forces `Q i = 0` since `z' i ≠ 1`; finally `z i₀ ≠ 0` and the
original identity force `Q i₀ = 0`.) -/
theorem expPoly_indep {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ι → ℂ)
    (Q : ι → Polynomial ℂ)
    (hz : ∀ i ∈ s, z i ≠ 0)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, z i = z j → i = j)
    (h : ∀ t : ℕ, ∑ i ∈ s, z i ^ t * (Q i).eval (t : ℂ) = 0) :
    ∀ i ∈ s, Q i = 0 := by
  classical
  -- Strong induction on the finite set, phrased through `Finset.induction_on`.
  have key : ∀ s : Finset ι, ∀ (z : ι → ℂ) (Q : ι → Polynomial ℂ),
      (∀ i ∈ s, z i ≠ 0) → (∀ i ∈ s, ∀ j ∈ s, z i = z j → i = j) →
      (∀ t : ℕ, ∑ i ∈ s, z i ^ t * (Q i).eval (t : ℂ) = 0) →
      ∀ i ∈ s, Q i = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro z Q hz hinj h i hi
        exact absurd hi (Finset.notMem_empty i)
    | insert a s ha ih =>
        intro z Q hz hinj h
        have hza : z a ≠ 0 := hz a (Finset.mem_insert_self a s)
        -- Divide all bases by `z a`, so that the base `a` becomes `1`.
        let w : ι → ℂ := fun i => z i / z a
        have hwa : w a = 1 := by dsimp only [w]; exact div_self hza
        have hzeq : ∀ i, z i = w i * z a := by
          intro i
          dsimp only [w]
          rw [div_mul_cancel₀ (z i) hza]
        have hw0 : ∀ t : ℕ, ∑ i ∈ insert a s, (w i) ^ t * (Q i).eval (t : ℂ) = 0 :=
          div_base_vanish (insert a s) z Q a hza h
        -- Apply the finite-difference operator `Op (w i)` `natDegree (Q a) + 1` times.
        let R : ι → Polynomial ℂ := fun i => ((Op (w i))^[(Q a).natDegree + 1]) (Q i)
        have hR0 : ∀ t : ℕ, ∑ i ∈ insert a s, (w i) ^ t * (R i).eval (t : ℂ) = 0 := by
          intro t
          exact sum_step_iterate (insert a s) w Q hw0 ((Q a).natDegree + 1) t
        -- The `a`-component is annihilated (its base is `1`).
        have hRa : R a = 0 := by
          dsimp only [R]
          rw [hwa]
          exact Op_one_iterate_zero (Q a)
        have hRs : ∀ t : ℕ, ∑ i ∈ s, (w i) ^ t * (R i).eval (t : ℂ) = 0 := by
          intro t
          have ht := hR0 t
          rw [Finset.sum_insert ha] at ht
          simp only [hRa, Polynomial.eval_zero, mul_zero, zero_add] at ht
          exact ht
        -- Induction hypothesis on the remaining set `s`.
        have hz' : ∀ i ∈ s, w i ≠ 0 := by
          intro i hi
          dsimp only [w]
          exact div_ne_zero (hz i (Finset.mem_insert_of_mem hi)) hza
        have hinj' : ∀ i ∈ s, ∀ j ∈ s, w i = w j → i = j := by
          intro i hi j hj hij
          refine hinj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) ?_
          rw [hzeq i, hzeq j, hij]
        have hQs : ∀ i ∈ s, Q i = 0 := by
          intro i hi
          have hRi : R i = 0 := ih w R hz' hinj' hRs i hi
          have hwi1 : w i ≠ 1 := by
            intro hwi
            have hia : i = a := by
              refine hinj i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s) ?_
              rw [hzeq i, hwi, one_mul]
            exact ha (hia ▸ hi)
          dsimp only [R] at hRi
          exact Op_iterate_eq_zero hwi1 (Q i) ((Q a).natDegree + 1) hRi
        -- Finally `Q a = 0` from the original identity.
        have hQa : Q a = 0 := by
          have heval : ∀ t : ℕ, (Q a).eval (t : ℂ) = 0 := by
            intro t
            have ht := h t
            rw [Finset.sum_insert ha] at ht
            have hsum0 : ∑ i ∈ s, z i ^ t * (Q i).eval (t : ℂ) = 0 := by
              refine Finset.sum_eq_zero (fun i hi => ?_)
              rw [hQs i hi, Polynomial.eval_zero, mul_zero]
            rw [hsum0, add_zero] at ht
            exact (mul_eq_zero.mp ht).resolve_left (pow_ne_zero t hza)
          refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
          refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective
            (f := fun t : ℕ => (t : ℂ)) (Nat.cast_injective))
          rintro x ⟨t, rfl⟩
          exact heval t
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hQa
        · exact hQs i hi
  exact key s z Q hz hinj h

end Work.BW
