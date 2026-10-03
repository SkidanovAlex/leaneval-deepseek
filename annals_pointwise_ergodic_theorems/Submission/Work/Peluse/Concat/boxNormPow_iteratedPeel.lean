import Mathlib
import Submission.Work.Peluse.Ulower.gap_defs
import Submission.Work.Peluse.Concat.boxNormPow_succ_peel_gen

namespace Work.Peluse.Concat

open scoped BigOperators

/-!
# Iterating the peel of the box-norm power

This module proves `Work.Peluse.Concat.boxNormPow_iteratedPeel`: iterating Peluse's level-lowering
recursion `Work.Peluse.Concat.boxNormPow_succ_peel_gen` over the first `m` direction sets of a
concatenated family `Fin.append Q P` expresses the `2^{m+t}`-th power of the box norm as the
`|Q j|⁻²`-weighted average, over all tuples of pairs of shifts from the `Q j`, of the `2^t`-th power
of the box norm of the iterated difference `iterDelta m` on the remaining sets `P`.

The auxiliary material is:

* `boxSumPow_cast` / `boxNormPow_cast` — reindexing a box sum along a `Fin.cast`;
* `peel_append` — the peel `boxNormPow_succ_peel_gen` transported to the `Fin.append` normal form,
  which is what makes the induction go through;
* `piSuccEquiv` / `sum_pi_fin_succ` / `sum_mem_mem_eq_sum_subtype` / `sum_stepRewrite` — the
  bookkeeping of sums over `Fin (m+1)`-tuples and over the square of a subtype;
* `iterDeltaStep_step_comm` / `iterDeltaStep_iterDelta_comm` / `iterDelta_cons_step` / `pairVal_cons`
  — the compatibility of the iterated difference with `Fin.cons`.
-/

/-! ## 1. Reindexing along a `Fin.cast` -/

/-- The box sum is unchanged by reindexing the direction sets along a `Fin.cast`. -/
lemma boxSumPow_cast {a b : ℕ} (h : a = b) (Q : Fin b → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxSumPow a (fun i => Q (Fin.cast h i)) S f = Work.Peluse.boxSumPow b Q S f := by
  cases h
  rfl

/-- The box-norm power is unchanged by reindexing the direction sets along a `Fin.cast`. -/
lemma boxNormPow_cast {a b : ℕ} (h : a = b) (Q : Fin a → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxNormPow a Q S f
      = Work.Peluse.boxNormPow b (fun j => Q (Fin.cast h.symm j)) S f :=
  congrArg (fun z : ℂ => ‖z‖) (boxSumPow_cast h.symm Q S f).symm

/-! ## 2. The peel in the `Fin.append` normal form -/

/-- **Peeling the first coordinate of a concatenated family of direction sets.**  For `t ≥ 1`, the
peel identity `boxNormPow_succ_peel_gen` applied to `Fin.append Q P` reads

`‖f‖^{2^{m+1+t}}_{□_{Q₀,…,Q_m,P₁,…,P_t}} = |Q 0|⁻² ∑_{a,b ∈ Q 0} ‖Δ'_{a,b} f‖^{2^{m+t}}_{□_{Q₁,…,Q_m,P₁,…,P_t}}`.

The point of this form is that the tail of the direction family is again a concatenation,
`Fin.append (Q ∘ Fin.succ) P`, so the identity can be iterated. -/
theorem peel_append {m t : ℕ} (ht : 1 ≤ t) (Q : Fin (m + 1) → Finset ℤ) (P : Fin t → Finset ℤ)
    (S : Finset ℤ) {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNormPow ((m + 1) + t) (Fin.append Q P) S f
      = (((Q 0).card : ℝ))⁻¹ ^ 2 *
        ∑ a ∈ Q 0, ∑ b ∈ Q 0,
          Work.Peluse.boxNormPow (m + t) (Fin.append (fun j : Fin m => Q j.succ) P) S
            (fun u : ℤ => f (u + a) * star (f (u + b))) := by
  have h : (m + 1) + t = (m + t) + 1 := Nat.succ_add m t
  set Q' : Fin ((m + t) + 1) → Finset ℤ := fun i => (Fin.append Q P) (Fin.cast h.symm i) with hQ'
  have hcast : Work.Peluse.boxNormPow ((m + 1) + t) (Fin.append Q P) S f
      = Work.Peluse.boxNormPow ((m + t) + 1) Q' S f := by
    rw [hQ']
    exact boxNormPow_cast h (Fin.append Q P) S f
  rw [hcast, Work.Peluse.Concat.boxNormPow_succ_peel_gen (t := m + t) (by omega) Q' S hf]
  have h0 : Q' 0 = Q 0 := by
    simp only [hQ']
    rw [show Fin.cast h.symm (0 : Fin ((m + t) + 1)) = (0 : Fin ((m + 1) + t)) from Fin.ext rfl]
    rw [show (0 : Fin ((m + 1) + t)) = Fin.castAdd t (0 : Fin (m + 1)) from Fin.ext rfl,
      Fin.append_left]
  have htail : (fun i : Fin (m + t) => Q' i.succ)
      = Fin.append (fun j : Fin m => Q j.succ) P := by
    simp only [hQ']
    funext i
    refine Fin.addCases (motive := fun i : Fin (m + t) =>
        (Fin.append Q P) (Fin.cast (Nat.succ_add m t).symm i.succ)
          = (Fin.append (fun j : Fin m => Q j.succ) P) i) ?_ ?_ i
    · intro j
      rw [Fin.append_left]
      have h2 : Fin.cast (Nat.succ_add m t).symm (Fin.castAdd t j).succ
          = Fin.castAdd t (Fin.succ j) := Fin.ext rfl
      rw [h2, Fin.append_left]
    · intro j
      rw [Fin.append_right]
      have h2 : Fin.cast (Nat.succ_add m t).symm (Fin.natAdd m j).succ
          = Fin.natAdd (m + 1) j := by
        apply Fin.ext
        simp only [Fin.natAdd, Fin.cast, Fin.succ, Fin.val_mk]
        omega
      rw [h2, Fin.append_right]
  rw [h0, htail]

/-! ## 3. Sums over a dependent `Fin (m+1)`-tuple and over a square of a subtype -/

/-- The equivalence splitting a dependent `Fin (m+1)`-tuple off its head. -/
def piSuccEquiv {m : ℕ} (α : Fin (m + 1) → Type*) :
    ((i : Fin (m + 1)) → α i) ≃ α 0 × ((i : Fin m) → α i.succ) where
  toFun f := ⟨f 0, fun i => f i.succ⟩
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by
    refine Prod.ext ?_ ?_ <;> simp

/-- **Splitting a sum over a dependent `Fin (m+1)`-tuple at its head.** -/
lemma sum_pi_fin_succ {m : ℕ} {α : Fin (m + 1) → Type*} [∀ i, Fintype (α i)]
    {M : Type*} [AddCommMonoid M] (F : ((i : Fin (m + 1)) → α i) → M) :
    (∑ sh, F sh) = ∑ q : α 0, ∑ sh' : ((i : Fin m) → α i.succ), F (Fin.cons q sh') := by
  rw [← Fintype.sum_prod_type
    (f := fun p : α 0 × ((i : Fin m) → α i.succ) => F (Fin.cons p.1 p.2))]
  refine Fintype.sum_equiv (piSuccEquiv α) (fun sh => F sh) _ (fun sh => ?_)
  exact (congrArg F (Fin.cons_self_tail sh)).symm

/-- **A double sum over the members of a finite set as a sum over the square of the subtype.** -/
lemma sum_mem_mem_eq_sum_subtype {s : Finset ℤ} {M : Type*} [AddCommMonoid M]
    (g : ℤ → ℤ → M) :
    (∑ a ∈ s, ∑ b ∈ s, g a b) = ∑ q : ↥s × ↥s, g q.1 q.2 := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.univ_eq_attach]
  rw [Finset.sum_attach s (f := fun z => ∑ y ∈ s.attach, g z ↑y)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact (Finset.sum_attach s (f := fun z => g x z)).symm

/-- **The product/sum rearrangement of one peel step.** -/
lemma sum_stepRewrite {m : ℕ} (Q : Fin (m + 1) → Finset ℤ)
    (H : ((j : Fin (m + 1)) → ↥(Q j) × ↥(Q j)) → ℝ) :
    (∏ j : Fin (m + 1), ((Q j).card : ℝ)⁻¹ ^ 2) *
        (∑ sh : (j : Fin (m + 1)) → ↥(Q j) × ↥(Q j), H sh)
      = (((Q 0).card : ℝ)⁻¹ ^ 2) *
        ((∏ j : Fin m, ((Q j.succ).card : ℝ)⁻¹ ^ 2) *
          (∑ q : ↥(Q 0) × ↥(Q 0),
            ∑ sh' : (j : Fin m) → ↥(Q j.succ) × ↥(Q j.succ), H (Fin.cons q sh'))) := by
  rw [Fin.prod_univ_succ (f := fun j : Fin (m + 1) => ((Q j).card : ℝ)⁻¹ ^ 2)]
  rw [show (∑ sh : (j : Fin (m + 1)) → ↥(Q j) × ↥(Q j), H sh)
      = ∑ q : ↥(Q 0) × ↥(Q 0),
          ∑ sh' : (j : Fin m) → ↥(Q j.succ) × ↥(Q j.succ), H (Fin.cons q sh')
      from sum_pi_fin_succ H]
  ring

/-! ## 4. The iterated difference and `Fin.cons` -/

/-- Two `iterDelta` steps commute. -/
lemma iterDeltaStep_step_comm (p q : ℤ × ℤ) (F : ℤ → ℂ) :
    Work.Peluse.Ulower.iterDeltaStep p (Work.Peluse.Ulower.iterDeltaStep q F)
      = Work.Peluse.Ulower.iterDeltaStep q (Work.Peluse.Ulower.iterDeltaStep p F) := by
  funext x
  simp only [Work.Peluse.Ulower.iterDeltaStep, star_mul, star_star, add_comm, add_left_comm,
    mul_assoc, mul_comm, mul_left_comm]

/-- A single `iterDelta` step commutes with an iterate of `iterDelta`. -/
lemma iterDeltaStep_iterDelta_comm {k : ℕ} (sh : Fin k → ℤ × ℤ) (s : ℤ × ℤ) (F : ℤ → ℂ) :
    Work.Peluse.Ulower.iterDelta k sh (Work.Peluse.Ulower.iterDeltaStep s F)
      = Work.Peluse.Ulower.iterDeltaStep s (Work.Peluse.Ulower.iterDelta k sh F) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show Work.Peluse.Ulower.iterDeltaStep (sh 0)
            (Work.Peluse.Ulower.iterDelta k (fun i => sh i.succ)
              (Work.Peluse.Ulower.iterDeltaStep s F))
          = Work.Peluse.Ulower.iterDeltaStep s
              (Work.Peluse.Ulower.iterDeltaStep (sh 0)
                (Work.Peluse.Ulower.iterDelta k (fun i => sh i.succ) F))
      rw [ih]
      exact (iterDeltaStep_step_comm s (sh 0)
        (Work.Peluse.Ulower.iterDelta k (fun i => sh i.succ) F)).symm

/-- The iterated difference of an `iterDelta` step is the iterated difference with the extra shift
pair put in front. -/
lemma iterDelta_cons_step {k : ℕ} (s : ℤ × ℤ) (sh : Fin k → ℤ × ℤ) (F : ℤ → ℂ) :
    Work.Peluse.Ulower.iterDelta k sh (Work.Peluse.Ulower.iterDeltaStep s F)
      = Work.Peluse.Ulower.iterDelta (k + 1) (Fin.cons s sh) F := by
  rw [iterDeltaStep_iterDelta_comm]
  simp only [Work.Peluse.Ulower.iterDelta, Fin.cons_zero, Fin.cons_succ]

/-- The shift tuple of an iterated difference, after `Fin.cons`. -/
lemma pairVal_cons {m : ℕ} {A : Fin (m + 1) → Finset ℤ} (q : ↥(A 0) × ↥(A 0))
    (t : (j : Fin m) → ↥(A j.succ) × ↥(A j.succ)) :
    (fun j : Fin (m + 1) =>
        Prod.mk (((Fin.cons (α := fun j : Fin (m + 1) => ↥(A j) × ↥(A j)) q t) j).1 : ℤ)
          (((Fin.cons (α := fun j : Fin (m + 1) => ↥(A j) × ↥(A j)) q t) j).2 : ℤ))
      = Fin.cons (α := fun _ : Fin (m + 1) => ℤ × ℤ) ((q.1 : ℤ), (q.2 : ℤ))
          (fun i : Fin m => (((t i).1 : ℤ), ((t i).2 : ℤ))) := by
  funext j
  refine Fin.cases ?_ ?_ j <;> simp

/-! ## 5. The iterated peel -/

/-- **Iterating the peel.** -/
theorem iterPeel_aux (m : ℕ) : ∀ (t : ℕ) (ht : 1 ≤ t) (Q : Fin m → Finset ℤ)
    (P : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ), Work.Peluse.FinSuppZ f →
    Work.Peluse.boxNormPow (m + t) (Fin.append Q P) S f
      = ((∏ j : Fin m, (((Q j).card : ℝ))⁻¹ ^ 2) *
          ∑ sh : (j : Fin m) → ↥(Q j) × ↥(Q j),
            Work.Peluse.boxNormPow t P S
              (Work.Peluse.Ulower.iterDelta m
                (fun j : Fin m => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f)) := by
  induction m with
  | zero =>
      intro t ht Q P S f hf
      have hL : Work.Peluse.boxNormPow (0 + t) (Fin.append (Q : Fin 0 → Finset ℤ) P) S f
          = Work.Peluse.boxNormPow t P S f := by
        have hQ : (Q : Fin 0 → Finset ℤ) = Fin.elim0 := funext (fun i => i.elim0)
        rw [hQ, Fin.elim0_append]
        exact congrArg (fun z : ℂ => ‖z‖) (boxSumPow_cast (Nat.zero_add t) P S f)
      have hR : (∏ j : Fin 0, (((Q j).card : ℝ))⁻¹ ^ 2) *
            (∑ sh : (j : Fin 0) → ↥(Q j) × ↥(Q j),
              Work.Peluse.boxNormPow t P S
                (Work.Peluse.Ulower.iterDelta 0
                  (fun j : Fin 0 => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f))
          = Work.Peluse.boxNormPow t P S f := by
        rw [Fin.prod_univ_zero, one_mul]
        rw [Fintype.sum_subsingleton
              (f := fun sh : (j : Fin 0) → ↥(Q j) × ↥(Q j) =>
                Work.Peluse.boxNormPow t P S
                  (Work.Peluse.Ulower.iterDelta 0
                    (fun j : Fin 0 => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f))
              (a := fun j => j.elim0)]
        rw [Work.Peluse.Ulower.iterDelta_zero]
      rw [hL, hR]
  | succ m ih =>
      intro t ht Q P S f hf
      have hfs : ∀ a b : ℤ,
          Work.Peluse.FinSuppZ (fun u : ℤ => f (u + a) * star (f (u + b))) := by
        intro a b
        obtain ⟨N, hN⟩ := hf
        refine ⟨max (N + a.natAbs) (N + b.natAbs), fun u hu => ?_⟩
        have h1 : f (u + a) = 0 := by
          apply hN
          have htri : u.natAbs ≤ (u + a).natAbs + a.natAbs := by
            have h' := Int.natAbs_add_le (u + a) (-a)
            simpa [Int.natAbs_neg, add_assoc] using h'
          have hlt : N + a.natAbs < u.natAbs := lt_of_le_of_lt (le_max_left _ _) hu
          omega
        have h2 : f (u + b) = 0 := by
          apply hN
          have htri : u.natAbs ≤ (u + b).natAbs + b.natAbs := by
            have h' := Int.natAbs_add_le (u + b) (-b)
            simpa [Int.natAbs_neg, add_assoc] using h'
          have hlt : N + b.natAbs < u.natAbs := lt_of_le_of_lt (le_max_right _ _) hu
          omega
        simp [h1, h2]
      have hIH : ∀ a ∈ Q 0, ∀ b ∈ Q 0,
          Work.Peluse.boxNormPow (m + t) (Fin.append (fun j : Fin m => Q j.succ) P) S
            (fun u : ℤ => f (u + a) * star (f (u + b)))
          = (∏ j : Fin m, (((Q j.succ).card : ℝ))⁻¹ ^ 2) *
            ∑ sh' : (j : Fin m) → ↥(Q j.succ) × ↥(Q j.succ),
              Work.Peluse.boxNormPow t P S
                (Work.Peluse.Ulower.iterDelta m
                  (fun j : Fin m => (((sh' j).1 : ℤ), ((sh' j).2 : ℤ)))
                  (fun u : ℤ => f (u + a) * star (f (u + b)))) :=
        fun a _ b _ => ih t ht (fun j : Fin m => Q j.succ) P S _ (hfs a b)
      have hstep1 :
          (∑ a ∈ Q 0, ∑ b ∈ Q 0,
            Work.Peluse.boxNormPow (m + t) (Fin.append (fun j : Fin m => Q j.succ) P) S
              (fun u : ℤ => f (u + a) * star (f (u + b))))
          = (∏ j : Fin m, (((Q j.succ).card : ℝ))⁻¹ ^ 2) *
            ∑ q : ↥(Q 0) × ↥(Q 0),
              ∑ sh' : (j : Fin m) → ↥(Q j.succ) × ↥(Q j.succ),
                Work.Peluse.boxNormPow t P S
                  (Work.Peluse.Ulower.iterDelta m
                    (fun j : Fin m => (((sh' j).1 : ℤ), ((sh' j).2 : ℤ)))
                    (fun u : ℤ => f (u + (q.1 : ℤ)) * star (f (u + (q.2 : ℤ))))) := by
        rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => hIH a ha b hb))]
        rw [sum_mem_mem_eq_sum_subtype (s := Q 0)
          (g := fun a b =>
            (∏ j : Fin m, (((Q j.succ).card : ℝ))⁻¹ ^ 2) *
              ∑ sh' : (j : Fin m) → ↥(Q j.succ) × ↥(Q j.succ),
                Work.Peluse.boxNormPow t P S
                  (Work.Peluse.Ulower.iterDelta m
                    (fun j : Fin m => (((sh' j).1 : ℤ), ((sh' j).2 : ℤ)))
                    (fun u : ℤ => f (u + a) * star (f (u + b)))))]
        rw [Finset.mul_sum]
      have hJ : ∀ q : ↥(Q 0) × ↥(Q 0),
          (∑ sh' : (j : Fin m) → ↥(Q j.succ) × ↥(Q j.succ),
              Work.Peluse.boxNormPow t P S
                (Work.Peluse.Ulower.iterDelta m
                  (fun j : Fin m => (((sh' j).1 : ℤ), ((sh' j).2 : ℤ)))
                  (fun u : ℤ => f (u + (q.1 : ℤ)) * star (f (u + (q.2 : ℤ))))))
          = ∑ sh' : (j : Fin m) → ↥(Q j.succ) × ↥(Q j.succ),
              Work.Peluse.boxNormPow t P S
                (Work.Peluse.Ulower.iterDelta (m + 1)
                  (fun j : Fin (m + 1) =>
                    Prod.mk
                      (((Fin.cons (α := fun j : Fin (m + 1) => ↥(Q j) × ↥(Q j)) q sh') j).1 : ℤ)
                      (((Fin.cons (α := fun j : Fin (m + 1) => ↥(Q j) × ↥(Q j)) q sh') j).2 : ℤ)) f) := by
        intro q
        refine Finset.sum_congr rfl (fun sh' _ => ?_)
        show Work.Peluse.boxNormPow t P S
              (Work.Peluse.Ulower.iterDelta m
                (fun j : Fin m => (((sh' j).1 : ℤ), ((sh' j).2 : ℤ)))
                (Work.Peluse.Ulower.iterDeltaStep ((q.1 : ℤ), (q.2 : ℤ)) f))
            = Work.Peluse.boxNormPow t P S
              (Work.Peluse.Ulower.iterDelta (m + 1)
                (fun j : Fin (m + 1) =>
                  Prod.mk
                    (((Fin.cons (α := fun j : Fin (m + 1) => ↥(Q j) × ↥(Q j)) q sh') j).1 : ℤ)
                    (((Fin.cons (α := fun j : Fin (m + 1) => ↥(Q j) × ↥(Q j)) q sh') j).2 : ℤ)) f)
        rw [iterDelta_cons_step (k := m) (s := ((q.1 : ℤ), (q.2 : ℤ)))
            (sh := fun j : Fin m => (((sh' j).1 : ℤ), ((sh' j).2 : ℤ))) (F := f), pairVal_cons]
      rw [peel_append ht Q P S hf, hstep1]
      rw [Finset.sum_congr rfl (fun q _ => hJ q)]
      exact (sum_stepRewrite Q (fun sh : (j : Fin (m + 1)) → ↥(Q j) × ↥(Q j) =>
        Work.Peluse.boxNormPow t P S
          (Work.Peluse.Ulower.iterDelta (m + 1)
            (fun j : Fin (m + 1) => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f))).symm

/-- **Iterated peeling of the box-norm power.**  For `t ≥ 1`, iterating the level-lowering
recursion `boxNormPow_succ_peel_gen` over the first `m` direction sets of a concatenated family
`Fin.append Q P` gives the `|Q j|⁻²`-weighted average, over all tuples of pairs of shifts from the
`Q j`, of the `2^t`-th power of the box norm of the iterated difference `iterDelta m` on the
remaining direction sets `P`. -/
theorem boxNormPow_iteratedPeel {t m : ℕ} (ht : 1 ≤ t) (Q : Fin m → Finset ℤ) (P : Fin t → Finset ℤ)
    (S : Finset ℤ) (f : ℤ → ℂ) (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNormPow (m + t) (Fin.append Q P) S f
      = ((∏ j : Fin m, (((Q j).card : ℝ))⁻¹ ^ 2) *
          ∑ sh : (j : Fin m) → ↥(Q j) × ↥(Q j),
            Work.Peluse.boxNormPow t P S
              (Work.Peluse.Ulower.iterDelta m
                (fun j : Fin m => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f)) :=
  iterPeel_aux m t ht Q P S f hf

end Work.Peluse.Concat
