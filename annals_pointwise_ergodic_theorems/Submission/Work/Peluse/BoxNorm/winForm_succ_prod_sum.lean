import Mathlib
import Submission.Work.Peluse.BoxNorm.WinHalf

namespace Work.Peluse.BoxNorm

noncomputable section

open scoped BigOperators

/-- Two-slot variant of `winForm_shift_prod`: the `ω`-product of a family of the form
`u_ω (· + a) · conj (v_ω (· + a'))` splits into the product of the `u_ω` and the conjugate of the
product of the `v_ω`.  (The lemma `winForm_shift_prod` of `WinAux` is the case `u = v`.) -/
lemma winForm_shift_prod_two {n : ℕ} (Q : Fin n → Finset ℤ) (W : Finset ℤ)
    (u v : (Fin n → Bool) → ℤ → ℂ) (a a' : ℤ) :
    winForm n Q W (fun ω y => u ω (y + a) * star (v ω (y + a')))
      = ∑ z : Tuple n Q, ∑ z' : Tuple n Q, ∑ x ∈ W,
          halfProd n Q u z z' x a * star (halfProd n Q v z z' x a') := by
  simp only [winForm, halfProd]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ =>
    Finset.sum_congr rfl fun x _ => ?_
  exact cube_prod_mul_star (fun ω => u ω (x + Tuple.total (Tuple.corner z z' ω) + a))
    (fun ω => v ω (x + Tuple.total (Tuple.corner z z' ω) + a'))

theorem winForm_succ_prod_sum {n : ℕ} (Q : Fin (n+1) → Finset ℤ) (W : Finset ℤ)
    (φ : (Fin (n+1) → Bool) → ℤ → ℂ) :
    winForm (n+1) Q W φ
      = ∑ p : Tuple n (fun i => Q i.succ) × Tuple n (fun i => Q i.succ),
          ∑ x ∈ W,
            (∑ a' : {x : ℤ // x ∈ Q 0}, halfProd n (fun i => Q i.succ) (slotF φ) p.1 p.2 x a'.1)
              * star (∑ a : {x : ℤ // x ∈ Q 0},
                  halfProd n (fun i => Q i.succ) (slotT φ) p.1 p.2 x a.1) := by
  have hstep : (∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
        winForm n (fun i : Fin n => Q i.succ) W
          (fun ω y => φ (Fin.cases false ω) (y + a'.1)
            * star (φ (Fin.cases true ω) (y + a.1))))
      = ∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          ∑ p : Tuple n (fun i => Q i.succ) × Tuple n (fun i => Q i.succ), ∑ x ∈ W,
            halfProd n (fun i => Q i.succ) (slotF φ) p.1 p.2 x a'.1
              * star (halfProd n (fun i => Q i.succ) (slotT φ) p.1 p.2 x a.1) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    exact (winForm_shift_prod_two (fun i : Fin n => Q i.succ) W (slotF φ) (slotT φ) a'.1 a.1).trans
      (Fintype.sum_prod_type' (fun (z z' : Tuple n (fun i : Fin n => Q i.succ)) =>
        ∑ x ∈ W, halfProd n (fun i => Q i.succ) (slotF φ) z z' x a'.1
          * star (halfProd n (fun i => Q i.succ) (slotT φ) z z' x a.1))).symm
  rw [winForm_succ n Q W φ, hstep]
  exact sum_factor_star W
    (fun (a' : {x : ℤ // x ∈ Q 0})
         (p : Tuple n (fun i => Q i.succ) × Tuple n (fun i => Q i.succ)) (x : ℤ) =>
       halfProd n (fun i => Q i.succ) (slotF φ) p.1 p.2 x a'.1)
    (fun (a : {x : ℤ // x ∈ Q 0})
         (p : Tuple n (fun i => Q i.succ) × Tuple n (fun i => Q i.succ)) (x : ℤ) =>
       halfProd n (fun i => Q i.succ) (slotT φ) p.1 p.2 x a.1)

end

end Work.Peluse.BoxNorm
