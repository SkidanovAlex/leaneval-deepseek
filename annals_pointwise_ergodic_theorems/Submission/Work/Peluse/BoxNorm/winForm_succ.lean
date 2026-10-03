import Mathlib
import Submission.Work.Peluse.BoxNorm.WinDefs

open scoped BigOperators

namespace Work.Peluse.BoxNorm

noncomputable section

/-! ## Auxiliary lemmas for the first-coordinate recursion of the box form

`winForm (n+1) Q W φ` sums over pairs of `(n+1)`-tuples `z, z'` and over `Fin (n+1) → Bool`;
splitting off the first coordinate of `z` (giving `a = z 0`), of `z'` (giving `a' = z' 0`) and of
`ω` (giving `β = ω 0`) turns the `2^{n+1}`-fold product into a `2^n`-fold product of a product of
two `φ`'s at shifted arguments, which is exactly the inner `winForm n` of the statement. -/

/-- `weight` splits at the first coordinate, `false` case. -/
private lemma weight_cases_false {n : ℕ} (τ : Fin n → Bool) :
    Work.Peluse.weight (Fin.cases false τ : Fin (n+1) → Bool) = Work.Peluse.weight τ := by
  rw [weight_cases]
  simp

/-- `weight` splits at the first coordinate, `true` case. -/
private lemma weight_cases_true {n : ℕ} (τ : Fin n → Bool) :
    Work.Peluse.weight (Fin.cases true τ : Fin (n+1) → Bool) = Work.Peluse.weight τ + 1 := by
  rw [weight_cases]
  simp

/-- The tail of a `Fin.cases` tuple is the tail tuple. -/
private lemma tail_cases {n : ℕ} {Q : Fin (n+1) → Finset ℤ} (a : {x : ℤ // x ∈ Q 0})
    (zt : Tuple n (fun i : Fin n => Q i.succ)) : Tuple.tail (Fin.cases a zt) = zt := by
  funext i
  simp only [Tuple.tail, Fin.cases_succ]

/-- The corner total splits at the first coordinate, `false` case. -/
private lemma total_corner_cases_false {n : ℕ} {Q : Fin (n+1) → Finset ℤ}
    (a a' : {x : ℤ // x ∈ Q 0}) (zt zt' : Tuple n (fun i : Fin n => Q i.succ))
    (τ : Fin n → Bool) :
    Tuple.total (Tuple.corner (Fin.cases a zt) (Fin.cases a' zt')
        (Fin.cases false τ : Fin (n+1) → Bool))
      = a'.1 + Tuple.total (Tuple.corner zt zt' τ) := by
  rw [total_corner_cases, tail_cases, tail_cases]
  simp

/-- The corner total splits at the first coordinate, `true` case. -/
private lemma total_corner_cases_true {n : ℕ} {Q : Fin (n+1) → Finset ℤ}
    (a a' : {x : ℤ // x ∈ Q 0}) (zt zt' : Tuple n (fun i : Fin n => Q i.succ))
    (τ : Fin n → Bool) :
    Tuple.total (Tuple.corner (Fin.cases a zt) (Fin.cases a' zt')
        (Fin.cases true τ : Fin (n+1) → Bool))
      = a.1 + Tuple.total (Tuple.corner zt zt' τ) := by
  rw [total_corner_cases, tail_cases, tail_cases]
  simp

/-- Splitting the inner product of the box form at the first coordinate: this is the
product-level content of `winForm_succ`. -/
private lemma prod_split (n : ℕ) (Q : Fin (n+1) → Finset ℤ)
    (φ : (Fin (n+1) → Bool) → ℤ → ℂ)
    (a a' : {x : ℤ // x ∈ Q 0}) (zt zt' : Tuple n (fun i : Fin n => Q i.succ)) (x : ℤ) :
    (∏ ω : Fin (n+1) → Bool,
        (star^[Work.Peluse.weight ω])
          (φ ω (x + Tuple.total (Tuple.corner (Fin.cases a zt) (Fin.cases a' zt') ω))))
      = ∏ τ : Fin n → Bool,
          (star^[Work.Peluse.weight τ])
            (φ (Fin.cases false τ) (x + Tuple.total (Tuple.corner zt zt' τ) + a'.1)
              * star (φ (Fin.cases true τ)
                  (x + Tuple.total (Tuple.corner zt zt' τ) + a.1))) := by
  classical
  set G : Bool → (Fin n → Bool) → ℂ := fun c τ =>
    (star^[Work.Peluse.weight (Fin.cases c τ)])
      (φ (Fin.cases c τ)
        (x + Tuple.total (Tuple.corner (Fin.cases a zt) (Fin.cases a' zt') (Fin.cases c τ))))
    with hG
  have hfalse : ∀ τ : Fin n → Bool, G false τ
      = (star^[Work.Peluse.weight τ])
          (φ (Fin.cases false τ) (x + Tuple.total (Tuple.corner zt zt' τ) + a'.1)) := by
    intro τ
    simp only [hG]
    rw [weight_cases_false, total_corner_cases_false]
    rw [show x + (a'.1 + Tuple.total (Tuple.corner zt zt' τ))
        = x + Tuple.total (Tuple.corner zt zt' τ) + a'.1 from by ring]
  have htrue : ∀ τ : Fin n → Bool, G true τ
      = star ((star^[Work.Peluse.weight τ])
          (φ (Fin.cases true τ) (x + Tuple.total (Tuple.corner zt zt' τ) + a.1))) := by
    intro τ
    simp only [hG]
    rw [weight_cases_true, total_corner_cases_true, Function.iterate_succ_apply']
    rw [show x + (a.1 + Tuple.total (Tuple.corner zt zt' τ))
        = x + Tuple.total (Tuple.corner zt zt' τ) + a.1 from by ring]
  have step1 : (∏ ω : Fin (n+1) → Bool,
        (star^[Work.Peluse.weight ω])
          (φ ω (x + Tuple.total (Tuple.corner (Fin.cases a zt) (Fin.cases a' zt') ω))))
      = ∏ p : Bool × (Fin n → Bool), G p.1 p.2 := by
    refine Fintype.prod_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).symm _ _ ?_
    intro ω
    simp only [hG]
    rw [Fin.consEquiv_symm_apply]
    exact congrArg (fun v : Fin (n+1) → Bool =>
        (star^[Work.Peluse.weight v])
          (φ v (x + Tuple.total (Tuple.corner (Fin.cases a zt) (Fin.cases a' zt') v))))
      (Fin.cons_self_tail ω).symm
  have step2 : (∏ p : Bool × (Fin n → Bool), G p.1 p.2)
      = ∏ c : Bool, ∏ τ : Fin n → Bool, G c τ := Fintype.prod_prod_type _
  have step3 : (∏ c : Bool, ∏ τ : Fin n → Bool, G c τ)
      = (∏ τ : Fin n → Bool, G false τ) * (∏ τ : Fin n → Bool, G true τ) := by
    rw [Fintype.prod_bool, mul_comm]
  have hprod_false : (∏ τ : Fin n → Bool, G false τ)
      = ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ])
          (φ (Fin.cases false τ) (x + Tuple.total (Tuple.corner zt zt' τ) + a'.1)) :=
    Finset.prod_congr rfl fun τ _ => hfalse τ
  have hprod_true : (∏ τ : Fin n → Bool, G true τ)
      = ∏ τ : Fin n → Bool, star ((star^[Work.Peluse.weight τ])
          (φ (Fin.cases true τ) (x + Tuple.total (Tuple.corner zt zt' τ) + a.1))) :=
    Finset.prod_congr rfl fun τ _ => htrue τ
  calc (∏ ω : Fin (n+1) → Bool,
        (star^[Work.Peluse.weight ω])
          (φ ω (x + Tuple.total (Tuple.corner (Fin.cases a zt) (Fin.cases a' zt') ω))))
      = ∏ p : Bool × (Fin n → Bool), G p.1 p.2 := step1
    _ = ∏ c : Bool, ∏ τ : Fin n → Bool, G c τ := step2
    _ = (∏ τ : Fin n → Bool, G false τ) * (∏ τ : Fin n → Bool, G true τ) := step3
    _ = (∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ])
            (φ (Fin.cases false τ) (x + Tuple.total (Tuple.corner zt zt' τ) + a'.1)))
        * (∏ τ : Fin n → Bool, star ((star^[Work.Peluse.weight τ])
            (φ (Fin.cases true τ) (x + Tuple.total (Tuple.corner zt zt' τ) + a.1)))) := by
          rw [hprod_false, hprod_true]
    _ = ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ])
            (φ (Fin.cases false τ) (x + Tuple.total (Tuple.corner zt zt' τ) + a'.1))
          * star ((star^[Work.Peluse.weight τ])
            (φ (Fin.cases true τ) (x + Tuple.total (Tuple.corner zt zt' τ) + a.1))) := by
          rw [← Finset.prod_mul_distrib]
    _ = ∏ τ : Fin n → Bool,
          (star^[Work.Peluse.weight τ])
            (φ (Fin.cases false τ) (x + Tuple.total (Tuple.corner zt zt' τ) + a'.1)
              * star (φ (Fin.cases true τ)
                  (x + Tuple.total (Tuple.corner zt zt' τ) + a.1))) := by
          refine Finset.prod_congr rfl fun τ _ => ?_
          rw [star_iterate_mul, star_iterate_conj]

theorem winForm_succ (n : ℕ) (Q : Fin (n+1) → Finset ℤ) (W : Finset ℤ)
    (φ : (Fin (n+1) → Bool) → ℤ → ℂ) :
    Work.Peluse.BoxNorm.winForm (n+1) Q W φ
      = ∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          Work.Peluse.BoxNorm.winForm n (fun i : Fin n => Q i.succ) W
            (fun ω y => φ (Fin.cases false ω) (y + a'.1) * star (φ (Fin.cases true ω) (y + a.1))) := by
  classical
  have hreindex : (∑ z : Tuple (n+1) Q, ∑ z' : Tuple (n+1) Q,
        ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
          (star^[Work.Peluse.weight ω]) (φ ω (x + Tuple.total (Tuple.corner z z' ω))))
      = ∑ a : {x : ℤ // x ∈ Q 0}, ∑ zt : Tuple n (fun i : Fin n => Q i.succ),
          ∑ a' : {x : ℤ // x ∈ Q 0}, ∑ zt' : Tuple n (fun i : Fin n => Q i.succ),
            ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
              (star^[Work.Peluse.weight ω])
                (φ ω (x + Tuple.total (Tuple.corner (Fin.cases a zt) (Fin.cases a' zt') ω))) := by
    have hz' : ∀ z : Tuple (n+1) Q,
        (∑ z' : Tuple (n+1) Q,
            ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
              (star^[Work.Peluse.weight ω]) (φ ω (x + Tuple.total (Tuple.corner z z' ω))))
          = ∑ a' : {x : ℤ // x ∈ Q 0}, ∑ zt' : Tuple n (fun i : Fin n => Q i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + Tuple.total (Tuple.corner z (Fin.cases a' zt') ω))) := by
      intro z
      have e1 : (∑ z' : Tuple (n+1) Q,
            ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
              (star^[Work.Peluse.weight ω]) (φ ω (x + Tuple.total (Tuple.corner z z' ω))))
          = ∑ p : {x : ℤ // x ∈ Q 0} × Tuple n (fun i : Fin n => Q i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + Tuple.total (Tuple.corner z (Fin.cases p.1 p.2) ω))) :=
        (Equiv.sum_comp (tupleEquiv n Q).symm
          (fun z' : Tuple (n+1) Q => ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
            (star^[Work.Peluse.weight ω])
              (φ ω (x + Tuple.total (Tuple.corner z z' ω))))).symm
      rw [e1, Fintype.sum_prod_type]
    have hz : (∑ z : Tuple (n+1) Q, ∑ a' : {x : ℤ // x ∈ Q 0},
            ∑ zt' : Tuple n (fun i : Fin n => Q i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + Tuple.total (Tuple.corner z (Fin.cases a' zt') ω))))
        = ∑ p : {x : ℤ // x ∈ Q 0} × Tuple n (fun i : Fin n => Q i.succ),
            ∑ a' : {x : ℤ // x ∈ Q 0}, ∑ zt' : Tuple n (fun i : Fin n => Q i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + Tuple.total (Tuple.corner (Fin.cases p.1 p.2)
                    (Fin.cases a' zt') ω))) :=
      (Equiv.sum_comp (tupleEquiv n Q).symm
        (fun z : Tuple (n+1) Q => ∑ a' : {x : ℤ // x ∈ Q 0},
            ∑ zt' : Tuple n (fun i : Fin n => Q i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + Tuple.total (Tuple.corner z (Fin.cases a' zt') ω))))).symm
    have hsplit : (∑ p : {x : ℤ // x ∈ Q 0} × Tuple n (fun i : Fin n => Q i.succ),
            ∑ a' : {x : ℤ // x ∈ Q 0}, ∑ zt' : Tuple n (fun i : Fin n => Q i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + Tuple.total (Tuple.corner (Fin.cases p.1 p.2)
                    (Fin.cases a' zt') ω))))
        = ∑ a : {x : ℤ // x ∈ Q 0}, ∑ zt : Tuple n (fun i : Fin n => Q i.succ),
            ∑ a' : {x : ℤ // x ∈ Q 0}, ∑ zt' : Tuple n (fun i : Fin n => Q i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + Tuple.total (Tuple.corner (Fin.cases a zt)
                    (Fin.cases a' zt') ω))) := by
      rw [Fintype.sum_prod_type]
    calc (∑ z : Tuple (n+1) Q, ∑ z' : Tuple (n+1) Q,
            ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
              (star^[Work.Peluse.weight ω]) (φ ω (x + Tuple.total (Tuple.corner z z' ω))))
        = ∑ z : Tuple (n+1) Q, ∑ a' : {x : ℤ // x ∈ Q 0},
            ∑ zt' : Tuple n (fun i : Fin n => Q i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + Tuple.total (Tuple.corner z (Fin.cases a' zt') ω))) :=
          Finset.sum_congr rfl fun z _ => hz' z
      _ = ∑ p : {x : ℤ // x ∈ Q 0} × Tuple n (fun i : Fin n => Q i.succ),
            ∑ a' : {x : ℤ // x ∈ Q 0}, ∑ zt' : Tuple n (fun i : Fin n => Q i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + Tuple.total (Tuple.corner (Fin.cases p.1 p.2)
                    (Fin.cases a' zt') ω))) := hz
      _ = ∑ a : {x : ℤ // x ∈ Q 0}, ∑ zt : Tuple n (fun i : Fin n => Q i.succ),
            ∑ a' : {x : ℤ // x ∈ Q 0}, ∑ zt' : Tuple n (fun i : Fin n => Q i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + Tuple.total (Tuple.corner (Fin.cases a zt)
                    (Fin.cases a' zt') ω))) := hsplit
  have hL : winForm (n+1) Q W φ
      = ∑ a : {x : ℤ // x ∈ Q 0}, ∑ zt : Tuple n (fun i : Fin n => Q i.succ),
          ∑ a' : {x : ℤ // x ∈ Q 0}, ∑ zt' : Tuple n (fun i : Fin n => Q i.succ),
            ∑ x ∈ W, ∏ τ : Fin n → Bool,
              (star^[Work.Peluse.weight τ])
                (φ (Fin.cases false τ) (x + Tuple.total (Tuple.corner zt zt' τ) + a'.1)
                  * star (φ (Fin.cases true τ)
                      (x + Tuple.total (Tuple.corner zt zt' τ) + a.1))) := by
    simp only [winForm]
    rw [hreindex]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun zt _ => ?_
    refine Finset.sum_congr rfl fun a' _ => ?_
    refine Finset.sum_congr rfl fun zt' _ => ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    exact prod_split n Q φ a a' zt zt' x
  have hR : (∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
        winForm n (fun i : Fin n => Q i.succ) W
          (fun ω y => φ (Fin.cases false ω) (y + a'.1)
            * star (φ (Fin.cases true ω) (y + a.1))))
      = ∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          ∑ zt : Tuple n (fun i : Fin n => Q i.succ),
            ∑ zt' : Tuple n (fun i : Fin n => Q i.succ),
              ∑ x ∈ W, ∏ τ : Fin n → Bool,
                (star^[Work.Peluse.weight τ])
                  (φ (Fin.cases false τ) (x + Tuple.total (Tuple.corner zt zt' τ) + a'.1)
                    * star (φ (Fin.cases true τ)
                        (x + Tuple.total (Tuple.corner zt zt' τ) + a.1))) := by
    simp only [winForm]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

end

end Work.Peluse.BoxNorm
