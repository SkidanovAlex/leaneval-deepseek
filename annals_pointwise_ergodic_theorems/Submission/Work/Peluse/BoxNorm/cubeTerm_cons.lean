import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.BoxNorm

/-!
# Splitting the cube term along the first coordinate

The cube term of Peluse's box norm,

`∏_{ω : Fin t → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')`,

splits along the first coordinate `ω 0`: the `ω 0 = 0` half contributes the cube term of the
`k`-tuple `(h, h')` shifted by the head `b = h' 0`, and the `ω 0 = 1` half contributes the
conjugate of the cube term shifted by the head `a = h 0`.  This is the identity
`cubeTerm_cons` used to run the recursion `t → t + 1` on the box norms.

All the auxiliary facts are `private`: `Submission.Work.Peluse.BoxNorm.WinDefs` already owns the
names `weight_eq_sum` and `star_iterate_succ` in this namespace.
-/

/-- `weight` as a sum of indicators. -/
private lemma weight_eq_sum' {t : ℕ} (ω : Fin t → Bool) :
    Work.Peluse.weight ω = ∑ i : Fin t, if ω i then 1 else 0 := by
  rw [Work.Peluse.weight, Finset.card_filter]

/-- `weight` splits off the first coordinate. -/
private lemma weight_cons {k : ℕ} (b : Bool) (τ : Fin k → Bool) :
    Work.Peluse.weight (Fin.cons b τ) = (if b then 1 else 0) + Work.Peluse.weight τ := by
  rw [weight_eq_sum', weight_eq_sum', Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

/-- `cornerShift` splits off the first coordinate. -/
private lemma cornerShift_cons {k : ℕ} (a b : ℤ) (h h' : Fin k → ℤ) (c : Bool)
    (τ : Fin k → Bool) :
    Work.Peluse.cornerShift (Fin.cons a h) (Fin.cons b h') (Fin.cons c τ)
      = (if c then a else b) + Work.Peluse.cornerShift h h' τ := by
  rw [Work.Peluse.cornerShift, Work.Peluse.cornerShift, Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

/-- The `ω 0 = 0` case of `weight_cons`. -/
private lemma weight_cons_false {k : ℕ} (τ : Fin k → Bool) :
    Work.Peluse.weight (Fin.cons false τ) = Work.Peluse.weight τ := by
  rw [weight_cons, if_neg (by decide : ¬ (false = true)), Nat.zero_add]

/-- The `ω 0 = 1` case of `weight_cons`. -/
private lemma weight_cons_true {k : ℕ} (τ : Fin k → Bool) :
    Work.Peluse.weight (Fin.cons true τ) = Work.Peluse.weight τ + 1 := by
  rw [weight_cons, if_pos (by decide : (true = true))]
  exact Nat.add_comm 1 (Work.Peluse.weight τ)

/-- The `ω 0 = 0` case of `cornerShift_cons`. -/
private lemma cornerShift_cons_false {k : ℕ} (a b : ℤ) (h h' : Fin k → ℤ)
    (τ : Fin k → Bool) :
    Work.Peluse.cornerShift (Fin.cons a h) (Fin.cons b h') (Fin.cons false τ)
      = b + Work.Peluse.cornerShift h h' τ := by
  rw [cornerShift_cons, if_neg (by decide : ¬ (false = true))]

/-- The `ω 0 = 1` case of `cornerShift_cons`. -/
private lemma cornerShift_cons_true {k : ℕ} (a b : ℤ) (h h' : Fin k → ℤ)
    (τ : Fin k → Bool) :
    Work.Peluse.cornerShift (Fin.cons a h) (Fin.cons b h') (Fin.cons true τ)
      = a + Work.Peluse.cornerShift h h' τ := by
  rw [cornerShift_cons, if_pos (by decide : (true = true))]

/-- `star^[n+1] = star ∘ star^[n]`, the form needed to pull the first coordinate's conjugation
out of a product.  (`WinDefs.star_iterate_succ` is the other composition order.) -/
private lemma star_iterate_succ' (n : ℕ) (z : ℂ) : (star^[n+1]) z = star ((star^[n]) z) :=
  Function.iterate_succ_apply' star n z

theorem cubeTerm_cons {k : ℕ} (a b : ℤ) (h h' : Fin k → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    (∏ ω : Fin (k+1) → Bool,
      (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift (Fin.cons a h) (Fin.cons b h') ω)))
    = (∏ τ : Fin k → Bool,
        (star^[Work.Peluse.weight τ]) (f ((x + b) + Work.Peluse.cornerShift h h' τ)))
      * star (∏ τ : Fin k → Bool,
        (star^[Work.Peluse.weight τ]) (f ((x + a) + Work.Peluse.cornerShift h h' τ))) := by
  classical
  set G : Bool → (Fin k → Bool) → ℂ := fun c τ =>
    (star^[Work.Peluse.weight (Fin.cons c τ)])
      (f (x + Work.Peluse.cornerShift (Fin.cons a h) (Fin.cons b h') (Fin.cons c τ))) with hG
  have hfalse : ∀ τ : Fin k → Bool,
      G false τ
        = (star^[Work.Peluse.weight τ]) (f ((x + b) + Work.Peluse.cornerShift h h' τ)) := by
    intro τ
    simp only [hG]
    rw [weight_cons_false, cornerShift_cons_false, ← add_assoc]
  have htrue : ∀ τ : Fin k → Bool,
      G true τ
        = star ((star^[Work.Peluse.weight τ])
            (f ((x + a) + Work.Peluse.cornerShift h h' τ))) := by
    intro τ
    simp only [hG]
    rw [weight_cons_true, cornerShift_cons_true, star_iterate_succ', ← add_assoc]
  have step1 : (∏ ω : Fin (k+1) → Bool,
      (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift (Fin.cons a h) (Fin.cons b h') ω)))
      = ∏ p : Bool × (Fin k → Bool), G p.1 p.2 := by
    refine Fintype.prod_equiv (Fin.consEquiv (fun _ : Fin (k+1) => Bool)).symm _ _ ?_
    intro ω
    simp only [hG]
    rw [Fin.consEquiv_symm_apply]
    simp
  have step2 : (∏ p : Bool × (Fin k → Bool), G p.1 p.2)
      = ∏ c : Bool, ∏ τ : Fin k → Bool, G c τ := Fintype.prod_prod_type _
  have step3 : (∏ c : Bool, ∏ τ : Fin k → Bool, G c τ)
      = (∏ τ : Fin k → Bool, G false τ) * (∏ τ : Fin k → Bool, G true τ) := by
    rw [Fintype.prod_bool, mul_comm]
  have hprod_false : (∏ τ : Fin k → Bool, G false τ)
      = ∏ τ : Fin k → Bool,
          (star^[Work.Peluse.weight τ]) (f ((x + b) + Work.Peluse.cornerShift h h' τ)) :=
    Finset.prod_congr rfl fun τ _ => hfalse τ
  have hprod_true : (∏ τ : Fin k → Bool, G true τ)
      = star (∏ τ : Fin k → Bool,
          (star^[Work.Peluse.weight τ]) (f ((x + a) + Work.Peluse.cornerShift h h' τ))) := by
    rw [show (∏ τ : Fin k → Bool, G true τ)
        = ∏ τ : Fin k → Bool, star ((star^[Work.Peluse.weight τ])
            (f ((x + a) + Work.Peluse.cornerShift h h' τ))) from
      Finset.prod_congr rfl fun τ _ => htrue τ]
    exact (star_prod Finset.univ _).symm
  calc (∏ ω : Fin (k+1) → Bool,
      (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift (Fin.cons a h) (Fin.cons b h') ω)))
      = ∏ p : Bool × (Fin k → Bool), G p.1 p.2 := step1
    _ = ∏ c : Bool, ∏ τ : Fin k → Bool, G c τ := step2
    _ = (∏ τ : Fin k → Bool, G false τ) * (∏ τ : Fin k → Bool, G true τ) := step3
    _ = (∏ τ : Fin k → Bool,
          (star^[Work.Peluse.weight τ]) (f ((x + b) + Work.Peluse.cornerShift h h' τ)))
        * star (∏ τ : Fin k → Bool,
          (star^[Work.Peluse.weight τ]) (f ((x + a) + Work.Peluse.cornerShift h h' τ))) := by
          rw [hprod_false, hprod_true]

end Work.Peluse.BoxNorm
