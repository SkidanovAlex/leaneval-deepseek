import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.PET

/-!
# Splitting the cube term along the *last* coordinate

The mirror image of `Work.Peluse.BoxNorm.cubeTerm_cons`: the cube term

`∏_{ω : Fin (n+1) → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')`

of the box norm, with `h = Fin.snoc hs a` and `h' = Fin.snoc hs' b`, splits along the last
coordinate `ω (last n)`: the `ω (last n) = 0` half contributes the cube term of the `n`-tuple
`(hs, hs')` shifted by the last entry `b`, and the `ω (last n) = 1` half contributes the
conjugate of the cube term of `(hs, hs')` shifted by the last entry `a`.

All auxiliary facts are `private`; `Work.Peluse.BoxNorm.WinDefs` owns `weight_eq_sum` and
`star_iterate_succ` in its own namespace.
-/

/-- `weight` as a sum of indicators. -/
private lemma cts_weight_eq_sum {t : ℕ} (ω : Fin t → Bool) :
    Work.Peluse.weight ω = ∑ i : Fin t, if ω i then 1 else 0 := by
  rw [Work.Peluse.weight, Finset.card_filter]

/-- `weight` splits off the last coordinate. -/
private lemma cts_weight_snoc {k : ℕ} (c : Bool) (τ : Fin k → Bool) :
    Work.Peluse.weight (Fin.snoc τ c) = Work.Peluse.weight τ + (if c then 1 else 0) := by
  rw [cts_weight_eq_sum, cts_weight_eq_sum, Fin.sum_univ_castSucc]
  simp

/-- `cornerShift` splits off the last coordinate. -/
private lemma cts_cornerShift_snoc {k : ℕ} (a b : ℤ) (h h' : Fin k → ℤ) (c : Bool)
    (τ : Fin k → Bool) :
    Work.Peluse.cornerShift (Fin.snoc h a) (Fin.snoc h' b) (Fin.snoc τ c)
      = (if c then a else b) + Work.Peluse.cornerShift h h' τ := by
  rw [Work.Peluse.cornerShift, Work.Peluse.cornerShift, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- The `ω (last k) = 0` case of `cts_weight_snoc`. -/
private lemma cts_weight_snoc_false {k : ℕ} (τ : Fin k → Bool) :
    Work.Peluse.weight (Fin.snoc τ false) = Work.Peluse.weight τ := by
  rw [cts_weight_snoc, if_neg (by decide : ¬ (false = true)), Nat.add_zero]

/-- The `ω (last k) = 1` case of `cts_weight_snoc`. -/
private lemma cts_weight_snoc_true {k : ℕ} (τ : Fin k → Bool) :
    Work.Peluse.weight (Fin.snoc τ true) = Work.Peluse.weight τ + 1 := by
  rw [cts_weight_snoc, if_pos (by decide : (true = true))]

/-- The `ω (last k) = 0` case of `cts_cornerShift_snoc`. -/
private lemma cts_cornerShift_snoc_false {k : ℕ} (a b : ℤ) (h h' : Fin k → ℤ)
    (τ : Fin k → Bool) :
    Work.Peluse.cornerShift (Fin.snoc h a) (Fin.snoc h' b) (Fin.snoc τ false)
      = b + Work.Peluse.cornerShift h h' τ := by
  rw [cts_cornerShift_snoc, if_neg (by decide : ¬ (false = true))]

/-- The `ω (last k) = 1` case of `cts_cornerShift_snoc`. -/
private lemma cts_cornerShift_snoc_true {k : ℕ} (a b : ℤ) (h h' : Fin k → ℤ)
    (τ : Fin k → Bool) :
    Work.Peluse.cornerShift (Fin.snoc h a) (Fin.snoc h' b) (Fin.snoc τ true)
      = a + Work.Peluse.cornerShift h h' τ := by
  rw [cts_cornerShift_snoc, if_pos (by decide : (true = true))]

/-- `star^[m+1] = star ∘ star^[m]`, the form needed to pull the last coordinate's conjugation
out of a product. -/
private lemma cts_star_iterate_succ' (m : ℕ) (z : ℂ) : (star^[m+1]) z = star ((star^[m]) z) :=
  Function.iterate_succ_apply' star m z

theorem cubeTerm_snoc {n : ℕ} (hs hs' : Fin n → ℤ) (a b : ℤ) (f : ℤ → ℂ) (x : ℤ) :
    (∏ ω : Fin (n + 1) → Bool,
      (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift (Fin.snoc hs a) (Fin.snoc hs' b) ω)))
      = (∏ τ : Fin n → Bool,
          (star^[Work.Peluse.weight τ]) (f ((x + b) + Work.Peluse.cornerShift hs hs' τ)))
        * star (∏ τ : Fin n → Bool,
          (star^[Work.Peluse.weight τ]) (f ((x + a) + Work.Peluse.cornerShift hs hs' τ))) := by
  classical
  set G : Bool → (Fin n → Bool) → ℂ := fun c τ =>
    (star^[Work.Peluse.weight (Fin.snoc τ c)])
      (f (x + Work.Peluse.cornerShift (Fin.snoc hs a) (Fin.snoc hs' b) (Fin.snoc τ c))) with hG
  have hfalse : ∀ τ : Fin n → Bool,
      G false τ
        = (star^[Work.Peluse.weight τ]) (f ((x + b) + Work.Peluse.cornerShift hs hs' τ)) := by
    intro τ
    simp only [hG]
    rw [cts_weight_snoc_false, cts_cornerShift_snoc_false, ← add_assoc]
  have htrue : ∀ τ : Fin n → Bool,
      G true τ
        = star ((star^[Work.Peluse.weight τ])
            (f ((x + a) + Work.Peluse.cornerShift hs hs' τ))) := by
    intro τ
    simp only [hG]
    rw [cts_weight_snoc_true, cts_cornerShift_snoc_true, cts_star_iterate_succ', ← add_assoc]
  have step1 : (∏ ω : Fin (n+1) → Bool,
      (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift (Fin.snoc hs a) (Fin.snoc hs' b) ω)))
      = ∏ p : Bool × (Fin n → Bool), G p.1 p.2 := by
    refine Fintype.prod_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => Bool)).symm _ _ ?_
    intro ω
    simp only [hG, Fin.snocEquiv_symm_apply]
    simp
  have step2 : (∏ p : Bool × (Fin n → Bool), G p.1 p.2)
      = ∏ c : Bool, ∏ τ : Fin n → Bool, G c τ := Fintype.prod_prod_type _
  have step3 : (∏ c : Bool, ∏ τ : Fin n → Bool, G c τ)
      = (∏ τ : Fin n → Bool, G false τ) * (∏ τ : Fin n → Bool, G true τ) := by
    rw [Fintype.prod_bool, mul_comm]
  have hprod_false : (∏ τ : Fin n → Bool, G false τ)
      = ∏ τ : Fin n → Bool,
          (star^[Work.Peluse.weight τ]) (f ((x + b) + Work.Peluse.cornerShift hs hs' τ)) :=
    Finset.prod_congr rfl fun τ _ => hfalse τ
  have hprod_true : (∏ τ : Fin n → Bool, G true τ)
      = star (∏ τ : Fin n → Bool,
          (star^[Work.Peluse.weight τ]) (f ((x + a) + Work.Peluse.cornerShift hs hs' τ))) := by
    rw [show (∏ τ : Fin n → Bool, G true τ)
        = ∏ τ : Fin n → Bool, star ((star^[Work.Peluse.weight τ])
            (f ((x + a) + Work.Peluse.cornerShift hs hs' τ))) from
      Finset.prod_congr rfl fun τ _ => htrue τ]
    exact (star_prod Finset.univ _).symm
  calc (∏ ω : Fin (n+1) → Bool,
      (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift (Fin.snoc hs a) (Fin.snoc hs' b) ω)))
      = ∏ p : Bool × (Fin n → Bool), G p.1 p.2 := step1
    _ = ∏ c : Bool, ∏ τ : Fin n → Bool, G c τ := step2
    _ = (∏ τ : Fin n → Bool, G false τ) * (∏ τ : Fin n → Bool, G true τ) := step3
    _ = (∏ τ : Fin n → Bool,
          (star^[Work.Peluse.weight τ]) (f ((x + b) + Work.Peluse.cornerShift hs hs' τ)))
        * star (∏ τ : Fin n → Bool,
          (star^[Work.Peluse.weight τ]) (f ((x + a) + Work.Peluse.cornerShift hs hs' τ))) := by
          rw [hprod_false, hprod_true]

end Work.Peluse.PET
