import Mathlib
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow
import Submission.Work.Peluse.BoxNorm.WinDefs

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

/-! ## Auxiliary facts about `weight` and `cornerShift` -/

/-- `weight` splits off the first coordinate. -/
private lemma weight_cons {k : ℕ} (b : Bool) (τ : Fin k → Bool) :
    Work.Peluse.weight (Fin.cons (α := fun _ : Fin (k+1) => Bool) b τ)
      = Work.Peluse.weight τ + (if b then 1 else 0) := by
  rw [Work.Peluse.BoxNorm.weight_eq_sum, Work.Peluse.BoxNorm.weight_eq_sum, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- `cornerShift` splits off the first coordinate. -/
private lemma cornerShift_cons {k : ℕ} (a b : ℤ) (h h' : Fin k → ℤ) (c : Bool) (τ : Fin k → Bool) :
    Work.Peluse.cornerShift (Fin.cons (α := fun _ : Fin (k+1) => ℤ) a h)
        (Fin.cons (α := fun _ : Fin (k+1) => ℤ) b h')
        (Fin.cons (α := fun _ : Fin (k+1) => Bool) c τ)
      = (if c then a else b) + Work.Peluse.cornerShift h h' τ := by
  rw [Work.Peluse.cornerShift, Work.Peluse.cornerShift, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- Swapping two nested finite sums. -/
private lemma sum_swap₂ {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℂ) :
    (∑ x, ∑ y, f x y) = ∑ y, ∑ x, f x y :=
  Finset.sum_comm

/-- Permuting four nested finite sums `(hs, a, hs', b) ↦ (a, b, hs, hs')`. -/
private lemma sum4_perm {H A : Type*} [Fintype H] [Fintype A] (f : H → A → H → A → ℂ) :
    (∑ hs, ∑ a, ∑ hs', ∑ b, f hs a hs' b) = ∑ a, ∑ b, ∑ hs, ∑ hs', f hs a hs' b := by
  calc ∑ hs, ∑ a, ∑ hs', ∑ b, f hs a hs' b
      = ∑ a, ∑ hs, ∑ hs', ∑ b, f hs a hs' b :=
        sum_swap₂ (fun hs a => ∑ hs', ∑ b, f hs a hs' b)
    _ = ∑ a, ∑ hs, ∑ b, ∑ hs', f hs a hs' b := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.sum_congr rfl (fun hs _ => ?_)
          exact sum_swap₂ (fun hs' b => f hs a hs' b)
    _ = ∑ a, ∑ b, ∑ hs, ∑ hs', f hs a hs' b := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          exact sum_swap₂ (fun hs b => ∑ hs', f hs a hs' b)

/-! ## Splitting the cube term in the first coordinate -/

/-- The cube term of order `t+1` based at `x`, with the two shift tuples split into their first
coordinate and their tail, equals the cube term of order `t` of `Δ'_{(a,b)} g`. -/
private lemma cubeTermZ_cons {t : ℕ} (Q : Fin (t+1) → Finset ℤ) (g : ℤ → ℂ)
    (a b : {y : ℤ // y ∈ Q 0})
    (hs hs' : (i : Fin t) → {x : ℤ // x ∈ Q i.succ}) (x : ℤ) :
    Work.Peluse.BoxNorm.cubeTermZ Q g
        (Fin.cons (α := fun i : Fin (t+1) => {x : ℤ // x ∈ Q i}) a hs)
        (Fin.cons (α := fun i : Fin (t+1) => {x : ℤ // x ∈ Q i}) b hs') x
      = Work.Peluse.BoxNorm.cubeTermZ (fun i : Fin t => Q i.succ)
          (Work.Peluse.DeltaP a.1 b.1 g) hs hs' x := by
  have hpt_true : ∀ τ : Fin t → Bool,
      star^[Work.Peluse.weight (Fin.cons (α := fun _ : Fin (t+1) => Bool) true τ)]
        (g (x + Work.Peluse.cornerShift
            (Fin.cons (α := fun _ : Fin (t+1) => ℤ) a.1 (fun i => (hs i).1))
            (Fin.cons (α := fun _ : Fin (t+1) => ℤ) b.1 (fun i => (hs' i).1))
            (Fin.cons (α := fun _ : Fin (t+1) => Bool) true τ)))
      = star (star^[Work.Peluse.weight τ]
          (g (x + a.1 + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ))) := by
    intro τ
    rw [weight_cons, cornerShift_cons]
    simp only [↓reduceIte]
    rw [Work.Peluse.BoxNorm.star_iterate_succ, Work.Peluse.BoxNorm.star_iterate_conj]
    rw [show x + (a.1 + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ)
        = x + a.1 + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ from by ring]
  have hpt_false : ∀ τ : Fin t → Bool,
      star^[Work.Peluse.weight (Fin.cons (α := fun _ : Fin (t+1) => Bool) false τ)]
        (g (x + Work.Peluse.cornerShift
            (Fin.cons (α := fun _ : Fin (t+1) => ℤ) a.1 (fun i => (hs i).1))
            (Fin.cons (α := fun _ : Fin (t+1) => ℤ) b.1 (fun i => (hs' i).1))
            (Fin.cons (α := fun _ : Fin (t+1) => Bool) false τ)))
      = star^[Work.Peluse.weight τ]
          (g (x + b.1 + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ)) := by
    intro τ
    rw [weight_cons, cornerShift_cons]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rw [show x + (b.1 + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ)
        = x + b.1 + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ from by ring]
  have hpt_mul : ∀ τ : Fin t → Bool,
      star (star^[Work.Peluse.weight τ]
            (g (x + a.1 + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ)))
        * star^[Work.Peluse.weight τ]
            (g (x + b.1 + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ))
      = star^[Work.Peluse.weight τ]
          (Work.Peluse.DeltaP a.1 b.1 g
            (x + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ)) := by
    intro τ
    simp only [Work.Peluse.DeltaP]
    rw [Work.Peluse.BoxNorm.star_iterate_mul, Work.Peluse.BoxNorm.star_iterate_conj]
    rw [show (x + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ) + a.1
          = x + a.1 + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ from by ring,
        show (x + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ) + b.1
          = x + b.1 + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ from by ring]
  rw [Work.Peluse.BoxNorm.cubeTermZ, Work.Peluse.BoxNorm.cubeTermZ,
      Work.Peluse.BoxNorm.Aux.prod_cons_equiv,
      Work.Peluse.BoxNorm.Aux.cons_val a hs, Work.Peluse.BoxNorm.Aux.cons_val b hs']
  rw [Fintype.prod_bool]
  rw [show (∏ τ : Fin t → Bool,
        star^[Work.Peluse.weight (Fin.cons (α := fun _ : Fin (t+1) => Bool) true τ)]
          (g (x + Work.Peluse.cornerShift
              (Fin.cons (α := fun _ : Fin (t+1) => ℤ) a.1 (fun i => (hs i).1))
              (Fin.cons (α := fun _ : Fin (t+1) => ℤ) b.1 (fun i => (hs' i).1))
              (Fin.cons (α := fun _ : Fin (t+1) => Bool) true τ))))
      = (∏ τ : Fin t → Bool, star (star^[Work.Peluse.weight τ]
          (g (x + a.1 + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ)))) from
      Finset.prod_congr rfl (fun τ _ => hpt_true τ),
    show (∏ τ : Fin t → Bool,
        star^[Work.Peluse.weight (Fin.cons (α := fun _ : Fin (t+1) => Bool) false τ)]
          (g (x + Work.Peluse.cornerShift
              (Fin.cons (α := fun _ : Fin (t+1) => ℤ) a.1 (fun i => (hs i).1))
              (Fin.cons (α := fun _ : Fin (t+1) => ℤ) b.1 (fun i => (hs' i).1))
              (Fin.cons (α := fun _ : Fin (t+1) => Bool) false τ))))
      = (∏ τ : Fin t → Bool, star^[Work.Peluse.weight τ]
          (g (x + b.1 + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ))) from
      Finset.prod_congr rfl (fun τ _ => hpt_false τ)]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun τ _ => hpt_mul τ)

/-! ## Splitting the unnormalised box sum -/

/-- The unnormalised box sum of order `t+1` is the sum over the first coordinates `a, b` of the
unnormalised box sum of order `t` of `Δ'_{(a,b)} g`. -/
theorem rawSum_split (t : ℕ) (Q : Fin (t+1) → Finset ℤ) (g : ℤ → ℂ) :
    Work.Peluse.BoxNorm.rawSum (t+1) Q g
      = ∑ a : {y : ℤ // y ∈ Q 0}, ∑ b : {y : ℤ // y ∈ Q 0},
          Work.Peluse.BoxNorm.rawSum t (fun i : Fin t => Q i.succ)
            (Work.Peluse.DeltaP a.1 b.1 g) := by
  simp only [Work.Peluse.BoxNorm.rawSum]
  have hsplit : (∑ h : (i : Fin (t+1)) → {x : ℤ // x ∈ Q i},
        ∑ h' : (i : Fin (t+1)) → {x : ℤ // x ∈ Q i},
          ∑' x : ℤ, ∏ ω : Fin (t+1) → Bool, (star^[Work.Peluse.weight ω])
            (g (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))
      = ∑ hs : (i : Fin t) → {x : ℤ // x ∈ Q i.succ},
          ∑ a : {y : ℤ // y ∈ Q 0},
            ∑ hs' : (i : Fin t) → {x : ℤ // x ∈ Q i.succ},
              ∑ b : {y : ℤ // y ∈ Q 0},
                ∑' x : ℤ, ∏ ω : Fin (t+1) → Bool, (star^[Work.Peluse.weight ω])
                  (g (x + Work.Peluse.cornerShift
                      (fun i => ((Fin.cons (α := fun i : Fin (t+1) => {x : ℤ // x ∈ Q i}) a hs) i).1)
                      (fun i => ((Fin.cons (α := fun i : Fin (t+1) => {x : ℤ // x ∈ Q i}) b hs') i).1)
                      ω)) := by
    refine (Work.Peluse.BoxNorm.Aux.sum_cons_equiv
      (F := fun h => ∑ h' : (i : Fin (t+1)) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin (t+1) → Bool, (star^[Work.Peluse.weight ω])
          (g (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))).trans ?_
    refine Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun a _ => ?_))
    exact Work.Peluse.BoxNorm.Aux.sum_cons_equiv
      (F := fun h' => ∑' x : ℤ, ∏ ω : Fin (t+1) → Bool, (star^[Work.Peluse.weight ω])
          (g (x + Work.Peluse.cornerShift
              (fun i => ((Fin.cons (α := fun i : Fin (t+1) => {x : ℤ // x ∈ Q i}) a hs) i).1)
              (fun i => (h' i).1) ω)))
  have hperm : (∑ hs : (i : Fin t) → {x : ℤ // x ∈ Q i.succ},
          ∑ a : {y : ℤ // y ∈ Q 0},
            ∑ hs' : (i : Fin t) → {x : ℤ // x ∈ Q i.succ},
              ∑ b : {y : ℤ // y ∈ Q 0},
                ∑' x : ℤ, ∏ ω : Fin (t+1) → Bool, (star^[Work.Peluse.weight ω])
                  (g (x + Work.Peluse.cornerShift
                      (fun i => ((Fin.cons (α := fun i : Fin (t+1) => {x : ℤ // x ∈ Q i}) a hs) i).1)
                      (fun i => ((Fin.cons (α := fun i : Fin (t+1) => {x : ℤ // x ∈ Q i}) b hs') i).1)
                      ω)))
      = ∑ a : {y : ℤ // y ∈ Q 0},
          ∑ b : {y : ℤ // y ∈ Q 0},
            ∑ hs : (i : Fin t) → {x : ℤ // x ∈ Q i.succ},
              ∑ hs' : (i : Fin t) → {x : ℤ // x ∈ Q i.succ},
                ∑' x : ℤ, ∏ ω : Fin (t+1) → Bool, (star^[Work.Peluse.weight ω])
                  (g (x + Work.Peluse.cornerShift
                      (fun i => ((Fin.cons (α := fun i : Fin (t+1) => {x : ℤ // x ∈ Q i}) a hs) i).1)
                      (fun i => ((Fin.cons (α := fun i : Fin (t+1) => {x : ℤ // x ∈ Q i}) b hs') i).1)
                      ω)) :=
    sum4_perm _
  have hpoint : ∀ (a b : {y : ℤ // y ∈ Q 0})
      (hs hs' : (i : Fin t) → {x : ℤ // x ∈ Q i.succ}),
      (∑' x : ℤ, ∏ ω : Fin (t+1) → Bool, (star^[Work.Peluse.weight ω])
        (g (x + Work.Peluse.cornerShift
            (fun i => ((Fin.cons (α := fun i : Fin (t+1) => {x : ℤ // x ∈ Q i}) a hs) i).1)
            (fun i => ((Fin.cons (α := fun i : Fin (t+1) => {x : ℤ // x ∈ Q i}) b hs') i).1)
            ω)))
      = ∑' x : ℤ, ∏ τ : Fin t → Bool, (star^[Work.Peluse.weight τ])
        (Work.Peluse.DeltaP a.1 b.1 g
          (x + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ)) := by
    intro a b hs hs'
    refine tsum_congr (fun x => ?_)
    simpa only [Work.Peluse.BoxNorm.cubeTermZ] using cubeTermZ_cons Q g a b hs hs' x
  rw [hsplit, hperm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun hs' _ => ?_))))
  exact hpoint a b hs hs'

/-! ## The main splitting identity -/

theorem boxSumPow_split (t : ℕ) (Q : Fin (t + 1) → Finset ℤ) (S : Finset ℤ) (F : ℤ → ℂ) :
    Work.Peluse.boxSumPow (t + 1) Q S F =
      (((Q 0).card : ℂ) ^ 2)⁻¹ *
        ∑ a : {x : ℤ // x ∈ Q 0}, ∑ b : {x : ℤ // x ∈ Q 0},
          Work.Peluse.boxSumPow t (fun i => Q i.succ) S (Work.Peluse.DeltaP a.1 b.1 F) := by
  have hscale : (Work.Peluse.BoxNorm.boxScaling (t+1) Q S : ℂ)
      = (((Q 0).card : ℂ) ^ 2)⁻¹ *
          (Work.Peluse.BoxNorm.boxScaling t (fun i : Fin t => Q i.succ) S : ℂ) := by
    rw [Work.Peluse.BoxNorm.boxScaling, Work.Peluse.BoxNorm.boxScaling, Fin.prod_univ_succ]
    push_cast
    ring_nf
  have hR : (∑ a : {x : ℤ // x ∈ Q 0}, ∑ b : {x : ℤ // x ∈ Q 0},
        (Work.Peluse.BoxNorm.boxScaling t (fun i : Fin t => Q i.succ) S : ℂ) *
          Work.Peluse.BoxNorm.rawSum t (fun i : Fin t => Q i.succ) (Work.Peluse.DeltaP a.1 b.1 F))
      = (Work.Peluse.BoxNorm.boxScaling t (fun i : Fin t => Q i.succ) S : ℂ) *
          ∑ a : {x : ℤ // x ∈ Q 0}, ∑ b : {x : ℤ // x ∈ Q 0},
            Work.Peluse.BoxNorm.rawSum t (fun i : Fin t => Q i.succ) (Work.Peluse.DeltaP a.1 b.1 F) := by
    calc (∑ a : {x : ℤ // x ∈ Q 0}, ∑ b : {x : ℤ // x ∈ Q 0},
          (Work.Peluse.BoxNorm.boxScaling t (fun i : Fin t => Q i.succ) S : ℂ) *
            Work.Peluse.BoxNorm.rawSum t (fun i : Fin t => Q i.succ) (Work.Peluse.DeltaP a.1 b.1 F))
        = ∑ a : {x : ℤ // x ∈ Q 0},
            (Work.Peluse.BoxNorm.boxScaling t (fun i : Fin t => Q i.succ) S : ℂ) *
              ∑ b : {x : ℤ // x ∈ Q 0},
                Work.Peluse.BoxNorm.rawSum t (fun i : Fin t => Q i.succ) (Work.Peluse.DeltaP a.1 b.1 F) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          exact (Finset.mul_sum Finset.univ (fun b : {x : ℤ // x ∈ Q 0} =>
            Work.Peluse.BoxNorm.rawSum t (fun i : Fin t => Q i.succ) (Work.Peluse.DeltaP a.1 b.1 F))
            (Work.Peluse.BoxNorm.boxScaling t (fun i : Fin t => Q i.succ) S : ℂ)).symm
      _ = (Work.Peluse.BoxNorm.boxScaling t (fun i : Fin t => Q i.succ) S : ℂ) *
            ∑ a : {x : ℤ // x ∈ Q 0}, ∑ b : {x : ℤ // x ∈ Q 0},
              Work.Peluse.BoxNorm.rawSum t (fun i : Fin t => Q i.succ) (Work.Peluse.DeltaP a.1 b.1 F) :=
          (Finset.mul_sum Finset.univ (fun a : {x : ℤ // x ∈ Q 0} =>
            ∑ b : {x : ℤ // x ∈ Q 0},
              Work.Peluse.BoxNorm.rawSum t (fun i : Fin t => Q i.succ) (Work.Peluse.DeltaP a.1 b.1 F))
            (Work.Peluse.BoxNorm.boxScaling t (fun i : Fin t => Q i.succ) S : ℂ)).symm
  simp only [Work.Peluse.BoxNorm.boxSumPow_eq_scaling]
  rw [rawSum_split, hR, hscale]
  ring

end

end Work.Peluse.Ulower
