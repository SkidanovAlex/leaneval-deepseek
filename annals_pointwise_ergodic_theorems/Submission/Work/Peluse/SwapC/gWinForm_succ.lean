import Mathlib
import Submission.Work.Peluse.SwapC.GDefs

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse

/-! ## Auxiliary lemmas for the first-coordinate recursion of `gWinForm`

`gWinForm (n+1) Y β W φ` sums over pairs of index tuples `z, z' : GIdx (n+1) Y` and over
`Fin (n+1) → Bool`; splitting off the first coordinate of `z` (giving `a = z 0`), of `z'`
(giving `a' = z' 0`) and of `ω` (giving `b = ω 0`) turns the `2^{n+1}`-fold product into a
`2^n`-fold product of a product of two `φ`'s at shifted arguments, which is exactly the inner
`gWinForm n` of the statement.  This mirrors `Work.Peluse.BoxNorm.winForm_succ`, but with
coordinate types `Y i` and direction maps `β i` in place of the coordinate sets `Q i`. -/

/-- `weight` splits at the first coordinate, `false` case. -/
private lemma weight_cons_false {n : ℕ} (τ : Fin n → Bool) :
    Work.Peluse.weight (Fin.cons false τ) = Work.Peluse.weight τ := by
  rw [Work.Peluse.BoxNorm.weight_eq_sum (Fin.cons false τ), Work.Peluse.BoxNorm.weight_eq_sum τ,
    Fin.sum_univ_succ]
  simp

/-- `weight` splits at the first coordinate, `true` case. -/
private lemma weight_cons_true {n : ℕ} (τ : Fin n → Bool) :
    Work.Peluse.weight (Fin.cons true τ) = Work.Peluse.weight τ + 1 := by
  rw [Work.Peluse.BoxNorm.weight_eq_sum (Fin.cons true τ), Work.Peluse.BoxNorm.weight_eq_sum τ,
    Fin.sum_univ_succ]
  simp [Nat.add_comm]

/-- The total shift of a tuple built by `Fin.cons`. -/
private lemma gtotal_cons {n : ℕ} {Y : Fin (n+1) → Type*} (β : (i : Fin (n+1)) → Y i → ℤ)
    (a : Y 0) (zt : (i : Fin n) → Y i.succ) :
    gtotal β (Fin.cons a zt) = β 0 a + gtotal (fun i : Fin n => β i.succ) zt := by
  simp only [gtotal, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- The corner of tuples built by `Fin.cons`. -/
private lemma gcorner_cons {n : ℕ} {Y : Fin (n+1) → Type*}
    (z z' : GIdx (n+1) Y) (b : Bool) (τ : Fin n → Bool) :
    gcorner z z' (Fin.cons b τ)
      = Fin.cons (if b then z 0 else z' 0) (gcorner (Fin.tail z) (Fin.tail z') τ) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp only [gcorner, Fin.cons_zero]
  · intro j
    simp only [gcorner, Fin.cons_succ]
    by_cases h : τ j = true
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]; rfl

/-- The total of the corner splits at the first coordinate, `false` case. -/
private lemma gtotal_corner_false {n : ℕ} {Y : Fin (n+1) → Type*}
    (β : (i : Fin (n+1)) → Y i → ℤ) (z z' : GIdx (n+1) Y) (τ : Fin n → Bool) :
    gtotal β (gcorner z z' (Fin.cons false τ))
      = β 0 (z' 0)
        + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ) := by
  rw [gcorner_cons, gtotal_cons]
  simp

/-- The total of the corner splits at the first coordinate, `true` case. -/
private lemma gtotal_corner_true {n : ℕ} {Y : Fin (n+1) → Type*}
    (β : (i : Fin (n+1)) → Y i → ℤ) (z z' : GIdx (n+1) Y) (τ : Fin n → Bool) :
    gtotal β (gcorner z z' (Fin.cons true τ))
      = β 0 (z 0)
        + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ) := by
  rw [gcorner_cons, gtotal_cons]
  simp

/-- Splitting `(n+1)`-index tuples into the first coordinate and the tail. -/
private def gIdxEquiv (n : ℕ) (Y : Fin (n+1) → Type*) [∀ i, Fintype (Y i)] :
    GIdx (n+1) Y ≃ Y 0 × GIdx n (fun i : Fin n => Y i.succ) where
  toFun z := (z 0, Fin.tail z)
  invFun p := Fin.cons p.1 p.2
  left_inv z := Fin.cons_self_tail z
  right_inv p := by
    obtain ⟨a, w⟩ := p
    exact Prod.ext (Fin.cons_zero a w) (Fin.tail_cons a w)

/-- Splitting the inner product of the box form at the first coordinate: this is the
product-level content of `gWinForm_succ`. -/
private lemma gprod_split {n : ℕ} {Y : Fin (n+1) → Type*}
    (β : (i : Fin (n+1)) → Y i → ℤ) (φ : (Fin (n+1) → Bool) → ℤ → ℂ)
    (z z' : GIdx (n+1) Y) (x : ℤ) :
    (∏ ω : Fin (n+1) → Bool,
        (star^[Work.Peluse.weight ω]) (φ ω (x + gtotal β (gcorner z z' ω))))
      = ∏ τ : Fin n → Bool,
          (star^[Work.Peluse.weight τ])
            (φ (Fin.cons false τ)
                (x + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ)
                  + β 0 (z' 0))
              * star (φ (Fin.cons true τ)
                  (x + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ)
                    + β 0 (z 0)))) := by
  classical
  set G : Bool → (Fin n → Bool) → ℂ := fun c τ =>
    (star^[Work.Peluse.weight (Fin.cons c τ)])
      (φ (Fin.cons c τ) (x + gtotal β (gcorner z z' (Fin.cons c τ)))) with hG
  have hfalse : ∀ τ : Fin n → Bool, G false τ
      = (star^[Work.Peluse.weight τ])
          (φ (Fin.cons false τ)
            (x + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ)
              + β 0 (z' 0))) := by
    intro τ
    simp only [hG]
    rw [weight_cons_false, gtotal_corner_false]
    rw [show x + (β 0 (z' 0)
          + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ))
        = x + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ)
          + β 0 (z' 0) from by ring]
  have htrue : ∀ τ : Fin n → Bool, G true τ
      = star ((star^[Work.Peluse.weight τ])
          (φ (Fin.cons true τ)
            (x + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ)
              + β 0 (z 0)))) := by
    intro τ
    simp only [hG]
    rw [weight_cons_true, gtotal_corner_true, Function.iterate_succ_apply']
    rw [show x + (β 0 (z 0)
          + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ))
        = x + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ)
          + β 0 (z 0) from by ring]
  have step1 : (∏ ω : Fin (n+1) → Bool,
        (star^[Work.Peluse.weight ω]) (φ ω (x + gtotal β (gcorner z z' ω))))
      = ∏ p : Bool × (Fin n → Bool), G p.1 p.2 := by
    refine Fintype.prod_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).symm _ _ ?_
    intro ω
    simp only [hG]
    rw [Fin.consEquiv_symm_apply]
    exact congrArg (fun v : Fin (n+1) → Bool =>
        (star^[Work.Peluse.weight v]) (φ v (x + gtotal β (gcorner z z' v))))
      (Fin.cons_self_tail ω).symm
  have step2 : (∏ p : Bool × (Fin n → Bool), G p.1 p.2)
      = ∏ c : Bool, ∏ τ : Fin n → Bool, G c τ := Fintype.prod_prod_type _
  have step3 : (∏ c : Bool, ∏ τ : Fin n → Bool, G c τ)
      = (∏ τ : Fin n → Bool, G false τ) * (∏ τ : Fin n → Bool, G true τ) := by
    rw [Fintype.prod_bool, mul_comm]
  have hprod_false : (∏ τ : Fin n → Bool, G false τ)
      = ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ])
          (φ (Fin.cons false τ)
            (x + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ)
              + β 0 (z' 0))) :=
    Finset.prod_congr rfl fun τ _ => hfalse τ
  have hprod_true : (∏ τ : Fin n → Bool, G true τ)
      = ∏ τ : Fin n → Bool, star ((star^[Work.Peluse.weight τ])
          (φ (Fin.cons true τ)
            (x + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ)
              + β 0 (z 0)))) :=
    Finset.prod_congr rfl fun τ _ => htrue τ
  calc (∏ ω : Fin (n+1) → Bool,
        (star^[Work.Peluse.weight ω]) (φ ω (x + gtotal β (gcorner z z' ω))))
      = ∏ p : Bool × (Fin n → Bool), G p.1 p.2 := step1
    _ = ∏ c : Bool, ∏ τ : Fin n → Bool, G c τ := step2
    _ = (∏ τ : Fin n → Bool, G false τ) * (∏ τ : Fin n → Bool, G true τ) := step3
    _ = (∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ])
            (φ (Fin.cons false τ)
              (x + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ)
                + β 0 (z' 0))))
        * (∏ τ : Fin n → Bool, star ((star^[Work.Peluse.weight τ])
            (φ (Fin.cons true τ)
              (x + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ)
                + β 0 (z 0))))) := by
          rw [hprod_false, hprod_true]
    _ = ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ])
            (φ (Fin.cons false τ)
              (x + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ)
                + β 0 (z' 0)))
          * star ((star^[Work.Peluse.weight τ])
            (φ (Fin.cons true τ)
              (x + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ)
                + β 0 (z 0)))) := by
          rw [← Finset.prod_mul_distrib]
    _ = ∏ τ : Fin n → Bool,
          (star^[Work.Peluse.weight τ])
            (φ (Fin.cons false τ)
                (x + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ)
                  + β 0 (z' 0))
              * star (φ (Fin.cons true τ)
                  (x + gtotal (fun i : Fin n => β i.succ) (gcorner (Fin.tail z) (Fin.tail z') τ)
                    + β 0 (z 0)))) := by
          refine Finset.prod_congr rfl fun τ _ => ?_
          rw [Work.Peluse.BoxNorm.star_iterate_mul, Work.Peluse.BoxNorm.star_iterate_conj]

theorem gWinForm_succ {n : ℕ} (Y : Fin (n+1) → Type*) [∀ i, Fintype (Y i)]
    (β : (i : Fin (n+1)) → Y i → ℤ) (W : Finset ℤ) (φ : (Fin (n+1) → Bool) → ℤ → ℂ) :
    Work.Peluse.SwapC.gWinForm (n+1) Y β W φ
      = ∑ a : Y 0, ∑ a' : Y 0,
          Work.Peluse.SwapC.gWinForm n (fun i : Fin n => Y i.succ) (fun i : Fin n => β i.succ) W
            (fun ω y => φ (Fin.cons false ω) (y + β 0 a')
              * star (φ (Fin.cons true ω) (y + β 0 a))) := by
  classical
  have hreindex : (∑ z : GIdx (n+1) Y, ∑ z' : GIdx (n+1) Y, ∑ x ∈ W,
        ∏ ω : Fin (n+1) → Bool,
          (star^[Work.Peluse.weight ω]) (φ ω (x + gtotal β (gcorner z z' ω))))
      = ∑ a : Y 0, ∑ zt : GIdx n (fun i : Fin n => Y i.succ),
          ∑ a' : Y 0, ∑ zt' : GIdx n (fun i : Fin n => Y i.succ),
            ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
              (star^[Work.Peluse.weight ω])
                (φ ω (x + gtotal β (gcorner (Fin.cons a zt) (Fin.cons a' zt') ω))) := by
    have hz' : ∀ z : GIdx (n+1) Y,
        (∑ z' : GIdx (n+1) Y, ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
            (star^[Work.Peluse.weight ω]) (φ ω (x + gtotal β (gcorner z z' ω))))
          = ∑ a' : Y 0, ∑ zt' : GIdx n (fun i : Fin n => Y i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + gtotal β (gcorner z (Fin.cons a' zt') ω))) := by
      intro z
      have e1 : (∑ z' : GIdx (n+1) Y, ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
            (star^[Work.Peluse.weight ω]) (φ ω (x + gtotal β (gcorner z z' ω))))
          = ∑ p : Y 0 × GIdx n (fun i : Fin n => Y i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + gtotal β (gcorner z (Fin.cons p.1 p.2) ω))) :=
        (Equiv.sum_comp (gIdxEquiv n Y).symm
          (fun z' : GIdx (n+1) Y => ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
            (star^[Work.Peluse.weight ω]) (φ ω (x + gtotal β (gcorner z z' ω))))).symm
      rw [e1, Fintype.sum_prod_type]
    have hz : (∑ z : GIdx (n+1) Y, ∑ a' : Y 0,
            ∑ zt' : GIdx n (fun i : Fin n => Y i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + gtotal β (gcorner z (Fin.cons a' zt') ω))))
        = ∑ p : Y 0 × GIdx n (fun i : Fin n => Y i.succ),
            ∑ a' : Y 0, ∑ zt' : GIdx n (fun i : Fin n => Y i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + gtotal β (gcorner (Fin.cons p.1 p.2) (Fin.cons a' zt') ω))) :=
      (Equiv.sum_comp (gIdxEquiv n Y).symm
        (fun z : GIdx (n+1) Y => ∑ a' : Y 0,
            ∑ zt' : GIdx n (fun i : Fin n => Y i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + gtotal β (gcorner z (Fin.cons a' zt') ω))))).symm
    have hsplit : (∑ p : Y 0 × GIdx n (fun i : Fin n => Y i.succ),
            ∑ a' : Y 0, ∑ zt' : GIdx n (fun i : Fin n => Y i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + gtotal β (gcorner (Fin.cons p.1 p.2) (Fin.cons a' zt') ω))))
        = ∑ a : Y 0, ∑ zt : GIdx n (fun i : Fin n => Y i.succ),
            ∑ a' : Y 0, ∑ zt' : GIdx n (fun i : Fin n => Y i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + gtotal β (gcorner (Fin.cons a zt) (Fin.cons a' zt') ω))) := by
      rw [Fintype.sum_prod_type]
    calc (∑ z : GIdx (n+1) Y, ∑ z' : GIdx (n+1) Y, ∑ x ∈ W,
            ∏ ω : Fin (n+1) → Bool,
              (star^[Work.Peluse.weight ω]) (φ ω (x + gtotal β (gcorner z z' ω))))
        = ∑ z : GIdx (n+1) Y, ∑ a' : Y 0,
            ∑ zt' : GIdx n (fun i : Fin n => Y i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + gtotal β (gcorner z (Fin.cons a' zt') ω))) :=
          Finset.sum_congr rfl fun z _ => hz' z
      _ = ∑ p : Y 0 × GIdx n (fun i : Fin n => Y i.succ),
            ∑ a' : Y 0, ∑ zt' : GIdx n (fun i : Fin n => Y i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + gtotal β (gcorner (Fin.cons p.1 p.2) (Fin.cons a' zt') ω))) := hz
      _ = ∑ a : Y 0, ∑ zt : GIdx n (fun i : Fin n => Y i.succ),
            ∑ a' : Y 0, ∑ zt' : GIdx n (fun i : Fin n => Y i.succ),
              ∑ x ∈ W, ∏ ω : Fin (n+1) → Bool,
                (star^[Work.Peluse.weight ω])
                  (φ ω (x + gtotal β (gcorner (Fin.cons a zt) (Fin.cons a' zt') ω))) := hsplit
  have hL : gWinForm (n+1) Y β W φ
      = ∑ a : Y 0, ∑ zt : GIdx n (fun i : Fin n => Y i.succ),
          ∑ a' : Y 0, ∑ zt' : GIdx n (fun i : Fin n => Y i.succ),
            ∑ x ∈ W, ∏ τ : Fin n → Bool,
              (star^[Work.Peluse.weight τ])
                (φ (Fin.cons false τ)
                    (x + gtotal (fun i : Fin n => β i.succ) (gcorner zt zt' τ) + β 0 a')
                  * star (φ (Fin.cons true τ)
                      (x + gtotal (fun i : Fin n => β i.succ) (gcorner zt zt' τ) + β 0 a))) := by
    simp only [gWinForm]
    rw [hreindex]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun zt _ => ?_
    refine Finset.sum_congr rfl fun a' _ => ?_
    refine Finset.sum_congr rfl fun zt' _ => ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    refine (gprod_split β φ (Fin.cons a zt) (Fin.cons a' zt') x).trans ?_
    simp only [Fin.tail_cons, Fin.cons_zero]
  have hR : (∑ a : Y 0, ∑ a' : Y 0,
        gWinForm n (fun i : Fin n => Y i.succ) (fun i : Fin n => β i.succ) W
          (fun ω y => φ (Fin.cons false ω) (y + β 0 a')
            * star (φ (Fin.cons true ω) (y + β 0 a))))
      = ∑ a : Y 0, ∑ a' : Y 0, ∑ zt : GIdx n (fun i : Fin n => Y i.succ),
          ∑ zt' : GIdx n (fun i : Fin n => Y i.succ),
            ∑ x ∈ W, ∏ τ : Fin n → Bool,
              (star^[Work.Peluse.weight τ])
                (φ (Fin.cons false τ)
                    (x + gtotal (fun i : Fin n => β i.succ) (gcorner zt zt' τ) + β 0 a')
                  * star (φ (Fin.cons true τ)
                      (x + gtotal (fun i : Fin n => β i.succ) (gcorner zt zt' τ) + β 0 a))) := by
    simp only [gWinForm]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

end

end Work.Peluse.SwapC
