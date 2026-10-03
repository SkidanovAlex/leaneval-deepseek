import Mathlib
import Submission.Work.Peluse.SwapC.concatCore

/-!
# `RestConsSplit`: splitting the `Rest`-product along the first coordinate

`Rest v f y = ∏_{ω ≠ 0} (star^[weight ω]) (f (y + cornerShift v 0 ω))` is the product over the
*nonzero* sign patterns of the asymmetric cube term.  Writing `v = Fin.cons dH u` and splitting
`ω = Fin.cons (ω 0) (Fin.tail ω)`, the nonzero patterns fall into

* `ω 0 = true` (all of them, indexed by `τ : Fin s → Bool`, with `weight = weight τ + 1` and
  corner shift `dH + cornerShift u 0 τ`), and
* `ω 0 = false` with `τ ≠ 0` (with `weight = weight τ` and corner shift `cornerShift u 0 τ`).

Hence `Rest (Fin.cons dH u) f y` factors into the two products displayed in `RestConsSplit`.
-/

namespace Work.Peluse.SwapC

open scoped BigOperators

noncomputable section

/-! ## Elementary facts about `weight` and `cornerShift` under `Fin.cons` -/

/-- `cornerShift` splits off the first coordinate. -/
lemma restCons_cornerShift_cons {t : ℕ} (a b : Fin (t + 1) → ℤ) (c : Bool) (ω : Fin t → Bool) :
    Work.Peluse.cornerShift a b (Fin.cons c ω) =
      (if c then a 0 else b 0) +
        Work.Peluse.cornerShift (Fin.tail a) (Fin.tail b) ω := by
  rw [Work.Peluse.cornerShift, Work.Peluse.cornerShift, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]

/-- `cornerShift`, first coordinate `true`, specialised to `a = Fin.cons dH u`, `b = 0`. -/
lemma restCons_cornerShift_cons_true {t : ℕ} (dH : ℤ) (u : Fin t → ℤ) (ω : Fin t → Bool) :
    Work.Peluse.cornerShift (Fin.cons dH u) (fun _ => (0 : ℤ)) (Fin.cons true ω) =
      dH + Work.Peluse.cornerShift u (fun _ => (0 : ℤ)) ω := by
  rw [restCons_cornerShift_cons]
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [if_pos trivial]
  rfl

/-- `cornerShift`, first coordinate `false`, specialised to `a = Fin.cons dH u`, `b = 0`. -/
lemma restCons_cornerShift_cons_false {t : ℕ} (dH : ℤ) (u : Fin t → ℤ) (ω : Fin t → Bool) :
    Work.Peluse.cornerShift (Fin.cons dH u) (fun _ => (0 : ℤ)) (Fin.cons false ω) =
      Work.Peluse.cornerShift u (fun _ => (0 : ℤ)) ω := by
  rw [restCons_cornerShift_cons]
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [if_neg (by decide : ¬ ((false : Bool) = true)), zero_add]
  rfl

/-- `weight` splits off the first coordinate. -/
lemma restCons_weight_cons_first {t : ℕ} (c : Bool) (ω : Fin t → Bool) :
    Work.Peluse.weight (Fin.cons c ω) = Work.Peluse.weight ω + (if c then 1 else 0) := by
  have e : ∀ {n : ℕ} (ω : Fin n → Bool),
      Work.Peluse.weight ω = ∑ i, (if ω i = true then 1 else 0) := by
    intro n ω
    rw [Work.Peluse.weight, Finset.card_filter]
  rw [e (Fin.cons c ω), e ω, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, add_comm]

/-- `weight`, first coordinate `true`. -/
lemma restCons_weight_cons_true {t : ℕ} (ω : Fin t → Bool) :
    Work.Peluse.weight (Fin.cons true ω) = Work.Peluse.weight ω + 1 := by
  rw [restCons_weight_cons_first]; rfl

/-- `weight`, first coordinate `false`. -/
lemma restCons_weight_cons_false {t : ℕ} (ω : Fin t → Bool) :
    Work.Peluse.weight (Fin.cons false ω) = Work.Peluse.weight ω := by
  rw [restCons_weight_cons_first]; rfl

/-! ## The zero pattern under `Fin.cons` -/

lemma restCons_tail_zero {n : ℕ} : Fin.tail (0 : Fin (n + 1) → Bool) = 0 := by
  funext i; rfl

lemma restCons_cons_false_zero {n : ℕ} :
    Fin.cons false (0 : Fin n → Bool) = (0 : Fin (n + 1) → Bool) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => rfl

lemma restCons_cons_true_ne_zero {n : ℕ} (τ : Fin n → Bool) :
    Fin.cons true τ ≠ (0 : Fin (n + 1) → Bool) := by
  intro h
  have h' := congrFun h (0 : Fin (n + 1))
  simp [Fin.cons_zero] at h'

lemma restCons_cons_false_eq_zero {n : ℕ} (τ : Fin n → Bool) :
    Fin.cons false τ = (0 : Fin (n + 1) → Bool) ↔ τ = 0 := by
  constructor
  · intro h
    have h' := congrArg Fin.tail h
    rw [Fin.tail_cons, restCons_tail_zero] at h'
    exact h'
  · rintro rfl
    exact restCons_cons_false_zero

/-! ## Two products lemmas -/

/-- A product over `s.erase a` as a product over `s` with an `if`. -/
lemma restCons_prod_erase_eq_prod_ite {ι M : Type*} [CommMonoid M] [DecidableEq ι]
    (s : Finset ι) (a : ι) (f : ι → M) :
    (∏ x ∈ s.erase a, f x) = ∏ x ∈ s, (if x = a then 1 else f x) := by
  by_cases ha : a ∈ s
  · have h1 : (∏ x ∈ s, (if x = a then 1 else f x))
        = ∏ x ∈ s.erase a, (if x = a then 1 else f x) := by
      conv_lhs => rw [← Finset.insert_erase ha]
      rw [Finset.prod_insert (Finset.notMem_erase a s), if_pos rfl, one_mul]
    rw [h1]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [if_neg (Finset.mem_erase.mp hx).1]
  · rw [Finset.erase_eq_of_notMem ha]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [if_neg]
    exact fun h => ha (h ▸ hx)

/-- Reindexing a product over `Fin (n+1) → Bool` by the first coordinate. -/
lemma restCons_prod_cons_reindex {n : ℕ} {M : Type*} [CommMonoid M]
    (T : (Fin (n + 1) → Bool) → M) :
    (∏ ω : Fin (n + 1) → Bool, T ω)
      = ∏ p : Bool × (Fin n → Bool), T (Fin.cons p.1 p.2) := by
  refine Fintype.prod_equiv
    { toFun := fun ω => (ω 0, Fin.tail ω)
      invFun := fun p => Fin.cons p.1 p.2
      left_inv := fun ω => Fin.cons_self_tail ω
      right_inv := fun p => by ext <;> simp } T
    (fun p : Bool × (Fin n → Bool) => T (Fin.cons p.1 p.2)) ?_
  intro ω
  show T ω = T (Fin.cons (ω 0) (Fin.tail ω))
  rw [Fin.cons_self_tail]

/-- **Splitting an erased product over `Fin (n+1) → Bool` along the first coordinate.** -/
lemma restCons_prod_erase_cons {n : ℕ} {M : Type*} [CommMonoid M]
    (T : (Fin (n + 1) → Bool) → M) :
    (∏ ω ∈ (Finset.univ : Finset (Fin (n + 1) → Bool)).erase 0, T ω)
      = (∏ τ : Fin n → Bool, T (Fin.cons true τ)) *
        (∏ τ ∈ (Finset.univ : Finset (Fin n → Bool)).erase 0, T (Fin.cons false τ)) := by
  have hstep : (∏ ω ∈ (Finset.univ : Finset (Fin (n + 1) → Bool)).erase 0, T ω)
      = ∏ ω : Fin (n + 1) → Bool, (if ω = 0 then (1 : M) else T ω) :=
    restCons_prod_erase_eq_prod_ite _ _ _
  rw [hstep,
    restCons_prod_cons_reindex (fun ω : Fin (n + 1) → Bool => if ω = 0 then (1 : M) else T ω)]
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    rw [if_neg (restCons_cons_true_ne_zero τ)]
  · rw [restCons_prod_erase_eq_prod_ite (Finset.univ : Finset (Fin n → Bool)) 0
      (fun τ => T (Fin.cons false τ))]
    refine Finset.prod_congr rfl fun τ _ => ?_
    by_cases h : τ = 0
    · rw [if_pos ((restCons_cons_false_eq_zero τ).mpr h), if_pos h]
    · rw [if_neg (fun hc => h ((restCons_cons_false_eq_zero τ).mp hc)), if_neg h]

/-! ## The target -/

theorem RestConsSplit {s : ℕ} (dH : ℤ) (u : Fin s → ℤ) (f : ℤ → ℂ) (y : ℤ) :
    Rest (Fin.cons dH u) f y =
      (∏ τ : Fin s → Bool, (star^[weight τ + 1]) (f (y + dH + cornerShift u (fun _ => 0) τ)))
      * (∏ τ ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
          (star^[weight τ]) (f (y + cornerShift u (fun _ => 0) τ))) := by
  simp only [Rest]
  rw [restCons_prod_erase_cons (T := fun ω : Fin (s + 1) → Bool =>
        (star^[weight ω]) (f (y + cornerShift (Fin.cons dH u) (fun _ => 0) ω)))]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    rw [restCons_weight_cons_true, restCons_cornerShift_cons_true, add_assoc]
  · refine Finset.prod_congr rfl fun τ _ => ?_
    rw [restCons_weight_cons_false, restCons_cornerShift_cons_false]

end

end Work.Peluse.SwapC
