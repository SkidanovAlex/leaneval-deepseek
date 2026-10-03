import Mathlib
import Submission.Work.Peluse.BoxNorm.WinDefs

namespace Work.Peluse.Ulower

open scoped BigOperators

noncomputable section

/-!
# `lemma74_phase_split`

Splitting the `ω`-sum of Peluse's Lemma 7.4 (the cube expansion of the bilinear average at the
first coordinate).  Writing `ω = Fin.cons (ω 0) (Fin.tail ω)`, the parity sign `(-1)^{|ω|}` turns
the `ω 0 = true` half into the negative of the corresponding `Fin s`-sum.
-/

/-- `weight` splits off the first coordinate (`Fin.cons` form). -/
private lemma weight_cons {k : ℕ} (β : Bool) (τ : Fin k → Bool) :
    Work.Peluse.weight (Fin.cons (α := fun _ : Fin (k+1) => Bool) β τ)
      = Work.Peluse.weight τ + (if β then 1 else 0) := by
  rw [Work.Peluse.BoxNorm.weight_eq_sum, Work.Peluse.BoxNorm.weight_eq_sum, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

private lemma weight_cons_true {k : ℕ} (τ : Fin k → Bool) :
    Work.Peluse.weight (Fin.cons (α := fun _ : Fin (k+1) => Bool) true τ)
      = Work.Peluse.weight τ + 1 := by
  rw [weight_cons]; simp

private lemma weight_cons_false {k : ℕ} (τ : Fin k → Bool) :
    Work.Peluse.weight (Fin.cons (α := fun _ : Fin (k+1) => Bool) false τ)
      = Work.Peluse.weight τ := by
  rw [weight_cons]; simp

private lemma neg_one_pow_succ (n : ℕ) : (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) := by
  rw [pow_succ]; ring

/-- The sum over the `(t+1)`-fold cube splits as the sum over the head bit and the tail. -/
private lemma sum_pi_bool_succ {t : ℕ} (F : (Fin (t+1) → Bool) → ℝ) :
    (∑ p : Bool × (Fin t → Bool), F (Fin.cons p.1 p.2)) = ∑ ω : Fin (t+1) → Bool, F ω := by
  refine Finset.sum_bij (fun x _ => Fin.cons x.1 x.2) (fun x _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro x₁ _ x₂ _ h
    refine Prod.ext ?_ ?_
    · have h0 := congrFun h 0
      simpa [Fin.cons_zero] using h0
    · funext i
      have hi := congrFun h i.succ
      simpa [Fin.cons_succ] using hi
  · intro u _
    exact ⟨(u 0, fun i => u i.succ), Finset.mem_univ _, Fin.cons_self_tail u⟩
  · intro x _
    rfl

/-- The argument of `φ` in the `β = true` half of the split. -/
private lemma if_cons_true {s : ℕ} (b c : Fin (s+1) → ℤ) (g : Fin s → Bool) (i : Fin (s+1)) :
    (if (Fin.cons (α := fun _ : Fin (s+1) => Bool) true g) i = true then c i else b i)
      = Fin.cons (α := fun _ : Fin (s+1) => ℤ) (c 0)
          (fun j : Fin s => if g j = true then c j.succ else b j.succ) i := by
  refine Fin.cases ?_ ?_ i <;> simp

/-- The argument of `φ` in the `β = false` half of the split. -/
private lemma if_cons_false {s : ℕ} (b c : Fin (s+1) → ℤ) (g : Fin s → Bool) (i : Fin (s+1)) :
    (if (Fin.cons (α := fun _ : Fin (s+1) => Bool) false g) i = true then c i else b i)
      = Fin.cons (α := fun _ : Fin (s+1) => ℤ) (b 0)
          (fun j : Fin s => if g j = true then c j.succ else b j.succ) i := by
  refine Fin.cases ?_ ?_ i <;> simp

private lemma func_eq_true {s : ℕ} (b c : Fin (s+1) → ℤ) (g : Fin s → Bool) :
    (fun i : Fin (s+1) =>
        if (Fin.cons (α := fun _ : Fin (s+1) => Bool) true g) i = true then c i else b i)
      = Fin.cons (α := fun _ : Fin (s+1) => ℤ) (c 0)
          (fun j : Fin s => if g j = true then c j.succ else b j.succ) :=
  funext (if_cons_true b c g)

private lemma func_eq_false {s : ℕ} (b c : Fin (s+1) → ℤ) (g : Fin s → Bool) :
    (fun i : Fin (s+1) =>
        if (Fin.cons (α := fun _ : Fin (s+1) => Bool) false g) i = true then c i else b i)
      = Fin.cons (α := fun _ : Fin (s+1) => ℤ) (b 0)
          (fun j : Fin s => if g j = true then c j.succ else b j.succ) :=
  funext (if_cons_false b c g)

/-- The `β = true` summand. -/
private lemma term_true {s : ℕ} (φ : (Fin (s+1) → ℤ) → (Fin (s+1) → ℤ) → ℝ)
    (a b c : Fin (s+1) → ℤ) (g : Fin s → Bool) :
    (-1 : ℝ) ^ (Work.Peluse.weight (Fin.cons (α := fun _ : Fin (s+1) => Bool) true g)) *
        φ a (fun i =>
          if (Fin.cons (α := fun _ : Fin (s+1) => Bool) true g) i = true then c i else b i)
      = - ((-1 : ℝ) ^ (Work.Peluse.weight g) *
          φ a (Fin.cons (α := fun _ : Fin (s+1) => ℤ) (c 0)
            (fun j => if g j = true then c j.succ else b j.succ))) := by
  rw [weight_cons_true, func_eq_true, neg_one_pow_succ]
  ring

/-- The `β = false` summand. -/
private lemma term_false {s : ℕ} (φ : (Fin (s+1) → ℤ) → (Fin (s+1) → ℤ) → ℝ)
    (a b c : Fin (s+1) → ℤ) (g : Fin s → Bool) :
    (-1 : ℝ) ^ (Work.Peluse.weight (Fin.cons (α := fun _ : Fin (s+1) => Bool) false g)) *
        φ a (fun i =>
          if (Fin.cons (α := fun _ : Fin (s+1) => Bool) false g) i = true then c i else b i)
      = (-1 : ℝ) ^ (Work.Peluse.weight g) *
          φ a (Fin.cons (α := fun _ : Fin (s+1) => ℤ) (b 0)
            (fun j => if g j = true then c j.succ else b j.succ)) := by
  rw [weight_cons_false, func_eq_false]

theorem lemma74_phase_split {s : ℕ} (φ : (Fin (s+1) → ℤ) → (Fin (s+1) → ℤ) → ℝ) (a b c : Fin (s+1) → ℤ) :
    (∑ ω : Fin (s+1) → Bool, (-1 : ℝ) ^ (Work.Peluse.weight ω) *
        φ a (fun i => if ω i = true then c i else b i))
      = (∑ ω : Fin s → Bool, (-1 : ℝ) ^ (Work.Peluse.weight ω) *
            φ a (Fin.cons (b 0) (fun i => if ω i = true then c i.succ else b i.succ)))
        - (∑ ω : Fin s → Bool, (-1 : ℝ) ^ (Work.Peluse.weight ω) *
            φ a (Fin.cons (c 0) (fun i => if ω i = true then c i.succ else b i.succ))) := by
  have hTrue :
      (∑ g : Fin s → Bool,
          (-1 : ℝ) ^ (Work.Peluse.weight (Fin.cons (α := fun _ : Fin (s+1) => Bool) true g)) *
            φ a (fun i =>
              if (Fin.cons (α := fun _ : Fin (s+1) => Bool) true g) i = true then c i else b i))
        = - (∑ g : Fin s → Bool, (-1 : ℝ) ^ (Work.Peluse.weight g) *
              φ a (Fin.cons (α := fun _ : Fin (s+1) => ℤ) (c 0)
                (fun j => if g j = true then c j.succ else b j.succ))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun g _ => term_true φ a b c g)
  have hFalse :
      (∑ g : Fin s → Bool,
          (-1 : ℝ) ^ (Work.Peluse.weight (Fin.cons (α := fun _ : Fin (s+1) => Bool) false g)) *
            φ a (fun i =>
              if (Fin.cons (α := fun _ : Fin (s+1) => Bool) false g) i = true then c i else b i))
        = (∑ g : Fin s → Bool, (-1 : ℝ) ^ (Work.Peluse.weight g) *
              φ a (Fin.cons (α := fun _ : Fin (s+1) => ℤ) (b 0)
                (fun j => if g j = true then c j.succ else b j.succ))) :=
    Finset.sum_congr rfl (fun g _ => term_false φ a b c g)
  calc (∑ ω : Fin (s+1) → Bool, (-1 : ℝ) ^ (Work.Peluse.weight ω) *
        φ a (fun i => if ω i = true then c i else b i))
      = ∑ p : Bool × (Fin s → Bool), ((-1 : ℝ) ^ (Work.Peluse.weight (Fin.cons p.1 p.2)) *
          φ a (fun i => if (Fin.cons p.1 p.2 : Fin (s+1) → Bool) i = true then c i else b i)) :=
        (sum_pi_bool_succ (fun ω : Fin (s+1) → Bool =>
          (-1 : ℝ) ^ (Work.Peluse.weight ω) *
            φ a (fun i => if ω i = true then c i else b i))).symm
    _ = ∑ β : Bool, ∑ g : Fin s → Bool,
          ((-1 : ℝ) ^ (Work.Peluse.weight (Fin.cons β g)) *
            φ a (fun i => if (Fin.cons β g : Fin (s+1) → Bool) i = true then c i else b i)) :=
        Fintype.sum_prod_type (f := fun p : Bool × (Fin s → Bool) =>
          (-1 : ℝ) ^ (Work.Peluse.weight (Fin.cons p.1 p.2)) *
            φ a (fun i => if (Fin.cons p.1 p.2 : Fin (s+1) → Bool) i = true then c i else b i))
    _ = (∑ g : Fin s → Bool,
          (-1 : ℝ) ^ (Work.Peluse.weight (Fin.cons (α := fun _ : Fin (s+1) => Bool) true g)) *
            φ a (fun i =>
              if (Fin.cons (α := fun _ : Fin (s+1) => Bool) true g) i = true then c i else b i))
        + (∑ g : Fin s → Bool,
          (-1 : ℝ) ^ (Work.Peluse.weight (Fin.cons (α := fun _ : Fin (s+1) => Bool) false g)) *
            φ a (fun i =>
              if (Fin.cons (α := fun _ : Fin (s+1) => Bool) false g) i = true then c i else b i)) :=
        Fintype.sum_bool (fun β : Bool => ∑ g : Fin s → Bool,
          ((-1 : ℝ) ^ (Work.Peluse.weight (Fin.cons β g)) *
            φ a (fun i => if (Fin.cons β g : Fin (s+1) → Bool) i = true then c i else b i)))
    _ = (∑ ω : Fin s → Bool, (-1 : ℝ) ^ (Work.Peluse.weight ω) *
            φ a (Fin.cons (b 0) (fun i => if ω i = true then c i.succ else b i.succ)))
        - (∑ ω : Fin s → Bool, (-1 : ℝ) ^ (Work.Peluse.weight ω) *
            φ a (Fin.cons (c 0) (fun i => if ω i = true then c i.succ else b i.succ))) := by
        rw [hTrue, hFalse]
        ring

end

end Work.Peluse.Ulower
