/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The skew Laurent series ring `A((t;τ))`

Carrier: the functions `ℤ → A` that vanish below some bound, with the skew convolution product
`(f * g) n = ∑_k f k * (k • g (n - k))` determined by `t a = τ(a) t`.  This is the ring
`A((t;τ))` of [JZLA20, §3.1].
-/
import Mathlib

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

/-- The carrier of the skew Laurent series ring `A((t;τ))`: functions `ℤ → A` vanishing below
some bound. -/
def SkewLaurentSeries (A : Type u) [Zero A] : Type u :=
  { f : ℤ → A // ∃ N : ℤ, ∀ n : ℤ, n < N → f n = 0 }

namespace SkewLaurentSeries

variable {A : Type u} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]

/-- A canonical lower bound for an element. -/
noncomputable def lo (f : SkewLaurentSeries A) : ℤ := Classical.choose f.2

omit [MulSemiringAction (Multiplicative ℤ) A] in
theorem lt_lo {f : SkewLaurentSeries A} {n : ℤ} (h : n < lo f) : f.1 n = 0 :=
  Classical.choose_spec f.2 n h

noncomputable instance : Zero (SkewLaurentSeries A) :=
  ⟨⟨fun _ => 0, ⟨0, fun _ _ => rfl⟩⟩⟩

noncomputable instance : Add (SkewLaurentSeries A) :=
  ⟨fun f g => ⟨fun n => f.1 n + g.1 n,
    ⟨min (lo f) (lo g), fun n hn => by
      rw [lt_min_iff] at hn
      show f.1 n + g.1 n = 0
      rw [lt_lo hn.1, lt_lo hn.2, add_zero]⟩⟩⟩

/-- The element `t` of `A((t;τ))`. -/
noncomputable def t : SkewLaurentSeries A :=
  ⟨fun n => if n = 1 then 1 else 0,
    ⟨0, fun n hn => by
      simp only [show n ≠ 1 by omega, if_false]⟩⟩

/-- The coefficient embedding `A → A((t;τ))`. -/
noncomputable def coeff (a : A) : SkewLaurentSeries A :=
  ⟨fun n => if n = 0 then a else 0,
    ⟨-1, fun n hn => by
      simp only [show n ≠ 0 by omega, if_false]⟩⟩

/-- The skew convolution product. -/
noncomputable def mul (f g : SkewLaurentSeries A) : SkewLaurentSeries A :=
  ⟨fun n => ∑ k ∈ Finset.Icc (lo f) (n - lo g),
      f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k)),
    ⟨lo f + lo g, fun n hn => by
      apply Finset.sum_eq_zero
      intro k hk
      have hk1 : lo f ≤ k := (Finset.mem_Icc.mp hk).1
      have hk2 : k ≤ n - lo g := (Finset.mem_Icc.mp hk).2
      rw [lt_lo (by omega : n - k < lo g), smul_zero, mul_zero]⟩⟩

noncomputable instance : One (SkewLaurentSeries A) :=
  ⟨⟨fun n => if n = 0 then 1 else 0,
    ⟨-1, fun n hn => by simp only [show n ≠ 0 by omega, if_false]⟩⟩⟩

noncomputable instance : Mul (SkewLaurentSeries A) := ⟨mul⟩

noncomputable instance : Neg (SkewLaurentSeries A) :=
  ⟨fun f => ⟨fun n => -f.1 n,
    ⟨lo f, fun n hn => by
      show -f.1 n = 0
      rw [lt_lo hn, neg_zero]⟩⟩⟩

@[simp] theorem neg_apply (f : SkewLaurentSeries A) (n : ℤ) : (-f).1 n = -f.1 n := rfl

@[simp] theorem zero_apply (n : ℤ) : (0 : SkewLaurentSeries A).1 n = 0 := rfl
@[simp] theorem add_apply (f g : SkewLaurentSeries A) (n : ℤ) :
    (f + g).1 n = f.1 n + g.1 n := rfl
@[simp] theorem mul_apply (f g : SkewLaurentSeries A) (n : ℤ) :
    (f * g).1 n = ∑ k ∈ Finset.Icc (lo f) (n - lo g),
      f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k)) := rfl
@[simp] theorem one_apply (n : ℤ) : (1 : SkewLaurentSeries A).1 n = if n = 0 then 1 else 0 := rfl
@[simp] theorem t_apply (n : ℤ) : (t : SkewLaurentSeries A).1 n = if n = 1 then 1 else 0 := rfl
@[simp] theorem coeff_apply (a : A) (n : ℤ) :
    (coeff a).1 n = if n = 0 then a else 0 := rfl

end SkewLaurentSeries

end Work.ORHughesFree
