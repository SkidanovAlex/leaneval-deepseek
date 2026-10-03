/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Functoriality of the skew Laurent series ring `A((t;τ))` in the coefficient ring

For a ring homomorphism `g : A →+* B` which is equivariant for the `ℤ`-actions defining the
skew Laurent series rings (i.e. `g (k • x) = k • g x`), the coefficientwise map
`f ↦ (n ↦ g (f n))` is a ring homomorphism `A((t;τ)) →+* B((t;τ))`.  It commutes with the
coefficient embeddings `A → A((t;τ))`, and it is injective whenever `g` is.
-/
import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_of_bounds

namespace Work.Section6

open Work.ORHughesFree

/-- The coefficientwise map on skew Laurent series induced by a ring homomorphism `g`. -/
noncomputable def skewLaurentMapFun {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    {B : Type} [Ring B] [MulSemiringAction (Multiplicative ℤ) B]
    (g : A →+* B) (f : SkewLaurentSeries A) : SkewLaurentSeries B :=
  ⟨fun n => g (f.1 n), SkewLaurentSeries.lo f, fun n hn => by
    show g (f.1 n) = 0
    rw [SkewLaurentSeries.lt_lo hn, map_zero]⟩

theorem skewLaurentMapFun_apply {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    {B : Type} [Ring B] [MulSemiringAction (Multiplicative ℤ) B]
    (g : A →+* B) (f : SkewLaurentSeries A) (n : ℤ) :
    (skewLaurentMapFun g f).1 n = g (f.1 n) := rfl

/-- The two convolution sums computing `(g f₁) * (g f₂)` and `g (f₁ * f₂)` differ only in their
range of summation: the summand vanishes outside both ranges. -/
theorem skewLaurentMapFun_sum_eq {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    {B : Type} [Ring B] [MulSemiringAction (Multiplicative ℤ) B]
    (g : A →+* B)
    (f₁ f₂ : SkewLaurentSeries A) (n : ℤ) :
    (∑ k ∈ Finset.Icc (SkewLaurentSeries.lo f₁) (n - SkewLaurentSeries.lo f₂),
        g (f₁.1 k) * ((Multiplicative.ofAdd k) • g (f₂.1 (n - k))))
      = ∑ k ∈ Finset.Icc (SkewLaurentSeries.lo (skewLaurentMapFun g f₁))
          (n - SkewLaurentSeries.lo (skewLaurentMapFun g f₂)),
        g (f₁.1 k) * ((Multiplicative.ofAdd k) • g (f₂.1 (n - k))) := by
  have h1 := SkewLaurentSeries.sum_Icc_eq_of_eq_zero_outside
    (fun k : ℤ => g (f₁.1 k) * ((Multiplicative.ofAdd k) • g (f₂.1 (n - k))))
    (SkewLaurentSeries.lo f₁) (n - SkewLaurentSeries.lo f₂)
    (SkewLaurentSeries.lo (skewLaurentMapFun g f₁))
    (n - SkewLaurentSeries.lo (skewLaurentMapFun g f₂))
    (fun x hx => by
      have h : (skewLaurentMapFun g f₁).1 x = 0 := SkewLaurentSeries.lt_lo hx
      show g (f₁.1 x) * ((Multiplicative.ofAdd x) • g (f₂.1 (n - x))) = 0
      rw [show g (f₁.1 x) = 0 from h, zero_mul])
    (fun x hx => by
      have h : (skewLaurentMapFun g f₂).1 (n - x) = 0 :=
        SkewLaurentSeries.lt_lo (by omega : n - x < SkewLaurentSeries.lo (skewLaurentMapFun g f₂))
      show g (f₁.1 x) * ((Multiplicative.ofAdd x) • g (f₂.1 (n - x))) = 0
      rw [show g (f₂.1 (n - x)) = 0 from h, smul_zero, mul_zero])
  have h2 := SkewLaurentSeries.sum_Icc_eq_of_eq_zero_outside
    (fun k : ℤ => g (f₁.1 k) * ((Multiplicative.ofAdd k) • g (f₂.1 (n - k))))
    (SkewLaurentSeries.lo (skewLaurentMapFun g f₁))
    (n - SkewLaurentSeries.lo (skewLaurentMapFun g f₂))
    (SkewLaurentSeries.lo f₁) (n - SkewLaurentSeries.lo f₂)
    (fun x hx => by
      show g (f₁.1 x) * ((Multiplicative.ofAdd x) • g (f₂.1 (n - x))) = 0
      rw [SkewLaurentSeries.lt_lo hx, map_zero, zero_mul])
    (fun x hx => by
      show g (f₁.1 x) * ((Multiplicative.ofAdd x) • g (f₂.1 (n - x))) = 0
      rw [SkewLaurentSeries.lt_lo (by omega : n - x < SkewLaurentSeries.lo f₂), map_zero,
        smul_zero, mul_zero])
  rw [h1, h2, max_comm, min_comm]

/-- The coefficientwise map is multiplicative. -/
theorem skewLaurentMapFun_mul {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    {B : Type} [Ring B] [MulSemiringAction (Multiplicative ℤ) B]
    (g : A →+* B) (hg : ∀ (k : ℤ) (x : A),
      g ((Multiplicative.ofAdd k) • x) = (Multiplicative.ofAdd k) • g x)
    (f₁ f₂ : SkewLaurentSeries A) :
    skewLaurentMapFun g (f₁ * f₂) = skewLaurentMapFun g f₁ * skewLaurentMapFun g f₂ := by
  refine SkewLaurentSeries.ext fun n => ?_
  show g ((f₁ * f₂).1 n) = (skewLaurentMapFun g f₁ * skewLaurentMapFun g f₂).1 n
  calc g ((f₁ * f₂).1 n)
      = ∑ k ∈ Finset.Icc (SkewLaurentSeries.lo f₁) (n - SkewLaurentSeries.lo f₂),
          g (f₁.1 k * ((Multiplicative.ofAdd k) • f₂.1 (n - k))) := by
          rw [SkewLaurentSeries.mul_apply_of_bounds f₁ f₂ (SkewLaurentSeries.lo f₁)
            (SkewLaurentSeries.lo f₂) (fun m hm => SkewLaurentSeries.lt_lo hm)
            (fun m hm => SkewLaurentSeries.lt_lo hm) n, map_sum]
    _ = ∑ k ∈ Finset.Icc (SkewLaurentSeries.lo f₁) (n - SkewLaurentSeries.lo f₂),
          g (f₁.1 k) * ((Multiplicative.ofAdd k) • g (f₂.1 (n - k))) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [map_mul, hg]
    _ = ∑ k ∈ Finset.Icc (SkewLaurentSeries.lo (skewLaurentMapFun g f₁))
          (n - SkewLaurentSeries.lo (skewLaurentMapFun g f₂)),
          g (f₁.1 k) * ((Multiplicative.ofAdd k) • g (f₂.1 (n - k))) :=
          skewLaurentMapFun_sum_eq g f₁ f₂ n
    _ = (skewLaurentMapFun g f₁ * skewLaurentMapFun g f₂).1 n := by
          rw [SkewLaurentSeries.mul_apply_of_bounds (skewLaurentMapFun g f₁)
            (skewLaurentMapFun g f₂) (SkewLaurentSeries.lo (skewLaurentMapFun g f₁))
            (SkewLaurentSeries.lo (skewLaurentMapFun g f₂))
            (fun m hm => SkewLaurentSeries.lt_lo hm) (fun m hm => SkewLaurentSeries.lt_lo hm) n]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [skewLaurentMapFun_apply, skewLaurentMapFun_apply]

/-- The coefficientwise map as a ring homomorphism. -/
noncomputable def skewLaurentMapRingHom {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    {B : Type} [Ring B] [MulSemiringAction (Multiplicative ℤ) B]
    (g : A →+* B) (hg : ∀ (k : ℤ) (x : A),
      g ((Multiplicative.ofAdd k) • x) = (Multiplicative.ofAdd k) • g x) :
    SkewLaurentSeries A →+* SkewLaurentSeries B where
  toFun := skewLaurentMapFun g
  map_one' := by
    refine SkewLaurentSeries.ext fun n => ?_
    rw [skewLaurentMapFun_apply, SkewLaurentSeries.one_apply, SkewLaurentSeries.one_apply]
    by_cases h : n = 0
    · rw [if_pos h, if_pos h, map_one]
    · rw [if_neg h, if_neg h, map_zero]
  map_mul' := skewLaurentMapFun_mul g hg
  map_zero' := by
    refine SkewLaurentSeries.ext fun n => ?_
    rw [skewLaurentMapFun_apply, SkewLaurentSeries.zero_apply, map_zero,
      SkewLaurentSeries.zero_apply]
  map_add' := by
    intro x y
    refine SkewLaurentSeries.ext fun n => ?_
    show g ((x + y).1 n) = (skewLaurentMapFun g x).1 n + (skewLaurentMapFun g y).1 n
    rw [SkewLaurentSeries.add_apply, map_add, skewLaurentMapFun_apply, skewLaurentMapFun_apply]

theorem skewLaurentMapRingHom_apply {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    {B : Type} [Ring B] [MulSemiringAction (Multiplicative ℤ) B]
    (g : A →+* B) (hg : ∀ (k : ℤ) (x : A),
      g ((Multiplicative.ofAdd k) • x) = (Multiplicative.ofAdd k) • g x)
    (f : SkewLaurentSeries A) (n : ℤ) :
    (skewLaurentMapRingHom g hg f).1 n = g (f.1 n) := rfl

/-- The coefficientwise map commutes with the coefficient embeddings. -/
theorem skewLaurentMapFun_coeff {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    {B : Type} [Ring B] [MulSemiringAction (Multiplicative ℤ) B]
    (g : A →+* B) (a : A) :
    skewLaurentMapFun g (skewLaurentCoeff A a) = skewLaurentCoeff B (g a) := by
  refine SkewLaurentSeries.ext fun n => ?_
  rw [skewLaurentMapFun_apply]
  have h1 : (skewLaurentCoeff A a).1 n = (if n = 0 then a else 0) := by
    show (SkewLaurentSeries.coeff a).1 n = (if n = 0 then a else 0)
    rw [SkewLaurentSeries.coeff_apply]
  have h2 : (skewLaurentCoeff B (g a)).1 n = (if n = 0 then g a else 0) := by
    show (SkewLaurentSeries.coeff (g a)).1 n = (if n = 0 then g a else 0)
    rw [SkewLaurentSeries.coeff_apply]
  rw [h1, h2]
  by_cases h : n = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, map_zero]

theorem skewLaurentSeries_mapRingHom {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    {B : Type} [Ring B] [MulSemiringAction (Multiplicative ℤ) B]
    (g : A →+* B) (hg : ∀ (k : ℤ) (x : A),
      g ((Multiplicative.ofAdd k) • x) = (Multiplicative.ofAdd k) • g x) :
    ∃ G : Work.ORHughesFree.SkewLaurentSeries A →+* Work.ORHughesFree.SkewLaurentSeries B,
      (∀ (f : Work.ORHughesFree.SkewLaurentSeries A) (n : ℤ), (G f).1 n = g (f.1 n)) ∧
      (∀ a : A, G (Work.ORHughesFree.skewLaurentCoeff A a) =
        Work.ORHughesFree.skewLaurentCoeff B (g a)) ∧
      (Function.Injective g → Function.Injective G) := by
  refine ⟨skewLaurentMapRingHom g hg, ?_, ?_, ?_⟩
  · intro f n
    exact skewLaurentMapRingHom_apply g hg f n
  · intro a
    exact skewLaurentMapFun_coeff g a
  · intro hinj f₁ f₂ h
    refine SkewLaurentSeries.ext fun n => ?_
    have h2 : (skewLaurentMapRingHom g hg f₁).1 n = (skewLaurentMapRingHom g hg f₂).1 n := by
      rw [h]
    rw [skewLaurentMapRingHom_apply, skewLaurentMapRingHom_apply] at h2
    exact hinj h2

end Work.Section6
