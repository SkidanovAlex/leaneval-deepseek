/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.KleinTwData
import Submission.Work.MotK.LinkTwData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Naturality of the T-twisted Klein link data

Every polynomial of the twisted Klein model (`kleinTwQ` = `kleinTwP0`, `kleinTwBilin`,
`kleinTwStereo`, `kleinTwS`, `kleinTwP`, `kleinTwR`) is a polynomial with *integer*
coefficients in `(a, b, h, y 0, …, y 4)`.  Hence it commutes with every ring homomorphism
`f : R →+* S`: this is `Work.MotK.KleinTwData.map_data`.

The proof is uniform: unfold the definition, push `f` through the ring operations with
`map_add`, `map_mul`, `map_pow`, `map_neg`, `map_sub` (and `map_ofNat` for the numeral
coefficients), then match the two sides syntactically.  The vector-valued maps
`kleinTwP`, `kleinTwR` are reduced to their five components by `fin_cases`.
-/

set_option linter.unusedSimpArgs false

namespace Work.MotK.KleinTwData

open Work.MotK

private theorem map_kleinTwP0 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (y : Fin 5 → R) :
    f (kleinTwP0 a b h y) = kleinTwP0 (f a) (f b) (f h) (fun i => f (y i)) := by
  simp only [kleinTwP0, map_add, map_mul, map_pow, map_neg, map_sub]
  try simp only [map_ofNat]

private theorem map_kleinTwP1 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (y : Fin 5 → R) :
    f (kleinTwP1 a b h y) = kleinTwP1 (f a) (f b) (f h) (fun i => f (y i)) := by
  simp only [kleinTwP1, map_add, map_mul, map_pow, map_neg, map_sub]
  try simp only [map_ofNat]

private theorem map_kleinTwP2 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (y : Fin 5 → R) :
    f (kleinTwP2 a b h y) = kleinTwP2 (f a) (f b) (f h) (fun i => f (y i)) := by
  simp only [kleinTwP2, map_add, map_mul, map_pow, map_neg, map_sub]
  try simp only [map_ofNat]

private theorem map_kleinTwP3 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (y : Fin 5 → R) :
    f (kleinTwP3 a b h y) = kleinTwP3 (f a) (f b) (f h) (fun i => f (y i)) := by
  simp only [kleinTwP3, map_add, map_mul, map_pow, map_neg, map_sub]
  try simp only [map_ofNat]

private theorem map_kleinTwP4 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (y : Fin 5 → R) :
    f (kleinTwP4 a b h y) = kleinTwP4 (f a) (f b) (f h) (fun i => f (y i)) := by
  simp only [kleinTwP4, map_add, map_mul, map_pow, map_neg, map_sub]
  try simp only [map_ofNat]

private theorem map_kleinTwS {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (y : Fin 5 → R) :
    f (kleinTwS a b h y) = kleinTwS (f a) (f b) (f h) (fun i => f (y i)) := by
  simp only [kleinTwS, map_add, map_mul, map_pow, map_neg, map_sub]
  try simp only [map_ofNat]

private theorem map_kleinTwR0 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (y : Fin 5 → R) :
    f (kleinTwR0 a b h y) = kleinTwR0 (f a) (f b) (f h) (fun i => f (y i)) := by
  simp only [kleinTwR0, map_add, map_mul, map_pow, map_neg, map_sub]
  try simp only [map_ofNat]

private theorem map_kleinTwR1 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (y : Fin 5 → R) :
    f (kleinTwR1 a b h y) = kleinTwR1 (f a) (f b) (f h) (fun i => f (y i)) := by
  simp only [kleinTwR1, map_add, map_mul, map_pow, map_neg, map_sub]
  try simp only [map_ofNat]

private theorem map_kleinTwR2 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (y : Fin 5 → R) :
    f (kleinTwR2 a b h y) = kleinTwR2 (f a) (f b) (f h) (fun i => f (y i)) := by
  simp only [kleinTwR2, map_add, map_mul, map_pow, map_neg, map_sub]
  try simp only [map_ofNat]

private theorem map_kleinTwR3 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (y : Fin 5 → R) :
    f (kleinTwR3 a b h y) = kleinTwR3 (f a) (f b) (f h) (fun i => f (y i)) := by
  simp only [kleinTwR3, map_add, map_mul, map_pow, map_neg, map_sub]
  try simp only [map_ofNat]

private theorem map_kleinTwR4 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (y : Fin 5 → R) :
    f (kleinTwR4 a b h y) = kleinTwR4 (f a) (f b) (f h) (fun i => f (y i)) := by
  simp only [kleinTwR4, map_add, map_mul, map_pow, map_neg, map_sub]
  try simp only [map_ofNat]

private theorem map_kleinTwP {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (y : Fin 5 → R) :
    ∀ k : Fin 5,
      f (kleinTwP a b h y k) = kleinTwP (f a) (f b) (f h) (fun i => f (y i)) k := by
  intro k
  fin_cases k <;>
    simp [kleinTwP, map_kleinTwP0, map_kleinTwP1, map_kleinTwP2, map_kleinTwP3, map_kleinTwP4]

private theorem map_kleinTwR {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (y : Fin 5 → R) :
    ∀ k : Fin 5,
      f (kleinTwR a b h y k) = kleinTwR (f a) (f b) (f h) (fun i => f (y i)) k := by
  intro k
  fin_cases k <;>
    simp [kleinTwR, map_kleinTwR0, map_kleinTwR1, map_kleinTwR2, map_kleinTwR3, map_kleinTwR4]

private theorem map_kleinTwQ {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (y : Fin 5 → R) :
    f (kleinTwQ a b h y) = kleinTwQ (f a) (f b) (f h) (fun i => f (y i)) := by
  simpa only [kleinTwQ] using map_kleinTwP0 f a b h y

private theorem map_kleinTwBilin {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (u v : Fin 5 → R) :
    f (kleinTwBilin a b h u v)
      = kleinTwBilin (f a) (f b) (f h) (fun i => f (u i)) (fun i => f (v i)) := by
  have h : (fun i => f ((u + v) i)) = (fun i => f (u i)) + (fun i => f (v i)) := by
    funext i
    simp [Pi.add_apply]
  simp only [kleinTwBilin, map_sub, map_kleinTwQ, h]

private theorem map_kleinTwStereo {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (p v : Fin 5 → R) (i : Fin 5) :
    f (kleinTwStereo a b h p v i)
      = kleinTwStereo (f a) (f b) (f h) (fun i => f (p i)) (fun i => f (v i)) i := by
  simp only [kleinTwStereo, map_sub, map_mul, map_kleinTwQ, map_kleinTwBilin]

theorem map_data {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b h : R) :
    (∀ y : Fin 5 → R, f (Work.MotK.kleinTwQ a b h y)
        = Work.MotK.kleinTwQ (f a) (f b) (f h) (fun i => f (y i))) ∧
    (∀ u v : Fin 5 → R, f (Work.MotK.kleinTwBilin a b h u v)
        = Work.MotK.kleinTwBilin (f a) (f b) (f h) (fun i => f (u i)) (fun i => f (v i))) ∧
    (∀ (p v : Fin 5 → R) (i : Fin 5), f (Work.MotK.kleinTwStereo a b h p v i)
        = Work.MotK.kleinTwStereo (f a) (f b) (f h) (fun i => f (p i)) (fun i => f (v i)) i) ∧
    (∀ y : Fin 5 → R, f (Work.MotK.kleinTwS a b h y)
        = Work.MotK.kleinTwS (f a) (f b) (f h) (fun i => f (y i))) ∧
    (∀ (y : Fin 5 → R) (k : Fin 5), f (Work.MotK.kleinTwP a b h y k)
        = Work.MotK.kleinTwP (f a) (f b) (f h) (fun i => f (y i)) k) ∧
    (∀ (y : Fin 5 → R) (k : Fin 5), f (Work.MotK.kleinTwR a b h y k)
        = Work.MotK.kleinTwR (f a) (f b) (f h) (fun i => f (y i)) k) :=
  ⟨fun y => map_kleinTwQ f a b h y,
   fun u v => map_kleinTwBilin f a b h u v,
   fun p v i => map_kleinTwStereo f a b h p v i,
   fun y => map_kleinTwS f a b h y,
   fun y k => map_kleinTwP f a b h y k,
   fun y k => map_kleinTwR f a b h y k⟩

end Work.MotK.KleinTwData
