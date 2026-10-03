import Mathlib
import Submission.Work.Peluse.SwapC.RestConsSplit
import Submission.Work.Peluse.SwapC.prodProdEraseEq
import Submission.Work.Peluse.SwapC.starRestEq
import Submission.Work.Peluse.SwapC.cUBZeroCases

namespace Work.Peluse.SwapC

open scoped BigOperators

noncomputable section

open Work.Peluse

/-!
# The concatenation identification

This file proves `Work.Peluse.SwapC.concat_ident`: the doubled `Rest`-product of a `2s`-slot cube
equals the box inner product over the `2s` slots, with the corner family `cUB`.

The proof is a product identity, pointwise in the free variable, followed by a shift of the
summation variable (`∑'` over `ℤ` is invariant under translation).  Concretely, for a fixed
four-tuple of indices the two `Rest` factors are split along their first slot
(`RestConsSplit` and its starred companion), while the double product over `(ε, ε')` is split at
`ε = 0`, `ε' = 0` (`prodProdEraseEq`) with the four possible values of `cUB` (`cUBZeroCases`);
both sides then reduce to the same product of six groups.
-/

private lemma star_iterate_add_two (n : ℕ) (z : ℂ) : (star^[n + 2]) z = (star^[n]) z := by
  rw [Function.iterate_add_apply]; simp

private lemma star_iterate_star_succ (n : ℕ) (z : ℂ) : (star^[n]) (star z) = (star^[n + 1]) z := by
  rw [Function.iterate_add_apply]; simp

private lemma star_iterate_one (n : ℕ) : (star^[n]) (1 : ℂ) = 1 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; simp

private lemma weight_zero' (s : ℕ) : weight (0 : Fin s → Bool) = 0 := by simp [weight]

private lemma cornerShift_zero' {s : ℕ} (u : Fin s → ℤ) :
    cornerShift u (fun _ => 0) (0 : Fin s → Bool) = 0 := by simp [cornerShift]

/-- `cornerShift` of a difference vector, with the second corner sent to `0`. -/
private lemma cornerShift_sub_add {s : ℕ} (g g' : Fin s → ℤ) (ω : Fin s → Bool) :
    cornerShift g g' ω
      = cornerShift (fun j => g j - g' j) (fun _ => 0) ω + ∑ j : Fin s, g' j := by
  rw [cornerShift, cornerShift, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : ω j = true
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; simp

/-- The starred companion of `RestConsSplit`. -/
private lemma star_Rest_cons_split (s : ℕ) (dH : ℤ) (u : Fin s → ℤ) (f : ℤ → ℂ) (y : ℤ) :
    star (Rest (Fin.cons dH u) f y)
      = (∏ τ : Fin s → Bool, (star^[weight τ]) (f (y + dH + cornerShift u (fun _ => 0) τ)))
        * (∏ τ ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
            (star^[weight τ + 1]) (f (y + cornerShift u (fun _ => 0) τ))) := by
  rw [starRestEq, RestConsSplit]
  have h1 : (∏ τ : Fin s → Bool, (star^[weight τ + 1])
        ((fun x => star (f x)) (y + dH + cornerShift u (fun _ => 0) τ)))
      = (∏ τ : Fin s → Bool, (star^[weight τ]) (f (y + dH + cornerShift u (fun _ => 0) τ))) := by
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp only [star_iterate_star_succ, star_iterate_add_two]
  have h2 : (∏ τ ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
        (star^[weight τ]) ((fun x => star (f x)) (y + cornerShift u (fun _ => 0) τ)))
      = (∏ τ ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
            (star^[weight τ + 1]) (f (y + cornerShift u (fun _ => 0) τ))) := by
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp only [star_iterate_star_succ]
  rw [h1, h2]

/-- The product of the two `Rest` factors, expanded along the first slot. -/
private lemma rest_mul_star_rest_eq (s : ℕ) (dH0 dH1 : ℤ) (u0 u1 : Fin s → ℤ)
    (f : ℤ → ℂ) (y : ℤ) :
    Rest (Fin.cons dH0 u0) f y * star (Rest (Fin.cons dH1 u1) f y)
      = (∏ τ : Fin s → Bool, (star^[weight τ + 1]) (f (y + dH0 + cornerShift u0 (fun _ => 0) τ)))
        * (∏ τ ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
            (star^[weight τ]) (f (y + cornerShift u0 (fun _ => 0) τ)))
        * (∏ τ : Fin s → Bool, (star^[weight τ]) (f (y + dH1 + cornerShift u1 (fun _ => 0) τ)))
        * (∏ τ ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
            (star^[weight τ + 1]) (f (y + cornerShift u1 (fun _ => 0) τ))) := by
  rw [RestConsSplit dH0 u0 f y, star_Rest_cons_split s dH1 u1 f y]
  ring

set_option maxHeartbeats 1000000 in
/-- The double product over the sign patterns, split at the corners `ε = 0`, `ε' = 0`. -/
private lemma cUB_prod_eq (s : ℕ) (dH0 dH1 : ℤ) (u0 u1 : Fin s → ℤ) (f : ℤ → ℂ) (W : ℤ) :
    (∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool,
        (star^[weight ε + weight ε'])
          (cUB s f dH0 dH1 ε ε'
            (W + cornerShift u0 (fun _ => 0) ε + cornerShift u1 (fun _ => 0) ε')))
      = star (f (W + dH0)) * f (W + dH1)
        * (∏ ε ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
            ((star^[weight ε]) (f (W + cornerShift u0 (fun _ => 0) ε))
              * (star^[weight ε + 1]) (f (W + dH0 + cornerShift u0 (fun _ => 0) ε))))
        * (∏ ε' ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
            ((star^[weight ε' + 1]) (f (W + cornerShift u1 (fun _ => 0) ε'))
              * (star^[weight ε']) (f (W + dH1 + cornerShift u1 (fun _ => 0) ε')))) := by
  obtain ⟨h00, h10, h01, h11⟩ := cUBZeroCases s f dH0 dH1
  have hsplit := prodProdEraseEq (M := ℂ) (a := (0 : Fin s → Bool))
      (F := fun ε ε' => (star^[weight ε + weight ε'])
        (cUB s f dH0 dH1 ε ε'
          (W + cornerShift u0 (fun _ => 0) ε + cornerShift u1 (fun _ => 0) ε')))
      (h := fun x y hx hy => by rw [h11 x y hx hy]; exact star_iterate_one _)
  refine hsplit.trans ?_
  have hF00 : (star^[weight (0 : Fin s → Bool) + weight (0 : Fin s → Bool)])
      (cUB s f dH0 dH1 0 0 (W + cornerShift u0 (fun _ => 0) 0 + cornerShift u1 (fun _ => 0) 0))
      = star (f (W + dH0)) * f (W + dH1) := by
    rw [weight_zero' s, cornerShift_zero' u0, cornerShift_zero' u1, Int.add_zero, Int.add_zero,
      Nat.add_zero, h00]
    rfl
  have hFε : (∏ ε ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
        (star^[weight ε + weight (0 : Fin s → Bool)])
          (cUB s f dH0 dH1 ε 0 (W + cornerShift u0 (fun _ => 0) ε + cornerShift u1 (fun _ => 0) 0)))
      = (∏ ε ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
          ((star^[weight ε]) (f (W + cornerShift u0 (fun _ => 0) ε))
            * (star^[weight ε + 1]) (f (W + dH0 + cornerShift u0 (fun _ => 0) ε)))) := by
    refine Finset.prod_congr rfl fun ε hε => ?_
    have hne : ε ≠ 0 := (Finset.mem_erase.mp hε).1
    rw [weight_zero' s, cornerShift_zero' u1, Int.add_zero, Nat.add_zero, h10 ε hne]
    beta_reduce
    rw [show W + cornerShift u0 (fun _ => 0) ε + dH0 = W + dH0 + cornerShift u0 (fun _ => 0) ε
      from by ring]
    rw [Work.Peluse.BoxNorm.star_iterate_mul, star_iterate_star_succ]
  have hFε' : (∏ ε' ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
        (star^[weight (0 : Fin s → Bool) + weight ε'])
          (cUB s f dH0 dH1 0 ε' (W + cornerShift u0 (fun _ => 0) 0 + cornerShift u1 (fun _ => 0) ε')))
      = (∏ ε' ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
          ((star^[weight ε' + 1]) (f (W + cornerShift u1 (fun _ => 0) ε'))
            * (star^[weight ε']) (f (W + dH1 + cornerShift u1 (fun _ => 0) ε')))) := by
    refine Finset.prod_congr rfl fun ε' hε' => ?_
    have hne : ε' ≠ 0 := (Finset.mem_erase.mp hε').1
    rw [weight_zero' s, cornerShift_zero' u0, Int.add_zero, Nat.zero_add, h01 ε' hne]
    beta_reduce
    rw [show W + cornerShift u1 (fun _ => 0) ε' + dH1 = W + dH1 + cornerShift u1 (fun _ => 0) ε'
      from by ring]
    rw [Work.Peluse.BoxNorm.star_iterate_mul, star_iterate_star_succ]
  rw [hF00, hFε, hFε']

set_option maxHeartbeats 1000000 in
/-- The expanded `cUB` product equals the expanded `Rest` product (as a function of the free
variable). -/
private lemma EE_eq_Q (s : ℕ) (dH0 dH1 : ℤ) (u0 u1 : Fin s → ℤ) (f : ℤ → ℂ) (y : ℤ) :
    star (f (y + dH0)) * f (y + dH1)
      * (∏ ε ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
          ((star^[weight ε]) (f (y + cornerShift u0 (fun _ => 0) ε))
            * (star^[weight ε + 1]) (f (y + dH0 + cornerShift u0 (fun _ => 0) ε))))
      * (∏ ε' ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
          ((star^[weight ε' + 1]) (f (y + cornerShift u1 (fun _ => 0) ε'))
            * (star^[weight ε']) (f (y + dH1 + cornerShift u1 (fun _ => 0) ε'))))
      = (∏ τ : Fin s → Bool, (star^[weight τ + 1]) (f (y + dH0 + cornerShift u0 (fun _ => 0) τ)))
        * (∏ τ ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
            (star^[weight τ]) (f (y + cornerShift u0 (fun _ => 0) τ)))
        * (∏ τ : Fin s → Bool, (star^[weight τ]) (f (y + dH1 + cornerShift u1 (fun _ => 0) τ)))
        * (∏ τ ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
            (star^[weight τ + 1]) (f (y + cornerShift u1 (fun _ => 0) τ))) := by
  have hP1 : (∏ τ : Fin s → Bool, (star^[weight τ + 1]) (f (y + dH0 + cornerShift u0 (fun _ => 0) τ)))
      = star (f (y + dH0)) * ∏ τ ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
          (star^[weight τ + 1]) (f (y + dH0 + cornerShift u0 (fun _ => 0) τ)) := by
    rw [← Finset.prod_erase_mul (Finset.univ)
      (fun τ => (star^[weight τ + 1]) (f (y + dH0 + cornerShift u0 (fun _ => 0) τ)))
      (Finset.mem_univ 0)]
    rw [weight_zero' s, cornerShift_zero' u0, Int.add_zero]
    exact mul_comm _ _
  have hP3 : (∏ τ : Fin s → Bool, (star^[weight τ]) (f (y + dH1 + cornerShift u1 (fun _ => 0) τ)))
      = f (y + dH1) * ∏ τ ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
          (star^[weight τ]) (f (y + dH1 + cornerShift u1 (fun _ => 0) τ)) := by
    rw [← Finset.prod_erase_mul (Finset.univ)
      (fun τ => (star^[weight τ]) (f (y + dH1 + cornerShift u1 (fun _ => 0) τ)))
      (Finset.mem_univ 0)]
    rw [weight_zero' s, cornerShift_zero' u1, Int.add_zero]
    exact mul_comm _ _
  have hM1 : (∏ ε ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
        ((star^[weight ε]) (f (y + cornerShift u0 (fun _ => 0) ε))
          * (star^[weight ε + 1]) (f (y + dH0 + cornerShift u0 (fun _ => 0) ε))))
      = (∏ ε ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
          (star^[weight ε]) (f (y + cornerShift u0 (fun _ => 0) ε)))
        * (∏ ε ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
          (star^[weight ε + 1]) (f (y + dH0 + cornerShift u0 (fun _ => 0) ε))) :=
    Finset.prod_mul_distrib
  have hM2 : (∏ ε' ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
        ((star^[weight ε' + 1]) (f (y + cornerShift u1 (fun _ => 0) ε'))
          * (star^[weight ε']) (f (y + dH1 + cornerShift u1 (fun _ => 0) ε'))))
      = (∏ ε' ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
          (star^[weight ε' + 1]) (f (y + cornerShift u1 (fun _ => 0) ε')))
        * (∏ ε' ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
          (star^[weight ε']) (f (y + dH1 + cornerShift u1 (fun _ => 0) ε'))) :=
    Finset.prod_mul_distrib
  rw [hP1, hP3, hM1, hM2]
  ring

set_option maxHeartbeats 2000000 in
/-- The pointwise (up to a shift of the free variable) form of the concatenation identification. -/
private lemma concat_ptwise (s : ℕ) (X : Type) [Fintype X] (βL βR : Fin s → X → ℤ)
    (f : ℤ → ℂ) (dH0 dH1 : ℤ) (k0 k0' k1 k1' : Fin s → X) :
    (∑' y : ℤ, Rest (Fin.cons dH0 (fun j => βL j (k0 j) - βL j (k0' j))) f y *
      star (Rest (Fin.cons dH1 (fun j => βR j (k1 j) - βR j (k1' j))) f y))
      = ∑' y : ℤ, ∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool,
            (star^[weight ε + weight ε'])
              (cUB s f dH0 dH1 ε ε'
                (y + cornerShift (fun j => βL j (k0 j)) (fun j => βL j (k0' j)) ε
                   + cornerShift (fun j => βR j (k1 j)) (fun j => βR j (k1' j)) ε')) := by
  classical
  set u0 : Fin s → ℤ := fun j => βL j (k0 j) - βL j (k0' j) with hu0
  set u1 : Fin s → ℤ := fun j => βR j (k1 j) - βR j (k1' j) with hu1
  set c : ℤ := (∑ j : Fin s, βL j (k0' j)) + (∑ j : Fin s, βR j (k1' j)) with hc
  set Edef : ℤ → ℂ := fun W =>
      star (f (W + dH0)) * f (W + dH1)
        * (∏ ε ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
            ((star^[weight ε]) (f (W + cornerShift u0 (fun _ => 0) ε))
              * (star^[weight ε + 1]) (f (W + dH0 + cornerShift u0 (fun _ => 0) ε))))
        * (∏ ε' ∈ (Finset.univ : Finset (Fin s → Bool)).erase 0,
            ((star^[weight ε' + 1]) (f (W + cornerShift u1 (fun _ => 0) ε'))
              * (star^[weight ε']) (f (W + dH1 + cornerShift u1 (fun _ => 0) ε')))) with hEdef
  have hcs0 : ∀ ω : Fin s → Bool,
      cornerShift (fun j => βL j (k0 j)) (fun j => βL j (k0' j)) ω
        = cornerShift u0 (fun _ => 0) ω + ∑ j : Fin s, βL j (k0' j) :=
    fun ω => cornerShift_sub_add _ _ ω
  have hcs1 : ∀ ω : Fin s → Bool,
      cornerShift (fun j => βR j (k1 j)) (fun j => βR j (k1' j)) ω
        = cornerShift u1 (fun _ => 0) ω + ∑ j : Fin s, βR j (k1' j) :=
    fun ω => cornerShift_sub_add _ _ ω
  have harg : ∀ (Y : ℤ) (ε ε' : Fin s → Bool),
      (star^[weight ε + weight ε'])
        (cUB s f dH0 dH1 ε ε'
          (Y + cornerShift (fun j => βL j (k0 j)) (fun j => βL j (k0' j)) ε
             + cornerShift (fun j => βR j (k1 j)) (fun j => βR j (k1' j)) ε'))
      = (star^[weight ε + weight ε'])
        (cUB s f dH0 dH1 ε ε'
          ((Y + c) + cornerShift u0 (fun _ => 0) ε + cornerShift u1 (fun _ => 0) ε')) := by
    intro Y ε ε'
    have hz : Y + cornerShift (fun j => βL j (k0 j)) (fun j => βL j (k0' j)) ε
        + cornerShift (fun j => βR j (k1 j)) (fun j => βR j (k1' j)) ε'
        = (Y + c) + cornerShift u0 (fun _ => 0) ε + cornerShift u1 (fun _ => 0) ε' := by
      rw [hcs0 ε, hcs1 ε', hc]
      ring
    exact congrArg (fun z => (star^[weight ε + weight ε']) (cUB s f dH0 dH1 ε ε' z)) hz
  have hargsum : (∑' Y : ℤ, ∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool,
        (star^[weight ε + weight ε'])
          (cUB s f dH0 dH1 ε ε'
            (Y + cornerShift (fun j => βL j (k0 j)) (fun j => βL j (k0' j)) ε
               + cornerShift (fun j => βR j (k1 j)) (fun j => βR j (k1' j)) ε')))
      = ∑' Y : ℤ, ∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool,
        (star^[weight ε + weight ε'])
          (cUB s f dH0 dH1 ε ε'
            ((Y + c) + cornerShift u0 (fun _ => 0) ε + cornerShift u1 (fun _ => 0) ε')) :=
    tsum_congr fun Y => Finset.prod_congr rfl fun ε _ =>
      Finset.prod_congr rfl fun ε' _ => harg Y ε ε'
  rw [hargsum]
  have keyA : (∑' y : ℤ, Rest (Fin.cons dH0 u0) f y * star (Rest (Fin.cons dH1 u1) f y))
      = ∑' y : ℤ, Edef y :=
    tsum_congr fun y =>
      (rest_mul_star_rest_eq s dH0 dH1 u0 u1 f y).trans (EE_eq_Q s dH0 dH1 u0 u1 f y).symm
  have keyB : (∑' Y : ℤ, ∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool,
        (star^[weight ε + weight ε'])
          (cUB s f dH0 dH1 ε ε'
            ((Y + c) + cornerShift u0 (fun _ => 0) ε + cornerShift u1 (fun _ => 0) ε')))
      = ∑' Y : ℤ, Edef (Y + c) :=
    tsum_congr fun Y => cUB_prod_eq s dH0 dH1 u0 u1 f (Y + c)
  have keyC : (∑' y : ℤ, Edef y) = ∑' Y : ℤ, Edef (Y + c) :=
    (Equiv.tsum_eq (Equiv.addRight c) Edef).symm
  exact keyA.trans (keyC.trans keyB.symm)

/-- **The concatenation identification.**  The doubled `Rest`-product equals the box inner product
over the `2s` slots of the two halves, with the corner family `cUB`. -/
theorem concat_ident (s : ℕ) (X : Type) [Fintype X] (βL βR : Fin s → X → ℤ)
    (f : ℤ → ℂ) (dH0 dH1 : ℤ) :
    (∑ k₀ : Fin s → X, ∑ k₀' : Fin s → X, ∑ k₁ : Fin s → X, ∑ k₁' : Fin s → X,
        ∑' y : ℤ, Rest (Fin.cons dH0 (fun j => βL j (k₀ j) - βL j (k₀' j))) f y *
          star (Rest (Fin.cons dH1 (fun j => βR j (k₁ j) - βR j (k₁' j))) f y))
      = ∑ k₀ : Fin s → X, ∑ k₀' : Fin s → X, ∑ k₁ : Fin s → X, ∑ k₁' : Fin s → X,
          ∑' y : ℤ, ∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool,
            (star^[weight ε + weight ε'])
              (cUB s f dH0 dH1 ε ε'
                (y + cornerShift (fun j => βL j (k₀ j)) (fun j => βL j (k₀' j)) ε
                   + cornerShift (fun j => βR j (k₁ j)) (fun j => βR j (k₁' j)) ε')) := by
  classical
  refine Finset.sum_congr rfl fun k₀ _ => ?_
  refine Finset.sum_congr rfl fun k₀' _ => ?_
  refine Finset.sum_congr rfl fun k₁ _ => ?_
  refine Finset.sum_congr rfl fun k₁' _ => ?_
  exact concat_ptwise s X βL βR f dH0 dH1 k₀ k₀' k₁ k₁'

end

end Work.Peluse.SwapC
