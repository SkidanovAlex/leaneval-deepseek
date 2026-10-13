/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The perfection of a ring along Frobenius, for rings with `p = 0`

`Work.DSEQP.Perf R p hp` is the filtered colimit of the system
`R --F--> R --F--> ⋯` along the Frobenius `F x = x ^ p`, defined for *every* commutative
ring `R` with `(p : R) = 0`.  This generality is needed by `Work.DSEQP.eqp_perfModel`: the
Čech complex of a finite affine cover has terms `∏ Γ(X, Uᵢ)` (and, for repeated indices,
`Γ(X, ∅) = 0`), so the perfection must be available for the zero ring as well; the existing
`Work.DSEQP.pPerfection` is only defined under `CharP R p`, which fails for the zero ring.

The element `of i x` is the `p ^ i`-th root of (the image of) `x`; the transition maps of the
system are the power maps `x ↦ x ^ (p ^ (j - i))`, which are additive precisely because
`p = 0` in `R` (Freshman's dream).
-/
import Mathlib
import Submission.Work.DSEQP.Basic

namespace Work.DSEQP

universe u

section Frob

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]

/-- Freshman's dream for `p ^ n`: `(x + y) ^ (p ^ n) = x ^ (p ^ n) + y ^ (p ^ n)`
whenever `p = 0` in the ring. -/
theorem add_pow_prime_pow_eq_of_cast_eq_zero (hp : (p : R) = 0) (x y : R) (n : ℕ) :
    (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, ih, add_pow_prime_eq (Fact.out : p.Prime), hp]
    simp [pow_succ, pow_mul]

/-- `(-x) ^ (p ^ n) = -(x ^ (p ^ n))` for rings with `p = 0`. -/
theorem neg_pow_prime_pow (hp : (p : R) = 0) (x : R) (n : ℕ) :
    (-x) ^ p ^ n = -(x ^ p ^ n) := by
  rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
  · subst h
    have h2 : (2 : R) = 0 := by simpa using hp
    have hneg : ∀ y : R, -y = y := fun y => by
      rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]
    have hx : (-x) = x := hneg x
    rw [hx]
    exact (hneg (x ^ 2 ^ n)).symm
  · exact (Nat.odd_iff.mpr h).pow.neg_pow x

/-- The `p ^ n`-th power map, as a ring homomorphism when `p = 0` in the ring. -/
noncomputable def powHom (hp : (p : R) = 0) (n : ℕ) : R →+* R where
  toFun x := x ^ p ^ n
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _
  map_zero' := zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)
  map_add' x y := add_pow_prime_pow_eq_of_cast_eq_zero hp x y n

@[simp] theorem powHom_apply (hp : (p : R) = 0) (n : ℕ) (x : R) :
    powHom hp n x = x ^ p ^ n := rfl

theorem powHom_zero (hp : (p : R) = 0) : powHom hp 0 = RingHom.id R := by
  ext x; simp [powHom_apply]

theorem powHom_comp_add (hp : (p : R) = 0) (a b : ℕ) :
    powHom hp (a + b) = (powHom hp b).comp (powHom hp a) := by
  ext x
  simp only [RingHom.comp_apply, powHom_apply, ← pow_mul, ← pow_add]

/-- The transition map `R → R`, `x ↦ x ^ (p ^ (j - i))`, of the directed system defining the
perfection (as a ring homomorphism). -/
noncomputable def perfTrans (hp : (p : R) = 0) (i j : ℕ) (h : i ≤ j) : R →+* R :=
  powHom hp (j - i)

theorem perfTrans_apply (hp : (p : R) = 0) (i j : ℕ) (h : i ≤ j) (x : R) :
    perfTrans hp i j h x = x ^ p ^ (j - i) := rfl

instance instDirectedSystem (hp : (p : R) = 0) :
    DirectedSystem (fun _ : ℕ => R) (fun i j h => perfTrans hp i j h) where
  map_self := fun x => by simp [perfTrans, powHom_apply]
  map_map := by
    intro k j i hij hjk x
    simp only [perfTrans_apply]
    rw [← pow_mul, ← pow_add, show j - i + (k - j) = k - i by omega]

end Frob

/-! ## The perfection -/

section Perf

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) = 0)

/-- The perfection `R ^ (1/p^∞)` of a commutative ring `R` with `(p : R) = 0`: the filtered
colimit of the system `R --F--> R --F--> ⋯` (an element of the `i`-th copy is regarded as a
`p ^ i`-th root). -/
noncomputable abbrev Perf : Type u :=
  Ring.DirectLimit (fun _ : ℕ => R) fun i j h => ⇑(perfTrans hp i j h)

namespace Perf

/-- The canonical map from the `i`-th copy of `R` into its perfection. -/
noncomputable def of (i : ℕ) : R →+* Perf R p hp :=
  Ring.DirectLimit.of (fun _ : ℕ => R) (fun i j h => ⇑(perfTrans hp i j h)) i

theorem of_f {i j : ℕ} (hij : i ≤ j) (x : R) :
    (of R p hp) j (x ^ p ^ (j - i)) = (of R p hp) i x :=
  Ring.DirectLimit.of_f (G := fun _ : ℕ => R)
    (f := fun i j h => ⇑(perfTrans hp i j h)) hij x

/-- `of (i+1) x` is a `p`-th root of `of i x`. -/
theorem of_succ_pow (i : ℕ) (x : R) : ((of R p hp) (i + 1) x) ^ p = (of R p hp) i x := by
  have h := of_f (R := R) (p := p) (hp := hp) (i := i) (j := i + 1)
    (Nat.le_succ i) x
  rw [show (i + 1 - i) = 1 by omega] at h
  simpa using h

/-- Every element of the perfection has a representative. -/
theorem exists_of (z : Perf R p hp) : ∃ (i : ℕ) (x : R), (of R p hp) i x = z :=
  Ring.DirectLimit.exists_of z

/-- Induction principle on the perfection. -/
@[elab_as_elim]
theorem induction_on {C : Perf R p hp → Prop} (z : Perf R p hp)
    (ih : ∀ (i : ℕ) (x : R), C ((of R p hp) i x)) : C z :=
  Ring.DirectLimit.induction_on z ih

/-- The defining recursion principle. -/
theorem hom_ext {P : Type*} [CommRing P] {g₁ g₂ : Perf R p hp →+* P}
    (h : ∀ i, g₁.comp (of R p hp i) = g₂.comp (of R p hp i)) : g₁ = g₂ :=
  Ring.DirectLimit.hom_ext (P := P) h

/-- A representative of `0` is `0` at a later stage. -/
theorem of_eq_zero_iff {i : ℕ} {x : R} :
    (of R p hp) i x = 0 ↔ ∃ j, ∃ (hij : i ≤ j), x ^ p ^ (j - i) = 0 := by
  haveI := instDirectedSystem (R := R) (p := p) hp
  constructor
  · intro h
    exact Ring.DirectLimit.of.zero_exact (f' := fun i j h => perfTrans hp i j h) h
  · rintro ⟨j, hij, h⟩
    rw [← of_f (R := R) (p := p) (hp := hp) hij x, h, map_zero]

/-- Multiplication of representatives in the perfection, expressed at a common level. -/
theorem of_mul {i j c : ℕ} (hij : i ≤ c) (hjc : j ≤ c) (x y : R) :
    ((of R p hp) i x) * ((of R p hp) j y) =
      (of R p hp) c (x ^ p ^ (c - i) * y ^ p ^ (c - j)) := by
  rw [← of_f (R := R) (p := p) (hp := hp) hij x,
    ← of_f (R := R) (p := p) (hp := hp) hjc y, map_mul]

/-- The power of a representative. -/
theorem of_pow {i c : ℕ} (hic : i ≤ c) (x : R) (m : ℕ) :
    (((of R p hp) i x) ^ m) = (of R p hp) c ((x ^ m) ^ p ^ (c - i)) := by
  rw [← of_f (R := R) (p := p) (hp := hp) hic x, ← map_pow]
  congr 1
  rw [← pow_mul, ← pow_mul, mul_comm]

/-- Equality of representatives in a reduced ring is tested at a later stage. -/
theorem of_eq_of_iff [IsReduced R] {i j : ℕ} (x y : R) :
    (of R p hp) i x = (of R p hp) j y ↔
      ∃ k : ℕ, ∃ (hik : i ≤ k) (hjk : j ≤ k), x ^ p ^ (k - i) = y ^ p ^ (k - j) := by
  haveI := instDirectedSystem (R := R) (p := p) hp
  constructor
  · intro h
    have hk : (of R p hp) (max i j) (x ^ p ^ (max i j - i)) =
        (of R p hp) (max i j) (y ^ p ^ (max i j - j)) := by
      rw [of_f (R := R) (p := p) (hp := hp) (i := i) (j := max i j) (le_max_left _ _) x,
        of_f (R := R) (p := p) (hp := hp) (i := j) (j := max i j) (le_max_right _ _) y]
      exact h
    have h0 : (of R p hp) (max i j) (x ^ p ^ (max i j - i) - y ^ p ^ (max i j - j)) = 0 := by
      rw [map_sub, hk, sub_self]
    obtain ⟨k', hkk', hk'⟩ := (of_eq_zero_iff (R := R) (p := p) (hp := hp)).mp h0
    refine ⟨k', le_trans (le_max_left _ _) hkk', le_trans (le_max_right _ _) hkk', ?_⟩
    have hmain : (x ^ p ^ (max i j - i)) ^ p ^ (k' - max i j)
        = (y ^ p ^ (max i j - j)) ^ p ^ (k' - max i j) := by
      have hAB : (x ^ p ^ (max i j - i) - y ^ p ^ (max i j - j)) ^ p ^ (k' - max i j)
          = (x ^ p ^ (max i j - i)) ^ p ^ (k' - max i j)
            - (y ^ p ^ (max i j - j)) ^ p ^ (k' - max i j) := by
        rw [sub_eq_add_neg, add_pow_prime_pow_eq_of_cast_eq_zero hp, neg_pow_prime_pow hp,
          ← sub_eq_add_neg]
      have h1 : (x ^ p ^ (max i j - i)) ^ p ^ (k' - max i j)
          - (y ^ p ^ (max i j - j)) ^ p ^ (k' - max i j) = 0 := by
        rw [← hAB]; exact hk'
      exact sub_eq_zero.mp h1
    have e1 : x ^ p ^ (k' - i) = (x ^ p ^ (max i j - i)) ^ p ^ (k' - max i j) := by
      rw [← pow_mul, ← pow_add,
        show k' - i = (max i j - i) + (k' - max i j) from by omega]
    have e2 : y ^ p ^ (k' - j) = (y ^ p ^ (max i j - j)) ^ p ^ (k' - max i j) := by
      rw [← pow_mul, ← pow_add,
        show k' - j = (max i j - j) + (k' - max i j) from by omega]
    rw [e1, e2]
    exact hmain
  · rintro ⟨k, hik, hjk, h⟩
    rw [← of_f (R := R) (p := p) (hp := hp) hik x,
      ← of_f (R := R) (p := p) (hp := hp) hjk y, h]

/-- In a reduced ring, a representative that vanishes is zero. -/
theorem of_eq_zero [IsReduced R] {i : ℕ} {x : R} (h : (of R p hp) i x = 0) : x = 0 := by
  obtain ⟨k, hik, hk⟩ := (of_eq_zero_iff (R := R) (p := p) (hp := hp)).mp h
  exact eq_zero_of_pow_eq_zero hk

end Perf

end Perf


/-! ## Functoriality of the perfection -/

section Map

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {p : ℕ} [Fact p.Prime]

theorem perfTrans_natural (hp : (p : R) = 0) (hpS : (p : S) = 0) (f : R →+* S)
    (i j : ℕ) (hij : i ≤ j) :
    f.comp (perfTrans hp i j hij) = (perfTrans hpS i j hij).comp f := by
  ext x
  simp only [RingHom.comp_apply, perfTrans_apply, map_pow]

/-- Functoriality of the perfection: a ring homomorphism induces a ring homomorphism of the
perfections. -/
noncomputable def Perf.map (hp : (p : R) = 0) (hpS : (p : S) = 0) (f : R →+* S) :
    Perf R p hp →+* Perf S p hpS :=
  Ring.DirectLimit.map (fun _ => f) (fun i j h => perfTrans_natural hp hpS f i j h)

theorem Perf.map_of (hp : (p : R) = 0) (hpS : (p : S) = 0) (f : R →+* S) (i : ℕ) (x : R) :
    Perf.map hp hpS f ((Perf.of R p hp) i x) = (Perf.of S p hpS) i (f x) :=
  Ring.DirectLimit.map_apply_of (fun _ => f) (fun i j h => perfTrans_natural hp hpS f i j h) x

theorem Perf.map_id (hp : (p : R) = 0) :
    Perf.map hp hp (RingHom.id R) = RingHom.id (Perf R p hp) := by
  refine Perf.hom_ext (R := R) (p := p) (hp := hp) (P := Perf R p hp) (fun i => ?_)
  ext x
  rw [RingHom.comp_apply, Perf.map_of, RingHom.comp_apply, RingHom.id_apply, RingHom.id_apply]

theorem Perf.map_comp (hp : (p : R) = 0) (hpS : (p : S) = 0) (hpT : (p : T) = 0)
    (f : R →+* S) (g : S →+* T) :
    (Perf.map hp hpT) (g.comp f) = (Perf.map hpS hpT g).comp (Perf.map hp hpS f) := by
  refine Perf.hom_ext (R := R) (p := p) (hp := hp) (P := Perf T p hpT) (fun i => ?_)
  ext x
  simp only [RingHom.comp_apply, Perf.map_of]

end Map

end Work.DSEQP
