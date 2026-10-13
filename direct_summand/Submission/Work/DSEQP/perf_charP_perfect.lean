/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The perfection of a char-`p` ring has characteristic `p` and is perfect

Let `R` be a commutative ring with `(p : R) = 0` and `CharP R p` (`p` prime), and let
`Work.DSEQP.Perf R p hp` be the perfection, i.e. the filtered colimit of the system
`R --F--> R --F--> ⋯` along the Frobenius (`PerfRing.lean`).  This file proves that

* `Perf R p hp` again has characteristic `p` (`perf_charP`), and
* `Perf R p hp` is perfect in the sense of Serre: `x ↦ x ^ p` is a bijection
  (`perf_perfectRing`);

together these are the requested statement `perf_charP_perfect`.

The two halves are independent.  For the second one we exhibit the two ring endomorphisms
`perfShift` (`of i x ↦ of (i+1) x`, the "take the `p`-th root" map) and `perfFrob`
(`of i x ↦ of i (x ^ p)`, the Frobenius), show that they are mutually inverse, and
conclude that the `p`-th power map is bijective.
-/
import Mathlib
import Submission.Work.DSEQP.PerfRing

namespace Work.DSEQP

universe u

/-- In a ring of characteristic `p` (prime), a natural number whose image is nilpotent is
already `0` modulo `p`.  Indeed `(n : R) = ((n % p) : R)`, so `(n : R) ^ k = 0` forces
`p ∣ (n % p) ^ k`, hence `p ∣ n % p` and (as `n % p < p`) `p ∣ n`. -/
private theorem dvd_of_natCast_pow_eq_zero {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (n k : ℕ) (h : (n : R) ^ k = 0) : p ∣ n := by
  have hr : (n : R) = ((n % p : ℕ) : R) := CharP.cast_eq_mod R p n
  rw [hr, ← Nat.cast_pow, CharP.cast_eq_zero_iff R p] at h
  exact Nat.dvd_of_mod_eq_zero
    (Nat.eq_zero_of_dvd_of_lt
      (Nat.Prime.dvd_of_dvd_pow (p := p) (m := n % p) (n := k) (Fact.out : p.Prime) h)
      (Nat.mod_lt n (Fact.out : p.Prime).pos))

/-- **The perfection has characteristic `p`.**  A natural number `n` vanishes in
`Perf R p hp` iff some `p ^ j`-th power of `(n : R)` vanishes there, which happens iff
`(n : R) = 0`, i.e. iff `p ∣ n`. -/
theorem perf_charP (R : Type u) [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) [CharP R p] : CharP (Perf R p hp) p := by
  refine CharP.mk fun n => ?_
  rw [show (n : Perf R p hp) = Perf.of R p hp 0 (n : R) from
    (map_natCast (Perf.of R p hp 0) n).symm]
  rw [Perf.of_eq_zero_iff]
  simp only [Nat.sub_zero]
  constructor
  · rintro ⟨j, -, h⟩
    exact dvd_of_natCast_pow_eq_zero n (p ^ j) h
  · intro h
    exact ⟨0, Nat.zero_le 0, by simpa using (CharP.cast_eq_zero_iff R p n).2 h⟩

/-! ## Perfection of the perfection -/

section Shift

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) = 0)

/-- The "take the `p`-th root" endomorphism of the perfection, `of i x ↦ of (i+1) x`. -/
private noncomputable def perfShift : Perf R p hp →+* Perf R p hp :=
  Ring.DirectLimit.lift (fun _ : ℕ => R) (fun i j h => ⇑(perfTrans hp i j h)) (Perf R p hp)
    (fun i => Perf.of R p hp (i + 1))
    (by
      intro i j hij x
      have key : x ^ p ^ (j + 1 - (i + 1)) = x ^ p ^ (j - i) := by
        rw [show j + 1 - (i + 1) = j - i by omega]
      rw [perfTrans_apply, ← key]
      exact Perf.of_f (R := R) (p := p) (hp := hp) (Nat.succ_le_succ hij) x)

private theorem perfShift_of (i : ℕ) (x : R) :
    perfShift R p hp (Perf.of R p hp i x) = Perf.of R p hp (i + 1) x := by
  simp only [perfShift, Perf.of]
  rw [Ring.DirectLimit.lift_of]

end Shift

section Frob

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) = 0) [CharP R p]

/-- The Frobenius endomorphism of the perfection, `of i x ↦ of i (x ^ p)`. -/
private noncomputable def perfFrob : Perf R p hp →+* Perf R p hp :=
  Ring.DirectLimit.lift (fun _ : ℕ => R) (fun i j h => ⇑(perfTrans hp i j h)) (Perf R p hp)
    (fun i => (Perf.of R p hp i).comp (frobenius R p))
    (by
      intro i j hij x
      simp only [RingHom.comp_apply, frobenius_def]
      rw [← map_pow (perfTrans hp i j hij) x p]
      exact Perf.of_f (R := R) (p := p) (hp := hp) hij (x ^ p))

private theorem perfFrob_of (i : ℕ) (x : R) :
    perfFrob R p hp (Perf.of R p hp i x) = Perf.of R p hp i (x ^ p) := by
  simp only [perfFrob, Perf.of]
  rw [Ring.DirectLimit.lift_of]
  simp [RingHom.comp_apply, frobenius_def]

private theorem perfFrob_comp_shift :
    (perfFrob R p hp).comp (perfShift R p hp) = RingHom.id (Perf R p hp) := by
  apply Perf.hom_ext R p hp
  intro i
  ext x
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [perfShift_of, perfFrob_of, map_pow (Perf.of R p hp (i + 1)) x p, Perf.of_succ_pow]

private theorem perfShift_comp_frob :
    (perfShift R p hp).comp (perfFrob R p hp) = RingHom.id (Perf R p hp) := by
  apply Perf.hom_ext R p hp
  intro i
  ext x
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [perfFrob_of, perfShift_of, map_pow (Perf.of R p hp (i + 1)) x p, Perf.of_succ_pow]

private theorem perfFrob_apply (z : Perf R p hp) : perfFrob R p hp z = z ^ p := by
  refine Perf.induction_on R p hp z (fun i x => ?_)
  rw [perfFrob_of, map_pow]

private theorem perf_bijective_pow : Function.Bijective (fun x : Perf R p hp => x ^ p) := by
  have hSF : ∀ z : Perf R p hp, perfShift R p hp (perfFrob R p hp z) = z :=
    fun z => congrArg (fun f : Perf R p hp →+* Perf R p hp => f z) (perfShift_comp_frob R p hp)
  have hFS : ∀ z : Perf R p hp, perfFrob R p hp (perfShift R p hp z) = z :=
    fun z => congrArg (fun f : Perf R p hp →+* Perf R p hp => f z) (perfFrob_comp_shift R p hp)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have h2 : perfFrob R p hp x = perfFrob R p hp y := by
      rw [perfFrob_apply, perfFrob_apply]
      simpa using hxy
    calc x = perfShift R p hp (perfFrob R p hp x) := (hSF x).symm
      _ = perfShift R p hp (perfFrob R p hp y) := by rw [h2]
      _ = y := hSF y
  · intro y
    refine ⟨perfShift R p hp y, ?_⟩
    show (perfShift R p hp y) ^ p = y
    rw [← perfFrob_apply]
    exact hFS y

end Frob

/-- **The perfection is perfect.**  The `p`-th power map on `Perf R p hp` is bijective, with
inverse the "root" map `of i x ↦ of (i+1) x`. -/
theorem perf_perfectRing (R : Type u) [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) [CharP R p] : PerfectRing (Perf R p hp) p :=
  PerfectRing.mk (perf_bijective_pow R p hp)

theorem perf_charP_perfect (R : Type u) [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) [CharP R p] :
    CharP (Work.DSEQP.Perf R p hp) p ∧ PerfectRing (Work.DSEQP.Perf R p hp) p :=
  ⟨perf_charP R p hp, perf_perfectRing R p hp⟩

end Work.DSEQP
