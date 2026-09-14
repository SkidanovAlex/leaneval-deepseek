import Mathlib

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Reduction maps between `ℤ`, `ℤ_[p]` and `ZMod p` (discindex bridge, 1b)

The discindex bridge compares facts over the *residue field* `F_p = ZMod p`
(where `polyIndex`, the per-prime sieve, and the irreducible factor data
live) with facts over the *p-adic integers* `ℤ_[p] = PadicInt p` (where
Hensel-type lifting and the local factors of a polynomial `f` live).  The
connecting map is

    toZMod : ℤ_[p] →+* ZMod p          (`PadicInt.toZMod`)

whose kernel is the maximal ideal `(p)` (`PadicInt.ker_toZMod`).  This
module records the elementary plumbing around that map:

* `toZMod_zmodCast`: `toZMod (ZMod.cast z) = z` for every `z : ZMod p` —
  the canonical representatives `0,…,p−1` are a section of the reduction;
* `toZMod_intCast`, `map_intCast_toZMod`: the reduction of the canonical
  map `ℤ → ℤ_[p]` composed with `toZMod` is the reduction `ℤ → ZMod p`, so
  reducing an *integer* polynomial through `ℤ_[p]` and then modulo `p`
  agrees with reducing it directly;
* `natDegree` preservation of the reduction map for monic polynomials
  (`Polynomial.Monic.natDegree_map`).

The main lifting content (Hensel: a coprime monic factorization over
`ZMod p` lifts to a factorization over `ℤ_[p]` with the same degrees and
exact reductions) is the shared-commons lemma
`Commons.NumberTheory.Padics.hensel_lift_coprime_factorization`
(proof delegated to the commons fleet); the corollary machinery that
applies it to the discriminant/index setting is built on top of this
module and that commons lemma.
-/

namespace Submission.Vdw

noncomputable section

/-- The canonical lift of residue classes: `ZMod.cast` sends `z` to its
representative `0 ≤ z < p` inside `ℤ_[p]`; `toZMod` takes it back. -/
theorem toZMod_zmodCast {p : ℕ} [Fact p.Prime] (z : ZMod p) :
    PadicInt.toZMod (ZMod.cast z : PadicInt p) = z := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out : Nat.Prime p)⟩
  apply ZMod.val_injective
  rw [PadicInt.val_toZMod_eq_zmodRepr]
  have hrep : z.val < p := ZMod.val_lt z
  have hcast : (ZMod.cast z : PadicInt p) = (z.val : ℤ_[p]) := by
    exact ZMod.cast_eq_val (n := p) (R := PadicInt p) z
  rw [hcast]
  exact PadicInt.zmodRepr_natCast_of_lt hrep

/-- Reducing the canonical image of an integer through `ℤ_[p]` gives the
direct reduction: for `x : ℤ`, `toZMod (x : ℤ_[p]) = (x : ZMod p)`. -/
theorem toZMod_intCast {p : ℕ} [Fact p.Prime] (x : ℤ) :
    PadicInt.toZMod (x : PadicInt p) = (x : ZMod p) := by
  have hhom :
      (PadicInt.toZMod.comp (Int.castRingHom (PadicInt p))) = Int.castRingHom (ZMod p) := by
    apply RingHom.ext_int
  exact congrArg (fun φ : ℤ →+* ZMod p => φ x) hhom

/-- For an integer polynomial `f`, reducing `f` to `ZMod p` directly or via
`ℤ_[p]` gives the same polynomial. -/
theorem map_intCast_toZMod {p : ℕ} [Fact p.Prime] (f : ℤ[X]) :
    (f.map (Int.castRingHom (PadicInt p))).map (PadicInt.toZMod : PadicInt p →+* ZMod p) =
      f.map (Int.castRingHom (ZMod p)) := by
  rw [Polynomial.map_map]
  congr 1
  apply RingHom.ext_int

/-- For a monic polynomial over `ℤ_[p]`, reduction to `ZMod p` preserves the
degree. -/
theorem natDegree_map_toZMod_of_monic {p : ℕ} [Fact p.Prime] (f : (PadicInt p)[X])
    (hf : f.Monic) : (f.map (PadicInt.toZMod : PadicInt p →+* ZMod p)).natDegree = f.natDegree :=
  Polynomial.Monic.natDegree_map hf (PadicInt.toZMod : PadicInt p →+* ZMod p)

/-- For a monic polynomial over `ℤ`, reduction to `ZMod p` preserves the
degree. -/
theorem natDegree_map_intCast_of_monic {p : ℕ} [Fact p.Prime] (f : ℤ[X]) (hf : f.Monic) :
    (f.map (Int.castRingHom (ZMod p))).natDegree = f.natDegree :=
  Polynomial.Monic.natDegree_map hf (Int.castRingHom (ZMod p))

end
end Submission.Vdw
