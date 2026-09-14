import Mathlib
import Submission.Vdw.ResidueFiber
import Submission.Vdw.PolyIndex
import Submission.Commons.FieldTheory.Polynomial.card_monic_degree
import Submission.Commons.FieldTheory.Polynomial.monic_index_ge_card_le

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Index residue classes over a prime field (Case-I, per-prime atom)

Bhargava's Case-I sieve counts box polynomials `f` whose reduction mod `p`
has *index* at least `k_p` for each prime `p | C` (`D = ∏ p^{k_p}`, squarefull,
`C = rad D`).  The counting ingredients are

* (CI-1, shared commons) `monic_index_ge_card_le`:
  `#{monic deg-n over F_p : index ≥ k} = O(p^{n−k})` — a bound on a *set of
  monic polynomials*;
* (CI-2, `ResidueFiber.lean`) `box_residue_set_le`:
  `#{f ∈ Box n H : (coeffs mod m) ∈ S} ≤ |S| · ((2H+1)/m + 1)^n` — a bound
  phrased over *residue vectors*.

This module is the glue between the two: it carries the monic-polynomial index
to the coefficient-vector level (`indexClass` / `indexClassSet`: `v` is in the
class iff the monic degree-`n` polynomial `X^n + Σᵢ vᵢ Xⁱ` built from the
trailing coefficient vector `v` has `polyIndex ≥ k`), proves the class bound
`|indexClassSet n k| ≤ 2^((n+1)^4) · q^(n−k)` over a finite field `F` of size
`q`, and then — over `F = ZMod p`, `p` prime — identifies the reduction
`f mod p` of a box polynomial with that polynomial (via `boxResidue`), yielding
the per-prime box count

    #{f ∈ Box n H : index(f mod p) ≥ k} ≤ 2^((n+1)^4) · p^(n−k) · ((2H+1)/p + 1)^n

(`box_index_ge_ncard_le`).  The multi-prime (CRT, modulus `C = ∏ p`) version
is the next stone of the Case-I assembly.
-/

namespace Submission.Vdw

noncomputable section

open UniqueFactorizationMonoid
open Commons.FieldTheory.Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- The monic degree-`n` polynomial whose trailing (degree `< n`) coefficients
are the vector `v`, i.e. `X^n + ofFn n v` — exactly the inverse of
`monicDegreeEquiv`'s trailing-coefficient map. -/
def monicOfTrail (n : ℕ) (v : Fin n → F) : F[X] :=
  X ^ n + Polynomial.ofFn n v

/-- `monicOfTrail n v` is monic. -/
theorem monicOfTrail_monic (n : ℕ) (v : Fin n → F) : (monicOfTrail n v).Monic :=
  (Commons.FieldTheory.Polynomial.isMonicOfDegree_X_pow_add_ofFn n v).monic

/-- `monicOfTrail n v` has degree exactly `n`. -/
theorem monicOfTrail_natDegree (n : ℕ) (v : Fin n → F) : (monicOfTrail n v).natDegree = n :=
  (Commons.FieldTheory.Polynomial.isMonicOfDegree_X_pow_add_ofFn n v).natDegree_eq

/-- The trailing coefficients of `monicOfTrail n v` are `v`. -/
theorem monicOfTrail_coeff (n : ℕ) (v : Fin n → F) {i : ℕ} (hi : i < n) :
    (monicOfTrail n v).coeff i = v ⟨i, hi⟩ := by
  rw [monicOfTrail]
  simp [Polynomial.ofFn_coeff_eq_val_of_lt (v := v) hi, ne_of_lt hi]

/-- `toFn` recovers the vector from `monicOfTrail`. -/
theorem toFn_monicOfTrail (n : ℕ) (v : Fin n → F) :
    Polynomial.toFn n (monicOfTrail n v) = v := by
  ext i
  simp only [Polynomial.toFn, LinearMap.pi_apply, Polynomial.lcoeff_apply]
  exact monicOfTrail_coeff n v (i : Fin n).isLt

/-- A monic degree-`n` polynomial is `monicOfTrail` applied to its own trailing
coefficients. -/
theorem monicOfTrail_toFn (n : ℕ) (p : F[X]) (hpM : p.Monic) (hpdeg : p.natDegree = n) :
    monicOfTrail n (Polynomial.toFn n p) = p := by
  rw [monicOfTrail]
  rw [Commons.FieldTheory.Polynomial.ofFn_toFn_eq_sub_X_pow (p := p) hpM hpdeg]
  ring

/-- Bhargava's index of a polynomial equals `deg − deg rad` in terms of
`monicRadical` (the explicit product of the distinct monic irreducible
factors). -/
theorem polyIndex_eq_sub_monicRadical (f : F[X]) :
    polyIndex f = f.natDegree - (monicRadical f).natDegree := by
  rw [polyIndex, monicRadical_eq_radical]

/-- A vector `v : Fin n → F` is in the **index class** `(n,k)` if the monic
degree-`n` polynomial with trailing coefficients `v` has `polyIndex ≥ k`
(= "`f mod p` has index at least `k`" when `F = ZMod p`). -/
def indexClass (n k : ℕ) (v : Fin n → F) : Prop :=
  k ≤ polyIndex (monicOfTrail n v)

/-- Set form of `indexClass`. -/
def indexClassSet (n k : ℕ) : Set (Fin n → F) :=
  {v | indexClass n k v}

/-- The index-class vectors correspond exactly to the monic degree-`n`
polynomials of index at least `k`. -/
noncomputable def indexClassEquivPoly (n k : ℕ) :
    {v : Fin n → F // indexClass n k v} ≃
      {f : F[X] // f.Monic ∧ f.natDegree = n ∧ k ≤ polyIndex f} where
  toFun v :=
    ⟨monicOfTrail n v.1,
      ⟨monicOfTrail_monic n v.1, ⟨monicOfTrail_natDegree n v.1, v.2⟩⟩⟩
  invFun f :=
    ⟨Polynomial.toFn n f.1, by
      dsimp [indexClass]
      rw [monicOfTrail_toFn n f.1 f.2.1 f.2.2.1]
      exact f.2.2.2⟩
  left_inv := by
    intro v
    apply Subtype.ext
    exact toFn_monicOfTrail n v.1
  right_inv := by
    intro f
    apply Subtype.ext
    exact monicOfTrail_toFn n f.1 f.2.1 f.2.2.1

/-- `polyIndex`-version of the counted set agrees with the radical-degree
expression used in the shared-commons density theorem
(`monic_index_ge_card_le`). -/
noncomputable def indexEquivRadical (n k : ℕ) :
    {f : F[X] // f.Monic ∧ f.natDegree = n ∧ k ≤ polyIndex f} ≃
      {f : F[X] // f.Monic ∧ f.natDegree = n ∧
        k ≤ f.natDegree - (monicRadical f).natDegree} := by
  refine Equiv.subtypeEquivRight ?_
  intro f
  constructor
  · intro h
    rwa [polyIndex_eq_sub_monicRadical f] at h
  · intro h
    rwa [← polyIndex_eq_sub_monicRadical f] at h

/-- **(CI-1 at the vector level)** the number of index-class vectors is at most
`2^((n+1)^4) · q^(n−k)`, `q = Fintype.card F`. -/
theorem indexClass_card_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n k : ℕ) (hk : k ≤ n) :
    Nat.card {v : Fin n → F // indexClass (F := F) n k v} ≤
      2 ^ ((n + 1) ^ 4) * Fintype.card F ^ (n - k) := by
  calc
    Nat.card {v : Fin n → F // indexClass (F := F) n k v}
        = Nat.card {f : F[X] // f.Monic ∧ f.natDegree = n ∧ k ≤ polyIndex f} :=
            Nat.card_congr (indexClassEquivPoly (F := F) n k)
    _ = Nat.card {f : F[X] // f.Monic ∧ f.natDegree = n ∧
          k ≤ f.natDegree - (monicRadical (F := F) f).natDegree} :=
            Nat.card_congr (indexEquivRadical (F := F) n k)
    _ ≤ 2 ^ ((n + 1) ^ 4) * Fintype.card F ^ (n - k) := by
      simpa [monicRadical] using (monic_index_ge_card_le (F := F) n k hk)

/-- Set version of `indexClass_card_le` (the form needed by
`box_residue_set_le`). -/
theorem indexClassSet_ncard_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n k : ℕ) (hk : k ≤ n) :
    (indexClassSet (F := F) n k).ncard ≤ 2 ^ ((n + 1) ^ 4) * Fintype.card F ^ (n - k) := by
  classical
  rw [ncard_eq_natCard (indexClassSet (F := F) n k)]
  change Nat.card {v : Fin n → F // indexClass (F := F) n k v} ≤
    2 ^ ((n + 1) ^ 4) * Fintype.card F ^ (n - k)
  exact indexClass_card_le (F := F) n k hk

/-! ## The prime case: box polynomials mod `p`, `p` prime -/

section Prime

/-- The reduction `f mod p` of a box polynomial, as a monic degree-`n`
polynomial over the field `ZMod p`. -/
def reductionPoly (p : ℕ) [Fact (Nat.Prime p)] (n H : ℕ) (f : ↥(Box n H)) :
    (ZMod p)[X] :=
  (f : ℤ[X]).map (Int.castRingHom (ZMod p))

/-- The index (in the sense of `polyIndex`) of the reduction of `f` modulo
the prime `p`. -/
def boxIndex (p : ℕ) [Fact (Nat.Prime p)] (n H : ℕ) (f : ↥(Box n H)) : ℕ :=
  polyIndex (reductionPoly p n H f)

/-- The trailing-coefficient vector of `f mod p` is exactly `boxResidue`. -/
theorem toFn_reductionPoly (p : ℕ) [Fact (Nat.Prime p)] (n H : ℕ) (f : ↥(Box n H)) :
    Polynomial.toFn n (reductionPoly p n H f) = boxResidue n H p f := by
  ext i
  simp only [Polynomial.toFn, LinearMap.pi_apply, Polynomial.lcoeff_apply]
  rw [boxResidue, reductionPoly, Polynomial.coeff_map]
  rfl

/-- The reduction of a box polynomial is monic. -/
theorem reductionPoly_monic (p : ℕ) [Fact (Nat.Prime p)] (n H : ℕ) (f : ↥(Box n H)) :
    (reductionPoly p n H f).Monic := by
  exact (f.2.1).map (Int.castRingHom (ZMod p))

/-- The reduction of a box polynomial has degree `n`. -/
theorem reductionPoly_natDegree (p : ℕ) [Fact (Nat.Prime p)] (n H : ℕ)
    (f : ↥(Box n H)) :
    (reductionPoly p n H f).natDegree = n := by
  letI : Fact (1 < p) := ⟨Nat.Prime.one_lt (Fact.out : Nat.Prime p)⟩
  calc
    (reductionPoly p n H f).natDegree =
        ((f : ℤ[X]).map (Int.castRingHom (ZMod p))).natDegree := rfl
    _ = (f : ℤ[X]).natDegree := by
      exact (f.2.1).natDegree_map (Int.castRingHom (ZMod p))
    _ = n := by
      exact Polynomial.natDegree_eq_of_degree_eq_some (f.2.2.1)

/-- `f mod p` is the polynomial built from the trailing coefficient vector
`boxResidue n H p f` (monic degree `n`). -/
theorem reductionPoly_eq_monicOfTrail (p : ℕ) [Fact (Nat.Prime p)] (n H : ℕ)
    (f : ↥(Box n H)) :
    reductionPoly p n H f = monicOfTrail n (boxResidue n H p f) := by
  rw [← toFn_reductionPoly p n H f]
  exact (monicOfTrail_toFn (F := ZMod p) n (reductionPoly p n H f)
    (reductionPoly_monic p n H f) (reductionPoly_natDegree p n H f)).symm

/-- `boxIndex` (the index of the reduction) is exactly the index-class
membership of the residue vector. -/
theorem boxIndex_iff_indexClass (p : ℕ) [Fact (Nat.Prime p)] (n H k : ℕ)
    (f : ↥(Box n H)) :
    k ≤ boxIndex p n H f ↔ indexClass (F := ZMod p) n k (boxResidue n H p f) := by
  dsimp [boxIndex, indexClass]
  rw [reductionPoly_eq_monicOfTrail p n H f]

/-- **(per-prime box count, CI-1+CI-2)** the number of box polynomials whose
reduction mod `p` has index at least `k` is at most
`2^((n+1)^4) · p^(n−k) · ((2H+1)/p + 1)^n`. -/
theorem box_index_ge_ncard_le (p : ℕ) [Fact (Nat.Prime p)] (n H k : ℕ) (hk : k ≤ n) :
    Nat.card {f : ↥(Box n H) // k ≤ boxIndex p n H f} ≤
      2 ^ ((n + 1) ^ 4) * p ^ (n - k) * ((2 * H + 1) / p + 1) ^ n := by
  classical
  have hp2 : 2 ≤ p := Nat.Prime.two_le (Fact.out : Nat.Prime p)
  have hp1 : 1 ≤ p := le_trans (by norm_num : 1 ≤ 2) hp2
  have e : {f : ↥(Box n H) // k ≤ boxIndex p n H f} ≃
      {f : ↥(Box n H) // boxResidue n H p f ∈ indexClassSet (F := ZMod p) n k} :=
    { toFun := fun f => ⟨f.1, by
        simpa [indexClassSet] using (boxIndex_iff_indexClass p n H k f.1).mp f.2⟩,
      invFun := fun f => ⟨f.1, by
        simpa [indexClassSet] using (boxIndex_iff_indexClass p n H k f.1).mpr f.2⟩,
      left_inv := by
        intro f
        apply Subtype.ext
        rfl,
      right_inv := by
        intro f
        apply Subtype.ext
        rfl }
  have hle : Nat.card {f : ↥(Box n H) // k ≤ boxIndex p n H f} ≤
      (indexClassSet (F := ZMod p) n k).ncard * ((2 * H + 1) / p + 1) ^ n := by
    calc
      Nat.card {f : ↥(Box n H) // k ≤ boxIndex p n H f}
          = Nat.card {f : ↥(Box n H) // boxResidue n H p f ∈ indexClassSet (F := ZMod p) n k} :=
              Nat.card_congr e
      _ ≤ (indexClassSet (F := ZMod p) n k).ncard * ((2 * H + 1) / p + 1) ^ n :=
              box_residue_set_le n H p hp1 (indexClassSet (F := ZMod p) n k)
  calc
    Nat.card {f : ↥(Box n H) // k ≤ boxIndex p n H f}
        ≤ (indexClassSet (F := ZMod p) n k).ncard * ((2 * H + 1) / p + 1) ^ n := hle
    _ ≤ (2 ^ ((n + 1) ^ 4) * Fintype.card (ZMod p) ^ (n - k)) *
          ((2 * H + 1) / p + 1) ^ n := by
      exact Nat.mul_le_mul_right _ (indexClassSet_ncard_le (F := ZMod p) n k hk)
    _ = 2 ^ ((n + 1) ^ 4) * p ^ (n - k) * ((2 * H + 1) / p + 1) ^ n := by
      rw [ZMod.card p]

end Prime

end
end Submission.Vdw
