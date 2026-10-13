import Mathlib
import Submission.Work.DSM1p.Family
import Submission.Work.DSM1p.Family.flat_closure

/-!
# `dim R ≤ dim` of every stage of the root tower

Let `R` be a Noetherian local ring with `ringKrullDim R = d` and let `x : Fin d → R` be an
arbitrary family (no hypothesis on `x`!).  We prove that every stage of the multi-parameter root
tower

`A_n = R[Z₁,…,Z_d] ⧸ (Z_i ^ (p^n) - x_i)`

has Krull dimension at least `d`.

## The argument

The relations `Z_i ^ (p^n) - x_i` are monic in `Z_i`, so `A_n` is a *free* `R`-module with the
classes of the monomials of exponent `< p^n` in each variable as a basis (`mvPolyQuotFree`,
`Submission.Work.DSM1p.Family.flat_closure`).  In particular `A_n` is nontrivial and free, hence
*faithfully flat* over `R`.  Faithful flatness has two consequences used here:

* `Ideal.exists_isPrime_liesOver_of_faithfullyFlat`: every prime of `R` has a prime of `A_n`
  above it;
* `Algebra.HasGoingDown.of_flat`: flat algebras satisfy going-down.

Pick a strictly increasing chain `l` of `d + 1` primes of `R` (it exists because
`ringKrullDim R = d`, via `Order.le_krullDim_iff`), lift its last member to a prime `P` of `A_n`
by lying-over, and descend the chain to a chain `L` of `A_n` of the same length by going-down
(`Ideal.exists_ltSeries_of_hasGoingDown`).  Then `L.length = d ≤ krullDim (PrimeSpectrum A_n)`
by `Order.LTSeries.length_le_krullDim`, which is the claim.
-/

namespace Work.DSM1p.Family

universe u

open Order

/-- **The defining ideal of a stage is proper.**  If `1` lay in
`stageIdeal N x = (X_i ^ N - C (x_i))` then the normal form map `red` (which sends `1` to `1`
and kills `stageIdeal N x`) would give `1 = 0` in the nontrivial ring `R[X]`. -/
lemma stageIdeal_ne_top (R : Type u) [CommRing R] [Nontrivial R] (d N : ℕ) (hN : N ≠ 0)
    (x : Fin d → R) : stageIdeal N x ≠ ⊤ := by
  intro h
  have hmem : (1 : MvPolynomial (Fin d) R) ∈ stageIdeal N x := by
    rw [h]; exact Submodule.mem_top
  have h1 : red N x hN (1 : MvPolynomial (Fin d) R) = 0 :=
    red_mem_stageIdeal N x hN hmem
  rw [red_one N x hN] at h1
  exact one_ne_zero h1

/-- **Every stage of the tower is nontrivial.** -/
lemma nontrivial_famTower (R : Type u) [CommRing R] [Nontrivial R]
    (p : ℕ) {d : ℕ} (x : Fin d → R) (n : ℕ) (hp : p ≠ 0) :
    Nontrivial (Work.DSM1p.FamTower R p x n) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (stageIdeal_ne_top R d (p ^ n) (pow_ne_zero n hp) x)

/-- **Every stage of the tower is a faithfully flat `R`-algebra.**  It is a nontrivial free
`R`-module (`mvPolyQuotFree`), and a nontrivial free module is faithfully flat. -/
lemma faithfullyFlat_famTower (R : Type u) [CommRing R] [Nontrivial R]
    (p : ℕ) {d : ℕ} (x : Fin d → R) (n : ℕ) (hp : p ≠ 0) :
    Module.FaithfullyFlat R (Work.DSM1p.FamTower R p x n) := by
  haveI : Module.Free R (Work.DSM1p.FamTower R p x n) :=
    mvPolyQuotFree R d (p ^ n) (pow_ne_zero n hp) x
  haveI : Nontrivial (Work.DSM1p.FamTower R p x n) := nontrivial_famTower R p x n hp
  infer_instance

theorem le_ringKrullDim_stage (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (p : ℕ) [Fact p.Prime] {d : ℕ} (x : Fin d → R)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (n : ℕ) :
    (d : WithBot ℕ∞) ≤ ringKrullDim (Work.DSM1p.FamTower R p x n) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : Module.FaithfullyFlat R (Work.DSM1p.FamTower R p x n) :=
    faithfullyFlat_famTower R p x n hp
  -- a strictly increasing chain of `d + 1` primes of `R`
  obtain ⟨l, hl⟩ : ∃ l : LTSeries (PrimeSpectrum R), l.length = d :=
    Order.le_krullDim_iff.mp hd.ge
  -- a prime of the stage above the top of the chain
  obtain ⟨P, hPprime, hPover⟩ :=
    Ideal.exists_isPrime_liesOver_of_faithfullyFlat (A := R)
      (B := Work.DSM1p.FamTower R p x n) l.last.asIdeal
  haveI : P.IsPrime := hPprime
  haveI : P.LiesOver l.last.asIdeal := hPover
  -- descend the chain to the stage
  obtain ⟨L, hLlen, -, -⟩ :=
    Ideal.exists_ltSeries_of_hasGoingDown (S := Work.DSM1p.FamTower R p x n) l P
  have hLd : L.length = d := hLlen.trans hl
  calc (d : WithBot ℕ∞) = (L.length : WithBot ℕ∞) := by rw [hLd]
    _ ≤ ringKrullDim (Work.DSM1p.FamTower R p x n) := Order.LTSeries.length_le_krullDim L

end Work.DSM1p.Family
