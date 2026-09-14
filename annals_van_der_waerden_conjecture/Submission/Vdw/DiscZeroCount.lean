import Mathlib
import Submission.Commons.FieldTheory.Polynomial.discr_ne_zero_of_separable
import Submission.Commons.FieldTheory.Polynomial.discr_eq_zero_iff_not_separable
import Submission.Commons.FieldTheory.Polynomial.squarefree_monic_card
import Submission.Commons.FieldTheory.Polynomial.card_monic_degree

/-!
# Monic polynomials over a finite field with vanishing discriminant

**Main theorems:** over a finite field `F` with `q` elements, exactly
`q^(n-1)` monic polynomials of degree `n ≥ 2` have vanishing discriminant:

`monic_disc_zero_ncard_eq`:
`({p : F[X] | p.Monic ∧ p.natDegree = n ∧ Polynomial.discr p = 0}).ncard
   = q^(n-1)`

and its `≤` corollary `monic_disc_zero_ncard_le` (the O-form used in the
Case III / geometric-sieve estimates: per prime `p`, at most `p^(n-1)`
monic degree-`n` polynomials over `𝔽_p` have `Disc ≡ 0 mod p`).

Proof chain:
* over a perfect field `F` (finite fields are perfect: `PerfectField.ofFinite`),
  `p.Separable ↔ Squarefree p` (`PerfectField.separable_iff_squarefree`); and
  for monic `p` of positive degree `Disc p = 0 ↔ ¬ p.Separable`
  (`Commons.FieldTheory.Polynomial.discr_eq_zero_iff_not_separable`), so among
  monic degree-`n ≥ 1` polynomials, `{Disc = 0}` equals `{monic} \ {squarefree}`
  (`monic_disc_zero_set_eq_not_squarefree`);
* the monic degree-`n` count is `q^n`
  (`Commons.FieldTheory.Polynomial.card_monic_degree`) and the squarefree
  monic degree-`n` count is `q^n − q^(n−1)` for `2 ≤ n`
  (`Commons.FieldTheory.Polynomial.squarefree_monic_card`).

The set of all monic degree-`n` polynomials is finite, being in bijection
with the coefficient vectors `Fin n → F`
(`Commons.FieldTheory.Polynomial.monicDegreeEquiv`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Submission.Vdw

noncomputable section

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F]

/-- Over a perfect field, a monic polynomial of positive degree has vanishing discriminant iff
it is not squarefree. -/
theorem discr_eq_zero_iff_not_squarefree [PerfectField F] {p : F[X]}
    (hp : p.Monic) (hn : 0 < p.natDegree) : Polynomial.discr p = 0 ↔ ¬ Squarefree p := by
  rw [Commons.FieldTheory.Polynomial.discr_eq_zero_iff_not_separable hp hn]
  exact not_congr (PerfectField.separable_iff_squarefree (K := F) (g := p))

/-- A monic squarefree polynomial over a perfect field has nonzero discriminant. -/
theorem discr_ne_zero_of_squarefree [PerfectField F] {p : F[X]}
    (hp : p.Monic) (hsq : Squarefree p) : Polynomial.discr p ≠ 0 := by
  have hsep : p.Separable := (PerfectField.separable_iff_squarefree (K := F) (g := p)).mpr hsq
  exact Commons.FieldTheory.Polynomial.discr_ne_zero_of_separable p hp hsep

variable [Fintype F] [DecidableEq F]

/-- The set of monic polynomials of degree `n` over a finite field is finite. -/
theorem monicDeg_finite (n : ℕ) :
    ({p : F[X] | p.Monic ∧ p.natDegree = n} : Set F[X]).Finite := by
  classical
  let s : Set F[X] := {p | p.Monic ∧ p.natDegree = n}
  refine Set.finite_def.mpr ?_
  refine ⟨Fintype.ofEquiv (Fin n → F) ((Commons.FieldTheory.Polynomial.monicDegreeEquiv F n).symm)⟩

/-- Monic degree-`n` polynomials with vanishing discriminant are not squarefree. -/
theorem monic_disc_zero_mem_not_squarefree (n : ℕ) :
    {p : F[X] | p.Monic ∧ p.natDegree = n ∧ Polynomial.discr p = 0} ⊆
      {p : F[X] | p.Monic ∧ p.natDegree = n} \
        {p : F[X] | p.Monic ∧ p.natDegree = n ∧ Squarefree p} := by
  intro p hp
  have hmon : p.Monic ∧ p.natDegree = n := ⟨hp.1, hp.2.1⟩
  letI : PerfectField F := PerfectField.ofFinite
  refine ⟨hmon, ?_⟩
  rintro ⟨hmon', hnat, hsq⟩
  exact (discr_ne_zero_of_squarefree (F := F) hp.1 hsq) hp.2.2

/-- Among monic degree-`n` polynomials over a finite field, vanishing discriminant is exactly
non-squarefreeness (set equality), for `1 ≤ n`. -/
theorem monic_disc_zero_set_eq_not_squarefree (n : ℕ) (hn : 1 ≤ n) :
    {p : F[X] | p.Monic ∧ p.natDegree = n ∧ Polynomial.discr p = 0} =
      {p : F[X] | p.Monic ∧ p.natDegree = n} \
        {p : F[X] | p.Monic ∧ p.natDegree = n ∧ Squarefree p} := by
  classical
  letI : PerfectField F := PerfectField.ofFinite
  ext p
  constructor
  · intro hp
    have hpos : 0 < p.natDegree := by
      rcases hp with ⟨hmon, hnat, hdisc⟩
      omega
    have hnsq : ¬ Squarefree p :=
      (discr_eq_zero_iff_not_squarefree (F := F) hp.1 hpos).mp hp.2.2
    refine ⟨⟨hp.1, hp.2.1⟩, ?_⟩
    rintro ⟨hmon, hnat, hsq⟩
    exact hnsq hsq
  · intro hp
    rcases hp with ⟨hpall, hnsqfull⟩
    rcases hpall with ⟨hmon, hnat⟩
    have hpos : 0 < p.natDegree := by omega
    have hnsq : ¬ Squarefree p := by
      intro hsq
      exact hnsqfull ⟨hmon, hnat, hsq⟩
    exact ⟨hmon, hnat, (discr_eq_zero_iff_not_squarefree (F := F) hmon hpos).mpr hnsq⟩

/-- **Exact count:** over a finite field `F` with `q` elements, exactly `q^(n-1)` monic
polynomials of degree `n ≥ 2` have vanishing discriminant. -/
theorem monic_disc_zero_ncard_eq (n : ℕ) (hn : 2 ≤ n) :
    ({p : F[X] | p.Monic ∧ p.natDegree = n ∧ Polynomial.discr p = 0} : Set (F[X])).ncard =
      Fintype.card F ^ (n - 1) := by
  classical
  let all : Set F[X] := {p : F[X] | p.Monic ∧ p.natDegree = n}
  let sq : Set F[X] := {p : F[X] | p.Monic ∧ p.natDegree = n ∧ Squarefree p}
  let dz : Set F[X] := {p : F[X] | p.Monic ∧ p.natDegree = n ∧ Polynomial.discr p = 0}
  have hall : all.Finite := by
    simpa [all] using monicDeg_finite (F := F) n
  have hsq_sub : sq ⊆ all := by
    intro p hp
    exact ⟨hp.1, hp.2.1⟩
  have hset : dz = all \ sq := by
    simpa [dz, sq, all] using (monic_disc_zero_set_eq_not_squarefree (F := F) n (by omega : 1 ≤ n))
  have hsqcard : sq.ncard = Fintype.card F ^ n - Fintype.card F ^ (n - 1) := by
    simpa [sq] using (Commons.FieldTheory.Polynomial.squarefree_monic_card (F := F) n hn)
  have hallcard : all.ncard = Fintype.card F ^ n := by
    simpa [all] using (Commons.FieldTheory.Polynomial.card_monic_degree (F := F) n)
  have hdiff : (all \ sq).ncard = Fintype.card F ^ n - sq.ncard := by
    have h := Set.ncard_sdiff_add_ncard_of_subset (s := sq) (t := all) hsq_sub hall
    omega
  have hdiff' : (all \ sq).ncard = Fintype.card F ^ (n - 1) := by
    rw [hdiff, hsqcard]
    have hq : 1 ≤ Fintype.card F := by
      exact Fintype.card_pos (α := F)
    have hpow : Fintype.card F ^ (n - 1) ≤ Fintype.card F ^ n := by
      exact Nat.pow_le_pow_right hq (Nat.sub_le n 1)
    omega
  calc
    dz.ncard = (all \ sq).ncard := by rw [hset]
    _ = Fintype.card F ^ (n - 1) := hdiff'

/-- **O-form:** over a finite field `F` with `q` elements, at most `q^(n-1)` monic
polynomials of degree `n ≥ 2` have vanishing discriminant. -/
theorem monic_disc_zero_ncard_le (n : ℕ) (hn : 2 ≤ n) :
    ({p : F[X] | p.Monic ∧ p.natDegree = n ∧ Polynomial.discr p = 0} : Set (F[X])).ncard ≤
      Fintype.card F ^ (n - 1) := by
  exact le_of_eq (monic_disc_zero_ncard_eq (F := F) n hn)

/-- Over `𝔽_p` (`p` prime), at most `p^(n-1)` monic degree-`n` polynomials have vanishing
discriminant. -/
theorem monic_disc_zero_ncard_le_zmod (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (hn : 2 ≤ n) :
    ({f : (ZMod p)[X] | f.Monic ∧ f.natDegree = n ∧ Polynomial.discr f = 0} : Set ((ZMod p)[X])).ncard ≤
      p ^ (n - 1) := by
  have h := monic_disc_zero_ncard_le (F := ZMod p) n hn
  simpa using h

end

end Submission.Vdw
