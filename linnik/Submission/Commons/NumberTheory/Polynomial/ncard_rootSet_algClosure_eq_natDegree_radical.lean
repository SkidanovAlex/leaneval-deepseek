import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial
open scoped Polynomial

namespace Commons.NumberTheory.Polynomial

/-- If `q ∣ p` and `p ∣ q ^ n` for some `n`, then `p` and `q` have the same roots in any
field extension. This is the key step in comparing a polynomial with its radical. -/
theorem rootSet_eq_of_dvd_of_dvd_pow {T S : Type*} [Field T] [Field S] [Algebra T S]
    [Module.IsTorsionFree T S] {p q : Polynomial T} (hp : p ≠ 0) (hq : q ≠ 0)
    (hdvd : q ∣ p) (hpow : ∃ n, p ∣ q ^ n) : p.rootSet S = q.rootSet S := by
  ext x
  rw [mem_rootSet_of_ne hp, mem_rootSet_of_ne hq]
  constructor
  · intro hx
    obtain ⟨n, r, hr⟩ := hpow
    have h1 : aeval x (q ^ n) = 0 := by rw [hr, map_mul, hx, zero_mul]
    rw [map_pow] at h1
    exact (pow_eq_zero_iff'.mp h1).1
  · intro hx
    obtain ⟨r, hr⟩ := hdvd
    rw [hr, map_mul, hx, zero_mul]

/-- Over a finite field, the number of **distinct** roots of a nonzero polynomial `f` in the
algebraic closure equals the degree of its squarefree part (`UniqueFactorizationMonoid.radical`).

Both sides are `∑_i deg g_i` over the distinct monic irreducible factors `g_i` of `f`: the
radical is `∏_i g_i`, and every irreducible polynomial over a finite field is separable, so `g_i`
has exactly `deg g_i` distinct roots in the algebraic closure. -/
theorem ncard_rootSet_algClosure_eq_natDegree_radical {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (hf : f ≠ 0) :
    (f.rootSet (AlgebraicClosure F)).ncard
      = (UniqueFactorizationMonoid.radical f).natDegree := by
  have hroot : f.rootSet (AlgebraicClosure F)
      = (UniqueFactorizationMonoid.radical f).rootSet (AlgebraicClosure F) :=
    rootSet_eq_of_dvd_of_dvd_pow hf UniqueFactorizationMonoid.radical_ne_zero
      UniqueFactorizationMonoid.radical_dvd_self
      (UniqueFactorizationMonoid.exists_dvd_radical_self_pow hf)
  have hsep : (UniqueFactorizationMonoid.radical f : Polynomial F).Separable :=
    PerfectField.separable_iff_squarefree.mpr (UniqueFactorizationMonoid.squarefree_radical (a := f))
  have hcard : Fintype.card ((UniqueFactorizationMonoid.radical f).rootSet (AlgebraicClosure F))
      = (UniqueFactorizationMonoid.radical f).natDegree :=
    card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _)
  rw [← hcard, Set.fintypeCard_eq_ncard, hroot]

end Commons.NumberTheory.Polynomial