import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.LocalAnabelian.ResidueField.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `κ(μ_{p'})` is Galois over `κ`

`unramifiedClosure p` is the compositum `κ(μ_{p'}) = ⨆ κ⟮ζ⟯` over all primitive roots
of unity `ζ` of order `n` prime to `p`, realised inside the ambient extension `K'`.

The point of this file is that this compositum is *always* Galois over `κ`, with no
hypothesis whatsoever on `κ`, `K'` or the algebra structure `κ → K'`:

* each simple extension `κ⟮ζ⟯`, with `ζ` a primitive `n`-th root of unity (`n ≠ 0`), is a
  cyclotomic extension of `κ` and hence Galois (`IsCyclotomicExtension.isGalois`);
* a compositum of Galois intermediate fields is Galois — normal extensions are closed
  under `iSup` (`IntermediateField.normal_iSup`) and so are separable ones
  (`IntermediateField.isSeparable_iSup`).

The only small subtlety is the index of the `iSup` in the definition: it ranges over
`(n : {n : ℕ // ¬ p ∣ n})`, then `ζ : K'`, then a *proof* `hζ : IsPrimitiveRoot ζ n`.
The last index is a proposition, which is handled by `isGalois_iSup_prop`: a supremum over
a proposition is either the term (if inhabited) or `⊥`, and both are Galois.
-/

set_option linter.style.haveILetI false

open scoped Classical
open IntermediateField

namespace NK.LocalAnabelian.ResidueField

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-- A compositum of Galois intermediate fields is Galois: normal and separable extensions
are both stable under arbitrary `iSup`s. -/
theorem isGalois_iSup {ι : Type*} (t : ι → IntermediateField κ K')
    [h : ∀ i, IsGalois κ (t i)] : IsGalois κ (↥(⨆ i, t i)) :=
  isGalois_iff.mpr ⟨IntermediateField.isSeparable_iSup κ K',
    IntermediateField.normal_iSup κ K' t⟩

/-- A supremum of a single intermediate field over a propositional index: it is the field
itself when the proposition holds and `⊥` otherwise; both are Galois. -/
theorem isGalois_iSup_prop {P : Prop} (a : IntermediateField κ K')
    (ha : P → IsGalois κ (↥a)) : IsGalois κ (↥(⨆ (_ : P), a)) := by
  by_cases h : P
  · rw [iSup_pos h]; exact ha h
  · rw [iSup_neg h]; exact isGalois_bot

/-- `κ⟮ζ⟯` is Galois over `κ` whenever `ζ` is a primitive `n`-th root of unity with
`n ≠ 0`: it is the splitting field of `X ^ n - 1`, i.e. a cyclotomic extension. -/
theorem isGalois_adjoin_primitiveRoot {n : ℕ} (hn : n ≠ 0) {ζ : K'}
    (hζ : IsPrimitiveRoot ζ n) : IsGalois κ (κ⟮ζ⟯) := by
  haveI : NeZero n := ⟨hn⟩
  have halg : IsAlgebraic κ ζ := by
    refine ⟨Polynomial.X ^ n - 1, ?_, ?_⟩
    · simpa using Polynomial.X_pow_sub_C_ne_zero (NeZero.pos n) (1 : κ)
    · simp [hζ.pow_eq_one]
  have hcyc : IsCyclotomicExtension {n} κ (κ⟮ζ⟯) := by
    change IsCyclotomicExtension {n} κ (IntermediateField.adjoin κ {ζ}).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
    exact hζ.adjoin_isCyclotomicExtension κ
  exact IsCyclotomicExtension.isGalois {n} κ (κ⟮ζ⟯)

theorem isGalois_unramifiedClosure {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    (p : ℕ) : IsGalois κ (unramifiedClosure (κ := κ) (K' := K') p) := by
  rw [unramifiedClosure]
  refine isGalois_iSup (t := fun n : {n : ℕ // ¬ p ∣ n} =>
    ⨆ (ζ : K') (_ : IsPrimitiveRoot ζ (↑n)), κ⟮ζ⟯) (h := ?_)
  intro n
  refine isGalois_iSup (t := fun ζ : K' =>
    ⨆ (_ : IsPrimitiveRoot ζ (↑n)), κ⟮ζ⟯) (h := ?_)
  intro ζ
  exact isGalois_iSup_prop (P := IsPrimitiveRoot ζ (↑n)) κ⟮ζ⟯
    (fun h => isGalois_adjoin_primitiveRoot (κ := κ) (K' := K')
      (n := (↑n)) (by rintro h0; exact n.2 (h0 ▸ dvd_zero p)) h)

end NK.LocalAnabelian.ResidueField
