/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `p`-perfection of a ring of characteristic `p`

For a commutative ring `A` of characteristic `p`, `Work.DSEQP.pPerfection A p` is the
filtered colimit of the system `A --F--> A --F--> ⋯`, i.e. the "perfection"
`A^{1/p^∞} = ⋃_e A^{1/p^e}` (direct limit form: an element of the `e`-th copy is
regarded as a `p^e`-th root).

This is the base change that the equal characteristic `p` proof of the direct summand
theorem uses:  `A → A^{1/p^∞}` is faithfully flat when `A` is regular (Kunz), and it is
perfect, so `p^e`-th roots exist.  See `Work.DSEQP.isSplinter_of_flat_perfect` for how
that is used.
-/
import Mathlib
import Submission.Work.DSEQP.Basic

namespace Work.DSEQP

universe u

/-- The `n`-th iterate of the Frobenius endomorphism of a ring of characteristic `p`. -/
noncomputable def frobPowHom (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p]
    (n : ℕ) : A →+* A :=
  (frobenius A p) ^ n

/-- The `p`-perfection of a commutative ring `A` of characteristic `p`: the filtered
colimit of the system `A --F--> A --F--> ⋯`.

The element `pPerfection.of e a` is the `p^e`-th root of (the image of) `a`. -/
abbrev pPerfection (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p] : Type u :=
  Ring.DirectLimit (fun _ : ℕ => A) fun i j _ => ⇑(frobPowHom A p (j - i))

namespace pPerfection

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] [CharP A p]

/-- The canonical map `A → A^{1/p^∞}` at level `e`. -/
noncomputable def of (e : ℕ) : A →+* pPerfection A p :=
  Ring.DirectLimit.of (fun _ : ℕ => A) (fun i j _ => ⇑(frobPowHom A p (j - i))) e

theorem of_f {i j : ℕ} (hij : i ≤ j) (a : A) :
    of (A := A) (p := p) j (frobPowHom A p (j - i) a) = of (A := A) (p := p) i a :=
  Ring.DirectLimit.of_f (G := fun _ : ℕ => A)
    (f := fun i j _ => ⇑(frobPowHom A p (j - i))) hij a

/-- `of (e+1) a` is a `p`-th root of `of e a`. -/
theorem of_succ_pow (e : ℕ) (a : A) :
    (of (A := A) (p := p) (e + 1) a) ^ p = of (A := A) (p := p) e a := by
  have h2 := of_f (A := A) (p := p) (i := e) (j := e + 1) (Nat.le_succ e) a
  simp only [Nat.add_sub_cancel_left, frobPowHom, pow_one, frobenius_def] at h2
  rw [← map_pow]
  exact h2

/-- The `p^e`-th root of an element of `A`, as an element of the perfection. -/
noncomputable def rootTower (a : A) (e : ℕ) : pPerfection A p := of (A := A) (p := p) e a

/-- The defining property of the root tower: `rootTower a (e+1) ^ p = rootTower a e`. -/
theorem rootTower_pow (a : A) (e : ℕ) :
    (rootTower (p := p) a (e + 1)) ^ p = rootTower (p := p) a e :=
  of_succ_pow (A := A) (p := p) e a

/-- The structure map `A → A^{1/p^∞}`. -/
noncomputable def algebraMap' : A →+* pPerfection A p := of (A := A) (p := p) 0

noncomputable instance : Algebra A (pPerfection A p) :=
  (algebraMap' (A := A) (p := p)).toAlgebra

end pPerfection

end Work.DSEQP
