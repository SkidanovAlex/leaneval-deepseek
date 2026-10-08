import Mathlib
import Submission.Work.BG.S02

/-!
# Area BG: shared definitions for Lemma 2.2, case one (`s02_lemma22CaseOne`)

This small module holds the definitions used both by the main file
`Submission/Work/BG/s02_lemma22CaseOne.lean` and by the delegated leaves underneath it.
It contains no `sorry` and no proofs beyond `simp`-level membership lemmas, so that any
colleague may import it freely while the main lemma is still in progress.

The object defined here is Bender–Glauberman's set of involutions of `H = C_G(t)` that lie
outside `H₀` (so the elements of `T = H₀ ∖ U` are products of two of them):

* `Work.BG.XH C` — the `Finset` of involutions `z ∈ H` with `z ∉ H₀`.
-/

namespace Work.BG

variable {G : Type} [Group G] [Finite G]

/-- The involutions of `H = C_G(t)` that do not lie in `H₀`: the `Finset` of all
`z : ↥C.P.H` with `z ∉ H₀` and `z² = 1`.

In Bender–Glauberman 1981 (p. 205) these are the elements of the classes `t₁^H ∪ t₂^H`
(involutions of `H ∖ H₀`); every `x ∈ T = H₀ ∖ U` is a product `xy` with `x, y` of this
form, and conversely the product of two such involutions lies in `H₀`. -/
noncomputable def XH (C : Sec2Ctx G) [Fintype ↥C.P.H] : Finset ↥C.P.H := by
  classical
  exact (Finset.univ : Finset ↥C.P.H).filter (fun z => (z : G) ∉ C.P.H0 ∧ z ^ 2 = 1)

@[simp] theorem mem_XH {C : Sec2Ctx G} [Fintype ↥C.P.H] {z : ↥C.P.H} :
    z ∈ XH C ↔ (z : G) ∉ C.P.H0 ∧ z ^ 2 = 1 := by
  classical
  simp [XH]

/-- The `Finset` of ordered pairs of elements of `X` whose product is `g`.  This is the
"pair count" set behind Bender–Glauberman's function `f(g) = #{(x,y) ∈ t^G × t^G : xy = g}`
(1981, proof of Lemma 2.2, p. 205).  It is a `def` (rather than an explicit `Finset.filter`
in every statement) so that the classical `DecidablePred` instance is available. -/
noncomputable def pairSet {G : Type} [Group G] (X : Finset G) (g : G) : Finset (G × G) := by
  classical
  exact (X ×ˢ X).filter (fun p => p.1 * p.2 = g)

@[simp] theorem mem_pairSet {G : Type} [Group G] {X : Finset G} {g : G} {p : G × G} :
    p ∈ pairSet X g ↔ p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 * p.2 = g := by
  classical
  simp [pairSet, and_assoc]

end Work.BG
