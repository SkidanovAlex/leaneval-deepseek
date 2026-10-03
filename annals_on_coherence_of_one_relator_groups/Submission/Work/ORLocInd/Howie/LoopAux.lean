/-
# Auxiliary path algebra for the loops of a datum (Howie 2000)

A datum of Howie's Theorem 3.1 contains, for each `j`, a list of *terms*
`t = ⟨i, sign, δ, hδ⟩` (a relator of `P` or its inverse, together with a reduced path `δ` from the
base vertex `v` to the base vertex of the relator), and the identity

`W_j(γ) = ∏_k δ_k · r_{i_k}^{±1} · δ_k⁻¹`

holds in the vertex group `F(Γ)_v` (`Datum.heq`, with `RelatorTerm.loop` the product on the right).

The purpose of this file is to record the two elementary identities about `RelatorTerm.loop` that
make the *existence* of a datum purely a statement about the normal closure of the relators of `P`:

* `RelatorTerm.loop` of the `flip`ped term (same relator and path, opposite sign) is the inverse of
  `RelatorTerm.loop`;
* conjugating a loop by an element of the vertex group `F(Γ)_v` is again the loop of a term
  (with `δ` replaced by `q · δ`, where `q` is the path of the conjugating element).

Both rest on the single path identity `pmul_reverse_comp`: the free-groupoid product is compatible
with the reversal of paths.  Also proved here is `RelatorTerm.signedPath_flip`, the corresponding
statement for the signed relator paths.

The main consumer is `Work.ORLocInd.Howie.exists_datum_of_lift_eq_one`: given `γ : Fin n → F(Γ)_v`
and words `W_j` in the free group on `n` generators whose images in the presented groupoid vanish,
a datum with these `γ` and `W` exists.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Datum

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- **Reversal is compatible with the free-groupoid product**: the reverse of `p · q` is
`q⁻¹ · p⁻¹`. -/
theorem pmul_reverse_comp {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    (pmul p q).reverse = pmul q.reverse p.reverse := by
  have h1 : (p.comp q).reverse.ReducesTo (pmul q.reverse p.reverse) := by
    rw [Quiver.Path.reverse_comp]
    exact comp_reducesTo_pmul q.reverse p.reverse
  have h2 : (p.comp q).reverse.ReducesTo (pmul p q).reverse :=
    Quiver.Path.ReducesTo.reverse (comp_reducesTo_pmul p q)
  exact (red_eq_of_reducesTo_isReduced h2 ((pmul_isReduced p q).reverse)).symm.trans
    (red_eq_of_reducesTo_isReduced h1 (pmul_isReduced _ _))

namespace RelatorTerm

variable {P : Presentation V} {v : V}

/-- The term with the same relator and the same path but the opposite sign: its loop is the inverse
of the loop of `t`. -/
def flip (t : RelatorTerm P v) : RelatorTerm P v := ⟨t.i, !t.sign, t.δ, t.reduced⟩

@[simp] theorem flip_i (t : RelatorTerm P v) : (flip t).i = t.i := rfl

@[simp] theorem flip_sign (t : RelatorTerm P v) : (flip t).sign = !t.sign := rfl

@[simp] theorem flip_delta (t : RelatorTerm P v) : (flip t).δ = t.δ := rfl

@[simp] theorem flip_reduced (t : RelatorTerm P v) : (flip t).reduced = t.reduced := rfl

/-- The signed relator path of the flipped term is the reverse of the signed relator path of the
term: this is the path-level content of `loop (flip t) = (loop t)⁻¹`. -/
theorem signedPath_flip (t : RelatorTerm P v) : (flip t).signedPath = (t.signedPath).reverse := by
  obtain ⟨i, sign, δ, h⟩ := t
  cases sign <;> simp [flip, signedPath]

end RelatorTerm

end Work.ORLocInd.Howie
