import Mathlib
import Submission.NK.GlobalCFTdeep.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ĥ¹` of the trivial representation on `ℤ`

For a finite group `G` and the trivial `ℤ[G]`-module `ℤ` (the representation `Rep.trivial ℤ G ℤ`),
the first Tate cohomology vanishes:

  `Ĥ¹(G, ℤ) = 0`,    equivalently   `hOne (Rep.trivial ℤ G ℤ) = 1`.

This is the odd-degree half of the classical computation `Ĥⁿ(G, ℤ) = 0` for `n` odd and
`Ĥⁿ(G, ℤ) = ℤ/|G|` for `n` even.  In degree one the argument is elementary:

* for `n = 1 ≠ 0` the Tate cohomology agrees with ordinary group cohomology
  (`TateCohomology.isoGroupCohomology`), and
* for a *trivial* representation Mathlib identifies `H¹(G, A) ≅ Hom(G, A)`
  (`groupCohomology.H1IsoOfIsTrivial`);

so `Ĥ¹(G, ℤ) ≅ Hom(G, ℤ)`, and every group homomorphism from the finite group `G` to the
torsion-free group `ℤ` is trivial: if `x : G` then `x ^ |G| = 1`, hence `|G| • f x = 0` and so
`f x = 0` because `|G| ≠ 0` in the domain `ℤ`.

The file is self-contained: the content specific to `ℤ` is only the vanishing of
`Hom(G, ℤ)`, which is proved below as `subsingleton_addHom_int`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

/-- Every additive homomorphism from the finite additive group `Additive G` to `ℤ` is zero:
`x ^ |G| = 1` gives `|G| • f x = 0` and `|G| ≠ 0` in `ℤ`. -/
private lemma addHom_int_apply_eq_zero (G : Type) [Group G] [Fintype G]
    (f : Additive G →+ ℤ) (x : Additive G) : f x = 0 := by
  have hx : Fintype.card G • x = 0 := by
    apply Additive.toMul.injective
    show (Fintype.card G • x).toMul = (0 : Additive G).toMul
    simp [pow_card_eq_one]
  have h3 := AddMonoidHom.map_nsmul f (Fintype.card G) x
  rw [hx, map_zero, nsmul_eq_mul] at h3
  have hn : (Fintype.card G : ℤ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := G)
  exact (mul_eq_zero.mp h3.symm).resolve_left hn

/-- `Hom(G, ℤ) = 0` for a finite group `G`: the target of `Ĥ¹` of the trivial representation on
`ℤ`. -/
private lemma subsingleton_addHom_int (G : Type) [Group G] [Fintype G] :
    Subsingleton (Additive G →+ ℤ) :=
  ⟨fun f g => AddMonoidHom.ext fun x => by
    rw [addHom_int_apply_eq_zero G f x, addHom_int_apply_eq_zero G g x]⟩

/-- **`Ĥ¹` of the trivial representation on `ℤ` is trivial**:
`hOne (Rep.trivial ℤ G ℤ) = |Ĥ¹(G, ℤ)| = 1` for a finite group `G`. -/
theorem hOne_trivial (G : Type) [Group G] [Fintype G] :
    hOne (Rep.trivial ℤ G ℤ) = 1 := by
  rw [hOne_def]
  -- `Ĥ¹` agrees with ordinary group cohomology in positive degrees.
  have h1 : Nat.card (tateCohomology (Rep.trivial ℤ G ℤ) 1)
      = Nat.card (groupCohomology (Rep.trivial ℤ G ℤ) 1) :=
    Nat.card_congr (CategoryTheory.Iso.toLinearEquiv
      ((TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app
        (Rep.trivial ℤ G ℤ))).toEquiv
  rw [h1]
  -- For a trivial representation, `H¹(G, A) ≅ Hom(G, A)`.
  have h2 : Nat.card (groupCohomology (Rep.trivial ℤ G ℤ) 1)
      = Nat.card (Additive G →+ (Rep.trivial ℤ G ℤ)) :=
    Nat.card_congr (CategoryTheory.Iso.toLinearEquiv
      (groupCohomology.H1IsoOfIsTrivial (Rep.trivial ℤ G ℤ))).toEquiv
  rw [h2, Nat.card_eq_one_iff_unique]
  exact ⟨subsingleton_addHom_int G, ⟨0⟩⟩

end NK.GlobalCFTdeep.Herbrand
