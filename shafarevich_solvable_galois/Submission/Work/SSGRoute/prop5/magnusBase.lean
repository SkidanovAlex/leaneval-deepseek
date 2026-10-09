/-
# `magnusBase`: shared vocabulary for the Magnus core theorem

This module collects the definitions that the proof of `magnusCore` (`prop5/magnusCore.lean`)
needs, and which the downstream files (lemmas about the commutator monomials, delegated to
colleagues) refer to:

* `monGrp X : Magma X → FreeGroup X`, the commutator monomial in the free group, of weight
  `Magma.size c` (i.e. lying in `γ_{size c - 1}` in Mathlib's indexing);
* `Phi X : FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆ FreeAssoc X`, the canonical Lie homomorphism, whose
  injectivity is Witt's theorem (`Phi_injective`, deduced from the team's Witt development).

The Lie-evaluation `monLie` and the bracket evaluation `monBrk` of a binary tree are imported from
`witt/Vocab` (identical definitions, kept in one place so that the hypothesis of `magnusCore` and
the leading-term lemmas of `witt/*` speak the same language).

Witt's theorem is assembled here (rather than imported from `witt/Main.lean`) because `witt/Main`
reaches `witt/Defs.lean`, whose `IsLyndon` clashes with the `IsLyndon` of `magnusLieDefs.lean`,
which is needed by the graded theory of `core/`.  The Hall-set inputs used here
(`witt/hall_spanning.lean`, `witt/leading_term_coeff.lean`, `witt/hall_foliage_lt_right.lean`,
`witt/Swap.lean`, `witt/Assembly.lean`) are all independent of `witt/Defs.lean`.
-/
import Mathlib
import Submission.Work.SSGRoute.prop5.magnusFramework
import Submission.Work.SSGRoute.prop5.magnus_mem_one_add
import Submission.Work.SSGRoute.prop5.commutator_lowerCentralSeries_le
import Submission.Work.SSGRoute.prop5.witt.Basic
import Submission.Work.SSGRoute.prop5.witt.Vocab
import Submission.Work.SSGRoute.prop5.witt.Assembly
import Submission.Work.SSGRoute.prop5.witt.Swap
import Submission.Work.SSGRoute.prop5.witt.hall_foliage_lt_right
import Submission.Work.SSGRoute.prop5.witt.hall_spanning
import Submission.Work.SSGRoute.prop5.witt.leading_term_coeff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-- The commutator monomial in the free group attached to a binary tree: generators go to the
corresponding free generator and a product of trees to the group commutator. -/
def monGrp (X : Type*) : Magma X → FreeGroup X
  | .gen x => FreeGroup.of x
  | .mul a b => ⁅monGrp X a, monGrp X b⁆

@[simp] theorem monGrp_gen (X : Type*) (x : X) : monGrp X (.gen x) = FreeGroup.of x := rfl

@[simp] theorem monGrp_mul (X : Type*) (a b : Magma X) :
    monGrp X (.mul a b) = ⁅monGrp X a, monGrp X b⁆ := rfl

/-- The commutator monomial attached to a tree of size `m` lies in the `(m-1)`-st term of the
lower central series (i.e. the paper's `γ_m`). -/
theorem monGrp_mem_lowerCentralSeries (c : Magma X) :
    monGrp X c ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (Magma.size c - 1) := by
  induction c with
  | gen x => simp [Magma.size_gen]
  | mul a b iha ihb =>
      rw [monGrp_mul, Magma.size_mul]
      have h := commutator_lowerCentralSeries_le (FreeGroup X) (Magma.size a - 1) (Magma.size b - 1)
        (Subgroup.commutator_mem_commutator iha ihb)
      have hidx : Magma.size a - 1 + (Magma.size b - 1) + 1 = Magma.size a + Magma.size b - 1 := by
        have ha := Magma.size_pos a
        have hb := Magma.size_pos b
        omega
      rwa [hidx] at h

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The algebra equivalence `FreeAlgebra ℤ X ≃ₐ[ℤ] ℤ[FreeMonoid X]`, regarded as a Lie
homomorphism. -/
noncomputable def equivLie (X : Type) : FreeAlgebra ℤ X →ₗ⁅ℤ⁆ FreeAssoc X :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℤ) (X := X) :
    FreeAlgebra ℤ X →ₐ[ℤ] FreeAssoc X).toLieHom

/-- The canonical Lie homomorphism from the free Lie algebra over `ℤ` on `X` to the free
associative algebra, sending each generator to itself.  Its injectivity is Witt's theorem. -/
noncomputable def Phi (X : Type) : FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆ FreeAssoc X :=
  (equivLie X).comp (fL X)

theorem Phi_apply (X : Type) (z : FreeLieAlgebra ℤ X) :
    Phi X z = FreeAlgebra.equivMonoidAlgebraFreeMonoid (fL X z) := rfl

theorem Phi_monLie (X : Type) (c : Magma X) : Phi X (monLie X c) = monBrk X c := by
  obtain ⟨instLO, -⟩ := exists_wellFoundedLT X
  letI := instLO
  rw [Phi_apply, fL_monLie, equivMonoidAlgebra_monBrkA]

/-- **Witt's theorem**: the canonical Lie map `L → A` is injective.

Assembled from the Hall-set inputs (Hall spanning, leading term, foliage injectivity) exactly as
in `witt/Main.lean`, but with the Hall-tree inputs that avoid `witt/Defs.lean`
(`witt/hall_spanning.lean` supplies the same foliage injectivity there). -/
theorem Phi_injective (X : Type) : Function.Injective (Phi X) := by
  have hord : Function.Injective (fL X) := by
    obtain ⟨instLO, -⟩ := exists_wellFoundedLT X
    letI := instLO
    intro z w hzw
    exact fL_injective (fun v => witt.hall_spanning (monLie X) (fun _ _ => rfl) v)
      (fun c hc => witt.leading_term_coeff hc (fun a b hab =>
        swap_hall_of_crux (fun _ _ hh => witt.hall_foliage_lt_right hh) hab))
      (fun a b ha hb h => witt.hall_foliage_injective_aux ha hb h) hzw
  intro z w hzw
  rw [Phi_apply, Phi_apply] at hzw
  exact hord ((FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℤ) (X := X)).injective hzw)

end Work.SSGRoute.prop5
