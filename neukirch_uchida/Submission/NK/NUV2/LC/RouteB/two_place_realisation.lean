import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.hasseSurjDefs
import Submission.NK.NUV2.LC.RouteB.hasseSurjTopDefs
import Submission.NK.NUV2.LC.RouteB.hasseSurj_of_top
import Submission.NK.NUV2.LC.RouteB.natCard_LocalH2_top
import Submission.NK.NUV2.LC.RouteB.onePlaceClasses
import Submission.NK.NUV2.LC.h2ProfiniteAddGroup
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction

/-!
# Route B, lemma (R2): the two-place realisation at an open level

The target theorem `NK.NUV2.LC.RouteB.two_place_realisation` is the `ι = Fin 2` instance of the
classical Hasse surjectivity `NK.NUV2.LC.RouteB.HasseSurj` (NSW (9.2.1), finite set of places).

## The assembly used here (deliberately *not* going through `RouteB/hasseSurj.lean`)

The classical statement is produced here from the `⊤`-case `HasseSurjTop`
(`NK.NUV2.LC.RouteB.hasseSurj_of_top`, proved) whose *only* remaining input is the "one-place
classes" statement `NK.NUV2.LC.RouteB.onePlaceClasses` (Kummer theory + weak approximation: for
each place of a finite family there is a global class non-trivial exactly there), together with the
local cardinality `NK.NUV2.LC.RouteB.natCard_LocalH2_top` (`|H²(D_A, Z/p)| = p`).

The reason for reproducing the few lines of `⊤`-case bookkeeping here (rather than importing
`Submission/Work/NUV2/LC/RouteB/hasseSurjTop.lean`, which contains them) is an import cycle: that
file imports `RouteB/open_two_place.lean`, which imports *this* file.  Keeping this file free of any
dependency on the `open_two_place`/`hasseSurj` chain breaks the cycle, so that `hasseSurj.lean` is
free to be proved from `hasseSurjTop`.  The auxiliary declarations below are `private` so that no
name is shared with the sibling files.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.NUV2.LC.RouteB

open NK.BrauerHasse

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## Auxiliary cohomological bookkeeping (private copies of sorry-free sibling lemmas) -/

/-- The `ZMod p`-module structure on the local cohomology `LocalH2 p U A` (the two types
`LocalH2 p U A` and `H2Profinite p (U ⊓ D_A)` are definitionally equal, but `LocalH2` is a `def`,
so type class search does not unfold it). -/
private noncomputable instance instModuleZModLocalH2Aux (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : ValuationSubring K') :
    Module (ZMod p) (NK.BrauerHasse.LocalH2 (K := K) (K' := K') p U A) :=
  inferInstanceAs (Module (ZMod p)
    (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p
      (U ⊓ NK.BrauerHasse.stabSubgroup A)))

/-- The localisation at a place, as an additive homomorphism (`LocalH2 p U A` and
`H2Profinite p (U ⊓ D_A)` are definitionally equal). -/
private noncomputable def locAddHomAux (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : NK.BrauerHasse.OverFinitePrime K K') :
    H2Profinite p U →+ H2Profinite p (U ⊓ stabSubgroup A.1) where
  toFun := fun x => H2Profinite.loc p U x A
  map_zero' := H2Profinite.loc_zero p U A
  map_add' := fun x y => H2Profinite.loc_add p U A x y

/-- The localisation is `ZMod p`-linear. -/
private theorem loc_smulAux (p : ℕ) [NeZero p] (U : Subgroup Gal(K'/K))
    (A : NK.BrauerHasse.OverFinitePrime K K') (c : ZMod p) (x : H2Profinite p U) :
    H2Profinite.loc p U (c • x) A = c • H2Profinite.loc p U x A := by
  have h : c = ((c.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val c).symm
  rw [h, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  exact map_nsmul (locAddHomAux p U A) c.val x

/-- **In a `ZMod p`-module of cardinality `p` (`p` a prime) every element is a scalar multiple of
every non-zero element.** -/
private theorem exists_smul_eq_of_card_eq_primeAux (p : ℕ) [Fact p.Prime] {M : Type} [AddCommGroup M]
    [Module (ZMod p) M] (hcard : Nat.card M = p) {y : M} (hy : y ≠ 0) :
    ∀ w : M, ∃ c : ZMod p, c • y = w := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Finite M := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact (Fact.out : p.Prime).ne_zero)
  have hinj : Function.Injective (fun c : ZMod p => c • y) := by
    intro c d hcd
    have h : (c - d) • y = 0 := by simp only [sub_smul, hcd, sub_self]
    rcases smul_eq_zero.mp h with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 hy
  have h1 : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hbij := (Nat.bijective_iff_injective_and_card (fun c : ZMod p => c • y)).mpr
    ⟨hinj, by rw [h1, hcard]⟩
  exact hbij.2





end NK.NUV2.LC.RouteB
