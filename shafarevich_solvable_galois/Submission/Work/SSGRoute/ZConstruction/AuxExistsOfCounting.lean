import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.AuxDatumZHyp
import Submission.Work.SSGRoute.ZDataMup.LocalData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `AuxExists` from the counting-side gates: the two pinned `∀ N` blocks

The auxiliary class `Work.SSGRoute.AuxExists` reduces, after this session, to the one-dimensional gate
`Work.SSGRoute.MupGate` together with two gates of the counting side, quantified over the *auxiliary
level* `N` (which `AuxExists` itself quantifies over: `Work.SSGRoute.z_data_of_spanning_of_aux`
applies it at `N₀ ⊔ Λ`):

* `AuxDatumOrthogonality` -- the *honest* dual condition `ZDataMup.IsOrthogonalToDual` for the
  prescribed datum `auxDatum K S ν` at the enlarged place set `T⁺`; for the datum it is supplied by
  the p. 18 chase together with `Work.SSGRoute.auxDatum_orthogonal_enlarged`
  (`ZConstruction/auxDatum_orthogonal_enlarged.lean`);
* `AuxDatumCounting` -- the level-`K` Poitou--Tate counting inequality at `T⁺`, the seam with the PT
  lane (`ZConstruction/NOTE_seam_counting.lean`).  It is stated **inline** here (same body as
  `Work.SSGRoute.ZDataMup.CountingInequality`) so that this module does not depend on
  `ZDataMup/tatePoitou_h1_realisation.lean`, which is a sibling lane's file and can be red
  independently of this one; the two are the same `Prop` up to unfolding.

The false mixed gate `∀ M, AuxRealisationExt K Λ M` of
`Work.SSGRoute.auxExists_of_pairing_and_realisation` is *not* used and cannot be
(`ZConstruction/NOTE_session17.lean`).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
variable {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [Fintype (K ≃ₐ[k] K)] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The honesty block**: for every auxiliary level `N ⊇ Λ` and every admissible configuration of
place sets (`S` the base set, `T` a level-`K` representative set of `cs(S)`, `T⁺ ⊇ T` its
enlargement) and every datum `ν` satisfying `ZHyp` at `(Λ, S)`, the prescribed datum
`auxDatum K S ν` is orthogonal to the honest dual family at `T⁺`. -/
def AuxDatumOrthogonality (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) →
    ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p) : Prop :=
  ∀ (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N], Λ ≤ N →
    ∀ {S T Te : Finset (ValuationSubring Ω)}, (∀ A ∈ S, SSGRoute.IsFinPlace k A) →
      (∀ A ∈ T, SSGRoute.IsFinPlace k A) →
      (∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.KConj K A B → A = B) →
      (∀ A ∈ T, ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A) →
      (∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∃ A' ∈ T, Work.SSGRoute.KConj K A' B) →
      (∀ A ∈ T, A ∈ Te) → (∀ A ∈ Te, SSGRoute.IsFinPlace k A) →
      (∀ A ∈ Te, ∀ B ∈ Te, Work.SSGRoute.KConj K A B → A = B) →
      ∀ {ν : (Ω ≃ₐ[k] Ω) → ZMod p}, Work.SSGRoute.ZHyp (p := p) K Λ S ν →
        Work.SSGRoute.ZDataMup.IsOrthogonalToDual p k Ω K pair Te
          (Work.SSGRoute.auxDatum (p := p) K S ν)

/-- **The counting block**: the level-`K` Poitou--Tate counting inequality at the enlarged set `T⁺`,
for every auxiliary level and every *covering* configuration.  Stated inline (see the module
docstring); it is `Work.SSGRoute.ZDataMup.CountingInequality` at `Te`, together with the hypothesis
that makes it true.

**The coverage hypothesis is not cosmetic.**  Milne, *Arithmetic Duality Theorems*, I.4.10 -- the
theorem the inequality instantiates -- assumes that the order of the coefficient module is a *unit in
the ring of `S`-integers*, i.e. that the place set contains the places above `p` (and, for the
level-`K` sequence to make sense, the places ramified in `K|k`).  Without it the inequality is
**false**: for `(k, Ω, K, p, Te) = (Q, Q-bar, Q, 3, {A})` with `A` the place of `Ω` over `2`, one has
`dim ∏_{A ∈ Te} H¹(K_A, ZMod 3) = 1` while the localisation image `W_Te` is `0`
(`lim_n Cl(2^n) = lim_n (Z/2^n)^x` has no `3`-part), so `1 ≤ 2·0` fails -- the counterexample
recorded in `ZDataMup/TATEPOITOU_STATUS.md`, section "SESSION 4".  The version of this block *without*
the coverage hypothesis, which stood here before, was therefore unprovable; the hypothesis is exactly
the `hSram` of the sibling statements (`PT.pt_selmer_counting_identity`,
`ZSplit.levelK_counting_identity`).

In the intended instantiation of the assembly below, `N` is the auxiliary level of the section-4
induction, `Te` is a level-`K` representative set of `cs(S')` for an `S'` that covers the places
ramified in `N` (the hypothesis `hS'ram` of `Work.SSGRoute.AuxExists`), and the coverage hypothesis
is supplied by that plus the coverage of `S` itself (`hcoverage` of the assembly). -/
def AuxDatumCounting : Prop :=
  ∀ (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N], Λ ≤ N →
    ∀ {Te : Finset (ValuationSubring Ω)}, (∀ A ∈ Te, SSGRoute.IsFinPlace k A) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
        ∃ A ∈ Te, SSGRoute.IsConjPlace k A B) →
      Module.finrank (ZMod p)
          (↥(Work.SSGRoute.ZDataMup.localDataSpace (p := p) K Te) ⧸
            Work.SSGRoute.ZDataMup.localVanish (p := p) K Te) ≤
        2 * Module.finrank (ZMod p)
          (((Work.SSGRoute.ZDataMup.localImageIn (p := p) K Te) ⊔
              Work.SSGRoute.ZDataMup.localVanish (p := p) K Te).map
            (Submodule.mkQ (Work.SSGRoute.ZDataMup.localVanish (p := p) K Te)))


/-- **The honesty gate, with the pairing axioms bundled in** -- the form the assembly consumes.

`Work.SSGRoute.ZConstruction.AuxDatumOrthogonality` is a block about a *given* `pair`; the assembly
also needs that `pair` to be the one carrying the local Tate axioms and the product formula (that is
what makes the chase available for it).  Bundling the three together removes the possibility of
mismatch between "the `pair` of the pairing gate" and "the `pair` of the orthogonality block", which
is the binder question recorded in `ZConstruction/NOTE_seam_counting.lean`. -/
def AuxDatumOrthogonalityGate : Prop :=
  ∀ pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p,
    Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair →
    Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair →
    AuxDatumOrthogonality (p := p) (K := K) (Λ := Λ) pair

end

end Work.SSGRoute.ZConstruction
