import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.Shafarevich.Defs
import Submission.Work.Tower.Shafarevich.Estimate
import Submission.Work.CFT.ShafarevichCore.Defs
import Submission.Work.CFT.ShafarevichCore.Splitting
import Submission.Work.CFT.Kummer.All

/-!
# The (a)-only arithmetic input of the tower: vocabulary

This area (`Work.Tower.MinkowskiGS`) re-architects the class-field tower of the unit-distance
construction so that its relation-rank input is **Koch's fact (a) alone** rather than the uniform
Shafarevich estimate `Work.CFT.ShafarevichTarget` (which additionally needs Artin reciprocity,
fact (b′)).

The mathematical content is recorded in `Submission/Work/CFT/MinkowskiCut.lean`: for a totally
real cubic field `F`, Koch's injection `H²(G,𝔽₃) ↪ 𝓒_∅` together with the *proved* Kummer
computation gives

`dim_{𝔽₃} H²(G,𝔽₃) ≤ dim_{𝔽₃} Cl_F[3] + 2`

(`Work.CFT.MinkowskiCut.finrank_H2Fp_le_classGroupRank_add_two_of_totallyReal_cubic`).  The
Golod–Šafarevič endgame applied to the maximal `T`-split everywhere-unramified `3`-extension
`K/F` needs only

`proPRelationRank 3 (Gal(K/F)) ≤ (dim Cl_F[3] + 2) + |T|`,

and the numerical condition `m² > 4 (M + |T|)` with `M = dim Cl_F[3] + 2` holds for the cyclotomic
cubic `F` and the split-prime set `T` of the construction, by Minkowski's class-number bound.

## What this file fixes

* `Work.Tower.MinkowskiGS.ClassGroupRelationBound` — the relation-rank bound at the finite maximal
  `T`-split level, with the class group in place of `dim H¹` (the exact input of the endgame).
* `Work.Tower.MinkowskiGS.KochInjectionInput` — Koch's fact (a) at the finite maximal `T`-split
  level, the arithmetic input of the whole area.
* `Work.Tower.MinkowskiGS.AbstractKochInput` — the `∃ G` form of fact (a) (a single abstract group
  per field, modelling the maximal everywhere-unramified pro-`3` group) together with the
  group-theoretic cutting data (`KochTransfer` and `SplittingCut`) that passes from `G` to its
  finite `T`-split quotients.

Everything is monomorphic in universe `0` (`F K : Type`), because `H1Fp`, `H2Fp`, `generatorRank`
and `SplittingCut` live in universe `0`.
-/

open NumberField
open scoped Classical nonZeroDivisors

noncomputable section

namespace Work
namespace Tower
namespace MinkowskiGS

/-- **The relation-rank bound at the finite maximal `T`-split level, from the class group.**

For a totally real cubic field `F` and an everywhere-unramified Galois `3`-extension `K/F` which is
maximal among those in which the primes of the finite set `T` split completely (with the primes of
`T` having trivial Frobenius class in the Frattini quotient),

`proPRelationRank 3 (Gal(K/F)) ≤ dim_{𝔽₃} Cl_F[3] + 2 + |T|`.

This is the exact hypothesis consumed by the Golod–Šafarevič endgame
(`Work.Tower.MinkowskiGS.unramified_tower_gs_classGroup`); it is derived from Koch's fact (a) alone
by `Work.Tower.MinkowskiGS.classGroupRelationBound_of_kochInjectionInput`. -/
def ClassGroupRelationBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    Module.finrank ℚ F = 3 →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K],
      Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
      ∀ (T : Finset (Ideal (𝓞 F))),
        Work.Tower.Shafarevich.IsFrobeniusTrivialInFrattini F T →
        Work.Tower.Shafarevich.IsMaximalSplittingExtension F K T →
        Work.Tower.Shafarevich.proPRelationRank 3 (Gal(K/F)) ≤
          Module.finrank (ZMod 3) (Work.CFT.Kummer.classGroupTorsion F 3) + 2 + T.card

/-- **Koch's fact (a) at the finite maximal `T`-split level.**

For a totally real cubic field `F` and an everywhere-unramified Galois `3`-extension `K/F` which is
maximal among those in which the primes of `T` split completely (a finite field extension, so
`Gal(K/F)` is a finite group and `H²(Gal(K/F), 𝔽₃)` is the honest finite group cohomology), the
Shafarevich map

`H²(Gal(K/F), 𝔽₃) ↪ 𝓒_∅ = Hom(V_∅/F^{×3}, 𝔽₃)`

is injective (Koch, *Galois theory of p-extensions*, Ch. 11; Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, Ch. X §10).  This is fact (a) with the prescribed splitting
conditions; because the Frobenius classes of the primes of `T` are Frattini, the Kummer group is
unchanged by the splitting condition (`𝓒_T = 𝓒_∅`).

This is the **single arithmetic input** of the re-architected tower: no class-group rank formula
(b′), i.e. no Artin reciprocity, is involved. -/
def KochInjectionInput : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    Module.finrank ℚ F = 3 →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K],
      Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
      ∀ (T : Finset (Ideal (𝓞 F))),
        Work.Tower.Shafarevich.IsFrobeniusTrivialInFrattini F T →
        Work.Tower.Shafarevich.IsMaximalSplittingExtension F K T →
        Work.CFT.ShafarevichCore.ShafarevichInjection F 3 (Gal(K/F))

/-- **The `∃ G` form of Koch's fact (a) together with the group-theoretic cutting data.**

For a totally real cubic field `F` there is an abstract group `G` modelling the maximal
everywhere-unramified pro-`3` group `Gal(F_∅(3)/F)` such that

* Koch's fact (a) holds for `G` (`ShafarevichInjection F 3 G`);
* Koch's transfer / pro-`3` presentation theorem holds for `G` (`KochTransfer 3 G`);
* the cutting at a splitting set `T` holds for `G` (`SplittingCut F G`):  every finite
  everywhere-unramified Galois `3`-extension `K/F` which is maximal for complete splitting of `T`
  is a quotient `G ⧸ N` by the normal closure of at most `|T|` elements, without changing the
  generator rank.

Only the first clause is *arithmetic*:  `KochTransfer` is a theorem of (pro-)group theory
(proved for finite `G` in `Work.CFT.KochTransfer.kochTransfer`), and `SplittingCut` is Galois
correspondence for the maximal pro-`3` group together with the Frattini/Frobenius facts.  Neither
involves a class-group rank formula.

WARNING.  The bare statement `∀ F, ∃ G, ShafarevichInjection F 3 G` is *trivially true* (take `G`
the trivial group, whose `H²` vanishes), so it says nothing; the `SplittingCut` clause is what
forces `G` to model the maximal group, and it is essential.  With it, this `Prop` is the same kind
of *abstract localization* as `Work.CFT.ShafarevichCore.ShafarevichCoreInput`: see
`Submission/Work/CFT/MaxProP/Defs.lean` for the caveat that the abstract group cohomology of the
honest (infinite) pro-`3` group does not have the required finiteness.  The honest, finite-level
form of the arithmetic input is `KochInjectionInput`, where the group is the honest finite
`Gal(K/F)`; that is the input the area's main theorem consumes. -/
def AbstractKochInput : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    Module.finrank ℚ F = 3 →
    ∃ (G : Type) (_ : Group G) (_ : Work.CFT.Kummer.KochTransfer 3 G),
      Work.CFT.ShafarevichCore.ShafarevichInjection F 3 G ∧
        Work.CFT.ShafarevichCore.SplittingCut F G

end MinkowskiGS
end Tower
end Work
