import Submission.Work.PTGeometric.AmbientRealisation
import Submission.Work.PTGeometric.ConcreteCollapse
import Submission.Work.PTGeometric.GenuineTransversality
import Submission.Work.PTGeometric.Orientation
import Submission.Work.PTGeometric.LocalPreimage
import Submission.Work.PTGeometric.Consistency
import Submission.Work.ThomBordism.Grassmann.ThomTarget
import Submission.Work.ThomBordism.Grassmann.thomSpaceClassesDetect_of_lowDegree
import Submission.Work.ThomBordism.Grassmann.GoodCover.Main
import Submission.Work.ThomBordism.nonemptyFamily

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the assembly — `TransversalityCoreFamily` from the genuine geometric statement

This file is the **deliverable** of the subproject: the re-assembly of
`Work.ThomBordism.TransversalityCoreFamily` (the crux input of Thom's theorem) with the chapter's
input `TransversalityFamily k D` **replaced by the genuine statement** `GenuineTransversality k D`
(G6): the transversality input is now a statement about the class of the class of the *genuine*
Pontryagin–Thom collapse data of the family (TUBULAR's `TubeThomRep`, i.e. the collapse map of the
tubular neighbourhood followed by the Gauss map into `Th(γ_k)`), and not about an arbitrary loop in
`π_{8+k}(T)` with the right Hurewicz pairings.

## The chain

For a finite family `F : ι → Man8` with vanishing total `p₁²`- and `p₂`-numbers:

1. choose a codimension `k ≥ 11` and the Grassmann Thom target `D = Th(γ_k)` (GRASSMANN's
   `grassmannThomTarget`: the space `Th(γ_k)` of the tautological bundle over `G̃r_k(ℝ^{k+10})`, the
   connectivity `ThomSpaceConnected k 8` and the detection `ThomSpaceClassesDetect k 8`,
   i.e. `H^{k+8}(Th(γ_k);ℚ) = ℚ{p₁²U, p₂U}`);
2. the tubular data of the pieces (TUBULAR's `FamilyTubeData`, i.e. `TubeThomRep` for each member and
   each normal class) gives a Pontryagin–Thom representative of each member;
3. additivity (`exists_ptFamilyRep_of_parts`, the explicit form of `ptAdditivity`) gives a
   representative `ρ` of the disjoint union whose class is the *product* of the pieces' classes;
4. its Hurewicz pairings are the total normal numbers, which by the Whitney relation are the total
   *tangent* numbers `∑ p₁²` and `∑ p₂`, both zero by hypothesis; rational Hurewicz in the stable range
   (`Work.Drive.RationalHurewiczStable3`, applied in
   `PTFamilyRep.exists_pow_eq_one_of_numbers_zero_three`) makes a positive power of `ρ.α` trivial;
5. **the genuine geometric statement** (`GenuineTransversality`, G6) applied to the genuine collapse
   data turns that into a null-bordism of a positive multiple of the family.

Step 5 is the only geometric input; `genuineTransversality_of_realisation` derives it from the
geometric realisation (`GenuineRealisation`: the smooth transverse null-homotopy of the collapse map /
`GenuineNullBordismData`) plus the local preimage theorem and the orientation datum of the situation,
and `exists_nullBordismFamily_of_genuineData` performs that derivation.

## Main results

* `Work.PTGeometric.transversalityCoreFamily_of_genuine` — the assembly from G6
* `Work.PTGeometric.transversalityCoreFamily` — the deliverable, with the genuine collapse data
* `Work.PTGeometric.transversalityCoreFamily_of_genuineRealisation` — the same with the refined
  geometric realisation (the form used by the neighbouring areas)
* `Work.PTGeometric.transversalityCoreFamily_of_realisation` — the assembly from the geometric data
* `Work.PTGeometric.transversalityCoreFamily_of_familyData'` — the check that this subsumes the
  chapter's route (`TransversalityFamily` implies G6)
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology Topology.Homotopy unitInterval
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology
open Work.ThomBordism.PontryaginThom

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.Cohomology

/-- **The assembly of the crux from the genuine geometric statement.**

For every finite family of closed oriented `8`-manifolds, a codimension `k ≥ 11`, the Grassmann Thom
target `D = Th(γ_k)`, the tubular data of the members (TUBULAR) and the genuine transversality
statement G6 (`GenuineTransversality k D`: the null-homotopy of the `m`-fold genuine collapse map of
the family bounds a multiple of the family) imply `TransversalityCoreFamily` — the vanishing of the
total `p₁²`- and `p₂`-numbers implies that a positive multiple of the family bounds.

The rational Hurewicz theorem in the stable range (`Work.Drive.RationalHurewiczStable3`) is the only
non-geometric input beyond the definitions; additivity is proved (`exists_ptFamilyRep_of_parts`). -/
theorem transversalityCoreFamily_of_genuine
    (hdata : ∀ (ι : Type) [Fintype ι] (F : ι → Man8),
      ∃ k : ℕ, 11 ≤ k ∧ ∃ D : ThomTarget k,
        FamilyTubeData k D ι F ∧ GenuineTransversality k D)
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily := by
  intro ι _ F h1 h2
  obtain ⟨k, hk, D, hfam, hG⟩ := hdata ι F
  haveI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  -- the normal-bundle and genuine collapse data of the pieces
  let Nd : ∀ i, NormalBundlData (F i) := fun i => Classical.choice (NormalBundlData.nonempty (F i))
  let r : ∀ i, Work.Tubular.TubeThomRep k D (F i) (Nd i) :=
    fun i => Classical.choice (hfam i (Nd i))
  -- additivity: a representative of the disjoint union with the product of the pieces' classes
  obtain ⟨ρ, hρα⟩ := exists_ptFamilyRep_of_parts (fun i => ptRepOfTubeThomRep (r i))
  -- rational Hurewicz in the stable range: a positive power of the class is trivial
  obtain ⟨m, hm, hpow⟩ := ρ.exists_pow_eq_one_of_numbers_zero_three hk hrat h1 h2
  have hρ : ρ.α = ∏ i, tubeAlpha (r i) := by rw [hρα]; rfl
  have hpow' : (∏ i, tubeAlpha (r i)) ^ m = 1 := by rw [← hρ]; exact hpow
  -- the genuine geometric statement
  obtain ⟨N', hN', ⟨W⟩⟩ := hG ι F Nd r m hm hpow'
  exact ⟨N', hN', ⟨W⟩⟩

/-- **The assembly from the geometric realisation** (`GenuineRealisation`): the smooth transverse
null-homotopy of the genuine collapse map of the family, with the ends identified with the pieces and
with the orientation datum of the situation.

The local preimage theorem `LocalPreimageTheorem` and, through it, the orientation theory of the
transverse preimage are the inputs of the realisation; everything else is as above. -/
theorem transversalityCoreFamily_of_realisation
    (hpre : LocalPreimageTheorem)
    (hdata : ∀ (ι : Type) [Fintype ι] (F : ι → Man8),
      ∃ k : ℕ, 11 ≤ k ∧ ∃ n : ℕ, ∃ D : ThomTarget k,
        FamilyTubeData k D ι F ∧ Nonempty (GenuineRealisation n k D))
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily := by
  refine transversalityCoreFamily_of_genuine (fun ι _ F => ?_) hrat
  obtain ⟨k, hk, n, D, hfam, ⟨R⟩⟩ := hdata ι F
  exact ⟨k, hk, D, hfam, genuineTransversality_of_realisation hpre R⟩

/-- **The assembly from the G5-refined geometric realisation.**

As `transversalityCoreFamily_of_realisation`, but the realisation produces the *refined* genuine data:
the orientation family of the preimage and the sign of the boundary identity
(`GenuineNullBordismDataRefined`), instead of the whole orientation datum.  The orientation data are
then re-assembled by `genuinePullbackOrientationData_of_orientation`, whose ORIENT input is the named
hypothesis `Work.Orient.RelativeFundamentalClassExists 8` (the collar being produced by construction,
`GenuineNullBordismDataRefined.collar`), and whose remaining content is the sign computation
(TUBULAR's local degree plus the already proved cap-boundary formula). -/
theorem transversalityCoreFamily_of_refinedRealisation
    (hpre : LocalPreimageTheorem) (hOrient : Work.Orient.RelativeFundamentalClassExists 8)
    (hdata : ∀ (ι : Type) [Fintype ι] (F : ι → Man8),
      ∃ k : ℕ, 11 ≤ k ∧ ∃ n : ℕ, ∃ D : ThomTarget k,
        FamilyTubeData k D ι F ∧ Nonempty (GenuineRealisationRefined hOrient n k D))
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily := by
  refine transversalityCoreFamily_of_genuine (fun ι _ F => ?_) hrat
  obtain ⟨k, hk, n, D, hfam, ⟨R⟩⟩ := hdata ι F
  exact ⟨k, hk, D, hfam, genuineTransversality_of_realisationRefined hpre R⟩

/-- **The check that the genuine statement is the honest weakening of the chapter's input.**  The
assembly above, run with the chapter's `TransversalityFamily k D` converted into G6 by
`genuineTransversality_of_family`, recovers the chapter's own
`Work.ThomBordism.transversalityCoreFamily_of_familyData`.  (The genuine statement quantifies over the
genuine collapse data only, so it is a specialisation of the chapter's — which is what makes the
deliverable a *reduction* of the crux and not a restatement of it.) -/
theorem transversalityCoreFamily_of_familyData'
    (hdata : ∀ (ι : Type) [Fintype ι] (F : ι → Man8),
      ∃ k : ℕ, 11 ≤ k ∧ ∃ D : ThomTarget k,
        FamilyTubeData k D ι F ∧ TransversalityFamily k D)
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily :=
  transversalityCoreFamily_of_genuine
    (fun ι _ F => by
      obtain ⟨k, hk, D, hfam, hF⟩ := hdata ι F
      exact ⟨k, hk, D, hfam, genuineTransversality_of_family hF⟩) hrat

/-! ## The deliverable, with the GRASSMANN and TUBULAR data

`Work.ThomBordism.Grassmann.grassmannThomTarget k 8 hconn U Φ hdet` is the universal Thom space
`T = Th(γ_k)` of the tautological bundle over `G̃r_k(ℝ^{k+10})` with the two named classes
`p₁(γ)² ⌣ U`, `p₂(γ) ⌣ U`.  The two properties of `T` the argument consumes are
`ThomSpaceConnected k 8` (the `(k-1)`-connectedness) and `ThomSpaceClassesDetect k 8 U Φ` (the two
classes detect torsion in degree `k+8`, i.e. `H^{k+8}(T;ℚ) = ℚ{p₁²U, p₂U}`). -/

/-- **The deliverable of PTGEOMETRIC**.

From

* GRASSMANN's universal Thom target of `γ_k` for every `k ≥ 11`: the connectivity and the detection
  property of the two Thom classes (each an explicit named hypothesis, as neither is proved in the
  workspace);
* TUBULAR's tubular data for each member of each finite family (`FamilyTubeData`: the collapse map of
  the tubular neighbourhood followed by the Gauss map, with its two Hurewicz pairings);
* the geometric realisation of the genuine collapse map, **at the true dimension of the manifold
  part of the Thom space** — `GenuineRealisationRefined hOrient (k * 10 + k) k D`, i.e. `9k` for the
  total space of `γ_k` over `G̃r_k(ℝ^{k+10})` (dimension `10k` for the Grassmannian plus `k` for the
  fibre) — whose data are the smooth transverse null-homotopy of a multiple of the genuine collapse
  map, the end identification, the orientation family and the boundary sign; its dimension is *not*
  free: for `n < k` a core point would force a submersion `ℝⁿ → ℝᵏ`, so no such realisation exists;
* rational Hurewicz in the stable range (`Work.Drive.RationalHurewiczStable3`),

the crux input of Thom's theorem holds: a finite family of closed oriented `8`-manifolds with
vanishing total `p₁²`- and `p₂`-numbers has a positive multiple which bounds. -/
theorem transversalityCoreFamily_of_preimage
    (hpre : LocalPreimageTheorem)
    (hOrient : Work.Orient.RelativeFundamentalClassExists 8)
    (hconn : ∀ (k : ℕ), 11 ≤ k → Grassmann.ThomSpaceConnected k 10)
    (hU : ∀ (k : ℕ), Work.Thom.ThomClass (Grassmann.tautologicalBundle k 10) k)
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8))
    (hdet : ∀ (k : ℕ) (hk : 11 ≤ k), Grassmann.ThomSpaceClassesDetect k 10 (hU k) (hΦ k))
    (htub : ∀ (k : ℕ) (hk : 11 ≤ k) (ι : Type) [Fintype ι] (F : ι → Man8),
      FamilyTubeData k
        (Grassmann.grassmannThomTarget k 10 (hconn k hk) (hU k) (hΦ k) (hdet k hk)) ι F)
    (hgen : ∀ (k : ℕ) (hk : 11 ≤ k),
      Nonempty (GenuineRealisationRefined hOrient (k * 10 + k) k
        (Grassmann.grassmannThomTarget k 10 (hconn k hk) (hU k) (hΦ k) (hdet k hk))))
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily :=
  transversalityCoreFamily_of_refinedRealisation hpre hOrient
    (fun ι _ F => ⟨11, le_rfl, 11 * 10 + 11, _,
      htub 11 le_rfl ι F, hgen 11 le_rfl⟩) hrat

/-- **The deliverable from the refined geometric realisation**, with the local preimage theorem
*proved* (`Work.PTGeometric.localPreimageTheorem`, from
`Submission.Work.PTGeometric.localLevelPreimageTheorem`) rather than assumed.

The hypothesis `hgen` here is the *refined* geometric realisation, i.e. it quantifies over an
arbitrary `Work.Tubular.TubeThomRep` of each piece; the interface defect of that form (the loop of an
arbitrary representative need not be the collapse map of the tubular neighbourhood) is recorded in
`README.md` §14 and repaired in `ConcreteCollapse.lean` and
`transversalityCoreFamily_of_concreteGeometry` below, which replaces `hgen` by the genuine collapse
data.  This form is kept because it is the one used by the neighbouring areas
(`Work.ThomBordism.collarRealisation`, `Work.ThomBordism.paddedEndgame`). -/
theorem transversalityCoreFamily_of_genuineRealisation
    (hOrient : Work.Orient.RelativeFundamentalClassExists 8)
    (hconn : ∀ (k : ℕ), 11 ≤ k → Grassmann.ThomSpaceConnected k 10)
    (hU : ∀ (k : ℕ), Work.Thom.ThomClass (Grassmann.tautologicalBundle k 10) k)
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8))
    (hdet : ∀ (k : ℕ) (hk : 11 ≤ k), Grassmann.ThomSpaceClassesDetect k 10 (hU k) (hΦ k))
    (htub : ∀ (k : ℕ) (hk : 11 ≤ k) (ι : Type) [Fintype ι] (F : ι → Man8),
      FamilyTubeData k
        (Grassmann.grassmannThomTarget k 10 (hconn k hk) (hU k) (hΦ k) (hdet k hk)) ι F)
    (hgen : ∀ (k : ℕ) (hk : 11 ≤ k),
      Nonempty (GenuineRealisationRefined hOrient (k * 10 + k) k
        (Grassmann.grassmannThomTarget k 10 (hconn k hk) (hU k) (hΦ k) (hdet k hk))))
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily :=
  transversalityCoreFamily_of_preimage localPreimageTheorem hOrient hconn hU hΦ hdet htub hgen hrat

/-! ## The deliverable with the GRASSMANN inputs discharged

GRASSMANN has since proved the three properties of `Th(γ_k)` that the statement above takes as
`hconn`, `hU` and `hdet`:

* `Grassmann.thomSpaceConnected k m` — the `(k-1)`-connectedness, for **all** `k`, `m`;
* `Grassmann.hasTautologicalThomClass k m` — a Thom class of `γ_k`, for all `k`, `m`;
* `Grassmann.thomSpaceClassesDetect_of_lowDegree k m hk hm U Φ` — the detection of the two named
  classes in degree `k + 8`, for **any** `Φ` and all `k, m ≥ 10`.

So the deliverable can be stated with those three discharged, at the base `G̃r_k(ℝ^{k+10})`:
only ORIENT, the excision identification `Φ`, TUBULAR's tube data, the geometric realisation and
rational Hurewicz remain. -/

/-- **The deliverable of PTGEOMETRIC with the GRASSMANN inputs discharged.** -/
theorem transversalityCoreFamily_of_grassmann
    (hOrient : Work.Orient.RelativeFundamentalClassExists 8)
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8))
    (htub : ∀ (k : ℕ) (hk : 11 ≤ k) (ι : Type) [Fintype ι] (F : ι → Man8),
      FamilyTubeData k
        (Grassmann.grassmannThomTarget k 10 (Grassmann.thomSpaceConnected k 10)
          (Grassmann.hasTautologicalThomClass k 10).some (hΦ k)
          (Grassmann.thomSpaceClassesDetect_of_lowDegree k 10 (by omega) le_rfl
            (Grassmann.hasTautologicalThomClass k 10).some (hΦ k))) ι F)
    (hgen : ∀ (k : ℕ) (hk : 11 ≤ k),
      Nonempty (GenuineRealisationRefined hOrient (k * 10 + k) k
        (Grassmann.grassmannThomTarget k 10 (Grassmann.thomSpaceConnected k 10)
          (Grassmann.hasTautologicalThomClass k 10).some (hΦ k)
          (Grassmann.thomSpaceClassesDetect_of_lowDegree k 10 (by omega) le_rfl
            (Grassmann.hasTautologicalThomClass k 10).some (hΦ k)))))
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily :=
  transversalityCoreFamily_of_genuineRealisation hOrient (fun k _ => Grassmann.thomSpaceConnected k 10)
    (fun k => (Grassmann.hasTautologicalThomClass k 10).some) hΦ
    (fun k hk => Grassmann.thomSpaceClassesDetect_of_lowDegree k 10 (by omega) le_rfl
      (Grassmann.hasTautologicalThomClass k 10).some (hΦ k)) htub hgen hrat

/-- **The assembly from the ambient realisation.**

As `transversalityCoreFamily_of_realisation`, but the geometric realisation is the *ambient* one
(`Work.PTGeometric.AmbientRealisation`): the data of the null-homotopy of a positive multiple of the
genuine collapse map recorded in ambient coordinates, on a source on which it avoids the basepoint of
the Thom space, with the orientation datum of the situation.  This is the form in which the geometric
construction is actually carryable: a *globally* smooth map from the disk with holes into the manifold
part `X.E` of the Thom space does not exist for the genuine null-homotopy (see `LastMile.lean`), so the
realisation has to be stated on the regular neighbourhood of the preimage of the core, and in ambient
coordinates (`Work.PTGeometric.AmbientCollapseEnd`).  Everything between the ambient data and the
null-bordism is proved
(`Work.PTGeometric.localLevelData_of_ambientCollapseEnd`, `…exists_nullBordismFamily_of_levelData`,
`…exists_nullBordismFamily_of_ambientCollapseEnd`). -/
theorem transversalityCoreFamily_of_ambientRealisation
    (hdata : ∀ (ι : Type) [Fintype ι] (F : ι → Man8),
      ∃ k : ℕ, 11 ≤ k ∧ ∃ n : ℕ, ∃ D : ThomTarget k,
        FamilyTubeData k D ι F ∧ Nonempty (AmbientRealisation n k D))
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily := by
  refine transversalityCoreFamily_of_genuine (fun ι _ F => ?_) hrat
  obtain ⟨k, hk, n, D, hfam, ⟨R⟩⟩ := hdata ι F
  exact ⟨k, hk, D, hfam, genuineTransversality_of_ambientRealisation R⟩

/-! ## The deliverable with the geometric input in its honest form

`Work.PTGeometric.GenuineTransversality` (and hence the geometric realisations of the preceding
sections) quantifies over an arbitrary `Work.Tubular.TubeThomRep` of each piece — a loop with the
family's two Hurewicz pairings, *not* the Pontryagin–Thom collapse map of the tubular neighbourhood.
That is the interface defect of `README.md` §14: the last mile (make the null-homotopy of the collapse
class smooth and transverse to the zero section, and take the preimage) has no well-defined object to
work on when the loop is arbitrary.

`Submission/Work/PTGeometric/ConcreteCollapse.lean` repairs this: it names TUBULAR's concrete collapse
of each piece (`GenuineTubeGeometry.isGeom`: the loop of the Pontryagin–Thom representative *is*
`Work.Tubular.alphaV`, the collapse of the tube composed with the Gauss map), records TUBULAR's
zero-set theorem (`GenuineTubeGeometry.zero`: the collapse vanishes exactly on the embedded piece),
and states the last mile for that genuine class (`ConcreteLastMile`), together with its split form
`ConcreteLastMileSource` — the source construction of the ambient collapse-end data plus the
orientation datum, from which the last mile follows by the proved endgame
(`concreteLastMile_of_source`, `exists_nullBordismFamily_of_ambientCollapseEnd`).

The deliverable below is therefore stated with the genuine collapse data as its geometric input: the
class equation `(∏ i, tubeAlpha (G.rep i))^m = 1` is an equation about the collapse maps of the
tubular neighbourhoods of the pieces. -/

/-- The universal Thom target `Th(γ_k)` of `G̃r_k(ℝ^{k+10})` with the GRASSMANN inputs (connectivity,
Thom class, detection of `p₁²U` and `p₂U`) discharged. -/
noncomputable abbrev grTarget
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8)) (k : ℕ) (hk : 10 ≤ k) : ThomTarget k :=
  Grassmann.grassmannThomTarget k 10 (Grassmann.thomSpaceConnected k 10)
    (Grassmann.hasTautologicalThomClass k 10).some (hΦ k)
    (Grassmann.thomSpaceClassesDetect_of_lowDegree k 10 hk le_rfl
      (Grassmann.hasTautologicalThomClass k 10).some (hΦ k))

/-- **The deliverable of PTGEOMETRIC, with the genuine collapse data as the geometric input, in the
nonempty-family form.**

For every finite family of closed oriented `8`-manifolds: the genuine collapse data of the family in
`Th(γ_k)` for some `k ≥ 11` (`GenuineTubeGeometry`: TUBULAR's tubular neighbourhoods of the pieces,
their Gauss maps into `Th(γ_k)` with the zero-set property, and the identification of the
Pontryagin–Thom representatives' loops with TUBULAR's concrete collapse maps), and the last mile for
it (`ConcreteLastMile`: the null-homotopy of the genuine collapse class bounds a positive multiple of
the family), together with the excision identification `Φ` and rational Hurewicz in the stable range,
give the nonempty-family form `Work.ThomBordism.TransversalityCoreFamilyNE` of
`Work.ThomBordism.TransversalityCoreFamily`.

This is the honest form of the deliverable: unlike `transversalityCoreFamily_of_genuineRealisation`,
whose geometric input quantifies over an arbitrary loop with the family's pairings, the class whose
power is trivialised here is the class of the genuine collapse of the family.

The geometric input `hgeo` asks for the genuine collapse data and the last mile of a family **all of
whose members are nonempty**: that is the honest form, since a `GenuineTubeGeometry` of an empty piece
does not exist (`TubeChart.inv` is total) while `Man8` allows the empty manifold.  The consumer recovers
the unrestricted statement by dropping the empty members
(`Work.ThomBordism.transversalityCoreFamily_of_nonempty`, used by
`transversalityCoreFamily_of_concreteGeometry` below). -/
theorem transversalityCoreFamilyNE_of_concreteGeometry
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8))
    (hgeo : ∀ (k : ℕ) (hk : 11 ≤ k) (ι : Type) [Fintype ι] (F : ι → Man8),
      (∀ i, Nonempty (F i).pt) →
      Nonempty (GenuineTubeGeometry k (grTarget hΦ k (by omega)) ι F) ∧
        ConcreteLastMile k (grTarget hΦ k (by omega)))
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamilyNE :=
  transversalityCoreFamilyNE_of_concreteDataNE
    (fun ι _ F hne => ⟨11, le_rfl, grTarget hΦ 11 (by omega), hgeo 11 le_rfl ι F hne⟩) hrat

/-- **The deliverable of PTGEOMETRIC, with the genuine collapse data as the geometric input.**

The unrestricted (all families) form of `transversalityCoreFamilyNE_of_concreteGeometry`: the empty
members of a family are dropped on the consumer's side. -/
theorem transversalityCoreFamily_of_concreteGeometry
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8))
    (hgeo : ∀ (k : ℕ) (hk : 11 ≤ k) (ι : Type) [Fintype ι] (F : ι → Man8),
      (∀ i, Nonempty (F i).pt) →
      Nonempty (GenuineTubeGeometry k (grTarget hΦ k (by omega)) ι F) ∧
        ConcreteLastMile k (grTarget hΦ k (by omega)))
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily :=
  Work.ThomBordism.transversalityCoreFamily_of_nonempty
    (transversalityCoreFamilyNE_of_concreteGeometry hΦ hgeo hrat)

/-- **The deliverable of PTGEOMETRIC, from the source construction alone.**

As `transversalityCoreFamily_of_concreteGeometry`, but the geometric input is split: the genuine
collapse data of the family (`GenuineTubeGeometry`) together with `ConcreteLastMileSource` — the
existence of the **ambient collapse-end data** of the null-homotopy of the genuine collapse class on a
positive multiple of the family, and of the **orientation datum** of the situation (ORIENT's relative
fundamental class through TUBULAR's local degree).  Everything between the source construction and
`TransversalityCoreFamily` is proved in this directory
(`Work.PTGeometric.concreteLastMile_of_source`, `Work.PTGeometric.exists_nullBordismFamily_of_ambientCollapseEnd`,
`Work.PTGeometric.transversalityCoreFamily_of_concreteData`); `README.md` §17 records what the source
construction itself requires. -/
theorem transversalityCoreFamilyNE_of_sourceConstruction
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8))
    (hsrc : ∀ (k : ℕ) (hk : 11 ≤ k) (ι : Type) [Fintype ι] (F : ι → Man8),
      (∀ i, Nonempty (F i).pt) →
      Nonempty (GenuineTubeGeometry k (grTarget hΦ k (by omega)) ι F) ∧
        ConcreteLastMileSource k (grTarget hΦ k (by omega)))
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamilyNE :=
  transversalityCoreFamilyNE_of_concreteGeometry hΦ
    (fun k hk ι _ F hne =>
      ⟨(hsrc k hk ι F hne).1, concreteLastMile_of_source (hsrc k hk ι F hne).2⟩) hrat

/-- **The deliverable of PTGEOMETRIC, from the source construction alone** (unrestricted form). -/
theorem transversalityCoreFamily_of_sourceConstruction
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8))
    (hsrc : ∀ (k : ℕ) (hk : 11 ≤ k) (ι : Type) [Fintype ι] (F : ι → Man8),
      (∀ i, Nonempty (F i).pt) →
      Nonempty (GenuineTubeGeometry k (grTarget hΦ k (by omega)) ι F) ∧
        ConcreteLastMileSource k (grTarget hΦ k (by omega)))
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily :=
  Work.ThomBordism.transversalityCoreFamily_of_nonempty
    (transversalityCoreFamilyNE_of_sourceConstruction hΦ hsrc hrat)

/-- **The deliverable of PTGEOMETRIC** (the genuine-collapse form of
`transversalityCoreFamily_of_concreteGeometry`).

The geometric input `hgeo` is the last mile in the honest form of `ConcreteCollapse.lean`: the
genuine collapse data of the family (TUBULAR's tubular neighbourhoods, Gauss maps and collapse maps,
with the zero-set property) and the statement `ConcreteLastMile` that the null-homotopy of the
genuine collapse class bounds a positive multiple of the family.  The state of `ConcreteLastMile`
(the analysis of the source construction, the obstructions, and the pieces that are proved) is
recorded in `README.md` §§17–22 and in `NOTE_TO_LEAD.md`: everything *below* it
(`concreteLastMile_of_source`, the preimage theorem, the perturbation, the endgame) is proved, and the
source construction itself is reduced to the gathering of the pieces proved in §§21–22 (the
collapse-end ambient data `tube_ambient_data`, the explicit concatenation of the pieces' collapse
loops and the source homotopy `exists_sourceHomotopy_of_family`). -/
theorem transversalityCoreFamily
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8))
    (hgeo : ∀ (k : ℕ) (hk : 11 ≤ k) (ι : Type) [Fintype ι] (F : ι → Man8),
      (∀ i, Nonempty (F i).pt) →
      Nonempty (GenuineTubeGeometry k (grTarget hΦ k (by omega)) ι F) ∧
        ConcreteLastMile k (grTarget hΦ k (by omega)))
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily :=
  transversalityCoreFamily_of_concreteGeometry hΦ hgeo hrat

theorem transversalityCoreFamilyConn_of_concreteGeometry
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8))
    (hgeo : ∀ (k : ℕ) (hk : 11 ≤ k) (ι : Type) [Fintype ι] (F : ι → Man8),
      (∀ i, ConnectedSpace (F i).pt) →
      Nonempty (GenuineTubeGeometry k (grTarget hΦ k (by omega)) ι F) ∧
        ConcreteLastMile k (grTarget hΦ k (by omega)))
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamilyConn :=
  transversalityCoreFamilyConn_of_concreteDataConn
    (fun ι _ F hconn => ⟨11, le_rfl, grTarget hΦ 11 (by omega), hgeo 11 le_rfl ι F hconn⟩) hrat

theorem transversalityCoreFamilyConn_of_sourceConstruction
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8))
    (hsrc : ∀ (k : ℕ) (hk : 11 ≤ k) (ι : Type) [Fintype ι] (F : ι → Man8),
      (∀ i, ConnectedSpace (F i).pt) →
      Nonempty (GenuineTubeGeometry k (grTarget hΦ k (by omega)) ι F) ∧
        ConcreteLastMileSource k (grTarget hΦ k (by omega)))
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamilyConn :=
  transversalityCoreFamilyConn_of_concreteGeometry hΦ
    (fun k hk ι _ F hconn =>
      ⟨(hsrc k hk ι F hconn).1, concreteLastMile_of_source (hsrc k hk ι F hconn).2⟩) hrat

/-- **The deliverable of PTGEOMETRIC, in the connected-family form** — the shape the consumer
`Work.ThomBordism.thomRational_of_transversalityCoreConn` asks for.  The geometric input carries the
connectivity of the family members (needed by the producers of the tubular data and of the local
degree); `(∀ i, ConnectedSpace (F i).pt)` gives `(∀ i, Nonempty (F i).pt)`, so this shape is implied
by `Work.PTGeometric.transversalityCoreFamilyNE_of_concreteGeometry`. -/
theorem transversalityCoreFamilyConn
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8))
    (hgeo : ∀ (k : ℕ) (hk : 11 ≤ k) (ι : Type) [Fintype ι] (F : ι → Man8),
      (∀ i, ConnectedSpace (F i).pt) →
      Nonempty (GenuineTubeGeometry k (grTarget hΦ k (by omega)) ι F) ∧
        ConcreteLastMile k (grTarget hΦ k (by omega)))
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamilyConn :=
  transversalityCoreFamilyConn_of_concreteGeometry hΦ hgeo hrat

end

end Work.PTGeometric
