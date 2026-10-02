import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.hirz8_of_generators_thom
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.assembly
import Submission.Work.ThomBordism.smooth8Fundamental
import Submission.Work.ThomBordism.orientedWiring
import Submission.Work.Serre.serreE3b
import Submission.Work.ThomBordism.nonemptyGenuineTubeGeometryAtFamily
import Submission.Work.ThomBordism.orientationProducerWiring
import Submission.Work.ThomBordism.levelClassData_of_coord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! Guidance from the project lead (the requester):

AREA THOM. Prove `Work.Drive.ThomRational` (see Submission/Work/Drive/Interfaces.lean), ASSUMING the stable
stems are torsion (`Work.Drive.StableStemsTorsion`, proved by a sibling area). This is Thom's theorem
Ω^SO_8 ⊗ ℚ ≅ ℚ² detected by (p₁², p₂). YOU are the owner: design the chapter, delegate the pieces, and
check every child statement for vacuity and correctness (earlier runs lost weeks to interfaces carrying the
key facts as free data, and to refutable statements).

The classical proof, to be adapted:
(1) Weighted family → one closed oriented (possibly DISCONNECTED) 8-manifold V (disjoint unions, orientation
    reversal) whose numbers are the weighted sums; σ and the numbers are additive. Submission/Work/Bordism/
    has homology/cohomology/intersection-form of coproducts and sigma_disj.
(2) Pontryagin–Thom: embed V ⊂ ℝ^{8+k}, normal bundle ν, tubular neighbourhood, Gauss map to a finite
    oriented Grassmannian G = G̃r_k(ℝ^{k+m}), collapse S^{8+k} → Th(γ_k) =: T. Get α_V ∈ π_{8+k}(T).
(3) Rational Hurewicz in the stable range for T (via StableStemsTorsion + homotopy excision/Freudenthal +
    induction over a cell or open-cover filtration of T) and H^{8+k}(T;ℚ) ≅ H⁸(G;ℚ) = ℚ{p₁², p₂}. The
    Hurewicz pairings of α_V with p₁²U, p₂U are the NORMAL Pontryagin numbers, polynomials in the tangent
    ones. Conclude: vanishing numbers ⇒ N·α_V = 0 for some N ≥ 1.
(4) Transversality: a null-homotopy of N·α_V made transverse to the zero section yields a compact oriented
    9-manifold W with ∂W = N·V.
(5) Bordism invariance of σ: ∂W = N·V ⇒ σ(N·V) = 0.
Choose ONE model for manifolds with boundary/bordisms early, and state (2)-(5) against it.
-/

namespace Work.ThomBordism

/-! ## Status of the area (for the project lead and future sessions)

**What is proved here (sorry-free).**

* `thomRational_of_hirzebruch` — `Work.Drive.Hirz8 → Work.Drive.ThomRational` (pure algebra:
  multiply `45σ = 7p₂ − p₁²` by the weights and sum).
* `thomRational_of_numbersInSpan` — the same from the per-manifold span condition
  `Work.SignatureBordism.NumbersInSpan8` (equivalently `Hirz8`, by
  `Work.SignatureBordism.mem_span_iff_hirzebruchEight`).
* `thomRational_iff_hirz8_of_generators` — with the project's algebra bridge
  `Work.Drive.hirz8_of_generators_thom`, `ThomRational` and `Hirz8` are *equivalent* once the two
  generator manifolds (area GEN) are available.

**The remaining gap, exactly.**  `thomRational` needs `Work.Drive.Hirz8`, which is the
dimension-`8` Hirzebruch signature theorem with the *tangent* Pontryagin classes
`Work.Thom.p1Tangent'`/`p2Tangent'`; by the equivalence above this is not a weakening but *is* the
rational generation `Ω^SO_8 ⊗ ℚ = ℚ{[ℂP⁴], [ℂP² × ℂP²]}`.  The classical proof is the
Pontryagin–Thom construction plus

* a model of manifolds with boundary and of bordism carrying the numbers (step (5): `σ` of a
  boundary is `0`);
* transversality/Sard for maps `ℝ^a → ℝ^b`, `a > b`, and tubular neighbourhoods (steps (2),(4));
* the Thom space of the oriented Grassmannian and its rational cohomology `ℚ{p₁², p₂}`, together
  with the Thom isomorphism (step (3), cohomological half);
* the *rational Hurewicz theorem* in the stable range for that Thom space (step (3), homotopical
  half — the only place `Work.Drive.StableStemsTorsion` enters).

Mathlib has none of the analytical/homotopical items above (the project's `HANDOFF.md` says so
explicitly: "Mathlib has none of: ... bordism, transversality/Sard for m > n, tubular
neighbourhoods, Hurewicz, spectral sequences").  In this workspace's `⌞ClosedOriented⌟` model one
further obstruction shows up: the numbers of `Work.Drive.Smooth8` are *opaque* (`sigma` of a
general manifold is not known to be finite-dimensional, so even the additivity
`Work.Bordism.sigma_disj` over disjoint unions cannot be applied), so the weighted-family step (1)
cannot be done in the `Smooth8` model either.

Accordingly `thomRational` is the assertion that the *whole* missing Pontryagin–Thom chapter has
been built; `Work.ThomBordism.hirz8_smooth8` (a sibling prover) is the direct bottleneck.
-/

/-- **The dimension-`8` signature theorem implies the rational form `ThomRational`.**

Pure algebra: if every closed oriented smooth `8`-manifold `M` satisfies the dimension-`8` Hirzebruch
identity in the Drive vocabulary, `45 σ(M) = 7 p₂(M) − p₁(M)²`, then a weighted family with vanishing
weighted `p₁²`- and `p₂`-numbers has vanishing weighted signature.  Multiplying the `i`-th identity by
`w i` and summing gives `45 · Σ w σ = 7 · Σ w p₂ − Σ w p₁² = 0`, and `45 ≠ 0` in `ℤ`.

The content of `Work.Drive.Hirz8` (the dimension-`8` signature theorem with the tangent Pontryagin
classes) is *not* proved here; this lemma isolates the linear algebra. -/
theorem thomRational_of_hirzebruch (h : Work.Drive.Hirz8) : Work.Drive.ThomRational := by
  intro n M w h1 h2
  have key : ∀ i, 45 * (M i).sigma = 7 * (M i).p2Num - (M i).p1Sq := fun i => h (M i)
  have h45 : 45 * (∑ i, w i * (M i).sigma) = 0 := by
    calc 45 * (∑ i, w i * (M i).sigma)
        = ∑ i, w i * (45 * (M i).sigma) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = ∑ i, w i * (7 * (M i).p2Num - (M i).p1Sq) :=
            Finset.sum_congr rfl (fun i _ => by rw [key i])
      _ = ∑ i, (7 * (w i * (M i).p2Num) - w i * (M i).p1Sq) :=
            Finset.sum_congr rfl (fun i _ => by ring)
      _ = 7 * (∑ i, w i * (M i).p2Num) - ∑ i, w i * (M i).p1Sq := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = 0 := by rw [h2, h1]; ring
  exact (mul_eq_zero.mp h45).resolve_left (by norm_num)

/-- **`ThomRational` from the per-manifold span condition.**

If for every closed oriented smooth `8`-manifold `M` the number triple
`(σ(M), p₁²(M), p₂(M))` lies in the rational span of the two generator triples
`(1, 25, 10)` (`ℂP⁴`) and `(1, 18, 9)` (`ℂP² × ℂP²`) — i.e. `NumbersInSpan8` holds for the honest
data of `M` — then `ThomRational` holds.  This is the form in which the *generation* statement
`Ω^SO_8 ⊗ ℚ = ℚ{[ℂP⁴], [ℂP² × ℂP²]}` is consumed: by
`Work.SignatureBordism.mem_span_iff_hirzebruchEight`, `NumbersInSpan8` for the honest tangent data of
`M` is *equivalent* to the dimension-`8` Hirzebruch identity for `M`. -/
theorem thomRational_of_numbersInSpan
    (h : ∀ M : Work.Drive.Smooth8,
      Work.SignatureBordism.NumbersInSpan8 M.toCOS8.sset M.c M.toCOS8.p1 M.toCOS8.p2) :
    Work.Drive.ThomRational :=
  thomRational_of_hirzebruch fun M =>
    (Work.SignatureBordism.mem_span_iff_hirzebruchEight _ _ _).mp (h M)

/-- **`ThomRational` is exactly the project's crux, given two Hirzebruch generators.**

With the pure-algebra bridge `Work.Drive.hirz8_of_generators_thom` (Cramer's rule) and the
reduction `thomRational_of_hirzebruch` above, the two areas `Hirz8` and `ThomRational` are
*equivalent* once the two generator manifolds are available: each is `45σ = 7p₂ − p₁²` for every
closed oriented smooth `8`-manifold, on the one hand, and the rational generation
`Ω^SO_8 ⊗ ℚ = ℚ{[ℂP⁴], [ℂP² × ℂP²]}` on the other.  In particular, proving `ThomRational` is
*exactly* the dimension-`8` Hirzebruch signature theorem: no argument can prove it from a weaker
input than the generation of `Ω^SO_8 ⊗ ℚ`. -/
theorem thomRational_iff_hirz8_of_generators (hG : Work.Drive.Generators8) :
    Work.Drive.ThomRational ↔ Work.Drive.Hirz8 :=
  ⟨Work.Drive.hirz8_of_generators_thom hG, thomRational_of_hirzebruch⟩

/-! ## The state of the reduction

The target is now reduced **exactly** to the three inputs of `Work.ThomBordism.Interface`, by
`Work.ThomBordism.thomRational_of_transversalityCore` (`Submission/Work/ThomBordism/assembly.lean`):

1. `Work.ThomBordism.TransversalityCoreFamily` — the Pontryagin–Thom chapter: the Pontryagin numbers
   detect rational bordism (a finite family of closed oriented `8`-manifolds whose total `p₁²`- and
   `p₂`-numbers vanish has a positive multiple that bounds).  This is where the embedding, the
   tubular neighbourhood, the Thom space of the oriented Grassmannian, the Thom isomorphism and the
   Gysin sequences (`H^*(T;ℚ) ≅ ℚ{p₁², p₂}`), rational Hurewicz in the stable range (**the only
   place `Work.Drive.StableStemsTorsion` is used**) and transversality (`Sard`) enter.  The
   Pontryagin numbers are computed *on the manifolds themselves*: the Hurewicz pairings of the
   Pontryagin–Thom class are the **normal** numbers, identified with the tangent ones via
   `TV ⊕ ν ≅ ε` and the Whitney formula.
2. `Work.ThomBordism.BoundarySigma` — bordism invariance of the signature (Lefschetz duality for
   `(W, ∂W)`).
3. `Work.ThomBordism.Smooth8Fundamental` — for a `Work.Drive.Smooth8` with non-vanishing class, the
   class is a local generator (so the manifold is a `Man8`); the degenerate case `c = 0` (a closed
   non-orientable `8`-manifold has `H₈ = 0`) is handled inside the assembly, where all three numbers
   vanish.

The assembly is *arithmetic* over explicit finite sums plus `BoundarySigma` applied to the family
`Fin N × (Σ i, |w i| copies of the i-th manifold)`.  Consequently:

* no additivity of `σ` over a disjoint union is used, so **no finite-dimensionality of any
  cohomology** is needed (the obstruction of the earlier "weighted coproduct" interface, where
  `Work.Bordism.sigma_disj` needs `FiniteDimensional ℚ (H⁴(·;ℚ))`, is avoided entirely);
* no bordism invariance of the Pontryagin numbers is used — that statement, for a boundary whose
  identification is only a homeomorphism, would need *Novikov's* topological invariance of rational
  Pontryagin classes; the (dead) earlier route in `Interface.lean`
  (`Generation` + `BoundaryP1Sq`/`BoundaryP2Num`) is kept only for the record;
* no generator manifolds are needed: the theorem is proved directly for every closed oriented
  `8`-manifold from the two geometric inputs.  (Consequently `Work.Drive.Generators8` is not needed
  by this area; `Work.ThomBordism.thomRational_iff_hirz8_of_generators` below records that the
  target is nevertheless equivalent to the dimension-`8` signature theorem.)

The three delegated lemmas are `Work.ThomBordism.smooth8Fundamental`,
`Work.ThomBordism.boundarySigma` and `Work.ThomBordism.transversalityCoreFamily`.

## Status after the interface audit of 2026-09-25 (see `CRITICAL_PATH.md`)

* `Smooth8Fundamental` and `BoundarySigma` are **proved** and axiom-clean; `BoundarySigma` rests on
  the chart-based finite generation `Work.ThomBordism.homologyFiniteOfNullBordism`, with no collar
  theorem in its input list.
* The Pontryagin–Thom input is reduced, without the general collar neighbourhood theorem, to the
  three geometric obligations recorded in `Work.ThomBordism.endgame`
  (`thomRational_of_geometricInputs`): TUBULAR's tubular data, PTGEOMETRIC's collar realisation and
  rational Hurewicz in the stable range.  The former interface carried
  `hOrient : Work.Orient.RelativeFundamentalClassExists 8`, which is available only from the general
  collar theorem (not in the workspace) — the collar-based files
  `Submission/Work/ThomBordism/orientOfCollar.lean`, `genuineOrientationOfCollar.lean`,
  `collarRealisation.lean` and `paddedEndgame.lean` remove it.

* **The connectivity obligation is CLOSED** (this session).  GRASSMANN's
  `chartPieceConnected`/`thomSpaceConnectedAssembly` is no longer needed: the area's own
  `Submission/Work/ThomBordism/pieceConnectivity.lean`
  (`Work.ThomBordism.thomSpaceConnected_of_pieceConnectivity`, proved, axiom-clean) gives
  `Grassmann.ThomSpaceConnected k m` for all `k, m`, by the finite-cover Mayer–Vietoris assembly
  `connectivityAssembly.lean` from the piece connectivity `Work.ThomBordism.pieceConnectivity`
  (proved).  So `Work.ThomBordism.thomRational_of_tubular_collar_rat`
  (`paddedEndgame.lean`) reduces the target to **three** inputs: TUBULAR's tubular data,
  PTGEOMETRIC's collar realisation, rational Hurewicz.  See `CRITICAL_PATH.md` §8.
* `Work.ThomBordism.paddedEndgame.thomRational_of_paddedGrassmann` is the version of the reduction
  whose universal Thom target is `G̃r_k(ℝ^{k+m})` with `m ≥ 10`, which is what makes GRASSMANN's
  proved degree-`8` results (stated for `m ≥ 10`) applicable; the honest `m = 8` target of the
  original interface is not covered by that area's degree-`8` bound. -/

/-- **The reduction, stated in terms of the three inputs.**  (The local-generator input
`Work.ThomBordism.Smooth8Fundamental` is being closed by the chain
`localGenDefs`/`localGenAux`/`localGeneration` → `smooth8Fundamental`; once that chain is
`sorry`-free this becomes a two-input reduction.) -/
theorem thomRational_of_inputs
    (hT : Work.ThomBordism.TransversalityCoreFamily) (hσ : Work.ThomBordism.BoundarySigma) :
    Work.Drive.ThomRational :=
  Work.ThomBordism.thomRational_of_transversalityCore hT hσ Work.ThomBordism.smooth8Fundamental

/-- **The remaining geometric input of the target**, isolated as a *single* named statement (the
only `sorry` of this file, and the project's last geometric gap).

It is the input of area PTGEOMETRIC's `SourceWiring` deliverable: for every finite family of
*connected* closed oriented `8`-manifolds the genuine tube geometry of the family at a codimension
**chosen for that family** (`GenuineTubeGeometry` = the TUBULAR half
`Work.ThomBordism.nonempty_genuineTubeData_family_at` plus the coordinate half), and the orientation
datum of the collapse end (`Work.PTGeometric.OrientationProducer`).

The quantifier order is the honest one: the pieces' embeddings into `ℝ^{8+k}` come from Mathlib's
Whitney embedding theorem, whose dimension is unbounded (one codimension per manifold, padded up
only), so the codimension must be chosen *after* the family. -/
def geometryInput : Prop :=
  (∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∀ i, ConnectedSpace (F i).pt) →
      ∃ (k : ℕ) (_ : 11 ≤ k),
        Nonempty (Work.PTGeometric.GenuineTubeGeometry k
          (connTarget k (by omega) (PhiG k (by omega))) ι F)) ∧
    Work.PTGeometric.OrientationProducerConn

/-- **The genuine tube geometry of a connected family is produced** (area THOM's own
`Work.ThomBordism.nonemptyGenuineTubeGeometryAtFamily`, at a codimension chosen *after* the family by
`Work.ThomBordism.exists_embeddingData_ge_family_odd'`).  This is the first conjunct of
`geometryInput`.

**Status (session 9).**  This theorem is *proved*, but its proof currently rests on the one remaining
sorry of the geometry half, `Work.ThomBordism.gaussTubeData`
(`Submission/Work/ThomBordism/gaussTubeData.lean`): the identity of the Pontryagin–Thom collapse of
the tube with TUBULAR's concrete collapse `alphaV` *at the Gauss map*, including the pointwise
description of that Gauss map (the two normal data `tubeNormalProj`/`tubeNormalCoord`).  That
statement is the bridge from TUBULAR's abstract `nuPairingExistsOdd` (whose `J` is a
`Classical.choose`, hence opaque) to the coordinate fields of PTGEOMETRIC's `GenuineTubeGeometry`.
It is in flight (child H4-L2427); `#print axioms Work.ThomBordism.gaussTubeData` shows `sorryAx`
until it lands.  Everything else of the chain below `thomRational` is axiom-clean (verified in
`_tbchk/axchain.lean`). -/
theorem geometryProducer_holds :
    (∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∀ i, ConnectedSpace (F i).pt) →
      ∃ (k : ℕ) (_ : 11 ≤ k),
        Nonempty (Work.PTGeometric.GenuineTubeGeometry k
          (connTarget k (by omega) (PhiG k (by omega))) ι F)) :=
  fun ι _ F hconn => by
    obtain ⟨k, hk, hodd, hE⟩ := exists_embeddingData_ge_family_odd' F
    exact ⟨k, hk, nonemptyGenuineTubeGeometryAtFamily hk hodd F hconn hE⟩

/-- **The residual orientation input** (area PTGEOMETRIC's G5, `SourceWiring.lean`): the orientation
datum of the collapse end.  **PROVED** (session 32) from the two inputs of
`Work.ThomBordism.orientationProducer_of_spec`:

* `Work.ThomBordism.sourceLevelOrientationHyp` — the `hspec` (collar and orientation family of the
  level model of `Work.PTGeometric.producedRawData`), read off the third conjunct of
  `Work.PTGeometric.producedRawData_spec`, which the source construction now *carries* (the (M1) work:
  the coframing of the smoothed plane field + `orientationFamily_of_coframingDataBase`);
* `Work.ThomBordism.levelClassData_of_coord` — the `hglue` (`w_fund` bookkeeping from the recorded
  boundary coordination).

Its `sorryAx` is inherited from the construction's boundary coordination
(`Work.ThomBordism.SourceBoundaryCoord D0'` in
`Submission/Work/ThomBordism/sourceRawAmbientData_tied_collar.lean:1159`), the project's last
geometric gap.  See `Submission/Work/ThomBordism/NOTE_SESSION32.md`. -/
theorem orientationProducer_holds : Work.PTGeometric.OrientationProducer := by
  refine Work.ThomBordism.orientationProducer_of_spec ?_ ?_
  · intro k D ι _ Fam _ hk hne G m hm hpow
    exact Work.ThomBordism.sourceLevelOrientationHyp hk G m hm hpow
  · intro k D ι _ Fam _ hk G m hm hpow hset hWcl L hcolγ hcoord
    exact Work.ThomBordism.levelClassData_of_coord hk G m hm hpow hset hcolγ hcoord

/-- **The same producer in the connected-family form** (`Work.PTGeometric.OrientationProducerConn`),
which is the form the endgame consumes (`Work.ThomBordism.thomRational_of_serreE3bStrict_orientedFamConn`)
and the form in which the last mile is provable: connectedness of the pieces is what pins the branch
of the coorientation (`Submission/Work/ThomBordism/NOTE_SESSION64.md` sections 8-10).  It is
*weaker* than `orientationProducer_holds`, so nothing is lost.  Derived here from the unrestricted
producer; it is replaced by a direct proof once the construction uses the connectedness hypothesis. -/
theorem orientationProducer_holdsConn : Work.PTGeometric.OrientationProducerConn :=
  Work.PTGeometric.orientationProducerConn_of_orientationProducer orientationProducer_holds

/-- The remaining geometric input (the `sorry` of this file). -/
theorem geometryInput_holds : geometryInput :=
  ⟨geometryProducer_holds, orientationProducer_holdsConn⟩

/-- **Thom's theorem, rational form** (the target).

**Where the reduction stands (session 8, 2026-09-27).**  Obligation 2 is **closed**:
`Work.ThomBordism.tubeAssemblyInterface` (`Submission/Work/ThomBordism/tubeConnProved.lean`) and the
family form `Work.ThomBordism.tubeDataPerFamilyConn`, with the *named* per-member choice
`Work.ThomBordism.familyTubeRep` and its spec lemmas; the prescribed-codimension form is
`Work.ThomBordism.tubeDataPerFamilyConn_at` (`Submission/Work/ThomBordism/tubeAssemblyClosed.lean`).
The homotopy input is reduced to **one** statement that avoids area SERRE's cellular step entirely:

* `Work.ThomBordism.rangeModelWiring.lean` discharges
  `Work.RatHurewicz.TorsionHomotopyVanishing` (`Work.ThomBordism.torsionHomotopyVanishing`, from the
  proved `Work.RatHurewicz.ratVanishing_of_torsion_homotopy`) and proves
  `Work.ThomBordism.ratHurewiczStable3_of_reduction (hβ : Work.RatHurewicz.RangeModelReduction) :
  Work.Drive.RationalHurewiczStable3`;
* so the target follows from
  `Work.ThomBordism.thomRational_of_reduction_genuine (hβ) (hdata)` — where `hdata` is area
  PTGEOMETRIC's per-family genuine tube geometry together with their last mile — or from
  `Work.ThomBordism.thomRational_of_reduction_collar (hβ) (hcol)` (the collar-realisation form), or
  from the `SerreE3bStrict` twins `Work.ThomBordism.thomRational_of_serreE3bStrict_collarConn` /
  `..._concreteDataConn` in `Submission/Work/ThomBordism/tubeAssemblyClosed.lean` and
  `Submission/Work/ThomBordism/ptGeometricWiring.lean`.

Two *independent* routes now exist for each of the two remaining inputs: for the homotopy one,
`Work.RatHurewicz.RangeModelReduction` (delegated) on the one hand and `Work.StemsB.SerreE3bStrict`
(SERRE/STEMSB) on the other; for the geometry one, `GenuineTubeGeometry` plus PTGEOMETRIC's
`ConcreteLastMile`, or the collar-realisation datum.  Note (session 8) that
`Work.PTGeometric.grTarget (fun k => Work.ThomBordism.PhiG k _) k _` is *definitionally*
`Work.ThomBordism.connTarget k _ (Work.ThomBordism.PhiG k _)`, so a PTGEOMETRIC producer can match
the per-member choice used by `Work.ThomBordism.familyTubeRep`.

**The state before the session-8 update (probe round 16).**  There are now *five* proved wirings of the target,
all with the honest hypotheses, and the target closes with whichever producer lands first:

* `Work.ThomBordism.thomRational_of_serreE3b_connData` / `..._serreE3bStrict_connData`
  (`connFinalWiring.lean`, `strictFinalWiring.lean`) — the per-family interface of this area: a
  tubular datum `FamilyTubeData k (Th γ_k) ι F` *and* a collar realisation
  `CollarRealisationConn n k` for every family of connected closed oriented `8`-manifolds, with an
  odd `k ≥ 11` and a comparison map `Φ` chosen per family;
* `Work.ThomBordism.thomRational_of_serreE3bStrict_grassmannGeometry` /
  `..._concreteGeometry` / `..._concreteDataConn` (`ptGeometricWiring.lean`) — area PTGEOMETRIC's
  packaging: `GenuineTubeGeometry` at a codimension chosen per family (with the comparison map `Φ`
  free per family in the `..._grassmannGeometry` form) together with their last mile
  (`ConcreteLastMile` / `ConcreteLastMileSource`);
* `Work.ThomBordism.thomRational_of_serreE3bStrict_tubeData_collar`
  (`strictFinalWiring.lean`) — the unrestricted-codimension form, kept for the record.

**Update (probe round 16, end of session).**  Obligation 2 has since been split into its two halves in
`Submission/Work/ThomBordism/tubeGeometryData.lean`: the *geometric* half is proved
(`Work.ThomBordism.exists_tubeGeometry_family`, with the odd codimension supplied by
`Work.ThomBordism.exists_embeddingData_ge_family_odd`), and the remaining content is stated as the
predicate `Work.ThomBordism.NuPairingFamily` (equivalently as the per-embedding statement
`Work.ThomBordism.tubeThomRepOfEmbedding`).  The consequent endgames are
`Work.ThomBordism.tubeDataPerFamily_of_nuPairingFamily`,
`Work.ThomBordism.tubeDataPerFamily_of_embeddingAssembly` (both giving `tubeDataPerFamily` from the
corresponding pairing statement) and **`Work.ThomBordism.thomRational_of_serreE3bStrict_nuPairingCollar`**
(the target from the strict Gysin range + `NuPairingFamily` + the collar data).  The sign convention
that the assembly and PTGEOMETRIC's boundary sign must share is the named fibre reflection
`Work.ThomBordism.thomReflect` (`Submission/Work/ThomBordism/thomReflect.lean`).

The two *topological* inputs are the strict Gysin range `Work.StemsB.SerreE3bStrict` (area STEMSB;
`Work.StemsB.rh3_of_e3bStrict`, axiom-clean, converts it into `Work.Drive.RationalHurewiczStable3`,
the hedge against the doubtful degenerate range of `Work.Serre.SerreE3b`) or its full-range form
(`Work.Drive.rh3_of_e3b`).  In the older description below, the reduction is stated with
`thomRational_of_serreE3b_connData`:

* `Work.Serre.SerreE3b` (area SERRE) — the rational Hurewicz theorem in the stable range
  (`Work.Drive.rh3_of_e3b`, proved, converts it; the target's own hypothesis
  `Work.Drive.StableStemsTorsion` is *not* used, as the project lead confirmed);
* the tubular data `FamilyTubeData k (Th γ_k) ι F` for every finite family of *connected* closed
  oriented `8`-manifolds (area TUBULAR, via
  `Work.Tubular.exists_localDegree_at_collapseRelK8_of_connected`);
* a collar realisation `Work.ThomBordism.CollarRealisationConn n k` for the same family and target
  (area PTGEOMETRIC's last mile);

with one *odd* codimension `k ≥ 11` and one comparison map `Φ` per family (odd because the
normal-bundle orientability `Work.ThomBordism.orthFrameOrientation` needs `Odd k`).  The consumer is
`Work.ThomBordism.thomRational_of_transversalityCoreConn` (`connAssembly.lean`), on top of the proved
`BoundarySigma` and `Smooth8Fundamental`.  See `CRITICAL_PATH.md` §8.17–§8.18.2 and `HANDOFF.md`; the
older reduction below (`thomRational_of_inputs`) uses the *unrestricted* `TransversalityCoreFamily`,
whose data hypotheses the geometric producers cannot reach (they quantify over families with empty
members, which have no tube chart — §8.17). -/
theorem thomRational (hS : Work.Drive.StableStemsTorsion) : Work.Drive.ThomRational :=
  thomRational_of_serreE3bStrict_orientedFamConn
    (Work.StemsB.serreE3bStrict_of_serreE3b Work.Serre.serreE3b)
    geometryInput_holds.1 geometryInput_holds.2

end Work.ThomBordism
