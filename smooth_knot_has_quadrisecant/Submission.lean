import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap
import Submission.QuadrisecantCircle
import Submission.ChordMap
import Submission.SecantSpace
import Submission.Pi1Mobius
import Submission.ChordModel
import Submission.MobiusModel
import Submission.CirclePairs
import Submission.MobiusHomotopy
import Submission.ChordParam
import Submission.ChordModelHomeo
import Submission.SecantModel
import Submission.OpenMobiusHomotopy
import Submission.Pi1OpenMobius
import Submission.EmbeddedCircleWinding
import Submission.QuadrisecantChord
import Submission.ChordCoefficient
import Submission.TrappedWinding
import Submission.TrisecantLocus
import Submission.TrisecantClosed
import Submission.QuadrisecantLimit
import Submission.TrisecantStructure
import Submission.ParameterWinding
import Submission.TrisecantCover
import Submission.SecantDisk
import Submission.SquareDisk
import Submission.ChordFamily
import Submission.BandDisk
import Submission.BandArcCover
import Submission.RadialArc
import Submission.OPrime
import Submission.CollinearityMap
import Submission.Transversality
import Submission.TrisecantCurve
import Submission.LocalCurve
import Submission.TorusCollinearity
import Submission.TorusCharts
import Submission.TorusChartGraph
import Submission.TorusGraphInstances
import Submission.TorusChartLift
import Submission.TorusAtlas
import Submission.TorusChartHomeo
import Submission.Torus1Chart
import Submission.TorusPathFollow
import Submission.ZeroSetPath
import Submission.CompactCover
import Submission.CoverRefine
import Submission.GridPartition
import Submission.AdaptedChain
import Submission.ZeroSetTopology
import Submission.StrictZero
import Submission.TrisecantTransverse
import Submission.EndpointEscape
import Submission.ClassSection
import Submission.SheetAssembly
import Submission.MiddleConvergence
import Submission.OpenMapAssembly
import Submission.OpenMapPackaging
import Submission.OLocalStructure
import Submission.ComponentPath
import Submission.ComponentLoop
import Submission.OSubChart
import Submission.OChartChain
import Submission.OChartOrder
import Submission.OChartMonotone
import Submission.OChartGlue
import Submission.OChartAssembly
import Submission.OChartAssemblyMonotone
import Submission.OChartChainJunction
import Submission.OChartComponent
import Submission.OChartExhaustion
import Submission.ChartTracePath
import Submission.ComponentWalk
import Submission.OChartFiniteGluing
import Submission.OChartTwoStep
import Submission.ChainTransport
import Submission.ConnectedWalk
import Submission.IntervalChartU
import Submission.IntervalChainU
import Submission.IntervalCoverU
import Submission.ChainAlignment
import Submission.WalkAlignment
import Submission.AlignedFamily
import Submission.AlignedCover
import Submission.PrefixArcChart
import Submission.NestedFamily
import Submission.WalkPartialUnion
import Submission.OneManifold
import Submission.RealIntervalShape
import Submission.ChainUnionInterval
import Submission.ChainUnionOrderedInitialSegment
import Submission.TerminalAttachment
import Submission.T1Abstract
import Submission.OneSidedAttach
import Submission.EndStripGlue
import Submission.ArcRestrict
import Submission.NoOscillation
import Submission.AmbientTwoArc
import Submission.FacingNormalization
import Submission.IntervalHomeoEnds
import Submission.TwoArcUnion
import Submission.OverlapConn
import Submission.OverlapHconn
import Submission.LevelZeroHconn
import Submission.IntervalSide
import Submission.ChartRefine
import Submission.CellWalk
import Submission.ComponentIntervalSide
import Submission.FirstPrefixChart
import Submission.TraceOverlap
import Submission.OverlapOrder
import Submission.SweepAligned
import Submission.NestedDatum
import Submission.PerLengthCell
import Submission.PrefixCoord
import Submission.JunctionOrder
import Submission.TwoChartGlue
import Submission.ComponentChart
import Submission.ComponentMiddle
import Submission.ComponentWindingData
import Submission.ComponentNullHomotopy
import Submission.AnalyticUnknot
import Submission.StripCrosscut
import Submission.Work.Drive.quadrisecant_of_genericCase_approx

open LeanEval.KnotTheory.Quadrisecant

/-!
# Pannwitz–Kuperberg: `smooth_knot_has_quadrisecant`

**Statement.** Every smooth knot `r` which is *not unknotted* (i.e. admits no
smooth isotopy through knots to the round circle `standardCircle`) has a
quadrisecant: four distinct parameter values in one period whose images are
collinear (`HasQuadrisecant r`).

**IMPORTANT — `ContDiff ℝ ⊤` here is ANALYTIC (`ω`), not smooth (`∞`).**
In this Mathlib `ContDiff 𝕜 n` takes `n : WithTop ℕ∞` and the scoped
notations are `∞ = ↑(⊤ : ℕ∞)` (smooth) and `ω = ⊤ : WithTop ℕ∞`
(analytic), with `contDiff_omega_iff_analyticOnNhd : ContDiff 𝕜 ω f ↔
AnalyticOnNhd 𝕜 f univ`.  `ChallengeDeps` writes `ContDiff ℝ ⊤ r`, i.e.
`ω`: so `IsSmoothKnot r` means `r` is *analytic* and `IsUnknotted r`
demands an *analytic* isotopy.  Nothing in `Submission/` uses a
smooth-but-not-analytic function, so the tree is unaffected; but any future
construction of an isotopy/knot must be analytic (no smooth cutoff /
`Real.smoothTransition` gluing — an analytic function constant on an open
interval is constant).  See ROADMAP S283b.

**Proof architecture** (Kuperberg, *Quadrisecants of knots and links*,
J. Knot Theory Ramif. 3 (1994); see also Denne's PhD thesis,
arXiv:math/0510561).  Contrapositive: assume `r` has *no* quadrisecant and
build an isotopy to `standardCircle`.

1. Secant space. The space of unordered pairs of distinct points of the knot
   is an open Möbius strip `M`. A pair is in the subset `O ⊆ M` when some
   third point of the knot lies on its chord. Generically `O` is the image of
   a smooth immersion of a 1-manifold; its double points are quadrisecants.
2. Obstruction lemma. If a *non-separating* properly embedded arc `A` of `M`
   avoids `O`, then the chords over `A` form a map of a disk whose boundary is
   the knot and whose interior misses the knot; a smoothing + Dehn-lemma /
   Alexander-trick argument turns this into an isotopy through knots to the
   standard circle, i.e. `IsUnknotted r`.
3. No quadrisecants ⇒ `O` is embedded. If `O` blocked every non-separating arc
   it would be trivial (step 2), so (elementary homology of the Möbius strip)
   `O` has a circular component winding once or twice around `M`.  Following
   the middle point of the trisecants on such a loop: a single winding forces
   a jump discontinuity, a double winding forces *every* point of the compact
   knot to lie strictly between two others — contradicting that a compact set
   has a point of maximal distance to a fixed centre. Hence `O` must have a
   double point, i.e. a quadrisecant. ∎

**Verified foundations built so far** (all files under `Submission/`, no
axioms, no `sorry`):

* `Helpers.lean` — the trusted-definition API: period facts, smooth-knot
  consequences (continuity, injectivity on the period, periodicity of the
  velocity), compactness of the knot image, the extremal-point lemma
  `exists_point_not_strictly_between` (backed by two commons lemmas of
  `Submission.Commons.Analysis`), and the full round-circle bundle
  (`standardCircle_isSmoothKnot`, `standardCircle_isUnknotted`).
* `KnotMap.lean` — Layer A1/A2: the parameter circle of a smooth knot.
  `knotMap r : AddCircle period → Space` is the canonical factorization of
  the `period`-periodic map `r` through the circle of parameters; it is
  continuous (`IsSmoothKnot.knotMap_continuous`), injective
  (`knotMap_injective`), has range exactly the knot image over one period
  (`knotMap_range`), and is a homeomorphism of the compact circle onto that
  image (`knotMap_homeo`).  Chords/trisecants will be parametrized by this
  circle.
* `QuadrisecantCircle.lean` — the target statement on the circle: distinct
  parameters in `[0, period)` with collinear images are the same as four
  distinct points of `AddCircle period` with collinear `knotMap` images
  (`hasQuadrisecant_iff_circle`), with all the `QuadDistinct`/`List.Nodup`
  bookkeeping.
* `ChordMap.lean` — Layer A3: `OrderedPairs` (ordered pairs of distinct
  parameters on the circle) and the secant-direction map
  `secantDir : OrderedPairs → Space`, a continuous unit-vector field
  (`continuous_secantDir`, `norm_secantDir`) that is odd under endpoint swap
  (`secantDir_swap`).  This is the analytic atom (Kuperberg's `π_L`) for the
  structure theory of the trisecant locus.
* `SecantSpace.lean` — Layer A3 (the Möbius band of secants).  The swap
  involution `pairFlip` on the parameter square, the swap-orbit setoid
  `pairSetoid` and the quotient `UnordCirclePairs = (S¹×S¹)/swap`
  (Kuperberg's `M`), which is compact; the boundary circle `diagClass` of
  degenerate secants and the full class API (`class_eq_iff`,
  `classOf_pairFlip`, `classOf_eq_diag_iff`, `class_eq_of_offdiag`,
  `exists_eq_diag_or_ordered`).  Double cover of the open part: `OpenMobius`
  (the interior, i.e. secants with distinct endpoints),
  `unordOfOrdered : OrderedPairs → UnordCirclePairs` and
  `mobiusCover : OrderedPairs → OpenMobius` (continuous, surjective, fibres
  exactly `{p, swapOrdered p}` — `mobiusCover_fiber`).  Descent machinery
  `liftSwapInvariant` / `continuous_liftSwapInvariant` for
  `pairFlip`-invariant continuous maps, applied to the chord midpoint
  `unordMidpoint : M → Space` and chord length `unordChordLength : M → ℝ`
  (both continuous), restricted to the open band as `mobiusMidpoint`,
  `mobiusChordLength`.  (`secantDir` is *odd* under the flip
  (`secantDir_swap`), so it descends only to projective directions; the
  invariant midpoint/length functions are the objects descended here.)
  Hausdorffness: the swap-quotient map is an open quotient map
  (`isOpenQuotientMap_unordClass`) with closed kernel
  (`isClosed_unordClass_kernel`), giving the instance
  `T2Space UnordCirclePairs`; `T2Space OpenMobius` and
  `CompactSpace UnordCirclePairs` follow.  The double-cover certificate
  (`IsCoveringMap mobiusCover`) is the next step (route mapped in
  `ROADMAP.md`).
  The `ZMod 2`-swap action on `OrderedPairs` (`vaddSwap`, `AddAction`/
  `ContinuousConstVAdd`/`ProperlyDiscontinuousVAdd` instances,
  `LocallyCompactSpace OrderedPairs`) is set up with its orbit
  characterisation (`mobiusCover_eq_iff_orbit`), freeness (`stabilizer_eq_bot`,
  `free_part_eq_univ`) — the hypotheses of
  `Topology.IsQuotientMap.isCoveringMapOn_of_properlyDiscontinuousVAdd`.
  **The certificate is done**: `mobiusCover` is an open map
  (`isOpenMap_mobiusCover`) and hence a quotient map
  (`isQuotientMap_mobiusCover`), so the group-action covering theorem
  applies and yields **`isCoveringMap_mobiusCover : IsCoveringMap mobiusCover`**
  — the open Möbius band is a genuine two-sheeted covering of the ordered
  pairs of distinct parameters (ready for the π₁(M) = ℤ computation via
  covering-space theory).

* `Pi1Mobius.lean` — Layer C (π₁ of the open Möbius band): the target
  `π₁(OpenMobius) ≅ ℤ` is specified and decomposed.  Proved: half-period
  facts, the core circle `core : AddCircle period → OpenMobius` of antipodal
  pairs (`core_eq_iff`: points coincide iff parameters differ by the half
  period), and **the factorisation through the half-period circle**:
  `periodToHalfPeriod : AddCircle period → AddCircle halfPeriod`
  (surjective), `coreFactor : AddCircle halfPeriod → OpenMobius` with
  `core = coreFactor ∘ periodToHalfPeriod` (`core_factorizes`),
  `coreFactor_injective`, `continuous_coreFactor`,
  `coreFactor_range_eq_core_range` and the embedding certificate
  `coreFactor_homeo : AddCircle halfPeriod ≃ₜ Set.range coreFactor` — the
  core is a compact circle, literally `AddCircle halfPeriod` inside
  `OpenMobius`.  Next: construct the retraction (target `OpenMobiusCoreRetract` formulated, decomposition recorded: chord-slide formula, quotient well-definedness/continuity, homotopy fixing the core), then the `π₁(S¹) = ℤ` sub-project (Mathlib gap), assembly.
  `π₁(S¹) = ℤ` sub-project (Mathlib gap), assembly.

  **S263 (appended, VERIFIED sorry-free) — π₁(S¹) ≅ ℤ for the parameter
  circle (route step 4 DONE)**: with Mathlib's quotient-covering machinery
  (`Topology/Covering/Quotient.lean`, `Topology/Covering/AddCircle.lean`,
  `Topology/Homotopy/Lifting.lean` — Junyan Xu), the missing engine of the
  layer is now in place: `zmultiplesHom` (+ injective/surjective) and
  `zmultiplesEquivInt` (the deck group of `ℝ → AddCircle p` is infinite
  cyclic: `zmultiples p ≃+ ℤ` for `p ≠ 0`), `mulOppositeIntEquiv`, and
  **`fundamentalGroupAddCircle_isoZ`**: `FundamentalGroup (AddCircle p) 0
  ≃* Multiplicative ℤ` — `(AddCircle.isAddQuotientCoveringMap_coe
  p).fundamentalGroupEquiv ⟨0, rfl⟩` (injective by `SimplyConnectedSpace
  ℝ` — lift uniqueness; surjective by `PathConnectedSpace ℝ` — the
  standard loops) followed by the deck-group identification.  The three
  ingredient facts (degree = lift endpoint difference, homotopy
  invariance, surjectivity/injectivity) are documented as the next
  explicit-API step.  ROADMAP S263.
  **S264 (appended, VERIFIED sorry-free) — the degree of a loop as the
  lift endpoint difference over ℝ (the winding route's first ingredient
  lemma)**: `coeffOfZmultiples` (+ `coeffOfZmultiples_spec`, the integer
  coefficient of a period-lattice element),
  `lift_endpoint_diff_mem_zmultiples` (a real lift Γ of a loop has
  `Γ 1 − Γ 0 ∈ zmultiples p` — circle-level equality + `AddCircle.coe_sub`
  + `coe_eq_zero_iff`), **`loopDegree`** (+ `loopDegree_spec`: for a loop
  γ with real lift Γ, `Γ 1 − Γ 0 = (loopDegree hp Γ hΓlifts : ℝ) * p` —
  the geometric meaning of the integer in π₁ ≅ ℤ: one circuit advances the
  lift by one period), and `exists_lift_of_loop` (every loop lifts over ℝ,
  so the degree is defined on all loops).  ROADMAP S264.
  **S265 (appended, VERIFIED sorry-free) — homotopy invariance of the
  degree (the winding route's hinge)**: `lift_endpoint_diff_independent`
  (two real lifts of the same loop have equal endpoint differences: their
  difference is a continuous map into the discrete `zmultiples p`,
  constant on the connected interval) and **`loopDegree_eq_of_homotopic`**
  (loops homotopic rel endpoints have equal `loopDegree` for any lifts —
  canonical lifts from a common base via `cov.liftPath`, Mathlib's
  `liftPath_apply_one_eq_of_homotopicRel` for the endpoint equality, the
  independence lemma + `loopDegree_spec` + `mul_right_cancel₀` for the
  integer equality).  This makes the S263 iso computable: the degree
  descends to the homotopy class.  ROADMAP S265.
  **S266 (appended, VERIFIED sorry-free) — the degree as a map on
  homotopy classes of loops**: `liftOfLoop` (+ `liftOfLoop_lifts`, a
  canonical real lift, so the degree is a plain function of the loop),
  `loopDegreePath` (the degree on paths via the canonical lift),
  `loopDegreePath_eq_of_homotopic` (S265 at canonical lifts), and
  **`loopDegreeQuotient`** (+ `loopDegreeQuotient_mk`): the well-defined
  `Path.Homotopic.Quotient x x → ℤ` induced by `loopDegreePath` via
  `Quotient.lift` (S265 well-definedness) — the degree now lives on the
  fundamental-group carrier.  ROADMAP S266.
  **S267 (appended, VERIFIED sorry-free) — the degree respects
  concatenation (the group-homomorphism content)**: `loopDegree_eq_of_lifts`
  (degree independent of the lift), `coeffOfZmultiples_unique` +
  `coeffOfZmultiples_add` (the period-lattice coefficient is unique and
  additive), **`loopDegreePath_trans`** (the path-level additivity
  `loopDegreePath (γ.trans δ) = loopDegreePath γ + loopDegreePath δ`:
  canonical lifts A of γ from e and B of δ from A 1; the real
  concatenation P := A.trans B lifts γ.trans δ pointwise
  (`Path.trans_apply`, split at 1/2), so the degree of the concatenation
  is the coefficient of `P 1 − P 0 = (A 1 − e) + (B 1 − A 1)`, and
  `coeffOfZmultiples_add` sums the three lattice elements), and
  **`loopDegreeQuotient_trans`** (the quotient-level concatenation law on
  `Path.Homotopic.Quotient`).  Together with the degree-1 generator this
  identifies the degree with the S263 iso.  ROADMAP S267.
  **S268 (appended, VERIFIED sorry-free) — the degree-1 generator loop of
  `AddCircle p`**: `standardLoop` (the loop `γ t = ((t : ℝ) * p :
  AddCircle p)`, a genuine loop at 0 by `AddCircle.coe_period`),
  `standardLift` (+ `standardLift_lifts`, its real lift, covering by rfl),
  **`standardLoop_degree`** (the generator has degree 1: lift endpoint
  difference `p − 0 = (1 : ℝ) * p`, coefficient 1 via `loopDegree_spec` +
  `mul_right_cancel₀`), and `standardLoop_degreePath` /
  `standardLoop_degreeQuotient` (path- and quotient-level `= 1` via
  `loopDegree_eq_of_lifts` and `loopDegreeQuotient_mk`).  ROADMAP S268.
  **S269 (part 1, appended, VERIFIED sorry-free) — the monodromy of the
  generator loop is the translation by `p`** (item (i) of the S263-iso
  agreement chain): `coeC` (the covering map `ℝ → AddCircle p`, bundled),
  `realPath` (the standard loop as a real path `0 → p`, toFun =
  `standardLift p`), and **`monodromy_standardLoop`**:
  `IsCoveringMap.monodromy (mk (standardLoop p)) ⟨0, ·⟩ = ⟨p,
  AddCircle.coe_period⟩` — via `IsCoveringMap.monodromy_eq_of_map_eq` with
  the lifted real path `Γ := mk (realPath p)`, side condition assembled
  from `mk_map`, `mk_cast` and the `Path.ext` path equality
  `realPath.map coeC = (standardLoop p).cast ex.2 ey.2`.  ROADMAP S269.
  **S270 (appended, VERIFIED sorry-free) — the S263 iso sends the
  generator loop to the generator of ℤ** (items (ii)+(iii) of the
  agreement chain): `deckP` (+ `deck_smul_zero`, the period translation
  and its action), `zmultiplesHom_one`, **`zmultiplesEquivInt_p`** (item
  (ii): the deck identification sends `⟨p, ·⟩` to `1`),
  `fgToMulOpposite_gen` (the monodromy hom of the generator is
  `op (ofAdd (deckP p))`), `isoZ_eq_comp` (the S263 iso decomposes into
  its three steps), and **`isoZ_gen`** (item (iii):
  `fundamentalGroupAddCircle_isoZ p hp (mk (standardLoop p)) =
  Multiplicative.ofAdd (1 : ℤ)`).  ROADMAP S270.
  **S271 (appended, VERIFIED sorry-free) — item (iv): the zpow-degree
  lemma**: `genElem` (the generator as a `FundamentalGroup` element),
  `loopDegreeQuotient_mul` (degree additive over the group multiplication
  — `mul` is the reversed `trans`, quotient induction + S267
  `loopDegreePath_trans`, ℤ commutative), `loopDegreeQuotient_one`
  (`deg 1 = 0` from additivity), `degreeHom` (the degree as a
  `MonoidHom` to `Multiplicative ℤ`), `loopDegreeQuotient_zpow`
  (`deg (q ^ n) = n • deg q`, `MonoidHom.map_zpow` + `toAdd_zpow`), and
  **`loopDegreeQuotient_gen_zpow`** (`deg (genElem p ^ n) = n`).  ROADMAP
  S271.  **S272 (appended, VERIFIED sorry-free) — the agreement theorem (item
  (v), the final assembly of the quadrant)**: `loopDegreeQuotient_eq_isoZ`
  — for every `q` in `π₁(AddCircle p)`, `loopDegreeQuotient hp q =
  Multiplicative.toAdd (α q)` with `α := fundamentalGroupAddCircle_isoZ p
  hp`, by the free-cyclic argument (`m := toAdd (α q)`; `q =
  α.symm (ofAdd m) = (α.symm (ofAdd 1))^m = genElem^m` via S270
  `α (genElem p) = ofAdd 1`, `ofAdd_zsmul` and `map_zpow`; `deg q =
  m` by S271).  The concrete loop degree IS the S263 isomorphism — the
  circle quadrant of the winding route is closed.  ROADMAP S272.  **S273 (appended, VERIFIED sorry-free) — the core-retraction transport
  along a homeomorphism**: `coreRetract_transport` — if `ρY` is a
  continuous deformation retraction of `Y` onto `range coreY` (slide to
  core at `t = 1`, fixed on the core), then for any `φ : X ≃ₜ Y` the
  conjugate `ρ (x, t) := φ.symm (ρY (φ x, t))` is a continuous
  deformation retraction of `X` onto the transported core
  `range (φ.symm ∘ coreY)`, fixing it pointwise.  This is the mechanical
  bridge from `MobiusModel.mobius_core_retract` to the existing target
  `OpenMobiusCoreRetract` (already declared at Pi1Mobius) once the
  plane-model homeo `OpenMobius ≃ₜ MobiusModel` is built.  ROADMAP S273.  **S274 (appended, VERIFIED sorry-free) — the plane-model homeo
  `OpenMobius ≃ₜ MobiusModel`: class-level descent seeds** (module
  `Submission/ChordModelHomeo.lean`): the four quotient translations of the
  ChordParam bijection identities — `forward_swap_invariant` (the forward
  chord-data class is swap-invariant), `backward_flip_invariant` (the
  backward pair-class is flip-invariant), `backwardOrdered_forward_id`
  (forward∘backward = id at class level), `forward_backward_id`
  (backward∘forward = id at class level) — the descent seeds from which the
  type-level `Equiv` and then the `Homeomorph` (via the open-quotient-map
  machinery) are assembled.  ROADMAP S274.










* `ChordModel.lean` — the plane chord model of the open Möbius band: chord
  data `(n, d)` (`n : Circle` unit normal, `d ∈ (-1,1)` signed offset,
  chord = `{z : ℂ | z·n = d}`) with the flip `(n,d) ~ (-n,-d)`; verified:
  flip involution (continuous, involutive, preserves the interval), the
  representative-level slide `chordSlideAt t (n,d) = (n, (1-t)·d)` with its
  offset bound, flip-equivariance (`chordSlideAt_flip` — the slide descends),
  identity at `t=0`, landing on the core at `t=1`
  (`chordSlideAt_one_offset`), core fixing (`chordSlideAt_fixed_on_core`).
* `MobiusModel.lean` — **the quotient model is built and the deformation
  retraction is proven**.  `MobiusModel = ChordData / flip` (`chordSetoid`),
  class API (`mobiusMk_eq_iff`, `mobiusMk_flip`), the *open quotient map*
  certificate `isOpenQuotientMap_mobiusMk` (saturation `U ∪ chordFlip '' U`
  open, since the flip is a continuous involution).  The slide descends:
  `mobiusSlide : MobiusModel × I → MobiusModel` is continuous
  (`continuous_mobiusSlide`, via `IsOpenQuotientMap.prodMap` +
  `continuous_comp_iff` on the representative slide `continuous_chordSlideAt_prod`),
  and satisfies `mobiusSlide (c, 0) = c`, `mobiusSlide (c, 1) ∈ range mobiusCore`,
  `mobiusSlide (mobiusCore n, t) = mobiusCore n` — i.e.
  **`mobius_core_retract : MobiusCoreRetract`**, the deformation retraction
  of the model Möbius band onto its core circle `mobiusCore n = [(n,0)]`
  (diameters).  The core is a circle: `mobiusCore n = mobiusCore m ↔ n = m ∨
  n = -m` (`mobiusCore_eq_iff`, via `mobiusCore_neg` /
  `chordRel_coreChord_iff`).

* `CirclePairs.lean` — **the parameter secant space is identified with the
  circle-pair plane model**.  The swap quotient of `Circle × Circle`
  (`circleSwapSetoid`, `CircleUnordPairs`, `circleDiagClass`,
  `CircleOpenPairs` = non-diagonal classes) and the homeomorphism
  `unordParamCircleEquiv : UnordCirclePairs ≃ₜ CircleUnordPairs` (Mathlib
  `Homeomorph.Quotient.congr` on `paramCircleHomeo.prodCongr
  paramCircleHomeo`, via the swap-relation transport `pairRel_circle_iff`),
  with the diagonal transport (`unordParamCircleEquiv_diag`, `openDiag_iff`,
  `openDiag_iff'`), and the restricted
  **`openMobiusCircleEquiv : OpenMobius ≃ₜ CircleOpenPairs`**.  This puts the
  trig chord parametrisation `CircleOpenPairs ≃ MobiusModel` (a later module,
  route recorded in ROADMAP) on the correct domain.

* `MobiusHomotopy.lean` — **the model Möbius band is homotopy equivalent to
  its core circle**: `mobius_model_homotopyEquiv_core :
  Nonempty (MobiusModel ≃ₕ {c : MobiusModel // c ∈ Set.range mobiusCore})`,
  an instantiation of the commons lemma
  `Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract` with the
  deformation retraction `mobius_core_retract` (MobiusModel.lean).

* `ChordParam.lean` — **the analytic core of the chord parametrisation
  `CircleOpenPairs ≃ MobiusModel`** (second half of the `OpenMobius ≃
  MobiusModel` bridge, on top of the `openMobiusCircleEquiv` of
  CirclePairs.lean).  A pair `{u,v}` of distinct unit-circle points maps to
  the chord data `(n, d)` with unit normal `n = I·(v-u)/‖v-u‖`
  (`circleNormal`) and signed offset `d = ⟪u,n⟫ ∈ (-1,1)`
  (`circleChordOffset`, strictness from the distinctness of `u,v`);
  `chordDataOf u v h : ChordData` is the forward map, and it is
  flip-equivariant under swapping the endpoints (`chordDataOf_swap`).
  Backward, chord data `(n,d)` give the two endpoints
  `n·(d ± I·√(1-d²))` (`chordEndpointPlus`/`chordEndpointMinus`, unit via
  Mathlib's `normSq_ofReal_add_I_mul_sqrt_one_sub`, distinct — the chord
  genuinely cuts the disk) packaged as `backwardOrdered q`.  The recovery
  identities hold: `unit_endpoint_of_inner_eq` shows every unit point on
  the chord is one of the two endpoints; `backwardOrdered_of_chordDataOf_rel`
  (identity (A): the endpoints of `chordDataOf u v h` are exactly `{u,v}`)
  and `chordDataOf_backwardOrdered` (identity (B): the forward map is a
  right inverse) are proved, together with the raw computations
  (`backward_I_mul_sub`, `norm_backward_sub`, `rawCircleNormal_endpoints`,
  `inner_endpoint_plus_normal`).  The topological quotient descent to a
  homeomorphism `OpenMobius ≃ MobiusModel` (continuity of the two maps,
  via the open-quotient-map machinery) is the next layer.

* `SecantModel.lean` — **topological quotient descent, forward half**: the
  analytic forward map of `ChordParam.lean` is carried through the
  quotients.  `forwardChordData : OrderedPairs → ChordData` (parameters
  through `paramCircleHomeo`) is continuous (`continuous_forwardChordData`,
  built from `continuous_rawNormal_ordered` /
  `continuous_circleChordOffset_ordered`, the pole at the diagonal handled
  by `ContinuousOn` on the off-diagonal set); it flips under the endpoint
  swap (`forwardChordData_swap`), so `forwardRep : OrderedPairs →
  MobiusModel` is continuous and swap-invariant (`forwardRep_swap`).
  Choosing a representative of each class of the open Möbius band gives the
  induced **`forwardModel : OpenMobius → MobiusModel`**, continuous
  (`continuous_forwardModel` — `mobiusCover` is an open quotient map, so
  continuity is checked on representatives via
  `IsOpenQuotientMap.continuous_comp_iff`; the choice is immaterial,
  `forwardModel_mobiusCover`).  **Backward descent (also done in
  SecantModel.lean)**: the chord endpoints `chordEndpointPlus/Minus` are
  continuous functions of the chord data (`continuous_chordEndpointPlus_data`,
  `continuous_chordEndpointMinus_data`), so the circle-pair class
  `backwardChordClass : ChordData → CircleUnordPairs` is continuous and
  `chordRel`-invariant (`backwardChordClass_resp`, from
  `backwardOrdered_flip_rel`); `backwardLift : MobiusModel → CircleUnordPairs`
  is its continuous quotient lift, it lands in the open part
  (`backwardLift_not_diag` — the endpoints of a nondegenerate chord are
  distinct, `circleClass_not_diag_of_ne`), giving
  `backwardCircle : MobiusModel → CircleOpenPairs` and the continuous
  **`backwardModel : MobiusModel → OpenMobius`** through the circle-pair
  homeomorphism (`continuous_backwardModel`).  **The homeomorphism is
  done**: recovery identity (A) at class level (`backwardCircle_chordDataOf`,
  `backwardModel_forwardModel_mobiusCover`, `backward_leftInverse_forwardModel`),
  recovery identity (B) at class level (`chordDataOf_param_self`,
  `forwardChordData_param_symm`, `forwardModel_backwardModel_mobiusMk`,
  `forward_rightInverse_backwardModel`), assembled as
  `openMobiusModelEquiv : OpenMobius ≃ MobiusModel` and the
  **`openMobiusModelHomeo : OpenMobius ≃ₜ MobiusModel`** — the open Möbius
  band of knot secants is homeomorphic to the chord model
  `MobiusModel = ChordData/flip`.  **The core correspondence and the
  retraction are done**: a half-period parameter shift is a negation of the
  circle point (`paramCircleHomeo_add_halfPeriod`, `paramCircleHomeo_symm_neg`,
  `toCircle_halfPeriod`); antipodal pairs give diameters
  (`circleChordOffset_neg_zero`, `chordDataOf_neg_eq_coreChord`,
  `forwardModel_core_mem_mobiusCore`) and conversely
  (`chordEndpointMinus_neg_endpoint`, `backwardModel_mobiusCore_mem_core`);
  transporting `mobius_core_retract` through `openMobiusModelHomeo` yields
  **`openMobiusCoreRetract`** — the deformation retraction of the open Möbius
  band onto its core circle (statement of `Pi1Mobius.lean`).

* `OpenMobiusHomotopy.lean` — **the open Möbius band is homotopy equivalent
  to its core circle**:
  `openMobius_homotopyEquiv_core :
  Nonempty (OpenMobius ≃ₕ {c : OpenMobius // c ∈ Set.range coreFactor})`,
  an instantiation of the commons lemma
  `Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract` with the
  deformation retraction `openMobiusCoreRetract` (SecantModel.lean) —
  exactly the `OpenMobius`-side analogue of `MobiusHomotopy.lean`.  The
  right-hand side is the core circle (homeomorphic to `Circle` via
  `coreRangeCircle`, Pi1Mobius.lean), so this is the certificate the
  π₁(OpenMobius) ≅ ℤ assembly consumes.

* `Pi1OpenMobius.lean` — **`π₁(OpenMobius) ≅ ℤ` is proven**:
  `pi1_openMobius_eq_int : Pi1OpenMobiusEqInt`, i.e.
  `Nonempty (FundamentalGroup OpenMobius pi1Base ≃* Multiplicative ℤ)` at
  the core basepoint `pi1Base = coreFactor (coreCircleHomeo.symm 1)`
  (whose core-circle image is `1 : Circle` — `coreRangeCircle_pi1Base`).
  Chain: the (fleet-proven, generic) π₁-along-homotopy-equivalence lemma
  `Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv`
  glues `openMobius_homotopyEquiv_core` (OpenMobius → core circle) and the
  homeomorphism `coreRangeCircle` (a homotopy equivalence via
  `Homeomorph.toHomotopyEquiv`, toFun equal to the homeo map by rfl), with
  path-connected basepoint transport inside the core circle (instance
  `coreRangePathConnected` from `coreFactor_homeo`'s surjectivity) and
  inside `Circle`, ending at the fleet's `pi1_circle_eq_int`.

* `EmbeddedCircleWinding.lean` — **Layer C: embedded circles, started**.
  Vocabulary: `IsSimpleClosedCurve` (image of an injective continuous map
  from `Circle`), `IsNonSeparating`/`IsSeparating` (complement connected /
  disconnected).  **Base case proved (model side)**: the core circle of the
  Möbius band does not separate it — `model_core_complement_isPathConnected`
  (the complement is an annulus: `offCoreOfPos : Circle × (0,1) → OffCore`
  is a continuous surjection, each off-core chord having a positive-offset
  representative; path-connectedness from the interval instance
  `intervalPathConnected` and `Function.Surjective.pathConnectedSpace`),
  hence `model_core_complement_isConnected` and
  `model_core_circle_nonSeparating`.  **The transport to `OpenMobius` is
  done**: `forwardModel_mem_mobiusCore_iff_mem_core` (the homeo maps the
  core circle of `OpenMobius` exactly onto the model core) restricts to the
  **bridge homeomorphism `openMobiusOffCoreEquiv : OpenMobiusOffCore ≃ₜ
  OffCore`** between the complements, transporting path-connectedness back
  (`PathConnectedSpace OpenMobiusOffCore`,
  `openMobius_core_complement_isPathConnected`, `_isConnected`) and giving
  **`openMobius_core_circle_nonSeparating`** — the core circle does not
  separate the open Möbius band of knot secants.  **Dichotomy statements
  (b/c) formalised**: `SimpleClosedCurve` (image `image`), `IsNullHomotopic`
  /`IsEssential`, `BoundsADisk` (embedded copy of the closed unit disk whose
  boundary is the curve), the target `TrivialCircleBoundsDisk_OpenMobius`
  (documented; proof pending surface-topology foundations absent from
  Mathlib), and first consequences `image_isCompact`, `image_isClosed`;  **the null-homotopy transfer is done**: a null-homotopic circle map stays null-homotopic after composition with any continuous map (`nullHomotopic_of_nullHomotopic_comp`), so null-homotopic embedded circles in `OpenMobius` push to null-homotopic loops in the core circle through the homotopy-equivalence map of `openMobius_homotopyEquiv_core` (`openMobius_core_nullHomotopic_loop`) — the first step of the trivial-side reduction.
* `QuadrisecantChord.lean` — **the quadrisecant/chord reformulation of the
  target**.  Kuperberg's "quadrisecant" is a *secant with two middle points*:
  four pairwise-distinct parameters `a b z w` with `knotMap z` and
  `knotMap w` strictly inside the chord from `a` to `b`
  (`IsMiddleOnChord`, `QuadrisecantChord r`).  The trusted statement
  `HasQuadrisecant r` (four distinct parameters with collinear images) is
  shown equivalent to it, `hasQuadrisecant_iff_quadrisecantChord`, in two
  steps through the circle form (`QuadrisecantCircle.lean`):
  `quadrisecantChord_imp_circleQuadrisecant` is immediate
  (`smul_add_smul_eq_add_smul_sub` re-expresses the convex combination
  against the chord direction); the converse
  (`circleQuadrisecant_imp_quadrisecantChord`) is the elementary fact that
  among four distinct collinear points the two *extreme* ones chord the
  other two strictly inside: the four coefficients (pairwise distinct by
  `coeff_eq_of_smul_eq_smul` on the nonzero direction `v`) have minimum and
  maximum indices (`Finset.exists_min_image`/`exists_max_image` over
  `Fin 4`; `fin4_injective_of_QuadDistinct`, `two_other_indices` pick the
  remaining two), and `mem_openSegment_affine_coeff` witnesses strict
  betweenness along the line `{p + s • v}`.  This is the bridge from the
  trusted four-parameter statement to the secant-space double-point /
  middle-point language used in the Kuperberg contradiction.
* `ChordCoefficient.lean` — **S276 (VERIFIED): the chord-coefficient of
  the trapped middle — continuous affine position along a chord**
  (`Submission/ChordCoefficient.lean`, sorry-free, warning-free;
  brick-(c) sub-problem 4, first stone).  For points `x y z` of an
  inner-product space over `ℝ`, `segmentCoeff x y z = ⟪z−x, y−x⟫/‖y−x‖²`
  is the unique `c` with `z = (1−c)•x + c•y`; for `z` strictly in the
  open segment and `x ≠ y` it is strict
  (`segmentCoeff_of_mem_openSegment`: the affine identity plus
  `0 < c < 1`) and the representation is unique
  (`segmentCoeff_eq_of_affine`), with the projections
  `segmentCoeff_pos`/`segmentCoeff_lt_one`/`segmentCoeff_spec`,
  `segmentCoeff_swap` (the swap law `segmentCoeff y x z = 1 −
  segmentCoeff x y z` — the odd-branch flip) and the congruence
  `segmentCoeff_congr`; **`continuous_segmentCoeff`** — the
  coefficient is continuous in continuous families `A B M : C(α, E)`
  with distinct endpoints (the explicit formula is a composition of
  continuous maps with a never-zero denominator).  Knot instances:
  `r_ne_of_class_ne` (distinct circle classes of real parameters have
  distinct knot values, via `knotMap_injective` + `knotMap_eq_r`) and
  **`continuous_knot_segmentCoeff`** (for the real endpoint/middle lifts
  of a circular component with `(a u) ≠ (b u)` as classes the coefficient
  `u ↦ segmentCoeff (r (a u)) (r (b u)) (r (m u))` is continuous — with
  the S260 trappedness it is the strict `(0,1)`-position of the middle
  knot point on its moving chord, the object of the S253b route-(i)
  "chord-coefficient continuity" step of the trapped-middle measurement).
  ROADMAP S276.
* `TrappedWinding.lean` — **S277 (VERIFIED): the λ-bridge of the trapped-
  middle measurement on a circular component** (`Submission/TrappedWinding.lean`,
  sorry-free, warning-free, imports ComponentLoop + ChordCoefficient).
  `chordCoeffAlong a b m u = segmentCoeff (r (a u)) (r (b u)) (r (m u))`
  instantiates the S276 coefficient on the real endpoint/middle lifts of
  a circular component; `continuous_chordCoeffAlong` /
  `chordCoeffAlong_mem_Ioo` (continuity; strict `(0,1)` under the S260
  trappedness with distinct endpoint classes), the component wiring
  `component_endpoint_classes_ne` (the ordered chord's endpoints are
  distinct classes), `component_middle_lift_class_periodic` (every real
  middle lift has `T`-periodic classes: the chart returns after one
  circuit), `component_trapped_coeff_continuous` /
  `component_trapped_coeff_strict` (S260's
  `componentMiddle_real_betweenness` supplies the membership, so the
  coefficient is a continuous strict `(0,1)`-function along the whole
  parametrisation); and **the branch laws** — `chordCoeffAlong_shift_of_even`
  (`λ (u+T) = λ u` when the endpoint/middle classes return: the EVEN
  branch), `chordCoeffAlong_shift_of_odd` (`λ (u+T) = 1 − λ u`: the ODD
  sheet-swap flips the coefficient, via the S276 swap law), with the
  sig-level instances `component_coeff_even_periodic` /
  `component_coeff_odd_flip`.  This is the object the winding measurement
  operates on; the measurement itself (deriving the middle's advance from
  the endpoint windings, against S255 / `no_onceWinding_advance`) is the
  recorded continuation of brick-(c) sub-problem 4.  ROADMAP S277.
  **S278 (appended, VERIFIED sorry-free) — the winding-measurement
  interfaces, TWICE and ONCE pinned precisely**: the two case targets of
  brick (c) written in the shape S253–S255/S257–S262 consume, separating
  verified assembly from the (documented, pinned) missing geometric core.
  TWICE: `TwiceWindingEndpointsData` (even ordered lift `sig (u+T) = sig
  u` + continuous real endpoint lifts whose per-circuit advances are
  exactly `±period`, `ka = ±1`/`kb = ±1` — each endpoint winds once),
  `MiddleNonZeroAdvance` (a continuous real lift of the canonical middle
  with integer degree `k ≠ 0`), the pin **`twice_winding_middle_advance`**
  (`TwiceWindingEndpointsData c₀ χ → MiddleNonZeroAdvance c₀ χ` —
  Kuperberg's "endpoints each wind once … and therefore so does m_t";
  open, documented as the missing geometric core), and the verified
  assembly **`twice_contradiction_of_middle_advance`** (a genuine
  nonzero-degree middle lift is contradictory: S254
  `no_twiceWinding_component_of_lift_zsmul`, genuine-middle membership
  automatic by `componentMiddle_mem_middleSet`) — so TWICE = pin +
  assembly.  ONCE: `OnceWindingData` (ODD ordered lift
  `sig (u+T) = swapOrdered (sig u)` + continuous real endpoint lifts),
  the verified negative interface **`once_winding_no_half_advance_lift`**
  (no half-period-advancing real middle lift exists over any circular
  component — `no_onceWinding_advance`; the ONCE geometry can never close
  via the S253 half-avatar), and the pin
  **`once_winding_component_contradiction`** (`OnceWindingData → False` —
  Kuperberg's jump; open, documented).  ROADMAP S278.
  **S279 (appended, VERIFIED sorry-free) — the winding measurement CLOSED
  at the chart level: elementary circle-map advance bookkeeping**: the two
  S278 pins are resolved.  `advance_eq_of_class_ne` — the advance-agreement
  principle: two continuous real curves whose classes in `AddCircle P`
  never meet have EQUAL per-circuit advances (fractional-part correction
  `H = g + P·fract((f−g)/P)` is a continuous lift of `f`'s class with `g`'s
  advance, so `H − f` is a continuous `Pℤ`-valued — hence constant —
  function; comparing at `u` and `u+T` gives `df = dg`; the lift-level
  form of "circle maps of different degrees intersect");
  `advance_eq_zero_of_periodic`; `exists_eq_zero_of_antiperiodic` (IVT);
  `middle_class_ne_endpoints` (strictness in class form,
  `IsMiddleOnChord.ne_params`).  EVEN branch: `even_endpoints_equal_advance`
  (h-free `ka = kb`) and **`even_endpoint_advances_zero`** (S255's periodic
  middle lift + advance-agreement force `ka = kb = 0`) — hence
  **`twice_winding_data_false`** (`TwiceWindingEndpointsData` is
  UNINHABITED) and the S278 TWICE pin in data form
  `twice_winding_middle_advance_of_endpoints`.  ODD branch:
  **`once_winding_data_false`** (over `2T` the endpoint advance `ka + kb`
  meets the periodic middle's `0` in advance-agreement, so `ka + kb = 0`,
  and the resulting continuous `T`-anti-periodic function
  `u ↦ a (u+T) − a u` has a zero — `a (u+T) = a u` — contradicting the
  sheet swap), and the S278 pin `once_winding_component_contradiction`
  becomes a THEOREM (`once_winding_component_contradiction_holds`).  So no
  circular component of the trisecant set winds: the Layer-C winding
  branch is closed at the chart level, with no chord-direction/π_K
  machinery needed.  ROADMAP S279.
* `ComponentNullHomotopy.lean` — **S280 (VERIFIED): brick (d), first step
  — the class map of a circular component of the trisecant set is
  NULL-HOMOTOPIC in the band** (`Submission/ComponentNullHomotopy.lean`,
  sorry-free, warning-free; imports TrappedWinding + ComponentWindingData
  and the commons `nullHomotopic_comp_left`,
  `interval_of_not_mem_zmultiples`).  `componentCircleClassMap` (the class
  map descended to the component circle), `orderedRealModel` /
  `orderedLiftLoop` (the ordered lift through the double cover from
  `T`-periodic endpoint lifts, with `liftIco_zero_coe_apply_of_periodic`
  and `mobiusCover_orderedLiftLoop`), `orderedHomotopy_diff_notMem` +
  `orderedHomotopyFun` (the explicit straight-line homotopy of the ordered
  pair to a constant pair `((k+1/2)·period, 0)`, staying off the diagonal
  because the difference `(1−s)(a u − b u) + s·(k+1/2)·period` is a convex
  combination of two points of the open window `(k·period, (k+1)·period)`,
  from the commons `interval_of_not_mem_zmultiples`),
  **`nullHomotopic_orderedLiftLoop`** (the descended null-homotopy in
  `OrderedPairs`), `componentClassMap_nullHomotopic_of_periodic_endpoints`,
  and **`circular_component_classMap_nullHomotopic`**: under general
  position and quadrisecant-freeness the class map of every circular
  component of `O` is null-homotopic — no circular component winds, so the
  (D) dichotomy's winding branch is vacuous (the even branch is null by
  S279 + the explicit homotopy; the odd branch is impossible by
  `once_winding_data_false`).  **S281 (VERIFIED)**: re-charting the
  conclusion through `paramCircleHomeo : AddCircle period ≃ₜ Circle`
  (`nullHomotopic_of_comp_paramCircleHomeo`, unwrapping the `Nonempty`
  homotopy via `ContinuousMap.Homotopy.apply_zero/apply_one`) yields
  **`circular_component_curve_nullHomotopic`**: for a circular component
  `c₀` of `O` and any circle chart `χ : Circle ≃ₜ TrisecantComponent r c₀`,
  the S250 `SimpleClosedCurve` of the component is `IsNullHomotopic` with
  its image still the component val-set — the `EmbeddedCircleWinding`
  essential-circle branch is vacuous for every circular component of `O`.
  ROADMAP S280/S281.
* `TrisecantLocus.lean` — **Layer A (iii): the trisecant locus over the
  secant space**.  A (strict) trisecant of `r` is a chord of distinct
  parameters `a, b` carrying a *middle point* `m` (`IsMiddleOnChord r a b m`,
  `knotMap m` strictly inside the chord); strictness forces `m` off the
  endpoints (`ne_left_right_of_mem_openSegment`, generic inner-product-space
  fact; `IsMiddleOnChord.ne_params` via knot injectivity).  On the Möbius
  band: `HasMiddleOnClass r c` — the unordered pair `c : OpenMobius` is a
  trisecant — is well defined (`IsMiddleOnChord_swap`, `OOrdered_swap`,
  rep-independence `HasMiddleOnClass_rep`, with the fibre description
  `mobiusCover_fiber`); `trisecantSet r` is Kuperberg's `O`.  The double
  points `HasTwoMiddlePointsOnClass r c` (two distinct middle points on the
  chord of `c`) are the quadrisecants at class level:
  `quadrisecantChord_iff_exists_class`, and the trusted target becomes
  `hasQuadrisecant_iff_exists_class : HasQuadrisecant r ↔
  ∃ c : OpenMobius, HasTwoMiddlePointsOnClass r c` — the class-level
  double-point form used in the Kuperberg contradiction.

* `TrisecantClosed.lean` — **Layer A (iii, continued): closed chords and the
  compactification of trisecant data**.  Since `O` is defined by a *strict*
  middle-point condition and lives over the *open* band, its limits need a
  compactified description over the compact band `UnordCirclePairs` (which
  adds the diagonal circle of degenerate secants).  The module records the
  precise degeneracy of the naive "closed segment" formulation: with the
  middle point *not attached as data*, the closed-segment condition is
  vacuous over the whole band — every pair qualifies because an endpoint of
  a chord lies on its own closed segment (`left_mem_segment`), so
  `closedMiddlePairSet r = Set.univ` and at class level
  `closedMiddleClassSet r = Set.univ` (`closedMiddleClassSet_eq_univ`,
  `isClosed_closedMiddleClassSet`).  The correct closed objects therefore
  attach the middle point, exactly as Kuperberg insists ("for a sequence of
  trisecants to converge we insist that the middle points converge as
  well"): the attached closed-middle data `closedMiddleData r ⊆ (S¹)³` is a
  closed — hence compact — subset of the compact parameter cube, proved via
  the unit-interval lift (`mem_segment_iff_lineMap` reduces segment
  membership to an equality with `AffineMap.lineMap` over `t ∈ [0,1]`; the
  zero set of a continuous map is closed, a closed set of a compact space
  is compact, and its image under the coordinate projection is compact
  hence closed).  Strict trisecant data `openMiddleData r` sit inside it
  (`openMiddleData_subset_closedMiddleData`), so the closure of the strict
  trisecant data lies in `closedMiddleData r`
  (`closure_openMiddleData_subset_closedMiddleData`): limits of genuine
  strict trisecants keep their middle point on the closed chord — the
  rigorous "degenerate trisecant at the boundary of `O`".

* `QuadrisecantLimit.lean` — **Layer A (iv): degenerate limits of
  quadrisecant configurations**.  The attached two-middle data over the
  parameter quadruple cube: `closedDoubleMiddleData r` = quadruples
  `(a,b,z,w)` whose `z`- and `w`-th knot points lie on the *closed* chord of
  `(a,b)` is closed (`isClosed_closedDoubleMiddleData`, as the preimage of
  the square of the `closedMiddleData` of TrisecantClosed under a continuous
  map) hence compact (`isCompact_closedDoubleMiddleData`); its strict
  analogue `openDoubleMiddleData r` (both middle points strictly inside)
  satisfies `closure (openDoubleMiddleData r) ⊆ closedDoubleMiddleData r`
  (`closure_openDoubleMiddleData_subset_closedDoubleMiddleData`) — limits of
  two-middle configurations keep both middles on the closed chord.  The
  sharp statements: honest quadrisecants `quadrisecantData r` (pairwise
  distinct `a b z w` with two strict middles) equal the closed two-middle
  data *intersected with the pairwise-distinct configurations*
  (`quadrisecantData_eq_closedDoubleMiddle_inter`; a non-endpoint of a
  closed segment lies in its interior, `mem_openSegment_of_ne_left_right`,
  and `knotMap_injective` converts parameter distinctness to point
  distinctness), and hence equal the *nondegenerate limits of strict
  two-middle data* — `quadrisecantData r = closure (openDoubleMiddleData r) ∩
  {QuadDistinct}` (`quadrisecantData_eq_closure_openDouble_inter`); any such
  nondegenerate limit is a genuine quadrisecant
  (`quadrisecant_of_closure_nondegenerate`).  `QuadrisecantChord r` is
  exactly non-emptiness of `quadrisecantData r`
  (`quadrisecantChord_iff_quadrisecantData_nonempty`).  This is the
  set-theoretic replacement for Kuperberg's sequential-compactness step
  ("by compactness, {Q_i} has a convergent subsequence"): limits live in the
  compact `closedDoubleMiddleData`, and limits that remain pairwise-distinct
  are already honest quadrisecants.

* `TrisecantStructure.lean` — **Layer A (v): structure of the trisecant
  locus (genericity-free foundations)**.  The full structure theorem of the
  layer — `O` is the image of a self-transverse smooth immersion of a
  1-manifold whose double points are the quadrisecants — needs
  general-position/transversality infrastructure absent from Mathlib (and is
  false without a genericity hypothesis); this module supplies the parts
  that hold for every smooth knot.  `MiddlePointsOnClass r c` — the middle
  parameters attached to a secant class (rep independence for a *fixed*
  middle: `middleOnChord_of_mobiusCover_eq`) — never contain the chord
  endpoints (`MiddlePointsOnClass_not_endpoint`).  The no-quadrisecant
  hypothesis `QuadrisecantFree r` is equivalent to at most one middle point
  per class (`quadrisecantFree_iff_atMostOneMiddle`): without double points
  `O` is a functional locus, carrying a single middle parameter at each
  point.  `O` is exactly the projection of the attached data
  `OrderedTrisecantData r` over the ordered double cover
  (`trisecantSet_eq_orderedTrisecantData_image`) — the set whose 1-manifold
  structure is the theorem.  The extremal contradictions end the winding
  analysis: no smooth knot has every point strictly between two others
  (`not_every_image_point_between`) nor every parameter middle-covered
  (`not_every_middle_of_smooth_knot`), so there is always an uncovered
  (extremal) parameter (`exists_uncovered_middle`) — Kuperberg's
  Lemma-compact in both the point and the parameter formulation.

* `TrisecantCover.lean` — **Layer A (v) data-level fibre analysis under the
  no-quadrisecant hypothesis** (`Submission/TrisecantCover.lean`,
  sorry-free, imported by Submission.lean).  Makes the class-level
  functional structure (`quadrisecantFree_iff_atMostOneMiddle`) operative
  at the *data* level: `middle_unique_of_quadrisecantFree` (for an ordered
  chord `(a,b)` of distinct parameters, two strict middle parameters
  coincide — the middle of a trisecant class is a *function* of the class,
  which is what makes the family `{a,b}_t, m_t` along a curve `C ⊆ O` of
  Kuperberg's winding argument well-defined),
  `openMiddleData_unique_of_quadrisecantFree` (the same uniqueness for the
  torus-level attached open data over fixed chord endpoints; the
  degenerate `a = b` chord is handled separately via `openSegment_same`),
  `orderedTrisecantData_middle_unique` (inside the attached data over the
  ordered double cover, equal chord representatives give equal middles),
  and `orderedTrisecantData_fiber_swap` (two attached data representing the
  same secant class have chords equal or swapped and equal middles: under
  `QuadrisecantFree` the projection of the attached data onto `O` is
  two-to-one — the ordered reps — with constant middle on each fibre, the
  data double cover of `O`).

* `ParameterWinding.lean` — **Layer C (W): advancing lifts of
  circle-valued families are surjective** (`Submission/ParameterWinding.lean`,
  sorry-free, imported by Submission.lean).  The elementary winding core of
  the twice-winding contradiction for the *parameter circle*
  `AddCircle period` of the knot.  `surj_of_lift_advance`: a continuous real
  lift `G : ℝ → ℝ` that advances by exactly `p > 0` over every circuit of
  length `T > 0` (`G (t + T) = G t + p`) induces a *surjective* family
  `t ↦ (G t : AddCircle p)` — proof by the intermediate value theorem on
  `[0,T]` against the lattice `p·ℤ` (`H = G − r` satisfies
  `H(T) = H(0) + p`, so it attains `k·p` for the floor-chosen integer
  `k = ⌊H(0)/p⌋ + 1`, and `k·p = 0` in the quotient by `zmultiples p`).
  `knotParam_surj_of_lift_advance` instantiates with `p = period`: a middle
  lift advancing by one knot period per circuit covers *every* parameter.
  `middle_surjective_contradiction` (with `TrisecantStructure`): a
  surjective genuine-middle family `m t ∈ MiddleCovered r` contradicts the
  extremal `exists_uncovered_middle` — the endpoint of Kuperberg's
  twice-winding argument (a twice-winding circular component of the
  trisecant locus has a middle lift advancing by exactly `period` per
  circuit, so its middle map would cover all of the compact knot, forcing
  every parameter to be middle-covered).  **S247 (appended, VERIFIED
  sorry-free) — the TWICE-branch contradiction assembled**:
  `twiceWinding_middle_contradiction` — a continuous real lift `G`
  advancing by a full period per circuit (`G (t+T) = G t + period`,
  `0 < T`) whose circle values are genuine middles (`∈ MiddleCovered r`)
  is impossible (surjectivity from `knotParam_surj_of_lift_advance` +
  `middle_surjective_contradiction` vs `exists_uncovered_middle`) — the
  analytic endpoint of the TWICE case; the geometric family-production
  lemma (TWICE circular data ⇒ such a `G`) is the only remaining input.
  **S254 (appended, VERIFIED sorry-free) — the `k ≠ 0` generalisation (the
  S253b fallback measurement)**: `surj_of_lift_advance_zsmul` — a
  continuous real lift advancing by ANY nonzero integer multiple of the
  period (`G (t + T) = G t + (k : ℝ) * p`, `0 < p`, `0 < T`, `k : ℤ`,
  `k ≠ 0`) is still surjective onto `AddCircle p` (proof: scale by `p` so
  the window endpoints differ by exactly the integer `k`; over one circuit
  the window has integer length `|k| ≥ 1` so it contains an integer — the
  floor argument in the `k < 0` and `k > 0` branches — and the
  intermediate value theorem, ordinary or reversed
  `intermediate_value_Icc'`, finds the witness; lattice helper
  `int_in_unit_window`: every `[a, a+1]` contains an integer);
  `knotParam_surj_of_lift_advance_zsmul` (the `period` instantiation);
  `twiceWinding_middle_contradiction_zsmul` (the S247 endpoint for ANY
  nonzero degree: a genuine-middle family with a `k ≠ 0`-advancing lift is
  impossible) — the TWICE branch now needs only "the middle map of a
  twice-winding component has nonzero degree", NOT the exact full-period
  advance.  ROADMAP S254.
  ROADMAP S78/S247.

* `SecantDisk.lean` — **Layer A1/Layer B: the topologically trivial secant
  (definitional layer)** (`Submission/SecantDisk.lean`, sorry-free, imported
  by Submission.lean).  Kuperberg's Definition ("a secant of a link `L` with
  no extra interior intersections with `L` is topologically trivial if its
  endpoints lie on the same component, and if it, together with one of the
  two arcs of this component, bounds a disk whose interior does not
  intersect `L`; the disk may intersect itself and the secant") made formal
  for a smooth knot: `ChordInteriorFree r a b` (no knot point strictly
  inside the open chord — `∀ m, ¬ IsMiddleOnOpenChord r a b m`; symmetric,
  `ChordInteriorFree_symm`); `chordPath r a b` (the affine chord from
  `knotMap r a` to `knotMap r b` as a `Path`, whose range is the closed
  space segment: `range_chordPath_eq_segment` via `mem_segment_iff_lineMap`);
  `PathsBoundDiskInteriorFree K γ δ` (two paths with common endpoints
  bound a possibly singular disk whose interior avoids `K` — a continuous
  `D : I × I → Space` with `D(·,0) = γ`, `D(·,1) = δ`, side edges pinned at
  the endpoints, interior points off `K`; a square formulation whose
  symmetries are elementary reflections:
  `PathsBoundDiskInteriorFree_rev`, reflecting across the vertical axis,
  reverses both boundary paths); `IsKnotArcPath r a b α` (a simple path on
  the knot image between the endpoints — "one of the two arcs"; reversed
  arcs are arcs: `IsKnotArcPath_symm`); and the target notion
  `ChordTrivialByArc` / `TrivialSecant r a b` / `NontrivialSecant r a b`
  (the chord is trivial when it is interior-free and, with some knot arc
  `α`, the disk spanned by `α` and the chord has interior avoiding the
  knot; the existential over the arc expresses "together with one of the
  two arcs"; endpoints on the same component are automatic for a knot).
  Elementary API: projections `ChordTrivialByArc.interior_free`,
  `.arc_simple`, `.arc_mem_knot`, `.disk`, `TrivialSecant.interior_free`.
  **D1 done**: endpoint symmetry — `chordPath_symm_eq`
  (`(chordPath r a b).symm = chordPath r b a` via
  `AffineMap.lineMap_apply_one_sub`), `ChordTrivialByArc_swap` (reverse the
  arc, reflect the disk), and **`TrivialSecant_swap`** /
  `NontrivialSecant_swap` (triviality and nontriviality are symmetric in the
  chord endpoints).  **D2 done**: the data-level triviality wrappers —
  `TrisecantTrivial r p q m` (a trisecant chord with middle is trivial when
  one of its endpoint-to-middle sub-chords `(p,m)`, `(m,q)` is a trivial
  secant; `TrisecantTrivial_swap_endpoints` — the chord endpoints commute)
  and `QuadrisecantMiddleSecantTrivial r z w` (a quadrisecant is trivial at
  the middle secant when the chord between its two middles is trivial;
  `QuadrisecantMiddleSecantTrivial_swap` — the middles commute), each with
  its unfolded `_iff`.  **D3-preparation done**: the class-level `O'`
  subset — `Submission/OPrime.lean` defines `NontrivialTrisecantData r`
  (attached `(p,m)` data with `¬ TrisecantTrivial`), `ClassNontrivialTrisecant
  r c` (the class carries a non-trivial trisecant; representative
  independence `NontrivialData_rep` via `mobiusCover_fiber` + the D1/D2
  swaps; `ClassNontrivialTrisecant_mobiusCover`; projection identity
  `nontrivialTrisecantData_image_eq`), `ClassNontrivialMiddleSecant r c`
  (two distinct middles whose middle secant is non-trivial, `¬
  QuadrisecantMiddleSecantTrivial`; empty under `QuadrisecantFree`), and
  **`OPrime r : Set OpenMobius`** (the union; `mem_OPrime_iff`,
  `OPrime_subset_trisecantSet` — `O' ⊆ O`, and
  `mem_OPrime_iff_of_quadrisecantFree` reducing membership to the trisecant
  clause).  Next A1 item: draft the Fig.-3 disk-surgery statement.

* `SquareDisk.lean` — **Layer A1/Layer B: square-disk transformations**
  (`Submission/SquareDisk.lean`, sorry-free, imported by Submission.lean).
  The relabelling/reparametrisation API of the spanning-square predicate
  `PathsBoundDiskInteriorFree K γ δ` of `SecantDisk.lean` that the Fig.-3
  disk surgery (Layer C) and the Dehn-lemma bridge (Layer B) will consume.
  `pathReparam γ φ hφ0 hφ1` + `pathReparam_apply`: the path `γ∘φ` for a
  continuous endpoint-fixing `φ : I → I`.  **`swap_edges`**: reflecting the
  square `(s,t) ↦ D(s, 1−t)` across the horizontal axis swaps the two
  boundary arcs — `PathsBoundDiskInteriorFree K δ γ` from
  `PathsBoundDiskInteriorFree K γ δ` (pinned sides and interior-off-`K`
  preserved; with the existing vertical reflection `_rev` this gives all
  four relabellings of the pair of arcs).  **`reparam`**: precomposing the
  square with `(φ, id)` reparametrises *both* arcs simultaneously —
  `PathsBoundDiskInteriorFree K (γ∘φ) (δ∘φ)` whenever `φ` fixes the
  endpoints and maps the interior of `I` into itself (exactly the two
  conditions that keep the sides pinned and the interior off `K`).
  `IsKnotArcPath_reparam`: reparametrising a simple knot path by an
  injective endpoint-fixing `φ` keeps it a simple knot path.

* `ChordFamily.lean` — **Layer A1/Layer-B interface: the chord-family disk
  over a band arc** (`Submission/ChordFamily.lean`, 138 lines, sorry-free,
  imported by Submission.lean).  Supporting object (1) of the D3 dependency
  list, with its precise statement pinned: `BandArcData` (a band arc in
  parameter-branch form: continuous `a b : I → AddCircle period` — the two
  ordered endpoint branches of the secant-class family — collapsing at the
  ends to single parameters `a 0 = b 0`, `a 1 = b 1` (the arc's endpoints on
  the diagonal boundary of the band) and staying distinct in the interior
  (`offdiag`)); `chordFamilyDisk r d : I × I → Space` (at secant parameter
  `s` the straight chord from `knotMap r (d.a s)` to `knotMap r (d.b s)`
  swept by `t` — the disk over the arc), continuous
  (`continuous_chordFamilyDisk`), with the boundary conditions proved as
  edge lemmas (`chordFamilyDisk_t0/_t1`: the two horizontal edges are the
  two endpoint branches of the arc on the knot; `chordFamilyDisk_s0/_s1`:
  the vertical edges are degenerate knot points — so the square's boundary
  loop is the knot itself), and the interior condition
  `chordFamilyDisk_mem_openSegment` (every interior disk point lies
  *strictly inside* its chord — the mechanism by which "the arc avoids `O`"
  yields "the disk interior avoids `K`").  **The `O`-avoidance corollary
  done**: `not_HasMiddleOnClass_iff_no_middle_rep` (glue: no strict middle
  on the representative ⇔ class ∉ `O`, via `HasMiddleOnClass_iff` +
  `not_congr`), and the contrapositive falling out:
  `chordFamilyDisk_interior_avoids_knot` (no strict-middle class on any
  interior parameter ⇒ interior disk points are not knot points) and its
  class-level phrasing `chordFamilyDisk_interior_avoids_knot_of_avoids_O`
  (the arc avoids `trisecantSet` ⇒ interior avoids `K` — Kuperberg's "the
  family of secants over an arc `A` avoiding `O` induces a disk whose
  interior does not intersect `K`").  **Band-arc interface glue (S70)**:
  `arcClosedClass d : I → UnordCirclePairs` (the unordered-class family
  `{a s, b s}` in the closed band; continuous), its ends on the diagonal
  boundary (`arcClosedClass_zero/_one` = `diagClass (d.a 0/1)`) and
  interior classes off the diagonal (`arcClosedClass_ne_diag`);
  `arcOpenClass d hs0 hs1 : OpenMobius` (interior classes in the open band,
  `arcOpenClass_val`); the provisional **`BandArc`** record (continuous
  path in the closed band with diagonal endpoints and open-band interior —
  the shape the Layer-C dichotomy supplies) and **`BandArcData.toBandArc`**
  (every `BandArcData` satisfies the band-arc obligations).  The reverse
  glue (band arc ⇒ branch functions) is the covering lift over the
  interior (`mobiusCover` is a covering map), documented as the next
  interface piece.  **Endpoint-collapse fibre geometry (S72)** — step 3 of
  the reverse glue, independent of the path-lift:
  `coords_mem_of_class_mem_image` (class `{x,y}` in the image of `W ×ˢ W`
  under the class map forces both coordinates into `W` — same-class pairs
  are equal or swapped), `coords_tendsto_of_class_tendsto_diag` (class
  family → `diagClass u` along a filter forces both coordinate families →
  `u`; the class map is open by `isOpenMap_unordClass`), and
  `coords_eq_of_class_eq_diag` (exactly-diagonal classes have collapsed
  coordinates).  **Step-4a collapse of an interior lift (S73)**: with
  `ParamInterior` (interior times) and the one-sided filters
  `interiorFilterLeft`/`interiorFilterRight` (subspace neighbourhoods of
  `0 : I` / `1 : I`, automatically one-sided),
  `interiorLift_coords_tendsto_left`/`_right` — a continuous interior lift
  `a₀ b₀` whose class equals the band arc `A` has its coordinates tending
  to the diagonal parameter `u` (resp. `v`) as the interior time approaches
  the arc's left (resp. right) end.
  **Step-4b closed-interval extension (S74)**: with `ParamInteriorSet`
  (the interior as an open subset of `I`), the extension
  `extendInterior u v f : I → AddCircle period` (equal to `f` on the
  interior, `u` at `0`, `v` at `1`) is continuous whenever `f` is
  continuous and has the endpoint limits `u` (left) and `v` (right):
  `continuous_extendInterior` (neighbourhood-form limits) and
  `continuous_extendInterior_of_tendsto` (the `Tendsto` form along
  `interiorFilterLeft`/`interiorFilterRight`, exactly the shape produced by
  step 4a) — continuity at interior points transfers through the open
  interior; at the endpoints the limit neighbourhood is intersected with a
  one-sided neighbourhood inside `I`.
  **Band-arc lifting complete (S75) — `BandArcData` from a class family**:
  `paramInteriorToIoo` (re-embedding of `ParamInterior` into the open unit
  interval `(0,1) ⊆ ℝ`, continuous), `openUnitClass A hopen` (the interior
  restriction of `A` as a continuous family in the *open* Möbius band),
  `continuous_openUnitClass`, `exists_lift_branch_family` (via the covering
  map `mobiusCover` and the fleet lemma
  `Commons.Topology.Covering.exists_liftOnIoo`: continuous interior branch
  functions `a₀ b₀` with `⟦(a₀ s, b₀ s)⟧ = A s` on `ParamInterior`, distinct
  there), and **`bandArc_lift`**: every class family `A` that is continuous,
  diagonal at the ends (`A 0 = diagClass u`, `A 1 = diagClass v`) and
  off-diagonal on the interior is realised by a `BandArcData` with endpoint
  values `u`,`v` and closed class family `= A` — steps 3–5 of the converse
  glue: the 4a collapse limits give endpoint `Tendsto` of the lift, step 4b
  extends each branch continuously with the endpoint values (`extendInterior
  u v a₀`/`b₀`), and the pieces assemble into `BandArcData` (the class
  agreement on the interior is the lift property, at the ends the diagonal
  values).  Together with `BandArcData.toBandArc`, `BandArc`/`BandArcData`
  are now mutually inverse interface objects.
* `BandDisk.lean` — **the chord-family disk over a band arc, packaged as a
  spanning square** (`Submission/BandDisk.lean`, 90 lines, sorry-free,
  imported by Submission.lean).  `bandArcPathA h d` / `bandArcPathB h d`
  (the two knot arcs traced by the `a`/`b` branches of a `BandArcData`,
  paths on the knot image between the collapsed endpoints), and
  **`bandArcDisk_bounds`**: if the arc avoids the trisecant set `O` at
  every interior parameter (`mobiusCover ⟨(a s, b s), offdiag⟩ ∉
  trisecantSet r`), then `chordFamilyDisk r d` realises
  `PathsBoundDiskInteriorFree (range (knotMap r)) (bandArcPathA h d)
  (bandArcPathB h d)` — bottom/top edges the two knot arcs, vertical edges
  pinned at the collapsed endpoint knot points, interior of the square
  mapped outside the knot (the `O`-avoidance corollary).  Combined with
  `ChordFamily.bandArc_lift`, any band-arc class family avoiding `O` yields
  the spanning disk between its two knot arcs — the object Layer B's
  Dehn-lemma bridge consumes.
  **`classBandArc_disk_bounds` (S77)** — the same at class-family level: a
  continuous `A : I → UnordCirclePairs` (diagonal ends `u`,`v`,
  off-diagonal and `O`-avoiding interior) realises a `BandArcData` (via
  `bandArc_lift`) and hence two knot arcs `γ δ : Path (knotMap u)
  (knotMap v)` bounding a disk whose interior avoids the knot
  (`PathsBoundDiskInteriorFree (range (knotMap r)) γ δ`): the full
  chord-family disk construction in class-level form.

* `BandArcCover.lean` — **Layer B, first half (S282, VERIFIED): the
  NON-SEPARATING band arc sweeps the knot** (`Submission/BandArcCover.lean`,
  sorry-free, warning-free; imports `BandDisk`).  `BandArcNonSeparating d`
  (a choice-free `∃`-form: continuous real lifts `ta`, `tb` of the two
  branches with `ta 0 = tb 0` and `tb 1 = ta 1 + period` — the two branches
  together travel once around the knot, i.e. the boundary loop of the
  chord-family disk is a generator of `π₁` of the knot, and equivalently
  Kuperberg's "non-separating arc of `M`");
  **`bandArcNonSeparating_covers`**: the two branches of a non-separating
  arc cover the whole knot, `range (K ∘ a) ∪ range (K ∘ b) = range K` (each
  real lift has an interval range — `IsPreconnected.ordConnected` — so the
  two ranges contain the full period window `Icc (ta 1) (ta 1 + period)`,
  and every class has a representative there by `AddCircle.eq_coe_Ico`);
  **`bandArc_spanningDisk`**: a non-separating arc avoiding `O` yields the
  two knot paths `bandArcPathA`/`bandArcPathB` bounding a disk whose
  interior avoids the knot AND whose arcs cover the knot — Kuperberg's "map
  from the unit disk to `ℝ³` whose boundary is `K`".  Two PINS (as
  `def Prop`, no `sorry`): **`NonSeparatingArcAvoidingO r`** (brick (d): a
  quadrisecant-free knot in general position has such an arc — Kuperberg's
  "elementary homology theory" obstruction step, vacuous since S280/S281
  make every circular component of `O` null-homotopic) and
  **`SpanningDisk_implies_IsUnknotted`** (Layer B: the
  Dehn-lemma/Alexander-trick bridge, the largest single missing piece); and
  **`isUnknotted_of_nonSeparatingArc`** — granting that pin, a single
  non-separating band arc avoiding `O` makes the knot unknotted (the exact
  shape in which the brick-(d) avoidance statement feeds Layer B).

* `StripCrosscut.lean` — **brick (d): the strip-crosscut interface (S284,
  VERIFIED, sorry-free, warning-free)**: `stripSecantClass p` is the secant
  class of a point `p = (x, y)` of the strip `ℝ × (0, period)` — the unordered
  pair `{x, x + y}` of knot parameters, i.e. the covering map from the
  *universal cover* of the band of secants (`M = OpenMobius`) in the
  coordinates in which the two boundary edges are `y = 0` and `y = period`;
  `liftedTrisecant r` is the preimage of Kuperberg's `O = trisecantSet r`
  under it; and **`bandArcData_of_stripCrosscut`** is THE REDUCTION: a
  continuous path of the closed strip from the bottom edge to the top edge
  (`(γ 0).2 = 0`, `(γ 1).2 = period`) whose interior lies in the open strip
  and avoids `liftedTrisecant r` *is* a non-separating band arc avoiding `O`
  (branches `a s = (γ s).1`, `b s = (γ s).1 + (γ s).2`; real lifts
  `ta s = (γ s).1`, `tb s = (γ s).1 + (γ s).2` exhibit
  `tb 1 = ta 1 + period`).  The residual two-dimensional statement is pinned
  as **`StripCrosscutAvoidingO r`** (`def Prop`), with
  **`nonSeparatingArcAvoidingO_of_stripCrosscut`**: it implies
  `NonSeparatingArcAvoidingO r`.  The companion commons lemma is
  `Commons.Topology.Strip.strip_crosscut_of_bounded_components` (closed
  `F ⊆ ℝ × (0, period)` with components bounded in `x` and finitely many
  points on each vertical line admits such a crosscut); applied to
  `liftedTrisecant r` it closes brick (d).  Key sub-lemma here:
  `coe_ne_coe_of_lt` (a parameter length strictly between `0` and `period`
  gives distinct parameter classes).

* `AnalyticUnknot.lean` — **Layer B, explicit-formula case (S284, VERIFIED,
  sorry-free, warning-free)**: vertical graphs over the round circle are
  unknotted.  Because `ContDiff ℝ ⊤` is analyticity (see the header warning),
  a Layer-B isotopy has to be *one formula* (no cutoff gluing).  A curve of
  the form `t ↦ standardCircle t + γ t • e₃` (`e₃ = !₂[0,0,1]`, `γ : ℝ → ℝ`)
  is a *vertical graph over the round circle*; if `γ` is analytic and
  `period`-periodic it is a smooth knot
  (`isSmoothKnot_verticalGraph`), and it is unknotted
  (`isUnknotted_of_verticalGraph`) via the completely explicit height
  interpolation `R t s = standardCircle t + ((1 − s) · γ t) • e₃`, analytic
  in `(t,s)` (`contDiff_verticalGraphFamily`) with every slice again a smooth
  knot (`isSmoothKnot_verticalGraph_slice`).  The supporting lemmas are the
  explicit derivative `deriv_verticalGraph` (the `xy`-part is the unit
  tangent of the round circle) and the resulting regularity
  `velocity_verticalGraph_ne_zero`; injectivity on a period
  (`injOn_verticalGraph`) comes from the `xy`-projection being the round
  circle.  `isUnknotted_of_verticalGraph_of_isSmoothKnot` is the form in
  which the trisecant geometry can feed it (the periodicity of the height is
  derived from `IsSmoothKnot r`).  This is the shape Kuperberg's §1 trivial
  case takes once an avoiding spanning disk is a graph over the round circle:
  no Dehn/Schoenflies input.  **The CYLINDRICAL (star-shaped) case (S287,
  VERIFIED)**: a curve `t ↦ (a t · cos t, a t · sin t, b t)` — radius `a > 0`
  and height `b` both varying — is unknotted
  (`isUnknotted_of_cylindricalGraph`) by the single formula
  `R t s = ((1−s)·a t + s)·(cos t, sin t) + (1−s)·b t · e₃`, with
  `isSmoothKnot_cylGraphSlice` (the slices are knots: `injOn_cylGraphSlice`
  via the `xy`-projection being the radial graph, and
  `velocity_cylGraphSlice_ne_zero` via the velocity's `xy`-part having squared
  norm `c'² + c² ≥ c² > 0` with `c = (1−s)·a t + s`),
  `contDiff_cylGraphFamily`, and the helpers `vec3_decomp` / `contDiff_vec3`
  and the coordinate vectors `e1`, `e2`.  This is the shape a *star-shaped*
  spanning disk (the cone from a point of the axis) produces.

* `RadialArc.lean` — **the radial (cone) band arc: Kuperberg's trivial case
  (S283, VERIFIED)** (`Submission/RadialArc.lean`, sorry-free, warning-free;
  imports `BandArcCover` + `TrisecantLocus`).  `NoTrisecantThrough r u` (the
  knot point `K(u)` lies on no trisecant: `∀ b z, ¬ IsMiddleOnChord r u b z`);
  `radialLift`/`radialArcA`/`radialArcB`/`radialArcData` (the radial arc at
  `u`: fixed branch `≡ u`, moving branch `s ↦ u₀ + s·period` sweeping the
  circle once); **`radialArcData_nonSeparating`** (the fixed branch lifts
  constantly to `u₀`, the moving branch to `u₀ + s·period`: exactly one
  period gained — the two branches sweep the knot);
  **`radialArcData_avoids`** (if `K(u)` carries no trisecant the radial arc
  avoids `O`); **`radialArc_spanningDisk`**: a knot point carrying no
  trisecant spans a disk whose interior avoids the knot and whose boundary
  arcs cover the whole knot (Kuperberg §1: "the union of the chords `p̄q̄`
  for all `q` in `K` is evidently a smooth embedded disk with boundary `K`,
  which renders `K` trivial").  Plus **`isUnknotted_of_noTrisecant`** —
  Kuperberg's §1 theorem modulo the Layer-B pin: granting
  `SpanningDisk_implies_IsUnknotted`, a smooth knot with a trisecant-free
  point is unknotted.

* `CollinearityMap.lean` — **Layer A (vi): the collinearity-map scaffold
  (real parameters)**.  The smooth map whose zero set (away from the
  diagonals) is the strict-trisecant locus with middle point attached:
  `cross3` (cross product on `Space`, transported from Mathlib's `⨯₃` via
  the `WithLp` equivalence; antisymmetry, self-zero, zero-vector and
  bilinearity identities, `cross3_collinear_zero`), and
  `collinearityMap r (a,b,m) = (r a − r b) × (r a − r m)` with the flat form
  `collinearityValue`.  **Smoothness**: `contDiff_collinearityMap` —
  `ContDiff ℝ ⊤` (hence `C¹`: `contDiff_one_collinearityMap`,
  `contDiffOn_collinearityMap`), via the fleet commons lemma
  `Commons.Analysis.Calculus.ContDiff.crossProduct` applied to the two
  smooth difference maps.  Degenerate triples lie in the zero set
  (`collinearity_diag_ab/am/bm`) and the map is `period`-periodic in each
  argument (`periodic_collinearity_arg1/2/3`) — it descends to the
  parameter torus.  **Partial derivatives (added):** the three hinges of the
  transversality engine, via the fleet-proven Leibniz rule
  `Commons.Analysis.CrossProduct.hasDerivAt_cross3`
  (wrapper `hasDerivAt_cross3_curves`):
  `∂/∂b Φ(a,b,m) = (r a − r m) × v(b)` (`hasDerivAt_collinearity_middle`),
  `∂/∂a Φ(a,b,m) = v(a) × (r a − r m) + (r a − r b) × v(a)`
  (`hasDerivAt_collinearity_first`), and
  `∂/∂m Φ(a,b,m) = v(m) × (r a − r b)` (`hasDerivAt_collinearity_third`),
  where `v(t) = velocity r t`; plus the small cross identities
  (`cross3_add_right`, `cross3_neg_left/right`, `cross3_neg_left_swap`) and
  `hasDerivAt_velocity` (regularity gives differentiability at every
  parameter).  The rank/regular-value (transversality) analysis of `Φ` on
  its zero set — the engine for the self-transverse-immersion structure of
  `O` under genericity — is the next layer.

* `Transversality.lean` — **Layer A (vii): the rank / regular-value
  criterion (provable core + precise target)**.  The three hinge partials
  as named objects `collPartialA/B/M` (`collPartial : Fin 3 → Space`) and
  their span `collPartialSpan` (the range of the assembled directional
  derivative of `Φ`); the operative rank-two criterion `PartialRankTwo`
  (two partials linearly independent — the regular-value hypothesis making
  `Φ⁻¹(0)` a smooth curve).  **Easy direction proved**:
  `not_PartialRankTwo_of_collPartialOnLine` — if the three partials lie on a
  common line (`collPartialOnLine`) no two are independent (via
  `linearDependent_pair_of_mem_span_singleton`).  **Orthogonality to the
  chord**: the cross product is ⟂ both factors (`inner_cross3_self_right`
  derived from the commons `inner_cross3_self_left`), so `∂_b ⟂ r a − r m`
  unconditionally (`inner_partialB_chord`) and `∂_a`, `∂_m` are ⟂ the chord
  once the chord vectors are parallel
  (`inner_partialA_chord_of_parallel`, `inner_partialM_chord_of_parallel`,
  `partials_orthogonal_chord_of_parallel`) — the derivative range then lies
  in the chord-perpendicular plane.  **Converse data (added)**: with the
  committed commons `cross3_eq_zero_iff_smul`, a zero of `Φ` with nonzero
  first chord vector forces chord parallelism
  (`chord_parallel_of_collinearity_eq_zero`) and the partials factor as
  nonzero multiples of `v(·) × (r a − r b)`
  (`collPartialA/B/M_eq_smul`) — reducing rank two to independence of two
  velocity-cross vectors.  **Rank-two criterion proved**:
  `PartialRankTwo_iff_velocityCross_pair` — under `Φ = 0`, `t ∉ {0,1}`,
  the derivative has rank two iff two of `v(p_i) × (r a − r b)` are
  independent (via the commons `linearIndependent_pair_smul` and the
  `collParam`/`collCoeff`/`collPartial_eq_coeff` glue).

* `TrisecantCurve.lean` — **Milestone 1: the local smooth-curve structure
  of `Φ⁻¹(0)` (statement + vocabulary)**.  Precise target recorded
  (`TrisecantLocalCurve`, `LocalSmoothCurveTheorem`): at a collinear
  off-diagonal real triple where the knot is in general position
  (`TrisecantGeneralPosition` = pairwise-distinct images + `PartialRankTwo`),
  a neighbourhood of the off-diagonal zero set of `Φ` is the injective `C¹`
  image of a curve through the triple.  Proved: the genericity predicate in
  its geometric form — under `Φ = 0`,
  `generalPosition_iff_velocityCrossGeneralPosition`
  (`TrisecantGeneralPosition ⟺ off-diagonal ∧ ∃ i≠j, two velocity-cross
  vectors `v(pᵢ) × Z` independent`), chaining the rank-two criterion.  The
  IFT/constant-rank proof of `LocalSmoothCurveTheorem` is the recorded
  frontier.  **Step-2(a) (submersion datum) is done**: the reduced map
  `H(q) = (⟨Φ q, P_A⟩, ⟨Φ q, P_B⟩) : ℝ³ → ℝ²` (partials frozen at the base
  triple) is smooth (`contDiff_collinearityInnerPair`); its axis-curve
  derivatives (`hasDerivAt_collinearity_a_axis`/`_b_axis`,
  `hasDerivAt_reduced_a_axis`/`_b_axis`) give the two Gram-column values;
  the generic bridge `fderiv_along_axis_eq_deriv` (affine-line derivative
  `(fderiv H p) e`) identifies those columns with `fderiv H p` applied to
  the two coordinate directions (`fderiv_reduced_a_col`/`_b_col`, via
  `HasDerivAt.unique`); independence of `P_A, P_B` makes the Gram matrix
  invertible and hence the two columns independent vectors of `ℝ²`
  (`linearIndependent_pair_prod_of_det_ne_zero`, 2×2 determinant
  criterion), so the fleet lemma
  `surjective_of_two_independent_in_range` gives
  **`reducedMap_fderiv_range_top`**: `range (fderiv H p) = ⊤` — `H` is a
  submersion at the general-position triple (the IFT input).  **Step 3
  (identification `Φ⁻¹(0) = H⁻¹(0)` near a rank-two zero) is DONE** —
  `identification_of_reduced_zero`: at a zero of `Φ` with `Z = r a − r b ≠ 0`
  and `P_A, P_B` independent, on an open neighbourhood `U` of the triple,
  `H(q) = 0 ⇒ Φ(q) = 0`.  Ingredients proved in-module: `Φ(q) ⊥ chord(q)`
  for every triple (`collinearityMap_orth_chord`, the cross product);
  `P_A, P_B ⊥ Z` from the collinear factorisation
  (`collPartialA_orth_chord`/`_B_orth_chord`, via the Transversality
  factorisations + commons `inner_cross3_self_left`); a nonzero vector
  orthogonal to two generators is outside their span (`chord_not_mem_span_
  of_orth` — generic inner-product-space lemma, no independence needed);
  `Z ∉ span{P_A,P_B}` persists to `chord(q) ∉ span{P_A,P_B}` on an open
  `U` (chord moves continuously, finite-dimensional subspaces are closed);
  three independent vectors in 3-dimensional `Space` span `⊤`
  (`finrank_Space` + commons `span_top_of_three_independent`), so
  `Φ(q) ⊥ {P_A, P_B, chord(q)}` (spanning) forces `Φ(q) = 0` (commons
  `eq_zero_of_inner_eq_zero_of_span_top`).

* `LocalCurve.lean` — **Milestone 1 PROVED: `LocalSmoothCurveTheorem`
  (`smooth_local_curve_of_general_position`)** — at every general-position
  collinear off-diagonal triple of a smooth knot, the off-diagonal zero set
  of `Φ` is locally the image of an injective `C¹` curve through the triple
  (`TrisecantLocalCurve`).  Content: (i) the missing `m`-axis derivative
  lemma (`hasDerivAt_collinearity_m_axis`); (ii) the *indexed* reduced map
  `pairReduced r a b m i j q = (⟨Φ q, ∂ᵢ⟩, ⟨Φ q, ∂ⱼ⟩)` with its smoothness
  (`contDiff_pairReduced`), generic axis-column lemma (`fderiv_pairReduced_
  axis`: the derivative along the axis of index `k` is the Gram column
  `(⟨∂_k, ∂_i⟩, ⟨∂_k, ∂_j⟩)`), generic surjectivity
  (`pairReduced_fderiv_range_top`: the pair-reduced map is a submersion at
  the triple when the pair of partials is independent), generic
  orthogonality of every partial to the chord (`collPartial_orth_chord_
  index`) and the generic Step-3 identification
  (`identification_pairReduced_zero`: `H_{ij}(q) = 0 ⇒ Φ(q) = 0` near the
  triple for any independent pair); (iii) the **split-coordinate curve
  assembly** `trisecantLocalCurve_of_splitData` — a single proof that
  packages the product-domain implicit function theorem
  (`Commons...implicitFunction_graph`, Mathlib `ContDiffAt.implicitFunction`,
  which is `C¹` on a neighbourhood by `ContDiffAt.contDiffOn`) together with
  all the interval/neighbourhood bookkeeping: given a smooth reduced map
  that vanishes at `p`, is a submersion along the second factor of a split
  `E = E₁ × E₂` (`E₂`-partial derivative invertible), identifies its zero
  set with `Φ⁻¹(0)` near `p` and respects collinearity, it produces the
  `C¹` injective curve over an interval through `p` covering the whole
  neighbourhood of off-diagonal zeros; (iv) the three general-position pair
  instances `localSmoothCurve_AB`/`_AM`/`_BM` (graph over the remaining
  coordinate `m`/`b`/`a`; Gram columns via the axis lemmas and
  `Commons...isInvertible_of_det_columns`, identification via the pair
  theorems); and (v) the case analysis over the `PartialRankTwo` witness
  (`smooth_local_curve_of_general_position`, with the pair-swap lemma
  `linearIndependent_pair_swap_iff`), completing Milestone 1.

* `TorusCollinearity.lean` — **Layer A (viii): Milestone 1 lifted to the
  parameter torus** (`Submission/TorusCollinearity.lean`, sorry-free,
  imported by Submission.lean).  The knot is a circle, so the collinearity
  data live on `T³ = KnotParamTriple`; this module builds the torus avatar
  of the Milestone-1 curve analysis.  Content: (i) the circle-level knot:
  `knotMap_eq_r` (`knotMap r` applied to the class of `x` equals `r x` for
  *every* real `x`, via the periodicity of `r` and the
  `AddSubgroup.zmultiples` congruence machinery `r_eq_of_coe_eq`); (ii)
  the **torus-level collinearity map**
  `torusCollinearity r (a,b,m) = (K a − K b) × (K a − K m)`, `K = knotMap r`,
  with the **bridge** `torusCollinearity_quotient` (`torusCollinearity r
  (π₃ w) = collinearityMap r w` for every real triple `w` — same
  collinearity information), continuity (`continuous_torusCollinearity`),
  closedness and **compactness** of the zero set
  (`isClosed_torusCollinearityZero`, `isCompact_torusCollinearityZero`),
  via the coordinate-wise period-quotient map `torusQuotient : ℝ³ → T³`
  (open and continuous: `isOpenMap_torusQuotient` — product of the open
  quotient maps `ℝ → AddCircle period`); (iii) the **strict trisecant data
  live in the zero set**: `openMiddleData_subset_collinearity_zero`
  (strict betweenness forces the cross product to vanish,
  `mem_openSegment_cross3`) and
  `openMiddleData_offDiag_of_endpoints_ne` (a strict middle with distinct
  chord endpoints gives three pairwise distinct knot points), with the
  compactness corollary `isCompact_closure_openMiddleData`; (iv) the
  **quotient is a local injection on fundamental boxes**: `coe_injOn_Ioo`
  (the period quotient is injective on any interval of width `< period`,
  via `abs_zsmul_lt_of_lt`) and `torusQuotient_injOn_box`/`FundBox`
  (product version); (v) **the torus local structure theorem**
  `torus_local_structure_of_general_position` (+ packaged
  `torus_local_structure_of_general_position_all` under the
  `TorusGeneralPosition` hypothesis): at a collinear off-diagonal torus
  triple `p ∈ T³` whose fundamental-domain representatives are in general
  position, there is a continuous curve in `T³` through `p`, contained in
  the zero/off-diagonal locus, which covers every torus-level off-diagonal
  zero in a torus neighbourhood `V` of `p` (covering via the bridge lemma
  against Milestone 1's real covering inside `W = U ∩ FundBox`) and is
  injective on a subinterval around `0` (injectivity via the box
  injectivity of the quotient).  This is the local embedded-arc structure
  of the torus trisecant locus that the global 1-manifold theory of `O`
  (Layer A, structure theorem) will glue together.

* `TorusCharts.lean` — **Layer A (ix): local arc charts of the trisecant
  locus and their overlap — the first gluing lemma**
  (`Submission/TorusCharts.lean`, sorry-free, imported by Submission.lean).
  Packages the existential torus structure data of the previous module into
  a chart record `TorusArcData r p` (neighbourhood `V` ∋ `p`, curve `γ`
  over `(lo,hi)` covering `V`'s trisecant zeros, injective sub-arc over
  `(lo',hi')` inside `V`); producing lemmas
  `exists_torusArcData_of_general_position(_all)` (Prop) and the
  `Classical.choice`-based `torusArcData_of_general_position(_all)`.
  Content: (i) **the zero set is traced by the arc** —
  `arcRange_eq_zeroSet_of_subset`: for any `W ⊆ V`, the trisecant zeros in
  `W` are exactly the curve points in `W` (arc stays in the zero set;
  covering puts every zero of `W` on the curve); (ii) **embedded local
  arcs** — `embedded_local_arc` (around `p` the zero set contains an
  injective continuous image of an interval through `p`, inside `V`),
  `TorusArcData.subarc_within` (refine the injective sub-arc into any
  pre-assigned open neighbourhood) and `TorusArcData.refine_within`
  (a refined chart with neighbourhood inside the pre-assigned one);
  (iii) **the overlap (first gluing) lemma** — `torus_arc_overlap`: two
  charts at the same base point `p` agree on their overlap
  `W = V₁ ∩ V₂`: both curves trace out exactly the same portion of the
  trisecant zero set (`arcRange γ₁ ∩ W = arcRange γ₂ ∩ W =
  trisecantZeroSet r ∩ W`), i.e. the two local families of trisecants
  describe the same object up to the torus quotient and their
  parameterisations; `torus_arc_agreement_on_common_subset` is the
  germ-level formulation used when gluing charts along overlaps.  (Not yet
  claimed: a single interval-parametrisation injective over a whole open
  zero-set neighbourhood — needs the implicit-function *graph* coordinates
  of the local curve; documented in the module header as the next stage of
  the 1-manifold theory).

* `TorusChartGraph.lean` — **Layer A (x): graph coordinates of the local
  trisecant arc, and no re-entry** (`Submission/TorusChartGraph.lean`,
  sorry-free, imported by Submission.lean).  The real local curves of
  Milestone 1 come from the implicit function theorem in *graph form*
  (`LocalCurve.lean`, `trisecantLocalCurve_of_splitData`): with the split
  `E = E₁ × E₂`, `E₁ = ℝ`, the curve is `γ(x) = A(x, ψ(x))`, `ψ` the `C¹`
  implicit function over an `x`-interval, and the first split coordinate is
  a monotone curve coordinate.  The module bundles that data as the record
  `RealGraphArc r` and proves the two bridging statements:
  (1) **graph-coordinate lemma** — `RealGraphArc.graph_coordinate` and
  `coord_along_t`: `(B(γ(x))).1 = x`, the map is injective on `(a,b)` (each
  `x`-slice meets the arc at most once) and (reparametrised in `t`,
  `x(t) = u.1 + t`) the curve coordinate is affine/monotone along the arc;
  (2) **no-re-entry / trace lemma** — `RealGraphArc.trace_eq_zeroSet_of_box`
  (`γ '' [α,β]` equals the whole off-diagonal collinearity zero set inside
  the graph-adapted box `{(B q).1 ∈ [α,β] ∧ B q ∈ W}` — the arc does not
  re-enter such a box; its trace is the whole local zero set there) and
  `RealGraphArc.arcHomeo` + `image_arc_isClosed` +
  `arc_closed_embedding` (the arc over `[α,β]` is a homeomorphism onto its
  compact, hence closed, image, with explicit continuous inverse
  `q ↦ (B q).1`).  These are the graph-coordinate/no-re-entry ingredients
  from which the honest charts (interval-parametrisation injective over an
  open zero-set neighbourhood) and the global 1-manifold atlas of `O` will
  be assembled; instantiating `RealGraphArc` at general-position triples
  (via the three split instances of `LocalCurve.lean`) is the next step.

* `TorusGraphInstances.lean` — **Layer A (xi): instantiating the graph arc
  at the general-position triples** (`Submission/TorusGraphInstances.lean`,
  sorry-free, imported by Submission.lean).  Fills the `RealGraphArc` record
  at every collinear off-diagonal real triple `(a,b,m)` of a smooth knot for
  the three rank-two witness pairs:
  * `(A,B)` — `exists_realGraphArc_AB` (Prop, `Nonempty`) and
    `realGraphArc_AB`: graph over the `m`-coordinate with the `splitAB`
    split;
  * `(A,M)` — `exists_realGraphArc_AM` and `realGraphArc_AM`: graph over
    the `b`-coordinate with the `splitAM` split;
  * `(B,M)` — `exists_realGraphArc_BM` and `realGraphArc_BM`: graph over
    the `a`-coordinate with the identity split `splitBM`.
  All three witnesses are sorry-free and verified by external API tests.
  The proofs re-derive, from `LocalCurve.lean`'s input data, the
  pair-reduced map `red = pairReduced r a b m i j` (indices `(0,1)` /
  `(0,2)`) with its invertible second-factor partial derivative (the Gram
  matrix of the independent pair) and the zero-set identification, run the
  product-domain implicit function theorem
  (`Commons...implicitFunction_graph`) with the matching split, and select a
  small `x`-interval `(a₁,b₁) ∋ u.1` on which the graph
  `γ(x) = split · (x, ψ(x))` lies in the collinear off-diagonal zero set and
  inside the `ψ`-covering neighbourhood `W`; the `RealGraphArc` record
  fields are filled one by one (`graph_coordinate`, `coord_along_t`,
  `trace_eq_zeroSet_of_box`, `arcHomeo`, `arc_closed_embedding` then apply
  to every instance).

* `TorusChartLift.lean` — **Layer A (xii): the torus-quotient lift of the
  `(A,B)` graph arc — an honest chart** (`Submission/TorusChartLift.lean`,
  sorry-free, imported by Submission.lean).  The real graph witnesses lift
  through the period quotient `torusQuotient : ℝ³ → T³` to a *single*
  interval parametrisation that is **injective over the whole interval** and
  covers an open torus neighbourhood of the base point
  `torusQuotient (a,(b,m))`:
  * `RealGraphArc.g_coord3_AB` — for the `(A,B)` split the graph coordinate
    is the third parameter: `(γ(x)).2.2 = x`;
  * `injOn_torusQuotient_g_of_graphCoord` — two torus-equal graph points
    force `x ≡ x′ (mod period)`, so on an interval of width `< period`
    (`coe_injOn_Ioo`) the parameters agree: quotient injectivity is *free*
    from the graph form (the improvement over `TorusCharts.lean`, whose
    opaque curves were only injective on a subinterval);
  * **`torus_chart_lift_AB`** — the chart theorem: given `d : RealGraphArc r`
    carrying the `(A,B)` split identities (`d.B = unSplitAB`,
    `d.A = splitAB`, `d.u = (m,(a,b))`; existence via
    `exists_realGraphArc_AB_splitting`) and an interval half-width `δ` with
    `d.a < m−δ`, `m+δ < d.b`, `0 < δ`, `2δ < period`, there is an open torus
    neighbourhood `V ∋ torusQuotient(a,(b,m))` (the `π₃`-image of the real
    curve window `{(B q).1 ∈ (m−δ,m+δ)} ∩ B⁻¹'W`) and a continuous injective
    `γ(x) = π₃(γ_real(x))` on `(m−δ,m+δ)` with `γ m = torusQuotient(a,(b,m))`,
    image in the trisecant zero set inside `V`, covering every zero of `V`
    (the `RealGraphArc.cover` covering property transported by the bridge
    `torusCollinearity_quotient`/`TorusOffDiag_quotient_iff`).  This is the
    honest-chart statement the atlas will glue.
  The same theorem is ported to the other two witnesses:
  `torus_chart_lift_AM` (`exists_realGraphArc_AM_splitting`: split
  identities `d.B = unSplitAM ∧ d.A = splitAM ∧ d.u = (b,(a,m))`; graph
  coordinate the *second* parameter — `RealGraphArc.g_coord2_AM`
  `(γ(x)).2.1 = x`, interval centred at `u.1 = b`) and `torus_chart_lift_BM`
  (`exists_realGraphArc_BM_splitting`: split identities
  `d.B = unSplitBM ∧ d.A = splitBM ∧ d.u = (a,(b,m))`; graph coordinate the
  *first* parameter — `RealGraphArc.g_coord1_BM` `(γ(x)).1 = x`, interval
  centred at `u.1 = a`, with `injOn_torusQuotient_g_of_graphCoord1/2` the
  matching free quotient-injectivity variants).

* `Torus1Chart.lean` — **Layer A (xv): bundled 1-dimensional charts of
  the trisecant zero set** (`Submission/Torus1Chart.lean`, sorry-free,
  imported by Submission.lean).  The record `ZeroSet1Chart r p` bundles `V`
  (open, `p ∈ Z ∩ V`), an open interval `(lo,hi) ∋ x₀`, and a homeomorphism
  `(lo,hi) ≃ₜ {q | q ∈ trisecantZeroSet r ∧ q ∈ V}` sending `x₀ ↦ p` — the
  statement that the zero set is a 1-dimensional topological manifold at
  `p` (chart neighbourhood `Z ∩ V`, open in `Z`).  Per-witness
  constructors `zeroSet1Chart_AB/AM/BM` (split instance +
  `RealGraphArc.exists_small_delta` + `torus_chart_homeo_*`) and the cover
  theorem **`zeroSet1Chart_at_general_position`**: under
  `TorusGeneralPosition r` every `p ∈ trisecantZeroSet r` carries a
  `ZeroSet1Chart r p` (dispatch over the rank-two witness, as in
  `zeroSetChart_at_general_position`).  **Transition maps**: for two charts
  `c₁`, `c₂` the transition domain `ChartTransitionDomain c₁ c₂` (the
  parameters of `c₁` whose zero-set points lie in `c₂.V`), mutually inverse
  forward/backward maps `chartTransitionTo`/`chartTransitionBack`
  (value-level unfoldings `chartTransitionTo_val`/`chartTransitionBack_val`),
  their continuity, the bundled homeo `chartTransitionHomeo` of transition
  domains, and the transition lemma **`zeroSet1Chart_transition`**
  (∃-form) with the standalone point-preservation
  `chartTransition_preserves_point`
  (`(c₂.homeo (h x)).1 = (c₁.homeo x).1`).  **Single-chart lifts and
  overlap agreement**: `ZeroSetPoint r` (zero-set points), the
  **single-chart lift** `chartLift c : ChartInterval c.lo c.hi →
  ZeroSetPoint r` (value lemma `chartLift_val`, continuity
  `continuous_chartLift`), and the local coherence for path-following —
  **`chartLift_overlap`**: on the transition domain,
  `chartLift c₁ x.1 = chartLift c₂ (chartTransitionHomeo c₁ c₂ x)`, i.e.
  the two charts describe the same zero-set point in compatible
  coordinates.  Next: the global path-following construction glues these
  local lifts along chains of charts.

* `TorusPathFollow.lean` — **Layer A (xvi): path-following along the
  zero set — chart chains** (`Submission/TorusPathFollow.lean`, sorry-free,
  imported by Submission.lean).  The inductive **`ChartChain c`** (finite
  chain of bundled charts starting at `c`: `nil`, `cons c' tail`), the
  neighbourhood intersection `chartChainVs` (the `V`'s of the chain's
  charts — the domain condition "the point lies in every `V`"), the
  endpoint type `chartChainEnd` and the **composite overlap transport**
  `chartChainTransport` (successively moving a parameter through the
  transition homeos of the chain, ending at a parameter of the last chart
  with the same zero-set point).  Two-step coherence: value unfoldings
  `chartDirectParam_eq`/`chartTwoStepParam_eq` (both transports are
  `c.homeo.symm` applied to the zero-set point of the original parameter)
  and **`transport_twoStep_eq`**: transporting through a middle chart `b`
  and then on to `c` ends at the same parameter of `c` as the direct
  transport `a → c`; the lift-level corollary **`chartLift_twoStep`**.  The
  local associativity on which the whole chain construction hangs.  (Also
  `chartTransitionHomeo_apply`: the bundled transition homeo is on values
  the forward transition map.)

* `ZeroSetPath.lean` — **Layer A (xvii): path-following applications —
  parameters of zero-set points and path round trips**
  (`Submission/ZeroSetPath.lean`, sorry-free, imported by Submission.lean).
  `chartParam c z hV` — the parameter of a zero-set point `z` in chart `c`
  (`c.homeo.symm` of the point; requires the point in `c.V`), with the
  round trips `chartParam_spec` (chart homeo recovers the point),
  `chartParam_point` (torus value is `z`), `chartParam_lift` (`chartLift c
  (chartParam c z hV) = z`).  **Path round trips**: for a path `σ` in the
  zero set lying in the chart region(s), the lift of the lifted parameter
  path is the original path — `chartLift_path_roundTrip` (single chart)
  and `chartChain_path_roundTrip` (whole chain: the lift at the endpoint
  chart of the transported parameter of `σ t` equals `σ t`, via
  `chartChain_lift` + `chartParam_lift`); `continuous_chartParam_path`:
  the lifted parameter path is continuous.  **Junction consistency
  `chartParam_transition`**: for `z` in both `c₁.V` and `c₂.V`, the
  parameter of `z` in `c₂` is the transition-transport of its parameter in
  `c₁` (via chart-homeo injectivity) — the chart-boundary glue of
  path-following.  **Compact-interval chain lift** (S47): `CompactInterval
  a b`, `chainDomainParam` (the chain-domain element of `σ t`),
  `ChartChainLiftOnInterval` (the statement: a path over `[a,b]` in the
  zero set whose points lie in every chart region of a chain has a
  continuous parameter lift `τ : [a,b] → chartChainEnd` whose value is the
  composite transport and whose endpoint lift is `σ t`),
  `singleChart_pathLift` (base case), `ChartChainLiftOnInterval_nil`,
  `chartParam_junction_agree` (at a junction time the next-chart parameter
  is the transition-transport of the current one).  **One-step extension
  (cons)** (S58): `chartTransition_irrel_mem` (transition transport is
  insensitive to the membership proof), `chainDomainParam_cons_transport_eq`
  (transporting the chain-domain parameter of `σ t` along the extended
  chain `cons c c' tail` equals the tail transport of its parameter in
  `c'` — the single transition is `chartParam_transition`), and
  **`ChartChainLiftOnInterval_cons`**: a lift through `tail` from `c'`
  extends to a lift through `cons c c' tail` from `c` (same continuous
  `τ'`; the transport equality is the cons lemma) — the cons step of the
  induction over the chain (base `nil` + cons), which the adapted chain of
  `AdaptedChain.lean` instantiates.  **Full-chain induction** (S59):
  `ChartChainLiftOnInterval_chain` closes the recursion — for *any* finite
  chain, a path over `[a,b]` whose points lie in the first chart's region
  and in the corridor of every chart of the chain lifts continuously
  through the whole chain (induction over the chain; the cons step applies
  `ChartChainLiftOnInterval_cons` with the corridor memberships
  `h₁ t := (hch t).1`, `h₂ t := (hch t).2`, and the nil case is
  `ChartChainLiftOnInterval_nil`).

* `ZeroSetTopology.lean` — **Layer A (xxii) / Milestone-2 step (i):
  the zero set is a locally path-connected 1-manifold — component
  structure** (`Submission/ZeroSetTopology.lean`, sorry-free, imported by
  Submission.lean).  The first *global* consequences of the local 1-chart
  structure (`ZeroSet1Chart`): (1) **openness in the zero-set subspace**
  `zeroSet_open_iff` / `zeroSetChartDomain_open_iff` — the open subsets of
  `ZeroSetPoint r` (and of the chart domain `{q | q ∈ Z ∧ q ∈ V}`) are
  exactly the traces of torus-open sets; (2) **the chart-domain projection
  is open** `zeroSetChartProj` / `zeroSetChartProj_open` (dropping the
  `V`-membership: the chart domain is the trace of the torus-open `V` in
  the zero set, so its open subsets project to open subsets of the zero
  set — the image of `O` is `{z | (z:K) ∈ W ∩ V}` for the ambient open
  `W`); (3) **`zeroSet_local_pathConnected_nhds`** — inside every open
  neighbourhood `u` of a zero-set point `z` there is an *open
  path-connected* neighbourhood `U` of `z` (`U ⊆ u`): the chart `c` at
  `z`, an ε-ball inside the pullback of `u` through the chart homeo, and
  the image `U = chartLift c '' cell` of a small open parameter interval
  `cell` (open in the zero set by (2) + `Homeomorph.isOpen_image`;
  path-connected as the continuous image of an interval — with the helper
  `mem_ball_of_mem_Ioo` for the real interval/ball transfer and the
  open-embedding fact that the chart-interval projection `x ↦ (x : ℝ)` is
  an open embedding); (4) **`zeroSet_locallyPathConnected`** — under
  `TorusGeneralPosition r` the trisecant zero set is a
  `LocallyPathConnectedSpace` (constructed via `Filter.hasBasis_iff` from
  (3)); (5) **component structure** `zeroSet_component_open`,
  `zeroSet_component_pathConnected` and
  `zeroSet_component_eq_pathComponent`,
  `zeroSet_component_pathConnectedSpace`, and
  `zeroSet_open_isConnected_iff_isPathConnected` — the connected components
  of the zero set are open, path-connected (also as subspaces), are exactly
  the path components, and connected *open* subsets of the zero set are
  path-connected (the `LocallyConnectedSpace`/
  `pathComponent_eq_connectedComponent`/
  `IsOpen.isConnected_iff_isPathConnected` corollaries).  This is the first global claim of Milestone 2: *the
  trisecant zero set of a general-position smooth knot is a locally
  path-connected space whose connected components are open path-connected
  pieces* — the substrate on which the component/path-following machinery
  (`TorusPathFollow`/`ZeroSetPath`/`CompactCover`) and the later
  circle/interval classification of the components operate.

* `StrictZero.lean` — **Layer A (xxiii) / Milestone-2 step (ii),
  dependency 1: quantitative chord betweenness and the openness of the
  strict trisecant data** (`Submission/StrictZero.lean`, 413 lines,
  sorry-free, warning-free, imported by Submission.lean).  The quantitative
  engine behind "strictly between" that the projection `strict data → O`
  (the local 1-manifold structure of `O`) needs:
  - **`chordCoeff`** — the Gram coefficient of `knotMap m` along the chord
    from `knotMap a` to `knotMap b` (inner product over squared chord
    length), with the Gram identity `inner_sub_chordCoeff`;
  - **`middle_parallel_of_torusCollinearity`** — at a collinear triple with
    distinct endpoints `knotMap m − knotMap a = chordCoeff q • (knotMap b −
    knotMap a)` (cross-product dependence factorisation with the explicit
    coefficient);
  - **betweenness criteria** `strict_iff_chordCoeff_mem_Ioo` /
    `closed_iff_chordCoeff_mem_Icc`: with collinearity and distinct chord
    endpoints, strict betweenness ⟺ coefficient in `(0,1)`, closed-segment
    betweenness ⟺ coefficient in `[0,1]`;
  - **continuity** `continuousAt_chordCoeff` (at triples with a distinct
    chord) and `zeroChordCoeff`/`continuous_zeroChordCoeff` (coefficient
    continuous on the whole trisecant zero set — the chord denominator
    never vanishes there since the zero set is off-diagonal);
  - **open/closed data** `isOpen_strictZero` / `isClosed_closedZero`: on
    the zero set, "the third point lies strictly between the chord
    endpoints" is an *open* condition and "lies on the closed chord" is
    *closed* (both are coefficient-preimages of intervals — the first
    global structural fact about the strict part of the zero set);
  - **the `O`-side interface** — `strictZero`, `zeroChordClass`,
    `zeroChord_endpoints_ne`, `strict_hasMiddleOnClass` (a strict data
    point realises its chord class as a trisecant), and the **fibre
    structure of the chord-class map**: `strictZero_fiber` (two strict
    data over the same class have equal or swapped chord endpoints — the
    fibres of the double cover are two-element) and
    `strictZero_fiber_middle` (under `QuadrisecantFree` the middle
    coordinate is constant on each fibre: the two-to-one cover of `O` by
    the strict data with the swap as the only identification);
  - **local injectivity on chart strict parts** — `tripleSwap`,
    `continuous_tripleSwap`, `tripleSwap_ne_self`,
    `exists_isOpen_disjoint_self_image` (generic displaced-neighbourhood
    lemma), `chartLift_injective`, and the milestone lemma
    **`zeroChordClass_injective_near_base`**: around the strict base
    parameter `x₀` of any 1-chart (`ZeroSet1Chart r p` at a point of
    `O`) there is an open parameter neighbourhood `J` of `x₀` on which
    the chord-class map `zeroChordClass` is injective among strict data
    (equal classes force equal data — equal ordered chords give equal
    middles under `QuadrisecantFree`, swapped chords would land both
    fibre elements inside a swap-free neighbourhood) — the injectivity
    half of the local-homeomorphism statement from which the 1-manifold
    charts of `O` are built.

* `TrisecantTransverse.lean` — **Milestone-2 step (iii), dependency:
  transverse general position for the trisecant locus over `O`**
  (`Submission/TrisecantTransverse.lean`, 165 lines, sorry-free,
  warning-free, imported by Submission.lean).  The strengthening that the
  chart-local *open-map* lemma needs: the rank-two `TrisecantGeneralPosition`
  alone does not exclude strict-class sequences whose middles run to a
  chord endpoint (a normalised-limit argument shows that forces the chord
  direction to be parallel to the endpoint tangent — consistent with rank
  two), and such sequences would break openness of the local sheet image in
  `O`.  Kuperberg's `π_L` genericity excludes exactly those tangencies; the
  formal mirror is: `EndpointTangentsOffChord` (six cross products
  `(r x − r y) × velocity x` nonzero — no chord direction through two of
  the three points is tangent at one of its own endpoints, with period-shift
  invariance lemmas `period_shift_left/right/middle`), the real
  `TrisecantGeneralPositionTransverse = TrisecantGeneralPosition ∧
  EndpointTangentsOffChord`, the torus-level
  `TorusGeneralPositionTransverse` (mirroring `TorusGeneralPosition`), and
  monotonicity `TrisecantGeneralPositionTransverse.imp_generalPosition` /
  `torusTransverse_monotone` (all existing chart/atlas theorems, proved
  under `TorusGeneralPosition`, remain available under the strengthened
  hypothesis).  The module header fixes the **chart-local open-map lemma
  statement**: for the strict open parameter neighbourhood `J` of
  `zeroChordClass_injective_near_base`, the image
  `zeroChordClass h '' (chartLift c '' J)` is open in `trisecantSet r` —
  with the endpoint-escape lemma (no strict middle running to a chord
  endpoint under `TorusGeneralPositionTransverse`) as the next dependency.

* `EndpointEscape.lean` — **Milestone-2 step (iii): the endpoint-escape
  lemma** (`Submission/EndpointEscape.lean`, 294 lines, sorry-free,
  warning-free, imported by Submission.lean).  The geometric content
  behind the local open-map structure of `O`: under the transversality
  `cross3 (r a₀ − r b₀) (velocity r a₀) ≠ 0`, no strict middle family of a
  smooth knot can have its chords tend to the chord `{a₀,b₀}` while its
  middles tend to the endpoint `a₀` (`no_middle_to_endpoint`).  Content:
  the coordinate projections `coordProj` (continuous linear), the C¹
  coordinate functions of the knot (`contDiffAt_coord`,
  `deriv_coord`), the scalar-slope consequences
  (`coord_tendsto_of_tendsto`, `chord_coord_tendsto`, and
  `coord_slope_eq_of_middle` — each coordinate of the chord direction
  times `t n/(m n − a n)` converges to the corresponding coordinate of
  the velocity, via the fleet lemma
  `Commons.Analysis.Calculus.tendsto_slope_of_contDiffAt` applied to the
  coordinate functions), and the **normalised-limit argument**
  (`middle_to_endpoint_cross_zero`): fixing a nonzero coordinate of the
  chord direction, the scalar sequence `s n = t n/(m n − a n)` converges
  to the quotient of velocity- and chord-coordinates, then every
  coordinate of the velocity equals that scalar times the corresponding
  chord coordinate — `velocity r a₀ = λ • (r b₀ − r a₀)` — so the cross
  product vanishes (`cross3_collinear_zero`); `no_middle_to_endpoint`
  negates this against the transversality (with the coefficient lemma
  `mem_openSegment_smul_sub`: strict segment membership gives the
  convex-coefficient factorisation `z − x = t • (y − x)`, `0 < t < 1`).
  Together with `TrisecantTransverse.lean` this is the escape half of the
  open-map proof; the canonical-section/open-map assembly (chart-local
  open-map lemma of the `TrisecantTransverse` header) is next.

* `ClassSection.lean` — **Milestone-2 step (iii), assembly item (a): the
  sheet local section of the chord-class double cover of the band**
  (`Submission/ClassSection.lean`, sorry-free, warning-free, imported by
  Submission.lean).  The open Möbius band of secants is double-covered by
  the ordered pairs of distinct parameters, `mobiusCover : OrderedPairs →
  OpenMobius` (a free `ZMod 2`-swap quotient, a covering map by
  `SecantSpace`); since a covering map is locally a homeomorphism,
  `mobiusCover_isLocalHomeomorph` and `exists_sheet_at` give an open
  partial homeomorphism through any ordered pair `p₀`, bundled as
  `MobiusSheet p₀` (open source `S ∋ p₀`, open target `T ∋ mobiusCover
  p₀`, homeo `φ : S ≃ₜ T` extending `mobiusCover`; existence
  `MobiusSheet.nonempty`).  The canonical continuous section
  `MobiusSheet.sec` over the target is a right inverse
  (`sec_comp`: `mobiusCover (sec c) = c`), a left inverse on the source
  (`sec_eq_of_source`, `sec_base` fixes the base pair), and continuous
  (`secContinuous`, `secContinuousMap`).  The classical sheet over an
  **endpoint box** is also built: for disjoint open circle
  neighbourhoods `Ua ∋ a₀`, `Ub ∋ b₀` (`exists_box_sheet` from
  `t2_separation` on the circle), `chordBox Ua Ub` (first endpoint in
  `Ua`, second in `Ub`) is open (`isOpen_chordBox`), `mobiusCover` is
  injective on it (`mobiusCover_injOn_chordBox` via the two-element
  fibre `mobiusCover_fiber` + disjointness), its image is open
  (`isOpen_chordBox_image`), and the restriction is a homeomorphism onto
  that image (`chordBoxHomeo`, with `chordBoxHomeo_apply`), i.e. the
  double cover has a sheet keeping the two endpoints on prescribed sides
  of the chord.  This is the band-side local section on which the
  canonical-section/open-map assembly (middle convergence of strict data
  over classes near `c₀`, then the chart-local open-map lemma) is built.

* `SheetAssembly.lean` — **Milestone-2 step (iii), assembly items (b)–(c):
  convergence along the sheet** (`Submission/SheetAssembly.lean`,
  sorry-free, warning-free, imported by Submission.lean).  The topological
  plumbing of the canonical-section/open-map assembly: subtype-valued
  sequence convergence (`tendsto_subtype_of_tendsto_val` /
  `tendsto_val_of_tendsto_subtype` — a `ℕ`-sequence in a subset converges
  iff its value sequence does, via `nhds_subtype_eq_comap` +
  `tendsto_comap_iff`), the natural shifts
  (`tendsto_nat_add_atTop`/`tendsto_nat_sub_atTop`), and the **class
  sequence lift onto a sheet**: `MobiusSheet.exists_lift_of_mem` (a class
  sequence lying entirely in the sheet target lifts through the continuous
  section to ordered pairs `Xₙ → p₀` with `mobiusCover (Xₙ) = yₙ` for
  every `n`) and `MobiusSheet.exists_lift_of_tendsto` (a class sequence
  merely *converging* to `mobiusCover p₀` lies in the target eventually,
  and after passing to the tail lifts to `Xₙ → p₀` with
  `mobiusCover (Xₙ) = yₙ` eventually).  These give the converging ordered
  chord representatives `(aₙ,bₙ) → (a₀,b₀)` on the sheet that the middle
  convergence (cluster points of strict middles `mₙ` forced to `m₀` by
  closed-data compactness + endpoint escape + `QuadrisecantFree`
  uniqueness) and then the chart-local open-map lemma are built on.
  Section 3 adds the **generic sheet lift** `exists_lift_tendsto_of_localSheet`
  (any map `q : X → Y` agreeing with an `OpenPartialHomeomorph` `e` on its
  source lifts convergent base sequences through `e.toHomeomorphSourceTarget.symm`,
  eventually, with the original `q`-values) and its circle instance
  `exists_real_lift_of_tendsto_circle`: a sequence `xₙ → x₀` in the
  parameter circle `AddCircle period` lifts to real sequences
  `Xₙ → X₀` through any chosen real lift `X₀` of `x₀` (covering
  certificate: Mathlib `AddCircle.isCoveringMap_coe`) — the bridge from
  circle-valued convergence of strict middle parameters to the
  real-sequence convergence of the endpoint-escape lemmas
  (`no_middle_to_endpoint` / `no_middle_to_endpoint_b`).

* `MiddleConvergence.lean` — **Milestone-2 step (iii), assembly item (b):
  the middle-convergence lemma PROVED** (`Submission/MiddleConvergence.lean`,
  473 lines, sorry-free, warning-free, imported by Submission.lean).  The
  statement `middle_tendsto_of_class_tendsto`: for a smooth knot `r` with
  `QuadrisecantFree r`, ordered chord `p₀ = (a₀,b₀)` with real
  representatives `A₀, B₀` (`r A₀ ≠ r B₀`, chord transverse at both
  endpoints, `ChordOffEndpointTangents r A₀ B₀`) and a strict middle `m₀`
  of the limit chord, any class sequence `cₙ → mobiusCover p₀` with
  `cₙ ∈ O = trisecantSet r` has its canonical strict middles converging:
  `classMiddle r (c n) (hc n) → m₀`.  Content chain: vocabulary glue
  (`strict_middle_on_chord_of_class_mem`, `strict_middle_unique_on_chord` /
  `_on_class`, `IsMiddleOnChord_iff_real`, `sub_ne_zero_of_real_ne`,
  `segment_mem_openSegment_of_ne`, `eventually_ne_of_tendsto_limits_ne`,
  `eventually_chord_endpoints_distinct_circle`); the circle-level endpoint
  escape `no_circle_middle_to_endpoint_a` / `_b` (strict-middle circle
  families with chords → the chord of `A₀,B₀` and middles → an endpoint
  class contradict the real escape `no_middle_to_endpoint(_b)` via real
  lifts + eventual `M n ≠ A n`/`B n` + tail shifts); the limit analysis
  `closed_middle_limit_of_transverse_chord` (triple limits in
  `closedMiddleData`, `IsClosed.mem_of_tendsto`,
  `segment_mem_openSegment_of_ne`) and `limit_middle_eq_strict_middle`
  (uniqueness via `middle_unique_of_quadrisecantFree`); the canonical
  middle `classMiddle` / `classMiddle_middle_on_rep` /
  `classMiddle_middle_on_lift`; the master proof: sheet chord lift
  (`MobiusSheet.exists_lift_of_tendsto`), `MapClusterPt.tendsto_subseq`
  from each cluster point, `limit_middle_eq_strict_middle`, then
  `IsCompact.tendsto_nhds_of_unique_mapClusterPt` upgrades unique cluster
  points to `Tendsto`.  This is the class-level middle continuity that the
  chart-local open-map assembly (item (c)) consumes.


* `OpenMapAssembly.lean` — **Milestone-2 step (iii), assembly item (c):
  strict data of converging classes converge along the sheet and enter the
  chart — analytic core PROVED** (`Submission/OpenMapAssembly.lean`, 326
  lines, sorry-free, warning-free, imported by Submission.lean).
  `chordOfZeroSet` / `zeroChordClass_eq_mobiusCover_chordOfZeroSet` /
  `strict_middle_of_strictZero` / `transverseReps_of_baseData` (real reps
  `A₀ B₀` of a strict base chord with `r A₀ ≠ r B₀` and
  `ChordOffEndpointTangents`, from `TorusGeneralPositionTransverse`);
  `middle_tendsto_of_strictBase` (instances the middle-convergence theorem
  of MiddleConvergence at the strict base class); the milestone
  `strictData_tendsto_of_class_tendsto` — a class sequence `yₙ ∈ O`
  converging to the class of the strict base point `z₀` is lifted by the
  sheet to chords `Pₙ → p₀` (`mobiusCover (Pₙ) = yₙ` eventually) and the
  strict data triples `Dₙ = (Pₙ.a, (Pₙ.b, classMiddle yₙ))` converge to
  the base triple `z₀`; `zeroSetPoint_of_classMiddle_on_rep` /
  `strictData_in_zeroSet_of_class_tendsto` (the strict data triples are
  zero-set points: strict middle ⇒ collinear (`openMiddleData_subset_collinearity_zero`)
  and off-diagonal via endpoint separation); `zeroChordClass_chartLift_of_window`
  and `zeroChordClass_eq_mobiusCover_of_triple` (the class of a chart-lift
  point over a window triple is the class of its canonical chord); and the
  theorem `classes_eventually_in_chart_image`: for a `ZeroSet1Chart c` at
  the strict base triple, every class sequence in `O` converging to the
  base class is eventually realised by chart parameters `xₙ → ⟨c.x₀,·⟩`
  with `zeroChordClass h (chartLift c (xₙ)) = yₙ` (data triples enter the
  open window `c.V`, the chart inverse is applied, spliced with the
  standard tail-shift).  Together with `classes_eventually_in_chart_trace`
  (any open interval `J` around the base parameter inherits the statement),
  this is the sequence-level surjectivity of the class map onto `O` that
  the open-map lemma needs; the remaining topological packaging — a
  countable decreasing neighbourhood base of the band at the base class
  (via the sheet homeo to `OrderedPairs`, which is first countable) +
  the sequence-⇒-neighbourhood lemma — turns it into the literal
  `∃ open W, zeroChordClass h '' (chartLift c '' J) = trisecantSet r ∩ W`
  (recorded in ROADMAP S91).


* `OpenMapPackaging.lean` — **Milestone-2 step (iii), assembly item (c):
  the open-map lemma PROVED (topological packaging)** (`Submission/
  OpenMapPackaging.lean`, 206 lines, sorry-free, warning-free, imported by
  Submission.lean).  Completes the open-map half of the local 1-manifold
  structure of `O`: instance `SecondCountableTopology OpenMobius` (the
  band is an open quotient of the second-countable `OrderedPairs` —
  `Topology.IsQuotientMap.secondCountableTopology` with
  `isQuotientMap_mobiusCover`/`isOpenMap_mobiusCover`), hence first
  countable; `exists_open_nhd_subset_of_seq_eventual` (the sequence-⇒-
  neighbourhood bridge: in a first-countable space a set containing the
  tail of every sequence in `O` converging to `y₀` contains a relative
  open neighbourhood of `y₀` — contradiction with a decreasing countable
  basis, `Filter.exists_antitone_basis`); `preimage_chartLift_of_point`
  and `open_nhd_at_chart_class` (per-point openness at every strict chart
  point: `classes_eventually_in_chart_trace` (OpenMapAssembly) + the
  bridge); and the milestone **`zeroChordClass_image_open_on_strict_J`**:
  for a `ZeroSet1Chart c` and an open parameter interval `J` on which all
  chart points are strict, the class image
  `zeroChordClass h '' (chartLift c '' J)` is open in `trisecantSet r` (=
  `O ∩ W` for the union of the per-point relative-open neighbourhoods,
  with `f(J) ⊆ O` by strictness).  Together with injectivity
  (`StrictZero.zeroChordClass_injective_near_base`) this makes the class
  map a local homeomorphism from strict chart data onto its image in `O` —
  Milestone-2 (iii) is complete; components of `O` inherit the interval
  structure.


* `OLocalStructure.lean` — **Milestone-2 (iv) / Layer C opener: strict
  representatives, continuity of the class map, and interval paths**
  (`Submission/OLocalStructure.lean`, 147 lines, sorry-free, warning-free,
  imported by Submission.lean).  First bricks of the component/winding
  classification of `O`: `strictRep_of_trisecant` (every class `c ∈ O` is
  the class of a strict zero-set data point — canonical middle on a chord
  representative, `zeroSetPoint_of_classMiddle_on_rep`); the continuity of
  the canonical chord and of the class map on the zero set
  (`continuous_chordOfZeroSet`, `continuous_zeroChordClass` — the class is
  `mobiusCover` of the chord, both continuous); and the interval path
  lemma `isPathConnected_univ_chartInterval` (the chart parameter interval
  is path connected via straight-line paths, convexity).  These are the
  building blocks for the open path-connected trace neighbourhoods of
  every class of `O` (openness: the open-map lemma of OpenMapPackaging;
  path connectedness: continuous image of an interval) and for the
  statement that the connected components of the subspace `O` are open —
  the local interval structure from which the arc/circle classification of
  components and the once/twice-winding dichotomy are derived.


  Step (4) landed in the same module: `chartLift_base_eq` and
  `exists_open_pathConnected_nhds_in_O` — every class `c₀ ∈ O` lies in an
  open (relative to `O`), path connected subset of `O`: pick a strict
  representative and a chart (`zeroSet1Chart_at_general_position`),
  refine a strict convex parameter cell (`exists_convex_strict_cell` via
  the metric ball in the strict-open chart region), whose class image is
  open in `O` (open-map lemma) and path connected (continuous image of
  `isPathConnected_convexCell`), containing `c₀`.
  Step (5) landed in the same module: `isPathConnected_lift_trisecant`
  (path-connected subsets of `O` lift to path-connected preimages in the
  subtype) and `isOpen_component_in_O` — under h, hqf,
  `TorusGeneralPositionTransverse`, every connected component of the
  subspace `O = trisecantSet r` is open (lift the step-(4) path-connected
  open neighbourhoods into the subtype, use `IsPreconnected.subset_connectedComponent`
  + `connectedComponent_eq` + `mem_of_superset`).
* `ComponentPath.lean` — **Milestone-2 (iv) step 6 (part A): components of
  `O` are path-connected; paths in `O` lift over the ordered double cover**
  (`Submission/ComponentPath.lean`, 261 lines, sorry-free, warning-free,
  imported by Submission.lean).  With the components of the subspace `O`
  open (OLocalStructure step (5)), this module makes them path-connected
  and adds the covering lift interface that the arc/circle classification
  and the once/twice-winding analysis consume.  Content: the *generic
  engine* `Commons.Topology.PathConnected.isPathConnected_of_isConnected_of_open_pathConnected_nhds`
  is imported from the commons (fleet-proven L27; in any topological space
  a connected set in which every point has an open path-connected
  neighbourhood inside the set is path-connected — path component `Q` of a
  point is open (each of its points carries a path-connected neighbourhood
  fully inside `Q`) and `IsPreconnected.subset_of_closure_inter_subset`
  forces the connected set into `Q`); the subtype `OSub r = {c // c ∈ trisecantSet
  r}` and `exists_open_pathConnected_nhds_in_OSub` (the step-(4) trace
  neighbourhoods re-exported into the subtype); **`component_isPathConnected_in_O`**
  (under h, hqf, `TorusGeneralPositionTransverse`, every connected
  component of the subspace `O` is path-connected — instance of the
  generic engine, using that a path-connected neighbourhood of a point of
  a component lies inside the component via
  `IsConnected.subset_connectedComponent` + `connectedComponent_eq`);
  `exists_path_in_component_in_O` (two classes in one component are joined
  by a path of trisecants staying inside the component);
  `bandPath_continuous`, **`exists_lift_orderedData_of_bandPath`** (a path
  in `O` lifts through the covering `mobiusCover` to a continuous path of
  ordered pairs through the ordered double cover, given a lift of its
  source class — the path-lifting property of
  `isCoveringMap_mobiusCover`), and **`lift_loop_end_in_fiber`** (a loop
  in `O` based at `c₀` lifts to an ordered-pair path starting at the
  representative `p₀` of `c₀` and ending in the two-element fibre
  `{p₀, swapOrdered p₀}` — the monodromy interface of the once/twice-
  winding step).  Section 5 completes the parity interface: `bandCMap`
  (the band path of an `O`-path), `bandCMap_zero_of_rep`,
  **`lift_loop_end_even_or_odd`** (the endpoint of the lift of a loop is
  either `p₀` — even/null monodromy — or `swapOrdered p₀` — odd/essential
  monodromy), and **`lift_from_swap_ends_swapped`** (the lift starting at
  the other representative is the swap of the lift from `p₀`, so the
  parity dichotomy is independent of the chosen representative; uses the
  uniqueness of covering path-lifts, `IsCoveringMap.eq_liftPath_iff'`).
* `ComponentLoop.lean` — **S256 (VERIFIED): the component loop — a
  circular component chart is a loop of `O`** (module
  `Submission/ComponentLoop.lean`, sorry-free, warning-free, imports
  ComponentChart + ComponentPath; registered after ComponentPath).  The
  bridge between the AddCircle charts of circular components (S249/S253:
  `χ : AddCircle T ≃ₜ TrisecantComponent r c₀`) and the double-cover
  parity machinery over paths in `O` (`ComponentPath`:
  `exists_lift_orderedData_of_bandPath`, `lift_loop_end_even_or_odd`):
  `componentLoopBase` (the class underlying `χ 0`, an `OSub r` trisecant
  class of the component), `componentLoop` (the loop `γ : Path b b`, `b =
  componentLoopBase c₀ χ`, tracing the whole circle once by
  `γ t = χ (t·T : AddCircle T)`, `t ∈ I` — source `χ 0 = b`, target
  `χ T = χ 0` by `AddCircle.coe_period`), `componentLoop_val` (the
  pointwise value identity), `exists_ordered_rep_of_component_loopBase`
  (the base class has an ordered representative `p₀` over the double
  cover), and **`component_loop_parity`** (the parity dichotomy of a
  circular component: the component loop lifts over the full circuit to
  `Γ : C(I, OrderedPairs)` with `Γ 1 = p₀` — even/twice-winding — or
  `Γ 1 = swapOrdered p₀` — odd/once-winding; the unit-interval half of
  S253b sub-problem 1).  ROADMAP S256.  **S257 (appended, VERIFIED sorry-free) — the ordered lift over the
  whole component circle (S253b sub-problem 1 COMPLETE)**: the `ℝ`-level
  statement of the parity dichotomy in advance form.
  `componentClassMap` (the continuous class map `u ↦ χ (u : AddCircle T)`
  into the band, `C(ℝ, OpenMobius)`), `componentClassMap_periodic` (it is
  `T`-periodic: the chart's class returns after a full circuit by
  `AddCircle.coe_period`), and **`component_ordered_lift_real`**: the
  class map lifts through the covering `mobiusCover` to a continuous
  `sig : C(ℝ, OrderedPairs)` with `sig 0 = p₀`,
  `mobiusCover ∘ sig = componentClassMap c₀ χ`, whose one-circuit advance
  is EVEN — `sig (u + T) = sig u` for all `u` (the lift is `T`-periodic,
  closed; each chord endpoint winds once around the knot — twice-winding)
  — or ODD — `sig (u + T) = swapOrdered (sig u)` (the sheets exchange —
  once-winding).  Proof: `sig T` lies in the fibre `{p₀, swapOrdered p₀}`
  of the base class, and uniqueness of continuous lifts over the connected
  line (`IsCoveringMap.eq_of_comp_eq`) identifies the shifted lift with
  `sig` / with `u ↦ swapOrdered (sig u)` (which also lifts by
  `mobiusCover_swap`).  ROADMAP S257.  **S258 (appended, VERIFIED sorry-free) — the endpoint real lifts of an
  EVEN ordered lift (S253b sub-problem 2)**: `continuous_ordered_endpoint1`
  / `continuous_ordered_endpoint2` (the endpoint projections
  `u ↦ (sig u).1.1`, `u ↦ (sig u).1.2` of an ordered lift are continuous)
  and **`component_endpoints_lift_even`**: for an EVEN (twice-winding)
  ordered lift `sig` of the class map (`sig (u + T) = sig u`, S257), each
  chord endpoint is a continuous `T`-periodic circle map, so by fleet L66
  (`Commons.Topology.AddCircle.circleMap_lift_advance`) it has a
  continuous real lift `a` / `b` (`(a u : AddCircle period) = (sig u).1.1`,
  `(b u : AddCircle period) = (sig u).1.2`) with integer per-circuit
  advances `a (u + T) = a u + (ka : ℝ) * period`,
  `b (u + T) = b u + (kb : ℝ) * period` — the formal endpoint winding
  numbers of the even branch, which the ±2g measurement pins to
  `±period`.  ROADMAP S258.  **S259 (appended, VERIFIED sorry-free) — the ordered lift's chord
  carries the canonical middle (the `sig`–`μ` connection)**:
  `componentMiddle_middle_of_ordered_lift` — for an ordered lift `sig` of
  the class map (`mobiusCover ∘ sig = componentClassMap c₀ χ`, S257),
  `IsMiddleOnChord r (sig u).1.1 (sig u).1.2 (componentMiddle c₀ (χ (u :
  AddCircle T)))` for every `u` (unconditional): `componentMiddle_mem_middleSet`
  (S252) provides a chord of the class whose strict middle the canonical
  middle is, and `middleOnChord_of_mobiusCover_eq` (representative
  independence) transfers it to the representative `sig u`.  This is the
  input of the trapped-middle measurement (S253b sub-problem 4).  ROADMAP
  S259.  **S260 (appended, VERIFIED sorry-free) — the middle lift is trapped on
  the endpoint chord (real strict betweenness — S253b sub-problem 3's core
  statement)**: `componentMiddle_real_betweenness` — with real endpoint
  lifts `a b` of the ordered lift `sig` (S258) and a real middle lift
  `mhat` (S255), for every `u` the middle knot point lies strictly inside
  the chord between the endpoint knot points in the real parametrisation:
  `r (mhat u) ∈ openSegment ℝ (r (a u)) (r (b u))` (S259's
  `componentMiddle_middle_of_ordered_lift` + endpoint/middle
  compatibilities + `IsMiddleOnChord_iff_real` converting the
  circle-level strict-middle condition to the real open-segment
  condition).  ROADMAP S260.  **S261 (appended, VERIFIED sorry-free) — the ONCE-case first beat: on
  the odd-advance branch the endpoint lifts travel and SWITCH**:
  `component_endpoints_lift` (any ordered lift — either branch — admits
  continuous real endpoint lifts `a b` over the whole line, via the
  `AddCircle period` covering; existence does not need periodicity),
  `component_ordered_endpoint_switch_odd` (the circle-level switch: on the
  odd branch `(sig (u+T)).1.1 = (sig u).1.2` and
  `(sig (u+T)).1.2 = (sig u).1.1`), and **`component_endpoint_switch_odd`**
  (the real-lift switch with integer offsets: `a (u + T) = b u + (ka :
  ℝ) * period`, `b (u + T) = a u + (kb : ℝ) * period` for fixed `ka kb` —
  the class of `a (u+T)` is the class of `b u`, so the continuous
  `period·ℤ`-valued difference is constant over the connected line, fleet
  L66's argument).  This is Kuperberg's "the endpoints travel … and switch
  places" in the once-winding branch.  ROADMAP S261.  **S262 (appended, VERIFIED sorry-free) — the once-case double circuit**:
  `component_endpoint_double_circuit_odd` — on the odd (once-winding)
  branch, over TWO circuits (the double cover of the Möbius band) the
  ordered lift closes (`sig (u + T + T) = sig u`, two swaps +
  `swapOrdered_involutive`) and both endpoint real lifts advance by the
  SAME integer multiple of the knot period: `a (u + T + T) = a u + (kd :
  ℝ) * period`, `b (u + T + T) = b u + (kd : ℝ) * period` with `kd = ka +
  kb` (algebra on the S261 switch relations applied twice).  The
  well-formed period structure of the once-case avatar (its natural
  fundamental period is the double circuit).  NOTE (honest): the
  half-period avatar itself is NOT derivable from the S254–S262 abstract
  data — `componentMiddle ∘ χ` is T-periodic (S255) and
  `no_onceWinding_advance` (S253) rules out any half-period lift; the
  once-contradiction needs the chord-direction (π_K) / π₁(M) geometry
  (brick-(c) sub-problem 4).  ROADMAP S262.
  **S275 (appended, VERIFIED sorry-free) — essentialness of the odd
  (once-winding) component loop**: `bandLoop` (a loop `γ : Path c₀ c₀`
  of trisecant classes read in the band as `Path ((c₀ : OSub r) :
  OpenMobius) ((c₀ : OSub r) : OpenMobius)`, with
  `bandLoop_eq_bandCMap`), **`bandLoop_essential_of_oddLift`** — an ODD
  ordered lift (`Γ 1 = swapOrdered p₀`, sheet swap after one circuit)
  makes the band loop NOT null-homotopic (`¬ Path.Homotopic (bandLoop γ)
  (Path.refl …)`): null-homotopy would force the canonical lift
  (`IsCoveringMap.liftPath`, `eq_liftPath_iff'`) to close at `p₀`
  (`liftPath_apply_one_eq_of_homotopicRel` + `liftPath_const`),
  contradicting `ordered_ne_swapOrdered` — the covering-space bridge from
  the measurable parity to *essentiality in the band*; its instance
  **`component_loop_essential_of_odd`** (once-winding circular components
  of the trisecant set are essential) and the complementary
  **`bandLoop_even_of_null`** / **`component_loop_even_of_null`** (a
  null-homotopic component loop sits on the EVEN branch: lift closes,
  `Γ 1 = p₀`).  Deduplication note: the plane-model homeo / core
  retraction / `π₁(OpenMobius) ≅ ℤ` already exist in `SecantModel.lean`,
  `OpenMobiusHomotopy.lean`, `Pi1OpenMobius.lean`.  ROADMAP S275.
* `OSubChart.lean` — **Milestone-2 (iv) step 6, brick (a): interval
  charts of `O` at every trisecant class — `O` is locally a
  1-dimensional topological manifold** (`Submission/OSubChart.lean`,
  646 lines incl. the S98 transition section, sorry-free, warning-free,
  imported by Submission.lean).
  With the components of `O` open and path-connected (OLocalStructure +
  ComponentPath), this module completes the *chart* half of the local
  1-manifold structure of the trisecant set: every class `c₀ ∈ O` has an
  open neighbourhood homeomorphic to an open interval of `ℝ`.  Content:
  `OSub1Chart r c₀` (a bundled chart of `O` at the class `c₀ ∈ O`: an
  open real interval `(lo,hi) ∋ x₀`, an open band set `W` with
  `(c₀ : OpenMobius) ∈ W`, and a homeomorphism of the interval onto the
  open trace `{c : OSub r | (c : OpenMobius) ∈ W}` sending `x₀` to
  `c₀`); the coordinate relabelling `cellIntervalHomeo` (an open real
  interval strictly inside the chart interval is homeomorphic to the
  corresponding cell of the chart parameter space); and **the chart
  theorem `osub1Chart_at_class`**: under h, hqf,
  `TorusGeneralPositionTransverse`, every trisecant class carries an
  `OSub1Chart`.  Proof: strict representative `z₀` of `c₀`
  (`strictRep_of_trisecant`), bundled zero-set chart `c` at `z₀`
  (`zeroSet1Chart_at_general_position`), a strict convex cell around the
  base parameter (`exists_convex_strict_cell`) shrunken into the local
  injectivity region of the class map (`zeroChordClass_injective_near_base`,
  radius controlled by the metric-ball neighbourhood of the base in `J₁`)
  and into the chart window; the class map of the cell is continuous
  (composition of the continuous chart lift and class map), injective
  (every cell parameter is strict and lies in `J₁`), and **open onto its
  image** — the image of any open sub-cell is `O ∩ W` by the open-map
  lemma `zeroChordClass_image_open_on_strict_J`, packaged as `IsOpenMap`
  of the cell map by the representation `fO '' U = val⁻¹ W₀` with the
  preimage-of-open-openness in the subspace `O`; surjectivity onto the
  trace `O ∩ W` by the open-map lemma applied to the whole cell; assembly
  via `Equiv.ofBijective` + `toHomeomorphOfContinuousOpen` after
  relabelling the coordinates back to the genuine open interval
  `(xb − δ, xb + δ)` (so the homeomorphism domain is a `ChartInterval`).
  This is the 1-manifold structure of the components of `O` that the
  arc/circle classification (brick (b)) and the once/twice-winding
  dichotomy (brick (c), feeding `ParameterWinding` (S78) and
  `TrisecantStructure.exists_uncovered_middle`) consume.  A section 3
  completes the **chart overlap / atlas compatibility** (S98): `oChartLift`
  (the `OSub` class of a chart parameter; `oChartLift_mem_W`,
  `oChartHomeo_eq_lift`, `oChartLift_base`, `oChartLift_eq_of_homeo`), the
  transition domain `OChartTransitionDomain` (`isOpen_oChartTransitionDomain`
  — the transition domain is an open subset of the chart interval), the
  forward/backward transition maps `oChartTransitionTo`/`_Back`
  (`oChartTransitionTo_val`, `oChartTransition_preserves`,
  mutual-inverse lemmas, the equivalence `oChartTransitionEquiv`), the
  continuity lemmas `continuous_oChartTransitionTo`/`_Back`, the bundled
  transition **homeomorphism `oChartTransitionHomeo` of open parameter
  domains**, its class preservation `oChartTransition_preserves_class`,
  the transition lemma **`oSub1Chart_transition`** (overlapping interval
  charts are compatible: on the transition domains the change of
  parameters is a homeomorphism preserving the trisecant class), and
  `exists_oChartTransitionParam_of_mem_both` (a class in both traces
  gives a transition parameter).
* `OChartChain.lean` — **Milestone-2 (iv) step 6, brick (b): chart
  chains along `O`-paths — every path of trisecant classes (in
  particular every path inside a connected component of `O`) is covered
  by a finite chain of interval charts with consecutive traces
  overlapping** (`Submission/OChartChain.lean`, 341 lines, sorry-free,
  warning-free, imported by Submission.lean).  On top of the bundled
  charts `OSub1Chart` and their transition homeomorphisms
  (`oSub1Chart_transition`, `oChartTransitionHomeo`, S98), this module
  supplies the global chaining statements that the component
  classification consumes.  Content: `realTime` (a real point of `[0,1]`
  as a unit-interval element), `oChartAtClass` (the interval chart at a
  class, a classical choice from `osub1Chart_at_class`), `oTraceTime`
  (the open set of times whose path class lies in the trace of the chart
  at `t`; `isOpen_oTraceTime`) and its ambient-open real representative
  `oTraceTimeReal` (`isOpen_oTraceTimeReal`,
  `oTraceTime_eq_oTraceTimeReal`), the real-cover fact
  `real_cover_oTraceTime` (the unit interval is covered by the real
  representatives of the chart traces), the uniform subdivision
  `oTraceTime_subdivision` (Lebesgue-number style through the commons
  lemma `Commons.Analysis.Real.open_cover_subdivision`), the grid real
  arithmetic `gridReal_mem_Icc`/`gridReal_mono`/`gridReal_succ_sub`
  (grid points `i/N` lie in `[0,1]`, are nondecreasing, and are spaced
  `1/N` apart), and `mem_trace_of_real_in_cell` (a real point of a
  covered subinterval gives a path class in the trace of the covering
  chart).  **The chain theorem `exists_oChart_chain_along_path`**: for a
  path `γ : Path a b` of trisecant classes under h, hqf, hgp there is a
  positive `N`, cover times `τ : Fin N → I` and charts
  `ch i` (centred at `γ (τ i)`) such that every path class over the grid
  subinterval `[i/N, (i+1)/N]` lies in the trace of `ch i` (the initial
  class lies in the trace of the first chart and the final class in the
  trace of the last chart), and the traces of consecutive charts both
  contain the class at the common grid point `(i+1)/N`.  Proof:
  `exists_nat_gt (1/δ)` provides `N` with step `1/N ≤ δ`, each grid
  interval is covered by the subdivision choice `τ i`, and the endpoint
  and overlap memberships come from `mem_trace_of_real_in_cell` on the
  corresponding cells.  **The transition chain
  `exists_oChartTransition_chain_along_path`** (`realTime_zero`,
  `realTime_one`): the grid chain has *inhabited* consecutive transition
  domains — the source-class chart chains to the first grid chart (both
  traces contain the initial class), the last grid chart chains to the
  target-class chart, and each consecutive pair `(ch i, ch (i+1))`
  chains at the common grid class — via
  `exists_oChartTransitionParam_of_mem_both`; hence the transition
  homeomorphisms `oChartTransitionHomeo` apply successively along the
  chain.  Applied to the component path of
  `ComponentPath.exists_path_in_component_in_O` this chains any two
  classes of one connected component of `O` by interval charts with
  compatible change-of-parameters — the input to the arc/circle
  classification of the components (brick (b) remainder) and to the
  once/twice-winding dichotomy (brick (c)).
* `OChartOrder.lean` — **Milestone-2 (iv) step 6, brick (b): ordering
  along a chain — the well-definedness half and component chainability**
  (`Submission/OChartOrder.lean`, 145 lines, sorry-free, warning-free,
  imported by Submission.lean).  With the interval charts of `O`
  (S97), their transition homeomorphisms (S98) and the chart chains along
  `O`-paths (S99), this module takes the first step of the ordering
  argument of the component classification: parameter transport along a
  chain is *well-defined*, each chart injectively parametrises its trace,
  and the classes of one connected component are *chain-connected*.
  Content: `oChartLift_injective` (two parameters of one chart with the
  same class are equal — via `oChartHomeo_eq_lift` + `ch.homeo.injective`),
  `oChartLift_surjOn_trace` (every class of a chart trace is the lift of
  its unique parameter — `oChartLift_eq_of_homeo`), and
  `oChartTransitionTo_depends_on_class` / `oChartTransitionBack_depends_on_class`
  (**the transported parameter depends only on the trisecant class**: two
  parameters of `ch₁` over the same class are sent by the transition to
  the same parameter of `ch₂` — value-level via
  `oChartTransitionTo_val` + `congrArg ch₂.homeo.symm` + `Subtype.ext`, so
  the interval-coordinates of overlapping charts are coherent and gluing
  along a chain is unambiguous), and **`exists_oChart_chain_between_component_classes`**
  (any two classes of one connected component of `O` are joined by a path
  staying inside the component that is covered by a finite chart chain
  with inhabited consecutive transition domains — the chain theorem of S99
  applied to the component path of
  `ComponentPath.exists_path_in_component_in_O`).  This is the "the chains
  bite" keystone: with well-defined class-mediated transport, the
  dichotomy "compact component ⇒ circular; non-compact ⇒ open interval"
  reduces to gluing the interval coordinates of a chain (the next step —
  monotone coordinates: any homeomorphism of real-interval pieces is
  order-preserving or order-reversing, so consecutive overlaps fix a
  coherent linear order; a closing chain gives a circle, an open one an
  interval).
* `OChartMonotone.lean` — **Milestone-2 (iv) step 6, brick (b): the
  monotone-coordinate engine — injective continuous maps on an open real
  interval are strictly monotone** (`Submission/OChartMonotone.lean`,
  98 lines, sorry-free, warning-free, imported by Submission.lean;
  consumes the fleet commons L28
  `Commons.Topology.Order.strictMonoOn_or_strictAntiOn_of_continuousOn_injOn`).
  Content: **`interval_inj_continuous_monotone`** — an injective
  continuous map `f : ChartInterval lo hi → ℝ` is either strictly
  order-preserving or strictly order-reversing (read `f` through the
  extension `F z := if z ∈ Ioo lo hi then f ⟨z,·⟩ else 0` to the real
  line; `F` is continuous on the preconnected open interval
  (`continuousOn_iff_continuous_domRestrict`, pointwise agreement with
  `f` via `dif_pos` on the restricted domain) and injective on it, so
  commons L28 supplies `StrictMonoOn ∨ StrictAntiOn`, transported back to
  the subtype statement).  Corollary **`homeoChartInterval_monotone`**:
  open-interval homeomorphisms (read through their real values, which are
  injective and continuous) are strictly monotone.  Also
  `cellIntervalHomeo_preserves_param` (the chart-cell relabelling homeo is
  the identity on the underlying real parameter).  Together with S100's
  well-definedness this is the monotone-coordinate machinery that the
  chain gluing (`OChartGlue.lean`, S102) consumes.
* `OChartGlue.lean` — **Milestone-2 (iv) step 6, brick (b): the
  chain-gluing local step — every transition parameter has a connected
  open interval neighbourhood on which the coordinate relabelling is
  strictly monotone** (`Submission/OChartGlue.lean`, 275 lines,
  sorry-free, warning-free, imported by Submission.lean).  Content
  (namespace LeanEval.KnotTheory.Quadrisecant): `oChartTransitionReal`
  (the real value of the transported parameter of `ch₂`) with
  `continuous_oChartTransitionReal` / `injective_oChartTransitionReal`
  on the whole transition domain; `oChartTransitionOnInterval` (the
  transition real value restricted to an open piece interval lying inside
  the chart interval and inside the transition domain) with its
  continuity and injectivity; the bundle **`OChartMonotoneNbhd`** (an
  open real interval `(lo,hi)` containing the parameter of `x₀`, inside
  the chart interval, all of whose parameters lie in the transition
  domain, plus the monotonicity clause on the interval-piece map) and the
  theorem **`exists_oChartMonotoneNbhd`**: every transition parameter of
  the overlap of two interval charts of `O` carries such a neighbourhood
  — shrink the metric ball of the open transition domain
  (`isOpen_oChartTransitionDomain`, S98) to stay inside the chart
  interval (the endpoint-gap arithmetic of the min-radius trick), then
  apply the monotone-coordinate engine
  (`interval_inj_continuous_monotone`) to the interval-piece map; and
  `oChartNbhd_piece_coordinate` — on the neighbourhood the interval-piece
  value of a parameter is the `ch₂`-coordinate of the *same* trisecant
  class (transition class preservation, S98), so the monotonicity
  direction compares the `ch₁`-order and the `ch₂`-order of the same
  classes: two interval coordinates agree or are reversed coherently
  along each overlap.  This is the local datum of the ordering along the
  chart chains of `OChartChain.lean` (S99): the next step assembles it
  along a chain — fix an orientation per chart, transport coordinates
  monotonically across the consecutive overlaps (order-preserving /
  order-reversing as recorded by each monotone neighbourhood), giving a
  coherent global order per chain — the input to the arc/circle
  classification of the components (brick (b) remainder) and the
  once/twice-winding dichotomy (brick (c)).
* `OChartAssembly.lean` — **Milestone-2 (iv) step 6, brick (b): the
  chain assembly — well-defined class coordinates (the first solid lemma
  of the assembly)** (`Submission/OChartAssembly.lean`, 194 lines,
  sorry-free, warning-free, imported by Submission.lean).  Content
  (namespace LeanEval.KnotTheory.Quadrisecant): `oChart_class_of_symm_mem`
  (the class of the parameter of `g` is `g` — membership transport used
  when packaging class coordinates into transition domains),
  `oChart_param_unique` (a trisecant class of a chart trace is the lift
  of exactly one parameter — chart homeo bijection +
  `oChartLift_injective` (S100) — so the class coordinate is
  well-defined) and `oChart_param_of_class_eq` (equal classes ⇒ equal
  parameters); `oChart_transition_class_mem` (the class of a transition
  result lies in any trace containing the source class) and
  **`oChart_param_transition`** (a class in the traces of both charts:
  the transition of the `ch₁`-coordinate of `g` is the `ch₂`-coordinate
  of the same `g` — the change of parameters along an overlap is the
  relabelling of well-defined class coordinates; `rw
  [oChartTransitionTo_val]` + `congrArg ch₂.homeo.symm` + `Subtype.ext`
  + `oChartLift_eq_of_homeo`); the cocycle **`oChart_param_transition_trans`**
  (transporting the coordinate of `g` through `ch₁ → ch₂ → ch₃` lands on
  the `ch₃`-coordinate of `g` — composition of transitions is the direct
  transition, so the coordinate at the end of a chain is a function of
  the endpoint class only: the assembly along a chain is unambiguous);
  and the junction lemma **`oChart_chain_junction_coherent`** (over the
  S99 chain data `γ N hN τ ch hover`: at every shared boundary class of
  consecutive charts the transition of the left chart's coordinate of the
  boundary class equals the right chart's coordinate of the same class —
  the assembled coordinates agree across the junctions of an
  `OChartChain.exists_oChart_chain_along_path` chain; an instance of
  `oChart_param_transition` on the boundary class).  This is the
  well-definedness half of the chain assembly the classification needs:
  the transported coordinate along a chain is a function of the class at
  each junction; its monotonicity along a component then comes from the
  local monotone patches of `OChartGlue` (S102) composed along the chain
  — the input to the arc/circle classification of the components (brick
  (b) remainder) and the winding dichotomy (brick (c)).
* `OChartAssemblyMonotone.lean` — **Milestone-2 (iv) step 6, brick (b):
  the chain assembly — monotone transport (composition of the local
  patches)** (`Submission/OChartAssemblyMonotone.lean`, 175 lines,
  sorry-free, warning-free, imported by Submission.lean).  Content
  (namespace LeanEval.KnotTheory.Quadrisecant): `MonotoneOnPiece` (a real
  map on an open interval piece is strictly increasing or strictly
  decreasing) with the two suppliers `monotoneOnPiece_of_inj_continuous`
  (S101's monotone-coordinate engine in predicate form) and
  `oChartMonotoneNbhd_piece_monotone` (the interval-piece transition map
  of an S102 monotone neighbourhood is `MonotoneOnPiece`);
  `TransportStepDomain` (the parameters of the first piece whose
  transported coordinate lands in the second piece) and the composition
  engine **`composite_monotone_direction`**: two transport steps each
  monotone in one direction compose to a transport monotone in one
  direction on the step domain (four cases; the overall direction is the
  product of the step directions) — the engine whose iteration along a
  chain gives the monotone transported coordinate; and the S99-chain
  instances `oChart_chain_single_junction_transport_monotone` (at one
  junction of an S99 chain a monotone neighbourhood makes the coordinate
  transport `ch i → ch (i+1)` monotone on the piece) and
  `oChart_chain_two_junction_transport_monotone` (monotone neighbourhoods
  at two consecutive junctions give a composite transport `ch i → ch (i+2)`
  monotone in one direction — the first induction step of the assembly).
  Next slice (ROADMAP S104): instantiate the patches at the junctions of
  an `OChartChain.exists_oChart_chain_along_path` chain, shrink
  consecutive pieces so each transport lands in the next patch (openness/
  continuity of the transitions), iterate the composition engine over the
  `Fin (N-1)` junctions — the monotone transported coordinate from the
  first to the last chart of one S99 chain, then the arc/circle
  classification of the components (brick (b) remainder) and brick (c).
* `OChartChainJunction.lean` — **Milestone-2 (iv) step 6, brick (b):
  the chain assembly — the S102 patches instantiated at the junctions of
  an S99 chain** (`Submission/OChartChainJunction.lean`, 251 lines,
  sorry-free, warning-free, imported by Submission.lean).  Content
  (namespace LeanEval.KnotTheory.Quadrisecant): `oChartChainJunctionParam`
  — the transition-domain element at a junction of an
  `OChartChain.exists_oChart_chain_along_path` chain (charts `ch i`,
  `ch (i+1)`, shared boundary class, memberships from `hover`): the
  `ch i`-coordinate of the boundary class packaged into
  `OChartTransitionDomain (ch i) (ch (i+1))`, with
  `oChartChainJunctionParam_class` (it describes the boundary class);
  `oChart_chain_junction_monotoneNbhd` (the S102 monotone neighbourhood
  exists at every junction — `exists_oChartMonotoneNbhd` on the junction
  parameter), `oChartChainJunctionNbhd` (the chosen one),
  `oChart_chain_junction_piece_monotone` (its piece map is
  `MonotoneOnPiece`) and `oChart_chain_junction_piece_coordinate` (on the
  piece the values are the `ch (i+1)`-coordinates of the same classes —
  the monotonicity direction compares the two charts' orders of the same
  classes); `oChartChainStepDomain` (the step-domain condition: the
  parameters of the first junction patch whose transport lands in the
  second junction patch's piece) and
  `oChart_chain_two_junction_step_monotone` (on that step domain the
  composite transport `ch i → ch (i+2)` is monotone in one direction —
  the composition engine applied to two consecutive instantiated junction
  patches).  A shrinking section (S106) adds
  `exists_interval_preimage_piece` (a continuous real map on an open
  interval sending a point into an open target interval sends a whole
  interval neighbourhood of the point into the target — the preimage of
  the target interval is open (continuity), so it contains a metric ball,
  hence an interval sub-piece) and **`exists_oChart_step_subpiece`** (its
  instance on the interval-piece transition maps of two consecutive
  monotone neighbourhoods: whenever the first patch's transport of a base
  parameter lands in the second patch's piece, the step-domain condition
  holds on a whole open interval around the base parameter — so the
  composite transport of `composite_monotone_direction` is defined and
  monotone there).  The alignment hypothesis `hx` is genuinely needed:
  consecutive junction patches sit at the coordinates of *different*
  boundary classes along the path, so a transport lands in the next patch
  only when the data are aligned (honest discussion recorded in ROADMAP
  S106).
* `OChartComponent.lean` — **Milestone-2 (iv) step 6, brick (b): the
  correct global slice over component objects — countable chart-trace
  covers of the components** (`Submission/OChartComponent.lean`, 95
  lines, sorry-free, warning-free, imported by Submission.lean).
  Content (namespace LeanEval.KnotTheory.Quadrisecant):
  **`component_countable_chart_cover`** — under h, hqf, hgp, every
  connected component `C = connectedComponent c₀` of the trisecant set
  lies in the union of the traces of the interval charts centred at
  countably many classes of `C` itself:
  `∃ cl : ℕ → OSub r, (∀ n, cl n ∈ connectedComponent c₀) ∧ (∀ y, y ∈
  connectedComponent c₀ → ∃ n, (y : OpenMobius) ∈ (oChartAtClass h hqf
  hgp (cl n)).W)`.  Proof: the trace sets `{y | (y : OpenMobius) ∈
  (oChartAtClass h hqf hgp x).W}` over `x : {x // x ∈ C}` are open
  (preimage of `W_open` under the continuous value map) and cover `C`
  (each class is in its own chart trace by the chart's `c₀_mem`); the
  component is a subspace of the second-countable band, so
  `HereditarilyLindelofSpace.isLindelof` + `eq_open_union_nat` (Mathlib,
  from `SecondCountableTopology.toHereditarilyLindelof`, automatically
  instantiated on `OSub r`) give the countable enumeration `cl`.  This is
  the countable-exhaustion input of the arc/circle classification route
  (next slices recorded in ROADMAP S107).
* `OChartExhaustion.lean` — **Milestone-2 (iv) step 6, brick (b): the
  exhaustion of a component by chart traces — first exhaustion lemma**
  (`Submission/OChartExhaustion.lean`, 129 lines, sorry-free,
  warning-free, imported by Submission.lean).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): the generic exhaustion set
  arithmetic `exhaustionStep C tr n` (`Eₙ = (⋃_{m<n} tr m) ∩ C`),
  `exhaustionStep_subset` (`Eₙ ⊆ C`), `exhaustionStep_mono` (`Eₙ ⊆
  Eₙ₊₁`), and `subset_iUnion_exhaustionStep_of_cover` (a family covering
  `C` gives `C ⊆ ⋃ₙ Eₙ`, witnessed at `E_{m+1}` for the covering index
  `m`); the chart-trace set `OChartTraceSet h hqf hgp x` (the trace of
  the interval chart at `x` as a set of `OSub r`), and
  **`component_chart_exhaustion`**: from `component_countable_chart_cover`
  (S107) one obtains `cl : ℕ → OSub r` (all `cl n` in the component) such
  that the chart-trace steps `Eₙ = (⋃_{m<n} trace(cl m)) ∩ C` are
* `ChartTracePath.lean` — **Milestone-2 (iv) step 6, brick (b): chart
  traces of the trisecant set are path-connected open sets with interval
  coordinates — the instantiation input of the walk/exhaustion ordering
  (S114)** (`Submission/ChartTracePath.lean`, 195 lines, sorry-free,
  warning-free, imported by Submission.lean).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): **`chartInterval_pathConnected`** —
  an open interval of `ℝ` as a subtype (`{t : ℝ // t ∈ Ioo lo hi}`) is a
  path-connected space for `lo < hi` (straight-line paths between
  parameters stay inside the open interval by the convexity lemmas
  `seg_mem_Icc`/`seg_mem_Ioo` — elementary real arithmetic with a case
  split on the order of the endpoints); **`chartTrace ch`** (the trace of
  an `OSub1Chart` as a set of `OSub r`), **`chartTrace_eq_range`** (the
  trace is the range of the chart's class map `t ↦ (ch.homeo t).1`),
  **`chartTrace_pathConnected`** (the trace is path-connected — the
  continuous image of the path-connected interval), **`chartTraceHomeo`**
  (the interval parametrisation of the trace, definitionally the chart
  homeo), `isOpen_chartTrace`, and the S107-cover instance
  **`oChartTrace_pathConnected`** (every `OChartTraceSet h hqf hgp x` is
  path-connected).  These are exactly the hypotheses that
* `ComponentWalk.lean` — **Milestone-2 (iv) step 6, brick (b): the
  component chart-trace walk — the S113 overlap-walk machinery
  instantiated over the S107 chart-trace cover of a component (S115)**
  (`Submission/ComponentWalk.lean`, ~230 lines, sorry-free, warning-free,
  imported by Submission.lean).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): `ComponentSub c₀` (a connected
  component of the trisecant set as the subspace
  `{y : OSub r // y ∈ connectedComponent c₀}`, with the global instance
  `preconnectedSpace_componentSub`), `isOpen_OChartTraceSet`, and
  `OChartTrace_subset_component` (the chart trace at `x` lies in the
  component of `x`: path-connected, hence connected, containing its
  centre — via `chartTrace_subset_connectedComponent` (S114) and
  `connectedComponent_eq`); the headline **`component_trace_walk`**: over
  a component, an S107 cover family `cl` and an overlap walk `e` of its
  trace indices (`e 0 = 0`, surjective; consecutive traces overlap) whose
  partial unions `⋃_{m < n+1} OChartTraceSet (cl (e m))` are
  path-connected, lie in the component, are increasing, and exhaust the
  component.  Proof: instantiate `ConnectedWalk.exists_pathConnected_open_exhaustion`
  on the subspace cover `U n = {p : ComponentSub c₀ | (p : OSub r) ∈
  OChartTraceSet (cl n)}` (open, nonempty, covering, path-connected —
  the latter via `IsInducing.isPathConnected_iff` over the embedding
  `ComponentSub c₀ → OSub r` and `Subtype.image_preimage_val`, since the
  trace lies inside the component), then transfer the exhaustion unions
  back to the ambient trace sets by the same embedding (`val '' V n =
  trace union`).  This is the completed topological skeleton of the
* `IntervalChartU.lean` — **Milestone-2 (iv) step 6, brick (b): the
  monotone-coordinate overlap hinge of the interval-chain glueing (S116)**
  (`Submission/IntervalChartU.lean`, 148 lines, sorry-free, warning-free,
  imported by Submission.lean).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): `mem_chartTrace` (trace membership
  = band membership in `W`), `oChartTraceOverlapParam` (the
  `ch₁`-coordinate of a class `z` in the overlap of two chart traces,
  packaged into the transition domain `ch₁ → ch₂`, with the lift lemma),
  and the headline **`oChart_trace_overlap_monotoneNbhd`**: for two
  interval charts whose traces overlap at `z`, there is an
  `OChartMonotoneNbhd` (S102) at the `ch₁`-coordinate of `z` — an open
  piece of the first interval on which the real coordinate relabelling to
  the second chart is strictly monotone in one direction, continuous and
  injective, and on which every parameter's class lies in both traces
  (`nb.dom` + `mem_chartTrace`) with the relabelling value equal to the
  `ch₂`-coordinate of the same class (`oChartNbhd_piece_coordinate`): the
  two `chartTraceHomeo` interval coordinates are order-compatible on the
  overlap piece.  Plus the `MonoPiece` builder
  **`oChartJunctionMonoPiece`** (a hinge neighbourhood as a
  `ChainTransport.MonoPiece` datum, feeding
  `chain_transport_monotone_direction`/`chain_transport_injective` of the
  S111 engine) and its monotonicity lemma.  This is the per-junction
  local glue of the exhaustion construction: applied at the overlaps of
  the S115 component walk it gives the monotone pieces over which the
* `IntervalChainU.lean` — **Milestone-2 (iv) step 6, brick (b): the
  atomic one-step extension of the interval-coordinate transport — the
  composite over two junctions is the genuine class-coordinate transport
  (S117)** (`Submission/IntervalChainU.lean`, 103 lines, sorry-free,
  warning-free, imported by Submission.lean).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): the headline
  **`oChart_two_step_composite_class_coordinate`**: with S102 monotone
  neighbourhoods at two consecutive transitions `ch₁ → ch₂ → ch₃` and a
  first-piece parameter whose transport lands in the second piece (the
  S110 `oChartTwoStepMap` step domain), the composite transport value is
  the `ch₃`-coordinate of the same trisecant class as the original
  `ch₁`-parameter: each piece's value is the next chart's coordinate of
  the same class (S102 `oChartNbhd_piece_coordinate` at both steps), the
  transported parameter equals that coordinate by value, and the second
  piece value is the `ch₃`-coordinate of the same class again — the
  coordinate semantics survive two-step composition.  Together with the
  S110 monotonicity/injectivity of the composite
  (`oChart_two_step_composite`) this is the atomic extension step of the
  exhaustion induction (interval-charted `Uₙ` covering `Eₙ` built by
  carrying the genuine class coordinate along the walk).  The S117
  S117–S119: the module also carries the finite-chain identification:
  `range_map_cons`, `map_eq_of_pointwise`, `chainValue_of_list_eq`,
  `chainValue_one`, `chainValue_cons`, the def-reducible tail-list
  **`chainTail p k n`** (so the S111 `chainValue` recursion reduces
  definitionally along the chain), `chain_transport_class_coordinate_base`
  (the `N = 0` base case), and the headline
  **`chain_transport_class_coordinate`** — the FULL finite-chain
  identification: for charts `ch i`, junction pieces `p i` with `hsub`
  and the S116 semantics `hsem`, the iterated transport of the S111
  engine over the `n+1` pieces `p k, …, p(k+n)` sends a starting
  parameter to the `ch (k+n+1)`-coordinate of the same class as the
  `ch k`-parameter (proved by induction on `n`: base = `hsem k` +
  `chainValue_one`; step = def-reducible cons recursion `rfl`,
  IH at `k+1`, class via the `hsem` conjunct at `k`, chart-index rewrite
  by `omega`).
* `OChartFiniteGluing.lean` — **Milestone-2 (iv) step 6, brick (b):
  finite-family gluing — the local embedding of interval pieces (first
  subgoal of the interval-chain exhaustion)** (`Submission/OChartFiniteGluing.lean`,
  110 lines, sorry-free, warning-free, imported by Submission.lean).
  Content (namespace LeanEval.KnotTheory.Quadrisecant):
  **`MonotoneOnPiece.injective`** — a map monotone in one direction on an
  open interval piece is injective (strictly increasing or strictly
  decreasing, by contradiction via the real-order trichotomy); and
  **`oChart_piece_embedding`** — the local gluing identification: on the
  interval piece of an S102 monotone neighbourhood, the coordinate
  transport from `ch₁` to `ch₂` is `MonotoneOnPiece`, injective,
  continuous, and its values are the `ch₂`-coordinates of the same
  classes as the `ch₁`-parameters (S102 `OChartMonotoneNbhd`, S103
  `oChartNbhd_piece_coordinate`, S104 engine, packaged as one lemma).
  The module doc records the finite-family gluing statement of the draft
  (iterated transport over a chain of aligned monotone pieces is a
  well-defined monotone injective coordinate; gluing into one interval
  additionally needs connected overlaps — no circle-like wrapping — which
  is where the compact/non-compact dichotomy enters), per the honest
  S106/S107 scoping notes.
* `ChainTransport.lean` — **Milestone-2 (iv) step 6, brick (b):
  finite-chain gluing — iterated transport along a chain of aligned
  monotone patches (third subgoal of the interval-chain exhaustion)**
  (`Submission/ChainTransport.lean`, 195 lines, sorry-free, warning-free,
  imported by Submission.lean).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): **`MonoPiece`** — a bundled open
  interval piece with a monotone-in-one-direction coordinate map
  (`lo hi : ℝ`, `τ : ChartInterval lo hi → ℝ`, `hmono : MonotoneOnPiece τ`);
  generic `MonotoneDirectionOn` composition engine —
  **`MonotoneDirectionOn.comp_of_coord`** (transport `f : D → E` monotone
  as a coordinate map `cE∘f` in `cD`, then `g` monotone in `cE` ⇒ `g∘f`
  monotone in `cD`; the four direction combinations) and
  **`MonotoneDirectionOn.coord_eq`** (pointwise coordinate change);
  **`transports`** (alignment predicate: a parameter transports through
  the rest of the chain iff each step's value lands in the next piece's
  interval, recursive with existential membership witnesses);
  **`ChainDomain`** (chain-start parameters: first-piece elements whose
  transport exists), **`chainCoord`** (start parameter's real value;
  `chainCoord_injective` by two `Subtype.ext`s), **`chainValue`** (the
  transported coordinate after all patches, by recursion on the chain);
  **`chain_transport_monotone_direction`** — the iterated transport is
  monotone in one direction with respect to the starting coordinate
  (induction: one-piece case = the patch's monotonicity on its subtype
  domain; cons case = composition engine + the recursion equation
  `chainValue (p :: q :: rest) x = chainValue (q :: rest) ⟨⟨p.τ x.1, …⟩,
  …⟩`), and **`chain_transport_injective`**.  Pure combinatorial engine
  (no path/chart geometry), per the S106 scoping note; instantiation with
  S99/S105 junction data + S106 shrinking is the next slice.
* `IntervalCoverU.lean` — **Milestone-2 (iv) step 6, brick (b): the
  interval-charted covering of the component — finite-chain prefix
  transport over the walk, packaged (S120)** (`Submission/IntervalCoverU.lean`,
  295 lines, sorry-free, warning-free, imported by Submission.lean).
  Content (namespace LeanEval.KnotTheory.Quadrisecant): the packaged
  engine **`chain_prefix_transport_summary`** — over a prefix
  `p k :: chainTail p k n` of an aligned piece chain (S119 hypotheses
  `hsub`, `hsem`) the chain value is monotone in one direction w.r.t. the
  starting parameter coordinate, injective, and is the class-coordinate
  transport (the `ch (k+n+1)`-coordinate of the same class as the `ch k`-
  parameter) — the three conjuncts the exhaustion reads off each prefix;
  the **walk instantiation** (the bridge from the S115 component walk to
  the S119 hypotheses): `walkChart` (chart at walk class `cl (e i)`),
  `walkOverlapClass` + `walkOverlapClass_mem_left/right` (overlap class of
  the consecutive traces, with trace memberships), `walkJunctionNbhd`
  (the S116 hinge choice at each junction), `walkJunctionPiece` (the
  MonoPiece at each junction), and the two hypothesis families
  `walkJunction_subset` / `walkJunction_semantics` (each piece interval
  embeds into the left chart interval; each piece parameter's class stays
  in the next trace and the piece value is the next chart's coordinate of
  the same class); and the headline **`walk_prefix_summary`** — from the
  S115 walk overlap data alone, for every prefix of `n+1` junctions
  starting at walk position `0`, the chain value over the prefix is
  monotone/injective and equals the `ch (n+1)`-coordinate of the same
  class (the `k = 0` instance of the packaged engine on the walk data —
  the input interface the interval-charted `Uₙ` covering consumes).
  NEXT (recorded in the ROADMAP): the S106-style alignment (shrinking)
  choosing the pieces so transports land in the next piece over the whole
  finite stretch, then the covering lemma (`Eₙ`/partial union ⊆
  interval-charted open `Uₙ` with the monotone injective coordinate).
* `ChainAlignment.lean` — **Milestone-2 (iv) step 6, brick (b): the
  chain alignment (shrinking) slice — sub-pieces along which every
  transport lands forward (S121)** (`Submission/ChainAlignment.lean`,
  242 lines, sorry-free, warning-free, imported by Submission.lean).
  Content (namespace LeanEval.KnotTheory.Quadrisecant): `mono_restrict`
  (restricting a `MonotoneOnPiece` map to a sub-interval keeps the
  monotonicity) and **`subMonoPiece`** (a piece cut down to a sub-interval
  of its interval, same coordinate map restricted; `subMonoPiece_τ` — the
  `τ` of the sub-piece is the restriction of the `τ` of the piece);
  **lemma 1 — `exists_subpiece_landing`** (single-step shrinking: if
  `p.τ` sends a parameter `x₀` into the interval of the next piece `q`
  (`p.τ x₀ ∈ Ioo q.lo q.hi` — the one-step transport lands in `q`), then
  — `p.τ` being continuous — it sends a whole sub-piece of `p` around
  `x₀` into the interval of `q`; the S106 real shrink packaged at the
  piece level with the sub-interval explicitly inside the domain of `p`);
  **`IsSubPiece`** (the correspondence: `s` is `r` cut down to a
  sub-interval) and **`AlignedTotality`** (recursive forward totality:
  from every element of every piece of the list, the transport through
  the remaining pieces is defined); **lemmas 2 + 3 —
  `exists_aligned_subpieces`** (backward-aligned sub-pieces: given pieces
  `p :: rest` and a start parameter `x₀` of `p` whose full forward orbit
  exists (`htr : transports p rest x₀`), there are sub-pieces `sp :: qs`
  — `sp` a sub-piece of `p` containing `x₀`, `qs` the sub-pieces of the
  corresponding `rest` pieces in order (`List.Forall₂ IsSubPiece`) —
  along which every transport lands forward (`AlignedTotality (sp ::
  qs)`); built backwards from the last piece: consume the orbit one step
  (`rcases htr`), recurse on the tail chain from the next orbit point,
  pull the next sub-piece's interval back through the continuous map).
  Honest framing (as at S106): `htr` is genuine data (not automatic) —
  an alignment exists exactly when an orbit does; the module's value is
  that an orbit extends to WHOLE sub-pieces with forward totality.
  S125 opener (appended): the explicit sub-piece data layer —
  `SubDatum p` (an interval + the embedding proof), `datumPiece` (the
  sub-piece `subMonoPiece p d.sub`; `(datumPiece d).τ` is DEFINITIONALLY
  the restriction of `p.τ` — `datumPiece_τ` by `rfl`), `datumPiece_lo/hi`,
  `IsSubPiece_datumPiece`, and `exists_subdata_landing` (the single-step
  shrink in datum form) — the `rfl`-level foundation of the S125 refactor
  that dissolves the dependent-`MonoPiece.τ` rewrite blocker of the
  `hsem` transfer.
  S126 (appended): the data-alignment layer — `SubDataFor : List
  MonoPiece → Type` (the dependent data list positionally aligned with a
  piece list: `SubDatum r` per head, recursive for the tail), the piece
  map `datumPieces`, the recursive forward-totality predicate
  `SubDataTotality`, and the headline **`exists_aligned_subdata`** — the
  `SubDatum` form of the S121 backward induction: given pieces `p :: rest`
  and an orbit `htr`, `∃ d0 : SubDatum p, ∃ tail : SubDataFor rest`, with
  `x₀ ∈ Ioo d0.lo d0.hi`, forward totality from `datumPiece d0` through
  `datumPieces tail`, and `SubDataTotality tail` — the aligned pieces are
  `datumPiece`s (definitional τ-restrictions), the explicit-data
  foundation of the S125 refactor.
  S140c (piece level, appended): **`exists_subdata_landing_within`** — if
  `p.τ x₀` lands in `q`'s interval and `J` is a datum of `p` containing
  `x₀`, there is a datum `d` of `p` with `x₀ ∈ d`, `Ioo d ⊆ Ioo J`, and
  the whole piece of `d` mapping into `q`'s interval (intersect the S127
  landing datum with `J`: `max`/`min` bounds — `max_lt_iff`/`lt_min_iff`
  for the membership, order-chain lemmas for the two subsets; the
  landing property is inherited by subsets) — the pure shrink that makes
  consecutive head intervals nest.
* `WalkAlignment.lean` — **Milestone-2 (iv) step 6, brick (b): the
  shrinking slice instantiated on the S115 component walk (S122)**
  (`Submission/WalkAlignment.lean`, 161 lines, sorry-free, warning-free,
  imported by Submission.lean).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): **`walkJunctionPiece_continuous`** —
  the coordinate map of a walk junction piece is continuous (the S102
  continuity of the interval-piece transition, read at the piece level:
  supplies the `hcont` hypothesis of the alignment machinery);
  **`chainTail_mem_iff`** (membership in `chainTail p k n` = the indexed
  family `p (k+j+1)`, `j < n`) and **`chainTail_continuous`** (continuity
  of every piece of a tail chain from the pointwise family — the list/ℕ
  bookkeeping for walk prefixes); and the packaging theorem
  **`walk_prefix_alignment`**: if a start parameter `x₀` of the first
  walk junction piece has a full forward orbit through the next `n`
  junction pieces, there are sub-pieces — `sp` a sub-piece of piece `0`
  containing `x₀`, `qs` the corresponding chain sub-pieces — along which
  every transport lands forward (`AlignedTotality (sp :: qs)`).  NEXT
  (recorded in the ROADMAP): the covering lemma — converting the aligned
  list back to the ℕ-family of `chain_transport_class_coordinate` and
  showing the partial union lies in the interval-charted set.
* `AlignedFamily.lean` — **Milestone-2 (iv) step 6, brick (b): the
  list → ℕ bridging — rebuilding the ℕ-indexed piece family from an
  aligned head and tail list (S123)** (`Submission/AlignedFamily.lean`,
  214 lines, sorry-free, warning-free, imported by Submission.lean).
  Content (namespace LeanEval.KnotTheory.Quadrisecant):
  **`familyFromAligned p sp qs`** — the ℕ-family rebuilt from an aligned
  head and tail list (`q 0 = sp`, `q (j+1) = qs[j]` via `List.getD` with
  default `p (j+1)`, so past the list the family falls back to `p`):
  `familyFromAligned_zero`, `_succ`, `_get` (the in-list values), and
  `familyFromAligned_beyond` (the past-list values, via
  `List.getD_eq_default`); the tail-chain arithmetic `chainTail_length`
  (`(chainTail p k n).length = n`) and `chainTail_get_eq` (the elements
  of `chainTail p k n` are `p (k+i+1)`; induction with the index proofs
  handled by `change` + `List.get_cons_succ`, since `rw` cannot rewrite
  under a proof-carrying `get` index); the bridging lemma
  **`chainTail_familyFromAligned`**: if `qs.length = n` then
  `chainTail (familyFromAligned p sp qs) 0 n = qs` (`List.ext_get`:
  lengths by `chainTail_length`, elements by `chainTail_get_eq` +
  `familyFromAligned_get`) — the tail of the rebuilt family is exactly
  the aligned list, so `ChainDomain (q 0 :: chainTail q 0 n)` is the
  aligned `ChainDomain (sp :: qs)`; `forall₂_length_eq` (a `Forall₂`
  correspondence forces equal lengths); and the walk instance
  **`walk_aligned_family`**: from the S115 walk data and an orbit `htr`
  through the first `n` walk junction pieces, `∃ q`, `q 0` a sub-piece of
  walk piece `0` containing `x₀`, `chainTail q 0 n` aligned against
  `chainTail (walkJunctionPiece …) 0 n` (`List.Forall₂ IsSubPiece`), with
  forward totality `AlignedTotality (q 0 :: chainTail q 0 n)` — the exact
  shape the covering lemma consumes (walk data + totality over the whole
  aligned prefix + correspondence to the original chain in one bundle;
  assembled from `walk_prefix_alignment` + `chainTail_familyFromAligned`
  + `forall₂_length_eq`).  NEXT (recorded in the ROADMAP): feed `q` into
  `chain_transport_class_coordinate` (transfer `hsub`/`hsem` to the
  sub-piece family), then the partial-union covering statement.
* `AlignedCover.lean` — **Milestone-2 (iv) step 6, brick (b): the
  covering slice stage 1 — the aligned family with explicit data and the
  `hsub` transfer (S124)** (`Submission/AlignedCover.lean`, 367 lines,
  sorry-free, warning-free, imported by Submission.lean).  Content
  (namespace LeanEval.KnotTheory.Quadrisecant): `forall₂_subPiece_chainTail`
  (positional `IsSubPiece` from a `Forall₂` against a chain tail, via
  Mathlib's `List.Forall₂.get`) and **`exists_alignedWalk_data`** (from
  walk overlap data + orbit `htr`: `∃ q sp qs`, `q = familyFromAligned w
  sp qs`, `q 0` a sub-piece of walk piece `0` containing `x₀`,
  `AlignedTotality (q 0 :: chainTail q 0 n)`, the `Forall₂ IsSubPiece`
  correspondence, `qs.length = n`); the chosen objects
  `alignedWalkQ`/`alignedWalkSp`/`alignedWalkQs` with
  `alignedWalkQ_full_spec` and projections (`alignedWalkQ_eq_family`,
  `_sub0`, `_mem0`, `_totality`, `_corr`, `alignedWalkQs_length`);
  `subPiece_self` (every piece is a sub-piece of itself) and
  **`alignedWalkQ_subPiece_all`** (`IsSubPiece (q i) (p i)` for ALL `i`:
  prefix via the correspondence, beyond via the `familyFromAligned`
  fall-back); and the **`hsub` transfer** **`alignedWalkQ_chart_subset`**
  (`Ioo (q i).lo (q i).hi ⊆ Ioo (ch i).lo (ch i).hi` for all `i` — the
  S119 `hsub` hypothesis for the aligned family).  Honest status (S125):
  the `hsem` transfer needs a contained refactor — `MonoPiece.τ`'s
  dependent domain blocks `rw`/`erw`/`cases` on the ∃-witness equality
  `q i = subMonoPiece (p i) hsubᵢ` for the opaque chosen `q`; carry the
  sub-pieces as explicit per-index data `(aᵢ,bᵢ,hᵢ)` with
  `q i := subMonoPiece (p i) hᵢ` (then τ-restriction is `rfl`), and the
  S119 application (`alignedWalkQ_chain_identification`) + reach-the-end
  covering statement assemble by composition.
  S126 step (2) (appended): the walk-prefix aligned sub-data —
  `subDatum_refl` (whole-interval datum), `datumPiece_refl`,
  `transports_congr_piece` (the `cases`-based transport of the transport
  predicate across a piece equality — avoiding every `MonoPiece.τ`
  dependent rewrite), `chainTail_congr_right` (chain tails of function
  families agreeing past `k` are equal), and the headline
  **`exists_walk_aligned_subdata`**: from walk overlap data and an orbit
  of a start parameter of piece `k` through the next `n` junction pieces,
  `∃ d0 : SubDatum (w k), ∃ sub : (i : ℕ) → SubDatum (w i)`,
  `sub k = d0`, `x₀ ∈ Ioo d0.lo d0.hi`, and forward totality from
  `datumPiece d0` through `chainTail (fun i => datumPiece (sub i)) k n` —
  per-index data typed at the CONCRETE walk pieces, so `datumPiece (sub
  i)` restricts `w i` definitionally (the S119-style backward induction;
  totality closed by `transports_congr_piece`).  NEXT (S127): reopen the
  `hsem` transfer (value conjunct = `datumPiece_τ`/`rfl`) and the S119
  application.
  S128 steps (1)–(2) (appended): the `hsem` transfer reopened at the
  datum level — `datumPiece_chartSubset` (the datum interval → walk
  interval → chart interval embedding: the S119 `hsub` for `datumPiece
  d`) and **`datumPiece_semantics`** (the full S119-`hsem` statement for
  a datum piece: the class of the `ch i`-parameter lies in the next
  trace, with a transition element whose lift is that class and whose
  real value is `(datumPiece d).τ u`) — the VALUE conjunct closes by
  `datumPiece_τ` (definitional, `rfl`-level), and the membership/lift
  conjuncts transfer by the equal-real-value element equality
  (`Subtype.ext` on the two chart-interval elements with equal real
  values).
  S129 (appended): the S119 application on the datum family —
  **`walkAligned_reaches_end`**: from walk overlap data and an orbit
  `htr` through the first `n` junction pieces, `∃ d0 : SubDatum (w 0),
  ∃ sub : (i : ℕ) → SubDatum (w i)`, `sub 0 = d0`, `x₀` in the aligned
  head interval, and every class parametrised by the aligned start
  interval (over `datumPiece (sub 0)`) lies in the trace of the
  `(n+1)`-th chart — the class-coordinate identification of S119 applied
  to the datum family `q i := datumPiece (sub i)` with the datum-level
  `hsub`/`hsem` (`datumPiece_chartSubset`, `datumPiece_semantics`), the
  totality transported to the head piece by `transports_congr_piece`
  (via `hpp : datumPiece (sub 0) = datumPiece d0` from `sub 0 = d0`).
  S130 (appended): the interval-charted arc — `walkAlignedArcMap`
  (the `ch 0`-lift of an aligned-start-interval parameter through the
  datum chart embedding), **`walkAligned_arc_reaches_end`** (from walk
  data + orbit: `∃ sub`, `x₀` in the aligned start interval, and every
  arc class lies in the trace of `ch (0+n+1)` — the arc form of
  `walkAligned_reaches_end`), and **`walkAlignedArcMap_injective`** (the
  arc has no self-intersections, via `oChartLift_injective`).
  S131 (appended): the orbit class in every prefix trace —
  `transports_chainTail_prefix` (transporting through a longer chain
  transports through any prefix) and **`walkOrbitClass_mem_traces`**: the
  class of the orbit-start parameter lies in `chartTrace (ch (0+i+1))`
  for every `i ≤ n` (the S119 identification applied at each prefix
  length — the deep-intersection content the exhaustion uses).
  S132 (appended): the arc as a continuous injective interval-chart at
  the orbit class — `continuous_oChartLift`, `continuous_walkAlignedArcMap`
  (the arc map is continuous), `walkAlignedArcMap_at_orbitClass` (the arc
  value at the orbit parameter is the orbit class — `rfl` by proof
  irrelevance of the equal-real-value memberships), and
  **`walkAligned_arcChart_at_orbit`** (∃ `sub`, the orbit parameter lies
  in the aligned start interval, the arc map is injective and continuous
  and sends the orbit parameter to the orbit class — which by S131 lies
  in every prefix chart trace).
  S133 (appended): the exhaustion-covering overlap —
  **`walkAligned_covering_overlap`**: for a walk prefix with an orbit
  `htr`, `∃ sub` whose aligned start interval contains the orbit
  parameter and whose arc map is injective, continuous, anchored at the
  orbit class (the arc value at the orbit parameter is the orbit class),
  and contained in the overlap of the start chart's trace with the far
  chart's trace `ch (0+n+1)` — the arc interval-chart bridges the
  exhaustion region to the next chart's trace around the common anchor
  class.
  S134/S135 (appended): the orbit-extension slice — pure
  `transports_extend` (ChainAlignment): an `n`-tail transport whose
  chain value lands in the next piece `p (k+n+1)` extends to an
  `(n+1)`-tail transport (induction with `revert k`; the step uses
  `htr.choose`/`htr.choose_spec` directly so the chain-value recursion
  equation closes by `rfl` — no proof-irrelevance rewrite needed; base
  case `simp [transports, chainTail]` since `simp` cannot unfold the
  stuck `chainTail p (k+1) 0` head); and the walk-level consequence
  **`walkOrbit_extend`** (orbit through `n` junction pieces + far-end
  chain value landing in `w (n+1)` ⇒ orbit through `n+1` pieces — the
  `transports_extend` instance at the walk, index `0+n+1 = n+1` bridged
  by `omega`/`simpa` since `Nat.zero_add` is not rfl) with its re-run
  **`walkOrbit_extend_reaches_end`** (the extended orbit feeds the
  alignment machinery at length `n+1`: `∃ sub`, `x₀` in the aligned
  start interval, and every arc class lies in the trace of
  `ch (0+(n+1)+1)` — the one-step extension of the interval-charted
  exhaustion arc; the far-end landing itself is where the
  component/curve hypothesis enters).
  S136 (appended): the all-lengths iteration — **`walkOrbit_all_lengths`**
  (under a UNIFORM landing hypothesis — whenever an orbit through `n`
  junction pieces exists, its chain value lands in `w (n+1)` — orbits
  through every prefix length exist; induction from the empty
  transport, extending by `transports_extend` at each step; the uniform
  hypothesis is the interface where the component/curve content plugs
  in) and **`walkOrbit_all_lengths_covering`** (the S133 covering
  overlap runs at every prefix length: for each `n`, datum `sub` whose
  aligned start interval contains the orbit parameter, arc injective /
  continuous / anchored at the orbit class / inside trace₀ ∩ trace
  `(0+n+1)` — the per-length exhaustion-covering data).
  S137 (appended): the arc in the component and in the walk partial
  unions — **`walkAligned_arc_subset_walkUnion`**: from walk data, an
  orbit `htr` through `n` pieces, and the first walk class in
  `connectedComponent c₀`, `∃ sub`, `x₀` in the aligned start interval,
  arc injective/continuous, every arc class in the component of `c₀`
  (the arc is inside `trace (ch 0)` ⊆ component of its centre, via
  `OChartTrace_subset_component`) and in the walk partial union
  `⋃_{m < n+2} OChartTraceSet (cl (e m))` (the arc reaches exactly the
  `(n+2)`-nd walk trace; `simpa [OChartTraceSet, chartTrace,
  walkChart]` bridges the trace forms) — the arc-side halves of
  `Eₙ ⊆ Uₙ ⊆ Uₙ₊₁` in walk-union form.
  S138 (appended): the per-length exhaustion arc datum —
  **`componentWalk_arcs_at_every_length`**: with all walk classes in
  `connectedComponent c₀` and the uniform landing hypothesis, every
  prefix length `n` carries datum `sub` (`x₀` in the aligned start
  interval; arc injective, continuous, anchored at the orbit class,
  contained in the component and in the walk partial union
  `⋃_{m < n+2} OChartTraceSet (cl (e m))`) — composition of the
  all-lengths orbits (S136) with the arc-in-component/partial-union
  theorem (S137); the input package the interval-chain exhaustion
  builder `Uₙ` consumes per length.
  S140c (appended): **`exists_walk_aligned_subdata_within`** — the S127
  aligned sub-data with the extra constraint that the head datum's
  interval lies inside a prescribed datum `J` of the start piece
  containing the orbit parameter: `∃ d0 sub`, `sub k = d0`,
  `Ioo d0 ⊆ Ioo J`, `x₀ ∈ d0`, forward totality — the backward
  induction threads `J` into the final head shrink
  (`exists_subdata_landing_within`); inner levels use the whole-interval
  constraint `subDatum_refl`; base case uses `J` itself (empty-tail
  totality).  The per-step nesting "take the previous length's head
  interval, shrink to the next length, record the inclusion" is the
  instantiation at `k = 0` with `J` := the previous head datum and an
  orbit at the new length.

* `PrefixArcChart.lean` — **Milestone-2 (iv) step 6, brick (b): the
  per-length arc datum is an open interval-charted subset of the
  component (S139)** (`Submission/PrefixArcChart.lean`, 181 lines,
  sorry-free, warning-free, imported by Submission.lean after
  AlignedCover).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): `isOpen_paramCell` (the open
  parameter cell `{t | (t : ℝ) ∈ Ioo a b}` of a chart-interval space —
  real preimage of an open interval); **`isOpen_lift_cell`** (the
  chart-lift image of a parameter cell is open in `OSub r`: cell open,
  chart homeo open (`Homeomorph.isOpenMap`), and the trace-subtype
  projection is an open map since `chartTrace ch` is open
  (`IsOpen.isOpenMap_subtype_val`)); `walkAlignedArcMap_range_eq_liftCell`
  (the arc's range = the chart-lift image of its parameter cell — the
  classes whose `ch 0`-parameter lies in the aligned start interval);
  and the S139 headline **`walkAligned_arc_openSet`**: from walk overlap
  data, an orbit `htr` through `n` pieces, and `cl (e 0)` in the
  component of `c₀`, `∃ sub`, `x₀` in the aligned start interval, arc
  injective/continuous with OPEN range, range ⊆ component, range ⊆ walk
  partial union `⋃_{m < n+2} OChartTraceSet (cl (e m))`, and the orbit
  class in the range — the per-length arc datum turned into a covering
  interval chart (the `Eₙ ⊆ Uₙ` covering of an exhaustion step by this
  chart's range is the ordering slice, ROADMAP S139).
  S140a (appended): the arc IS an interval-chart of its range —
  `homeo_range_of_continuous_injective_isOpenMap` (generic: continuous
  injective open map ⇒ homeo onto range, one line via
  `Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap` +
  `isEmbedding.toHomeomorph`); `isOpenMap_oChartLift` (the chart lift is
  open: trace-subtype projection open since `chartTrace ch` is open,
  after the chart homeo); `paramCellHomeo` (the parameter cell
  `{t : ChartInterval lo hi // (t : ℝ) ∈ Ioo a b}` ≃ₜ
  `ChartInterval a b`); `isOpenMap_paramEmbedding` (the sub-piece
  embedding is open — the cell homeo after the open cell inclusion);
  and **`walkAlignedArcMap_homeo_range`**: `ChartInterval a b ≃ₜ {c :
  OSub r // c ∈ range arc}` — the per-length datum as an explicit
  interval-chart (the T1 piece of the ROADMAP S140 ordering
  specification).
  S140b (appended): compatibility of nested per-length cell charts —
  **`walkAlignedArcMap_eq_of_nested`** (nested start intervals
  `Ioo a' b' ⊆ Ioo a b` ⇒ the class maps agree through the real-value
  reindexing: both are the `ch 0`-lift of the same real parameter),
  `walkAlignedArcMap_nested_range_mem` (nested ranges), and
  **`walkAligned_changeChart_of_nested`** (the change-of-chart triangle:
  `φ.symm ∘ range-embedding ∘ φ'` equals the interval reindexing
  `u ↦ ⟨(u : ℝ), hI u.2⟩` — the restriction of the `(n+1)` chart to the
  inner interval agrees with the `n` chart up to the change-of-chart
  map; the nesting hypothesis `hI` is genuine data — choosing nested
  sub-data across lengths is the S140c ordering step).
  S140d (appended): the arc theorems relativized to a GIVEN datum —
  **`alignedData_reaches_end`** (given `d0 sub`, `sub 0 = d0`, and
  forward totality `htot` through the `n`-tail datum chain, every class
  of the aligned start interval is reached in `ch (0+n+1)` with the
  class equality: the inner half of S129 run on a given datum — totality
  transported to the head by `transports_congr_piece` through `hpp`,
  then `chain_transport_class_coordinate` on the datum family) and
  **`alignedData_arc_openSet`** (the single-level S139 package for a
  given datum: arc injective, continuous, OPEN range, range ⊆ the
  component (via `OChartTrace_subset_component` at `cl (e 0)`), range ⊆
  the walk partial union `⋃_{m < n+2} OChartTraceSet (cl (e m))` (from
  the datum-relative reach), and the orbit class in the range) — so the
  per-length arcs built from the S140c NESTED datums carry the full
  property set; the S140b change-of-chart between consecutive nested
  lengths applies directly.

* `NestedFamily.lean` — **Milestone-2 (iv) step 6, brick (b): the nested
  per-length datum family (S140e)** (`Submission/NestedFamily.lean`, 189
  lines, sorry-free, warning-free, imported by Submission.lean after
  PrefixArcChart).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): **`NestedArcLevel`** (one level of
  the nested family: head datum `J` of the start piece containing `x₀`,
  full aligned datum `sub` with `sub 0 = J`, forward totality through
  the `n`-tail datum chain); `nestedArcLevel_zero` (length-`0` level,
  whole-interval head); **`nestedArcLevel_step`** (the recursion step:
  from a level of length `n` and an orbit at `n+1`, the next level whose
  head lies inside the previous — `Ioo L'.J ⊆ Ioo L.J`, exactly the
  S140b `hI` — via `exists_walk_aligned_subdata_within` at `k = 0`,
  packaged as a subtype with the inclusion); **`nestedArcLevel_family`**
  (the per-length levels by `Nat.rec`, stepping with the S136
  all-lengths orbit at `m+1`); and **`nestedArcLevel_family_nested`**
  (`Ioo (J (n+1)) ⊆ Ioo (J n)` for all `n` — unfold the recursion by
  `change`, read off the step's inclusion).  Each level feeds S140d
  `alignedData_arc_openSet` + S140a `walkAlignedArcMap_homeo_range`, and
  consecutive levels are S140b-compatible — the per-length cells of the
  exhaustion, compatibly nested.
  S141 (appended): the per-level cell family — **`nestedArcLevel_range`**
  (the level-`n` cell: the range of the level-`n` arc), `range_open`
  (open by S139), **`nestedArcLevel_cellChart`** (the S140a chart
  `ChartInterval (datumPiece (sub 0)) ≃ₜ {c // c ∈ cell}`),
  `nestedArcLevel_datum_head_subset` (the datum-piece form of the head
  nesting: `Ioo (J (n+1)) ⊆ Ioo (J n)` — the S140b `hI`), and
  **`nestedArcLevel_range_subset`** (cell `n+1` ⊆ cell `n`, via the S140b
  reindexing); `nestedArcLevel_mem_sub0` and **`nestedArcLevel_package`**
  (the S140d single-level package at the level: cell `n` ⊆ component,
  cell `n` ⊆ walk partial union `P'_{n+2}`, arc injective/continuous) —
  the interval-charted nested cells with their inclusions, i.e. the
  T2-shape objects read off the nested family (the E-side clause is in
  walk-union form: cell `n` ⊆ `P'_{n+2}`).
  S142 (appended): **`nestedArcLevel_cell_in_step`** — the F1 E-side
  covering clause: `cell n ⊆ P'_{n+2} ∩ C` (the two conjuncts of
  `nestedArcLevel_package` combined pointwise) — each level's cell is an
  interval-charted open subset of its exhaustion step inside the
  component; the increasing family itself (ROADMAP S142 statement F2)
  remains the design item, with the consecutive-cell change-of-chart
  (F3) being the S140b instantiation.
  S143 (appended): the F2 set side — **`walkPartialUnion`** (`P'_k :=
  ⋃_{m<k} T_m`, the candidate `Uₙ = P'_{n+2}`), `walkPartialUnion_mono`
  / **`nestedU_mono`** (`Uₙ ⊆ Uₙ₊₁`, pure `Iio` arithmetic), and
  **`nestedArcLevel_cell_in_U`** (`cell n ⊆ Uₙ`, F1 projected onto the
  union) — the cell-containment refinement on the set side; the charted
  side (interval-charting `Uₙ` by the monotone transport coordinate)
  remains the open ordering design content (ROADMAP S143 F2-b).
  S144 (appended): the transitive compatibility (S2 of the S144
  statement block) — **`nestedArcLevel_range_antitone`** (for `m ≤ n`,
  cell `n` ⊆ cell `m`: iterating the S141 consecutive inclusion) and
  **`nestedArcLevel_head_antitone`** (`Ioo (J n) ⊆ Ioo (J m)`: iterating
  `nestedArcLevel_family_nested`) — the multi-level change-of-chart is
  the iterated S140b reindexing, the structural core of the F2-b
  charting coordinate.
  S145 (appended): S1 of the S144 block is ALREADY in the commons
  (`OChartMonotone.interval_inj_continuous_monotone` +
  `OChartAssemblyMonotone.monotoneOnPiece_of_inj_continuous` — no
  delegation needed), and this section adds the multi-level coordinate
  agreement: **`nestedArcLevel_datum_head_subset_antitone`** (the
  S140b `hI` for any pair `m ≤ n`) and
  **`nestedArcLevel_arc_eq_antitone`** (a class of the level-`n` cell has
  the same real parameter in the level-`m` cell — the iterated S140b
  reindexing by induction over the consecutive equalities) — the
  coordinate consistency the F2-b charting coordinate requires.
  S146 (appended): the ordering pivot — **`nestedArcLevel_changeChart_antitone`**
  (the general change-of-chart triangle: for `m ≤ n`,
  `φₘ.symm ⟨arcₙ u, range-membership⟩ = ⟨(u : ℝ), hI u.2⟩` with the
  antitone head nesting as `hI` — the S140b triangle instantiated at the
  pair `(m,n)`); together with O1 (`nestedArcLevel_arc_eq_antitone`,
  S145) the family of cell charts is order-consistent (any two levels
  read the same real coordinate for a common class up to the
  identity-on-reals reindexing) — the pivot of the F2-b charting step,
  whose remaining (open) content is the sweep of `P'_{n+2}` by cells
  (the S106-flagged ordering core).
  S147/S148 (appended): the SWEEP decided and stated (S147-T: chart
  `P'_{n+2}` by the per-trace charts chained from the base chart through
  consecutive overlaps — the H1/H2/H3 hypotheses listed, the winding
  alternative flagged as the dichotomy's compact side; not proved), with
  the H1 monotone-order fact for connected open domains landed in the
  commons (L29: `Commons.Analysis.Order.ConnectedReal.injOn_continuousOn_monotoneOrAntitone`)
  and its subtype wrap **`monotone_or_antitone_on_connected_open`** (a
  continuous injective real map `g : ChartInterval lo hi → ℝ` on a
  connected open set `C` of the chart type is strictly monotone-or-
  antitone on `C` — via ambientizing `C` to its real-coordinate image:
  open since the coordinate projection of the open subtype `Ioo lo hi`
  is an open map, preconnected as a continuous image — then L29) — the
  (W) step of the S148 statement block, ready for the overlap-component
  transition instance (T).
  S149 (appended): **`transition_monotone_on_connected_open`** — the T
  overlap-component transition lemma (parametric): for two interval
  charts `ch₁ ch₂` and a connected open set `C` of the `ch₁`-interval
  whose classes all lie in `ch₂`'s trace, the `ch₂`-coordinate of the
  class is strictly monotone-or-antitone in the `ch₁`-coordinate on `C`
  (the S98 `oChartTransitionReal` is continuous/injective on the
  transition domain; extend to a total `g` agreeing on `C` with
  `oChartTransitionReal ∘ pack`, then apply the W wrap) — the H1 fact of
  the S147-T chaining, ready for the walk instance (`ch m`/`ch (m+1)`,
  the connected component of `walkOverlapClass m`).
  S150 (appended): the WI closure of the S147-T chaining —
  **`isOpen_connectedComponentIn_transitionDomain`** (CO: the connected
  component of a transition-domain parameter `t₀` inside `D := {x |
  (oChartLift ch₁ x) ∈ ch₂.W}` is open in the chart-interval type — the
  capped-interval proof: metric-ball neighbourhood in `D`, preimage of
  `Ioo (max lo (y.1−ε)) (min hi (y.1+ε))` open + preconnected via
  `IsPreconnected.preimage_of_isOpenMap`, then
  `IsPreconnected.subset_connectedComponentIn` + `connectedComponentIn_eq`;
  and **`walk_junction_transition_monotone`** (WI: at a walk junction
  `m`, on the connected component of the transition domain containing
  the `ch m`-coordinate of `walkOverlapClass m`, the `ch (m+1)`-
  coordinate relabelling `oChartTransitionReal (walkChart m)
  (walkChart (m+1))` is strictly monotone-or-antitone in the `ch m`-
  coordinate — the instance of `transition_monotone_on_connected_open`
  with `ch₁ := walkChart m`, `ch₂ := walkChart (m+1)`, `C` the component
  of `t₀`).  With H1 = WI in hand, the S147-T chaining's remaining items
  are the H2/H3 sweep bookkeeping (cells of `P'_{n+2}` each inside some
  chained chart + consecutive overlap classes), i.e. the S106-flagged
  ordering core of the F2-b charting.
* `WalkPartialUnion.lean` — **Milestone-2 (iv) step 6, brick (b): the
  walk partial-union API (open / path-connected / component-subset /
  trace-membership / overlap-class / covering)** (new module
  `Submission/WalkPartialUnion.lean`, 178 lines, sorry-free,
  warning-free, imported by Submission.lean after NestedFamily).
  Content (namespace LeanEval.KnotTheory.Quadrisecant), in the
  S135–S150 walk notation (`P'_k := ⋃ m ∈ Iio k, OChartTraceSet
  (cl (e m))`, `walkPartialUnion` of NestedFamily/S143):
  **`isOpen_walkPartialUnion`** (each `P'_k` open in `OSub r` — finite
  union of the open chart traces), **`walkPartialUnion_pathConnected`**
  (each `P'_{k+1}` path-connected — `IsPathConnected.union` induction
  over the chain of pairwise-overlapping traces, the overlap point of
  `T_n ∩ T_{n+1}` lying in `P'_{n+1}` through the left trace),
  **`walkPartialUnion_subset_component`** (under
  `hcl : ∀ n, cl (e n) ∈ C` each `P'_k` lies in `connectedComponent
  c₀`), **`walkTrace_subset_partialUnion`** (`m < k` ⇒ `T_m ⊆ P'_k`),
  **`walkOverlapClass_mem_partialUnion`** (the junction class
  `walkOverlapClass m` lies in `P'_{m+2}`),
  **`walkPartialUnion_covers_component`** (S107 cover property of `cl`
  + surjectivity of `e` ⇒ `C ⊆ ⋃ₖ P'_k`),
  **`walkPartialUnion_subset_of_le`** (`m ≤ k` ⇒ `P'_m ⊆ P'_k`),
  **`compact_subset_walkPartialUnion`** (compact `K ⊆ C` is absorbed by
  one partial union: `∃ k, K ⊆ P'_k`, via `IsCompact.elim_finite_subcover`
  + `Finset.le_sup`), and **`compact_component_in_partialUnion`**
  (compact component ⇒ `∃ k, C ⊆ P'_k`, the wraps-around marker of the
  circle side of the dichotomy).  With
  `walkPartialUnion_mono`/`nestedU_mono` (S143) this is the complete
  walk-side skeleton of the classification: an increasing open
  path-connected covering family of the component, instantiable on the
  `component_trace_walk` (S115) output.  (S151.)
* `OneManifold.lean` — **S153, the generic classification engine for
  the trisecant-set components: topological 1-manifolds and their
  countable open-arc covers** (new module `Submission/OneManifold.lean`,
  119 lines, sorry-free, warning-free, PURE Mathlib — no problem-specific
  imports; imported by Submission.lean before ComponentChart and by
  ComponentChart itself).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): **`OpenRealInterval lo hi`** — the
  open real interval `(lo,hi)` as a type (definitionally the chart
  interval `ChartInterval`); **`LocallyIntervalChart X`** — every point
  has an open neighbourhood homeomorphic to an open real interval;
  **`IsOneManifold X`** — Hausdorff + second countable + locally
  interval-charted (a topological 1-manifold without boundary); and the
  existence half of the exhaustion engine,
  **`countable_open_arc_cover`** — every 1-manifold is covered by
  countably many open arcs (`∃ A : ℕ → Set X`, each `A n` open and
  homeomorphic to an open real interval, `⋃ n, A n = univ`), proved by
  choosing an arc chart at every point and passing to a countable
  subcover via second countability (`eq_open_union_nat` through the
  hereditarily-Lindelöf instance).  This cover is NOT nested (a nested
  exhaustion exists exactly on the interval side of the dichotomy; the
  circle side is the compactness dichotomy) — the full dichotomy
  statement and slice plan are recorded in ROADMAP S153.
* `RealIntervalShape.lean` — **S162: the real-interval shape
  foundation of the dichotomy's interval side, slice (b2)/(d) at the
  real-coordinate level** (new module `Submission/RealIntervalShape.lean`,
  429 lines, sorry-free, warning-free, PURE Mathlib + the commons affine
  homeo L30; imported by Submission.lean after OneManifold).  Content
  (namespace LeanEval.KnotTheory.Quadrisecant): (1) **the
  classification** `open_preconnected_nonempty_ℝ_shape` — a nonempty
  open connected subset of ℝ is an open bounded interval `(a,b)`, an
  upper half-line `(a,∞)`, a lower half-line `(−∞,b)`, or all of ℝ —
  via `IsPreconnected.mem_intervals` + openness (ε-ball endpoint lemmas
  `isOpen_not_sup_mem`/`isOpen_not_inf_mem` eliminate the closed shapes
  `Icc`/`Ico`/`Ioc`/`Ici`/`Iic`); (2) **homeomorphisms to the open unit
  interval** `OpenRealInterval 0 1`: bounded via the commons affine homeo
  (L30), half-lines via translation/reflection to `(0,∞)` and the
  rational model `x ↦ x/(1+x)` (`homeo_Ioi_zero_openUnit`, inverse
  `y ↦ y/(1−y)`, both `Continuous.div₀`), and `ℝ ≃ (0,∞)` via
  `Real.expOrderIso.toHomeomorph` (subtype `OrderTopology` instances
  automatic through `orderTopology_of_ordConnected`);
  (3) **the headline** `open_connected_ℝ_homeo_openUnit` — every
  nonempty open connected subset of ℝ is homeomorphic to `(0,1)`;
  (4) **the union theorem** `open_connected_ℝ_union_homeo_openUnit` —
  the union of two nonempty open connected subsets of ℝ with nonempty
  intersection is again homeomorphic to `(0,1)` (the coordinate model of
  the two-arc gluing of slices b2/d); (5) **the compactness marker**
  `exists_eq_univ_of_compact_nested_union` — compact `univ` + nested
  open `U n` covering `univ` forces some `U k = univ` (the
  interval-side marker: a compact/circle ambient is never exhausted by
  proper open arcs); (6) **the non-compactness hinge**
  `not_compactSpace_openUnit` — the model arc `(0,1)` is NOT compact
  (the `U n = {x | x < 1 − 1/(n+2)}` cover has no finite subcover) and
  the corollary `not_homeo_compact_openUnit` — a compact space is never
  homeomorphic to `(0,1)`: together with (5) this pins the dichotomy
  (interval side = non-compact side; a compact connected component never
  carries a whole-space interval chart).  ROADMAP S162.
* `ChainUnionInterval.lean` — **S216: the real-coordinate limit step of
  the interval side** (new module `Submission/ChainUnionInterval.lean`,
  157 lines, sorry-free, warning-free, PURE Mathlib + RealIntervalShape;
  imported by Submission.lean after RealIntervalShape).  Content
  (namespace LeanEval.KnotTheory.Quadrisecant): (1)
  **`nested_chain_preconnected_iUnion`** / **`nested_chain_connected_iUnion`**
  — the union of a nested chain of nonempty (pre)connected sets in any
  topological space is (pre)connected (Mathlib
  `IsPreconnected.iUnion_of_chain` with the consecutive overlaps
  `U n ∩ U (n+1) = U n`); (2)
  **`nested_open_preconnected_ℝ_union_open_preconnected`** /
  **`nested_open_preconnected_ℝ_union_shape`** / (3) THE limit step
  **`nested_open_preconnected_ℝ_union_homeo_openUnit`** — the union of a
  nested chain of nonempty open preconnected subsets of ℝ is an open
  connected subset of ℝ (shape `Ioo`/`Ioi`/`Iio`/`univ`), hence
  homeomorphic to `(0,1)` via
  `open_connected_ℝ_homeo_openUnit` — the terminal identification of
  any exhaustion-to-interval assembly whose prefixes are interval-charted
  (the union of their coordinate images is such a nested chain);
  (4) **`not_isCompact_of_proper_nested_open_exhaustion`** /
  **`not_compactSpace_of_proper_nested_open_exhaustion`** — the
  properness marker, contrapositive of the S161 compactness marker: an
  exhaustion by PROPER open sets nested increasing forces
  non-compactness (how the interval side's `¬ CompactSpace` keeps the
  arc-prefix exhaustion from being absorbed at a finite stage).
  ROADMAP S216.
* `ChainUnionOrderedInitialSegment.lean` — **S217: ordered
  initial-segment chains — the data format of the exhaustion-to-interval
  assembly** (new module `Submission/ChainUnionOrderedInitialSegment.lean`,
  sorry-free, warning-free, PURE Mathlib + OneManifold/RealIntervalShape;
  imported by Submission.lean after ChainUnionInterval).  Content
  (namespace LeanEval.KnotTheory.Quadrisecant): (1) the real ordered
  initial segments — `Ioo0_subset_of_le`/`Ioo0_mem_of_le`,
  `reEmbedIoo0` (subtype re-embedding `(0,L) ↪ (0,L')`, identity on the
  value), `L_mono_of_le`, and **`agree_chain`** (consecutive coordinate
  agreement `i n = i (n+1) ∘ reEmbed` extends to any `n ≤ m` — the
  well-definedness spine of the assembly); (2) the limit interval —
  `sSup_rangeL_pos`/`sSup_rangeL_le_one`/`sSup_rangeL_bdd`
  (`0 < sSup (range L) ≤ 1`), **`union_Ioo_zero_range_eq`** (the
  monotone chain of initial segments fills `(0, sSup (range L))`),
  `exists_lt_of_mem_Ioo_zero_sSup`; (3) **T1 (real model of the one-sided
  terminal attachment)** — `terminalStrip_inter` (`(0,1) ∩ (a,b) = (a,1)`
  for `0 < a < 1 ≤ b`: the overlap is exactly the prefix's terminal
  strip, the engine's `hVend`), `terminalStrip_union`
  (`(0,1) ∪ (a,b) = (0,b)`: the `P ∪ V` extension model),
  `beyond_end_nonempty` (genuine extension `1 < b`),
  `terminalStrip_arc`/`extendedPrefix_arc` (new/extended arcs
  `≃ₜ (0,1)`); the ABSTRACT glue consuming exactly this data is already
  verified (`OverlapConn.terminalTwoChart_union_is_openInterval` S207 /
  `chain_step_prefix_interval_of_terminal` S208); (4) the ASSEMBLY
  (`chain_initialSegments_union_homeo`, delegated as commons fleet L35,
  in flight) — `X` exhausted by nested agreeing `(0,L n)`-embeddings is
  `≃ₜ (0, sSup (range L))`, whence `≃ₜ (0,1)` by
  `homeo_Ioo_openUnit` (corollary added when L35 lands).  Honest status:
  the open part of the interval side is unchanged — PRODUCING such data
  for the trisecant components (the T1-abstract/T2 end analysis); this
  module fixes the data format and verifies the final assembly hop.
  ROADMAP S217.
* `TerminalAttachment.lean` — **S218: T1-abstract — the one-step
  attaching-arc construction, statement + verified real-coordinate
  core** (new module `Submission/TerminalAttachment.lean`,
  sorry-free, warning-free, PURE Mathlib + OneManifold/OverlapConn/
  RealIntervalShape; imported by Submission.lean after
  ChainUnionOrderedInitialSegment).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): (1) **the target records** —
  `TerminalAttach P V κ s` (V meets the arc prefix P exactly over the
  terminal interval `(s,1)` of its coordinate — the bundled `hVend`),
  `OneStepTerminalExtension P κ` (proper open arc prefix ⇒ an open arc V
  attaching terminally with `V ∖ P ≠ ∅` — the one-step output the
  ordering needs), `TwoSidedStripCover P V κ` (V contains BOTH end
  strips `(0,a) ∪ (b,1)` of the prefix — the two-sided wrap data),
  `TwoSidedClosedWrap P κ` (wrap closes: `P ∪ V = univ`); (2) **the
  verified attach-glue** `glue_of_TerminalAttach` — TerminalAttach data
  ⇒ `P ∪ V` interval-charted (restatement of S207
  `terminalTwoChart_union_is_openInterval`): the one-step extension is
  reduced to PRODUCING the data; (3) **the real-coordinate wrap model**:
  `preconnected_overlap_with_unit` — every open arc of ℝ meets the unit
  prefix connectedly (no two-sided overlap in the line; shape cases +
  `max_lt_iff`/`lt_min_iff`), `twoSidedStrip_forces_cover_unit` — a real
  arc containing both end strips of `(0,1)` must contain the whole
  prefix (the two-sided cover closes over the middle), and
  `overlap_eq_unit_of_twoSidedStrip`.  Honest status: the ambient
  T1-abstract theorem ("every proper open arc prefix of a connected
  non-compact 1-manifold admits a one-step terminal extension") and the
  wrap-exclusion proof (a closed two-sided wrap makes the ambient
  compact) remain open one-dimensional analysis, recorded in ROADMAP
  S218 together with T2 (no-infinite-oscillation).  ROADMAP S218.
* `T1Abstract.lean` — **S219: T1-abstract, ambient statement — the
  one-step terminal extension of a proper arc prefix in a connected
  non-compact 1-manifold** (new module `Submission/T1Abstract.lean`, 149
  lines, sorry-free, warning-free, PURE Mathlib + OneManifold +
  TerminalAttachment; imported by Submission.lean after
  TerminalAttachment).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): (1) **the ambient target record**
  `AmbientOneStepTerminalExtension X` — `T2Space X → LocallyIntervalChart
  X → ConnectedSpace X → ¬ CompactSpace X → ∀ P κ, OneStepTerminalExtension
  P κ` (every open arc prefix of a Hausdorff locally-interval-charted
  connected non-compact space admits the one-step terminal extension of
  S218); (2) **verified peel** `proper_arc_prefix_has_boundary` — a
  proper open arc prefix of a CONNECTED space has a boundary point
  `(closure P \ P).Nonempty` (if `P` were closed it would be clopen,
  separating `isPreconnected_univ` into `P` and `Pᶜ`; the chart `κ`
  supplies the nonemptiness via `arc_prefix_nonempty` — the coordinate
  witness `(1/2)` transported by the homeo); (3) the supporting
  `complement_nonempty_of_ne_univ`.  The construction at the boundary
  point (chart setup, one-sided ⇒ end strip ⇒ TerminalAttach via the T2
  finite-component core L36, two-sided ⇒ TwoSidedClosedWrap ⇒ compact
  contradiction) is the open continuation, recorded in ROADMAP S219;
  **S220 (appended to this module)**: the chart-setup bridge —
  `chart_coord_mem_closure` (the coordinate `c₀ = ψ.symm ⟨y, hyU⟩` of a
  boundary point `y ∈ P̄` in the arc chart `ψ : (0,1) ≃ₜ U`, `U ∋ y`
  open, lies in the closure of the overlap-coordinate set `S` — via
  `closure_subtype` and `ψ.symm.image_closure`), `chart_coord_not_mem`
  (`c₀ ∉ S`), and `chart_real_coord_mem_closure` (the real-coordinate
  form consumed by the L36 strip core) — the bridge from the boundary
  point to the `hacc`-type strip hypothesis of the one-sided
  attachment.  ROADMAP S219/S220.
* `OneSidedAttach.lean` — **S221: the one-sided attachment — side
  condition from L36 + strip cut + geometric target** (new module
  `Submission/OneSidedAttach.lean`, ~200 lines, sorry-free,
  warning-free, PURE Mathlib + OneManifold/TerminalAttachment/T1Abstract
  + the L36 commons theorem; imported by Submission.lean after
  T1Abstract).  Content (namespace LeanEval.KnotTheory.Quadrisecant):
  (1) **the real-coordinate side-condition core (VERIFIED)** —
  `RightFreeAt S c` (no points of `S` in some right-neighbourhood of `c`:
  the one-sidedness side condition), `closure_left_accumulation_of_rightFree`
  (right-free + `c ∈ closure S` + `c ∉ S` ⇒ left accumulation — the L36
  `hacc`), **`left_strip_of_rightFree`** (THE side-condition glue:
  right-free + closure + finite local structure `hF` ⇒ end strip
  `(p,c) ⊆ S` — L36 fed by the accumulation lemma), and
  `strip_cut_left` (given the strip and right-freeness, the overlap of
  `S` with the cut interval `(p', c+δ)` is exactly the strip `(p',c)` —
  the real avatar of `V ∩ P ∩ U` being a clean strip); (2) **the
  geometric target (record)** `OneSidedBoundaryAttach` — at a boundary
  point `y ∈ P̄∖P` in an open arc chart `ψ : (0,1) ≃ₜ U`, with the
  overlap-coordinate set right-free at `c₀` and finitely structured,
  there is an open arc `V` attaching over an end strip of the prefix
  chart (`TerminalAttach P V κ s`, `V ∖ P ≠ ∅`; initial strips reversed
  by `t ↦ 1 − t`); `AttachingArcOutput` (the one-step existential output,
  = the content of `OneStepTerminalExtension` after its antecedents).
  Proof obligations documented: (i) S220 bridge + `left_strip_of_rightFree`
  ⇒ the end strip, (ii) `strip_cut_left` + `ψ` cut the arc `V`, (iii) the
  transition/end sub-lemma T1b (OPEN — maps the U-chart end strip to an
  end strip of `κ`; needs the T2 geometric no-oscillation input).
  ROADMAP S221; **S222 (appended)**: T1b crystallized and its core
  VERIFIED — `end_coords_reach_prefix_end`: in a Hausdorff space, if
  `A ⊆ P` is a strip of the arc prefix `P` (chart `κ`) with `y ∈ closure
  A`, `y ∉ P`, the set of κ-coordinates of `A` is not contained in any
  strict `(ε, 1−ε)` (it reaches a prefix end): proof via the commons L37
  compactness of `{ε ≤ r ≤ 1−ε}` in `(0,1)` (`closedInterval_inside_unit_open`),
  continuous-image compactness, closedness in the Hausdorff ambient, and
  the open-complement neighbourhood vs `y ∈ closure A`.  The transition
  role in `OneSidedBoundaryAttach` (U-side strip ⇒ prefix-end strip ⇒
  cut the attaching arc) is documented.  ROADMAP S222; **S223
  (appended)**: step (i)/(ii) VERIFIED — the strip → point-set transport
  and the end-reaches application: `stripPoints U ψ p c₀` (the ambient
  point set of the U-coordinate strip), `strip_coord_mem_closure` (the
  endpoint `c₀` in the closure of the coordinate strip, via the fleet L38
  `mem_closure_left_interval` + `closure_subtype`),
  **`stripPoints_mem_closure`** (the transport: `y ∈ closure stripPoints`
  — continuous chart coercion + `image_closure_subset_closure_image`),
  `stripPoints_subset` (`⊆ P`), and
  **`boundaryStrip_coords_reach_prefix_end`** (the application: the
  κ-coordinates of the strip point set reach a prefix end — T1b core with
  `A := stripPoints`).  Closes proof obligations (i)/(ii) of
  `OneSidedBoundaryAttach`; the attach cutting (iii) and the T2 geometric
  no-oscillation input remain (recorded in ROADMAP).  ROADMAP S223;
  **S224 (appended)**: step (iii) — the attach cutting from the prefix
  end: statement pinned + first subgoal VERIFIED.  `InitialAttach P V κ s`
  (initial-strip attach) / `EndStripAttach P V κ` (end-strip attach,
  initial or terminal) and **`AttachCuttingStatement`** (the
  theorem-shaped target: boundary point + one-sided right-freeness + T2
  finite structure + bridge ⇒ an open arc `V` with an end-strip attach
  over `κ` and `V \ P ≠ ∅`) are pinned; **`right_free_beyond_arc`** is
  VERIFIED (from the right-freeness of the overlap set at `c₀` there is a
  NONEMPTY beyond-arc `beyondArc U ψ c₀ δ` DISJOINT from `P` — the
  `V \ P` ingredient of the attaching arc; `δ` shrunk to
  `min δ₀ ((1−c₀)/2)` to stay inside the chart).  The assembly
  (prefix-end strip + beyond-arc + the arc through `y`, with the
  transition/end monotone-limit sub-analysis and the reversal
  normalization) is recorded in ROADMAP S224 with the T2 geometric
  no-oscillation input (consumption form fixed — delegable).  ROADMAP
  S224; **S225 (appended)**: step (iii-a) — the clean prefix-end strip
  (payoff VERIFIED): `boundaryStripCoordSet P U κ ψ p c₀` (the
  κ-coordinate set of the strip point set) and
  **`boundaryStrip_coords_end_strip`** — given the strip point set
  (`A ⊆ P`, boundary point `y ∉ P`, `y ∈ closure A`) whose coordinate
  set `T` is open/preconnected/nonempty (bridge outputs), `T` is a clean
  END STRIP `(a,1)` or `(0,b)` of the prefix coordinate — via the
  untrapped fact (`end_coords_reach_prefix_end`) and the fleet L39
  `open_preconnected_untrapped_unit_end_strip` (open preconnected
  nonempty `⊆ (0,1)`, untrapped ⇒ terminal or initial strip).  No
  monotone-limit argument is needed (openness + preconnectedness +
  untrapped suffice).  Remaining: the iii-a bridge (T open/preconnected/
  nonempty from the openness/connectedness of `stripPoints`), iii-b (the
  cutting assembly), iii-c (the T2 input).  ROADMAP S225; **S226
  (appended)**: step (iii-b) — the cutting assembly: statement pinned +
  first real-coordinate sublemma VERIFIED.  Terminal-subcase
  construction recorded (attaching arc `V := ψArc U ψ p (c₀+δ)` — the
  ψ-arc through the boundary point beyond the strip — with the four
  proof obligations); **`overlapStrip_rightFree_cut_at_left`** VERIFIED
  (`S ∩ (p, c₀+δ) = (p,c₀)` from the strip + `c₀ ∉ S` + right-freeness —
  the `V ∩ P` real half); `ψArc` and `AttachCuttingTerminalAssembled`
  (terminal-subcase target record) pinned.  The initial subcase
  (`T = (0,b)`) is the mirror with the reversal normalization;
  obligations 2–4 (prefix-end identity `A = κ((a,1))`, openness/arc-
  charting of `V`, `V \ P ≠ ∅` via the beyond bit) are the next
  sub-lemmas.  ROADMAP S226; **S227 (appended)**: step (iii-b-2) — the
  prefix-end identity VERIFIED: `stripPoints_mem_iff_of_coordSet` (the
  pointwise identity `((κ r : X) ∈ A) ↔ (r : ℝ) ∈ (a,1)` from the
  coordinate-set identity `T = (a,1)` — iii-a's payoff; the
  `TerminalAttach`-shaped membership iff, by `mem_image_of_mem` and the
  injectivity of the coordinate value map) and
  `stripPoints_eq_prefixEnd_of_coordSet` (the set identity
  `A = κ((a,1))`, with `A ⊆ P`) — obligation 2 of the cutting assembly,
  which with `V ∩ P = A` gives the `TerminalAttach P V κ a` data.
  Remaining: iii-b-3 (openness/interval-charting of `ψArc`), iii-b-4
  (`V \ P ≠ ∅` via the beyond bit), the initial-subcase mirror +
  reversal normalization, the iii-a bridge, iii-c.  ROADMAP S227; **S228
  (appended)**: step (iii-b-3) — openness/interval-charting of `ψArc`
  VERIFIED: `ψArc_isOpen` (the chart-arc over `(lo,hi)` is open when `U`
  is open — fleet L40 `chartArc_isOpen`), `ψArc_intervalChart`
  (`ORI ≃ₜ ↑(ψArc U ψ lo hi)` when the interval meets `(0,1)` — fleet L41
  `chartArc_intervalChart`, via `e.symm`), and
  `interval_meets_unit_of_nonneg_bounds` (the `hne` source for the attach
  interval `(p, c₀+δ)`).  Obligation 3 of the cutting assembly closed.
  Remaining: iii-b-4 (`V \ P ≠ ∅` via the beyond bit), the initial-
  subcase mirror + reversal normalization, the iii-a bridge, iii-c.
  ROADMAP S228; **S229 (appended)**: step (iii-b-4) VERIFIED —
  `ψArc_diff_P_nonempty`: `(ψArc U ψ p (c₀+δ) \ P).Nonempty` from
  `p ≤ c₀`, `0 < δ`, the beyond arc nonempty, and its disjointness from
  `P` (the beyond point lies in the attach arc — `p ≤ c₀ < t.1` — and
  outside `P` by `hbdP`).  With this ALL FOUR obligations of the cutting
  assembly are VERIFIED (real cut + prefix-end identity + openness/
  interval-charting + genuine extension): the terminal-subcase assembly
  `AttachCuttingTerminalAssembled` is one composition away from the
  boundary data.  Remaining: the terminal assembly composition, the
  initial-subcase mirror + reversal normalization, the iii-a bridge,
  iii-c.  ROADMAP S229; **S230 (appended)**: the terminal-subcase
  cutting assembly VERIFIED (section 11): `chart_mem_P_iff_coord`
  (chart-point-in-`P` iff coordinate in the real overlap set) and
  `P_inter_ψArc_eq_stripPoints` (from the real cut:
  `P ∩ ψArc U ψ p (c₀+δ) = stripPoints U ψ p c₀`) are the plumbing, and
  **`attach_cutting_terminal`** produces the arc `V := ψArc U ψ p (c₀+δ)`
  from the boundary data (strip `p < c₀`, `c₀ ∈ (0,1)`, `0 < δ`, the
  clean terminal end `0 < a < 1` with the prefix-end identity, the real
  cut, the beyond arc): `V` open, interval-charted,
  `TerminalAttach P V κ a`, `V \ P ≠ ∅` — the terminal half of
  `AttachCuttingTerminalAssembled` closed by composing the four verified
  obligations.  Remaining: the initial-subcase mirror (`T = (0,b)`) +
  reversal normalization, the iii-a bridge, iii-c.  ROADMAP S230; **S231
  (appended)**: the initial-subcase cutting assembly + the reversal
  normalization VERIFIED (sections 12–13): `attach_cutting_initial`
  mirrors `attach_cutting_terminal` over the INITIAL strip `(0,b)`
  (`0 < b < 1`): the arc `V := ψArc U ψ p (c₀+δ)` is open,
  interval-charted, `InitialAttach P V κ b`, `V \ P ≠ ∅`; `revORI`
  (the self-inverse interval reversal `t ↦ 1 − t`), `revORI_val`, and
  `initialAttach_to_terminal_rev` (from `InitialAttach P V κ b` the
  reversed chart `revORI.trans κ` satisfies
  `TerminalAttach P V (revORI.trans κ) (1 − b)`).  With sections 11–13
  BOTH halves of the attach cutting are closed and the initial half
  normalizes to the `TerminalAttach` form the chain consumes (the
  delegated L42 was declared FALSE — `theorem` types must be Props — and
  rebuilt in-module as the `def revORI`).  Remaining: instantiating the
  halves from the raw boundary data, the iii-a bridge, iii-c.  ROADMAP
  S231; **S232 (appended)**: the attach-cutting disjunction realized
  (section 14): `attach_cutting_endStrip` — from the boundary data and
  the clean END-STRIP disjunction (`hend`: the κ-coordinate set of the
  strip point set is `(a,1)`, `0 < a < 1`, or `(0,b)`, `0 < b < 1`) plus
  the real cut and the beyond arc, the arc `V := ψArc U ψ p (c₀+δ)` is
  open, interval-charted, `EndStripAttach P V κ`, `V \ P ≠ ∅` — a
  case-split on `hend` applying the terminal or the initial half (the
  `EndStripAttach` disjunction of `AttachCuttingStatement` realized).
  Remaining: producing `hend` + the transport inputs from the raw
  boundary data (needs the iii-a bridge: T open/preconnected/nonempty),
  iii-c.  ROADMAP S232; **S233 (appended, section 15)**: the iii-a
  bridge + the raw-data instantiation VERIFIED:
  `boundaryStripCoordSet_open_preconnected_nonempty` (the bridge: the
  κ-coordinate set of the strip point set is open/preconnected/nonempty
  — the commons L43 `coordSet_open_preconnected_nonempty` transported by
  `simpa`, `ORI` defeq the raw subtype `{t : ℝ // t ∈ Ioo 0 1}`);
  `coordSet_full_implies_all_members` (Fact A: coordinate-set `= (0,1)`
  ⇒ every prefix point `κ r` lies in the strip) and
  `exists_P_not_mem_stripPoints_cut` (Fact B: cutting at `p₀ ∈ (p, c₀)`
  leaves a point of `P` out — the ψ-coordinate `(p+p₀)/2` is in the
  overlap but below the cut) — the cut strictness ruling out the
  degenerate full-interval end; `stripPoints_mem_iff_of_coordSet_initial`
  (the `(0,b)` mirror of the terminal membership-iff); and THE
  RAW-DATA ASSEMBLY **`attach_cutting_realized`** — realizes
  `AttachCuttingStatement P U κ ψ hyU hyPc`: from `IsOpen U`, the
  right-freeness, the finite local structure `hF`, and `y ∈ closure P`,
  the attaching arc `V` exists (open, interval-charted,
  `EndStripAttach P V κ`, `V \ P ≠ ∅`).  Proof: (i) `c₀ ∈ closure Sℝ`
  (S220 bridge) + `c₀ ∉ Sℝ` (value-injectivity) feed `left_strip_of_rightFree`
  ⇒ strip `(p,c₀) ⊆ Sℝ`; (ii) cut at the midpoint `p₀` and force the
  clean end strip non-degenerate (Facts A+B) ⇒ `hend`; (iii) the shrunk
  right-free radius `δ := min δ₀ ((1−c₀)/2)` gives the real cut and the
  beyond arc; (iv) `attach_cutting_endStrip` assembles `V`.  Remaining
  on the interval side: iii-c (the T2 no-oscillation input supplying
  `hF`), the strict-terminal normalization (`OneSidedBoundaryAttach` +
  reversal bookkeeping for the chain), the ordered chain + alignment,
  the S206 extraction, the H2 compact side, Layer-C winding.  ROADMAP
  S233.
* `EndStripGlue.lean` — **S234: the END-STRIP GLUE and the
  chain-consumption interface** (new module
  `Submission/EndStripGlue.lean`, 169 lines, sorry-free, warning-free;
  imports OneSidedAttach + TerminalAttachment; imported by Submission.lean
  after OneSidedAttach).  Resolves the chain-consumption design decision:
  the per-level loop keeps only (prefix `P`, its chart); the boundary
  attach supplies orientation-neutral `EndStripAttach P V κ` (terminal OR
  initial), and gluing works at that level — no per-level reversal
  bookkeeping (initial attaches first reverse the prefix chart via
  `initialAttach_to_terminal_rev`, S231, then the terminal glue applies).
  Content (namespace LeanEval.KnotTheory.Quadrisecant):
  **`glue_of_endStripAttach`** — open arcs `P`, `V` with charts and
  `EndStripAttach P V κ` glue to an interval arc (terminal branch:
  `glue_of_TerminalAttach`; initial branch: reversed prefix chart);
  **`EndStripExtension P κ`** — the per-level extension record (open
  arc-charted `V` over an END strip of `κ` with `V \ P ≠ ∅`);
  **`glue_step_of_EndStripExtension`** — the chain-step consumption: from
  `IsOpen P` + the extension record there is a STRICT open arc prefix
  `P' ⊃ P` interval-charted (`P' = P ∪ V`, glued chart) — the per-level
  step of the exhaustion loop; **`endStripExtension_of_rawBoundary`** —
  the attach-cutting output (S233) re-bundled into the extension record
  from the raw boundary data (`IsOpen U`, `RightFreeAt`, `hF`,
  `y ∈ closure P`).  ROADMAP S234.
* `ArcRestrict.lean` — **S235: the sub-arc restriction — an arc chart
  restricted to a coordinate sub-interval** (new module
  `Submission/ArcRestrict.lean`, 212 lines, sorry-free, warning-free,
  PURE Mathlib + OneManifold/RealIntervalShape/AmbientTwoArc; imported by
  Submission.lean after EndStripGlue).  Route (α) / the maximal-chart
  route's generic "restriction of an arc chart to a sub-arc is an arc
  chart" content.  Decls (namespace LeanEval.KnotTheory.Quadrisecant):
  **`coordArc e lo hi`** — the coordinate sub-arc of an open arc `U`
  (chart `e : (0,1) ≃ₜ U`): points of `U` with chart coordinate in
  `(lo,hi)` (value-image definition, no proof-dependent comprehension);
  **`coordArc_mem_iff`** — `x ∈ coordArc ↔ ∃ hx : x ∈ U, coordinate
  ∈ (lo,hi)` (usable membership form); **`isOpen_coordArc`** — open
  when `U` is open, via the private **`isOpenMap_coe_of_isOpen`** (the
  value-coercion from the subtype of an open set is an open map:
  subtype-open `S = val ⁻¹' W`, `val '' S = W ∩ U`); **`oriIooHomeo`**
  — the ORI-coordinate subtype `{t : (0,1) // t ∈ (lo,hi)}` reassociates
  with `{r : ℝ // r ∈ Ioo lo hi}` for `0 ≤ lo < hi ≤ 1`; and
  **`subIoo_chart_openUnit`** — every coordinate sub-interval subtype is
  itself `≃ₜ ORI 0 1` (oriIooHomeo + affine `homeo_Ioo_openUnit`).  The
  full X-level chart of `coordArc` (carrier reassociation · chart
  restriction `e.symm` · `subIoo_chart_openUnit`) is recorded as future
  work in the module doc (classical-choice plumbing of image witnesses;
  NOT a sorry).  ROADMAP S235.
* `NoOscillation.lean` — **S236/S242: iii-c DONE (non-compact side) —
  the T2 geometric no-oscillation input** (module
  `Submission/NoOscillation.lean`, 520 lines, imported by Submission.lean
  after ArcRestrict; all sorry-free — `iii_c_finite_structure` proved on
  its non-compact side via fleet L46 + L55; the pin now carries the
  `hnc : ¬ CompactSpace` hypothesis because its only consumer is the
  interval side).  The last raw input of the one-sided
  attach cutting (S233/S234): at a one-sided boundary point `y` of an
  open arc prefix `P ≃ (0,1)` in a connected Hausdorff second-countable
  locally-interval-charted space (`LocallyIntervalChart`), with arc
  chart `ψ : (0,1) ≃ U` of `y`, the overlap-coordinate real set
  `Sℝ := overlapCoordReal P ψ` right-free at `c₀ := boundaryCoord ψ
  hyU` has FINITE local structure: `∃ F : Finset (ℝ×ℝ), Sℝ ∩ Iio c₀ =
  ⋃p∈F Ioo p.1 p.2 ∧ ∀ p ∈ F, p.2 ≤ c₀` — exactly the `hF` of
  `attach_cutting_realized`.  Content: the factored coordinate objects
  **`overlapCoordReal`**/**`boundaryCoord`** (shared with the
  attach-cutting inline form); **`overlapCoordSet_isOpen`** ((α): the
  coordinate set is open — continuous preimage); **`left_strip_of_boundary`**
  ((γ), VERIFIED: from `hF` + `RightFreeAt` + the S220 closure/non-
  membership bridges the end strip `∃ p < c₀, Ioo p c₀ ⊆ Sℝ` exists —
  iii-c's output plugs into the attach).  Module doc records the truth
  analysis (one-dimensional: infinite oscillation is possible for bare
  open sets but not for arc-prefix overlaps in 1-manifolds; the circle
  side is excluded by `RightFreeAt`), the decomposition (α/β/γ), and the
  DELEGATION DECISION: `noncompact_connected_oneManifold_interval`
  (ComponentIntervalSide.lean:210) is the right child for the
  1-manifold content — iii-c is a corollary once the component is
  charted by `(0,1)`.  **S240 (appended, VERIFIED sorry-free) — the
  iii-c corollary on the interval side, canonical chart form**: once the
  interval chart `e : (0,1) ≃ₜ X` exists (the S206 output, fleet L46),
  the `hF` of the attach is a short corollary with no oscillation
  analysis — `hF_prefix_in_interval_chart` (every open arc prefix `P`
  over a single interval by `prefix_coord_interval`, S237; `Ioo a b ∩
  Iio c₀` packed by `singleInterval_finiteStructure`, S239) and
  `canonicalChart_overlapCoord_eq` (the canonical boundary chart at any
  point — the whole space `U := univ`, `ψe := e.trans
  (subtypeUnivHomeo X).symm` — has overlap-coordinate set equal to the
  prefix-coordinate set).  **S241 (appended, VERIFIED sorry-free
  statement + reduction) — the arbitrary-`ψ` hF target**: 
  `hF_of_interval_chart` (pinned `def Prop`, no `sorry`): in the
  interval chart `e`, for open arc `P` (chart `κ`) and open arc `U`
  (chart `ψ`), `overlapCoordReal P ψ ∩ Iio c₀` has the finite local
  structure at every `c₀`; and `hF_of_interval_chart_of_coord_shape`
  (VERIFIED): from the residual shape (the ψ-coordinate set is EMPTY or
  a SINGLE open interval) the `hF` follows with no analysis
  (`singleInterval_finiteStructure`, S239).  The residual is delegated
  as commons L55 (`Commons.Topology.OneManifold.psi_coord_set_single_or_empty`,
  LANDED; its proof uses the already-landed L46-child
  `Commons.Topology.OneManifold.chart_pullback_interval_shape`).
  **S240 (completion, appended, VERIFIED sorry-free) — the canonical
  boundary `hF` composition**: `hF_canonical_boundary_of_interval` —
  `overlapCoordReal P ψe ∩ Iio c₀` has the finite local structure at
  every `c₀` for the canonical boundary chart `ψe := e.trans
  (subtypeUnivHomeo X).symm` (`U := univ`): `rw
  [canonicalChart_overlapCoord_eq]` + `hF_prefix_in_interval_chart` —
  where `ψ := e` the shape lemma is literally
  `prefix_coord_interval`, so the canonical branch bypasses the L55 /
  `chart_pullback_interval_shape` route entirely.  **S241 (completion,
  appended, VERIFIED sorry-free) — the arbitrary-`ψ` hF composition**:
  `hF_of_interval_chart_obtain` — the two-line composition of L55's
  `psi_coord_set_single_or_empty` with the verified reduction
  `hF_of_interval_chart_of_coord_shape`; with the canonical branch every
  interval-side `hF` input is now VERIFIED.  ROADMAP S236/S240/S241.
* `AmbientTwoArc.lean` — **S163: the ambient two-arc theorem, slice
  (a): coordinate transport of the overlap along the arc charts** (new
  module `Submission/AmbientTwoArc.lean`, 312 lines, sorry-free,
  warning-free, PURE Mathlib + RealIntervalShape; imported by
  Submission.lean after RealIntervalShape).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): **`overlapPullbackHomeo`** — for a
  chart `φ : (0,1) ≃ₜ {x // x ∈ U}` of an open arc `U`, the pullback of
  `V` to the chart `{t ∈ (0,1) | φ t ∈ V}` is homeomorphic via `φ` to
  `{x // x ∈ U ∩ V}`; **`homeoRestrictImage`** — restricting a homeo to
  a subset gives a homeo onto its image (`↑A ≃ₜ ↑(e '' A)`);
  **`overlapPullback_isOpen`** — the pullback of an open `V` is open in
  `(0,1)`; **`overlap_pullback_arc`** (headline) — if the overlap
  `U ∩ V` is connected (as a subspace) then the coordinate pullback is
  again an open arc `≃ₜ (0,1)` (via `overlapPullbackHomeo` + a real
  chart `ℝ ≃ₜ (0,1)` (`homeoRestrictImage`) + RealIntervalShape's
  classification `open_connected_ℝ_homeo_openUnit`);
  **`two_arc_contained`** — the containment case of the ambient two-arc
  theorem (`V ⊆ U` ⇒ `U∪V ≃ₜ (0,1)`); **`subspaceOverlapReassoc`**,
  **`two_arc_union_locallyInterval`** and
  **`two_arc_union_isOneManifold`** — the union of two open arcs of a
  Hausdorff second-countable ambient is itself a topological 1-manifold
  (the dichotomy's local input for slice (a)).  ROADMAP S163.
* `FacingNormalization.lean` — **S164: the facing-normalization
  vocabulary and the coordinate overlap shape** (new module
  `Submission/FacingNormalization.lean`, 256 lines, sorry-free,
  warning-free, imports AmbientTwoArc; imported by Submission.lean after
  AmbientTwoArc).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): **`coordRealSet φ V`** — the
  `V`-part of the `U`-chart as a subset of ℝ (`{r | ∃ t ∈ (0,1),
  r = t.1 ∧ φ t ∈ V}`); `coordRealSet_isOpen` (the chart pullback is
  open and `subtype.val : (0,1) → ℝ` is an open map), 
  `coordRealSet_isConnected` (connected/nonempty when the overlap
  subspace `{x // x ∈ U ∩ V}` is connected), 
  `coordRealSet_subset_openUnit`; **`overlap_coord_shape`** (headline) —
  the coordinate overlap is an open interval `(a,b)` with `0 ≤ a < b ≤
  1` (RealIntervalShape classification + the openness/connectedness
  transport) — the **seam points** of the `U`-chart live at coordinates
  `a`/`b`; `coord_mem_iff_mem_coordRealSet` (membership translation) and
  the first exclusions **`left_seam_not_in_V_of_shape`** /
  **`right_seam_not_in_V_of_shape`** — a seam point of `U` is NOT in `V`
  (lies in `U∖V`, at the chart boundary of the overlap).  **S166 (seam
  approach through the first chart)**: `left_seam_approached_by_overlap`
  — every neighbourhood `N` of the left seam `φ⟨a⟩` contains the
  `φ`-images of the overlap points with coordinates `(a,a+δ)` (`δ ≤ b−a`,
  `δ ≤ 1−a` returned); `left_seam_mem_closure_overlap` — the left seam
  lies in the closure of `U∩V` (midpoint witness); and the `V`-mirrors
  `left_seam_approached_by_overlap_swap` /
  `left_seam_mem_closure_overlap_swap` (`simpa [inter_comm]`
  instantiation under `U↔V`, `φ↔ψ`).  **S167 (seam inseparability)**:
  `seam_pair_common_point` — if both left seams are strict (`0<a`, `0<c`)
  and the transition is left-to-left compatible (`hcomp`: every `ε>0`
  gives a `V`-strip `(c,c+η)` whose overlap points have `U`-coordinate
  `< a+ε` — the increasing case of IntervalHomeoEnds S165), then every
  pair of neighbourhoods of `φ⟨a⟩` and `ψ⟨c⟩` shares a common overlap
  point (two approach lemmas + the midpoint `c+η/2` + the
  apply-symm coordinate rewrite);
  `not_T2_of_left_strict_seams` — in a `T2Space X` the configuration is
  impossible (equal seam points contradict
  `left_seam_not_in_V_of_shape`; distinct ones are separated by
  `t2_separation`, contradicting the common point).  **S168 (the
  transition homeomorphism)**: `pullbackToRealCoordHomeo` — the
  canonical interval identification: the chart-overlap pullback
  `{t : (0,1) // (φ t : X) ∈ V}` is homeomorphic via the coordinate map
  to `{r : ℝ // r ∈ coordRealSet φ V}`; and **`transitionHomeo`** — the
  assembled coordinate change `g : (c,d) ≃ₜ (a,b)` between the two
  overlap charts (composition of the pullback homeos
  `overlapPullbackHomeo` (S163), the set-congruences `U∩V = V∩U`, and
  the two canonical interval identifications) — the `(a)` glue of the
  S167 record; next: the coordinate value lemma of `g` and the
  `hcomp` instantiation from IntervalHomeoEnds S165 — **S169 (the
  coordinate value lemma)**: `overlapPullbackHomeo_apply_val` /
  `_symm_apply_val`, `pullbackToRealCoordHomeo_apply_val` /
  `_symm_apply_val`, `setEqSubtypeHomeoX_apply_val` (the piece value
  lemmas) and **`transitionHomeo_coord`** — for `s ∈ (c,d)` with lifts,
  `(g s : ℝ) = (φ.symm ⟨(ψ⟨s⟩ : X), hψU⟩ : (0,1) : ℝ)`: the two chart
  points at matching coordinates coincide (staged evaluation through
  `x1..x7`, `Subtype.ext` for proof-irrelevant lifts).  **S170 (the
  strict-left-seam case closed)**: `left_seam_hcomp` — the `hcomp`
  hypothesis is produced from the increasing-case left-end approach `hg`
  of the transition (strip `η := min δ (min (1−c) (d−c))`; each
  `V`-overlap point `w` in `(c,c+η)` gives `s := ⟨(w : ℝ), ·⟩` with
  `g s < a+ε` by `hg`, and `transitionHomeo_coord` rewrites `(g s : ℝ)`
  to `(φ.symm ⟨(ψ w : X), w.2⟩).1` via `congrArg` congruences); and
  `not_T2_of_left_strict_seams_increasing` — with `[T2Space X]`,
  `0 < a`, `0 < c` and `hg`: `False` (through `left_seam_hcomp` +
  `not_T2_of_left_strict_seams`).  **S171 (the left-`U` / right-`V`
  case)**: `right_seam_approached_by_overlap_swap` — every neighbourhood
  of the right seam `ψ⟨d⟩` contains the `ψ`-images of the overlap points
  with coordinates in `(d−δ,d)`; `leftU_rightV_hcomp` — the `hcompR`
  inequality from the decreasing right-end approach `hgR` (the second
  disjunct of `intervalHomeo_right_end_reaches_endpoint`): `V`-overlap
  points near `d⁻` have `U`-coordinate `< a+ε`; `seam_pair_common_point_rightV`
  — every pair of neighbourhoods of `φ⟨a⟩` and `ψ⟨d⟩` shares a common
  overlap point; `not_T2_of_leftU_rightV_decreasing` — under
  `[T2Space X]`, `0<a`, `d<1`, `hgR`: `False`.  **S172 (the `U`-right approach)**: `right_seam_approached_by_overlap`
  — every neighbourhood of the right seam `φ⟨b⟩` (`b < 1`) contains the
  `φ`-images of the overlap points with coordinates in the left strip
  `(b−δ, b)` (`δ ≤ b−a`, `δ ≤ b`; the distance is `b − u`,
  `abs_of_neg`); `right_seam_mem_closure_overlap` — `φ⟨b⟩ ∈ closure
  (U∩V)` (midpoint `b − δ/2`).  **S173 (the right-`U` / left-`V` case
  via `D2`)**: `rightU_leftV_hcomp` — the `hcompD2` inequality from the
  decreasing left-end approach `hgD2` (second disjunct of
  `intervalHomeo_left_end_reaches_endpoint`): `V`-overlap points near
  `c⁺` have `U`-coordinate `> b−ε`; `seam_pair_common_point_rightU_leftV`
  — common point for `(φ⟨b⟩, ψ⟨c⟩)` (U-right approach + V-left approach
  + midpoint `c + η/2`, `u0`-lift in `(b−δ, b)`); and
  `not_T2_of_rightU_leftV_decreasing` — under `[T2Space X]`, `b<1`,
  `0<c`, `hgD2`: `False`.  **S174 (the right-`U` / right-`V` case via `D′1`) —
  four for four**: `rightU_rightV_hcomp` (the `hcompD1` inequality from
  the increasing right-end approach `hgD1`, first disjunct of
  `intervalHomeo_right_end_reaches_endpoint`: `V`-overlap points in
  `(d−η,d)` have `U`-coordinate `> b−ε`), `seam_pair_common_point_rightU_rightV`
  (common point for `(φ⟨b⟩, ψ⟨d⟩)`: U-right + V-right approaches +
  midpoint `d − η/2`), and `not_T2_of_rightU_rightV_increasing` (under
  `[T2Space X]`, `b<1`, `d<1`, `hgD1`: `False`).  **S175 (the transition
  end-approach disjunction)**: `transitionEndApproach` — one of the four
  one-sided approach shapes holds (left-end of the `V`-chart to the
  left/right end of the `U`-chart as `s → c⁺`; right end to left/right as
  `s → d⁻`), each disjunct being exactly the side-approach hypothesis
  `hg`/`hgD2`/`hgR`/`hgD1` of the four closed seam cases S170/S173/S171/
  S174 (proved from `intervalHomeo_left_end_reaches_endpoint`, S165 — the
  disjunction is witnessed by the left end alone);
  `transitionEndApproach_right` — the right-end theorem supplies the
  `s → d⁻` disjuncts.  **S176 (four-pairing assembly atoms)**: each
  end-approach disjunct kills the corresponding strict pair under
  `[T2Space X]`: `left_end_strict_pair_forbidden` (left→a kills
  `0<a ∧ 0<c` via S170), `leftU_rightV_strict_pair_forbidden`
  (right→a kills `0<a ∧ d<1` via S171), `rightU_leftV_strict_pair_forbidden`
  (left→b kills `b<1 ∧ 0<c` via S173),
  `right_end_strict_pair_forbidden` (right→b kills `b<1 ∧ d<1` via
  S174) — each a one-line wrapper of the corresponding
  `not_T2_of_*`.  **S177 (left-left routing through the far end)**:
  `left_strict_pair_forbidden_of_leftToB` — left-left strict with the
  decreasing left-end approach (`left→b`) and `b < 1` is impossible (the
  pair `(φ⟨b⟩, ψ⟨c⟩)` of S173 closes it);
  `left_strict_pair_forbidden_of_rightToA` — left-left strict with the
  decreasing right-end approach (`right→a`) and `d < 1` is impossible
  (S171).  HONEST FINDING recorded in ROADMAP S177: the fully degenerate
  left-left configuration under decreasing behavior with `b = d = 1` is
  CONSISTENT (realizable in S¹ with an orientation-reversed `V`-chart:
  `U = (0.1,0.9)`, `V = (0.2,0.95)` with reversed chart), so no
  `strict_pair_forbidden_degenerate` lemma exists and the previously
  scoped "each overlap end is an end of at least one chart" packaging
  must be restated.  **S178 (route (a): the consistently-oriented
  section)**: `TransitionIncreasing` — the bundled orientation hypothesis
  (`g s < a+ε` as `s → c⁺` AND `b−ε < g s` as `s → d⁻`); under it the
  strict-seam predicates become sound:
  `left_seam_pair_free_of_increasing` (`¬ (0<a ∧ 0<c)`, S170 atom),
  `right_seam_pair_free_of_increasing` (`¬ (b<1 ∧ d<1)`, S174 atom), and
  **`ends_of_at_least_one_chart_of_increasing`** — the corrected packaging
  claim: at each overlap end at least one chart's overlap reaches that
  chart's end.  **S179 (the StrictMono branch realises the consistent
  orientation)**: `transitionHomeo_leftToA_of_strictMono` — a strictly
  increasing transition map sends the left end to the left end
  (`g s < a+ε` as `s → c⁺`: the reversed disjunct is impossible under
  `StrictMono` — witness `s₀` at the midpoint, `ε := (b − g s₀)/2`, an
  `s` between `c` and `min (c+δ) s₀` via `exists_between`); 
  `transitionHomeo_rightToB_of_strictMono` — the right end goes to the
  right end (`b−ε < g s` as `s → d⁻`, ruling out the reversed disjunct by
  an `s` between `max (d−δ) s₀` and `d`); and **`increasing_of_strictMono`**
  — the StrictMono branch of the transition dichotomy supplies
  `TransitionIncreasing` (conjunction of the two).  **S180 (the StrictAnti
  mirror)**: `TransitionDecreasing` (left→b as `s → c⁺` AND right→a as
  `s → d⁻`); `transitionHomeo_leftToB_of_strictAnti` (the increasing
  left-end disjunct is impossible under `StrictAnti` — midpoint `s₀`,
  `ε := (g s₀ − a)/2`, an `s` below `min (c+δ) s₀` gives `g s < a+ε <
  g s₀ < g s`); `transitionHomeo_rightToA_of_strictAnti` (the increasing
  right-end disjunct ruled out by an `s` above `max (d−δ) s₀`); and
  **`decreasing_of_strictAnti`** — the StrictAnti branch supplies
  `TransitionDecreasing`.  Both monotone branches are now realized.  The
  module doc
  records the precise facing-normalization lemma statement (seam-pair
  incompatibility at each overlap end in a Hausdorff ambient) and its
  remaining sub-lemmas (interval-homeo end correspondence — DONE in
  IntervalHomeoEnds S165 — and the seam inseparability).  **S181 (the
  chart-orientation reversal — the orientation-normalization half of the
  two-arc assembly)**: `reversedChart ψ` — the chart composed with the
  coordinate reflection `u ↦ 1 − u` (`intervalReflection 0 1`, S165), +
  `reversedChart_apply_val`; **`coordRealSet_reversedShape`** — in the
  reversed chart the overlap mirrors to `(1−d, 1−c)` (set equality via
  two membership directions through `coord_mem_iff_mem_coordRealSet` +
  the reflection coordinate identity);
  **`transitionHomeo_reversedCoord`** — the value identity: the new
  transition at `t` equals the old transition at `reflectCoord c d t`
  (the S181 coordinate reflection of IntervalHomeoEnds; both sides
  evaluated via `transitionHomeo_coord`, the `φ.symm` arguments equated
  by `Subtype.ext` through the reflection);
  **`transitionDecreasing_reversed_increasing`** — THE S181 theorem: a
  `TransitionDecreasing` transition becomes `TransitionIncreasing` after
  reversing `ψ` (coordinate core `increasing_ends_after_reflection` +
  the value identity — left end of `(1−d,1−c)` maps near `a`, right end
  near `b`); **`transition_increasing_or_decreasing`** — the orientation
  dichotomy of any two charts (S165 monotonicity +
  `increasing_of_strictMono`/`decreasing_of_strictAnti`, S179/S180); and
  **`exists_increasing_orientation`** — the normalization packaging:
  either the transition is already increasing or it is increasing after
  reversing `ψ`, so `ends_of_at_least_one_chart_of_increasing` (S178)
  applies to a suitably oriented pair (one chart orientation always
  realises the consistent orientation).  ROADMAP S164 + S166.
* `IntervalHomeoEnds.lean` — **S165: end correspondence for
  homeomorphisms of open intervals** (new module
  `Submission/IntervalHomeoEnds.lean`, 324 lines, sorry-free,
  warning-free, PURE Mathlib; imported by Submission.lean after
  FacingNormalization).  This is sub-lemma (3)(i) of the
  facing-normalization record (S163/S164): content (namespace
  LeanEval.KnotTheory.Quadrisecant): `intervalHomeoTotal` (totalize the
  coordinate map of `e : (c,d) ≃ₜ (a,b)`; value lemma
  `intervalHomeoTotal_eq`); `intervalHomeoTotal_contOn_injOn`
  (continuous on `(c,d)` via
  `continuousOn_iff_continuous_domRestrict` — the restriction equals
  `val ∘ e` — and injective there); **`intervalHomeo_coord_strictMono_or_anti`**
  — a homeo between open real intervals is strictly increasing or
  strictly decreasing (`ContinuousOn.strictMonoOn_of_injOn_Ioo`);
  `intervalReflection` (the order-reversing reflection
  `t ↦ c+d−t`, + `intervalReflection_apply`/`_involutive`);
  **`intervalHomeo_left_end_reaches_endpoint`** — left-end
  correspondence: as `t → c⁺`, `(e t : ℝ)` is eventually below `a + ε`
  (increasing) or above `b − ε` (decreasing) — proof: surjectivity
  (`e.symm` hits `a+ε`/`b−ε`) + strict monotonicity + the large-ε
  bound; **`intervalHomeo_right_end_reaches_endpoint`** — the right-end
  analogue derived through the reflection.  These supply the one-sided
  approach of the transition homeo needed by the seam-inseparability
  argument (3)(ii).  **S181 (the coordinate-level orientation flip)**:
  `reflectCoord c d` — the reflection `s ↦ 1 − s` carrying
  `(1−d, 1−c)`-coordinates to `(c,d)`-coordinates (+ `reflectCoord_val`),
  and **`increasing_ends_after_reflection`** — a DECREASING interval
  homeo `e : (c,d) ≃ₜ (a,b)` (left→`b`, right→`a`) precomposed with
  `reflectCoord` is INCREASING (new left end `(1−d)⁺` → near `a`, new
  right end `(1−c)⁻` → near `b`): the pure-coordinate core of the S181
  chart-orientation lemma of FacingNormalization.  ROADMAP S165.
* `TwoArcUnion.lean` — **S182: the ambient two-arc theorem** (new
  module `Submission/TwoArcUnion.lean`, 542 lines, sorry-free,
  warning-free, imports FacingNormalization + TwoChartGlue +
  AmbientTwoArc; imported by Submission.lean after IntervalHomeoEnds,
  before TwoChartGlue).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): `subset_of_coordShape_all` /
  `_symm` — overlap shape `(0,1)` ⟹ `U ⊆ V` / `V ⊆ U`;
  `endIff_of_shape` — the shape read off as the terminal membership iff
  (the glue engine's `hVend`/`hUend` data); `Tfun_eq_transitionHomeo_coord`
  — the engine `Tfun` agrees pointwise with the `transitionHomeo`
  coordinate value; **`two_arc_union_straight_facing`** and
  **`two_arc_union_straight_facing_of_strictMono`** — overlap
  right-terminal `(a,1)` in `U` / left-terminal `(0,d)` in `V` with
  `StrictMono` transition glue to an open interval (engine step
  `prefix_two_charts_interval` S159 driven by shape data);
  `reversedChart_symm_apply_val` / `_coord_val` — the symm of a reversed
  chart is the reflected `φ.symm` (coordinate `1 −` value);
  **`two_arc_union_mirror_facing_of_strictMono`** — the MIRROR overlap
  `(0,b)` LEFT-terminal in `U` / `(c,1)` RIGHT-terminal in `V` also glues:
  reverse BOTH chart orientations (`(1−b,1)`/`(0,1−c)`, the doubly
  reversed transition `t ↦ 1−g(1−t)` stays `StrictMono`) then the
  straight driver; **`two_open_arcs_union_of_shapes_inc`** — the
  four-pairing theorem under the increasing orientation: `[T2Space X]`
  + shapes `(a,b)`/`(c,d)` + `StrictMono` transition ⟹ union is an open
  interval; via `TransitionIncreasing` (S179) +
  `ends_of_at_least_one_chart_of_increasing` (S178) each overlap end is an
  end of at least one chart `(a=0∨c=0) ∧ (b=1∨d=1)`, and the four corners
  are containment / straight-gluing / mirror-gluing (degenerate sub-corners
  collapse to containment); **`two_open_arcs_union_is_openInterval`** —
  THE ambient two-arc theorem: `[T2Space X]`, open `U V` with interval
  charts `φ ψ`, connected overlap ⟹ `Nonempty ({x // x ∈ U∪V} ≃ₜ
  OpenRealInterval 0 1)` (orientation normalization: transition monotone
  dichotomy S165 — `StrictMono` applies the four-pairing theorem, `StrictAnti`
  reverses the `V`-chart (S181) making the transition `StrictMono`, and
  applies it to the reversed pair).  This closes the S164/S177/S181 gap —
  the union of two overlapping open arcs of a Hausdorff space is an arc.
  **S183 (the finite-chain union theorem)**: `finite_chain_union_interval`
  — in a Hausdorff space, a finite chain of open arcs `T 0 … T n` (each
  open with an interval chart, every prefix `P k := ⋃ j ∈ range (k+1),
  T j` meeting the next trace `T (k+1)` in a CONNECTED overlap) glues to
  one open interval `{x // x ∈ P n} ≃ₜ (0,1)` — induction over the trace
  count carrying the explicit prefix homeomorphism (base: a single trace;
  step: `union_range_succ` + the ambient two-arc theorem applied to
  `(P k, T (k+1))`; prefix-openness by the finite-union induction
  `hgo`).  NOTE: hypotheses are PREFIX-overlap (successive-overlap alone
  is insufficient — a wrapping trace can touch the prefix in two
  components; the walk geometry must supply prefix connectivity).
* `TraceOverlap.lean` — **S184: trace-overlap local arcs** (new module
  `Submission/TraceOverlap.lean`, 147 lines, sorry-free, warning-free,
  imports PrefixArcChart; imported by Submission.lean after TwoArcUnion,
  before TwoChartGlue).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): **`traceOverlap_localArc`** — every
  class `c` in the traces of two interval charts `ch₀ ch₁` carries an
  open arc inside `chartTrace ch₀ ∩ chartTrace ch₁`: `c ∈ V`, `V` open
  in `OSub r`, `V ⊆` the trace intersection, `Nonempty (V ≃ₜ
  ChartInterval lo hi)` — `V` is the chart-lift image of the
  `OChartMonotoneNbhd` cell (OChartGlue S98) around the parameter of `c`
  (an open interval of `ch₀`-coordinates inside the transition domain on
  which the coordinate relabelling is strictly monotone); openness via
  `isOpenMap_paramEmbedding` ∘ `isOpenMap_oChartLift`, the homeo via
  `homeo_range_of_continuous_injective_isOpenMap`
  (`continuous_oChartLift` + `oChartLift_injective` S100).  This is the
  local content of every overlap-connectivity statement in the walk
  geometry (overlap components are unions of such arcs).  ROADMAP S184
  records the honest status: the S183 prefix-overlap hypothesis
  `ConnectedSpace {x // x ∈ P'_k ∩ T (k+1)}` is NOT yet derivable from
  the walk data (hoverlap gives only nonempty successive intersections;
  the component interval/circle dichotomy is still open), so the
  prefix-overlap connectivity must come from the sweep's interval-chain
  ordering machinery (S139/S147-T) — the ordering slice S183 waits for.
* `OverlapOrder.lean` — **S185: the monotone cell transport (first
  lemma of the sweep's ordering slice)** (new module
  `Submission/OverlapOrder.lean`, 147 lines, sorry-free, warning-free,
  imports TraceOverlap; imported by Submission.lean after TraceOverlap,
  before TwoChartGlue).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): `cellTransport ch₀ ch₁ x₀ nb` — the
  real transport value at a cell parameter `u ∈ (nb.lo, nb.hi)` (the
  `ch₁`-coordinate of the class that `ch₀`'s parameter describes);
  `continuousOn_cellTransport` (continuous on the open cell);
  **`oChartCellTransport_image_connected`** — the transported coordinate
  set is CONNECTED (continuous image of the connected interval
  `isConnected_Ioo nb.lo_lt_hi`); `oChartCellTransport_image_eq_range`
  (the image is the range of `oChartTransitionOnInterval`); and
  **`oChartTransitionOnInterval_range_subset_chart`** — the range lies
  inside the next chart's interval `(ch₁.lo, ch₁.hi)`.  Together with
  `nb.monotone` (strict one-direction monotonicity on the cell) these
  say: through each junction's monotone cell the walk's transport reaches
  a single connected, strictly-ordered interval of the next chart's
  coordinates — the local "single interval" half of the ordered-chain
  overlap content the S147-T sweep composes; the full prefix-overlap
  connectivity (S183 `hconn`) still needs the S147-T ordered-chain
  induction (H1 directions consistent / H2 no-wrap), for which this
  module is the per-cell transport fact.  **S186 (the S147-T preamble:
  the ordered-cell-chain transport)**: `iterTrans trans m` (the `m`-fold
  composed cell transport), `InterlockCells cellLo cellHi trans` (H1:
  each cell transport sends its cell into the NEXT cell),
  `iterTrans_mapsTo` (interlock keeps the iterate in cell `m`),
  `iterTrans_continuousOn` / `iterTrans_injOn` (composition of the
  per-junction continuity/injectivity), and
  **`orderedChain_transport`** — under H1 with each cell transport
  continuous and injective on its cell, the `m`-fold transport is
  continuous, injective, and sweeps a CONNECTED interval of window `m`
  (`IsConnected (iterTrans trans m '' C 0)`); base `m = 1` is the
  single-junction certificate, the step composes it at the next junction
  through H1.  O-side seeds: `cellTransport_eq_transitionOnInterval`
  (pointwise identity on the cell), `injOn_cellTransport` (injectivity
  from `nb.monotone` via `injective_oChartTransitionOnInterval`), and
  **`oChartCell_single_transport_cert`** (injective ∧ continuous ∧
  connected-image at one junction — the `m = 1` hypothesis instance).
  The precise junction-level H1 (interlock) and H2 (no-wrap) are
  recorded in the module doc as the geometric inputs the walk must supply
  when S147-T is instantiated.  **S187 (correction)**: the naive
  interlock `trans m '' C m ⊆ C (m+1)` for the RAW S185 cells is FALSE —
  `C m` sits around the coordinate of `z m ∈ T m ∩ T (m+1)` and its
  image around `z m`'s coordinate in chart `(m+1)`, while `C (m+1)` sits
  around the independent coordinate of the next junction class
  `z (m+1)` (`hoverlap` links nothing between `z m` and `z (m+1)`); the
  true interlock is the aligned sub-piece shrinking
  (`ChainAlignment.exists_aligned_subpieces`, AlignedTotality) in the
  ChainTransport/ChainDomain representation the sweep actually uses
  (S111/S119), recorded as the S147-T assembly input.  ROADMAP S185 +
  S186 + S187.
* `SweepAligned.lean` — **S188: the walk-aligned sub-pieces — the O-side
  interlock in the ChainTransport representation** (new module
  `Submission/SweepAligned.lean`, 138 lines, sorry-free, warning-free,
  imports IntervalCoverU + ChainAlignment; imported by Submission.lean
  after OverlapOrder, before TwoChartGlue).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): `chainTail_mem_index` (membership in
  a `chainTail p k n` tail ⟹ an index `k < m ≤ k+n` with `q = p m`);
  `continuous_walkJunctionPiece_τ` (every walk junction piece has a
  continuous coordinate map — its `τ` is the S98 interval-piece
  transition of the walk junction neighbourhood); and
  **`walk_aligned_subpieces`** — the S133 `exists_aligned_subpieces`
  instantiated on the walk junction-piece chain `p 0 :: chainTail p 0 n`
  (`p m := walkJunctionPiece … m`): given a start parameter `x₀` with a
  forward orbit (`htr`), aligned sub-pieces `sp :: qs` exist (`sp` a
  sub-piece of `p 0` containing `x₀`, `qs` sub-pieces of the successive
  walk pieces) with `AlignedTotality (sp :: qs)` — every parameter of
  `sp` transports through the whole chain: the true junction-level
  interlock (per the S187 correction, NOT the raw-cell containment).
  With `AlignedTotality`, `ChainDomain (sp :: qs)` is all of `sp`, so
  `chain_prefix_transport_summary` (S119) applies to every start
  parameter — the next bookkeeping step toward the S147-T `Uₙ`.  The
  `htr` orbit input is the single remaining walk-geometric hypothesis
  (S135 machinery).  ROADMAP S188.

* `NestedDatum.lean` — **S190–S194: the per-length nested datum family,
  its recursion, and the per-pair reindexing** (module
  `Submission/NestedDatum.lean`, 466 lines, sorry-free, warning-free,
  imports PrefixArcChart + AlignedCover; imported by Submission.lean
  after SweepAligned).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): `WP` (walk junction-piece
  abbreviation); `perLength_base_datum` (level-0 datum: S140c at
  `(k=0,n=0)`, whole-piece constraint); `perLength_step_datum` (nesting
  step: level-`(n+1)` from the level-`n` head via S140c with constraint
  `J`, giving `Ioo (datumPiece d0) ⊆ Ioo J`, `x₀ ∈ d0`, totality).
  `PerLevelBundle`/`datumInterval_of_pieceEq`; the recursion in
  EQUATION-COMPILER form — `perLevelBase`, `perLevelStep` (extraction by
  `.1/.2` projections — no stuck `And.casesOn` in the Type-valued value),
  `perLevelData` (`| 0 => base | n+1 => step n (perLevelData n)`), and
  **`perLevelData_succ`** (recursion-relation by `rw [perLevelData]`).
  **`perLevelStep_spec`** — the step datum's interface (head `d0`,
  `Ioo (datumPiece d0) ⊆ Ioo (ih.1 0)`, head membership, totality).
  **`perLength_nested_datum_family`** — the family theorem:
  `subfam n := (perLevelData n).1` with heads containing `x₀`, heads
  NESTING across consecutive lengths, per-length forward totality.
  **S194**: the S189 reindexing instantiated per consecutive pair —
  `perLength_reindex_identity` (level-`(n+1)` chart reindexes into
  level-`n` by the real identity) and `perLength_reindex_monotone`
  (`MonotoneDirectionOn` of the change of chart) — the per-pair
  coordinate-compatibility conjuncts of the S140-T2 family.  ROADMAP
  S190–S194.
* `PerLengthCell.lean` — **S195–S197: the per-length cell interface of
  the nested datum family** (module `Submission/PerLengthCell.lean`,
  430 lines, sorry-free, warning-free, imports NestedDatum; imported by
  Submission.lean after NestedDatum).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): `perLengthCell` (the level-`n`
  cell = the range of the level-`n` arc `walkAlignedArcMap …
  (subfam n)`); `perLengthCell_open` (each cell is open — the S139
  range openness read off the datum); `perLengthCell_antitone` (cells
  nest: level-`(n+1)` ⊆ level-`n` via the S140b range nesting from the
  head nesting `hI`); `perLengthOrbitClass` (the orbit class = the
  `ch 0`-lift of `x₀`, common to all the walk traces);
  `perLengthCell_package` (at every level the cell lies in the
  component of `c₀` and in the walk partial union `P'_{n+2}`, and the
  orbit class lies in the cell — the S140d single-level package read
  off the datum via `alignedData_arc_openSet`); `perLengthCell_chart`
  (each cell is interval-charted, the S140a chart of the datum range);
  and **`perLength_cell_family`** — the packaged family theorem: from
  walk data + component (`c₀`, `hc0`) + orbit (`x₀`, `hland`), a
  per-length datum family `subfam` with the three datum conjuncts
  (head contains `x₀`; heads nest; forward totality) AND the per-level
  cell interface (open; antitone; in the component; in `P'_{n+2}`;
  containing the orbit class; interval-charted).  The consecutive-level
  real-identity reindexing remains `perLength_reindex_identity` /
  `perLength_reindex_monotone` (S194), instantiable from the returned
  `subfam` + nesting conjunct.  **S196 (appended)**: the cells sit
  inside EVERY prefix trace — `perLengthCell_subset_trace` (the level-`n`
  cell ⊆ `T_m` for every `m ≤ n+1`: the level totality restricted to the
  prefix `m−1` + the S119 class-coordinate identification at the prefix
  places every cell class in the `m`-th chart's trace; `m=0` is the
  start chart) and `perLengthOrbitClass_mem_all_traces` (the orbit class
  lies in EVERY walk trace `T_m`, `m ∈ ℕ` — `walkOrbit_all_lengths` +
  `walkOrbitClass_mem_traces`, the S147 "one class common to all the
  walk traces" special configuration).  Together: each level-`n` cell is
  an interval-charted open arc inside `C ∩ ⋂_{m ≤ n+1} T_m` containing
  the orbit class — the coordinate refinement of the prefix union
  `P'_{n+2}` around the common class that the S147-T chaining (H1
  interlock) composes.  This is the clean-interface cell family of the
  sweep's ordering slice (S147-T): the T2 increasing family
  `Uₙ = P'_{n+2}` (S143) is exhausted by these antitone interval-charted
  cells around the orbit class, each inside its exhaustion step.  **S197**: `perLength_cell_family_prefix` — the combined family
  theorem: from walk data + component + orbit (`hland`) a per-length
  datum family whose level-`n` cells are open interval-charted arcs in
  `C ∩ P'_{n+2}` containing the orbit class, antitone, AND inside every
  prefix trace `T_m` (`m ≤ n+1`) — the single-interface statement of
  the S147-T chaining (cells as the common-class coordinate refinements
  of each prefix union).  ROADMAP
  S195–S197.
* `PrefixCoord.lean` — **S198: the prefix-coordinate interlock of the
  per-length cell family** (module `Submission/PrefixCoord.lean`, 151
  lines, sorry-free, warning-free, imports PerLengthCell; imported by
  Submission.lean after PerLengthCell).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): `perLengthCell_totality_prefix`
  (the level-`n` forward totality restricted to the prefix chain of
  length `i ≤ n`); `perLengthCell_prefix_coord` (the prefix-coordinate
  IDENTIFICATION: the cell class of a head parameter `u` lies in the
  trace of chart `(0+i+1)` with its coordinate's real value equal to the
  `i`-th chain value of the level-`n` datum chain started at `u` — S119
  at the prefix, VALUE conjunct kept); and
  **`perLengthCell_prefixCoord_monotone`** (the O1/O2 pivot in cell
  form: for every prefix `i ≤ n`, the chain-value coordinate attached to
  chart `(0+i+1)` is `MonotoneDirectionOn` in the head parameter `u` —
  S111 `chain_transport_monotone_direction` pulled back along the
  totality embedding of the head interval into the chain domain; along
  the level-`n` cell the base (`ch 0`) order is preserved/reversed in
  every prefix trace the cell meets).  This is the H3/base-coordinate
  side of the S147-T chaining in cell form: together with S196 the
  level-`n` cell is an interval-charted arc inside
  `⋂_{m ≤ n+1} T_m` whose base-coordinate order matches its order in
  every one of those traces — the certified coordinate refinement the
  S147-T traceUnion coordinate must agree with on the cells (F2-c /
  O1+O2).  ROADMAP S198.
* `OverlapConn.lean` — **S200 + S207 + S208: the overlap-connectivity
  certificates and the prefix chain — the `hconn` of the S183 engine,
  the abstract two-chart gluing, and the chain step** (module
  `Submission/OverlapConn.lean`, 278 lines, sorry-free, warning-free,
  imports TwoArcUnion; imported by Submission.lean after TwoArcUnion).
  Content (namespace LeanEval.KnotTheory.Quadrisecant):
  **`prefixOverlap_connected_of_terminal`** — if the `k`-prefix
  `P_k := ⋃ j ∈ range (k+1), T j` carries an interval chart
  `κk : ORI 0 1 ≃ₜ ↑P_k` and the next trace `T (k+1)` attaches over the
  TERMINAL interval `(s,1)` of the prefix coordinate (`hVend`, the
  chain-step data of TwoChartGlue, with `0 < s < 1`), then the
  prefix-overlap `P_k ∩ T (k+1)` is connected — exactly the
  `hconn k` hypothesis the S183 `finite_chain_union_interval` engine
  consumes.  Proof: the overlap is the range of the continuous map
  `t ↦ (κk (emb t) : X)` from the connected interval
  `{t // t ∈ Ioo s 1}` (`emb` the `Ioo s 1 ↪ Ioo 0 1` embedding from
  `s > 0`); the range equals `P_k ∩ T (k+1)` by the two inclusions given
  by `hVend`; `isConnected_range` + `Subtype.connectedSpace` give the
  overlap subtype's `ConnectedSpace`.  This is the overlap-connectivity
  lemma for one `P'_k`: the facing-terminal data of the chain step
  certifies the prefix-overlap connectivity, closing the gap between the
  TwoChartGlue engine (hdata with `hVend`) and the S183 engine (hconn).
  **S207 (appended)**: the two-set level — `overlap_connected_of_terminal`
  (the S200 certificate with no trace indexing: an arc `U` charted by
  `κ` with `V` attaching over the terminal `(s,1)` of `U`'s coordinate
  ⇒ `ConnectedSpace {x // x ∈ U ∩ V}`), and
  **`terminalTwoChart_union_is_openInterval`** — the ABSTRACT TWO-CHART
  PREFIX GLUING: terminal-attaching open arcs `U`, `V` with interval
  charts glue to an open interval arc (the certificate supplies the
  connected-overlap hypothesis of the S182 ambient two-arc theorem) —
  the first load-bearing step under the generic dichotomy extraction
  `noncompact_connected_oneManifold_interval` (S206).  **S208
  (appended)**: `chain_step_prefix_interval_of_terminal` — the CHAIN
  STEP, abstracted from the S203 walk pattern to generic `X`: an open
  interval-charted `k`-prefix `P_k` with the next trace `T (k+1)` (open,
  interval-charted) attaching over the terminal `(s,1)` of the prefix
  coordinate ⇒ the `(k+1)`-prefix `P_{k+1}` is interval-charted — the
  S200 certificate (`prefixOverlap_connected_of_terminal`) supplies the
  S183 `hconn k`, the S182 two-arc gluing the glued chart, and
  `union_range_succ` the set identity.  With per-level data, iterating
  (via S183/S160) charts every prefix — the chain side of the
  exhaustion assembly under the S206 extraction.  ROADMAP
  S200, S207, S208.
* `FirstPrefixChart.lean` — **S203: the `hNW` interface at the first
  non-vacuous level and the first two-junction prefix chart** (module
  `Submission/FirstPrefixChart.lean`, 138 lines, sorry-free,
  warning-free, imports LevelZeroHconn + TwoArcUnion + RealIntervalShape;
  imported by Submission.lean after LevelZeroHconn).  Content
  (namespace LeanEval.KnotTheory.Quadrisecant):
  `walk_prefixOverlap_connected_one` — the S183 `hconn 1` instance:
  `hNW₁` (the k=1 non-wrapping interface `P'_2 ∩ T 2 ⊆ T 1`) + `hD₁`
  (k=1 transition-domain connectedness) ⇒ prefix-overlap connected at
  k=1 (S201(ii) at k=1 — the first level where `hNW` is genuinely
  needed); `walkChart_lt` (the walk chart interval is nondegenerate);
  `walkTraceORI` (the ORI-`(0,1)` chart of a walk trace: `chartTraceHomeo`
  + the affine interval normalisation `homeo_Ioo_openUnit`);
  and **`walk_prefixThree_intervalChart`** — the LANDMARK: from `hD₀`
  (S202) + `hNW₁` + `hD₁`, the S183 finite-chain engine charts the
  three-trace prefix: `Nonempty (ORI 0 1 ≃ₜ ↑(T 0 ∪ T 1 ∪ T 2))` —
  the first verified interval chart of a MULTI-JUNCTION walk prefix,
  the shape the S147-T chaining was aiming for, delivered from the two
  atomic interfaces `hD`/`hNW` (per-trace openness + ORI charts +
  the two `hconn` instances are exactly `finite_chain_union_interval`
  (S183)'s hypotheses at n = 2).  ROADMAP S203.
* `ComponentIntervalSide.lean` — **S205/S206/S237: the interval side of
  the component dichotomy** (module `Submission/ComponentIntervalSide.lean`,
  468 lines, imports ComponentChart + FirstPrefixChart + IntervalSide +
  ArcRestrict; imported by Submission.lean after IntervalSide; all
  sorry-free except the documented S206 extraction
  `noncompact_connected_oneManifold_interval`, line 211).  **S205 (the
  region chart and what it unlocks):**  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): `TrisecantComponentIntervalSide`
  (the TARGET statement of the dichotomy's interval case: non-compact
  component ⇒ `Nonempty (ORI 0 1 ≃ₜ TrisecantComponent r c₀)` —
  proof = the generic connected-1-manifold dichotomy (S153) on
  `trisecantComponent_isOneManifold`, the recorded remainder);
  `trisecantComponent_connectedSpace` (every component type is
  `ConnectedSpace`, via `Subtype.connectedSpace
  (isConnected_connectedComponent)`); `trace_subset_component` (every
  walk trace lies in the component of `c₀`, from
  `hC : ∀ n, cl n ∈ connectedComponent c₀` — the component serves as
  the region `Ω`); **`walk_transitionDomain_connected_of_component_chart`**
  (the GATE CROSSING: once the component chart `χ` exists, EVERY
  per-level `hD_k` is supplied — the S204(iii) interval-side supply
  with `Ω := connectedComponent c₀`); and
  **`walk_prefixThree_intervalChart_of_component`** (the WIRED output:
  component chart `χ` + the first non-vacuous `hNW₁` ⇒ the interval
  chart of the three-trace prefix `P'_3`, the S203 pattern with
  `hD₀`/`hD₁` interval-side-sourced).  **S206 (the SAME module's
  single `sorry`, IN PROGRESS)**: `trisecantComponent_notCompactSpace`
  (subtype-compactness bridge), `noncompact_connected_oneManifold_interval`
  (THE generic dichotomy extraction: connected T2 second-countable
  locally-interval-charted non-compact `X` is `≃ₜ (0,1)` — documented
  route through the S154–S203 engine) and the assembled gate
  `trisecantComponent_intervalSide`; plus the S209 section
  (`trisecantComponent_pathConnectedSpace`, the targets
  `TerminalExtensionExists`/`ConnectedNoncompactOneManifold_TerminalExtension`).
  **S237 (appended, VERIFIED sorry-free) — the first lemma of the
  independent route / iii-c bridge**: with the interval chart
  `e : (0,1) ≃ₜ X` of the whole space (the S206 output), every open arc
  prefix `P` (chart `κ`) occupies a FINITE coordinate interval:
  `chartPrefixCoord e P = Ioo a b` (`a < b`) — via the coordinate set
  open (`e.continuous.isOpen_preimage`), connected (homeo `{x ∈ P}` via
  the chart and `(0,1)` via `κ`, using the L44 commons
  `Commons.Topology.Homeomorph.subtype_preimage_homeo`), value-image
  open (`isOpenMap_coe_of_isOpen`, S235), preconnected (continuous
  image) and the bounded shape classification (the L45 commons
  `Commons.Analysis.RealIntervals.open_preconnected_nonempty_subset_unit_Ioo_shape`).
  This makes iii-c a corollary once S206 lands (the overlap-coordinate
  set is interval-like ⇒ `hF` and the end strip).  **S238 (appended) —
  the S206 decomposition and the exhaustion base**: the S206 doc now
  records the three-step decomposition (A: compatible exhaustion by
  proper arc prefixes — per-level supply pinned as
  `OneManifoldPerLevelExtension`, a `def Prop`; B: alignment to the
  length-form, S217 item (2); C: the L35 assembly, VERIFIED), and the
  FULL generic classification has been dispatched to the fleet in pure
  form (commons L46 `Commons.Topology.OneManifold.
  noncompact_connected_oneManifold_interval`); verified sorry-free in
  the module: `subtypeUnivHomeo` (the `univ`-subtype reassociation
  homeo) and **`arc_or_proper_open_prefix`** — the exhaustion BASE:
  either `X ≃ₜ (0,1)` already or a proper open arc prefix exists
  (an arc chart of any point is the whole space, or is the proper
  prefix).  **S239 (appended, VERIFIED sorry-free) — the single-interval
  finite structure and the coordinate-set intersections**: Step B /
  iii-c interval-corollary machinery: `Ioo_inter_Ioo_eq` (`(a,b) ∩
  (c,d) = (max a c, min b d)`), `chartPrefixCoord_inter`
  (`chartPrefixCoord e (P∩Q) = chartPrefixCoord e P ∩ chartPrefixCoord
  e Q` — the value-coercion is injective), and
  **`singleInterval_finiteStructure`** — for ANY `a' b' c₀`, `Ioo a'
  b' ∩ Iio c₀` is a finite union of open intervals with upper endpoints
  `≤ c₀` (the single (possibly empty) interval `Ioo a' (min b' c₀)`,
  Finset `{(a', min b' c₀)}`): the `hF` of the attach statements in the
  interval-like case, with no-oscillation automatic (one interval cannot
  oscillate).  With `prefix_coord_interval` (S237) this yields the iii-c
  corollary once the S206 chart exists.  ROADMAP
  S205/S206/S209/S237/S238/S239.  **S242/S243 (appended): S206 CLOSED
  and the H2 COMPACT side opened** — the local
  `noncompact_connected_oneManifold_interval` is now the one-line
  `simpa` bridge to fleet L46 (`Commons.Topology.OneManifold.
  noncompact_connected_oneManifold_interval`, LANDED): the interval side
  of the component classification is COMPLETE
  (`trisecantComponent_intervalSide` holds).  S243: the compact side's
  gate `TrisecantComponentCompactSide` (def Prop) and the verified
  set-to-type bridge `trisecantComponent_compactSpace`
  (`isCompact_iff_compactSpace`); the generic compact classification is
  fleet L65 (`Commons.Topology.OneManifold.
  compact_connected_oneManifold_circle`, IN FLIGHT) — when it lands,
  `trisecantComponent_compactSide` closes the compact case exactly as
  L46 closed the interval case.  **S244 (appended, VERIFIED reduction) —
  the interval-branch obstruction statement**: `LoopsTrivial X` (every
  continuous circle map is null-homotopic — no essential loops),
  `nullHomotopic_iff_comp_homeo` (null-homotopy transfers across a
  homeomorphism, both directions), `LoopsTrivial_of_intervalChart`
  (the S242 chart reduces loop-triviality to `LoopsTrivial (ORI 0 1)`),
  and the gate `TrisecantIntervalComponentLoopsTrivial`.  **S244
  (completion, appended, VERIFIED) — the interval branch CLOSED**:
  `LoopsTrivial_openUnit` (loops into `(0,1)` are null: transport to `ℝ`
  via `homeo_real_openUnit`, `ContractibleSpace ℝ` via Mathlib's
  `id_nullhomotopic` + `ContinuousMap.Nullhomotopic.comp_left`, pull
  back through the inverse homeo) and `trisecantIntervalComponent_loopsTrivial`
  (the S242 chart + `LoopsTrivial_of_intervalChart` + openUnit close the
  interval branch of the Layer-C obstruction: interval components carry
  no essential loops — "only circular components obstruct" holds on the
  interval side).  **S245 (appended, VERIFIED drafts + skeleton) — the
  compact-side completion and the circular winding skeleton**: the
  assembly tail `trisecantComponent_compactSide_of_circleClassification`
  (given `Nonempty (Circle ≃ₜ component)`, the compact gate holds) and
  the L65 premises `trisecantComponent_compactSide_premises`
  (`LocallyIntervalChart ∧ ConnectedSpace ∧ CompactSpace` from S152/S205/
  S243) — the three-line `trisecantComponent_compactSide` final body is
  recorded for the L65 landing; plus the winding skeleton
  (`IsCircleEmbedding`, `CircularTrisecantComponent` — essential circle
  components of O — and the once/twice statement split with chart
  assumptions and the two case decompositions recorded).  **S246
  (appended, VERIFIED avatar) — the ONCE branch**: `no_periodic_advance`
  (a real function cannot be simultaneously `T`-periodic and advance by a
  non-zero `p` per circuit — the real-analysis avatar of the ONCE jump:
  well-defined middles (`AtMostOneMiddle`) cannot carry a half-period
  advance); the full ONCE contradiction needs the circle-map degree fact
  (integer lift advance), recorded as the missing formal object with the
  S112-C reduction tree.  **S248 (appended, VERIFIED) — the TWICE
  family-production endpoint**: `MiddlePointsOnClass_subset_MiddleCovered`
  (the class-middle ⊆ covered-middle bridge, witnessed by the
  representative's endpoints) and `no_twiceWinding_data` (given the
  TWICE circular-component data — L65 circle chart `χ`, the continuous
  unique-middle selection `μ` on the component, and a full-period
  advancing real lift `G` of `μ ∘ χ` — the TWICE contradiction closes by
  pure assembly with `S247.twiceWinding_middle_contradiction`); the
  constituent facts (i) chart `χ`, (ii) `μ` continuity, (iii) TWICE
  measurement, are itemized.  ROADMAP S242–S248.
**S249 (appended, VERIFIED) — the COMPACT side CLOSED (fleet L65 landed)**: `compact_connected_oneManifold_circle_local` (the bundled-`LocallyIntervalChart` bridge mirroring the interval-side wrapper, `simpa [LocallyIntervalChart, OpenRealInterval]` to `Commons.Topology.OneManifold.compact_connected_oneManifold_circle`) and **`trisecantComponent_compactSide`** (THE compact-case gate ASSEMBLED: `IsCompact (connectedComponent c₀ : Set (OSub r)) → Nonempty (Circle ≃ₜ TrisecantComponent r c₀)` via the S152/S205/S243 premises feeding L65).  Together with the interval side (S206/S242) this CLOSES the component dichotomy: every connected component of the trisecant set is an open interval (non-compact side) or a circle (compact side).  ROADMAP S249.
  **S250 (appended, VERIFIED) — compact components are embedded circles of the band**: `component_simpleClosedCurve_of_circleHomeo` (given the circle homeo χ : Circle ≃ₜ TrisecantComponent r c₀, the composite with the subtype projections is an injective continuous circle map into OpenMobius — a `SimpleClosedCurve` — with image exactly the component val-set `(fun s : OSub r => (s : OpenMobius)) '' (connectedComponent c₀ : Set (OSub r))`) and `compact_component_isCircleEmbedding` (a compact component is `IsCircleEmbedding` of its val-image: S249 + the former) — the `IsCircleEmbedding` half of the S245(b) `CircularTrisecantComponent` vocabulary, feeding the Layer-C winding measurement.  ROADMAP S250.
  **S251 (appended, VERIFIED) — the dichotomy in disjunctive form + interval components as embedded open arcs**: `trisecantComponent_dichotomy` (every connected component of the trisecant set is homeomorphic to the open unit interval or to the circle — by_cases on set-level compactness feeding S242/S249) and `component_arc_of_intervalHomeo` (the S250 mirror: an interval-charted component is an embedded open arc of the band, injective continuous (0,1)-map with range = the component val-set).  S250+S251 realize BOTH sides of the dichotomy as concrete embedded subsets of the band.  ROADMAP S251.
* `ComponentMiddle.lean` — **S252 (VERIFIED): the continuous
  unique-middle selection on a component — TWICE-branch family-production
  item (ii)** (module `Submission/ComponentMiddle.lean`, sorry-free,
  imports ComponentChart).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): `componentMiddle` (the canonical
  strict middle of the class of a component point,
  `classMiddle r (z : OSub r : OpenMobius) (z : OSub r).2`);
  `componentMiddle_mem_middleSet` (membership `componentMiddle c₀ z ∈
  MiddlePointsOnClass r (z : OSub r)`); `seqContinuous_componentMiddle`
  (SEQUENTIAL continuity: a component sequence `xₙ → p` carries middles
  to the canonical middle of `p`'s class — strict representative of the
  limit class (`strictRep_of_trisecant`) + the strict-base middle
  convergence (`middle_tendsto_of_strictBase`, instancing
  `middle_tendsto_of_class_tendsto` with the `TorusGeneralPositionTransverse`
  fundamental-domain reps) + `strict_middle_unique_on_class` under
  `QuadrisecantFree` identifies the limit with the canonical middle);
  `componentMiddle_continuous` (the TOPOLOGICAL upgrade: the component
  (subspace of the second-countable band) is a `SequentialSpace`, so
  `SeqContinuous.continuous`); and the packaged
  `exists_continuous_unique_middle_on_component` (item (ii): every
  component carries `μ` with `Continuous μ` and `μ z ∈
  MiddlePointsOnClass r (z : OSub r)`).  Together with item (i)
  (`trisecantComponent_compactSide`, S249) the TWICE branch reduces to
  item (iii) — the full-period advancing lift `G` (the winding
  measurement of Layer-C brick (c)); the ONCE branch has the same `μ`
  with its half-period-advance avatar.  ROADMAP S252.
* `ComponentWindingData.lean` — **S253 (VERIFIED): the pinned
  ONCE/TWICE winding-data interfaces** (module
  `Submission/ComponentWindingData.lean`, sorry-free, warning-free,
  imports ComponentMiddle + ComponentIntervalSide + Pi1Mobius).  Content
  (namespace LeanEval.KnotTheory.Quadrisecant):
  `no_onceWinding_advance` (THE ONCE contradiction pinned in final
  geometric form: a continuous real lift `mhat` of the middle selection
  `componentMiddle c₀ ∘ χ` advancing HALF a knot period per circuit
  (`mhat (t+T) = mhat t + halfPeriod`) is impossible — the class is
  `T`-periodic (`(t+T : AddCircle T) = (t : AddCircle T)`), so the circle
  value returns at `t+T`, while the advance shifts it by the non-zero
  `(halfPeriod : AddCircle period)`; Kuperberg's ±g "endpoints travel half
  way around and switch, trapping the middle into a jump");
  `TwiceWindingAdvancingLift` (item (iii) — the TWICE data shape: a
  continuous real lift `G` of `componentMiddle c₀ ∘ χ` advancing a FULL
  knot period per circuit, `G (t+T) = G t + period`, exactly the datum
  consumed by `no_twiceWinding_data` S248); `no_twiceWinding_component_of_lift`
  (the TWICE contradiction ASSEMBLED: item (i) `χ` + item (ii)
  `componentMiddle` continuous/membership (S252) + the item-(iii) datum
  feed `no_twiceWinding_data` with no further analysis);
  `addCircleHomeo_of_circleHomeo` + `trisecantComponent_compactSide_addCircle`
  (item (i) in `AddCircle` form: the S249 `Circle ≃ₜ` output
  reparametrises through `Pi1Mobius.paramCircleHomeo` to
  `AddCircle period ≃ₜ TrisecantComponent r c₀`, circuit length
  `period > 0`); and `componentMiddle_lift_advance` (fleet L66
  `Commons.Topology.AddCircle.circleMap_lift_advance` instanced at the
  continuous `T`-periodic middle map: the middle selection on a circular
  component has an INTEGER degree — a continuous real lift with advance
  `G (t + T) = G t + (k : ℝ) * period`, `k : ℤ`; the formal integer-degree
  fact of the ONCE analysis and the carrier of the TWICE measurement,
  which pins `k = 1`).  Both branches are now pure assembly away from their
  geometric measurements — the derivation of the half/full-period
  advancing lifts from a once/twice-winding circular component (Layer-C
  brick (c): the real-lift bookkeeping on the ordered double cover over
  the component's winding parity, `lift_loop_end_even_or_odd` /
  `lift_from_swap_ends_swapped`), recorded not yet formalised.  ROADMAP
  S253.  **S254 (appended, VERIFIED sorry-free) — the `k ≠ 0` TWICE
  contradiction at component level** (the S253b sub-problem-5 fallback):
  `no_twiceWinding_component_of_lift_zsmul` — the S253 mirror for ANY
  nonzero integer degree: a continuous real lift `G` of the middle
  selection `componentMiddle c₀ ∘ χ` advancing by `(k : ℝ) * period`,
  `k ≠ 0`, per circuit is impossible (ParameterWinding S254
  `twiceWinding_middle_contradiction_zsmul` fed by
  `componentMiddle_mem_middleSet` through the
  `MiddlePointsOnClass_subset_MiddleCovered` bridge; `componentMiddle`
  continuity is NOT needed — the lift `G` carries the regularity) — the
  twice-winding geometry only needs to produce `k ≠ 0` (μ∘χ not
  null-homotopic), a strictly weaker measurement than `k = 1`.  ROADMAP
  S254.  **S255 (appended, VERIFIED sorry-free) — the middle selection of every
  circular component has DEGREE ZERO**: `componentMiddle_has_periodic_lift`
  — under the full hypotheses the middle selection `componentMiddle c₀ ∘
  χ` of a circular component chart `χ : AddCircle T ≃ₜ
  TrisecantComponent r c₀` (`0 < T`) admits a continuous `T`-periodic
  real lift (`G (t + T) = G t`), because the integer degree of
  `componentMiddle_lift_advance` (S253) must be `0` (a nonzero degree
  would be the S254 contradiction).  This is the structural fact that the
  twice-winding geometry (full-period or nonzero-degree advance) and the
  once-winding avatar (half-period advance) both contradict — the formal
  "degree must vanish" statement brick (c) negates.  ROADMAP S255.
* `ChartRefine.lean` — **S210–S213: route (α) — the two-chart
  intersection mechanism, the local-refinement heart, the cell
  neighbourhood basis, and the countable cell cover** (module
  `Submission/ChartRefine.lean`, 502 lines, sorry-free, warning-free,
  imports the L34 commons `preconnected_inter_of_homeoUnit` +
  OneManifold + IntervalSide; imported by Submission.lean after
  IntervalSide).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant):
  `inter_connected_of_common_intervalChart` — the precise meaning of
  "intersecting arcs meet connectedly" in interval-chart coordinates:
  two open preconnected subsets `s`, `t` of `X` inside ONE
  interval-charted open region `W` (`ρ : ↑W ≃ₜ (0,1)`) meet
  CONNECTEDLY when nonempty (both are open intervals in the region's
  coordinates — the L34 commons fact at subtype level); and
  `walkTrace_inter_connected_of_common_region` — the O-side instance:
  two consecutive walk traces inside one interval-charted region meet
  connectedly (traces open by `isOpen_chartTrace`, preconnected by
  `chartTrace_preconnected` (S204)) — the region-local form of the
  per-level overlap content, with the region possibly SMALLER than the
  whole component (the refinement-style locality route (α) needs).
  **S211 (appended) — the local-refinement heart**: `chartCell` /
  `isOpen_chartCell` (the subregion of a chart trace over a coordinate
  interval `(a,b)`, open); **`chartCellHomeo`** (a sub-interval
  `(a,b) ⊆ (lo,hi)` is still a chart of the open subregion:
  `ChartInterval a b ≃ₜ {c // c ∈ chartCell ch a b}` — the S140a
  pattern at raw chart level); `chartCell_inter` (two cells of one chart
  meet in the cell of the overlap interval:
  `cell(a,b) ∩ cell(c,d) = cell(max a c, min b d)`); and
  `chartCell_inter_homeo` (the pairwise content: the intersection of two
  cells of one chart is interval-charted by the overlap interval — any
  two sub-arcs of one chart meet connectedly).  **S212
  (appended)**: `chartCell_nhds_basis` — for a chart `ch`, a parameter
  `t₀` and any open neighbourhood `U` of `oChartLift ch t₀`, a cell
  `chartCell ch a b` over a coordinate interval around `t₀` contains the
  point and lies inside `U` (the cells over coordinate intervals form a
  NEIGHBOURHOOD BASIS of the lift: open preimage of `U` under the
  continuous lift → ε-ball → halved real interval `(max lo (t₀−δ),
  min hi (t₀+δ))`); and `chartCell_pairwise_common_at_point` — two
  cells containing the same lifted point meet in the interval-charted
  common cell over the overlap interval, containing the point.  The
  covering argument (S209/S210) picks a basis cell at each point and
  uses (2) for pairwise-connected overlaps.  **S213 (appended) — the
  countable cell cover**: `basisCellA`/`basisCellB`/`basisCell_spec`
  (the canonical basis cell of a chart around a parameter, with its
  coordinate interval embedding in the chart's via the S212 containment
  conjunct), and **`osub_countable_chartCell_cover`** — the COVER
  LEMMA: a COUNTABLE set `R` of centres whose basis cells are open and
  interval-charted (`chartCellHomeo`, S211) and cover the whole
  trisecant set (each class is in its own chart's canonical cell; the
  Lindelöf property of the second-countable trisecant set extracts the
  countable subcover via `IsLindelof.elim_countable_subcover`).  This is
  the combinatorial core of route (α): a countable cover by chart cells,
  each carrying its parent chart for the S212 pairwise content.  ROADMAP
  S210–S213.
* `CellWalk.lean` — **S215: the component traversal walk over the
  countable cell cover (clause (i) of the exhaustion ordering)** (module
  `Submission/CellWalk.lean`, ~350 lines, sorry-free, warning-free,
  imports ChartRefine + ComponentWalk + ComponentChart + ConnectedWalk;
  imported by Submission.lean after ChartRefine).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): `centreCell` (the canonical basis
  cell of the chart at a class, an abbrev unfolding to
  `chartCell (oChartAtClass … y) (basisCellA …) (basisCellB …)`),
  **L1** `centre_mem_own_cell` (every centre lies in its own cell, via
  `basisCell_spec` + `chParam_lift`), `centreCell_lt`/`centreCell_charted`/
  `centreCell_isConnected`/`centreCell_pathConnected` (the centre cell
  is interval-charted — `chartCellHomeo` — hence connected and
  path-connected), **L2** `centreCell_subset_component_of_meets` (a
  connected centre cell meeting `connectedComponent c₀` is contained in
  it; `IsConnected.subset_connectedComponent` + `connectedComponent_eq`
  with the direction `.symm`) and `centreCell_subset_component` (the
  derived form: the cell centred at a class of the component lies in the
  component), **L3** `component_cell_cover` (the countable ENUMERATED
  cover of a component by cells centred at its own classes:
  `eq_open_union_nat` over the second-countable trisecant set, the S107
  pattern with cells), and **L4 — the S214 target**
  `component_cell_traversal`: there is an enumeration `Y : ℕ → OSub r`
  of centre classes of the component with consecutive cells meeting,
  path-connected open prefix unions `⋃ m ∈ Iio (n+1), cell(Y m)`
  contained in the component and increasing, the nested prefixes
  exhausting the component, and the single cells covering it.  The proof
  instantiates `ConnectedWalk.exists_pathConnected_open_exhaustion` over
  the component subspace `ComponentSub c₀` exactly as S115's
  `component_trace_walk`, transferring the ambient-level
  path-connectedness of the prefix unions through the embedding via
  `Topology.IsInducing.isPathConnected_iff` +
  `Subtype.image_preimage_val` + `Set.inter_eq_left`.  ROADMAP S215.
* `IntervalSide.lean` — **S204: the interval-side supply of the
  per-level `hD_k`** (module `Submission/IntervalSide.lean`, 196 lines,
  sorry-free, warning-free, imports LevelZeroHconn + the L34 commons
  `preconnected_inter_of_homeoUnit`; imported by
  Submission.lean after LevelZeroHconn).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): `chartTrace_preconnected` (every
  chart trace is preconnected — continuous image of the connected chart
  interval); `overlapCoordMap`/`continuous_overlapCoordMap` (the
  `ch₁`-coordinate map on a trace overlap); 
  `transitionDomain_preconnected_of_overlap_preconnected` (the
  coordinate transfer: preconnectedness of the overlap passes to the
  transition domain, its image); and
  **`walk_transitionDomain_connected_of_intervalAmbient`** — the supply
  theorem: given an open region `Ω ⊇ T k ∪ T (k+1)` and the region's
  interval fact `hInter` (intersection of two open preconnected subsets
  of `Ω` is preconnected — the L33/L34-derived consequence of the
  region chart `χ : ↑Ω ≃ₜ (0,1)`), the transition domain `D_k` is
  CONNECTED: the `hD_k` interface, Nonempty half from the overlap class
  (S202) + Preconnected half from the interval-side geometry.  This is
  the per-level interface the dichotomy's interval case instantiates.
  **S204(iii) (L34 LANDED)**: `walk_transitionDomain_connected_of_intervalChart`
  — the corollary instantiating `hInter` from the region chart `χ` via
  the L34 commons lemma `preconnected_inter_of_homeoUnit`: with
  `χ : ↑Ω ≃ₜ ORI 0 1` and `T k ∪ T (k+1) ⊆ Ω`, the transition domain
  `D_k` is CONNECTED — the first genuinely interval-side-sourced `hD_k`
  statement (the dichotomy's interval case supplies `χ` and the
  trace-containment per level).  ROADMAP S204.
* `LevelZeroHconn.lean` — **S202: the first-level `hD` interface —
  what the junction geometry must deliver** (module
  `Submission/LevelZeroHconn.lean`, 116 lines, sorry-free, warning-free,
  imports OverlapHconn; imported by Submission.lean after OverlapHconn).
  Content (namespace LeanEval.KnotTheory.Quadrisecant):
  `walk_prefixOverlap_connected_zero` — the S183 `hconn 0` instance: at
  the FIRST junction the non-wrapping hypothesis is VACUOUS (the prefix
  `P'_1` is the single trace `T 0`), so `hconn 0` reduces to the single
  atomic interface `hD₀ = IsConnected (transitionDomain (walkChart 0)
  (walkChart 1))` (connectedness of the coordinate set of `T 0 ∩ T 1`;
  proof: `Finset.range_one` prefix equality + the S201(i) transfer +
  `Subtype.connectedSpace`); and `walk_transitionDomain_nonempty` — the
  `Nonempty` HALF of the `hD` interface at every junction `k` (the
  walk-overlap class has a `ch k`-coordinate in the transition domain).
  Honest analysis recorded in the module doc: `hD = Nonempty ∧
  IsPreconnected`; the Nonempty half is now proved (overlap data), the
  IsPreconnected half (no SECOND/wrap component of `D_k`) is NOT
  derivable from the junction-component geometry alone — two open arcs
  of a circle component can intersect in two components — so `hD` is an
  ATOMIC interface supplied by the dichotomy's interval side (the
  per-level `IsConnected (transitionDomain (walkChart k) …)` feeding
  `walk_prefixOverlap_connected_zero` at k = 0 and
  `walk_prefixOverlap_connected_of_nonWrapping` at k ≥ 1).  ROADMAP
  S202.
* `OverlapHconn.lean` — **S201: the overlap-connectivity reduction to
  the local interfaces — the first ordering-content lemmas of the
  O-side** (module `Submission/OverlapHconn.lean`, 158 lines,
  sorry-free, warning-free, imports NestedFamily + JunctionOrder +
  OverlapConn; imported by Submission.lean after OverlapConn).
  Content (namespace LeanEval.KnotTheory.Quadrisecant):
  `chartOverlap_connected_of_transitionDomain` (the trace-overlap
  connectedness TRANSFER: the overlap `chartTrace ch₁ ∩ chartTrace ch₂`
  is connected iff the transition domain `transitionDomain ch₁ ch₂`
  — the coordinate set of the overlap — is connected; proof: the
  overlap is the range of `x ↦ oChartLift ch₁ x` on the
  transition-domain subtype (`isConnected_range`), and every overlap
  class is the lift of its own `ch₁`-coordinate (`chParam` +
  `chParam_lift`)); and **`walk_prefixOverlap_connected_of_nonWrapping`**
  — the S183 `hconn k` of the walk prefix from TWO local interfaces:
  the non-wrapping hypothesis `hNW : P'_k ∩ T (k+1) ⊆ T k` (the next
  trace attaches only at the terminal end) + connectedness of the
  successive transition domain `D_k` (where the S199/WI machinery
  certifies the junction component) ⇒ `ConnectedSpace` of the
  prefix-overlap subtype.  Proof: `hNW` gives the set equality
  `P'_k ∩ T (k+1) = T k ∩ T (k+1)` (`T k ⊆ P'_k` the reverse
  inclusion), then (i) transfers the transition-domain connectedness.
  This is the first verified piece of the O-side ordering content: the
  global overlap-connectivity obligation of the chaining is reduced to
  the non-wrapping interface (dichotomy content) plus the local
  transition-domain connectedness.  ROADMAP S201.
* `JunctionOrder.lean` — **S199: the single-junction class-order
  transition — the H1 step of the S147-T chaining** (module
  `Submission/JunctionOrder.lean`, 227 lines, sorry-free, warning-free,
  imports NestedFamily; imported by Submission.lean after PrefixCoord).
  Content (namespace LeanEval.KnotTheory.Quadrisecant): `chParam` (the
  inverse-coordinate map: the chart parameter of a trace class, with
  `chParam_lift`); `chParam_transition_real` (the coordinate-change
  identification at real-value level: the real transition value of the
  `ch₁`-parameter of a shared class equals the real value of its
  `ch₂`-parameter — corollary of the S98 `oChart_param_transition`);
  `transitionDomain`/`junctionComponent` (the transition-domain set of
  `ch₁` towards `ch₂`, and the connected component of the junction
  parameter); `junctionClassOrder_of_monotone` (the generic H1
  transfer: monotone-or-antitone of the real transition on the junction
  component ⇒ two overlap classes with `ch₁`-coordinates in the
  component keep their `ch₁`-order in their `ch₂`-coordinates, same
  direction); and **`walk_junction_classOrder`** (the S199 headline:
  the S150-WI monotone transition read at CLASS level — classes of the
  overlap of the walk traces `T_m`/`T_{m+1}` whose `ch m`-coordinates
  lie in the junction component of the walk-overlap class are
  consistently ordered by the two trace coordinates).  This is the
  single-junction transition the prefix-union chaining composes: the
  coordinate gluing at a junction keeps the order of the overlap
  classes, so a monotone prefix coordinate extends across the junction
  over the overlap component.  ROADMAP S199.
* `PrefixArcChart.lean` — **S189: nested per-length reindexing (the first
  overlap-and-reindex lemma of the `Uₙ` assembly)** (appended to
  `Submission/PrefixArcChart.lean`, 543 → 588 lines, sorry-free,
  warning-free).  Corollaries of the S140b change-of-chart
  `walkAligned_changeChart_of_nested`: **`walkAligned_changeChart_reindex_val`**
  — for two aligned datums with nested start intervals `hI : (a′,b′) ⊆
  (a,b)`, the outer-chart coordinate of an inner-range class equals its
  inner coordinate (`(u : ℝ)`): the consecutive-length change of chart is
  the REAL IDENTITY reindexing; and
  **`walkAligned_changeChart_monotone`** — the change of chart is
  real-monotone in one direction (`MonotoneDirectionOn` with the start
  coordinate).  These are the S140-T2 coordinate-compatibility conjuncts
  at one consecutive-length pair; the `Uₙ` assembly chains them over
  consecutive lengths.  ROADMAP S189.
* `TwoChartGlue.lean` — **S154–S155: the ordered two-chart gluing core
  (the engine's atomic step: facing end-overlap charts glue to an open
  interval)** (new module `Submission/TwoChartGlue.lean`, 316 lines,
  sorry-free, warning-free, imported by Submission.lean after
  OneManifold; generic topology on `OneManifold`'s `OpenRealInterval` +
  the fleet facts L30/L31).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): charts normalised to `(0,1)`;
  `T hu1 φ ψ hUend hv` (the U-chart coordinate of the overlap point
  `ψ v`, `v ∈ (0,u)`) with `T_mem` (values in `(s,1)`) and `T_range`
  (surjectivity onto `(s,1)`); `Tfun` (the real-function form; its
  `if`-condition is `0 < v ∧ v < u` — the membership form does not match
  `dif_pos`) with `Tfun_eq`/`Tfun_range`/`Tfun_strictMonoOn`; the
  endpoint-limit **`T_endpoint_right`** (S154 (P1): under the
  orientation-preserving hypothesis `hinc`, `T v → 1` as `v → u⁻`,
  invoking the fleet L31) and `T_lt_one`; the seam function **`Gfun`**
  (`T v` on `(0,u)`, `v + 1 − u` elsewhere) with `G_at_u` (`G u = 1`)
  and **`G_continuousAt`** (S155: continuous at `u` — left side by
  `T_endpoint_right` + `T_lt_one`, right side affine).  S156: the global
  **`twoChartF hu1 φ ψ hUend hUV : X → OpenRealInterval 0 (2 − u)`**
  (U-coordinate on `U`, V-coordinate + `1 − u` on `V∖U`) with value
  lemmas `twoChartF_val_memU`/`twoChartF_val_not_memU`, the tail-bound
  `coord_ge_u_of_not_memU`, and **bijectivity**
  (`twoChartF_surjective`/`twoChartF_injective`/`twoChartF_bijective`:
  image regions `(0,1)` and `[1,2−u)` disjoint, coordinates injective
  on each side).  S157: **continuity of `twoChartF`** —
  `Tfun_continuousOn` on `(0,u)` (coordinate composition of the chart
  homeos); `Gfun_continuousOn` on `(0,u)` (equals `Tfun`), `(u,1)`
  (affine) and `(0,1)` (seam by `G_continuousAt`);
  `twoChartF_comp_ψ_val` (`F(ψ t) = Gfun t`); `twoChartF_continuousOn_U`
  and `twoChartF_continuousOn_V`; the open-cover glue
  `continuous_of_continuousOn_open_cover`; **`twoChartF_continuous`**
  (S157 (d)); the inverse transition `Sfun` with its endpoint limit
  `Sfun_endpoint_top` (S157 (e)); the inverse **`twoChartG`** with the
  seam identity `φ_eq_ψ_Sfun`, the seam convergence
  `twoChartG_left_converge`/`twoChartG_right_converge`, the seam
  `twoChartG_continuousAt_seam` and **`twoChartG_continuous`** (S157 (f)
  steps 1–3); and the inverse identities
  `twoChartG_comp_twoChartF`/`twoChartF_comp_twoChartG` with the
  **two-chart gluing theorem `two_chart_glue_homeo`** — facing
  end-overlap charts (open `U V`, `0<s<1`, `0<u<1`, overlap
  `(s,1)`/`(0,u)` in coordinates, `hinc` orientation-preserving,
  `U ∪ V = univ`) glue to `X ≃ₜ OpenRealInterval 0 (2 − u)` (S157 (f)
  step 4).  S158: the finite real-chain coordinate model
  `range_chain_union_interval`, the generalized reassociation
  `unionSubtypeHomeo`, and **`single_junction_extension`** — the
  chain-induction step: two open regions `U V` of an ambient space with
  facing terminal-overlap charts glue to
  `{z | z ∈ U ∪ V} ≃ₜ OpenRealInterval 0 (2 − u)`, via
  `two_chart_glue_homeo` on the union-subtype with transported overlap
  equivalences and the (computational) `Tfun`-invariance under
  reassociation.  (ROADMAP S154/S157/S158: the atomic gluing step and
  the single-junction extension of the sweep are fully verified).
  S159: **`prefix_two_charts_interval`** and the abstract
  **`chain_step`** (with `setEqSubtypeHomeo`, `union_range_succ`,
  `norm01`) — a prefix union that is an interval chart extends by one
  facing terminal-overlap trace to the `(k+2)`-prefix
  (`ORI 0 1 ≃ₜ {z | z ∈ ⋃ j∈range(k+2), T j}`): the finite-chain
  induction step, ready for `Nat` recursion.  S160: the
  **finite-chain prefix interval theorem** — `prefix_open` (each prefix
  union `⋃ j ∈ range (k+1), T j` is open), `prefix_zero_interval`
  (base: single trace), `chain_step_open` (chain_step with derived
  prefix-openness), and **`finite_prefix_interval`**: given per-trace
  interval charts `η` and per-level facing terminal-overlap data
  (`hdata`, stated against the current prefix homeo `κk`) with the
  `hinc` monotone transitions, every prefix union is an interval chart
  (`∀ k, Nonempty (ORI 0 1 ≃ₜ {z | z ∈ ⋃ j∈range(k+1), T j})`) — the
  chain-induction harness of the S147-T sweep.  S161: the
  **interval-side dichotomy markers** — `prefix_proper_growth` (a
  facing-terminal chain step strictly grows the prefix union: the new
  trace has points outside the `k`-prefix when its overlap is `(0,u)`,
  `u < 1`) and `chain_data_fails_at_full_prefix` (facing-terminal data
  with `u < 1` is impossible at a level whose prefix already covers the
  whole space — the wrap marker: compact/circle components are not
  chainable, infinite facing-terminal chains are the non-compact
  (interval) side's certificate).
* `ComponentChart.lean` — **Milestone-2 (iv) step 6, brick (b): the
  components of the trisecant set `O` are topological 1-manifolds (the
  local-interval interface of the interval/circle classification)**
  (new module `Submission/ComponentChart.lean`, 149 lines, sorry-free,
  warning-free, imported by Submission.lean after WalkPartialUnion).
  Content (namespace LeanEval.KnotTheory.Quadrisecant): **`osub_local_interval`**
  — at every trisecant class `x`, an open neighbourhood `U` of `x` in
  `O = trisecantSet r` with `U ⊆ connectedComponent x` and `U`
  homeomorphic to an open real interval `ChartInterval lo hi` (the trace
  of the `OSub1Chart` at `x` — `isOpen_chartTrace` +
  `chartTrace_subset_connectedComponent` + `chartTraceHomeo`);
  **`TrisecantComponent r c₀`** — the type of trisecant classes in the
  connected component of `c₀`; **`compSubtypeHomeo`** — the
  reassociation homeo transporting the chart homeo between a subtype of
  the ambient trisecant set and the corresponding subtype of the
  component; **`component_local_interval`** — every point of a component
  has an open neighbourhood in the component homeomorphic to an open real
  interval (the local-1-manifold interface of the classification); and
  `component_t2Space` / `component_secondCountableTopology` (the
  component is Hausdorff and second countable, a subspace of the band
  `OpenMobius`).  Together with path-connectedness (ComponentPath) this
  is the precise input the generic classification of connected
  topological 1-manifolds without boundary (compact component ⇒ circle;
  non-compact ⇒ open interval) will instantiate on the `OSub1Chart`-atlas
  of `O` (S152).  Section 5 (S153 bridge) adds
  **`trisecantComponent_isOneManifold`** (each component satisfies the
  generic `IsOneManifold` predicate of `Submission.OneManifold`) and
  **`trisecantComponent_countable_open_arc_cover`** (each component is
  covered by countably many open arcs — the S153 exhaustion-engine
  existence theorem instantiated on the components).
* `ConnectedWalk.lean` — **Milestone-2 (iv) step 6, brick (b):
  generic point-set-topology input of the component-classification
  exhaustion ordering: overlap-walks of a countable connected open
  cover** (`Submission/ConnectedWalk.lean`, 577 lines, sorry-free,
  warning-free, imported by Submission.lean).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant.ConnectedWalk, pure `Mathlib`, no
  problem-specific imports): over a preconnected space `X` with a
  countable open cover `U : ℕ → Set X` by nonempty open sets
  (`hU : IsOpen`, `hUn : Nonempty`, `hcover`) —
  **`graph_connected`** (the overlap graph is connected: any two indices
  are joined by a chain of consecutive overlaps
  `Adj U a b := (U a ∩ U b).Nonempty`, in `Relation.ReflTransGen` form;
  proof: separate the reachable-from-`a` indices from the rest and apply
  preconnectedness of `univ` to the two open unions);
  **`Walk R a b`** (bundled finite walk: nonempty list with `IsChain`,
  head `a`, last `b`), `Walk.append_last`, `tail_ne`/`tail_last`/
  `rel_head_tail`, `exists_walk_of_rtc` and **`walkOf`** (concrete chain
  extracted from an RTC proof by choice);
  the **round construction**: `RoundData`, `nextRound`, **`rounds`**
  (round `r` walks from `r` to `r+1` along the chosen finite chain and
  appends the new vertices, so `rounds r` contains every vertex `≤ r`
  and ends at `r`), with the joint invariant `rounds_ind` (nonempty,
  `cur = r`, `IsChain`, last `= r`, contains all `≤ r`) and the derived
  `rounds_ne`/`rounds_chain`/`rounds_last`/`rounds_mem`/
  `rounds_succ_list`/`rounds_length_ge`;
  **`walkPos`** (the diagonal flattening: vertex at time `n` is position
  `n` of round `n`; the prefix lemma `rounds_fix` shows elements of a
  round stay fixed in later rounds), **`walkPos_adjacent`** (consecutive
  times are overlap-adjacent: both positions lie inside round `n+1`,
  whose list is a chain) and **`walkPos_surjective`** (every vertex `k`
  lies in round `k` at some position `i`, and the diagonal reads it off
  by the prefix fix in the appropriate direction);
  the packaged theorems: **`exists_overlap_walk`** — `∃ e : ℕ → ℕ`,
  `e 0 = 0`, `(U (e n) ∩ U (e (n+1))).Nonempty` for all `n`, and
  `Function.Surjective e`; and **`exists_pathConnected_open_exhaustion`**
  — if every `U n` is path-connected, an overlap walk `e` with the
  partial unions `V n = ⋃_{m<n+1} U (e m)` (returned with `e`): open,
  path-connected, increasing, covering `X` (combined form, tied by the
  equality `V n = ⋃ m ∈ Iio (n+1), U (e m)`).  This is the topological skeleton of the ordering
  construction: the interval-chain exhaustion over a component of the
  trisecant set instantiates it with the chart traces (each
  homeomorphic to an open interval, hence path-connected, and the
  S107/S108 trace-cover gives the countable open cover of the component)
  — the next slice glues the interval coordinates monotonically along
  the walk (S102–S111 machinery) to classify the components.
* `OChartTwoStep.lean` — **Milestone-2 (iv) step 6, brick (b):
  finite-chain gluing — the two-step composite of aligned monotone patches
  (second subgoal of the interval-chain exhaustion)**
  (`Submission/OChartTwoStep.lean`, 130 lines, sorry-free, warning-free,
  imported by Submission.lean).  Content (namespace
  LeanEval.KnotTheory.Quadrisecant): **`MonotoneDirectionOn`** — a
  real-valued function on a domain with a real coordinate is monotone in
  one direction with respect to the coordinate (strictly increasing or
  strictly decreasing), and **`MonotoneDirectionOn.injective`** — with an
  injective coordinate it is injective; `transportStepDomain_coord_injective`
  — the real coordinate of a step-domain element is injective;
  **`oChartTwoStepMap`** — the composite transport over two aligned
  monotone pieces (defined on the step domain: first-piece parameters
  whose transport lands in the second piece); **`oChart_two_step_composite`**
  — the two-step composite is monotone in one direction and injective on
  its step domain (S104 composition engine `composite_monotone_direction`
  on the two S102 `MonotoneOnPiece` maps, plus
  `MonotoneDirectionOn.injective`).  This is the atomic two-step lemma of
  the finite-chain iterated transport (next subgoal of the interval-chain
  exhaustion).
* `CompactCover.lean` — **Layer A (xviii): compact-interval covering of a
  path by chart regions, and the chart-chain construction**
  (`Submission/CompactCover.lean`, sorry-free, imported by
  Submission.lean).  `chartAtPoint h hgp z` (the bundled chart at a
  zero-set point, from `zeroSet1Chart_at_general_position`; `V_open`,
  `chartAtPoint_self`), `chartTimeSet` (the open set of times whose path
  point lies in the chart region of `σ t`; `isOpen_chartTimeSet`,
  `mem_chartTimeSet_self`), the compactness instance for
  `CompactInterval a b`, **`finite_chart_cover`**: a continuous path over
  `[a,b]` is covered by finitely many chart-time regions
  (`isCompact_univ.elim_finite_subcover`); `sortedCoverCharts` (the chart
  sigma-list ordered by time), `mem_sortedCoverCharts`,
  `finite_chart_cover_sorted` (every path point lies in some chart of the
  sorted list), and `chainFromList` (builds the `ChartChain` from an
  ordered list of charts).  The raw material of the Lebesgue-style
  refinement into the adapted chain that the `ChartChainLiftOnInterval`
  induction consumes.

* `CoverRefine.lean` — **Layer A (xix): refinement of a chart cover of a
  compact-interval path** (`Submission/CoverRefine.lean`, sorry-free,
  imported by Submission.lean).  `pathInChart σ g` (the open set of times
  whose path point lies in the region of cover chart `g`;
  `isOpen_pathInChart`), its ambient-open representative `coverOpenReal σ
  hσ g` (`isOpen_coverOpenReal`, `pathInChart_eq_coverOpenReal` — the
  chart-time set is the pullback of the representative along the interval
  inclusion), `mem_coverOpenReal_of_mem_pathInChart`, `real_chart_cover`
  (the real interval `[a,b]` is covered by the representatives of the
  cover charts), and **`chart_refinement`**: from a finite chart cover one
  gets `δ > 0` such that every subinterval of `[a,b]` of length at most
  `δ` lies entirely in the region of one chart of the cover (the path over
  the subinterval stays inside that chart region).  The proof applies the
  fleet's uniform-subdivision commons lemma
  (`Commons.Analysis.Real.open_cover_subdivision`) to the real
  representatives.  The uniform refinement from which the grid partition
  and the adapted chain are built.

* `GridPartition.lean` — **Layer A (xx): grid partition of a compact
  interval** (`Submission/GridPartition.lean`, sorry-free, imported by
  Submission.lean).  `exists_grid_step` (Archimedean: `∃ m > 0` with
  `(b−a)/m ≤ δ`), `gridPoint a b m i` (`pᵢ = a + i·(b−a)/m`),
  `gridPoint_mono`, `gridPoint_mem_Icc_left`/`_right` (grid points with
  `i ≤ m` lie in `[a,b]`), `gridPoint_step` (cell length is `(b−a)/m`),
  **`grid_partition`** (the grid lemma: cells lie in `[a,b]` and have
  length at most `δ`), and **`perCell_chart`**: from the uniform chart
  refinement, a cell count `m` such that every cell `[pᵢ, pᵢ₊₁]` lies
  entirely in the region of one cover chart — the raw material for the
  adapted chain (cell-to-chart assignment with junctions in the overlaps
  of consecutive regions).

* `AdaptedChain.lean` — **Layer A (xxi): the adapted chain of a
  compact-interval path** (`Submission/AdaptedChain.lean`, sorry-free,
  imported by Submission.lean).  `CellChartData σ` (the packaged per-cell
  data: cell count `m`, the cell charts `cell i`, and `cellRegion` — the
  path over cell `i` stays in the region of `cell i`), `cellChartData_of`
  (built from `perCell_chart` via `Classical.choice` of a `Nonempty` data
  instance — `rcases` of the Prop-exists would hit the elimination
  restriction), `adaptedCellCharts` (the ordered sigma list via
  `List.finRange`), `adaptedChartChain` (the `ChartChain` from the first
  cell chart over the tail through `chainFromList`),
  `cellBoundaryTime` (the time `pᵢ₊₁` inside the compact interval), and
  **`junction_cell_overlap`**: at every junction `pᵢ₊₁` (with `i+1 < m`)
  the path point lies in the regions of *both* consecutive cell charts —
  the right endpoint of cell `i` and the left endpoint of cell `i+1` —
  the local fact behind `chartParam_junction_agree` at every junction of
  the chain.  **Junction parameter agreement** (S52): `junctionTime`
  (the time `pᵢ₊₁`) and **`junction_param_agree`** — at each junction the
  parameter of `σ(pᵢ₊₁)` in the next cell's chart is exactly the
  transition-transport of its parameter in the current cell's chart
  (the instantiation of `chartParam_junction_agree` with the two
  memberships supplied by `junction_cell_overlap`).  **Piecewise
  parameter lift over the grid** (S53): `gridPoint_zero`/`gridPoint_last`
  (`p₀ = a`, `p_m = b`), the canonical per-cell lift `cellParam`
  (continuous on the cell: `continuous_cellParam_cell`; round trip:
  `cellParam_lift_roundTrip`), the **single-cell base case**
  `single_cell_grid_lift` (`m = 1`: a continuous whole-interval parameter
  lift round-tripping through the single cell chart), the **grid-lift
  statement** `GridLift` (per-cell continuous round-tripping lifts; junction
  coherence is the separate `junction_param_agree`), and
  `grid_lift_canonical` (the canonical per-cell lifts realise `GridLift`).
  **Canonical junction equality** (S54): `junctionTime_mem_Icc_left` /
  `junctionTime_mem_Icc_right` (the junction time lies in the intervals of
  cell `i` and cell `i+1` as right/left endpoint), `cellParam_point_mem_next`
  (the chart point of the cell-`i` parameter at the junction lies in the
  next cell's region — via the round trip + `junction_cell_overlap`), and
  **`cellParam_junction`**: at `pᵢ₊₁` the transition-transport of the
  cell-`i` parameter of `σ(pᵢ₊₁)` equals the cell-`(i+1)` parameter — both
  are `chartParam` of the same point in the same next-cell chart, so the
  equality is `chartParam_junction_agree` (named `a b` arguments resolve
  the implicit interval parameters).  **Whole-grid lift: cell selection and
  junction well-definedness** (S55): `exists_cell_upper` (the last cell
  always contains `x` on its right — its right endpoint is `b`),
  `cellIndexOf` (the deterministic leftmost cell containing `x`),
  `cellIndexOf_lt` / `cellIndexOf_le_right`, **`JunctionCoherent`** (the
  junction well-definedness statement: at each `pᵢ₊₁` the transition of
  the left cell's lift value is the right cell's lift value) and
  **`junction_coherent`** (packaging `cellParam_junction`).
  **Certified cell membership** (S56): **`cellIndexOf_ge_left`** — the
  selected cell contains `x` on its left (`pᵢ ≤ x`), from the minimality
  of `Nat.find` (`Nat.find_min`: no cell to the left of `i` reaches `x`;
  base case `p₀ = a ≤ x`).  Together with `cellIndexOf_le_right`, the
  selected cell is fully certified as a genuine containing cell of `x`
  (`cellIndexOf_mem`: `pᵢ ≤ x ≤ pᵢ₊₁`), and **`wholeGridParam`** — the
  whole-grid lift value `x ↦ cellParam … (cellIndexOf …)` with the
  certified cell membership — is defined on all of `[a,b]` (now ℝ-valued:
  the per-cell parameters live in different chart intervals, so the
  whole-grid lift reads them as reals).  **Open-cell continuity** (S57):
  `cellIndexOf_of_Ioo` (on the interior of cell `i` the selector picks
  `i` — minimality of the `Nat.find`; on the open cell `pᵢ < x` rules out
  all cells left of `i`), `cell_eq_of_fin_eq` (same index, different
  proofs → same chart), `chartParam_val_eq_of_sigma_eq` (equal bundled
  charts give equal real parameter values — memberships proof-irrelevant
  after the substitution), `cellParam_val_eq_of_nat_index` (per-cell lift
  real values are insensitive to the index proof), and
  **`wholeGridParam_val_eq_cellParam`** + **`continuous_wholeGridParam_on_open_cell`**:
  on the open cell the whole-grid lift coincides with — and hence inherits
  the continuity of — the per-cell lift of cell `i` (open cell
  continuously included into the closed cell; pointwise equality via the
  value lemma).

* `TorusChartHomeo.lean` — **Layer A (xiv): chart homeomorphisms — the
  trisecant zero set is covered by honest 1-dimensional charts**
  (`Submission/TorusChartHomeo.lean`, sorry-free, imported by
  Submission.lean).  The open-trace identity
  `RealGraphArc.zeroSet_trace_open`: for any parameter interval
  `J ⊆ (a,b)` the quotient curve images exactly the zero set over `J` —
  `γ '' J = trisecantZeroSet r ∩ torusQuotient '' (chartWindow d J)`
  (forward: `(B (γ x)).1 = x` and `B (γ x) = (x,ψ x) ∈ W`; backward: the
  graph-arc covering property puts every zero over `J` on the graph at
  parameter `(B w).1`).  The **generic chart homeo theorem**
  `torus_chart_homeo`: for a graph arc and an interval `(lo,hi) ⊆ (a,b)`
  on which the quotient curve is injective, there is an open torus
  neighbourhood `V` (the window over `(lo,hi)`) and a homeomorphism
  `(lo,hi) ≃ₜ {q | q ∈ trisecantZeroSet r ∧ q ∈ V}` tracing `π₃ ∘ d.g` —
  the inverse continuity (not automatic for injective continuous interval
  maps!) comes from the open-map property supplied by the trace identity
  (`IsHomeomorph` route: continuous + bijective + open, assembled by
  `Equiv.ofBijective` + `toHomeomorphOfContinuousOpen`).  Per-witness
  homeo theorems `torus_chart_homeo_AB/AM/BM` give the homeo with the base
  point `m/b/a ↦ torusQuotient (a,(b,m))` and the membership facts for the
  base point in the zero set and in `V`.  This is the honest local chart
  structure (every point of the zero set has a neighbourhood homeomorphic
  to an open interval) on which the component/1-manifold analysis of the
  zero set rests.

* `TorusAtlas.lean` — **Layer A (xiii): the atlas of the trisecant zero
  set — honest charts, cover, overlap** (`Submission/TorusAtlas.lean`,
  sorry-free, imported by Submission.lean).  The bundled chart record
  `ZeroSetChart r p` (`V` open ∋ `p`, base parameter `x₀ ∈ (lo,hi)`, `γ`
  continuous injective on `(lo,hi)`, `γ x₀ = p`, and the chart identity
  `image_eq : γ '' (lo,hi) = trisecantZeroSet r ∩ V`) wraps a
  `torus_chart_lift_*` chart (`zeroSetChart_of_lift`).  Per-witness covers
  `zeroSetChart_cover_AB/AM/BM` assemble a chart from each splitting
  instance plus `RealGraphArc.exists_small_delta`; the **atlas/cover
  theorem** `zeroSetChart_at_general_position`: under
  `TorusGeneralPosition r` every `p ∈ trisecantZeroSet r` carries a
  `ZeroSetChart r p` (dispatch over the rank-two witness by `fin_cases`,
  mapped to `(A,B)`/`(A,M)`/`(B,M)` with `linearIndependent_pair_swap_iff`,
  mirroring `smooth_local_curve_of_general_position`).  Overlap
  compatibility `zeroSetChart_overlap` / `zeroSetChart_agree_on_overlap`:
  two charts at the same base point agree on `W = V₁ ∩ V₂`, both tracing
  exactly `trisecantZeroSet r ∩ W`.  The component/1-manifold statement is
  the next gluing stage built on cover + overlap.

The deep layers (1)–(3) require building, from scratch, a substantial theory
of secants/trisecants of smooth closed curves, 1-manifold structure theory,
the homological argument on the Möbius strip of chords, and the
Dehn-lemma/Alexander-trick bridge from spanning disks to isotopies — several
stages of a long research-level formalization; the theorem below is the
assembly point for those stages.
-/

namespace Submission

open LeanEval.KnotTheory.Quadrisecant

theorem smooth_knot_has_quadrisecant {r : ℝ → Space} (_hknot : IsSmoothKnot r)
    (_hnontrivial : ¬ IsUnknotted r) : HasQuadrisecant r :=
  Work.Drive.quadrisecant_of_genericCase_fullK_noHgen Work.Drive.genericFullFiniteDenseK
    Work.Drive.spreadQuadrisecantFullCloseK_of_OFatS r _hknot _hnontrivial

end Submission
