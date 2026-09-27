import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.LevelData
import Submission.Work.Drive.N2.levelEmbeddingAssembly
import Submission.Work.Drive.N2.finite_critical_set
import Submission.Work.Drive.N2.mobiusRealModel
-- The certified-window endgame of the compact `n = 2` case, through the *proved* assembly of the
-- certified saddle window from the one-component core and the pin dichotomy
-- (`Work.Drive.N2C.certifiedWindowSaddle_of_core`, `N2C/d2AssemblyAuto.lean`).  Routing the target
-- directly through it (instead of through `Work.Drive.N2.levelSeparatingMap`, whose wiring consumes
-- the *holder* `Work.N2C.exists_certifiedWindow_saddle`) makes the target's dependency cone contain
-- exactly the two genuine remaining obligations of the compact case, the core
-- `Work.Drive.N2Lead.exists_certifiedWindow_saddle_oneComp` and the dichotomy
-- `Work.Drive.N2Lead.saddlePin_oneComp_or`, and no wiring stub.
import Submission.Work.Drive.N2C.certifiedWindowAssembly
import Submission.Work.N2C.exists_certifiedWindow_extremum
-- H8 (this lane): the target now runs through an INDEPENDENT copy of the Möbius chain
-- (`Submission/Work/Drive/N2/MobiusChainX.lean` + `MobiusChainInstantiate.lean`), which is
-- parameterised by the lane's single core-rows lemma `Work.Drive.N2C.mfrCoreRows`.  This makes the
-- target's build independent of the lane's wiring (`N2C/d2Assembly*`, whose consumer
-- `mobiusUpperStarRowsOfShape` currently does not elaborate) while keeping exactly the same single
-- mathematical input.
import Submission.Work.Drive.N2.MobiusChainInstantiate

open scoped Manifold ContDiff

/-! Guidance from the project lead (the requester):

# Guidance (project lead) — embedding_of_morse_movie (the MOVIE construction)
WHY: compact n = 2 (every compact surface embeds in ℝ⁴) is the last of the three inputs of Whitney's strong
embedding theorem. The lead chose MORSE THEORY. The vocabulary is `Submission/Work/Drive/Morse.lean`: `IsCritical`,
`NondegCrit`, `IsMorseDistinct`, `HasLevelFlow`, `MorseLemma2`. Other agents prove the other pieces in parallel:
existence of Morse functions, the level flow, the planar Morse lemma, and the embedding from these. Every piece
consumes the others ONLY through those definitions, so do not change them. If one is unusable or false for your
purpose, stop and say so precisely with `declare_false`.
A second agent proves the SAME statement by a different route (classification + connected sums). Both routes
are legitimate; do not coordinate, just finish.

The idea is a level-preserving embedding, e = (g, f) : M → ℝ³ × ℝ = ℝ⁴.
- e is injective iff g is injective on each level set f⁻¹(c).
- e is an immersion iff dg is injective on ker df at regular points and dg is injective at critical points.
- M is compact, so an injective immersion is an embedding. The workspace has
  `Work.Whitney.isEmbedding_of_injective_of_compactSpace`.
So you construct a "movie" of embedded 1-manifolds (links) in ℝ³ that changes by births, deaths and saddle bands.

1. Critical values c_1 < … < c_k. Regular values a_0 < c_1 < a_1 < … < c_k < a_k.
2. By `hflow`, over each regular interval the level flow identifies f⁻¹(I) with (level set) × I, preserving f.
   The level set f⁻¹(a_i) is a compact 1-manifold, hence a finite union of circles. The 1-dimensional
   classification in Submission/Work/OneDim (`classify_connected_one_manifold`) is PROVED. It needs the level
   set as a manifold: implicit function theorem, or parametrise by flow lines of a vector field TANGENT to the
   levels.
3. Standard position: at each regular value a_i, g maps the m circles of f⁻¹(a_i) to m round, pairwise
   unlinked circles in the plane z = 0 of ℝ³ (for example centres (3j, 0, 0), radius 1), through a
   diffeomorphism to Fin m × S¹. Over a regular interval, use the flow to transport this: g is constant along
   flow lines, up to the chosen identifications.
4. Near each critical point, use `hmorse` (in a chart) to get f = c ± u² ± v². Local models:
   - index 0 (minimum, f = c + u² + v²): a small round circle is born at a far-away spot of the plane,
     g = (u, v, 0) + offset;
   - index 2 (maximum): a circle dies;
   - index 1 (saddle, u² − v²): two arcs of the link are joined by a band. Take g(u, v) = (u, v, 0) in the
     model. The two sheets of the level set near the saddle are the branches of the hyperbola u² − v² = s.
     Around the model disc, move the attached arcs of the standard circles into position by a
     level-preserving isotopy (this is "g depends on the level").
5. After each critical level, return the new link to standard position by an explicit isotopy, done as a
   function of the level. After a saddle the link is again an unlink, because the band is chosen planar or with
   a single half twist. Twisted bands, which come from non-orientability, need a half-twist in ℝ³; an unlink
   stays an unlink.
Delegate the self-contained pieces as lemmas with EXACT statements: "round circles in the plane under a
level-dependent smooth isotopy", "the saddle model", "injective immersion from level data".
-/

namespace Work.Drive.N2

/- NOTE (session of 2026-09-25, agent H8): the route to `Work.Drive.N2.levelSeparatingMap` that this
file reduces the target to is analysed in
`Submission/Work/Drive/N2/NOTES_S_H8_level_dependent_picture_FIX.md`.  It shows that a *level
independent* transport picture cannot be glued to a chart model around a critical point (the model is
constant along the flow lines only on the collar, and the collar does not surround the critical
point), and that the fix is a picture depending on the level, `A (f x) (T x)`, for which the
transport formula *equals* the chart model on the chart by construction.  The bricks of that route
that are on disk: `Work.Drive.N2.crossingTransportDrawingAt` (PROVED, the localised transport
engine) and `Work.Drive.N2.level_mono_of_modelAdaptedFlow` (delegated: the `hmono` of the
model-adapted flow). -/

open scoped Manifold ContDiff in
open Work.Drive.Morse in
/-- **The transport of a level flow is injective on level sets.**

This is the first geometric ingredient of the MOVIE construction: for a level flow `Φ` over `[a,b]`
(no critical values in `[a,b]`), two points `x, y` with the same value `f x = f y ∈ [a,b]` whose
transports `Φ (t, x)`, `Φ (t, y)` (with the value `f x + t` still in `[a,b]`) coincide must be equal.
Building a map `g` that is constant along the flow lines therefore automatically gives a map whose
restriction to every level set is injective, as soon as it separates the points of a single level. -/
theorem HasLevelFlow.transport_injective {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (f : M → ℝ) {a b : ℝ} (h : HasLevelFlow f a b) :
    ∃ Φ : ℝ × M → M,
      (∀ x : M, Φ (0, x) = x) ∧
      ∀ x y : M, ∀ t : ℝ, f x = f y → f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b →
        Φ (t, x) = Φ (t, y) → x = y := by
  obtain ⟨Φ, -, h0, hflow, hcomp⟩ := h
  refine ⟨Φ, h0, ?_⟩
  intro x y t hxy hx hxt hEq
  have hy : f y ∈ Set.Icc a b := hxy ▸ hx
  have key : ∀ z : M, f z ∈ Set.Icc a b → f z + t ∈ Set.Icc a b → Φ (-t, Φ (t, z)) = z := by
    intro z hz hzt
    calc Φ (-t, Φ (t, z)) = Φ (-t + t, z) := hcomp z (-t) t hz hzt (by simpa using hz)
      _ = Φ (0, z) := by rw [neg_add_cancel]
      _ = z := h0 z
  rw [← key x hx hxt, ← key y hy (hxy ▸ hxt), hEq]

end Work.Drive.N2

namespace Work.Drive.N2

open scoped Manifold ContDiff in
/-- **The target, reduced to its single remaining obligation.**

If the MOVIE construction produces level embedding data for `f` (a smooth `g : M → ℝ³` separating
the points of every level set of `f` with `ker dg ∩ ker df = 0`, see
`Work.Drive.N2.HasLevelEmbedding`), then the conclusion of `embedding_of_morse_movie` follows.  This
is the "injective immersion from level data" step of the plan; the existence of the level data is
the geometric content of the movie (see `NOTES_movie_route_analysis.md`). -/
theorem embedding_of_morse_movie_of_levelData {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : Work.Drive.Morse.IsMorseDistinct f) (hmorse : Work.Drive.Morse.MorseLemma2)
    (D : HasLevelEmbedding f) :
    ∃ e : M → EuclideanSpace ℝ (Fin 4), ContMDiff (𝓡 2) (𝓡 4) ∞ e ∧ Topology.IsEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 2) (𝓡 4) e x) :=
  levelEmbeddingAssembly f hf.1 D

end Work.Drive.N2

namespace Work.Drive.N2

open scoped Manifold ContDiff in
open Work.Drive.Morse in
/-- A compact surface with a Morse function (distinct critical values) embeds in ℝ⁴, given smooth level flows over
critical-point-free intervals and the planar Morse lemma. -/
theorem embedding_of_morse_movie {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : IsMorseDistinct f)
    (hflow : ∀ a b : ℝ, (∀ x, f x ∈ Set.Icc a b → ¬ IsCritical f x) → HasLevelFlow f a b)
    (hmorse : MorseLemma2) :
    ∃ e : M → EuclideanSpace ℝ (Fin 4), ContMDiff (𝓡 2) (𝓡 4) ∞ e ∧ Topology.IsEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 2) (𝓡 4) e x) := by
  -- The geometric heart (the MOVIE construction) is the block-cover endgame
  -- `Work.Drive.N2C.exists_levelSeparatingMap_of_certifiedCases`, whose two inputs are the certified
  -- windows at the extrema (`Work.N2C.exists_certifiedWindow_extremum`, proved) and at the saddles
  -- (`Work.Drive.N2C.certifiedWindowSaddle_of_core`, the proved assembly
  -- `core + pin dichotomy + the negation transfers`, `N2C/d2AssemblyAuto.lean`).  The rest of the
  -- proof is the assembly `levelEmbeddingAssembly`.
  obtain ⟨g, hg, himm, hinj⟩ :=
    Work.Drive.N2C.exists_levelSeparatingMap_of_certifiedCases f hf hmorse
      (fun p D h => Work.N2C.exists_certifiedWindow_extremum hf D h)
      (fun p D h => Work.Drive.N2.MfrX.certifiedWindowSaddle_of_coreX
        Work.Drive.N2.MfrX.coreRowsLane hf D h hmorse)
  exact levelEmbeddingAssembly f hf.1 ⟨g, hg, hinj, fun x v hv1 hv2 => himm x v hv2 hv1⟩

end Work.Drive.N2
