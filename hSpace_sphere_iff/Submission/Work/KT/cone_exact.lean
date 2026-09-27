import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.Cone.Setup
import Submission.Work.KT.Cone.Assembly
import Submission.Work.KT.Cone.stable_lift

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/KT/DESIGN.md (the lead's design for the odd case: Adams–Atiyah via K₀ of rings of continuous functions, ψ² and ψ³ from symmetric-power eigenspaces, Bott periodicity via Atiyah–Bott clutching). Shared definitions: Submission/Work/KT/Defs.lean (do NOT edit). CONVENTION: use [Ring A] plus an explicit commutativity hypothesis, never [CommRing A] on subalgebras (unification timeouts). Siblings run in parallel.

# Node `cone_exact`

**Statement** (`cone_exact.lean`, harness format; imports: `Submission.Work.KT.Defs`; namespace `Work.KT`):

`K`-theory of the mapping cone `C_f`, `f : S_V → T`: exactness of `K̃(C_f/T) → K̃(C_f) → K(T)`, extension of classes whose pull-back along `f` is trivial, and injectivity of `K̃(C_f/T) → K(C_f)` when `K¹(T)` is trivial.

**Route.**  `A = coneAlg f = C(C_f)` is the pull-back `C(T) ×_{C(S_V)} C(D_V)`, and
`U = ℂ·1 + ker (coneToT f)` is the range of `relToCone f y0 hy0`, isomorphic to `Kpair V` via
`Cone.sigma`.  The three assertions are obtained from the three parts of `Work.KT.k0_exact`
instantiated at this Milnor square (`Cone.cone_exact_mid`, `Cone.cone_exact_lift`,
`Cone.cone_exact_inj`); the stable lifting hypothesis of `k0_exact` (2) is supplied by
`Cone.stable_lift`, which converts `GLStablyTrivial T` into the lifting of invertible matrices
over `C(T)` along `coneToT f` by the radial extension of the homotopy that `GLStablyTrivial T`
provides.
-/

namespace Work.KT

open Work.KT.Cone

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {T : Type} [TopologicalSpace T] [CompactSpace T] [T2Space T] [Nonempty T]

/-- `K`-theory of the mapping cone `C_f`, `f : S_V → T`: exactness of
`K̃(C_f/T) → K̃(C_f) → K(T)`, extension of classes whose pull-back along `f` is trivial, and
injectivity of `K̃(C_f/T) → K(C_f)` when `K¹(T)` is trivial. -/
theorem cone_exact (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : Type) [TopologicalSpace T] [CompactSpace T] [T2Space T] [Nonempty T]
    (f : C(Sph V, T)) (y0 : Ball V) (hy0 : y0 ∈ bdry V) :
    (∀ z : K0 (coneAlg f), K0.mapA (coneToT f) z = 0 →
      ∃ w, K0.mapA (augPair V y0) w = 0 ∧ K0.mapA (relToCone f y0 hy0) w = z) ∧
    (∀ (z : K0 C(T, ℂ)) (c : K0 ℂ),
      K0.mapA (pullAlg f) z = K0.mapA (Algebra.ofId ℂ C(Sph V, ℂ)) c →
        ∃ a, K0.mapA (coneToT f) a = z) ∧
    (GLStablyTrivial T → ∀ w, K0.mapA (augPair V y0) w = 0 →
      K0.mapA (relToCone f y0 hy0) w = 0 → w = 0) := by
  have hT : Nonempty T := inferInstance
  obtain ⟨t0⟩ := hT
  refine ⟨cone_exact_mid f y0 hy0 t0, cone_exact_lift f, ?_⟩
  intro hgl
  exact cone_exact_inj f y0 hy0 t0 (stable_lift V T f hgl)

end

end Work.KT
