/-
  Subproject WilE9G — ambient (Gabrielov–Vorobjov) strata, in the form in which G1 is stated.

  The frozen `E5_strat` is stated for `Stratum p q` with ambient dimension `p + q`; at `p = 0` it
  gives the *ambient* stratification of a semi-Pfaffian set: strata cut out by `j` equations whose
  Jacobian has rank `j` on the whole ambient space, with `X.set` locally equal to the zero set of
  the equations (`Stratum.good_zero_ambient`).

  `AmbStratum N` is the same object with the ambient dimension `N` written directly (no `0 + N`),
  which is what the statements of G1/G3 use.  The dictionary with `Stratum 0 N` is
  `Work.WilE9G.Amb.ofStratum` (a delegated lemma).
-/
import Submission.Work.WilE9G.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G
open WilkiesDesign WilkiesDesign.E Work.WilE9.Sharp

/-- An ambient effectively smooth stratum in `ℝ^N`: an EA semi-Pfaffian set `X` together with
`j` equations `h`, whose `Good` predicate (below) requires the equations to vanish on `X.set`,
their Jacobian to have rank `j`, and `X.set` to be *ambiently* locally equal to the zero set of
the equations. -/
structure AmbStratum (N : ℕ) where
  X : SemiPf N
  j : ℕ
  h : Fin j → EAPoly N X.r

/-- The degree budget of an ambient stratum. -/
def AmbStratum.deg {N : ℕ} (S : AmbStratum N) : ℕ := S.X.deg + ∑ a, atomDeg (S.h a)

/-- **Gabrielov–Vorobjov effective smoothness**: at every point of `X.set` the equations vanish,
their Jacobian (a `j × N` matrix) has rank `j`, and `X.set` is ambiently locally the zero set of
the equations. -/
def AmbStratum.Good {N : ℕ} (S : AmbStratum N) : Prop :=
  ∀ z ∈ S.X.set,
    (∀ a, eaEval S.X.c (S.h a) z = 0) ∧
    (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
      eaEval S.X.c (eaD S.X.c l (S.h a)) z).rank = S.j ∧
    (∀ᶠ z' in 𝓝 z, (∀ a, eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set)

/-- The projection of the ambient space to its first ``n`` coordinates (for ``n`` at most the ambient dimension). -/
def projBase {N : ℕ} {n : ℕ} (hn : n ≤ N) (z : Fin N → ℝ) : Fin n → ℝ :=
  fun i => z (Fin.castLE hn i)

/-- **Base-submersivity along the stratum.**  `S.IsBaseSubmersiveAt n z` says that the projection
to the first `n` coordinates is surjective when restricted to the tangent space of the stratum at
`z` — equivalently, that `z` is *not* a critical point of the base projection `π_n|S`.  Together
with `Good` (which makes `dh(z)` surjective) this says that `(π_n, h) : ℝ^N → ℝ^n × ℝ^{S.j}` is
surjective at `z`, which by the implicit function theorem makes the fibres of the stratum over
`π_n z` submanifolds of dimension `N - S.j - n`. -/
def AmbStratum.IsBaseSubmersiveAt {N : ℕ} (S : AmbStratum N) {n : ℕ} (hn : n ≤ N)
    (z : Fin N → ℝ) : Prop :=
  ∀ w : Fin n → ℝ, ∃ v : Fin N → ℝ, projBase hn v = w ∧
    ∀ a, fderiv ℝ (fun z' : Fin N → ℝ => eaEval S.X.c (S.h a) z') z v = 0

/-- The matrix form of the differential of the equations at `z`. -/
def AmbStratum.jac {N : ℕ} (S : AmbStratum N) (z : Fin N → ℝ) : Matrix (Fin S.j) (Fin N) ℝ :=
  Matrix.of fun a l => (fderiv ℝ (fun z' : Fin N → ℝ => eaEval S.X.c (S.h a) z') z) (Pi.single l 1)

/-! ## The same notions for the frozen ambient strata `Stratum 0 q` -/

/-- The base projection of the ambient space `Fin (0 + q) → ℝ` of a `Stratum 0 q` to its
first `n` coordinates (for `n ≤ q`). -/
def projBase0 {q : ℕ} {n : ℕ} (hn : n ≤ q) (z : Fin (0 + q) → ℝ) : Fin n → ℝ :=
  fun i => z (Fin.cast (Nat.zero_add q).symm (Fin.castLE hn i))

/-- Base-submersivity along a frozen ambient stratum `S : Stratum 0 q`. -/
def Stratum.IsBaseSubmersiveAt {q : ℕ} (S : Stratum 0 q) {n : ℕ} (hn : n ≤ q)
    (z : Fin (0 + q) → ℝ) : Prop :=
  ∀ w : Fin n → ℝ, ∃ v : Fin (0 + q) → ℝ, projBase0 hn v = w ∧
    ∀ a, fderiv ℝ (fun z' : Fin (0 + q) → ℝ => eaEval S.X.c (S.h a) z') z v = 0

/-! ## Elementary API -/

theorem AmbStratum_eq_zero {N : ℕ} (S : AmbStratum N) (hS : S.Good) {z : Fin N → ℝ}
    (hz : z ∈ S.X.set) : ∀ a, eaEval S.X.c (S.h a) z = 0 := (hS z hz).1

theorem AmbStratum_rank {N : ℕ} (S : AmbStratum N) (hS : S.Good) {z : Fin N → ℝ}
    (hz : z ∈ S.X.set) :
    (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
      eaEval S.X.c (eaD S.X.c l (S.h a)) z).rank = S.j := (hS z hz).2.1

theorem AmbStratum_locality {N : ℕ} (S : AmbStratum N) (hS : S.Good) {z : Fin N → ℝ}
    (hz : z ∈ S.X.set) :
    ∀ᶠ z' in 𝓝 z, (∀ a, eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set := (hS z hz).2.2

theorem AmbStratum.set_subset_cubeC {N : ℕ} (S : AmbStratum N) : S.X.set ⊆ cubeC N :=
  SemiPf_set_subset_cubeC S.X

theorem AmbStratum.isCompact_closure {N : ℕ} (S : AmbStratum N) :
    IsCompact (closure S.X.set) := SemiPf_isCompact_closure S.X

/-- A stratum point lies in the image of the base projection (trivially). -/
theorem AmbStratum.projBase_mem_image {N : ℕ} (S : AmbStratum N) {n : ℕ} (hn : n ≤ N)
    {z : Fin N → ℝ} (hz : z ∈ S.X.set) : projBase hn z ∈ projBase hn '' S.X.set := ⟨z, hz, rfl⟩

end Work.WilE9G
