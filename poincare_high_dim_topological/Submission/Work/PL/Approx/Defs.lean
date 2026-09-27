import Mathlib
import Submission.Work.PL.Defs

/-!
# PL approximation in a cube (area A5, `Submission.Work.PL.Approx`)

This file fixes the vocabulary of area A5 of `Submission/Work/NOTES_LEAD_poincare_blueprint.md`
(item G5 `pl_approx` plus its frozen variant).  Nothing here depends on a particular subdivision
operator: `Subdiv` is the interface through which area A2 (barycentric subdivision `Cx.sd`) is
plugged in, exactly as the blueprint allows hypotheses on other areas to be carried as explicit
holders.

* `clamp`, `seg`, `cubeCut` -- the cutoff construction of G5 (product of one-dimensional cutoffs,
  no coning).
* `Subdiv`, `Subdiv.iter` -- a subdivision operator with mesh tending to `0`.
* `RestrictsTo` -- the compatibility of a subdivision with a subcomplex (needed for the frozen
  variant).

All results about these notions live in the other files of `Submission/Work/PL/Approx/`.
-/

open Set Metric
open scoped BigOperators

namespace Work.PL.Approx

noncomputable section

/-! ## The cutoff -/

/-- `clamp a b x` clamps `x` to the interval `[a,b]`. -/
def clamp (a b x : ℝ) : ℝ := max a (min b x)

/-- One-dimensional cutoff: `seg a b u = 1` for `|u| ≤ a`, `seg a b u = 0` for `b ≤ |u|`,
and affine in `|u|` in between (for `a < b`). -/
def seg (a b u : ℝ) : ℝ := clamp 0 1 ((b - |u|) / (b - a))

/-- The cutoff of G5: a continuous function which is `1` on `closedCube a` and `0` outside
`closedCube b` (for `a < b`).  It is a product of the one-dimensional cutoffs `seg a b`. -/
def cubeCut {n : ℕ} (a b : ℝ) (x : PL.E n) : ℝ := ∏ i : Fin n, seg a b (x i)

/-! ## A subdivision operator

`Subdiv N` is the interface used by this area in place of the barycentric subdivision `Cx.sd`
of area A2 (which is not available here).  An element of `Subdiv N` is a subdivision operation
on complexes in `ℝᴺ` whose iterates subdivide and have arbitrarily small mesh. -/

/-- `iterAux sd fin r F` is the `r`-fold subdivision of the finite complex `F`. -/
def iterAux {N : ℕ} (sd : (K : PL.Cx N) → K.faces.Finite → PL.Cx N)
    (fin : ∀ (K : PL.Cx N) (hK : K.faces.Finite), (sd K hK).faces.Finite) :
    ℕ → PL.FinCx N → PL.FinCx N :=
  fun r F => Nat.rec F (fun _ G => ⟨sd G.1 G.2, fin G.1 G.2⟩) r

/-- The `r`-fold subdivision of `K`. -/
def iterAuxK {N : ℕ} (sd : (K : PL.Cx N) → K.faces.Finite → PL.Cx N)
    (fin : ∀ (K : PL.Cx N) (hK : K.faces.Finite), (sd K hK).faces.Finite)
    (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite) : PL.Cx N :=
  (iterAux sd fin r ⟨K, hK⟩).1

/-- The `r`-fold subdivision is finite. -/
theorem iterAuxK_fin {N : ℕ} (sd : (K : PL.Cx N) → K.faces.Finite → PL.Cx N)
    (fin : ∀ (K : PL.Cx N) (hK : K.faces.Finite), (sd K hK).faces.Finite)
    (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite) : (iterAuxK sd fin r K hK).faces.Finite :=
  (iterAux sd fin r ⟨K, hK⟩).2

@[simp]
theorem iterAuxK_zero {N : ℕ} (sd : (K : PL.Cx N) → K.faces.Finite → PL.Cx N)
    (fin : ∀ (K : PL.Cx N) (hK : K.faces.Finite), (sd K hK).faces.Finite)
    (K : PL.Cx N) (hK : K.faces.Finite) : iterAuxK sd fin 0 K hK = K := rfl

theorem iterAuxK_succ {N : ℕ} (sd : (K : PL.Cx N) → K.faces.Finite → PL.Cx N)
    (fin : ∀ (K : PL.Cx N) (hK : K.faces.Finite), (sd K hK).faces.Finite)
    (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite) :
    iterAuxK sd fin (r + 1) K hK = sd (iterAuxK sd fin r K hK) (iterAuxK_fin sd fin r K hK) := rfl

/-- A subdivision operation on geometric complexes in `ℝᴺ` whose iterates have arbitrarily small
mesh.  This is the holder for area A2's `Cx.sd`; see the blueprint §5 A5. -/
structure Subdiv (N : ℕ) where
  /-- The subdivision of a finite complex. -/
  sd : (K : PL.Cx N) → K.faces.Finite → PL.Cx N
  /-- Subdivisions of finite complexes are finite. -/
  fin : ∀ (K : PL.Cx N) (hK : K.faces.Finite), (sd K hK).faces.Finite
  /-- The subdivision subdivides. -/
  subdivides : ∀ (K : PL.Cx N) (hK : K.faces.Finite), PL.Subdivides (sd K hK) K
  /-- Iterated subdivisions have arbitrarily small mesh. -/
  mesh : ∀ (K : PL.Cx N) (hK : K.faces.Finite) (δ : ℝ), 0 < δ →
    ∃ r : ℕ, PL.MeshLT (iterAuxK sd fin r K hK) δ

namespace Subdiv

variable {N : ℕ} (S : Subdiv N)

/-- The `r`-fold subdivision of `K` using `S`. -/
def iter (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite) : PL.Cx N :=
  iterAuxK S.sd S.fin r K hK

/-- The `r`-fold subdivision is finite. -/
theorem iter_fin (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite) : (S.iter r K hK).faces.Finite :=
  iterAuxK_fin S.sd S.fin r K hK

@[simp]
theorem iter_zero' (K : PL.Cx N) (hK : K.faces.Finite) : S.iter 0 K hK = K := rfl

theorem iter_succ' (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite) :
    S.iter (r + 1) K hK = S.sd (S.iter r K hK) (S.iter_fin r K hK) := rfl

/-- Every face of the `r`-fold subdivision of `K` is contained in a simplex of `K`. -/
theorem iter_simplex_subset (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite) (s' : Finset (PL.E N))
    (hs' : s' ∈ (S.iter r K hK).faces) : ∃ s ∈ K.faces, PL.simp s' ⊆ PL.simp s := by
  induction r generalizing s' with
  | zero => exact ⟨s', hs', Subset.rfl⟩
  | succ r ih =>
    rw [iter_succ'] at hs'
    obtain ⟨s, hs, hsub⟩ := (S.subdivides (S.iter r K hK) (S.iter_fin r K hK)).2 s' hs'
    obtain ⟨t, ht, hts⟩ := ih s hs
    exact ⟨t, ht, hsub.trans hts⟩

/-- The `r`-fold subdivision of `K` subdivides `K`. -/
theorem iter_subdivides (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite) :
    PL.Subdivides (S.iter r K hK) K := by
  refine ⟨?_, ?_⟩
  · induction r with
    | zero => rfl
    | succ r ih =>
      rw [iter_succ']
      exact (S.subdivides _ _).1.trans ih
  · exact fun s' hs' => S.iter_simplex_subset r K hK s' hs'

/-- The `r`-fold subdivision of `K` has the same underlying space as `K`. -/
theorem iter_space (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite) :
    (S.iter r K hK).space = K.space :=
  (S.iter_subdivides r K hK).1

end Subdiv

/-! ## The frozen part of a simplex -/

/-- The vertices of `s` that lie in `L.space`. -/
def frozenPart {N : ℕ} (L : PL.Cx N) (s : Finset (PL.E N)) : Finset (PL.E N) := by
  classical
  exact s.filter fun v => v ∈ L.space

/-! ## Compatibility of a subdivision with a subcomplex -/

/-- `RestrictsTo S K hK L` says that the subdivision `S` of `K` behaves well with respect to the
subcomplex `L` (of `K`): every face of every iterate meets `L.space` in the face spanned by its
vertices lying in `L.space`, and those vertices lie in a single face of `L`.  This is the
hypothesis under which the frozen variant of `pl_approx` freezes `L` pointwise.

**This hypothesis is *not* automatic, and not every subcomplex satisfies it.**  Already for the
unsubdivided complex (`r = 0`) it can fail: let `K` be the complex on the two points `0` and `1`
of `E 1` with faces `{0}`, `{1}`, `{0,1}`, and let `L` be the subcomplex with faces `{0}`, `{1}`
(so `L.space = {0,1}`).  For the face `s = {0,1}` all vertices lie in `L.space`, so
`simp (frozenPart L s) = simp s` is the whole segment, whereas `simp s ∩ L.space = {0,1}`.  So
`RestrictsTo` is a genuine geometric condition on the pair `(K, L)`: for the barycentric
subdivision it holds precisely when no subdivided simplex crosses from one face of `L` to
another (which is the case for `L` a union of faces of the subdivision itself, or when the
intersections `simp s ∩ L.space` happen to be faces of the `s` that carry `f`'s linearity).

The frozen variants `pl_approx_frozen_faces` and `pl_approx_frozen_sub` (and the Subdiv form
`pl_approx_frozen_at`) avoid this hypothesis altogether: there the frozen datum is a subcomplex
of the *fine* complex `K'` (or a finite list of its faces), which is the form in which the
engulfing argument produces frozen pieces.  Use `Sd/exists_frozen_faces` to turn a subcomplex
`L ⊆ K` into such a datum for the concrete barycentric subdivision `sdSubdiv`. -/
def RestrictsTo {N : ℕ} (S : Subdiv N) (K : PL.Cx N) (hK : K.faces.Finite) (L : PL.Cx N) : Prop :=
  ((∀ (r : ℕ) (s : Finset (PL.E N)), s ∈ (S.iter r K hK).faces →
      PL.simp s ∩ L.space = PL.simp (frozenPart L s)) ∧
    (∀ (r : ℕ) (s : Finset (PL.E N)), s ∈ (S.iter r K hK).faces →
      (∃ v ∈ s, v ∈ L.space) → ∃ ρ ∈ L.faces, ∀ v ∈ s, v ∈ L.space → v ∈ PL.simp ρ))

end

end Work.PL.Approx
