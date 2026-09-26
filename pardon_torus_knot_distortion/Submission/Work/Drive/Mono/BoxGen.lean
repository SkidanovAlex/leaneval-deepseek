import Mathlib
import Submission.Work.Smooth.OneManifold.ae_unconditional
import Submission.Work.Smooth.BoxGeneric.AeVertex
import Submission.Work.Drive.Mono.AESweep

/-!
# `BoxGen`: the general position of the box sphere at a *fixed* level

The trace of a level of the tilted sweep has a junction at every point of the surface which lies on
the **box sphere** `{y | boxNorm c σ y = s}` and in the slab; the local models of the trace at those
junctions (`Work.Drive.Mono.isLocallyEuclidean_trace_of_wallSphereJunction`,
`..._sphereFaceJunction`) need the box sphere to be in **general position** with respect to the
surface *at the given level* `s`.  That genericity is not automatic for an arbitrary level `s`
(a *graze* — the surface tangent to the box sphere — is possible, and at a graze the trace can fail
to be a locally Euclidean curve), but it **is** automatic for almost every level:

* `Work.Smooth.BoxGeneric.FaceRegular.ae_face_regular_of_sardCoord` — a.e. level is a regular value
  of every signed face function (Sard);
* `Work.Smooth.BoxGeneric.AeCorner.ae_transverseCorner_of_regularBisector` — a.e. level has only
  transverse corners;
* `Work.Smooth.BoxGeneric.aeVertexTangent` — a.e. level has only tangential vertex points;
* `Work.Smooth.OneManifold.ae_isLocallyEuclidean_levelSet_uncond` — a.e. level set is locally
  Euclidean (hence, being compact, a finite union of circles);
* `Work.Smooth.OneManifold.aeTransverseBox_uncond` — a.e. box sphere is transverse to the surface.

`Work.Drive.Mono.BoxGen ψ c σ s` below is the conjunction of those five conditions **at the single
level `s`**, and `Work.Drive.Mono.ae_boxGen` is the (proved, unconditional) statement that it holds
for almost every `s`.  It is the honest extra hypothesis which the tilted-sweep route must carry at
its box level: the sweep of Pardon, whose box level is chosen by
`Work.BoxShrink.exists_level_of_ae_count` (a level in an arbitrary conull set), always satisfies it.

The point of the file is that `BoxGen` is **provable for a.e. level**, so it can be added to the
hypotheses of the residual of the sweep (in place of the unsatisfiable `hreg` form of the withdrawn
`Work.Drive.Mono.JunctionGenData_exists`), while the consumer of the residual may choose its level in
the conull set of `Work.Drive.Mono.ae_boxGen`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set MeasureTheory
open scoped ENNReal Topology

namespace Work.Drive.Mono

noncomputable section

/-- **Corners are transverse at the level `s`** (the pointwise form of
`Work.Smooth.BoxGeneric.AeTransverseCorner`). -/
def CornerGen (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) : Prop :=
  ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, Submission.boxNorm c σ y = s →
    ∀ (i j : Fin 3) (ε ε' : ℝ), i ≠ j → (ε = 1 ∨ ε = -1) → (ε' = 1 ∨ ε' = -1) →
      Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε y →
      Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s j ε' y →
      (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧
        fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε)) p ≠ 0) →
      (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧
        fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε')) p ≠ 0) →
      (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧
        fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun z : R3 =>
          Work.Smooth.BoxGeneric.faceLin c σ i ε z -
            Work.Smooth.BoxGeneric.faceLin c σ j ε' z)) p ≠ 0) →
      Work.Smooth.BoxGeneric.CornerTransverseAt ψ c σ i j ε ε' y

/-- **Vertex points are tangential at the level `s`** (the pointwise form of
`Work.Smooth.BoxGeneric.AeVertexTangent`). -/
def VertexGen (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) : Prop :=
  ∀ ε : Fin 3 → ℝ, (∀ i : Fin 3, ε i = 1 ∨ ε i = -1) →
    Work.Smooth.BoxGeneric.boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier →
      ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = Work.Smooth.BoxGeneric.boxVertex c σ ε s ∧
        ∃ r : ℝ × ℝ,
          fderiv ℝ (Work.Smooth.Morse.param ψ) p r = Work.Smooth.BoxGeneric.Vertex.vertexDir σ ε

/-- **The general position of the box sphere at the level `s`.**

* every signed face function has the levels `±s` as regular values (no graze, no tangency of the
  surface with a box face);
* the corners at the level are transverse;
* the vertex points at the level are tangential;
* the level set `F ∩ {boxNorm c σ = s}` is locally Euclidean of dimension one;
* the box sphere is transverse to the surface.

All five hold at **almost every** level (`Work.Drive.Mono.ae_boxGen`). -/
def BoxGen (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) : Prop :=
  (∀ i : Fin 3, ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      Work.Smooth.Morse.IsRegularValue ψ (Work.Smooth.BoxGeneric.signedFace c σ i) (ε * s)) ∧
  CornerGen ψ c σ s ∧ VertexGen ψ c σ s ∧
  Work.Smooth.OneManifold.IsLocallyEuclidean
    (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) ∧
  Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ)
    {y : R3 | Submission.boxNorm c σ y = s}

/-- **`BoxGen` holds at almost every level.**  This is the unconditional a.e. general position of
the box sphere, assembled from the five theorems of the box-genericity chapter. -/
theorem ae_boxGen (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ s ∂(volume : Measure ℝ), BoxGen ψ c σ s := by
  have hreg := Work.Smooth.BoxGeneric.FaceRegular.ae_face_regular_of_sardCoord
    (Work.Smooth.BoxGeneric.Sard.sardCoord ψ) c σ
  have hcorn := Work.Smooth.BoxGeneric.AeCorner.ae_transverseCorner_of_regularBisector (ψ := ψ) c σ
  have htan := Work.Smooth.BoxGeneric.aeVertexTangent ψ c σ
  have hloc := Work.Smooth.OneManifold.ae_isLocallyEuclidean_levelSet_uncond ψ c σ
  have htrans := Work.Smooth.OneManifold.aeTransverseBox_uncond ψ c σ
  filter_upwards [hreg, hcorn, htan, hloc, htrans] with s hs_reg hs_corn hs_tan hs_loc hs_trans
  exact ⟨hs_reg, hs_corn, hs_tan, hs_loc, hs_trans⟩

end

end Work.Drive.Mono
