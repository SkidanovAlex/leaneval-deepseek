import Mathlib
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_of_forall
import Submission.Work.Smooth.OneManifold.isLocallyEuclideanAt_of_uniqueActiveFace
import Submission.Work.Smooth.OneManifold.isLocallyEuclideanAt_of_corner
import Submission.Work.Smooth.OneManifold.isLocallyEuclideanAt_of_tangentialCorner
import Submission.Work.Smooth.BoxGeneric.AeMain
import Submission.Work.Smooth.BoxGeneric.Case.exists_active_signed_of_not_vertex
import Submission.Work.Smooth.Morse.Flow.exists_descentRate_lower_bound
import Submission.Work.Core.torusMap_eq_iff

/-!
# A good box level is locally Euclidean

If `s > 0` is a level at which

* every signed face function is regular at the value `± s` (the a.e. hypothesis
  `Work.Smooth.BoxGeneric.FaceRegular.ae_face_regular_of_sardCoord`),
* every corner of the level set at which the bisector is regular is transverse
  (`Work.Smooth.BoxGeneric.CornerTransverseAt`, supplied a.e. by
  `Work.Smooth.BoxGeneric.AeCorner.ae_transverseCorner_of_regularBisector`), and
* no point of the level set is a vertex of the box,

then the box-norm level set `F ∩ {boxNorm c σ = s}` is locally Euclidean of dimension one: every
point has a neighbourhood, in the level set, homeomorphic to `ℝ`.

The three local models — a unique active face
(`Work.Smooth.OneManifold.isLocallyEuclideanAt_of_uniqueActiveFace`), a transverse corner
(`Work.Smooth.OneManifold.isLocallyEuclideanAt_of_corner`) and a tangential corner
(`Work.Smooth.OneManifold.isLocallyEuclideanAt_of_tangentialCorner`) — are assembled by
`Work.Smooth.OneManifold.isLocallyEuclidean_of_forall_exists`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

open scoped Topology

/-- **A good box level is locally Euclidean.** -/
theorem isLocallyEuclidean_levelSet_of_regular {ψ : Submission.Diffeo} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {s : ℝ} (hs : 0 < s)
    (hreg : ∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) →
      Work.Smooth.Morse.IsRegularValue ψ (Work.Smooth.BoxGeneric.signedFace c σ i) (ε * s))
    (hcorn : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, Submission.boxNorm c σ y = s →
      ∀ (i j : Fin 3) (ε ε' : ℝ), i ≠ j → (ε = 1 ∨ ε = -1) → (ε' = 1 ∨ ε' = -1) →
        Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε y →
        Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s j ε' y →
        (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧ fderiv ℝ
          (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε)) p ≠ 0) →
        (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧ fderiv ℝ
          (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε')) p ≠ 0) →
        (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧ fderiv ℝ
          (Work.Smooth.Morse.pullback ψ
            (fun z : R3 => Work.Smooth.BoxGeneric.faceLin c σ i ε z -
              Work.Smooth.BoxGeneric.faceLin c σ j ε' z)) p ≠ 0) →
        Work.Smooth.BoxGeneric.CornerTransverseAt ψ c σ i j ε ε' y)
    (hvert : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier,
      ¬ Work.Smooth.BoxGeneric.IsBoxVertexPoint c σ s y) :
    IsLocallyEuclidean (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  refine isLocallyEuclidean_of_forall_exists
    (Work.Smooth.Morse.levelSet_subset_carrier ψ (Submission.boxNorm c σ) s) ?_
  intro x
  obtain ⟨hxcar, hxbox⟩ := Work.Smooth.Morse.mem_levelSet.mp x.2
  have hnv := hvert x hxcar
  rcases Work.Smooth.BoxGeneric.Case.exists_active_signed_of_not_vertex hs hxbox hnv with
    ⟨i, ε, hε, hact, huniq⟩ | ⟨i, j, ε, ε', hij, hε, hε', hacti, hactj, huniq⟩
  · exact isLocallyEuclideanAt_of_uniqueActiveFace hs hε hxcar hact huniq (hreg i ε hε)
  · have hregi := Work.Smooth.BoxGeneric.exists_fderiv_pullback_faceLin_ne_zero hε hxcar hacti
        (hreg i ε hε)
    have hregj := Work.Smooth.BoxGeneric.exists_fderiv_pullback_faceLin_ne_zero hε' hxcar hactj
        (hreg j ε' hε')
    by_cases hcrit : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = (x : R3) ∧ fderiv ℝ
        (Work.Smooth.Morse.pullback ψ
          (fun z : R3 => Work.Smooth.BoxGeneric.faceLin c σ i ε z -
            Work.Smooth.BoxGeneric.faceLin c σ j ε' z)) p = 0
    · -- tangential corner: reconcile the two parameters over `x`
      obtain ⟨p, hp, hregp⟩ := hregi
      obtain ⟨p', hp', htangp'⟩ := hcrit
      have hper : Work.Core.torusMap p.1 p.2 = Work.Core.torusMap p'.1 p'.2 := by
        apply ψ.injective
        simpa only [Work.Smooth.Morse.param_def] using hp.trans hp'.symm
      obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := (Work.Core.torusMap_eq_iff p.1 p.2 p'.1 p'.2).mp hper
      have hpeq : p = (p'.1 + (k : ℝ) * (2 * Real.pi), p'.2 + (l : ℝ) * (2 * Real.pi)) :=
        Prod.ext hk hl
      have htangp : fderiv ℝ (Work.Smooth.Morse.pullback ψ
          (fun z : R3 => Work.Smooth.BoxGeneric.faceLin c σ i ε z -
            Work.Smooth.BoxGeneric.faceLin c σ j ε' z)) p = 0 := by
        rw [hpeq, Work.Smooth.Morse.Flow.fderiv_pullback_add_lattice ψ _ p' k l]
        exact htangp'
      exact isLocallyEuclideanAt_of_tangentialCorner hs hij hε hε' hxcar hacti hactj huniq
        p hp htangp hregp
    · -- transverse corner
      have hregbis : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = (x : R3) ∧ fderiv ℝ
          (Work.Smooth.Morse.pullback ψ
            (fun z : R3 => Work.Smooth.BoxGeneric.faceLin c σ i ε z -
              Work.Smooth.BoxGeneric.faceLin c σ j ε' z)) p ≠ 0 := by
        obtain ⟨p, hp, -⟩ := hregi
        exact ⟨p, hp, fun h0 => hcrit ⟨p, hp, h0⟩⟩
      exact isLocallyEuclideanAt_of_corner hs hij hε hε' hxcar hacti hactj huniq
        (hcorn x hxcar hxbox i j ε ε' hij hε hε' hacti hactj hregi hregj hregbis)

end

end Work.Smooth.OneManifold
