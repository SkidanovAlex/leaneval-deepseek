import Mathlib
import Submission.Work.Drive.encodedEndData
import Submission.Work.Drive.meet32_bordism_invariance
import Submission.Work.Drive.localSard_family_in_open
import Submission.Work.Drive.encodedGenericAlt

/-!
# The ends-clause genericity: `Meet3Hyp` for the encoded triple, from the class-level regularities

**Statement stub** of `NOTES_LEAD_hodd_blockT6.md` §2.1 (project lead's design, 2026-09-26 14:xx).  The
content is the per-clause genericity of the ends clause: *moving the homotopy alone* produces a
`Meet3Hyp` for the encoded triple

> `encodedChains (fun x ↦ H' (x 2, pt2 (x 0) (x 1))) A B c₀`

whose two ends coincide with those of `H`, provided the class-level regularities `PairReg A B` and
`EndTripleReg (H (e, ·)) A B` (`e ∈ {0,1}`) hold.  The clauses are independent, so the proof uses
`localSard_family_in_open` once per clause (the family of §2.2 of the note adds box reparametrisations
of all three blocks — the `richness` hypothesis `hrich` of `localSard` fails for the homotopy alone,
which moves only in the diagonal `(u,u)` direction; see `REF_TRIPLE_JOINT_DESIGN.md` §7.2).

The three clauses of `HasClassLinearization` are then handled by `hasClassLinearization_of_endData`
(§2.5), with the ends read off in the order `(P̂₀,P̂₁,P̂₂)`, `(lin₀,P̂₁,P̂₂)`, `(lin₁,lin₀,P̂₂)`,
`(lin₂,lin₀,lin₁)`.

**The four `FoldFlat` hypotheses** (`NOTES_LEAD_hodd_faces.md` §1–§2) are the shape in which the
richness `hrich` consumes the fold behaviour of the plane and end presentations: `FoldFlat A` says the
derivative of `A` kills the boundary coordinate directions `eᵢ` at `y i ∈ {0,1}`, which is exactly what
makes the box shear — which *fixes* those coordinates — lose only directions that `A` already kills
(`Work.Drive.range_mfderiv_shear_eq`).  They are **theorems**, not hypotheses, for the design's own
presentations (`Work.Drive.mfderiv_planeClassMap_diskPlane_single` for the folded disk presentations
and `Work.Drive.mfderiv_planeClassMap_chartPert_diskPlane_single` for their chart perturbations), so a
consumer discharges them from the design data; they are demanded here because §2.1 is stated for an
abstract triple.  There is **no** `betaG ≠ 0` side condition and no `(C0)`: a fold meet is handled by
`PairReg` alone (`NOTES_LEAD_hodd_faces.md` §0.2).
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

attribute [local instance] Work.Drive.projCharted
attribute [local instance] Work.Drive.projTimesLineCharted
  Work.Drive.isManifold_projTimesLineCharted

/-- **The homotopy-genericity lemma of the ends clause** (`NOTES_LEAD_hodd_blockT6.md` §2.1). -/
theorem exists_homotopy_meet3Hyp_encoded
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    {c₀ : ℝ} (hc₀0 : 0 < c₀) (hc₀1 : c₀ < 1)
    (hH : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))))
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hseamH : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      H (t, seamInv2 y) = H (t, y))
    (hseamA : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → A (seamInv2 y) = A y)
    (hseamB : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → B (seamInv2 y) = B y)
    (hH0 : ∀ s : ℝ, s ≤ 0 → ∀ y : EuclideanSpace ℝ (Fin 2), H (s, y) = H (0, y))
    (hH1 : ∀ s : ℝ, 1 ≤ s → ∀ y : EuclideanSpace ℝ (Fin 2), H (s, y) = H (1, y))
    (hpair : PairReg A B)
    (hend0 : EndTripleReg (fun y => H (0, y)) A B)
    (hend1 : EndTripleReg (fun y => H (1, y)) A B)
    (hfoldA : FoldFlat A) (hfoldB : FoldFlat B)
    (hfold0 : FoldFlat (fun y : EuclideanSpace ℝ (Fin 2) => H (0, y)))
    (hfold1 : FoldFlat (fun y : EuclideanSpace ℝ (Fin 2) => H (1, y))) :
    ∃ H' : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3),
      (∀ y, H' (0, y) = H (0, y)) ∧ (∀ y, H' (1, y) = H (1, y)) ∧
      Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ)
        (encodedChains (fun x : EuclideanSpace ℝ (Fin 3) => H' (x 2, pt2 (x 0) (x 1)))
          A B c₀) := by
  exact exists_homotopy_meet3Hyp_encodedAlt H A B hc₀0 hc₀1 hH hA hB hseamH hseamA hseamB
    hH0 hH1 hpair hend0 hend1 hfoldA hfoldB hfold0 hfold1

end

end Work.Drive
