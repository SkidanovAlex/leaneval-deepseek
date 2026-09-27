import Mathlib
import Submission.Work.Drive.ppParity.Shift
import Submission.Work.Drive.transportThreeLevel

/-!
# Smoothness of the intrinsically perturbed chains

`Work.Drive.ppShift Ξ w v E s u = Ξ (w s • v) (E s u)`.  The joint smoothness of `Ξ` (`hΞsm`), of the
weight `w` and of the chain `E` give the smoothness of the perturbed chain, which is what the
box-parity engines (`Work.Drive.even_ncard_ppMeetBdry`, S2) require of their chains.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **Smoothness of the perturbed chain.** -/
theorem contMDiff_ppShift
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞsm : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    {w : ℝ → ℝ} (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (v : EuclideanSpace ℝ (Fin 4)) (E : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (hE : ContMDiff
      (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E)) :
    ContMDiff
      (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (ppShift Ξ w v E)) := by
  have hw1 : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => w q.1) :=
    (contMDiff_iff_contDiff (𝕜 := ℝ) (E := ℝ × EuclideanSpace ℝ (Fin 2)) (E' := ℝ)).mpr
      (hw.comp (contDiff_fst))
  have h1 : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => w q.1 • v) :=
    ContMDiff.smul hw1 contMDiff_const
  have h2 : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => E q.1 q.2) := hE
  have h3 := hΞsm.comp (h1.prodMk h2)
  rw [show Function.uncurry (ppShift Ξ w v E)
      = fun q : ℝ × EuclideanSpace ℝ (Fin 2) => Ξ (w q.1 • v) (E q.1 q.2) from rfl]
  exact h3

end

end Work.Drive
