import Mathlib
import Submission.Work.Drive.ppParity.Good
import Submission.Work.Drive.ppParity.Contain

/-!
# The **interface** of the repaired (collar-line-safe) intrinsic pair Sard

The collar data shared by S3 (`Work.Drive.exists_ppReg_shift`) and S4
(`Work.Drive.exists_even_ppMeetEnd_add_intrinsic`) — `hwne : ∀ x ∈ K, w (ftS x) ≠ 0`, the slab of box
points inside `K`, and `hwleft : s ≤ δ → w s = 0` — are jointly unsatisfiable for `δ ∈ (0, 1/2]`
(`Submission/Work/Drive/ppParity/CollarDefect.lean`, four machine-checked lemmas); the repair, with its
analysis and its two routes, is `Submission/Work/Drive/PPPARITY_COLLAR_DEFECT.md` §§2–3bis.  The key
idea is that *the perturbation is trivial exactly where the weight vanishes*, so a perturbed meet with
`w (ftS x) = 0` is an honest meet and its regularity is the hypothesis `hregBase`, never a conclusion of
the Sard; the Sard is only ever applied where `w ≠ 0`.

This file fixes the *interface* of that repair (definitions and `Prop`-valued statements only —
deliberately no theorem with a proof obligation, so that nothing here can be a `sorry`):

* `PPChartGoodStrip` — the conclusion of the restricted localized pair Sard: the pair map's zeros in
  `K` **with `δ < ftS · < 1 - δ`** are regular, together with the face clause at those zeros;
* `PieceDataStrip` — the per-piece bundle `hpdrel` that the repaired S3 assembly consumes: at every
  point of the piece the surjectivity input is available (so the relaxed Sard applies), and the output
  is a good parameter with the restricted conclusion;
* `ExistsPPRegShiftStrip` — the *repaired statement* of S3, as a `Prop`;
* `ExistsPPRegShift` — the statement that S3 as currently on disk proves (`ppParity/Assembly.lean`),
  as a `Prop`, for comparison.

The remaining work of the lane is: prove `PieceDataStrip` (a copy of
`Submission/Work/Drive/piece_data_pp.lean` whose Sard call is the *relaxed* one,
`Work.Drive.ppParity.exists_forall_good_face_and_notMem_family_rel`, proved) and then prove
`ExistsPPRegShiftStrip` by the three-region case analysis (`ftS x < δ ∨ 1 - δ < ftS x`:
`PPRegAt_ppShift_of_collar`; `ftS x ∈ {δ, 1 - δ}`:
`ppIntrinsic.PPRegAt_ppShift_of_collarBoundary`; `δ < ftS x < 1 - δ`: the tube lemma plus
`PieceDataStrip`).
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The restricted conclusion of the localized pair Sard.**  As `PPChartGood`, but only at the pair
map's zeros in `K` whose family parameter lies in the *active* strip `δ < ftS · < 1 - δ`; the zeros in
the collar (`ftS · ≤ δ` or `1 - δ ≤ ftS ·`) are honest meets of the base family, whose regularity is
`hregBase` and whose charted derivative differs from the base one — they are deliberately not claimed
here. -/
def PPChartGoodStrip (δ : ℝ) (p p' : M)
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M)
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (w : ℝ → ℝ) (τ : EuclideanSpace ℝ (Fin 8))
    (K : Set (EuclideanSpace ℝ (Fin 9))) : Prop :=
  (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 →
      δ < ftS y → ftS y < 1 - δ →
      ppDiff p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W y = 0 →
      Function.Surjective (fderiv ℝ (ppDiff p p' (ppShift Ξ w (unpackFst τ) E)
        (ppShift Ξ w (unpackSnd τ) E') V W) y)) ∧
  (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 →
      δ < ftS y → ftS y < 1 - δ →
      ppDiff p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W y = 0 →
      y ∈ Submission.Drive.unitBoxBdry 8 →
      ∃ i : Fin 9, (y i = 0 ∨ y i = 1) ∧ (∀ j : Fin 9, j ≠ i → y j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (ppDiff p p' (ppShift Ξ w (unpackFst τ) E)
            (ppShift Ξ w (unpackSnd τ) E') V W) y v.1))

/-- **The per-piece bundle of the repaired S3** (the hypothesis `hpdrel` of the repaired assembly).
For every chart pair `(p, p')` and every compact piece `K'` on which the four values stay in the two
chart sources and on which the *surjectivity input of the relaxed Sard* is available — namely at every
pair-map zero `y ∈ K'` **in the active strip** `δ < ftS y < 1 - δ` (where `w (ftS y) ≠ 0` if
`K' ⊆ K`) — there is a good parameter at which the perturbed pair map is regular at all its zeros in
`K'` that lie in the active strip.

The off-strip zeros are *not* the Sard's business: they are honest meets and their regularity comes
from `hregBase` (this is the content of the relaxed Sard's `hregOff`, which at a zero with
`w (ftS z) = 0` is exactly `PPRegAt` of the base family, the two systems coinciding there). -/
def PieceDataStrip (δ : ℝ) (p p' : M)
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M)
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (w : ℝ → ℝ) : Prop :=
  ∀ (K : Set (EuclideanSpace ℝ (Fin 9))) (δ' : ℝ), IsCompact K → 0 < δ' →
    (∀ (τ : EuclideanSpace ℝ (Fin 8)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ' → y ∈ K →
      y ∈ ppRegion p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W) →
    (∀ (τ : EuclideanSpace ℝ (Fin 8)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ' → y ∈ K →
      ppDiff p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W y = 0 →
      δ < ftS y → ftS y < 1 - δ →
      Function.Surjective (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 8) =>
        ppDiff p p' (ppShift Ξ w (unpackFst τ') E) (ppShift Ξ w (unpackSnd τ') E') V W y) τ)) →
    ∃ (ρ : ℝ) (Ψ : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) →
        EuclideanSpace ℝ (Fin 8)),
      0 < ρ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
      IsOpen {τ : EuclideanSpace ℝ (Fin 8) | ppGoodSet Ψ K τ} ∧
      (∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < ρ → ppGoodSet Ψ K τ →
        PPChartGoodStrip δ p p' E E' V W Ξ w τ K) ∧
      (∀ τ₀ : EuclideanSpace ℝ (Fin 8), ‖τ₀‖ < ρ → ∀ ε' : ℝ, 0 < ε' →
        ∃ τ : EuclideanSpace ℝ (Fin 8), ‖τ - τ₀‖ < ε' ∧ ‖τ‖ < ρ ∧ ppGoodSet Ψ K τ)

/-- **The repaired statement of S3**, as a `Prop` carrying the whole hypothesis list:
`Work.Drive.exists_ppReg_shift` restated with the non-vanishing `hwne` restricted to the *active strip*
`δ < ftS · < 1 - δ`, *closed* collars `s ≤ δ → w s = 0`, `1 - δ ≤ s → w s = 0`, the honesty hypothesis
`hregBase` at the base meets in the closed collar, and the same covering condition `hKcover` on the
closed slab of the box.  This is the form that is *consistent* and *applicable*; the statement of
`ppParity/Assembly.lean` is not (see `PPPARITY_COLLAR_DEFECT.md` §0). -/
def ExistsPPRegShiftStrip (Q : ℂ → CappingSpace)
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (w : ℝ → ℝ) : Prop :=
  (ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E)) →
  (ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E')) →
  (ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V) →
  (ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W) →
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w →
  ChartPert Q 4 Ξ →
  (K : Set (EuclideanSpace ℝ (Fin 9))) → IsCompact K → (δ : ℝ) → 0 ≤ δ →
  (∀ x ∈ K, δ < ftS x → ftS x < 1 - δ → w (ftS x) ≠ 0) →
  (∀ x ∈ Submission.Drive.unitBox 8, δ ≤ ftS x → ftS x ≤ 1 - δ → x ∈ interior K) →
  (∀ s : ℝ, s ≤ δ → w s = 0) → (∀ s : ℝ, 1 - δ ≤ s → w s = 0) →
  (∀ x ∈ Submission.Drive.unitBox 8, (ftS x ≤ δ ∨ 1 - δ ≤ ftS x) →
    ppMeet E E' V W x → PPRegAt E E' V W x) →
  (ε : ℝ) → 0 < ε →
  ∃ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < ε ∧ ∀ x ∈ Submission.Drive.unitBox 8,
    ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W x →
    PPRegAt (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W x

end

end Work.Drive
