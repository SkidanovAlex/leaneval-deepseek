import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB4.B7Kernel
import Submission.Work.BoseB4.BoxGram
import Submission.Work.BoseB4.Sect4Kernels
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.BoxOperators` — FS's box modes `a_k` and their CCR, hypothesis-free

`Work.BoseB4.BoxGram.exists_gram_ccrKernel` shows that the box kernel
`χ̂²((k−k')ℓ) − χ̂(kℓ)χ̂(k'ℓ)` of FS `eq:Commutator_general` is the Gram matrix of
honest vectors of `L²(Λ)` (the localised plane waves `qVec ℓ k = Q(e^{ikx}χ_Λ)`,
up to the normalising `ℓ^{-3/2}`).  This module packages the consequence in the
form FS state it:

* `boxFockData` — the bosonic mode system `a_k`, `a_k†` on the real Fock space
  over the mode lattice, built from the box data alone (no `hgram` hypothesis:
  `exists_gram_ccrKernel` supplies it);
* `boxFockData_ccrK` — `[a_k,a_{k'}†] = χ̂²((k−k')ℓ) − χ̂(kℓ)χ̂(k'ℓ)`;
* `boxFockData_ccrValue` — the same kernel as `ℓ⁻³⟨Q(e^{ikx}χ_Λ), Q(e^{ik'x}χ_Λ)⟩`,
  i.e. FS's `ℓ⁻³⟨Q(e^{ikx}χ_Λ), Q(e^{ik'x}χ_Λ)⟩ = χ̂²((k−k')ℓ) − χ̂(kℓ)χ̂(k'ℓ)`;
* `exists_boxCCR` — the packaged existential: there are coordinates such that the
  *operator* commutator is the box kernel.

The condensate `a₀` is the mode whose momentum is `0` (`kmom 0 = 0`): its mode
vector is `Q(χ_Λ)` in this model, so `[a₀,a₀†] = 1 − (∫χ)² ≥ 0` — the model
faithfully represents the *excited* modes (which is all §8–§11 use:
`excited Mode = Finset.univ.erase 0`).
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The box mode system**: the bosonic modes `a_k = a(Q(e^{ikx}χ_Λ))` of FS
`eq:ak-akdagger`, on the real Fock space over the mode lattice, with the box
kernel as their commutator.  The only data are the box `B`, the side `ℓ`, the
momenta `kmom` and the coordinates `f` (whose Gram matrix is the box kernel);
`Work.BoseB4.exists_gram_ccrKernel` supplies such `f` from the box data. -/
noncomputable def boxFockData (B : BoxData) {ℓ : ℝ} {Mode : Type*} [AddCommGroup Mode]
    [Fintype Mode] (kmom : Mode → ℝ³) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i)
    (m : ℕ) (f : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode,
      gram (f i) (f j) = BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j)) :
    BoseB7.FockData Mode :=
  b7FockDataBox kmom hkmom ℓ B.hatChiSq B.hatChi m f hf

/-- **FS `eq:Commutator_general` for the box modes.** -/
theorem boxFockData_ccrK (B : BoxData) {ℓ : ℝ} {Mode : Type*} [AddCommGroup Mode]
    [Fintype Mode] (kmom : Mode → ℝ³) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i)
    (m : ℕ) (f : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode,
      gram (f i) (f j) = BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
    (i j : Mode) :
    (boxFockData B kmom hkmom m f hf).ccrK i j = B.boxKernel ℓ (kmom i) (kmom j) := by
  rw [boxFockData, b7FockDataBox_ccrK, BoxData.boxKernel]

/-- **The value of the box commutator**: the kernel is `ℓ⁻³` times the Gram
product of the localised plane waves (`Work.BoseB4.BoxKernel.realIP_qVec_qVec`). -/
theorem boxFockData_ccrValue (B : BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ) {Mode : Type*}
    [AddCommGroup Mode] [Fintype Mode] (kmom : Mode → ℝ³)
    (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) (m : ℕ) (f : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode,
      gram (f i) (f j) = BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
    (i j : Mode) :
    (boxFockData B kmom hkmom m f hf).ccrK i j
      = ℓ ^ (-3 : ℝ) * B.realIP (B.qVec ℓ (kmom i)) (B.qVec ℓ (kmom j)) := by
  have hone : ℓ ^ (-3 : ℝ) * ℓ ^ 3 = 1 := by
    rw [Real.rpow_neg (le_of_lt hℓ), show ℓ ^ (3 : ℝ) = ℓ ^ 3 from Real.rpow_natCast ℓ 3,
      inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ))]
  rw [boxFockData_ccrK B kmom hkmom m f hf i j, realIP_qVec_qVec B hℓ (kmom i) (kmom j),
    ← mul_assoc, hone, one_mul]

/-- **FS `eq:Commutator_general` at the operator level, hypothesis-free.**  For
the box data `B`, the side `ℓ > 0` and any momentum assignment, there are
coordinates in which the bosonic modes `a_k`, `a_k†` on the real Fock space over
the mode lattice satisfy

    `[a_k, a_{k'}†] = (χ̂²((k−k')ℓ) − χ̂(kℓ)χ̂(k'ℓ))·1`,

the box kernel being the Gram product `ℓ⁻³⟨Q(e^{ikx}χ_Λ), Q(e^{ik'x}χ_Λ)⟩` of the
localised plane waves. -/
theorem exists_boxCCR (B : BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (kmom : Mode → ℝ³) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) :
    ∃ (m : ℕ) (f : Mode → Fin m → ℝ)
      (hf : ∀ i j : Mode,
        gram (f i) (f j) = BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j)),
      ∀ i j : Mode,
        ((boxFockData B kmom hkmom m f hf).a i).comp
            ((boxFockData B kmom hkmom m f hf).aDag j)
          = ((boxFockData B kmom hkmom m f hf).aDag j).comp
              ((boxFockData B kmom hkmom m f hf).a i)
            + (B.boxKernel ℓ (kmom i) (kmom j)) •
                (1 : (boxFockData B kmom hkmom m f hf).H →ₗ[ℝ]
                  (boxFockData B kmom hkmom m f hf).H) := by
  obtain ⟨m, f, hf⟩ := exists_gram_ccrKernel B hℓ kmom
  refine ⟨m, f, hf, fun i j => ?_⟩
  rw [(boxFockData B kmom hkmom m f hf).ccr i j, boxFockData_ccrK B kmom hkmom m f hf i j]

/-- **`hasKernel` for the box modes, in the mode-indexed form of node `B7A`.**
With `χ̂`, `χ̂²` read off the box data at `ℓ·kmom`, the box commutator is FS
`eq:Commutator_general`'s kernel `χ̂²(i−j) − χ̂(i)χ̂(j)` in the *mode* indices —
the field `hasKernel` of `Work.BoseB7A.Q3Kernel`. -/
theorem boxFockData_ccrK_hatChiMode (B : BoxData) {ℓ : ℝ} {Mode : Type*}
    [AddCommGroup Mode] [Fintype Mode] (kmom : Mode → ℝ³)
    (hkmom : ∀ i : Mode, kmom (-i) = -kmom i)
    (had : ∀ i j : Mode, kmom (i - j) = kmom i - kmom j) (m : ℕ) (f : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode,
      gram (f i) (f j) = BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
    (i j : Mode) :
    (boxFockData B kmom hkmom m f hf).ccrK i j
      = chiHatSqMode (Mode := Mode) B ℓ kmom (i - j)
        - chiHatMode (Mode := Mode) B ℓ kmom i * chiHatMode (Mode := Mode) B ℓ kmom j := by
  have h1 : chiHatSqMode (Mode := Mode) B ℓ kmom (i - j)
      = B.hatChiSq (ℓ • (kmom i - kmom j)) := by
    simp only [chiHatSqMode, had i j]
  have h2 : chiHatMode (Mode := Mode) B ℓ kmom i = B.hatChi (ℓ • kmom i) := rfl
  have h3 : chiHatMode (Mode := Mode) B ℓ kmom j = B.hatChi (ℓ • kmom j) := rfl
  rw [boxFockData_ccrK B kmom hkmom m f hf i j, BoxData.boxKernel, h1, h2, h3]


end Work.BoseB4
