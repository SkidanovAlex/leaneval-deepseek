import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.chiW1_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.wordSplitDefs` — vocabulary of the `d = 0` word split

The abbreviations of `Work.BoseBoxFock.PCFU.Dchan_dzero_word_split`:

* `smearW ℓ W z = ∫ y, χ_ℓ(y)·W(y − z) dy` — the `χ`-smear of the pair kernel `W` (for
  `W = W1fun v h ℓ` this is the object in the target's remainder term);
* `wordB fc κ ℓ i j Θ y = Q_{L,j}(Q_jP_iΘ)(y)·wLoc ℓ (g0 v h) 0 (y i) (y j)` — the integrand of the
  target's word term;
* `wordF fc κ ℓ i j Θ x z = Q_{L,j}(Q_jP_iΘ)(x[j↦z])` — the low-slot factor of the remainder.

All three are just transparent unfoldings; nothing is proved here.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The `χ_ℓ`-smear of a kernel: `z ↦ ∫ y, χ_ℓ(y)·W(y − z) dy`. -/
noncomputable def smearW (ℓ : ℝ) (W : E3 → ℝ) (z : E3) : ℝ :=
  ∫ y : E3, Submission.BoseGases.chiScale ℓ y * W (y - z)

/-- The word integrand: `Q_{L,j}(Q_jP_iΘ)·wLoc ℓ (g0 v h) 0 (·i) (·j)`. -/
noncomputable def wordB {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) :
    Submission.BoseGases.X n → ℝ :=
  fun y => Work.BoseBoxFix.lowSlot fc κ ℓ j
      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) y
    * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (y i) (y j)

/-- The low-slot factor of the remainder term. -/
noncomputable def wordF {n : ℕ} (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (i j : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) (z : E3) : ℝ :=
  Work.BoseBoxFix.lowSlot fc κ ℓ j
    (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) (Function.update x j z)

end Work.BoseBoxFock.PCFU
