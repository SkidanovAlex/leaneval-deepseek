import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.XSrpSector
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sectorXSpowWidth` — the width form of the sector spectral bound

The BF3c step-6 chain (`FINDING_sector_XSpow_le_s11.md`) needs the **width** form of the sector
bound: for a box state `Φ` whose `n₊`-spectrum lies in `[0, 𝓜]` and the mode family `e`,

    `∫_{abox n ℓ} ‖XSpow ℓ S j (slotExact e S Φc)‖² ≤ 𝓜^{2j} ∫_{abox n ℓ} Φ²`   (E2w)

with `Φc = (Φ : ℂ)`.  The right-hand side carries `Φ` (not the sector): this is what the assembly
consumes, because the unused sharp constant is killed by the geometric limit `m → ∞`.

**(E2w) is a consequence of two facts about the mode family, and of nothing else:**

* **(comm)** `XSpow ℓ S j` commutes with the sector projection `slotExact e S`;
* **(contr)** the sector projection is an `L²`-contraction.

Together with the *geometry half*, `Work.BoseBoxFock.XSpow_L2_le` (proved, no mode hypothesis),

    `∫ ‖XSpow ℓ S j Φc‖² ≤ 𝓜^{2j} ∫ Φ²` ,

the chain closes in one line.  This module records exactly that, so that the two mode-theoretic
inputs can be produced separately (`FINDING_sector_XSpow_le_s11.md` §3: the absorption `Q_i P_i = P_i`
and its transpose `P_i Q_i = P_i`, the peel, and the Möbius sum for **(comm)**; the same
absorption/peel data for **(contr)**).

Everything is `sorry`-free and rests on the standard axioms only.
-/

noncomputable section

open MeasureTheory
open Submission.BoseGases

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The width form of the sector spectral bound**, from the commutation and the contraction. -/
theorem sector_XSpow_width {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n))
    {Φ : X n → ℝ} (hΦ : Continuous Φ) {M : ℝ} (hM : 0 ≤ M)
    (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ) {m : ℕ} [NeZero m]
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ} (j : ℕ)
    (hcomm : XSpow ℓ S j (slotExact e S (fun x => ((Φ x : ℝ) : ℂ)))
      =ᵐ[(volume : Measure (X n)).restrict (abox n ℓ)]
      slotExact e S (XSpow ℓ S j (fun x => ((Φ x : ℝ) : ℂ))))
    (hcontr : (∫ x in abox n ℓ,
        ‖slotExact e S (XSpow ℓ S j (fun x => ((Φ x : ℝ) : ℂ))) x‖ ^ 2)
      ≤ ∫ x in abox n ℓ, ‖XSpow ℓ S j (fun x => ((Φ x : ℝ) : ℂ)) x‖ ^ 2) :
    (∫ x in abox n ℓ, ‖XSpow ℓ S j (slotExact e S (fun x => ((Φ x : ℝ) : ℂ))) x‖ ^ 2)
      ≤ M ^ (2 * j) * (∫ x in abox n ℓ, (Φ x) ^ 2) := by
  have hcomm' : (fun x => ‖XSpow ℓ S j (slotExact e S (fun x => ((Φ x : ℝ) : ℂ))) x‖ ^ 2)
      =ᵐ[(volume : Measure (X n)).restrict (abox n ℓ)]
      fun x => ‖slotExact e S (XSpow ℓ S j (fun x => ((Φ x : ℝ) : ℂ))) x‖ ^ 2 := by
    filter_upwards [hcomm] with x hx
    rw [hx]
  have h1 : (∫ x in abox n ℓ, ‖XSpow ℓ S j (slotExact e S (fun x => ((Φ x : ℝ) : ℂ))) x‖ ^ 2)
      = ∫ x in abox n ℓ,
          ‖slotExact e S (XSpow ℓ S j (fun x => ((Φ x : ℝ) : ℂ))) x‖ ^ 2 :=
    integral_congr_ae hcomm'
  rw [h1]
  exact le_trans hcontr (XSpow_L2_le ℓ hℓ S hΦ hM hmom j)

end Work.BoseBoxFock
