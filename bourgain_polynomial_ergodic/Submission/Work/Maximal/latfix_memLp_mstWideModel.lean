import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.Maximal.wideModel_small_s_bound

open MeasureTheory Finset
open Work.BourgainPlan.IonescuWainger Work.BourgainPlan.Maximal

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Maximal

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-- The `L^∞(𝕋)`-class of the wide level model symbol exists: it is a finite sum of translates of
the a.e. bounded function `star Φ_{2^k} · ϱ_s`. -/
theorem memLp_mstWideModel (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hηc : Continuous η) (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (k s : ℕ) :
    MemLp (mstWideModel P l χ η k s) ⊤ haarT := by
  have hϱ : MemLp (mstWideBump P χ η s) ⊤ haarT :=
    (mstWideBump_memLp_and_narrow P χ η hηc hηsup s).1
  have hφ : MemLp (fun ζ : Circ => star (mstProf P (2 ^ k) ζ) * mstWideBump P χ η s ζ) ⊤ haarT :=
    memLp_star_mstProf_mul_mstWideBump P k s χ η hηc hϱ
  have h := memLp_arcSymbolW (fun β : Circ => β) (fun β : Circ => star (mstG P β))
    (mstAnnulus l s) hφ
  simpa only [mstWideModel, mstModelFn] using h

end

end Work.Maximal
