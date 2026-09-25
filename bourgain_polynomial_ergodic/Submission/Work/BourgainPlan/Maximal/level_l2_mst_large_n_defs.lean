import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_decay_sharp
import Submission.Work.BourgainPlan.Maximal.sigmaN_denom_le
import Submission.Work.BourgainPlan.Maximal.sigmaN_separated
import Submission.Work.BourgainPlan.Maximal.sigmaN_card_le
import Submission.Work.BourgainPlan.Maximal.mstEta_support
import Submission.Work.BourgainPlan.Maximal.memLp_scaled_bump
import Submission.Work.BourgainPlan.Maximal.memLp_mst_symbols
import Submission.Work.BourgainPlan.Maximal.opMul_l2_bound
import Submission.Work.BourgainPlan.Maximal.eLpNorm_two_opMul_le
import Submission.Work.BourgainPlan.IonescuWainger.opArc_strata_incl_excl
import Submission.Work.BourgainPlan.IonescuWainger.ArcSep
import Submission.Work.BourgainPlan.IonescuWainger.msw_sampling_lp

/-!
# The vocabulary of the large-`n` half of MST Theorem 2

Objects of MST §4.3, arXiv:1512.07518:

* `mstLvl l s = 𝒰((s+1)^l) \ 𝒰(s^l)` — the level-`s` set of arcs;
* `mstModelSym P l d χ η s n G` — the level-`s` major-arc model symbol at the dyadic scale `2^n`,
  i.e. MST's `ν^s_{2^n}(ξ) = Σ_{β ∈ 𝒰((s+1)^l)\𝒰(s^l)} G β Φ_{2^n}(ξ-β) η_s(ξ-β)`;
* `mstN₀ P s = 2^{κ_s}`, `κ_s = 20 d (⌊(s+1)^{1/10}⌋+1)` — where the large-`n` regime starts;
* `mstQ s = (⌈e^{(s+1)^{1/10}}⌉)!` — a common denominator of the level-`s` arcs;
* `mstChar u β = e^{2πiβu}` — the character used in the freezing/periodicity step.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

noncomputable section

/-- The level-`s` set of arcs of the MST major-arc model. -/
def mstLvl (l s : ℕ) : Finset Circ := (mstU l (s + 1)) \ (mstU l s)

/-- The level-`s` major-arc model symbol at the dyadic scale `2^n` (MST's `ν^s_{2^n}`). -/
def mstModelSym (P : Polynomial ℤ) (l : ℕ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s n : ℕ)
    (G : Circ → ℂ) : Circ → ℂ :=
  mstModelFn G (mstProf P (2 ^ n)) (mstEta d χ η s) (mstLvl l s)

@[simp] theorem mstModelSym_apply (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (s n : ℕ) (G : Circ → ℂ) (ξ : Circ) :
    mstModelSym P l d χ η s n G ξ
      = ∑ β ∈ mstLvl l s,
          G β * (mstProf P (2 ^ n) (ξ - β) * mstEta d χ η s (ξ - β)) := by
  rw [mstModelSym, mstModelFn_apply]

/-- The common denominator `Q_s = (⌈e^{(s+1)^{1/10}}⌉)!` of the level-`s` arcs. -/
def mstQ (s : ℕ) : ℕ := Nat.factorial ⌈Real.exp (((s : ℝ) + 1) ^ (1 / 10))⌉₊

/-- The scale `2^{κ_s}`, `κ_s = 20 d (⌊(s+1)^{1/10}⌋+1)`, where the large-`n` regime starts. -/
def mstN₀ (P : Polynomial ℤ) (s : ℕ) : ℕ :=
  2 ^ (20 * P.natDegree * (⌊((s : ℝ) + 1) ^ (1 / 10)⌋₊ + 1))

/-- The character `e^{2πiβu}` of the circle, read through the canonical lift `iwRep`. -/
def mstChar (u : ℤ) (β : Circ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((u : ℂ) * ((iwRep β : ℝ) : ℂ)))

theorem mstQ_pos (s : ℕ) : 0 < mstQ s := Nat.factorial_pos _

theorem mstQ_ne_zero (s : ℕ) : mstQ s ≠ 0 := (mstQ_pos s).ne'

theorem one_le_mstQ (s : ℕ) : 1 ≤ mstQ s := Nat.one_le_iff_ne_zero.mpr (mstQ_ne_zero s)

/-! ## The character `mstChar` -/

theorem mstChar_norm (u : ℤ) (β : Circ) : ‖mstChar u β‖ = 1 := by
  rw [mstChar, Complex.norm_exp]
  have h : (2 * Real.pi * Complex.I * ((u : ℂ) * ((iwRep β : ℝ) : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero]

theorem mstChar_add (u v : ℤ) (β : Circ) :
    mstChar (u + v) β = mstChar u β * mstChar v β := by
  rw [mstChar, mstChar, mstChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem mstChar_zero (β : Circ) : mstChar 0 β = 1 := by
  rw [mstChar]
  simp

end

end Work.BourgainPlan.Maximal
