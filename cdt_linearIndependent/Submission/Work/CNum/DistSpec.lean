import Mathlib
import Submission.Work.CNum.SmallBox
import Submission.Work.CNum.NrmSpec
import Submission.Work.CNum.AbsMaxSpec
import Submission.Work.CNum.CpxSound
import Submission.Work.CNum.LgInfra
import Submission.Work.CNum.DistUpCore
import Submission.Work.CNum.ChordSpec

/-!
# `Work.CNum.DistSpec` — the chord/numerics specification used by the `CNum` certificate

This module collects the soundness statements that the arc certificate of Theorem C
(`Work.CNum.Gv`/`gv`, `Fx.lean`) is built on:

* `‖z - w‖ ≤ m2r (distUp a b)` for `z ∈ a`, `w ∈ b` (`Small` boxes): the mantissa `distUp` really
  dominates the distance of two points of the two boxes — proved in `Work.CNum.DistUpCore`;
* the same with the constants `4/3` (`W = (4/3)·ψ_C` coordinates, `dWup`) and `143/115`
  (`V = (ψ_C - c₂)/ρ₂` coordinates, `dVup`): the two normalisations multiply distances by
  `4/3 = 1/c₂` resp. `143/115 = 1/ρ₂` — proved here, by feeding the `distUp` bound through the
  outward-rounded quotient `divU` (`LgInfra`);
* the chord growth bounds `400·(d + d³/12 + 4096/SC)² ≤ m2r (chord1 d)` and the same with `1000`
  (`chord2`): on an arc of length `d` in the `W`- resp. `V`-coordinates the function `log ‖h‖`
  varies by at most `C·(d + d³/12 + 4096/SC)²` — proved in `Work.CNum.ChordSpec`.
-/

namespace Work.CNum

open Work.ANum

/-! ## The rescaled arc-length bounds -/

/-- **The `dWup` specification** (`W = (4/3)·ψ_C` coordinates): rescaling by `4/3`, as the
outward-rounded mantissa `divU (distUp a b * 4) 3 + 4096`. -/
private lemma dWup_conj : ∀ (a b : Cpx) (z w : ℂ), Small a → Small b → a.Mem z → b.Mem w →
    (4 / 3) * ‖z - w‖ ≤ m2r (dWup a b) := by
  intro a b z w ha hb hz hw
  have h1 := DistUpCore a b z w ha hb hz hw
  have h3 : m2r (distUp a b * 4) / 3 ≤ m2r (divU (distUp a b * 4) 3) :=
    divU_ge (k := 3) (by norm_num) _
  have h2 : m2r (distUp a b * 4) = 4 * m2r (distUp a b) := by rw [m2r_mul_int]; ring
  have hunf : m2r (dWup a b) = m2r (divU (distUp a b * 4) 3) + 4096/(SC:ℝ) := by
    rw [dWup, m2r_add]; rfl
  rw [hunf]
  have h4 : (4/3) * ‖z - w‖ ≤ m2r (distUp a b * 4) / 3 := by rw [h2]; linarith
  have h5 : (0:ℝ) ≤ 4096/(SC:ℝ) := div_nonneg (by norm_num) SC_posR.le
  linarith

/-- **The `dVup` specification** (`V = (ψ_C - c₂)/ρ₂` coordinates, `ρ₂ = 115/143`): rescaling by
`143/115`, as the outward-rounded mantissa `divU (distUp a b * 143) 115 + 4096`. -/
private lemma dVup_conj : ∀ (a b : Cpx) (z w : ℂ), Small a → Small b → a.Mem z → b.Mem w →
    (143 / 115) * ‖z - w‖ ≤ m2r (dVup a b) := by
  intro a b z w ha hb hz hw
  have h1 := DistUpCore a b z w ha hb hz hw
  have h3 : m2r (distUp a b * 143) / 115 ≤ m2r (divU (distUp a b * 143) 115) :=
    divU_ge (k := 115) (by norm_num) _
  have h2 : m2r (distUp a b * 143) = 143 * m2r (distUp a b) := by rw [m2r_mul_int]; ring
  have hunf : m2r (dVup a b) = m2r (divU (distUp a b * 143) 115) + 4096/(SC:ℝ) := by
    rw [dVup, m2r_add]; rfl
  rw [hunf]
  have h4 : (143/115) * ‖z - w‖ ≤ m2r (distUp a b * 143) / 115 := by rw [h2]; linarith
  have h5 : (0:ℝ) ≤ 4096/(SC:ℝ) := div_nonneg (by norm_num) SC_posR.le
  linarith

theorem DistSpec : (∀ (a b : Work.CNum.Cpx) (z w : ℂ), Work.CNum.Small a → Work.CNum.Small b → a.Mem z → b.Mem w → ‖z - w‖ ≤ Work.ANum.m2r (Work.CNum.distUp a b)) ∧ (∀ (a b : Work.CNum.Cpx) (z w : ℂ), Work.CNum.Small a → Work.CNum.Small b → a.Mem z → b.Mem w → (4 / 3) * ‖z - w‖ ≤ Work.ANum.m2r (Work.CNum.dWup a b)) ∧ (∀ (a b : Work.CNum.Cpx) (z w : ℂ), Work.CNum.Small a → Work.CNum.Small b → a.Mem z → b.Mem w → (143 / 115) * ‖z - w‖ ≤ Work.ANum.m2r (Work.CNum.dVup a b)) ∧ (∀ d : ℤ, 0 ≤ Work.ANum.m2r d → 400 * (Work.ANum.m2r d + (Work.ANum.m2r d) ^ 3 / 12 + 4096 / Work.ANum.SC) ^ 2 ≤ Work.ANum.m2r (Work.CNum.chord1 d)) ∧ (∀ d : ℤ, 0 ≤ Work.ANum.m2r d → 1000 * (Work.ANum.m2r d + (Work.ANum.m2r d) ^ 3 / 12 + 4096 / Work.ANum.SC) ^ 2 ≤ Work.ANum.m2r (Work.CNum.chord2 d)) :=
  ⟨DistUpCore, dWup_conj, dVup_conj, ChordSpec.1, ChordSpec.2⟩

end Work.CNum
