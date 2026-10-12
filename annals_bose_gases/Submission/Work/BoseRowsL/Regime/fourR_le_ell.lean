import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseGateFS.GateThresholdsExist
import Submission.Work.BoseRowsL.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsL.Regime

/-!
# `Work.BoseRowsL.Regime.fourR_le_ell` — the box is much larger than the range of `v`

The row `4R ≤ ℓ` (FS `sec:params`: `R ≪ ℓ`, the box side dominates the range of the
potential many times over) at the **honest model** `honE v h fc fu HM μ`, i.e. at
`ℓ = ellH v μ = sideAt μ (a v) = K_ℓ (μ a v)^{-1/2}`, `K_ℓ = (μ a v³)^{-3/646}`.

It is a pure *parameter* row: no state, no mode choice and no geometry enters.  The two
threshold rows of `GateThresholds.dil` that produce it are

* `R ≤ 2 K_H a`                    (`R ≪ K_H a`, FS's range row), and
* `K_H a / (s ℓ) ≤ 1/32`           (`K_H a ≪ s ℓ`).

Multiplying the second by `sℓ > 0` and combining,

  `R ≤ 2 K_H a ≤ 2 · s ℓ / 32 = s ℓ / 16 ≤ ℓ / 16`,

because `s = (μ a v³)^{1/323} ≤ 1` at the admissible diluteness `μ a v³ ≤ εg ≤ 1`
(`GateThresholds.le_one`).  Hence `16 R ≤ ℓ`, in particular `4 R ≤ ℓ`.

Note that `s ≤ 1` is the *only* use of the diluteness cap: the row is genuinely a
consequence of the two threshold rows alone, at any diluteness `≤ 1`.
-/

open Work.BoseBoxFock

/-- **The honest `s` in closed form**: `s = (μ (a v)³)^{1/323}`. -/
lemma honE_s_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).s = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) 1 :=
  rfl

/-- `s = (μ (a v)³)^{1/323} > 0` at `0 < μ`, `0 < a v`. -/
lemma honE_s_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    0 < (Work.BoseRowsFS.honE v h fc fu HM μ).s := by
  have ht0 : 0 < Work.BoseFixR.dil v μ := by
    rw [Work.BoseFixR.dil]
    positivity
  rw [honE_s_eq, Work.BoseBox.fsXp]
  exact Real.rpow_pos_of_pos ht0 _

/-- `s ≤ 1` in the diluteness window `μ (a v)³ ≤ 1`. -/
lemma honE_s_le_one {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) (h1 : μ * _root_.BoseGases.a v ^ 3 ≤ 1) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).s ≤ 1 := by
  have ht0 : 0 < Work.BoseFixR.dil v μ := by
    rw [Work.BoseFixR.dil]
    positivity
  have htle : Work.BoseFixR.dil v μ ≤ 1 := by
    rw [Work.BoseFixR.dil]
    exact h1
  rw [honE_s_eq, Work.BoseBox.fsXp]
  exact Real.rpow_le_one ht0.le htle (by norm_num)

theorem fourR_le_ell {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hav : 0 < _root_.BoseGases.a v)
    (hthr : Work.BoseGateFS.GateThresholds v h fc fu R)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (hN : ∀ μ, hthr.Ng μ ≤ (HM μ).N)
    (μ : ℝ) (hμ : 0 < μ) (hdil : μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg) :
    4 * R ≤ Work.BoseBoxFock.ellH v μ := by
  obtain ⟨-, hR2KH, -, -, -, hlast⟩ := hthr.dil HM hN μ hμ hdil
  have hspos : 0 < (Work.BoseRowsFS.honE v h fc fu HM μ).s := honE_s_pos HM μ hμ hav
  have hsle : (Work.BoseRowsFS.honE v h fc fu HM μ).s ≤ 1 :=
    honE_s_le_one HM μ hμ hav (le_trans hdil hthr.le_one)
  have hell : (Work.BoseRowsFS.honE v h fc fu HM μ).ell = Work.BoseBoxFock.ellH v μ :=
    Work.BoseRowsFS.honE_ell v h fc fu HM μ hμ hav
  have hellpos : 0 < (Work.BoseRowsFS.honE v h fc fu HM μ).ell := by
    rw [hell]; exact Work.BoseBoxFock.ellH_pos v μ
  -- `K_H a ≤ s ℓ / 32` from the threshold row `K_H a / (s ℓ) ≤ 1/32`
  have hupper : (Work.BoseRowsFS.honE v h fc fu HM μ).KH
        * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat
      ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).s * (Work.BoseRowsFS.honE v h fc fu HM μ).ell / 32 := by
    rw [div_le_iff₀ (by positivity)] at hlast
    linarith
  -- `R ≤ 2 K_H a ≤ s ℓ / 16 ≤ ℓ / 16`
  have h16 : 16 * R ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).ell := by
    nlinarith [hR2KH, hupper, hsle, hellpos.le]
  rw [← hell]
  linarith

end Work.BoseRowsL.Regime
