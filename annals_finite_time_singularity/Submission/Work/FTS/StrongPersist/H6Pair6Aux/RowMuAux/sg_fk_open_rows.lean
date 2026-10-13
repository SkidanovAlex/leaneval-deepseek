/-
# `H6Pair6Aux/RowMuAux/sg_fk_open_rows` — the two `sg`-`FK` rows in the open class

`Work.FTS.NonlinRows.Rl1.sgRows45` proves the two rows

  `N₄^{sg} = -(1/2)·FK (F_*)·D_θg`,  `N₅^{sg} = -sin²θ·FK (F_*)·g`

of the primed `rl¹` block for a datum `g` in the **closed**-quadrant class `GalClass α g`
(`SmoothQuad g ∧ HkMem α 4 g`) against the envelope `Env α g`.  The level-six consumers of this
route only ever have the *honest* open-quadrant class

  `SmoothOpen f`  (`C^∞` on the open quadrant `(0,∞) × (0,π/2)`)  `∧  HkMem α 4 f`,

which is exactly what `H6Adm α f` supplies; this file re-proves the two rows in that class.

The analytic content is identical to `sgRows45`: the coefficient `FK (F_*)` is the *explicit*
profile `α·2r/(1+r)²` (`FK_Fstar_pt`), hence pointwise of size `≤ α/2` (`abs_FK_Fstar_le`), and
the angular Cauchy–Schwarz engine `PsgAux.rl1_slot_le` applies to the slots `D_θ f` resp. `f`
via the pointwise comparisons `PsgAux.slot_dth`/`PsgAux.slot_g`.  The only change is the source
of the two continuity hypotheses: `SmoothOpen.continuousOn` / `SmoothOpen.Dth.continuousOn`
replace the closed-quadrant `PsgAux.contOn_of_smoothQuad` (which needs `SmoothQuad`).  Note that
`StarPkgo`, which `sgRows45` carries as an unused hypothesis, is not needed at all.

Every declaration in this file is complete, with no gaps.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.SlotDataOpen
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.Rows45

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The explicit profile coefficient -/

/-- `|FK (F_*) r| ≤ α/2` for `0 < α ≤ 1`, `r > 0` (the profile `FK (F_*) = α·2r/(1+r)²` is
maximal at `r = 1`, where it equals `α/2`). -/
theorem abs_FK_Fstar_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {r : ℝ} (hr : 0 < r) :
    |Work.Construction.FK (Work.Construction.Fstar α) r| ≤ α / 2 := by
  rw [Work.FTS.NonlinRows.Rl1.FK_Fstar_pt hα hα1]
  have h1 : (0 : ℝ) ≤ 2 * r / (1 + r) ^ 2 := div_nonneg (by linarith) (by positivity)
  rw [abs_mul, abs_of_nonneg hα.le, abs_of_nonneg h1]
  have h2 : 2 * r / (1 + r) ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (1 - r)]
  nlinarith [h2, hα.le]

/-! ## Row `N₄^{sg} = -(1/2)·FK (F_*)·D_θf` -/

/-- **Row `N₄^{sg}` in the open class**, with the explicit constant `3√(π/2)`:
`Fa (N₄^{sg} α f) ≤ ofReal (3√(π/2)·α·|f|_{ℋ⁴})`. -/
theorem row4sg_open {α : ℝ} {f : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    Fa (Work.FTS.Nonlin.N4sg α f)
      ≤ ENNReal.ofReal (3 * Real.sqrt (Real.pi / 2)
          * (α * Work.FTS.Nonlin.Xn α f)) := by
  have hcontD : ContinuousOn (Function.uncurry (Work.Spaces.Dth f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hso.Dth.continuousOn
  have hmain := Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.rl1_slot_le
    (α := α) (C := 3 * α) (g := f)
    (A := fun z _ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z)
    (B := Work.Spaces.Dth f)
    (by positivity) hmem
    (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ => by
      have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.NonlinRows.Rl1.K_abs_le_three' hθ
      have h1 : |Work.Spaces.K θ * (-(1 / 2)
            * Work.Construction.FK (Work.Construction.Fstar α) r)|
          = |Work.Spaces.K θ| * (1 / 2)
            * |Work.Construction.FK (Work.Construction.Fstar α) r| := by
        simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
        ring
      rw [h1]
      have h3 : |Work.Spaces.K θ| * (1 / 2)
          * |Work.Construction.FK (Work.Construction.Fstar α) r| ≤ 3 * (1 / 2) * (α / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hK (by norm_num))
          (abs_FK_Fstar_le hα hα1 hr) (abs_nonneg _) (by norm_num)
      refine h3.trans ?_
      nlinarith [hα.le])
    (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slice_sq_aemeasurable hcontD hr)
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_aemeasurable hcontD)
    (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ =>
      Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_dth hα hr hθ f)
  have hid : Work.FTS.Nonlin.N4sg α f
      = fun r θ => (-(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) r)
          * Work.Spaces.Dth f r θ := by
    funext r θ
    simp only [Work.FTS.Nonlin.N4sg]
  rw [hid, Work.FTS.NonlinRows.Rl1.Fa_mul_eq (A := fun z _ =>
      -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z)
    (B := Work.Spaces.Dth f)]
  refine hmain.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring

/-! ## Row `N₅^{sg} = -sin²θ·FK (F_*)·f` -/

/-- **Row `N₅^{sg}` in the open class**, with the explicit constant `6√(π/2)`:
`Fa (N₅^{sg} α f) ≤ ofReal (6√(π/2)·α·|f|_{ℋ⁴})`. -/
theorem row5sg_open {α : ℝ} {f : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    Fa (Work.FTS.Nonlin.N5sg α f)
      ≤ ENNReal.ofReal (6 * Real.sqrt (Real.pi / 2)
          * (α * Work.FTS.Nonlin.Xn α f)) := by
  have hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hso.continuousOn
  have hmain := Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.rl1_slot_le
    (α := α) (C := 6 * α) (g := f)
    (A := fun z θ => -(Real.sin θ) ^ 2
      * Work.Construction.FK (Work.Construction.Fstar α) z)
    (B := f)
    (by positivity) hmem
    (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ => by
      have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.NonlinRows.Rl1.K_abs_le_three' hθ
      have hsin : (Real.sin θ) ^ 2 ≤ 1 := by
        nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
      have h1 : |Work.Spaces.K θ * (-(Real.sin θ) ^ 2
            * Work.Construction.FK (Work.Construction.Fstar α) r)|
          = |Work.Spaces.K θ| * (Real.sin θ) ^ 2
            * |Work.Construction.FK (Work.Construction.Fstar α) r| := by
        simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
        ring
      rw [h1]
      have h3 : |Work.Spaces.K θ| * (Real.sin θ) ^ 2
          * |Work.Construction.FK (Work.Construction.Fstar α) r| ≤ 3 * 1 * (α / 2) :=
        mul_le_mul (mul_le_mul hK hsin (sq_nonneg _) (by norm_num))
          (abs_FK_Fstar_le hα hα1 hr) (abs_nonneg _) (by norm_num)
      exact h3.trans (by nlinarith [hα.le]))
    (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slice_sq_aemeasurable hcont hr)
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_aemeasurable hcont)
    (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ =>
      Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_g hα hr hθ f)
  have hid : Work.FTS.Nonlin.N5sg α f
      = fun r θ => (-(Real.sin θ) ^ 2
          * Work.Construction.FK (Work.Construction.Fstar α) r) * f r θ := by
    funext r θ
    simp only [Work.FTS.Nonlin.N5sg]
  rw [hid, Work.FTS.NonlinRows.Rl1.Fa_mul_eq (A := fun z θ =>
      -(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z) (B := f)]
  refine hmain.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring

/-! ## Assembly -/

/-- **Rows `N₄^{sg}`, `N₅^{sg}` in the open class, against `Env`.**  The existential constant
`6√(π/2) + 1` works because `α·|f|_{ℋ⁴} ≤ Env α f` (`alpha_mul_Xn_le_Env`). -/
theorem sg_fk_open_rows : ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4sg α f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5sg α f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) := by
  refine ⟨6 * Real.sqrt (Real.pi / 2) + 1, by positivity, ?_⟩
  intro α f hα hα1 hso hmem
  have hEnvn : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α f :=
    Work.FTS.NonlinRows.Rl1.Env_nonneg f hα.le
  have hαX : α * Work.FTS.Nonlin.Xn α f ≤ Work.FTS.NonlinRows.Rl1.Env α f :=
    Work.FTS.NonlinRows.Rl1.alpha_mul_Xn_le_Env (g := f) hα hα1
  have hsv : (0 : ℝ) ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  have hK3 : 3 * Real.sqrt (Real.pi / 2) ≤ 6 * Real.sqrt (Real.pi / 2) + 1 := by
    nlinarith [hsv]
  have hK6 : 6 * Real.sqrt (Real.pi / 2) ≤ 6 * Real.sqrt (Real.pi / 2) + 1 := by
    linarith
  have key : ∀ c : ℝ, 0 ≤ c → c ≤ 6 * Real.sqrt (Real.pi / 2) + 1 →
      c * (α * Work.FTS.Nonlin.Xn α f)
        ≤ (6 * Real.sqrt (Real.pi / 2) + 1) * Work.FTS.NonlinRows.Rl1.Env α f := by
    intro c hc0 hcle
    have h1 : c * (α * Work.FTS.Nonlin.Xn α f) ≤ c * Work.FTS.NonlinRows.Rl1.Env α f :=
      mul_le_mul_of_nonneg_left hαX hc0
    have h2 : c * Work.FTS.NonlinRows.Rl1.Env α f
        ≤ (6 * Real.sqrt (Real.pi / 2) + 1) * Work.FTS.NonlinRows.Rl1.Env α f :=
      mul_le_mul_of_nonneg_right hcle hEnvn
    exact h1.trans h2
  constructor
  · refine (row4sg_open hα hα1 hso hmem).trans (ENNReal.ofReal_le_ofReal ?_)
    exact key (3 * Real.sqrt (Real.pi / 2)) (by positivity) hK3
  · refine (row5sg_open hα hα1 hso hmem).trans (ENNReal.ofReal_le_ofReal ?_)
    exact key (6 * Real.sqrt (Real.pi / 2)) (by positivity) hK6

end

end Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux
