import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.PhiStar.CoreAux.F0_mul
import Submission.Work.FTS.PhiStar.CoreAux.F0_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_zpz
import Submission.Work.FTS.PhiStar.CoreAux.F0_theta_coefs
import Submission.Work.FTS.PhiStar.CoreAux.F0_z_coefs
import Submission.Work.FTS.PhiStar.CoreAux.Fb_basic
import Submission.Work.FTS.PhiStar.CoreAux.Fb_add
import Submission.Work.FTS.PhiStar.CoreAux.Fb_mul_theta_free
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr
import Submission.Work.FTS.PhiStar.CoreAux.LopIter_continuousOn_of_contDiff
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs
import Submission.Work.FTS.StrongPersist.SP6.EH6
import Submission.Work.FTS.StrongPersist.SP6.EVz6
import Submission.Work.FTS.StrongPersist.SP6.EV6
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.StrongPersist.SP6.EU6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

/-!
# `FTS/StrongPersist/SP6/FlatW6FieldsAlpha` — the order-six flat bounds of the five star fields

The five fields of the star package are, on the open quadrant,

* `EH α Y = 2Y + 2α sin²θ·(Y/(z+1) + z∂_zY) + sin 2θ·∂_θY`,
* `EVz Y = 2(cos²θ - 2 sin²θ)·Y + sin 2θ·∂_θY`,  `EV Y = (z/(z+1))·EVz Y`,
* `EUz α Y = -(3Y + α(Y/(z+1) + z∂_zY))`,  `EU α Y = (z/(z+1))·EUz α Y`,

and they are *linear* in the three blocks `Y`, `∂_θY`, `z∂_zY`; hence from the flat data of the
blocks (`Fb 6 KY Y`, `FlatW 7 Y K`, `F0 6 KD (Yblk Y)`) one gets `FlatW 6` of each field at a
constant `C·(α+1)·(K+KY+KD)`.  The factor `(α+1)` is genuinely needed for `EH`, `EUz`, `EU`
(they grow linearly in `α`); on `EV`, `EVz` it is only a weakening.  The α-free variant is
*false*: see `Submission/Work/FTS/StrongPersist/SP6/FlatW6Fields.lean`, `not_FlatW6Fields`.

## The decomposition

Each field is proved separately, following the route fixed in
`Submission/Work/FTS/StrongPersist/SP6/Flat6Defs.lean`: the first clause `F0 6 (field)` from the
bilinear flat calculus (`F0_mul`/`F0_add`/`F0_const_mul`, which keep the constant *linear* in
the block bounds), and the second clause `F0 5 (∂_θ(field))` from an `Fb 5` bound of the field
(`Fb_add`, `Fb_mul_theta_free`, `Fb_const_mul`), assembled with `flatW6_of_F0`:

* `Work.FTS.StrongPersist.SP6.EH6` — the `EH`-field;
* `Work.FTS.StrongPersist.SP6.EVz6` — the `EVz`-field;
* `Work.FTS.StrongPersist.SP6.EV6` — the `EV`-field;
* `Work.FTS.StrongPersist.SP6.EUz6` — the `EUz`-field;
* `Work.FTS.StrongPersist.SP6.EU6` — the `EU`-field.

This file is the assembly: the five constants are merged by taking
`C = C_EH + C_EVz + C_EV + C_EUz + C_EU + 1`, which dominates each of them and is positive.
-/

theorem FlatW6FieldsAlpha : ∃ C : ℝ, 0 < C ∧ ∀ (α K KY KD : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.VocabO2.FlatW 7 Y K → Work.FTS.PhiStar.Fb 6 KY Y → Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) →
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EH α Y) (C * (α + 1) * (K + KY + KD)) ∧
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EVz Y) (C * (α + 1) * (K + KY + KD)) ∧
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EV Y) (C * (α + 1) * (K + KY + KD)) ∧
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EUz α Y) (C * (α + 1) * (K + KY + KD)) ∧
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EU α Y) (C * (α + 1) * (K + KY + KD)) := by
  obtain ⟨C₁, hC₁, hH⟩ := EH6
  obtain ⟨C₂, hC₂, hVz⟩ := EVz6
  obtain ⟨C₃, hC₃, hV⟩ := EV6
  obtain ⟨C₄, hC₄, hUz⟩ := EUz6
  obtain ⟨C₅, hC₅, hU⟩ := EU6
  refine ⟨C₁ + C₂ + C₃ + C₄ + C₅ + 1, by linarith, ?_⟩
  intro α K KY KD Y hα hK hKY hKD hsm hW hFb hD
  have hS : (0 : ℝ) ≤ (α + 1) * (K + KY + KD) :=
    mul_nonneg (by linarith) (by linarith)
  have hbig1 : C₁ ≤ C₁ + C₂ + C₃ + C₄ + C₅ + 1 := by linarith
  have hbig2 : C₂ ≤ C₁ + C₂ + C₃ + C₄ + C₅ + 1 := by linarith
  have hbig3 : C₃ ≤ C₁ + C₂ + C₃ + C₄ + C₅ + 1 := by linarith
  have hbig4 : C₄ ≤ C₁ + C₂ + C₃ + C₄ + C₅ + 1 := by linarith
  have hbig5 : C₅ ≤ C₁ + C₂ + C₃ + C₄ + C₅ + 1 := by linarith
  have step : ∀ c : ℝ, c ≤ C₁ + C₂ + C₃ + C₄ + C₅ + 1 → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.VocabO2.FlatW 6 f (c * (α + 1) * (K + KY + KD)) →
      Work.FTS.VocabO2.FlatW 6 f ((C₁ + C₂ + C₃ + C₄ + C₅ + 1) * (α + 1) * (K + KY + KD)) := by
    intro c hc f hf
    refine FlatW_mono6 hf ?_
    calc c * (α + 1) * (K + KY + KD) = c * ((α + 1) * (K + KY + KD)) := by ring
      _ ≤ (C₁ + C₂ + C₃ + C₄ + C₅ + 1) * ((α + 1) * (K + KY + KD)) :=
          mul_le_mul_of_nonneg_right hc hS
      _ = (C₁ + C₂ + C₃ + C₄ + C₅ + 1) * (α + 1) * (K + KY + KD) := by ring
  exact ⟨step C₁ hbig1 _ (hH α K KY KD Y hα hK hKY hKD hsm hW hFb hD),
    step C₂ hbig2 _ (hVz α K KY KD Y hα hK hKY hKD hsm hW hFb hD),
    step C₃ hbig3 _ (hV α K KY KD Y hα hK hKY hKD hsm hW hFb hD),
    step C₄ hbig4 _ (hUz α K KY KD Y hα hK hKY hKD hsm hW hFb hD),
    step C₅ hbig5 _ (hU α K KY KD Y hα hK hKY hKD hsm hW hFb hD)⟩

end Work.FTS.StrongPersist.SP6
