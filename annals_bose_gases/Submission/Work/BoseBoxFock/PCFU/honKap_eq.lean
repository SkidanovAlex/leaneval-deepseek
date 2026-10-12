import ChallengeDeps
import Submission.Work.BoseBoxFock.PCFU.UnivFrames
import Submission.Work.BoseRowQ2.rowGchiMaskRow_honest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.honKap_eq`

The honest `n₊^H` threshold, at the honest (= FS's) box side, coincides with the inverse of
`(d²·ℓ)`:

    `honKap v μ = ((paramsAt μ (a v)).d ^ 2 * ellH v μ)⁻¹`.

Both sides are elementary functions of the parameter block `paramsAt μ (a v) = fsParams (μ(a v)³)`
and of `ℓ = sideAt μ (a v) = Kl·(μa)^{-1/2}`:

* `honKap v μ = (Kl·d²)^{-1}·√(μa)` (definition, `RowGchiMaskRowAux.honKap`);
* `ellH v μ = sideAt μ (a v) = Kl·(μa)^{-1/2}` whenever `sideAt μ (a v) > 0`
  (definition of `ellH`, discharged by `Work.BoseBox.sideAt_pos` at `0 < μ`, `0 < a v`).

Since `(μa)^{-1/2} = (√(μa))⁻¹`, the right-hand side is `(d²·Kl·(√(μa))⁻¹)⁻¹ =
(Kl·d²)⁻¹·√(μa)`, the left-hand side.  This is a pure algebra lemma about the parameter
vocabulary; no scattering theory is used beyond the positivity of `a v` and `μ`.
-/

namespace Work.BoseBoxFock.PCFU

theorem honKap_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseRowQ2.RowGchiMaskRowAux.honKap v μ
      = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2
          * Work.BoseBoxFock.ellH v μ)⁻¹ := by
  -- the two positivity facts that make `ellH` unfold to the box side, and make
  -- `(μa)^{-1/2} = (√(μa))⁻¹`
  have hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseBox.sideAt_pos hμ hav
  have hxpos : 0 < μ * _root_.BoseGases.a v := mul_pos hμ hav
  -- the (unconditional) division-ring identity underlying the equality
  have key : ∀ a b s : ℝ, (a * b)⁻¹ * s = (b * (a * s⁻¹))⁻¹ := by
    intro a b s
    simp only [mul_inv_rev, inv_inv]
    ring
  -- unfold both sides
  unfold Work.BoseRowQ2.RowGchiMaskRowAux.honKap Work.BoseBoxFock.ellH
  rw [if_pos hside]
  unfold Work.BoseBox.sideAt Work.BoseBox.boxSide
  rw [Real.rpow_neg_one, Real.sqrt_eq_rpow]
  -- turn `(μa)^{-1/2}` into `(√(μa))⁻¹`
  rw [Real.rpow_neg hxpos.le]
  exact key _ _ _

end Work.BoseBoxFock.PCFU
