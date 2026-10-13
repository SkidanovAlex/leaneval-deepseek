import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

open scoped Real

/-!
# `continuous_logW_leaf` — continuity of the log-coordinate leaf densities

For each of the three leaf weights `leafEta`, `leafOne`, `leafGam α` of the `IP4`-unfolding
(`TransportS.Slots`), the log-coordinate density

  `logW w y = logJac y.1 y.2 * w (e^{y.1}) (arctan (e^{y.2}))`

is continuous on the plane.  This is the regularity hypothesis consumed by the transfer
estimates of `JepsTransfer` (e.g. the convolution identities relating `logPair` to the pairings
`slotPairing`).

Everything reduces to the continuity of the thre factors on `ℝ²`:

* the Jacobian `logJac s ζ = e^s · e^ζ / (1 + e^{2ζ})`;
* the radial factor `w (e^s)² = ((1+e^s)²/(e^s)²)²` (continuous because `e^s > 0` for all `s`,
  which is exactly why the pole of `Spaces.w` at `0` is harmless);
* the angular factor `sin(2 arctan (e^ζ))^{-q}`, `q ≥ 0`; here `arctan (e^ζ) ∈ (0, π/2)` for
  *every* `ζ`, so the base is genuinely positive and `Real.rpow` is continuous in the base on
  this range (no junk-value issues).
-/

private lemma arctan_exp_mem_clw (ζ : ℝ) :
    Real.arctan (Real.exp ζ) ∈ Set.Ioo 0 (π / 2) :=
  ⟨Real.arctan_pos.mpr (Real.exp_pos ζ), Real.arctan_lt_pi_div_two _⟩

/-- The Jacobian `logJac` of the log-coordinate substitution is continuous on the plane. -/
private lemma continuous_logJac_clw :
    Continuous (fun y : ℝ × ℝ => Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2) := by
  simp only [Work.FTS.StrongEps.HkSqAux.logJac, Work.FTS.StrongEps.HkSqAux.kappa]
  exact ((Real.continuous_exp.comp continuous_fst)).mul
    (((Real.continuous_exp.comp continuous_snd)).div
      (continuous_const.add ((Real.continuous_exp.comp (continuous_const.mul continuous_snd))))
      (fun y => by positivity))

/-- The radial factor `y ↦ w (e^{y.1})²` of the leaf weights is continuous on the plane. -/
private lemma continuous_wtZ_exp_clw :
    Continuous (fun y : ℝ × ℝ => Work.Spaces.w (Real.exp y.1) ^ 2) := by
  have h : Continuous fun y : ℝ × ℝ =>
      ((1 + Real.exp y.1) ^ 2 / (Real.exp y.1) ^ 2) ^ 2 :=
    (((continuous_const.add (Real.continuous_exp.comp continuous_fst)).pow 2).div
      ((Real.continuous_exp.comp continuous_fst).pow 2)
      (fun y => pow_ne_zero 2 (ne_of_gt (Real.exp_pos _)))).pow 2
  simpa only [Work.Spaces.w] using h

/-- The angular factor `y ↦ sin(2 arctan (e^{y.2}))^{-q}` is continuous on the plane for every
exponent `q`. -/
private lemma continuous_sinTwo_arctan_exp_clw (q : ℝ) :
    Continuous (fun y : ℝ × ℝ => Real.sin (2 * Real.arctan (Real.exp y.2)) ^ (-q)) := by
  have hsin : Continuous (fun y : ℝ × ℝ => Real.sin (2 * Real.arctan (Real.exp y.2))) :=
    Real.continuous_sin.comp
      (continuous_const.mul (Real.continuous_arctan.comp (Real.continuous_exp.comp continuous_snd)))
  refine hsin.rpow_const (fun y => Or.inl ?_)
  have hθ := arctan_exp_mem_clw y.2
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))

theorem continuous_logW_leaf {w : ℝ → ℝ → ℝ} {α : ℝ}
    (hw : w = Work.FTS.TransportS.leafEta ∨ w = Work.FTS.TransportS.leafOne
      ∨ w = Work.FTS.TransportS.leafGam α) :
    Continuous (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w) := by
  rcases hw with rfl | rfl | rfl
  · show Continuous (fun y : ℝ × ℝ => Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2 *
      (Work.Spaces.w (Real.exp y.1) ^ 2 *
        Real.sin (2 * Real.arctan (Real.exp y.2)) ^ (-(Work.Spaces.eta))))
    exact continuous_logJac_clw.mul (continuous_wtZ_exp_clw.mul
      (continuous_sinTwo_arctan_exp_clw Work.Spaces.eta))
  · show Continuous (fun y : ℝ × ℝ => Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2 *
      Work.Spaces.w (Real.exp y.1) ^ 2)
    exact continuous_logJac_clw.mul continuous_wtZ_exp_clw
  · show Continuous (fun y : ℝ × ℝ => Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2 *
      (Work.Spaces.w (Real.exp y.1) ^ 2 *
        Real.sin (2 * Real.arctan (Real.exp y.2)) ^ (-(Work.Spaces.gam α))))
    exact continuous_logJac_clw.mul (continuous_wtZ_exp_clw.mul
      (continuous_sinTwo_arctan_exp_clw (Work.Spaces.gam α)))

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
