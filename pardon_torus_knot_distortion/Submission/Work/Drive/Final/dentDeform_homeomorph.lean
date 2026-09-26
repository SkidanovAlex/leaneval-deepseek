import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs

/-!
# The dent deformation is a homeomorphism

`Work.Drive.Final.dentDeform χ centre d r a'` is the map `z ↦ z + a'·χ(‖z − centre‖/r)·d` of a dent
at `centre`, of depth `a'` and radius `r`.  This file proves that under the standing hypotheses of
the design — `χ` differentiable with `|χ'| ≤ κ`, `0 < r`, `‖d‖ ≤ 1`, `κ > 0`, and the smallness
condition `|a'|·κ < r` — this map is a **homeomorphism** of `ℝ³`.

The mathematical content is that `z ↦ z + a'·χ(‖z − centre‖/r)·d` is the identity perturbed by a
*strict contraction*: writing `D = a'•d`, the perturbation `z ↦ χ(‖z − centre‖/r) • D` is
`C`-Lipschitz with `C = κ‖D‖/r ≤ κ|a'|/r < 1` (mean value theorem for `χ`, triangle inequality for
the norm).  A map `x ↦ x + f x` with `f` Lipschitz of constant `< 1` is a bijection whose inverse is
Lipschitz: for each `y`, `x ↦ y − f x` is a contracting self-map of the complete space, so it has a
unique fixed point `ψ y`, and `ψ` is Lipschitz because two fixed points of nearby contractions are
close.  The abstract lemma `exists_homeomorph_add_of_lipschitz` below is that statement.

This is the `dentDeform_homeomorph` brick of the (L) route: it is what lets one pull geometric
statements (sphere covers, traces) back and forth along a dent.
-/

open scoped NNReal

namespace Work.Drive.Final

noncomputable section

/-- **A Lipschitz-small perturbation of the identity is a homeomorphism.**  If `f : E → E` is
`c`-Lipschitz with `c < 1` on a complete normed additive group, then `x ↦ x + f x` is a homeomorphism
of `E`.  (Injectivity and surjectivity by the Banach fixed point theorem applied to `x ↦ y − f x`,
and the inverse is Lipschitz with constant `(1 − c)⁻¹`.) -/
theorem exists_homeomorph_add_of_lipschitz {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [Nonempty E] {f : E → E} {c : ℝ≥0} (hf : LipschitzWith c f) (hc : c < 1) :
    ∃ Φ : E ≃ₜ E, ∀ x : E, Φ x = x + f x := by
  have hcR : (0 : ℝ) < 1 - (c : ℝ) := by
    have h : (c : ℝ) < 1 := by exact_mod_cast hc
    linarith
  -- the contraction `x ↦ y - f x` whose fixed point is the preimage of `y`
  have hT : ∀ y, ContractingWith c (fun x => y - f x) := by
    intro y
    refine ⟨hc, ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x x'
    have h1 : dist (y - f x) (y - f x') = dist (f x) (f x') := by
      rw [dist_eq_norm, dist_eq_norm,
        show (y - f x) - (y - f x') = -(f x - f x') by abel, norm_neg]
    rw [h1]
    exact hf.dist_le_mul x x'
  let ψ : E → E := fun y => ContractingWith.fixedPoint (fun x => y - f x) (hT y)
  have hψfix : ∀ y, y - f (ψ y) = ψ y := by
    intro y
    have h := ContractingWith.fixedPoint_isFixedPt (hT y)
    exact h
  have hleft : ∀ y, ψ y + f (ψ y) = y := by
    intro y
    nth_rewrite 1 [← hψfix y]
    abel
  have hright : ∀ x, ψ (x + f x) = x := by
    intro x
    have hfix : Function.IsFixedPt (fun z => (x + f x) - f z) x := by
      show (x + f x) - f x = x
      abel
    have h := ContractingWith.fixedPoint_unique (hT (x + f x)) hfix
    exact h.symm
  have hψcont : Continuous ψ := by
    have hlip : LipschitzWith ((1 - (c : ℝ))⁻¹).toNNReal ψ := by
      apply LipschitzWith.of_dist_le'
      intro y y'
      have hdist : ∀ z : E,
          dist ((fun x => y - f x) z) ((fun x => y' - f x) z) ≤ dist y y' := by
        intro z
        rw [dist_eq_norm, dist_eq_norm]
        have : (y - f z) - (y' - f z) = y - y' := by abel
        rw [this]
      have hmain := ContractingWith.dist_fixedPoint_fixedPoint_of_dist_le' (hT y)
        (fun x => y' - f x) (ContractingWith.fixedPoint_isFixedPt (hT y))
        (ContractingWith.fixedPoint_isFixedPt (hT y')) hdist
      calc dist (ψ y) (ψ y') ≤ dist y y' / (1 - (c : ℝ)) := hmain
        _ = (1 - (c : ℝ))⁻¹ * dist y y' := by rw [div_eq_inv_mul, mul_comm]
    exact hlip.continuous
  have hgcont : Continuous (fun x : E => x + f x) := continuous_id.add hf.continuous
  refine ⟨⟨⟨fun x => x + f x, ψ, hright, hleft⟩, hgcont, hψcont⟩, ?_⟩
  intro x
  rfl

/-- **`dentDeform` is a homeomorphism.**  With `χ` differentiable and `|χ'| ≤ κ`, `0 < r`,
`‖d‖ ≤ 1`, `κ > 0` and `|a'|·κ < r`, the map `z ↦ z + a'·χ(‖z − centre‖/r)·d` of a dent is a
homeomorphism of `ℝ³`. -/
theorem dentDeform_homeomorph {χ : ℝ → ℝ} {centre d : LeanEval.KnotTheory.PardonDistortion.R3}
    {r a' κ : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hd : ‖d‖ ≤ 1) (hχdiff : Differentiable ℝ χ)
    (hχb : ∀ t : ℝ, |deriv χ t| ≤ κ) (ha' : |a'| * κ < r) :
    ∃ Φ : LeanEval.KnotTheory.PardonDistortion.R3 ≃ₜ LeanEval.KnotTheory.PardonDistortion.R3,
      ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
        Φ z = Work.Drive.Final.dentDeform χ centre d r a' z := by
  set D : LeanEval.KnotTheory.PardonDistortion.R3 := a' • d with hD
  -- the perturbation is supported in the ball, so its size is `≤ |a'|`
  have hDnorm : ‖D‖ ≤ |a'| := by
    rw [hD, norm_smul]
    calc |a'| * ‖d‖ ≤ |a'| * 1 := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ = |a'| := mul_one _
  -- the Lipschitz constant of the perturbation
  set C : ℝ≥0 := NNReal.mk (κ * ‖D‖ / r)
    (div_nonneg (mul_nonneg hκ.le (norm_nonneg D)) hr.le) with hC
  have hClt : C < 1 := by
    rw [← NNReal.coe_lt_one, hC, NNReal.coe_mk, div_lt_one hr]
    calc κ * ‖D‖ ≤ κ * |a'| := mul_le_mul_of_nonneg_left hDnorm hκ.le
      _ = |a'| * κ := by ring
      _ < r := ha'
  -- `χ` is `κ`-Lipschitz, by the mean value theorem
  have hχlip : LipschitzWith (NNReal.mk κ (le_of_lt hκ)) χ := by
    apply lipschitzWith_of_nnnorm_deriv_le hχdiff
    intro t
    rw [← NNReal.coe_le_coe, NNReal.coe_mk]
    simpa [Real.norm_eq_abs] using hχb t
  have hflip : LipschitzWith C (fun z : LeanEval.KnotTheory.PardonDistortion.R3 => χ (‖z - centre‖ / r) • D) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hC, NNReal.coe_mk]
    rw [dist_eq_norm, dist_eq_norm]
    rw [show χ (‖x - centre‖ / r) • D - χ (‖y - centre‖ / r) • D
        = (χ (‖x - centre‖ / r) - χ (‖y - centre‖ / r)) • D from (sub_smul _ _ _).symm]
    simp only [norm_smul, Real.norm_eq_abs]
    -- `|χ u - χ v| ≤ κ|u - v|`
    have h2 : |χ (‖x - centre‖ / r) - χ (‖y - centre‖ / r)|
        ≤ κ * |‖x - centre‖ / r - ‖y - centre‖ / r| := by
      have h := hχlip.dist_le_mul (‖x - centre‖ / r) (‖y - centre‖ / r)
      rw [Real.dist_eq] at h
      simpa only [Real.dist_eq, NNReal.coe_mk] using h
    -- `|‖x − centre‖/r − ‖y − centre‖/r| ≤ ‖x − y‖/r`
    have h3 : |‖x - centre‖ / r - ‖y - centre‖ / r| ≤ ‖x - y‖ / r := by
      rw [div_sub_div_same, abs_div, abs_of_pos hr]
      have h4 : |‖x - centre‖ - ‖y - centre‖| ≤ ‖x - y‖ := by
        have h := abs_norm_sub_norm_le (x - centre) (y - centre)
        rwa [show (x - centre) - (y - centre) = x - y by abel] at h
      exact div_le_div_of_nonneg_right h4 hr.le
    have h1 : |χ (‖x - centre‖ / r) - χ (‖y - centre‖ / r)| ≤ κ * (‖x - y‖ / r) :=
      calc |χ (‖x - centre‖ / r) - χ (‖y - centre‖ / r)|
          ≤ κ * |‖x - centre‖ / r - ‖y - centre‖ / r| := h2
        _ ≤ κ * (‖x - y‖ / r) := mul_le_mul_of_nonneg_left h3 hκ.le
    calc |χ (‖x - centre‖ / r) - χ (‖y - centre‖ / r)| * ‖D‖
        ≤ (κ * (‖x - y‖ / r)) * ‖D‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg D)
      _ = κ * ‖D‖ / r * ‖x - y‖ := by ring
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph_add_of_lipschitz hflip hClt
  refine ⟨Φ, fun z => ?_⟩
  rw [hΦ z, hD]
  show z + χ (‖z - centre‖ / r) • (a' • d) = z + (a' * χ (‖z - centre‖ / r)) • d
  rw [← smul_comm a' (χ (‖z - centre‖ / r)) d, ← mul_smul]

end

end Work.Drive.Final
