import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.Statements
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.Assembly` — the assembly of `thm:Control3Q` (node `N6`)

Two results:

* `control3QA_of_estimates` — the *pure algebra* of FS's "Theorem
  `thm:Control3Q` follows by adding the estimates of `lem:EstimatesOnQ3-js`":
  the three estimate inequalities, the splitting `Q₃ = Σ Q₃⁽ʲ⁾`, the
  monotonicity of `∫_R 𝒟_k b_k†b_k dk` in `R` and the non-negativity of the gap
  word give the target inequality with the error `e1+e23+e4`.
  (This is the design's `control3QA_of_estimates`, Appendix A.)

* `control3QA_of_three` — the same with the estimates taken in their `Prop` form
  (`EstQ3oneA`, `EstQ3twoThreeA`, `EstQ3fourA`), i.e.
  **`Control3QA` holds with the *single* absolute constant `1` and a threshold
  which is the minimum of the four thresholds**.  This is the theorem a caller
  uses: it reduces `thm:Control3Q` to the three `Prop`s plus the arithmetic
  (`ErrALe`) plus the preparation bundle (`SplitQ3A`).

## The operator identity behind the addition

Writing `𝒟R` for `dNumOpR E R = Σ_{k∈R} 𝒟_k b_k†b_k`, `PH = P_H`,
`PHq = P_H^q ⊇ PH ⊇ all` and dropping the mode arguments, the three estimates
carry

* `Q₃⁽¹⁾ + (1−𝓁²)𝒟PH + (𝓁²/2)𝒟PHq + Q₂^ex + (b/100)gap`,
* `Q₃⁽²⁾ + Q₃⁽³⁾ + (𝓁²/2)𝒟PHq`,
* `Q₃⁽⁴⁾ + linOp + ((b/100)ℓ⁻²)n₊`,

so their sum is `Q₃ + (1−𝓁²)𝒟PH + 𝓁²𝒟PHq + Q₂^ex + linOp + (b/100)gap +
((b/100)ℓ⁻²)n₊`, while the target `controlWordT` is
`𝒟all + Q₃ + Q₂^ex + linOp + (b/50)gap`.  Since
`(b/50)gap − (b/100)gap − ((b/100)ℓ⁻²)n₊ = ((b/100)ε_T(dℓ)⁻²)n₊^H` and

`𝒟all − (1−𝓁²)𝒟PH − 𝓁²𝒟PHq = (𝒟all − 𝒟PHq) + (1−𝓁²)(𝒟PHq − 𝒟PH)`,

the difference of the two words is the sum of the three non-negative forms

`(𝒟all − 𝒟PHq)`, `(1−𝓁²)(𝒟PHq − 𝒟PH)`, `((b/100)ε_T(dℓ)⁻²)n₊^H`,

each non-negative by `dNumOpR_mono` (twice, with `PH ⊆ PHq ⊆ all`), `𝓁² ≤ 1` and
`T.NH_nonneg`.

## Universes

The statements are written at *fixed* universes: `EstQ3oneA.{u, v}` etc., with
`u` the universe of the mode group and `v` that of the Fock space.  A caller with
`Mode : Type`, `H : Type` uses `u = v = 0`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7

universe u v

/-- **The assembly of `thm:Control3Q` from the three estimates** (node `N6`,
pure operator algebra).  This is the design's `control3QA_of_estimates`: no
window hypothesis (it is consumed by the estimates), and the three estimate
hypotheses are taken at one fixed state `Φ`.

* `hsplit` — FS `lem:EstimatesOnQ3-js`, the splitting `Q₃ = Σ_j Q₃⁽ʲ⁾`;
* `hKa` — `K_H a > 0` (for `P_H ⊆ P_H^q`);
* `hD` — `|ℬ_k| ≤ 𝒜_k`, i.e. `𝒟_k ≥ 0` (so that `dNumOpR` is monotone);
* `hl` — `𝓁² ≤ 1`; `hb` — `b ≥ 0`; `heT` — `ε_T ≥ 0`. -/
theorem control3QA_of_estimates {Mode : Type u} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData.{u, v} Mode) (T : TildeData.{u, v} F)
    (E : Q3Env.{u} Mode) (Φ : F.H) (e1 e23 e4 : ℝ)
    (hsplit : T.Q3T E = T.Q3oneT E + T.Q3twoT E + T.Q3threeT E + T.Q3fourT E)
    (hKa : 0 < E.KH * E.aScat) (hD : ∀ k, |E.B k| ≤ E.A k) (hl : E.lille ^ 2 ≤ 1)
    (hb : 0 ≤ E.b) (heT : 0 ≤ E.eT)
    (h1 : -e1 * F.normSq Φ ≤ F.qw Φ (T.Q3oneT E + (1 - E.lille ^ 2) • F.dNumOpR E (F.PH E.KH E.aScat) +
              (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat) + F.Q2ex E +
              (E.b / 100) • T.gapOpT E))
    (h23 : -e23 * F.normSq Φ ≤ F.qw Φ (T.Q3twoT E + T.Q3threeT E +
              (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat)))
    (h4 : -e4 * F.normSq Φ ≤
            F.qw Φ (T.Q3fourT E + T.linOpT E + (E.b / 100 * E.ell ^ (-(2 : ℝ))) • T.N)) :
    -(e1 + e23 + e4) * F.normSq Φ ≤ F.qw Φ (T.controlWordT E) := by
  -- `𝒟_k ≥ 0` from `|ℬ_k| ≤ 𝒜_k`
  have hDn : ∀ i : Mode, 0 ≤ E.D i := fun i =>
    FockData.Dcoef_nonneg (by linarith [hD i, abs_nonneg (E.B i)])
  -- the region inclusion `P_H ⊆ P_H^q`
  have hPHq : ∀ i : Mode, F.PH E.KH E.aScat i → F.PHq E.KH E.aScat i := by
    intro i hi
    have hle : 1 / (4 * E.KH * E.aScat) ≤ 1 / (2 * E.KH * E.aScat) := by
      have h := one_div_le_one_div_of_le (a := 2 * (E.KH * E.aScat)) (b := 4 * (E.KH * E.aScat))
        (by nlinarith [hKa]) (by nlinarith [hKa])
      simpa only [mul_assoc] using h
    have h2 : F.PH E.KH E.aScat i = (1 / (2 * E.KH * E.aScat) ≤ ‖F.kmom i‖) := rfl
    have h4 : F.PHq E.KH E.aScat i = (1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom i‖) := rfl
    rw [h2] at hi
    rw [h4]
    linarith
  -- (i) the sum of the three estimates, at the level of quadratic forms
  have hsum : -((e1 + e23 + e4) * F.normSq Φ) ≤
      F.qw Φ ((T.Q3oneT E + (1 - E.lille ^ 2) • F.dNumOpR E (F.PH E.KH E.aScat) +
            (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat) + F.Q2ex E +
            (E.b / 100) • T.gapOpT E) +
          (T.Q3twoT E + T.Q3threeT E + (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat)) +
          (T.Q3fourT E + T.linOpT E + (E.b / 100 * E.ell ^ (-(2 : ℝ))) • T.N)) := by
    simp only [FockData.qw_add] at h1 h23 h4 ⊢
    nlinarith [h1, h23, h4]
  -- (ii) the three corrections have non-negative quadratic form
  have hB1 : 0 ≤ F.qw Φ (F.dNumOpR E (fun _ => True) - F.dNumOpR E (F.PHq E.KH E.aScat)) := by
    have hm := dNumOpR_mono F E (R := F.PHq E.KH E.aScat) (R' := fun _ => True)
      (fun _ _ => trivial) hDn Φ
    simp only [FockData.qw, LinearMap.sub_apply, map_sub]
    linarith
  have hB2 : 0 ≤ F.qw Φ ((1 - E.lille ^ 2) •
      (F.dNumOpR E (F.PHq E.KH E.aScat) - F.dNumOpR E (F.PH E.KH E.aScat))) := by
    have hm := dNumOpR_mono F E (R := F.PH E.KH E.aScat) (R' := F.PHq E.KH E.aScat)
      hPHq hDn Φ
    simp only [FockData.qw, LinearMap.sub_apply, map_sub, LinearMap.smul_apply, map_smul,
      smul_eq_mul]
    nlinarith [hm, hl]
  have hB3 : 0 ≤ F.qw Φ (((E.b / 100) * E.eT * (E.d * E.ell) ^ (-(2 : ℝ))) • T.NH) := by
    have hnn := T.NH_nonneg Φ
    have hc : 0 ≤ (E.b / 100) * E.eT * (E.d * E.ell) ^ (-(2 : ℝ)) :=
      mul_nonneg (mul_nonneg (div_nonneg hb (by norm_num)) heT)
        (Work.BoseB7.rpow_neg_two_nonneg _)
    simp only [FockData.qw, LinearMap.smul_apply, map_smul, smul_eq_mul]
    exact mul_nonneg hc hnn
  have hC : 0 ≤ F.qw Φ
      ((F.dNumOpR E (fun _ => True) - F.dNumOpR E (F.PHq E.KH E.aScat)) +
        ((1 - E.lille ^ 2) •
          (F.dNumOpR E (F.PHq E.KH E.aScat) - F.dNumOpR E (F.PH E.KH E.aScat))) +
        (((E.b / 100) * E.eT * (E.d * E.ell) ^ (-(2 : ℝ))) • T.NH)) := by
    simp only [FockData.qw_add]
    linarith
  -- (iii) the target word is the sum plus the correction
  have hkey : T.controlWordT E =
      ((T.Q3oneT E + (1 - E.lille ^ 2) • F.dNumOpR E (F.PH E.KH E.aScat) +
            (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat) + F.Q2ex E +
            (E.b / 100) • T.gapOpT E) +
          (T.Q3twoT E + T.Q3threeT E + (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat)) +
          (T.Q3fourT E + T.linOpT E + (E.b / 100 * E.ell ^ (-(2 : ℝ))) • T.N)) +
        ((F.dNumOpR E (fun _ => True) - F.dNumOpR E (F.PHq E.KH E.aScat)) +
          ((1 - E.lille ^ 2) •
            (F.dNumOpR E (F.PHq E.KH E.aScat) - F.dNumOpR E (F.PH E.KH E.aScat))) +
          (((E.b / 100) * E.eT * (E.d * E.ell) ^ (-(2 : ℝ))) • T.NH)) := by
    simp only [TildeData.controlWordT, TildeData.gapOpT, TildeData.linOpT]
    rw [hsplit]
    ext f
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
    module
  -- (iv) hence the same sum is a lower bound for the target form
  have hup : F.qw Φ
      ((T.Q3oneT E + (1 - E.lille ^ 2) • F.dNumOpR E (F.PH E.KH E.aScat) +
            (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat) + F.Q2ex E +
            (E.b / 100) • T.gapOpT E) +
          (T.Q3twoT E + T.Q3threeT E + (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat)) +
          (T.Q3fourT E + T.linOpT E + (E.b / 100 * E.ell ^ (-(2 : ℝ))) • T.N)) ≤
      F.qw Φ (T.controlWordT E) := by
    rw [hkey]
    simp only [FockData.qw_add]
    linarith
  linarith [hsum, hup]

/-- **The final assembly: the three `Prop`-valued estimates give
`thm:Control3Q`** with the absolute constant `1` and a threshold which is the
minimum of the four thresholds.  The preparation facts (`SplitQ3A`: the split
and `𝓁² ≤ 1`) and the arithmetic (`ErrALe`) are the only further inputs; both are
proved elsewhere in this subproject. -/
theorem control3QA_of_three (K₀ b₀ : ℝ) (hb₀ : 0 < b₀)
    (hspl : SplitQ3A.{u, v} K₀ b₀ hb₀) (h1 : EstQ3oneA.{u, v} K₀ b₀ hb₀)
    (h23 : EstQ3twoThreeA.{u, v} K₀ b₀ hb₀) (h4 : EstQ3fourA.{u, v} K₀ b₀ hb₀)
    (hErr : ∀ C₁ C₂₃ C₄ : ℝ, ErrALe.{u} b₀ hb₀ C₁ C₂₃ C₄) :
    Control3QA.{u, v} K₀ b₀ hb₀ := by
  obtain ⟨C1, t1, _, ht1, H1⟩ := h1
  obtain ⟨C23, t23, _, ht23, H23⟩ := h23
  obtain ⟨C4, t4, _, ht4, H4⟩ := h4
  obtain ⟨tE, htE, HE⟩ := hErr C1 C23 C4
  refine ⟨1, min (min (min hspl.t₀ t1) (min t23 t4)) tE, zero_le_one, ?_, ?_⟩
  · exact lt_min (lt_min (lt_min hspl.t₀_pos ht1) (lt_min ht23 ht4)) htE
  intro Mode instAC instF instD F T E hv ht hb hK Φ hΦ
  have hA : hv.t ≤ min (min hspl.t₀ t1) (min t23 t4) := le_trans ht (min_le_left _ _)
  have htE' : hv.t ≤ tE := le_trans ht (min_le_right _ _)
  have hB1' : hv.t ≤ min hspl.t₀ t1 := le_trans hA (min_le_left _ _)
  have hB2' : hv.t ≤ min t23 t4 := le_trans hA (min_le_right _ _)
  have htspl : hv.t ≤ hspl.t₀ := le_trans hB1' (min_le_left _ _)
  have ht1' : hv.t ≤ t1 := le_trans hB1' (min_le_right _ _)
  have ht23' : hv.t ≤ t23 := le_trans hB2' (min_le_left _ _)
  have ht4' : hv.t ≤ t4 := le_trans hB2' (min_le_right _ _)
  have ha : 0 < E.aScat := hv.a_pos
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have heT : 0 ≤ E.eT := by
    rw [hv.eT_eq]
    exact Work.BoseBox.fsXp_nonneg hv.t_pos.le
  have hb' : 0 ≤ E.b := le_trans (le_of_lt hb₀) hb
  have hmain := control3QA_of_estimates F T E Φ (C1 * e1A E) (C23 * e23A E) (C4 * e4A E)
    (hspl.split F T E hv htspl hb hK) (mul_pos hKH ha) hK.AB
    (hspl.lille_sq_le_one E hv htspl) hb' heT
    (H1 F T E hv ht1' hb hK Φ hΦ) (H23 F T E hv ht23' hb hK Φ hΦ)
    (H4 F T E hv ht4' hb hK Φ hΦ)
  have hle : (C1 * e1A E) + (C23 * e23A E) + (C4 * e4A E) ≤ controlErrA E :=
    HE E hv htE' hb
  have hn : 0 ≤ F.normSq Φ := FockData.normSq_nonneg F Φ
  nlinarith [hmain, hle, hn]

end Work.BoseB7A
