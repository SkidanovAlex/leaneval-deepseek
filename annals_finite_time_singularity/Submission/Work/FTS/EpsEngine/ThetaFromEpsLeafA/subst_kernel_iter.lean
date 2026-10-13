import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst
import Submission.Work.FTS.StrongEps.EpsLocalPStar.Jker_shift_logsubst

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafA

open MeasureTheory

/-- The reflection `x ↦ c - x` does not change the Lebesgue `lintegral` on `ℝ`: it is the
composition of the translation `x ↦ x + c` (invariance: `lintegral_add_right_eq_self`) with the
negation `x ↦ -x` (invariance: `lintegral_neg_eq_self`). -/
private lemma lintegral_add_neg_eq_self (F : ℝ → ENNReal) (c : ℝ) :
    (∫⁻ s, F (c + -s)) = ∫⁻ s, F s := by
  rw [MeasureTheory.lintegral_neg_eq_self (fun y => F (c + y))]
  rw [show (∫⁻ s, F (c + s)) = ∫⁻ s, F (s + c) from
    MeasureTheory.lintegral_congr (fun s => by rw [add_comm])]
  exact MeasureTheory.lintegral_add_right_eq_self F c

/-- The two-dimensional form of the previous lemma. -/
private lemma lintegral_prod_neg_sub (F : ℝ → ℝ → ENNReal) (c d : ℝ) :
    (∫⁻ s, ∫⁻ ζ, F (c - s) (d - ζ)) = ∫⁻ s, ∫⁻ ζ, F s ζ := by
  have hinner : ∀ s, (∫⁻ ζ, F (c - s) (d - ζ)) = ∫⁻ ζ, F (c - s) ζ := by
    intro s
    simpa only [sub_eq_add_neg] using lintegral_add_neg_eq_self (fun ζ => F (c - s) ζ) d
  rw [MeasureTheory.lintegral_congr hinner]
  simpa only [sub_eq_add_neg] using lintegral_add_neg_eq_self (fun s => ∫⁻ ζ, F s ζ) c

/-- The angular Jacobian identity behind the log-coordinate substitution: the derivative of
`θ ↦ log tan θ` is `2 / sin (2θ)`, and in the coordinate `ζ = log tan θ` (`θ = arctan (e^ζ)`)
this reads `sin (2 · arctan (e^ζ)) = 2 · kappa ζ`, where `kappa ζ = e^ζ/(1 + e^{2ζ})` is the
derivative of `ζ ↦ arctan (e^ζ)`. -/
private lemma sin_two_arctan_exp (ζ : ℝ) :
    Real.sin (2 * Real.arctan (Real.exp ζ)) = 2 * Work.FTS.StrongEps.HkSqAux.kappa ζ := by
  have hpos : 0 < 1 + (Real.exp ζ) ^ 2 := by positivity
  have hsq : (Real.sqrt (1 + (Real.exp ζ) ^ 2)) ^ 2 = 1 + Real.exp (2 * ζ) := by
    rw [Real.sq_sqrt hpos.le]
    congr 1
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan, Work.FTS.StrongEps.HkSqAux.kappa,
    div_eq_mul_inv, div_eq_mul_inv, ← hsq]
  have hne : Real.sqrt (1 + (Real.exp ζ) ^ 2) ≠ 0 := by positivity
  field_simp

/-- The Jacobian of the log-coordinate substitution `(z, θ) ↦ (log z, log tan θ)` cancels the
weight `2 / (z sin 2θ)` of the quadrant integral. -/
private lemma logJac_mul_weight (s ζ : ℝ) :
    Work.FTS.StrongEps.HkSqAux.logJac s ζ
      * (2 / (Real.exp s * Real.sin (2 * Real.arctan (Real.exp ζ)))) = 1 := by
  rw [Work.FTS.StrongEps.HkSqAux.logJac, sin_two_arctan_exp, div_eq_mul_inv]
  have hk0 : Work.FTS.StrongEps.HkSqAux.kappa ζ ≠ 0 :=
    ne_of_gt (Work.FTS.StrongEps.HkSqAux.kappa_pos ζ)
  have he : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  field_simp

/-- **The log-coordinate substitution for an arbitrary kernel.** For an arbitrary
`ENNReal`-valued kernel `K` (no measurability or integrability hypothesis) and an arbitrary
`ENNReal`-valued `Ψ`, the iterated integral of `Ψ (zShift z s) (thShift θ ζ)` against `K` over
the plane equals the iterated integral over the quadrant `(0,∞) × (0,π/2)` of `Ψ` against the
reflected kernel `K (log z - log z', log tan θ - log tan θ')`, with the Jacobian weight of the
change of variables `z' = e^s`, `θ' = arctan (e^ζ)` and the measure preserving reflection
`(s, ζ) ↦ (log z - s, log tan θ - ζ)`.

Both sides are `ENNReal`-valued, so no measurability or finiteness hypothesis is required: the
identity is a pure change of variables (the two one-dimensional substitutions
`lintegral_exp_subst_gen`, `lintegral_arctan_exp_subst_gen` and the invariances of the Lebesgue
measure under translation and negation). -/
theorem subst_kernel_iter {K : ℝ × ℝ → ENNReal} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (Ψ : ℝ → ℝ → ENNReal) :
    (∫⁻ s, ∫⁻ ζ, K (s, ζ)
        * Ψ (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ ζ))
      = ∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
          K (Real.log z - Real.log z', Real.log (Real.tan θ) - Real.log (Real.tan θ'))
            * Ψ z' θ' * ENNReal.ofReal (2 / (z' * Real.sin (2 * θ'))) := by
  -- **Step 1.** the log-coordinate substitution `z' = e^s`, `θ' = arctan (e^ζ)` applied to the
  -- quadrant integral, with Jacobian `logJac s ζ = e^s · kappa ζ`.
  have hfirst : (∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
          K (Real.log z - Real.log z', Real.log (Real.tan θ) - Real.log (Real.tan θ'))
            * Ψ z' θ' * ENNReal.ofReal (2 / (z' * Real.sin (2 * θ'))))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * (K (Real.log z - Real.log (Real.exp s),
                Real.log (Real.tan θ) - Real.log (Real.tan (Real.arctan (Real.exp ζ))))
              * Ψ (Real.exp s) (Real.arctan (Real.exp ζ))
              * ENNReal.ofReal
                  (2 / (Real.exp s * Real.sin (2 * Real.arctan (Real.exp ζ))))) :=
    Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst
      (fun z' θ' => K (Real.log z - Real.log z', Real.log (Real.tan θ) - Real.log (Real.tan θ'))
            * Ψ z' θ' * ENNReal.ofReal (2 / (z' * Real.sin (2 * θ'))))
  -- **Step 2.** the pointwise simplification: `log (e^s) = s`, `log (tan (arctan (e^ζ))) = ζ`
  -- and the Jacobian cancellation.
  have hmiddle : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * (K (Real.log z - Real.log (Real.exp s),
                Real.log (Real.tan θ) - Real.log (Real.tan (Real.arctan (Real.exp ζ))))
              * Ψ (Real.exp s) (Real.arctan (Real.exp ζ))
              * ENNReal.ofReal
                  (2 / (Real.exp s * Real.sin (2 * Real.arctan (Real.exp ζ))))))
      = ∫⁻ s, ∫⁻ ζ, K (Real.log z - s, Real.log (Real.tan θ) - ζ)
            * Ψ (Real.exp s) (Real.arctan (Real.exp ζ)) := by
    refine MeasureTheory.lintegral_congr fun s => MeasureTheory.lintegral_congr fun ζ => ?_
    simp only [Real.log_exp, Real.tan_arctan]
    set X : ENNReal := K (Real.log z - s, Real.log (Real.tan θ) - ζ) with hX
    set P : ENNReal := Ψ (Real.exp s) (Real.arctan (Real.exp ζ)) with hP
    set Y : ENNReal :=
      ENNReal.ofReal (2 / (Real.exp s * Real.sin (2 * Real.arctan (Real.exp ζ)))) with hY
    set Z : ENNReal := ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ) with hZ
    have hw : Z * Y = 1 := by
      rw [hZ, hY, ← ENNReal.ofReal_mul (Work.FTS.StrongEps.HkSqAux.logJac_nonneg s ζ),
        logJac_mul_weight, ENNReal.ofReal_one]
    calc Z * (X * P * Y) = (Z * Y) * (X * P) := by ac_rfl
      _ = 1 * (X * P) := by rw [hw]
      _ = X * P := one_mul _
  -- **Step 3.** the measure preserving reflection `(s, ζ) ↦ (log z - s, log tan θ - ζ)`.
  have hlast : (∫⁻ s, ∫⁻ ζ, K (Real.log z - s, Real.log (Real.tan θ) - ζ)
            * Ψ (Real.exp s) (Real.arctan (Real.exp ζ)))
      = ∫⁻ s, ∫⁻ ζ, K (s, ζ)
        * Ψ (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ ζ) := by
    have hF := lintegral_prod_neg_sub
      (fun a b => K (a, b)
        * Ψ (Real.exp (Real.log z - a))
            (Real.arctan (Real.exp (Real.log (Real.tan θ) - b))))
      (Real.log z) (Real.log (Real.tan θ))
    have h1 : ∀ s : ℝ, Real.exp (Real.log z - s) = z * Real.exp (-s) := fun s => by
      rw [Real.exp_sub, Real.exp_log hz, Real.exp_neg, div_eq_mul_inv]
    have h2 : ∀ ζ : ℝ, Real.exp (Real.log (Real.tan θ) - ζ)
        = Real.tan θ * Real.exp (-ζ) := fun ζ => by
      rw [Real.exp_sub,
        Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2), Real.exp_neg,
        div_eq_mul_inv]
    calc (∫⁻ s, ∫⁻ ζ, K (Real.log z - s, Real.log (Real.tan θ) - ζ)
            * Ψ (Real.exp s) (Real.arctan (Real.exp ζ)))
        = ∫⁻ s, ∫⁻ ζ, (fun a b => K (a, b)
              * Ψ (Real.exp (Real.log z - a))
                  (Real.arctan (Real.exp (Real.log (Real.tan θ) - b))))
              (Real.log z - s) (Real.log (Real.tan θ) - ζ) := by
          refine MeasureTheory.lintegral_congr fun s =>
            MeasureTheory.lintegral_congr fun ζ => ?_
          simp only
          rw [show Real.log z - (Real.log z - s) = s from by ring,
            show Real.log (Real.tan θ) - (Real.log (Real.tan θ) - ζ) = ζ from by ring]
      _ = ∫⁻ s, ∫⁻ ζ, (fun a b => K (a, b)
              * Ψ (Real.exp (Real.log z - a))
                  (Real.arctan (Real.exp (Real.log (Real.tan θ) - b)))) s ζ := hF
      _ = ∫⁻ s, ∫⁻ ζ, K (s, ζ)
            * Ψ (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ ζ) := by
          refine MeasureTheory.lintegral_congr fun s =>
            MeasureTheory.lintegral_congr fun ζ => ?_
          simp only [Work.FTS.StrongEps.zShift, Work.FTS.StrongEps.thShift]
          rw [h1, h2]
  rw [hfirst, hmiddle, hlast]

end Work.FTS.EpsEngine.ThetaFromEpsLeafA
