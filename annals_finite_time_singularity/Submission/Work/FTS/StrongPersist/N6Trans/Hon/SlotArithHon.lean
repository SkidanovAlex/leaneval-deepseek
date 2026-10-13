/-
Copyright: work module for the Elgindi finite-time singularity project.

The `N6Trans/Hon` layer: the honest (`SmoothOpen`-based) form of the level-4 transport clauses.

The pieces are split over four small modules (the build guard refuses files above 30 KB):

* `Hon/Defs` — the honest bundles, the honest sup bound `pwAny_sup`, the abstract vanishing
  `prim_limit_zero`, and the two `Prop`s (`TopSlotHonProp`, `DelicateHonProp`);
* `Hon/SmainHon` — the `Smain` summand (top slot from `TopSlotHonProp`);
* `Hon/DelicateMargIntHon`, `Hon/SdelMargIntDelicateHon` — the delicate marginal integrability;
* `Hon/SlotArithHon` — the arithmetic of the final constant;
* `Hon/SdelGamHon` — the `Sdel` summand at `q = γ`;
* `Hon/SlotAbsHon` — the honest per-slot engine `slotAbsBound_hon`.
-/
import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false

/-- The arithmetic of the final constant in the honest shape: the frozen `slot_arith` with the
honest `Smain` constant `Csm` (only `0 ≤ Csm` is used) in place of `2`. -/
theorem slot_arith_hon {r Xf Kf Xg Cs Cl Cg Cd Csm : ℝ}
    (hr1 : 1 ≤ r) (hr0 : 0 ≤ r) (hXf : 0 ≤ Xf) (hKf : 0 ≤ Kf) (hXg : 0 ≤ Xg)
    (hCs : 0 ≤ Cs) (hCl : 0 ≤ Cl) (hCg : 0 ≤ Cg) (hCd : 0 ≤ Cd) (hCsm : 0 ≤ Csm)
    (h10 : Real.sqrt 10 ≤ 10) :
    Csm * (Cs * (Real.sqrt 10 * r) * Xf) * Xg ^ 2
      + (6400 * ((Cs * (Real.sqrt 10 * r) * Xf + Cl * Kf) * Xg ^ 2
          + Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
        + (16 * ((Cs * (Real.sqrt 10 * r) * Xf + Cl * Kf) * Xg ^ 2
            + Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
          + Cd * r * (Xf + Kf) * Xg ^ 2))
      ≤ (11 * Csm + 10 ^ 8) * (Cs + Cl + Cg + Cd + 1) * r * (Xf + Kf) * Xg ^ 2 := by
  have hsq : (0 : ℝ) ≤ Xg ^ 2 := sq_nonneg Xg
  have hsq10 : (0 : ℝ) ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  set T : ℝ := r * (Xf + Kf) * Xg ^ 2 with hTdef
  have hT : 0 ≤ T := by rw [hTdef]; positivity
  have h1 : r * Xf * Xg ^ 2 ≤ T := by
    rw [hTdef]; nlinarith [mul_nonneg hr0 (mul_nonneg hKf hsq)]
  have h3 : Kf * Xg ^ 2 ≤ T := by
    rw [hTdef]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r - 1) (mul_nonneg hKf hsq),
      mul_nonneg hr0 (mul_nonneg hXf hsq), mul_nonneg hKf hsq]
  have H1 : Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2 ≤ 10 * Cs * T := by
    rw [show Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2
        = Cs * Real.sqrt 10 * (r * Xf * Xg ^ 2) by ring]
    calc Cs * Real.sqrt 10 * (r * Xf * Xg ^ 2)
        ≤ Cs * Real.sqrt 10 * T := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCs hsq10)
      _ ≤ 10 * Cs * T := by
          have hc : Cs * Real.sqrt 10 ≤ 10 * Cs := by nlinarith [hCs, h10]
          exact mul_le_mul_of_nonneg_right hc hT
  have H2 : Cl * Kf * Xg ^ 2 ≤ Cl * T := by
    rw [show Cl * Kf * Xg ^ 2 = Cl * (Kf * Xg ^ 2) by ring]
    exact mul_le_mul_of_nonneg_left h3 hCl
  have H3 : Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg) ≤ 10 * Cg * T := by
    rw [show Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg)
        = Cg * Real.sqrt 10 * (r * Xf * Xg ^ 2) by ring]
    calc Cg * Real.sqrt 10 * (r * Xf * Xg ^ 2)
        ≤ Cg * Real.sqrt 10 * T := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCg hsq10)
      _ ≤ 10 * Cg * T := by
          have hc : Cg * Real.sqrt 10 ≤ 10 * Cg := by nlinarith [hCg, h10]
          exact mul_le_mul_of_nonneg_right hc hT
  have H4 : Cd * r * (Xf + Kf) * Xg ^ 2 = Cd * T := by rw [hTdef]; ring
  have H0 : Csm * (Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2) ≤ 11 * Csm * (Cs * T) :=
    le_trans (mul_le_mul_of_nonneg_left H1 hCsm)
      (by nlinarith [mul_nonneg hCsm (mul_nonneg hCs hT)])
  have hLHS : Csm * (Cs * (Real.sqrt 10 * r) * Xf) * Xg ^ 2
      + (6400 * ((Cs * (Real.sqrt 10 * r) * Xf + Cl * Kf) * Xg ^ 2
          + Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
        + (16 * ((Cs * (Real.sqrt 10 * r) * Xf + Cl * Kf) * Xg ^ 2
            + Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
          + Cd * r * (Xf + Kf) * Xg ^ 2))
      = Csm * (Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2)
        + (6400 * (Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2)
          + (6400 * (Cl * Kf * Xg ^ 2)
            + (6400 * (Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
              + (16 * (Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2)
                + (16 * (Cl * Kf * Xg ^ 2)
                  + (16 * (Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
                    + Cd * r * (Xf + Kf) * Xg ^ 2)))))) := by ring
  rw [hLHS, H4]
  have hSum : (0 : ℝ) ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  have hSumT : 0 ≤ (Cs + Cl + Cg + Cd + 1) * T := mul_nonneg hSum hT
  have hCsSum : Cs ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  have hClSum : Cl ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  have hCgSum : Cg ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  have hCdSum : Cd ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  nlinarith [H0, H1, H2, H3, hT, hSum, hSumT, hCsm, hCs, hCl, hCg, hCd, hXg,
    mul_le_mul_of_nonneg_left hCsSum hT, mul_le_mul_of_nonneg_left hClSum hT,
    mul_le_mul_of_nonneg_left hCgSum hT, mul_le_mul_of_nonneg_left hCdSum hT]

end Work.FTS.StrongPersist.N6Trans.Hon
