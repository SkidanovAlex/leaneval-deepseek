import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB7A.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseGateFS

theorem perMode_bounds_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {E : Work.BoseB7.Q3Env Mode} {Cw : ℝ}
    (hCw : 0 ≤ Cw) (hKH : 0 < E.KH) (ha : 0 < E.aScat) (hKHa : 1 ≤ E.KH * E.aScat)
    (hrho0 : 0 ≤ E.rho)
    (hW1le : ∀ k : Mode, |E.W1 k| ≤ Cw * E.aScat)
    (hB : ∀ k : Mode, E.B k = E.rho * E.W1 k)
    (hAge : ∀ q : Mode, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 2 ≤ E.A q)
    (hAB : ∀ q : Mode, F.PHq E.KH E.aScat q → 2 * |E.B q| ≤ E.A q) :
    (∀ q : Mode, F.PHq E.KH E.aScat q →
        1 / (32 * (E.KH * E.aScat) ^ 2) ≤ E.A q)
      ∧ (∀ q : Mode, F.PHq E.KH E.aScat q →
          |E.B q| / E.A q ≤ 32 * (E.KH * E.aScat) ^ 2 * (E.rho * (Cw * E.aScat)))
      ∧ (∀ p q : Mode, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
          1 / max (E.A p) (E.A q) ≤ 32 * (E.KH * E.aScat) ^ 2)
      ∧ (∀ p q : Mode, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
          1 / max ‖F.kmom p‖ ‖F.kmom q‖ ≤ 4 * (E.KH * E.aScat)) := by
  -- `K_H a ≥ 1 > 0`
  have hKHa_pos : 0 < E.KH * E.aScat := lt_of_lt_of_le zero_lt_one hKHa
  -- the two positive constants of the statement
  have hc : 0 < 1 / (4 * E.KH * E.aScat) := by
    apply one_div_pos.mpr; nlinarith [hKH, ha]
  have hA0 : 0 < 1 / (32 * (E.KH * E.aScat) ^ 2) := by
    apply one_div_pos.mpr; nlinarith [pow_pos hKHa_pos 2]
  -- `(1/(4K_Ha))²/2 = 1/(32 (K_Ha)²)`
  have hkey : (1 / (4 * E.KH * E.aScat)) ^ 2 / 2 = 1 / (32 * (E.KH * E.aScat) ^ 2) := by
    field_simp
    ring
  -- **(1)** `A q ≥ 1/(32(K_Ha)²)` on `PHq`, from `PHq : 1/(4K_Ha) ≤ ‖k_q‖` and
  -- `A q ≥ ‖k_q‖²/2`
  have hAge_le : ∀ q : Mode, F.PHq E.KH E.aScat q →
      1 / (32 * (E.KH * E.aScat) ^ 2) ≤ E.A q := by
    intro q hq
    have hsq : (1 / (4 * E.KH * E.aScat)) ^ 2 ≤ ‖F.kmom q‖ ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hc) hq 2
    have h2 : (1 / (4 * E.KH * E.aScat)) ^ 2 / 2 ≤ E.A q := by
      have := hAge q hq; linarith
    rwa [hkey] at h2
  refine ⟨hAge_le, ?_, ?_, ?_⟩
  -- **(2)** `|B q|/A q ≤ 32(K_Ha)²·ρ C_w a`
  · intro q hq
    have hB_abs : |E.B q| = E.rho * |E.W1 q| := by
      rw [hB q, abs_mul, abs_of_nonneg hrho0]
    have hB_le : |E.B q| ≤ E.rho * (Cw * E.aScat) := by
      rw [hB_abs]; exact mul_le_mul_of_nonneg_left (hW1le q) hrho0
    have hAc : 0 ≤ E.rho * (Cw * E.aScat) :=
      mul_nonneg hrho0 (mul_nonneg hCw (le_of_lt ha))
    have hstep := div_le_div₀ hAc hB_le hA0 (hAge_le q hq)
    have hfin : (E.rho * (Cw * E.aScat)) / (1 / (32 * (E.KH * E.aScat) ^ 2))
        = 32 * (E.KH * E.aScat) ^ 2 * (E.rho * (Cw * E.aScat)) := by
      rw [one_div, div_inv_eq_mul]
      ring
    rwa [hfin] at hstep
  -- **(3)** `1/max (A p) (A q) ≤ 32(K_Ha)²`
  · intro p q hp hq
    have hmax : (1 / (32 * (E.KH * E.aScat) ^ 2)) ≤ max (E.A p) (E.A q) :=
      le_trans (hAge_le p hp) (le_max_left _ _)
    have hstep := one_div_le_one_div_of_le hA0 hmax
    simpa [one_div_one_div] using hstep
  -- **(4)** `1/max ‖k_p‖ ‖k_q‖ ≤ 4 K_H a`
  · intro p q hp hq
    have hmax : (1 / (4 * E.KH * E.aScat)) ≤ max ‖F.kmom p‖ ‖F.kmom q‖ :=
      le_trans hp (le_max_left _ _)
    have hstep := one_div_le_one_div_of_le hc hmax
    simpa [one_div_one_div, mul_assoc] using hstep

end Work.BoseGateFS
