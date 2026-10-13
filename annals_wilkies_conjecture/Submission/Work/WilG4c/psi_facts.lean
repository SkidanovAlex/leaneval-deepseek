/-
  WilG4c — elementary calculus facts about the "rescaler" `ψ` of `hbdd_defs.lean`:

      `ψ u  = 1/2 + u/(2√(1+u²))`,      `dpsi u = 1/(2(1+u²)√(1+u²))`.

  `ψ` is a strictly increasing diffeomorphism `ℝ → (0,1)` with `0 < ψ' ≤ 1/2` and with `ψ'`
  even and decreasing in `|u|`.  These are the hypotheses under which `hbdd` (BNZ Lemma 5.6)
  is applied to `ψ ∘ χ`.
-/
import Mathlib
import Submission.Work.WilG4c.hbdd_defs

set_option autoImplicit false
noncomputable section

namespace Work.WilG4c

open Work.WilkG4c

/-- `ψ` is differentiable everywhere, with derivative the closed form `dpsi`. -/
theorem psi_hasDerivAt (u : ℝ) :
    HasDerivAt Work.WilkG4c.psi (Work.WilkG4c.dpsi u) u := by
  have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
    simpa using hasDerivAt_pow 2 u
  have h1 : HasDerivAt (fun v : ℝ => 1 + v ^ 2) (2 * u) u := hp.const_add 1
  -- derivative of `√(1 + u²)`
  have hsq : HasDerivAt (fun v : ℝ => Real.sqrt (1 + v ^ 2))
      (u / Real.sqrt (1 + u ^ 2)) u := by
    have h2 := (Real.hasDerivAt_sqrt (x := 1 + u ^ 2) (by positivity)).comp u h1
    refine h2.congr_deriv ?_
    field_simp
  have hne : (2 : ℝ) * Real.sqrt (1 + u ^ 2) ≠ 0 := by positivity
  have hmain := (hasDerivAt_const (x := u) (c := (1 / 2 : ℝ))).add
    ((hasDerivAt_id u).div (hsq.const_mul (2 : ℝ)) hne)
  simp only [id_eq] at hmain
  have hv : (0 : ℝ) + (1 * (2 * Real.sqrt (1 + u ^ 2)) - u * (2 * (u / Real.sqrt (1 + u ^ 2)))) /
      (2 * Real.sqrt (1 + u ^ 2)) ^ 2 = Work.WilkG4c.dpsi u := by
    rw [Work.WilkG4c.dpsi]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
    ring
  rw [hv] at hmain
  exact hmain

/-- `ψ` takes values in the open unit interval. -/
theorem psi_mem_Ioo_one (u : ℝ) : Work.WilkG4c.psi u ∈ Set.Ioo (0 : ℝ) 1 := by
  have hlt : |u| < Real.sqrt (1 + u ^ 2) := by
    rw [Real.lt_sqrt (x := |u|) (y := 1 + u ^ 2) (abs_nonneg u)]
    rw [sq_abs]
    linarith
  have hu : u < Real.sqrt (1 + u ^ 2) := lt_of_le_of_lt (le_abs_self u) hlt
  have hnu : -u < Real.sqrt (1 + u ^ 2) := lt_of_le_of_lt (neg_le_abs u) hlt
  have heq : (1 : ℝ) / 2 + u / (2 * Real.sqrt (1 + u ^ 2))
      = (Real.sqrt (1 + u ^ 2) + u) / (2 * Real.sqrt (1 + u ^ 2)) := by
    field_simp
  rw [Work.WilkG4c.psi, Set.mem_Ioo, heq]
  constructor
  · exact div_pos (by linarith) (by positivity)
  · rw [div_lt_one (by positivity)]
    linarith

/-- `ψ' = dpsi` is strictly positive. -/
theorem dpsi_pos_of_psi (u : ℝ) : 0 < Work.WilkG4c.dpsi u := by
  rw [Work.WilkG4c.dpsi]
  positivity

/-- `ψ' = dpsi` is bounded above by `1/2`. -/
theorem dpsi_le_half (u : ℝ) : Work.WilkG4c.dpsi u ≤ 1 / 2 := by
  have hAs : (2 : ℝ) * (1 + u ^ 2) * Real.sqrt (1 + u ^ 2)
      = 2 * ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) := by ring
  have h1 : (1 : ℝ) ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg u]
  have h2 : (1 : ℝ) ≤ Real.sqrt (1 + u ^ 2) := Real.one_le_sqrt.mpr h1
  have h3 : (1 : ℝ) ≤ (1 + u ^ 2) * Real.sqrt (1 + u ^ 2) := by
    have h := mul_le_mul h1 h2 (zero_le_one) (by positivity : (0 : ℝ) ≤ 1 + u ^ 2)
    simpa using h
  rw [Work.WilkG4c.dpsi, hAs]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)

/-- `dpsi` is even and decreasing in `|u|`. -/
theorem dpsi_antitone_abs {C u : ℝ} (hC : 0 ≤ C) (hu : |u| ≤ C) :
    Work.WilkG4c.dpsi C ≤ Work.WilkG4c.dpsi u := by
  have hu2 : u ^ 2 ≤ C ^ 2 := by
    have habs : |u| ≤ |C| := by rwa [abs_of_nonneg hC]
    exact sq_le_sq.mpr habs
  have h1 : 1 + u ^ 2 ≤ 1 + C ^ 2 := by linarith
  have h2 : Real.sqrt (1 + u ^ 2) ≤ Real.sqrt (1 + C ^ 2) := Real.sqrt_le_sqrt h1
  have h34 : (1 + u ^ 2) * Real.sqrt (1 + u ^ 2)
      ≤ (1 + C ^ 2) * Real.sqrt (1 + C ^ 2) :=
    mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
  have h4 : 2 * (1 + u ^ 2) * Real.sqrt (1 + u ^ 2)
      ≤ 2 * (1 + C ^ 2) * Real.sqrt (1 + C ^ 2) := by
    nlinarith [h34]
  rw [Work.WilkG4c.dpsi, Work.WilkG4c.dpsi]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h4

/-- On `ℝ` the Fréchet derivative of `ψ` is multiplication by `ψ'`. -/
theorem psi_fderiv_apply (u w : ℝ) :
    (fderiv ℝ Work.WilkG4c.psi u) w = deriv Work.WilkG4c.psi u * w := by
  have h := psi_hasDerivAt u
  rw [h.hasFDerivAt.fderiv, h.deriv]
  simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]

theorem psi_facts : (∀ u : ℝ, HasDerivAt Work.WilkG4c.psi (Work.WilkG4c.dpsi u) u) ∧
    (∀ u : ℝ, Work.WilkG4c.psi u ∈ Set.Ioo (0 : ℝ) 1) ∧
    (∀ u : ℝ, 0 < Work.WilkG4c.dpsi u) ∧ (∀ u : ℝ, Work.WilkG4c.dpsi u ≤ 1 / 2) ∧
    (∀ C u : ℝ, 0 ≤ C → |u| ≤ C → Work.WilkG4c.dpsi C ≤ Work.WilkG4c.dpsi u) ∧
    (∀ u w : ℝ, (fderiv ℝ Work.WilkG4c.psi u) w = deriv Work.WilkG4c.psi u * w) :=
  ⟨psi_hasDerivAt, psi_mem_Ioo_one, dpsi_pos_of_psi, dpsi_le_half,
    fun _ _ hC hu => dpsi_antitone_abs hC hu, psi_fderiv_apply⟩

end Work.WilG4c
