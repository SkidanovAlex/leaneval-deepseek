import Mathlib
import Submission.Work.C17.lc_defs
import Submission.Work.C17I.subst_eval_abs
import Submission.Work.C17I.sympSym_deriv_coeff_bound
import Submission.Work.C17I.pureB_coeff_bound
import Submission.Work.C17I.seventeen_coeff_bounds

namespace Work.C17I

open PowerSeries

noncomputable section

/-!
# The seventeen substituted series at the safe harbour point `p₀ = 1/4 + i/5`

This file evaluates the composition `f ↦ f.subst sympY` of each of the seventeen series of
Theorem C (`Submission.CDTPlan.seventeen`) at the point `p₀ = Work.C17.p0C`, using
`Work.C17I.subst_eval_abs`: for `f` whose coefficients decay at rate `R = 1/5`
(`Work.C17I.seventeen_coeff_bounds`) and for `g = sympY` with absolute series at radius
`ρ = 33/100` smaller than `1/5`, the substituted series converges at `p₀` to the `tsum` of the
`y`-series evaluated at `yC p₀`.

The auxiliary facts about `sympY = x²/(x-1) = -x² - x³ - …` used here are the explicit
coefficient formula `coeff_n sympY = if n < 2 then 0 else -1` (proved below from the defining
relation `sympPhi · (X-1) = X`), which yields both the geometric HasSum
`Σ_n coeff_n sympY · z^n = yC z` for `‖z‖ < 1` and the value `Σ_n ‖coeff_n sympY‖ ρ^n = ρ²/(1-ρ)`
of the absolute series.
-/

/-- The inverse of `X - 1` in `ℚ⟦X⟧` has all coefficients `-1` (it is `-(1 + X + X² + …)`). -/
private lemma symp_sub_one_inv : ((X : PowerSeries ℚ) - 1)⁻¹ = PowerSeries.mk (fun _ : ℕ => (-1 : ℚ)) := by
  have hX1 : PowerSeries.constantCoeff ((X : PowerSeries ℚ) - 1) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, PowerSeries.coeff_X,
      PowerSeries.coeff_one]
    norm_num
  rw [PowerSeries.inv_eq_iff_mul_eq_one hX1]
  ext k
  rw [mul_sub, mul_one, map_sub,
    show (X : PowerSeries ℚ) = X ^ 1 from (pow_one X).symm,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_one]
  simp only [PowerSeries.coeff_mk]
  by_cases h : 1 ≤ k
  · rw [if_pos h, if_neg (by omega)]
    ring
  · rw [if_neg h, if_pos (by omega)]
    norm_num

/-- The coefficient of the symmetrisation coordinate `sympY = x²/(x-1) = -x² - x³ - …`. -/
lemma sympY_coeff (n : ℕ) : PowerSeries.coeff n Submission.CDT.sympY = if n < 2 then 0 else -1 := by
  have hsy : Submission.CDT.sympY = X ^ 2 * PowerSeries.mk (fun _ : ℕ => (-1 : ℚ)) := by
    unfold Submission.CDT.sympY Submission.CDT.sympPhi
    rw [symp_sub_one_inv]
    ring
  rw [hsy, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk]
  by_cases h : 2 ≤ n
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega)]

/-- The norm of the `n`-th coefficient of `sympY` (as a complex number) is `0` below `2` and `1`
from `2` on. -/
private lemma norm_coeff (n : ℕ) :
    ‖((PowerSeries.coeff n Submission.CDT.sympY : ℚ) : ℂ)‖ = if n < 2 then (0 : ℝ) else 1 := by
  rw [sympY_coeff n]; split_ifs <;> norm_num

/-- The truncated geometric series `Σ_n (if n < 2 then z^n else 0) = 1 + z`. -/
private lemma hasSum_trunc {z : ℂ} : HasSum (fun n : ℕ => if n < 2 then z ^ n else (0 : ℂ)) (1 + z) := by
  have h0 : HasSum (fun n : ℕ => if n = 0 then (1 : ℂ) else 0) 1 := hasSum_ite_eq 0 1
  have h1 : HasSum (fun n : ℕ => if n = 1 then z else (0 : ℂ)) z := hasSum_ite_eq 1 z
  have h := h0.add h1
  have heq : (fun n : ℕ => (if n = 0 then (1 : ℂ) else 0) + (if n = 1 then z else 0))
      = (fun n : ℕ => if n < 2 then z ^ n else 0) := by
    funext k
    by_cases hk : k < 2
    · interval_cases k <;> simp
    · simp only [if_neg hk, if_neg (show ¬ k = 0 by omega), if_neg (show ¬ k = 1 by omega),
        add_zero]
  rw [heq] at h
  exact h

/-- The real version of `hasSum_trunc`. -/
private lemma hasSum_trunc_real {ρ : ℝ} : HasSum (fun n : ℕ => if n < 2 then ρ ^ n else (0 : ℝ)) (1 + ρ) := by
  have h0 : HasSum (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) 1 := hasSum_ite_eq 0 1
  have h1 : HasSum (fun n : ℕ => if n = 1 then ρ else (0 : ℝ)) ρ := hasSum_ite_eq 1 ρ
  have h := h0.add h1
  have heq : (fun n : ℕ => (if n = 0 then (1 : ℝ) else 0) + (if n = 1 then ρ else 0))
      = (fun n : ℕ => if n < 2 then ρ ^ n else 0) := by
    funext k
    by_cases hk : k < 2
    · interval_cases k <;> simp
    · simp only [if_neg hk, if_neg (show ¬ k = 0 by omega), if_neg (show ¬ k = 1 by omega),
        add_zero]
  rw [heq] at h
  exact h

/-- **`sympY` evaluated at `z`.**  For `‖z‖ < 1` the series of `sympY` converges at `z` to
`yC z = z²/(z-1)`: this is `Σ_{n≥2} (-1) z^n = -z²/(1-z)`. -/
lemma sympY_hasSum (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => ((PowerSeries.coeff n Submission.CDT.sympY : ℚ) : ℂ) * z ^ n)
      (Work.C17.yC z) := by
  have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
  have hgeo : HasSum (fun n : ℕ => z ^ n) ((1 - z)⁻¹) := hasSum_geometric_of_norm_lt_one hz
  have hneg : HasSum (fun n : ℕ => -(z ^ n)) (-(1 - z)⁻¹) := hgeo.neg
  have hadd := hneg.add (hasSum_trunc (z := z))
  have hdecomp : ∀ n : ℕ, ((PowerSeries.coeff n Submission.CDT.sympY : ℚ) : ℂ) * z ^ n
      = -(z ^ n) + (if n < 2 then z ^ n else 0) := by
    intro n; rw [sympY_coeff n]; split_ifs <;> norm_num
  have hv : -(1 - z)⁻¹ + (1 + z) = Work.C17.yC z := by
    rw [Work.C17.yC]; field_simp; ring
  rw [hv] at hadd
  exact hadd.congr_fun hdecomp

/-- **The absolute series of `sympY`.**  For `0 ≤ ρ < 1`,
`Σ_n ‖coeff_n sympY‖ ρ^n = ρ²/(1-ρ)` (the terms with `n = 0, 1` vanish). -/
lemma sympY_norm_hasSum {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    HasSum (fun n : ℕ => ‖((PowerSeries.coeff n Submission.CDT.sympY : ℚ) : ℂ)‖ * ρ ^ n)
      (ρ ^ 2 / (1 - ρ)) := by
  have hgeo : HasSum (fun n : ℕ => ρ ^ n) ((1 - ρ)⁻¹) :=
    hasSum_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg hρ0])
  have hsub := hgeo.sub (hasSum_trunc_real (ρ := ρ))
  have hdecomp : ∀ n : ℕ, ‖((PowerSeries.coeff n Submission.CDT.sympY : ℚ) : ℂ)‖ * ρ ^ n
      = ρ ^ n - (if n < 2 then ρ ^ n else 0) := by
    intro n; rw [norm_coeff n]; split_ifs <;> ring
  have hv : (1 - ρ)⁻¹ - (1 + ρ) = ρ ^ 2 / (1 - ρ) := by
    have h : (1 : ℝ) - ρ ≠ 0 := by linarith
    field_simp; ring
  rw [hv] at hsub
  exact hsub.congr_fun hdecomp

/-- Guidance from the requester (area C17, input for `Work.C17.relation_to_LC`).

# The seventeen substituted series at the safe harbour point

`Submission.CDTPlan.seventeen m n ra rb rab r0 : Fin 17 → ℚ⟦y⟧` is the ordered list
`B₁,…,B₅, G, G', G'', G''', B₆, B₇, ∫yG, ∫G, ∫(G-jet₁)/y, … , ∫(G-jet₄)/y⁴`
(with `G = Sym⁺(logP a b ra rb rab r0)`, `a = aOf m = 2m+1`, `b = aOf n`), `sympY ∈ ℚ⟦x⟧` is the
series of `y = x²/(x-1)`, and `p₀ = 1/4 + i/5 = Work.C17.p0C` satisfies `‖p₀‖ ≤ 33/100`
(`Work.C17.norm_p0C_le`, in `Submission.Work.C17.lc_defs`).

The claim: for each of the seventeen entries `f`, the *substituted* series `f.subst sympY`
converges at `p₀` to the value `Σ_k coeff_k(f) · (yC p₀)^k` — i.e. Lean's `HasSum` statement of the
classical composition formula, with the value written as the (possibly non-summable) `tsum` of the
`y`-series.

This is a case analysis using `Work.C17I.subst_eval_abs` (proved): for `f` with
`∀k, ‖coeff_k f‖ · R^k ≤ C` and `g = sympY` with `Σ_k ‖coeff_k sympY‖ ρ^k < R`, `‖z‖ ≤ ρ`,
it gives exactly the displayed `HasSum`.  Take `ρ = 33/100 ≥ ‖p₀‖`; then `sympY = -X²/(1-X)`, so
`‖coeff_k sympY‖ = 0` for `k < 2` and `1` afterwards, whence
`Σ_k ‖coeff_k sympY‖ ρ^k = ρ²/(1-ρ) = 1089/6700 < 1/5`.  The coefficient bounds for the seventeen
entries are `Work.C17I.seventeen_coeff_bounds`, giving directly the hypothesis at rate `R = 1/5`.
The auxiliary `Σ_k coeff_k sympY · z^k = yC z` (needed to identify the value of `subst_eval_abs`)
is `Work.C17I.sympY_hasSum`, and `constantCoeff sympY = 0` is `Submission.CDT.coeff_sympY_zero`.

Helper auxiliary results may be added above the claim; do not change the claim. -/
theorem seventeen_subst_eval (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n) (ra rb rab r0 : ℤ) {C : ℝ} (hC : 0 < C)
    (hP : ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) : ℚ) : ℂ)‖
        ≤ C * (6 / 5 : ℝ) ^ k) :
    ∀ i : Fin 17,
      HasSum (fun k : ℕ =>
          ((PowerSeries.coeff k
            ((Submission.CDTPlan.seventeen m n ra rb rab r0 i).subst Submission.CDT.sympY) : ℚ) : ℂ)
            * Work.C17.p0C ^ k)
        (∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDTPlan.seventeen m n ra rb rab r0 i) : ℚ) : ℂ)
          * (Work.C17.yC Work.C17.p0C) ^ k) := by
  intro i
  obtain ⟨C', hC', hb⟩ := seventeen_coeff_bounds m n ra rb rab r0 hC hP i
  have hz33 : ‖Work.C17.p0C‖ ≤ (33 : ℝ) / 100 := Work.C17.norm_p0C_le
  have hzlt : ‖Work.C17.p0C‖ < 1 := lt_of_le_of_lt hz33 (by norm_num)
  -- the absolute series of `sympY` at radius `33/100` has sum `1089/6700 < 1/5`
  have hsum : HasSum
      (fun k : ℕ => ‖((PowerSeries.coeff k Submission.CDT.sympY : ℚ) : ℂ)‖ * (33 / 100) ^ k)
      (((33 : ℝ) / 100) ^ 2 / (1 - 33 / 100)) := sympY_norm_hasSum (by norm_num) (by norm_num)
  have hgS : Summable
      (fun k : ℕ => ‖((PowerSeries.coeff k Submission.CDT.sympY : ℚ) : ℂ)‖ * (33 / 100) ^ k) :=
    hsum.summable
  have hgR : (∑' k : ℕ,
      ‖((PowerSeries.coeff k Submission.CDT.sympY : ℚ) : ℂ)‖ * (33 / 100) ^ k) < 1 / 5 := by
    rw [hsum.tsum_eq]; norm_num
  have hg0 : PowerSeries.constantCoeff Submission.CDT.sympY = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Submission.CDT.coeff_sympY_zero
  have hkey := Work.C17I.subst_eval_abs
    (f := Submission.CDTPlan.seventeen m n ra rb rab r0 i) (g := Submission.CDT.sympY)
    (C := C') (R := 1 / 5) (ρ := 33 / 100) (z := Work.C17.p0C)
    hC'.le (by norm_num) (by norm_num) hg0 hb hgS hgR hz33
  have hsymp : (∑' m : ℕ, ((PowerSeries.coeff m Submission.CDT.sympY : ℚ) : ℂ) * Work.C17.p0C ^ m)
      = Work.C17.yC Work.C17.p0C := (sympY_hasSum Work.C17.p0C hzlt).tsum_eq
  rw [hsymp] at hkey
  exact hkey

end

end Work.C17I
