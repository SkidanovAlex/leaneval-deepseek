/-
# P9F — the Table 9 assembly (HB numbering argument)

`lam3_of_row`: from the Lemma 9.2 inequality (`hcore`, available for every admissible pair
`(χj, ρj)`) together with the numerical contradiction at the tabulated point `(a, c)`
(`hcontra`), we deduce `Lam3Bound χ₁ c` for a pair `(χ₁, ρ₁)` with `λ₁ ≤ a`.

The argument is Heath-Brown's: if the conclusion failed, there would be a bad pair `(χ_b, ρ_b)`
with `χ_b ∉ {χ₁^{±1}}`; taking `χ₂ := χ_b`, a second bad pair `(χ, ρ)` with
`χ ∉ {χ₁^{±1}, χ_b^{±1}}` either contradicts the core applied to `(χ_b, ρ_b)` (when
`χ₁² ∉ {χ_b^{±1}}`) or to `(χ, ρ)` (otherwise, since then `χ₁² ∉ {χ^{±1}}`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9F.Defs
import Submission.Work.ZeroFreeTables.P9F.La_defs
import Submission.Work.ZeroFreeTables.hbLemma9_3_engine
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip

open DirichletCharacter Complex
open scoped Real
noncomputable section

namespace Work.ZeroFreeTables.P9F

open Work.ZeroFreeTables Work.LinnikContract

/-- A zero of the ordinary `L`-function of the primitive character inducing `χ`, at height
`≤ 10`, is to the left of the minimal zero `ρ₁` (`IsMin1WideAt 10` version of
`Work.LinnikAreas.le_re_of_LFunction_primitive_eq_zero`). -/
theorem le_re_of_LFunction_of_minWide {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hmin : IsMin1WideAt 10 χ₁ ρ₁) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) [NeZero χ.conductor]
    {u : ℂ} (hu : DirichletCharacter.LFunction χ.primitiveCharacter u = 0) (him : |u.im| ≤ 10) :
    u.re ≤ ρ₁.re := by
  classical
  have hq0 : q ≠ 0 := NeZero.ne q
  have hqne1 : q ≠ 1 := by
    rintro rfl
    exact hχ (Subsingleton.elim χ (1 : DirichletCharacter ℂ 1))
  have hlogpos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hρ₁pos : 0 < ρ₁.re :=
    (zeroMult_re_mem_strip (χ := χ₁) (ρ := ρ₁) hmin.1.1.1 hmin.1.1.2.1).1
  by_cases hpos : 0 < u.re
  · have hψ : χ.primitiveCharacter ≠ 1 := by
      intro h1
      have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
      rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h2
      exact hχ h2.symm
    have hu1 : u.re < 1 := by
      by_contra hcon
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.primitiveCharacter (Or.inl hψ)
        (le_of_not_gt hcon)) hu
    have horder :=
      Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip
        χ.primitiveCharacter hψ hpos hu1
    have hL_an : ∀ z : ℂ, AnalyticAt ℂ (DirichletCharacter.LFunction χ.primitiveCharacter) z :=
      fun z => (DirichletCharacter.differentiable_LFunction hψ).analyticAt z
    have hL_ne : DirichletCharacter.LFunction χ.primitiveCharacter ≠ 0 := by
      intro h0
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.primitiveCharacter (Or.inl hψ)
        (s := (2 : ℂ)) (by norm_num)) (by simp [h0])
    have hord_ne : analyticOrderAt (DirichletCharacter.LFunction χ.primitiveCharacter) u ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hL_an u, hu⟩
    have hfinite : analyticOrderAt (DirichletCharacter.LFunction χ.primitiveCharacter) u ≠ ⊤ := by
      intro htop
      exact hL_ne ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero u hL_an).mp htop)
    have hNat_ne :
        analyticOrderNatAt (DirichletCharacter.LFunction χ.primitiveCharacter) u ≠ 0 := by
      intro h0
      have hcast := Nat.cast_analyticOrderNatAt
        (f := DirichletCharacter.LFunction χ.primitiveCharacter) (z₀ := u) hfinite
      rw [h0, Nat.cast_zero] at hcast
      exact hord_ne hcast.symm
    have hzu : zeroMult χ u ≠ 0 := by
      have hΛne :
          analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u ≠ 0 := by
        rw [← horder]
        exact hNat_ne
      simpa only [Work.LinnikContract.zeroMult] using hΛne
    have hle2 := hmin.2 χ u hχ hzu him
    rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at hle2
    have h3 : 1 - ρ₁.re ≤ 1 - u.re := (mul_le_mul_iff_left₀ hlogpos).mp hle2
    linarith
  · have hle : u.re ≤ 0 := le_of_not_gt hpos
    linarith

/-- `λ₁ ≥ 0` for the minimal zero. -/
theorem lamOf_nonneg_of_minWide {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hmin : IsMin1WideAt 10 χ₁ ρ₁) : 0 ≤ lamOf q ρ₁ := by
  have hstrip := zeroMult_re_mem_strip (χ := χ₁) (ρ := ρ₁)
    hmin.1.1.1 hmin.1.1.2.1
  rw [lamOf]
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by
    have := NeZero.ne q
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this)
  nlinarith [hstrip.2]

/-- **The Heath-Brown numbering argument of Lemma 9.2.**  From the Lemma 9.2 inequality
(`hcore`, available for every admissible pair) and the numerical contradiction at `(a, c)`
(`hcontra`) we get `Lam3Bound χ₁ c`, for a pair `(χ₁, ρ₁)` of the working region with
`λ₁ ≤ a` and `χ₁² ≠ 1`. -/
theorem lam3_of_row {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    {a c : ℝ} {θ lam k slack : ℝ}
    (hmin : IsMin1WideAt 10 χ₁ ρ₁) (hcplx : χ₁ ^ 2 ≠ 1) (hlam1 : lamOf q ρ₁ ≤ a)
    (hcore : ∀ (χj : DirichletCharacter ℂ q) (ρj : ℂ), IsZ χj ρj →
      χj ≠ χ₁ → χj ≠ χ₁⁻¹ → χ₁ ^ 2 ≠ χj → χ₁ ^ 2 ≠ χj⁻¹ → lamOf q ρj ≤ c →
      0 ≤ (k ^ 2 + 1/2) * (La θ lam (lamOf q ρ₁) - La θ lam (lamOf q ρ₁ - lamOf q ρj))
          - 2 * k * La θ lam 0 + tf71f θ lam 0 * slack)
    (hcontra : ∀ {la1 laj : ℝ}, 0 ≤ la1 → la1 ≤ a → laj ≤ c →
      0 ≤ (k ^ 2 + 1/2) * (La θ lam la1 - La θ lam (la1 - laj)) - 2 * k * La θ lam 0
        + tf71f θ lam 0 * slack → False) :
    Lam3Bound χ₁ c := by
  obtain ⟨hl0, hl1⟩ := hmin.1.1
  by_contra hcon
  rw [Lam3Bound] at hcon
  push_neg at hcon
  obtain ⟨χb, ρb, hZb, hb1, hb2, -, -, hblt⟩ := hcon χ₁
  have hkey : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
      χ ≠ χb → χ ≠ χb⁻¹ → c ≤ lamOf q ρ := by
    intro χ ρ hZ h1 h2 h3 h4
    by_contra hlt
    rw [not_le] at hlt
    by_cases hcase : χ₁ ^ 2 = χb ∨ χ₁ ^ 2 = χb⁻¹
    · have hne : χ₁ ^ 2 ≠ χ ∧ χ₁ ^ 2 ≠ χ⁻¹ := by
        rcases hcase with hc | hc
        · constructor
          · intro h; exact h3 (h.symm.trans hc)
          · intro h; exact h4 (by rw [← inv_inv χ, ← h, ← hc])
        · constructor
          · intro h; exact h4 (by rw [← h, ← hc])
          · intro h; exact h3 (by rw [← inv_inv χ, ← h, hc, inv_inv])
      exact hcontra (lamOf_nonneg_of_minWide hmin) hlam1 (le_of_lt hlt)
        (hcore χ ρ hZ h1 h2 hne.1 hne.2 (le_of_lt hlt))
    · push_neg at hcase
      exact hcontra (lamOf_nonneg_of_minWide hmin) hlam1 (le_of_lt hblt)
        (hcore χb ρb hZb hb1 hb2 hcase.1 hcase.2 (le_of_lt hblt))
  obtain ⟨χ, ρ, hZ, h1, h2, h3, h4, hlt⟩ := hcon χb
  exact absurd (hkey χ ρ hZ h1 h2 h3 h4) (not_le.mpr hlt)

end Work.ZeroFreeTables.P9F

