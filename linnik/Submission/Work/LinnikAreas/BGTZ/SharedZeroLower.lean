import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZZFR
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.BGTZ.LFunctionZeroFromZeroMult
import Submission.Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one

namespace Work.LinnikAreas.BGTZ

/-- **Landau's "at most one exceptional zero", in the boundary case `ρ = β₁`.**

Let `χ₁` be a real non-principal character mod `q` with a real zero `β₁` of `L(·,χ₁)` such that
`λ₁ = (1-β₁)log q ≤ 1/10` (so `β₁ ≥ 1 - 1/(10 log q)`), let the zero-free region `ZFR` (for zeros
`ρ ≠ β₁`, `Re ρ > 1/2`, of `L(·,χ)` or `L(·,χχ₁)`, with constant `cZ > 0`) hold at level `q`, and
let `hrep` be the level-`q` instantiation of Landau's repulsion
`Work.LinnikAreas.OtherCharRepel.otherCharRepelConst` (`1/25` for zeros of characters other than a
minimal real one).  Then every *other* character `χ ≠ χ₁` (the principal one included) with a zero
of its completed `L`-function at the same point `β₁` forces `λ₁ ≥ min cZ 1 / 2200`.

Proof: if `λ₁ < min cZ 1 / 2200` then `λ₁ < 1/10`, so `β₁ > 1 - 1/(10 log q)` strictly and `hZFR`
yields `IsMin1 χ₁ β₁` (any `IsZ` zero with `λ < λ₁` would have `Re ρ > 1 - 1/(10 log q)` and
`|Im ρ| ≤ 1`, hence `λ(ρ) ≥ cZ/2 > λ₁`, a contradiction); then `hrep` gives `λ₁ ≥ 1/25`, absurd.
For `χ = 1` the configuration is impossible outright (`λ(β₁) = 0` would make `ζ(β₁) = 0` with
`1/2 < β₁ < 1`). -/
theorem SharedZeroLower {q : ℕ} [NeZero q] (cZ : ℝ) (hcZ : 0 < cZ)
    (hZFR : ∀ (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ), χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 →
      Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 → 1 - 1 / (10 * Real.log q) < β₁ →
      ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ),
        (DirichletCharacter.LFunction χ ρ = 0 ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0) →
        (1 / 2 : ℝ) < ρ.re → ρ ≠ (β₁ : ℂ) →
        cZ / Real.log ((q : ℝ) * max 4 |ρ.im|) ≤ 1 - ρ.re)
    (hrep : ∀ (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
      Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
      Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
      ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), χ ≠ χ₀ → χ ≠ χ₀⁻¹ → χ ≠ 1 →
        Work.LinnikContract.zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
        (1 / 25 : ℝ) ≤ Work.LinnikContract.lamOf q ρ)
    {χ₁ : DirichletCharacter ℂ q} {β₁ : ℝ} (hχ₁ : χ₁ ≠ 1) (hsq : χ₁ ^ 2 = 1) (hβ₁ : β₁ < 1)
    (hz₁ : Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0)
    (hlam1 : Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ 1 / 10)
    (hbig : 1000 ≤ Real.log q)
    {χ : DirichletCharacter ℂ q} (hχne : χ ≠ χ₁)
    (hzχ : Work.LinnikContract.zeroMult χ (β₁ : ℂ) ≠ 0) :
    min cZ 1 / 2200 ≤ Work.LinnikContract.lamOf q (β₁ : ℂ) := by
  have hβ₁re : (β₁ : ℂ).re = β₁ := by simp
  have hβ₁im : (β₁ : ℂ).im = 0 := by simp
  have hlam_eq : Work.LinnikContract.lamOf q (β₁ : ℂ) = (1 - β₁) * Real.log q := by
    simp only [Work.LinnikContract.lamOf, hβ₁re]
  by_contra hcon
  push_neg at hcon
  -- `λ₁ < min cZ 1 / 2200`
  have hmin_le : min cZ 1 / 2200 ≤ 1 / 2200 :=
    div_le_div_of_nonneg_right (min_le_right cZ 1) (by norm_num)
  have hmin_le' : min cZ 1 / 2200 ≤ cZ / 2200 :=
    div_le_div_of_nonneg_right (min_le_left cZ 1) (by norm_num)
  have hlt2200 : Work.LinnikContract.lamOf q (β₁ : ℂ) < 1 / 2200 :=
    lt_of_lt_of_le hcon hmin_le
  have hltcZ : Work.LinnikContract.lamOf q (β₁ : ℂ) < cZ / 2200 :=
    lt_of_lt_of_le hcon hmin_le'
  have hlt100 : Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ 1 / 100 := by linarith
  -- `1 - β₁` is very small
  have hβ1lt : 1 - β₁ < 1 / 2200000 := by
    have hpos : (0 : ℝ) ≤ 1 - β₁ := by linarith
    have h1 : (1 - β₁) * 1000 ≤ (1 - β₁) * Real.log q :=
      mul_le_mul_of_nonneg_left hbig hpos
    have h2 : (1 - β₁) * Real.log q < 1 / 2200 := by
      rw [← hlam_eq]; exact hlt2200
    linarith
  have hβ1half : (1 : ℝ) / 2 < β₁ := by linarith
  have hβ1zfr : 1 - 1 / (10 * Real.log q) < β₁ := by
    have hlogpos : 0 < Real.log q := lt_of_lt_of_le (by norm_num) hbig
    have h10pos : 0 < 10 * Real.log q := by linarith
    have h2 : (1 - β₁) * Real.log q < 1 / 2200 := by
      rw [← hlam_eq]; exact hlt2200
    have hle : 1 - β₁ < 1 / (10 * Real.log q) := by
      rw [lt_div_iff₀ h10pos]
      nlinarith [h2]
    linarith
  by_cases hχone : χ = 1
  · -- the principal character cannot have a zero at `β₁` (that would be a real zero of `ζ`)
    subst hχone
    have hΛ : completedRiemannZeta (β₁ : ℂ) = 0 := by
      rw [Work.LinnikAreas.boxMaxZeroAux.zeroMult_one_eq_completedRiemannZeta q (β₁ : ℂ)]
        at hzχ
      exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hzχ
    have hζ0 : riemannZeta (β₁ : ℂ) = 0 := by
      have hbne : (β₁ : ℂ) ≠ 0 := by
        intro h
        have h2 : β₁ = 0 := Complex.ofReal_eq_zero.mp h
        linarith
      rw [riemannZeta_def_of_ne_zero hbne, hΛ, zero_div]
    obtain ⟨c, hcneg, hceq⟩ :=
      Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one hβ1half hβ₁
    rw [hζ0] at hceq
    exact (ne_of_lt hcneg) (Complex.ofReal_eq_zero.mp hceq.symm)
  · -- `χ ≠ 1`: `hZFR` makes `β₁` the minimal zero, and `hrep` repels every other character
    have hinv : χ₁⁻¹ = χ₁ := by
      have hmul : χ₁ * χ₁ = 1 := by simpa [pow_two] using hsq
      exact inv_eq_of_mul_eq_one_left hmul
    have hIsMin : Work.LinnikContract.IsMin1 χ₁ (β₁ : ℂ) := by
      refine ⟨⟨hχ₁, hz₁, ?_⟩, ?_⟩
      · rw [hβ₁im]; norm_num
      · intro χ' ρ hZ
        obtain ⟨hχ'1, hz', him'⟩ := hZ
        by_contra hnot
        push_neg at hnot
        -- `ρ` lies in the zero-free region: `Re ρ < 1`, `Re ρ > 1/2`, `ρ ≠ β₁`
        have hρre_lt : ρ.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ' hz'
        have hρsmall : 1 - ρ.re < 1 / 2200000 := by
          have hpos : (0 : ℝ) ≤ 1 - ρ.re := by linarith
          have h1 : (1 - ρ.re) * 1000 ≤ (1 - ρ.re) * Real.log q :=
            mul_le_mul_of_nonneg_left hbig hpos
          have h2 : (1 - ρ.re) * Real.log q < 1 / 2200 := by
            have h3 := lt_trans hnot hlt2200
            rw [Work.LinnikContract.lamOf] at h3
            exact h3
          linarith
        have hρhalf : (1 : ℝ) / 2 < ρ.re := by linarith
        have hρne : ρ ≠ (β₁ : ℂ) := by
          intro h
          rw [h] at hnot
          exact lt_irrefl _ hnot
        have hL0 : DirichletCharacter.LFunction χ' ρ = 0 :=
          Work.LinnikAreas.BGTZ.LFunction_eq_zero_of_zeroMult_complex χ'
            (le_of_lt hρhalf) (le_of_lt hρre_lt) hz'
        have hres := hZFR χ₁ β₁ hχ₁ hsq hβ₁ hz₁ hβ1zfr χ' ρ (Or.inl hL0) hρhalf hρne
        -- the region gives `1 - Re ρ ≥ cZ / log (4q) ≥ cZ / (2 log q)`, i.e. `λ ρ ≥ cZ / 2`
        have hm4le : max 4 |ρ.im| ≤ (4 : ℝ) := max_le le_rfl (by linarith [him'])
        have hmpos : (0 : ℝ) < max 4 |ρ.im| :=
          lt_of_lt_of_le (by norm_num) (le_max_left _ _)
        have hqpos : (0 : ℝ) < (q : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
        have hlogm_pos : 0 < Real.log ((q : ℝ) * max 4 |ρ.im|) := by
          apply Real.log_pos
          have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
          have hm4ge : (4 : ℝ) ≤ max 4 |ρ.im| := le_max_left _ _
          nlinarith [hm4ge, hq1]
        have h1 : cZ ≤ (1 - ρ.re) * Real.log ((q : ℝ) * max 4 |ρ.im|) :=
          (div_le_iff₀ hlogm_pos).mp hres
        have hlogbound : Real.log ((q : ℝ) * max 4 |ρ.im|) ≤ 2 * Real.log q := by
          rw [Real.log_mul (ne_of_gt hqpos) (ne_of_gt hmpos)]
          have h4 : Real.log (max 4 |ρ.im|) ≤ Real.log 4 := Real.log_le_log hmpos hm4le
          have hlog4 : Real.log (4 : ℝ) ≤ Real.log q := by
            have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
            linarith
          linarith
        have hnonneg : (0 : ℝ) ≤ 1 - ρ.re := by linarith
        have hcZle : cZ ≤ 2 * Work.LinnikContract.lamOf q ρ := by
          rw [Work.LinnikContract.lamOf]
          calc cZ ≤ (1 - ρ.re) * Real.log ((q : ℝ) * max 4 |ρ.im|) := h1
            _ ≤ (1 - ρ.re) * (2 * Real.log q) := mul_le_mul_of_nonneg_left hlogbound hnonneg
            _ = 2 * ((1 - ρ.re) * Real.log q) := by ring
        have hfinal : 2 * Work.LinnikContract.lamOf q (β₁ : ℂ) < cZ := by linarith
        linarith
    have hrepRes := hrep χ₁ (β₁ : ℂ) hIsMin hsq hβ₁im hlt100 χ (β₁ : ℂ) hχne
      (by rw [hinv]; exact hχne) hχone hzχ (by rw [hβ₁im]; norm_num)
    linarith

end Work.LinnikAreas.BGTZ
