import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Vocab
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzDefs
import Submission.Work.FTS.CoercivityFix.Assembly.ProdDeriv
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzAux
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzEval
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzAsym
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzAsymB
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzRegQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Assembly

/-- **The `RegQ`-counterexample to the norm comparison for `α < -1/10`.**

For `α < -1/10` one has `γ(α) = 1 + α/10 < η = 99/100`, so the angular weight gap is
*reversed*: the pure `z`-slots of `D_θ f` carry the heavier weight `w·sin(2θ)^{-η/2}` while
the only level-`(n+1)` slot with the same function carries `w·sin(2θ)^{-γ/2} < w·sin(2θ)^{-η/2}`.
As a result the comparison `HkSq α n (D_θ f) ≤ HkSq α (n+1) f` of `StepReg2.normSub` **fails**:
there is an honest `f ∈ RegQ α (n+2)` whose level-`n` `ℋ`-seminorm of `D_θ f` is *strictly
larger* than its level-`(n+1)` `ℋ`-seminorm.

Construction (verified numerically; the product ansatz makes every integral factor).
Take `ψ z = z^2 * exp(-z)`, a smooth bump `Λ` (`Λ = 1` on `[-1,1]`, `Λ = 0` off `[-2,2]`),
`θ₀ ∈ (0,π/2)`, `δ > 0` small, and `f z θ = ψ z * Λ ((θ - θ₀)/δ)`.
Write `Z_i = ∫ z in Iz, (DzIter i ψ z * w z)^2` (`Z_0 = 5.25`, `Z_1 = 6.875`, `Z_2 = 19.75`, …),
`T = ∫ θ in Iθ, (Λ ((θ-θ₀)/δ))^2 * sin(2θ)^{-η}` and, with `h = Λ((·-θ₀)/δ)`,
`S_η = ∫ θ in Iθ, (D_θ h)^2 sin(2θ)^{-η}`, `S_γ = ∫ θ in Iθ, (D_θ h)^2 sin(2θ)^{-γ}`.
Then every mixed slot of `HkIntegrand α n (D_θ f)` is *literally* a mixed slot of
`HkIntegrand α (n+1) f`, and the mixed sums cancel index-by-index, leaving the exact identity
  `HkSq α (n+1) f - HkSq α n (D_θ f) = (∑_{i≤n} Z_i) * (S_γ - S_η) + (∑_{i≤n+1} Z_i) * T`,
which is **negative** for `δ` small: as `δ → 0` one has `S_η - S_γ ≍ (sin(2θ₀)^{2-η} -
sin(2θ₀)^{2-γ}) ∫(Λ')² / δ > 0` while `T ≍ sin(2θ₀)^{-η} ∫Λ² * δ → 0`, so that
`(∑_{i≤n} Z_i)(S_η - S_γ) > (∑_{i≤n+1} Z_i) T` as soon as `δ` is small enough (the quantities
`Z_i`, `∫(Λ')²`, `∫Λ²` are all fixed positive reals).
`sorry`-free target: this is what makes `StepReg2 α n` *unsatisfiable* for `α < -1/10`. -/
theorem exists_not_normSub_lt (α : ℝ) (hα : α < -(1/10 : ℝ)) (n : ℕ) :
    ∃ f : ℝ → ℝ → ℝ, Work.FTS.Nonlin.RegQ α (n + 2) f ∧
      Work.Spaces.HkSq α (n + 1) f < Work.Spaces.HkSq α n (Work.Spaces.Dth f) := by
  obtain ⟨C₁, C₂, hC₁pos, hC₂pos, hb⟩ := thBounds α hα
  set A : ℝ := ∑ i ∈ Finset.range (n + 1 + 1), Zc psiA i with hAdef
  set B : ℝ := ∑ i ∈ Finset.range (n + 1), Zc psiA i with hBdef
  have hZnn : ∀ i : ℕ, 0 ≤ Zc psiA i := fun i => by
    rw [Zc]
    exact MeasureTheory.integral_nonneg fun z => sq_nonneg _
  have hsum0 : ∀ m : ℕ, Zc psiA 0 ≤ ∑ i ∈ Finset.range (m + 1), Zc psiA i :=
    fun m => Finset.single_le_sum (fun i _ => hZnn i) (Finset.mem_range.mpr (Nat.succ_pos m))
  have hBpos : 0 < B := by
    rw [hBdef]
    exact lt_of_lt_of_le Zc_psiA_zero_pos (hsum0 n)
  have hApos : 0 < A := by
    rw [hAdef]
    exact lt_of_lt_of_le Zc_psiA_zero_pos (hsum0 (n + 1))
  have hXpos : 0 < B * C₁ / (A * C₂) :=
    div_pos (mul_pos hBpos hC₁pos) (mul_pos hApos hC₂pos)
  set δ : ℝ := min (1 / 8) (Real.sqrt (B * C₁ / (A * C₂)) / 2) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    refine lt_min (by norm_num) ?_
    have h := Real.sqrt_pos.mpr hXpos
    linarith
  have hδ1 : δ ≤ 1 / 8 := by
    rw [hδdef]
    exact min_le_left _ _
  have hδ2 : δ ≤ Real.sqrt (B * C₁ / (A * C₂)) / 2 := by
    rw [hδdef]
    exact min_le_right _ _
  have hδsq : δ ^ 2 < B * C₁ / (A * C₂) := by
    have hroot : Real.sqrt (B * C₁ / (A * C₂)) ^ 2 = B * C₁ / (A * C₂) :=
      Real.sq_sqrt (le_of_lt hXpos)
    have h := pow_le_pow_left₀ (le_of_lt hδ0) hδ2 2
    have h4 : (Real.sqrt (B * C₁ / (A * C₂)) / 2) ^ 2 = B * C₁ / (A * C₂) / 4 := by
      rw [div_pow, hroot]
      norm_num
    rw [h4] at h
    linarith
  obtain ⟨hT, hS⟩ := hb δ hδ0 hδ1
  have hev1 : Work.Spaces.HkSq α (n + 1) (ansatz δ) = HkSqForm α (n + 1) psiA (hA δ) :=
    HkSq_eq_form α (n + 1) psiA (hA δ) contDiff_psiA (contDiff_hA δ)
      (slotU_integrable (n + 1)) (slotV_integrable_hA α (n + 1) δ hδ0 hδ1)
  have hev2 : Work.Spaces.HkSq α n (Work.Spaces.Dth (ansatz δ))
      = HkSqForm α n psiA (vthIter 1 (hA δ)) := by
    have hDth : Work.Spaces.Dth (ansatz δ)
        = fun z θ => psiA z * vthIter 1 (hA δ) θ := by
      have h := DthIter_prod 1 psiA (hA δ) (contDiff_hA δ)
      rw [show Work.Spaces.Dth (ansatz δ)
          = Work.Spaces.DthIter 1 (fun z θ => psiA z * hA δ θ) from rfl, h]
    rw [hDth]
    exact HkSq_eq_form α n psiA (vthIter 1 (hA δ)) contDiff_psiA
      (contDiff_vthIter_hA δ 1) (slotU_integrable n) (slotV_integrable_vth α n δ hδ0 hδ1)
  have hmain : HkSqForm α (n + 1) psiA (hA δ) - HkSqForm α n psiA (vthIter 1 (hA δ)) < 0 := by
    rw [HkSqForm_shift α n psiA (hA δ)]
    rw [← hAdef, ← hBdef]
    have h1' : A * Sc (hA δ) 0 Work.Spaces.eta ≤ A * (C₂ * δ) :=
      mul_le_mul_of_nonneg_left hT (le_of_lt hApos)
    have h2' : B * (Sc (hA δ) 1 (Work.Spaces.gam α) - Sc (hA δ) 1 Work.Spaces.eta)
        ≤ -(B * (C₁ / δ)) := by
      have heq : Sc (hA δ) 1 (Work.Spaces.gam α) - Sc (hA δ) 1 Work.Spaces.eta
          = -(Sc (hA δ) 1 Work.Spaces.eta - Sc (hA δ) 1 (Work.Spaces.gam α)) := by ring
      rw [heq]
      have h := mul_le_mul_of_nonneg_left hS (le_of_lt hBpos)
      linarith
    have hkey : A * C₂ * δ ^ 2 < B * C₁ := by
      have h := hδsq
      rw [lt_div_iff₀ (mul_pos hApos hC₂pos)] at h
      linarith
    have hval : A * (C₂ * δ) - B * (C₁ / δ) = (A * C₂ * δ ^ 2 - B * C₁) / δ := by
      field_simp
    have hneg : A * (C₂ * δ) - B * (C₁ / δ) < 0 := by
      rw [hval]
      exact div_neg_of_neg_of_pos (by linarith) hδ0
    linarith [h1', h2', hneg]
  refine ⟨ansatz δ, RegQ_ansatz α n δ hδ0 hδ1, ?_⟩
  rw [hev1, hev2]
  linarith [hmain]

end Work.FTS.CoercivityFix.Assembly
