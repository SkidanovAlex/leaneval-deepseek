import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P3Pos
import Submission.Work.LinnikAreas.boxMaxZero

namespace Work.ZeroFreeTables.XY

open Complex
open scoped Classical BigOperators

noncomputable section

/-- **The `P₃`-term at a window zero under the minimality condition is non-negative.**
If `λ(u) = (1 - u.re)L ≥ λ₁` and `0 < a + λ₁`, then `Re P₃((a+λ₁)/((s-u)L)) ≥ 0` (`P3Bounds.1`),
because `Re((s-u)L) = a + L(1-u.re) ≥ a + λ₁`. -/
private lemma p3Term_nonneg_of_window {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {L a lam : ℝ} (hL : 0 < L) {s u : ℂ} (hs : s.re = 1 + a / L) (hα : 0 < a + lam)
    (hlam : lam ≤ (1 - u.re) * L) :
    0 ≤ (Work.ZeroFreeTables.P3 (((a + lam : ℝ) : ℂ) / ((s - u) * (L : ℂ)))).re := by
  have hre : ((s - u) * (L : ℂ)).re = a + L * (1 - u.re) := by
    rw [Complex.mul_re, Complex.sub_re, hs]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    field_simp
    ring
  have hle : a + lam ≤ ((s - u) * (L : ℂ)).re := by
    rw [hre]; nlinarith [hlam]
  have harg : ((s - u) * (L : ℂ)) = ((((s - u) * (L : ℂ)).re : ℂ)
      + (((s - u) * (L : ℂ)).im : ℂ) * Complex.I) := (Complex.re_add_im _).symm
  rw [harg]
  exact Work.ZeroFreeTables.P3.P3Bounds.1 (a + lam) ((s - u) * (L : ℂ)).re
    ((s - u) * (L : ℂ)).im hα hle

theorem NearP3sumExtractTwo2 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {L a lam δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hδ : 0 < δ) (hα : 0 < a + lam)
    {s u₁ u₂ : ℂ} (hmin : ∀ u' : ℂ, Work.LinnikContract.zeroMult χ u' ≠ 0 →
      ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u'‖ ≤ δ → lam ≤ (1 - u'.re) * L)
    (hs : s.re = 1 + a / L)
    (hu₁ : Work.LinnikContract.zeroMult χ u₁ ≠ 0)
    (hu₂ : Work.LinnikContract.zeroMult χ u₂ ≠ 0) (hne : u₁ ≠ u₂)
    (hn₁ : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u₁‖ ≤ δ)
    (hn₂ : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u₂‖ ≤ δ) :
    (Work.LinnikContract.zeroMult χ u₁ : ℝ)
        * (Work.ZeroFreeTables.P3 (((a + lam : ℝ) : ℂ) / ((s - u₁) * (L : ℂ)))).re
      + (Work.LinnikContract.zeroMult χ u₂ : ℝ)
        * (Work.ZeroFreeTables.P3 (((a + lam : ℝ) : ℂ) / ((s - u₂) * (L : ℂ)))).re
      ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ s a lam δ := by
  classical
  set T : ℂ → ℝ := fun u' => (Work.LinnikContract.zeroMult χ u' : ℝ)
      * Work.ZeroFreeTables.P9.nearInd s δ u'
      * (Work.ZeroFreeTables.P3 (((a + lam : ℝ) : ℂ) / ((s - u') * (L : ℂ)))).re with hT
  -- `nearP3sum` is the sum of `T`
  have htsum : Work.ZeroFreeTables.P9.nearP3sum q L χ s a lam δ = ∑' u' : ℂ, T u' := by
    unfold Work.ZeroFreeTables.P9.nearP3sum
    refine tsum_congr (fun u' => ?_)
    rw [hT]
    simp only
    push_cast
    rw [Work.ZeroFreeTables.P9.P3_re_div_eq]
  -- every summand is non-negative
  have hTnn : ∀ u' : ℂ, 0 ≤ T u' := by
    intro u'
    rw [hT]
    simp only
    by_cases hz : Work.LinnikContract.zeroMult χ u' = 0
    · rw [hz]; simp
    by_cases hw : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u'‖ ≤ δ
    · have h3 : 0 ≤ (Work.ZeroFreeTables.P3 (((a + lam : ℝ) : ℂ)
          / ((s - u') * (L : ℂ)))).re :=
        p3Term_nonneg_of_window hL (χ := χ) hs hα (hmin u' hz hw)
      have h4 : 0 ≤ Work.ZeroFreeTables.P9.nearInd s δ u' :=
        Work.ZeroFreeTables.P9.nearInd_nonneg s δ u'
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) h4) h3
    · have h0 : Work.ZeroFreeTables.P9.nearInd s δ u' = 0 := by
        rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_neg hw]
      rw [h0]; simp
  -- the support of `T` is contained in a compact box, hence finite
  have hsupp : ∀ u' : ℂ, T u' ≠ 0 → Work.LinnikContract.zeroMult χ u' ≠ 0 ∧
      1 - δ ≤ u'.re ∧ u'.re ≤ 1 ∧ |u'.im| ≤ |s.im| + δ := by
    intro u' hu'
    have hz : Work.LinnikContract.zeroMult χ u' ≠ 0 := by
      intro h
      exact hu' (by rw [hT]; simp [h])
    have hnear : Work.ZeroFreeTables.P9.nearInd s δ u' ≠ 0 := by
      intro h
      exact hu' (by rw [hT]; simp [h])
    have hw : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u'‖ ≤ δ := by
      by_contra hc
      exact hnear (by rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_neg hc])
    have hzre : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u').re = 1 - u'.re := by simp
    have hzim : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u').im = s.im - u'.im := by simp
    have h1 : |1 - u'.re| ≤ δ := by
      have h := Complex.abs_re_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u')
      rw [hzre] at h
      exact h.trans hw
    have h2 : |s.im - u'.im| ≤ δ := by
      have h := Complex.abs_im_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u')
      rw [hzim] at h
      exact h.trans hw
    refine ⟨hz, ?_, le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hz), ?_⟩
    · have h := (abs_le.mp h1).2
      linarith
    · have h3 : |u'.im| ≤ |s.im| + |s.im - u'.im| := by
        calc |u'.im| = |s.im - (s.im - u'.im)| := by congr 1; ring
          _ ≤ |s.im| + |s.im - u'.im| := abs_sub _ _
      linarith
  have hfin : (Function.support T).Finite :=
    (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ (1 - δ) (|s.im| + δ)).subset
      (fun u' hu' => hsupp u' (by simpa [Function.mem_support] using hu'))
  have hsumT : Summable T :=
    summable_of_ne_finset_zero (s := hfin.toFinset) (fun u' hu' => by
      by_contra h
      exact hu' ((Set.Finite.mem_toFinset hfin).mpr (by simpa [Function.mem_support] using h)))
  -- the two summands at `u₁`, `u₂`
  have hTu₁ : T u₁ = (Work.LinnikContract.zeroMult χ u₁ : ℝ)
      * (Work.ZeroFreeTables.P3 (((a + lam : ℝ) : ℂ) / ((s - u₁) * (L : ℂ)))).re := by
    rw [hT]
    simp only
    have hind : Work.ZeroFreeTables.P9.nearInd s δ u₁ = 1 := by
      rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_pos hn₁]
    rw [hind, mul_one]
  have hTu₂ : T u₂ = (Work.LinnikContract.zeroMult χ u₂ : ℝ)
      * (Work.ZeroFreeTables.P3 (((a + lam : ℝ) : ℂ) / ((s - u₂) * (L : ℂ)))).re := by
    rw [hT]
    simp only
    have hind : Work.ZeroFreeTables.P9.nearInd s δ u₂ = 1 := by
      rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_pos hn₂]
    rw [hind, mul_one]
  rw [htsum]
  calc (Work.LinnikContract.zeroMult χ u₁ : ℝ)
        * (Work.ZeroFreeTables.P3 (((a + lam : ℝ) : ℂ) / ((s - u₁) * (L : ℂ)))).re
      + (Work.LinnikContract.zeroMult χ u₂ : ℝ)
        * (Work.ZeroFreeTables.P3 (((a + lam : ℝ) : ℂ) / ((s - u₂) * (L : ℂ)))).re
      = ∑ u' ∈ ({u₁, u₂} : Finset ℂ), T u' := by
        rw [Finset.sum_pair hne, hTu₁, hTu₂]
    _ ≤ ∑' u' : ℂ, T u' := hsumT.sum_le_tsum _ (fun i _ => hTnn i)

end

end Work.ZeroFreeTables.XY
