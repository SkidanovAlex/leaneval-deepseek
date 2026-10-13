import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.RadialWAux.Defs
import Submission.Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled
import Submission.Work.FTS.PhiStar.RadialWAux.phiKernel_hasDerivAt
import Submission.Work.FTS.PhiStar.RadialWAux.psiKernel_hasDerivAt
import Submission.Work.FTS.PhiStar.FlatWAux.Kernels.psiKernelWeightedLe
import Submission.Work.FTS.PhiStar.FlatWAux.Kernels.phiKernelWeightedLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.FlatWAux.RadGreenDivFlatU`

The flat (`(z+1)^k∂_z^k`) estimate for the *divided* radial Green function
`(z+1)/z · radGreen α m c`, uniform in `α ≤ 1/5` and in the mode `m ≥ 1`.

Route (see `NOTES_radialWAux.md` / `_DevDivFlat.lean`): with the rescaled pieces
`Φ z = ∫₀¹ c(zu)u^{q-1}du`, `Ψ z = ∫_{u>1} c(zu)u^{-p-1}du` (`q = (2m+5)/α`, `p = 2m/α`,
`K = 1/(α(4m+5))`), the rescaled identity `radGreen = K(Φ+Ψ)` and the substitution `t = zu`
give, for `h = c/t`,

  `(z+1)/z · radGreen α m c z = K·(z+1)·(PhiQ (q+1) h z + PsiP (p-1) h z)`.

Every `z`-derivative is then a differentiation under the integral sign over a fixed domain
(`phiKernel_hasDerivAt`, `psiKernel_hasDerivAt`), and the weighted bounds
`phiKernelWeightedLe` / `psiKernelWeightedLe` give
`(z+1)^{j+1}|(Φ̃+Ψ̃)^{(j)}(z)| ≤ 2^{j+1}A(1/(j+q+1) + 1/(q-1) + 1/(p-1-j) + 1/(p+1))`,
which after multiplication by `K` is `≤ 10A/λ_m` by the four arithmetic lemmas below
(the `α`-smallness of `1/(j+q+1)` and `1/(q-1)` is exactly what makes the estimate uniform).
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

open Work.FTS.PhiStar.RadialWAux

/-! ## The `j`-th `z`-derivative kernel of `PhiQ Q h + PsiP P h` -/

/-- The `j`-th `z`-derivative kernel of `PhiQ Q h + PsiP P h`, i.e. the parametric integral
`z ↦ ∫₀¹ h^{(j)}(zu)u^{j+Q-1}du + ∫_{u>1} h^{(j)}(zu)u^{j-P-1}du`. -/
def Wker (Q P : ℝ) (h : ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun z => (∫ u in (0 : ℝ)..1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) + Q - 1))
    + (∫ u in Set.Ioi (1 : ℝ), iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1))

/-! ## The uniform arithmetic

The four bounds `K/(j+q+1) ≤ 1/λ_m`, `K/(q-1) ≤ 1/λ_m`, `K/(p-1-j) ≤ 4/λ_m`,
`K/(p+1) ≤ 4/λ_m` (`K = radK`, `q = radQ`, `p = radP`, `λ_m = 2m(2m+5)`), all uniform in
`α ≤ 1/5`, `m ≥ 1`, `j ≤ 7`. -/

private lemma radK_inv_jQ_le {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) {j : ℕ} :
    radK α m * (1 / ((j : ℝ) + (radQ α m + 1))) ≤ 1 / Gegenbauer.lam m := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  rw [radK, radQ, Gegenbauer.lam]
  have hkey : 1 / (α * (4 * (m : ℝ) + 5)) * (1 / ((j : ℝ) + ((2 * (m : ℝ) + 5) / α + 1)))
      = 1 / ((4 * (m : ℝ) + 5) * (α * ((j : ℝ) + 1) + 2 * (m : ℝ) + 5)) := by
    field_simp
    ring
  rw [hkey]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [hj0, hm0, hα, mul_nonneg (le_of_lt hα) (by linarith : (0 : ℝ) ≤ (j : ℝ) + 1)]

private lemma radK_inv_Q2_le {α : ℝ} (hα : 0 < α) (hα5 : α ≤ 1 / 5) {m : ℕ} (hm : 1 ≤ m) :
    radK α m * (1 / ((radQ α m + 1) - 2)) ≤ 1 / Gegenbauer.lam m := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  rw [radK, radQ, Gegenbauer.lam]
  have hkey : 1 / (α * (4 * (m : ℝ) + 5)) * (1 / (((2 * (m : ℝ) + 5) / α + 1) - 2))
      = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5 - α)) := by
    field_simp
    ring
  rw [hkey]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [sq_nonneg (2 * (m : ℝ) + 5), hα5, hα, hm1,
      mul_le_mul_of_nonneg_left hα5 (by linarith : (0 : ℝ) ≤ 4 * (m : ℝ) + 5)]

private lemma radK_inv_Pj_le {α : ℝ} (hα : 0 < α) (hα5 : α ≤ 1 / 5) {m : ℕ} (hm : 1 ≤ m)
    {j : ℕ} (hj : j ≤ 7) :
    radK α m * (1 / ((radP α m - 1) - (j : ℝ))) ≤ 4 / Gegenbauer.lam m := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [radK, radP, Gegenbauer.lam]
  have hkey : 1 / (α * (4 * (m : ℝ) + 5)) * (1 / ((2 * (m : ℝ) / α - 1) - (j : ℝ)))
      = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) - α * ((j : ℝ) + 1))) := by
    field_simp
    ring
  rw [hkey, show (4 : ℝ) / (2 * (m : ℝ) * (2 * (m : ℝ) + 5))
      = 1 / (2 * (m : ℝ) * (2 * (m : ℝ) + 5) / 4) by field_simp]
  apply one_div_le_one_div_of_le
  · positivity
  · have hj8 : (j : ℝ) + 1 ≤ 8 := by
      have h : (j : ℝ) ≤ 7 := by exact_mod_cast hj
      linarith
    have h1 : α * ((j : ℝ) + 1) ≤ (1 / 5) * 8 :=
      mul_le_mul hα5 hj8 (by positivity) (by norm_num)
    nlinarith [h1, hm1, hα]

private lemma radK_inv_P2_le {α : ℝ} (hα : 0 < α) (hα5 : α ≤ 1 / 5) {m : ℕ} (hm : 1 ≤ m) :
    radK α m * (1 / ((radP α m - 1) + 2)) ≤ 4 / Gegenbauer.lam m := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  rw [radK, radP, Gegenbauer.lam]
  have hkey : 1 / (α * (4 * (m : ℝ) + 5)) * (1 / ((2 * (m : ℝ) / α - 1) + 2))
      = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + α)) := by
    have h1 : (2 * (m : ℝ) / α - 1) + 2 = (2 * (m : ℝ) + α) / α := by field_simp; ring
    rw [h1, one_div_div]
    field_simp
  rw [hkey, show (4 : ℝ) / (2 * (m : ℝ) * (2 * (m : ℝ) + 5))
      = 1 / (2 * (m : ℝ) * (2 * (m : ℝ) + 5) / 4) by field_simp]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [hm1, hα, mul_nonneg (le_of_lt hα) (by linarith : (0 : ℝ) ≤ 2 * (m : ℝ) + 5)]

/-! ## The main theorem -/

theorem RadGreenDivFlatU : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ), 0 < α → α ≤ 1 / 5 → ∀ (m : ℕ), 1 ≤ m → ∀ (c : ℝ → ℝ) (A : ℝ), 0 ≤ A →
      ContDiffOn ℝ 14 c (Set.Ioi 0) →
      (∀ k : ℕ, k ≤ 14 → ∀ t : ℝ, 0 < t → |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1))) →
      (∀ k : ℕ, k ≤ 14 → ∀ t : ℝ, 0 < t →
        |iteratedDeriv k (fun t => c t / t) t| ≤ A / (1 + t ^ (k + 2))) →
      ∀ k : ℕ, k ≤ 7 → ∀ z : ℝ, 0 < z →
        |(z + 1) ^ k * iteratedDeriv k
            (fun z' => (z' + 1) / z' * Work.FTS.PhiStar.Radial.radGreen α m c z') z|
          ≤ C * A / Work.FTS.PhiStar.Gegenbauer.lam m := by
  refine ⟨10 ^ 6, by norm_num, ?_⟩
  intro α hα hα5 m hm c A hA hc hb hbt k hk z hz
  have hlam : 0 < Gegenbauer.lam m := by
    simp only [Gegenbauer.lam]; positivity
  have hKpos : 0 < radK α m := radK_pos hα m
  have hPge : (10 : ℝ) ≤ radP α m := ten_le_radP hα hα5 hm
  have hQge : (35 : ℝ) ≤ radQ α m := thirtyfive_le_radQ hα hα5 hm
  let h : ℝ → ℝ := fun t => c t / t
  have hh : ContDiffOn ℝ 14 h (Set.Ioi 0) := by
    show ContDiffOn ℝ 14 (fun t : ℝ => c t / t) (Set.Ioi 0)
    exact hc.div contDiffOn_id (fun t ht => ne_of_gt ht)
  have hsharp : ∀ j : ℕ, j ≤ 10 → ∀ t : ℝ, 0 < t →
      |iteratedDeriv j h t| ≤ A / (1 + t ^ (j + 2)) :=
    fun j hj t ht => hbt j (by omega) t ht
  have hbdd : BddDeriv 14 h A := by
    intro j hj t ht
    refine le_trans (hbt j hj t ht) ?_
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ (j + 2))]
    nlinarith [hA, pow_nonneg (le_of_lt ht) (j + 2)]
  -- the divided identity `(z+1)/z·radGreen = K·(z+1)·Wker_0`
  have hY : ∀ z : ℝ, 0 < z →
      (z + 1) / z * Radial.radGreen α m c z
        = radK α m * ((z + 1) * Wker (radQ α m + 1) (radP α m - 1) h 0 z) := by
    intro z hz
    have hgr := radGreen_eq_rescaled hα m c z hz
    have hPhi : radPhi α m c z = z * PhiQ (radQ α m + 1) h z := by
      show (∫ u in (0 : ℝ)..1, c (z * u) * u ^ (radQ α m - 1))
          = z * ∫ u in (0 : ℝ)..1, h (z * u) * u ^ ((radQ α m + 1) - 1)
      rw [show ((radQ α m + 1) - 1) = radQ α m from by ring]
      rw [show (∫ u in (0 : ℝ)..1, c (z * u) * u ^ (radQ α m - 1))
          = ∫ u in (0 : ℝ)..1, z * (h (z * u) * u ^ (radQ α m)) from by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with u hu
            change c (z * u) * u ^ (radQ α m - 1) = z * (h (z * u) * u ^ (radQ α m))
            rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
            have hu0 : 0 < u := hu.1
            have hc1 : c (z * u) = (z * u) * h (z * u) := by
              simp only [h]
              field_simp
            have hpw : u * u ^ (radQ α m - 1) = u ^ (radQ α m) := by
              have h2 : u ^ (radQ α m) = u ^ (1 : ℝ) * u ^ (radQ α m - 1) := by
                rw [← Real.rpow_add hu0 (1 : ℝ) (radQ α m - 1)]
                congr 1
                ring
              rw [h2, Real.rpow_one]
            rw [hc1, ← hpw]
            ring,
          intervalIntegral.integral_const_mul]
    have hPsi : radPsi α m c z = z * PsiP (radP α m - 1) h z := by
      show (∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ (-(radP α m) - 1))
          = z * ∫ u in Set.Ioi (1 : ℝ), h (z * u) * u ^ (-(radP α m - 1) - 1)
      rw [show (-(radP α m - 1) - 1) = -(radP α m) from by ring]
      rw [show (∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ (-(radP α m) - 1))
          = ∫ u in Set.Ioi (1 : ℝ), z * (h (z * u) * u ^ (-(radP α m))) from by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro u hu
            change c (z * u) * u ^ (-(radP α m) - 1) = z * (h (z * u) * u ^ (-(radP α m)))
            have hu0 : 0 < u := lt_trans zero_lt_one hu
            have hc1 : c (z * u) = (z * u) * h (z * u) := by
              simp only [h]
              field_simp
            have hpw : u * u ^ (-(radP α m) - 1) = u ^ (-(radP α m)) := by
              have h2 : u ^ (-(radP α m)) = u ^ (1 : ℝ) * u ^ (-(radP α m) - 1) := by
                rw [← Real.rpow_add hu0 (1 : ℝ) (-(radP α m) - 1)]
                congr 1
                ring
              rw [h2, Real.rpow_one]
            rw [hc1, ← hpw]
            ring,
          MeasureTheory.integral_const_mul]
    have hWker0 : Wker (radQ α m + 1) (radP α m - 1) h 0 z
        = PhiQ (radQ α m + 1) h z + PsiP (radP α m - 1) h z := by
      simp only [Wker, PhiQ, PsiP, iteratedDeriv_zero, Nat.cast_zero, zero_add, zero_sub]
    rw [hgr, hPhi, hPsi, hWker0]
    field_simp
  -- differentiating the kernel
  have hWkderiv : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z →
      HasDerivAt (Wker (radQ α m + 1) (radP α m - 1) h j)
        (Wker (radQ α m + 1) (radP α m - 1) h (j + 1) z) z := by
    intro j hj z hz
    have hjP : (j : ℝ) + 1 < radP α m - 1 := by
      have hj6 : (j : ℝ) ≤ 6 := by exact_mod_cast hj
      linarith
    have h1 := phiKernel_hasDerivAt (Q := radQ α m + 1) (B := A) (by linarith) hA hh hbdd
      (j := j) (by omega) hz
    have h2 := psiKernel_hasDerivAt (P := radP α m - 1) (B := A) hA hh hbdd
      (j := j) (by omega) hjP hz
    have hfun : Wker (radQ α m + 1) (radP α m - 1) h j
        = ((fun x : ℝ => ∫ u in (0 : ℝ)..1,
              iteratedDeriv j h (x * u) * u ^ ((j : ℝ) + (radQ α m + 1) - 1))
          + fun x : ℝ => ∫ u in Set.Ioi (1 : ℝ),
              iteratedDeriv j h (x * u) * u ^ ((j : ℝ) - (radP α m - 1) - 1)) := rfl
    rw [hfun]
    simpa only [Wker, Pi.add_apply] using h1.add h2
  -- the iterated derivative formula
  have key : ∀ k : ℕ, k ≤ 7 → ∀ x : ℝ, 0 < x →
      iteratedDeriv k (fun z' => (z' + 1) / z' * Radial.radGreen α m c z') x
        = radK α m * ((x + 1) * Wker (radQ α m + 1) (radP α m - 1) h k x
            + (k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) x) := by
    intro k
    induction k with
    | zero =>
      intro _ x hx
      simpa only [iteratedDeriv_zero, Nat.cast_zero, zero_mul, add_zero] using hY x hx
    | succ k ih =>
      intro hk x hx
      have hk6 : k ≤ 6 := by omega
      have hfun : iteratedDeriv k (fun z' => (z' + 1) / z' * Radial.radGreen α m c z')
          =ᶠ[𝓝 x] (fun y => radK α m * ((y + 1) * Wker (radQ α m + 1) (radP α m - 1) h k y
              + (k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) y)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact ih (by omega) y hy
      rw [iteratedDeriv_succ, hfun.deriv_eq]
      have hdWk : HasDerivAt (Wker (radQ α m + 1) (radP α m - 1) h k)
          (Wker (radQ α m + 1) (radP α m - 1) h (k + 1) x) x := hWkderiv k hk6 x hx
      have hlin : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
        simpa using (hasDerivAt_id x).add_const (1 : ℝ)
      have hderA := hlin.mul hdWk
      have hfunA : ((fun y : ℝ => y + 1) * Wker (radQ α m + 1) (radP α m - 1) h k)
          = fun y : ℝ => (y + 1) * Wker (radQ α m + 1) (radP α m - 1) h k y := rfl
      rw [hfunA] at hderA
      have hderB : HasDerivAt
          (fun y : ℝ => (k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) y)
          ((k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h k x) x := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          have h0 : (fun y : ℝ => ((0 : ℕ) : ℝ)
                * Wker (radQ α m + 1) (radP α m - 1) h (0 - 1) y) = fun _ => 0 := by
            funext y
            simp
          rw [h0]
          simpa using hasDerivAt_const x (0 : ℝ)
        · have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
          have hh' := (hWkderiv (k - 1) (by omega) x hx).const_mul (k : ℝ)
          rwa [hk1] at hh'
      have hsum := hderA.add hderB
      have hfunF : ((fun y : ℝ => (y + 1) * Wker (radQ α m + 1) (radP α m - 1) h k y)
            + fun y : ℝ => (k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) y)
          = fun y : ℝ => (y + 1) * Wker (radQ α m + 1) (radP α m - 1) h k y
              + (k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) y := rfl
      rw [hfunF] at hsum
      have hderF := hsum.const_mul (radK α m)
      rw [hderF.deriv, show (k + 1) - 1 = k from by omega]
      push_cast
      ring
  -- the arithmetic package
  have hSle : ∀ j : ℕ, j ≤ 7 → radK α m *
      (1 / ((j : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
        + 1 / ((radP α m - 1) - (j : ℝ)) + 1 / ((radP α m - 1) + 2))
      ≤ 10 / Gegenbauer.lam m := by
    intro j hj
    have h1 := radK_inv_jQ_le hα hm (j := j)
    have h2 := radK_inv_Q2_le hα hα5 hm
    have h3 := radK_inv_Pj_le hα hα5 hm (j := j) hj
    have h4 := radK_inv_P2_le hα hα5 hm
    have hexp : radK α m *
        (1 / ((j : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
          + 1 / ((radP α m - 1) - (j : ℝ)) + 1 / ((radP α m - 1) + 2))
        = radK α m * (1 / ((j : ℝ) + (radQ α m + 1)))
          + radK α m * (1 / ((radQ α m + 1) - 2))
          + radK α m * (1 / ((radP α m - 1) - (j : ℝ)))
          + radK α m * (1 / ((radP α m - 1) + 2)) := by ring
    rw [hexp]
    have hcomb : 1 / Gegenbauer.lam m + 1 / Gegenbauer.lam m + 4 / Gegenbauer.lam m
          + 4 / Gegenbauer.lam m = 10 / Gegenbauer.lam m := by ring
    calc radK α m * (1 / ((j : ℝ) + (radQ α m + 1))) + radK α m * (1 / ((radQ α m + 1) - 2))
          + radK α m * (1 / ((radP α m - 1) - (j : ℝ))) + radK α m * (1 / ((radP α m - 1) + 2))
        ≤ 1 / Gegenbauer.lam m + 1 / Gegenbauer.lam m + 4 / Gegenbauer.lam m
          + 4 / Gegenbauer.lam m :=
          add_le_add (add_le_add (add_le_add h1 h2) h3) h4
      _ = 10 / Gegenbauer.lam m := hcomb
  -- the weighted kernel bound
  have hker : ∀ j : ℕ, j ≤ 7 → ∀ z : ℝ, 0 < z →
      (z + 1) ^ (j + 1) * |Wker (radQ α m + 1) (radP α m - 1) h j z| ≤
        (2 : ℝ) ^ (j + 1) * A *
          (1 / ((j : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
            + 1 / ((radP α m - 1) - (j : ℝ)) + 1 / ((radP α m - 1) + 2)) := by
    intro j hj z hz
    have hQ2 : (2 : ℝ) < radQ α m + 1 := by linarith
    have hP9 : (9 : ℝ) ≤ radP α m - 1 := by linarith
    have hjP : (j : ℝ) < radP α m - 1 := by
      have hj7 : (j : ℝ) ≤ 7 := by exact_mod_cast hj
      linarith
    have hp := Kernels.phiKernelWeightedLe (Q := radQ α m + 1) (B := A) hQ2 hA hh hsharp j (by omega) z hz
    have hq := Kernels.psiKernelWeightedLe (P := radP α m - 1) (B := A) hP9 hA hh hsharp j (by omega) hjP z hz
    have htri : (z + 1) ^ (j + 1) * |Wker (radQ α m + 1) (radP α m - 1) h j z|
        ≤ (z + 1) ^ (j + 1) * |(∫ u in (0 : ℝ)..1,
              iteratedDeriv j h (z * u) * u ^ ((j : ℝ) + (radQ α m + 1) - 1))|
          + (z + 1) ^ (j + 1) * |(∫ u in Set.Ioi (1 : ℝ), iteratedDeriv j h (z * u)
              * u ^ ((j : ℝ) - (radP α m - 1) - 1))| := by
      rw [show Wker (radQ α m + 1) (radP α m - 1) h j z
          = (∫ u in (0 : ℝ)..1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) + (radQ α m + 1) - 1))
            + (∫ u in Set.Ioi (1 : ℝ), iteratedDeriv j h (z * u)
                * u ^ ((j : ℝ) - (radP α m - 1) - 1)) from rfl]
      have h := mul_le_mul_of_nonneg_left
        (abs_add_le (∫ u in (0 : ℝ)..1,
            iteratedDeriv j h (z * u) * u ^ ((j : ℝ) + (radQ α m + 1) - 1))
          (∫ u in Set.Ioi (1 : ℝ),
            iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - (radP α m - 1) - 1)))
        (by positivity : (0 : ℝ) ≤ (z + 1) ^ (j + 1))
      rwa [mul_add] at h
    refine le_trans htri ?_
    have hsplit : (2 : ℝ) ^ (j + 1) * A *
          (1 / ((j : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
            + 1 / ((radP α m - 1) - (j : ℝ)) + 1 / ((radP α m - 1) + 2))
        = (2 : ℝ) ^ (j + 1) * A * (1 / ((j : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2))
          + (2 : ℝ) ^ (j + 1) * A
            * (1 / ((radP α m - 1) - (j : ℝ)) + 1 / ((radP α m - 1) + 2)) := by ring
    rw [hsplit]
    exact add_le_add hp hq
  -- numerical bounds on the powers of `2`
  have h2k : (2 : ℝ) ^ k ≤ 128 := by
    calc (2 : ℝ) ^ k ≤ 2 ^ 7 := pow_le_pow_right₀ (by norm_num) hk
      _ = 128 := by norm_num
  have h2k1 : (2 : ℝ) ^ (k + 1) ≤ 256 := by
    calc (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      _ ≤ 2 * 128 := by linarith
      _ = 256 := by norm_num
  have hkR : (k : ℝ) ≤ 7 := by exact_mod_cast hk
  have hkmul : (k : ℝ) * (2 : ℝ) ^ k ≤ 7 * 128 :=
    mul_le_mul hkR h2k (by positivity) (by norm_num)
  have hkey := key k hk z hz
  have hkerk := hker k hk z hz
  have hSK := hSle k hk
  have hSK1 := hSle (k - 1) (by omega)
  -- the `k-1` term: `(k-1)+1 = k` needs `k ≥ 1`, and the case `k = 0` is trivial
  have hkerk1 : (k : ℝ) * ((z + 1) ^ k * |Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z|)
      ≤ (k : ℝ) * ((2 : ℝ) ^ k * A *
          (1 / (((k - 1 : ℕ) : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
            + 1 / ((radP α m - 1) - ((k - 1 : ℕ) : ℝ)) + 1 / ((radP α m - 1) + 2))) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp
    · have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
      have h := hker (k - 1) (by omega) z hz
      rw [hk1] at h
      exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k)
  have hb1 : radK α m * ((2 : ℝ) ^ (k + 1) * A *
        (1 / ((k : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
          + 1 / ((radP α m - 1) - (k : ℝ)) + 1 / ((radP α m - 1) + 2)))
      ≤ (2 : ℝ) ^ (k + 1) * A * (10 / Gegenbauer.lam m) := by
    calc radK α m * ((2 : ℝ) ^ (k + 1) * A *
          (1 / ((k : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
            + 1 / ((radP α m - 1) - (k : ℝ)) + 1 / ((radP α m - 1) + 2)))
        = (2 : ℝ) ^ (k + 1) * A * (radK α m *
            (1 / ((k : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
              + 1 / ((radP α m - 1) - (k : ℝ)) + 1 / ((radP α m - 1) + 2))) := by ring
      _ ≤ (2 : ℝ) ^ (k + 1) * A * (10 / Gegenbauer.lam m) :=
          mul_le_mul_of_nonneg_left hSK (by positivity)
  have hb2 : radK α m * ((k : ℝ) * ((2 : ℝ) ^ k * A *
        (1 / (((k - 1 : ℕ) : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
          + 1 / ((radP α m - 1) - ((k - 1 : ℕ) : ℝ)) + 1 / ((radP α m - 1) + 2))))
      ≤ (k : ℝ) * ((2 : ℝ) ^ k * A * (10 / Gegenbauer.lam m)) := by
    calc radK α m * ((k : ℝ) * ((2 : ℝ) ^ k * A *
          (1 / (((k - 1 : ℕ) : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
            + 1 / ((radP α m - 1) - ((k - 1 : ℕ) : ℝ)) + 1 / ((radP α m - 1) + 2))))
        = (k : ℝ) * ((2 : ℝ) ^ k * A * (radK α m *
            (1 / (((k - 1 : ℕ) : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
              + 1 / ((radP α m - 1) - ((k - 1 : ℕ) : ℝ)) + 1 / ((radP α m - 1) + 2)))) := by
          ring
      _ ≤ (k : ℝ) * ((2 : ℝ) ^ k * A * (10 / Gegenbauer.lam m)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
          exact mul_le_mul_of_nonneg_left hSK1 (by positivity)
  have habs1 : |(z + 1) ^ k * iteratedDeriv k
        (fun z' => (z' + 1) / z' * Radial.radGreen α m c z') z|
      = radK α m * |(z + 1) ^ (k + 1) * Wker (radQ α m + 1) (radP α m - 1) h k z
          + (k : ℝ) * ((z + 1) ^ k * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z)| := by
    rw [hkey]
    rw [show (z + 1) ^ k * (radK α m * ((z + 1) * Wker (radQ α m + 1) (radP α m - 1) h k z
          + (k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z))
        = radK α m * ((z + 1) ^ k * ((z + 1) * Wker (radQ α m + 1) (radP α m - 1) h k z
          + (k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z)) from by ring]
    rw [abs_mul, abs_of_pos hKpos]
    congr 1
    rw [pow_succ]
    ring_nf
  have habs2 : |(z + 1) ^ (k + 1) * Wker (radQ α m + 1) (radP α m - 1) h k z
        + (k : ℝ) * ((z + 1) ^ k * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z)|
      ≤ (z + 1) ^ (k + 1) * |Wker (radQ α m + 1) (radP α m - 1) h k z|
        + (k : ℝ) * ((z + 1) ^ k * |Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z|) := by
    calc |(z + 1) ^ (k + 1) * Wker (radQ α m + 1) (radP α m - 1) h k z
          + (k : ℝ) * ((z + 1) ^ k * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z)|
        ≤ |(z + 1) ^ (k + 1) * Wker (radQ α m + 1) (radP α m - 1) h k z|
          + |(k : ℝ) * ((z + 1) ^ k * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z)| :=
          abs_add_le _ _
      _ = (z + 1) ^ (k + 1) * |Wker (radQ α m + 1) (radP α m - 1) h k z|
          + (k : ℝ) * ((z + 1) ^ k * |Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z|) := by
          simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (z + 1) ^ (k + 1) by positivity),
            abs_of_nonneg (show (0 : ℝ) ≤ ((k : ℕ) : ℝ) by positivity),
            abs_of_nonneg (show (0 : ℝ) ≤ (z + 1) ^ k by positivity)]
  calc |(z + 1) ^ k * iteratedDeriv k
        (fun z' => (z' + 1) / z' * Radial.radGreen α m c z') z|
      = radK α m * |(z + 1) ^ (k + 1) * Wker (radQ α m + 1) (radP α m - 1) h k z
          + (k : ℝ) * ((z + 1) ^ k * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z)| := habs1
    _ ≤ radK α m * ((z + 1) ^ (k + 1) * |Wker (radQ α m + 1) (radP α m - 1) h k z|
          + (k : ℝ) * ((z + 1) ^ k
            * |Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z|)) :=
          mul_le_mul_of_nonneg_left habs2 (le_of_lt hKpos)
    _ ≤ radK α m * ((2 : ℝ) ^ (k + 1) * A *
          (1 / ((k : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
            + 1 / ((radP α m - 1) - (k : ℝ)) + 1 / ((radP α m - 1) + 2))
          + (k : ℝ) * ((2 : ℝ) ^ k * A *
            (1 / (((k - 1 : ℕ) : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
              + 1 / ((radP α m - 1) - ((k - 1 : ℕ) : ℝ)) + 1 / ((radP α m - 1) + 2)))) :=
          mul_le_mul_of_nonneg_left (add_le_add hkerk hkerk1) (le_of_lt hKpos)
    _ ≤ (2 : ℝ) ^ (k + 1) * A * (10 / Gegenbauer.lam m)
          + (k : ℝ) * ((2 : ℝ) ^ k * A * (10 / Gegenbauer.lam m)) := by
          rw [mul_add]
          exact add_le_add hb1 hb2
    _ ≤ 10 ^ 6 * A / Gegenbauer.lam m := by
        rw [show (2 : ℝ) ^ (k + 1) * A * (10 / Gegenbauer.lam m)
              + (k : ℝ) * ((2 : ℝ) ^ k * A * (10 / Gegenbauer.lam m))
            = A * (10 / Gegenbauer.lam m)
              * ((2 : ℝ) ^ (k + 1) + (k : ℝ) * (2 : ℝ) ^ k) by ring]
        have hsum : (2 : ℝ) ^ (k + 1) + (k : ℝ) * (2 : ℝ) ^ k ≤ 256 + 896 := by linarith
        calc A * (10 / Gegenbauer.lam m) * ((2 : ℝ) ^ (k + 1) + (k : ℝ) * (2 : ℝ) ^ k)
            ≤ A * (10 / Gegenbauer.lam m) * (256 + 896) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = A * 11520 / Gegenbauer.lam m := by ring
          _ ≤ A * 10 ^ 6 / Gegenbauer.lam m := by
              apply div_le_div_of_nonneg_right _ (le_of_lt hlam)
              nlinarith [hA]
          _ = 10 ^ 6 * A / Gegenbauer.lam m := by ring

end Work.FTS.PhiStar.FlatWAux
