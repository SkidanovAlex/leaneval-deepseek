import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

-- (`ℝ³` is the *global* notation `EuclideanSpace ℝ (Fin 3)` of
-- `Submission/Work/BoseKinLoc/Defs.lean`, which is in this file's import cone.)

/-!
# `Work.BoseFixB1S.boxMuSumAgree` — the `μ`-weighted box words reassemble into `Φ²`

The FS-faithful box projections `Pᵢ = boxPInd volA A i` and `Qᵢ = boxQInd volA A i` of
`Submission/Work/UBBInputs8/Defs.lean` satisfy `Pᵢ + Qᵢ = 1_A(xᵢ)·` *definitionally*.  Hence
the mixed square `(PᵢΦ)² + 2(QᵢΦ)(PᵢΦ) + (QᵢΦ)²` is `(1_A(xᵢ)Φ)² = 1_A(xᵢ)·Φ²`, and since the
one-body fibre `w1Fibre ℓ w1 (xᵢ) = ∫_{acube ℓ} w1(xᵢ,y)dy` vanishes whenever `xᵢ ∉ A`
(the support hypothesis `hsuppA` on `w` and the relation `w1 = w(1−ω)`), the extra factor
`1_A(xᵢ)` may be dropped:

  `Σᵢ ∫ (PᵢΦ)²·fib + 2 Σᵢ ∫ (QᵢΦ)(PᵢΦ)·fib + Σᵢ ∫ (QᵢΦ)²·fib = Σᵢ ∫ Φ²·fib`,

which is exactly the statement of `boxMuSumAgree` after unfolding `boxMuP`, `boxMuQP`,
`boxMuQ` and `boxMuPhi`.
-/

/-- `Pᵢ + Qᵢ = 1_A(xᵢ)·` — the defining decomposition of the FS box projections
(definitional, from `boxQInd = 1_A· − boxPInd`). -/
theorem boxPInd_add_boxQInd_coneC (volA : ℝ) (A : Set ℝ³) {N : ℕ} (i : Fin N)
    (Φ : X N → ℝ) (x : X N) :
    Work.UBBInputs8.boxPInd volA A i Φ x + Work.UBBInputs8.boxQInd volA A i Φ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x := by
  unfold Work.UBBInputs8.boxQInd
  ring

/-- The one-body fibre kernel of `w1` vanishes off the support box `A`: if `u ∉ A` then
`w u y = 0` for every `y` (by `hsuppA`), hence `w1 u y = 0` for every `y` (by `hw1rel`), hence
the fibre integral over `acube ℓ` is `0`. -/
theorem w1Fibre_eq_zero_of_notMem {ℓ : ℝ} {A : Set ℝ³}
    {w w1 om : ℝ³ → ℝ³ → ℝ}
    (hw1rel : ∀ x y, w1 x y = w x y * (1 - om x y))
    (hsuppA : ∀ x y, w x y ≠ 0 → x ∈ A ∧ y ∈ A)
    {u : ℝ³} (hu : u ∉ A) : w1Fibre ℓ w1 u = 0 := by
  have hzero : (fun y : ℝ³ => w1 u y) = fun _ => (0 : ℝ) := by
    funext y
    have hwy : w u y = 0 := by
      by_contra hne
      exact hu (hsuppA u y hne).1
    rw [hw1rel u y, hwy, zero_mul]
  unfold w1Fibre
  rw [hzero]
  simp

/-- **The per-slot `μ`-identity.**  `boxMuP + 2·boxMuQP + boxMuQ = boxMuPhi` in slot `i`. -/
theorem boxMu_summand {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ)
    {w w1 om : ℝ³ → ℝ³ → ℝ}
    (hw1c : Continuous (fun p : ℝ³ × ℝ³ => w1 p.1 p.2))
    (hw1rel : ∀ x y, w1 x y = w x y * (1 - om x y))
    (hsuppA : ∀ x y, w x y ≠ 0 → x ∈ A ∧ y ∈ A)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) :
    boxMuP volA ℓ A w1 Φ i + 2 * boxMuQP volA ℓ A w1 Φ i + boxMuQ volA ℓ A w1 Φ i
      = boxMuPhi (N := N) ℓ w1 Φ i := by
  classical
  simp only [boxMuP, boxMuQP, boxMuQ, boxMuPhi]
  set fib : ℝ³ → ℝ := w1Fibre ℓ w1 with hfibdef
  set P : X N → ℝ := Work.UBBInputs8.boxPInd volA A i Φ with hPdef
  set Q : X N → ℝ := Work.UBBInputs8.boxQInd volA A i Φ with hQdef
  -- bounds
  obtain ⟨C₀, hC₀⟩ :=
    (abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hCb : ∀ x ∈ abox N ℓ, |Φ x| ≤ C := by
    intro x hx
    have h := hC₀ x hx
    rw [Real.norm_eq_abs] at h
    rw [hCdef]
    exact le_trans h (le_max_left _ _)
  obtain ⟨Cf₀, hCf₀⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    ((w1Fibre_continuous hℓ hw1c).comp (continuous_apply i)).continuousOn
  set Cf : ℝ := max Cf₀ 0 with hCfdef
  have hCf0 : 0 ≤ Cf := by rw [hCfdef]; exact le_max_right _ _
  have hCfb : ∀ x ∈ abox N ℓ, |fib (x i)| ≤ Cf := by
    intro x hx
    have h := hCf₀ x hx
    rw [Real.norm_eq_abs] at h
    rw [hCfdef, hfibdef]
    exact le_trans h (le_max_left _ _)
  -- measurability
  have hfibm : Measurable fib := by
    rw [hfibdef]
    exact (w1Fibre_continuous hℓ hw1c).measurable
  have hfibmi : Measurable (fun x : X N => fib (x i)) :=
    hfibm.comp (measurable_pi_apply i)
  have hPIndm : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    measurable_boxPInd volA A hA i hΦc.measurable
  have hPm : Measurable P := by rw [hPdef]; exact hPIndm
  have hAim : Measurable (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i)) :=
    (measurable_const.indicator hA).comp (measurable_pi_apply i)
  have hQm : Measurable Q := by
    rw [hQdef]
    unfold Work.UBBInputs8.boxQInd
    exact (hAim.mul hΦc.measurable).sub hPIndm
  -- bounds on the projections
  have hPb : ∀ x ∈ abox N ℓ, |P x| ≤ C := by
    intro x hx
    rw [hPdef]
    exact abs_boxPInd_le hℓ hvol hA hvolA hAc i hCb x hx
  have hAind : ∀ y : ℝ³, |A.indicator (fun _ => (1 : ℝ)) y| ≤ 1 := by
    intro y
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy]; norm_num
    · rw [Set.indicator_of_notMem hy]; norm_num
  have hQb : ∀ x ∈ abox N ℓ, |Q x| ≤ 2 * C := by
    intro x hx
    have hQx : Q x = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - P x := by
      rw [hQdef, hPdef]
      rfl
    rw [hQx]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - P x|
        ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| + |P x| := abs_sub _ _
      _ ≤ 1 * |Φ x| + C := by
          refine add_le_add ?_ (hPb x hx)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hAind (x i)) (abs_nonneg _)
      _ ≤ 2 * C := by
          have h := hCb x hx
          linarith
  -- the pointwise vanishing of the `μ`-weight beyond `P + Q = 1_A(xᵢ)`
  have hsum : ∀ x : X N, P x + Q x = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x := by
    intro x
    rw [hPdef, hQdef]
    exact boxPInd_add_boxQInd_coneC volA A i Φ x
  have hpt : ∀ x : X N, (P x ^ 2 + 2 * (Q x * P x) + Q x ^ 2) * fib (x i)
      = Φ x ^ 2 * fib (x i) := by
    intro x
    have hs2 : P x ^ 2 + 2 * (Q x * P x) + Q x ^ 2
        = (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 := by
      rw [← hsum x]
      ring
    have hs3 : (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2
        = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x ^ 2 := by
      rw [mul_pow]
      by_cases hx : x i ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
    rw [hs2, hs3]
    by_cases hx : x i ∈ A
    · rw [Set.indicator_of_mem hx]
      ring
    · have hfib0 : fib (x i) = 0 := by
        rw [hfibdef]
        exact w1Fibre_eq_zero_of_notMem (ℓ := ℓ) hw1rel hsuppA hx
      rw [Set.indicator_of_notMem hx, hfib0]
      ring
  -- integrability of the four integrands
  set D : ℝ := (2 * C) ^ 2 * Cf with hDdef
  have hbP : ∀ x ∈ abox N ℓ, |P x ^ 2 * fib (x i)| ≤ D := by
    intro x hx
    rw [hDdef, abs_mul, abs_pow]
    calc |P x| ^ 2 * |fib (x i)| ≤ C ^ 2 * Cf :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hPb x hx) 2) (hCfb x hx)
            (abs_nonneg _) (pow_nonneg hC0 2)
      _ ≤ (2 * C) ^ 2 * Cf :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC0 (by linarith) 2) hCf0
  have hbQ : ∀ x ∈ abox N ℓ, |Q x ^ 2 * fib (x i)| ≤ D := by
    intro x hx
    rw [hDdef, abs_mul, abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hQb x hx) 2) (hCfb x hx)
      (abs_nonneg _) (pow_nonneg (by linarith : (0 : ℝ) ≤ 2 * C) 2)
  have hbQP : ∀ x ∈ abox N ℓ, |Q x * P x * fib (x i)| ≤ D := by
    intro x hx
    rw [hDdef, abs_mul, abs_mul]
    calc (|Q x| * |P x|) * |fib (x i)| ≤ (2 * C * C) * Cf :=
          mul_le_mul (mul_le_mul (hQb x hx) (hPb x hx) (abs_nonneg _) (by linarith))
            (hCfb x hx) (abs_nonneg _) (mul_nonneg (by linarith) hC0)
      _ ≤ (2 * C) ^ 2 * Cf :=
          mul_le_mul_of_nonneg_right (by nlinarith [hC0]) hCf0
  have hbPhi : ∀ x ∈ abox N ℓ, |Φ x ^ 2 * fib (x i)| ≤ D := by
    intro x hx
    rw [hDdef, abs_mul, abs_pow]
    calc |Φ x| ^ 2 * |fib (x i)| ≤ C ^ 2 * Cf :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hCb x hx) 2) (hCfb x hx)
            (abs_nonneg _) (pow_nonneg hC0 2)
      _ ≤ (2 * C) ^ 2 * Cf :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC0 (by linarith) 2) hCf0
  have hIntb : ∀ {f : X N → ℝ}, Measurable f → (∀ x ∈ abox N ℓ, |f x| ≤ D) →
      IntegrableOn f (abox N ℓ) volume := by
    intro f hfm hb
    refine IntegrableOn.of_bound (abox_lt_top N ℓ hℓ.le) hfm.aestronglyMeasurable D ?_
    rw [ae_restrict_iff' (abox_measurable N ℓ)]
    exact ae_of_all _ (fun x hx => by rw [Real.norm_eq_abs]; exact hb x hx)
  have hIntF : IntegrableOn (fun x : X N => P x ^ 2 * fib (x i)) (abox N ℓ) volume :=
    hIntb ((hPm.pow_const 2).mul hfibmi) hbP
  have hIntG : IntegrableOn (fun x : X N => Q x * P x * fib (x i)) (abox N ℓ) volume :=
    hIntb ((hQm.mul hPm).mul hfibmi) hbQP
  have hIntH : IntegrableOn (fun x : X N => Q x ^ 2 * fib (x i)) (abox N ℓ) volume :=
    hIntb ((hQm.pow_const 2).mul hfibmi) hbQ
  -- the linearity of the integral on the three pieces
  have hInt2G : Integrable (fun x : X N => 2 * (Q x * P x * fib (x i)))
      (volume.restrict (abox N ℓ)) := hIntG.const_mul 2
  have h2G : 2 * (∫ x in abox N ℓ, Q x * P x * fib (x i))
      = ∫ x in abox N ℓ, 2 * (Q x * P x * fib (x i)) :=
    (integral_const_mul 2 (fun x : X N => Q x * P x * fib (x i))).symm
  have hA1 : (∫ x in abox N ℓ, P x ^ 2 * fib (x i))
        + (∫ x in abox N ℓ, 2 * (Q x * P x * fib (x i)))
      = ∫ x in abox N ℓ, (P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i))) :=
    (integral_add hIntF hInt2G).symm
  have hA2 : (∫ x in abox N ℓ, (P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i))))
        + (∫ x in abox N ℓ, Q x ^ 2 * fib (x i))
      = ∫ x in abox N ℓ,
          (P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i))) + Q x ^ 2 * fib (x i) :=
    (integral_add (hIntF.add hInt2G) hIntH).symm
  have hA3 : (∫ x in abox N ℓ,
          (P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i))) + Q x ^ 2 * fib (x i))
      = ∫ x in abox N ℓ, Φ x ^ 2 * fib (x i) := by
    apply setIntegral_congr_fun (abox_measurable N ℓ)
    intro x _
    show (P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i))) + Q x ^ 2 * fib (x i)
      = Φ x ^ 2 * fib (x i)
    rw [← hpt x]
    ring
  linarith [h2G, hA1, hA2, hA3]

theorem boxMuSumAgree {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w w1 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw1c : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => w1 p.1 p.2))
    (hw : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => w p.1 p.2))
    (hw1rel : ∀ x y : EuclideanSpace ℝ (Fin 3), w1 x y = w x y * (1 - om x y))
    (hsuppA : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y ≠ 0 → x ∈ A ∧ y ∈ A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i)
      + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i)
      + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i)
      = ∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i := by
  have hLHS : (∑ i : Fin N, boxMuP volA ℓ A w1 Φ i)
        + 2 * (∑ i : Fin N, boxMuQP volA ℓ A w1 Φ i)
        + (∑ i : Fin N, boxMuQ volA ℓ A w1 Φ i)
      = ∑ i : Fin N,
          (boxMuP volA ℓ A w1 Φ i + 2 * boxMuQP volA ℓ A w1 Φ i + boxMuQ volA ℓ A w1 Φ i) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hLHS]
  exact Finset.sum_congr rfl
    (fun i _ => boxMu_summand hℓ hvol hA hvolA hAc hw1c hw1rel hsuppA hΦc i)

end Work.BoseFixB1S
