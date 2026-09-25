import Mathlib
import Submission.Work.NN.Core.fiberBeurling
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.norm_beurlingTransform_le
import Submission.Work.CR.Flat.Cauchy.norm_beurlingTransform_holder
import Submission.Work.CR.Flat.Cauchy.norm_beurlingTransform_sub_le_explicit
import Submission.Work.NN.Ratio.holderNorm_zero_le_of_bounds

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory

namespace Work.NN.Core

/-! ## Helper: the global `α`-Hölder constant of a function supported in a disc

A function `f : ℂ → ℂ` which vanishes on and outside the circle of radius `R`, is continuous, and
is differentiable inside the disc with `‖fderiv ℝ f z‖ ≤ M` there, is globally `α`-Hölder with
constant `(2R)^{1-α} M`.  This is the "geometric decay argument to reach the boundary" mentioned in
the plan: near the boundary of the disc `f` decays like `R - ‖z‖`, and the mean value inequality
on the radial segment turns that into the missing factor `‖x - y‖ ^ α`. -/

lemma holderConst_global_of_supported {R α M : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : 0 ≤ M) {f : ℂ → ℂ} (hcont : Continuous f)
    (hsupp : ∀ z : ℂ, R ≤ ‖z‖ → f z = 0)
    (hdiff : ∀ z : ℂ, ‖z‖ < R → DifferentiableAt ℝ f z)
    (hderiv : ∀ z : ℂ, ‖z‖ < R → ‖fderiv ℝ f z‖ ≤ M) :
    ∀ x y : ℂ, ‖f x - f y‖ ≤ (2 * R) ^ (1 - α) * M * ‖x - y‖ ^ α := by
  have hα0 : (0 : ℝ) ≤ 1 - α := by linarith
  -- mean value inequality along a segment contained in the open disc
  have seg : ∀ u v : ℂ, (∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → ‖u + t • (v - u)‖ < R) →
      ‖f v - f u‖ ≤ M * ‖v - u‖ := by
    intro u v hseg
    have hc : ∀ t : ℝ, HasDerivAt (fun t : ℝ => u + t • (v - u)) (v - u) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => t • (v - u)) ((1 : ℝ) • (v - u)) t :=
        (hasDerivAt_id' t).smul_const (v - u)
      simpa using h1.const_add u
    have hder : ∀ t ∈ Set.Ico (0 : ℝ) 1,
        HasDerivWithinAt (f ∘ fun t : ℝ => u + t • (v - u))
          ((fderiv ℝ f (u + t • (v - u))) (v - u)) (Set.Ici t) t := by
      intro t ht
      exact ((hdiff _ (hseg t ht)).hasFDerivAt.comp_hasDerivAt t (hc t)).hasDerivWithinAt
    have hbd : ∀ t ∈ Set.Ico (0 : ℝ) 1,
        ‖(fderiv ℝ f (u + t • (v - u))) (v - u)‖ ≤ M * ‖v - u‖ := by
      intro t ht
      calc ‖(fderiv ℝ f (u + t • (v - u))) (v - u)‖
          ≤ ‖fderiv ℝ f (u + t • (v - u))‖ * ‖v - u‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M * ‖v - u‖ := mul_le_mul_of_nonneg_right (hderiv _ (hseg t ht)) (norm_nonneg _)
    have hcont' : ContinuousOn (f ∘ fun t : ℝ => u + t • (v - u)) (Set.Icc (0 : ℝ) 1) :=
      (hcont.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment (a := (0 : ℝ)) (b := 1)
      (f := f ∘ fun t : ℝ => u + t • (v - u))
      (f' := fun t : ℝ => (fderiv ℝ f (u + t • (v - u))) (v - u))
      (C := M * ‖v - u‖) hcont' hder hbd 1 (by norm_num)
    simpa using h
  -- decay at the boundary
  have decay : ∀ u : ℂ, ‖u‖ < R → ‖f u‖ ≤ M * (R - ‖u‖) := by
    intro u hu
    rcases eq_or_ne u 0 with hu0 | hu0
    · subst hu0
      set s : ℂ := (R : ℂ) with hsd
      have hsnorm : ‖s‖ = R := by
        rw [hsd, Complex.norm_real, Real.norm_of_nonneg hR.le]
      have hseg : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → ‖(0 : ℂ) + t • (s - 0)‖ < R := by
        intro t ht
        have ht1 : t < 1 := ht.2
        have ht0 : 0 ≤ t := ht.1
        rw [zero_add, sub_zero, hsd, norm_smul, Complex.norm_real, Real.norm_of_nonneg hR.le,
          Real.norm_of_nonneg ht0]
        nlinarith
      have h1 := seg 0 s hseg
      rw [hsupp s hsnorm.ge, zero_sub, norm_neg, sub_zero] at h1
      simpa [hsnorm, norm_zero] using h1
    · have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      set lam : ℝ := R / ‖u‖ with hlamd
      have hlam1 : 1 < lam := (lt_div_iff₀ hupos).mpr (by linarith)
      have hlam0 : 0 ≤ lam := le_of_lt (lt_trans zero_lt_one hlam1)
      set s : ℂ := lam • u with hsd
      have hsnorm : ‖s‖ = R := by
        rw [hsd, norm_smul, Real.norm_of_nonneg hlam0, hlamd,
          div_mul_cancel₀ R (ne_of_gt hupos)]
      have hsum : s - u = (lam - 1) • u := by
        rw [hsd, sub_smul, one_smul]
      have hseg : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → ‖u + t • (s - u)‖ < R := by
        intro t ht
        have ht1 : t < 1 := ht.2
        have ht0 : 0 ≤ t := ht.1
        have heq : u + t • (s - u) = (1 + t * (lam - 1)) • u := by
          rw [hsum, smul_smul]
          calc u + (t * (lam - 1)) • u = (1 : ℝ) • u + (t * (lam - 1)) • u := by rw [one_smul]
            _ = (1 + t * (lam - 1)) • u := (add_smul 1 (t * (lam - 1)) u).symm
        rw [heq, norm_smul, Real.norm_of_nonneg (by nlinarith : (0 : ℝ) ≤ 1 + t * (lam - 1))]
        have hlt : 1 + t * (lam - 1) < lam := by nlinarith
        have := mul_lt_mul_of_pos_right hlt hupos
        rwa [hlamd, div_mul_cancel₀ R (ne_of_gt hupos)] at this
      have h1 := seg u s hseg
      rw [hsupp s hsnorm.ge, zero_sub, norm_neg] at h1
      have h2 : ‖s - u‖ = R - ‖u‖ := by
        rw [hsum, norm_smul, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ lam - 1), hlamd,
          sub_mul, div_mul_cancel₀ R (ne_of_gt hupos), one_mul]
      rw [h2] at h1
      simpa using h1
  -- main pointwise bound
  have key : ∀ u v : ℂ, ‖u‖ < R → ‖f v - f u‖ ≤ (2 * R) ^ (1 - α) * M * ‖v - u‖ ^ α := by
    intro u v hu
    by_cases hv : ‖v‖ < R
    · have hseg : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → ‖u + t • (v - u)‖ < R := by
        intro t ht
        have ht0 : 0 ≤ t := ht.1
        have ht1 : t < 1 := ht.2
        have heq : u + t • (v - u) = (1 - t) • u + t • v := by
          rw [smul_sub, sub_smul, one_smul]
          abel
        rw [heq]
        calc ‖(1 - t) • u + t • v‖ ≤ ‖(1 - t) • u‖ + ‖t • v‖ := norm_add_le _ _
          _ = (1 - t) * ‖u‖ + t * ‖v‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
                Real.norm_of_nonneg ht0]
          _ < (1 - t) * R + t * R := by
              have h1 : (1 - t) * ‖u‖ < (1 - t) * R :=
                mul_lt_mul_of_pos_left hu (by linarith)
              have h2 : t * ‖v‖ ≤ t * R := mul_le_mul_of_nonneg_left (le_of_lt hv) ht0
              linarith
          _ = R := by ring
      have h1 := seg u v hseg
      have hvu : ‖v - u‖ ≤ 2 * R := by
        calc ‖v - u‖ ≤ ‖v‖ + ‖u‖ := norm_sub_le _ _
          _ ≤ R + R := by linarith
          _ = 2 * R := by ring
      have hmain : M * ‖v - u‖ ≤ (2 * R) ^ (1 - α) * M * ‖v - u‖ ^ α := by
        by_cases h0 : ‖v - u‖ = 0
        · rw [h0, Real.zero_rpow (ne_of_gt hα)]
          simp
        · have hpos : 0 < ‖v - u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
          have hpow : ‖v - u‖ ^ (1 - α) ≤ (2 * R) ^ (1 - α) :=
            Real.rpow_le_rpow (norm_nonneg _) hvu hα0
          calc M * ‖v - u‖ = M * (‖v - u‖ ^ (1 - α) * ‖v - u‖ ^ α) := by
                rw [← Real.rpow_add hpos (1 - α) α, show 1 - α + α = 1 from by ring,
                  Real.rpow_one]
            _ = (M * ‖v - u‖ ^ (1 - α)) * ‖v - u‖ ^ α := by ring
            _ ≤ (M * (2 * R) ^ (1 - α)) * ‖v - u‖ ^ α :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hM)
                  (Real.rpow_nonneg (norm_nonneg _) _)
            _ = (2 * R) ^ (1 - α) * M * ‖v - u‖ ^ α := by ring
      exact le_trans h1 hmain
    · have hvR : R ≤ ‖v‖ := not_lt.mp hv
      have hfv : f v = 0 := hsupp v hvR
      have hdec := decay u hu
      have hR0 : 0 ≤ R - ‖u‖ := by linarith
      have hle2 : R - ‖u‖ ≤ ‖v - u‖ := by
        have h := norm_sub_norm_le v u
        linarith
      have hpow1 : (R - ‖u‖) ^ (1 - α) ≤ (2 * R) ^ (1 - α) := by
        refine Real.rpow_le_rpow hR0 ?_ hα0
        linarith [norm_nonneg u]
      have hstep : M * (R - ‖u‖) = M * ((R - ‖u‖) ^ (1 - α) * (R - ‖u‖) ^ α) := by
        by_cases h0 : R - ‖u‖ = 0
        · rw [h0, Real.zero_rpow (ne_of_gt hα), mul_zero, mul_zero, mul_zero]
        · have hpos : 0 < R - ‖u‖ := lt_of_le_of_ne hR0 (Ne.symm h0)
          rw [← Real.rpow_add hpos (1 - α) α, show 1 - α + α = 1 from by ring,
            Real.rpow_one]
      rw [hfv, zero_sub, norm_neg]
      calc ‖f u‖ ≤ M * (R - ‖u‖) := hdec
        _ = M * ((R - ‖u‖) ^ (1 - α) * (R - ‖u‖) ^ α) := hstep
        _ = (M * (R - ‖u‖) ^ (1 - α)) * (R - ‖u‖) ^ α := by ring
        _ ≤ (M * (2 * R) ^ (1 - α)) * ‖v - u‖ ^ α := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hpow1 hM)
              (Real.rpow_le_rpow hR0 hle2 hα.le) (Real.rpow_nonneg hR0 α) ?_
            exact mul_nonneg hM (Real.rpow_nonneg (by linarith) _)
        _ = (2 * R) ^ (1 - α) * M * ‖v - u‖ ^ α := by ring
  intro x y
  by_cases hx : ‖x‖ < R
  · have h := key x y hx
    rwa [norm_sub_rev (f y) (f x), norm_sub_rev y x] at h
  · by_cases hy : ‖y‖ < R
    · exact key y x hy
    · rw [hsupp x (not_lt.mp hx), hsupp y (not_lt.mp hy), sub_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) hM)
        (Real.rpow_nonneg (norm_nonneg _) _)

/-! ## Helper: additivity of the Beurling transform in the data -/

theorem norm_beurlingTransform_sub_le_of_holder {ρ α : ℝ} (hρ : 0 < ρ) (hα : 0 < α) :
    ∀ {g h : ℂ → ℂ} {Cg Ch C' : ℝ}, 0 ≤ Cg → 0 ≤ Ch → 0 ≤ C' →
      (∀ x y : ℂ, ‖g x - g y‖ ≤ Cg * ‖x - y‖ ^ α) →
      (∀ x y : ℂ, ‖h x - h y‖ ≤ Ch * ‖x - y‖ ^ α) →
      (∀ x y : ℂ, ‖(g x - h x) - (g y - h y)‖ ≤ C' * ‖x - y‖ ^ α) →
      ∀ z : ℂ, ‖z‖ < ρ →
        ‖Work.CR.Flat.beurlingTransform ρ g z - Work.CR.Flat.beurlingTransform ρ h z‖
          ≤ 2 * C' * ρ ^ α / α := by
  intro g h Cg Ch C' hCg hCh hC' hg hh hgh z hz
  have hIg : IntegrableOn (fun w : ℂ => (g (z + w) - g z) / w ^ 2) (Metric.ball 0 ρ) :=
    Work.CR.Flat.Cauchy.BeurlingCZ.integrableOn_beurlingIntegrand hα hCg hg z
  have hIh : IntegrableOn (fun w : ℂ => (h (z + w) - h z) / w ^ 2) (Metric.ball 0 ρ) :=
    Work.CR.Flat.Cauchy.BeurlingCZ.integrableOn_beurlingIntegrand hα hCh hh z
  have hkey : (∫ w in Metric.ball 0 ρ, (g (z + w) - g z) / w ^ 2)
      - (∫ w in Metric.ball 0 ρ, (h (z + w) - h z) / w ^ 2)
      = ∫ w in Metric.ball 0 ρ,
          ((g - h) (z + w) - (g - h) z) / w ^ 2 := by
    rw [← integral_sub hIg hIh]
    refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    simp only [Pi.sub_apply]
    ring
  have hmain1 : Work.CR.Flat.beurlingTransform ρ g z - Work.CR.Flat.beurlingTransform ρ h z
      = -((Real.pi : ℂ))⁻¹
        * ((∫ w in Metric.ball 0 ρ, (g (z + w) - g z) / w ^ 2)
            - (∫ w in Metric.ball 0 ρ, (h (z + w) - h z) / w ^ 2)) := by
    simp only [Work.CR.Flat.beurlingTransform]
    ring
  have hmain2 : -((Real.pi : ℂ))⁻¹
        * ((∫ w in Metric.ball 0 ρ, (g (z + w) - g z) / w ^ 2)
            - (∫ w in Metric.ball 0 ρ, (h (z + w) - h z) / w ^ 2))
      = Work.CR.Flat.beurlingTransform ρ (fun w => g w - h w) z := by
    rw [hkey]
    simp only [Work.CR.Flat.beurlingTransform, Pi.sub_apply]
  rw [hmain1.trans hmain2]
  exact Work.CR.Flat.Cauchy.norm_beurlingTransform_le hα hC' hgh hz

/-! ## Slices of a function in one coordinate -/

section Slice

variable {n : ℕ}

/-- A slice of band-supported data is supported in the disc of radius `R`. -/
lemma fiberSlice_eq_zero_of_band {R : ℝ} {j : Fin n} {v : Cn n → ℂ} (hband : fiberBand R j v)
    (z : Cn n) {w : ℂ} (hw : R ≤ ‖w‖) : fiberSlice j v z w = 0 := by
  rw [fiberSlice_apply]
  exact hband _ (by simpa using hw)

/-- `w ↦ Function.update z j w` is differentiable (componentwise it is either the identity or a
constant). -/
lemma differentiableAt_update (z : Cn n) (j : Fin n) (w : ℂ) :
    DifferentiableAt ℝ (Function.update z j) w := by
  rw [differentiableAt_pi]
  intro i
  by_cases hi : i = j
  · rw [show (fun t : ℂ => Function.update z j t i) = fun t : ℂ => t from by
      funext t; rw [Function.update_apply, if_pos hi]]
    exact differentiableAt_id
  · rw [show (fun t : ℂ => Function.update z j t i) = fun _ : ℂ => z i from by
      funext t; rw [Function.update_apply, if_neg hi]]
    exact differentiableAt_const _

/-- The derivative of `w ↦ Function.update z j w` is the injection `Pi.single j` (an isometry). -/
lemma fderiv_update_eq (z : Cn n) (j : Fin n) (w : ℂ) :
    fderiv ℝ (Function.update z j) w = ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j := by
  rw [fderiv_update]
  ext c i
  rw [ContinuousLinearMap.pi_apply]
  rw [show (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) c = Pi.single j c from rfl]
  by_cases hi : i = j
  · rw [hi, Pi.single_eq_same, Pi.single_eq_same]
    rfl
  · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi]
    rfl

lemma norm_fderiv_update_eq (z : Cn n) (j : Fin n) (w : ℂ) :
    ‖fderiv ℝ (Function.update z j) w‖ = 1 := by
  rw [fderiv_update_eq, ContinuousLinearMap.norm_single]

lemma differentiableAt_fiberSlice {j : Fin n} {v : Cn n → ℂ} (hv : Differentiable ℝ v) (z : Cn n)
    (w : ℂ) : DifferentiableAt ℝ (fiberSlice j v z) w :=
  (hv _).comp w (differentiableAt_update z j w)

/-- Chain rule for the slice. -/
lemma fderiv_fiberSlice {j : Fin n} {v : Cn n → ℂ} (hv : Differentiable ℝ v) (z : Cn n) (w : ℂ) :
    fderiv ℝ (fiberSlice j v z) w
      = (fderiv ℝ v (Function.update z j w)).comp (fderiv ℝ (Function.update z j) w) := by
  have hcomp : fiberSlice j v z = v ∘ Function.update z j := rfl
  rw [hcomp, fderiv_comp w (hv _) (differentiableAt_update z j w)]

/-- The update map sends the disc of radius `R` into the access polydisc. -/
private lemma update_mem_fiberAccess {r : Fin n → ℝ} {j : Fin n} {R : ℝ} {z : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc 0 r) {w : ℂ} (hw : ‖w‖ < R) :
    Function.update z j w ∈ fiberAccess r j R := by
  rw [mem_fiberAccess]
  exact ⟨fun i hi => by rw [Function.update_of_ne hi]; simpa using hz i,
    by rwa [Function.update_self]⟩

/-- Derivative bound for a slice. -/
lemma norm_fderiv_fiberSlice_le {R M : ℝ} {j : Fin n} {r : Fin n → ℝ}
    {v : Cn n → ℂ} (hv : Differentiable ℝ v) {z : Cn n} (hz : z ∈ Work.CR.Flat.polydisc 0 r)
    (hderiv : ∀ x ∈ fiberAccess r j R, ‖fderiv ℝ v x‖ ≤ M) :
    ∀ w : ℂ, ‖w‖ < R → ‖fderiv ℝ (fiberSlice j v z) w‖ ≤ M := by
  intro w hw
  rw [fderiv_fiberSlice hv z w]
  calc ‖(fderiv ℝ v (Function.update z j w)).comp (fderiv ℝ (Function.update z j) w)‖
      ≤ ‖fderiv ℝ v (Function.update z j w)‖ * ‖fderiv ℝ (Function.update z j) w‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fderiv ℝ v (Function.update z j w)‖ := by rw [norm_fderiv_update_eq]; ring
    _ ≤ M := hderiv _ (update_mem_fiberAccess hz hw)

/-- The norm of the difference of the `fderiv`s is dominated by the norm of the difference of the
corresponding `1`-multilinear maps: the latter is a supremum over the constant functions
`m = fun _ => e`. -/
lemma norm_fderivWithin_sub_le_iterated {A : Set (Cn n)} {v : Cn n → ℂ} {x y : Cn n}
    (hx : UniqueDiffWithinAt ℝ A x) (hy : UniqueDiffWithinAt ℝ A y) :
    ‖fderivWithin ℝ v A x - fderivWithin ℝ v A y‖
      ≤ ‖iteratedFDerivWithin ℝ 1 v A x - iteratedFDerivWithin ℝ 1 v A y‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun e => ?_
  have h := ContinuousMultilinearMap.le_opNorm
    (iteratedFDerivWithin ℝ 1 v A x - iteratedFDerivWithin ℝ 1 v A y) (fun _ : Fin 1 => e)
  have heq1 : (fderivWithin ℝ v A x - fderivWithin ℝ v A y) e
      = (iteratedFDerivWithin ℝ 1 v A x - iteratedFDerivWithin ℝ 1 v A y)
          (fun _ : Fin 1 => e) := by
    rw [sub_apply, sub_apply,
      iteratedFDerivWithin_one_apply (𝕜 := ℝ) (s := A) (f := v) (x := x) hx,
      iteratedFDerivWithin_one_apply (𝕜 := ℝ) (s := A) (f := v) (x := y) hy]
  rw [heq1]
  simpa using h

/-- Derivative bound for the difference of two slices. -/
lemma norm_fderiv_fiberSlice_sub_le {R α Hs : ℝ} {j : Fin n} {r : Fin n → ℝ}
    {v : Cn n → ℂ} (hv : Differentiable ℝ v) {z z' : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc 0 r) (hz' : z' ∈ Work.CR.Flat.polydisc 0 r) (hα : 0 < α)
    (hHs : 0 ≤ Hs)
    (hhs : ∀ x ∈ fiberAccess r j R, ∀ y ∈ fiberAccess r j R,
        ‖fderiv ℝ v x - fderiv ℝ v y‖ ≤ Hs * ‖x - y‖ ^ α) :
    ∀ w : ℂ, ‖w‖ < R →
      ‖fderiv ℝ (fiberSlice j v z - fiberSlice j v z') w‖ ≤ Hs * ‖z - z'‖ ^ α := by
  intro w hw
  have h1 : fderiv ℝ (fiberSlice j v z - fiberSlice j v z') w
      = fderiv ℝ (fiberSlice j v z) w - fderiv ℝ (fiberSlice j v z') w :=
    fderiv_sub (differentiableAt_fiberSlice hv z w) (differentiableAt_fiberSlice hv z' w)
  rw [h1, fderiv_fiberSlice hv z w, fderiv_fiberSlice hv z' w, fderiv_update_eq z j w,
    fderiv_update_eq z' j w]
  have hcomp : (fderiv ℝ v (Function.update z j w)).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)
        - (fderiv ℝ v (Function.update z' j w)).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)
      = (fderiv ℝ v (Function.update z j w) - fderiv ℝ v (Function.update z' j w)).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) := by
    ext c
    simp [ContinuousLinearMap.comp_apply]
  rw [hcomp]
  calc ‖((fderiv ℝ v (Function.update z j w) - fderiv ℝ v (Function.update z' j w)).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j))‖
      ≤ ‖fderiv ℝ v (Function.update z j w) - fderiv ℝ v (Function.update z' j w)‖
          * ‖ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fderiv ℝ v (Function.update z j w) - fderiv ℝ v (Function.update z' j w)‖ := by
        rw [ContinuousLinearMap.norm_single]; ring
    _ ≤ Hs * ‖Function.update z j w - Function.update z' j w‖ ^ α :=
        hhs _ (update_mem_fiberAccess hz hw) _ (update_mem_fiberAccess hz' hw)
    _ ≤ Hs * ‖z - z'‖ ^ α := by
        refine mul_le_mul_of_nonneg_left ?_ hHs
        refine Real.rpow_le_rpow (norm_nonneg _) ?_ hα.le
        rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
        intro i
        by_cases hi : i = j
        · subst hi
          simp
        · rw [Pi.sub_apply, Function.update_of_ne hi, Function.update_of_ne hi]
          exact norm_le_pi_norm (z - z') i

end Slice

/-- The order-zero estimate for the fibrewise Beurling transform `fiberBeurling R j v` (the `(1,0)`-derivative of the fixed-disc potential) on `polydisc 0 r`, for data supported in the band `‖z j‖ < R`, in terms of the `C^{1,α}` norm of the data on the access polydisc `fiberAccess r j R`. The transverse Hölder differences of the Beurling transform require one derivative of the data; the fibre differences and the sup bound only need the `C^{0,α}` norm.

Suggested route. With `F := fiberSlice j v z` (supported in `ball 0 R` by `hband`) and `ρ := 2R`, `fiberBeurling R j v z = beurlingTransform ρ F (z j)`. The sup bound is `Work.CR.Flat.Cauchy.norm_beurlingTransform_le` (no support needed) with the *global* `α`-Hölder constant of `F`, which is controlled by `‖v‖_{C^{0,α}(A)} ≤ ‖v‖_{C^{1,α}(A)}` (the slice is continuous with support in `ball 0 R`, and its `α`-seminorm over that ball is the `α`-seminorm of `v` on `A`; use a geometric decay argument to reach the boundary). The fibre difference is `Work.CR.Flat.Cauchy.norm_beurlingTransform_holder`. For the transverse difference, use `beurlingTransform`'s linearity: the difference of the two transforms is the Beurling transform of the difference of the slices `G = F_z - F_{z'}`, whose global `α`-Hölder constant is bounded by `C ‖v‖_{C^{1,α}(A)} ‖z - z'‖^α` (its `α`-seminorm over `ball 0 R` is estimated by the sup of its Laplacian/derivative, i.e. by the `α`-seminorm of the first derivatives of `v`, via a mean value bound), and apply `norm_beurlingTransform_le` to `G`. -/
theorem holderNorm_zero_fiberBeurling_le {n : ℕ} {R α : ℝ} (hR : 0 < R) (j : Fin n) (hα : 0 < α)
    (hα1 : α < 1) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Cn n → ℂ, ContDiff ℝ 1 v → fiberBand R j v →
      Work.CR.Flat.holderNorm 0 α (fiberBeurling R j v) (Work.CR.Flat.polydisc 0 r)
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm 1 α v (fiberAccess r j R) := by
  obtain ⟨Ch, hChpos, hCh⟩ :=
    Work.CR.Flat.Cauchy.norm_beurlingTransform_holder (ρ := 2 * R) (α := α)
      (by linarith) hα hα1
  have hKpos : 0 < 8 * R / α + Ch * (2 * R) ^ (1 - α) := by
    have h1 : 0 < 8 * R / α := by positivity
    have h2 : 0 ≤ Ch * (2 * R) ^ (1 - α) :=
      mul_nonneg hChpos.le (Real.rpow_nonneg (by linarith) _)
    linarith
  have hK2pos : 0 ≤ Ch * (2 * R) ^ (1 - α) + 4 * R / α := by
    have h1 : 0 ≤ Ch * (2 * R) ^ (1 - α) :=
      mul_nonneg hChpos.le (Real.rpow_nonneg (by linarith) _)
    have h2 : 0 ≤ 4 * R / α := by positivity
    linarith
  refine ⟨max 1 (8 * R / α + Ch * (2 * R) ^ (1 - α)), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  · intro v hv hband
    have hmain : Work.CR.Flat.holderNorm 0 α (fiberBeurling R j v)
          (Work.CR.Flat.polydisc 0 r)
        ≤ ENNReal.ofReal (8 * R / α + Ch * (2 * R) ^ (1 - α))
            * Work.CR.Flat.holderNorm 1 α v (fiberAccess r j R) := by
      let N : ℝ≥0∞ := Work.CR.Flat.holderNorm 1 α v (fiberAccess r j R)
      let M : ℝ := N.toReal
      change Work.CR.Flat.holderNorm 0 α (fiberBeurling R j v) (Work.CR.Flat.polydisc 0 r)
        ≤ ENNReal.ofReal (8 * R / α + Ch * (2 * R) ^ (1 - α)) * N
      by_cases hNtop : N = ⊤
      · rw [hNtop, ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; exact hKpos)]
        exact le_top
      · have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
        have hN_eq : N = ENNReal.ofReal M := (ENNReal.ofReal_toReal hNtop).symm
        have hAopen : IsOpen (fiberAccess r j R) := fiberAccess_isOpen r j R
        have hderivA : ∀ x ∈ fiberAccess r j R, ‖fderiv ℝ v x‖ ≤ M := by
          intro x hx
          have h1 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ 1 v (fiberAccess r j R) x‖ ≤ N :=
            le_trans (Work.CR.Flat.le_iterDerivNorm 1 v (fiberAccess r j R) hx)
              (Work.CR.Flat.iterDerivNorm_le_holderNorm 1 α v (fiberAccess r j R) le_rfl)
          have h2 : ‖iteratedFDerivWithin ℝ 1 v (fiberAccess r j R) x‖ = ‖fderiv ℝ v x‖ := by
            rw [iteratedFDerivWithin_of_isOpen 1 hAopen hx]
            exact norm_iteratedFDeriv_one v
          rw [h2] at h1
          exact (ENNReal.ofReal_le_iff_le_toReal hNtop).mp h1
        have hhsWithin : ∀ x ∈ fiberAccess r j R, ∀ y ∈ fiberAccess r j R,
            ‖fderivWithin ℝ v (fiberAccess r j R) x
              - fderivWithin ℝ v (fiberAccess r j R) y‖ ≤ M * ‖x - y‖ ^ α := by
          intro x hx y hy
          by_cases hxy : x = y
          · subst hxy
            simp only [sub_self, norm_zero]
            exact mul_nonneg hM0 (Real.rpow_nonneg le_rfl α)
          · have h1 : ENNReal.ofReal (‖iteratedFDerivWithin ℝ 1 v (fiberAccess r j R) x
                - iteratedFDerivWithin ℝ 1 v (fiberAccess r j R) y‖ / ‖x - y‖ ^ α) ≤ N :=
              le_trans (Work.CR.Flat.le_holderSeminorm 1 α v (fiberAccess r j R) hx hy hxy)
                (Work.CR.Flat.holderSeminorm_le_holderNorm 1 α v (fiberAccess r j R) le_rfl)
            have h2 := (ENNReal.ofReal_le_iff_le_toReal hNtop).mp h1
            have hpos : 0 < ‖x - y‖ ^ α :=
              Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
            rw [div_le_iff₀ hpos] at h2
            exact le_trans (norm_fderivWithin_sub_le_iterated
              (hAopen.uniqueDiffWithinAt hx) (hAopen.uniqueDiffWithinAt hy)) h2
        have hhsA : ∀ x ∈ fiberAccess r j R, ∀ y ∈ fiberAccess r j R,
            ‖fderiv ℝ v x - fderiv ℝ v y‖ ≤ M * ‖x - y‖ ^ α := by
          intro x hx y hy
          have h := hhsWithin x hx y hy
          rwa [fderivWithin_of_isOpen hAopen hx, fderivWithin_of_isOpen hAopen hy] at h
        have hslice : ∀ z ∈ Work.CR.Flat.polydisc 0 r, ∀ x y : ℂ,
            ‖fiberSlice j v z x - fiberSlice j v z y‖
              ≤ (2 * R) ^ (1 - α) * M * ‖x - y‖ ^ α := by
          intro z hz x y
          refine holderConst_global_of_supported hR hα (le_of_lt hα1) hM0
            (hv.continuous.comp (continuous_update z j)) ?_ ?_ ?_ x y
          · intro w hw
            exact fiberSlice_eq_zero_of_band hband z hw
          · intro w hw
            exact differentiableAt_fiberSlice hv.differentiable_one z w
          · intro w hw
            exact norm_fderiv_fiberSlice_le hv.differentiable_one hz hderivA w hw
        have hpow : (2 * R) ^ (1 - α) * (2 * R) ^ α = 2 * R := by
          rw [← Real.rpow_add (by linarith : (0 : ℝ) < 2 * R) (1 - α) α,
            show 1 - α + α = 1 from by ring, Real.rpow_one]
        have hbound1 : ∀ z ∈ Work.CR.Flat.polydisc 0 r,
            ‖fiberBeurling R j v z‖ ≤ (4 * R / α) * M := by
          intro z hz
          have hzj : ‖z j‖ < 2 * R := by
            have h1 : ‖z j‖ < R := lt_trans (by simpa using hz j) (hrR j)
            linarith
          have h := Work.CR.Flat.Cauchy.norm_beurlingTransform_le (ρ := 2 * R) (α := α)
            (C := (2 * R) ^ (1 - α) * M) hα (mul_nonneg (by positivity) hM0)
            (hslice z hz) hzj
          calc ‖fiberBeurling R j v z‖
              = ‖Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z) (z j)‖ := rfl
            _ ≤ 2 * ((2 * R) ^ (1 - α) * M) * (2 * R) ^ α / α := h
            _ = (4 * R / α) * M := by
                rw [show 2 * ((2 * R) ^ (1 - α) * M) * (2 * R) ^ α / α
                    = 2 * ((2 * R) ^ (1 - α) * (2 * R) ^ α) * M / α from by ring, hpow]
                ring
        have hbound2 : ∀ z ∈ Work.CR.Flat.polydisc 0 r, ∀ z' ∈ Work.CR.Flat.polydisc 0 r,
            ‖fiberBeurling R j v z - fiberBeurling R j v z'‖
              ≤ ((Ch * (2 * R) ^ (1 - α) + 4 * R / α) * M) * ‖z - z'‖ ^ α := by
          intro z hz z' hz'
          have hzjR : ‖z j‖ < R := lt_trans (by simpa using hz j) (hrR j)
          have hz'jR : ‖z' j‖ < R := lt_trans (by simpa using hz' j) (hrR j)
          have hzj_ball : z j ∈ Metric.ball (0 : ℂ) ((2 * R) / 2) := by
            rw [Metric.mem_ball, dist_eq_norm, sub_zero]
            rw [show (2 * R) / 2 = R from by ring]
            exact hzjR
          have hz'j_ball : z' j ∈ Metric.ball (0 : ℂ) ((2 * R) / 2) := by
            rw [Metric.mem_ball, dist_eq_norm, sub_zero]
            rw [show (2 * R) / 2 = R from by ring]
            exact hz'jR
          have hMz : 0 ≤ M * ‖z - z'‖ ^ α :=
            mul_nonneg hM0 (Real.rpow_nonneg (norm_nonneg _) _)
          have hC'z : 0 ≤ (2 * R) ^ (1 - α) * (M * ‖z - z'‖ ^ α) :=
            mul_nonneg (Real.rpow_nonneg (by linarith) _) hMz
          have hsuppz : Work.CR.Flat.SupportedInBall ((2 * R) / 2) (fiberSlice j v z) := by
            intro w hw
            refine fiberSlice_eq_zero_of_band hband z ?_
            rwa [show (2 * R) / 2 = R from by ring] at hw
          have hA : ‖Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z) (z j)
                - Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z) (z' j)‖
              ≤ Ch * ((2 * R) ^ (1 - α) * M) * ‖z - z'‖ ^ α := by
            have h := hCh ((2 * R) ^ (1 - α) * M) (mul_nonneg (by positivity) hM0)
              (f := fiberSlice j v z) (hslice z hz) hsuppz (z j) hzj_ball (z' j) hz'j_ball
            refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by positivity))
            refine Real.rpow_le_rpow (norm_nonneg _) ?_ hα.le
            calc ‖z j - z' j‖ = ‖(z - z') j‖ := by rw [Pi.sub_apply]
              _ ≤ ‖z - z'‖ := norm_le_pi_norm _ j
          have hG : ∀ x y : ℂ,
              ‖(fiberSlice j v z x - fiberSlice j v z' x)
                - (fiberSlice j v z y - fiberSlice j v z' y)‖
              ≤ ((2 * R) ^ (1 - α) * (M * ‖z - z'‖ ^ α)) * ‖x - y‖ ^ α := by
            intro x y
            refine holderConst_global_of_supported hR hα (le_of_lt hα1) hMz
              ((hv.continuous.comp (continuous_update z j)).sub
                (hv.continuous.comp (continuous_update z' j))) ?_ ?_ ?_ x y
            · intro w hw
              show fiberSlice j v z w - fiberSlice j v z' w = 0
              rw [fiberSlice_eq_zero_of_band hband z hw,
                fiberSlice_eq_zero_of_band hband z' hw, sub_zero]
            · intro w hw
              exact (differentiableAt_fiberSlice hv.differentiable_one z w).sub
                (differentiableAt_fiberSlice hv.differentiable_one z' w)
            · intro w hw
              exact norm_fderiv_fiberSlice_sub_le hv.differentiable_one hz hz' hα hM0 hhsA w hw
          have hB : ‖Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z) (z' j)
                - Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z') (z' j)‖
              ≤ (4 * R / α) * (M * ‖z - z'‖ ^ α) := by
            have h := norm_beurlingTransform_sub_le_of_holder (ρ := 2 * R) (α := α)
              (by linarith) hα (g := fiberSlice j v z) (h := fiberSlice j v z')
              (Cg := (2 * R) ^ (1 - α) * M) (Ch := (2 * R) ^ (1 - α) * M)
              (C' := (2 * R) ^ (1 - α) * (M * ‖z - z'‖ ^ α))
              (mul_nonneg (by positivity) hM0) (mul_nonneg (by positivity) hM0) hC'z
              (hslice z hz) (hslice z' hz') hG (z' j) (by linarith)
            calc _ ≤ 2 * ((2 * R) ^ (1 - α) * (M * ‖z - z'‖ ^ α)) * (2 * R) ^ α / α := h
              _ = (4 * R / α) * (M * ‖z - z'‖ ^ α) := by
                  rw [show 2 * ((2 * R) ^ (1 - α) * (M * ‖z - z'‖ ^ α)) * (2 * R) ^ α / α
                      = 2 * ((2 * R) ^ (1 - α) * (2 * R) ^ α) * (M * ‖z - z'‖ ^ α) / α
                      from by ring, hpow]
                  ring
          have htri : ‖fiberBeurling R j v z - fiberBeurling R j v z'‖
              ≤ ‖Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z) (z j)
                  - Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z) (z' j)‖
                + ‖Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z) (z' j)
                  - Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z') (z' j)‖ := by
            simp only [fiberBeurling_apply]
            have hsplit : Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z) (z j)
                  - Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z') (z' j)
                = (Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z) (z j)
                    - Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z) (z' j))
                  + (Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z) (z' j)
                    - Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z') (z' j)) := by
              ring
            rw [hsplit]
            exact norm_add_le _ _
          calc ‖fiberBeurling R j v z - fiberBeurling R j v z'‖
              ≤ _ + _ := htri
            _ ≤ Ch * ((2 * R) ^ (1 - α) * M) * ‖z - z'‖ ^ α
                + (4 * R / α) * (M * ‖z - z'‖ ^ α) := add_le_add hA hB
            _ = ((Ch * (2 * R) ^ (1 - α) + 4 * R / α) * M) * ‖z - z'‖ ^ α := by ring
        have hA0 : 0 ≤ (4 * R / α) * M := mul_nonneg (by positivity) hM0
        have hB0 : 0 ≤ (Ch * (2 * R) ^ (1 - α) + 4 * R / α) * M := mul_nonneg hK2pos hM0
        have hfin := Work.NN.Ratio.holderNorm_zero_le_of_bounds (X := Cn n) (α := α)
          (Ω := Work.CR.Flat.polydisc 0 r) (v := fiberBeurling R j v)
          (A := (4 * R / α) * M) (B := (Ch * (2 * R) ^ (1 - α) + 4 * R / α) * M)
          hA0 hB0 hbound1 hbound2
        calc Work.CR.Flat.holderNorm 0 α (fiberBeurling R j v) (Work.CR.Flat.polydisc 0 r)
            ≤ ENNReal.ofReal ((4 * R / α) * M)
              + ENNReal.ofReal ((Ch * (2 * R) ^ (1 - α) + 4 * R / α) * M) := hfin
          _ = ENNReal.ofReal ((8 * R / α + Ch * (2 * R) ^ (1 - α)) * M) := by
              rw [← ENNReal.ofReal_add (p := (4 * R / α) * M)
                (q := (Ch * (2 * R) ^ (1 - α) + 4 * R / α) * M) hA0 hB0]
              congr 1
              ring
          _ = ENNReal.ofReal (8 * R / α + Ch * (2 * R) ^ (1 - α)) * ENNReal.ofReal M :=
              ENNReal.ofReal_mul (le_of_lt hKpos)
          _ = ENNReal.ofReal (8 * R / α + Ch * (2 * R) ^ (1 - α)) * N := by rw [← hN_eq]
    refine le_trans hmain (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right _ _)) _)

end Work.NN.Core
