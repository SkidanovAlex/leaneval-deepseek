import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.bmCz.bmPot_dCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.czKernel_holderBound
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_bmDzKernel_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmDzKernel_eucShell_eq_zero
import Submission.Work.CR.Flat.Cauchy.bmCz.abs_eucNorm_sub_le

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-- If `∑ j, r j ≤ ‖y‖` (sup norm) then some coordinate of `y` is at least `r` there.
(Private copy, to keep this file independent of the in-flux module
`bmPotential_holderNorm_le.lean`.) -/
lemma exists_coord_le_of_sum_le_norm_aux {n : ℕ} (hn : 0 < n) {r : Fin n → ℝ} {y : Fin n → ℂ}
    (h : ∑ j, r j ≤ ‖y‖) : ∃ k, r k ≤ ‖y k‖ := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hsum : ∑ j, ‖y j‖ < ∑ j, r j :=
    Finset.sum_lt_sum (fun j _ => le_of_lt (hcon j))
      ⟨⟨0, hn⟩, Finset.mem_univ _, hcon ⟨0, hn⟩⟩
  have hle : ‖y‖ ≤ ∑ j, ‖y j‖ := by
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]
    exact fun j => Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ j)
  linarith

/-- If `√n · ∑ j, r j ≤ eucNorm y` then some coordinate of `y` is at least `r` there.
(Private copy, see above.) -/
lemma exists_coord_le_of_sqrt_mul_sum_le_eucNorm_aux {n : ℕ} (hn : 0 < n) {r : Fin n → ℝ}
    (hr : ∀ j, 0 < r j) {y : Fin n → ℂ}
    (h : Real.sqrt n * (∑ j, r j) ≤ eucNorm y) : ∃ k, r k ≤ ‖y k‖ := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hsq : ∑ j, ‖y j‖ ^ 2 < ∑ j, (r j) ^ 2 :=
    Finset.sum_lt_sum
      (fun j _ => by nlinarith [norm_nonneg (y j), hcon j, hr j])
      ⟨⟨0, hn⟩, Finset.mem_univ _, by
        nlinarith [norm_nonneg (y ⟨0, hn⟩), hcon ⟨0, hn⟩, hr ⟨0, hn⟩]⟩
  have hle : ∑ j, (r j) ^ 2 ≤ (∑ j, r j) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [pow_two]
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (le_of_lt (hr j)) (le_of_lt (hr k))) (Finset.mem_univ j)
  have hsumpos : 0 < ∑ j, r j :=
    Finset.sum_pos (fun j _ => hr j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hlt : eucNorm y < ∑ j, r j := by
    have h2 : eucNorm y ^ 2 < (∑ j, r j) ^ 2 := by
      rw [eucNorm_sq]; linarith
    nlinarith [h2, eucNorm_nonneg y, hsumpos]
  have hge : ∑ j, r j ≤ eucNorm y := by
    have h1 : 1 ≤ Real.sqrt n := by
      have h2 : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
      have h3 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [Real.sqrt_nonneg n]
    nlinarith
  linarith

/-- `D^0 f = f`, so the norm of the difference of two `0`-th iterated within-derivatives is the
norm of the difference of the values.  (Private copy, see above.) -/
lemma norm_iteratedFDerivWithin_zero_sub_aux {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (Ω : Set (Fin n → ℂ)) (x y : Fin n → ℂ) :
    ‖iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y‖ = ‖f x - f y‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (M := ‖f x - f y‖) (norm_nonneg _) fun m => ?_
    rw [ContinuousMultilinearMap.sub_apply, iteratedFDerivWithin_zero_apply,
      iteratedFDerivWithin_zero_apply]
    rw [show (∏ i : Fin 0, ‖m i‖) = 1 from by simp, mul_one]
  · have h := ContinuousMultilinearMap.le_opNorm
      (iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y) (0 : Fin 0 → Fin n → ℂ)
    simp only [ContinuousMultilinearMap.sub_apply, iteratedFDerivWithin_zero_apply] at h
    rw [show (∏ i : Fin 0, ‖(0 : Fin 0 → Fin n → ℂ) i‖) = 1 from by simp, mul_one] at h
    exact h

/-! ## Auxiliary lemmas -/

/-- `√n ≥ 1` for `n ≥ 1`. -/
lemma one_le_sqrt_nat {n : ℕ} (hn : 0 < n) : 1 ≤ Real.sqrt n := by
  have h2 : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have h3 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [Real.sqrt_nonneg n]

/-- A positive multi-radius has positive sum. -/
lemma sum_pos_of_pos {n : ℕ} (hn : 0 < n) {r : Fin n → ℝ} (hr : ∀ j, 0 < r j) :
    0 < ∑ j, r j :=
  Finset.sum_pos (fun j _ => hr j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- `∂_j` of a translate is the translate of `∂_j`. -/
lemma dCoord_comp_add {n : ℕ} (j : Fin n) (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    Work.CR.Flat.dCoord j (fun x : Fin n → ℂ => g (z + x))
      = fun x => Work.CR.Flat.dCoord j g (z + x) := by
  funext x
  simp only [Work.CR.Flat.dCoord, fderiv_comp_add_left]

/-- Translates of `C¹` functions are `C¹`. -/
lemma contDiff_comp_add {n : ℕ} {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g)
    (z : Fin n → ℂ) : ContDiff ℝ 1 (fun x : Fin n → ℂ => g (z + x)) :=
  hg.comp (contDiff_const.add contDiff_id)

/-! ## The uniform Calderón–Zygmund bound for `∂_{z_k}(bmKernel j)` -/

/-- Decay bound for the Calderón–Zygmund kernel `∂_{z_k}(bmKernel j)`: it is dominated by
`n ‖x‖^{-2n}`. -/
lemma norm_bmDzKernel_le_rpow_aux {n : ℕ} (k j : Fin n) {x : Fin n → ℂ} (hx : x ≠ 0) :
    ‖bmDzKernel k j x‖ ≤ (n : ℝ) * eucNorm x ^ (-(2 * (n : ℝ))) := by
  have hX : 0 < eucNorm x := eucNorm_pos hx
  have hnorm : ‖bmDzKernel k j x‖
      = (n : ℝ) * ‖x j‖ * ‖x k‖ / (eucNorm x) ^ (2 * n + 2) := by
    simp only [bmDzKernel, norm_div, norm_mul, norm_neg, Complex.norm_conj, Complex.norm_natCast,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX]
    try ring
  rw [hnorm]
  have hle : (n : ℝ) * ‖x j‖ * ‖x k‖ ≤ (n : ℝ) * (eucNorm x) ^ 2 := by
    have hj : ‖x j‖ ≤ eucNorm x := bmCz.norm_apply_le_eucNorm' x j
    have hk : ‖x k‖ ≤ eucNorm x := bmCz.norm_apply_le_eucNorm' x k
    calc (n : ℝ) * ‖x j‖ * ‖x k‖ ≤ (n : ℝ) * eucNorm x * eucNorm x := by gcongr
      _ = (n : ℝ) * (eucNorm x) ^ 2 := by ring
  calc (n : ℝ) * ‖x j‖ * ‖x k‖ / (eucNorm x) ^ (2 * n + 2)
      ≤ (n : ℝ) * (eucNorm x) ^ 2 / (eucNorm x) ^ (2 * n + 2) :=
        div_le_div_of_nonneg_right hle (by positivity)
    _ = (n : ℝ) / (eucNorm x) ^ (2 * n) := by
        rw [pow_add]
        rw [mul_div_mul_right _ _ (pow_ne_zero _ hX.ne')]
    _ = (n : ℝ) * (eucNorm x) ^ (-(2 * (n : ℝ))) := by
        have hpow : (eucNorm x) ^ (2 * n) = (eucNorm x) ^ (2 * (n : ℝ)) := by
          rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
        rw [hpow, Real.rpow_neg hX.le, div_eq_mul_inv]

/-- Measurability of the kernel. -/
lemma measurable_bmDzKernel_aux {n : ℕ} (k j : Fin n) : Measurable (bmDzKernel k j) := by
  have h1 : Measurable fun x : Fin n → ℂ => starRingEnd ℂ (x j) :=
    Complex.continuous_conj.measurable.comp (continuous_apply j).measurable
  have h2 : Measurable fun x : Fin n → ℂ => starRingEnd ℂ (x k) :=
    Complex.continuous_conj.measurable.comp (continuous_apply k).measurable
  have h3 : Measurable fun x : Fin n → ℂ => ((eucNorm x : ℝ) : ℂ) ^ (2 * n + 2) :=
    Measurable.pow_const (Complex.continuous_ofReal.measurable.comp
      continuous_eucNorm.measurable) (2 * n + 2)
  unfold bmDzKernel
  exact ((measurable_const.mul h1).mul h2).div h3

/-- **Uniform Calderón–Zygmund bound for `∂_{z_k}(bmKernel j)`.**  This bundles the `L^∞`
estimate (`czSupBound_bmDzKernel`) with the Hölder estimate for the difference (the general
singular-integral statement `bmCz.czDifferenceEstimate`), with a constant independent of
`k`, `j` and of `g`. -/
theorem bmDzKernel_czBound {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k j : Fin n) (K : ℝ), 0 ≤ K → ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x : Fin n → ℂ, R ≤ eucNorm x → g x = 0) →
      (∀ z : Fin n → ℂ,
        ‖∫ x in eucBall (4 * R), bmDzKernel k j x * (g (z + x) - g z)‖ ≤ C * K) ∧
      (∀ z z' : Fin n → ℂ,
        ‖(∫ x in eucBall (4 * R), bmDzKernel k j x * (g (z + x) - g z))
            - (∫ x in eucBall (4 * R), bmDzKernel k j x * (g (z' + x) - g z'))‖
          ≤ C * K * ‖z - z'‖ ^ α) := by
  obtain ⟨C0, hC0pos, hC0⟩ := bmCz.norm_bmDzKernel_sub_le hn
  set A : ℝ := max (n : ℝ) C0 with hAdef
  have hApos : 0 < A := lt_of_lt_of_le (by exact_mod_cast hn) (le_max_left _ _)
  have hP1 : ∀ (k j : Fin n) (x : Fin n → ℂ), x ≠ 0 →
      ‖bmDzKernel k j x‖ ≤ A / (eucNorm x) ^ (2 * n) := by
    intro k j x hx
    have h1 : ‖bmDzKernel k j x‖ ≤ (n : ℝ) * eucNorm x ^ (-(2 * (n : ℝ))) :=
      norm_bmDzKernel_le_rpow_aux k j hx
    have h2 : (n : ℝ) * eucNorm x ^ (-(2 * (n : ℝ)))
        = (n : ℝ) / (eucNorm x) ^ (2 * n) := by
      rw [show (eucNorm x) ^ (2 * n) = (eucNorm x) ^ (2 * (n : ℝ)) by
        rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]]
      rw [Real.rpow_neg (eucNorm_pos hx).le, div_eq_mul_inv]
    rw [h2] at h1
    exact le_trans h1 ((div_le_div_iff_of_pos_right (pow_pos (eucNorm_pos hx) _)).mpr
      (le_max_left _ _))
  have hP2 : ∀ (k j : Fin n) (x h : Fin n → ℂ), 2 * eucNorm h ≤ eucNorm x →
      ‖bmDzKernel k j (x - h) - bmDzKernel k j x‖
        ≤ A * eucNorm h / (eucNorm x) ^ (2 * n + 1) := by
    intro k j x h hxh
    rcases eq_or_ne x 0 with rfl | hx0
    · have hh0 : eucNorm h = 0 := by
        rw [eucNorm_zero] at hxh
        have := eucNorm_nonneg h
        linarith
      have hh : h = 0 := eucNorm_eq_zero.mp hh0
      subst hh
      simp
    · have hX : 0 < eucNorm x := eucNorm_pos hx0
      have hb := hC0 k j x h hxh
      have hrw : eucNorm x ^ (-(2 * (n : ℝ) + 1)) = 1 / (eucNorm x) ^ (2 * n + 1) := by
        rw [show 2 * (n : ℝ) + 1 = ((2 * n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hX.le,
          Real.rpow_natCast, one_div]
      rw [hrw] at hb
      have hCA : C0 ≤ A := le_max_right _ _
      have hnn : 0 ≤ eucNorm h := eucNorm_nonneg h
      calc ‖bmDzKernel k j (x - h) - bmDzKernel k j x‖
          ≤ C0 * eucNorm h * (1 / (eucNorm x) ^ (2 * n + 1)) := hb
        _ = (C0 * eucNorm h) * ((eucNorm x) ^ (2 * n + 1))⁻¹ := by ring
        _ ≤ (A * eucNorm h) * ((eucNorm x) ^ (2 * n + 1))⁻¹ := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right hCA hnn
        _ = A * eucNorm h / (eucNorm x) ^ (2 * n + 1) := by ring
  have hpair : ∀ k j : Fin n, ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 0 ≤ K → ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x : Fin n → ℂ, R ≤ eucNorm x → g x = 0) →
      (∀ z : Fin n → ℂ,
        ‖∫ x in eucBall (4 * R), bmDzKernel k j x * (g (z + x) - g z)‖ ≤ C * K) ∧
      (∀ z z' : Fin n → ℂ,
        ‖(∫ x in eucBall (4 * R), bmDzKernel k j x * (g (z + x) - g z))
            - (∫ x in eucBall (4 * R), bmDzKernel k j x * (g (z' + x) - g z'))‖
          ≤ C * K * ‖z - z'‖ ^ α) := by
    intro k j
    obtain ⟨C, hC, hCb⟩ := bmCz.czKernel_holderBound hn hα hα1 hR
      (Φ := bmDzKernel k j) (measurable_bmDzKernel_aux k j).aestronglyMeasurable hApos
      (hP1 k j) (fun x h => hP2 k j x h)
      (fun a b ha hab => bmCz.integral_bmDzKernel_eucShell_eq_zero (k := k) (j := j) ha)
    exact ⟨C, hC, fun K hK g hg hgs => hCb K hK g hg hgs⟩
  choose C hCpos hCb using hpair
  set Cu : ℝ := ∑ p : Fin n × Fin n, C p.1 p.2 with hCudef
  have hCu_pos : 0 < Cu := by
    rw [hCudef]
    exact Finset.sum_pos (fun p _ => hCpos p.1 p.2) ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  have hle : ∀ k j : Fin n, C k j ≤ Cu := by
    intro k j
    rw [hCudef]
    exact Finset.single_le_sum (fun p _ => le_of_lt (hCpos p.1 p.2)) (Finset.mem_univ (k, j))
  refine ⟨Cu, hCu_pos, ?_⟩
  intro k j K hK g hg hgs
  refine ⟨fun z => ?_, fun z z' => ?_⟩
  · refine le_trans ((hCb k j K hK g hg hgs).1 z) ?_
    exact mul_le_mul_of_nonneg_right (hle k j) hK
  · refine le_trans ((hCb k j K hK g hg hgs).2 z z') ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hle k j) hK)
      (Real.rpow_nonneg (norm_nonneg _) α)

/-! ## The potential's derivative as a subtracted singular integral -/

/-- **The `(1,0)`-derivative of the Bochner–Martinelli potential as a subtracted singular
integral.**  For `f` a family of `C¹` functions supported in the open half-polydisc
`polydisc c (r/2)` and `z` in that polydisc,

`∂_k (bmPotential f)(z) = -Σ_j ∫_{‖x‖<4ρ} ∂_{z_k}(bmKernel j) x · (f_j(z+x) - f_j(z)) dx`,

with `ρ = ‖c‖ + √n Σ_i r_i`.  The integration by parts is
`bmCz.integral_bmKernel_mul_dCoord`; the radius `ρ` is chosen so that both `f` and every
translate `f(·+z)`, `z ∈ polydisc c (r/2)`, have support in the Euclidean ball of radius `ρ`. -/
theorem bmPotential_dCoord_eq_sum_eucBall {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ}
    {r : Fin n → ℝ} (hr : ∀ j, 0 < r j) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hsupp : ∀ j z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → f j z = 0) (k : Fin n) :
    ∀ z ∈ Work.CR.Flat.polydisc c (fun i => r i / 2),
      Work.CR.Flat.dCoord k (bmPotential f) z
        = -∑ j, ∫ x in eucBall (4 * (eucNorm c + Real.sqrt n * ∑ i, r i)),
            bmDzKernel k j x * (f j (z + x) - f j z) := by
  intro z hz
  have hsum_pos : 0 < ∑ i, r i := sum_pos_of_pos hn hr
  have hRpos : 0 < eucNorm c + Real.sqrt n * ∑ i, r i := by
    have h1 : 0 < Real.sqrt n * ∑ i, r i :=
      mul_pos (lt_of_lt_of_le one_pos (one_le_sqrt_nat hn)) hsum_pos
    linarith [eucNorm_nonneg c]
  -- (1) differentiation under the integral sign
  have hambsupp : ∀ j (x : Fin n → ℂ), (∑ i, (r i / 2 + ‖c i‖)) ≤ ‖x‖ → f j x = 0 := by
    intro j x hx
    obtain ⟨i, hi⟩ := exists_coord_le_of_sum_le_norm_aux hn hx
    refine hsupp j x ⟨i, ?_⟩
    have h2 : ‖x i‖ - ‖c i‖ ≤ ‖x i - c i‖ :=
      le_trans (le_abs_self (‖x i‖ - ‖c i‖)) (abs_norm_sub_norm_le (x i) (c i))
    linarith
  have hambpos : 0 < ∑ i, (r i / 2 + ‖c i‖) := by
    refine Finset.sum_pos (fun i _ => ?_) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    exact add_pos_of_pos_of_nonneg (by have := hr i; linarith) (norm_nonneg (c i))
  have h1 : Work.CR.Flat.dCoord k (bmPotential f) z
      = ∑ j, ∫ x, bmKernel j x * Work.CR.Flat.dCoord k (f j) (z + x) := by
    have hfun : bmPotential f = bmPot f := funext fun w => bmPotential_eq_bmPot f w
    rw [hfun]
    exact Work.CR.Flat.Cauchy.bmCz.bmPot_dCoord hn hf hambpos hambsupp k z
  -- (2) integration by parts term by term
  have hstep : ∀ j : Fin n, (∫ x, bmKernel j x * Work.CR.Flat.dCoord k (f j) (z + x))
      = -∫ x in eucBall (4 * (eucNorm c + Real.sqrt n * ∑ i, r i)),
          bmDzKernel k j x * (f j (z + x) - f j z) := by
    intro j
    have hsupp' : ∀ x : Fin n → ℂ, (eucNorm c + Real.sqrt n * ∑ i, r i) ≤ eucNorm x →
        (fun x : Fin n → ℂ => f j (z + x)) x = 0 := by
      intro x hx
      have hx' : Real.sqrt n * ∑ i, r i ≤ eucNorm x := by linarith [eucNorm_nonneg c]
      obtain ⟨i, hi⟩ := exists_coord_le_of_sqrt_mul_sum_le_eucNorm_aux hn hr hx'
      have hzi : ‖z i - c i‖ < r i / 2 := hz i
      have h2 : ‖x i‖ - ‖z i - c i‖ ≤ ‖(z + x) i - c i‖ := by
        have h3 : (z + x) i - c i = x i + (z i - c i) := by
          simp only [Pi.add_apply]; ring
        rw [h3]
        have h4 : ‖x i‖ ≤ ‖x i + (z i - c i)‖ + ‖z i - c i‖ := by
          have h5 := norm_add_le (x i + (z i - c i)) (-(z i - c i))
          rw [add_neg_cancel_right, norm_neg] at h5
          exact h5
        linarith
      exact hsupp j (z + x) ⟨i, by linarith⟩
    have h := Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord hn k j
      (fun x : Fin n → ℂ => f j (z + x)) (eucNorm c + Real.sqrt n * ∑ i, r i) hRpos
      (contDiff_comp_add (hf j) z) hsupp'
    simpa only [dCoord_comp_add, add_zero] using h
  have htarget : (∑ j, ∫ x, bmKernel j x * Work.CR.Flat.dCoord k (f j) (z + x))
      = ∑ j, -∫ x in eucBall (4 * (eucNorm c + Real.sqrt n * ∑ i, r i)),
          bmDzKernel k j x * (f j (z + x) - f j z) :=
    Finset.sum_congr rfl fun j _ => hstep j
  rw [h1, htarget, Finset.sum_neg_distrib]

/-! ## The main estimate -/

theorem bmPotential_dCoord_holderNorm_le {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ}
    {r : Fin n → ℝ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : ∀ j, 0 < r j) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (f j)) →
      (∀ j z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → f j z = 0) →
      ∀ k : Fin n,
        Work.CR.Flat.holderNorm 0 α
            (fun z => Work.CR.Flat.dCoord k (Work.CR.Flat.Cauchy.bmPotential f) z)
            (Work.CR.Flat.polydisc c (fun j => r j / 2))
          ≤ ENNReal.ofReal C * ∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ := by
  have hsum_pos : 0 < ∑ i, r i := sum_pos_of_pos hn hr
  have hρpos : 0 < eucNorm c + Real.sqrt n * ∑ i, r i := by
    have h1 : 0 < Real.sqrt n * ∑ i, r i :=
      mul_pos (lt_of_lt_of_le one_pos (one_le_sqrt_nat hn)) hsum_pos
    linarith [eucNorm_nonneg c]
  obtain ⟨Cz, hCzpos, hCz⟩ := bmDzKernel_czBound hn hα hα1 hρpos
  refine ⟨2 * Cz, by linarith, ?_⟩
  intro f hf hsupp k
  -- the support radius: `f` vanishes outside the Euclidean ball of radius `ρ`
  have hsuppρ : ∀ j (x : Fin n → ℂ), (eucNorm c + Real.sqrt n * ∑ i, r i) ≤ eucNorm x →
      f j x = 0 := by
    intro j x hx
    have hx' : Real.sqrt n * ∑ i, r i ≤ eucNorm (x - c) := by
      have h2 : |eucNorm x - eucNorm c| ≤ eucNorm (x - c) := bmCz.abs_eucNorm_sub_le x c
      have h3 : eucNorm x - eucNorm c ≤ eucNorm (x - c) := le_trans (le_abs_self _) h2
      linarith
    obtain ⟨i, hi⟩ := exists_coord_le_of_sqrt_mul_sum_le_eucNorm_aux hn hr hx'
    refine hsupp j x ⟨i, ?_⟩
    have h3 : (x - c) i = x i - c i := by simp only [Pi.sub_apply]
    rw [← h3]
    have hri : 0 < r i := hr i
    linarith
  set hh : (Fin n → ℂ) → ℂ := fun z => Work.CR.Flat.dCoord k (bmPotential f) z with hhdef
  by_cases hfin : ∀ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ ≠ ⊤
  · set K : Fin n → ℝ := fun j => (Work.CR.Flat.holderNorm 0 α (f j) Set.univ).toReal with hKdef
    have hKnn : ∀ j, 0 ≤ K j := fun j => ENNReal.toReal_nonneg
    have hHolder : ∀ j (x y : Fin n → ℂ), ‖f j x - f j y‖ ≤ K j * ‖x - y‖ ^ α := by
      intro j x y
      by_cases hxy : x = y
      · subst hxy
        simp [Real.zero_rpow (ne_of_gt hα)]
      · have hden : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
        have h1 : ENNReal.ofReal (‖f j x - f j y‖ / ‖x - y‖ ^ α)
            ≤ Work.CR.Flat.holderNorm 0 α (f j) Set.univ := by
          have h := Work.CR.Flat.le_holderSeminorm 0 α (f j) Set.univ (Set.mem_univ x)
            (Set.mem_univ y) hxy
          rw [norm_iteratedFDerivWithin_zero_sub_aux] at h
          exact le_trans h (Work.CR.Flat.holderSeminorm_le_holderNorm 0 α (f j) Set.univ le_rfl)
        have h2 : ‖f j x - f j y‖ / ‖x - y‖ ^ α ≤ K j := by
          have h3 := (ENNReal.toReal_le_toReal (by simp) (hfin j)).mpr h1
          simpa only [ENNReal.toReal_ofReal (div_nonneg (norm_nonneg _) hden.le), hKdef] using h3
        calc ‖f j x - f j y‖ = (‖f j x - f j y‖ / ‖x - y‖ ^ α) * ‖x - y‖ ^ α :=
              (div_mul_cancel₀ _ hden.ne').symm
          _ ≤ K j * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_right h2 hden.le
    have hident : ∀ z ∈ Work.CR.Flat.polydisc c (fun i => r i / 2),
        hh z = -∑ j, ∫ x in eucBall (4 * (eucNorm c + Real.sqrt n * ∑ i, r i)),
            bmDzKernel k j x * (f j (z + x) - f j z) := by
      intro z hz
      rw [hhdef]
      exact bmPotential_dCoord_eq_sum_eucBall hn hr hf hsupp k z hz
    have hcoef : ENNReal.ofReal (Cz * ∑ j, K j)
        ≤ ENNReal.ofReal Cz * ∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ := by
      rw [ENNReal.ofReal_mul hCzpos.le,
        ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (fun j _ => hKnn j)]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) bot_le
      simpa only [hKdef] using
        (ENNReal.ofReal_toReal_le (a := Work.CR.Flat.holderNorm 0 α (f j) Set.univ))
    have hsup : ∀ z ∈ Work.CR.Flat.polydisc c (fun i => r i / 2),
        ‖hh z‖ ≤ Cz * ∑ j, K j := by
      intro z hz
      rw [hident z hz, norm_neg]
      calc ‖∑ j, ∫ x in eucBall (4 * (eucNorm c + Real.sqrt n * ∑ i, r i)),
              bmDzKernel k j x * (f j (z + x) - f j z)‖
          ≤ ∑ j, ‖∫ x in eucBall (4 * (eucNorm c + Real.sqrt n * ∑ i, r i)),
              bmDzKernel k j x * (f j (z + x) - f j z)‖ := norm_sum_le _ _
        _ ≤ ∑ j, Cz * K j :=
            Finset.sum_le_sum fun j _ =>
              (hCz k j (K j) (hKnn j) (f j) (hHolder j)
                (hsuppρ j)).1 z
        _ = Cz * ∑ j, K j := (Finset.mul_sum Finset.univ K Cz).symm
    have hholder : ∀ z ∈ Work.CR.Flat.polydisc c (fun i => r i / 2),
        ∀ z' ∈ Work.CR.Flat.polydisc c (fun i => r i / 2), z ≠ z' →
        ‖hh z - hh z'‖ ≤ Cz * (∑ j, K j) * ‖z - z'‖ ^ α := by
      intro z hz z' hz' hzz'
      have hA := hident z hz
      have hB := hident z' hz'
      rw [hA, hB]
      have hstep : (-∑ j, ∫ x in eucBall (4 * (eucNorm c + Real.sqrt n * ∑ i, r i)),
              bmDzKernel k j x * (f j (z + x) - f j z))
            - (-∑ j, ∫ x in eucBall (4 * (eucNorm c + Real.sqrt n * ∑ i, r i)),
              bmDzKernel k j x * (f j (z' + x) - f j z'))
          = ∑ j, ((∫ x in eucBall (4 * (eucNorm c + Real.sqrt n * ∑ i, r i)),
                bmDzKernel k j x * (f j (z' + x) - f j z'))
              - (∫ x in eucBall (4 * (eucNorm c + Real.sqrt n * ∑ i, r i)),
                bmDzKernel k j x * (f j (z + x) - f j z))) := by
        rw [Finset.sum_sub_distrib]
        ring
      rw [hstep]
      calc ‖∑ j, ((∫ x in eucBall (4 * (eucNorm c + Real.sqrt n * ∑ i, r i)),
                  bmDzKernel k j x * (f j (z' + x) - f j z'))
              - (∫ x in eucBall (4 * (eucNorm c + Real.sqrt n * ∑ i, r i)),
                  bmDzKernel k j x * (f j (z + x) - f j z)))‖
          ≤ ∑ j, ‖(∫ x in eucBall (4 * (eucNorm c + Real.sqrt n * ∑ i, r i)),
                  bmDzKernel k j x * (f j (z' + x) - f j z'))
              - (∫ x in eucBall (4 * (eucNorm c + Real.sqrt n * ∑ i, r i)),
                  bmDzKernel k j x * (f j (z + x) - f j z))‖ := norm_sum_le _ _
        _ ≤ ∑ j, Cz * K j * ‖z - z'‖ ^ α := Finset.sum_le_sum fun j _ =>
              le_trans (le_of_eq (norm_sub_rev _ _))
                ((hCz k j (K j) (hKnn j) (f j) (hHolder j)
                  (hsuppρ j)).2 z z')
        _ = Cz * (∑ j, K j) * ‖z - z'‖ ^ α := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hIter : iterDerivNorm 0 hh (Work.CR.Flat.polydisc c (fun i => r i / 2))
        ≤ ENNReal.ofReal Cz * ∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ := by
      refine iSup₂_le fun z hz => ?_
      have h1 : ‖iteratedFDerivWithin ℝ 0 hh
            (Work.CR.Flat.polydisc c (fun i => r i / 2)) z‖ ≤ Cz * ∑ j, K j := by
        rw [norm_iteratedFDerivWithin_zero]
        exact hsup z hz
      calc ENNReal.ofReal ‖iteratedFDerivWithin ℝ 0 hh
              (Work.CR.Flat.polydisc c (fun i => r i / 2)) z‖
          ≤ ENNReal.ofReal (Cz * ∑ j, K j) := ENNReal.ofReal_le_ofReal h1
        _ ≤ ENNReal.ofReal Cz * ∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ := hcoef
    have hSem : holderSeminorm 0 α hh (Work.CR.Flat.polydisc c (fun i => r i / 2))
        ≤ ENNReal.ofReal Cz * ∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ := by
      refine iSup₂_le fun z hz => iSup₂_le fun z' hz' => iSup_le fun hzz' => ?_
      have hden : 0 < ‖z - z'‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzz')) α
      have h1 : ‖iteratedFDerivWithin ℝ 0 hh
            (Work.CR.Flat.polydisc c (fun i => r i / 2)) z
            - iteratedFDerivWithin ℝ 0 hh (Work.CR.Flat.polydisc c (fun i => r i / 2)) z'‖
            / ‖z - z'‖ ^ α ≤ Cz * ∑ j, K j := by
        rw [norm_iteratedFDerivWithin_zero_sub_aux, div_le_iff₀ hden]
        exact hholder z hz z' hz' hzz'
      calc ENNReal.ofReal (‖iteratedFDerivWithin ℝ 0 hh
                (Work.CR.Flat.polydisc c (fun i => r i / 2)) z
              - iteratedFDerivWithin ℝ 0 hh
                (Work.CR.Flat.polydisc c (fun i => r i / 2)) z'‖ / ‖z - z'‖ ^ α)
          ≤ ENNReal.ofReal (Cz * ∑ j, K j) := ENNReal.ofReal_le_ofReal h1
        _ ≤ ENNReal.ofReal Cz * ∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ := hcoef
    rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    calc iterDerivNorm 0 hh (Work.CR.Flat.polydisc c (fun i => r i / 2))
          + holderSeminorm 0 α hh (Work.CR.Flat.polydisc c (fun i => r i / 2))
        ≤ ENNReal.ofReal Cz * (∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ)
          + ENNReal.ofReal Cz * (∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ) :=
          add_le_add hIter hSem
      _ = (ENNReal.ofReal Cz + ENNReal.ofReal Cz)
          * (∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ) := by rw [add_mul]
      _ = ENNReal.ofReal (Cz + Cz) * (∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ) := by
          rw [ENNReal.ofReal_add hCzpos.le hCzpos.le]
      _ = ENNReal.ofReal (2 * Cz) * (∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ) := by
          rw [show Cz + Cz = 2 * Cz by ring]
  · push_neg at hfin
    obtain ⟨j₀, hj₀⟩ := hfin
    have hsum_top : (∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ) = ⊤ := by
      refine le_antisymm le_top ?_
      have hle : Work.CR.Flat.holderNorm 0 α (f j₀) Set.univ
          ≤ ∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ :=
        Finset.single_le_sum (fun i _ =>
          show (0 : ℝ≥0∞) ≤ Work.CR.Flat.holderNorm 0 α (f i) Set.univ from zero_le)
          (Finset.mem_univ j₀)
      rw [hj₀] at hle
      exact hle
    rw [hsum_top,
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith : (0 : ℝ) < 2 * Cz)))]
    exact le_top

end Work.CR.Flat.Cauchy
