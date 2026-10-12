import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseKinLoc.Momentum.chFT_eq_ofReal
import Submission.Work.BoseKinLoc.Momentum.cubFT_deriv
import Submission.Work.BoseKinLoc.Momentum.dom_bounds
import Submission.Work.BoseKinLoc.Momentum.exterior_prod_le
import Submission.Work.BoseKinLoc.Momentum.hFT_bounds
import Submission.Work.BoseKinLoc.Momentum.hasDerivAt_hFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Exterior decay of the unit-cube Fourier symbol `cubFT`

The symbol `cubFT q = ∫_{acube 1} cos ⟪q,x⟫ dx` factorises as `∏ i, hFT (q i)` and the coordinate
derivatives are `-(mFT (q i)) ∏_{j ≠ i} hFT (q j)` (see `cubFT_prod`/`cubFT_deriv`).  The 1D
estimates `|hFT t| ≤ 1`, `|t hFT t| ≤ 2`, `|mFT t| ≤ 1/2`, `|t mFT t| ≤ 2` (`hFT_bounds`) give

    `(hFT t)² ≤ hBox t`,  `(mFT t)² ≤ mBox t`   (everywhere, after correcting the point `t = 0`),

so `(cubFT q)²` and `Σ i (∂ᵢ cubFT q)²` are dominated by products of one-dimensional densities
with `8/L`-tails, and the union bound `exterior_prod_le` gives the exterior decay.

This file contains the assembly: the point-corrected dominating functions `hBox`, `mBox`, their
one-dimensional bounds (transferred from `dom_bounds`), the pointwise domination of `(cubFT ·)²`
and of the coordinate derivatives, and the final two exterior estimates.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false

/-- The dominating function for `(hFT ·)²`, corrected at the single point `t = 0`
(where `Fdom 0 = min 1 (4/0²) = 0` but `(hFT 0)² = 1`). -/
def hBox (t : ℝ) : ℝ := if t = 0 then 1 else Fdom t

/-- The dominating function for `(mFT ·)²`, corrected at `t = 0`. -/
def mBox (t : ℝ) : ℝ := if t = 0 then 1 / 2 else Gdom t

lemma hBox_nonneg (t : ℝ) : 0 ≤ hBox t := by
  rw [hBox]; split <;> simp [Fdom_nonneg]

lemma mBox_nonneg (t : ℝ) : 0 ≤ mBox t := by
  rw [mBox]; split <;> simp [Gdom_nonneg]

lemma hBox_ae : hBox =ᵐ[volume] Fdom := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  exact measure_mono_null (fun t ht => by
    by_contra h
    exact ht (by rw [hBox, if_neg (by simpa using h)])) (measure_singleton 0)

lemma mBox_ae : mBox =ᵐ[volume] Gdom := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  exact measure_mono_null (fun t ht => by
    by_contra h
    exact ht (by rw [mBox, if_neg (by simpa using h)])) (measure_singleton 0)

lemma integrable_hBox : Integrable hBox := dom_bounds.1.congr hBox_ae.symm

lemma integrable_mBox : Integrable mBox := dom_bounds.2.2.2.1.congr mBox_ae.symm

lemma hBox_integral : ∫ t : ℝ, hBox t = 8 := by
  rw [integral_congr_ae hBox_ae, dom_bounds.2.1]

lemma mBox_integral_le : ∫ t : ℝ, mBox t ≤ 6 := by
  rw [integral_congr_ae mBox_ae]
  exact dom_bounds.2.2.2.2.1

lemma hBox_tail (s : ℝ) (hs : 0 < s) : ∫ t in {u : ℝ | s ≤ |u|}, hBox t ≤ 8 / s := by
  have hmeas : MeasurableSet {u : ℝ | s ≤ |u|} :=
    (isClosed_le continuous_const continuous_id.abs).measurableSet
  rw [setIntegral_congr_fun hmeas (fun t ht => by
    rw [hBox, if_neg (abs_pos.mp (lt_of_lt_of_le hs ht))])]
  exact dom_bounds.2.2.1 s hs

lemma mBox_tail (s : ℝ) (hs : 0 < s) : ∫ t in {u : ℝ | s ≤ |u|}, mBox t ≤ 8 / s := by
  have hmeas : MeasurableSet {u : ℝ | s ≤ |u|} :=
    (isClosed_le continuous_const continuous_id.abs).measurableSet
  rw [setIntegral_congr_fun hmeas (fun t ht => by
    rw [mBox, if_neg (abs_pos.mp (lt_of_lt_of_le hs ht))])]
  exact dom_bounds.2.2.2.2.2 s hs

/-- `(hFT t)² ≤ hBox t` for every `t`. -/
lemma hFT_sq_le_hBox (t : ℝ) : (hFT t) ^ 2 ≤ hBox t := by
  by_cases ht : t = 0
  · rw [hBox, if_pos ht, ht, hFT_zero]; norm_num
  · rw [hBox, if_neg ht]
    have h1 : (hFT t) ^ 2 ≤ 1 := by
      have h := hFT_bounds.1 t
      nlinarith [abs_nonneg (hFT t), sq_abs (hFT t)]
    have h2 : (hFT t) ^ 2 ≤ 4 / t ^ 2 := by
      have h := hFT_bounds.2.1 t
      have h4 : (t * hFT t) ^ 2 ≤ 4 := by
        have h5 := abs_le.mp h
        nlinarith [h5.1, h5.2]
      rw [mul_pow, sq] at h4
      rw [le_div_iff₀ (by positivity)]
      linarith [h4]
    exact le_min h1 h2

/-- `(mFT t)² ≤ mBox t` for every `t`. -/
lemma mFT_sq_le_mBox (t : ℝ) : (mFT t) ^ 2 ≤ mBox t := by
  by_cases ht : t = 0
  · rw [mBox, if_pos ht, ht, mFT_zero]; norm_num
  · rw [mBox, if_neg ht]
    have h1 : (mFT t) ^ 2 ≤ 1 / 2 := by
      have h := hFT_bounds.2.2.1 t
      nlinarith [abs_nonneg (mFT t), sq_abs (mFT t)]
    have h2 : (mFT t) ^ 2 ≤ 4 / t ^ 2 := by
      have h := hFT_bounds.2.2.2 t
      have h4 : (t * mFT t) ^ 2 ≤ 4 := by
        have h5 := abs_le.mp h
        nlinarith [h5.1, h5.2]
      rw [mul_pow, sq] at h4
      rw [le_div_iff₀ (by positivity)]
      linarith [h4]
    exact le_min h1 h2

/-- Integrability on `ℝ³` of a product of integrable functions of a single coordinate. -/
lemma integrable_prod_euclidean {g : Fin 3 → ℝ → ℝ} (hg : ∀ i, Integrable (g i)) :
    Integrable (fun q : EuclideanSpace ℝ (Fin 3) => ∏ i, g i (q i)) := by
  have h1 : Integrable (fun x : Fin 3 → ℝ => ∏ i, g i (x i))
      (Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)) :=
    Integrable.fintype_prod fun i => hg i
  rw [← volume_pi] at h1
  exact ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)).mpr h1

/-- The product formula for the square of `cubFT`. -/
lemma cubFT_sq_eq_prod (w : EuclideanSpace ℝ (Fin 3)) :
    (cubFT w) ^ 2 = ∏ i : Fin 3, (hFT (w i)) ^ 2 := by
  rw [cubFT_eq_prod_of chFT_eq_ofReal w, Finset.prod_pow]

/-- The product formula for the square of a coordinate derivative of `cubFT`. -/
lemma fderiv_sq_eq_prod
    (hder : ∀ (w : EuclideanSpace ℝ (Fin 3)) (i : Fin 3),
      fderiv ℝ cubFT w (kcStdBasis i)
        = -(mFT (w i)) * ∏ j ∈ Finset.univ.erase i, hFT (w j))
    (w : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    (fderiv ℝ cubFT w (kcStdBasis i)) ^ 2
      = (∏ j ∈ Finset.univ.erase i, (hFT (w j)) ^ 2) * (mFT (w i)) ^ 2 := by
  rw [hder w i, mul_pow, neg_sq, Finset.prod_pow, mul_comm]

/-- The elementary bound on the sum of the union-bound terms used twice below. -/
lemma sum_erase_bound (A : ℝ) (hA : 0 ≤ A) (B : Fin 3 → ℝ) (hBnn : ∀ i, 0 ≤ B i)
    (hB : ∀ i, B i ≤ 8) :
    ∑ i : Fin 3, A * ∏ j ∈ Finset.univ.erase i, B j ≤ 3 * 512 * A := by
  have h1 : ∑ i : Fin 3, A * ∏ j ∈ Finset.univ.erase i, B j
      ≤ ∑ _i : Fin 3, A * 512 :=
    Finset.sum_le_sum fun i _ => by
      refine mul_le_mul_of_nonneg_left ?_ hA
      calc ∏ j ∈ Finset.univ.erase i, B j ≤ ∏ j ∈ Finset.univ.erase i, (8 : ℝ) :=
            Finset.prod_le_prod₀ (fun j _ => hBnn j) (fun j _ => hB j)
        _ = 8 ^ (Finset.univ.erase i).card := Finset.prod_const (8 : ℝ)
        _ ≤ 8 ^ 3 := by
            refine pow_le_pow_right₀ (by norm_num) ?_
            simpa using Finset.card_erase_le (s := (Finset.univ : Finset (Fin 3))) i
        _ = 512 := by norm_num
  have h2 : ∑ _i : Fin 3, A * 512 = 3 * 512 * A := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  exact h1.trans h2.le

theorem cubFT_exterior_bounds : ∃ C : ℝ, 0 < C ∧
    (∀ L : ℝ, 0 < L → ∫ w in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖}, (cubFT w) ^ 2 ≤ C / L) ∧
    (∀ L : ℝ, 0 < L → ∑ i : Fin 3, ∫ w in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖},
        (fderiv ℝ cubFT w (Submission.BoseGases.kcStdBasis i)) ^ 2 ≤ C / L) := by
  have hder : ∀ (w : EuclideanSpace ℝ (Fin 3)) (i : Fin 3),
      fderiv ℝ cubFT w (kcStdBasis i)
        = -(mFT (w i)) * ∏ j ∈ Finset.univ.erase i, hFT (w j) :=
    fun w i => fderiv_cubFT_coord_of
      (fun q => cubFT_eq_prod_of chFT_eq_ofReal q) hasDerivAt_hFT w i
  have hsqrt3 : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have htail_eq : ∀ L : ℝ, 0 < L → (8 : ℝ) / (L / Real.sqrt 3) = 8 * Real.sqrt 3 / L := by
    intro L _
    rw [div_div_eq_mul_div]
  have hfinal : ∀ L : ℝ, 0 < L → (3 : ℝ) * 512 * (8 * Real.sqrt 3 / L) ≤ 100000 / L := by
    intro L hL
    have h1 : (3 : ℝ) * 512 * (8 * Real.sqrt 3) ≤ 100000 := by
      nlinarith [hsqrt3, Real.sqrt_nonneg 3]
    calc (3 : ℝ) * 512 * (8 * Real.sqrt 3 / L)
        = (3 * 512 * (8 * Real.sqrt 3)) / L := by ring
      _ ≤ 100000 / L := div_le_div_of_nonneg_right h1 hL.le
  refine ⟨100000, by norm_num, ?_, ?_⟩
  · intro L hL
    have hpos : 0 < L / Real.sqrt 3 := div_pos hL (Real.sqrt_pos.mpr (by norm_num))
    have hInt : Integrable (fun q : EuclideanSpace ℝ (Fin 3) => ∏ i : Fin 3, hBox (q i)) :=
      integrable_prod_euclidean fun _ => integrable_hBox
    have hle : ∀ w : EuclideanSpace ℝ (Fin 3), (cubFT w) ^ 2 ≤ ∏ i : Fin 3, hBox (w i) := by
      intro w
      rw [cubFT_sq_eq_prod w]
      exact Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) (fun i _ => hFT_sq_le_hBox (w i))
    calc ∫ w in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖}, (cubFT w) ^ 2
        ≤ ∫ w in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖}, ∏ i : Fin 3, hBox (w i) :=
          setIntegral_mono_of_nonneg (fun w _ => sq_nonneg _)
            (fun w _ => hle w) hInt.integrableOn
      _ ≤ ∑ i : Fin 3, (8 * Real.sqrt 3 / L) * ∏ j ∈ Finset.univ.erase i, 8 := by
          refine exterior_prod_le (fun _ : Fin 3 => hBox) (fun _ => 8 * Real.sqrt 3 / L)
            (fun _ => 8) L hL (fun _ t => hBox_nonneg t) (fun _ => integrable_hBox)
            (fun _ => hBox_integral) fun _ => ?_
          rw [← htail_eq L hL]
          exact hBox_tail _ hpos
      _ ≤ 100000 / L :=
          (sum_erase_bound (8 * Real.sqrt 3 / L) (by positivity) (fun _ => 8)
            (fun _ => by norm_num) (fun _ => le_refl 8)).trans (hfinal L hL)
  · intro L hL
    have hpos : 0 < L / Real.sqrt 3 := div_pos hL (Real.sqrt_pos.mpr (by norm_num))
    have hstep : ∀ i : Fin 3, ∫ w in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖},
        (fderiv ℝ cubFT w (kcStdBasis i)) ^ 2 ≤ 3 * 512 * (8 * Real.sqrt 3 / L) := by
      intro i
      set g : Fin 3 → ℝ → ℝ := fun j t => if j = i then mBox t else hBox t with hg
      have hgnn : ∀ j t, 0 ≤ g j t := by
        intro j t
        show 0 ≤ (if j = i then mBox t else hBox t)
        by_cases hji : j = i
        · rw [if_pos hji]; exact mBox_nonneg t
        · rw [if_neg hji]; exact hBox_nonneg t
      have hge_mBox : g i = mBox := by
        rw [hg]; funext t; simp
      have hge_hBox : ∀ j : Fin 3, j ≠ i → g j = hBox := by
        intro j hj
        rw [hg]; funext t; simp [hj]
      have hgint : ∀ j, Integrable (g j) := by
        intro j
        by_cases hji : j = i
        · rw [hji, hge_mBox]; exact integrable_mBox
        · rw [hge_hBox j hji]; exact integrable_hBox
      have hgB : ∀ j, ∫ t : ℝ, g j t = (if j = i then ∫ t : ℝ, mBox t else 8) := by
        intro j
        by_cases hji : j = i
        · rw [if_pos hji, hji, hge_mBox]
        · rw [if_neg hji, hge_hBox j hji, hBox_integral]
      have hB8 : ∀ j, (if j = i then ∫ t : ℝ, mBox t else 8) ≤ 8 := by
        intro j
        by_cases hji : j = i
        · rw [if_pos hji]; exact mBox_integral_le.trans (by norm_num)
        · rw [if_neg hji]
      have hBnn : ∀ j, 0 ≤ (if j = i then ∫ t : ℝ, mBox t else 8) := by
        intro j
        by_cases hji : j = i
        · rw [if_pos hji]
          exact integral_nonneg fun t => mBox_nonneg t
        · rw [if_neg hji]; norm_num
      have hgA : ∀ j, ∫ t in {u : ℝ | L / Real.sqrt 3 ≤ |u|}, g j t
          ≤ 8 * Real.sqrt 3 / L := by
        intro j
        by_cases hji : j = i
        · rw [hji, hge_mBox, ← htail_eq L hL]
          exact mBox_tail _ hpos
        · rw [hge_hBox j hji, ← htail_eq L hL]
          exact hBox_tail _ hpos
      have hle : ∀ w : EuclideanSpace ℝ (Fin 3),
          (fderiv ℝ cubFT w (kcStdBasis i)) ^ 2 ≤ ∏ j : Fin 3, g j (w j) := by
        intro w
        have h1 : ∏ j : Fin 3, g j (w j)
            = (∏ j ∈ Finset.univ.erase i, hBox (w j)) * mBox (w i) := by
          rw [← Finset.prod_erase_mul Finset.univ (fun j : Fin 3 => g j (w j))
            (Finset.mem_univ i), hge_mBox]
          congr 1
          exact Finset.prod_congr rfl fun j hj => by
            rw [hge_hBox j (Finset.ne_of_mem_erase hj)]
        rw [h1, fderiv_sq_eq_prod hder w i]
        exact mul_le_mul (Finset.prod_le_prod₀ (fun j _ => sq_nonneg _)
          (fun j _ => hFT_sq_le_hBox (w j))) (mFT_sq_le_mBox (w i))
          (sq_nonneg _) (Finset.prod_nonneg fun j _ => hBox_nonneg (w j))
      have hInt : Integrable (fun q : EuclideanSpace ℝ (Fin 3) => ∏ j : Fin 3, g j (q j)) :=
        integrable_prod_euclidean hgint
      refine (setIntegral_mono_of_nonneg (fun w _ => sq_nonneg _)
        (fun w _ => hle w) hInt.integrableOn).trans ?_
      refine (exterior_prod_le g (fun _ => 8 * Real.sqrt 3 / L)
        (fun j => if j = i then ∫ t : ℝ, mBox t else 8) L hL hgnn hgint hgB hgA).trans ?_
      exact sum_erase_bound (8 * Real.sqrt 3 / L) (by positivity) _ hBnn hB8
    calc ∑ i : Fin 3, ∫ w in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖},
          (fderiv ℝ cubFT w (kcStdBasis i)) ^ 2
        ≤ ∑ _i : Fin 3, 3 * 512 * (8 * Real.sqrt 3 / L) := Finset.sum_le_sum fun i _ => hstep i
      _ ≤ 100000 / L := by
          have h2 : (∑ _i : Fin 3, (3 : ℝ) * 512 * (8 * Real.sqrt 3 / L))
              = 3 * (3 * 512 * (8 * Real.sqrt 3 / L)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            norm_num
          rw [h2]
          have h3 : (3 : ℝ) * (3 * 512 * (8 * Real.sqrt 3)) ≤ 100000 := by
            nlinarith [hsqrt3, Real.sqrt_nonneg 3]
          calc (3 : ℝ) * (3 * 512 * (8 * Real.sqrt 3 / L))
              = (3 * (3 * 512 * (8 * Real.sqrt 3))) / L := by ring
            _ ≤ 100000 / L := div_le_div_of_nonneg_right h3 hL.le

end Work.BoseKinLoc.Momentum
