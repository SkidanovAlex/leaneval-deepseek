import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.ModeExpansion
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.pz_aux
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.phiAj_smooth2
import Submission.Work.FTS.EllExist.Honesty.Pieces.primitive_contDiffOn
import Submission.Work.FTS.EllExist.Honesty.Pieces.tailIntegral_contDiffOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `Work.FTS.PhiStar.FlatWAux.ModeZDeriv`

Termwise `z`-differentiation of the mode series of `psiSeries α (RemSource α ψ)`
(the obligation `P1` of `FlatWAux/NOTES.md`); the route is recorded in `NOTES_ModeZDeriv.md`.

* `resc α m z = (z+1)/z · radGreen α m (phiA α) z` — the rescaled radial mode;
* `sliceSum` / `sliceMode` — the `θ`-slices of the rescaled series and of its `m`-th summand;
* `modeF` — the summand written through `bmode`;
* `iteratedDeriv_tsum_of_majorant` — the M-test for iterated derivatives of a `tsum`.

The only analytic input is the smoothness of `resc α m` on `(0,∞)` (`ModeRescaledSmooth`),
which is used for the differentiability of the individual modes.
-/

/-! ## The rescaled mode functions -/

/-- `resc α m z = (z+1)/z · radGreen α m (phiA α) z`, the rescaled radial mode. -/
private def resc (α : ℝ) (m : ℕ) : ℝ → ℝ :=
  fun z => (z + 1) / z * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z

/-- The `θ`-slice of the rescaled mode series. -/
private def sliceSum (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) : ℝ → ℝ :=
  fun y => (y + 1) / y
    * Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) y θ

/-- The `θ`-slice of the `m`-th summand of the rescaled mode series. -/
private def sliceMode (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) (m : ℕ) : ℝ → ℝ :=
  fun y => (y + 1) / y
    * (Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) y
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ)

/-- The same summand, written through `bmode` and `resc`. -/
private def modeF (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) (m : ℕ) : ℝ → ℝ :=
  fun y => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
    * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * resc α m y

private theorem sliceMode_eq_modeF (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) (m : ℕ) :
    sliceMode α ψ θ m = modeF α ψ θ m := by
  funext y
  simp only [sliceMode, modeF, resc]
  rw [Work.FTS.PhiStar.Series.acoeff_RemSource]
  ring

private theorem sliceSum_eq_tsum (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) :
    sliceSum α ψ θ = fun y => ∑' m : ℕ, modeF α ψ θ m y := by
  funext y
  simp only [sliceSum, modeF, resc, Work.FTS.PhiStar.Series.psiSeries]
  rw [← tsum_mul_left]
  refine tsum_congr (fun m => ?_)
  rw [Work.FTS.PhiStar.Series.acoeff_RemSource]
  ring

/-! ## Iterated derivatives of a `C^n` function on `(0,∞)` -/

private theorem continuousOn_iteratedDeriv_of_Ioi {f : ℝ → ℝ} {n m : ℕ}
    (hf : ContDiffOn ℝ n f (Set.Ioi 0)) (hmn : m ≤ n) :
    ContinuousOn (iteratedDeriv m f) (Set.Ioi 0) := by
  have h := ((contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
    (isOpen_Ioi.uniqueDiffOn) (n := n) (f := f)).mp hf).1 m hmn
  exact h.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm)

private theorem differentiableOn_iteratedDeriv_of_Ioi {f : ℝ → ℝ} {n m : ℕ}
    (hf : ContDiffOn ℝ n f (Set.Ioi 0)) (hmn : m < n) :
    DifferentiableOn ℝ (iteratedDeriv m f) (Set.Ioi 0) := by
  have h := ((contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
    (isOpen_Ioi.uniqueDiffOn) (n := n) (f := f)).mp hf).2 m hmn
  exact h.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm)

/-! ## Smoothness of the rescaled radial mode on `(0,∞)` -/

/-- A tail integral of a function of class `C^n` on `(0,∞)` is of class `C^n` there; if the
integrand is integrable on no tail, every integral is the junk value `0` (the dichotomy follows
from the continuity of the integrand on `(0,∞)`: two tails differ by a compact interval). -/
private theorem contDiffOn_Ioi_integral_all (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ n f (Set.Ioi 0)) :
    ContDiffOn ℝ n (fun z => ∫ t in Set.Ioi z, f t) (Set.Ioi 0) := by
  have hcont : ContinuousOn f (Set.Ioi 0) := hf.continuousOn
  by_cases h1 : MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ))
  · have hall : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn f (Set.Ioi z) := by
      intro z hz
      rcases le_or_gt 1 z with hle | hlt
      · exact h1.mono_set (Set.Ioi_subset_Ioi hle)
      · rw [← Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hlt)]
        refine IntegrableOn.union ?_ h1
        exact IntegrableOn.mono_set
          (ContinuousOn.integrableOn_Icc (hcont.mono (fun x hx => lt_of_lt_of_le hz hx.1)))
          Set.Ioc_subset_Icc_self
    exact Work.FTS.EllExist.Honesty.Pieces.tailIntegral_contDiffOn n hf (hall 1 one_pos)
  · have hzero : (fun z => ∫ t in Set.Ioi z, f t) = fun _ => (0 : ℝ) := by
      funext z
      apply MeasureTheory.integral_undef
      intro hint
      have hInt : MeasureTheory.IntegrableOn f (Set.Ioi z) := hint
      apply h1
      rcases le_or_gt z 1 with hle | hlt
      · exact hInt.mono_set (Set.Ioi_subset_Ioi hle)
      · rw [← Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hlt)]
        refine IntegrableOn.union ?_ hInt
        exact IntegrableOn.mono_set
          (ContinuousOn.integrableOn_Icc (hcont.mono (fun x hx => lt_of_lt_of_le one_pos hx.1)))
          Set.Ioc_subset_Icc_self
    rw [hzero]
    exact contDiffOn_const

/-- **The rescaled radial mode is smooth on `(0,∞)`** for every real `α`: the two integrals
defining `radGreen α m (phiA α)` are a primitive and a tail integral of functions that are `C^∞`
there, and the prefactors `z^{s^±}`, `(z+1)/z` are `C^∞` on `(0,∞)`. -/
private theorem resc_contDiffOn (α : ℝ) (m : ℕ) (n : ℕ) :
    ContDiffOn ℝ n (resc α m) (Set.Ioi 0) := by
  have hc : ContDiffOn ℝ n (Work.FTS.VocabO.phiA α) (Set.Ioi 0) :=
    fun z hz => (Work.FTS.PhiStar.contDiffAt_phiA_of α (n : WithTop ℕ∞) hz).contDiffWithinAt
  have hf1 : ContDiffOn ℝ n
      (fun t : ℝ => Work.FTS.VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioi 0) :=
    hc.mul (contDiffOn_id.rpow_const_of_ne (p := (2 * (m : ℝ) + 5) / α - 1)
      (fun x hx => ne_of_gt hx))
  have hf2 : ContDiffOn ℝ n
      (fun t : ℝ => Work.FTS.VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 0) :=
    hc.mul (contDiffOn_id.rpow_const_of_ne (p := -(2 * (m : ℝ) / α) - 1)
      (fun x hx => ne_of_gt hx))
  have hA : ContDiffOn ℝ n
      (fun z => ∫ t in (0 : ℝ)..z, Work.FTS.VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioi 0) :=
    Work.FTS.EllExist.Honesty.Pieces.primitive_contDiffOn n hf1
  have hB : ContDiffOn ℝ n
      (fun z => ∫ t in Set.Ioi z, Work.FTS.VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 0) :=
    contDiffOn_Ioi_integral_all n hf2
  have hza : ContDiffOn ℝ n (fun z : ℝ => z ^ (-(2 * (m : ℝ) + 5) / α)) (Set.Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (p := -(2 * (m : ℝ) + 5) / α) (fun x hx => ne_of_gt hx)
  have hzb : ContDiffOn ℝ n (fun z : ℝ => z ^ (2 * (m : ℝ) / α)) (Set.Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (p := 2 * (m : ℝ) / α) (fun x hx => ne_of_gt hx)
  have hmain : ContDiffOn ℝ n (fun z : ℝ => 1 / (α * (4 * (m : ℝ) + 5)) *
      (z ^ (-(2 * (m : ℝ) + 5) / α)
          * (∫ t in (0 : ℝ)..z, Work.FTS.VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        + z ^ (2 * (m : ℝ) / α)
          * (∫ t in Set.Ioi z, Work.FTS.VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1))))
      (Set.Ioi 0) :=
    contDiffOn_const.mul ((hza.mul hA).add (hzb.mul hB))
  have hG : ContDiffOn ℝ n
      (fun z => Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z) (Set.Ioi 0) :=
    hmain.congr (fun z _ => rfl)
  have hfac : ContDiffOn ℝ n (fun z : ℝ => (z + 1) / z) (Set.Ioi 0) :=
    (contDiffOn_id.add contDiffOn_const).div contDiffOn_id (fun z hz => ne_of_gt hz)
  exact (hfac.mul hG).congr (fun z _ => rfl)

/-! ## The M-test for iterated derivatives of a `tsum` -/

/-- **Termwise `k`-fold differentiation of a series.**  On an open preconnected set `t` on which
the iterated derivatives of each term are differentiable and dominated by summable majorants
`u j`, the iterated derivative of the sum is the sum of the iterated derivatives. -/
private theorem iteratedDeriv_tsum_of_majorant {k : ℕ} {t : Set ℝ} (ht : IsOpen t)
    (h't : IsPreconnected t) {f : ℕ → ℝ → ℝ} {u : ℕ → ℕ → ℝ}
    (hu : ∀ j : ℕ, j ≤ k → Summable (u j))
    (hdiff : ∀ j : ℕ, j < k → ∀ m : ℕ, DifferentiableOn ℝ (iteratedDeriv j (f m)) t)
    (hb : ∀ j : ℕ, j ≤ k → ∀ m : ℕ, ∀ y : ℝ, y ∈ t → |iteratedDeriv j (f m) y| ≤ u j m) :
    ∀ j : ℕ, j ≤ k → ∀ y : ℝ, y ∈ t →
      iteratedDeriv j (fun y' => ∑' m : ℕ, f m y') y = ∑' m : ℕ, iteratedDeriv j (f m) y := by
  intro j
  induction j with
  | zero =>
    intro _ y _
    simp only [iteratedDeriv_zero]
  | succ n ih =>
    intro hn1 y hy
    have hn : n ≤ k := Nat.le_of_succ_le hn1
    have hnk : n < k := Nat.lt_of_succ_le hn1
    have hIH : ∀ y' ∈ t, iteratedDeriv n (fun y' => ∑' m : ℕ, f m y') y'
        = ∑' m : ℕ, iteratedDeriv n (f m) y' := ih hn
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n (fun y' => ∑' m : ℕ, f m y') =ᶠ[𝓝 y]
        fun y' => ∑' m : ℕ, iteratedDeriv n (f m) y' := by
      filter_upwards [ht.mem_nhds hy] with y' hy'
      exact hIH y' hy'
    rw [hev.deriv_eq]
    have hder : HasDerivAt (fun y' => ∑' m : ℕ, iteratedDeriv n (f m) y')
        (∑' m : ℕ, iteratedDeriv (n + 1) (f m) y) y := by
      refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ) (u := u (n + 1))
        (g := fun m y' => iteratedDeriv n (f m) y')
        (g' := fun m y' => iteratedDeriv (n + 1) (f m) y')
        (hu (n + 1) hn1) ht h't ?_ ?_ (y₀ := y) hy ?_ hy
      · intro m y' hy'
        have hd : DifferentiableAt ℝ (iteratedDeriv n (f m)) y' :=
          (hdiff n hnk m).differentiableAt (ht.mem_nhds hy')
        have h := hd.hasDerivAt
        rwa [← iteratedDeriv_succ] at h
      · intro m y' hy'
        rw [Real.norm_eq_abs]
        exact hb (n + 1) hn1 m y' hy'
      · refine Summable.of_norm_bounded (hu n hn) (fun m => ?_)
        rw [Real.norm_eq_abs]
        exact hb n hn m y hy
    exact hder.deriv

/-! ## The arithmetic of the majorant -/

private lemma four_mul_sq_le_lam {m : ℕ} (hm : 1 ≤ m) :
    4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  nlinarith

private lemma sqrt_two_mul_add_one_ge {m : ℕ} (hm : 1 ≤ m) :
    (3 : ℝ) / 2 ≤ Real.sqrt (2 * (m : ℝ) + 1) := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Real.le_sqrt (by norm_num) (by linarith)]
  nlinarith

private lemma majorant_le {m : ℕ} (hm : 1 ≤ m) :
    (2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
        * Real.sqrt (2 * (m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m)
      ≤ (((m : ℝ) + 1) ^ 2)⁻¹ := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlam4 : 4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := four_mul_sq_le_lam hm
  have hlamp : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
    simp only [Work.FTS.PhiStar.Gegenbauer.lam]
    nlinarith
  have hs : (3 : ℝ) / 2 ≤ Real.sqrt (2 * (m : ℝ) + 1) := sqrt_two_mul_add_one_ge hm
  have hsp : 0 < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos_of_pos (by linarith)
  have hden : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
      * Work.FTS.PhiStar.Gegenbauer.lam m := by positivity
  rw [show (((m : ℝ) + 1) ^ 2)⁻¹ = 1 / ((m : ℝ) + 1) ^ 2 from by rw [one_div]]
  rw [div_le_div_iff₀ hden (by positivity : (0 : ℝ) < ((m : ℝ) + 1) ^ 2)]
  simp only [one_mul]
  have hm2 : 2 * (m : ℝ) + 1 ≤ 3 * (m : ℝ) := by linarith
  have hs2 : ((m : ℝ) + 1) ^ 2 ≤ (2 * (m : ℝ)) ^ 2 := by nlinarith
  have hstep1 : (2 * (m : ℝ) + 1) * ((m : ℝ) + 1) ^ 2
      ≤ (3 * (m : ℝ)) * (2 * (m : ℝ)) ^ 2 :=
    mul_le_mul hm2 hs2 (by positivity) (by positivity)
  have hstep2 : (3 * (m : ℝ)) * (2 * (m : ℝ)) ^ 2 = 12 * (m : ℝ) ^ 3 := by ring
  have hstep3 : 12 * (m : ℝ) ^ 3 ≤ 24 * (m : ℝ) ^ 4 := by nlinarith
  have hstep4 : 24 * (m : ℝ) ^ 4
      ≤ Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
        * Work.FTS.PhiStar.Gegenbauer.lam m := by
    have h2 : (4 * (m : ℝ) ^ 2) * ((3 : ℝ) / 2) ≤ Work.FTS.PhiStar.Gegenbauer.lam m
        * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_le_mul hlam4 hs (by norm_num) (le_of_lt hlamp)
    calc 24 * (m : ℝ) ^ 4 = (4 * (m : ℝ) ^ 2) * ((3 : ℝ) / 2) * (4 * (m : ℝ) ^ 2) := by ring
      _ ≤ (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * Work.FTS.PhiStar.Gegenbauer.lam m :=
          mul_le_mul h2 hlam4 (by positivity) (by positivity)
  linarith

private lemma summable_inv_sq_shift : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ 2)⁻¹) := by
  have h : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(2 : ℝ))) := by
    have h0 : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) :=
      (Real.summable_nat_rpow).mpr (by norm_num)
    have h1 := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) 1).mpr h0
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  refine h.congr (fun m => ?_)
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
  norm_num

/-! ## The core identity -/

private theorem core (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (hrb : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (resc α m) z'| ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m)
    (hS : ∀ (m n : ℕ), ContDiffOn ℝ n (resc α m) (Set.Ioi 0)) :
    ∀ k : ℕ, k ≤ 7 →
      iteratedDeriv k (sliceSum α ψ θ) z = ∑' m : ℕ, iteratedDeriv k (sliceMode α ψ θ m) z := by
  obtain ⟨Cb, hCb, hdec'⟩ := hdec
  obtain ⟨Ce, hCe, hgr'⟩ := hgr
  obtain ⟨Cr, hCr, hrb'⟩ := hrb
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  set V : ℝ := α ^ 2 * (Cb * Ce * Cr) with hV
  have hVnn : 0 ≤ V := by rw [hV]; positivity
  have hz2 : 0 < z / 2 := by linarith
  have ht : IsOpen (Set.Ioo (z / 2) (2 * z)) := isOpen_Ioo
  have h't : IsPreconnected (Set.Ioo (z / 2) (2 * z)) := isPreconnected_Ioo
  have hzt : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  have hsub : Set.Ioo (z / 2) (2 * z) ⊆ Set.Ioi 0 := by
    intro y hy
    exact lt_of_lt_of_le hz2 (le_of_lt hy.1)
  -- the iterated derivatives of the modes factor through `resc`
  have hconst_mode : ∀ (m j : ℕ) (y : ℝ), y ∈ Set.Ioi 0 →
      iteratedDeriv j (modeF α ψ θ m) y
        = (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * iteratedDeriv j (resc α m) y := by
    intro m j y hy
    rw [show modeF α ψ θ m = (fun x => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * resc α m x) from rfl]
    exact iteratedDeriv_const_mul _ ((hS m j).contDiffAt (isOpen_Ioi.mem_nhds hy))
  -- the `m = 0` term only needs a compact bound
  have hB : ∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ Set.Ioo (z / 2) (2 * z),
      |iteratedDeriv j (modeF α ψ θ 0) y| ≤ B := by
    intro j
    have hcont : ContinuousOn (iteratedDeriv j (resc α 0)) (Set.Ioi 0) :=
      continuousOn_iteratedDeriv_of_Ioi (hS 0 (j + 1)) (Nat.le_succ j)
    have hcc : Set.Icc (z / 2) (2 * z) ⊆ Set.Ioi 0 := by
      intro y hy
      exact lt_of_lt_of_le hz2 hy.1
    obtain ⟨C0, hC0⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc (hcont.mono hcc)
    refine ⟨|α ^ 2 * Work.FTS.PhiStar.Series.bmode 0 ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| * max C0 0 + 1, ?_⟩
    intro y hy
    have hy0 : y ∈ Set.Ioi (0 : ℝ) := hsub hy
    have hycc : y ∈ Set.Icc (z / 2) (2 * z) := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hbd : |iteratedDeriv j (resc α 0) y| ≤ C0 := by
      have h := hC0 y hycc
      rwa [Real.norm_eq_abs] at h
    rw [hconst_mode 0 j y hy0, abs_mul]
    calc |α ^ 2 * Work.FTS.PhiStar.Series.bmode 0 ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| * |iteratedDeriv j (resc α 0) y|
        ≤ |α ^ 2 * Work.FTS.PhiStar.Series.bmode 0 ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| * max C0 0 :=
          mul_le_mul_of_nonneg_left (le_max_of_le_left hbd) (abs_nonneg _)
      _ ≤ |α ^ 2 * Work.FTS.PhiStar.Series.bmode 0 ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| * max C0 0 + 1 := by linarith
  choose B hBspec using hB
  set U : ℕ → ℕ → ℝ := fun j m =>
    (if m = 0 then B j else 0) + V * (((m : ℝ) + 1) ^ 2)⁻¹ with hUdef
  have hU_sum : ∀ j : ℕ, Summable (U j) := by
    intro j
    rw [hUdef]
    refine Summable.add ?_ (summable_inv_sq_shift.mul_left V)
    refine summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) (fun b hb => ?_)
    simp only [Finset.mem_singleton] at hb
    simp [hb]
  -- the pointwise bound of the majorant
  have hU_bound : ∀ j : ℕ, j ≤ 7 → ∀ m : ℕ, ∀ y : ℝ, y ∈ Set.Ioo (z / 2) (2 * z) →
      |iteratedDeriv j (modeF α ψ θ m) y| ≤ U j m := by
    intro j hj m y hy
    have hy0 : 0 < y := lt_of_lt_of_le hz2 (le_of_lt hy.1)
    have hypos : y ∈ Set.Ioi (0 : ℝ) := hy0
    rw [hconst_mode m j y hypos, abs_mul]
    change |α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |iteratedDeriv j (resc α m) y|
      ≤ (if m = 0 then B j else 0) + V * (((m : ℝ) + 1) ^ 2)⁻¹
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [if_pos rfl]
      have hle : |α ^ 2 * Work.FTS.PhiStar.Series.bmode 0 ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| * |iteratedDeriv j (resc α 0) y|
          ≤ B j := by
        have h := hBspec j y hy
        rwa [hconst_mode 0 j y hy0, abs_mul] at h
      calc |α ^ 2 * Work.FTS.PhiStar.Series.bmode 0 ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| * |iteratedDeriv j (resc α 0) y|
          ≤ B j := hle
        _ ≤ B j + V * ((((0 : ℕ) : ℝ) + 1) ^ 2)⁻¹ := by
            have h2 : (0 : ℝ) ≤ V * ((((0 : ℕ) : ℝ) + 1) ^ 2)⁻¹ := by positivity
            linarith
    · rw [if_neg (Nat.pos_iff_ne_zero.mp hm), zero_add]
      have hk' : |iteratedDeriv j (resc α m) y| ≤ Cr / Work.FTS.PhiStar.Gegenbauer.lam m := by
        have hpow : (1 : ℝ) ≤ (y + 1) ^ j := one_le_pow₀ (by linarith)
        have h1 : |iteratedDeriv j (resc α m) y|
            ≤ |(y + 1) ^ j * iteratedDeriv j (resc α m) y| := by
          calc |iteratedDeriv j (resc α m) y| = 1 * |iteratedDeriv j (resc α m) y| := by ring
            _ ≤ (y + 1) ^ j * |iteratedDeriv j (resc α m) y| :=
                mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
            _ = |(y + 1) ^ j * iteratedDeriv j (resc α m) y| := by
                rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (y + 1) ^ j by positivity)]
        exact le_trans h1 (hrb' m hm j hj y hy0)
      have hbm : |Work.FTS.PhiStar.Series.bmode m ψ|
          ≤ Cb / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
        hdec' m hm
      have hem : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Ce * (2 * (m : ℝ) + 1) :=
        hgr' m θ hθIθ
      have hlamp : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
        simp only [Work.FTS.PhiStar.Gegenbauer.lam]
        have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        nlinarith
      have hlamnn : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := le_of_lt hlamp
      have hsnn : 0 ≤ Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_nonneg _
      have hm2nn : (0 : ℝ) ≤ 2 * (m : ℝ) + 1 := by positivity
      have hc1 : |α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          ≤ α ^ 2 * (Cb / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1))) * (Ce * (2 * (m : ℝ) + 1)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hbm (by positivity)) hem
          (abs_nonneg _)
          (mul_nonneg (by positivity)
            (div_nonneg (le_of_lt hCb) (mul_nonneg hlamnn hsnn)))
      have hprod : |α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |iteratedDeriv j (resc α m) y|
          ≤ V * ((2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m)) := by
        calc |α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |iteratedDeriv j (resc α m) y|
            ≤ (α ^ 2 * (Cb / (Work.FTS.PhiStar.Gegenbauer.lam m
                * Real.sqrt (2 * (m : ℝ) + 1))) * (Ce * (2 * (m : ℝ) + 1)))
                * (Cr / Work.FTS.PhiStar.Gegenbauer.lam m) :=
              mul_le_mul hc1 hk' (abs_nonneg _)
                (mul_nonneg (mul_nonneg (by positivity)
                  (div_nonneg (le_of_lt hCb) (mul_nonneg hlamnn hsnn)))
                  (mul_nonneg (le_of_lt hCe) hm2nn))
          _ = V * ((2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
                * Real.sqrt (2 * (m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m)) := by
              rw [hV]
              field_simp
      have hmaj := majorant_le hm
      calc |α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |iteratedDeriv j (resc α m) y|
          ≤ V * ((2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m)) := hprod
        _ ≤ V * (((m : ℝ) + 1) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hmaj hVnn
  intro k hk
  have hdiff_arg : ∀ j : ℕ, j < k → ∀ m : ℕ,
      DifferentiableOn ℝ (iteratedDeriv j (modeF α ψ θ m)) (Set.Ioo (z / 2) (2 * z)) := by
    intro j hj m
    have h1 : DifferentiableOn ℝ (fun y => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * iteratedDeriv j (resc α m) y)
        (Set.Ioo (z / 2) (2 * z)) :=
      ((differentiableOn_iteratedDeriv_of_Ioi (hS m (j + 1)) (Nat.lt_succ_self j)).const_mul
        (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ)).mono hsub
    exact h1.congr (fun y hy => hconst_mode m j y (hsub hy))
  have hmain := iteratedDeriv_tsum_of_majorant (t := Set.Ioo (z / 2) (2 * z)) ht h't
    (f := modeF α ψ θ) (u := U) (fun j _ => hU_sum j) hdiff_arg
    (fun j hj m y hy => hU_bound j (le_trans hj hk) m y hy) k le_rfl z hzt
  rw [sliceSum_eq_tsum]
  simp only [sliceMode_eq_modeF]
  exact hmain

theorem ModeZDeriv (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (hrb : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'') z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m) :
    ∀ k : ℕ, k ≤ 7 →
      (z + 1) ^ k * Work.Spaces.pzIter k
          (fun z' θ' => (z' + 1) / z' * Work.FTS.PhiStar.Series.psiSeries α
            (Work.FTS.PhiStar.RemSource α ψ) z' θ') z θ
        = ∑' m : ℕ, (z + 1) ^ k * Work.Spaces.pzIter k
            (fun z' θ' => (z' + 1) / z'
              * (Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z'
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ')) z θ := by
  intro k hk
  have hS : ∀ (m n : ℕ), ContDiffOn ℝ n (resc α m) (Set.Ioi 0) := fun m n => resc_contDiffOn α m n
  have hrb' : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (resc α m) z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m := by
    obtain ⟨C, hC, h⟩ := hrb
    exact ⟨C, hC, fun m hm k hk z' hz' => h m hm k hk z' hz'⟩
  have hcore := core α ψ z θ hz hθ hdec hgr hrb' hS k hk
  have hLHS : Work.Spaces.pzIter k (fun z' θ' => (z' + 1) / z'
      * Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z' θ') z θ
      = iteratedDeriv k (sliceSum α ψ θ) z := by
    rw [Work.Spaces.pzIter_eq_iteratedDeriv]
    exact congrArg (fun g => iteratedDeriv k g z) (by funext y; simp only [sliceSum])
  have hRHS : ∀ m : ℕ, Work.Spaces.pzIter k (fun z' θ' => (z' + 1) / z'
      * (Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z'
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ')) z θ
      = iteratedDeriv k (sliceMode α ψ θ m) z := by
    intro m
    rw [Work.Spaces.pzIter_eq_iteratedDeriv]
    exact congrArg (fun g => iteratedDeriv k g z) (by funext y; simp only [sliceMode])
  simp only [hLHS, hRHS]
  rw [hcore, tsum_mul_left]

end Work.FTS.PhiStar.FlatWAux
