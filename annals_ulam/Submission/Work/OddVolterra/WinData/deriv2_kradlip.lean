import Mathlib
import Submission.Work.OddVolterra.WinData.deriv2_zrad
import Submission.Work.OddVolterra.Window.krad_data

/-!
# Lipschitz-in-`t` bounds for `krad` and its first two `u`-derivatives
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.WinData

noncomputable section

open Work.OddVolterra Work.OddVolterra.Window

/-- `krad` as a product, with the `t`-dependence displayed. -/
lemma krad_eq_lin (h : ℝ → ℝ) (σ t u : ℝ) :
    krad h σ t u = (t + hquot h u σ) * ((σ + u) * t + h σ + h u) := by
  rw [krad_apply]; simp only [line]; ring

/-- First `u`-derivative of `krad`, as a function of `t`. -/
lemma deriv_krad_fst {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t u : ℝ) :
    deriv (fun u' : ℝ => krad h σ t u') u
      = deriv (fun u' : ℝ => hquot h u' σ) u * ((σ + u) * t + h σ + h u)
        + (t + hquot h u σ) * (t + deriv h u) := by
  have hqd : ContDiff ℝ (⊤ : ℕ∞) (fun u' : ℝ => hquot h u' σ) := by
    have hp : ContDiff ℝ (⊤ : ℕ∞) (fun u' : ℝ => (u', σ)) := by fun_prop
    have hcomp := (Work.OddVolterra.Existence.hquot_contDiff hh).comp hp
    rwa [show ((fun p : ℝ × ℝ => hquot h p.1 p.2) ∘ fun u' : ℝ => (u', σ))
        = fun u' : ℝ => hquot h u' σ from by funext u'; rfl] at hcomp
  have hfun : (fun u' : ℝ => krad h σ t u')
      = fun u' : ℝ => (t + hquot h u' σ) * ((σ + u') * t + h σ + h u') := by
    funext u'; exact krad_eq_lin h σ t u'
  rw [hfun]
  have hd1 : HasDerivAt (fun u' : ℝ => t + hquot h u' σ)
      (deriv (fun u' : ℝ => hquot h u' σ) u) u :=
    ((hqd.differentiable (by simp)).differentiableAt.hasDerivAt).const_add t
  have hd2 : HasDerivAt (fun u' : ℝ => (σ + u') * t + h σ + h u') (t + deriv h u) u := by
    have hlin : HasDerivAt (fun u' : ℝ => (σ + u') * t) t u := by
      have he : (fun u' : ℝ => (σ + u') * t) = fun u' : ℝ => t * u' + σ * t := by
        funext u'; ring
      rw [he]; simpa using ((hasDerivAt_id u).const_mul t).add_const (σ * t)
    have hsum := hlin.add ((hh.differentiable (by simp) u).hasDerivAt.const_add (h σ))
    have heq : ((fun u' : ℝ => (σ + u') * t) + fun x : ℝ => h σ + h x)
        = fun u' : ℝ => (σ + u') * t + h σ + h u' := by
      funext u'; simp only [Pi.add_apply]; ring
    rwa [heq] at hsum
  exact ((hd1.mul hd2)).deriv

/-- Second `u`-derivative of `krad`, as a function of `t`. -/
lemma deriv2_krad_fst {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t u : ℝ) :
    deriv (deriv (fun u' : ℝ => krad h σ t u')) u
      = deriv (deriv (fun u' : ℝ => hquot h u' σ)) u * ((σ + u) * t + h σ + h u)
        + 2 * deriv (fun u' : ℝ => hquot h u' σ) u * (t + deriv h u)
        + (t + hquot h u σ) * iteratedDeriv 2 h u := by
  have hqd : ContDiff ℝ (⊤ : ℕ∞) (fun u' : ℝ => hquot h u' σ) := by
    have hp : ContDiff ℝ (⊤ : ℕ∞) (fun u' : ℝ => (u', σ)) := by fun_prop
    have hcomp := (Work.OddVolterra.Existence.hquot_contDiff hh).comp hp
    rwa [show ((fun p : ℝ × ℝ => hquot h p.1 p.2) ∘ fun u' : ℝ => (u', σ))
        = fun u' : ℝ => hquot h u' σ from by funext u'; rfl] at hcomp
  have hqd1 : ContDiff ℝ (⊤ : ℕ∞) (deriv (fun u' : ℝ => hquot h u' σ)) :=
    ContDiff.deriv' (n := (⊤ : ℕ∞)) (by simpa using hqd)
  -- the first derivative as a function of the point
  have hE1 : ∀ u' : ℝ, deriv (fun v : ℝ => krad h σ t v) u'
      = deriv (fun v : ℝ => hquot h v σ) u' * ((σ + u') * t + h σ + h u')
        + (t + hquot h u' σ) * (t + deriv h u') := fun u' => deriv_krad_fst hh σ t u'
  have hE1fun : deriv (fun u' : ℝ => krad h σ t u')
      = fun u' : ℝ => deriv (fun v : ℝ => hquot h v σ) u' * ((σ + u') * t + h σ + h u')
          + (t + hquot h u' σ) * (t + deriv h u') := by
    funext u'; exact hE1 u'
  rw [hE1fun]
  -- differentiate the two products
  have hdA : HasDerivAt (fun u' : ℝ => deriv (fun v : ℝ => hquot h v σ) u' * ((σ + u') * t + h σ + h u'))
      (deriv (deriv (fun v : ℝ => hquot h v σ)) u * ((σ + u) * t + h σ + h u)
        + deriv (fun v : ℝ => hquot h v σ) u * (t + deriv h u)) u := by
    have hd1 : HasDerivAt (fun u' : ℝ => deriv (fun v : ℝ => hquot h v σ) u')
        (deriv (deriv (fun v : ℝ => hquot h v σ)) u) u :=
      ((hqd1.differentiable (by simp)).differentiableAt.hasDerivAt)
    have hd2 : HasDerivAt (fun u' : ℝ => (σ + u') * t + h σ + h u') (t + deriv h u) u := by
      have hlin : HasDerivAt (fun u' : ℝ => (σ + u') * t) t u := by
        have he : (fun u' : ℝ => (σ + u') * t) = fun u' : ℝ => t * u' + σ * t := by
          funext u'; ring
        rw [he]; simpa using ((hasDerivAt_id u).const_mul t).add_const (σ * t)
      have hsum := hlin.add ((hh.differentiable (by simp) u).hasDerivAt.const_add (h σ))
      have heq : ((fun u' : ℝ => (σ + u') * t) + fun x : ℝ => h σ + h x)
          = fun u' : ℝ => (σ + u') * t + h σ + h u' := by
        funext u'; simp only [Pi.add_apply]; ring
      rwa [heq] at hsum
    exact hd1.mul hd2
  have hdB : HasDerivAt (fun u' : ℝ => (t + hquot h u' σ) * (t + deriv h u'))
      (deriv (fun v : ℝ => hquot h v σ) u * (t + deriv h u)
        + (t + hquot h u σ) * iteratedDeriv 2 h u) u := by
    have hd1 : HasDerivAt (fun u' : ℝ => t + hquot h u' σ)
        (deriv (fun u' : ℝ => hquot h u' σ) u) u :=
      ((hqd.differentiable (by simp)).differentiableAt.hasDerivAt).const_add t
    have hd2 : HasDerivAt (fun u' : ℝ => t + deriv h u') (iteratedDeriv 2 h u) u := by
      have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv h) :=
        ContDiff.deriv' (n := (⊤ : ℕ∞)) (by simpa using hh)
      have hd' : DifferentiableAt ℝ (deriv h) u := (hd.differentiable (by simp)).differentiableAt
      have hthis : HasDerivAt (deriv h) (deriv (deriv h) u) u := hd'.hasDerivAt
      have he : iteratedDeriv 2 h u = deriv (deriv h) u := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      rw [he]
      exact hthis.const_add t
    exact hd1.mul hd2
  have hsplit : (fun u' : ℝ => deriv (fun v : ℝ => hquot h v σ) u' * ((σ + u') * t + h σ + h u')
        + (t + hquot h u' σ) * (t + deriv h u'))
      = ((fun u' : ℝ => deriv (fun v : ℝ => hquot h v σ) u' * ((σ + u') * t + h σ + h u'))
          + fun u' => (t + hquot h u' σ) * (t + deriv h u')) := by
    funext u'; simp only [Pi.add_apply]
  rw [hsplit, (hdA.add hdB).deriv]
  ring

/-- **Lipschitz-in-`t` of `krad` and its first two `u`-derivatives.** -/
theorem krad_lipschitz_t :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (h : ℝ → ℝ) (u σ : ℝ),
        ContDiff ℝ (⊤ : ℕ∞) h →
        (∀ k : ℕ, k ≤ 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
        u ∈ Set.Icc (3 / 16 : ℝ) 1 → σ ∈ Set.Icc (1 / 4 : ℝ) 1 →
        ∀ t t' : ℝ, 1 / 5 ≤ |t| → |t| ≤ 2 → 1 / 5 ≤ |t'| → |t'| ≤ 2 →
        (|krad h σ t u - krad h σ t' u| ≤ K * |t - t'| ∧
         |deriv (fun x : ℝ => krad h σ t x) u -
          deriv (fun x : ℝ => krad h σ t' x) u| ≤ K * |t - t'| ∧
         |deriv (deriv (fun x : ℝ => krad h σ t x)) u -
          deriv (deriv (fun x : ℝ => krad h σ t' x)) u| ≤ K * |t - t'|) := by
  refine ⟨11, by norm_num, ?_⟩
  intro h u σ hh hjet hu hσ t t' ht1 ht2 ht1' ht2'
  have h0 : ∀ s : ℝ, |h s| ≤ 1 / 100 := fun s => hjet 0 (by norm_num) s
  have h1 : ∀ s : ℝ, |deriv h s| ≤ 1 / 100 := fun s => by
    have := hjet 1 (by norm_num) s; rwa [iteratedDeriv_one] at this
  have h2 : ∀ s : ℝ, |iteratedDeriv 2 h s| ≤ 1 / 100 := fun s => hjet 2 (by norm_num) s
  have h3 : ∀ s : ℝ, |iteratedDeriv 3 h s| ≤ 1 / 100 := fun s => hjet 3 (by norm_num) s
  have hu_abs : |u| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
  have hσ_abs : |σ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2]
  have hsu : |σ + u| ≤ 5 / 2 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hσ.1, hσ.2]
  have hQ : |hquot h u σ| ≤ 1 / 100 := Work.OddExistence.Manifest.AW.abs_hquot_le_state h1
  have hQd := Work.OddExistence.Manifest.AW.hquot_deriv_bound hh (by norm_num) h1 h2 u σ
  have hQ1 : |deriv (fun x : ℝ => hquot h x σ) u| ≤ 1 / 100 := hQd.2
  have hQ2 : |deriv (deriv (fun x : ℝ => hquot h x σ)) u| ≤ 1 / 100 :=
    hquot_deriv2_bound hh (by norm_num) h3 σ u
  have htt : |t + t'| ≤ 4 := by have := abs_add_le t t'; linarith
  have hhul : |h σ + h u| ≤ 1 / 50 := by
    have a := abs_le.mp (h0 σ); have b := abs_le.mp (h0 u)
    rw [abs_le]; constructor <;> linarith [a.1, a.2, b.1, b.2]
  refine ⟨?_, ?_, ?_⟩
  · -- the value of `krad`
    have hfac : krad h σ t u - krad h σ t' u
        = (t - t') * (((σ + u) * t + h σ + h u) + (t' + hquot h u σ) * (σ + u)) := by
      rw [krad_eq_lin h σ t u, krad_eq_lin h σ t' u]; ring
    rw [hfac, abs_mul]
    have hb1 : |(σ + u) * t + h σ + h u| ≤ 21 / 4 := by
      have hσt : |(σ + u) * t| ≤ 5 := by
        rw [abs_mul]
        calc |σ + u| * |t| ≤ (5 / 2) * 2 := mul_le_mul hsu ht2 (abs_nonneg _) (by norm_num)
          _ = 5 := by norm_num
      have h2 := abs_add_le ((σ + u) * t) (h σ)
      have h3 := abs_add_le ((σ + u) * t + h σ) (h u)
      have h4 : |h σ| ≤ 1 / 100 := h0 σ
      have h5 : |h u| ≤ 1 / 100 := h0 u
      linarith [h3, h2, hσt, h4, h5]
    have hb2 : |t' + hquot h u σ| ≤ 201 / 100 := by
      calc |t' + hquot h u σ| ≤ |t'| + |hquot h u σ| := abs_add_le _ _
        _ ≤ 2 + 1 / 100 := by linarith [ht2', hQ]
        _ ≤ 201 / 100 := by norm_num
    have hb3 : |(t' + hquot h u σ) * (σ + u)| ≤ 201 / 100 * (5 / 2) := by
      rw [abs_mul]; exact mul_le_mul hb2 hsu (abs_nonneg _) (by norm_num)
    have hB : |((σ + u) * t + h σ + h u) + (t' + hquot h u σ) * (σ + u)| ≤ 11 := by
      calc |((σ + u) * t + h σ + h u) + (t' + hquot h u σ) * (σ + u)|
          ≤ |(σ + u) * t + h σ + h u| + |(t' + hquot h u σ) * (σ + u)| := abs_add_le _ _
        _ ≤ 21 / 4 + 201 / 100 * (5 / 2) := add_le_add hb1 hb3
        _ ≤ 11 := by norm_num
    calc |t - t'| * |((σ + u) * t + h σ + h u) + (t' + hquot h u σ) * (σ + u)|
        ≤ |t - t'| * 11 := mul_le_mul_of_nonneg_left hB (abs_nonneg _)
      _ = 11 * |t - t'| := by ring
  · -- the first `u`-derivative
    have hfac : (deriv (fun u' : ℝ => krad h σ t u') u - deriv (fun u' : ℝ => krad h σ t' u') u)
        = (t - t') * ((deriv (fun u' : ℝ => hquot h u' σ) u * (σ + u) + (t + t'))
            + (deriv h u + hquot h u σ)) := by
      rw [deriv_krad_fst hh σ t u, deriv_krad_fst hh σ t' u]; ring
    rw [hfac, abs_mul]
    have hA1 : |deriv (fun u' : ℝ => hquot h u' σ) u * (σ + u)| ≤ 1 / 100 * (5 / 2) := by
      rw [abs_mul]; exact mul_le_mul hQ1 hsu (abs_nonneg _) (by norm_num)
    have hB : |(deriv (fun u' : ℝ => hquot h u' σ) u * (σ + u) + (t + t'))
        + (deriv h u + hquot h u σ)| ≤ 11 := by
      calc |(deriv (fun u' : ℝ => hquot h u' σ) u * (σ + u) + (t + t'))
            + (deriv h u + hquot h u σ)|
          ≤ |deriv (fun u' : ℝ => hquot h u' σ) u * (σ + u) + (t + t')|
            + |deriv h u + hquot h u σ| := abs_add_le _ _
        _ ≤ (|deriv (fun u' : ℝ => hquot h u' σ) u * (σ + u)| + |t + t'|)
            + (|deriv h u| + |hquot h u σ|) :=
              add_le_add (abs_add_le _ _) (abs_add_le _ _)
        _ ≤ (1 / 100 * (5 / 2) + 4) + (1 / 100 + 1 / 100) :=
              add_le_add (add_le_add hA1 htt) (add_le_add (h1 u) hQ)
        _ ≤ 11 := by norm_num
    calc |t - t'| * |(deriv (fun u' : ℝ => hquot h u' σ) u * (σ + u) + (t + t'))
          + (deriv h u + hquot h u σ)|
        ≤ |t - t'| * 11 := mul_le_mul_of_nonneg_left hB (abs_nonneg _)
      _ = 11 * |t - t'| := by ring
  · -- the second `u`-derivative
    have hfac : (deriv (deriv (fun u' : ℝ => krad h σ t u')) u -
          deriv (deriv (fun u' : ℝ => krad h σ t' u')) u)
        = (t - t') * ((deriv (deriv (fun u' : ℝ => hquot h u' σ)) u * (σ + u)
            + 2 * deriv (fun u' : ℝ => hquot h u' σ) u) + iteratedDeriv 2 h u) := by
      rw [deriv2_krad_fst hh σ t u, deriv2_krad_fst hh σ t' u]; ring
    rw [hfac, abs_mul]
    have hA1 : |deriv (deriv (fun u' : ℝ => hquot h u' σ)) u * (σ + u)| ≤ 1 / 100 * (5 / 2) := by
      rw [abs_mul]; exact mul_le_mul hQ2 hsu (abs_nonneg _) (by norm_num)
    have hA2 : |2 * deriv (fun u' : ℝ => hquot h u' σ) u| ≤ 2 * (1 / 100) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left hQ1 (by norm_num)
    have hB : |(deriv (deriv (fun u' : ℝ => hquot h u' σ)) u * (σ + u)
        + 2 * deriv (fun u' : ℝ => hquot h u' σ) u) + iteratedDeriv 2 h u| ≤ 11 := by
      calc |(deriv (deriv (fun u' : ℝ => hquot h u' σ)) u * (σ + u)
            + 2 * deriv (fun u' : ℝ => hquot h u' σ) u) + iteratedDeriv 2 h u|
          ≤ |deriv (deriv (fun u' : ℝ => hquot h u' σ)) u * (σ + u)
              + 2 * deriv (fun u' : ℝ => hquot h u' σ) u| + |iteratedDeriv 2 h u| :=
            abs_add_le _ _
        _ ≤ (|deriv (deriv (fun u' : ℝ => hquot h u' σ)) u * (σ + u)|
              + |2 * deriv (fun u' : ℝ => hquot h u' σ) u|) + |iteratedDeriv 2 h u| :=
            add_le_add (abs_add_le _ _) le_rfl
        _ ≤ (1 / 100 * (5 / 2) + 2 * (1 / 100)) + 1 / 100 :=
            add_le_add (add_le_add hA1 hA2) (h2 u)
        _ ≤ 11 := by norm_num
    calc |t - t'| * |(deriv (deriv (fun u' : ℝ => hquot h u' σ)) u * (σ + u)
          + 2 * deriv (fun u' : ℝ => hquot h u' σ) u) + iteratedDeriv 2 h u|
        ≤ |t - t'| * 11 := mul_le_mul_of_nonneg_left hB (abs_nonneg _)
      _ = 11 * |t - t'| := by ring

end

end Work.OddVolterra.WinData
