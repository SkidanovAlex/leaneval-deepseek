import Mathlib
import Submission.Work.OddVolterra.WinData.Basic
import Submission.Work.OddExistence.Manifest.aw_toolkit

/-!
# Bounds for the Abel radicand on a general slope box

For a bump `h` supported in `[1-2τ,1-τ]` and `C²`-small by `δ`, on the slope box
`A ≤ a, σ ≤ 1` (with `0 < A`) and for `|t| ∈ [1/5, 2]`, the radicand
`krad h σ t a = (t + hquot h a σ) (line h σ t + line h a t)` is bounded below by
`kradLo A := (19/100) min (2A/5) (7/50) > 0` and above by `20`, it differs from the
unperturbed radicand by `O(δ)`, and its `a`-derivative obeys the same two bounds.
-/

namespace Work.OddVolterra.WinData

open Work.OddVolterra
open scoped Topology ContDiff Interval

noncomputable section

/-- The divided difference and its first `a`-derivative are bounded by the `C²`-bound of `h`. -/
lemma hquot_bounds {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h1 : ∀ x : ℝ, |deriv h x| ≤ δ) (h2 : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ δ) (a σ : ℝ) :
    |hquot h a σ| ≤ δ ∧ |deriv (fun a' : ℝ => hquot h a' σ) a| ≤ δ :=
  Work.OddExistence.Manifest.AW.hquot_deriv_bound hh hδ0 h1 h2 a σ

/-- The lowering constant of the Abel radicand. -/
def kradLo (A : ℝ) : ℝ := (19 / 100 : ℝ) * min (2 * A / 5) (7 / 50)

lemma kradLo_pos {A : ℝ} (hA : 0 < A) : 0 < kradLo A := by
  have h : 0 < min (2 * A / 5) (7 / 50) := lt_min (by linarith) (by norm_num)
  exact mul_pos (by norm_num) h

lemma min_lo_pos {A : ℝ} (hA : 0 < A) : 0 < min (2 * A / 5) (7 / 50) :=
  lt_min (by linarith) (by norm_num)

/-- **The Abel radicand on a general slope box.** -/
theorem krad_jets {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ)
    {A a σ t : ℝ} (hA : 0 < A) (ha : A ≤ a) (hσ : A ≤ σ) (hσ1 : σ ≤ 1) (ha1 : a ≤ 1)
    (ht : 1 / 5 ≤ |t|) (ht2 : |t| ≤ 2) :
    kradLo A ≤ krad h σ t a ∧ krad h σ t a ≤ 20 ∧
    |krad h σ t a - krad 0 σ t a| ≤ 10 * δ ∧
    |deriv (fun a' : ℝ => krad h σ t a') a| ≤ 20 ∧
    |deriv (fun a' : ℝ => krad h σ t a') a - deriv (fun a' : ℝ => krad 0 σ t a') a| ≤ 10 * δ := by
  have hh0 : ∀ x : ℝ, |h x| ≤ δ := fun x => by simpa using hjet 0 (by norm_num) x
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ δ := fun x => by simpa using hjet 1 (by norm_num) x
  have hh2 : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ δ := fun x => hjet 2 (by norm_num) x
  have hq : |hquot h a σ| ≤ δ := (hquot_bounds hh hδ0 hh1 hh2 a σ).1
  have hqd : |deriv (fun a' : ℝ => hquot h a' σ) a| ≤ δ := (hquot_bounds hh hδ0 hh1 hh2 a σ).2
  have hqb : -δ ≤ hquot h a σ ∧ hquot h a σ ≤ δ := abs_le.mp hq
  -- `h` vanishes below `4/5`
  have hzero : ∀ x : ℝ, x < 4 / 5 → h x = 0 := by
    intro x hx
    by_contra hne
    have hmem := hsupp (Function.mem_support.mpr hne)
    have h1 : (1 : ℝ) - 2 * tau = 4 / 5 := by rw [tau]; norm_num
    have h2 : (1 : ℝ) - tau = 9 / 10 := by rw [tau]; norm_num
    rw [h1, h2] at hmem
    linarith [hmem.1]
  have hline : line h σ t + line h a t = (σ + a) * t + (h σ + h a) := by
    unfold line; ring
  have hS : (0 : ℝ) < σ + a := by linarith
  have hc : |h σ + h a| ≤ 2 * δ := by
    have h1 := abs_le.mp (hh0 σ); have h2 := abs_le.mp (hh0 a)
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hc1 : |h σ + h a| ≤ 1 / 50 := by linarith
  have hSab : σ + a ≤ 2 := by linarith
  -- ## the lower bound for the second factor
  have hkey : min (2 * A / 5) (7 / 50) ≤ (σ + a) * |t| - |h σ + h a| := by
    rcases le_or_gt (4 / 5 : ℝ) σ with h45 | h45
    · have h3 : (4 : ℝ) / 5 ≤ σ + a := by linarith
      have h4 : (4 : ℝ) / 25 ≤ (σ + a) * |t| := by
        have h4' := mul_le_mul h3 ht (show (0:ℝ) ≤ 1/5 by norm_num)
          (show (0:ℝ) ≤ σ + a by linarith)
        linarith [h4']
      have h5 : |h σ + h a| ≤ 1 / 50 := hc1
      have h6 : min (2 * A / 5) (7 / 50) ≤ 7 / 50 := min_le_right _ _
      linarith
    · have hzσ : h σ = 0 := hzero σ h45
      have hca : |h a| ≤ 2 * δ := by
        have h' : |h σ + h a| = |h a| := by rw [hzσ, zero_add]
        simpa [h'] using hc
      by_cases ha45 : (4 / 5 : ℝ) ≤ a
      · have h3 : (4 : ℝ) / 5 ≤ σ + a := by linarith
        have h4 : (4 : ℝ) / 25 ≤ (σ + a) * |t| := by
          have h4' := mul_le_mul h3 ht (show (0:ℝ) ≤ 1/5 by norm_num)
            (show (0:ℝ) ≤ σ + a by linarith)
          linarith [h4']
        have h5 : |h a| ≤ 1 / 50 := by linarith
        have h6 : min (2 * A / 5) (7 / 50) ≤ 7 / 50 := min_le_right _ _
        have h' : |h σ + h a| = |h a| := by rw [hzσ, zero_add]
        rw [h']
        linarith
      · have hza : h a = 0 := hzero a (lt_of_not_ge ha45)
        have h3 : 2 * A ≤ σ + a := by linarith
        have h4 : 2 * A / 5 ≤ (σ + a) * |t| := by
          have h4' := mul_le_mul h3 ht (show (0:ℝ) ≤ 1/5 by norm_num)
            (show (0:ℝ) ≤ σ + a by linarith)
          linarith [h4']
        have h6 : min (2 * A / 5) (7 / 50) ≤ 2 * A / 5 := min_le_left _ _
        have h' : |h σ + h a| = 0 := by rw [hzσ, hza, add_zero, abs_zero]
        rw [h']; linarith
  -- ## the first factor
  have htpos : 0 < |t| := by linarith
  have hfac1 : (19 / 100 : ℝ) ≤ |t + hquot h a σ| := by
    have h' : |t| ≤ |t + hquot h a σ| + |hquot h a σ| := by
      have habs := abs_add_le (t + hquot h a σ) (-(hquot h a σ))
      rw [show t + hquot h a σ + -(hquot h a σ) = t by ring] at habs
      simpa only [abs_neg] using habs
    have h2 : |hquot h a σ| ≤ 1 / 100 := le_trans hq hδ1
    linarith
  -- ## positivity of the product
  have hprod : 0 ≤ (t + hquot h a σ) * ((σ + a) * t + (h σ + h a)) := by
    have h1 : (0 : ℝ) < t * (t + hquot h a σ) := by
      have hb : |t| * (|t| - |hquot h a σ|) ≤ t * (t + hquot h a σ) := by
        have h4 : |t| * |t| = t * t := abs_mul_abs_self t
        have h5 : -(|t| * |hquot h a σ|) ≤ t * hquot h a σ := by
          have h6 := neg_abs_le (t * hquot h a σ)
          rwa [abs_mul] at h6
        nlinarith [h4, h5, abs_nonneg t, abs_nonneg (hquot h a σ)]
      have h7 : |hquot h a σ| ≤ 1 / 100 := le_trans hq hδ1
      have h8 : (0 : ℝ) < |t| * (|t| - |hquot h a σ|) := by
        have h9 : (19 : ℝ) / 100 ≤ |t| - |hquot h a σ| := by linarith
        exact mul_pos htpos (lt_of_lt_of_le (by norm_num) h9)
      linarith
    have h2 : (0 : ℝ) < t * ((σ + a) * t + (h σ + h a)) := by
      have hb : |t| * ((σ + a) * |t| - |h σ + h a|) ≤ t * ((σ + a) * t + (h σ + h a)) := by
        have h4 : |t| * |t| = t * t := abs_mul_abs_self t
        have h5 : -(|t| * |h σ + h a|) ≤ t * (h σ + h a) := by
          have h6 := neg_abs_le (t * (h σ + h a))
          rwa [abs_mul] at h6
        nlinarith [h4, h5, abs_nonneg t, abs_nonneg (h σ + h a), hS]
      have h8 : (0 : ℝ) < |t| * ((σ + a) * |t| - |h σ + h a|) := by
        have h9 : (0 : ℝ) < (σ + a) * |t| - |h σ + h a| :=
          lt_of_lt_of_le (min_lo_pos hA) hkey
        exact mul_pos htpos h9
      linarith
    have h3 : (0 : ℝ) < t ^ 2 * ((t + hquot h a σ) * ((σ + a) * t + (h σ + h a))) := by
      have he : t ^ 2 * ((t + hquot h a σ) * ((σ + a) * t + (h σ + h a)))
          = (t * (t + hquot h a σ)) * (t * ((σ + a) * t + (h σ + h a))) := by ring
      rw [he]; exact mul_pos h1 h2
    by_contra hlt
    have h4 : t ^ 2 * ((t + hquot h a σ) * ((σ + a) * t + (h σ + h a))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hlt)
    linarith
  have hkr : krad h σ t a = (t + hquot h a σ) * ((σ + a) * t + (h σ + h a)) := by
    rw [krad_apply, hline]
  have hsgn : krad h σ t a = |t + hquot h a σ| * |(σ + a) * t + (h σ + h a)| := by
    rw [hkr, ← abs_of_nonneg hprod, abs_mul]
  -- ## bounds on the factors
  have htq : |t + hquot h a σ| ≤ 3 := by
    have h := abs_le.mp ht2
    rw [abs_le]; constructor <;> linarith [hqb.1, hqb.2, h.1, h.2]
  have hsum2 : |(σ + a) * t + (h σ + h a)| ≤ 5 := by
    have h1 : |(σ + a) * t| ≤ 4 := by
      rw [abs_mul, abs_of_pos hS]
      have h2 : (σ + a) * |t| ≤ 2 * 2 :=
        mul_le_mul hSab ht2 (abs_nonneg t) (by norm_num)
      linarith
    have h4 : |h σ + h a| ≤ 1 / 50 := hc1
    linarith [abs_add_le ((σ + a) * t) (h σ + h a), h1, h4]
  -- ## summary bounds
  have hge : kradLo A ≤ krad h σ t a := by
    have h2 : min (2 * A / 5) (7 / 50) ≤ |(σ + a) * t + (h σ + h a)| := by
      have habs : (σ + a) * |t| - |h σ + h a| ≤ |(σ + a) * t + (h σ + h a)| := by
        have hrev := abs_add_le ((σ + a) * t + (h σ + h a)) (-(h σ + h a))
        have h1 : (σ + a) * t + (h σ + h a) + -(h σ + h a) = (σ + a) * t := by ring
        rw [h1, abs_neg, abs_mul, abs_of_pos hS] at hrev
        linarith
      linarith
    rw [hsgn, kradLo]
    exact mul_le_mul hfac1 h2 (min_lo_pos hA).le (abs_nonneg _)
  have hle : krad h σ t a ≤ 20 := by
    rw [hkr]
    have h6 : |(t + hquot h a σ) * ((σ + a) * t + (h σ + h a))| ≤ 3 * 5 := by
      rw [abs_mul]
      exact mul_le_mul htq hsum2 (abs_nonneg _) (by norm_num)
    linarith [le_abs_self ((t + hquot h a σ) * ((σ + a) * t + (h σ + h a))), h6]
  -- ## the unperturbed radicand
  have hkr0 : (fun a' : ℝ => krad 0 σ t a') = fun a' => (σ + a') * t * t := by
    funext a'; rw [krad_apply]; simp [line, hquot]; ring
  -- ## the difference of the values
  have hval : |krad h σ t a - krad 0 σ t a| ≤ 10 * δ := by
    have hkr0' : krad 0 σ t a = (σ + a) * t * t := congrFun hkr0 a
    rw [hkr, hkr0']
    have hsplit : (t + hquot h a σ) * ((σ + a) * t + (h σ + h a)) - (σ + a) * t * t
        = t * (h σ + h a) + hquot h a σ * ((σ + a) * t + (h σ + h a)) := by ring
    rw [hsplit]
    have hb1 : |t * (h σ + h a)| ≤ 2 * (2 * δ) := by
      rw [abs_mul]
      exact mul_le_mul ht2 hc (abs_nonneg _) (by norm_num)
    have hb2 : |hquot h a σ * ((σ + a) * t + (h σ + h a))| ≤ δ * 5 := by
      rw [abs_mul]
      exact mul_le_mul hq hsum2 (abs_nonneg _) hδ0
    calc |t * (h σ + h a) + hquot h a σ * ((σ + a) * t + (h σ + h a))|
        ≤ 2 * (2 * δ) + δ * 5 := le_trans (abs_add_le _ _) (add_le_add hb1 hb2)
      _ ≤ 10 * δ := by linarith
  -- ## differentiability and the derivative
  have hdh : DifferentiableAt ℝ h a := (hh.differentiable (by simp)).differentiableAt
  have hd1 : DifferentiableAt ℝ (fun a' : ℝ => hquot h a' σ) a := by
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => hquot h p.1 p.2) :=
      Work.OddExistence.Manifest.AW.hquot_contDiff_local hh
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => (a', σ)) := by fun_prop
    exact ((hcd.comp h2).differentiable (by simp)).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun a' : ℝ => (σ + a') * t + (h σ + h a')) a := by
    have hfun : (fun a' : ℝ => (σ + a') * t + (h σ + h a'))
        = fun a' => (a' * t + h a') + (σ * t + h σ) := by funext a'; ring
    rw [hfun]
    exact (((differentiableAt_id (x := a)).mul_const t).add hdh).add_const _
  have hdl : HasDerivAt (fun a' : ℝ => (σ + a') * t + (h σ + h a')) (t + deriv h a) a := by
    have h2 : HasDerivAt (fun a' : ℝ => a' * t) t a := by
      simpa using (hasDerivAt_id a).mul_const t
    have h3 : HasDerivAt (fun a' : ℝ => a' * t + h a') (t + deriv h a) a :=
      h2.add hdh.hasDerivAt
    have h4 : HasDerivAt (fun a' : ℝ => (a' * t + h a') + (σ * t + h σ))
        (t + deriv h a) a := h3.add_const _
    have he : (fun a' : ℝ => (a' * t + h a') + (σ * t + h σ))
        = fun a' => (σ + a') * t + (h σ + h a') := by funext a'; ring
    rw [he] at h4
    exact h4
  have hder : deriv (fun a' : ℝ => krad h σ t a') a
      = deriv (fun a' : ℝ => hquot h a' σ) a * ((σ + a) * t + (h σ + h a))
        + (t + hquot h a σ) * (t + deriv h a) := by
    have h1 : (fun a' : ℝ => krad h σ t a')
        = fun a' => (t + hquot h a' σ) * (line h σ t + line h a' t) := by
      funext a'; rw [krad_apply]
    rw [h1]
    have hl : ∀ a' : ℝ, line h σ t + line h a' t = (σ + a') * t + (h σ + h a') := by
      intro a'; unfold line; ring
    simp_rw [hl]
    have hHD : HasDerivAt (fun a' : ℝ => (t + hquot h a' σ) * ((σ + a') * t + (h σ + h a')))
        (deriv (fun a' : ℝ => hquot h a' σ) a * ((σ + a) * t + (h σ + h a))
          + (t + hquot h a σ) * (t + deriv h a)) a := by
      have h1' : HasDerivAt (fun a' : ℝ => t + hquot h a' σ)
          (deriv (fun a' : ℝ => hquot h a' σ) a) a := by
        have := hd1.hasDerivAt
        simpa only [add_comm] using this.const_add t
      exact h1'.mul hdl
    exact hHD.deriv
  have h3 : |t + deriv h a| ≤ 3 := by
    have h := abs_le.mp ht2
    rw [abs_le]; constructor <;> linarith [(abs_le.mp (hh1 a)).1, (abs_le.mp (hh1 a)).2, h.1, h.2]
  have hderb : |deriv (fun a' : ℝ => krad h σ t a') a| ≤ 20 := by
    rw [hder]
    have hb1 : |deriv (fun a' : ℝ => hquot h a' σ) a * ((σ + a) * t + (h σ + h a))|
        ≤ (1 / 100) * 5 := by
      rw [abs_mul]; exact mul_le_mul (le_trans hqd hδ1) hsum2 (abs_nonneg _) (by norm_num)
    have hb2 : |(t + hquot h a σ) * (t + deriv h a)| ≤ 3 * 3 := by
      rw [abs_mul]; exact mul_le_mul htq h3 (abs_nonneg _) (by norm_num)
    calc |deriv (fun a' : ℝ => hquot h a' σ) a * ((σ + a) * t + (h σ + h a))
          + (t + hquot h a σ) * (t + deriv h a)|
        ≤ (1 / 100) * 5 + 3 * 3 := le_trans (abs_add_le _ _) (add_le_add hb1 hb2)
      _ ≤ 20 := by norm_num
  have hder0 : deriv (fun a' : ℝ => krad 0 σ t a') a = t * t := by
    rw [hkr0]
    have h6 : (fun a' : ℝ => (σ + a') * t * t) = fun a' => a' * (t * t) + σ * (t * t) := by
      funext a'; ring
    rw [h6]
    have h7 : HasDerivAt (fun a' : ℝ => a' * (t * t) + σ * (t * t)) (t * t) a := by
      simpa using ((hasDerivAt_id a).mul_const (t * t)).add_const (σ * (t * t))
    rw [h7.deriv]
  have hderd : |deriv (fun a' : ℝ => krad h σ t a') a - deriv (fun a' : ℝ => krad 0 σ t a') a|
      ≤ 10 * δ := by
    have hkey' : deriv (fun a' : ℝ => krad h σ t a') a - deriv (fun a' : ℝ => krad 0 σ t a') a
        = deriv (fun a' : ℝ => hquot h a' σ) a * ((σ + a) * t + (h σ + h a))
          + (t * deriv h a + hquot h a σ * (t + deriv h a)) := by
      rw [hder, hder0]; ring
    rw [hkey']
    have hb1 : |deriv (fun a' : ℝ => hquot h a' σ) a * ((σ + a) * t + (h σ + h a))| ≤ δ * 5 := by
      rw [abs_mul]; exact mul_le_mul hqd hsum2 (abs_nonneg _) hδ0
    have hb2 : |t * deriv h a + hquot h a σ * (t + deriv h a)| ≤ 2 * δ + δ * 3 := by
      have h2 : |t * deriv h a| ≤ 2 * δ := by
        rw [abs_mul]; exact mul_le_mul ht2 (hh1 a) (abs_nonneg _) (by norm_num)
      have h4 : |hquot h a σ * (t + deriv h a)| ≤ δ * 3 := by
        rw [abs_mul]; exact mul_le_mul hq h3 (abs_nonneg _) hδ0
      exact le_trans (abs_add_le _ _) (add_le_add h2 h4)
    calc |deriv (fun a' : ℝ => hquot h a' σ) a * ((σ + a) * t + (h σ + h a))
          + (t * deriv h a + hquot h a σ * (t + deriv h a))|
        ≤ δ * 5 + (2 * δ + δ * 3) := le_trans (abs_add_le _ _) (add_le_add hb1 hb2)
      _ ≤ 10 * δ := by linarith
  exact ⟨hge, hle, hval, hderb, hderd⟩

end

end Work.OddVolterra.WinData
