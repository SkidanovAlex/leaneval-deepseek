import Mathlib
import Submission.Work.OddVolterra.WinData.Kden
import Submission.Work.OddVolterra.WinData.Jets
import Submission.Work.OddVolterra.Defs

/-!
# `Kden_jets_ext`: bounds for the Abel denominator on the extended slope box

`Kden h a σ t = √(krad h σ t a)`, and `WinData/Jets.lean` proves all the radicand bounds on the
box `a ≤ 1`.  The consumer (`WinData/thetaM_close_box.lean`) differentiates the Abel average
`u ↦ ∫₀¹ KvecM n h (u + τ(σ-u)) σ · dτ` at a point `s ≤ 1` over a two-sided neighbourhood, so the
moving first slot reaches `3/2`; the estimates are therefore needed up to `a = 3/2`.

Nothing in the proof of `krad_jets` is specific to `a ≤ 1` except the bound
`σ + a ≤ 2` used for the *upper* bounds; the lower bound `kradLo A ≤ krad h σ t a` is
`a`-independent.  We redo the (mechanical) estimate with `σ + a ≤ 5/2`, which only changes the
numerical constants, and then transfer the resulting radicand data to `Kden = √krad` with the
generous constant `kdenC A = 10⁸ (kdenK A)⁶` of `WinData/Kden.lean`.
-/

namespace Work.OddVolterra.WinData

open Work.OddVolterra
open scoped Topology ContDiff Interval

noncomputable section

set_option maxHeartbeats 1000000 in
/-- **The Abel radicand on the extended box.**  Same as `krad_jets` but with the first slot
allowed to run up to `3/2`; the numerical constants are enlarged accordingly. -/
theorem krad_jets_ext {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ)
    {A a σ t : ℝ} (hA : 0 < A) (ha : A ≤ a) (hσ : A ≤ σ) (hσ1 : σ ≤ 1) (ha1 : a ≤ 3 / 2)
    (ht : 1 / 5 ≤ |t|) (ht2 : |t| ≤ 2) :
    kradLo A ≤ krad h σ t a ∧ krad h σ t a ≤ 20 ∧
    |krad h σ t a - krad 0 σ t a| ≤ 20 * δ ∧
    |deriv (fun a' : ℝ => krad h σ t a') a| ≤ 20 ∧
    |deriv (fun a' : ℝ => krad 0 σ t a') a| ≤ 20 ∧
    |deriv (fun a' : ℝ => krad h σ t a') a - deriv (fun a' : ℝ => krad 0 σ t a') a| ≤ 20 * δ := by
  have hδ0' : (0 : ℝ) ≤ δ := le_of_lt hδ0
  have hh0 : ∀ x : ℝ, |h x| ≤ δ := fun x => by simpa using hjet 0 (by norm_num) x
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ δ := fun x => by simpa using hjet 1 (by norm_num) x
  have hh2 : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ δ := fun x => hjet 2 (by norm_num) x
  have hq : |hquot h a σ| ≤ δ := (hquot_bounds hh hδ0' hh1 hh2 a σ).1
  have hqd : |deriv (fun a' : ℝ => hquot h a' σ) a| ≤ δ :=
    (hquot_bounds hh hδ0' hh1 hh2 a σ).2
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
  have hSab : σ + a ≤ 5 / 2 := by linarith
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
  have hsum2 : |(σ + a) * t + (h σ + h a)| ≤ 251 / 50 := by
    have h1 : |(σ + a) * t| ≤ 5 := by
      rw [abs_mul, abs_of_pos hS]
      have h2 : (σ + a) * |t| ≤ 5 / 2 * 2 :=
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
    have h6 : |(t + hquot h a σ) * ((σ + a) * t + (h σ + h a))| ≤ 3 * (251 / 50) := by
      rw [abs_mul]
      exact mul_le_mul htq hsum2 (abs_nonneg _) (by norm_num)
    linarith [le_abs_self ((t + hquot h a σ) * ((σ + a) * t + (h σ + h a))), h6]
  -- ## the unperturbed radicand
  have hkr0 : (fun a' : ℝ => krad 0 σ t a') = fun a' => (σ + a') * t * t := by
    funext a'; rw [krad_apply]; simp [line, hquot]; ring
  -- ## the difference of the values
  have hval : |krad h σ t a - krad 0 σ t a| ≤ 20 * δ := by
    have hkr0' : krad 0 σ t a = (σ + a) * t * t := congrFun hkr0 a
    rw [hkr, hkr0']
    have hsplit : (t + hquot h a σ) * ((σ + a) * t + (h σ + h a)) - (σ + a) * t * t
        = t * (h σ + h a) + hquot h a σ * ((σ + a) * t + (h σ + h a)) := by ring
    rw [hsplit]
    have hb1 : |t * (h σ + h a)| ≤ 2 * (2 * δ) := by
      rw [abs_mul]
      exact mul_le_mul ht2 hc (abs_nonneg _) (by norm_num)
    have hb2 : |hquot h a σ * ((σ + a) * t + (h σ + h a))| ≤ δ * (251 / 50) := by
      rw [abs_mul]
      exact mul_le_mul hq hsum2 (abs_nonneg _) hδ0'
    calc |t * (h σ + h a) + hquot h a σ * ((σ + a) * t + (h σ + h a))|
        ≤ 2 * (2 * δ) + δ * (251 / 50) := le_trans (abs_add_le _ _) (add_le_add hb1 hb2)
      _ ≤ 20 * δ := by linarith [hδ0']
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
  have h3 : |t + deriv h a| ≤ 201 / 100 := by
    have h := abs_le.mp ht2
    rw [abs_le]; constructor <;> linarith [(abs_le.mp (hh1 a)).1, (abs_le.mp (hh1 a)).2, h.1, h.2]
  have hderb : |deriv (fun a' : ℝ => krad h σ t a') a| ≤ 20 := by
    rw [hder]
    have hb1 : |deriv (fun a' : ℝ => hquot h a' σ) a * ((σ + a) * t + (h σ + h a))|
        ≤ (1 / 100) * (251 / 50) := by
      rw [abs_mul]; exact mul_le_mul (le_trans hqd hδ1) hsum2 (abs_nonneg _) (by norm_num)
    have hb2 : |(t + hquot h a σ) * (t + deriv h a)| ≤ 3 * (201 / 100) := by
      rw [abs_mul]; exact mul_le_mul htq h3 (abs_nonneg _) (by norm_num)
    calc |deriv (fun a' : ℝ => hquot h a' σ) a * ((σ + a) * t + (h σ + h a))
          + (t + hquot h a σ) * (t + deriv h a)|
        ≤ (1 / 100) * (251 / 50) + 3 * (201 / 100) := le_trans (abs_add_le _ _) (add_le_add hb1 hb2)
      _ ≤ 20 := by norm_num
  have hder0 : deriv (fun a' : ℝ => krad 0 σ t a') a = t * t := by
    rw [hkr0]
    have h6 : (fun a' : ℝ => (σ + a') * t * t) = fun a' => a' * (t * t) + σ * (t * t) := by
      funext a'; ring
    rw [h6]
    have h7 : HasDerivAt (fun a' : ℝ => a' * (t * t) + σ * (t * t)) (t * t) a := by
      simpa using ((hasDerivAt_id a).mul_const (t * t)).add_const (σ * (t * t))
    rw [h7.deriv]
  have hderb0 : |deriv (fun a' : ℝ => krad 0 σ t a') a| ≤ 20 := by
    rw [hder0, abs_mul]
    nlinarith [abs_le.mp ht2, abs_nonneg t]
  have hderd : |deriv (fun a' : ℝ => krad h σ t a') a - deriv (fun a' : ℝ => krad 0 σ t a') a|
      ≤ 20 * δ := by
    have hkey' : deriv (fun a' : ℝ => krad h σ t a') a - deriv (fun a' : ℝ => krad 0 σ t a') a
        = deriv (fun a' : ℝ => hquot h a' σ) a * ((σ + a) * t + (h σ + h a))
          + (t * deriv h a + hquot h a σ * (t + deriv h a)) := by
      rw [hder, hder0]; ring
    rw [hkey']
    have hb1 : |deriv (fun a' : ℝ => hquot h a' σ) a * ((σ + a) * t + (h σ + h a))|
        ≤ δ * (251 / 50) := by
      rw [abs_mul]; exact mul_le_mul hqd hsum2 (abs_nonneg _) hδ0'
    have hb2 : |t * deriv h a + hquot h a σ * (t + deriv h a)| ≤ 2 * δ + δ * (201 / 100) := by
      have h2 : |t * deriv h a| ≤ 2 * δ := by
        rw [abs_mul]; exact mul_le_mul ht2 (hh1 a) (abs_nonneg _) (by norm_num)
      have h4 : |hquot h a σ * (t + deriv h a)| ≤ δ * (201 / 100) := by
        rw [abs_mul]; exact mul_le_mul hq h3 (abs_nonneg _) hδ0'
      exact le_trans (abs_add_le _ _) (add_le_add h2 h4)
    calc |deriv (fun a' : ℝ => hquot h a' σ) a * ((σ + a) * t + (h σ + h a))
          + (t * deriv h a + hquot h a σ * (t + deriv h a))|
        ≤ δ * (251 / 50) + (2 * δ + δ * (201 / 100)) :=
          le_trans (abs_add_le _ _) (add_le_add hb1 hb2)
      _ ≤ 20 * δ := by linarith [hδ0']
  exact ⟨hge, hle, hval, hderb, hderb0, hderd⟩

/-! ## From the radicand to `Kden = √krad` -/

/-- Above `κ > 0` the square root is `1/(2κ)`-Lipschitz. -/
lemma abs_sqrt_sub_sqrt_le {x y κ C δ : ℝ} (hκ : 0 < κ) (hx : κ ^ 2 ≤ x) (hy : κ ^ 2 ≤ y)
    (hxy : |x - y| ≤ C * δ) :
    |Real.sqrt x - Real.sqrt y| ≤ C * δ / (2 * κ) := by
  have hx0 : 0 < x := lt_of_lt_of_le (pow_pos hκ 2) hx
  have hy0 : 0 < y := lt_of_lt_of_le (pow_pos hκ 2) hy
  have hden : 2 * κ ≤ Real.sqrt x + Real.sqrt y := by
    have h1 : κ ≤ Real.sqrt x := by
      have h := Real.sqrt_le_sqrt hx
      rwa [Real.sqrt_sq_eq_abs, abs_of_pos hκ] at h
    have h2 : κ ≤ Real.sqrt y := by
      have h := Real.sqrt_le_sqrt hy
      rwa [Real.sqrt_sq_eq_abs, abs_of_pos hκ] at h
    linarith
  have hkey : |Real.sqrt x - Real.sqrt y| = |x - y| / (Real.sqrt x + Real.sqrt y) := by
    rw [eq_div_iff (by positivity)]
    rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt x + Real.sqrt y), ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt hx0.le, Real.sq_sqrt hy0.le]
  rw [hkey]
  exact div_le_div₀ (le_trans (abs_nonneg _) hxy) hxy (by positivity) hden

/-- The `a`-derivative of `Kden` is `∂_a krad / (2 Kden)`. -/
lemma deriv_Kden_ext {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a σ t : ℝ}
    (hpos : krad h σ t a ≠ 0) :
    deriv (fun a' : ℝ => Kden h a' σ t) a
      = deriv (fun a' : ℝ => krad h σ t a') a / (2 * Kden h a σ t) := by
  have hd : HasDerivAt (fun a' : ℝ => krad h σ t a') (deriv (fun a' : ℝ => krad h σ t a') a) a :=
    ((contDiff_krad hh σ t).differentiable (by simp)).differentiableAt.hasDerivAt
  have hs := hd.sqrt hpos
  have h1 : (fun a' : ℝ => Real.sqrt (krad h σ t a')) = fun a' : ℝ => Kden h a' σ t := by
    funext x; rw [Kden_eq_sqrt_krad]
  rw [h1] at hs
  rw [hs.deriv, Kden_eq_sqrt_krad]

/-- Telescoping identity for the difference of two quotients with halved denominators. -/
lemma div_sub_div_half (a b f g : ℝ) (hf : f ≠ 0) (hg : g ≠ 0) :
    b / (2 * g) - a / (2 * f) = (b - a) / (2 * g) + a * (f - g) / (2 * g * f) := by
  field_simp
  ring

/-- The derivative-difference estimate for two quotients `D/(2g)` with `g ≥ κ` and the three
bounds on `D1 - D0`, `D0` and `g0 - g1`. -/
lemma div_gap_le {D1 D0 g1 g0 κ K δ : ℝ} (hκ : 0 < κ) (hδ : 0 ≤ δ)
    (hDd : |D1 - D0| ≤ 20 * δ) (hD0 : |D0| ≤ 20)
    (hgg : |g0 - g1| ≤ 10 * K * δ) (hg1 : κ ≤ g1) (hg0 : κ ≤ g0) :
    |D1 / (2 * g1) - D0 / (2 * g0)|
      ≤ 20 * δ / (2 * κ) + 20 * (10 * K * δ) / (2 * κ ^ 2) := by
  have hg1pos : 0 < g1 := lt_of_lt_of_le hκ hg1
  have hg0pos : 0 < g0 := lt_of_lt_of_le hκ hg0
  rw [div_sub_div_half D0 D1 g0 g1 (ne_of_gt hg0pos) (ne_of_gt hg1pos)]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 * g1 by linarith)]
    exact div_le_div₀ (by positivity) hDd (by linarith) (by linarith)
  · rw [abs_div, abs_mul, abs_of_pos (show (0 : ℝ) < 2 * g1 * g0 by positivity)]
    have hnum : |D0| * |g0 - g1| ≤ 20 * (10 * K * δ) :=
      mul_le_mul hD0 hgg (abs_nonneg _) (by norm_num)
    have hden : 2 * κ ^ 2 ≤ 2 * g1 * g0 := by nlinarith [hg1, hg0, hκ]
    exact div_le_div₀ (le_trans (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hnum) hnum
      (by positivity) hden

/-- `20 / (2κ) = 10 (1/κ)`. -/
lemma twenty_div_two_kap (A : ℝ) (hA : 0 < A) : 20 / (2 * kdenKap A) = 10 * kdenK A := by
  have h0 : kdenKap A ≠ 0 := ne_of_gt (kdenKap_pos hA)
  rw [kdenK]
  field_simp
  ring

/-- `20 δ / (2 κ) = 10 (1/κ) δ`. -/
lemma kap_div_eq (A δ : ℝ) (hA : 0 < A) :
    20 * δ / (2 * kdenKap A) = 10 * kdenK A * δ := by
  have h0 : kdenKap A ≠ 0 := ne_of_gt (kdenKap_pos hA)
  rw [kdenK]
  field_simp
  ring

/-- `20 (10 (1/κ) δ) / (2 κ²) = 100 (1/κ)³ δ`. -/
lemma kap_sq_div_eq (A δ : ℝ) (hA : 0 < A) :
    20 * (10 * kdenK A * δ) / (2 * (kdenKap A) ^ 2) = 100 * (kdenK A) ^ 3 * δ := by
  have h0 : kdenKap A ≠ 0 := ne_of_gt (kdenKap_pos hA)
  rw [kdenK]
  field_simp
  ring

end

theorem Kden_jets_ext {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ)
    {A a σ t : ℝ} (hA : 0 < A) (ha : A ≤ a) (hσ : A ≤ σ) (hσ1 : σ ≤ 1) (ha1 : a ≤ 3 / 2)
    (ht : 1 / 5 ≤ |t|) (ht2 : |t| ≤ 2) :
    Work.OddVolterra.WinData.kdenKap A ≤ Work.OddVolterra.Kden h a σ t ∧
    Work.OddVolterra.WinData.kdenKap A ≤ Work.OddVolterra.Kden 0 a σ t ∧
    |Work.OddVolterra.Kden h a σ t - Work.OddVolterra.Kden 0 a σ t| ≤ Work.OddVolterra.WinData.kdenC A * δ ∧
    |deriv (fun a' : ℝ => Work.OddVolterra.Kden h a' σ t) a| ≤ Work.OddVolterra.WinData.kdenC A ∧
    |deriv (fun a' : ℝ => Work.OddVolterra.Kden 0 a' σ t) a| ≤ Work.OddVolterra.WinData.kdenC A ∧
    |deriv (fun a' : ℝ => Work.OddVolterra.Kden h a' σ t) a -
     deriv (fun a' : ℝ => Work.OddVolterra.Kden 0 a' σ t) a| ≤ Work.OddVolterra.WinData.kdenC A * δ := by
  obtain ⟨hkrad_ge, hkrad_le, hkrad_val, hkrad_der, hkrad_der0, hkrad_derd⟩ :=
    krad_jets_ext hh hsupp hδ0 hδ1 hjet hA ha hσ hσ1 ha1 ht ht2
  have hδ0' : (0 : ℝ) ≤ δ := le_of_lt hδ0
  have hκpos : 0 < kdenKap A := kdenKap_pos hA
  have hK1 : 1 ≤ kdenK A := one_le_kdenK hA
  have hsqrt_h : Kden h a σ t = Real.sqrt (krad h σ t a) := Kden_eq_sqrt_krad h a σ t
  have hsqrt_0 : Kden 0 a σ t = Real.sqrt (krad 0 σ t a) := Kden_eq_sqrt_krad 0 a σ t
  -- the unperturbed radicand: `krad 0 σ t a = (σ + a) t²`
  have hkrad0_apply : krad 0 σ t a = (σ + a) * t ^ 2 := by
    rw [krad_apply]; simp [line, hquot]; ring
  have htsq : (1 / 25 : ℝ) ≤ t ^ 2 := by
    have h1 : (1 / 5 : ℝ) * (1 / 5) ≤ |t| * |t| := mul_self_le_mul_self (by norm_num) ht
    rw [abs_mul_abs_self t] at h1
    nlinarith [h1]
  have h2A : 2 * A ≤ σ + a := by linarith
  have hkrad0_lo : kradLo A ≤ krad 0 σ t a := by
    rw [hkrad0_apply]
    have h1 : kradLo A ≤ (19 / 100) * (2 * A / 5) := by
      rw [kradLo]; exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
    have h2 : (19 / 100) * (2 * A / 5) = 19 * A / 250 := by ring
    have h3 : 19 * A / 250 ≤ 2 * A / 25 := by linarith [hA]
    have h4 : 2 * A / 25 ≤ (σ + a) * t ^ 2 := by nlinarith [h2A, htsq, hA]
    linarith
  have hkradh_pos : 0 < krad h σ t a := lt_of_lt_of_le (kradLo_pos hA) hkrad_ge
  have hkrad0_pos : 0 < krad 0 σ t a := lt_of_lt_of_le (kradLo_pos hA) hkrad0_lo
  have hkap_sq_ge : (kdenKap A) ^ 2 ≤ krad h σ t a := by
    rw [kdenKap, Real.sq_sqrt (kradLo_pos hA).le]
    exact hkrad_ge
  have hkap_sq_ge0 : (kdenKap A) ^ 2 ≤ krad 0 σ t a := by
    rw [kdenKap, Real.sq_sqrt (kradLo_pos hA).le]
    exact hkrad0_lo
  -- the two lower bounds for `Kden`
  have hKdenh_ge : kdenKap A ≤ Kden h a σ t := by
    rw [hsqrt_h, kdenKap]; exact Real.sqrt_le_sqrt hkrad_ge
  have hKden0_ge : kdenKap A ≤ Kden 0 a σ t := by
    rw [hsqrt_0, kdenKap]; exact Real.sqrt_le_sqrt hkrad0_lo
  have hKdenh_pos : 0 < Kden h a σ t := lt_of_lt_of_le hκpos hKdenh_ge
  have hKden0_pos : 0 < Kden 0 a σ t := lt_of_lt_of_le hκpos hKden0_ge
  -- ## the constants
  have hC10 : 10 * kdenK A ≤ kdenC A := by
    simpa using kdenC_ge_pow hA (c := 10) (by norm_num) (by norm_num) (m := 1)
      (by norm_num) (by norm_num)
  have hC200 : 200 * (kdenK A) ^ 3 ≤ kdenC A := by
    simpa using kdenC_ge_pow hA (c := 200) (by norm_num) (by norm_num) (m := 3)
      (by norm_num) (by norm_num)
  -- ## the value difference
  have hval : |Kden h a σ t - Kden 0 a σ t| ≤ kdenC A * δ := by
    have h1 : |Kden h a σ t - Kden 0 a σ t| ≤ 20 * δ / (2 * kdenKap A) := by
      rw [hsqrt_h, hsqrt_0]
      exact abs_sqrt_sub_sqrt_le hκpos hkap_sq_ge hkap_sq_ge0 hkrad_val
    calc |Kden h a σ t - Kden 0 a σ t| ≤ 20 * δ / (2 * kdenKap A) := h1
      _ = 10 * kdenK A * δ := kap_div_eq A δ hA
      _ ≤ kdenC A * δ := mul_le_mul_of_nonneg_right hC10 hδ0'
  -- ## the derivatives
  have hderh : deriv (fun a' : ℝ => Kden h a' σ t) a
      = deriv (fun a' : ℝ => krad h σ t a') a / (2 * Kden h a σ t) :=
    deriv_Kden_ext hh (ne_of_gt hkradh_pos)
  have hder0 : deriv (fun a' : ℝ => Kden 0 a' σ t) a
      = deriv (fun a' : ℝ => krad 0 σ t a') a / (2 * Kden 0 a σ t) :=
    deriv_Kden_ext contDiff_const (ne_of_gt hkrad0_pos)
  have hderh_bd : |deriv (fun a' : ℝ => Kden h a' σ t) a| ≤ kdenC A := by
    rw [hderh, abs_div, abs_of_pos (show (0 : ℝ) < 2 * Kden h a σ t by linarith)]
    calc |deriv (fun a' : ℝ => krad h σ t a') a| / (2 * Kden h a σ t)
        ≤ 20 / (2 * kdenKap A) := div_le_div₀ (by norm_num) hkrad_der (by linarith)
          (by linarith [hKdenh_ge])
      _ = 10 * kdenK A := twenty_div_two_kap A hA
      _ ≤ kdenC A := hC10
  have hder0_bd : |deriv (fun a' : ℝ => Kden 0 a' σ t) a| ≤ kdenC A := by
    rw [hder0, abs_div, abs_of_pos (show (0 : ℝ) < 2 * Kden 0 a σ t by linarith)]
    calc |deriv (fun a' : ℝ => krad 0 σ t a') a| / (2 * Kden 0 a σ t)
        ≤ 20 / (2 * kdenKap A) := div_le_div₀ (by norm_num) hkrad_der0 (by linarith)
          (by linarith [hKden0_ge])
      _ = 10 * kdenK A := twenty_div_two_kap A hA
      _ ≤ kdenC A := hC10
  -- ## the derivative difference
  have hderd : |deriv (fun a' : ℝ => Kden h a' σ t) a - deriv (fun a' : ℝ => Kden 0 a' σ t) a|
      ≤ kdenC A * δ := by
    have hgg : |Kden 0 a σ t - Kden h a σ t| ≤ 10 * kdenK A * δ := by
      rw [abs_sub_comm]
      calc |Kden h a σ t - Kden 0 a σ t| ≤ 20 * δ / (2 * kdenKap A) := by
            rw [hsqrt_h, hsqrt_0]
            exact abs_sqrt_sub_sqrt_le hκpos hkap_sq_ge hkap_sq_ge0 hkrad_val
        _ = 10 * kdenK A * δ := kap_div_eq A δ hA
    have hmain := div_gap_le (D1 := deriv (fun a' : ℝ => krad h σ t a') a)
      (D0 := deriv (fun a' : ℝ => krad 0 σ t a') a) (g1 := Kden h a σ t)
      (g0 := Kden 0 a σ t) (κ := kdenKap A) (K := kdenK A) (δ := δ)
      hκpos hδ0' hkrad_derd hkrad_der0 hgg hKdenh_ge hKden0_ge
    rw [hderh, hder0]
    refine le_trans hmain ?_
    rw [kap_div_eq A δ hA, kap_sq_div_eq A δ hA]
    have hstep : 10 * kdenK A * δ + 100 * (kdenK A) ^ 3 * δ
        = ((10 * kdenK A + 100 * (kdenK A) ^ 3)) * δ := by ring
    rw [hstep]
    refine mul_le_mul_of_nonneg_right ?_ hδ0'
    have h1 : (kdenK A) ^ 1 ≤ (kdenK A) ^ 3 := pow_le_pow_right₀ hK1 (by norm_num)
    rw [pow_one] at h1
    have h2 : (0 : ℝ) ≤ (kdenK A) ^ 3 := by positivity
    linarith
  exact ⟨hKdenh_ge, hKden0_ge, hval, hderh_bd, hder0_bd, hderd⟩

end Work.OddVolterra.WinData
