import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.xi_close_of_small
import Submission.Work.OddVolterra.Existence.abel_deriv_bound
import Submission.Work.OddVolterra.Smooth.Q_regularity
import Submission.Work.OddVolterra.Existence.aw_xi_smooth

/-!
# `Q̃` is the derivative of the Abel transform, and the derivative is additive

`Qtilde n h s` is by definition the derivative of the Abel transform of the inhomogeneity
`Q n h`, and the goal of this file is the additivity statement

`(Qtilde n h)'(s) - (Qtilde n 0)'(s) = (abelF (Q n h - Q n 0))''(s)`

which is what makes the difference `Qtilde n h - Qtilde n 0` accessible to the second-derivative
bounds `abelF_deriv2_bound`/`E1_E2_deriv2_bounds`.

The mathematical content is that the second derivative of the Abel transform is additive on the
smooth functions considered here.  Since `deriv` is *not* additive without differentiability,
we establish the differentiability of the intervening objects:

* `abelF f = ∫_u^1 f v / √(v-u) dv` is additive in `f` near `s` (the singular integrand is
  interval integrable, so `∫ (f-g)/√ = ∫ f/√ - ∫ g/√`);
* `abelF f` is differentiable at every interior point (`abel_transform_diff`);
* `deriv (abelF f)` is `C^∞` on the window (`aw_abel_deriv_contDiffOn`), hence differentiable.

The regularity of the two inhomogeneities `(Q n h ·) i` and `(Q n 0 ·) i` comes from
`contDiffOn_Q_Ioo` (smoothness on `(0,1)`) and `Smooth.Q_regularity` (continuity up to `1`,
`C²` on compact subintervals).
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Existence

noncomputable section

/-! ## Elementary facts about the Abel transform -/

/-- The Abel transform written with the inverse-square-root `smul` kernel. -/
lemma abelF_eq_invSqrt_smul (f : ℝ → ℝ) :
    abelF f = fun u : ℝ => ∫ v in u..(1 : ℝ), (Real.sqrt (v - u))⁻¹ • f v := by
  funext u
  rw [abelF]
  refine intervalIntegral.integral_congr (fun v _ => ?_)
  simp [div_eq_mul_inv, smul_eq_mul, mul_comm]

/-- `deriv` respects eventual equality of functions. -/
lemma deriv_eventuallyEq_of_eventuallyEq {φ ψ : ℝ → ℝ} {x : ℝ} (h : φ =ᶠ[𝓝 x] ψ) :
    deriv φ =ᶠ[𝓝 x] deriv ψ := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
  filter_upwards [Metric.ball_mem_nhds x (half_pos hε)] with u hu
  have hloc : φ =ᶠ[𝓝 u] ψ := by
    filter_upwards [Metric.ball_mem_nhds u (half_pos hε)] with v hv
    exact hball (by
      rw [Metric.mem_ball] at hu hv ⊢
      calc dist v x ≤ dist v u + dist u x := dist_triangle v u x
        _ < ε / 2 + ε / 2 := add_lt_add hv hu
        _ = ε := by ring)
  exact Filter.EventuallyEq.deriv_eq hloc

/-- The derivative of the Abel transform, in the form in which the smoothness lemmas are
stated. -/
lemma deriv_abelF_eq_deriv_integral (f : ℝ → ℝ) :
    deriv (abelF f)
      = fun s : ℝ => deriv (fun u : ℝ => ∫ v in u..(1 : ℝ), f v / Real.sqrt (v - u)) s := by
  funext s
  rfl

/-! ## Additivity of `abelF` near an interior point -/

/-- `abelF` is additive on functions continuous up to `1`. -/
lemma abelF_sub_eventuallyEq {a : ℝ} {f g : ℝ → ℝ} {s : ℝ} (has : a < s) (hs1 : s < 1)
    (hfc : ContinuousOn f (Set.Icc a 1)) (hgc : ContinuousOn g (Set.Icc a 1)) :
    abelF (fun v => f v - g v) =ᶠ[𝓝 s] fun u => abelF f u - abelF g u := by
  filter_upwards [isOpen_Ioo.mem_nhds (show s ∈ Set.Ioo a 1 from ⟨has, hs1⟩)] with u hu
  have hu1 : u ≤ 1 := le_of_lt hu.2
  have hif : IntervalIntegrable (fun v : ℝ => f v / Real.sqrt (v - u)) volume u 1 := by
    have hb := Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub (a := u) (b := (1 : ℝ)) hu.2
    have hc : ContinuousOn (fun v : ℝ => f v) (Set.uIcc u 1) := by
      rw [Set.uIcc_of_le hu1]
      exact hfc.mono (fun v hv => ⟨le_trans hu.1.le hv.1, hv.2⟩)
    have h := hb.smul_continuousOn hc
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using h
  have hig : IntervalIntegrable (fun v : ℝ => g v / Real.sqrt (v - u)) volume u 1 := by
    have hb := Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub (a := u) (b := (1 : ℝ)) hu.2
    have hc : ContinuousOn (fun v : ℝ => g v) (Set.uIcc u 1) := by
      rw [Set.uIcc_of_le hu1]
      exact hgc.mono (fun v hv => ⟨le_trans hu.1.le hv.1, hv.2⟩)
    have h := hb.smul_continuousOn hc
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using h
  simp only [abelF]
  rw [← intervalIntegral.integral_sub hif hig]
  refine intervalIntegral.integral_congr (fun v _ => ?_)
  simp only [div_eq_mul_inv]
  ring

/-! ## Additivity of the second derivative of `abelF` -/

/-- **The second derivative of the Abel transform is additive.**  On functions which are
continuous up to `1` and `C²` on compact subintervals of `(a,1)`, and whose Abel transforms have
a differentiable derivative at `s`, the second derivative of `abelF` is additive at `s`. -/
lemma deriv_deriv_abelF_sub {a : ℝ} (ha1 : a < 1) {f g : ℝ → ℝ} {s : ℝ} (has : a < s)
    (hs1 : s < 1) (hfc : ContinuousOn f (Set.Icc a 1)) (hgc : ContinuousOn g (Set.Icc a 1))
    (hf2 : ∀ b : ℝ, a < b → b < 1 → ContDiffOn ℝ 2 f (Set.Icc a b))
    (hg2 : ∀ b : ℝ, a < b → b < 1 → ContDiffOn ℝ 2 g (Set.Icc a b))
    (hdf : DifferentiableAt ℝ (deriv (abelF f)) s)
    (hdg : DifferentiableAt ℝ (deriv (abelF g)) s) :
    deriv (deriv (abelF (fun v => f v - g v))) s
      = deriv (deriv (abelF f)) s - deriv (deriv (abelF g)) s := by
  have hmem : s ∈ Set.Ioo a 1 := ⟨has, hs1⟩
  -- the Abel transform is additive near `s`
  have hsub : abelF (fun v => f v - g v) =ᶠ[𝓝 s] fun u => abelF f u - abelF g u :=
    abelF_sub_eventuallyEq has hs1 hfc hgc
  -- both Abel transforms are differentiable near `s`
  have hdiff : deriv (fun u => abelF f u - abelF g u)
      =ᶠ[𝓝 s] fun u => deriv (abelF f) u - deriv (abelF g) u := by
    filter_upwards [isOpen_Ioo.mem_nhds hmem] with u hu
    have hdu : DifferentiableAt ℝ (abelF f) u := by
      rw [abelF_eq_invSqrt_smul]
      exact Work.OddVolterra.Abel.abel_transform_diff ha1 hfc hf2 u hu
    have hdv : DifferentiableAt ℝ (abelF g) u := by
      rw [abelF_eq_invSqrt_smul]
      exact Work.OddVolterra.Abel.abel_transform_diff ha1 hgc hg2 u hu
    exact deriv_fun_sub hdu hdv
  calc deriv (deriv (abelF (fun v => f v - g v))) s
      = deriv (deriv (fun u => abelF f u - abelF g u)) s :=
        Filter.EventuallyEq.deriv_eq (deriv_eventuallyEq_of_eventuallyEq hsub)
    _ = deriv (fun u => deriv (abelF f) u - deriv (abelF g) u) s :=
        Filter.EventuallyEq.deriv_eq hdiff
    _ = deriv (deriv (abelF f)) s - deriv (deriv (abelF g)) s := by
        rw [deriv_fun_sub hdf hdg]

/-! ## `Qtilde` is the derivative of the Abel transform -/

lemma Qtilde_eq_deriv_abelF (n : ℕ) (h : ℝ → ℝ) (i : Fin 2) :
    (fun s : ℝ => (Qtilde n h s) i) = deriv (abelF (fun v : ℝ => (Q n h v) i)) := by
  funext s
  fin_cases i <;> simp [Qtilde] <;> rfl

/-! ## The main statement -/

theorem deriv_Qtilde_sub_abelF (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) (i : Fin 2) {s : ℝ} (hs : 1 / 4 ≤ s) (hs1 : s < 1) :
    deriv (fun u : ℝ => (Work.OddVolterra.Qtilde n h u) i) s
      - deriv (fun u : ℝ => (Work.OddVolterra.Qtilde n 0 u) i) s =
      deriv (deriv (Work.OddVolterra.Existence.abelF
        (fun v : ℝ => (Work.OddVolterra.Q n h v) i - (Work.OddVolterra.Q n 0 v) i))) s := by
  classical
  have hsmall0 : ∀ t : ℝ, |(0 : ℝ → ℝ) t| ≤ 1 / 100 := by intro t; simp
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆ Set.Icc (1 - 2 * tau) (1 - tau) := by
    intro x hx
    rw [Function.mem_support] at hx
    exact absurd rfl hx
  have hmid : ∀ σ ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      0 < psi h Commons.Geometry.Ulam.semicircle σ t :=
    fun σ hσ t ht =>
      Work.OddVolterra.Smooth.psi_pos_of_window hsupp hsmall hσ.1 hσ.2 (abs_le.mpr ht)
  have hmid0 : ∀ σ ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      0 < psi (0 : ℝ → ℝ) Commons.Geometry.Ulam.semicircle σ t :=
    fun σ hσ t ht =>
      Work.OddVolterra.Smooth.psi_pos_of_window hsupp0 hsmall0 hσ.1 hσ.2 (abs_le.mpr ht)
  have hreg := Work.OddVolterra.Smooth.Q_regularity n hn hh (a := (1 : ℝ) / 8) (by norm_num)
    hsupp hsmall hmid
  have hreg0 := Work.OddVolterra.Smooth.Q_regularity n hn contDiff_const (a := (1 : ℝ) / 8)
    (by norm_num) hsupp0 hsmall0 hmid0
  have hcont : ContinuousOn (fun v : ℝ => (Q n h v) i) (Set.Icc ((1 : ℝ) / 8) 1) :=
    (continuousOn_pi.mp hreg.1) i
  have hcont0 : ContinuousOn (fun v : ℝ => (Q n 0 v) i) (Set.Icc ((1 : ℝ) / 8) 1) :=
    (continuousOn_pi.mp hreg0.1) i
  have hcd : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℝ => (Q n h v) i) (Set.Ioo (0 : ℝ) 1) :=
    (contDiffOn_pi.mp (Work.OddBridge.contDiffOn_Q_Ioo n hn hh hmid)) i
  have hcd0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℝ => (Q n 0 v) i) (Set.Ioo (0 : ℝ) 1) :=
    (contDiffOn_pi.mp (Work.OddBridge.contDiffOn_Q_Ioo n hn contDiff_const hmid0)) i
  have hmem8 : s ∈ Set.Ioo ((1 : ℝ) / 8) 1 := ⟨by linarith, hs1⟩
  have hderiv : DifferentiableAt ℝ (deriv (abelF (fun v : ℝ => (Q n h v) i))) s := by
    have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (abelF (fun v : ℝ => (Q n h v) i)))
        (Set.Ioo ((1 : ℝ) / 8) 1) := by
      rw [deriv_abelF_eq_deriv_integral]
      exact aw_abel_deriv_contDiffOn (Q := fun v : ℝ => (Q n h v) i) (a := (1 : ℝ) / 8)
        (by norm_num) (by norm_num) hcd hcont
    exact (hsm.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hmem8)
  have hderiv0 : DifferentiableAt ℝ (deriv (abelF (fun v : ℝ => (Q n 0 v) i))) s := by
    have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (abelF (fun v : ℝ => (Q n 0 v) i)))
        (Set.Ioo ((1 : ℝ) / 8) 1) := by
      rw [deriv_abelF_eq_deriv_integral]
      exact aw_abel_deriv_contDiffOn (Q := fun v : ℝ => (Q n 0 v) i) (a := (1 : ℝ) / 8)
        (by norm_num) (by norm_num) hcd0 hcont0
    exact (hsm.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hmem8)
  have hkey : deriv (deriv (abelF (fun v : ℝ => (Q n h v) i - (Q n 0 v) i))) s
      = deriv (deriv (abelF (fun v : ℝ => (Q n h v) i))) s
        - deriv (deriv (abelF (fun v : ℝ => (Q n 0 v) i))) s :=
    deriv_deriv_abelF_sub (a := (1 : ℝ) / 8) (by norm_num)
      (f := fun v : ℝ => (Q n h v) i) (g := fun v : ℝ => (Q n 0 v) i) (by linarith) hs1
      hcont hcont0
      (fun b hab hb1 => (contDiffOn_pi.mp (hreg.2 b hab hb1)) i)
      (fun b hab hb1 => (contDiffOn_pi.mp (hreg0.2 b hab hb1)) i)
      hderiv hderiv0
  rw [Qtilde_eq_deriv_abelF n h i, Qtilde_eq_deriv_abelF n 0 i]
  exact hkey.symm

end

end Work.OddVolterra.Existence
