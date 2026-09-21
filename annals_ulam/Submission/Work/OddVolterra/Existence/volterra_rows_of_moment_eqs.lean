import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddEnvelope.Defs
import Submission.Work.OddEnvelope.Main
import Submission.Work.OddVolterra.Existence.abel_inversion_b1
import Submission.Work.OddVolterra.Existence.setup_of_envelope
import Submission.Work.OddVolterra.Existence.theta_integrable
import Submission.Work.OddVolterra.RowIdentity.odd_rowF
import Submission.Work.OddVolterra.RowIdentity.odd_rowH
import Submission.Work.OddVolterra.Smooth.Qy_pos_of_isEnvelopeCurve
import Submission.Work.OddBridge.KvecM_eq_Kvec
import Submission.Work.OddBridge.KvecM_contDiffOn_box
import Submission.Work.OddBridge.dvi_reduce
import Submission.Work.OddBridge.dvi_of_volterra_regular
import Submission.Work.OddBridge.abel_integral_Kvec_eq_KvecM

/-!
# The two differentiated rows of the odd-case Volterra system, from the moment equations

`Work.OddVolterra.Existence.volterra_rows_of_moment_eqs`: rows `2` and `3` of the paper's
system `(hah44)` (Ryabogin, *A negative answer to Ulam's Problem 19 from the Scottish Book*,
Ann. of Math. **195** (2022), odd case `d = 2n+1`),

`𝐆(s, Z(s)) = ∫_s^1 𝚯(s,σ,Z(σ)) dσ + 𝚵(s)`,

follow from the two moment equations `(A)`, `(B)` (as `momentF = C/√(1+s²)`, `momentH = 0` on
`(0,1]`), the envelope hypothesis `IsEnvelopeCurve` and the `1/100`-closeness of the curve to
the semicircle chord function `profileX`.

The route is the inverse of the paper's Step 2:

* the two **row identities** `odd_rowF`, `odd_rowH` differentiate `momentF` `n+1` times and
  `momentH` `n` times and rewrite the result as the **Abel system** of the kernels `Kvec`
  (`abel_Kvec_of_moment_eqs`);
* the manifest, globally smooth representative `KvecM` agrees with `Kvec` on the triangle
  `s ≤ σ` (`KvecM_eq_Kvec`, with the positivity of the endpoint factors from
  `Qy_pos_of_isEnvelopeCurve`), so the Abel equation holds with `KvecM` too
  (`abel_KvecM_of_moment_eqs`);
* **Abel inversion** (`dvi_of_abel`, the `b = 1` differentiated form of the Abel/Volterra
  equivalence, applied to the smooth manifest kernel on a box whose positivity is
  `Kden_pos_box` and whose smoothness is `KvecM_contDiffOn_box`) turns the Abel equation into
  the differentiated form `(dvi)`, i.e. rows `2`, `3` of `(hah44)` (`dvi_component`).

The analytic inputs are proved in this workspace: the `Setup` package of the two row identities
(`setup_of_envelope`), the positivity of the Abel denominator on a box (`Kden_pos_box`) and the
interval-integrability of the `𝚯`-integrand (`theta_integrable`).
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Existence

noncomputable section

/-- **The Abel equation `(arik)` with the paper's kernel `Kvec`, from the two moment equations.** -/
theorem abel_Kvec_of_moment_eqs (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hmeF : ∀ s : ℝ, 0 < s → s ≤ 1 →
      Work.OddVolterra.momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
        Commons.Geometry.Ulam.oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2))
    (hmeH : ∀ s : ℝ, 0 < s → s ≤ 1 →
      Work.OddVolterra.momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100 ∧
      |y s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (∫ σ in s..1,
        (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
          Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 0 ∧
    (∫ σ in s..1,
        (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
          Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 1 := by
  obtain ⟨S, hSn, hSa, hSc, hSh, hSx, hSy, hSf⟩ :=
    setup_of_envelope n hn hh H hclose hs hs1
  have hmem : s ∈ Set.Icc S.a S.c := by rw [hSa, hSc]; exact ⟨le_rfl, le_rfl⟩
  have hrowF := Work.OddVolterra.RowIdentity.odd_rowF n hn S.ha S.hac S.hc1 S.hh S.hx S.hy S.hf
    S.hxy S.hxdec S.hydec S.hxb S.hyb S.hfb S.hxle S.hyle S.hord S.hint S.hKden S.hmid hmem
  have hrowH := Work.OddVolterra.RowIdentity.odd_rowH n hn S.ha S.hac S.hc1 S.hh S.hx S.hy S.hf
    S.hxy S.hxdec S.hydec S.hxb S.hyb S.hfb S.hxle S.hyle S.hord S.hint S.hKden S.hmid hmem
  simp only [hSh, hSx, hSy, hSf] at hrowF hrowH
  have hF : iteratedDeriv (n + 1)
      (fun u : ℝ => Work.OddVolterra.momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u) s
      = iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) s := by
    have hev : (fun u : ℝ => Work.OddVolterra.momentF n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u) =ᶠ[𝓝 s]
        (fun u : ℝ => Work.OddVolterra.momentRHS n u) := by
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (show s ∈ Set.Ioo (0:ℝ) 1 from ⟨hs, hs1⟩))
        (fun u hu => ?_)
      simpa [Work.OddVolterra.momentRHS] using hmeF u hu.1 (le_of_lt hu.2)
    exact hev.iteratedDeriv_eq (n + 1)
  have hH : iteratedDeriv n
      (fun u : ℝ => Work.OddVolterra.momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) u) s
      = 0 := by
    have hev : (fun u : ℝ => Work.OddVolterra.momentH n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u) =ᶠ[𝓝 s] (fun _ : ℝ => 0) := by
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (show s ∈ Set.Ioo (0:ℝ) 1 from ⟨hs, hs1⟩))
        (fun u hu => ?_)
      exact hmeH u hu.1 (le_of_lt hu.2)
    rw [hev.iteratedDeriv_eq n]
    simp
  constructor
  · rw [hF] at hrowF
    have hQ : (Work.OddVolterra.Q n h s) 0
        = - Work.OddVolterra.E1 n h s + iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) s := by
      simp [Work.OddVolterra.Q]
    rw [hQ]
    linarith [hrowF]
  · rw [hH] at hrowH
    have hQ : (Work.OddVolterra.Q n h s) 1 = - Work.OddVolterra.E2 n h s := by
      simp [Work.OddVolterra.Q]
    rw [hQ]
    linarith [hrowH]

/-- **The same Abel equation with the manifest kernel `KvecM`.** -/
theorem abel_KvecM_of_moment_eqs (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hmeF : ∀ s : ℝ, 0 < s → s ≤ 1 →
      Work.OddVolterra.momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
        Commons.Geometry.Ulam.oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2))
    (hmeH : ∀ s : ℝ, 0 < s → s ≤ 1 →
      Work.OddVolterra.momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100 ∧
      |y s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ s ∈ Set.Ioo a 1,
      (∫ σ in s..1,
          (Work.OddBridge.KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
            Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 0 ∧
      (∫ σ in s..1,
          (Work.OddBridge.KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
            Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 1 := by
  intro s hs
  have hs0 : 0 < s := lt_trans ha hs.1
  obtain ⟨h0, h1⟩ := abel_Kvec_of_moment_eqs n hn hh H hmeF hmeH hclose hs0 hs.2
  have hae : ∀ u σ : ℝ, a ≤ u → u < σ → σ ≤ 1 →
      Work.OddBridge.KvecM n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Work.OddVolterra.Kvec n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ) := by
    intro u σ hu huσ hσ1
    have hu0 : 0 < u := lt_of_lt_of_le ha hu
    obtain ⟨hQy, hQx⟩ :=
      Work.OddVolterra.Smooth.Qy_pos_of_isEnvelopeCurve H u σ hu0 (le_of_lt huσ) hσ1
    exact Work.OddBridge.KvecM_eq_Kvec n hn hh (le_of_lt huσ) (x σ) (y σ)
      (deriv x σ) (deriv y σ) hQy hQx
  obtain ⟨e0, e1⟩ :=
    Work.OddBridge.abel_integral_Kvec_eq_KvecM n ha hae (le_trans (le_of_lt hs.1) le_rfl) (le_of_lt hs.2)
  exact ⟨by rw [← e0]; exact h0, by rw [← e1]; exact h1⟩

theorem dvi_component (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    {a s : ℝ} (ha : 0 < a) (has : a < s) (hs1 : s < 1)
    (hposy : ∀ u σ : ℝ, u ∈ Set.Icc a 1 → σ ∈ Set.Icc a 1 →
      0 < Work.OddVolterra.Kden h u σ (y σ))
    (hposx : ∀ u σ : ℝ, u ∈ Set.Icc a 1 → σ ∈ Set.Icc a 1 →
      0 < Work.OddVolterra.Kden h u σ (-(x σ)))
    (i : Fin 2)
    (habel : ∀ σ ∈ Set.Ioo a 1,
      (∫ v in σ..1,
        (Real.sqrt (v - σ))⁻¹ *
          (Work.OddBridge.KvecM n h σ v (x v) (y v) (deriv x v) (deriv y v)) i)
        = (Work.OddVolterra.Q n h σ) i) :
    - ((Work.OddVolterra.G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) i)
      + (∫ σ in s..1,
          deriv (fun u : ℝ =>
            (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s)
      = deriv (fun u : ℝ =>
          ∫ v in u..1, (Real.sqrt (v - u))⁻¹ * (Work.OddVolterra.Q n h v) i) s := by
  have ha1 : a < 1 := lt_trans has hs1
  have hae : ∀ u σ : ℝ, a ≤ u → u ≤ σ → σ ≤ 1 →
      Work.OddBridge.KvecM n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Work.OddVolterra.Kvec n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ) := by
    intro u σ hu huσ hσ1
    have hu0 : 0 < u := lt_of_lt_of_le ha hu
    obtain ⟨hpy, hpx⟩ :=
      Work.OddVolterra.Smooth.Qy_pos_of_isEnvelopeCurve H u σ hu0 huσ hσ1
    exact Work.OddBridge.KvecM_eq_Kvec n hn hh huσ (x σ) (y σ) (deriv x σ) (deriv y σ) hpy hpx
  have hKvecM : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ =>
        Work.OddBridge.KvecM n h p.1 p.2 (x p.2) (y p.2) (deriv x p.2) (deriv y p.2))
      (Set.Icc a 1 ×ˢ Set.Icc a 1) :=
    Work.OddBridge.KvecM_contDiffOn_box n hh H.smooth_x H.smooth_y ha le_rfl hposy hposx
  have hKsmooth : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ =>
        (Work.OddBridge.KvecM n h p.1 p.2 (x p.2) (y p.2) (deriv x p.2) (deriv y p.2)) i)
      (Set.Icc a 1 ×ˢ Set.Icc a 1) := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).contDiff.comp_contDiffOn hKvecM
  have habel' : ∀ σ ∈ Set.Ioo a 1,
      (∫ v in σ..1, (Real.sqrt (v - σ))⁻¹ •
        (Work.OddBridge.KvecM n h σ v (x v) (y v) (deriv x v) (deriv y v)) i)
        = (Work.OddVolterra.Q n h σ) i := by
    intro σ hσ
    simpa only [smul_eq_mul] using habel σ hσ
  have hdvi := dvi_of_abel (E := ℝ) ha1 hKsmooth habel' s ⟨has, hs1⟩
  have hfirst : (∫ τ in (0:ℝ)..1, (Real.sqrt (τ * ((1:ℝ) - τ)))⁻¹ •
        (Work.OddBridge.KvecM n h s s (x s) (y s) (deriv x s) (deriv y s)) i)
      = (Work.OddVolterra.G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) i := by
    rw [← congrFun (Work.OddBridge.dvi_first_term_eq n ha hae s ⟨has, hs1⟩) i]
    simp only [Pi.smul_apply, smul_eq_mul, intervalIntegral.integral_smul_const,
      intervalIntegral.integral_mul_const]
  have hsecond : (∫ σ in s..1, deriv (fun u : ℝ => ∫ τ in (0:ℝ)..1,
        (Real.sqrt (τ * ((1:ℝ) - τ)))⁻¹ •
          (Work.OddBridge.KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ)
            (deriv x σ) (deriv y σ)) i) s)
      = (∫ σ in s..1, deriv (fun u : ℝ =>
          (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s) := by
    refine intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs1) (fun σ hσ => ?_)
    have hσs : s < σ := hσ.1
    have hσ1 : σ ≤ 1 := le_of_lt hσ.2
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioo.mem_nhds (show s ∈ Set.Ioo a σ from ⟨has, hσs⟩)] with u hu
    have hmem : ∀ τ ∈ Set.uIcc (0:ℝ) 1,
        a ≤ u + τ * (σ - u) ∧ u + τ * (σ - u) ≤ σ := by
      intro τ hτ
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      exact ⟨by nlinarith [hu.1, hτ.1, hτ.2], by nlinarith [hu.2, hτ.1, hτ.2]⟩
    have h1 : (∫ τ in (0:ℝ)..1, (Real.sqrt (τ * ((1:ℝ) - τ)))⁻¹ •
          (Work.OddBridge.KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ)
            (deriv x σ) (deriv y σ)) i)
        = (∫ τ in (0:ℝ)..1, (Real.sqrt (τ * ((1:ℝ) - τ)))⁻¹ *
          (Work.OddBridge.KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ)
            (deriv x σ) (deriv y σ)) i) := by
      simp only [smul_eq_mul]
    rw [h1]
    have h2 : (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i
        = (∫ τ in (0:ℝ)..1,
            (Work.OddVolterra.Kvec n h (u + τ * (σ - u)) σ (x σ) (y σ)
              (deriv x σ) (deriv y σ)) i / Real.sqrt (τ * ((1:ℝ) - τ))) := rfl
    rw [h2]
    refine intervalIntegral.integral_congr (fun τ hτ => ?_)
    obtain ⟨haτ, hτσ⟩ := hmem τ hτ
    rw [hae (u + τ * (σ - u)) σ haτ hτσ hσ1]
    rw [div_eq_mul_inv, mul_comm]
  rw [hfirst, hsecond] at hdvi
  exact hdvi


/-- **The two differentiated (Volterra) rows, from the moment equations.** -/
theorem volterra_rows_of_moment_eqs (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hmeF : ∀ s : ℝ, 0 < s → s ≤ 1 →
      Work.OddVolterra.momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
        Commons.Geometry.Ulam.oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2))
    (hmeH : ∀ s : ℝ, 0 < s → s ≤ 1 →
      Work.OddVolterra.momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100 ∧
      |y s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100)
    :
    ∀ s ∈ Set.Ioo (0:ℝ) 1,
    (Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s)) 2 =
        (∫ σ in s..(1:ℝ), Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 2 +
          (Work.OddVolterra.Xi n h s) 2 ∧
      (Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s)) 3 =
        (∫ σ in s..(1:ℝ), Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 3 +
          (Work.OddVolterra.Xi n h s) 3 := by
  intro s hs
  obtain ⟨hs0, hs1⟩ := hs
  have ha : (0:ℝ) < s / 2 := by linarith
  have has : s / 2 < s := by linarith
  have ha1 : s / 2 < 1 := by linarith
  have hcomp := abel_KvecM_of_moment_eqs n hn hh H hmeF hmeH hclose ha ha1
  have hbox := Kden_pos_box hs0 hs1 hh H hclose
  have hintTheta : IntervalIntegrable
      (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ))
      volume s 1 :=
    theta_integrable n hn hh H hmeF hmeH hclose s ⟨hs0, hs1⟩
  -- the componentwise Abel equations in the multiplicative form
  have habel0 : ∀ σ ∈ Set.Ioo (s / 2) 1,
      (∫ v in σ..1, (Real.sqrt (v - σ))⁻¹ *
        (Work.OddBridge.KvecM n h σ v (x v) (y v) (deriv x v) (deriv y v)) 0)
        = (Work.OddVolterra.Q n h σ) 0 := by
    intro σ hσ
    rw [← (hcomp σ hσ).1]
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [div_eq_mul_inv, mul_comm]
  have habel1 : ∀ σ ∈ Set.Ioo (s / 2) 1,
      (∫ v in σ..1, (Real.sqrt (v - σ))⁻¹ *
        (Work.OddBridge.KvecM n h σ v (x v) (y v) (deriv x v) (deriv y v)) 1)
        = (Work.OddVolterra.Q n h σ) 1 := by
    intro σ hσ
    rw [← (hcomp σ hσ).2]
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [div_eq_mul_inv, mul_comm]
  have hdvi0 := dvi_component n hn hh H ha has hs1 hbox.1 hbox.2 0 habel0
  have hdvi1 := dvi_component n hn hh H ha has hs1 hbox.1 hbox.2 1 habel1
  -- ## the two rows
  have hG0 : (Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s)) 2
      = - (Work.OddVolterra.G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) 0 := by
    simp [Work.OddVolterra.Godd, Work.OddVolterra.stateOf]
  have hG1 : (Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s)) 3
      = - (Work.OddVolterra.G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) 1 := by
    simp [Work.OddVolterra.Godd, Work.OddVolterra.stateOf]
  have hX2 : (Work.OddVolterra.Xi n h s) 2 = (Work.OddVolterra.Qtilde n h s) 0 := by
    simp [Work.OddVolterra.Xi]
  have hX3 : (Work.OddVolterra.Xi n h s) 3 = (Work.OddVolterra.Qtilde n h s) 1 := by
    simp [Work.OddVolterra.Xi]
  have hQ0 : (Work.OddVolterra.Qtilde n h s) 0
      = deriv (fun u : ℝ => ∫ v in u..1,
          (Real.sqrt (v - u))⁻¹ * (Work.OddVolterra.Q n h v) 0) s := by
    simp only [Work.OddVolterra.Qtilde, Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 1
    funext u
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [div_eq_mul_inv, mul_comm]
  have hQ1 : (Work.OddVolterra.Qtilde n h s) 1
      = deriv (fun u : ℝ => ∫ v in u..1,
          (Real.sqrt (v - u))⁻¹ * (Work.OddVolterra.Q n h v) 1) s := by
    simp only [Work.OddVolterra.Qtilde, Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 1
    funext u
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [div_eq_mul_inv, mul_comm]
  have hTheta2 :
      (∫ σ in s..(1:ℝ), Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 2
        = - (∫ σ in s..1, deriv (fun u : ℝ =>
            (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0) s) := by
    rw [Work.OddBridge.intervalIntegral_apply_fin4 (i := 2) (h := hintTheta)]
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun σ _ => ?_)
    simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
  have hTheta3 :
      (∫ σ in s..(1:ℝ), Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 3
        = - (∫ σ in s..1, deriv (fun u : ℝ =>
            (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1) s) := by
    rw [Work.OddBridge.intervalIntegral_apply_fin4 (i := 3) (h := hintTheta)]
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun σ _ => ?_)
    simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
  constructor
  · rw [hG0, hTheta2, hX2, hQ0]
    linarith [hdvi0]
  · rw [hG1, hTheta3, hX3, hQ1]
    linarith [hdvi1]

end

end Work.OddVolterra.Existence
