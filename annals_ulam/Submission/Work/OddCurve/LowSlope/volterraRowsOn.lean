import Mathlib
import Submission.Work.OddVolterra.Existence.volterra_rows_of_moment_eqs
import Submission.Work.OddVolterra.Existence.theta_integrable

namespace Work.OddCurve.LowSlope

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddVolterra

noncomputable section

/-- **Interval-integrability of the `𝚯`-integrand.**  The version of
`Work.OddVolterra.Existence.theta_integrable` without the (unused) moment-equation hypotheses, so
that it applies when the moment equations are only known on a right interval `(a,1]`. -/
theorem theta_integrable_close (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100 ∧
      |y s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100) :
    ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      IntervalIntegrable (fun σ : ℝ =>
        Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) volume s 1 := by
  intro s hs
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hposy, hposx⟩ := Work.OddVolterra.Existence.Kden_pos_box hs0 hs1 hh H hclose
  -- the manifest kernel is `C²` on the square `[s/2,1]²`
  have hbox2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      Work.OddVolterra.KernelExt.KvecM n h p.1 p.2 (x p.2) (y p.2) (deriv x p.2) (deriv y p.2))
      (Set.Icc (s / 2) 1 ×ˢ Set.Icc (s / 2) 1) :=
    Work.OddVolterra.KernelExt.KvecM_contDiffOn_box n hh H.smooth_x H.smooth_y
      (by linarith) le_rfl hposy hposx
  have hGfun : ∀ i : Fin 2, ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      (Work.OddVolterra.KernelExt.KvecM n h p.1 p.2 (x p.2) (y p.2) (deriv x p.2)
        (deriv y p.2)) i) (Set.Icc (s / 2) 1 ×ˢ Set.Icc (s / 2) 1) := by
    intro i
    have h1 := hbox2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).contDiff.comp_contDiffOn
      h1).of_le (by norm_num)
  -- the last two rows of `ΘM`, via the parametric differentiation lemma
  have hrow : ∀ i : Fin 2, IntervalIntegrable (fun σ : ℝ => deriv (fun u : ℝ =>
      ∫ τ in (0 : ℝ)..1, (Work.OddVolterra.KernelExt.KvecM n h (u + τ * (σ - u)) σ
        (x σ) (y σ) (deriv x σ) (deriv y σ)) i / Real.sqrt (τ * (1 - τ))) s) volume s 1 :=
    fun i => Work.OddVolterra.Existence.theta_deriv_parametrization_integrable _ (hGfun i) hs0 hs1
  -- the manifest integrand is interval-integrable
  have hintM : IntervalIntegrable (fun σ : ℝ =>
      Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ))
      volume s 1 := by
    rw [intervalIntegrable_iff, uIoc_of_le hs1.le]
    have hiff : IntegrableOn (fun σ : ℝ =>
        Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ))
        (Set.Ioc s 1) volume ↔
        ∀ i : Fin 4, IntegrableOn (fun σ : ℝ =>
          (Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)) i)
          (Set.Ioc s 1) volume := by
      show Integrable (fun σ : ℝ =>
          Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ))
          (volume.restrict (Set.Ioc s 1)) ↔
        ∀ i : Fin 4, Integrable (fun σ : ℝ =>
          (Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)) i)
          (volume.restrict (Set.Ioc s 1))
      exact integrable_pi_iff
    rw [hiff]
    intro i
    fin_cases i
    · have hcont : ContinuousOn (fun σ : ℝ => -deriv x σ) (Set.uIcc s 1) := by
        refine ContinuousOn.neg ?_
        refine (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_x).continuousOn.mono ?_
        intro σ hσ
        exact lt_of_lt_of_le hs0 (by simpa [min_eq_left hs1.le] using hσ.1)
      refine (hcont.intervalIntegrable).1.congr_fun (fun σ _ => ?_) measurableSet_Ioc
      simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
    · have hcont : ContinuousOn (fun σ : ℝ => -deriv y σ) (Set.uIcc s 1) := by
        refine ContinuousOn.neg ?_
        refine (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_y).continuousOn.mono ?_
        intro σ hσ
        exact lt_of_lt_of_le hs0 (by simpa [min_eq_left hs1.le] using hσ.1)
      refine (hcont.intervalIntegrable).1.congr_fun (fun σ _ => ?_) measurableSet_Ioc
      simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
    · have hmain : IntervalIntegrable (fun σ : ℝ => -deriv (fun u : ℝ =>
          (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0) s)
          volume s 1 := (hrow 0).neg
      refine hmain.1.congr_fun (fun σ _ => ?_) measurableSet_Ioc
      simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
    · have hmain : IntervalIntegrable (fun σ : ℝ => -deriv (fun u : ℝ =>
          (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1) s)
          volume s 1 := (hrow 1).neg
      refine hmain.1.congr_fun (fun σ _ => ?_) measurableSet_Ioc
      simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
  -- `G2` and `G2M` agree eventually in the `u`-slot at `u = s`
  have hG2eq : ∀ (σ : ℝ) (i : Fin 2), σ ∈ Set.Ioo s 1 →
      (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i)
        =ᶠ[𝓝 s] (fun u : ℝ =>
          (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) := by
    intro σ i hσ
    filter_upwards [isOpen_Ioo.mem_nhds
      (show s ∈ Set.Ioo (s / 2) σ from ⟨by linarith, hσ.1⟩)] with u hu
    simp only [Work.OddVolterra.G2, Work.OddVolterra.KernelExt.G2M]
    refine intervalIntegral.integral_congr (fun τ hτ => ?_)
    have hτ0 : (0:ℝ) ≤ τ := by simpa using hτ.1
    have hτ1 : τ ≤ 1 := by simpa using hτ.2
    have hv : u + τ * (σ - u) ∈ Set.Icc (s / 2) 1 := by
      constructor
      · nlinarith [hu.1, hτ0, hτ1, hσ.1]
      · nlinarith [hu.2, hτ0, hτ1, hσ.2]
    have hσI : σ ∈ Set.Icc (s / 2) 1 := ⟨by linarith [hσ.1], hσ.2.le⟩
    have hR1 : 0 < (y σ + Work.OddVolterra.hquot h (u + τ * (σ - u)) σ) *
        (Work.OddVolterra.line h σ (y σ) + Work.OddVolterra.line h (u + τ * (σ - u)) (y σ)) :=
      Real.sqrt_pos.mp (hposy (u + τ * (σ - u)) σ hv hσI)
    have hR2 : 0 < (-(x σ) + Work.OddVolterra.hquot h (u + τ * (σ - u)) σ) *
        (Work.OddVolterra.line h σ (-(x σ))
          + Work.OddVolterra.line h (u + τ * (σ - u)) (-(x σ))) :=
      Real.sqrt_pos.mp (hposx (u + τ * (σ - u)) σ hv hσI)
    have hK := Work.OddVolterra.KernelExt.KvecM_eq_Kvec (s := u + τ * (σ - u)) (σ := σ)
      n hn hh (by nlinarith [hu.2, hτ0, hτ1]) (x σ) (y σ) (deriv x σ) (deriv y σ) hR1 hR2
    rw [hK]
  -- `Θ` and `ΘM` agree on the open interval
  have heq : Set.EqOn (fun σ : ℝ =>
      Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ))
      (fun σ : ℝ => Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ))
      (Set.Ioo s 1) := by
    intro σ hσ
    show Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)
      = Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)
    funext i
    fin_cases i
    · simp [Work.OddVolterra.Theta, Work.OddVolterra.KernelExt.ThetaM,
        Work.OddVolterra.stateOf]
    · simp [Work.OddVolterra.Theta, Work.OddVolterra.KernelExt.ThetaM,
        Work.OddVolterra.stateOf]
    · show (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 2
        = (Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)) 2
      have h1 : (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 2
          = -(deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (x σ) (y σ)
              (deriv x σ) (deriv y σ)) 0) s) := by
        simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
      have h2 : (Work.OddVolterra.KernelExt.ThetaM n h s σ
            (Work.OddVolterra.stateOf x y σ)) 2
          = -(deriv (fun u : ℝ => (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ)
              (deriv x σ) (deriv y σ)) 0) s) := by
        simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
      rw [h1, h2]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (hG2eq σ 0 hσ)
    · show (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 3
        = (Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)) 3
      have h1 : (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 3
          = -(deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (x σ) (y σ)
              (deriv x σ) (deriv y σ)) 1) s) := by
        simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
      have h2 : (Work.OddVolterra.KernelExt.ThetaM n h s σ
            (Work.OddVolterra.stateOf x y σ)) 3
          = -(deriv (fun u : ℝ => (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ)
              (deriv x σ) (deriv y σ)) 1) s) := by
        simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
      rw [h1, h2]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (hG2eq σ 1 hσ)
  refine hintM.congr_uIoo ?_
  rw [Set.uIoo_of_le hs1.le]
  exact heq.symm


/-- **The Abel system `(arik)` of the paper's kernel `Kvec`, from the two moment equations on
`(b,1]`.**  The analogue of `Work.OddVolterra.Existence.abel_Kvec_of_moment_eqs` in which the
moment equations are only assumed on a right interval. -/
theorem abel_kvec_of_moment_eqs_on (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hmeF : ∀ s : ℝ, b < s → s ≤ 1 →
      Work.OddVolterra.momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
        Commons.Geometry.Ulam.oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2))
    (hmeH : ∀ s : ℝ, b < s → s ≤ 1 →
      Work.OddVolterra.momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100 ∧
      |y s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100) :
    ∀ s ∈ Set.Ioo b 1,
      (∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
            Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 0 ∧
      (∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
            Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 1 := by
  intro s hs
  obtain ⟨hsb, hs1⟩ := hs
  have hs0 : 0 < s := lt_trans hb hsb
  obtain ⟨S, hSn, hSa, hSc, hSh, hSx, hSy, hSf⟩ :=
    Work.OddVolterra.Existence.setup_of_envelope n hn hh H hclose hs0 hs1
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
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (show s ∈ Set.Ioo b 1 from ⟨hsb, hs1⟩))
        (fun u hu => ?_)
      simpa [Work.OddVolterra.momentRHS] using hmeF u hu.1 (le_of_lt hu.2)
    exact hev.iteratedDeriv_eq (n + 1)
  have hH : iteratedDeriv n
      (fun u : ℝ => Work.OddVolterra.momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) u) s
      = 0 := by
    have hev : (fun u : ℝ => Work.OddVolterra.momentH n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u) =ᶠ[𝓝 s] (fun _ : ℝ => 0) := by
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (show s ∈ Set.Ioo b 1 from ⟨hsb, hs1⟩))
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

/-- **The same Abel system with the manifest kernel `KvecM`, from the moment equations on
`(b,1]`.** -/
theorem abel_kvecM_of_moment_eqs_on (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hb1 : b < 1)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hmeF : ∀ s : ℝ, b < s → s ≤ 1 →
      Work.OddVolterra.momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
        Commons.Geometry.Ulam.oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2))
    (hmeH : ∀ s : ℝ, b < s → s ≤ 1 →
      Work.OddVolterra.momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100 ∧
      |y s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100) :
    ∀ s ∈ Set.Ioo b 1,
      (∫ σ in s..1,
          (Work.OddBridge.KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
            Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 0 ∧
      (∫ σ in s..1,
          (Work.OddBridge.KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
            Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 1 := by
  intro s hs
  obtain ⟨h0, h1⟩ := abel_kvec_of_moment_eqs_on n hn hb hh H hmeF hmeH hclose s hs
  have hae : ∀ u σ : ℝ, b ≤ u → u < σ → σ ≤ 1 →
      Work.OddBridge.KvecM n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Work.OddVolterra.Kvec n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ) := by
    intro u σ hu huσ hσ1
    have hu0 : 0 < u := lt_of_lt_of_le hb hu
    obtain ⟨hQy, hQx⟩ :=
      Work.OddVolterra.Smooth.Qy_pos_of_isEnvelopeCurve H u σ hu0 (le_of_lt huσ) hσ1
    exact Work.OddBridge.KvecM_eq_Kvec n hn hh (le_of_lt huσ) (x σ) (y σ)
      (deriv x σ) (deriv y σ) hQy hQx
  obtain ⟨e0, e1⟩ :=
    Work.OddBridge.abel_integral_Kvec_eq_KvecM n hb hae (le_of_lt hs.1) (le_of_lt hs.2)
  exact ⟨by rw [← e0]; exact h0, by rw [← e1]; exact h1⟩

theorem volterraRowsOn (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ} {a : ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (ha : 0 < a) (ha1 : a < 1)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hmeF : ∀ s : ℝ, a < s → s ≤ 1 →
      Work.OddVolterra.momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
        Commons.Geometry.Ulam.oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2))
    (hmeH : ∀ s : ℝ, a < s → s ≤ 1 →
      Work.OddVolterra.momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100 ∧
      |y s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100) :
    ∀ s ∈ Set.Ioo a 1,
      (Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s)) 2 =
          (∫ σ in s..1, Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 2 +
            (Work.OddVolterra.Xi n h s) 2 ∧
      (Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s)) 3 =
          (∫ σ in s..1, Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 3 +
            (Work.OddVolterra.Xi n h s) 3 := by
  intro s hs
  have hs0 : 0 < s := lt_trans ha hs.1
  have hs1 : s < 1 := hs.2
  have hcomp := abel_kvecM_of_moment_eqs_on n hn ha ha1 hh H hmeF hmeH hclose
  -- positivity of the Abel denominators on the square `[a,1]²`
  obtain ⟨hposy', hposx'⟩ :=
    Work.OddVolterra.Existence.Kden_pos_box ha ha1 hh H hclose
  have hposy : ∀ u σ : ℝ, u ∈ Set.Icc a 1 → σ ∈ Set.Icc a 1 →
      0 < Work.OddVolterra.Kden h u σ (y σ) :=
    fun u σ hu hσ => hposy' u σ ⟨by linarith [hu.1, ha], hu.2⟩ ⟨by linarith [hσ.1, ha], hσ.2⟩
  have hposx : ∀ u σ : ℝ, u ∈ Set.Icc a 1 → σ ∈ Set.Icc a 1 →
      0 < Work.OddVolterra.Kden h u σ (-(x σ)) :=
    fun u σ hu hσ => hposx' u σ ⟨by linarith [hu.1, ha], hu.2⟩ ⟨by linarith [hσ.1, ha], hσ.2⟩
  have hintTheta : IntervalIntegrable
      (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ))
      volume s 1 :=
    theta_integrable_close n hn hh H hclose s ⟨hs0, hs1⟩
  -- the componentwise Abel equations in the multiplicative form
  have habel0 : ∀ σ ∈ Set.Ioo a 1,
      (∫ v in σ..1, (Real.sqrt (v - σ))⁻¹ *
        (Work.OddBridge.KvecM n h σ v (x v) (y v) (deriv x v) (deriv y v)) 0)
        = (Work.OddVolterra.Q n h σ) 0 := by
    intro σ hσ
    rw [← (hcomp σ hσ).1]
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [div_eq_mul_inv, mul_comm]
  have habel1 : ∀ σ ∈ Set.Ioo a 1,
      (∫ v in σ..1, (Real.sqrt (v - σ))⁻¹ *
        (Work.OddBridge.KvecM n h σ v (x v) (y v) (deriv x v) (deriv y v)) 1)
        = (Work.OddVolterra.Q n h σ) 1 := by
    intro σ hσ
    rw [← (hcomp σ hσ).2]
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [div_eq_mul_inv, mul_comm]
  have hdvi0 := Work.OddVolterra.Existence.dvi_component n hn hh H ha hs.1 hs1 hposy hposx 0 habel0
  have hdvi1 := Work.OddVolterra.Existence.dvi_component n hn hh H ha hs.1 hs1 hposy hposx 1 habel1
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

end Work.OddCurve.LowSlope
