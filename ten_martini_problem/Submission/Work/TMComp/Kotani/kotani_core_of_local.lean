import Mathlib
import Submission.Work.TMComp.Kotani.Assembly
import Submission.Work.TMComp.Kotani.mfun_props
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.UniformExt
import Submission.Work.TMComp.Kotani.continuousAt_prod_of_lipschitz_fst
import Submission.Work.TMComp.Kotani.eq_of_ext_upper
import Submission.Work.TMComp.Kotani.analyticOnNhd_inv_star_conj_center
import Submission.Work.TMComp.MAnalytic.kotaniDomain_open_and_preconnected

/-!
# The core statement of Kotani theory from the *local* continuation hypothesis

`kotani_core_of_local` produces, from the hypothesis that `mfun α lam · x` continues
analytically across every real point `E₀ ∈ (a,b)` (for every phase `x`), the `CoreStatement`:
a single function `M : ℂ → ℝ → ℂ`, jointly continuous on `kotaniDomain a b × ℝ`, holomorphic in
`z` on `kotaniDomain a b`, `ℍ`-valued there, agreeing with `mfun` above and with the reflected
formula below the real axis.

The uniformity in the phase is `uniform_ext` (a Baire category argument); the rest of the
argument glues the local continuations into one function and proves continuity (in `z` by
analyticity, in `x` by a `Cayley` transform argument which makes the family bounded).
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

/-- The predicate saying "`mfun α lam · x` continues to `B(E₀,r)` for every phase `x`". -/
def UniformLocal (α lam a b : ℝ) : Prop :=
  ∀ E₀ ∈ Set.Ioo a b, ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, ExtOn α lam E₀ r x


/-! ## The chosen local extension -/

/-- The radius given by the uniform local continuation hypothesis at `E₀`. -/
def extRad (α lam a b : ℝ) (H : UniformLocal α lam a b) (E₀ : ℝ)
    (h : E₀ ∈ Set.Ioo a b) : ℝ := (H E₀ h).choose

theorem extRad_pos (α lam a b : ℝ) (H : UniformLocal α lam a b) (E₀ : ℝ)
    (h : E₀ ∈ Set.Ioo a b) : 0 < extRad α lam a b H E₀ h :=
  (H E₀ h).choose_spec.1

theorem extRad_ext (α lam a b : ℝ) (H : UniformLocal α lam a b) (E₀ : ℝ)
    (h : E₀ ∈ Set.Ioo a b) (x : ℝ) : ExtOn α lam E₀ (extRad α lam a b H E₀ h) x :=
  (H E₀ h).choose_spec.2 x

/-- The chosen analytic continuation of `mfun α lam · x` to the ball at `E₀`. -/
def extFun (α lam a b : ℝ) (H : UniformLocal α lam a b) (E₀ : ℝ)
    (h : E₀ ∈ Set.Ioo a b) (x : ℝ) : ℂ → ℂ :=
  Classical.choose (extRad_ext α lam a b H E₀ h x)

theorem extFun_spec (α lam a b : ℝ) (H : UniformLocal α lam a b) (E₀ : ℝ)
    (h : E₀ ∈ Set.Ioo a b) (x : ℝ) :
    AnalyticOnNhd ℂ (extFun α lam a b H E₀ h x)
        (Metric.ball (E₀ : ℂ) (extRad α lam a b H E₀ h)) ∧
    (∀ z ∈ Metric.ball (E₀ : ℂ) (extRad α lam a b H E₀ h), 0 < z.im →
        extFun α lam a b H E₀ h x z = mfun α lam z x) ∧
    (∀ z ∈ Metric.ball (E₀ : ℂ) (extRad α lam a b H E₀ h), z.im < 0 →
        extFun α lam a b H E₀ h x z = 1 / star (mfun α lam (star z) (α - x))) ∧
    (∀ z ∈ Metric.ball (E₀ : ℂ) (extRad α lam a b H E₀ h), 0 < (extFun α lam a b H E₀ h x z).im) :=
  Classical.choose_spec (extRad_ext α lam a b H E₀ h x)

/-- The value at the centre of the ball of the chosen continuation. -/
def extVal (α lam a b : ℝ) (H : UniformLocal α lam a b) (E₀ : ℝ)
    (h : E₀ ∈ Set.Ioo a b) (x : ℝ) : ℂ :=
  extFun α lam a b H E₀ h x E₀

/-- The glued function.  Above the axis it is `mfun`, below it the reflected formula, and on the
real axis inside `(a,b)` the (unique) value of the analytic continuation across that point. -/
def MX (α lam a b : ℝ) (H : UniformLocal α lam a b) (z : ℂ) (x : ℝ) : ℂ :=
  if _ : 0 < z.im then mfun α lam z x
  else if _ : z.im < 0 then 1 / star (mfun α lam (star z) (α - x))
  else if hz : z.re ∈ Set.Ioo a b then extVal α lam a b H z.re hz x
  else 0

theorem MX_of_pos (α lam a b : ℝ) (H : UniformLocal α lam a b) {z : ℂ} {x : ℝ}
    (h : 0 < z.im) : MX α lam a b H z x = mfun α lam z x := by
  unfold MX; rw [dif_pos h]

theorem MX_of_neg (α lam a b : ℝ) (H : UniformLocal α lam a b) {z : ℂ} {x : ℝ}
    (h : z.im < 0) :
    MX α lam a b H z x = 1 / star (mfun α lam (star z) (α - x)) := by
  unfold MX; rw [dif_neg (not_lt.mpr (le_of_lt h)), dif_pos h]

theorem MX_of_real (α lam a b : ℝ) (H : UniformLocal α lam a b) {z : ℂ} {x : ℝ}
    (h0 : z.im = 0) (hz : z.re ∈ Set.Ioo a b) :
    MX α lam a b H z x = extVal α lam a b H z.re hz x := by
  unfold MX
  rw [dif_neg (by rw [h0]; exact lt_irrefl 0), dif_neg (by rw [h0]; exact lt_irrefl 0),
    dif_pos hz]

/-! ## Elementary helpers -/

theorem im_pos_of_mem_ball {c w : ℂ} {ρ : ℝ} (h : ρ ≤ c.im) (hw : w ∈ Metric.ball c ρ) :
    0 < w.im := by
  have h1 : |w.im - c.im| ≤ ‖w - c‖ := by
    simpa [Complex.sub_im] using Complex.abs_im_le_norm (w - c)
  have h2 : ‖w - c‖ < ρ := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw
  have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
  linarith [h3.2]

theorem im_neg_of_mem_ball {c w : ℂ} {ρ : ℝ} (h : ρ ≤ -c.im) (hw : w ∈ Metric.ball c ρ) :
    w.im < 0 := by
  have h1 : |w.im - c.im| ≤ ‖w - c‖ := by
    simpa [Complex.sub_im] using Complex.abs_im_le_norm (w - c)
  have h2 : ‖w - c‖ < ρ := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw
  have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
  linarith [h3.2]

theorem mfun_analytic_upper (α lam : ℝ) (x : ℝ) :
    AnalyticOnNhd ℂ (fun w : ℂ => mfun α lam w x) {w : ℂ | 0 < w.im} :=
  (MfunProbs.mfun_differentiableOn α lam x).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_im)

theorem analyticOnNhd_cayley_comp' {s : Set ℂ} (hs : IsOpen s) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f s) (hpos : ∀ z ∈ s, 0 < (f z).im) :
    AnalyticOnNhd ℂ (fun z => cayley (f z)) s := by
  have h1 : AnalyticOnNhd ℂ (fun z => f z - Complex.I) s := hf.sub analyticOnNhd_const
  have h2 : AnalyticOnNhd ℂ (fun z => f z + Complex.I) s := hf.add analyticOnNhd_const
  have hden : ∀ z ∈ s, f z + Complex.I ≠ 0 := by
    intro z hz hc
    have h := congrArg Complex.im hc
    simp at h
    have := hpos z hz
    linarith
  refine (AnalyticOnNhd.div h1 h2 hden).congr hs ?_
  intro z hz
  simp [cayley]

theorem continuousAt_cayleyInv' {u : ℂ} (hu : ‖u‖ < 1) : ContinuousAt cayleyInv u := by
  have hmem : u ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; exact hu
  exact continuousOn_cayleyInv.continuousAt (Metric.isOpen_ball.mem_nhds hmem)

/-! ## Agreement of the chosen extension with any other upper-half extension -/

theorem extVal_agree (α lam a b : ℝ) (H : UniformLocal α lam a b) (E₀ : ℝ)
    (hE₀ : E₀ ∈ Set.Ioo a b) (x : ℝ) {w : ℂ}
    (hw : w ∈ Metric.ball (E₀ : ℂ) (extRad α lam a b H E₀ hE₀))
    (hwim : w.im = 0) (hwr : w.re ∈ Set.Ioo a b) :
    extFun α lam a b H E₀ hE₀ x w = extVal α lam a b H w.re hwr x := by
  have hweq : w = ((w.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hwim]
  have hw' : w ∈ Metric.ball ((w.re : ℝ) : ℂ) (extRad α lam a b H w.re hwr) := by
    rw [Metric.mem_ball, dist_eq_norm, ← hweq]
    rw [sub_self, norm_zero]
    exact extRad_pos α lam a b H w.re hwr
  have hspec₁ := extFun_spec α lam a b H E₀ hE₀ x
  have hspec₂ := extFun_spec α lam a b H w.re hwr x
  have := eq_of_ext_upper (α := α) (lam := lam) (x := x)
    (extRad_pos α lam a b H E₀ hE₀) (extRad_pos α lam a b H w.re hwr)
    hspec₁.1 hspec₂.1 hspec₁.2.1 hspec₂.2.1 hw hw' hwim
  simp only [extVal]
  rw [this]
  exact congrArg (fun u : ℂ => extFun α lam a b H w.re hwr x u) hweq

/-! ## The local analytic description of `MX` -/

theorem MX_local_radius (α lam a b : ℝ) (H : UniformLocal α lam a b) {z : ℂ}
    (hz : z ∈ kotaniDomain a b) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : ℝ, ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f (Metric.ball z ρ) ∧
      (∀ w ∈ Metric.ball z ρ, f w = MX α lam a b H w x) ∧
      (∀ w ∈ Metric.ball z ρ, 0 < (MX α lam a b H w x).im) := by
  rcases lt_trichotomy z.im 0 with hlt | heq | hgt
  · -- lower half plane
    have hcim : (star z).im = -z.im := by simp [Complex.star_def, Complex.conj_im]
    have hρ : 0 < -z.im / 2 := by linarith
    have hle : -z.im / 2 ≤ (star z).im := by rw [hcim]; linarith
    refine ⟨-z.im / 2, hρ, fun x => ?_⟩
    have hbase : AnalyticOnNhd ℂ (fun u : ℂ => mfun α lam u (α - x))
        (Metric.ball (star z) (-z.im / 2)) :=
      (mfun_analytic_upper α lam (α - x)).mono fun u hu => im_pos_of_mem_ball hle hu
    have hnz : ∀ u ∈ Metric.ball (star z) (-z.im / 2), mfun α lam u (α - x) ≠ 0 :=
      fun u hu => ne_of_apply_ne Complex.im
        (ne_of_gt (mfun_im_pos' α lam (im_pos_of_mem_ball hle hu) (α - x)))
    refine ⟨fun w => 1 / star (mfun α lam (star w) (α - x)), ?_, ?_, ?_⟩
    · show AnalyticOnNhd ℂ (fun w : ℂ => 1 / star ((fun u : ℂ => mfun α lam u (α - x)) (star w)))
        (Metric.ball z (-z.im / 2))
      exact analyticOnNhd_inv_star_conj_center (c := z) (r := -z.im / 2)
        (f := fun u : ℂ => mfun α lam u (α - x)) hbase hnz
    · intro w hw
      rw [MX_of_neg α lam a b H (im_neg_of_mem_ball (by linarith) hw)]
    · intro w hw
      rw [MX_of_neg α lam a b H (im_neg_of_mem_ball (by linarith) hw)]
      exact inv_star_im_pos (mfun_im_pos' α lam
        (star_im_neg (im_neg_of_mem_ball (by linarith) hw)) (α - x))
  · -- real axis
    have hzr : z.re ∈ Set.Ioo a b := by
      rcases hz with h | h
      · exact absurd heq h
      · exact ⟨h.2.1, h.2.2⟩
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_Ioo).mem_nhds hzr)
    have hzeq : z = (z.re : ℂ) := by apply Complex.ext <;> simp [heq]
    have hball : Metric.ball (z.re : ℂ) (extRad α lam a b H z.re hzr)
        = Metric.ball z (extRad α lam a b H z.re hzr) :=
      congrArg (fun c : ℂ => Metric.ball c (extRad α lam a b H z.re hzr)) hzeq.symm
    refine ⟨min δ (extRad α lam a b H z.re hzr),
      lt_min hδpos (extRad_pos α lam a b H z.re hzr), fun x => ?_⟩
    have hspec := extFun_spec α lam a b H z.re hzr x
    have han : AnalyticOnNhd ℂ (extFun α lam a b H z.re hzr x)
        (Metric.ball z (extRad α lam a b H z.re hzr)) := hball ▸ hspec.1
    have hup : ∀ w ∈ Metric.ball z (extRad α lam a b H z.re hzr), 0 < w.im →
        extFun α lam a b H z.re hzr x w = mfun α lam w x := by
      rw [← hball]; exact hspec.2.1
    have hdown : ∀ w ∈ Metric.ball z (extRad α lam a b H z.re hzr), w.im < 0 →
        extFun α lam a b H z.re hzr x w = 1 / star (mfun α lam (star w) (α - x)) := by
      rw [← hball]; exact hspec.2.2.1
    have hposr : ∀ w ∈ Metric.ball z (extRad α lam a b H z.re hzr),
        0 < (extFun α lam a b H z.re hzr x w).im := by
      rw [← hball]; exact hspec.2.2.2
    have hsubm : Metric.ball z (min δ (extRad α lam a b H z.re hzr)) ⊆
        Metric.ball z (extRad α lam a b H z.re hzr) := Metric.ball_subset_ball (min_le_right _ _)
    have hwre : ∀ w ∈ Metric.ball z (min δ (extRad α lam a b H z.re hzr)), w.re ∈ Set.Ioo a b := by
      intro w hw
      apply hδsub
      have h1 : |w.re - z.re| ≤ dist w z := by
        rw [dist_eq_norm]; simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
      rw [Metric.mem_ball, Real.dist_eq]
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _))
    refine ⟨extFun α lam a b H z.re hzr x, han.mono hsubm, ?_, ?_⟩
    · intro w hw
      have hwr := hwre w hw
      have hwR := hsubm hw
      rcases lt_trichotomy w.im 0 with hwlt | hweq | hwgt
      · rw [MX_of_neg α lam a b H hwlt, hdown w hwR hwlt]
      · have hwe : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hweq]
        have hw'' : w ∈ Metric.ball (w.re : ℂ) (extRad α lam a b H w.re hwr) := by
          have hb := congrArg (fun c : ℂ => Metric.ball c (extRad α lam a b H w.re hwr)) hwe
          rw [← hb]
          exact Metric.mem_ball_self (extRad_pos α lam a b H w.re hwr)
        have hwzre : w ∈ Metric.ball (z.re : ℂ) (extRad α lam a b H z.re hzr) := hball.symm ▸ hwR
        have hval := eq_of_ext_upper (α := α) (lam := lam) (x := x)
          (extRad_pos α lam a b H z.re hzr) (extRad_pos α lam a b H w.re hwr)
          hspec.1 (extFun_spec α lam a b H w.re hwr x).1
          hspec.2.1 (extFun_spec α lam a b H w.re hwr x).2.1 hwzre hw'' hweq
        rw [MX_of_real α lam a b H hweq hwr, hval]
        simp only [extVal]
        exact congrArg (fun u : ℂ => extFun α lam a b H w.re hwr x u) hwe
      · rw [MX_of_pos α lam a b H hwgt, hup w hwR hwgt]
    · intro w hw
      have hwr := hwre w hw
      have hwR := hsubm hw
      rcases lt_trichotomy w.im 0 with hwlt | hweq | hwgt
      · rw [MX_of_neg α lam a b H hwlt]
        exact inv_star_im_pos (mfun_im_pos' α lam (star_im_neg hwlt) (α - x))
      · have hwe : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hweq]
        have hw'' : w ∈ Metric.ball (w.re : ℂ) (extRad α lam a b H w.re hwr) := by
          have hb := congrArg (fun c : ℂ => Metric.ball c (extRad α lam a b H w.re hwr)) hwe
          rw [← hb]
          exact Metric.mem_ball_self (extRad_pos α lam a b H w.re hwr)
        rw [MX_of_real α lam a b H hweq hwr]
        have hp := (extFun_spec α lam a b H w.re hwr x).2.2.2 w hw''
        simp only [extVal]
        exact congrArg (fun u : ℂ => (extFun α lam a b H w.re hwr x u).im) hwe ▸ hp
      · rw [MX_of_pos α lam a b H hwgt]
        exact mfun_im_pos' α lam hwgt x
  · -- upper half plane
    have hρ : 0 < z.im / 2 := by linarith
    have hle : z.im / 2 ≤ z.im := by linarith
    refine ⟨z.im / 2, hρ, fun x => ?_⟩
    have hbase : AnalyticOnNhd ℂ (fun w : ℂ => mfun α lam w x) (Metric.ball z (z.im / 2)) :=
      (mfun_analytic_upper α lam x).mono fun w hw => im_pos_of_mem_ball hle hw
    refine ⟨fun w => mfun α lam w x, hbase, ?_, ?_⟩
    · intro w hw
      rw [MX_of_pos α lam a b H (im_pos_of_mem_ball hle hw)]
    · intro w hw
      rw [MX_of_pos α lam a b H (im_pos_of_mem_ball hle hw)]
      exact mfun_im_pos' α lam (im_pos_of_mem_ball hle hw) x

theorem MX_pos (α lam a b : ℝ) (H : UniformLocal α lam a b) {z : ℂ}
    (hz : z ∈ kotaniDomain a b) (x : ℝ) : 0 < (MX α lam a b H z x).im := by
  obtain ⟨ρ, hρ, hf⟩ := MX_local_radius α lam a b H hz
  exact (hf x).choose_spec.2.2 z (Metric.mem_ball_self hρ)

theorem MX_analytic (α lam a b : ℝ) (H : UniformLocal α lam a b) (x : ℝ) :
    AnalyticOnNhd ℂ (fun z => MX α lam a b H z x) (kotaniDomain a b) := by
  intro z hz
  obtain ⟨ρ, hρ, hf⟩ := MX_local_radius α lam a b H hz
  obtain ⟨f, hfan, hfeq, _⟩ := hf x
  refine (hfan z (Metric.mem_ball_self hρ)).congr ?_
  filter_upwards [Metric.ball_mem_nhds z hρ] with w hw
  exact hfeq w hw

theorem MX_lipschitz (α lam a b : ℝ) (H : UniformLocal α lam a b) {z : ℂ}
    (hz : z ∈ kotaniDomain a b) :
    ∃ s : ℝ, 0 < s ∧ ∃ L : ℝ, 0 < L ∧ ∀ x : ℝ,
      ∀ z' ∈ Metric.ball z s, ∀ w ∈ Metric.ball z s,
        ‖cayley (MX α lam a b H z' x) - cayley (MX α lam a b H w x)‖ ≤ L * ‖z' - w‖ := by
  obtain ⟨ρ, hρ, hf⟩ := MX_local_radius α lam a b H hz
  refine ⟨ρ / 2, by linarith, 4 / ρ, by positivity, fun x => ?_⟩
  obtain ⟨f, hfan, hfeq, hpos⟩ := hf x
  have hfpos : ∀ w ∈ Metric.ball z ρ, 0 < (f w).im := by
    intro w hw
    rw [hfeq w hw]
    exact hpos w hw
  have hfc : AnalyticOnNhd ℂ (fun w => cayley (f w)) (Metric.ball z ρ) :=
    analyticOnNhd_cayley_comp' Metric.isOpen_ball hfan hfpos
  have hb : ∀ w ∈ Metric.ball z ρ, ‖cayley (f w)‖ ≤ 1 :=
    fun w hw => le_of_lt (norm_cayley_lt_one (hfpos w hw))
  have hzs : ‖z - z‖ + ρ / 2 < ρ := by rw [sub_self, norm_zero]; linarith
  have hkey := lipschitz_of_bounded hfc hb hzs
  have hsub : Metric.closedBall z (ρ / 2) ⊆ Metric.ball z ρ :=
    Metric.closedBall_subset_ball (by linarith)
  intro z' hz' w hw
  have h1 : z' ∈ Metric.closedBall z (ρ / 2) := by
    rw [Metric.mem_closedBall]
    exact le_of_lt (Metric.mem_ball.mp hz')
  have h2 : w ∈ Metric.closedBall z (ρ / 2) := by
    rw [Metric.mem_closedBall]
    exact le_of_lt (Metric.mem_ball.mp hw)
  have hc : cayley (MX α lam a b H z' x) - cayley (MX α lam a b H w x)
      = cayley (f z') - cayley (f w) := by
    rw [hfeq z' (hsub h1), hfeq w (hsub h2)]
  rw [hc]
  have hkey2 := hkey z' h1 w h2
  have hd : ρ - ‖z - z‖ - ρ / 2 = ρ / 2 := by rw [sub_self, norm_zero]; ring
  rw [hd] at hkey2
  have hle : 2 / (ρ / 2) ≤ 4 / ρ := by
    have hρne : ρ ≠ 0 := ne_of_gt hρ
    have he : 2 / (ρ / 2) = 4 / ρ := by
      field_simp
      ring
    rw [he]
  exact le_trans hkey2 (mul_le_mul_of_nonneg_right hle (norm_nonneg _))

theorem cayleyMX_continuous_x (α lam a b : ℝ) (H : UniformLocal α lam a b) {z : ℂ}
    (hz : z ∈ kotaniDomain a b) (x₀ : ℝ) :
    ContinuousAt (fun x : ℝ => cayley (MX α lam a b H z x)) x₀ := by
  rcases lt_trichotomy z.im 0 with hlt | heq | hgt
  · -- lower half plane
    have hcont : ContinuousAt (fun x : ℝ => 1 / star (mfun α lam (star z) (α - x))) x₀ :=
      (continuous_sig_fst α lam (star_im_neg hlt)).continuousAt
    have hc : ContinuousAt cayley (1 / star (mfun α lam (star z) (α - x₀))) := by
      refine continuousAt_cayley (fun hc' => ?_)
      have him := inv_star_im_pos (mfun_im_pos' α lam (star_im_neg hlt) (α - x₀))
      rw [hc'] at him
      simp at him
      exact absurd him (by norm_num)
    have hT : ContinuousAt (fun x : ℝ => cayley (1 / star (mfun α lam (star z) (α - x)))) x₀ :=
      hc.tendsto.comp hcont.tendsto
    refine hT.congr ?_
    filter_upwards with x
    rw [MX_of_neg α lam a b H hlt]
  · -- on the real axis: approximate vertically and use the uniform Lipschitz bound
    have hzr : z.re ∈ Set.Ioo a b := by
      rcases hz with h | h
      · exact absurd heq h
      · exact ⟨h.2.1, h.2.2⟩
    obtain ⟨s, hs, L, hL, hbound⟩ := MX_lipschitz α lam a b H hz
    rw [Metric.continuousAt_iff]
    intro ε hε
    set t : ℝ := min (s / 2) (ε / (4 * L)) with htdef
    have htpos : 0 < t := lt_min (by linarith) (by positivity)
    have htlt : t < s := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hzt : z + (t : ℂ) * Complex.I ∈ Metric.ball z s := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : z + (t : ℂ) * Complex.I - z = (t : ℂ) * Complex.I := by ring
      rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos htpos]
      exact htlt
    have hztim : 0 < (z + (t : ℂ) * Complex.I).im := by
      have h : (z + (t : ℂ) * Complex.I).im = z.im + t := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
      rw [h, heq, zero_add]
      exact htpos
    have hcont2 : ContinuousAt (fun x : ℝ => cayley (mfun α lam (z + (t : ℂ) * Complex.I) x)) x₀ := by
      have hc : ContinuousAt cayley (mfun α lam (z + (t : ℂ) * Complex.I) x₀) := by
        refine continuousAt_cayley (fun hc' => ?_)
        have him := mfun_im_pos' α lam hztim x₀
        rw [hc'] at him
        simp at him
        exact absurd him (by norm_num)
      exact hc.tendsto.comp (continuous_mfun_fst α lam hztim).continuousAt.tendsto
    obtain ⟨δ, hδ, hδ2⟩ := Metric.continuousAt_iff.mp hcont2 (ε / 2) (by linarith)
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have h1 : ‖cayley (MX α lam a b H z x) - cayley (MX α lam a b H (z + (t : ℂ) * Complex.I) x)‖ ≤ L * t := by
      have hb := hbound x z (Metric.mem_ball_self hs) (z + (t : ℂ) * Complex.I) hzt
      have hzn : ‖z - (z + (t : ℂ) * Complex.I)‖ = t := by
        rw [show z - (z + (t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) by ring, norm_neg,
          norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
      rwa [hzn] at hb
    have h3 : ‖cayley (MX α lam a b H (z + (t : ℂ) * Complex.I) x₀) - cayley (MX α lam a b H z x₀)‖ ≤ L * t := by
      have hb := hbound x₀ (z + (t : ℂ) * Complex.I) hzt z (Metric.mem_ball_self hs)
      have hzn : ‖(z + (t : ℂ) * Complex.I) - z‖ = t := by
        rw [show (z + (t : ℂ) * Complex.I) - z = (t : ℂ) * Complex.I by ring, norm_mul,
          Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
      rwa [hzn] at hb
    have h2 : ‖cayley (MX α lam a b H (z + (t : ℂ) * Complex.I) x) - cayley (MX α lam a b H (z + (t : ℂ) * Complex.I) x₀)‖ < ε / 2 := by
      rw [MX_of_pos α lam a b H hztim, MX_of_pos α lam a b H hztim]
      have hh := hδ2 hx
      rwa [dist_eq_norm] at hh
    have hLt : L * t ≤ ε / 4 := by
      have hle : t ≤ ε / (4 * L) := min_le_right _ _
      have heq2 : L * (ε / (4 * L)) = ε / 4 := by
        have hLne : L ≠ 0 := ne_of_gt hL
        field_simp
      calc L * t ≤ L * (ε / (4 * L)) := mul_le_mul_of_nonneg_left hle (le_of_lt hL)
        _ = ε / 4 := heq2
    rw [dist_eq_norm]
    calc ‖cayley (MX α lam a b H z x) - cayley (MX α lam a b H z x₀)‖
        = ‖(cayley (MX α lam a b H z x) - cayley (MX α lam a b H (z + (t : ℂ) * Complex.I) x))
            + (cayley (MX α lam a b H (z + (t : ℂ) * Complex.I) x)
                - cayley (MX α lam a b H (z + (t : ℂ) * Complex.I) x₀))
            + (cayley (MX α lam a b H (z + (t : ℂ) * Complex.I) x₀) - cayley (MX α lam a b H z x₀))‖ := by
          congr 1; ring
      _ ≤ _ := norm_add₃_le
      _ < ε := by linarith [h1, h2, h3, hLt]
  · -- upper half plane
    have hcont : ContinuousAt (fun x : ℝ => mfun α lam z x) x₀ :=
      (continuous_mfun_fst α lam hgt).continuousAt
    have hc : ContinuousAt cayley (mfun α lam z x₀) := by
      refine continuousAt_cayley (fun hc' => ?_)
      have him := mfun_im_pos' α lam hgt x₀
      rw [hc'] at him
      simp at him
      exact absurd him (by norm_num)
    have hT : ContinuousAt (fun x : ℝ => cayley (mfun α lam z x)) x₀ :=
      hc.tendsto.comp hcont.tendsto
    refine hT.congr ?_
    filter_upwards with x
    rw [MX_of_pos α lam a b H hgt]

theorem MX_continuous_x (α lam a b : ℝ) (H : UniformLocal α lam a b) {z : ℂ}
    (hz : z ∈ kotaniDomain a b) (x₀ : ℝ) :
    ContinuousAt (fun x : ℝ => MX α lam a b H z x) x₀ := by
  have h1 := cayleyMX_continuous_x α lam a b H hz x₀
  have h2 : ContinuousAt cayleyInv (cayley (MX α lam a b H z x₀)) :=
    continuousAt_cayleyInv' (norm_cayley_lt_one (MX_pos α lam a b H hz x₀))
  have h3 : ContinuousAt (fun x : ℝ => cayleyInv (cayley (MX α lam a b H z x))) x₀ :=
    h2.tendsto.comp h1.tendsto
  refine h3.congr ?_
  filter_upwards with x
  exact cayleyInv_cayley (MX_pos α lam a b H hz x)

theorem MX_continuousAt (α lam a b : ℝ) (H : UniformLocal α lam a b) (hab : a < b) {z₀ : ℂ}
    (hz₀ : z₀ ∈ kotaniDomain a b) (x₀ : ℝ) :
    ContinuousAt (fun p : ℂ × ℝ => MX α lam a b H p.1 p.2) (z₀, x₀) := by
  have hG : ContinuousAt (fun p : ℂ × ℝ => cayley (MX α lam a b H p.1 p.2)) (z₀, x₀) :=
    continuousAt_prod_of_lipschitz_fst (U := kotaniDomain a b)
      (g := fun z x => cayley (MX α lam a b H z x))
      (fun z hz => MX_lipschitz α lam a b H hz)
      (fun z hz x => cayleyMX_continuous_x α lam a b H hz x)
      z₀ hz₀ x₀
  have h2 : ContinuousAt cayleyInv (cayley (MX α lam a b H z₀ x₀)) :=
    continuousAt_cayleyInv' (norm_cayley_lt_one (MX_pos α lam a b H hz₀ x₀))
  have h3 : ContinuousAt (fun p : ℂ × ℝ => cayleyInv (cayley (MX α lam a b H p.1 p.2)))
      (z₀, x₀) :=
    h2.tendsto.comp hG.tendsto
  have hopen : IsOpen (kotaniDomain a b) :=
    (Work.TMComp.MAnalytic.kotaniDomain_open_and_preconnected a b hab).1
  have hev : ∀ᶠ p : ℂ × ℝ in 𝓝 (z₀, x₀), p.1 ∈ kotaniDomain a b :=
    (continuousAt_fst : ContinuousAt (fun p : ℂ × ℝ => p.1) (z₀, x₀)).eventually
      (hopen.mem_nhds hz₀)
  refine h3.congr ?_
  filter_upwards [hev] with p hp
  exact cayleyInv_cayley (MX_pos α lam a b H hp p.2)

theorem MX_continuousOn (α lam a b : ℝ) (H : UniformLocal α lam a b) (hab : a < b) :
    ContinuousOn (fun p : ℂ × ℝ => MX α lam a b H p.1 p.2) (kotaniDomain a b ×ˢ Set.univ) := by
  rintro ⟨z₀, x₀⟩ hp
  simp only [Set.mem_prod, Set.mem_univ, and_true] at hp
  exact (MX_continuousAt α lam a b H hab hp x₀).continuousWithinAt

/-- **Kotani's theorem, local-to-global form.**  The local continuation hypothesis
(`hloc`: at every real `E₀ ∈ (a,b)` and every phase `x`, `mfun α lam · x` continues
analytically across `E₀`, with the reflection formula below the axis and positive imaginary
part) yields the core statement of Kotani theory: a single function `M` on
`kotaniDomain a b × ℝ`, jointly continuous, holomorphic in the energy, `ℍ`-valued, agreeing
with `mfun` above the axis and with the reflected formula below it. -/
theorem kotani_core_of_local (α lam a b : ℝ) (hα : Irrational α) (h0 : 0 ≤ lam)
    (hab : a < b) (hL : ∀ E ∈ Set.Ioo a b, Work.TMContract.lyap α lam (E : ℂ) = 0)
    (hloc : ∀ E₀ ∈ Set.Ioo a b, ∀ x : ℝ, ∃ f : ℂ → ℂ,
      AnalyticAt ℂ f (E₀ : ℂ) ∧
      (∀ᶠ E in nhds (E₀ : ℂ), 0 < E.im → f E = Work.TMComp.Kotani.mfun α lam E x) ∧
      (∀ᶠ E in nhds (E₀ : ℂ), E.im < 0 →
        f E = 1 / star (Work.TMComp.Kotani.mfun α lam (star E) (α - x))) ∧
      (∀ᶠ E in nhds (E₀ : ℂ), 0 < (f E).im)) :
    Work.TMComp.Kotani.CoreStatement α lam a b := by
  have H : UniformLocal α lam a b := uniform_ext α lam a b hα hab hloc
  exact ⟨MX α lam a b H, MX_continuousOn α lam a b H hab,
    fun z hz x => MX_pos α lam a b H hz x,
    fun E hE x => MX_of_pos α lam a b H hE,
    fun E hE x => MX_of_neg α lam a b H hE,
    fun x => (MX_analytic α lam a b H x).differentiableOn⟩

end Work.TMComp.Kotani
