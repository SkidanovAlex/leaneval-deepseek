import Mathlib
import Submission.Work.Pert.Ksub2.anchor_at_scale
import Submission.Work.Pert.Ksub2.Xc_sharp_on_strip
import Submission.Work.Pert.Ksub2.anchor_scale_deriv
import Submission.Work.Pert.Ksub2.F0f_near_translation_anchor
import Submission.Work.Pert.Ksub2.exists_model_data_full
import Submission.Work.Pert.Ksub2.exists_lipschitzOn_of_compact
import Submission.Work.Pert.Ksub2.f0_amp_band
import Submission.Work.PertCrux.f0_amp_uniform_K
import Submission.Work.PertCrux.defect_le_of_trap
import Submission.Work.PertCrux.tauC_tau0_close_of_far
import Submission.Work.PertCrux.dev_le_of_deriv_diff_le
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Pert.Pin.walk_room
import Submission.Work.Pert.Pin.band_goodP_sqrt_im
import Submission.Work.Pert.Pin.band_dev_arith
import Submission.Work.Pert.Pin.defect_le_of_norm_bound
import Submission.Work.Pert.Pin.eventually_log_le_sqrt
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert.Pin

open MandelDim Complex Set Metric Filter Topology
open scoped Topology

set_option maxHeartbeats 8000000

/-! ## Elementary list and threshold lemmas (small contexts, cheap to elaborate) -/

private lemma foldr_max_ge {l : List ℝ} {z a : ℝ} (ha : a ∈ l) : a ≤ l.foldr max z := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp ha with rfl | hmem
      · exact le_max_left _ _
      · exact le_trans (ih hmem) (le_max_right _ _)

private lemma le_foldr_max {l : List ℝ} {z : ℝ} : z ≤ l.foldr max z := by
  induction l with
  | nil => simp
  | cons b t ih => simp only [List.foldr_cons]; exact le_trans ih (le_max_right _ _)

/-- `√M ≤ M/2` for `M = s²`, `s ≥ 1000`. -/
private lemma sqrt_le_half {M s : ℝ} (hspos : 0 < s) (hsq : s * s = M) (hs1000 : 1000 ≤ s) :
    s ≤ M / 2 := by
  have h2 : (2 : ℝ) ≤ s := by linarith
  have h : s * 2 ≤ s * s := mul_le_mul_of_nonneg_left h2 hspos.le
  linarith [h, hsq]

/-- `x ≤ M/d` from `x ≤ s`, `d ≤ s`, `M = s²`. -/
private lemma le_div_of_le_sqrt {M s x d : ℝ} (hspos : 0 < s) (hsq : s * s = M)
    (hd : 0 < d) (hxd : d ≤ s) (hx : x ≤ s) : x ≤ M / d := by
  have h1 : s * d ≤ s * s := mul_le_mul_of_nonneg_left hxd hspos.le
  have h2 : x * d ≤ s * d := mul_le_mul_of_nonneg_right hx hd.le
  rw [le_div_iff₀ hd]
  linarith [h1, h2, hsq]

/-- BAND `y₁ ≤ |Im w| ≤ √M` of the strip, for the pinned coordinate.

This combines with `Work.Pert.Pin.strip_high_pin` (heights `≥ Ξ + C (1 + log M)`) to give the full
strip: for `M ≥ Ms` one has `Ξ + C (1 + log M) ≤ √M`, so every `w` with `|w.re| ≤ 1` and
`|w.im| ≥ y₁` falls in one of the two bands.  So the cap `|w.im| ≤ √M` does NOT lose generality.

Route: the walk of length `n ≈ M + Re w` from the deep point `u = w - n ∈ Dstrip M Tb`, `Tb := √M`.
Two cases for the seed's orbit `f^j (τζ)`:
* while `F^j ζ ∈ Qm Ξ α`, the hypothesis `∀ z ∈ Qm Ξ α, tauC σ α z ∈ ball 0 rr` (plus the local
  Abel identity at `τ z`, where `f` is given by `f z = z + z (z-σ) u z`) puts the value in
  `ball 0 rr ⊆ L`;
* for the tail, the shadowing of the datum's walk `d.φ (u+j)` with the trap
  `Work.PertCrux.defect_le_of_trap`: the seed error `‖τζ - d.φ u‖` is `O(h/M³)` and the datum
  amplification over the `n`-step walk is `O(M²)` (`Work.PertCrux.f0_amp_uniform_K`, via
  `‖ζ - Xc d u‖ ≤ (Cdev·80/M + 4E)·‖ζ - c‖` with `ζ := Φm⁻¹ u`, `c := Xc d (-M)`, and the pin
  `Φm c = -M = Φ₀ c`), so the trap radius may be taken `R := c/√M` — this is why the cap `√M`
  matters: the room around `d.φ (u+j)` is `~1/|u+j| ≥ 1/√M`, whereas the *uncapped* band
  (`|w.im| ≤ M/160`) would force `R ≳ h/M` and the room `≲ 1/h` to clash near `h ≈ M`;
  take the Lipschitz constant from `Work.Pert.Ksub2.exists_lipschitzOn_of_compact` on a compact
  tube around the walk (which `Work.Pert.Ksub2.defect_le_fix`/`exists_shadow_set` supply inside
  `D₀`), and `δ₀` tiny (it is quantified after `M`) for the accumulated defect.

`Work.Pert.band_goodP` is the same conclusion with the *extra* hypothesis `4 ≤ R` and hence only
covers `D₀` thick enough at the walk; here `R` must be allowed to be `c/√M`, so do not route the
tail through `band_goodP`'s `hLtrap`/`hR4`.
-/
theorem strip_band_pin {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ : ℝ) (hΞ : 0 < Ξ)
    {rr : ℝ} (hrr : 0 < rr) (hrrD : Metric.closedBall (0 : ℂ) rr ⊆ D₀)
    {y₁ : ℝ} (hy₁ : d.η₀ < y₁) :
    ∃ Ms : ℝ, 0 < Ms ∧ ∀ M : ℝ, Ms ≤ M →
      ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ Metric.closedBall (0 : ℂ) rr ⊆ L ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f →
        DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) →
        MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) →
        ∀ Φm : ℂ → ℂ, MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α) →
          Work.Pert.Xc d (((-M : ℝ)) : ℂ) ∈ Work.Pert.Qm Ξ α →
          Φm (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) = (((-M : ℝ)) : ℂ) →
          ∀ w : ℂ, y₁ ≤ |w.im| → |w.re| ≤ 1 → |w.im| ≤ Real.sqrt M →
            w ∈ Work.Pert.DphiP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α) := by
  classical
  -- ## 0. the constants of the datum
  obtain ⟨Camp, hCamp1, hampA0⟩ := Work.Pert.Ksub2.f0_amp_band d hy₁
  obtain ⟨Csh, hCshpos, Msh, hMshpos, hXcSh0⟩ := Work.Pert.Ksub2.Xc_sharp_on_strip d
  obtain ⟨Cdv, hCdvpos, hdevA0⟩ := Work.PertCrux.dev_le_of_deriv_diff_le hF.2.2.2.2.1
  obtain ⟨Csd, hCsdpos, hseedA0⟩ := Work.PertCrux.tauC_tau0_close_of_far
  obtain ⟨r₀s, hr₀spos, hr₀sD, Csm0, hCsm0pos, hsmallA0⟩ := Work.Pert.small_of_nearOn hd
  obtain ⟨R₁, C₁, C₂r, hR₁pos, hC₁pos, hC₂rpos, hDE0⟩ := hF.2.2.2.2.1
  obtain ⟨hFm, ρm, Dm, hρmpos, hρm8, hDmnn, hFm0, hρmD, hfem, hFmd, hFld, hFbm⟩ :=
    Work.Pert.Ksub2.exists_model_data_full hd
  obtain ⟨Manch, hManchpos, hanch0⟩ := Work.Pert.Ksub2.anchor_at_scale d
  obtain ⟨MF0, hMF0pos, hF0nt0⟩ :=
    Work.Pert.Ksub2.F0f_near_translation_anchor (D := Dm) d hρmpos hρm8 hρmD hfem hFm0 hFmd
  obtain ⟨Mder, hMderpos, hTaud0⟩ := Work.Pert.Ksub2.anchor_scale_deriv d
  obtain ⟨R₀, hR₀pos, hwalkroom⟩ := walk_room d hd hy₁
  obtain ⟨Mlog, hMlogpos, hlogbound⟩ := eventually_log_le_sqrt Csh
  -- ## 1. normalised constants
  set Cdev : ℝ := max Cdv 1 with hCdevdef
  set Cseed : ℝ := max Csd 1 with hCseeddef
  set Csm : ℝ := max Csm0 1 with hCsmdef
  set C₂ : ℝ := max C₂r 1 with hC₂def
  set R₁' : ℝ := max R₁ 1 with hR₁def
  have hCdvCdev : Cdv ≤ Cdev := le_max_left _ _
  have hCdev1 : (1 : ℝ) ≤ Cdev := le_max_right _ _
  have hCdevpos : 0 < Cdev := lt_of_lt_of_le one_pos hCdev1
  have hCsdCseed : Csd ≤ Cseed := le_max_left _ _
  have hCseed1 : (1 : ℝ) ≤ Cseed := le_max_right _ _
  have hCseedpos : 0 < Cseed := lt_of_lt_of_le one_pos hCseed1
  have hCsm0Csm : Csm0 ≤ Csm := le_max_left _ _
  have hCsm1 : (1 : ℝ) ≤ Csm := le_max_right _ _
  have hCsmpos : 0 < Csm := lt_of_lt_of_le one_pos hCsm1
  have hC₂rC₂ : C₂r ≤ C₂ := le_max_left _ _
  have hC₂1 : (1 : ℝ) ≤ C₂ := le_max_right _ _
  have hR₁R₁' : R₁ ≤ R₁' := le_max_left _ _
  have hR₁'1 : (1 : ℝ) ≤ R₁' := le_max_right _ _
  set K₀ : ℝ := 40000 * (Camp * Cseed * Cdev) with hK₀def
  have hK₀pos : 0 < K₀ := by rw [hK₀def]; positivity
  -- ## 2. the threshold
  set Lthr : List ℝ := ([Mlog, Msh, Manch, MF0, Mder, y₁ ^ 2 + 1, (2 * Camp) ^ 2 + 1,
    (1000 * Cseed) ^ 2 + 1, (1000 * Cdev) ^ 2 + 1, (1000 * Csm) ^ 2 + 1,
    (1000 * Csh) ^ 2 + 1, (1000 * C₂) ^ 2 + 1, (1000 * R₁') ^ 2 + 1, (1000 * Ξ) ^ 2 + 1,
    (K₀ / R₀) ^ 2 + 1, (K₀ / 4) ^ 2 + 1, 32 / ρm + 4, (1000000 : ℝ)] : List ℝ) with hLthrdef
  set Ms : ℝ := Lthr.foldr max 1 with hMsdef
  have hMspos : 0 < Ms := lt_of_lt_of_le one_pos (by rw [hMsdef]; exact le_foldr_max)
  refine ⟨Ms, hMspos, ?_⟩
  intro M hM
  have hb : ∀ a ∈ Lthr, a ≤ M := by
    intro a ha
    have hM' : Lthr.foldr max 1 ≤ M := by rw [hMsdef] at hM; exact hM
    exact le_trans (foldr_max_ge ha) hM'
  set s : ℝ := Real.sqrt M with hsdef
  have hMbig : (1000000 : ℝ) ≤ M := hb _ (by simp [hLthrdef])
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hM1000 : (1000 : ℝ) ≤ M := by linarith
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hs2 : s ^ 2 = M := by rw [hsdef]; exact Real.sq_sqrt hMpos.le
  have hspos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hMpos
  have hMss : M = s * s := by rw [← hs2]; ring
  have hsq : s * s = M := by rw [← hs2]; ring
  -- ## 3. the constants are all `≤ s`
  have hsqrt_of_sq : ∀ {x : ℝ}, 0 ≤ x → x ^ 2 + 1 ≤ M → x ≤ s := by
    intro x hx h1
    have h2 : x ^ 2 ≤ s ^ 2 := by rw [hs2]; linarith
    by_contra hc
    push_neg at hc
    have h3 : 0 < x + s := by linarith
    have h4 : 0 < (x - s) * (x + s) := mul_pos (by linarith) h3
    nlinarith [h2, h4]
  have h2Camps : 2 * Camp ≤ s :=
    hsqrt_of_sq (by positivity) (hb _ (by simp [hLthrdef]))
  have hCamps : Camp ≤ s / 2 := by linarith
  have hCseeds : Cseed ≤ s := by
    have h := hsqrt_of_sq (x := 1000 * Cseed) (by positivity) (hb _ (by simp [hLthrdef]))
    linarith
  have hCdevs : Cdev ≤ s := by
    have h := hsqrt_of_sq (x := 1000 * Cdev) (by positivity) (hb _ (by simp [hLthrdef]))
    linarith
  have hCsms : Csm ≤ s := by
    have h := hsqrt_of_sq (x := 1000 * Csm) (by positivity) (hb _ (by simp [hLthrdef]))
    linarith
  have hCshs : Csh ≤ s := by
    have h := hsqrt_of_sq (x := 1000 * Csh) (by positivity) (hb _ (by simp [hLthrdef]))
    linarith
  have hC₂s : C₂ ≤ s := by
    have h := hsqrt_of_sq (x := 1000 * C₂) (by positivity) (hb _ (by simp [hLthrdef]))
    linarith
  have hR₁'s : R₁' ≤ s := by
    have h := hsqrt_of_sq (x := 1000 * R₁') (by positivity) (hb _ (by simp [hLthrdef]))
    linarith
  have hΞs : Ξ ≤ s := by
    have h := hsqrt_of_sq (x := 1000 * Ξ) (by positivity) (hb _ (by simp [hLthrdef]))
    linarith
  have hy₁s : y₁ ≤ s := by
    have h1 : |y₁| ≤ s := hsqrt_of_sq (abs_nonneg y₁) (hb _ (by simp [hLthrdef]))
    linarith [le_abs_self y₁]
  have hK₀R₀s : K₀ / R₀ ≤ s :=
    hsqrt_of_sq (div_nonneg hK₀pos.le hR₀pos.le) (hb _ (by simp [hLthrdef]))
  have hK₀4s : K₀ / 4 ≤ s := hsqrt_of_sq (by positivity) (hb _ (by simp [hLthrdef]))
  have hρmM2 : 32 / ρm + 4 ≤ M := hb _ (by simp [hLthrdef])
  have hs1000 : 1000 ≤ s := by
    have h1 : (1000 : ℝ) ^ 2 ≤ s ^ 2 := by rw [hs2]; linarith
    nlinarith [h1, hspos, sq_nonneg (s - 1000)]
  have hs1 : (1 : ℝ) ≤ s := by linarith
  have hhalf : s ≤ M / 2 := sqrt_le_half hspos hsq hs1000
  -- ## 4. the per-`M` quantities
  set Tb : ℝ := s with hTbdef
  set Xdev : ℝ := Csh * (1 + Real.log M) with hXdevdef
  have hXdev_le : Xdev ≤ s := by
    have h1 : Csh * (1 + Real.log M) ≤ Real.sqrt M :=
      hlogbound M (hb Mlog (by simp [hLthrdef]))
    have h2 : s = Real.sqrt M := hsdef
    linarith [h1, h2.le, h2.ge]
  have hXdev0 : 0 ≤ Xdev := by
    have h1 : (0 : ℝ) ≤ Real.log M := Real.log_nonneg hM1
    have h2 : Xdev = Csh * (1 + Real.log M) := hXdevdef
    rw [h2]
    positivity
  set R : ℝ := min (R₀ / 2) (K₀ / s) with hRdef
  have hRpos : 0 < R := lt_min (by linarith) (div_pos hK₀pos hspos)
  have hRtrap : K₀ / (2 * s) ≤ R := by
    rcases le_total (K₀ / s) (R₀ / 2) with h | h
    · rw [hRdef, min_eq_right h]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hK₀pos, hspos]
    · rw [hRdef, min_eq_left h]
      have h2 : K₀ ≤ R₀ * s := by
        have h3 : K₀ / R₀ ≤ s := hK₀R₀s
        rw [div_le_iff₀ hR₀pos] at h3
        linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h2]
  have hR4 : R ≤ 4 := by
    have h1 : K₀ / s ≤ 4 := by
      rw [div_le_iff₀ hspos]
      linarith [hK₀4s]
    exact le_trans (min_le_right _ _) h1
  have hRle : 2 * R ≤ R₀ := by
    have h1 : min (R₀ / 2) (K₀ / s) ≤ R₀ / 2 := min_le_left _ _
    rw [hRdef]; linarith
  have h160 : Real.sqrt M ≤ M / 160 := by
    have h1 : s ≤ M / 160 := le_div_of_le_sqrt hspos hsq (by norm_num) (by linarith) (by linarith)
    have h2 : s = Real.sqrt M := hsdef
    linarith [h1, h2.le, h2.ge]
  -- ## 5. the walk region and the tube around its `φ`-image
  set c : ℂ := Work.Pert.Xc d (((-M : ℝ)) : ℂ) with hcdef
  set Kwalk : Set ℂ := {q : ℂ | -M - 1 ≤ q.re} ∩ ({q : ℂ | q.re ≤ 3} ∩
    ({q : ℂ | y₁ ≤ |q.im|} ∩ {q : ℂ | |q.im| ≤ Tb})) with hKwalkdef
  have hceilM : ((⌈M⌉₊ : ℕ) : ℝ) < M + 1 := Nat.ceil_lt_add_one hMpos.le
  have hKwalk_sub : Kwalk ⊆ Metric.closedBall (0 : ℂ) (M + 4 + Tb) := by
    intro q hq
    have h1 : -M - 1 ≤ q.re := hq.1
    have h2 : q.re ≤ 3 := hq.2.1
    have h4 : |q.im| ≤ Tb := hq.2.2.2
    rw [Metric.mem_closedBall, dist_zero_right]
    have h5 : |q.re| ≤ M + 1 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have h6 : ‖q‖ ≤ |q.re| + |q.im| := Complex.norm_le_abs_re_add_abs_im q
    linarith [abs_nonneg q.im]
  have hKwalk_closed : IsClosed Kwalk := by
    rw [hKwalkdef]
    exact (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im.abs).inter
          (isClosed_le Complex.continuous_im.abs continuous_const)))
  have hKwalkc : IsCompact Kwalk :=
    (isCompact_closedBall (0 : ℂ) (M + 4 + Tb)).of_isClosed_subset hKwalk_closed hKwalk_sub
  have hKwalkDE : Kwalk ⊆ d.DE := by
    intro q hq
    have h3 : y₁ ≤ |q.im| := hq.2.2.1
    exact d.ends_sub q (by linarith [h3, hy₁])
  set W : Set ℂ := d.φ '' Kwalk with hWdef
  have hWc : IsCompact W :=
    hKwalkc.image_of_continuousOn (d.φ_holo.continuousOn.mono (fun z hz => (hKwalkDE hz).1))
  have hWcth : Metric.cthickening R W = ⋃ q ∈ W, Metric.closedBall q R :=
    hWc.cthickening_eq_biUnion_closedBall hRpos.le
  have hcthD₀ : Metric.cthickening R W ⊆ D₀ := by
    intro z hz
    rw [hWcth] at hz
    obtain ⟨q, hqW, hzq⟩ := mem_iUnion₂.mp hz
    obtain ⟨q', hq'K, rfl⟩ := hqW
    have k1 : -M - 1 ≤ q'.re := hq'K.1
    have k2 : q'.re ≤ 3 := hq'K.2.1
    have k3 : y₁ ≤ |q'.im| := hq'K.2.2.1
    have hzq' : dist z (d.φ q') ≤ R := by rwa [Metric.mem_closedBall] at hzq
    exact hwalkroom M hMpos q' k1 k2 k3 (by
      rw [Metric.mem_closedBall]
      linarith [hzq', hRle])
  -- ## 6. the defect on the anchor ball
  have hXcM : ‖c - (((-M : ℝ)) : ℂ)‖ ≤ Xdev := by
    have h1 := (hXcSh0 M (hb Msh (by simp [hLthrdef])) Tb h160).1
    have h2 : Xdev = Csh * (1 + Real.log M) := hXdevdef
    rw [h2]
    exact h1
  have hcs : ‖c‖ ≤ M + s := by
    have h1 : ‖c‖ ≤ ‖c - (((-M : ℝ)) : ℂ)‖ + ‖(((-M : ℝ)) : ℂ)‖ := by
      have h := norm_add_le (c - (((-M : ℝ)) : ℂ)) ((((-M : ℝ)) : ℂ))
      rw [sub_add_cancel] at h; exact h
    have h2 : ‖(((-M : ℝ)) : ℂ)‖ = M := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hMpos.le]
    linarith [h1, h2, hXcM, hXdev_le]
  have hcs_low : M - s ≤ ‖c‖ := by
    have h0 : ‖(((-M : ℝ)) : ℂ)‖ = M := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hMpos.le]
    have h := abs_norm_sub_norm_le c (((-M : ℝ)) : ℂ)
    rw [h0] at h
    have h2 := (abs_le.mp h).1
    linarith [h2, hXcM, hXdev_le]
  obtain ⟨Ld, hLdc, hLdD, δd, ηd, hδdpos, hηdpos, hdefect0⟩ :=
    Work.Pert.Pin.defect_le_of_norm_bound hd (ξ := 1) one_pos
      (Kd := Metric.ball c (M / 40)) (Mb := 2 * M)
      (fun z hz => by
        rw [Metric.mem_ball] at hz
        have h1 : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
          have h := norm_add_le c (z - c); rw [add_sub_cancel] at h; exact h
        have h2 : ‖z - c‖ < M / 40 := by rwa [dist_eq_norm] at hz
        have h3 : M / 40 ≤ M / 2 := by linarith
        linarith [h1, h2, hcs, hXdev_le, hMpos])
      (fun z hz => by
        rw [Metric.mem_ball] at hz
        constructor
        · intro b hb
          simp at hb
        · intro b hb
          rw [Option.mem_some_iff] at hb
          subst hb
          have h1 : ‖z - c‖ < M / 40 := by rwa [dist_eq_norm] at hz
          have h2 : z.re ≤ c.re + M / 40 := by
            have h3 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
            have h4 : (z - c).re = z.re - c.re := by simp
            rw [h4] at h3
            have h5 := (abs_le.mp (le_of_lt (lt_of_le_of_lt h3 h1))).2
            linarith
          have h3 : c.re ≤ -M + Xdev := by
            have h4 : |(c - (((-M : ℝ)) : ℂ)).re| ≤ ‖c - (((-M : ℝ)) : ℂ)‖ :=
              Complex.abs_re_le_norm _
            have h5 : (c - (((-M : ℝ)) : ℂ)).re = c.re + M := by simp
            rw [h5] at h4
            have h6 := (abs_le.mp (le_trans h4 hXcM)).2
            linarith
          have h9 : z.re + 1 < 0 := by linarith [h2, h3, hXdev_le, hhalf]
          have hgoal : (z - (-(1 : ℂ))).re < |(z - (-(1 : ℂ))).im| := by
            have hz1 : (z - (-(1 : ℂ))).re = z.re + 1 := by
              rw [Complex.sub_re]; norm_num
            have hz2 : (z - (-(1 : ℂ))).im = z.im := by
              rw [Complex.sub_im]; norm_num
            rw [hz1, hz2]
            linarith [h9, abs_nonneg z.im]
          exact hgoal)
      (fun z hz => by
        rw [Metric.mem_ball] at hz
        have h1 : ‖c‖ ≤ ‖z‖ + ‖z - c‖ := by
          have h := norm_add_le z (c - z)
          rw [add_sub_cancel] at h
          rwa [norm_sub_rev c z] at h
        have h2 : ‖z - c‖ < M / 40 := by rwa [dist_eq_norm] at hz
        have h3 : M - s - M / 40 ≤ ‖z‖ := by linarith [h1, h2, hcs_low]
        have h4 : 1 < M - s - M / 40 := by linarith [hhalf, hM1000]
        linarith)
      hρmpos hρm8 hDmnn hfem hFmd hFld hFbm hρmD
      (fun z hz => by
        rw [Metric.mem_ball] at hz
        have h1 : ‖c‖ ≤ ‖z‖ + ‖z - c‖ := by
          have h := norm_add_le z (c - z)
          rw [add_sub_cancel] at h
          rwa [norm_sub_rev c z] at h
        have h2 : ‖z - c‖ < M / 40 := by rwa [dist_eq_norm] at hz
        have h3 : M - s - M / 40 ≤ ‖z‖ := by linarith [h1, h2, hcs_low]
        have h4 : 1 < ‖z‖ := by linarith [h3, hhalf, hM1000]
        have h6 : 8 / ρm ≤ ‖z‖ := by
          have h7 : 8 / ρm ≤ M / 4 := by
            have h8 : 32 / ρm ≤ M := by linarith [hρmM2]
            rw [div_le_div_iff₀ hρmpos (by norm_num : (0 : ℝ) < 4)]
            rw [div_le_iff₀ hρmpos] at h8
            linarith [h8]
          have h9 : M / 4 ≤ M - s - M / 40 := by linarith [hhalf, hM1000]
          linarith [h7, h9]
        have h7 : 1 / ‖z‖ ≤ ρm / 8 := by
          rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < ‖z‖) (by norm_num : (0 : ℝ) < 8)]
          rw [div_le_iff₀ hρmpos] at h6
          rw [mul_comm ‖z‖ ρm] at h6
          linarith [h6]
        have h5 : ‖MandelDim.tau0 z‖ = 1 / ‖z‖ := by
          rw [MandelDim.tau0, norm_div, norm_neg, norm_one]
        rw [h5]
        exact h7)
      (1 / M ^ 2) (by positivity)
  have hEnn : (0 : ℝ) ≤ 1 / M ^ 2 := by positivity
  -- ## 7. the set `L` and the Lipschitz constant
  set L : Set ℂ := Metric.cthickening R W ∪ Ld ∪ Metric.closedBall (0 : ℂ) rr with hLdef
  have hLc : IsCompact L := by
    rw [hLdef]
    exact ((hWc.cthickening (r := R)).union hLdc).union (isCompact_closedBall 0 rr)
  have hLD₀ : L ⊆ D₀ := by
    rw [hLdef]
    intro z hz
    rcases hz with (hz | hz) | hz
    · exact hcthD₀ hz
    · exact hLdD hz
    · exact hrrD hz
  have hLdL : Ld ⊆ L := by rw [hLdef]; intro z hz; exact Or.inl (Or.inr hz)
  have hLrr : Metric.closedBall (0 : ℂ) rr ⊆ L := by
    rw [hLdef]; intro z hz; exact Or.inr hz
  obtain ⟨L₀, hL₀nn, hL₀lip⟩ :=
    Work.Pert.Ksub2.exists_lipschitzOn_of_compact hd.1 hLc hLD₀ hd.2.2.1
  set Lf : ℝ := max L₀ 1 with hLfdef
  have hLf1 : (1 : ℝ) ≤ Lf := le_max_right _ _
  -- ## 8. the smallness parameters
  set mρ : ℝ := min (min r₀s rr) 1 / 2 with hmρdef
  have hmρpos : 0 < mρ := by
    rw [hmρdef]; exact div_pos (lt_min (lt_min hr₀spos hrr) one_pos) two_pos
  have hmρr₀ : mρ ≤ r₀s := by
    rw [hmρdef]
    have h1 : min (min r₀s rr) 1 ≤ r₀s := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hmρrr : mρ ≤ rr := by
    rw [hmρdef]
    have h1 : min (min r₀s rr) 1 ≤ rr := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  set bα : ℝ := min (min (1 / (32 * (M + 2))) (R / (24 * Cseed * Camp * M * M))) ηd
    with hbαdef
  have hbαpos : 0 < bα := by
    rw [hbαdef]
    exact lt_min (lt_min (by positivity) (by positivity)) hηdpos
  set bu : ℝ := min (1 / 4) (min ηd (R / (24 * Cseed * Camp * M))) with hbudef
  have hbupos : 0 < bu := by
    rw [hbudef]
    exact lt_min (by norm_num) (lt_min hηdpos (by positivity))
  set dA : ℝ := min (mρ / 2) δd with hdAdef
  have hdApos : 0 < dA := by rw [hdAdef]; exact lt_min (by linarith) hδdpos
  set dB : ℝ := min (mρ * bα / Csm)
    (min (bu * mρ ^ 2 / (2 * Csm)) (bu * mρ * rr / (2 * Csm))) with hdBdef
  have hdBpos : 0 < dB := by
    rw [hdBdef]
    refine lt_min (by positivity) (lt_min (by positivity) (by positivity))
  set dC : ℝ := min dA dB with hdCdef
  have hdCpos : 0 < dC := by rw [hdCdef]; exact lt_min hdApos hdBpos
  set dP : ℝ := R / (4 * (((⌈M⌉₊ + 2 : ℕ) : ℝ)) * Lf ^ (⌈M⌉₊ + 2)) with hdPdef
  have hdPpos : 0 < dP := by
    rw [hdPdef]
    have h1 : (0 : ℝ) < Lf ^ (⌈M⌉₊ + 2) := by positivity
    have h2 : (0 : ℝ) < (((⌈M⌉₊ + 2 : ℕ) : ℝ)) := by positivity
    positivity
  set δ₀ : ℝ := min dC dP with hδ₀def
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀def]; exact lt_min hdCpos hdPpos
  have hδ₀2 : 2 * δ₀ ≤ mρ := by
    have h1 : δ₀ ≤ mρ / 2 := le_trans (min_le_left dC dP)
      (le_trans (min_le_left dA dB) (min_le_left (mρ / 2) δd))
    linarith
  have hδ₀d : δ₀ ≤ δd := le_trans (min_le_left dC dP)
    (le_trans (min_le_left dA dB) (min_le_right (mρ / 2) δd))
  have hδ₀α : Csm * δ₀ / mρ ≤ bα := by
    have h1 : δ₀ ≤ mρ * bα / Csm := le_trans (min_le_left dC dP)
      (le_trans (min_le_right dA dB) (min_le_left (mρ * bα / Csm) (min _ _)))
    rw [div_le_iff₀ hmρpos]
    have h2 : Csm * δ₀ ≤ Csm * (mρ * bα / Csm) := mul_le_mul_of_nonneg_left h1 hCsmpos.le
    have h3 : Csm * (mρ * bα / Csm) = mρ * bα := by field_simp
    linarith [h2, h3.le, h3.ge]
  have hδ₀u : Csm * (δ₀ / mρ ^ 2 + δ₀ / (mρ * rr)) ≤ bu := by
    have e1 : δ₀ ≤ dB := le_trans (min_le_left dC dP) (min_le_right dA dB)
    have e2 : dB ≤ min (bu * mρ ^ 2 / (2 * Csm)) (bu * mρ * rr / (2 * Csm)) := by
      rw [hdBdef]; exact min_le_right _ _
    have h1 : δ₀ ≤ bu * mρ ^ 2 / (2 * Csm) :=
      le_trans e1 (le_trans e2 (min_le_left _ _))
    have h2 : δ₀ ≤ bu * mρ * rr / (2 * Csm) :=
      le_trans e1 (le_trans e2 (min_le_right _ _))
    have h3 : Csm * (δ₀ / mρ ^ 2) ≤ bu / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < mρ ^ 2)]
      have h4 : Csm * δ₀ ≤ Csm * (bu * mρ ^ 2 / (2 * Csm)) :=
        mul_le_mul_of_nonneg_left h1 hCsmpos.le
      have h5 : Csm * (bu * mρ ^ 2 / (2 * Csm)) = bu * mρ ^ 2 / 2 := by field_simp
      linarith [h4, h5.le, h5.ge]
    have h6 : Csm * (δ₀ / (mρ * rr)) ≤ bu / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < mρ * rr)]
      have h4 : Csm * δ₀ ≤ Csm * (bu * mρ * rr / (2 * Csm)) :=
        mul_le_mul_of_nonneg_left h2 hCsmpos.le
      have h5 : Csm * (bu * mρ * rr / (2 * Csm)) = bu * (mρ * rr) / 2 := by field_simp
      linarith [h4, h5.le, h5.ge]
    have h7 : Csm * (δ₀ / mρ ^ 2 + δ₀ / (mρ * rr))
        = Csm * (δ₀ / mρ ^ 2) + Csm * (δ₀ / (mρ * rr)) := by ring
    linarith [h7.le, h7.ge, h3, h6]
  have hδ₀trap : δ₀ * (((⌈M⌉₊ + 2 : ℕ) : ℝ)) * Lf ^ (⌈M⌉₊ + 2) ≤ R / 4 := by
    have h1 : δ₀ ≤ dP := min_le_right dC dP
    have h2 : (0 : ℝ) < (((⌈M⌉₊ + 2 : ℕ) : ℝ)) := by positivity
    have h3 : (0 : ℝ) < Lf ^ (⌈M⌉₊ + 2) := by positivity
    have h5 : dP * (((⌈M⌉₊ + 2 : ℕ) : ℝ)) * Lf ^ (⌈M⌉₊ + 2) = R / 4 := by
      rw [hdPdef]; field_simp
    calc δ₀ * (((⌈M⌉₊ + 2 : ℕ) : ℝ)) * Lf ^ (⌈M⌉₊ + 2)
        ≤ dP * (((⌈M⌉₊ + 2 : ℕ) : ℝ)) * Lf ^ (⌈M⌉₊ + 2) := by
          have h6 := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h1 h2.le) h3.le
          linarith [h6]
      _ = R / 4 := h5
  -- ## 9. the numerical hypotheses
  have hXc40 : 2 * Xdev + 1 + Tb < M / 40 := by
    have h2 : 3 * s + 1 ≤ 4 * s := by linarith
    have h3 : 4 * s < M / 40 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 40)]
      have h4 : (160 : ℝ) * s < s * s := mul_lt_mul_of_pos_right (by linarith) hspos
      linarith [h4, hsq]
    have h5 : 2 * Xdev + 1 + Tb ≤ 3 * s + 1 := by linarith [hXdev_le]
    linarith
  have hXc80 : 2 * Xdev + 1 + Tb + Xdev < M / 80 := by
    have h2 : 4 * s + 1 ≤ 5 * s := by linarith
    have h3 : 5 * s < M / 80 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 80)]
      have h4 : (400 : ℝ) * s < s * s := mul_lt_mul_of_pos_right (by linarith) hspos
      linarith [h4, hsq]
    have h5 : 2 * Xdev + 1 + Tb + Xdev ≤ 4 * s + 1 := by linarith [hXdev_le]
    linarith
  have hXc8 : Xdev + (1 + Tb) + Xdev ≤ M / 8 := by
    have h2 : 4 * s ≤ M / 8 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      have h4 : (32 : ℝ) * s ≤ s * s :=
        mul_le_mul_of_nonneg_right (by linarith : (32 : ℝ) ≤ s) hspos.le
      linarith [h4, hsq]
    have h5 : Xdev + (1 + Tb) + Xdev ≤ 4 * s := by linarith [hXdev_le, hs1]
    linarith
  have hCampTb : Camp * (1 + Tb) ≤ M := by
    have h1 : Camp * (1 + s) ≤ (s / 2) * (1 + s) :=
      mul_le_mul_of_nonneg_right hCamps (by linarith)
    have h2 : (s / 2) * (1 + s) ≤ s * s := by nlinarith [hs1]
    linarith [h1, h2, hsq]
  have hCdevM : Cdev ≤ M / 80 := le_div_of_le_sqrt hspos hsq (by norm_num) (by linarith) hCdevs
  have hC₂M : 64 * C₂ ≤ M := by
    have h1 : 64 * C₂ ≤ 64 * s := mul_le_mul_of_nonneg_left hC₂s (by norm_num)
    have h2 : 64 * s ≤ s * s := mul_le_mul_of_nonneg_right (by linarith : (64 : ℝ) ≤ s) hspos.le
    linarith [h1, h2, hsq]
  have hR₁M : R₁' ≤ M / 8 := le_div_of_le_sqrt hspos hsq (by norm_num) (by linarith) hR₁'s
  have hM8 : (8 : ℝ) ≤ M := by linarith
  have hMΞ : 8 * Ξ + 8 ≤ M := by
    have h1 : 8 * Ξ ≤ 8 * s := mul_le_mul_of_nonneg_left hΞs (by norm_num)
    have h2 : 8 * s + 8 ≤ 9 * s := by linarith [hs1]
    have h3 : 9 * s ≤ s * s := mul_le_mul_of_nonneg_right (by linarith : (9 : ℝ) ≤ s) hspos.le
    linarith [h1, h2, h3, hsq]
  have hXdevM : Xdev ≤ M / 320 := le_div_of_le_sqrt hspos hsq (by norm_num) (by linarith) hXdev_le
  have hTbM : Tb ≤ M / 160 := by
    have h2 : s ≤ M / 160 := le_div_of_le_sqrt hspos hsq (by norm_num) (by linarith) (by linarith)
    linarith [h2]
  have hy₁Tb : y₁ ≤ Tb := hy₁s
  have hTb0 : 0 ≤ Tb := hspos.le
  have harith := band_dev_arith hspos hs1 hs1000 hMpos hMss hXdev_le rfl hCdevpos.le
    hCdev1 hCdevs hCseedpos hCamp1 rfl hRtrap rfl
  have hdevcov := harith.1
  have hdevR := harith.2
  -- ## 10. the auxiliary hypotheses of the band lemma
  have hsmallA : ∀ {f : ℂ → ℂ} {Df : Set ℂ} {ρ δ₀' : ℝ} {u : ℂ → ℂ} {σ : ℂ},
      0 < ρ → ρ ≤ r₀s → 0 < δ₀' → 2 * δ₀' ≤ ρ → 0 < rr →
      MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) ρ) δ₀' → f 0 = 0 →
      DifferentiableOn ℂ u (Metric.ball 0 rr) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
      ‖u 0 - 1‖ ≤ Csm * (δ₀' / ρ ^ 2 + δ₀' / (ρ * rr)) ∧ ‖σ‖ ≤ Csm * δ₀' / ρ ∧
        ‖MandelDim.rotOf f‖ ≤ Csm * δ₀' / ρ := by
    intro f Df ρ δ₀' u σ h1 h2 h3 h4 h5 hN hf0 hud hub hform
    obtain ⟨e1, e2, e3⟩ := hsmallA0 h1 h2 h3 h4 h5 hN hf0 hud hub hform
    have h6 : (0 : ℝ) ≤ δ₀' / ρ ^ 2 + δ₀' / (ρ * rr) := by positivity
    have h7 : (0 : ℝ) ≤ δ₀' / ρ := by positivity
    have h8 : Csm0 * (δ₀' / ρ ^ 2 + δ₀' / (ρ * rr)) ≤ Csm * (δ₀' / ρ ^ 2 + δ₀' / (ρ * rr)) :=
      mul_le_mul_of_nonneg_right hCsm0Csm h6
    have h9 : Csm0 * δ₀' / ρ ≤ Csm * δ₀' / ρ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCsm0Csm (le_of_lt h3)) h1.le
    exact ⟨le_trans e1 h8, le_trans e2 h9, le_trans e3 h9⟩
  have hdevA : ∀ {F F₀ Φ Φ₀ : ℂ → ℂ} {c' : ℂ} {R' E' : ℝ}, Cdev ≤ R' → 0 ≤ E' →
      DifferentiableOn ℂ F (Metric.ball c' (2 * R')) →
      DifferentiableOn ℂ F₀ (Metric.ball c' (2 * R')) →
      MandelDim.IsFatouCoordOn F Φ (Metric.ball c' (2 * R')) →
      MandelDim.IsFatouCoordOn F₀ Φ₀ (Metric.ball c' (2 * R')) →
      (∀ w ∈ Metric.ball c' (2 * R'), ‖F w - (w + 1)‖ < 1 / 4) →
      (∀ w ∈ Metric.ball c' (2 * R'), ‖F₀ w - (w + 1)‖ < 1 / 4) →
      (∀ w ∈ Metric.ball c' (2 * R'), ‖F w - F₀ w‖ ≤ E') → Φ c' = Φ₀ c' →
      ∀ z ∈ Metric.ball c' R', ‖Φ z - Φ₀ z‖ ≤ (Cdev / R' + 4 * E') * ‖z - c'‖ := by
    intro F F₀ Φ Φ₀ c' R' E' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    intro z hz
    have hRpos : 0 < R' := lt_of_lt_of_le one_pos (le_trans hCdev1 h1)
    refine le_trans (hdevA0 (le_trans hCdvCdev h1) h2 h3 h4 h5 h6 h7 h8 h9 h10 z hz) ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h11 : Cdv / R' ≤ Cdev / R' := div_le_div_of_nonneg_right hCdvCdev hRpos.le
    linarith [h11]
  have hseedA : ∀ {u : ℂ → ℂ} {σ α ς y : ℂ} {M' dev : ℝ}, 0 < M' → 1 ≤ M' → 0 ≤ dev →
      M' / 2 ≤ ‖ς‖ → M' / 2 ≤ ‖y‖ → ‖ς - y‖ ≤ 2 * dev → 2 * Real.pi * ‖α‖ * ‖ς‖ ≤ 1 / 2 →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) → α ≠ 0 →
      ‖u 0 - 1‖ ≤ 1 / 4 → ‖α‖ ≤ 1 / 4 →
      ‖Work.Pert.tauC σ α ς - MandelDim.tau0 y‖
        ≤ Cseed * (dev / (M' * M') + ‖u 0 - 1‖ / M' + ‖α‖) := by
    intro u σ α ς y M' dev h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    refine le_trans (hseedA0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    linarith [hCsdCseed]
  have hDE : ∀ (Φ v : ℂ → ℂ) (z₀ : ℂ) (R' : ℝ), R₁' ≤ R' →
      DifferentiableOn ℂ Φ (Metric.ball z₀ R') → Set.InjOn Φ (Metric.ball z₀ R') →
      DifferentiableOn ℂ v (Metric.ball z₀ R') → (∀ z ∈ Metric.ball z₀ R', ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z₀ R', z + v z ∈ Metric.ball z₀ R' → Φ (z + v z) = Φ z + 1) →
      ‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₂ / R' := by
    intro Φ v z₀ R' h1 h2 h3 h4 h5 h6
    have hRpos : 0 < R' := lt_of_lt_of_le one_pos (le_trans hR₁'1 h1)
    refine le_trans ((hDE0 Φ v z₀ R' (le_trans hR₁R₁' h1) h2 h3 h4 h5 h6)).2 ?_
    have h7 : C₂r / R' ≤ C₂ / R' := div_le_div_of_nonneg_right hC₂rC₂ hRpos.le
    linarith [h7]
  have hXcsv : ∀ v ∈ Work.Pert.Dstrip M Tb, ‖Work.Pert.Xc d v - v‖ ≤ Xdev := by
    intro v hv
    have h1 := (hXcSh0 M (hb Msh (by simp [hLthrdef])) Tb h160).2 v hv
    have h2 : Xdev = Csh * (1 + Real.log M) := hXdevdef
    rw [h2]
    exact h1
  have hTaud : ∀ u ∈ Metric.ball (((-M : ℝ)) : ℂ) (M / 4),
      ‖deriv (fun v : ℂ => MandelDim.tau0 (d.φ v)) u - 1‖ ≤ 1 / 2 :=
    fun u hu => hTaud0 M (hb Mder (by simp [hLthrdef])) u hu
  obtain ⟨Φ₀, hΦ₀, hΦ₀data, hΦ₀pin, -⟩ :=
    hanch0 M (hb Manch (by simp [hLthrdef]))
  have hΦ₀inv : ∀ ζ ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) (M / 40),
      Work.Pert.Xc d (Φ₀ ζ) = ζ := fun ζ hζ => (hΦ₀data ζ hζ).1
  have hΦ₀dev : ∀ ζ ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) (M / 40),
      ‖Φ₀ ζ - ζ‖ ≤ M / 40 := fun ζ hζ => (hΦ₀data ζ hζ).2
  obtain ⟨hF0d, hF0nt⟩ := hF0nt0 M (hb MF0 (by simp [hLthrdef]))
  -- ## 11. the conclusion
  refine ⟨L, hLc, hLD₀, hLrr, δ₀, hδ₀pos, ?_⟩
  intro f Df u σ α hNear hf0 hInF1 hα hud hub hform hnorm hτQ hQAdm hNT Φm hΦm hXcm hpin w hw1 hw2
    hw3
  have hdefect : ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ),
      MandelDim.NearOn f₀ f Df Ld δd → f 0 = 0 → MandelDim.InF1 α → ‖α‖ ≤ ηd → 0 < rr →
      DifferentiableOn ℂ u (Metric.ball 0 rr) →
      (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
      (∀ w ∈ Metric.ball c (M / 40), Work.Pert.tauC σ α w ∈ Metric.ball 0 rr) →
      ‖u 0 - 1‖ ≤ ηd →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
      ∀ w ∈ Metric.ball c (M / 40),
        ‖Work.Pert.liftF u σ α w - Work.Pert.F0f f₀ w‖ ≤ 1 / M ^ 2 := by
    intro f' Df' u' σ' α' hN hf' hInF1' hαη' hrr' hud' hub' hform' hτQ' hu0' hnorm' w' hw'
    have hαne : α' ≠ 0 := by
      intro h0
      rw [h0] at hInF1'
      simp [MandelDim.InF1] at hInF1'
    exact hdefect0 f' Df' rr u' σ' α' hN hf' hαne hαη' hrr' hud' hub' hform' hτQ' hu0' hnorm'
      w' hw'
  have hwalkmem : ∀ (v : ℂ), v ∈ Work.Pert.Dstrip M Tb → v.im = w.im → ∀ j : ℕ,
      j ≤ ⌈M⌉₊ + 2 → v + (j : ℂ) ∈ Kwalk := by
    intro v hv hvim j hj
    rw [hKwalkdef]
    have h1 : v.re ≤ -M := hv.2.1
    have h2 : -M - 1 ≤ v.re := hv.1
    have h3 : |v.im| ≤ Tb := hv.2.2
    have h4 : y₁ ≤ |v.im| := by rw [hvim]; exact hw1
    have h5 : v.re + (j : ℝ) ≤ 3 := by
      have h6 : (j : ℝ) ≤ (⌈M⌉₊ : ℝ) + 2 := by
        have h7 : (j : ℝ) ≤ ((⌈M⌉₊ + 2 : ℕ) : ℝ) := by exact_mod_cast hj
        push_cast at h7 ⊢
        linarith
      linarith [h1, h6, hceilM]
    have e1 : (v + (j : ℂ)).re = v.re + (j : ℝ) := by simp
    have e2 : (v + (j : ℂ)).im = v.im := by simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · change -M - 1 ≤ (v + (j : ℂ)).re
      rw [e1]; linarith [h2]
    · change (v + (j : ℂ)).re ≤ 3
      rw [e1]; linarith [h5]
    · change y₁ ≤ |(v + (j : ℂ)).im|
      rw [e2]; linarith [h4]
    · change |(v + (j : ℂ)).im| ≤ Tb
      rw [e2]; linarith [h3]
  have hLlip : ∀ j : ℕ, j ≤ ⌈M⌉₊ + 2 → ∀ v ∈ Work.Pert.Dstrip M Tb, v.im = w.im →
      ∀ x y : ℂ, ‖x - d.φ (v + (j : ℂ))‖ ≤ R → ‖y - d.φ (v + (j : ℂ))‖ ≤ R →
        ‖f₀ x - f₀ y‖ ≤ Lf * ‖x - y‖ := by
    intro j hj v hv hvim x y hx hy
    have hq := hwalkmem v hv hvim j hj
    have hxL : x ∈ L := by
      rw [hLdef]
      refine Or.inl (Or.inl (Metric.mem_cthickening_of_dist_le x (d.φ (v + (j : ℂ))) R W
        ⟨v + (j : ℂ), hq, rfl⟩ ?_))
      rw [dist_eq_norm]; exact hx
    have hyL : y ∈ L := by
      rw [hLdef]
      refine Or.inl (Or.inl (Metric.mem_cthickening_of_dist_le y (d.φ (v + (j : ℂ))) R W
        ⟨v + (j : ℂ), hq, rfl⟩ ?_))
      rw [dist_eq_norm]; exact hy
    exact le_trans (hL₀lip x hxL y hyL)
      (mul_le_mul_of_nonneg_right (le_max_left L₀ 1) (norm_nonneg _))
  have hLtrap : ∀ j : ℕ, j ≤ ⌈M⌉₊ + 2 → ∀ v ∈ Work.Pert.Dstrip M Tb, v.im = w.im →
      Metric.closedBall (d.φ (v + (j : ℂ))) R ⊆ L := by
    intro j hj v hv hvim z hz
    have hq := hwalkmem v hv hvim j hj
    rw [hLdef]
    refine Or.inl (Or.inl (Metric.mem_cthickening_of_dist_le z (d.φ (v + (j : ℂ))) R W
      ⟨v + (j : ℂ), hq, rfl⟩ ?_))
    have hz1 : ‖z - d.φ (v + (j : ℂ))‖ ≤ R := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      exact hz
    rw [dist_eq_norm]
    exact hz1
  have hgood := band_goodP_sqrt_im d hΞ hrr hy₁ hy₁Tb hTb0 hXdev0 hCdevpos hCseedpos hCseed1
    hCamp1 hLf1 hRpos hR4 hr₀spos hCsmpos hmρpos hmρr₀ hmρrr hM8 hMΞ hTbM hXdevM hXc40 hXc80 hXc8
    hCampTb hCdevM hC₂M hR₁M hDE hEnn hδ₀pos hηdpos hδdpos hδ₀2 hδ₀α hδ₀u hdevcov hdevR hδ₀d hδ₀trap
    hsmallA hdevA hseedA hampA0
    hΦ₀ hΦ₀inv hΦ₀dev hΦ₀pin hF0d hF0nt hXcsv hXcM hTaud hdefect hLdL hLrr hLlip hLtrap
    hNear hf0 hInF1 hα hud hub hform hnorm hτQ hNT hΦm hpin hw2 hw1 hw3
  exact hgood

end Work.Pert.Pin
