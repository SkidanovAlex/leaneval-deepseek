import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.aw_data
import Submission.Work.OddVolterra.Smooth.Q_regularity
import Submission.Work.OddVolterra.Smooth.E1_E2_regularity
import Submission.Work.OddVolterra.Abel.abel_transform_diff
import Submission.Work.OddVolterra.KernelExt.KvecM_contDiffOn_box
import Submission.Work.OddVolterra.KernelExt.KvecM_eq_Kvec
import Submission.Work.OddVolterra.Existence.aw_contDiffOn_awTheta
import Submission.Work.OddBridge.contDiffOn_Q_Ioo
import Submission.Work.OddBridge.Q_continuousOn_Icc

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

open Work.OddVolterra

noncomputable section

/-! ## The window on which the localised source is analysed -/

/-- The open window `(9/20, 1)`: it contains the (closed) support `[0.48, 0.97]` of the source
cutoff `awCsX`, and it is contained in the region where the manifest `Θ`-data agrees with
`awThetaMs`. -/
def awWin : Set ℝ := Set.Ioo (9 / 20 : ℝ) 1

lemma isOpen_awWin : IsOpen awWin := isOpen_Ioo

/-- The support of the source cutoff is contained in the window. -/
lemma tsupport_awCsX_subset_awWin : tsupport (awCsX : ℝ → ℝ) ⊆ awWin := by
  rw [ContDiffBump.tsupport_eq, awCsX_rOut]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq] at hx
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  exact ⟨by linarith, by linarith⟩

/-! ## A generic cutoff lemma -/

/-- If `f : ℝ → ℝ` is `C^∞` everywhere and `g` is `C^∞` on an open set `R` containing the
support of `f`, then `x ↦ f x • g x` is `C^∞` everywhere. -/
lemma contDiff_smul_of_contDiffOn_of_tsupport_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {R : Set ℝ} (hR : IsOpen R) {f : ℝ → ℝ} {g : ℝ → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g R)
    (hsupp : tsupport f ⊆ R) : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => f x • g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ R
  · exact hf.contDiffAt.smul (hg.contDiffAt (hR.mem_nhds hx))
  · have hx' : x ∉ tsupport f := fun h => hx (hsupp h)
    rw [tsupport, mem_closure_iff] at hx'
    push Not at hx'
    obtain ⟨o, ho, hxo, hdisj⟩ := hx'
    refine (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      (Filter.eventually_of_mem (ho.mem_nhds hxo) ?_)
    intro y hy
    have hfy : f y = 0 := by
      by_contra hne
      have hmem : y ∈ o ∩ Function.support f := ⟨hy, Function.mem_support.mpr hne⟩
      rw [hdisj] at hmem
      exact hmem
    simp [hfy]

/-! ## The hypotheses in the forms used below -/

lemma aw_tau_left : (1 : ℝ) - 2 * tau = 4 / 5 := by rw [tau]; norm_num
lemma aw_tau_right : (1 : ℝ) - tau = 9 / 10 := by rw [tau]; norm_num

/-- Non-degeneracy of the ball sections, from the support and smallness hypotheses. -/
lemma aw_hmid {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      0 < psi h Commons.Geometry.Ulam.semicircle s t :=
  fun s hs t ht => Work.OddVolterra.Smooth.psi_pos_of_window hsupp
    (fun x => by simpa using hsmall 0 (by norm_num) x) hs.1 hs.2 (abs_le.mpr ht)

/-- Smoothness of `Q` on `(0,1)`. -/
lemma aw_Q_contDiffOn (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Q n h) (Set.Ioo (0 : ℝ) 1) :=
  Work.OddBridge.contDiffOn_Q_Ioo n hn hh (aw_hmid hsupp hsmall)

/-- Continuity of `Q` on `[a,1]`. -/
lemma aw_Q_continuousOn_Icc (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) {a : ℝ}
    (ha : 0 < a) : ContinuousOn (Q n h) (Set.Icc a 1) :=
  (Work.OddVolterra.Smooth.Q_regularity n hn hh ha hsupp
    (fun t => by simpa using hsmall 0 (by norm_num) t) (aw_hmid hsupp hsmall)).1

/-! ## Smoothness of the two summands of the localised source -/

/-- **The frozen tail is smooth.**  On the window `awWin` the integrand
`ThetaM n h s σ (baseState σ)` agrees with the globally smooth localised data `awThetaMs`, so
the `σ`-integral is `C^∞`. -/
lemma aw_thetaM_integral_contDiffOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => ∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
        KernelExt.ThetaM n h s σ (baseState σ)) awWin := by
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => baseState p.1) :=
    contDiff_baseState_comp.comp (contDiff_fst.prodMk (contDiff_const (c := (0 : St))))
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => (p.2, (p.1, baseState p.1))) :=
    contDiff_snd.prodMk (contDiff_fst.prodMk hb)
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => awThetaMs n h p.2 p.1 (baseState p.1)) :=
    (contDiff_awThetaMs n hh hsupp hsmall).comp hφ
  have hInt : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => ∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
        awThetaMs n h s σ (baseState σ)) := by
    refine contDiff_infty.mpr (fun m => ?_)
    have hle : ((m : ℕ∞) : ℕ∞ω) ≤ ∞ := by
      show ((m : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact_mod_cast le_top
    simpa only [WithTop.coe_natCast] using
      (Work.Analysis.Calculus.contDiff_intervalIntegral_param ℝ m St
        (fun q : ℝ × ℝ => awThetaMs n h q.2 q.1 (baseState q.1)) (19 / 20) 1
        (hF.of_le hle))
  have hmono : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => ∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
        awThetaMs n h s σ (baseState σ)) awWin :=
    hInt.contDiffOn.mono (Set.subset_univ awWin)
  refine hmono.congr (fun s hs => ?_)
  refine intervalIntegral.integral_congr (fun σ hσ => ?_)
  rw [Set.uIcc_of_le (by norm_num : (19 : ℝ) / 20 ≤ 1)] at hσ
  exact (awThetaMs_eq_ThetaM n
    (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2])
    (by rw [abs_lt]; constructor <;> linarith [hσ.1, hσ.2])
    (by simp)).symm

/-! ## Truncated Abel integrals with fractional-power kernels

The derivative of the truncated Abel transform is analysed by splitting the integral at a fixed
point `c < 1`: the piece over `[c,1]` is a "tail" integral whose kernel `(v-u)^{-1/2}` is singular
only at the *fixed* point `v = c`, and the piece over `[u,c]` is handled by a substitution.  This
section develops the smoothness of the tail, iterating the dominated-differentiation lemma
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`; the derivative of the
`k`-th tail integral `u ↦ ∫_v in d..1, (v-u)^{-1/2-k} H v` is `(k+1/2)` times the `(k+1)`-st one,
so all orders are covered by a single argument. -/

/-- The truncated Abel integral `u ↦ ∫_v in d..1, (v-u)^(-1/2-k) H v`, `k : ℕ`. -/
noncomputable def abelK (H : ℝ → ℝ) (d : ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  ∫ v in d..(1 : ℝ), (v - u) ^ (-(1 / 2) - (k : ℝ)) * H v

/-- **Differentiation under the integral sign for a fractional-power kernel.**  For `p ≤ 0` and
`H` continuous on `[d,1]`, the function `u ↦ ∫_v in d..1, (v-u)^p H v` is differentiable at every
`s < d`, with derivative `-p ∫_v in d..1, (v-s)^(p-1) H v`.  Only continuity of `H` is needed:
the kernel `(v-u)^p` is smooth in `(u,v)` on the region `u < d ≤ v` and dominated by an integrable
function of `v`. -/
theorem hasDerivAt_intervalIntegral_rpow_mul {H : ℝ → ℝ} {p d : ℝ} (hp : p ≤ 0) (hd1 : d ≤ 1)
    (hH : ContinuousOn H (Set.Icc d 1)) {s : ℝ} (hs : s < d) :
    HasDerivAt (fun u : ℝ => ∫ v in d..(1 : ℝ), (v - u) ^ p * H v)
      (-p * ∫ v in d..(1 : ℝ), (v - s) ^ (p - 1) * H v) s := by
  set δ : ℝ := (d - s) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hsδ : s + δ < d := by rw [hδdef]; linarith
  have hmem_lt : ∀ x ∈ Metric.ball s δ, x < s + δ := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    linarith [(abs_lt.mp hx).2]
  have hHsub : ContinuousOn H (Set.uIoc d 1) := hH.mono (fun t ht => by
    rw [Set.uIoc_of_le hd1] at ht
    exact ⟨ht.1.le, ht.2⟩)
  have hHuIcc : ContinuousOn H (Set.uIcc d 1) := hH.mono (fun t ht => by
    rwa [Set.uIcc_of_le hd1] at ht)
  have hcont_rpow : ∀ (q : ℝ) {x : ℝ}, x < d →
      ContinuousOn (fun t : ℝ => (t - x) ^ q) (Set.uIcc d 1) := by
    intro q x hxd
    have hg : ContinuousOn (fun y : ℝ => y ^ q) (Set.Ioi 0) := fun y hy =>
      (Real.continuousAt_rpow_const y q (Or.inl (ne_of_gt hy))).continuousWithinAt
    have hlin : ContinuousOn (fun t : ℝ => t - x) (Set.uIcc d 1) :=
      continuousOn_id.sub continuousOn_const
    have hmap : MapsTo (fun t : ℝ => t - x) (Set.uIcc d 1) (Set.Ioi 0) := fun t ht => by
      rw [Set.uIcc_of_le hd1] at ht
      exact sub_pos.mpr (lt_of_lt_of_le hxd ht.1)
    simpa only [Function.comp_def, Pi.sub_apply] using hg.comp hlin hmap
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hH
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM d ⟨le_rfl, hd1⟩)
  have hδpow : 0 < δ ^ (p - 1) := Real.rpow_pos_of_pos hδpos _
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc d 1 → ∀ x ∈ Metric.ball s δ,
      ‖(-p) * (t - x) ^ (p - 1) * H t‖ ≤ |p| * δ ^ (p - 1) * M := by
    refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    have htI : t ∈ Set.Icc d 1 := by
      rw [Set.uIoc_of_le hd1] at ht; exact ⟨ht.1.le, ht.2⟩
    have htx : δ ≤ t - x := by have := hmem_lt x hx; linarith [htI.1]
    have htxpos : 0 < t - x := lt_of_lt_of_le hδpos htx
    have hstep : (t - x) ^ (p - 1) ≤ δ ^ (p - 1) := by
      have h1 : δ ^ (1 - p) ≤ (t - x) ^ (1 - p) :=
        Real.rpow_le_rpow hδpos.le htx (by linarith : (0 : ℝ) ≤ 1 - p)
      have h2 : (t - x) ^ (p - 1) = ((t - x) ^ (1 - p))⁻¹ := by
        rw [← Real.rpow_neg htxpos.le]; norm_num
      have h3 : δ ^ (p - 1) = (δ ^ (1 - p))⁻¹ := by
        rw [← Real.rpow_neg hδpos.le]; norm_num
      rw [h2, h3]
      exact inv_anti₀ (Real.rpow_pos_of_pos hδpos _) h1
    have htpow : 0 < (t - x) ^ (p - 1) := Real.rpow_pos_of_pos htxpos _
    have hnorm : ‖(-p) * (t - x) ^ (p - 1) * H t‖
        = |p| * (t - x) ^ (p - 1) * ‖H t‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos htpow, Real.norm_eq_abs]
    rw [hnorm]
    have h1 : |p| * (t - x) ^ (p - 1) ≤ |p| * δ ^ (p - 1) :=
      mul_le_mul_of_nonneg_left hstep (abs_nonneg p)
    have h2 : ‖H t‖ ≤ M := by
      have := hM t htI; rwa [Real.norm_eq_abs] at this
    have h3 : 0 ≤ |p| * δ ^ (p - 1) := mul_nonneg (abs_nonneg p) hδpow.le
    exact mul_le_mul h1 h2 (norm_nonneg _) h3
  have hF_meas : ∀ᶠ x in 𝓝 s, AEStronglyMeasurable (fun t : ℝ => (t - x) ^ p * H t)
      (volume.restrict (Set.uIoc d 1)) := by
    filter_upwards [Metric.ball_mem_nhds s hδpos] with x hx
    have hxd : x < d := lt_trans (hmem_lt x hx) hsδ
    exact (((hcont_rpow p hxd).mono Set.uIoc_subset_uIcc).mul hHsub).aestronglyMeasurable
      measurableSet_uIoc
  have hF_int : IntervalIntegrable (fun t : ℝ => (t - s) ^ p * H t) volume d 1 :=
    ((hcont_rpow p hs).mul hHuIcc).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => (-p) * (t - s) ^ (p - 1) * H t)
      (volume.restrict (Set.uIoc d 1)) := by
    have h1 : ContinuousOn (fun t : ℝ => (-p) * (t - s) ^ (p - 1) * H t) (Set.uIcc d 1) :=
      (continuousOn_const.mul (hcont_rpow (p - 1) hs)).mul hHuIcc
    exact (h1.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc d 1 → ∀ x ∈ Metric.ball s δ,
      HasDerivAt (fun y : ℝ => (t - y) ^ p * H t) ((-p) * (t - x) ^ (p - 1) * H t) x := by
    refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    have htI : t ∈ Set.Icc d 1 := by rw [Set.uIoc_of_le hd1] at ht; exact ⟨ht.1.le, ht.2⟩
    have htxpos : 0 < t - x := by have := hmem_lt x hx; linarith [htI.1]
    have h3 : HasDerivAt (fun z : ℝ => z ^ p) (p * (t - x) ^ (p - 1)) (t - x) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt htxpos))
    have h1 : HasDerivAt (fun y : ℝ => t - y) (-1) x := (hasDerivAt_id x).const_sub t
    have h2 : HasDerivAt (fun y : ℝ => (t - y) ^ p) ((-1) * (p * (t - x) ^ (p - 1))) x := by
      have h2' := h3.comp x h1
      have hval : (p * (t - x) ^ (p - 1)) * (-1) = (-1) * (p * (t - x) ^ (p - 1)) := by ring
      simpa only [Function.comp_def] using h2'.congr_deriv hval
    have h4 : HasDerivAt (fun y : ℝ => (t - y) ^ p * H t)
        (((-1) * (p * (t - x) ^ (p - 1))) * H t) x := h2.mul_const (H t)
    have hval : ((-1) * (p * (t - x) ^ (p - 1))) * H t = (-p) * (t - x) ^ (p - 1) * H t := by ring
    exact h4.congr_deriv hval
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (E := ℝ)
    (F := fun x t : ℝ => (t - x) ^ p * H t)
    (F' := fun x t : ℝ => (-p) * (t - x) ^ (p - 1) * H t)
    (x₀ := s) (s := Metric.ball s δ) (a := d) (b := 1) (bound := fun _ => |p| * δ ^ (p - 1) * M)
    (Metric.ball_mem_nhds s hδpos) hF_meas hF_int hF'_meas h_bound intervalIntegrable_const h_diff
  have hderiv : (∫ t in d..(1 : ℝ), (-p) * (t - s) ^ (p - 1) * H t)
      = -p * ∫ t in d..(1 : ℝ), (t - s) ^ (p - 1) * H t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  rw [hderiv] at hmain
  exact hmain.2

/-- **One step of the recursion for the truncated Abel integrals.** -/
lemma hasDerivAt_abelK {H : ℝ → ℝ} {d : ℝ} (hd1 : d ≤ 1) (hH : ContinuousOn H (Set.Icc d 1))
    (k : ℕ) {s : ℝ} (hs : s < d) :
    HasDerivAt (abelK H d k) ((1 / 2 + (k : ℝ)) * abelK H d (k + 1) s) s := by
  have hp : (-(1 / 2) - (k : ℝ)) ≤ 0 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h := hasDerivAt_intervalIntegral_rpow_mul (H := H) (p := -(1 / 2) - (k : ℝ)) (d := d)
    hp hd1 hH hs
  have hexp : (-(1 / 2) - (k : ℝ)) - 1 = -(1 / 2) - ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  have hnum : -(-(1 / 2) - (k : ℝ)) = 1 / 2 + (k : ℝ) := by ring
  simp only [abelK]
  rw [hexp, hnum] at h
  exact h

/-- **The truncated Abel integral is `C^∞` in its free variable.**  For `H` continuous on `[d,1]`,
`u ↦ ∫_v in d..1, (v-u)^{-1/2} H v` is `C^∞` on `(-∞,d)`. -/
theorem contDiffOn_abelK {H : ℝ → ℝ} {d : ℝ} (hd1 : d ≤ 1)
    (hH : ContinuousOn H (Set.Icc d 1)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (abelK H d 0) (Set.Iio d) := by
  have key : ∀ m k : ℕ, ContDiffOn ℝ (((m : ℕ∞) : ℕ∞ω)) (abelK H d k) (Set.Iio d) := by
    intro m
    induction m with
    | zero =>
      intro k
      have hdiff : DifferentiableOn ℝ (abelK H d k) (Set.Iio d) :=
        fun u hu => ((hasDerivAt_abelK hd1 hH k hu).differentiableAt).differentiableWithinAt
      exact contDiffOn_zero.mpr hdiff.continuousOn
    | succ m ih =>
      intro k
      have hcast : (((m : ℕ∞) : ℕ∞ω)) + 1 = ((((m + 1 : ℕ)) : ℕ∞) : ℕ∞ω) := by push_cast; ring
      rw [← hcast, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Iio]
      refine ⟨fun u hu => ((hasDerivAt_abelK hd1 hH k hu).differentiableAt).differentiableWithinAt,
        fun hcontra => absurd hcontra (by simp), ?_⟩
      exact (contDiffOn_const.mul (ih (k + 1))).congr
        (fun u hu => (hasDerivAt_abelK hd1 hH k hu).deriv)
  exact (contDiffOn_infty).mpr (fun m => key m 0)

/-- **Smoothness of a parametric integral over a fixed interval, localised in the parameter.**

If `G : ℝ → ℝ → ℝ` is `C^∞` on `U ×ˢ R`, where `U` and `R` are open and `R` contains the support
of a smooth function `χ` which equals `1` on `[a,b]`, then `u ↦ ∫_t in a..b, G u t` is `C^∞` on
`U`.  The bump `χ` is supplied by the caller; it is what localises the parametric integral lemma
`Work.Analysis.Calculus.contDiff_intervalIntegral_param`, which requires *global* smoothness of
the integrand in the variable of integration. -/
theorem contDiffOn_intervalIntegral_param_local {G : ℝ → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    {a b : ℝ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ1 : ∀ t ∈ Set.uIcc a b, χ t = 1)
    {R : Set ℝ} (hR : IsOpen R) (hχR : tsupport χ ⊆ R)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => G p.1 p.2) (U ×ˢ R)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun u : ℝ => ∫ t in a..b, G u t) U := by
  intro u₀ hu₀
  rw [contDiffWithinAt_iff_contDiffAt (hU.mem_nhds hu₀)]
  obtain ⟨ρ, hρpos, hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hu₀)
  have hρU' : ∀ y : ℝ, dist y u₀ ≤ ρ / 2 → y ∈ U := fun y hy =>
    hρU (Metric.mem_ball.mpr (lt_of_le_of_lt hy (by linarith)))
  let β : ContDiffBump u₀ := ⟨ρ / 4, ρ / 2, by linarith, by linarith⟩
  have hβrIn : (β : ContDiffBump u₀).rIn = ρ / 4 := rfl
  have hβrInpos : (0 : ℝ) < (β : ContDiffBump u₀).rIn := by rw [hβrIn]; linarith
  -- the globalising bump `(t, u) ↦ χ t * β u` is supported inside `R ×ˢ U`
  have hgsup : closure (Function.support (fun q : ℝ × ℝ => χ q.1 * (β : ℝ → ℝ) q.2))
      ⊆ R ×ˢ U := by
    have hsuppsub : Function.support (fun q : ℝ × ℝ => χ q.1 * (β : ℝ → ℝ) q.2)
        ⊆ Function.support (fun q : ℝ × ℝ => χ q.1)
          ∩ Function.support (fun q : ℝ × ℝ => (β : ℝ → ℝ) q.2) := by
      intro q hq
      have hq' : (fun p : ℝ × ℝ => χ p.1 * (β : ℝ → ℝ) p.2) q ≠ 0 := hq
      refine ⟨fun h0 => hq' ?_, fun h0 => hq' ?_⟩
      · have h0' : χ q.1 = 0 := h0
        simp only [h0', zero_mul]
      · have h0' : (β : ℝ → ℝ) q.2 = 0 := h0
        simp only [h0', mul_zero]
    have hA : closure (Function.support (fun q : ℝ × ℝ => χ q.1))
        ⊆ tsupport χ ×ˢ (Set.univ : Set ℝ) := by
      refine closure_minimal ?_ ((isClosed_tsupport χ).prod isClosed_univ)
      intro q hq
      refine ⟨subset_closure ?_, trivial⟩
      exact hq
    have hB : closure (Function.support (fun q : ℝ × ℝ => (β : ℝ → ℝ) q.2))
        ⊆ (Set.univ : Set ℝ) ×ˢ Metric.closedBall u₀ (ρ / 2) := by
      refine closure_minimal ?_ (isClosed_univ.prod
        (Metric.isClosed_closedBall (x := u₀) (ε := ρ / 2)))
      intro q hq
      refine ⟨trivial, ?_⟩
      rw [Function.mem_support] at hq
      by_contra hcon
      rw [Metric.mem_closedBall, not_le] at hcon
      exact hq (ContDiffBump.zero_of_le_dist β hcon.le)
    have hmem := closure_mono hsuppsub
    intro q hq
    have hqA := hA (closure_mono Set.inter_subset_left (hmem hq))
    have hqB := hB (closure_mono Set.inter_subset_right (hmem hq))
    exact ⟨hχR hqA.1, hρU' q.2 hqB.2⟩
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => χ q.1 * (β : ℝ → ℝ) q.2) :=
    (hχ.comp contDiff_fst).mul ((ContDiffBump.contDiff β).comp contDiff_snd)
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => G q.2 q.1) (R ×ˢ U) :=
    hG.comp ((by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => (q.2, q.1))).contDiffOn)
      (fun q hq => ⟨hq.2, hq.1⟩)
  have hprod : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => G q.2 q.1 * (χ q.1 * (β : ℝ → ℝ) q.2)) :=
    Work.OddVolterra.Existence.contDiff_mul_of_contDiffOn_of_closure_support_subset
      (V := ℝ × ℝ) (hR.prod hU) hf hg hgsup
  have hInt : ContDiff ℝ (⊤ : ℕ∞)
      (fun u : ℝ => ∫ t in a..b, G u t * (χ t * (β : ℝ → ℝ) u)) := by
    rw [contDiff_infty]
    intro m
    have hle : ((m : ℕ∞) : ℕ∞ω) ≤ ∞ := by
      show ((m : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact_mod_cast le_top
    simpa only [WithTop.coe_natCast] using
      (Work.Analysis.Calculus.contDiff_intervalIntegral_param ℝ m ℝ
        (fun q : ℝ × ℝ => G q.2 q.1 * (χ q.1 * (β : ℝ → ℝ) q.2)) a b
        (hprod.of_le hle))
  have hev : (fun u : ℝ => ∫ t in a..b, G u t) =ᶠ[𝓝 u₀]
      (fun u : ℝ => ∫ t in a..b, G u t * (χ t * (β : ℝ → ℝ) u)) := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds u₀ hβrInpos) ?_
    intro u hu
    have hβu : (β : ℝ → ℝ) u = 1 := by
      refine ContDiffBump.one_of_mem_closedBall β (Metric.mem_closedBall.mpr ?_)
      rw [Metric.mem_ball, Real.dist_eq] at hu
      rw [hβrIn]
      exact le_of_lt hu
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [hχ1 t ht, hβu, mul_one, mul_one]
  exact hInt.contDiffAt.congr_of_eventuallyEq hev

/-- **The Abel substitution on a compact piece.**  For `u ≤ c`,
`∫_v in u..c, φ v / √(v-u) = 2 √(c-u) ∫_t in 0..1, φ (u + (c-u) t²)`. -/
lemma abel_subst_Icc {φ : ℝ → ℝ} {u c : ℝ} (huc : u ≤ c) :
    (∫ v in u..c, φ v / Real.sqrt (v - u))
      = 2 * Real.sqrt (c - u) * ∫ t in (0 : ℝ)..1, φ (u + (c - u) * t ^ 2) := by
  have h := Commons.Analysis.Abel.intervalIntegral_abel_subst (E := ℝ) (x := u) (b := c) huc
    (fun _ σ => φ σ)
  have h1 : (∫ σ in u..c, (Real.sqrt (σ - u))⁻¹ • φ σ)
      = ∫ v in u..c, φ v / Real.sqrt (v - u) := by
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have h2 : ((2 * Real.sqrt (c - u)) • ∫ t in (0 : ℝ)..1, φ (u + (c - u) * t ^ 2))
      = 2 * Real.sqrt (c - u) * ∫ t in (0 : ℝ)..1, φ (u + (c - u) * t ^ 2) := by
    rw [smul_eq_mul]
  rw [h1, h2] at h
  exact h

/-- **Derivative of the truncated Abel transform.**  If `Q` is `C^∞` on `(0,1)` and continuous
up to `1`, then `s ↦ d/ds ∫_v in s..1, Q v / √(v-s)` is `C^∞` on `(a,1)`. -/
theorem aw_abel_deriv_contDiffOn {Q : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q (Set.Ioo 0 1))
    (hQcont : ContinuousOn Q (Set.Icc a 1)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => deriv (fun u : ℝ => ∫ v in u..(1 : ℝ), Q v / Real.sqrt (v - u)) s)
      (Set.Ioo a 1) := by
  intro x hx
  have hxa : a < x := hx.1
  have hx1 : x < 1 := hx.2
  rw [contDiffWithinAt_iff_contDiffAt (isOpen_Ioo.mem_nhds hx)]
  set c : ℝ := (x + 1) / 2 with hcdef
  have hxc : x < c := by rw [hcdef]; linarith
  have hc1 : c < 1 := by rw [hcdef]; linarith
  have hac : a < c := by rw [hcdef]; linarith
  set δ : ℝ := min (min ((c - x) / 2) ((x - a) / 2)) ((1 - x) / 2) with hδdef
  have hδ1 : δ ≤ (c - x) / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ2 : δ ≤ (x - a) / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ3 : δ ≤ (1 - x) / 2 := min_le_right _ _
  have hδpos : 0 < δ := by
    have h1 : 0 < (c - x) / 2 := by linarith
    have h2 : 0 < (x - a) / 2 := by linarith
    have h3 : 0 < (1 - x) / 2 := by linarith
    rw [hδdef]
    exact lt_min (lt_min h1 h2) h3
  set U : Set ℝ := Metric.ball x δ with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hxU : x ∈ U := Metric.mem_ball_self hδpos
  have hUac : ∀ u ∈ U, a < u ∧ u < c := by
    intro u hu
    rw [Metric.mem_ball, Real.dist_eq] at hu
    obtain ⟨h1, h2⟩ := abs_lt.mp hu
    constructor
    · linarith [hδ2]
    · linarith [hδ1]
  -- the two pieces of the transform
  set F1 : ℝ → ℝ := fun u => ∫ v in u..c, Q v / Real.sqrt (v - u) with hF1def
  set F2 : ℝ → ℝ := fun u => ∫ v in c..(1 : ℝ), Q v / Real.sqrt (v - u) with hF2def
  -- ## `F₂` (the tail over `[c,1]`)
  have hF2 : ContDiffOn ℝ (⊤ : ℕ∞) F2 (Set.Iio c) := by
    have hcontQ : ContinuousOn Q (Set.Icc c 1) :=
      hQcont.mono (fun t ht => ⟨le_of_lt (lt_of_lt_of_le hac ht.1), ht.2⟩)
    have hmain : ContDiffOn ℝ (⊤ : ℕ∞) (abelK Q c 0) (Set.Iio c) :=
      contDiffOn_abelK (le_of_lt hc1) hcontQ
    refine hmain.congr (fun u hu => ?_)
    have huc : u < c := hu
    simp only [abelK, hF2def]
    refine intervalIntegral.integral_congr (fun v hv => ?_)
    have hv1 : c ≤ v := by rw [Set.uIcc_of_le (le_of_lt hc1)] at hv; exact hv.1
    have hvu : 0 ≤ v - u := by linarith
    have hpow : (v - u) ^ (-(1 / 2) - ((0 : ℕ) : ℝ)) = (Real.sqrt (v - u))⁻¹ := by
      rw [show (-(1 / 2) - ((0 : ℕ) : ℝ)) = -(1 / 2) by norm_num, Real.rpow_neg hvu (1 / 2),
        ← Real.sqrt_eq_rpow]
    rw [hpow, div_eq_mul_inv, mul_comm]
  -- ## `F₁` (the piece over `[u,c]`) via the Abel substitution
  have hF1 : ContDiffOn ℝ (⊤ : ℕ∞) F1 U := by
    set χ : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, 3 / 5, by norm_num, by norm_num⟩ with hχdef
    have hχrIn : (χ : ContDiffBump (1 / 2 : ℝ)).rIn = 1 / 2 := rfl
    have hχrOut : (χ : ContDiffBump (1 / 2 : ℝ)).rOut = 3 / 5 := rfl
    have hχ1 : ∀ t ∈ Set.uIcc (0 : ℝ) 1, (χ : ℝ → ℝ) t = 1 := by
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      refine ContDiffBump.one_of_mem_closedBall χ (Metric.mem_closedBall.mpr ?_)
      rw [hχrIn, Real.dist_eq, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hχR : tsupport (χ : ℝ → ℝ) ⊆ Set.Ioo (-(1 / 5)) (6 / 5) := by
      rw [ContDiffBump.tsupport_eq, hχrOut]
      intro t ht
      rw [Metric.mem_closedBall, Real.dist_eq] at ht
      obtain ⟨h1, h2⟩ := abs_le.mp ht
      constructor <;> linarith
    have hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Q (p.1 + (c - p.1) * p.2 ^ 2))
        (U ×ˢ Set.Ioo (-(1 / 5)) (6 / 5)) := by
      refine hQ.comp ((by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ => p.1 + (c - p.1) * p.2 ^ 2)).contDiffOn) (fun p hp => ?_)
      obtain ⟨hu, ht⟩ := hp
      obtain ⟨hua, huc⟩ := hUac p.1 hu
      obtain ⟨ht1, ht2⟩ := ht
      have hcp : 0 ≤ c - p.1 := sub_nonneg.mpr (le_of_lt huc)
      have hsq : 0 ≤ p.2 ^ 2 := sq_nonneg p.2
      constructor
      · have h1 : 0 ≤ (c - p.1) * p.2 ^ 2 := mul_nonneg hcp hsq
        linarith
      · have hzu : p.2 ^ 2 ≤ 36 / 25 := by nlinarith [ht1, ht2]
        have hu_ge : x - δ ≤ p.1 := by
          rw [Metric.mem_ball, Real.dist_eq] at hu
          linarith [(abs_lt.mp hu).1]
        have hkey : p.1 + (c - p.1) * p.2 ^ 2 ≤ p.1 + (c - p.1) * (36 / 25) := by
          have := mul_le_mul_of_nonneg_left hzu hcp
          linarith
        have hbound : p.1 + (c - p.1) * (36 / 25) < 1 := by
          rw [hcdef] at *
          nlinarith [hu_ge, hδ3, hx1]
        linarith
    have hloc := contDiffOn_intervalIntegral_param_local (G := fun u t : ℝ => Q (u + (c - u) * t ^ 2))
      hUopen (χ := fun t : ℝ => (χ : ℝ → ℝ) t) (ContDiffBump.contDiff χ) hχ1 isOpen_Ioo hχR hG
    have hsqrt : ContDiffOn ℝ (⊤ : ℕ∞) (fun u : ℝ => Real.sqrt (c - u)) U := by
      refine ContDiffOn.sqrt (contDiffOn_const.sub contDiffOn_id) (fun u hu => ?_)
      exact ne_of_gt (sub_pos.mpr (hUac u hu).2)
    have hsmooth1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun u : ℝ => 2 * Real.sqrt (c - u)) U :=
      contDiffOn_const.mul hsqrt
    have hsmooth2 : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun u : ℝ => 2 * Real.sqrt (c - u) * ∫ t in (0 : ℝ)..1, Q (u + (c - u) * t ^ 2)) U :=
      hsmooth1.mul hloc
    refine hsmooth2.congr (fun u hu => ?_)
    exact abel_subst_Icc (le_of_lt (hUac u hu).2)
  -- ## splitting and assembly
  have hsplit : ∀ u ∈ U, (∫ v in u..(1 : ℝ), Q v / Real.sqrt (v - u)) = F1 u + F2 u := by
    intro u hu
    obtain ⟨hua, huc⟩ := hUac u hu
    have huc' : u ≤ c := le_of_lt huc
    have hcont1 : ContinuousOn Q (Set.uIcc u c) := hQcont.mono (fun t ht => by
      rw [Set.uIcc_of_le huc'] at ht
      exact ⟨le_of_lt (lt_of_lt_of_le hua ht.1), le_of_lt (lt_of_le_of_lt ht.2 hc1)⟩)
    have hcont2 : ContinuousOn Q (Set.uIcc c 1) := hQcont.mono (fun t ht => by
      rw [Set.uIcc_of_le (le_of_lt hc1)] at ht
      exact ⟨le_of_lt (lt_of_lt_of_le hac ht.1), ht.2⟩)
    have hint1 : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • Q v) volume u c :=
      (Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub huc).smul_continuousOn hcont1
    have hint2 : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • Q v) volume c 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ((Real.continuous_sqrt.comp_continuousOn
        (continuousOn_id.sub continuousOn_const)).inv₀ ?_).smul hcont2
      intro v hv
      have hv1 : c ≤ v := by rw [Set.uIcc_of_le (le_of_lt hc1)] at hv; exact hv.1
      exact ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr (lt_of_lt_of_le huc hv1)))
    have hsum := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    have e1 : (∫ v in u..c, (Real.sqrt (v - u))⁻¹ • Q v) = F1 u := by
      simp only [hF1def]
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
    have e2 : (∫ v in c..(1 : ℝ), (Real.sqrt (v - u))⁻¹ • Q v) = F2 u := by
      simp only [hF2def]
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
    have e3 : (∫ v in u..(1 : ℝ), Q v / Real.sqrt (v - u))
        = ∫ v in u..(1 : ℝ), (Real.sqrt (v - u))⁻¹ • Q v := by
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [e3, ← hsum, e1, e2]
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun u : ℝ => F1 u + F2 u) U :=
    hF1.add (hF2.mono (fun u hu => (hUac u hu).2))
  have hmono : ((⊤ : ℕ∞) : ℕ∞ω) + 1 ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
    rw [ENat.coe_top_add_one]
  have hderiv : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (fun u : ℝ => F1 u + F2 u)) U :=
    hsmooth.deriv_of_isOpen hUopen hmono
  have hev : (fun s : ℝ => deriv (fun u : ℝ => ∫ v in u..(1 : ℝ), Q v / Real.sqrt (v - u)) s)
      =ᶠ[𝓝 x] deriv (fun u : ℝ => F1 u + F2 u) := by
    refine Filter.eventually_of_mem (hUopen.mem_nhds hxU) (fun y hy => ?_)
    refine Filter.EventuallyEq.deriv_eq ?_
    refine Filter.eventually_of_mem (hUopen.mem_nhds hy) (fun z hz => ?_)
    exact hsplit z hz
  exact (hderiv.contDiffAt (hUopen.mem_nhds hxU)).congr_of_eventuallyEq hev

/-- **Smoothness of the Abel-transform derivative.**  The `i`-th component of `Qtilde` is the
derivative of the truncated Abel transform of `(Q n h) i`, which is smooth on the window. -/
lemma aw_Qtilde_contDiffOn (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) (i : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => deriv (fun u : ℝ => ∫ v in u..(1 : ℝ),
        (Q n h v) i / Real.sqrt (v - u)) s) awWin :=
  aw_abel_deriv_contDiffOn (Q := fun v : ℝ => (Q n h v) i) (a := 9 / 20)
    (by norm_num) (by norm_num)
    ((contDiffOn_pi.mp (aw_Q_contDiffOn n hn hh hsupp hsmall)) i)
    (continuousOn_pi.mp (aw_Q_continuousOn_Icc n hn hh hsupp hsmall (by norm_num)) i)

/-- **The localised source data `Xi` is smooth on the window.** -/
lemma aw_Xi_contDiffOn (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => Xi n h s) awWin := by
  have hfun : (fun s : ℝ => Xi n h s) = fun s : ℝ =>
      ![Commons.Geometry.Ulam.profileX 1, Commons.Geometry.Ulam.profileX 1,
        deriv (fun u : ℝ => ∫ v in u..(1 : ℝ), (Q n h v) 0 / Real.sqrt (v - u)) s,
        deriv (fun u : ℝ => ∫ v in u..(1 : ℝ), (Q n h v) 1 / Real.sqrt (v - u)) s] := by
    funext s
    simp [Xi, Qtilde]
  rw [hfun, contDiffOn_pi]
  intro i
  fin_cases i
  · simpa using (contDiffOn_const (c := Commons.Geometry.Ulam.profileX 1) (s := awWin))
  · simpa using (contDiffOn_const (c := Commons.Geometry.Ulam.profileX 1) (s := awWin))
  · simpa using aw_Qtilde_contDiffOn n hn hh hsupp hsmall 0
  · simpa using aw_Qtilde_contDiffOn n hn hh hsupp hsmall 1

/-! ## The target -/

/-- **Smoothness of the localised source.**  For a smooth bump `h` supported in the transition
window `[1-2τ,1-τ]` and `C¹`-small by `1/100`, the localised source `awXi n h (19/20)` (the
paper's `Ξ` plus the frozen tail, cut off by `awCsX`, whose support is contained in `(0.48,0.97)`)
is `C^∞` on all of `ℝ`.  This is the `hΞ_cont` input of the smoothness bootstrap
`Commons.Analysis.Calculus.contDiffOn_of_continuous_volterra_fixedPoint`.

PROOF HINTS.
* `awXi n h b s = awCsX s • (Xi n h s + ∫_σ in b..1, ThetaM n h s σ (baseState σ))` and `awCsX`
  is a bump with support inside `(0.48, 0.97)`, so it suffices that the inner factor be `C^∞` on an
  open neighbourhood of `[0.48,0.97]` (which is a compact inside `(0,1)`, with a gap from `1`).
* Integral term: the integrand `(s,σ) ↦ ThetaM n h s σ (baseState σ)` is `C^∞` on a neighbourhood
  of `[0.48,0.98] × [19/20,1]`: on that box `baseState σ` has components `≥ 1/√2 ≥ 1/5` and the
  Abel radicands are positive (`Work.OddVolterra.Existence.aw_krad_pos_box`,
  `KernelExt.KvecM_eq_Kvec`, `KernelExt.KvecM_contDiffOn_box`); the `σ`-integral is then `C^∞` in
  `s` by differentiating under the integral.
* `Xi n h s = ![profileX 1, profileX 1, Qtilde n h s 0, Qtilde n h s 1]` with
  `Qtilde = deriv (fun u => ∫_v u..1, Q n h v / √(v-u))`.  The substitution `v = u + z²` gives
  `∫_v u..1 Q(v)/√(v-u) dv = 2 ∫_0^{√(1-u)} Q n h (u + z²) dz`, a parametric integral whose
  integrand is `C^∞` on `(0,1) × ℝ` and whose upper limit is `C^∞` on `(0,1)`; differentiating
  under the integral (Mathlib's `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  plus the endpoint chain rule, cf. `Commons/Analysis/Calculus/intervalIntegral_hasDerivAt_upper_piece_of_continuous`)
  yields the `C^∞`-regularity of the transform and of `Qtilde` on compacts inside `(0,1)`.
  **Beware**: `Q n h` is only continuous at `v = 1` (`Q_regularity` gives `C²` on `[a,b]`, `b < 1`;
  `E1` has a `√(1-s)` cusp at `s = 1`), so split `∫_u^1 = ∫_u^c + ∫_c^1` at a fixed `c < 1` and
  differentiate only the first piece (the second is constant in `u` for `u < c`).
  `Q n h` is `C^∞` on compacts inside `(0,1)` by `Work.OddVolterra.Smooth.Q_regularity`,
  `E1_E2_regularity` and the smoothness of `iteratedDeriv (n+1) momentRHS`. -/
theorem aw_xi_smooth (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => Work.OddVolterra.Existence.awXi n h (19 / 20) s) Set.univ := by
  have hH : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => Xi n h s + ∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
        KernelExt.ThetaM n h s σ (baseState σ)) awWin :=
    (aw_Xi_contDiffOn n hn hh hsupp hsmall).add (aw_thetaM_integral_contDiffOn n hh hsupp hsmall)
  have hmain := contDiff_smul_of_contDiffOn_of_tsupport_subset isOpen_awWin
    (ContDiffBump.contDiff awCsX) hH tsupport_awCsX_subset_awWin
  simpa [awXi] using hmain.contDiffOn

end

end Work.OddVolterra.Existence
