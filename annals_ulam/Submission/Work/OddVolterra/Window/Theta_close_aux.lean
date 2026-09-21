import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.JM_eq_J
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.Geometry.Ulam.ulam_faa_j
import Submission.Work.OddVolterra.Existence.deriv_G2_apply_eq_integral
import Submission.Work.OddVolterra.Existence.continuousOn_deriv_G2_apply
import Submission.Work.OddVolterra.Existence.krad_pos_state_region

/-!
# Auxiliary lemmas for `Theta_close_window`

The `s ≥ σ` half of the closeness statement (where both kernels vanish identically) plus the
elementary facts about the window used by the `s < σ` half.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## Part 1: the region `s ≥ σ` -/

/-- **The first Abel kernel vanishes above the diagonal.**  For `σ < a` the radicand
`ψ = (σ - a) · krad` of the numerator is `≤ 0` as soon as `krad ≥ 0`, and the denominator
radicand is `0` otherwise; in both cases `K₁ = J₁ / Kden = 0`. -/
lemma K1_eq_zero_of_lt (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {a σ t : ℝ} (haσ : σ < a) :
    K1 n h a σ t = 0 := by
  have hne : ¬ (σ = a) := ne_of_lt haσ
  have hpsi : psi h (fun t' => line h σ t') a t = (σ - a) * krad h σ t a :=
    psi_eq_mul_krad hh σ t a
  have hJ1 : J1 n h a σ t =
      iteratedDeriv (n + 1) (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ n *
        Real.sqrt (psi h (fun t' => line h σ t') u t)) a *
      Real.sqrt (psi h (fun t' => line h σ t') a t) := by
    unfold J1; rw [if_neg hne]
  unfold K1
  rw [hJ1]
  by_cases hk : 0 ≤ krad h σ t a
  · have hsqrt : Real.sqrt (psi h (fun t' => line h σ t') a t) = 0 := by
      rw [hpsi, Real.sqrt_eq_zero_of_nonpos]
      nlinarith
    rw [hsqrt, mul_zero, zero_div]
  · have hK : Kden h a σ t = 0 := by
      rw [Kden_eq_sqrt_krad, Real.sqrt_eq_zero_of_nonpos (le_of_lt (not_le.mp hk))]
    rw [hK, div_zero]

/-- **The second Abel kernel vanishes above the diagonal.** -/
lemma K2_eq_zero_of_lt (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {a σ t : ℝ} (haσ : σ < a) :
    K2 n h a σ t = 0 := by
  have hne : ¬ (σ = a) := ne_of_lt haσ
  have hpsi : psi h (fun t' => line h σ t') a t = (σ - a) * krad h σ t a :=
    psi_eq_mul_krad hh σ t a
  have hJ2 : J2 n h a σ t =
      iteratedDeriv n (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ (n - 1) *
        Real.sqrt (psi h (fun t' => line h σ t') u t) * lineSlope h u t) a *
      Real.sqrt (psi h (fun t' => line h σ t') a t) := by
    unfold J2; rw [if_neg hne]
  unfold K2
  rw [hJ2]
  by_cases hk : 0 ≤ krad h σ t a
  · have hsqrt : Real.sqrt (psi h (fun t' => line h σ t') a t) = 0 := by
      rw [hpsi, Real.sqrt_eq_zero_of_nonpos]
      nlinarith
    rw [hsqrt, mul_zero, zero_div]
  · have hK : Kden h a σ t = 0 := by
      rw [Kden_eq_sqrt_krad, Real.sqrt_eq_zero_of_nonpos (le_of_lt (not_le.mp hk))]
    rw [hK, div_zero]

/-- **The kernel vector vanishes above the diagonal.** -/
lemma Kvec_eq_zero_of_lt (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {a σ : ℝ} (haσ : σ < a)
    (x y x' y' : ℝ) : Kvec n h a σ x y x' y' = 0 := by
  funext i
  fin_cases i <;>
    simp [Kvec, K1_eq_zero_of_lt n hh haσ, K2_eq_zero_of_lt n hh haσ]

/-- **The Abel average `G₂` vanishes above the diagonal.** -/
lemma G2_eq_zero_of_lt (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {σ u : ℝ} (hσu : σ < u)
    (x y x' y' : ℝ) : G2 n h u σ x y x' y' = 0 := by
  funext i
  simp only [G2, Pi.zero_apply]
  rw [show (∫ τ in (0:ℝ)..1,
        Kvec n h (u + τ * (σ - u)) σ x y x' y' i / Real.sqrt (τ * (1 - τ)))
      = ∫ τ in (0:ℝ)..1, (0:ℝ) from
    intervalIntegral.integral_congr_ae (by
      filter_upwards with τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      rcases eq_or_lt_of_le hτ.2 with h1 | h1
      · subst h1
        norm_num
      · have hlt : σ < u + τ * (σ - u) := by nlinarith [hσu, hτ.1, h1]
        rw [Kvec_eq_zero_of_lt n hh hlt]
        simp)]
  simp

/-- A function vanishing on `(c, ∞)` has derivative `0` at `c` (the two-sided derivative
either does not exist, in which case Mathlib's `deriv` is `0`, or it exists and equals the
right-hand derivative, which is `0`). -/
lemma deriv_eq_zero_of_eq_zero_on_Ioi {f : ℝ → ℝ} {c : ℝ} (h : ∀ u : ℝ, c < u → f u = 0) :
    deriv f c = 0 := by
  rw [deriv]
  by_cases hd : DifferentiableAt ℝ f c
  · have hfd : HasFDerivAt f (fderiv ℝ f c) c := hd.hasFDerivAt
    have hderiv : HasDerivAt f (deriv f c) c := hfd.hasDerivAt
    have hcont : ContinuousAt f c := hderiv.continuousAt
    have hfc : f c = 0 := by
      have h1 : Tendsto f (𝓝[>] c) (𝓝 (f c)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : f =ᶠ[𝓝[>] c] fun _ : ℝ => (0 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact h u hu
      exact tendsto_nhds_unique h1 h2.tendsto
    have hslope : Tendsto (fun u : ℝ => (u - c)⁻¹ * (f u - f c)) (𝓝[>] c) (𝓝 (deriv f c)) :=
      hderiv.tendsto_slope.mono_left (nhdsWithin_mono _ (by intro u hu; exact ne_of_gt hu))
    have hzero : (fun u : ℝ => (u - c)⁻¹ * (f u - f c)) =ᶠ[𝓝[>] c] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      rw [h u hu, hfc, sub_zero, mul_zero]
    have h0 : (0 : ℝ) = deriv f c := tendsto_nhds_unique hzero.tendsto hslope
    exact h0.symm
  · simp [fderiv_zero_of_not_differentiableAt hd]

/-- **The two `Θ`'s agree for `s ≥ σ`**: both last two rows vanish, so the difference of the
vectors is `0`. -/
lemma Theta_sub_Theta_eq_zero_of_le (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {s σ : ℝ}
    (hsσ : σ ≤ s) (z : St) : Theta n h s σ z - Theta n 0 s σ z = 0 := by
  have hG2 : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (i : Fin 2),
      deriv (fun u : ℝ => (G2 n g u σ (z 0) (z 1) (z 2) (z 3)) i) s = 0 := by
    intro g hg i
    rcases lt_or_eq_of_le hsσ with hlt | heq
    · exact deriv_eq_zero_of_eq_zero_on_Ioi
        (fun u hu => by rw [G2_eq_zero_of_lt n hg (lt_trans hlt hu), Pi.zero_apply])
    · subst heq
      exact deriv_eq_zero_of_eq_zero_on_Ioi
        (fun u hu => by rw [G2_eq_zero_of_lt n hg hu, Pi.zero_apply])
  funext i
  fin_cases i <;>
    simp [Theta, hG2 h hh, hG2 0 contDiff_const]


/-! ## Part 2: general analytic tools -/

/-- The `i`-th iterated derivative of a `C^∞` function is again `C^∞`. -/
lemma contDiff_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => iteratedDeriv i f x) := by
  induction i with
  | zero => simpa using hf
  | succ i ih =>
      rw [show (fun x : ℝ => iteratedDeriv (i + 1) f x) = deriv (fun x : ℝ => iteratedDeriv i f x)
        from funext (fun x => congrFun (iteratedDeriv_succ (n := i) (f := f)) x)]
      exact ih.deriv'

/-- **Lipschitz lemma for `x ↦ x ^ p` on a nondegenerate interval of `(0,∞)`.** -/
lemma exists_rpow_lipschitz_Icc {κ C : ℝ} (hκ : 0 < κ) (p : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, κ ≤ x → x ≤ C → κ ≤ y → y ≤ C →
      |x ^ p - y ^ p| ≤ L * |x - y| := by
  set M : ℝ := max κ C with hM
  have hκM : κ ≤ M := le_max_left _ _
  have hM0 : (0:ℝ) < M := lt_of_lt_of_le hκ hκM
  have hsmooth : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun x : ℝ => x ^ p) (Set.Icc κ M) := by
    intro x hx
    have hxpos : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hκ hx.1)
    exact (Real.contDiffAt_rpow_const_of_ne (p := p) (n := ⊤) hxpos).contDiffWithinAt
  obtain ⟨L, hL⟩ := hsmooth.exists_lipschitzOnWith (by simp) (convex_Icc κ M) isCompact_Icc
  refine ⟨L, L.coe_nonneg, ?_⟩
  intro x y hx hxC hy hyC
  have hx' : x ∈ Set.Icc κ M := ⟨hx, le_trans hxC (le_max_right _ _)⟩
  have hy' : y ∈ Set.Icc κ M := ⟨hy, le_trans hyC (le_max_right _ _)⟩
  exact hL.norm_sub_le hx' hy'

/-- The derivative of `X / √Y` where `Y > 0`. -/
lemma deriv_div_sqrt {X Y : ℝ → ℝ} {a : ℝ} (hX : DifferentiableAt ℝ X a)
    (hY : DifferentiableAt ℝ Y a) (hYpos : 0 < Y a) :
    deriv (fun u : ℝ => X u / Real.sqrt (Y u)) a =
      deriv X a / Real.sqrt (Y a) - X a * deriv Y a / (2 * Real.sqrt (Y a) ^ 3) := by
  have hs : HasDerivAt (fun u : ℝ => Real.sqrt (Y u))
      (deriv Y a / (2 * Real.sqrt (Y a))) a := hY.hasDerivAt.sqrt (ne_of_gt hYpos)
  have hd : HasDerivAt (fun u : ℝ => X u / Real.sqrt (Y u))
      ((deriv X a * Real.sqrt (Y a) - X a * (deriv Y a / (2 * Real.sqrt (Y a)))) /
        (Real.sqrt (Y a)) ^ 2) a := hX.hasDerivAt.div hs (ne_of_gt (Real.sqrt_pos_of_pos hYpos))
  rw [hd.deriv]
  have hsq : Real.sqrt (Y a) ^ 2 = Y a := Real.sq_sqrt (le_of_lt hYpos)
  have h3 : Real.sqrt (Y a) ^ 3 = Y a * Real.sqrt (Y a) := by rw [pow_succ, hsq]
  rw [hsq, h3]
  have hne : Real.sqrt (Y a) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hYpos)
  have hneY : Y a ≠ 0 := ne_of_gt hYpos
  field_simp
  rw [hsq]
  ring

/-- The derivative of `1 / √Y` where `Y > 0`. -/
lemma deriv_one_div_sqrt {Y : ℝ → ℝ} {a : ℝ} (hY : DifferentiableAt ℝ Y a)
    (hYpos : 0 < Y a) :
    deriv (fun u : ℝ => 1 / Real.sqrt (Y u)) a =
      -(deriv Y a) / (2 * Real.sqrt (Y a) ^ 3) := by
  have h := deriv_div_sqrt (X := fun _ : ℝ => (1:ℝ)) (Y := Y) (a := a)
    (differentiableAt_const (1:ℝ)) hY hYpos
  simpa [neg_div] using h


/-- **The jet-curve Lipschitz lemma.**  A `C^∞` function `F` of a finite jet vector is bounded
and Lipschitz on the compact set of jets of radius `B < R`, with all constants uniform in the
jet curves.  Both the values `F (j a)` and the derivatives `deriv (F ∘ j) a` are controlled;
the two curves `j₁`, `j₀` are compared through their jets and their jet-derivatives. -/
theorem JetCurve_lipschitz (K : ℕ) (F : (Fin K → ℝ) → ℝ) {R B B' δ : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hB' : 0 ≤ B') (hδ : 0 ≤ δ) (hBR : B < R)
    (hF : ContDiffOn ℝ (⊤ : WithTop ℕ∞) F {v : Fin K → ℝ | ‖v‖ < R}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j₁ j₀ : ℝ → Fin K → ℝ),
      ContDiff ℝ (⊤ : WithTop ℕ∞) j₁ → ContDiff ℝ (⊤ : WithTop ℕ∞) j₀ →
      (∀ a : ℝ, ‖j₁ a‖ ≤ B) → (∀ a : ℝ, ‖j₀ a‖ ≤ B) →
      (∀ a : ℝ, ‖deriv j₁ a‖ ≤ B') → (∀ a : ℝ, ‖deriv j₀ a‖ ≤ B') →
      (∀ a : ℝ, ‖j₁ a - j₀ a‖ ≤ δ) → (∀ a : ℝ, ‖deriv j₁ a - deriv j₀ a‖ ≤ δ) →
      (∀ a : ℝ, |F (j₁ a)| ≤ C ∧ |F (j₀ a)| ≤ C ∧
        |deriv (fun a => F (j₁ a)) a| ≤ C ∧ |deriv (fun a => F (j₀ a)) a| ≤ C ∧
        |F (j₁ a) - F (j₀ a)| ≤ C * δ ∧
        |deriv (fun a => F (j₁ a)) a - deriv (fun a => F (j₀ a)) a| ≤ C * δ) := by
  have hUopen : IsOpen {v : Fin K → ℝ | ‖v‖ < R} := isOpen_lt continuous_norm continuous_const
  set Bc : Set (Fin K → ℝ) := Metric.closedBall (0 : Fin K → ℝ) B with hBc
  have hBcU : Bc ⊆ {v : Fin K → ℝ | ‖v‖ < R} := by
    intro v hv
    rw [hBc, Metric.mem_closedBall, dist_zero_right] at hv
    exact lt_of_le_of_lt hv hBR
  have hmem : ∀ v : Fin K → ℝ, (v ∈ Bc ↔ ‖v‖ ≤ B) := by
    intro v; rw [hBc, Metric.mem_closedBall, dist_zero_right]
  have hFB : ContDiffOn ℝ (⊤ : WithTop ℕ∞) F Bc := hF.mono hBcU
  have hFd : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ F) Bc :=
    (hF.fderiv_of_isOpen hUopen (m := ⊤) le_top).mono hBcU
  have hconv : Convex ℝ Bc := convex_closedBall 0 B
  have hcomp : IsCompact Bc := isCompact_closedBall 0 B
  obtain ⟨L₀, hL₀⟩ := hFB.exists_lipschitzOnWith (by simp) hconv hcomp
  obtain ⟨L₁, hL₁⟩ := hFd.exists_lipschitzOnWith (by simp) hconv hcomp
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hFB.continuousOn
  obtain ⟨M₁, hM₁⟩ := hcomp.exists_bound_of_continuousOn hFd.continuousOn
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hM10 : 0 ≤ max M₁ 0 := le_max_right _ _
  have hM' : ∀ v ∈ Bc, |F v| ≤ max M 0 :=
    fun v hv => le_trans (by simpa [Real.norm_eq_abs] using hM v hv) (le_max_left _ _)
  have hM₁' : ∀ v ∈ Bc, ‖fderiv ℝ F v‖ ≤ max M₁ 0 :=
    fun v hv => le_trans (hM₁ v hv) (le_max_left _ _)
  set C : ℝ := max M 0 + max M₁ 0 + (L₀ : ℝ) + (L₁ : ℝ) + max M₁ 0 * B' + (L₁ : ℝ) * B' + 1
    with hC
  have hL₀0 : (0:ℝ) ≤ (L₀ : ℝ) := NNReal.coe_nonneg _
  have hL₁0 : (0:ℝ) ≤ (L₁ : ℝ) := NNReal.coe_nonneg _
  have hM10B' : 0 ≤ max M₁ 0 * B' := mul_nonneg hM10 hB'
  have hL1B' : 0 ≤ (L₁ : ℝ) * B' := mul_nonneg hL₁0 hB'
  have hC0 : 0 ≤ C := by rw [hC]; linarith
  have hle_M : max M 0 ≤ C := by rw [hC]; linarith
  have hle_M1B : max M₁ 0 * B' ≤ C := by rw [hC]; linarith
  have hle_L0 : (L₀ : ℝ) ≤ C := by rw [hC]; linarith
  have hle_L1B : max M₁ 0 + (L₁ : ℝ) * B' ≤ C := by rw [hC]; linarith
  refine ⟨C, hC0, ?_⟩
  intro j₁ j₀ hj₁ hj₀ hb₁ hb₀ hd₁ hd₀ he₁ he₀ a
  have hm₁ : j₁ a ∈ Bc := (hmem _).mpr (hb₁ a)
  have hm₀ : j₀ a ∈ Bc := (hmem _).mpr (hb₀ a)
  have hU₁ : j₁ a ∈ {v : Fin K → ℝ | ‖v‖ < R} := hBcU hm₁
  have hU₀ : j₀ a ∈ {v : Fin K → ℝ | ‖v‖ < R} := hBcU hm₀
  have hFd₁ : DifferentiableAt ℝ F (j₁ a) :=
    (hF.differentiableOn (by simp) (j₁ a) hU₁).differentiableAt (hUopen.mem_nhds hU₁)
  have hFd₀ : DifferentiableAt ℝ F (j₀ a) :=
    (hF.differentiableOn (by simp) (j₀ a) hU₀).differentiableAt (hUopen.mem_nhds hU₀)
  have hj₁d : DifferentiableAt ℝ j₁ a := (hj₁.differentiable (by simp)).differentiableAt
  have hj₀d : DifferentiableAt ℝ j₀ a := (hj₀.differentiable (by simp)).differentiableAt
  have hchain₁ : deriv (fun a => F (j₁ a)) a = (fderiv ℝ F (j₁ a)) (deriv j₁ a) := by
    have hcomp : fderiv ℝ (fun a => F (j₁ a)) a = (fderiv ℝ F (j₁ a)).comp (fderiv ℝ j₁ a) :=
      fderiv_comp a hFd₁ hj₁d
    show (fderiv ℝ (fun a => F (j₁ a)) a) 1 = (fderiv ℝ F (j₁ a)) (deriv j₁ a)
    rw [hcomp]
    rfl
  have hchain₀ : deriv (fun a => F (j₀ a)) a = (fderiv ℝ F (j₀ a)) (deriv j₀ a) := by
    have hcomp : fderiv ℝ (fun a => F (j₀ a)) a = (fderiv ℝ F (j₀ a)).comp (fderiv ℝ j₀ a) :=
      fderiv_comp a hFd₀ hj₀d
    show (fderiv ℝ (fun a => F (j₀ a)) a) 1 = (fderiv ℝ F (j₀ a)) (deriv j₀ a)
    rw [hcomp]
    rfl
  have hlip₀ : ‖F (j₁ a) - F (j₀ a)‖ ≤ (L₀ : ℝ) * ‖j₁ a - j₀ a‖ := hL₀.norm_sub_le hm₁ hm₀
  have hlip₁ : ‖fderiv ℝ F (j₁ a) - fderiv ℝ F (j₀ a)‖ ≤ (L₁ : ℝ) * ‖j₁ a - j₀ a‖ :=
    hL₁.norm_sub_le hm₁ hm₀
  have hb1 : |F (j₁ a)| ≤ C := le_trans (hM' _ hm₁) hle_M
  have hb0 : |F (j₀ a)| ≤ C := le_trans (hM' _ hm₀) hle_M
  have hd1 : |deriv (fun a => F (j₁ a)) a| ≤ C := by
    refine le_trans ?_ hle_M1B
    rw [hchain₁, ← Real.norm_eq_abs]
    calc ‖(fderiv ℝ F (j₁ a)) (deriv j₁ a)‖ ≤ ‖fderiv ℝ F (j₁ a)‖ * ‖deriv j₁ a‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ max M₁ 0 * B' := mul_le_mul (hM₁' _ hm₁) (hd₁ a) (norm_nonneg _) hM10
  have hd0 : |deriv (fun a => F (j₀ a)) a| ≤ C := by
    refine le_trans ?_ hle_M1B
    rw [hchain₀, ← Real.norm_eq_abs]
    calc ‖(fderiv ℝ F (j₀ a)) (deriv j₀ a)‖ ≤ ‖fderiv ℝ F (j₀ a)‖ * ‖deriv j₀ a‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ max M₁ 0 * B' := mul_le_mul (hM₁' _ hm₀) (hd₀ a) (norm_nonneg _) hM10
  have hdiffval : |F (j₁ a) - F (j₀ a)| ≤ C * δ := by
    have h1 : |F (j₁ a) - F (j₀ a)| ≤ (L₀ : ℝ) * δ := by
      rw [← Real.norm_eq_abs]
      exact le_trans hlip₀ (mul_le_mul_of_nonneg_left (he₁ a) hL₀0)
    exact le_trans h1 (mul_le_mul_of_nonneg_right hle_L0 hδ)
  have hdiffder : |deriv (fun a => F (j₁ a)) a - deriv (fun a => F (j₀ a)) a| ≤ C * δ := by
    have hmain : |deriv (fun a => F (j₁ a)) a - deriv (fun a => F (j₀ a)) a| ≤
        (max M₁ 0 + (L₁ : ℝ) * B') * δ := by
      rw [hchain₁, hchain₀, ← Real.norm_eq_abs]
      have hdecomp : (fderiv ℝ F (j₁ a)) (deriv j₁ a) - (fderiv ℝ F (j₀ a)) (deriv j₀ a) =
          (fderiv ℝ F (j₁ a)) (deriv j₁ a - deriv j₀ a) +
            ((fderiv ℝ F (j₁ a)) - (fderiv ℝ F (j₀ a))) (deriv j₀ a) := by
        rw [map_sub, sub_apply]; abel
      rw [hdecomp]
      refine le_trans (norm_add_le _ _) ?_
      have h2 : ‖((fderiv ℝ F (j₁ a)) - (fderiv ℝ F (j₀ a))) (deriv j₀ a)‖ ≤
          (L₁ : ℝ) * B' * δ := by
        have h3 : ‖(fderiv ℝ F (j₁ a) - fderiv ℝ F (j₀ a)) (deriv j₀ a)‖ ≤
            ‖fderiv ℝ F (j₁ a) - fderiv ℝ F (j₀ a)‖ * ‖deriv j₀ a‖ :=
          ContinuousLinearMap.le_opNorm _ _
        have h4 : ‖fderiv ℝ F (j₁ a) - fderiv ℝ F (j₀ a)‖ * ‖deriv j₀ a‖ ≤
            ((L₁ : ℝ) * ‖j₁ a - j₀ a‖) * B' :=
          mul_le_mul hlip₁ (hd₀ a) (norm_nonneg _) (by positivity)
        have h5 : ((L₁ : ℝ) * ‖j₁ a - j₀ a‖) * B' ≤ ((L₁ : ℝ) * δ) * B' :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (he₁ a) hL₁0) hB'
        calc ‖(fderiv ℝ F (j₁ a) - fderiv ℝ F (j₀ a)) (deriv j₀ a)‖
            ≤ ((L₁ : ℝ) * δ) * B' := le_trans (le_trans h3 h4) h5
          _ = (L₁ : ℝ) * B' * δ := by ring
      have h1 : ‖(fderiv ℝ F (j₁ a)) (deriv j₁ a - deriv j₀ a)‖ ≤ max M₁ 0 * δ := by
        calc ‖(fderiv ℝ F (j₁ a)) (deriv j₁ a - deriv j₀ a)‖
            ≤ ‖fderiv ℝ F (j₁ a)‖ * ‖deriv j₁ a - deriv j₀ a‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ max M₁ 0 * δ := mul_le_mul (hM₁' _ hm₁) (he₀ a) (norm_nonneg _) hM10
      linarith
    exact le_trans hmain (mul_le_mul_of_nonneg_right hle_L1B hδ)
  exact ⟨hb1, hb0, hd1, hd0, hdiffval, hdiffder⟩


/-! ## The state ball -/

lemma state_ball_box' {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∀ σ ∈ Set.Icc b 1, ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (1 / 2),
      (1 / 5 : ℝ) ≤ z 0 ∧ (1 / 5 : ℝ) ≤ z 1 ∧ (∀ i : Fin 4, |z i| ≤ 2) := by
  intro σ hσ z hz
  have hcoord : ∀ i : Fin 4, |z i - Work.OddVolterra.baseState σ i| ≤ 1 / 2 := by
    intro i
    have h := dist_le_pi_dist z (Work.OddVolterra.baseState σ) i
    rw [Real.dist_eq] at h
    linarith [Metric.mem_closedBall.mp hz]
  have hbase : ∀ i : Fin 4, |Work.OddVolterra.baseState σ i| ≤ 1 := by
    intro i
    fin_cases i
    · show |Work.OddVolterra.baseState σ 0| ≤ 1
      rw [show Work.OddVolterra.baseState σ 0 = Commons.Geometry.Ulam.profileX σ from rfl]
      exact abs_le.mpr ⟨(Commons.Geometry.Ulam.profileX_mem_Icc σ).1,
        (Commons.Geometry.Ulam.profileX_mem_Icc σ).2⟩
    · show |Work.OddVolterra.baseState σ 1| ≤ 1
      rw [show Work.OddVolterra.baseState σ 1 = Commons.Geometry.Ulam.profileX σ from rfl]
      exact abs_le.mpr ⟨(Commons.Geometry.Ulam.profileX_mem_Icc σ).1,
        (Commons.Geometry.Ulam.profileX_mem_Icc σ).2⟩
    · show |Work.OddVolterra.baseState σ 2| ≤ 1
      rw [show Work.OddVolterra.baseState σ 2 = deriv Commons.Geometry.Ulam.profileX σ from rfl]
      linarith [Commons.Geometry.Ulam.abs_deriv_profileX_le σ]
    · show |Work.OddVolterra.baseState σ 3| ≤ 1
      rw [show Work.OddVolterra.baseState σ 3 = deriv Commons.Geometry.Ulam.profileX σ from rfl]
      linarith [Commons.Geometry.Ulam.abs_deriv_profileX_le σ]
  have hprof : (1 : ℝ) / 5 ≤ Commons.Geometry.Ulam.profileX σ - 1 / 2 := by
    have h0 : 0 ≤ σ := le_trans hb.le hσ.1
    have h1 : Commons.Geometry.Ulam.profileX 1 ≤ Commons.Geometry.Ulam.profileX σ :=
      Commons.Geometry.Ulam.profileX_le_profileX' h0 hσ.2
    have h2 : Commons.Geometry.Ulam.profileX 1 = 1 / Real.sqrt 2 := by
      simp only [Commons.Geometry.Ulam.profileX]; norm_num
    have h3 : Real.sqrt 2 < 10 / 7 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h4 : (7 : ℝ) / 10 < 1 / Real.sqrt 2 := by
      rw [lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
      nlinarith [h3]
    rw [h2] at h1
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have h := hcoord 0
    rw [show Work.OddVolterra.baseState σ 0 = Commons.Geometry.Ulam.profileX σ from rfl] at h
    linarith [abs_le.mp h]
  · have h := hcoord 1
    rw [show Work.OddVolterra.baseState σ 1 = Commons.Geometry.Ulam.profileX σ from rfl] at h
    linarith [abs_le.mp h]
  · intro i
    have h := abs_le.mp (hcoord i)
    have hb' := abs_le.mp (hbase i)
    rw [abs_le]
    constructor <;> linarith

/-! ## Part 3: the statement of the kernel comparison, and the assembly -/

/-- The kernel comparison hypothesis: `Kvec` and its first-slot derivative are bounded and
`δ`-close to their unperturbed values on the region of use.  This is the statement proved in
`Work.OddVolterra.Window.Kvec_deriv_close`. -/
def KvecClose (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
    ContDiff ℝ (⊤ : ℕ∞) h → 0 ≤ δ → δ ≤ 1 / 100 →
    Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
    (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
    ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1, ∀ z : St,
      (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
      ∀ a ∈ Set.Icc (9 / 20 : ℝ) σ, a < σ →
        ‖Kvec n h a σ (z 0) (z 1) (z 2) (z 3)‖ ≤ C ∧
        ‖Kvec n h a σ (z 0) (z 1) (z 2) (z 3) -
          Kvec n 0 a σ (z 0) (z 1) (z 2) (z 3)‖ ≤ C * δ ∧
        ‖deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a‖ ≤ C ∧
        ‖deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a -
         deriv (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) a‖ ≤ C * δ


/-- `deriv_G2_apply_eq_integral` with `s < σ` in place of `σ < 1`. -/
lemma deriv_G2_eq_integral_of_lt (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {s σ : ℝ} (hsσ : s < σ) (z : St) {e Cm : ℝ} (he : 0 < e) (hCm : 0 < Cm)
    (hbdK : ∀ x ∈ Set.Ioo (s - e) (s + e), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      ‖Kvec n h (x + τ * (σ - x)) σ (z 0) (z 1) (z 2) (z 3)‖ ≤ Cm)
    (hdiff : ∀ x ∈ Set.Ioo (s - e) (s + e), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      DifferentiableAt ℝ (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (x + τ * (σ - x)))
    (hbdD : ∀ x ∈ Set.Ioo (s - e) (s + e), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖(1 - τ) • deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (x + τ * (σ - x))‖ ≤ Cm)
    (i : Fin 2) :
    deriv (fun u : ℝ => (G2 n h u σ (z 0) (z 1) (z 2) (z 3)) i) s =
      ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * ((deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
          (s + τ * (σ - s))) i)) := by
  have hH := hasDerivAt_G2 (h := h) n hh hsσ z he hbdK hdiff hbdD
  have hw_meas : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
    ((Real.continuous_sqrt.measurable.comp
      (measurable_id.mul (measurable_const.sub measurable_id)))).inv
  have hVint : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ •
        ((1 - τ) • deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))))
      volume (0:ℝ) 1 := by
    refine (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const Cm).mono_fun' ?_ ?_
    · have hm : Measurable (fun τ : ℝ => deriv (fun u : ℝ =>
          Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) :=
        (measurable_deriv (𝕜 := ℝ) (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))).comp
          (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
      exact (hw_meas.smul ((measurable_const.sub measurable_id).smul hm)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      rcases eq_or_lt_of_le hτ.2 with h1 | h1
      · subst h1
        have h0 : (Real.sqrt ((1:ℝ) * (1 - 1)))⁻¹ = 0 := by
          rw [show (1:ℝ) * (1 - 1) = 0 by norm_num, Real.sqrt_zero, inv_zero]
        rw [h0]
        simp
      · have hx : s ∈ Set.Ioo (s - e) (s + e) := ⟨by linarith, by linarith⟩
        have hb := hbdD s hx τ ⟨le_of_lt hτ.1, le_of_lt h1⟩
        calc ‖(Real.sqrt (τ * (1 - τ)))⁻¹ •
              ((1 - τ) • deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
                (s + τ * (σ - s)))‖
            = (Real.sqrt (τ * (1 - τ)))⁻¹ * ‖(1 - τ) • deriv (fun u : ℝ =>
                Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))‖ := by
              rw [norm_smul, Real.norm_eq_abs,
                abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
          _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * Cm :=
              mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hdiffcomp : ∀ j : Fin 2, DifferentiableAt ℝ
      (fun u : ℝ => (G2 n h u σ (z 0) (z 1) (z 2) (z 3)) j) s :=
    fun j => (differentiableAt_pi.mp hH.differentiableAt) j
  have hcomp_eq : deriv (fun u : ℝ =>
        (G2 n h u σ (z 0) (z 1) (z 2) (z 3)) i) s
      = (deriv (fun u : ℝ =>
        G2 n h u σ (z 0) (z 1) (z 2) (z 3)) s) i :=
    (congrFun (deriv_pi (𝕜 := ℝ) (x := s)
      (φ := fun u : ℝ => G2 n h u σ (z 0) (z 1) (z 2) (z 3))
      (fun j => hdiffcomp j)) i).symm
  have hproj_eq : (∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ •
        ((1 - τ) • deriv (fun u : ℝ =>
          Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s)))) i
      = ∫ τ in (0:ℝ)..1, ((Real.sqrt (τ * (1 - τ)))⁻¹ •
        ((1 - τ) • deriv (fun u : ℝ =>
          Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s)))) i := by
    have h := ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) hVint
    simpa [ContinuousLinearMap.proj_apply] using h.symm
  have key : ∀ τ : ℝ, ((Real.sqrt (τ * (1 - τ)))⁻¹ •
        ((1 - τ) • deriv (fun u : ℝ =>
          Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s)))) i
      = (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * ((deriv (fun u : ℝ =>
          Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)) :=
    fun τ => by simp [Pi.smul_apply, smul_eq_mul]
  calc deriv (fun u : ℝ => (G2 n h u σ (z 0) (z 1) (z 2) (z 3)) i) s
      = (deriv (fun u : ℝ =>
          G2 n h u σ (z 0) (z 1) (z 2) (z 3)) s) i := hcomp_eq
    _ = (∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ •
          ((1 - τ) • deriv (fun u : ℝ =>
            Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s)))) i := by
          rw [hH.deriv]
    _ = ∫ τ in (0:ℝ)..1, ((Real.sqrt (τ * (1 - τ)))⁻¹ •
          ((1 - τ) • deriv (fun u : ℝ =>
            Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s)))) i := hproj_eq
    _ = ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * ((deriv (fun u : ℝ =>
            Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)) :=
          intervalIntegral.integral_congr (fun τ _ => key τ)

/-- **The assembly.** -/
theorem Theta_close_window_of_kvec (n : ℕ) (hn : 1 ≤ n) (hK : KvecClose n) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ), ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1,
        ∀ z : St, ‖z - baseState σ‖ ≤ 2 / 5 →
        ‖Theta n h s σ z - Theta n 0 s σ z‖ < ε := by
  intro ε hε
  obtain ⟨C, hC0, hKC⟩ := hK
  have hπ : 0 < Real.pi := Real.pi_pos
  set D : ℝ := min (1 / 100) (ε / (Real.pi * (C + 1) + 1)) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; exact lt_min (by norm_num) (by positivity)
  have hD100 : D ≤ 1 / 100 := by rw [hDdef]; exact min_le_left _ _
  have hDeps : D ≤ ε / (Real.pi * (C + 1) + 1) := by rw [hDdef]; exact min_le_right _ _
  have hkey : C * D * Real.pi < ε := by
    have hden : 0 < Real.pi * (C + 1) + 1 := by positivity
    have h3 : C * Real.pi / (Real.pi * (C + 1) + 1) < 1 := by
      rw [div_lt_one hden]
      nlinarith [hπ, hC0]
    have h5 : C * D ≤ C * (ε / (Real.pi * (C + 1) + 1)) :=
      mul_le_mul_of_nonneg_left hDeps hC0
    have h6 : C * D * Real.pi ≤ ε * (C * Real.pi / (Real.pi * (C + 1) + 1)) := by
      calc C * D * Real.pi ≤ (C * (ε / (Real.pi * (C + 1) + 1))) * Real.pi :=
            mul_le_mul_of_nonneg_right h5 (le_of_lt hπ)
        _ = ε * (C * Real.pi / (Real.pi * (C + 1) + 1)) := by ring
    have h7 : ε * (C * Real.pi / (Real.pi * (C + 1) + 1)) < ε * 1 :=
      mul_lt_mul_of_pos_left h3 hε
    linarith [h6, h7]
  refine ⟨D, hDpos, ?_⟩
  intro h hh hsupp hjet s hs σ hσ z hz
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  by_cases hle : σ ≤ s
  · have hzero : Theta n h s σ z - Theta n 0 s σ z = 0 :=
      Theta_sub_Theta_eq_zero_of_le n hh1 hle z
    rw [hzero, norm_zero]; exact hε
  have hlt : s < σ := not_le.mp hle
  have hzball : z ∈ Metric.closedBall (baseState σ) (1 / 2) :=
    Metric.closedBall_subset_closedBall (by norm_num) hz
  obtain ⟨hz0, hz1, hzbd⟩ :=
    state_ball_box' (b := 7 / 10) (by norm_num) (by norm_num) σ hσ z hzball
  set e : ℝ := min (1 / 20) ((σ - s) / 2) with hedef
  have hepos : 0 < e := by rw [hedef]; exact lt_min (by norm_num) (by linarith)
  have he20 : e ≤ 1 / 20 := by rw [hedef]; exact min_le_left _ _
  have he2 : e ≤ (σ - s) / 2 := by rw [hedef]; exact min_le_right _ _
  have hse : (9 / 20 : ℝ) ≤ s - e := by linarith [hs.1, he20]
  have hsmallg : ∀ (g : ℝ → ℝ), (∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ D) →
      ∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ 1 / 100 :=
    fun g hgj k hk x => le_trans (hgj k (le_trans hk (by omega)) x) hD100
  have hposg : ∀ (g : ℝ → ℝ), (∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ 1 / 100) →
      Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      ∀ σ' ∈ Set.Icc (7 / 10 : ℝ) 1, ∀ a ∈ Set.Icc (s - e) σ',
        0 < krad g σ' (-(z 0)) a ∧ 0 < krad g σ' (z 1) a := by
    intro g hg1 hgs σ' hσ' a ha
    have ha9 : (9 / 20 : ℝ) ≤ a := le_trans hse ha.1
    have ht0 : (1 / 5 : ℝ) ≤ |-(z 0)| := by
      rw [abs_neg, abs_of_nonneg (by linarith [hz0])]; exact hz0
    have ht1 : (1 / 5 : ℝ) ≤ |z 1| := by
      rw [abs_of_nonneg (by linarith [hz1])]; exact hz1
    exact ⟨Existence.krad_pos_state_region hgs hg1 (by norm_num : (0:ℝ) < 9 / 20) ha9 ha.2 hσ'.2 ht0,
      Existence.krad_pos_state_region hgs hg1 (by norm_num : (0:ℝ) < 9 / 20) ha9 ha.2 hσ'.2 ht1⟩
  have hpoint : ∀ x ∈ Set.Ioo (s - e) (s + e), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      x + τ * (σ - x) ∈ Set.Icc (s - e) σ ∧ x + τ * (σ - x) < σ := by
    intro x hx τ hτ
    have hxσ : x < σ := by linarith [hx.2, he2]
    have hconvex : x + τ * (σ - x) = (1 - τ) * x + τ * σ := by ring
    have hge : s - e ≤ x := le_of_lt hx.1
    constructor
    · rw [hconvex]
      constructor
      · nlinarith [hτ.1, hτ.2, hge]
      · nlinarith [hτ.1, hτ.2, hxσ]
    · rw [hconvex]; nlinarith [hτ.1, hτ.2, hxσ]
  have hjet0 : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ,
      |iteratedDeriv k (0 : ℝ → ℝ) x| ≤ D := by
    intro k hk x
    have h0 : iteratedDeriv k (0 : ℝ → ℝ) x = 0 := by
      rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
      split <;> simp
    rw [h0, abs_zero]; exact le_of_lt hDpos
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆ Set.Icc (1 - 2 * tau) (1 - tau) := by
    intro x hx
    rw [Function.mem_support] at hx
    exact absurd rfl hx
  have hbK : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
      (hgj : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ D)
      (hgs : Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau)),
      ∀ x ∈ Set.Ioo (s - e) (s + e), ∀ τ ∈ Set.Ico (0:ℝ) 1,
        ‖Kvec n g (x + τ * (σ - x)) σ (z 0) (z 1) (z 2) (z 3)‖ ≤ C + 1 := by
    intro g hg hgj hgs x hx τ hτ
    obtain ⟨hmem, hlt'⟩ := hpoint x hx τ hτ
    have := (hKC g D hg (le_of_lt hDpos) hD100 hgs hgj σ hσ z hz0 hz1 hzbd _ ⟨le_trans hse hmem.1, hmem.2⟩ hlt').1
    linarith
  have hbD : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
      (hgj : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ D)
      (hgs : Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau)),
      ∀ x ∈ Set.Ioo (s - e) (s + e), ∀ τ ∈ Set.Icc (0:ℝ) 1,
        ‖(1 - τ) • deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
          (x + τ * (σ - x))‖ ≤ C + 1 := by
    intro g hg hgj hgs x hx τ hτ
    rcases eq_or_lt_of_le hτ.2 with h1 | h1
    · subst h1
      simp only [sub_self, zero_smul, norm_zero]; linarith [hC0]
    · obtain ⟨hmem, hlt'⟩ := hpoint x hx τ ⟨hτ.1, h1⟩
      have hb := (hKC g D hg (le_of_lt hDpos) hD100 hgs hgj σ hσ z hz0 hz1 hzbd _ ⟨le_trans hse hmem.1, hmem.2⟩ hlt').2.2.1
      have hτle : (0:ℝ) ≤ 1 - τ := by linarith [hτ.1, h1]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτle]
      have h2 : (1 - τ) * ‖deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
          (x + τ * (σ - x))‖ ≤ 1 * (C + 1) := by
        calc (1 - τ) * ‖deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
              (x + τ * (σ - x))‖
            ≤ 1 * ‖deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
              (x + τ * (σ - x))‖ :=
              mul_le_mul_of_nonneg_right (by linarith [hτ.1, h1]) (norm_nonneg _)
          _ ≤ 1 * (C + 1) := mul_le_mul_of_nonneg_left (le_trans hb (by linarith)) (by norm_num)
      linarith [h2]
  have hdiffg : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
      (hgj : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ D)
      (hgs : Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau)),
      ∀ x ∈ Set.Ioo (s - e) (s + e), ∀ τ ∈ Set.Ico (0:ℝ) 1,
        DifferentiableAt ℝ (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
          (x + τ * (σ - x)) := by
    intro g hg hgj hgs x hx τ hτ
    obtain ⟨hmem, hlt'⟩ := hpoint x hx τ hτ
    exact Existence.differentiableAt_Kvec n hn hg (z := z) hlt'
      (hposg g (hsmallg g hgj) hgs σ hσ _ hmem).1
      (hposg g (hsmallg g hgj) hgs σ hσ _ hmem).2
  have hformula : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
      (hgj : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ D)
      (hgs : Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) (i : Fin 2),
      deriv (fun u : ℝ => (G2 n g u σ (z 0) (z 1) (z 2) (z 3)) i) s =
        ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * ((deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
            (s + τ * (σ - s))) i)) :=
    fun g hg hgj hgs i =>
      deriv_G2_eq_integral_of_lt n hn hg hlt z hepos (by linarith [hC0])
        (hbK g hg hgj hgs) (hdiffg g hg hgj hgs) (hbD g hg hgj hgs) i
  have hIntF : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
      (hgj : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ D)
      (hgs : Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) (i : Fin 2),
      IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * ((deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
          (s + τ * (σ - s))) i))) volume (0:ℝ) 1 := by
    intro g hg hgj hgs i
    refine (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const (C + 1)).mono_fun' ?_ ?_
    · have hmw : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
        ((Real.continuous_sqrt.measurable.comp
          (measurable_id.mul (measurable_const.sub measurable_id)))).inv
      have hA : Measurable (fun τ : ℝ => (deriv (fun u : ℝ =>
          Kvec n g u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i) :=
        (measurable_pi_apply i).comp
          ((measurable_deriv (𝕜 := ℝ) (fun u : ℝ =>
            Kvec n g u σ (z 0) (z 1) (z 2) (z 3))).comp
            (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s)))
      exact (hmw.mul ((measurable_const.sub measurable_id).mul hA)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      rcases eq_or_lt_of_le hτ.2 with h1 | h1
      · subst h1
        have h0 : (Real.sqrt ((1:ℝ) * (1 - 1)))⁻¹ = 0 := by
          rw [show (1:ℝ) * (1 - 1) = 0 by norm_num, Real.sqrt_zero, inv_zero]
        rw [h0]; simp
      · obtain ⟨hmem, hlt'⟩ := hpoint s ⟨by linarith, by linarith⟩ τ ⟨le_of_lt hτ.1, h1⟩
        have hb := (hKC g D hg (le_of_lt hDpos) hD100 hgs hgj σ hσ z hz0 hz1 hzbd _ ⟨le_trans hse hmem.1, hmem.2⟩ hlt').2.2.1
        have hτle : (0:ℝ) ≤ 1 - τ := by linarith
        have hwb : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
        calc ‖(Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
              Kvec n g u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i))‖
            = (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * |(deriv (fun u : ℝ =>
                Kvec n g u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i|) := by
              rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hwb, abs_of_nonneg hτle]
          _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ‖deriv (fun u : ℝ =>
                Kvec n g u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))‖) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hτle) hwb
              exact norm_le_pi_norm (deriv (fun u : ℝ =>
                Kvec n g u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i
          _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 * (C + 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ hwb
              calc (1 - τ) * ‖deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
                    (s + τ * (σ - s))‖
                  ≤ 1 * ‖deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
                    (s + τ * (σ - s))‖ :=
                    mul_le_mul_of_nonneg_right (by linarith [hτ.1] : (1:ℝ) - τ ≤ 1) (norm_nonneg _)
                _ ≤ 1 * (C + 1) := mul_le_mul_of_nonneg_left (le_trans hb (by linarith))
                    (by norm_num)
          _ = (Real.sqrt (τ * (1 - τ)))⁻¹ * (C + 1) := by ring
  have hpt : ∀ i : Fin 2, ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖(Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
          Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)) -
        (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
          Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i))‖ ≤
      (Real.sqrt (τ * (1 - τ)))⁻¹ * (C * D) := by
    intro i τ hτ
    rcases eq_or_lt_of_le hτ.2 with h1 | h1
    · subst h1
      have h0 : (Real.sqrt ((1:ℝ) * (1 - 1)))⁻¹ = 0 := by
        rw [show (1:ℝ) * (1 - 1) = 0 by norm_num, Real.sqrt_zero, inv_zero]
      rw [h0]; simp
    · have hwb : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have hτle : (0:ℝ) ≤ 1 - τ := by linarith [hτ.1, h1]
      have hrewrite : ((Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
              Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)) -
            (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
              Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)))
          = (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) *
              (((deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
                (s + τ * (σ - s))) i) -
               ((deriv (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3))
                (s + τ * (σ - s))) i))) := by ring
      rw [hrewrite, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hwb, abs_of_nonneg hτle]
      refine mul_le_mul_of_nonneg_left ?_ hwb
      refine le_trans (mul_le_mul_of_nonneg_right (by linarith [hτ.1] : (1:ℝ) - τ ≤ 1) (abs_nonneg _)) ?_
      rw [one_mul]
      have hab : ((deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
            (s + τ * (σ - s))) i) - ((deriv (fun u : ℝ =>
            Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)
          = ((deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
            (s + τ * (σ - s))) - (deriv (fun u : ℝ =>
            Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s)))) i := rfl
      rw [hab, ← Real.norm_eq_abs]
      obtain ⟨hmem, hlt'⟩ := hpoint s ⟨by linarith, by linarith⟩ τ ⟨hτ.1, h1⟩
      have hb := (hKC h D hh (le_of_lt hDpos) hD100 hsupp hjet σ hσ z hz0 hz1 hzbd _ ⟨le_trans hse hmem.1, hmem.2⟩ hlt').2.2.2
      exact le_trans (norm_le_pi_norm (deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
        (s + τ * (σ - s)) - deriv (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3))
        (s + τ * (σ - s))) i) hb
  have hfinal : ∀ i : Fin 2,
      |deriv (fun u : ℝ => (G2 n h u σ (z 0) (z 1) (z 2) (z 3)) i) s -
        deriv (fun u : ℝ => (G2 n 0 u σ (z 0) (z 1) (z 2) (z 3)) i) s| ≤
        C * D * Real.pi := by
    intro i
    rw [hformula h hh hjet hsupp i, hformula 0 contDiff_const hjet0 hsupp0 i]
    have hIh := hIntF h hh hjet hsupp i
    have hI0 := hIntF 0 contDiff_const hjet0 hsupp0 i
    rw [← intervalIntegral.integral_sub hIh hI0, ← Real.norm_eq_abs]
    calc ‖∫ τ in (0:ℝ)..1, ((Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
            Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)) -
          (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
            Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)))‖
        ≤ ∫ τ in (0:ℝ)..1, ‖((Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
            Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)) -
          (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
            Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)))‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * (C * D) :=
          intervalIntegral.integral_mono_on (by norm_num) (hIh.sub hI0).norm
            (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const (C * D))
            (fun τ hτ => hpt i τ hτ)
      _ = C * D * Real.pi := by
          rw [intervalIntegral.integral_mul_const, Existence.abel_weight_integral]
          ring
  set A : ℝ := (deriv (fun u : ℝ => (G2 n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s - deriv (fun u : ℝ => (G2 n 0 u σ (z 0) (z 1) (z 2) (z 3)) 0) s) with hA
  set B' : ℝ := (deriv (fun u : ℝ => (G2 n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s - deriv (fun u : ℝ => (G2 n 0 u σ (z 0) (z 1) (z 2) (z 3)) 1) s) with hB
  have hkeyA : |A| ≤ C * D * Real.pi := by rw [hA]; exact hfinal 0
  have hkeyB : |B'| ≤ C * D * Real.pi := by rw [hB]; exact hfinal 1
  rw [pi_norm_lt_iff hε]
  intro i
  fin_cases i
  · show ‖(Theta n h s σ z - Theta n 0 s σ z) 0‖ < ε
    have h0 : (Theta n h s σ z - Theta n 0 s σ z) 0 = 0 := by
      simp [Theta, Pi.sub_apply]
    rw [h0, norm_zero]; exact hε
  · show ‖(Theta n h s σ z - Theta n 0 s σ z) 1‖ < ε
    have h0 : (Theta n h s σ z - Theta n 0 s σ z) 1 = 0 := by
      simp [Theta, Pi.sub_apply]
    rw [h0, norm_zero]; exact hε
  · show ‖(Theta n h s σ z - Theta n 0 s σ z) 2‖ < ε
    have h0 : (Theta n h s σ z - Theta n 0 s σ z) 2 = -((deriv (fun u : ℝ => (G2 n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s - deriv (fun u : ℝ => (G2 n 0 u σ (z 0) (z 1) (z 2) (z 3)) 0) s)) := by
      simp only [Theta, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      ring
    rw [h0, norm_neg, Real.norm_eq_abs]
    exact lt_of_le_of_lt hkeyA hkey
  · show ‖(Theta n h s σ z - Theta n 0 s σ z) 3‖ < ε
    have h0 : (Theta n h s σ z - Theta n 0 s σ z) 3 = -((deriv (fun u : ℝ => (G2 n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s - deriv (fun u : ℝ => (G2 n 0 u σ (z 0) (z 1) (z 2) (z 3)) 1) s)) := by
      simp only [Theta, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      ring
    rw [h0, norm_neg, Real.norm_eq_abs]
    exact lt_of_le_of_lt hkeyB hkey

end

end Work.OddVolterra.Window
