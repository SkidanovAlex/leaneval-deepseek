import Mathlib
import Submission.Work.HFN.BlLowTS.Hsemi
import Submission.Work.HFN.BlLowTS.F2Paper
import Submission.Work.HFN.kernelTransform_seminorm_on_compact
import Submission.Work.Asymptotics.punctured_iteratedDeriv

/-!
# The `r`-seminorm bound on the low bad-line region `blLowSet`

Assembly of the target: from the translate-pole decomposition
(`hdec1`, `hdec2`) on `blLowSet = {τ ∈ 𝒟 : 2/5 ≤ Im τ ≤ 1/2, |Re τ| > 3/4}`, the `r`-seminorms
`|r|^k ∂_r^l` of the CKMRV contour integral `τ ↦ kernelTransform (Kfun ℓ d) τ ·` are uniformly
bounded on `blLowSet`, exactly as in `Work.Asymptotics.HalfFunnel.lowRegion_badLine`:

* the punctured pole-split layer `blLowF2` has bounded seminorms (from `blLow_hsemi_of_bounds`,
  with the explicit spike `BlLow.blLow_PhiSpike_deriv` and the spike-removed amplitudes
  `BlLow.blLow_Phi12_deriv`);
* `blLowF2 = paperLayer = kernelTransform` at every `r ≠ 0` where the contour integral converges;
* `kernelTransform_seminorm_of_layer_on_compact` transfers the bound to the contour integral.
-/

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology ContDiff

namespace Work.HFN.BlLowTS
open Work.Asymptotics  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Asymptotics.HalfFunnel Work.HFN.HalfFunnel
open Work.Kernels

/-- The pole-split layer `lowF2` with its value at `r = 0` replaced by `0` (the value of
`kernelTransform` at `r = 0`). -/
def blLowF2 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) : ℂ :=
  if r = 0 then 0 else lowF2 ℓ d τ r

lemma blLowF2_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) :
    blLowF2 ℓ d τ (-r) = blLowF2 ℓ d τ r := by
  rw [blLowF2, blLowF2]
  by_cases h : r = 0
  · subst h; simp
  · rw [if_neg h, if_neg (neg_ne_zero.mpr h), lowF2_neg_blLow]

/-- The `r`-seminorm bound for the punctured layer `blLowF2` on `blLowSet`. -/
theorem blLowF2_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {Cdec : ℝ} (hCdec : 0 ≤ Cdec)
    (hdec1 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ Cdec)
    (hdec2 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      lowRho ≤ |t - τ.im| → ‖Kaxis (Kfun ℓ d) τ t‖ ≤ Cdec) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (r : ℝ),
      Work.Asymptotics.BlLow.blLowSet τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => blLowF2 ℓ d τ s) r‖ ≤ C := by
  intro k l
  obtain ⟨Ct, Mt, hCt, hMt, htail⟩ := Work.HFN.BlLow.blLow_Aexp_tail ℓ d hd
  have hsemi := blLow_hsemi_of_bounds ℓ d hd hCdec hdec1 hdec2 ⟨Ct, Mt, hCt, hMt, htail⟩
    (fun m N => Work.Asymptotics.BlLow.blLow_PhiSpike_deriv ℓ d hd m N)
    (fun m N => Work.HFN.BlLow.blLow_Phi12_deriv ℓ d hd Cdec hCdec hdec1 m N) k l
  obtain ⟨c, hc, hb⟩ := hsemi
  refine ⟨c, hc, fun τ r hτ => ?_⟩
  rcases eq_or_ne r 0 with hr | hr
  · subst hr
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rcases Nat.eq_zero_or_pos l with hl | hl
      · subst hl
        have hz : blLowF2 ℓ d τ 0 = 0 := by rw [blLowF2]; simp
        simp only [iteratedDeriv_zero, hz, norm_zero, mul_zero]
        exact hc
      · have hfun : (fun s : ℝ => blLowF2 ℓ d τ s)
            = fun s : ℝ => (if s = 0 then 0 else lowF2 ℓ d τ s) := by
          funext s; rw [blLowF2]
        rw [hfun, punctured_iteratedDeriv (lowF2_neg_blLow ℓ d τ)
          ((contDiff_lowF2 ℓ d hd hCdec hdec1 hdec2 ⟨Ct, Mt, hCt, hMt, htail⟩ hτ).differentiable
            (by simp)) l hl]
        simpa using hb τ 0 hτ
    · have hz : (0 : ℝ) ^ k = 0 := zero_pow hk.ne'
      simp only [abs_zero, hz, zero_mul]
      exact hc
  · have heq : (fun s : ℝ => blLowF2 ℓ d τ s)
        =ᶠ[𝓝 r] (fun s : ℝ => lowF2 ℓ d τ s) := by
      filter_upwards [isOpen_ne.mem_nhds hr] with s hs
      rw [blLowF2, if_neg hs]
    rw [iteratedDeriv_congr_of_eventuallyEq heq l]
    exact hb τ r hτ

/-- On `blLowSet` the punctured layer `blLowF2` agrees with the paper's layer, hence with the
contour integral wherever the latter converges. -/
theorem blLowF2_agreement (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {Cdec : ℝ} (hCdec : 0 ≤ Cdec)
    (hdec1 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ Cdec)
    (hdec2 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      lowRho ≤ |t - τ.im| → ‖Kaxis (Kfun ℓ d) τ t‖ ≤ Cdec) :
    ∀ (τ : ℍ) (r : ℝ), Work.Asymptotics.BlLow.blLowSet τ → r ≠ 0 →
      MeasureTheory.IntegrableOn (fun t : ℝ => Kaxis (Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      blLowF2 ℓ d τ r = kernelTransform (Kfun ℓ d) τ r := by
  intro τ r hτ hr hInt
  rw [blLowF2, if_neg hr,
    lowF2_eq_paperLayer ℓ d hd Cdec hCdec hdec1 hdec2 τ r hτ]
  have hsub : ({τ} : Set ℍ) ⊆ Work.Asymptotics.DomainD := by rintro x rfl; exact hτ.1
  have hcpt : IsCompact ({τ} : Set ℍ) := isCompact_singleton
  exact Work.Asymptotics.Compact.local_agreement (K := ({τ} : Set ℍ)) ℓ d hd
    (Gcusp ℓ d) (fun i j => Gcusp_moderate ℓ d i j)
    (by
      intro h8 j
      rw [Gcusp, if_pos h8]
      funext x
      fin_cases j <;> simp [Gcusp8])
    (Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd hcpt hsub)
    (Work.HFN.cusp_expansion_of_kernel ℓ d hd hcpt hsub) τ r (by simp) hr hInt

/-- **The `r`-seminorm bound on `blLowSet`**, from the translate-pole decomposition. -/
theorem blLowLayer_transform_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {Cdec : ℝ} (hCdec : 0 ≤ Cdec)
    (hdec1 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ Cdec)
    (hdec2 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      lowRho ≤ |t - τ.im| → ‖Kaxis (Kfun ℓ d) τ t‖ ≤ Cdec) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (r : ℝ),
      Work.Asymptotics.BlLow.blLowSet τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        kernelTransform (Kfun ℓ d) τ s) r‖ ≤ C :=
  kernelTransform_seminorm_of_layer_on_compact (K := Work.Asymptotics.BlLow.blLowSet) ℓ d
    (blLowF2 ℓ d)
    (fun τ _ => by
      rw [blLowF2]; simp only [if_true]; rw [kernelTransform]; simp)
    (fun τ hτ r hr hInt => blLowF2_agreement ℓ d hd hCdec hdec1 hdec2 τ r hτ hr hInt)
    (fun k l => blLowF2_seminorm ℓ d hd hCdec hdec1 hdec2 k l)

/-! ## Gluing the window and off-window bounds -/

/-- **The translate-pole decomposition on `blLowSet`** from the window and off-window bounds.
Inside the window `|t - Im τ| ≤ 1/8` the bound is `hwin`; outside, `K - tpole` is bounded by
`hoff` and `‖tpole‖ ≤ 1/(2π lowRho)`. -/
theorem blLow_kernel_spike (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {Cw Co : ℝ} (hCw : 0 ≤ Cw) (hCo : 0 ≤ Co)
    (hwin : ∀ (τ : ℍ) (t : ℝ), Work.Asymptotics.BlLow.blLowSet τ → 0 < t → t ≤ lowT →
      |t - τ.im| ≤ 1 / 8 → ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ Cw)
    (hoff : ∀ (τ : ℍ) (t : ℝ), Work.Asymptotics.BlLow.blLowSet τ → 0 < t → t ≤ lowT →
      (1 / 8 : ℝ) ≤ |t - τ.im| → ‖Kaxis (Kfun ℓ d) τ t‖ ≤ Co) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (t : ℝ), Work.Asymptotics.BlLow.blLowSet τ → 0 < t →
      t ≤ lowT → ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C := by
  have hRho : 0 < lowRho := Work.HFN.BlLow.lowRho_pos
  refine ⟨max Cw (Co + 1 / (2 * Real.pi * lowRho)), ?_, fun τ t hτ ht htT => ?_⟩
  · exact le_trans hCw (le_max_left _ _)
  · by_cases hw : |t - τ.im| ≤ 1 / 8
    · exact le_trans (hwin τ t hτ ht htT hw) (le_max_left _ _)
    · have hsep : lowRho ≤ |t - τ.im| := le_of_lt (not_le.mp hw)
      have hK := hoff τ t hτ ht htT hsep
      have htp := blLow_norm_tpole_le_of_sep hτ hsep
      have h1 : ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖
          ≤ ‖Kaxis (Kfun ℓ d) τ t‖ + ‖tpole τ t‖ := norm_sub_le _ _
      have h2 : Co + 1 / (2 * Real.pi * lowRho) ≤ max Cw (Co + 1 / (2 * Real.pi * lowRho)) :=
        le_max_right _ _
      linarith


/-- **Region conversion**: the explicit hypotheses of the target produce a point of `blLowSet`. -/
theorem blLowSet_of_region {τ : ℍ} (hD : τ ∈ Work.Asymptotics.DomainD)
    (him1 : (2 : ℝ) / 5 ≤ τ.im) (him2 : τ.im ≤ 1 / 2) (hre : 3 / 4 < |τ.re|) :
    Work.Asymptotics.BlLow.blLowSet τ := by
  refine ⟨hD, him1, him2, ?_⟩
  rcases lt_abs.mp hre with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)


end Work.HFN.BlLowTS
