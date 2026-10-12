import Mathlib.Tactic.Have
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseBogFS.W1momentAux
import Submission.Work.BoseBogFS.fourier_mul_eq_integral_shift
import Submission.Work.BoseBogFS.integrable_integral_integral_mul_sub
import Submission.Work.BoseBogFS.scaled_moment_integrable
import Submission.Work.BoseBogFS.scaled_representation
import Submission.Work.BoseFixR.Rb5Lin.chiR0_le_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.momentbound_theta_factor`

Uniform-in-`ε` bound on the weighted `L¹`-moment of the Fourier transform of
`f_ε(z) = (z_j)^m · θ((χ⋆χ)(ε•z)) · β z` for `0 < ε ≤ chiR0`.

The proof follows the route of the statement's docstring: with the fixed smooth compactly
supported functions `A z = (z_j)^m β z` and `B̃_1 y = θ((χ⋆χ)(y)) - θ 0`, one writes
`f_ε = θ 0 · A + A · B̃_ε` with `B̃_ε = B̃_1 ∘ (ε • ·)`; Fourier inversion of `B̃_1` (a Schwartz
function) dilated by `ε` (the `scaled_representation`/`scaled_moment_integrable` bricks) gives an
integrable profile `G` with `B̃_ε x = ∫ η, 𝐞⟪η,x⟫ • G η` and `∫ (1+‖η‖)‖G η‖ ≤ (1+chiR0)·M`,
and the Fubini/Parseval step `fourier_mul_eq_integral_shift` together with the convolution moment
identity `integrable_integral_integral_mul_sub` (Young's inequality) bounds the moment of
`𝓕(A·B̃_ε)` by the product of the moments.  The final constant is
`|θ 0|·M(A) + (1+chiR0)·M(B̃_1)·M(A)`.

Main ingredients (all proved here or imported from `Submission/Work/BoseBogFS/`):
`chiConv`, `thetaComp`, `polyBetaR/C`, `fTheta`, `thetaCompScale`,
`fourierMoment_mul_le`, `polyBetaC_data`, `thetaComp_data`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real FourierTransform RealInnerProductSpace ContDiff

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

-- ===============================================================
-- definitions
-- ===============================================================

/-- `(χ ⋆ χ)`. -/
noncomputable def chiConv (x : E3) : ℝ :=
  Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x

/-- `θ((χ⋆χ)(y)) - θ 0`: the compactly supported part of the `θ`-factor. -/
noncomputable def thetaComp (y : E3) : ℝ := theta (chiConv y) - theta 0

/-- `z ↦ z_j^m · β z`, real valued. -/
noncomputable def polyBetaR (m : ℕ) (j : Fin 3) (z : E3) : ℝ := (z.ofLp j) ^ m * beta z

/-- `z ↦ z_j^m · β z`, complex valued. -/
noncomputable def polyBetaC (m : ℕ) (j : Fin 3) (z : E3) : ℂ := (polyBetaR m j z : ℂ)

/-- `z ↦ z_j^m · θ((χ⋆χ)(ε•z)) · β z`, the function whose Fourier moment is bounded. -/
noncomputable def fTheta (m : ℕ) (j : Fin 3) (ε : ℝ) : E3 → ℂ :=
  fun z => ((((z.ofLp j) ^ m * theta (Submission.BoseGases.convScale (ε⁻¹) z) * beta z : ℝ)) : ℂ)

/-- The compactly supported `θ`-factor at scale `ε`: `z ↦ θ((χ⋆χ)(ε•z)) - θ 0`. -/
noncomputable def thetaCompScale (ε : ℝ) (z : E3) : ℂ := ((thetaComp (ε • z) : ℝ) : ℂ)

-- ===============================================================
-- basic facts
-- ===============================================================

lemma chiConv_cd_top : ContDiff ℝ ∞ chiConv := Submission.BoseGases.conv_contDiff

lemma chiConv_cd (n : ℕ) : ContDiff ℝ n chiConv := contDiff_infty.mp chiConv_cd_top n

lemma chiConv_eq_zero_of_one_lt_norm {x : E3} (hx : 1 < ‖x‖) : chiConv x = 0 :=
  Work.BoseFixR.Rb5Lin.conv3_chi_eq_zero_of_one_lt_norm hx

lemma chiConv_hasCompactSupport : HasCompactSupport chiConv := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E3) 1) ?_
  intro x hx
  rw [Function.mem_support] at hx
  have h2 : ‖x‖ ≤ 1 := by
    by_contra h
    exact hx (chiConv_eq_zero_of_one_lt_norm (not_le.mp h))
  simpa [mem_closedBall, dist_eq_norm] using h2

lemma thetaComp_cd (n : ℕ) : ContDiff ℝ n thetaComp := by
  have h1 : ContDiff ℝ n (fun y : E3 => theta (chiConv y)) :=
    (theta_contDiff n).comp (chiConv_cd n)
  exact h1.sub contDiff_const

lemma thetaComp_continuous : Continuous thetaComp := (thetaComp_cd 0).continuous

lemma thetaComp_hasCompactSupport : HasCompactSupport thetaComp := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E3) 1) ?_
  intro x hx
  rw [Function.mem_support] at hx
  have h2 : ‖x‖ ≤ 1 := by
    by_contra h
    have hz : chiConv x = 0 := chiConv_eq_zero_of_one_lt_norm (not_le.mp h)
    refine hx ?_
    simp only [thetaComp, hz, sub_self]
  simpa [mem_closedBall, dist_eq_norm] using h2

lemma thetaComp_bdd : ∃ c : ℝ, 0 ≤ c ∧ ∀ y : E3, ‖thetaComp y‖ ≤ c := by
  obtain ⟨c, hc⟩ := IsCompact.exists_bound_of_continuousOn thetaComp_hasCompactSupport
    thetaComp_continuous.continuousOn
  refine ⟨max c 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ tsupport thetaComp
  · exact (hc y hy).trans (le_max_left _ _)
  · have h0 : thetaComp y = 0 := by
      by_contra h
      exact hy (subset_tsupport _ h)
    simp [h0]

lemma polyBetaR_cd (m : ℕ) (j : Fin 3) (n : ℕ) : ContDiff ℝ n (polyBetaR m j) := by
  change ContDiff ℝ n fun z : E3 => (z.ofLp j) ^ m * beta z
  have h1 : ContDiff ℝ n (fun z : E3 => z.ofLp j) := by fun_prop
  exact (h1.pow m).mul (beta_contDiff n)

lemma polyBetaR_continuous (m : ℕ) (j : Fin 3) : Continuous (polyBetaR m j) :=
  (polyBetaR_cd m j 0).continuous

lemma polyBetaR_hasCompactSupport (m : ℕ) (j : Fin 3) : HasCompactSupport (polyBetaR m j) := by
  refine beta_hasCompactSupport.mono ?_
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hb
  exact hz (by simp [polyBetaR, hb])

lemma polyBetaC_cd (m : ℕ) (j : Fin 3) (n : ℕ) : ContDiff ℝ n (polyBetaC m j) :=
  Complex.ofRealCLM.contDiff.comp (polyBetaR_cd m j n)

lemma polyBetaC_continuous (m : ℕ) (j : Fin 3) : Continuous (polyBetaC m j) :=
  (polyBetaC_cd m j 0).continuous

lemma polyBetaC_hasCompactSupport (m : ℕ) (j : Fin 3) : HasCompactSupport (polyBetaC m j) :=
  (polyBetaR_hasCompactSupport m j).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)

lemma polyBetaC_integrable (m : ℕ) (j : Fin 3) : Integrable (polyBetaC m j) :=
  Continuous.integrable_of_hasCompactSupport (polyBetaC_continuous m j)
    (polyBetaC_hasCompactSupport m j)

-- ===============================================================
-- the Fourier transform of a continuous, compactly supported function
-- ===============================================================

/-- The Fourier transform of an integrable function is continuous. -/
lemma continuous_fourier_of_integrable {f : E3 → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

/-- The moment integrability of the Fourier transform of a smooth compactly supported function. -/
lemma integrable_fourier_moment {F : E3 → ℝ} (hF : ∀ n : ℕ, ContDiff ℝ n F)
    (hFs : HasCompactSupport F) :
    Integrable (fun η : E3 => (1 + ‖η‖) * ‖𝓕 (fun x : E3 => (F x : ℂ)) η‖) := by
  have hcs : HasCompactSupport (fun x : E3 => (F x : ℂ)) :=
    hFs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hcd : ContDiff ℝ ∞ (fun x : E3 => (F x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_infty.mpr hF)
  let Fs : SchwartzMap E3 ℂ := HasCompactSupport.toSchwartzMap hcs hcd
  have hcoe : (Fs : E3 → ℂ) = fun x : E3 => (F x : ℂ) := rfl
  let Phi : SchwartzMap E3 ℂ := 𝓕 Fs
  have hPcoe : (Phi : E3 → ℂ) = 𝓕 (fun x : E3 => (F x : ℂ)) := by
    rw [show (Phi : E3 → ℂ) = 𝓕 (Fs : E3 → ℂ) from SchwartzMap.fourier_coe Fs, hcoe]
  have h0 : Integrable (fun η : E3 => (Phi : E3 → ℂ) η) := SchwartzMap.integrable (μ := volume) Phi
  have h1 : Integrable (fun η : E3 => ‖η‖ ^ 1 * ‖(Phi : E3 → ℂ) η‖) :=
    SchwartzMap.integrable_pow_mul (μ := volume) Phi 1
  have h0' : Integrable (fun η : E3 => 𝓕 (fun x : E3 => (F x : ℂ)) η) := by
    rw [← hPcoe]; exact h0
  have h1' : Integrable (fun η : E3 => ‖η‖ ^ 1 * ‖𝓕 (fun x : E3 => (F x : ℂ)) η‖) := by
    rw [← hPcoe]; exact h1
  have heq : (fun η : E3 => (1 + ‖η‖) * ‖𝓕 (fun x : E3 => (F x : ℂ)) η‖)
      = fun η : E3 => ‖𝓕 (fun x : E3 => (F x : ℂ)) η‖ + ‖η‖ ^ 1 * ‖𝓕 (fun x : E3 => (F x : ℂ)) η‖ := by
    funext η; ring
  have hmain : Integrable (fun η : E3 => (1 + ‖η‖) * ‖𝓕 (fun x : E3 => (F x : ℂ)) η‖) := by
    rw [heq]; exact h0'.norm.add h1'
  exact hmain

/-- The weight `(1+‖·‖)` times `𝓕` of a smooth compactly supported function is bounded. -/
lemma bounded_fourier_moment {F : E3 → ℝ} (hF : ∀ n : ℕ, ContDiff ℝ n F)
    (hFs : HasCompactSupport F) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∀ ν : E3, (1 + ‖ν‖) * ‖𝓕 (fun x : E3 => (F x : ℂ)) ν‖ ≤ CA := by
  have hcs : HasCompactSupport (fun x : E3 => (F x : ℂ)) :=
    hFs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hcd : ContDiff ℝ ∞ (fun x : E3 => (F x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_infty.mpr hF)
  let Fs : SchwartzMap E3 ℂ := HasCompactSupport.toSchwartzMap hcs hcd
  have hcoe : (Fs : E3 → ℂ) = fun x : E3 => (F x : ℂ) := rfl
  let Phi : SchwartzMap E3 ℂ := 𝓕 Fs
  have hPcoe : (Phi : E3 → ℂ) = 𝓕 (fun x : E3 => (F x : ℂ)) := by
    rw [show (Phi : E3 → ℂ) = 𝓕 (Fs : E3 → ℂ) from SchwartzMap.fourier_coe Fs, hcoe]
  refine ⟨(SchwartzMap.seminorm ℂ 0 0 Phi : ℝ) + (SchwartzMap.seminorm ℂ 1 0 Phi : ℝ),
    by positivity, fun ν => ?_⟩
  have h0 : ‖(Phi : E3 → ℂ) ν‖ ≤ (SchwartzMap.seminorm ℂ 0 0 Phi : ℝ) :=
    SchwartzMap.norm_le_seminorm ℂ Phi ν
  have h1 : ‖ν‖ ^ 1 * ‖(Phi : E3 → ℂ) ν‖ ≤ (SchwartzMap.seminorm ℂ 1 0 Phi : ℝ) :=
    SchwartzMap.norm_pow_mul_le_seminorm ℂ Phi 1 ν
  have h0' : ‖𝓕 (fun x : E3 => (F x : ℂ)) ν‖ ≤ (SchwartzMap.seminorm ℂ 0 0 Phi : ℝ) := by
    rw [← hPcoe]; exact h0
  have h1' : ‖ν‖ ^ 1 * ‖𝓕 (fun x : E3 => (F x : ℂ)) ν‖
      ≤ (SchwartzMap.seminorm ℂ 1 0 Phi : ℝ) := by
    rw [← hPcoe]; exact h1
  have h2 : (1 + ‖ν‖) * ‖𝓕 (fun x : E3 => (F x : ℂ)) ν‖
      = ‖𝓕 (fun x : E3 => (F x : ℂ)) ν‖ + ‖ν‖ * ‖𝓕 (fun x : E3 => (F x : ℂ)) ν‖ := by ring
  rw [h2]
  linarith [h0', h1']

-- ===============================================================
-- the two complex-linearity facts for 𝓕 on functions
-- ===============================================================

lemma fourier_add_of_integrable {f g : E3 → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (f + g) = 𝓕 f + 𝓕 g :=
  VectorFourier.fourierIntegral_add Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf hg

lemma fourier_const_smul (c : ℂ) (f : E3 → ℂ) : 𝓕 (c • f) = c • 𝓕 f :=
  VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (innerₗ E3) f c

-- ===============================================================
-- the product law for the moment of 𝓕
-- ===============================================================

/-- **The moment law for `𝓕(A · B)`.**  If `G` is integrable with integrable first moment and
`B x = ∫ η, 𝐞⟪η,x⟫ • G η`, and if `𝓕 A` has a bounded weight `(1+‖·‖)` and an integrable one, then
the weighted `L¹`-moment of `𝓕(A·B)` is integrable and bounded by the product of the moments. -/
lemma fourierMoment_mul_le {A B G : E3 → ℂ} {CA : ℝ}
    (hA : Integrable A) (hG : Integrable G) (hAB : Integrable (fun x => A x * B x))
    (hB : ∀ x : E3, B x = ∫ η : E3, Real.fourierChar (inner ℝ η x) • G η)
    (hAm : Integrable (fun ν : E3 => (1 + ‖ν‖) * ‖𝓕 A ν‖))
    (hCA : ∀ ν : E3, (1 + ‖ν‖) * ‖𝓕 A ν‖ ≤ CA)
    (hGm : Integrable (fun η : E3 => (1 + ‖η‖) * ‖G η‖)) :
    Integrable (fun ν : E3 => (1 + ‖ν‖) * ‖𝓕 (fun x => A x * B x) ν‖)
      ∧ (∫ ν : E3, (1 + ‖ν‖) * ‖𝓕 (fun x => A x * B x) ν‖)
          ≤ (∫ η : E3, (1 + ‖η‖) * ‖G η‖) * (∫ ν : E3, (1 + ‖ν‖) * ‖𝓕 A ν‖) := by
  set F : E3 → ℝ := fun η => (1 + ‖η‖) * ‖G η‖ with hFdef
  set H : E3 → ℝ := fun ν => (1 + ‖ν‖) * ‖𝓕 A ν‖ with hHdef
  have hFint : Integrable F := hGm
  have hHint : Integrable H := hAm
  obtain ⟨hconvint, hconvval⟩ := integrable_integral_integral_mul_sub hFint hHint
  have hAcont : Continuous (𝓕 A) := continuous_fourier_of_integrable hA
  have hCA' : ∀ w : E3, ‖𝓕 A w‖ ≤ CA := by
    intro w
    have h2 : ‖𝓕 A w‖ ≤ (1 + ‖w‖) * ‖𝓕 A w‖ := by
      nlinarith [norm_nonneg w, norm_nonneg (𝓕 A w)]
    linarith [hCA w]
  -- pointwise domination
  have hpt : ∀ ν : E3, (1 + ‖ν‖) * ‖𝓕 (fun x => A x * B x) ν‖ ≤ ∫ η, F η * H (ν - η) := by
    intro ν
    have h1 : 𝓕 (fun x => A x * B x) ν = ∫ η, G η * 𝓕 A (ν - η) :=
      fourier_mul_eq_integral_shift hA hG hB ν
    have hmeas : AEStronglyMeasurable (fun η : E3 => 𝓕 A (ν - η)) volume :=
      (hAcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    have hinner : Integrable (fun η : E3 => G η * 𝓕 A (ν - η)) :=
      Integrable.mul_bdd hG hmeas (Eventually.of_forall fun η => hCA' (ν - η))
    have hmeasH : AEStronglyMeasurable (fun η : E3 => H (ν - η)) volume := by
      rw [hHdef]
      exact hHint.aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume ν)
    have hinnerH : Integrable (fun η : E3 => F η * H (ν - η)) :=
      Integrable.mul_bdd hFint hmeasH (Eventually.of_forall fun η => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hCA (ν - η))
    rw [h1]
    refine (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
      (by positivity)).trans ?_
    rw [← integral_const_mul]
    have hpoint : ∀ η : E3, (1 + ‖ν‖) * ‖G η * 𝓕 A (ν - η)‖ ≤ F η * H (ν - η) := by
      intro η
      rw [norm_mul]
      have hkey : (1 + ‖ν‖) ≤ (1 + ‖η‖) * (1 + ‖ν - η‖) := by
        have hsplit : ‖ν‖ ≤ ‖η‖ + ‖ν - η‖ := by
          calc ‖ν‖ = ‖η + (ν - η)‖ := by rw [add_sub_cancel]
            _ ≤ ‖η‖ + ‖ν - η‖ := norm_add_le _ _
        nlinarith [norm_nonneg η, norm_nonneg (ν - η)]
      calc (1 + ‖ν‖) * (‖G η‖ * ‖𝓕 A (ν - η)‖)
          ≤ ((1 + ‖η‖) * (1 + ‖ν - η‖)) * (‖G η‖ * ‖𝓕 A (ν - η)‖) :=
            mul_le_mul_of_nonneg_right hkey (by positivity)
        _ = F η * H (ν - η) := by rw [hFdef, hHdef]; ring
    exact integral_mono_of_nonneg (Eventually.of_forall fun η => by positivity) hinnerH
      (Eventually.of_forall hpoint)
  refine ⟨?_, ?_⟩
  · have hcont : Continuous (fun ν : E3 => (1 + ‖ν‖) * ‖𝓕 (fun x => A x * B x) ν‖) :=
      (continuous_const.add continuous_norm).mul ((continuous_fourier_of_integrable hAB).norm)
    refine hconvint.mono' hcont.aestronglyMeasurable ?_
    · filter_upwards with ν
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpt ν
  · refine (integral_mono_of_nonneg (Eventually.of_forall fun ν => by positivity) hconvint
      (Eventually.of_forall hpt)).trans ?_
    rw [hconvval]

-- ===============================================================
-- the data for `A = polyBetaC m j`
-- ===============================================================

lemma polyBetaC_data (m : ℕ) (j : Fin 3) :
    ∃ CA MA : ℝ, 0 ≤ CA ∧ 0 ≤ MA ∧
      (∀ ν : E3, (1 + ‖ν‖) * ‖𝓕 (polyBetaC m j) ν‖ ≤ CA) ∧
      Integrable (fun ν : E3 => (1 + ‖ν‖) * ‖𝓕 (polyBetaC m j) ν‖) ∧
      (∫ ν : E3, (1 + ‖ν‖) * ‖𝓕 (polyBetaC m j) ν‖) = MA := by
  obtain ⟨CA, hCAnn, hCA⟩ := bounded_fourier_moment (polyBetaR_cd m j)
    (polyBetaR_hasCompactSupport m j)
  refine ⟨CA, ∫ ν : E3, (1 + ‖ν‖) * ‖𝓕 (polyBetaC m j) ν‖, hCAnn,
    integral_nonneg (fun ν => by positivity), hCA, ?_, rfl⟩
  exact integrable_fourier_moment (polyBetaR_cd m j) (polyBetaR_hasCompactSupport m j)

-- ===============================================================
-- the data for the compact `θ`-factor
-- ===============================================================

lemma thetaComp_data :
    ∃ Φ : E3 → ℂ, Integrable Φ ∧ Integrable (fun η : E3 => (1 + ‖η‖) * ‖Φ η‖) ∧
      (∀ x : E3, (thetaComp x : ℂ) = ∫ η : E3, Real.fourierChar (inner ℝ η x) • Φ η) := by
  obtain ⟨Φs, hΦrepr⟩ :=
    Work.BoseFixR.LatGreen.exists_schwartz_inversion thetaComp_cd thetaComp_hasCompactSupport
  refine ⟨(Φs : E3 → ℂ), SchwartzMap.integrable (μ := volume) Φs, ?_, fun x => hΦrepr x⟩
  have h0 := SchwartzMap.integrable (μ := volume) Φs
  have h1 := SchwartzMap.integrable_pow_mul (μ := volume) Φs 1
  have heq : (fun η : E3 => (1 + ‖η‖) * ‖(Φs : E3 → ℂ) η‖)
      = fun η : E3 => ‖(Φs : E3 → ℂ) η‖ + ‖η‖ ^ 1 * ‖(Φs : E3 → ℂ) η‖ := by
    funext η; ring
  rw [heq]; exact h0.norm.add h1

-- ===============================================================
-- the main theorem
-- ===============================================================

/-- Uniform-in-`ε` bound on the weighted `L¹`-moment of the Fourier transform of
`f_ε(z) = (z_j)^m · theta ((χ⋆χ)(ε•z)) · beta z`, for `0 < ε ≤ chiR0`.

Route that avoids any derivative bookkeeping (recommended):
write `f_ε = theta 0 · A + A · B̃_ε` with `A z = (z_j)^m · beta z` (a *fixed* smooth compactly
supported function) and `B̃_ε z = theta ((χ⋆χ)(ε•z)) - theta 0` (smooth, compactly supported
because `χ⋆χ` vanishes outside `ball 0 1`, `Submission.Work.BoseFixR.Rb5Lin.conv3_chi_eq_zero_of_one_lt_norm`).
Then `B̃_ε z = B̃_1 (ε•z)` and, with `Φ_1 := 𝓕 (fun x => (B̃_1 x : ℂ))` (a Schwartz function, by
`HasCompactSupport.toSchwartzMap` + `SchwartzMap.fourier`), Fourier inversion
(`Continuous.fourierInv_fourier_eq`, as used in `Work.BoseFixR.LatGreen.exists_schwartz_inversion`)
gives `B̃_1 x = ∫ η, 𝐞⟪η,x⟫ • Φ_1 η`, whence `B̃_ε x = ∫ u, 𝐞⟪u,x⟫ • (ε⁻³ • Φ_1 (ε⁻¹ • u))`
(one substitution in the integral). Then
`FourierTransform.fourier (f_ε : ℂ) ν = ∫ u, Φ_ε u * 𝓕(A:ℂ)(ν-u)` by
`Work.BoseFixR.LatGreen.fubini_mul_fourierChar`, and `(1+‖ν‖) ≤ (1+‖ν-u‖)(1+‖u‖)` turns the
moment integral into `M(A) · M̃(Φ_ε)` with `M̃(Φ_ε) = ∫(1+‖u‖)‖Φ_ε u‖ ≤ (1+chiR0) M̃(Φ_1)`
(scaling of the measure, `(1+ε‖η‖) ≤ (1+chiR0)(1+‖η‖)`). -/
theorem momentbound_theta_factor {m : ℕ} {j : Fin 3} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ Submission.BoseGases.chiR0 →
      (∫ η : EuclideanSpace ℝ (Fin 3),
          (1 + ‖η‖) * ‖FourierTransform.fourier
            (fun z : EuclideanSpace ℝ (Fin 3) =>
              (((((z.ofLp j) ^ m : ℝ)
                * Work.BoseBogFS.theta (Submission.BoseGases.convScale (ε⁻¹) z)
                * Work.BoseBogFS.beta z : ℝ)) : ℂ)) η‖) ≤ C := by
  obtain ⟨CA, MA, hCAnn, hMAnn, hCA, hAm, hMAeq⟩ := polyBetaC_data m j
  obtain ⟨Φ, hΦint, hΦm, hΦrepr⟩ := thetaComp_data
  set MB : ℝ := ∫ η : E3, (1 + ‖η‖) * ‖Φ η‖ with hMBdef
  have hMBnn : 0 ≤ MB := integral_nonneg (fun η => by positivity)
  set C : ℝ := |theta 0| * MA + (1 + Submission.BoseGases.chiR0) * MB * MA with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ (1 + Submission.BoseGases.chiR0) * MB * MA :=
      mul_nonneg (mul_nonneg (by linarith [Submission.BoseGases.chiR0_pos]) hMBnn) hMAnn
    nlinarith [abs_nonneg (theta 0)]
  refine ⟨C, hCnn, fun ε hε hεR => ?_⟩
  -- the dilated profile and its properties
  obtain ⟨hrepr, hGint, hGm⟩ := scaled_representation (F := thetaComp) hε hΦrepr hΦint hΦm
  have hGmint : Integrable (fun η : E3 => (1 + ‖η‖) * ‖(ε ^ 3)⁻¹ • Φ (ε⁻¹ • η)‖) :=
    scaled_moment_integrable hε hΦint hΦm
  set G : E3 → ℂ := fun η => (ε ^ 3)⁻¹ • Φ (ε⁻¹ • η) with hGdef
  have hGrepr : ∀ x : E3, thetaCompScale ε x = ∫ η : E3, Real.fourierChar (inner ℝ η x) • G η :=
    fun x => hrepr x
  -- the two summands
  have hAint : Integrable (polyBetaC m j) := polyBetaC_integrable m j
  obtain ⟨cBdd, hcBddnn, hcBdd⟩ := thetaComp_bdd
  have hBdd : ∀ z : E3, ‖thetaCompScale ε z‖ ≤ cBdd := by
    intro z
    show ‖((thetaComp (ε • z) : ℝ) : ℂ)‖ ≤ cBdd
    simpa using hcBdd (ε • z)
  have hBcont : Continuous (thetaCompScale ε) := by
    have h1 : Continuous (fun z : E3 => ε • z) := by fun_prop
    have h2 : Continuous (fun z : E3 => thetaComp (ε • z)) := thetaComp_continuous.comp h1
    exact Complex.continuous_ofReal.comp h2
  have hABint : Integrable (fun z : E3 => polyBetaC m j z * thetaCompScale ε z) :=
    Integrable.mul_bdd hAint hBcont.aestronglyMeasurable (Eventually.of_forall hBdd)
  -- the decomposition `fTheta = c • A + A · B̃_ε`
  have hdecomp : fTheta m j ε
      = (fun z : E3 => polyBetaC m j z * ((theta 0 : ℝ) : ℂ))
        + (fun z : E3 => polyBetaC m j z * thetaCompScale ε z) := by
    funext z
    have hconv : Submission.BoseGases.convScale (ε⁻¹) z = chiConv (ε • z) := by
      simp only [chiConv, Submission.BoseGases.convScale, inv_inv]
    have hth : theta (Submission.BoseGases.convScale (ε⁻¹) z)
        = theta 0 + thetaComp (ε • z) := by
      rw [hconv, thetaComp]; ring
    show ((((z.ofLp j) ^ m * theta (Submission.BoseGases.convScale (ε⁻¹) z) * beta z : ℝ)) : ℂ) = _
    rw [hth]
    simp only [Pi.add_apply, thetaCompScale, polyBetaC, polyBetaR]
    push_cast
    ring
  have hAint' : Integrable (fun z : E3 => polyBetaC m j z * ((theta 0 : ℝ) : ℂ)) :=
    hAint.mul_const _
  -- moment bound for the two summands
  obtain ⟨hI2int, hI2⟩ := fourierMoment_mul_le (A := polyBetaC m j) (B := thetaCompScale ε)
    (G := G) hAint hGint hABint hGrepr hAm hCA hGmint
  have hI1point : ∀ ν : E3, (1 + ‖ν‖) * ‖𝓕 (fun z : E3 => polyBetaC m j z * ((theta 0 : ℝ) : ℂ)) ν‖
      = |theta 0| * ((1 + ‖ν‖) * ‖𝓕 (polyBetaC m j) ν‖) := by
    intro ν
    have hfun : (fun z : E3 => polyBetaC m j z * ((theta 0 : ℝ) : ℂ))
        = ((theta 0 : ℝ) : ℂ) • (polyBetaC m j) := by
      funext z; rw [Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [hfun, fourier_const_smul]
    rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    ring
  have hI1int : Integrable (fun ν : E3 =>
      (1 + ‖ν‖) * ‖𝓕 (fun z : E3 => polyBetaC m j z * ((theta 0 : ℝ) : ℂ)) ν‖) := by
    rw [show (fun ν : E3 => (1 + ‖ν‖) * ‖𝓕 (fun z : E3 => polyBetaC m j z * ((theta 0 : ℝ) : ℂ)) ν‖)
        = fun ν : E3 => |theta 0| * ((1 + ‖ν‖) * ‖𝓕 (polyBetaC m j) ν‖) from
        funext hI1point]
    exact hAm.const_mul _
  have hI1val : (∫ ν : E3,
      (1 + ‖ν‖) * ‖𝓕 (fun z : E3 => polyBetaC m j z * ((theta 0 : ℝ) : ℂ)) ν‖)
      = |theta 0| * MA := by
    rw [show (fun ν : E3 => (1 + ‖ν‖) * ‖𝓕 (fun z : E3 => polyBetaC m j z * ((theta 0 : ℝ) : ℂ)) ν‖)
        = fun ν : E3 => |theta 0| * ((1 + ‖ν‖) * ‖𝓕 (polyBetaC m j) ν‖) from
        funext hI1point]
    rw [integral_const_mul, hMAeq]
  -- assemble
  have hGM : (∫ η : E3, (1 + ‖η‖) * ‖G η‖) ≤ (1 + ε) * MB := by
    rw [hGdef, hMBdef]
    exact hGm
  have hIM : (∫ η : E3, (1 + ‖η‖) * ‖G η‖) ≤ (1 + Submission.BoseGases.chiR0) * MB :=
    hGM.trans (mul_le_mul_of_nonneg_right (by linarith) hMBnn)
  have hsum_int : Integrable (fun ν : E3 =>
      (1 + ‖ν‖) * (‖𝓕 (fun z : E3 => polyBetaC m j z * ((theta 0 : ℝ) : ℂ)) ν‖
        + ‖𝓕 (fun z : E3 => polyBetaC m j z * thetaCompScale ε z) ν‖)) := by
    have h := hI1int.add hI2int
    refine h.congr (Eventually.of_forall fun ν => ?_)
    simp only [Pi.add_apply]
    ring
  have hsub : ∀ ν : E3, ‖𝓕 (fTheta m j ε) ν‖
      ≤ ‖𝓕 (fun z : E3 => polyBetaC m j z * ((theta 0 : ℝ) : ℂ)) ν‖
        + ‖𝓕 (fun z : E3 => polyBetaC m j z * thetaCompScale ε z) ν‖ := by
    intro ν
    have hfun : 𝓕 (fTheta m j ε)
        = 𝓕 (fun z : E3 => polyBetaC m j z * ((theta 0 : ℝ) : ℂ))
          + 𝓕 (fun z : E3 => polyBetaC m j z * thetaCompScale ε z) := by
      rw [hdecomp]
      exact fourier_add_of_integrable hAint' hABint
    rw [hfun]
    exact norm_add_le _ _
  have hmain : (∫ ν : E3, (1 + ‖ν‖) * ‖𝓕 (fTheta m j ε) ν‖)
      ≤ |theta 0| * MA + ((1 + Submission.BoseGases.chiR0) * MB) * MA := by
    have hstep : (∫ ν : E3, (1 + ‖ν‖) * ‖𝓕 (fTheta m j ε) ν‖)
        ≤ ∫ ν : E3, (1 + ‖ν‖) * (‖𝓕 (fun z : E3 => polyBetaC m j z * ((theta 0 : ℝ) : ℂ)) ν‖
            + ‖𝓕 (fun z : E3 => polyBetaC m j z * thetaCompScale ε z) ν‖) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun ν => by positivity) hsum_int
        (Eventually.of_forall fun ν => ?_)
      exact mul_le_mul_of_nonneg_left (hsub ν) (by positivity)
    refine hstep.trans ?_
    have hsplit : (∫ ν : E3,
          (1 + ‖ν‖) * (‖𝓕 (fun z : E3 => polyBetaC m j z * ((theta 0 : ℝ) : ℂ)) ν‖
            + ‖𝓕 (fun z : E3 => polyBetaC m j z * thetaCompScale ε z) ν‖))
        = (∫ ν : E3, (1 + ‖ν‖) * ‖𝓕 (fun z : E3 => polyBetaC m j z * ((theta 0 : ℝ) : ℂ)) ν‖)
          + (∫ ν : E3, (1 + ‖ν‖) * ‖𝓕 (fun z : E3 => polyBetaC m j z * thetaCompScale ε z) ν‖) := by
      rw [← integral_add hI1int hI2int]
      refine integral_congr_ae (Eventually.of_forall fun ν => ?_)
      ring
    rw [hsplit, hI1val]
    have hI2' : (∫ ν : E3, (1 + ‖ν‖) * ‖𝓕 (fun z : E3 => polyBetaC m j z * thetaCompScale ε z) ν‖)
        ≤ ((1 + Submission.BoseGases.chiR0) * MB) * MA := by
      rw [← hMAeq]
      exact hI2.trans (mul_le_mul_of_nonneg_right hIM
        (integral_nonneg (fun ν => by positivity)))
    exact add_le_add le_rfl hI2'
  have hfin : (∫ ν : E3, (1 + ‖ν‖) * ‖𝓕 (fTheta m j ε) ν‖) ≤ C := by
    refine hmain.trans (le_of_eq ?_)
    rw [hCdef]
  exact hfin

end Work.BoseBogFS
