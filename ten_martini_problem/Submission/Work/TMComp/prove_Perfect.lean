import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.PerfectDefs
import Submission.Work.TMComp.Perfect.proj_spec
import Submission.Work.TMComp.Perfect.amoOp_selfadjoint
import Submission.Work.TMComp.Perfect.amoOp_norm_sub
import Submission.Work.TMComp.Perfect.amoOp_covariance
import Submission.Work.TMComp.Perfect.phase_independence
import Submission.Work.TMComp.Perfect.proj_continuous
import Submission.Work.TMComp.Perfect.kernel_dim_le_one
import Submission.Work.TMComp.Perfect.proj_apply_unit
import Submission.Work.TMComp.Perfect.no_periodic_partition

/-!
# C2 (`P_Perfect`): the spectrum of the almost Mathieu operator has no isolated points

Main argument (Avila--Jitomirskaya, `TMPlan/ROUTE_LEAD.md` C2): if `E` is isolated in the
spectrum `Σ` of `amoOp α lam θ₀` for irrational `α`, then by phase independence `E` is isolated in
the spectrum of `amoOp α lam θ` for *every* phase `θ`, the canonical spectral projection
`proj α lam θ E δ` is a nonzero self-adjoint idempotent with range the one-dimensional eigenspace
of `E`, and `G θ = ‖proj α lam θ E δ δ₀‖²` satisfies `∑_n G (θ + nα) = 1` for every `θ`.
`G` is continuous and `1`-periodic, and `no_periodic_partition` gives a contradiction.
-/

open LeanEval.Analysis.TenMartini
open Work.TMContract
open Work.TMComp.Perfect
open scoped ENNReal

noncomputable section

namespace Work.TMComp

namespace C2

/-! ## 0. Auxiliary lemmas (proved by colleagues; see `Submission/Work/TMComp/Perfect/`) -/

theorem amoOp_selfadjoint_aux (α lam θ : ℝ) : IsSelfAdjoint (amoOp α lam θ) :=
  amoOp_selfadjoint α lam θ

theorem amoOp_norm_sub_aux (α lam θ θ' : ℝ) :
    ‖amoOp α lam θ - amoOp α lam θ'‖ ≤ 4 * Real.pi * |lam| * |θ - θ'| :=
  amoOp_norm_sub α lam θ θ'

theorem amoOp_covariance_aux (α lam θ : ℝ) (k : ℤ) :
    sh k * amoOp α lam θ = amoOp α lam (θ + (k : ℝ) * α) * sh k :=
  amoOp_covariance α lam θ k

theorem phase_independence_aux (α lam : ℝ) (hα : Irrational α) (θ θ' : ℝ)
    (hsa : ∀ θ₀ : ℝ, IsSelfAdjoint (amoOp α lam θ₀))
    (hnc : ∀ θ₁ θ₂ : ℝ, ‖amoOp α lam θ₁ - amoOp α lam θ₂‖ ≤ 4 * Real.pi * |lam| * |θ₁ - θ₂|) :
    spectrum ℂ (amoOp α lam θ) = spectrum ℂ (amoOp α lam θ') :=
  phase_independence α lam hα θ θ' hsa hnc

theorem proj_spec_aux (α lam θ : ℝ) (E δ : ℝ) (hδ : 0 < δ)
    (hE : (E : ℂ) ∈ spectrum ℂ (amoOp α lam θ))
    (hsa : IsSelfAdjoint (amoOp α lam θ))
    (hiso : ∀ x ∈ spectrum ℂ (amoOp α lam θ), ‖x - (E : ℂ)‖ < δ → x = (E : ℂ)) :
    proj α lam θ E δ * proj α lam θ E δ = proj α lam θ E δ ∧
      star (proj α lam θ E δ) = proj α lam θ E δ ∧
      proj α lam θ E δ ≠ 0 ∧
      (amoOp α lam θ - (E : ℂ) • 1) * proj α lam θ E δ = 0 :=
  proj_spec α lam θ E δ hδ hE hsa hiso

theorem proj_continuous_aux (α lam : ℝ) (E δ : ℝ) (s : Set ℂ)
    (hsa : ∀ θ : ℝ, IsSelfAdjoint (amoOp α lam θ))
    (hnc : ∀ θ θ' : ℝ, ‖amoOp α lam θ - amoOp α lam θ'‖ ≤ 4 * Real.pi * |lam| * |θ - θ'|)
    (hcont : ContinuousOn (projFun E δ) s)
    (hspec : ∀ θ : ℝ, spectrum ℂ (amoOp α lam θ) ⊆ s) :
    Continuous (fun θ : ℝ => proj α lam θ E δ) :=
  proj_continuous α lam E δ s hsa hnc hcont hspec

theorem kernel_dim_le_one_aux (α lam θ E : ℝ) (H : EllTwo →L[ℂ] EllTwo)
    (hH : IsAlmostMathieuOperator α lam θ H) {u v : EllTwo}
    (hu : H u = (E : ℂ) • u) (hv : H v = (E : ℂ) • v) :
    ∃ c : ℂ, v = c • u ∨ u = c • v :=
  kernel_dim_le_one α lam θ E H hH hu hv

theorem proj_apply_unit_aux (P : EllTwo →L[ℂ] EllTwo) (hP : P * P = P) (hPstar : star P = P)
    {u : EllTwo} (hu : ‖u‖ = 1) (hPu : P u = u)
    (hrange : ∀ w : EllTwo, P w = w → ∃ c : ℂ, w = c • u) :
    ∀ x : EllTwo, P x = (inner ℂ u x) • u :=
  proj_apply_unit P hP hPstar hu hPu hrange

theorem no_periodic_partition_aux (G : ℝ → ℝ) (α : ℝ) (hmeas : Measurable G)
    (hnn : ∀ x : ℝ, 0 ≤ G x) (hper : ∀ x : ℝ, G (x + 1) = G x)
    (hsum : ∀ x : ℝ, ∑' n : ℤ, ENNReal.ofReal (G (x + (n : ℝ) * α)) = 1) : False :=
  no_periodic_partition G α hmeas hnn hper hsum

/-! ## 1. The vector `δ₀` -/

/-- The standard basis vector `δ₀` of `ℓ²(ℤ)`. -/
def delta0 : EllTwo := lp.single 2 (0 : ℤ) (1 : ℂ)

@[simp] theorem delta0_apply : delta0 0 = (1 : ℂ) := lp.single_apply_self 2 0 1

theorem delta0_apply_ne {n : ℤ} (h : n ≠ 0) : delta0 n = 0 := lp.single_apply_ne 2 0 1 h

theorem norm_delta0 : ‖delta0‖ = 1 := by
  rw [delta0, lp.norm_single (show (0 : ℝ≥0∞) < 2 by norm_num)]
  norm_num

/-! ## 2. The eigenspace at an isolated spectral point -/

theorem exists_unit_eigenvector (α lam θ E δ : ℝ) (hδ : 0 < δ)
    (hE : (E : ℂ) ∈ spectrum ℂ (amoOp α lam θ)) (hsa : IsSelfAdjoint (amoOp α lam θ))
    (hiso : ∀ x ∈ spectrum ℂ (amoOp α lam θ), ‖x - (E : ℂ)‖ < δ → x = (E : ℂ)) :
    ∃ u : EllTwo, ‖u‖ = 1 ∧ amoOp α lam θ u = (E : ℂ) • u ∧
      (∀ w : EllTwo, amoOp α lam θ w = (E : ℂ) • w → ∃ c : ℂ, w = c • u) ∧
      (∀ x : EllTwo, proj α lam θ E δ x = (inner ℂ u x) • u) := by
  obtain ⟨hPidem, hPstar, hPne, hPkill⟩ := proj_spec_aux α lam θ E δ hδ hE hsa hiso
  obtain ⟨x, hx⟩ : ∃ x : EllTwo, proj α lam θ E δ x ≠ 0 := by
    by_contra h
    exact hPne (ContinuousLinearMap.ext (by simpa using h))
  set u₀ : EllTwo := proj α lam θ E δ x with hu₀
  have hu₀ne : u₀ ≠ 0 := hx
  have hu₀pos : 0 < ‖u₀‖ := norm_pos_iff.mpr hu₀ne
  have hPidem_u₀ : proj α lam θ E δ u₀ = u₀ := by
    have h := congrArg (fun T : EllTwo →L[ℂ] EllTwo => T x) hPidem
    simp only [ContinuousLinearMap.mul_apply] at h
    exact h
  have hker₀ : amoOp α lam θ u₀ = (E : ℂ) • u₀ := by
    have h := congrArg (fun T : EllTwo →L[ℂ] EllTwo => T x) hPkill
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply, sub_apply,
      smul_apply, one_apply_eq_self] at h
    rw [← hu₀] at h
    exact sub_eq_zero.mp h
  set c : ℂ := (((‖u₀‖ : ℝ)⁻¹ : ℝ) : ℂ) with hc
  set u : EllTwo := c • u₀ with hu
  have hcne : c ≠ 0 := by
    rw [hc]
    intro hzero
    exact inv_ne_zero (ne_of_gt hu₀pos) (by exact_mod_cast hzero)
  have hu_ne : u ≠ 0 := by
    rw [hu]
    exact smul_ne_zero hcne hu₀ne
  have hu_norm : ‖u‖ = 1 := by
    rw [hu, norm_smul, hc, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (ne_of_gt hu₀pos)]
  have hu_ker : amoOp α lam θ u = (E : ℂ) • u := by
    rw [hu, map_smul, hker₀, smul_comm]
  have hPu : proj α lam θ E δ u = u := by
    rw [hu, map_smul, hPidem_u₀]
  have hker_line : ∀ w : EllTwo, amoOp α lam θ w = (E : ℂ) • w → ∃ d : ℂ, w = d • u := by
    intro w hw
    rcases kernel_dim_le_one_aux α lam θ E (amoOp α lam θ) (amoOp_isAMO α lam θ) hu_ker hw with
      ⟨a, ha | ha⟩
    · exact ⟨a, ha⟩
    · have ha0 : a ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at ha
        exact hu_ne ha
      refine ⟨a⁻¹, ?_⟩
      rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  have hrange : ∀ w : EllTwo, proj α lam θ E δ w = w → ∃ d : ℂ, w = d • u := by
    intro w hw
    have hwker : amoOp α lam θ w = (E : ℂ) • w := by
      have h := congrArg (fun T : EllTwo →L[ℂ] EllTwo => T w) hPkill
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply, sub_apply,
        smul_apply, one_apply_eq_self] at h
      rw [hw] at h
      exact sub_eq_zero.mp h
    exact hker_line w hwker
  exact ⟨u, hu_norm, hu_ker, hker_line,
    proj_apply_unit_aux (u := u) _ hPidem hPstar hu_norm hPu hrange⟩

/-! ## 3. Covariance: the shift moves eigenspaces to shifted phases -/

theorem kernel_shift (α lam θ E : ℝ) (k : ℤ) {v : EllTwo}
    (hv : amoOp α lam θ v = (E : ℂ) • v) :
    amoOp α lam (θ + (k : ℝ) * α) (sh k v) = (E : ℂ) • (sh k v) := by
  have h := congrArg (fun T : EllTwo →L[ℂ] EllTwo => T v) (amoOp_covariance_aux α lam θ k)
  simp only [ContinuousLinearMap.mul_apply] at h
  rw [← h, hv, map_smul]

/-! ## 4. The key sum identity -/

theorem tsum_sq_norm (u : EllTwo) : ∑' n : ℤ, ‖u n‖ ^ (2 : ℕ) = ‖u‖ ^ (2 : ℕ) := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℤ => ℂ)
    (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num) u
  simpa using h.symm

theorem summable_sq_norm (u : EllTwo) : Summable (fun n : ℤ => ‖u n‖ ^ (2 : ℕ)) := by
  have h := (lp.memℓp u).summable (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num)
  simpa using h

theorem tsum_proj_sq (α lam : ℝ) (θ E δ : ℝ) (hδ : 0 < δ)
    (hsa : ∀ θ₀ : ℝ, IsSelfAdjoint (amoOp α lam θ₀))
    (hphase : ∀ θ₁ θ₂ : ℝ, spectrum ℂ (amoOp α lam θ₁) = spectrum ℂ (amoOp α lam θ₂))
    (hE : (E : ℂ) ∈ spectrum ℂ (amoOp α lam θ))
    (hiso : ∀ θ₁ : ℝ, ∀ x ∈ spectrum ℂ (amoOp α lam θ₁), ‖x - (E : ℂ)‖ < δ → x = (E : ℂ)) :
    Summable (fun n : ℤ => ‖proj α lam (θ + (n : ℝ) * α) E δ delta0‖ ^ (2 : ℕ)) ∧
      ∑' n : ℤ, ‖proj α lam (θ + (n : ℝ) * α) E δ delta0‖ ^ (2 : ℕ) = 1 := by
  obtain ⟨u, hu_norm, hu_ker, hu_span, hu_proj⟩ :=
    exists_unit_eigenvector α lam θ E δ hδ hE (hsa θ) (hiso θ)
  have key : ∀ n : ℤ, ‖proj α lam (θ + (n : ℝ) * α) E δ delta0‖ ^ (2 : ℕ) = ‖u n‖ ^ (2 : ℕ) := by
    intro n
    obtain ⟨uₙ, huₙ_norm, huₙ_ker, huₙ_span, huₙ_proj⟩ :=
      exists_unit_eigenvector α lam (θ + (n : ℝ) * α) E δ hδ
        (by rw [hphase (θ + (n : ℝ) * α) θ]; exact hE) (hsa _) (hiso _)
    have hsh_ker : amoOp α lam (θ + (n : ℝ) * α) (sh n u) = (E : ℂ) • (sh n u) :=
      kernel_shift α lam θ E n hu_ker
    have hsh_norm : ‖sh n u‖ = 1 := by rw [sh_isometry, hu_norm]
    obtain ⟨b, hb⟩ := huₙ_span (sh n u) hsh_ker
    have hb_abs : ‖b‖ = 1 := by
      have h : ‖sh n u‖ = ‖b‖ * ‖uₙ‖ := by rw [hb, norm_smul]
      rw [hsh_norm, huₙ_norm, mul_one] at h
      exact h.symm
    have hval : ‖proj α lam (θ + (n : ℝ) * α) E δ delta0‖ = ‖uₙ 0‖ := by
      rw [huₙ_proj delta0, norm_smul, huₙ_norm, mul_one]
      rw [delta0, lp.inner_single_right, RCLike.inner_apply, one_mul, Complex.norm_conj]
    rw [hval]
    have h0 : ‖uₙ 0‖ = ‖(sh n u) 0‖ := by
      have h1 : (sh n u) 0 = b * (uₙ 0) := by rw [hb]; rfl
      rw [h1, norm_mul, hb_abs, one_mul]
    rw [h0, sh_apply]
    simp
  refine ⟨?_, ?_⟩
  · exact (summable_sq_norm u).congr (fun n => (key n).symm)
  · calc ∑' n : ℤ, ‖proj α lam (θ + (n : ℝ) * α) E δ delta0‖ ^ (2 : ℕ)
        = ∑' n : ℤ, ‖u n‖ ^ (2 : ℕ) := tsum_congr key
      _ = 1 := by rw [tsum_sq_norm, hu_norm]; norm_num

/-! ## 5. Measurability of `θ ↦ ‖proj α lam θ E δ δ₀‖²` -/

theorem measurable_proj_norm_sq (α lam : ℝ) (E δ : ℝ) (s : Set ℂ)
    (hsa : ∀ θ : ℝ, IsSelfAdjoint (amoOp α lam θ))
    (hnc : ∀ θ θ' : ℝ, ‖amoOp α lam θ - amoOp α lam θ'‖ ≤ 4 * Real.pi * |lam| * |θ - θ'|)
    (hcont : ContinuousOn (projFun E δ) s)
    (hspec : ∀ θ : ℝ, spectrum ℂ (amoOp α lam θ) ⊆ s) :
    Measurable (fun θ : ℝ => ‖proj α lam θ E δ delta0‖ ^ (2 : ℕ)) := by
  refine Continuous.measurable ?_
  have h1 : Continuous (fun θ : ℝ => proj α lam θ E δ) :=
    proj_continuous_aux α lam E δ s hsa hnc hcont hspec
  have h2 : Continuous (fun θ : ℝ => proj α lam θ E δ delta0) :=
    (ContinuousLinearMap.apply ℂ EllTwo delta0).continuous.comp h1
  exact h2.norm.pow 2

end C2

/-! ## 6. The component -/

theorem prove_Perfect : Work.TMContract.P_Perfect := by
  intro α lam θ₀ hα H hH
  rw [amoOp_unique hH]
  have hsa : ∀ θ : ℝ, IsSelfAdjoint (amoOp α lam θ) := fun θ => C2.amoOp_selfadjoint_aux α lam θ
  have hnc : ∀ θ₁ θ₂ : ℝ, ‖amoOp α lam θ₁ - amoOp α lam θ₂‖
      ≤ 4 * Real.pi * |lam| * |θ₁ - θ₂| := fun θ₁ θ₂ => C2.amoOp_norm_sub_aux α lam θ₁ θ₂
  have hphase : ∀ θ θ' : ℝ, spectrum ℂ (amoOp α lam θ) = spectrum ℂ (amoOp α lam θ') :=
    fun θ θ' => C2.phase_independence_aux α lam hα θ θ' hsa hnc
  refine ⟨spectrum.isClosed (amoOp α lam θ₀), ?_⟩
  intro E hE
  have hre : E = ((E.re : ℝ) : ℂ) := (hsa θ₀).mem_spectrum_eq_re hE
  set E' : ℝ := E.re with hE'
  by_contra hacc
  rw [accPt_iff_nhds] at hacc
  push_neg at hacc
  obtain ⟨U, hU, hUiso⟩ := hacc
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hiso₀ : ∀ y ∈ spectrum ℂ (amoOp α lam θ₀), y ≠ E → ε ≤ dist E y := by
    intro y hy hne
    by_contra hlt
    push_neg at hlt
    have hyU : y ∈ U := hball (by rw [Metric.mem_ball]; rwa [dist_comm] at hlt)
    exact hne (hUiso y ⟨hyU, hy⟩)
  have hiso : ∀ θ : ℝ, ∀ x ∈ spectrum ℂ (amoOp α lam θ),
      ‖x - (E' : ℂ)‖ < ε / 2 → x = (E' : ℂ) := by
    intro θ x hx hx2
    by_contra hne
    have hx₀ : x ∈ spectrum ℂ (amoOp α lam θ₀) := by rw [← hphase θ θ₀]; exact hx
    have hne' : x ≠ E := by rw [hre]; simpa using hne
    have hle := hiso₀ x hx₀ hne'
    rw [dist_eq_norm] at hle
    rw [hre] at hle
    have hcomm : ‖x - (E' : ℂ)‖ = ‖(E' : ℂ) - x‖ := norm_sub_rev _ _
    linarith
  have hEθ : (E' : ℂ) ∈ spectrum ℂ (amoOp α lam θ₀) := by rw [← hre]; exact hE
  set δ : ℝ := ε / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hsum : ∀ θ : ℝ, ∑' n : ℤ,
      ENNReal.ofReal (‖proj α lam (θ + (n : ℝ) * α) E' δ C2.delta0‖ ^ (2 : ℕ)) = 1 := by
    intro θ
    have hEθ' : (E' : ℂ) ∈ spectrum ℂ (amoOp α lam θ) := by
      rw [hphase θ θ₀]; exact hEθ
    obtain ⟨hsumm, hval⟩ := C2.tsum_proj_sq α lam θ E' δ hδ hsa hphase hEθ' hiso
    have h2 : ENNReal.ofReal (∑' n : ℤ,
        ‖proj α lam (θ + (n : ℝ) * α) E' δ C2.delta0‖ ^ (2 : ℕ))
        = ∑' n : ℤ, ENNReal.ofReal
            (‖proj α lam (θ + (n : ℝ) * α) E' δ C2.delta0‖ ^ (2 : ℕ)) :=
      ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm
    rw [← h2, hval]
    norm_num
  have hmeas : Measurable
      (fun θ : ℝ => ‖proj α lam θ E' δ C2.delta0‖ ^ (2 : ℕ)) :=
    C2.measurable_proj_norm_sq α lam E' δ Set.univ hsa hnc
      (projFun_continuous E' δ).continuousOn (fun θ => Set.subset_univ _)
  have hper : ∀ θ : ℝ, ‖proj α lam (θ + 1) E' δ C2.delta0‖ ^ (2 : ℕ)
      = ‖proj α lam θ E' δ C2.delta0‖ ^ (2 : ℕ) := by
    intro θ
    have hp : amoOp α lam (θ + 1) = amoOp α lam θ := amoOp_periodic α lam θ
    simp only [proj, hp]
  exact C2.no_periodic_partition_aux
    (fun θ : ℝ => ‖proj α lam θ E' δ C2.delta0‖ ^ (2 : ℕ)) α hmeas
    (fun θ => by positivity) hper hsum

end Work.TMComp
