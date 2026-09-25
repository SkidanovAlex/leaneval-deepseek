import Mathlib
import Submission.Work.NN.Core.czB_L2_defs
import Submission.Work.NN.Core.czB_L2_aux
import Submission.Work.NN.Core.czbL2_kernel_laplacian
import Submission.Work.NN.Core.czbL2_energy
import Submission.Work.NN.Core.czbL2_energy_eq_dbar
import Submission.Work.NN.Core.czbL2_dCoord_decay
import Submission.Work.CR.Flat.integral_mul_dbarCoord_eq_neg
import Submission.Work.NN.Core.integral_normSq_dCoord_eq_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv

set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace Work.NN.Core

open Work.CR.Flat.Cauchy


private lemma czbL2bs_two_le_smooth : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr le_top

private lemma czbL2bs_one_le_smooth : ((1 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr le_top

private lemma czbL2bs_finrank_fin_complex (n : ℕ) : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_comm _ _

/-- The `∂_k`-derivative of the Bochner–Martinelli potential decays like `(1+‖z‖)^{-2n}`. -/
private lemma czbL2bs_bmPotential_dCoord_bound {n : ℕ} (hn : 0 < n) {h : Fin n → (Fin n → ℂ) → ℂ}
    (hh2 : ∀ j, ContDiff ℝ 2 (h j)) (hcs : ∀ j, HasCompactSupport (h j)) (k : Fin n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Fin n → ℂ,
      ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ≤ K * (1 + ‖z‖) ^ (-(2 * (n : ℝ))) := by
  obtain ⟨C₀, R₀, hC₀pos, hdec⟩ := czbL2_dCoord_decay hn hh2 hcs
  have hC₀nn : 0 ≤ C₀ := le_of_lt hC₀pos
  set R : ℝ := max R₀ 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hdecR : ∀ z : Fin n → ℂ, R ≤ ‖z‖ →
      ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ≤ C₀ * ‖z‖ ^ (-(2 * (n : ℝ))) :=
    fun z hz => hdec z (le_trans (le_max_left _ _) hz) k
  have hu1 : ContDiff ℝ 1 (bmPotential h) :=
    bmPotential_contDiff_of_hasCompactSupport hn (i := 1) (fun j => (hh2 j).of_le (by norm_num)) hcs
  have hcont : Continuous (fun z => Work.CR.Flat.dCoord k (bmPotential h) z) :=
    continuous_dCoord k hu1
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : Fin n → ℂ) R).exists_bound_of_continuousOn
    hcont.continuousOn
  set M : ℝ := max M₀ 0 with hMdef
  have hMnn : 0 ≤ M := le_max_right _ _
  have hM : ∀ z ∈ Metric.closedBall (0 : Fin n → ℂ) R,
      ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ≤ M :=
    fun z hz => le_trans (hM₀ z hz) (le_max_left _ _)
  have hexpnn : (0:ℝ) ≤ 2 * (n : ℝ) := by positivity
  have hAnn : 0 ≤ M * (1 + R) ^ (2 * (n : ℝ)) :=
    mul_nonneg hMnn (Real.rpow_nonneg (by linarith) _)
  have hBnn : 0 ≤ C₀ * ((R + 1) / R) ^ (2 * (n : ℝ)) :=
    mul_nonneg hC₀nn (Real.rpow_nonneg (by positivity) _)
  set K : ℝ := max (M * (1 + R) ^ (2 * (n : ℝ))) (C₀ * ((R + 1) / R) ^ (2 * (n : ℝ)))
    with hKdef
  have hKnn : 0 ≤ K := le_trans hAnn (le_max_left _ _)
  refine ⟨K, hKnn, fun z => ?_⟩
  rcases lt_or_ge ‖z‖ R with hz | hz
  · have hzmem : z ∈ Metric.closedBall (0 : Fin n → ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hz
    have h1 : ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ≤ M := hM z hzmem
    have hbase : (1 + R) ^ (-(2 * (n : ℝ))) ≤ (1 + ‖z‖) ^ (-(2 * (n : ℝ))) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have hprod : (1 + R) ^ (2 * (n : ℝ)) * (1 + R) ^ (-(2 * (n : ℝ))) = 1 := by
      rw [← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero]
    have h3 : M * (1 + R) ^ (2 * (n : ℝ)) ≤ K := le_max_left _ _
    calc ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ≤ M := h1
      _ = M * (1 + R) ^ (2 * (n : ℝ)) * (1 + R) ^ (-(2 * (n : ℝ))) := by
            rw [mul_assoc, hprod, mul_one]
      _ ≤ K * (1 + R) ^ (-(2 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (by linarith) _)
      _ ≤ K * (1 + ‖z‖) ^ (-(2 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hbase hKnn
  · have hzR : R ≤ ‖z‖ := hz
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hRpos hzR
    have h1 := hdecR z hzR
    have hbase : (1 + ‖z‖) / ‖z‖ ≤ (R + 1) / R := by
      rw [div_le_div_iff₀ (by positivity) hRpos]
      nlinarith [hzR]
    have hpow : ((1 + ‖z‖) / ‖z‖) ^ (2 * (n : ℝ)) ≤ ((R + 1) / R) ^ (2 * (n : ℝ)) :=
      Real.rpow_le_rpow (by positivity) hbase hexpnn
    have hsplit : ((1 + ‖z‖) / ‖z‖) ^ (2 * (n : ℝ)) * (1 + ‖z‖) ^ (-(2 * (n : ℝ)))
        = ‖z‖ ^ (-(2 * (n : ℝ))) := by
      rw [Real.div_rpow (by positivity) (le_of_lt hzpos), div_eq_mul_inv]
      rw [show ((1 + ‖z‖) ^ (2 * (n : ℝ)) * (‖z‖ ^ (2 * (n : ℝ)))⁻¹)
            * (1 + ‖z‖) ^ (-(2 * (n : ℝ)))
          = ((1 + ‖z‖) ^ (2 * (n : ℝ)) * (1 + ‖z‖) ^ (-(2 * (n : ℝ))))
            * (‖z‖ ^ (2 * (n : ℝ)))⁻¹ by ring]
      rw [← Real.rpow_add (by positivity : 0 < 1 + ‖z‖), add_neg_cancel, Real.rpow_zero,
        one_mul, Real.rpow_neg (le_of_lt hzpos)]
    have hK2 : C₀ * ((R + 1) / R) ^ (2 * (n : ℝ)) ≤ K := le_max_right _ _
    calc ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ≤ C₀ * ‖z‖ ^ (-(2 * (n : ℝ))) := h1
      _ = C₀ * (((1 + ‖z‖) / ‖z‖) ^ (2 * (n : ℝ))
            * (1 + ‖z‖) ^ (-(2 * (n : ℝ)))) := by rw [hsplit]
      _ ≤ C₀ * (((R + 1) / R) ^ (2 * (n : ℝ)) * (1 + ‖z‖) ^ (-(2 * (n : ℝ)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hC₀nn
            exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _)
      _ = (C₀ * ((R + 1) / R) ^ (2 * (n : ℝ))) * (1 + ‖z‖) ^ (-(2 * (n : ℝ))) := by ring
      _ ≤ K * (1 + ‖z‖) ^ (-(2 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_right hK2 (Real.rpow_nonneg (by positivity) _)

/-- `‖∂_k (bmPotential h) z‖²` is integrable for `C²` compactly supported data. -/
private lemma czbL2bs_integrable_normSq_dCoord_bmPotential {n : ℕ} (hn : 0 < n)
    {h : Fin n → (Fin n → ℂ) → ℂ} (hh2 : ∀ j, ContDiff ℝ 2 (h j))
    (hcs : ∀ j, HasCompactSupport (h j)) (k : Fin n) :
    Integrable (fun z : Fin n → ℂ => ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2) := by
  obtain ⟨K, hKnn, hbound⟩ := czbL2bs_bmPotential_dCoord_bound hn hh2 hcs k
  have hu1 : ContDiff ℝ 1 (bmPotential h) :=
    bmPotential_contDiff_of_hasCompactSupport hn (i := 1) (fun j => (hh2 j).of_le (by norm_num)) hcs
  have hcont : Continuous (fun z : Fin n → ℂ => ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2) :=
    (continuous_dCoord k hu1).norm.pow 2
  have hfr : (Module.finrank ℝ (Fin n → ℂ) : ℝ) < 4 * (n : ℝ) := by
    rw [czbL2bs_finrank_fin_complex]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    push_cast
    linarith
  have hint : Integrable (fun z : Fin n → ℂ => K ^ 2 * (1 + ‖z‖) ^ (-(4 * (n : ℝ)))) :=
    (integrable_one_add_norm (μ := volume) (E := Fin n → ℂ) hfr).const_mul (K ^ 2)
  refine hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  have h1 := hbound z
  have h1nn : 0 ≤ K * (1 + ‖z‖) ^ (-(2 * (n : ℝ))) :=
    mul_nonneg hKnn (Real.rpow_nonneg (by positivity) _)
  have hsq : ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2
      ≤ (K * (1 + ‖z‖) ^ (-(2 * (n : ℝ)))) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hAA : ((1 + ‖z‖) ^ (-(2 * (n : ℝ)))) ^ 2
      = (1 + ‖z‖) ^ (-(4 * (n : ℝ))) := by
    rw [← Real.rpow_natCast ((1 + ‖z‖) ^ (-(2 * (n : ℝ)))) 2,
      ← Real.rpow_mul (by positivity : 0 ≤ 1 + ‖z‖)]
    congr 1
    ring
  have hsq2 : (K * (1 + ‖z‖) ^ (-(2 * (n : ℝ)))) ^ 2
      = K ^ 2 * (1 + ‖z‖) ^ (-(4 * (n : ℝ))) := by
    rw [mul_pow, hAA]
  have hleft : ‖‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2‖
      = ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2 :=
    Real.norm_of_nonneg (by positivity)
  rw [hleft, ← hsq2]
  exact hsq

/-- If `g` is continuous with compact support then `z ↦ f z * g z` is integrable for continuous
`f`. -/
private lemma czbL2bs_integrable_mul_of_hasCompactSupport_right {n : ℕ} {f g : (Fin n → ℂ) → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun z : Fin n → ℂ => f z * g z) :=
  (hf.mul hg).integrable_of_hasCompactSupport (hgc.mul_left)

/-- A directional derivative of a compactly supported function is compactly supported. -/
private lemma czbL2bs_hasCompactSupport_fderiv_apply {n : ℕ} {v : (Fin n → ℂ) → ℂ}
    (hv : HasCompactSupport v) (e : Fin n → ℂ) :
    HasCompactSupport (fun x : Fin n → ℂ => fderiv ℝ v x e) :=
  (hv.fderiv (𝕜 := ℝ)).comp_left (g := fun L : (Fin n → ℂ) →L[ℝ] ℂ => L e) (by simp)

/-- The L2 bound for the derivative of the Bochner-Martinelli potential on smooth compactly
supported data.  The smooth level is written explicitly as `((⊤ : ℕ∞) : WithTop ℕ∞)` because the
scoped notation `∞` for `ENNReal` is in scope in this file.

Assembly of the pieces (each either proved in the workspace or being proved in parallel; import
them): `Work.NN.Core.czbL2_kernel_laplacian` (the kernel identity
`∫ x, bmKernel j x * flatLap ψ x = 4 * bmGamma n * dCoord j ψ 0` for `ψ ∈ C²_c`), which via
`Work.NN.Core.flatLap_bmPot_eq` (in `czB_L2_aux`) gives
`flatLap (bmPot h) = 4 * bmGamma n * Σ_j ∂_j h_j`; the energy identity
`Work.NN.Core.czbL2_energy` (`Σ_k ∫ ‖∂_k u‖² = -(1/4) ∫ Re (u * conj (Δu))` for `u = bmPot h`);
`Work.NN.Core.czbL2_energy_eq_dbar` (`Σ_k ∫⁻ ‖∂_k u‖² = Σ_k ∫⁻ ‖∂̄_k u‖²`); the finiteness
`Work.NN.Core.czbL2_dCoord_decay`; and the bilinear integration by parts
`Work.CR.Flat.integral_mul_dbarCoord_eq_neg` (`∫ u * ∂̄_k v = -∫ ∂̄_k u * v`), which turns
`∫ u * conj (∂_j h_j) = -∫ ∂̄_j u * conj h_j`.  Writing
`E := Σ_k ∫⁻ z, ofReal ‖∂_k u z‖²` and `H := Σ_k ∫⁻ z, ofReal ‖h_k z‖²`, the energy identity plus
the Δ-identity give, with `c : ℝ` such that `bmGamma n = (c : ℂ)` (so `bmGamma n` is real),
`E = ofReal (c * Re (Σ_j ∫ ∂̄_j u * conj h_j))`, and Cauchy-Schwarz
`|Σ_j ∫ ∂̄_j u * conj h_j| ≤ (Σ_j ∫ ‖∂̄_j u‖²)^(1/2) * (Σ_j ∫ ‖h_j‖²)^(1/2)` together with
`Σ_j ∫ ‖∂̄_j u‖² = Σ_j ∫ ‖∂_j u‖²` gives `E ≤ ofReal (c^2) * H`, i.e. the claim with `C = |c|`. -/
theorem czbL2_bound_smooth {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j, ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (h j)) →
      (∀ j, HasCompactSupport (h j)) →
      ∫⁻ z : Fin n → ℂ, (∑ k : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
        ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ z : Fin n → ℂ, (∑ j : Fin n, ENNReal.ofReal ‖h j z‖ ^ 2) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, bmGamma n = (c : ℂ) :=
    ⟨-(∫ x : Fin n → ℂ, (n : ℝ) / (nrmSq x + 1) ^ (n + 1)), by
      rw [bmGamma]; simp⟩
  refine ⟨|c|, abs_nonneg c, ?_⟩
  intro h hh hcs
  have hh2 : ∀ j, ContDiff ℝ 2 (h j) := fun j => (hh j).of_le czbL2bs_two_le_smooth
  have hh1 : ∀ j, ContDiff ℝ 1 (h j) := fun j => (hh j).of_le czbL2bs_one_le_smooth
  have hu1 : ContDiff ℝ 1 (bmPotential h) :=
    bmPotential_contDiff_of_hasCompactSupport hn (i := 1) hh1 hcs
  have hu_cont : Continuous (bmPotential h) := hu1.continuous
  have hInt_dc : ∀ k : Fin n,
      Integrable (fun z : Fin n → ℂ => ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2) :=
    fun k => czbL2bs_integrable_normSq_dCoord_bmPotential hn hh2 hcs k
  -- ## (1) the left-hand side is `ofReal F`
  set F : ℝ := ∑ k : Fin n, ∫ z : Fin n → ℂ,
    ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2 with hFdef
  have hFnn : 0 ≤ F := by
    rw [hFdef]
    exact Finset.sum_nonneg fun k _ => integral_nonneg fun z => by positivity
  have hLsum : (∑ k : Fin n, ∫⁻ z : Fin n → ℂ,
        ENNReal.ofReal (‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2))
      = ENNReal.ofReal F := by
    rw [hFdef, ENNReal.ofReal_sum_of_nonneg
      (fun k _ => integral_nonneg fun z => by positivity)]
    exact Finset.sum_congr rfl fun k _ =>
      (ofReal_integral_eq_lintegral_ofReal (hInt_dc k)
        (Filter.Eventually.of_forall fun z => by positivity)).symm
  have hgoalL : (∫⁻ z : Fin n → ℂ, ∑ k : Fin n, ENNReal.ofReal
        ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2) = ENNReal.ofReal F := by
    have hsummand : (fun z : Fin n → ℂ =>
          ∑ k : Fin n, ENNReal.ofReal ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
        = fun z : Fin n → ℂ =>
          ∑ k : Fin n, ENNReal.ofReal (‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2) := by
      funext z
      exact Finset.sum_congr rfl fun k _ => (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
    have hsplit : (∫⁻ z : Fin n → ℂ, ∑ k : Fin n,
          ENNReal.ofReal (‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2))
        = ∑ k : Fin n, ∫⁻ z : Fin n → ℂ,
          ENNReal.ofReal (‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2) :=
      lintegral_finsetSum Finset.univ
        (f := fun (k : Fin n) (z : Fin n → ℂ) =>
          ENNReal.ofReal (‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2))
        (fun k _ => ENNReal.measurable_ofReal.comp
          (((continuous_dCoord k hu1).norm.pow 2).measurable))
    rw [hsummand, hsplit]
    exact hLsum
  -- ## (2) energy identity and the Δ-identity
  have hEnergy : F = -(1 / 4) * ∫ z : Fin n → ℂ,
      (bmPotential h z * star (flatLap (bmPotential h) z)).re := by
    rw [hFdef]
    exact czbL2_energy hn hh2 hcs
  have hΔpt : ∀ z : Fin n → ℂ, flatLap (bmPotential h) z
      = 4 * (c : ℂ) * ∑ j : Fin n, Work.CR.Flat.dCoord j (h j) z := by
    intro z
    have h1 := flatLap_bmPot_eq hn hh2 hcs (czbL2_kernel_laplacian hn) z
    rw [show (fun w : Fin n → ℂ => bmPot h w) = bmPotential h from
      funext fun w => (bmPotential_eq_bmPot h w).symm] at h1
    rw [h1, hc]
  set T : ℂ := ∑ j : Fin n, ∫ z : Fin n → ℂ,
      Work.CR.Flat.dbarCoord j (bmPotential h) z * star (h j z) with hTdef
  set G : ℝ := ∑ j : Fin n, ∫ z : Fin n → ℂ, ‖h j z‖ ^ 2 with hGdef
  have hGnn : 0 ≤ G := by
    rw [hGdef]
    exact Finset.sum_nonneg fun j _ => integral_nonneg fun z => by positivity
  have hmem_h : ∀ j : Fin n, MemLp (fun z : Fin n → ℂ => h j z) 2 volume := fun j =>
    (hh1 j).continuous.memLp_of_hasCompactSupport (hcs j)
  have hInt_h : ∀ j : Fin n, Integrable (fun z : Fin n → ℂ => ‖h j z‖ ^ 2) := fun j =>
    (memLp_two_iff_integrable_sq_norm (hh1 j).continuous.aestronglyMeasurable).mp (hmem_h j)
  have hH2 : (∫⁻ z : Fin n → ℂ, ∑ j : Fin n,
        ENNReal.ofReal (‖h j z‖ ^ 2)) = ENNReal.ofReal G := by
    have hsplit : (∫⁻ z : Fin n → ℂ, ∑ j : Fin n, ENNReal.ofReal (‖h j z‖ ^ 2))
        = ∑ j : Fin n, ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (‖h j z‖ ^ 2) :=
      lintegral_finsetSum Finset.univ
        (f := fun (j : Fin n) (z : Fin n → ℂ) => ENNReal.ofReal (‖h j z‖ ^ 2))
        (fun j _ => ENNReal.measurable_ofReal.comp
          (((hh1 j).continuous.norm.pow 2).measurable))
    rw [hsplit, hGdef, ENNReal.ofReal_sum_of_nonneg
      (fun j _ => integral_nonneg fun z => by positivity)]
    exact Finset.sum_congr rfl fun j _ =>
      (ofReal_integral_eq_lintegral_ofReal (hInt_h j)
        (Filter.Eventually.of_forall fun z => by positivity)).symm
  have hH : (∫⁻ z : Fin n → ℂ, ∑ j : Fin n, ENNReal.ofReal ‖h j z‖ ^ 2)
      = ENNReal.ofReal G := by
    have hsummand : (fun z : Fin n → ℂ => ∑ j : Fin n, ENNReal.ofReal ‖h j z‖ ^ 2)
        = fun z : Fin n → ℂ => ∑ j : Fin n, ENNReal.ofReal (‖h j z‖ ^ 2) := by
      funext z
      exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
    rw [hsummand]
    exact hH2
  -- ## (3) integrability of the ∂̄-energies
  have hAsum : (∑ j : Fin n, ∫⁻ z : Fin n → ℂ,
        ENNReal.ofReal (‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2))
      = ENNReal.ofReal F := by
    have h1 : (∑ j : Fin n, ∫⁻ z : Fin n → ℂ,
          ENNReal.ofReal (‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2))
        = ∑ j : Fin n, ∫⁻ z : Fin n → ℂ,
          ENNReal.ofReal ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2 :=
      Finset.sum_congr rfl fun j _ =>
        lintegral_congr fun z => ENNReal.ofReal_pow (norm_nonneg _) 2
    have h2 : (∑ k : Fin n, ∫⁻ z : Fin n → ℂ,
          ENNReal.ofReal ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
        = ∑ k : Fin n, ∫⁻ z : Fin n → ℂ,
          ENNReal.ofReal (‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2) :=
      Finset.sum_congr rfl fun k _ =>
        lintegral_congr fun z => (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
    rw [h1, ← czbL2_energy_eq_dbar hn hh2 hcs, h2]
    exact hLsum
  have hInt_dbar : ∀ k : Fin n,
      Integrable (fun z : Fin n → ℂ => ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2) := by
    intro k
    have hle : (∫⁻ z : Fin n → ℂ, ENNReal.ofReal
          (‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2)) ≤ ENNReal.ofReal F :=
      calc (∫⁻ z : Fin n → ℂ, ENNReal.ofReal
            (‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2))
          ≤ ∑ j : Fin n, ∫⁻ z : Fin n → ℂ, ENNReal.ofReal
              (‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2) :=
            Finset.single_le_sum (f := fun j : Fin n => ∫⁻ z : Fin n → ℂ, ENNReal.ofReal
              (‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2))
              (fun j _ => bot_le) (Finset.mem_univ k)
        _ = ENNReal.ofReal F := hAsum
    have hfin : (∫⁻ z : Fin n → ℂ,
        ENNReal.ofReal (‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2)) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      (((continuous_dbarCoord_of_contDiff hu1 k).norm.pow 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => sq_nonneg (‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖))).mp hfin
  have hsum_dbar : (∑ j : Fin n, ∫ z : Fin n → ℂ,
        ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2) = F := by
    have hA2 : ENNReal.ofReal (∑ j : Fin n, ∫ z : Fin n → ℂ,
          ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2) = ENNReal.ofReal F := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => integral_nonneg fun z => by positivity),
        ← hAsum]
      exact Finset.sum_congr rfl fun j _ =>
        ofReal_integral_eq_lintegral_ofReal (hInt_dbar j)
          (Filter.Eventually.of_forall fun z => by positivity)
    have h := congrArg ENNReal.toReal hA2
    rwa [ENNReal.toReal_ofReal
        (Finset.sum_nonneg fun j _ => integral_nonneg fun z => by positivity),
      ENNReal.toReal_ofReal hFnn] at h
  -- ## (4) Cauchy–Schwarz
  have hCSj : ∀ j : Fin n, ‖∫ z : Fin n → ℂ,
        Work.CR.Flat.dbarCoord j (bmPotential h) z * star (h j z)‖
      ≤ Real.sqrt (∫ z : Fin n → ℂ, ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2)
        * Real.sqrt (∫ z : Fin n → ℂ, ‖h j z‖ ^ 2) := by
    intro j
    have hmem1 : MemLp (fun z : Fin n → ℂ => Work.CR.Flat.dbarCoord j (bmPotential h) z)
        2 volume :=
      (memLp_two_iff_integrable_sq_norm
        (continuous_dbarCoord_of_contDiff hu1 j).aestronglyMeasurable).mpr (hInt_dbar j)
    have hmem2 : MemLp (fun z : Fin n → ℂ => h j z) 2 volume :=
      (hh1 j).continuous.memLp_of_hasCompactSupport (hcs j)
    have hCS := integral_mul_norm_le_Lp_mul_Lq (μ := volume)
      (f := fun z : Fin n → ℂ => Work.CR.Flat.dbarCoord j (bmPotential h) z)
      (g := fun z : Fin n → ℂ => h j z) (p := 2) (q := 2)
      Real.HolderConjugate.two_two (by simpa using hmem1) (by simpa using hmem2)
    calc ‖∫ z : Fin n → ℂ, Work.CR.Flat.dbarCoord j (bmPotential h) z * star (h j z)‖
        ≤ ∫ z : Fin n → ℂ, ‖Work.CR.Flat.dbarCoord j (bmPotential h) z * star (h j z)‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ z : Fin n → ℂ, ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ * ‖h j z‖ := by
          simp_rw [norm_mul, norm_star]
      _ ≤ (∫ z : Fin n → ℂ, ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ (2 : ℝ)) ^ (1 / 2)
            * (∫ z : Fin n → ℂ, ‖h j z‖ ^ (2 : ℝ)) ^ (1 / 2) := hCS
      _ = Real.sqrt (∫ z : Fin n → ℂ, ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2)
            * Real.sqrt (∫ z : Fin n → ℂ, ‖h j z‖ ^ 2) := by
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
          simp_rw [Real.rpow_ofNat]
  have hTle : ‖T‖ ≤ Real.sqrt F * Real.sqrt G := by
    calc ‖T‖ = ‖∑ j : Fin n, ∫ z : Fin n → ℂ,
          Work.CR.Flat.dbarCoord j (bmPotential h) z * star (h j z)‖ := by rw [hTdef]
      _ ≤ ∑ j : Fin n, ‖∫ z : Fin n → ℂ,
            Work.CR.Flat.dbarCoord j (bmPotential h) z * star (h j z)‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, Real.sqrt (∫ z : Fin n → ℂ,
              ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2)
            * Real.sqrt (∫ z : Fin n → ℂ, ‖h j z‖ ^ 2) :=
          Finset.sum_le_sum fun j _ => hCSj j
      _ ≤ Real.sqrt (∑ j : Fin n, ∫ z : Fin n → ℂ,
              ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2)
            * Real.sqrt (∑ j : Fin n, ∫ z : Fin n → ℂ, ‖h j z‖ ^ 2) := by
          refine le_trans (Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
            (f := fun j => ∫ z : Fin n → ℂ,
              ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2)
            (g := fun j => ∫ z : Fin n → ℂ, ‖h j z‖ ^ 2)
            (fun j => integral_nonneg fun z => by positivity)
            (fun j => integral_nonneg fun z => by positivity)) ?_
          rw [hsum_dbar, ← hGdef]
      _ = Real.sqrt F * Real.sqrt G := by rw [hsum_dbar, ← hGdef]
  -- ## (5) the identity `F = c * Re T`
  have hIntWj : ∀ j : Fin n, Integrable (fun z : Fin n → ℂ =>
      bmPotential h z * star (Work.CR.Flat.dCoord j (h j) z)) := by
    intro j
    refine czbL2bs_integrable_mul_of_hasCompactSupport_right hu_cont ?_ ?_
    · exact continuous_star.comp (contDiff_one_dCoord (hh2 j) j).continuous
    · exact hasCompactSupport_star_comp (hasCompactSupport_dCoord_flat (hcs j) j)
  have hIntTj : ∀ j : Fin n, Integrable (fun z : Fin n → ℂ =>
      Work.CR.Flat.dbarCoord j (bmPotential h) z * star (h j z)) := by
    intro j
    refine czbL2bs_integrable_mul_of_hasCompactSupport_right
      (continuous_dbarCoord_of_contDiff hu1 j) ?_ ?_
    · exact continuous_star.comp (hh1 j).continuous
    · exact hasCompactSupport_star_comp (hcs j)
  have hIBPj : ∀ j : Fin n, (∫ z : Fin n → ℂ,
        (bmPotential h z * star (Work.CR.Flat.dCoord j (h j) z)).re)
      = -∫ z : Fin n → ℂ,
        (Work.CR.Flat.dbarCoord j (bmPotential h) z * star (h j z)).re := by
    intro j
    have hdv : ContDiff ℝ 1 (fun w : Fin n → ℂ => star (h j w)) :=
      (contDiff_two_star_comp (hh2 j)).of_le (by norm_num)
    have hstarcs : HasCompactSupport (fun w : Fin n → ℂ => star (h j w)) :=
      hasCompactSupport_star_comp (hcs j)
    have hstar : ∀ z, star (Work.CR.Flat.dCoord j (h j) z)
        = Work.CR.Flat.dbarCoord j (fun w => star (h j w)) z := fun z =>
      (dbarCoord_star_comp j ((hh2 j).differentiable (by norm_num) z)).symm
    have hdfu1_cont : Continuous (fun x : Fin n → ℂ =>
        fderiv ℝ (bmPotential h) x (Pi.single j (1 : ℂ))) :=
      (hu1.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hdfuI_cont : Continuous (fun x : Fin n → ℂ =>
        fderiv ℝ (bmPotential h) x (Pi.single j Complex.I)) :=
      (hu1.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hdv_cont : Continuous (fun w : Fin n → ℂ => star (h j w)) := hdv.continuous
    have hdfv1_cs : HasCompactSupport (fun x : Fin n → ℂ =>
        fderiv ℝ (fun w : Fin n → ℂ => star (h j w)) x (Pi.single j (1 : ℂ))) :=
      czbL2bs_hasCompactSupport_fderiv_apply hstarcs _
    have hdfvI_cs : HasCompactSupport (fun x : Fin n → ℂ =>
        fderiv ℝ (fun w : Fin n → ℂ => star (h j w)) x (Pi.single j Complex.I)) :=
      czbL2bs_hasCompactSupport_fderiv_apply hstarcs _
    have hdfv1_cont : Continuous (fun x : Fin n → ℂ =>
        fderiv ℝ (fun w : Fin n → ℂ => star (h j w)) x (Pi.single j (1 : ℂ))) :=
      (hdv.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hdfvI_cont : Continuous (fun x : Fin n → ℂ =>
        fderiv ℝ (fun w : Fin n → ℂ => star (h j w)) x (Pi.single j Complex.I)) :=
      (hdv.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hIBP := Work.CR.Flat.integral_mul_dbarCoord_eq_neg j hu1 hdv
      (czbL2bs_integrable_mul_of_hasCompactSupport_right hdfu1_cont hdv_cont hstarcs)
      (czbL2bs_integrable_mul_of_hasCompactSupport_right hdfuI_cont hdv_cont hstarcs)
      (czbL2bs_integrable_mul_of_hasCompactSupport_right hu_cont hdfv1_cont hdfv1_cs)
      (czbL2bs_integrable_mul_of_hasCompactSupport_right hu_cont hdfvI_cont hdfvI_cs)
      (czbL2bs_integrable_mul_of_hasCompactSupport_right hu_cont hdv_cont hstarcs)
    calc (∫ z : Fin n → ℂ, (bmPotential h z * star (Work.CR.Flat.dCoord j (h j) z)).re)
        = (∫ z : Fin n → ℂ,
            bmPotential h z * star (Work.CR.Flat.dCoord j (h j) z)).re :=
          integral_re_eq (hIntWj j)
      _ = (∫ z : Fin n → ℂ,
            bmPotential h z * Work.CR.Flat.dbarCoord j (fun w => star (h j w)) z).re := by
          rw [show (fun z : Fin n → ℂ =>
                bmPotential h z * star (Work.CR.Flat.dCoord j (h j) z))
              = fun z : Fin n → ℂ => bmPotential h z
                * Work.CR.Flat.dbarCoord j (fun w => star (h j w)) z from
            funext fun z => by rw [hstar z]]
      _ = (-∫ z : Fin n → ℂ,
            Work.CR.Flat.dbarCoord j (bmPotential h) z * star (h j z)).re := by rw [hIBP]
      _ = -∫ z : Fin n → ℂ,
            (Work.CR.Flat.dbarCoord j (bmPotential h) z * star (h j z)).re :=
          re_neg_integral_eq (hIntTj j)
  have hWdist : (∫ z : Fin n → ℂ,
        (bmPotential h z * star (∑ j : Fin n, Work.CR.Flat.dCoord j (h j) z)).re)
      = -T.re := by
    have hptW : (fun z : Fin n → ℂ =>
          bmPotential h z * star (∑ j : Fin n, Work.CR.Flat.dCoord j (h j) z))
        = fun z : Fin n → ℂ => ∑ j : Fin n,
          bmPotential h z * star (Work.CR.Flat.dCoord j (h j) z) := by
      funext z
      rw [star_sum, Finset.mul_sum]
    have hIntW : Integrable (fun z : Fin n → ℂ =>
        bmPotential h z * star (∑ j : Fin n, Work.CR.Flat.dCoord j (h j) z)) := by
      rw [hptW]
      exact integrable_finsetSum Finset.univ (fun j _ => hIntWj j)
    calc (∫ z : Fin n → ℂ,
          (bmPotential h z * star (∑ j : Fin n, Work.CR.Flat.dCoord j (h j) z)).re)
        = (∫ z : Fin n → ℂ,
            bmPotential h z * star (∑ j : Fin n, Work.CR.Flat.dCoord j (h j) z)).re :=
          integral_re_eq hIntW
      _ = (∫ z : Fin n → ℂ, ∑ j : Fin n,
            bmPotential h z * star (Work.CR.Flat.dCoord j (h j) z)).re := by rw [hptW]
      _ = (∑ j : Fin n, ∫ z : Fin n → ℂ,
            bmPotential h z * star (Work.CR.Flat.dCoord j (h j) z)).re := by
          rw [integral_finsetSum Finset.univ (fun j _ => hIntWj j)]
      _ = ∑ j : Fin n, (∫ z : Fin n → ℂ,
            bmPotential h z * star (Work.CR.Flat.dCoord j (h j) z)).re :=
          Complex.re_sum Finset.univ _
      _ = ∑ j : Fin n, ∫ z : Fin n → ℂ,
            (bmPotential h z * star (Work.CR.Flat.dCoord j (h j) z)).re :=
          Finset.sum_congr rfl fun j _ => (integral_re_eq (hIntWj j)).symm
      _ = ∑ j : Fin n, (-∫ z : Fin n → ℂ,
            (Work.CR.Flat.dbarCoord j (bmPotential h) z * star (h j z)).re) :=
          Finset.sum_congr rfl fun j _ => hIBPj j
      _ = -(∑ j : Fin n, ∫ z : Fin n → ℂ,
            (Work.CR.Flat.dbarCoord j (bmPotential h) z * star (h j z)).re) := by
          rw [Finset.sum_neg_distrib]
      _ = -(∑ j : Fin n, (∫ z : Fin n → ℂ,
            Work.CR.Flat.dbarCoord j (bmPotential h) z * star (h j z)).re) := by
          congr 1
          exact Finset.sum_congr rfl fun j _ => integral_re_eq (hIntTj j)
      _ = -T.re := by rw [hTdef, Complex.re_sum]
  have hW : (∫ z : Fin n → ℂ,
        (bmPotential h z * star (flatLap (bmPotential h) z)).re)
      = 4 * c * ∫ z : Fin n → ℂ,
        (bmPotential h z * star (∑ j : Fin n, Work.CR.Flat.dCoord j (h j) z)).re := by
    have hpt : ∀ z : Fin n → ℂ,
        (bmPotential h z * star (flatLap (bmPotential h) z)).re
        = 4 * c * (bmPotential h z
            * star (∑ j : Fin n, Work.CR.Flat.dCoord j (h j) z)).re := by
      intro z
      rw [hΔpt z]
      have hs : star (4 * (c : ℂ) * ∑ j : Fin n, Work.CR.Flat.dCoord j (h j) z)
          = 4 * (c : ℂ) * star (∑ j : Fin n, Work.CR.Flat.dCoord j (h j) z) := by
        rw [star_mul, star_mul]
        have h1 : star (c : ℂ) = (c : ℂ) := by simp
        have h2 : star (4 : ℂ) = (4 : ℂ) := by simp
        rw [h1, h2]
        ring
      rw [hs]
      rw [show bmPotential h z
            * (4 * (c : ℂ) * star (∑ j : Fin n, Work.CR.Flat.dCoord j (h j) z))
          = ((4 * c : ℝ) : ℂ) * (bmPotential h z
              * star (∑ j : Fin n, Work.CR.Flat.dCoord j (h j) z)) by push_cast; ring]
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  have hFrT : F = c * T.re := by
    rw [hEnergy, hW, hWdist]
    ring
  -- ## (6) the quantitative bound
  have hF_bd : F ≤ c ^ 2 * G := by
    rcases eq_or_lt_of_le hFnn with hF0 | hFpos
    · rw [← hF0]; positivity
    · have hspos : 0 < Real.sqrt F := Real.sqrt_pos.mpr hFpos
      have h1 : F ≤ |c| * (Real.sqrt F * Real.sqrt G) := by
        calc F = c * T.re := hFrT
          _ ≤ |c * T.re| := le_abs_self _
          _ = |c| * |T.re| := abs_mul c T.re
          _ ≤ |c| * ‖T‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm T) (abs_nonneg c)
          _ ≤ |c| * (Real.sqrt F * Real.sqrt G) :=
              mul_le_mul_of_nonneg_left hTle (abs_nonneg c)
      have h2 : Real.sqrt F ≤ |c| * Real.sqrt G := by
        have h4 : Real.sqrt F * Real.sqrt F ≤ Real.sqrt F * (|c| * Real.sqrt G) := by
          calc Real.sqrt F * Real.sqrt F = F := by rw [← sq, Real.sq_sqrt hFnn]
            _ ≤ |c| * (Real.sqrt F * Real.sqrt G) := h1
            _ = Real.sqrt F * (|c| * Real.sqrt G) := by ring
        exact (mul_le_mul_iff_of_pos_left hspos).mp h4
      calc F = Real.sqrt F ^ 2 := (Real.sq_sqrt hFnn).symm
        _ ≤ (|c| * Real.sqrt G) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg F) h2 2
        _ = c ^ 2 * G := by rw [mul_pow, Real.sq_sqrt hGnn, sq_abs]
  calc (∫⁻ z : Fin n → ℂ, ∑ k : Fin n, ENNReal.ofReal
        ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
      = ENNReal.ofReal F := hgoalL
    _ ≤ ENNReal.ofReal (c ^ 2 * G) := ENNReal.ofReal_le_ofReal hF_bd
    _ = ENNReal.ofReal (|c| ^ 2) * ENNReal.ofReal G := by
          rw [ENNReal.ofReal_mul (by positivity), ← sq_abs c]
    _ = ENNReal.ofReal (|c| ^ 2) * (∫⁻ z : Fin n → ℂ,
          ∑ j : Fin n, ENNReal.ofReal ‖h j z‖ ^ 2) := by rw [← hH]

end Work.NN.Core
