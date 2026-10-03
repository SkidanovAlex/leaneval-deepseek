import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.Gates
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.Parabolic
import Submission.Work.PertCrux.coordP_close_dphi
import Submission.Work.PertCrux.gateP_coord_converges
import Submission.Work.PertCrux.exists_tauC_preimage_gate
import Submission.Work.Analysis.PertCrux.QpPrime_props
import Submission.Work.Analysis.PertCrux.ball_subset_gates
import Submission.Work.Analysis.PertCrux.tube_shadowing
import Submission.Work.Analysis.PertCrux.small_data
import Submission.Work.Analysis.PertCrux.rr_ge_sigma
import Submission.Work.Analysis.PertCrux.orbit_harmonic_sum
import Submission.Work.Analysis.PertCrux.gate_fatou_lipschitz
import Submission.Work.Analysis.PertCrux.walk_mem_Dphi
import Submission.Work.Analysis.PertCrux.orbit_shift_close
import Submission.Work.Analysis.PertCrux.exists_shadow_set
import Submission.Work.Pert.limitCoord_plus_exists
import Submission.Work.Pert.tools
import Submission.Work.PertCrux.norm_alpha_le_norm_one_sub_exp
import Submission.Work.Analysis.PertCrux.landing_data_v3
import Submission.Work.Analysis.PertCrux.scale_data
import Submission.Work.Analysis.PertCrux.scale_data_v2
import Submission.Work.Analysis.PertCrux.ball_subset_Qp_of_bounds
import Submission.Work.Analysis.PertCrux.crux_estimates
import Submission.Work.Analysis.PertCrux.crux_numeric_final

/-! ## Session-2 helper lemmas (route in `NOTES_CRUX_V2_SESSION2.md`)

The residual argument of this file evaluates the datum's Fatou coordinate `d.Φ` along the walk
`w ↦ w+1`, so the two basic translational identities of `d.E = d.Φ ∘ d.φ` are stated first. -/

namespace Work.PertCrux

open MandelDim Filter Metric Set
open scoped Topology

/-- `d.E (w+1) = d.E w + 1` for `w ∈ d.DE` with `w+1 ∈ d.DE` (T-equivariance of the lifted horn
map): `d.φ_abel` (`w+1 ∈ d.Dφ`) and `d.Φ_abel` at `d.φ w ∈ basin`. -/
theorem ParabData.E_add_one {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {w : ℂ} (hw : w ∈ d.DE) (hw1 : w + 1 ∈ d.DE) :
    d.E (w + 1) = d.E w + 1 := by
  have hφ : d.φ (w + 1) = f₀ (d.φ w) := d.φ_abel w hw.1 hw1.1
  have hΦ : d.Φ (f₀ (d.φ w)) = d.Φ (d.φ w) + 1 := d.Φ_abel (d.φ w) hw.2
  show d.Φ (d.φ (w + 1)) = d.Φ (d.φ w) + 1
  rw [hφ, hΦ]

/-- `d.E (w+n) = d.E w + n` along a walk in `d.DE`. -/
theorem ParabData.E_add_nat {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {w : ℂ} (n : ℕ) (h : ∀ j : ℕ, j ≤ n → w + (j : ℂ) ∈ d.DE) :
    d.E (w + (n : ℂ)) = d.E w + (n : ℂ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : d.E (w + (k : ℂ)) = d.E w + (k : ℂ) := ih (fun j hj => h j (by omega))
    rw [Nat.cast_succ]
    have hw : w + (k : ℂ) ∈ d.DE := h k (by omega)
    have hw1 : (w + (k : ℂ)) + 1 ∈ d.DE := by
      have h'' := h (k + 1) (by omega)
      simpa only [Nat.cast_succ, add_assoc] using h''
    have hstep : d.E ((w + (k : ℂ)) + 1) = d.E (w + (k : ℂ)) + 1 :=
      ParabData.E_add_one d hw hw1
    have hcast : w + ((k : ℂ) + 1) = (w + (k : ℂ)) + 1 := by ring
    rw [hcast, hstep, hk]
    ring


/-! ## Helper lemmas for the assembly -/

/-- `NearOn` is monotone in the compact set (downwards) and in the tolerance (upwards). -/
theorem NearOn.mono {f₀ f : ℂ → ℂ} {Df L L' : Set ℂ} {δ δ' : ℝ}
    (h : MandelDim.NearOn f₀ f Df L δ) (hL : L' ⊆ L) (hδ : δ ≤ δ') :
    MandelDim.NearOn f₀ f Df L' δ' := by
  obtain ⟨hopen, hsub, hdiff, hclose⟩ := h
  exact ⟨hopen, hL.trans hsub, hdiff, fun z hz => lt_of_lt_of_le (hclose z (hL hz)) hδ⟩

private lemma inv_two_pi_I_re : ((2 * Real.pi * Complex.I : ℂ)⁻¹).re = 0 := by
  rw [Complex.inv_re]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num

private lemma inv_two_pi_I_im : ((2 * Real.pi * Complex.I : ℂ)⁻¹).im = -(1 / (2 * Real.pi)) := by
  rw [Complex.inv_im]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  try field_simp

/-- `rotOf f = log (f' 0) / (2πi)` has real part `arg (f' 0) / (2π)`. -/
theorem rotOf_re_eq (f : ℂ → ℂ) :
    (MandelDim.rotOf f).re = (deriv f 0).arg / (2 * Real.pi) := by
  rw [MandelDim.rotOf, div_eq_mul_inv, Complex.mul_re, inv_two_pi_I_re, inv_two_pi_I_im]
  simp only [Complex.log_re, Complex.log_im]
  ring

/-- `Re (rotOf f) ≤ 1/2`. -/
theorem rotOf_re_le (f : ℂ → ℂ) : (MandelDim.rotOf f).re ≤ 1 / 2 := by
  rw [rotOf_re_eq, div_le_iff₀ (by positivity)]
  nlinarith [Complex.arg_le_pi (deriv f 0), Real.pi_pos]

/-- `Re (rotOf f) > -1/2`. -/
theorem rotOf_re_gt (f : ℂ → ℂ) : -(1 / 2 : ℝ) < (MandelDim.rotOf f).re := by
  rw [rotOf_re_eq, lt_div_iff₀ (by positivity)]
  nlinarith [Complex.neg_pi_lt_arg (deriv f 0), Real.pi_pos]

/-- **The rotation number is controlled by `σ`.**  From `σ u₀ = 1 - e^{2πiα}` with
`‖u₀‖ ≤ 2`, `‖σ‖ ≤ √(2δ₀)`, `α ∈ 𝓕₁` and `α.re ≤ 1/2` (true for `α = rotOf f`):
`‖α‖ ≤ 2 √(2δ₀)`. -/
theorem norm_alpha_le_two_sqrt {σ α u₀ : ℂ} {δ₀ : ℝ}
    (hinf : MandelDim.InF1 α) (hre : α.re ≤ 1 / 2) (hu₀ : ‖u₀‖ ≤ 2)
    (hσ : ‖σ‖ ≤ Real.sqrt (2 * δ₀))
    (hexp : σ * u₀ = 1 - Complex.exp (2 * Real.pi * Complex.I * α)) :
    ‖α‖ ≤ 2 * Real.sqrt (2 * δ₀) := by
  have hα : ‖α‖ ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ :=
    Work.PertCrux.norm_alpha_le_norm_one_sub_exp hinf hre
  have hσu : ‖σ * u₀‖ ≤ Real.sqrt (2 * δ₀) * 2 := by
    rw [norm_mul]
    exact mul_le_mul hσ hu₀ (norm_nonneg _) (Real.sqrt_nonneg _)
  rw [hexp] at hσu
  linarith [hα, hσu]

/-- `‖a‖ ≤ ‖a - b‖ + ‖b‖` (the "reverse triangle" in the additive form used below). -/
theorem norm_le_norm_add_sub {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
  calc ‖a‖ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
    _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _

set_option maxHeartbeats 2000000 in
theorem crux_limit_v2 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ)
    (hsize : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ Metric.ball 0 ρ₀ ⊆ D₀ ∧ 16 * Real.pi < ρ₀ * Ξ)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ d.DE) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Ξ₀ : ℝ, ∀ Ξ' : ℝ, Ξ₀ ≤ Ξ' → Ξ ≤ Ξ' →
    ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ Metric.ball 0 (16 * Real.pi / Ξ') ⊆ L ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (rr : ℝ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f → 0 < rr →
        DifferentiableOn ℂ u (Metric.ball 0 rr) →
        (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) →
        (∀ z ∈ Work.Pert.Qp Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) →
        MandelDim.QAdm (some ((Ξ' : ℂ) - 1 / α)) (some (-(Ξ' : ℂ))) →
        MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / α)) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ' α) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qp Ξ' α) →
        ∃ Φm Φp : ℂ → ℂ, ∃ Qp' : Set ℂ, ∃ m : ℕ, ∃ k : ℤ,
          MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ' α) ∧
          MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φp (Work.Pert.Qp Ξ' α) ∧
          IsOpen Qp' ∧ Qp' ⊆ Work.Pert.Qp Ξ' α ∧ Set.InjOn (Work.Pert.tauC σ α) Qp' ∧
          (∀ w ∈ K, Work.Pert.liftF u σ α (Work.Pert.invOn (Work.Pert.tauC σ α) Qp'
              (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))) ∈ Qp') ∧
          (∀ w ∈ K,
            (∀ j : ℕ, j ≤ m →
              f^[j] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w) ∈ Df) ∧
            f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)
              ∈ Work.Pert.tauC σ α '' Qp') ∧
          ∀ w ∈ K,
            ‖Φp (Work.Pert.invOn (Work.Pert.tauC σ α) Qp'
                (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)))
              - (m : ℂ) - (k : ℂ) - d.E w‖ < δ := by

  classical
  -- ===========================================================================
  -- ## 0. `f`-independent data
  -- ===========================================================================
  obtain ⟨ρ₀, hρ₀pos, hρ₀sub, hρ₀Ξ⟩ := hsize
  obtain ⟨ξg, hξgpos, hgate⟩ := Work.PertCrux.gateP_coord_converges d hF hd
  obtain ⟨Rgl, Cgl, hRglpos, hCglpos, hgatelip⟩ := Work.Analysis.PertCrux.gate_fatou_lipschitz hF
  obtain ⟨r₁, M₀, hr₁pos, hM₀nn, hsmallT⟩ := Work.Analysis.PertCrux.small_data hd
  -- `d.E` is bounded on the compact `K`
  obtain ⟨MK, hMK0, hMK⟩ : ∃ MK : ℝ, 0 ≤ MK ∧ ∀ w ∈ K, ‖d.E w‖ ≤ MK := by
    have hbasin_open : IsOpen (MandelDim.ParabolicBasin f₀ D₀) := by
      rw [isOpen_iff_mem_nhds]
      intro z hz
      obtain ⟨U, hU, hmap, hconv⟩ := hz
      obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
      refine Filter.mem_of_superset (hVopen.mem_nhds hzV) (fun y hy => ?_)
      exact ⟨V, hVopen.mem_nhds hy, fun n => (hmap n).mono hVU Subset.rfl, hconv.mono hVU⟩
    have hDEopen : IsOpen d.DE := by
      rw [isOpen_iff_mem_nhds]
      intro w hw
      have hφcont : ContinuousAt d.φ w :=
        (d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hw.1)).continuousAt
      have hpre : d.φ ⁻¹' (MandelDim.ParabolicBasin f₀ D₀) ∈ 𝓝 w :=
        hφcont.preimage_mem_nhds (hbasin_open.mem_nhds hw.2)
      exact Filter.inter_mem (d.Dφ_open.mem_nhds hw.1) hpre
    have hcont : ContinuousOn d.E K := by
      intro w hw
      have hwDE : w ∈ d.DE := hK hw
      have hΦ : ContinuousAt d.Φ (d.φ w) :=
        (d.Φ_holo.differentiableAt (hbasin_open.mem_nhds hwDE.2)).continuousAt
      have hφ : ContinuousAt d.φ w :=
        (d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hwDE.1)).continuousAt
      exact hΦ.comp_continuousWithinAt hφ.continuousWithinAt
    have hbdd : Bornology.IsBounded (d.E '' K) :=
      (hKc.image_of_continuousOn hcont).isBounded
    obtain ⟨Cn, hCn⟩ := hbdd.exists_norm_le
    refine ⟨max Cn 0, le_max_right _ _, fun w hw => ?_⟩
    exact le_trans (hCn (d.E w) (Set.mem_image_of_mem d.E hw)) (le_max_left _ _)
  -- the one analytic gap of this route: the walk avoids `0` (see NOTES_CRUX_V2_SESSION3.md)
  have havoid : ∀ w ∈ K, ∀ j : ℕ, f₀^[j] (d.φ w) ≠ 0 :=
    fun w hw j => d.orbit_avoid (d.φ w) (hK hw).2 j
  -- (W): the orbit-corrected location of `τ₀ (f₀^[m] (d.φ w))`
  obtain ⟨CW, hCWpos, hW⟩ := Work.Analysis.PertCrux.orbit_shift_close d hd hKc hK havoid
  -- ===========================================================================
  -- ## 1. the threshold `Ξ₀`
  -- ===========================================================================
  set Ξ₀ : ℝ := ξg + Ξ + (1 + 64 * Real.pi) + 2 * (Metric.diam K + 1) + (MK + 1) + (CW + 1)
      + (Rgl + 1) + (r₁ + 1) + (M₀ + 1) + (ρ₀ + 1) + (1 / δ + 1) + (δ + 1) + (Cgl + 1) + 5 with hΞ₀def
  refine ⟨Ξ₀, ?_⟩
  intro Ξ' hΞ' hΞΞ'
  -- nonnegativities of the summands of `Ξ₀`
  have hΞnn : (0:ℝ) ≤ Ξ := by linarith only [Real.pi_pos, hΞ]
  have hπnn : (0:ℝ) ≤ 1 + 64 * Real.pi := by positivity
  have hdiam1nn : (0:ℝ) ≤ 2 * (Metric.diam K + 1) := by
    linarith only [Metric.diam_nonneg (s := K)]
  have hMK1 : (0:ℝ) ≤ MK + 1 := by linarith
  have hCW1 : (0:ℝ) ≤ CW + 1 := by linarith
  have hRgl1 : (0:ℝ) ≤ Rgl + 1 := by linarith
  have hr₁1 : (0:ℝ) ≤ r₁ + 1 := by linarith
  have hM₀1 : (0:ℝ) ≤ M₀ + 1 := by linarith
  have hρ₀1 : (0:ℝ) ≤ ρ₀ + 1 := by linarith
  have h1δ1 : (0:ℝ) ≤ 1 / δ + 1 := by linarith only [one_div_pos.mpr hδ]
  have hδ1 : (0:ℝ) ≤ δ + 1 := by linarith
  have h5 : (0:ℝ) ≤ 5 := by norm_num
  have hproj := hΞ'
  rw [hΞ₀def] at hproj
  have hξgΞ : ξg ≤ Ξ' := by linarith
  have hΞΞ'' : Ξ ≤ Ξ' := by linarith
  have h64 : 1 + 64 * Real.pi ≤ Ξ' := by linarith
  have hdiamΞ : 2 * (Metric.diam K + 1) ≤ Ξ' := by linarith
  have hMKΞ : MK + 1 ≤ Ξ' := by linarith
  have hCWΞ : CW + 1 ≤ Ξ' := by linarith
  have hRglΞ : Rgl + 1 ≤ Ξ' := by linarith
  have hr₁Ξ : r₁ + 1 ≤ Ξ' := by linarith
  have hM₀Ξ : M₀ + 1 ≤ Ξ' := by linarith
  have hρ₀Ξ' : ρ₀ + 1 ≤ Ξ' := by linarith
  have h1δΞ : 1 / δ + 1 ≤ Ξ' := by linarith
  have hδΞ : δ + 1 ≤ Ξ' := by linarith
  have hCglΞ' : Cgl + 1 ≤ Ξ' := by linarith
  have h5Ξ : 5 ≤ Ξ' := by linarith
  have hΞ'10 : (10 : ℝ) ≤ Ξ' := by linarith
  -- the exported projections used below
  have hΞ'1 : (1 : ℝ) ≤ Ξ' := by linarith only [Real.pi_pos, h64]
  have hΞ'pos : 0 < Ξ' := by linarith only [Real.pi_pos, h64]
  have hRgl0 : (0 : ℝ) ≤ Rgl := hRglpos.le
  -- ===========================================================================
  -- ## 2. the per-`Ξ'` scale `Lam` and the landing time `m`
  -- ===========================================================================
  obtain ⟨Lam, hLam64, hLamΞ, hLamMK, hLamCW, hLamRgl8, hLamub, hLamlog⟩ :
      ∃ Lam : ℝ, 64 ≤ Lam ∧ Ξ' ≤ Lam ∧ MK ≤ Lam ∧ CW ≤ Lam ∧ Rgl ≤ Lam / 8 ∧
        Lam ≤ 10 ^ 6 * (Ξ' + MK + CW + Rgl + 1) ^ 3 + 10 ^ 6 ∧
        32 * CW * (2 + Real.log (Ξ' + 3 * Lam + MK + 5 * CW + 4)) ≤ Lam := by
    exact Work.Analysis.PertCrux.scale_data_v2 hΞ'1 hMK0 hCWpos.le hRglpos.le
  obtain ⟨m, hmge, hdtau16, hmub, hmnrm, hmcone⟩ :
      ∃ m : ℕ, Ξ' + Lam ≤ (m : ℝ) ∧
        CW * (1 + Real.log ((m : ℝ) + 1)) ≤ Lam / 16 ∧
        (m : ℝ) ≤ (Ξ' + 3 * Lam + MK + 5 * CW + 2) ^ 2 + 2 ∧
        (∀ w ∈ K, ‖MandelDim.tau0 (f₀^[m] (d.φ w))‖ ≤
          (Ξ' + 3 * Lam + MK + 5 * CW + 2) ^ 2 + MK + Lam + 4) ∧
        (∀ w ∈ K, ∀ z : ℂ, ‖z - MandelDim.tau0 (f₀^[m] (d.φ w))‖ ≤ Lam →
          Ξ' + 2 * Lam ≤ z.re + |z.im|) := by
    exact Work.Analysis.PertCrux.landing_data_v3 d hΞ'1 hMK0 hCWpos.le hLam64 hLamΞ hLamMK hLamCW hLamlog hMK hW
  set dtau : ℝ := CW * (1 + Real.log ((m : ℝ) + 1)) with hdtaudef
  set Rsc : ℝ := (Ξ' + 3 * Lam + MK + 5 * CW + 2) ^ 2 + MK + Lam + 4 with hRscdef
  set Rbig : ℝ := dtau + Rgl + 4 with hRbigdef
  have hdtau_le : dtau ≤ Lam / 16 := hdtau16
  have hRsc_ge : 0 ≤ Rsc := by
    rw [hRscdef]
    nlinarith only [sq_nonneg (Ξ' + 3 * Lam + MK + 5 * CW + 2), hMK0, hLam64]
  have hRsc_le : Rsc ≤ 200 * Lam ^ 2 := by
    rw [hRscdef]
    have h2 : Ξ' + 3 * Lam + MK + 5 * CW + 2 ≤ 10 * Lam + 2 := by
      linarith only [hLamΞ, hLamMK, hLamCW, hLam64]
    have h3 : (Ξ' + 3 * Lam + MK + 5 * CW + 2) ^ 2 ≤ (10 * Lam + 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    have h4 : (10 * Lam + 2) ^ 2 ≤ 121 * Lam ^ 2 := by nlinarith only [hLam64]
    have h5 : MK ≤ Lam ^ 2 := by nlinarith only [hLamMK, hLam64]
    have h6 : Lam + 4 ≤ Lam ^ 2 := by nlinarith only [hLam64]
    have h7 : (0:ℝ) ≤ Lam ^ 2 := sq_nonneg Lam
    linarith only [h3, h4, h5, h6, h7]
  have hRbig_le : Rbig ≤ Lam / 2 := by
    rw [hRbigdef]
    linarith only [hdtau_le, hLamRgl8, hLam64]
  -- ===========================================================================
  -- ## 3. the shadowing set, the `coordP` set, the gate compact, `L` and `δ₀`
  -- ===========================================================================
  obtain ⟨Ls, L', rom, K₀, ε₀, hK₀1, hrom0, hrom1, hε₀0, hLsc, hL'c, hLsL', hL'D₀,
      hballε₀, horb, hmapsLs, hlipL', hroomL'⟩ :=
    Work.Analysis.PertCrux.exists_shadow_set d hd hKc hK m
  set εs : ℝ := min (rom / 4) (δ / (10 ^ 9 * (Ξ' ^ 2 + 1) ^ 20)) with hεsdef
  have hεspos : 0 < εs := by
    rw [hεsdef]
    exact lt_min (by linarith) (div_pos hδ (by positivity))
  have hεsrom : εs ≤ rom := by
    rw [hεsdef]
    have h := min_le_left (rom / 4) (δ / (10 ^ 9 * (Ξ' ^ 2 + 1) ^ 20))
    linarith only [h, hrom0]
  have hεs_le : εs ≤ δ / (10 ^ 9 * (Ξ' ^ 2 + 1) ^ 20) := min_le_right _ _
  obtain ⟨δsh, hδsh_pos, hδsh_le1, η, hη_pos, hshadow⟩ :=
    Work.Analysis.PertCrux.tube_shadowing hL'c hLsL' hK₀1 hrom0 hrom1 hlipL' hmapsLs hroomL'
      (m := m) hεspos hεsrom
  set εc : ℝ := min η ε₀ / 2 with hεcdef
  have hεcpos : 0 < εc := by
    rw [hεcdef]
    have := lt_min hη_pos hε₀0
    linarith
  have hεcη : εc ≤ η := by
    rw [hεcdef]
    have := min_le_left η ε₀
    linarith
  have hεcε₀ : εc ≤ ε₀ := by
    rw [hεcdef]
    have := min_le_right η ε₀
    linarith
  obtain ⟨Lc, hLcc, hLcD₀, δc, hδc_pos, hcoord⟩ :=
    Work.PertCrux.coordP_close_dphi d hF hd Ξ' hΞ'pos hKc hK εc hεcpos
  -- the compact set of the pinning (a piece of the right cone above height `Ξ'`)
  set KΦ : Set ℂ := Metric.closedBall 0 (Rsc + Lam + 2) ∩ {z : ℂ | Ξ' + 1 ≤ z.re + |z.im|}
    with hKΦdef
  have hKΦc : IsCompact KΦ := by
    rw [hKΦdef]
    refine IsCompact.inter_right (isCompact_closedBall 0 (Rsc + Lam + 2)) ?_
    refine isClosed_le continuous_const (Continuous.add Complex.continuous_re ?_)
    exact Complex.continuous_im.abs
  have hKΦsub : KΦ ⊆ MandelDim.Qreg (some (Ξ' : ℂ)) none := by
    intro z hz
    rw [Work.Pert.mem_Qreg_cone]
    exact lt_of_lt_of_le (by linarith) hz.2
  set εp : ℝ := δ / 4 with hεpdef
  have hεppos : 0 < εp := by rw [hεpdef]; linarith
  obtain ⟨Lg, hLgc, hLgD₀, hLgball, δg, hδg_pos, hgateP⟩ :=
    hgate Ξ' hξgΞ hKΦc hKΦsub εp hεppos
  -- the compact `L` of the conclusion
  set ρ₁ : ℝ := min (ρ₀ / 2) (r₁ / 2) with hρ₁def
  have hρ₁pos : 0 < ρ₁ := by
    rw [hρ₁def]
    exact lt_min (by linarith) (by linarith)
  have hρ₁_le_ρ₀ : ρ₁ ≤ ρ₀ := by
    rw [hρ₁def]
    have h := min_le_left (ρ₀ / 2) (r₁ / 2)
    linarith only [h, hρ₀pos.le]
  have hρ₁_le_half : ρ₁ ≤ ρ₀ / 2 := by rw [hρ₁def]; exact min_le_left _ _
  have hρ₁_le_r₁ : ρ₁ ≤ r₁ := by
    rw [hρ₁def]
    have h := min_le_right (ρ₀ / 2) (r₁ / 2)
    linarith only [h, hr₁pos.le]
  set L : Set ℂ := Lc ∪ Lg ∪ (Ls ∪ L' ∪ Metric.closedBall 0 (ρ₀ / 2)) with hLdef
  have hLcpt : IsCompact L := by
    rw [hLdef]
    exact (hLcc.union hLgc).union ((hLsc.union hL'c).union (isCompact_closedBall (0:ℂ) (ρ₀ / 2)))
  have hLcl_D₀ : Metric.closedBall (0 : ℂ) (ρ₀ / 2) ⊆ D₀ :=
    (Metric.closedBall_subset_ball (by linarith)).trans hρ₀sub
  have hLD₀ : L ⊆ D₀ := by
    intro z hz
    rw [hLdef] at hz
    rcases hz with hz | hz
    · rcases hz with hz | hz
      · exact hLcD₀ hz
      · exact hLgD₀ hz
    · rcases hz with hz | hz
      · rcases hz with hz | hz
        · exact hL'D₀ (hLsL' hz)
        · exact hL'D₀ hz
      · exact hLcl_D₀ hz
  have hLball : Metric.ball (0 : ℂ) (16 * Real.pi / Ξ') ⊆ L := by
    intro z hz
    rw [hLdef]
    exact Or.inl (Or.inr (hLgball (Metric.ball_subset_closedBall hz)))
  have hρ₁_sub_L : Metric.closedBall (0 : ℂ) ρ₁ ⊆ L := by
    intro z hz
    rw [hLdef]
    exact Or.inr (Or.inr (Metric.closedBall_subset_closedBall
      (by linarith only [hρ₁_le_half]) hz))
  set δ₀ : ℝ := min (min (min (min (min δc δg) δsh) (ρ₁ ^ 2 / 20))
      (ρ₁ / (20 * (M₀ + 1)))) (ρ₁ ^ 2 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200))
    with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]
    exact lt_min (lt_min (lt_min (lt_min (lt_min hδc_pos hδg_pos) hδsh_pos)
      (by positivity)) (by positivity)) (by positivity)
  have hδ₀c : δ₀ ≤ δc := by
    rw [hδ₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _))))
  have hδ₀g : δ₀ ≤ δg := by
    rw [hδ₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _))))
  have hδ₀sh : δ₀ ≤ δsh := by
    rw [hδ₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (min_le_right _ _)))
  have hδ₀sq : δ₀ ≤ ρ₁ ^ 2 / 20 := by
    rw [hδ₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ₀lin : δ₀ ≤ ρ₁ / (20 * (M₀ + 1)) := by
    rw [hδ₀def]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₀tiny : δ₀ ≤ ρ₁ ^ 2 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200) := by
    rw [hδ₀def]
    exact min_le_right _ _
  refine ⟨L, hLcpt, hLD₀, hLball, δ₀, hδ₀pos, ?_⟩
  -- ===========================================================================
  -- ## 4. the `∀ f` block
  -- ===========================================================================
  intro f Df rr u σ α hNear hf0 hInF1 hαeq hrr hudiff hub hform hexp hQmball hQpball hAdm1 hAdm2 hNTm hNTp
  -- ## 4a. monotonicity of `NearOn`, and the basic data of `f`
  have hLc_sub : Lc ⊆ L := fun z hz => by rw [hLdef]; exact Or.inl (Or.inl hz)
  have hLg_sub : Lg ⊆ L := fun z hz => by rw [hLdef]; exact Or.inl (Or.inr hz)
  have hL'_sub : L' ⊆ L := fun z hz => by rw [hLdef]; exact Or.inr (Or.inl (Or.inr hz))
  have hNear_c : MandelDim.NearOn f₀ f Df Lc δc := NearOn.mono hNear hLc_sub hδ₀c
  have hNear_g : MandelDim.NearOn f₀ f Df Lg δg := NearOn.mono hNear hLg_sub hδ₀g
  have hNear_s : ∀ z ∈ L', ‖f z - f₀ z‖ < δsh :=
    fun z hz => lt_of_lt_of_le (hNear.2.2.2 z (hL'_sub hz)) hδ₀sh
  have hNear_cl : MandelDim.NearOn f₀ f Df (Metric.closedBall (0:ℂ) ρ₁) δ₀ :=
    NearOn.mono hNear hρ₁_sub_L le_rfl
  have hInF1α : MandelDim.InF1 α := hαeq ▸ hInF1
  have hαne : α ≠ 0 := by
    intro h0; rw [h0] at hInF1α; simp [MandelDim.InF1] at hInF1α
  have hαre : α.re ≤ 1 / 2 := by rw [hαeq]; exact rotOf_re_le f
  -- ## 4b. `σ ≠ 0`
  have hσne : σ ≠ 0 := by
    intro hσ0
    have hE : ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ = 0 := by
      rw [← hexp, hσ0]
      simp
    have h := norm_alpha_le_norm_one_sub_exp hInF1α hαre
    rw [hE] at h
    exact hαne (norm_eq_zero.mp (le_antisymm h (norm_nonneg α)))
  -- ## 4c. the small data of `σ`, `u 0` and `α`
  have hδ₀ρ : δ₀ * (20 * (M₀ + 1)) ≤ ρ₁ := by
    have hpos : (0 : ℝ) < 20 * (M₀ + 1) := by linarith
    calc δ₀ * (20 * (M₀ + 1)) ≤ (ρ₁ / (20 * (M₀ + 1))) * (20 * (M₀ + 1)) :=
          mul_le_mul_of_nonneg_right hδ₀lin hpos.le
      _ = ρ₁ := by field_simp
  have hσrr : ‖σ‖ ≤ rr :=
    Work.Analysis.PertCrux.rr_ge_sigma h64 hσne hαne hInF1α hAdm2 hQpball
  obtain ⟨hσsqrt, hu1b⟩ := hsmallT hρ₁pos hρ₁_le_r₁ hδ₀pos hδ₀sq hδ₀ρ hrr hσrr hNear_cl hf0
    hudiff hub hform hexp
  have hu0lo : (1 / 2 : ℝ) ≤ ‖u 0‖ := (hub 0 (Metric.mem_ball_self hrr)).1
  have hu0hi : ‖u 0‖ ≤ 2 := (hub 0 (Metric.mem_ball_self hrr)).2
  have hσu : σ * u 0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
    rw [← hexp]; ring
  have hαle : ‖α‖ ≤ 2 * Real.sqrt (2 * δ₀) :=
    norm_alpha_le_two_sqrt hInF1α hαre hu0hi hσsqrt hσu
  -- ## 4d. the Fatou coordinates
  obtain ⟨Φm, hΦm, hKm, hcm⟩ := hcoord f Df rr u σ α hNear_c hf0 hInF1 hαeq hrr hudiff hub hform hexp
    hQmball hAdm1 hNTm
  obtain ⟨Φp, hΦp, hgatePin⟩ := hgateP f Df rr u σ α hNear_g hf0 hInF1 hαeq hrr hudiff hub hform
    hexp hQpball hAdm2 hAdm1 hNTp
  -- ## 4e. the walk and the exact identity of bracket (C)
  have hφm : ∀ w ∈ K, d.φ (w + (m : ℂ)) = f₀^[m] (d.φ w) := fun w hw =>
    (Work.Analysis.PertCrux.walk_mem_Dphi d hd (hK hw) (havoid w hw) m).2.1
  have hbasin : ∀ w ∈ K, ∀ j : ℕ, j ≤ m → f₀^[j] (d.φ w) ∈ MandelDim.ParabolicBasin f₀ D₀ :=
    fun w hw j _ => (Work.Analysis.PertCrux.walk_mem_Dphi d hd (hK hw) (havoid w hw) j).2.2 j le_rfl
  have hCz : ∀ w ∈ K, d.Φ (f₀^[m] (d.φ w)) = d.E w + (m : ℂ) := by
    intro w hw
    have hDE : ∀ j : ℕ, j ≤ m → w + (j : ℂ) ∈ d.DE := by
      intro j hj
      obtain ⟨h1, h2, h3⟩ := Work.Analysis.PertCrux.walk_mem_Dphi d hd (hK hw) (havoid w hw) j
      exact ⟨h1, h2 ▸ h3 j le_rfl⟩
    have h1 : d.E (w + (m : ℂ)) = d.E w + (m : ℂ) := ParabData.E_add_nat d (w := w) m hDE
    have h2 : d.φ (w + (m : ℂ)) = f₀^[m] (d.φ w) := hφm w hw
    rw [← h2]
    exact h1

  -- ===========================================================================
  -- ## 4f. the quantitative estimates
  -- ===========================================================================
  have hdtau0 : (0 : ℝ) ≤ dtau := by
    rw [hdtaudef]
    refine mul_nonneg hCWpos.le ?_
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have h2 := Real.log_nonneg h1
    linarith only [h2]
  -- the geometric radius: at least `2` and at least `Rgl`
  set RG : ℝ := max Rgl 2 with hRGdef
  have hRG2 : 2 ≤ RG := le_max_right Rgl 2
  have hRG0 : (0 : ℝ) ≤ RG := le_trans (by norm_num) hRG2
  have hRGl : Rgl ≤ RG := le_max_left Rgl 2
  have hRGΞ : RG ≤ Ξ' := max_le (by linarith only [hRglΞ]) (by linarith only [hΞ'10])
  have hLamRG : RG ≤ Lam / 8 := max_le (by linarith only [hLamRgl8]) (by linarith only [hLam64])
  have hLamubRG : Lam ≤ 10 ^ 6 * (Ξ' + MK + CW + RG + 1) ^ 3 + 10 ^ 6 := by
    refine le_trans hLamub ?_
    have hle : Ξ' + MK + CW + Rgl + 1 ≤ Ξ' + MK + CW + RG + 1 := by linarith only [hRGl]
    have hb : (0 : ℝ) ≤ Ξ' + MK + CW + Rgl + 1 := by
      linarith only [hMK0, hCWpos.le, hΞ'1, hRglpos.le]
    have h2 : (Ξ' + MK + CW + Rgl + 1) ^ (3 : ℕ) ≤ (Ξ' + MK + CW + RG + 1) ^ (3 : ℕ) :=
      pow_le_pow_left₀ hb hle 3
    linarith only [h2]
  obtain ⟨hu1half, hRrle, hαRsc, -, hεsRsc, hαinv20⟩ :=
    Work.Analysis.PertCrux.crux_estimates hδ hCglpos hΞ'10 hM₀nn hMK0 hCWpos.le hRglpos.le
      (by linarith only [hM₀Ξ]) hρ₁pos (by linarith only [hρ₁_le_ρ₀, hρ₀Ξ'])
      (by linarith only [hδΞ]) (by linarith only [hMKΞ]) (by linarith only [hCWΞ])
      (by linarith only [hRglΞ]) (by linarith only [hCglΞ'])
      hLam64 hLamΞ hLamMK hLamCW hLamRgl8 hLamub hdtau0 hdtau_le hRsc_ge
      (le_of_eq hRscdef) hmub hmge hδ₀tiny hu1b hαle hInF1α hαne hεspos hεs_le
  have hRsc64 : 64 ≤ Rsc := by
    have h := hRsc_ge
    rw [hRscdef] at h
    nlinarith only [h, hMK0, hLam64, sq_nonneg (Ξ' + 3 * Lam + MK + 5 * CW + 2)]
  have hRsc_pos : (0 : ℝ) < Rsc := by linarith only [hRsc64]
  obtain ⟨hσtiny, hαinj, hfarα, hCglRsc⟩ :=
    Work.Analysis.PertCrux.crux_numeric_final h64 hρ₁pos
      (by linarith only [hρ₁_le_ρ₀, hρ₀Ξ']) hδ (by linarith only [hδΞ])
      hMK0 hCWpos.le hRG2 (by linarith only [hMKΞ]) (by linarith only [hCWΞ]) hRGΞ
      hCglpos (by linarith only [hCglΞ']) hLam64 hLamΞ hLamMK hLamCW hLamRG hLamubRG
      hdtau0 hdtau_le hRsc_pos hRsc_le hmub hδ₀tiny hσsqrt hεspos hεs_le hαne hInF1α hαinv20
  -- ===========================================================================
  -- ## 4g. `Qp'` and the gate preimage of every perturbed landing point
  -- ===========================================================================
  set Qp' : Set ℂ := ⋃ w ∈ K, Metric.ball (MandelDim.tau0 (f₀^[m] (d.φ w))) 4 with hQp'def
  have hτ0p_mem : ∀ w ∈ K, MandelDim.tau0 (f₀^[m] (d.φ w)) ∈ KΦ := by
    intro w hw
    have hmem := hmcone w hw (MandelDim.tau0 (f₀^[m] (d.φ w)))
      (by rw [sub_self, norm_zero]; linarith only [hLam64])
    rw [hKΦdef]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      linarith only [hmnrm w hw, hLam64]
    · have h2 : Ξ' + 1 ≤ Ξ' + 2 * Lam := by linarith only [hLam64]
      exact le_trans h2 hmem
  have hpinnW : ∀ w ∈ K,
      ‖Φp (MandelDim.tau0 (f₀^[m] (d.φ w))) - d.Φ (f₀^[m] (d.φ w))‖ < εp := by
    intro w hw
    have h1 := hgatePin (MandelDim.tau0 (f₀^[m] (d.φ w))) (hτ0p_mem w hw)
    have h2 : MandelDim.tau0 (MandelDim.tau0 (f₀^[m] (d.φ w))) = f₀^[m] (d.φ w) :=
      Work.Pert.tau0_tau0 _
    have h3 : f₀^[m] (d.φ w) ∈ MandelDim.ParabolicBasin f₀ D₀ := hbasin w hw m le_rfl
    have h4 := h1 (by rw [h2]; exact h3)
    rwa [h2] at h4
  have hballQp : ∀ w ∈ K,
      Metric.ball (MandelDim.tau0 (f₀^[m] (d.φ w))) (RG + 2) ⊆ Work.Pert.Qp Ξ' α := by
    intro w hw
    have hcone : Ξ' + 2 * (RG + 2) < (MandelDim.tau0 (f₀^[m] (d.φ w))).re
        + |(MandelDim.tau0 (f₀^[m] (d.φ w))).im| := by
      have h := hmcone w hw (MandelDim.tau0 (f₀^[m] (d.φ w)))
        (by rw [sub_self, norm_zero]; linarith only [hLam64])
      have h4 : RG + 2 < Lam := by linarith only [hLamRG, hLam64]
      linarith only [h, h4]
    have hfar : (MandelDim.tau0 (f₀^[m] (d.φ w))).re + Ξ' - (1 / α).re + 2 * (RG + 2)
        < |(MandelDim.tau0 (f₀^[m] (d.φ w))).im - (1 / α).im| := by
      have hre : (MandelDim.tau0 (f₀^[m] (d.φ w))).re ≤ (m : ℝ) + MK + dtau := by
        have h := hW w hw m
        have h1 : (MandelDim.tau0 (f₀^[m] (d.φ w))).re
            ≤ (((m : ℂ) + d.E w)).re + dtau := by
          calc (MandelDim.tau0 (f₀^[m] (d.φ w))).re
              = (((m : ℂ) + d.E w)).re
                + (MandelDim.tau0 (f₀^[m] (d.φ w)) - ((m : ℂ) + d.E w)).re := by
                rw [← Complex.add_re]; ring
            _ ≤ (((m : ℂ) + d.E w)).re
                + ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - ((m : ℂ) + d.E w)‖ :=
                add_le_add le_rfl (Complex.re_le_norm _)
            _ ≤ (((m : ℂ) + d.E w)).re + dtau := by linarith only [h]
        have h3 : (((m : ℂ) + d.E w)).re ≤ ‖((m : ℂ) + d.E w)‖ := Complex.re_le_norm _
        have h4 : ‖((m : ℂ) + d.E w)‖ ≤ (m : ℝ) + MK := by
          calc ‖((m : ℂ) + d.E w)‖ ≤ ‖((m : ℂ))‖ + ‖d.E w‖ := norm_add_le _ _
            _ = (m : ℝ) + ‖d.E w‖ := by rw [Complex.norm_natCast]
            _ ≤ (m : ℝ) + MK := by linarith only [hMK w hw]
        linarith only [h1, h3, h4]
      have habs : (0 : ℝ) ≤ |(MandelDim.tau0 (f₀^[m] (d.φ w))).im - (1 / α).im| := abs_nonneg _
      have hneg : (MandelDim.tau0 (f₀^[m] (d.φ w))).re + Ξ' - (1 / α).re + 2 * (RG + 2) < 0 := by
        linarith only [hre, hfarα]
      linarith only [hneg, habs]
    exact (Work.Analysis.PertCrux.ball_subset_gates (Ξ' := Ξ') (R := RG + 2) (α := α)
      (z := MandelDim.tau0 (f₀^[m] (d.φ w))) (by linarith only [hRG0]) hcone hfar).1
  -- the gate preimage of the perturbed landing point `ρ_w`, with its two quantitative bounds
  have hexζ : ∀ w ∈ K, ∃ ζ : ℂ,
      ζ ∈ Metric.ball (MandelDim.tau0 (f₀^[m] (d.φ w))) 2 ∧
      Work.Pert.tauC σ α ζ
        = f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w) ∧
      ‖ζ - MandelDim.tau0 (f₀^[m] (d.φ w))‖
        ≤ 64 * (‖u 0 - 1‖ + ‖α‖ * (Rsc + 1)) * (Rsc + 1) + 2 * εs * Rsc ^ 2 := by
    intro w hw
    have hcxε₀ : Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w
        ∈ Metric.ball (d.φ w) ε₀ := by
      rw [Metric.mem_ball, Complex.dist_eq]
      exact lt_of_lt_of_le (hcm w hw) hεcε₀
    have hcxLs : Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w ∈ Ls :=
      hballε₀ w hw hcxε₀
    have hφwLs : d.φ w ∈ Ls := hballε₀ w hw (Metric.mem_ball_self hε₀0)
    have hdist : ‖Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w
        - d.φ w‖ < η := lt_of_lt_of_le (hcm w hw) hεcη
    have hρp : ‖f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)
        - f₀^[m] (d.φ w)‖ < εs := hshadow hNear_s hcxLs hφwLs hdist m le_rfl
    -- `p_w ≠ 0`
    have hpwne : f₀^[m] (d.φ w) ≠ 0 := by
      intro h0
      have hmem0 : Ξ' + 2 * Lam ≤ (MandelDim.tau0 (f₀^[m] (d.φ w))).re
          + |(MandelDim.tau0 (f₀^[m] (d.φ w))).im| :=
        hmcone w hw _ (by rw [sub_self, norm_zero]; linarith only [hLam64])
      rw [h0] at hmem0
      have h00 : MandelDim.tau0 (0 : ℂ) = 0 := by simp [MandelDim.tau0]
      rw [h00] at hmem0
      simp only [Complex.zero_re, Complex.zero_im, abs_zero, add_zero] at hmem0
      linarith only [hmem0, hΞ'1, hLam64]
    have hτ0p_le : ‖MandelDim.tau0 (f₀^[m] (d.φ w))‖ ≤ Rsc := hmnrm w hw
    have hpwlb : 1 / Rsc ≤ ‖f₀^[m] (d.φ w)‖ := by
      have h1 : ‖MandelDim.tau0 (f₀^[m] (d.φ w))‖ = 1 / ‖f₀^[m] (d.φ w)‖ := by
        rw [MandelDim.tau0, norm_div, norm_neg, norm_one]
      rw [h1] at hτ0p_le
      have h2 : 0 < ‖f₀^[m] (d.φ w)‖ := norm_pos_iff.mpr hpwne
      rw [div_le_iff₀ h2] at hτ0p_le
      rw [div_le_iff₀ hRsc_pos]
      simpa only [mul_comm] using hτ0p_le
    have hεs_small : εs ≤ (1 / 2) / Rsc := by
      rw [le_div_iff₀ hRsc_pos]
      have h : (εs * Rsc) * Rsc ≤ (1 / 2) * Rsc := by nlinarith only [hεsRsc, hRsc64]
      exact le_of_mul_le_mul_right h hRsc_pos
    have hsub : 1 / Rsc - (1 / 2) / Rsc = (1 / 2) / Rsc := by
      rw [div_sub_div_same]
      norm_num
    have hρlow : 1 / Rsc - εs ≤ ‖f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)‖ := by
      have h1 : ‖f₀^[m] (d.φ w)‖
          ≤ ‖f₀^[m] (d.φ w) - f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)‖
            + ‖f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)‖ :=
        norm_le_norm_add_sub _ _
      have h2 : ‖f₀^[m] (d.φ w) - f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)‖
          = ‖f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)
              - f₀^[m] (d.φ w)‖ := norm_sub_rev _ _
      rw [h2] at h1
      linarith only [h1, hρp, hpwlb]
    have hρwlb : (1 / 2) / Rsc
        ≤ ‖f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)‖ := by
      linarith only [hρlow, hεs_small, hsub]
    have hρne : f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w) ≠ 0 := by
      intro h0
      rw [h0, zero_sub, norm_neg] at hρp
      have hhalf : (1 / 2) / Rsc < 1 / Rsc := by
        rw [div_lt_div_iff₀ hRsc_pos hRsc_pos]
        linarith only [hRsc_pos]
      linarith only [hρp, hpwlb, hεs_small, hhalf]
    have hρσ : f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w) ≠ σ := by
      intro h0
      rw [h0] at hρwlb
      linarith only [hσtiny, hρwlb]
    have hτclose : ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))
        - MandelDim.tau0 (f₀^[m] (d.φ w))‖ ≤ 2 * εs * Rsc ^ 2 := by
      have hkey : MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))
          - MandelDim.tau0 (f₀^[m] (d.φ w))
          = (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)
              - f₀^[m] (d.φ w))
            / (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)
              * f₀^[m] (d.φ w)) := by
        simp only [MandelDim.tau0]
        field_simp
        ring
      rw [hkey, norm_div, norm_mul, div_le_iff₀ (by positivity)]
      have hD : (1 / 2) / Rsc * (1 / Rsc) = 1 / (2 * Rsc ^ 2) := by
        have hL : (1 / 2) / Rsc * (1 / Rsc) = (1 / 2) * (Rsc ^ 2)⁻¹ := by
          rw [div_eq_mul_inv, div_eq_mul_inv, one_div, pow_two, mul_inv]
          ring
        have hR : 1 / (2 * Rsc ^ 2) = (1 / 2) * (Rsc ^ 2)⁻¹ := by
          rw [one_div, mul_inv]
          ring
        rw [hL, hR]
      have hden : 1 / (2 * Rsc ^ 2)
          ≤ ‖f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)‖
            * ‖f₀^[m] (d.φ w)‖ :=
        hD ▸ mul_le_mul hρwlb hpwlb (by positivity) (by positivity)
      have hfin : εs ≤ 2 * εs * Rsc ^ 2 * (1 / (2 * Rsc ^ 2)) := by
        have h2 : 2 * Rsc ^ 2 * (1 / (2 * Rsc ^ 2)) = 1 := by
          rw [one_div, mul_inv_cancel₀ (by positivity : (2 : ℝ) * Rsc ^ 2 ≠ 0)]
        have h3 : 2 * εs * Rsc ^ 2 * (1 / (2 * Rsc ^ 2))
            = εs * (2 * Rsc ^ 2 * (1 / (2 * Rsc ^ 2))) := by ring
        rw [h3, h2, mul_one]
      calc ‖f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)
              - f₀^[m] (d.φ w)‖
          ≤ εs := le_of_lt hρp
        _ ≤ 2 * εs * Rsc ^ 2 * (1 / (2 * Rsc ^ 2)) := hfin
        _ ≤ 2 * εs * Rsc ^ 2
              * (‖f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)‖
                * ‖f₀^[m] (d.φ w)‖) := by
            exact mul_le_mul_of_nonneg_left hden (by positivity)
    have hτclose' : ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))
        - MandelDim.tau0 (f₀^[m] (d.φ w))‖ ≤ 1 / 2 := by
      linarith only [hτclose, hεsRsc]
    have hτ0ρ_le : ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖
        ≤ Rsc + 1 := by
      calc ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖
          ≤ ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))
              - MandelDim.tau0 (f₀^[m] (d.φ w))‖ + ‖MandelDim.tau0 (f₀^[m] (d.φ w))‖ :=
            norm_le_norm_add_sub _ _
        _ ≤ 2 * εs * Rsc ^ 2 + Rsc := by linarith only [hτclose, hτ0p_le]
        _ ≤ Rsc + 1 := by linarith only [hεsRsc]
    have hbd' : 64 * (‖u 0 - 1‖ + ‖α‖
          * ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖)
        * ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖
        ≤ 64 * (‖u 0 - 1‖ + ‖α‖ * (Rsc + 1)) * (Rsc + 1) := by
      have h2 : ‖u 0 - 1‖ + ‖α‖
          * ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖
          ≤ ‖u 0 - 1‖ + ‖α‖ * (Rsc + 1) := by
        have h3 := mul_le_mul_of_nonneg_left hτ0ρ_le (norm_nonneg α)
        linarith only [h3]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) hτ0ρ_le
        (by positivity) (by positivity)
    have hsmall64 : 64 * ‖α‖
        * ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖
        ≤ 1 := by
      have h1 : ‖α‖ * (Rsc + 1) ≤ 1 / 64 := hαRsc
      calc 64 * ‖α‖
            * ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖
          ≤ 64 * ‖α‖ * (Rsc + 1) := mul_le_mul_of_nonneg_left hτ0ρ_le (by positivity)
        _ ≤ 1 := by linarith only [h1]
    have hRrval : 64 * (‖u 0 - 1‖ + ‖α‖
        * ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖)
        * ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖
        ≤ 1 / 2 := by
      calc 64 * (‖u 0 - 1‖ + ‖α‖
              * ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖)
            * ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖
          ≤ 64 * (‖u 0 - 1‖ + ‖α‖ * (Rsc + 1)) * (Rsc + 1) := hbd'
        _ ≤ 1 / 2 := le_trans hRrle (min_le_left _ _)
    have hroom : Metric.ball (MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)))
        (64 * (‖u 0 - 1‖ + ‖α‖
          * ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖)
          * ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖)
        ⊆ Work.Pert.Qp Ξ' α := by
      refine Subset.trans ?_ (hballQp w hw)
      intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      rw [Metric.mem_ball, Complex.dist_eq]
      have h1 : ‖z - MandelDim.tau0 (f₀^[m] (d.φ w))‖
          ≤ ‖z - MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖
            + ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))
              - MandelDim.tau0 (f₀^[m] (d.φ w))‖ := by
        have h := dist_triangle z
          (MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)))
          (MandelDim.tau0 (f₀^[m] (d.φ w)))
        simpa only [dist_eq_norm] using h
      have h2 : ‖z - MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖
          ≤ 1 / 2 := le_of_lt (lt_of_lt_of_le hz hRrval)
      linarith only [h1, h2, hτclose', hRG2]
    obtain ⟨ζ, -, hζeq, hζbd⟩ := Work.PertCrux.exists_tauC_preimage_gate h64 hu0lo hu1half hexp
      hσne hInF1α hAdm2 hρne hρσ hsmall64 hroom
    refine ⟨ζ, ?_, hζeq, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have h1 : ‖ζ - MandelDim.tau0 (f₀^[m] (d.φ w))‖
          ≤ ‖ζ - MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖
            + ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))
              - MandelDim.tau0 (f₀^[m] (d.φ w))‖ := by
        have h := dist_triangle ζ
          (MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)))
          (MandelDim.tau0 (f₀^[m] (d.φ w)))
        simpa only [dist_eq_norm] using h
      have h2 : ‖ζ - MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖
          ≤ 1 / 2 := le_trans hζbd hRrval
      linarith only [h1, h2, hτclose']
    · have h1 : ‖ζ - MandelDim.tau0 (f₀^[m] (d.φ w))‖
          ≤ ‖ζ - MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))‖
            + ‖MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))
              - MandelDim.tau0 (f₀^[m] (d.φ w))‖ := by
        have h := dist_triangle ζ
          (MandelDim.tau0 (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)))
          (MandelDim.tau0 (f₀^[m] (d.φ w)))
        simpa only [dist_eq_norm] using h
      linarith only [h1, hζbd, hbd', hτclose]
  have hζex : ∀ w : ℂ, ∃ ζ : ℂ, w ∈ K →
      (ζ ∈ Metric.ball (MandelDim.tau0 (f₀^[m] (d.φ w))) 2 ∧
        Work.Pert.tauC σ α ζ
          = f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w) ∧
        ‖ζ - MandelDim.tau0 (f₀^[m] (d.φ w))‖
          ≤ 64 * (‖u 0 - 1‖ + ‖α‖ * (Rsc + 1)) * (Rsc + 1) + 2 * εs * Rsc ^ 2) := by
    intro w
    by_cases hw : w ∈ K
    · exact ⟨(hexζ w hw).choose, fun _ => (hexζ w hw).choose_spec⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose ζ hζ2 using hζex
  have hζmem2 : ∀ w ∈ K, ζ w ∈ Metric.ball (MandelDim.tau0 (f₀^[m] (d.φ w))) 2 :=
    fun w hw => (hζ2 w hw).1
  have hζeq' : ∀ w ∈ K, Work.Pert.tauC σ α (ζ w)
      = f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w) :=
    fun w hw => (hζ2 w hw).2.1
  have hζbd' : ∀ w ∈ K, ‖ζ w - MandelDim.tau0 (f₀^[m] (d.φ w))‖
      ≤ 64 * (‖u 0 - 1‖ + ‖α‖ * (Rsc + 1)) * (Rsc + 1) + 2 * εs * Rsc ^ 2 :=
    fun w hw => (hζ2 w hw).2.2
  have hζmem : ∀ w ∈ K, ζ w ∈ Qp' := by
    intro w hw
    rw [hQp'def]
    exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hw,
      Metric.ball_subset_ball (by norm_num) (hζmem2 w hw)⟩⟩
  have hζτ : ∀ w ∈ K, ‖ζ w - MandelDim.tau0 (f₀^[m] (d.φ w))‖ < 2 := by
    intro w hw
    have hz := hζmem2 w hw
    rwa [Metric.mem_ball, Complex.dist_eq] at hz
  have hdiam : ∀ w ∈ K, ∀ w' ∈ K,
      ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - MandelDim.tau0 (f₀^[m] (d.φ w'))‖ + 2 * 4 < 1 / ‖α‖ := by
    intro w hw w' hw'
    have h1 : ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - ((m : ℂ) + d.E w)‖ ≤ dtau := hW w hw m
    have h2 : ‖MandelDim.tau0 (f₀^[m] (d.φ w')) - ((m : ℂ) + d.E w')‖ ≤ dtau := hW w' hw' m
    have h3 : ‖d.E w - d.E w'‖ ≤ 2 * MK := by
      calc ‖d.E w - d.E w'‖ ≤ ‖d.E w‖ + ‖d.E w'‖ := norm_sub_le _ _
        _ ≤ MK + MK := by linarith only [hMK w hw, hMK w' hw']
        _ = 2 * MK := by ring
    have h4 : ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - MandelDim.tau0 (f₀^[m] (d.φ w'))‖
        ≤ 2 * dtau + 2 * MK := by
      have hsplit : MandelDim.tau0 (f₀^[m] (d.φ w)) - MandelDim.tau0 (f₀^[m] (d.φ w'))
          = (MandelDim.tau0 (f₀^[m] (d.φ w)) - ((m : ℂ) + d.E w))
            + (((m : ℂ) + d.E w) - ((m : ℂ) + d.E w'))
            + (((m : ℂ) + d.E w') - MandelDim.tau0 (f₀^[m] (d.φ w'))) := by ring
      rw [hsplit]
      calc ‖(MandelDim.tau0 (f₀^[m] (d.φ w)) - ((m : ℂ) + d.E w))
            + (((m : ℂ) + d.E w) - ((m : ℂ) + d.E w'))
            + (((m : ℂ) + d.E w') - MandelDim.tau0 (f₀^[m] (d.φ w')))‖
          ≤ ‖(MandelDim.tau0 (f₀^[m] (d.φ w)) - ((m : ℂ) + d.E w))
              + (((m : ℂ) + d.E w) - ((m : ℂ) + d.E w'))‖
            + ‖((m : ℂ) + d.E w') - MandelDim.tau0 (f₀^[m] (d.φ w'))‖ := norm_add_le _ _
        _ ≤ (‖MandelDim.tau0 (f₀^[m] (d.φ w)) - ((m : ℂ) + d.E w)‖
              + ‖((m : ℂ) + d.E w) - ((m : ℂ) + d.E w')‖)
            + ‖((m : ℂ) + d.E w') - MandelDim.tau0 (f₀^[m] (d.φ w'))‖ := by
            have h := norm_add_le (MandelDim.tau0 (f₀^[m] (d.φ w)) - ((m : ℂ) + d.E w))
              (((m : ℂ) + d.E w) - ((m : ℂ) + d.E w'))
            linarith only [h]
        _ ≤ (dtau + 2 * MK) + dtau := by
            have h5 : ‖((m : ℂ) + d.E w) - ((m : ℂ) + d.E w')‖ = ‖d.E w - d.E w'‖ := by
              apply congrArg norm; ring
            have h6 : ‖((m : ℂ) + d.E w') - MandelDim.tau0 (f₀^[m] (d.φ w'))‖
                = ‖MandelDim.tau0 (f₀^[m] (d.φ w')) - ((m : ℂ) + d.E w')‖ := norm_sub_rev _ _
            rw [h5, h6]
            linarith only [h1, h2, h3]
        _ = 2 * dtau + 2 * MK := by ring
    linarith only [h4, hαinj]
  have hQp'props := Work.Analysis.PertCrux.QpPrime_props (Ξ' := Ξ') hσne hαne
    (ζ := fun w => MandelDim.tau0 (f₀^[m] (d.φ w))) (r := 4) (by norm_num)
    (fun w hw => (Metric.ball_subset_ball (by linarith only [hRG2])).trans (hballQp w hw)) hdiam
  have hQp'open : IsOpen Qp' := by rw [hQp'def]; exact hQp'props.1
  have hQp'sub : Qp' ⊆ Work.Pert.Qp Ξ' α := by rw [hQp'def]; exact hQp'props.2.1
  have hQp'inj : Set.InjOn (Work.Pert.tauC σ α) Qp' := by rw [hQp'def]; exact hQp'props.2.2.1
  have hinvOn : ∀ w ∈ K, Work.Pert.invOn (Work.Pert.tauC σ α) Qp'
      (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)) = ζ w := by
    intro w hw
    exact Work.Pert.invOn_eq hQp'inj ⟨ζ w, hζmem w hw, hζeq' w hw⟩ (hζmem w hw) (hζeq' w hw)
  -- the two Lipschitz constants of the residual
  have hCR : Cgl * (64 * (‖u 0 - 1‖ + ‖α‖ * (Rsc + 1)) * (Rsc + 1)) ≤ δ / 8 := by
    have h4 : 64 * (‖u 0 - 1‖ + ‖α‖ * (Rsc + 1)) * (Rsc + 1) ≤ δ / (8 * Cgl) :=
      le_trans hRrle (min_le_right _ _)
    have h5 : Cgl * (δ / (8 * Cgl)) = δ / 8 := by
      have h : Cgl * (δ / (8 * Cgl)) = Cgl * δ / (8 * Cgl) := by ring
      rw [h, mul_div_assoc]
      field_simp
    have h6 : Cgl * (64 * (‖u 0 - 1‖ + ‖α‖ * (Rsc + 1)) * (Rsc + 1))
        ≤ Cgl * (δ / (8 * Cgl)) := mul_le_mul_of_nonneg_left h4 hCglpos.le
    linarith only [h6, h5]
  have hCε : Cgl * (2 * εs * Rsc ^ 2) ≤ δ / 4 := by
    have h1 : 2 * Cgl * Rsc ^ 2 / (10 ^ 9 * (Ξ' ^ 2 + 1) ^ 20) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      linarith only [hCglRsc]
    calc Cgl * (2 * εs * Rsc ^ 2) = 2 * Cgl * Rsc ^ 2 * εs := by ring
      _ ≤ 2 * Cgl * Rsc ^ 2 * (δ / (10 ^ 9 * (Ξ' ^ 2 + 1) ^ 20)) :=
          mul_le_mul_of_nonneg_left hεs_le (by positivity)
      _ = δ * (2 * Cgl * Rsc ^ 2 / (10 ^ 9 * (Ξ' ^ 2 + 1) ^ 20)) := by ring
      _ ≤ δ * (1 / 4) := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ / 4 := by ring
  -- the residual
  have hres : ∀ w ∈ K, ‖Φp (Work.Pert.invOn (Work.Pert.tauC σ α) Qp'
      (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)))
      - (m : ℂ) - (0 : ℂ) - d.E w‖ < δ := by
    intro w hw
    rw [hinvOn w hw]
    have htube : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Metric.closedBall ((1 - t) * ζ w + t * MandelDim.tau0 (f₀^[m] (d.φ w))) RG
          ⊆ Work.Pert.Qp Ξ' α := by
      intro t ht
      refine Subset.trans ?_ (hballQp w hw)
      intro z hz2
      rw [Metric.mem_closedBall, Complex.dist_eq] at hz2
      rw [Metric.mem_ball, Complex.dist_eq]
      have hzx : (1 - t) * ζ w + t * MandelDim.tau0 (f₀^[m] (d.φ w))
          - MandelDim.tau0 (f₀^[m] (d.φ w))
          = (1 - t) • (ζ w - MandelDim.tau0 (f₀^[m] (d.φ w))) := by
        rw [Complex.real_smul]
        push_cast
        ring
      have h1 : ‖(1 - t) * ζ w + t * MandelDim.tau0 (f₀^[m] (d.φ w))
          - MandelDim.tau0 (f₀^[m] (d.φ w))‖ < 2 := by
        rw [hzx, norm_smul, Real.norm_eq_abs]
        have h2 : |1 - t| ≤ 1 := by
          rw [abs_le]
          exact ⟨by linarith only [ht.2], by linarith only [ht.1]⟩
        have h4 : (0 : ℝ) ≤ ‖ζ w - MandelDim.tau0 (f₀^[m] (d.φ w))‖ := norm_nonneg _
        calc |1 - t| * ‖ζ w - MandelDim.tau0 (f₀^[m] (d.φ w))‖
            ≤ 1 * ‖ζ w - MandelDim.tau0 (f₀^[m] (d.φ w))‖ := mul_le_mul_of_nonneg_right h2 h4
          _ = ‖ζ w - MandelDim.tau0 (f₀^[m] (d.φ w))‖ := one_mul _
          _ < 2 := hζτ w hw
      have hs : ‖z - MandelDim.tau0 (f₀^[m] (d.φ w))‖
          ≤ ‖z - ((1 - t) * ζ w + t * MandelDim.tau0 (f₀^[m] (d.φ w)))‖
            + ‖(1 - t) * ζ w + t * MandelDim.tau0 (f₀^[m] (d.φ w))
              - MandelDim.tau0 (f₀^[m] (d.φ w))‖ := by
        have h := dist_triangle z ((1 - t) * ζ w + t * MandelDim.tau0 (f₀^[m] (d.φ w)))
          (MandelDim.tau0 (f₀^[m] (d.φ w)))
        simpa only [dist_eq_norm] using h
      linarith only [hs, hz2, h1]
    have hgate : ‖Φp (ζ w) - Φp (MandelDim.tau0 (f₀^[m] (d.φ w)))‖
        ≤ Cgl * ‖ζ w - MandelDim.tau0 (f₀^[m] (d.φ w))‖ :=
      hgatelip (Ξ' := Ξ') (σ := σ) (α := α) (u := u) (Φ := Φp) (R := RG)
        (x := ζ w) (y := MandelDim.tau0 (f₀^[m] (d.φ w))) h64 (by linarith only [hRGl])
        hAdm2 hNTp hΦp htube
    have hA2 : ‖Φp (ζ w) - Φp (MandelDim.tau0 (f₀^[m] (d.φ w)))‖ ≤ δ / 8 + δ / 4 := by
      have hb := hζbd' w hw
      have h1 : Cgl * ‖ζ w - MandelDim.tau0 (f₀^[m] (d.φ w))‖ ≤ Cgl
          * (64 * (‖u 0 - 1‖ + ‖α‖ * (Rsc + 1)) * (Rsc + 1) + 2 * εs * Rsc ^ 2) :=
        mul_le_mul_of_nonneg_left hb hCglpos.le
      have h2 : Cgl * (64 * (‖u 0 - 1‖ + ‖α‖ * (Rsc + 1)) * (Rsc + 1) + 2 * εs * Rsc ^ 2)
          = Cgl * (64 * (‖u 0 - 1‖ + ‖α‖ * (Rsc + 1)) * (Rsc + 1))
            + Cgl * (2 * εs * Rsc ^ 2) := by ring
      linarith only [hgate, h1, h2, hCR, hCε]
    have hzC : d.Φ (f₀^[m] (d.φ w)) - (m : ℂ) - d.E w = 0 := by
      have h := hCz w hw
      linear_combination h
    have hB : ‖Φp (MandelDim.tau0 (f₀^[m] (d.φ w))) - d.Φ (f₀^[m] (d.φ w))‖ < εp := hpinnW w hw
    have hsplit : Φp (ζ w) - (m : ℂ) - (0 : ℂ) - d.E w
        = (Φp (ζ w) - Φp (MandelDim.tau0 (f₀^[m] (d.φ w))))
          + (Φp (MandelDim.tau0 (f₀^[m] (d.φ w))) - d.Φ (f₀^[m] (d.φ w)))
          + (d.Φ (f₀^[m] (d.φ w)) - (m : ℂ) - d.E w) := by ring
    rw [hsplit]
    have htri : ‖(Φp (ζ w) - Φp (MandelDim.tau0 (f₀^[m] (d.φ w))))
        + (Φp (MandelDim.tau0 (f₀^[m] (d.φ w))) - d.Φ (f₀^[m] (d.φ w)))
        + (d.Φ (f₀^[m] (d.φ w)) - (m : ℂ) - d.E w)‖
        ≤ ‖Φp (ζ w) - Φp (MandelDim.tau0 (f₀^[m] (d.φ w)))‖
          + ‖Φp (MandelDim.tau0 (f₀^[m] (d.φ w))) - d.Φ (f₀^[m] (d.φ w))‖
          + ‖d.Φ (f₀^[m] (d.φ w)) - (m : ℂ) - d.E w‖ := by
      have h1 := norm_add_le (Φp (ζ w) - Φp (MandelDim.tau0 (f₀^[m] (d.φ w)))
          + (Φp (MandelDim.tau0 (f₀^[m] (d.φ w))) - d.Φ (f₀^[m] (d.φ w))))
          (d.Φ (f₀^[m] (d.φ w)) - (m : ℂ) - d.E w)
      have h2 := norm_add_le (Φp (ζ w) - Φp (MandelDim.tau0 (f₀^[m] (d.φ w))))
          (Φp (MandelDim.tau0 (f₀^[m] (d.φ w))) - d.Φ (f₀^[m] (d.φ w)))
      linarith only [h1, h2]
    have hbnd : ‖Φp (ζ w) - Φp (MandelDim.tau0 (f₀^[m] (d.φ w)))‖
        + ‖Φp (MandelDim.tau0 (f₀^[m] (d.φ w))) - d.Φ (f₀^[m] (d.φ w))‖
        + ‖d.Φ (f₀^[m] (d.φ w)) - (m : ℂ) - d.E w‖ ≤ 5 * δ / 8 := by
      have hC0 : ‖d.Φ (f₀^[m] (d.φ w)) - (m : ℂ) - d.E w‖ = 0 := by rw [hzC, norm_zero]
      linarith only [hA2, hB, hC0, hεpdef, hδ]
    exact lt_of_le_of_lt (le_trans htri hbnd) (by linarith only [hδ])
  refine ⟨Φm, Φp, Qp', m, (0 : ℤ), hΦm, hΦp, hQp'open, hQp'sub, hQp'inj, ?_, ?_, ?_⟩
  · -- F-closure of the landing points
    intro w hw
    rw [hinvOn w hw]
    have h1 : ‖Work.Pert.liftF u σ α (ζ w) - (ζ w + 1)‖ ≤ 1 / 32 :=
      (hNTp.1.2 (ζ w) (hQp'sub (hζmem w hw))).1
    rw [hQp'def]
    refine Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hw, ?_⟩⟩
    rw [Metric.mem_ball, Complex.dist_eq]
    have h3 : ‖Work.Pert.liftF u σ α (ζ w) - MandelDim.tau0 (f₀^[m] (d.φ w))‖
        ≤ ‖Work.Pert.liftF u σ α (ζ w) - (ζ w + 1)‖
          + ‖(ζ w + 1) - MandelDim.tau0 (f₀^[m] (d.φ w))‖ := by
      have h := dist_triangle (Work.Pert.liftF u σ α (ζ w)) (ζ w + 1)
        (MandelDim.tau0 (f₀^[m] (d.φ w)))
      simpa only [dist_eq_norm] using h
    have h4 : ‖(ζ w + 1) - MandelDim.tau0 (f₀^[m] (d.φ w))‖
        ≤ ‖ζ w - MandelDim.tau0 (f₀^[m] (d.φ w))‖ + 1 := by
      have h5 : (ζ w + 1) - MandelDim.tau0 (f₀^[m] (d.φ w))
          = (ζ w - MandelDim.tau0 (f₀^[m] (d.φ w))) + 1 := by ring
      rw [h5]
      simpa using norm_add_le (ζ w - MandelDim.tau0 (f₀^[m] (d.φ w))) (1 : ℂ)
    have h6 : ‖ζ w - MandelDim.tau0 (f₀^[m] (d.φ w))‖ < 2 := hζτ w hw
    linarith only [h1, h3, h4, h6]
  · -- the orbits stay in `Df` and land in the gate image
    intro w hw
    refine ⟨?_, ?_⟩
    · intro j hj
      have hcxε₀ : Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w
          ∈ Metric.ball (d.φ w) ε₀ := by
        rw [Metric.mem_ball, Complex.dist_eq]
        exact lt_of_lt_of_le (hcm w hw) hεcε₀
      by_cases hj0 : j = 0
      · subst hj0
        simpa using hNear.2.1 (hL'_sub (hLsL' (hballε₀ w hw hcxε₀)))
      · have h1 : ‖f^[j] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)
            - f₀^[j] (d.φ w)‖ < εs :=
          hshadow hNear_s (hballε₀ w hw hcxε₀) (hballε₀ w hw (Metric.mem_ball_self hε₀0))
            (lt_of_lt_of_le (hcm w hw) hεcη) j hj
        have h3 : f₀^[j] (d.φ w) = f₀ (f₀^[j-1] (d.φ w)) := by
          conv_lhs => rw [show j = (j - 1) + 1 by omega, Function.iterate_succ_apply']
        have h4 : f₀^[j-1] (d.φ w) ∈ Ls := horb w hw (j - 1) (by omega)
        have h5 : Metric.ball (f₀ (f₀^[j-1] (d.φ w))) rom ⊆ L' := hroomL' _ h4
        have h6 : f^[j] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)
            ∈ Metric.ball (f₀ (f₀^[j-1] (d.φ w))) rom := by
          rw [Metric.mem_ball, Complex.dist_eq, ← h3]
          exact lt_of_lt_of_le h1 hεsrom
        exact hNear.2.1 (hL'_sub (h5 h6))
    · exact ⟨ζ w, hζmem w hw, hζeq' w hw⟩
  · intro w hw
    simpa using hres w hw

end Work.PertCrux
