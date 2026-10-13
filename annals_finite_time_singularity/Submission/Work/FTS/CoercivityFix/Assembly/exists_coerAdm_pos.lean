import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.CoercivityFix.Assembly.WitDefs
import Submission.Work.FTS.LocDataExt.Majorant5
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.LocDataExt.SepFactor
import Submission.Work.FTS.LocDataExt.Traces
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.HlocFactor
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.angMaj_mem
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.Vocab
import Submission.Work.Construction.Defs
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-! ## The angular jet bound, for every `α > 0`

The delivered `Work.FTS.LocData.DthIter_Gam_abs_le` and `Work.FTS.LocDataExt.DthIter_Gam_abs_le5`
carry the hypothesis `α ≤ 1` (they bound the polynomials `Qp j α` on `[-1,1]` by numerical
constants valid only there).  The non-vacuity statement is for **every** `α > 0`, so we redo the
bound with an `α`-dependent constant: `Tfun j α` is continuous on the compact `Iθ`, hence
bounded, and `Work.Spaces.dthU_iter_Gam_abs_bound` (which has no restriction on `α`) turns a
bound on `Tfun (i-1) α` into `|D_θ^i Γ| ≤ C·Γ`. -/

/-- `Tfun j α` is bounded on the compact interval `Iθ`. -/
theorem Tfun_bounded (α : ℝ) (j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun j α θ| ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((Work.Spaces.Tfun_smooth j α).continuous.continuousOn)
  refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
  have hθ' : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hθ
  have h := hC θ hθ'
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

/-- **Angular jet bound for every `α > 0`**: `|D_θ^i Γ| ≤ C·Γ` on `Iθ` for `i ≤ 5`. -/
theorem witGam_bound (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ℕ, i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
        ≤ C * Work.Spaces.Gam α θ := by
  classical
  let M : ℕ → ℝ := fun j => Classical.choose (Tfun_bounded α j)
  have hMspec : ∀ j : ℕ, 0 ≤ M j ∧
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun j α θ| ≤ M j :=
    fun j => Classical.choose_spec (Tfun_bounded α j)
  refine ⟨max 1 (∑ j ∈ Finset.range 5, (α * M j + 1)), ?_, ?_⟩
  · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
  · intro i hi θ hθ
    have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      rw [Work.Spaces.DthIter_zero, abs_of_nonneg hG0]
      calc Work.Spaces.Gam α θ = 1 * Work.Spaces.Gam α θ := by ring
        _ ≤ (max 1 (∑ j ∈ Finset.range 5, (α * M j + 1))) * Work.Spaces.Gam α θ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hG0
    · have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i h α hα (M (i - 1))
        (fun θ' hθ' => (hMspec (i - 1)).2 θ' hθ') θ hθ
      rw [Work.FTS.LocData.DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]
      have hMle : α * M (i - 1) + 1 ≤ ∑ j ∈ Finset.range 5, (α * M j + 1) := by
        refine Finset.single_le_sum (s := Finset.range 5) (f := fun j => α * M j + 1)
          (fun j _ => ?_) (Finset.mem_range.mpr (by omega))
        have := (hMspec j).1
        nlinarith [hα]
      have h2 : α * M (i - 1) ≤ max 1 (∑ j ∈ Finset.range 5, (α * M j + 1)) :=
        le_trans (le_of_lt (by linarith [hMle])) (le_max_right _ _)
      calc |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
          ≤ α * M (i - 1) * Work.Spaces.Gam α θ := hkey
        _ ≤ (max 1 (∑ j ∈ Finset.range 5, (α * M j + 1))) * Work.Spaces.Gam α θ :=
            mul_le_mul_of_nonneg_right h2 hG0

/-! ## The radial weighted bound -/

/-- **The radial bound** of the separable `ℋ^k`-majorant for `radW = D_z(bumpZ)`: the jets of
`radW` up to order `5` are bounded (they are the jets of the bump up to order `6`), and the
weight `w` is controlled by `(1+z)^{-2}` on the support of the bump. -/
theorem radW_bound :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j : ℕ, j ≤ 5 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => radW z) z θ
        * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2 := by
  classical
  set D : ℝ := ∑ c ∈ Finset.range 7,
    Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c) with hDdef
  have hMspec : ∀ c : ℕ, 0 ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c)
      ∧ ∀ z : ℝ, |(Work.FTS.LocData.T1^[c]) Work.FTS.LocData.bumpZ z|
        ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c) :=
    fun c => Classical.choose_spec (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c)
  have hDnn : 0 ≤ D := by
    rw [hDdef]
    exact Finset.sum_nonneg (fun c _ => (hMspec c).1)
  have hjet : ∀ j : ℕ, j ≤ 5 → ∀ z θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => radW z) z θ| ≤ D := by
    intro j hj z θ
    rw [DzIter_radW j, Work.FTS.LocData.DzIter_bumpZ_eq (j + 1) θ z]
    have h1 := (hMspec (j + 1)).2 z
    have h2 : Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ (j + 1)) ≤ D :=
      Finset.single_le_sum (fun c _ => (hMspec c).1) (Finset.mem_range.mpr (by omega))
    linarith
  refine ⟨D ^ 2 * (1771561 / 1296 : ℝ), by positivity, fun j hj z hz θ => ?_⟩
  rw [mul_pow]
  by_cases hsupp : z ∈ Set.Icc (3 / 4 : ℝ) (7 / 4)
  · have h1 : (Work.Spaces.DzIter j (fun z _ => radW z) z θ) ^ 2 ≤ D ^ 2 := by
      have h := hjet j hj z θ
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      rwa [sq_abs] at h2
    have hw := Work.FTS.LocData.w_sq_le_on_support hsupp
    calc (Work.Spaces.DzIter j (fun z _ => radW z) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ D ^ 2 * ((1771561 / 1296 : ℝ) / (1 + z) ^ 2) :=
          mul_le_mul h1 hw (sq_nonneg _) (by positivity)
      _ = D ^ 2 * (1771561 / 1296 : ℝ) / (1 + z) ^ 2 := by ring
  · have hev : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, radW z' = 0 := by
      have hmem : (Set.Icc (3 / 4 : ℝ) (7 / 4))ᶜ ∈ 𝓝 z :=
        isClosed_Icc.isOpen_compl.mem_nhds hsupp
      filter_upwards [hmem] with z' hz'
      intro θ'
      exact radW_eq_zero_of_notMem hz'
    have hzero : Work.Spaces.DzIter j (fun z _ => radW z) z θ = 0 :=
      Work.FTS.LocData.ZFBase.DzIter_eq_zero_of_eventually_zero hev j
    rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    exact div_nonneg (mul_nonneg (sq_nonneg D) (by norm_num)) (sq_nonneg _)

/-! ## Integrability of the angular majorant, for every `α > 0` -/

/-- `Γ(θ)²·sin(2θ)^{-γ(α)} ≤ 2^{-2α/3}·sin(2θ)^{17α/30-1}` on `Iθ` — the copy of
`Work.FTS.LocData.GamSq_sin_neg_gam_le` without its (unused) hypothesis `α ≤ 1`. -/
private theorem gamSq_sin_neg_gam_le_general (α : ℝ) (hα : 0 < α) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hX0 : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; positivity
  have hexp : 2 * α / 3 + -(Work.Spaces.gam α) = 17 * α / 30 - 1 := by
    simp only [Work.Spaces.gam]; ring
  have hΓ2 : Work.Spaces.Gam α θ ^ 2 = (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) := by
    rw [Work.Spaces.Gam, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2)]
    congr 1
    ring
  have hc2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [hc0, hc1]
  have hYle : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin θ * Real.cos θ :=
    mul_le_mul_of_nonneg_left hc2 hs0
  have hstat : Work.Spaces.Gam α θ ^ 2 ≤ (Real.sin θ * Real.cos θ) ^ (2 * α / 3) := by
    rw [hΓ2]
    exact Real.rpow_le_rpow (by positivity) hYle (by linarith : (0 : ℝ) ≤ 2 * α / 3)
  rcases eq_or_ne (Real.sin (2 * θ)) 0 with hXzero | hXne
  · -- degenerate case `sin(2θ) = 0`: both sides vanish
    have hY0 : Real.sin θ * Real.cos θ = 0 := by
      have hY : Real.sin θ * Real.cos θ = Real.sin (2 * θ) / 2 := by
        rw [Real.sin_two_mul]; ring
      rw [hY, hXzero]; ring
    have hGzero : Work.Spaces.Gam α θ = 0 := by
      rw [Work.Spaces.Gam]
      have h1 : Real.sin θ * Real.cos θ ^ 2 = 0 := by
        rw [show Real.sin θ * Real.cos θ ^ 2
            = (Real.sin θ * Real.cos θ) * Real.cos θ from by ring, hY0, zero_mul]
      rw [h1, Real.zero_rpow (by positivity : α / 3 ≠ 0)]
    rw [hGzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (Real.rpow_nonneg hX0 _)
  · have hXpos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hX0 (Ne.symm hXne)
    have hstep2 : (Real.sin θ * Real.cos θ) ^ (2 * α / 3)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
      have hY : Real.sin θ * Real.cos θ = Real.sin (2 * θ) / 2 := by
        rw [Real.sin_two_mul]; ring
      rw [hY, Work.FTS.LocData.angMaj_div_two_rpow _ hX0, mul_assoc, ← Real.rpow_add hXpos, hexp]
    calc Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ (Real.sin θ * Real.cos θ) ^ (2 * α / 3)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right hstat (Real.rpow_nonneg hX0 _)
      _ = 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := hstep2

/-- **The angular majorant is integrable on `Iθ` for every `α > 0`.** -/
theorem angMaj_integrable (α : ℝ) (hα : 0 < α) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.LocData.angMaj α θ) Work.Spaces.Iθ
      MeasureTheory.volume := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsin2 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  -- the pure `sin`-power majorant of the first term
  have hIntP : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) Work.Spaces.Iθ := by
    by_cases hp0 : 17 * α / 30 - 1 ≤ 0
    · exact (Work.Spaces.sin_two_rpow (17 * α / 30 - 1) (by linarith) hp0).1
    · push_neg at hp0
      refine MeasureTheory.Integrable.mono'
        (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ)) ?_) ?_ ?_
      · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      · exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const
          (17 * α / 30 - 1)).aestronglyMeasurable
      · refine MeasureTheory.ae_restrict_of_forall_mem hmeasIθ (fun θ hθ => ?_)
        have h0 := hsin2 θ hθ
        rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 _)]
        exact Real.rpow_le_one h0 (Real.sin_le_one _) (le_of_lt hp0)
  have hM1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
      Work.Spaces.Iθ := hIntP.const_mul _
  have hIntS2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by simp only [Work.Spaces.eta]; norm_num)
      (by simp only [Work.Spaces.eta]; norm_num)).1
  have hpt1 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    exact gamSq_sin_neg_gam_le_general α hα hθ
  have hpt2 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    exact Work.FTS.LocData.GamSq_sin_neg_eta_le α hα hθ
  have hmeas1 : AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  have hmeas2 : AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  have hf1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ :=
    hM1.mono' hmeas1 (by
      filter_upwards [hpt1, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2 θ h2) _))]
      exact h1)
  have hf2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    hIntS2.mono' hmeas2 (by
      filter_upwards [hpt2, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2 θ h2) _))]
      exact h1)
  have hInt0 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (1 : ℝ))
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hangMaj : (fun θ : ℝ => Work.FTS.LocData.angMaj α θ)
      = fun θ : ℝ => (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) + 1 := by
    funext θ
    rw [Work.FTS.LocData.angMaj_apply]
  rw [hangMaj]
  exact (hf1.add hf2).add hInt0

/-! ## The witness is `L₁₂`-orthogonal -/

theorem L12_witF_zero (α : ℝ) :
    Work.Construction.L12 (witF α) 0 = 0 := by
  have hdens : ∀ s : ℝ, Work.FM.L12dens Work.Spaces.K (witF α) s
      = (radW s / s) * Work.Spaces.c α := by
    intro s
    rw [Work.FM.L12dens,
      show (fun θ : ℝ => Work.Spaces.K θ * witF α s θ / s)
        = fun θ : ℝ => (radW s / s) * (Work.Spaces.Gam α θ * Work.Spaces.K θ) from by
          funext θ; rw [witF_apply]; ring,
      MeasureTheory.integral_const_mul]
    rfl
  have hL12 : Work.Construction.L12 (witF α) 0
      = Work.Spaces.c α * (∫ s in Set.Ioi (0 : ℝ), radW s / s) := by
    rw [Work.Construction.L12, Work.FM.L12]
    simp only [hdens]
    rw [MeasureTheory.integral_mul_const]
    ring
  have hfun : (fun s : ℝ => radW s / s) = fun s : ℝ => deriv Work.FTS.LocData.bumpZ s := by
    funext s
    rcases eq_or_ne s 0 with rfl | hs
    · rw [radW, zero_mul, zero_div]
      exact (Work.FTS.LocData.deriv_eq_zero_of_eq_zero_off_closed isClosed_Icc
        (fun z' hz' => Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc z' hz')
        (by norm_num)).symm
    · rw [radW, mul_div_cancel_left₀ _ hs]
  have hcomp : HasCompactSupport Work.FTS.LocData.bumpZ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun x hx => by
      by_contra h
      exact hx (Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc x h))
  have hint : (∫ s in Set.Ioi (0 : ℝ), deriv Work.FTS.LocData.bumpZ s) = 0 := by
    rw [hcomp.integral_Ioi_deriv_eq (Work.FTS.LocData.BumpZ_contDiff.of_le (by norm_num)) 0,
      Work.FTS.LocData.bumpZ_zero, neg_zero]
  rw [hL12, hfun, hint, mul_zero]

/-! ## The boundary traces of the witness -/

theorem bdryTraces_witF (α : ℝ) (hα : 0 < α) {CR CΓ : ℝ} (hCR : 0 ≤ CR) (hCΓ : 0 ≤ CΓ)
    (hB : ∀ j : ℕ, j ≤ 5 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => radW z) z θ * Work.Spaces.w z) ^ 2 ≤ CR / (1 + z) ^ 2)
    (hΓ : ∀ i : ℕ, i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ CΓ * Work.Spaces.Gam α θ) :
    Work.FTS.Nonlin.BdryTraces α 5 (witF α) := by
  intro a b hab
  have hb : b ≤ 5 := by omega
  have ha : a ≤ 5 := by omega
  have hsep : ∀ z θ : ℝ, Work.Spaces.mixed b a (witF α) z θ
      = Work.Spaces.DzIter b (fun z _ => radW z) z θ
        * (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) := by
    intro z θ
    change Work.Spaces.mixed b a (fun z θ => radW z * Work.Spaces.Gam α θ) z θ = _
    exact congrFun (congrFun
      (Work.FTS.LocDataExt.mixed_sepGam α (fun z => radW z) b a) z) θ
  constructor
  · intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
    have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθI).2
    have hAb : (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2 ≤ CΓ ^ 2 := by
      have h1 := hΓ a ha θ hθI
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs, mul_pow] at h2
      refine h2.trans ?_
      have h3 : Work.Spaces.Gam α θ ^ 2 ≤ 1 := by nlinarith
      exact mul_le_of_le_one_right (sq_nonneg CΓ) h3
    have hbd : ∀ z : ℝ, 0 < z →
        z * (Work.Spaces.mixed b a (witF α) z θ * Work.Spaces.w z) ^ 2
          ≤ CR * CΓ ^ 2 * (z / (1 + z) ^ 2) := by
      intro z hz
      have hzI : z ∈ Work.Spaces.Iz := by
        rw [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz
      have h1 := hB b hb z hzI θ
      rw [hsep z θ, mul_pow]
      calc z * ((Work.Spaces.DzIter b (fun z _ => radW z) z θ
              * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
            * (Work.Spaces.w z) ^ 2)
          = z * ((Work.Spaces.DzIter b (fun z _ => radW z) z θ * Work.Spaces.w z) ^ 2
              * (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2) := by ring
        _ ≤ z * ((CR / (1 + z) ^ 2) * CΓ ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul h1 hAb (sq_nonneg _) (by positivity)) (le_of_lt hz)
        _ = CR * CΓ ^ 2 * (z / (1 + z) ^ 2) := by ring
    constructor
    · -- `z → 0⁺`
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (f := fun z : ℝ => z * (Work.Spaces.mixed b a (witF α) z θ * Work.Spaces.w z) ^ 2)
        (g := fun _ : ℝ => (0 : ℝ)) (h := fun z : ℝ => CR * CΓ ^ 2 * z)
        tendsto_const_nhds ?_ ?_ ?_
      · have hz : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        have : Tendsto (fun z : ℝ => CR * CΓ ^ 2 * z) (𝓝[>] 0) (𝓝 (CR * CΓ ^ 2 * 0)) :=
          tendsto_const_nhds.mul hz
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact mul_nonneg (le_of_lt hz) (sq_nonneg _)
      · filter_upwards [self_mem_nhdsWithin] with z hz
        have hz0 : 0 < z := hz
        refine (hbd z hz0).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCR (sq_nonneg CΓ))
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
        have h2 : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
        calc z = z * 1 := by ring
          _ ≤ z * (1 + z) ^ 2 := mul_le_mul_of_nonneg_left h2 (le_of_lt hz0)
    · -- `z → +∞`
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (f := fun z : ℝ => z * (Work.Spaces.mixed b a (witF α) z θ * Work.Spaces.w z) ^ 2)
        (g := fun _ : ℝ => (0 : ℝ)) (h := fun z : ℝ => CR * CΓ ^ 2 / z)
        tendsto_const_nhds (tendsto_id.const_div_atTop (CR * CΓ ^ 2)) ?_ ?_
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
        exact mul_nonneg hz (sq_nonneg _)
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
        refine (hbd z (by linarith)).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCR (sq_nonneg CΓ))
        have hz0 : 0 < z := by linarith
        have hden : (0 : ℝ) < (1 + z) ^ 2 := by nlinarith
        rw [div_le_iff₀ hden]
        rw [show z⁻¹ * (1 + z) ^ 2 = (1 + z) ^ 2 / z from by rw [div_eq_mul_inv]; ring,
          le_div_iff₀ hz0]
        nlinarith
  · -- the two `θ`-limits
    intro z hz
    have hzI : z ∈ Work.Spaces.Iz := by
      rw [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz
    refine Work.FTS.LocDataExt.tendsto_sin_gam_trace α hα
      (C := |Work.Spaces.DzIter b (fun z _ => radW z) z 0| * CΓ)
      (mul_nonneg (abs_nonneg _) hCΓ) (fun θ' hθ' => ?_)
    have h1 := hΓ a ha θ' hθ'
    rw [hsep z θ', Work.FTS.LocDataExt.DzIter_z_only_apply (fun z => radW z) b z θ', abs_mul]
    calc |Work.Spaces.DzIter b (fun z _ => radW z) z 0|
            * |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ'|
        ≤ |Work.Spaces.DzIter b (fun z _ => radW z) z 0| * (CΓ * Work.Spaces.Gam α θ') :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = (|Work.Spaces.DzIter b (fun z _ => radW z) z 0| * CΓ) * Work.Spaces.Gam α θ' := by
          ring

/-! ## The separable `ℋ^k`-majorant of the witness, and its `ℋ^k`-membership -/

/-- **The `ℋ^k`-majorant of the witness** for `k ≤ 5`: the delivered separable majorant
`Work.FTS.LocDataExt.HkIntegrand_sepGam_le` with the radial input `radW_bound` and the angular
input `witGam_bound`. -/
theorem HkIntegrand_witF_le (α : ℝ) (hα : 0 < α) {k : ℕ} (hk : k ≤ 5) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (witF α) z θ
        ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
  obtain ⟨R, hR, hB⟩ := radW_bound
  obtain ⟨CΓ, hCΓ, hΓ⟩ := witGam_bound α hα
  refine ⟨(((k + 1 : ℕ) : ℝ) + (((k + 1) ^ 2 : ℕ) : ℝ) * CΓ ^ 2) * R, by positivity,
    fun z hz θ hθ => ?_⟩
  have hB' : ∀ j : ℕ, j ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => radW z) z θ * Work.Spaces.w z) ^ 2
        ≤ R / (1 + z) ^ 2 := fun j hj => hB j (le_trans hj hk)
  have hΓ2 : ∀ i : ℕ, i ≤ k → ∀ θ' ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ CΓ ^ 2 * (Work.Spaces.Gam α θ') ^ 2 := by
    intro i hi θ' hθ'
    have h1 := hΓ i (le_trans hi hk) θ' hθ'
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [sq_abs, mul_pow] at h2
  have hmain := Work.FTS.LocDataExt.HkIntegrand_sepGam_le α hα k (ρ := fun z => radW z)
    (R := R) (Rθ := CΓ ^ 2) hR (sq_nonneg CΓ) hB' hΓ2 hz hθ
  have hfun : (fun z θ => radW z * Work.Spaces.Gam α θ) = witF α := rfl
  rw [← hfun]
  refine hmain.trans_eq ?_
  push_cast
  ring

/-- The majorant `c·angMaj α θ/(1+z)²` of the witness is integrable in `θ` for every `z ∈ Iz`,
and its `z`-integral is integrable on `Iz` (no smallness restriction on `α`). -/
theorem majorant_witF_integrable (α : ℝ) (hα : 0 < α) (c : ℝ) :
    (∀ z ∈ Work.Spaces.Iz,
        IntegrableOn (fun θ => c * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
          Work.Spaces.Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        c * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) Work.Spaces.Iz := by
  have hint := angMaj_integrable α hα
  constructor
  · intro z _
    have h3 : IntegrableOn (fun θ => (c / (1 + z) ^ 2) * Work.FTS.LocData.angMaj α θ)
        Work.Spaces.Iθ := hint.const_mul (c / (1 + z) ^ 2)
    refine h3.congr_fun (fun θ _ => ?_) measurableSet_Icc
    ring
  · have hbase : IntegrableOn (fun x : ℝ => (x + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num)
    have hconst : IntegrableOn (fun x : ℝ =>
        (∫ θ in Work.Spaces.Iθ, c * Work.FTS.LocData.angMaj α θ) * (x + 1) ^ (-2 : ℝ))
        (Set.Ioi (0 : ℝ)) := hbase.const_mul _
    have heq : ∀ z ∈ Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, c * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
          = (∫ θ in Work.Spaces.Iθ, c * Work.FTS.LocData.angMaj α θ)
            * (z + 1) ^ (-2 : ℝ) := by
      intro z hz
      have hzpos : (0 : ℝ) < z + 1 := by linarith [Set.mem_Ioi.mp hz]
      rw [show (fun θ => c * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
          = fun θ => (c * Work.FTS.LocData.angMaj α θ) * (z + 1) ^ (-2 : ℝ) from by
        funext θ
        rw [show ((z + 1) ^ (-2 : ℝ)) = ((z + 1) ^ 2)⁻¹ by
          rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hzpos),
            Real.rpow_two]]
        ring]
      rw [MeasureTheory.integral_mul_const]
    have hfin : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        c * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) (Set.Ioi (0 : ℝ)) :=
      hconst.congr_fun (fun z hz => (heq z hz).symm) measurableSet_Ioi
    rw [Work.Spaces.Iz]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr hfin

/-- **The witness lies in `ℋ^k` for every `k ≤ 5`** (and every `α > 0`). -/
theorem HkMem_witF (α : ℝ) (hα : 0 < α) {k : ℕ} (hk : k ≤ 5) :
    Work.Spaces.HkMem α k (witF α) := by
  obtain ⟨K, hK, hKle⟩ := HkIntegrand_witF_le α hα hk
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k (witF α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α k (witF α) (smoothQuad_witF α)
  refine Work.FTS.LocData.HkMem_of_majorant (f := witF α)
    (M := fun z θ => K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) α k hcont ?_ ?_ ?_
  · exact (majorant_witF_integrable α hα K).1
  · exact (majorant_witF_integrable α hα K).2
  · intro z hz θ hθ
    exact hKle z hz θ hθ

/-! ## Strict positivity of the `ℋ⁴`-functional of the witness -/

theorem witF_HkSq_pos (α : ℝ) (hα : 0 < α)
    (hmem : Work.Spaces.HkMem α 4 (witF α)) :
    0 < Work.Spaces.HkSq α 4 (witF α) := by
  obtain ⟨a, b, ha, hab, hrad⟩ := exists_radW_ne_zero_interval
  -- the `i = 0` term of the integrand
  set Sθ : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.DzIter 0 (witF α) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 with hSθdef
  have hslot_int : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Sθ z θ) Work.Spaces.Iθ := by
    intro z hz
    refine MeasureTheory.Integrable.mono' (hmem.1 z hz) ?_ ?_
    · apply Measurable.aestronglyMeasurable
      rw [hSθdef]
      simp only [Work.Spaces.DzIter_zero, witF_apply, Work.Spaces.Gam, Work.Spaces.w]
      fun_prop
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hSθdef]; exact sq_nonneg _)]
      rw [hSθdef]
      exact Work.Spaces.sq_le_HkIntegrand_z α 4 (witF α) z θ 0 (by norm_num)
  have hslot_pos : ∀ z ∈ Set.Ioo a b, 0 < ∫ θ in Work.Spaces.Iθ, Sθ z θ := by
    intro z hz
    have hz0 : 0 < z := lt_trans ha hz.1
    have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz0
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun θ => by rw [hSθdef]; exact sq_nonneg _)
      (hslot_int z hzI)]
    have hsub : Set.Ioo (Real.pi / 8) (3 * Real.pi / 8) ⊆
        Function.support (fun θ => Sθ z θ) ∩ Work.Spaces.Iθ := by
      intro θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ :=
        ⟨le_of_lt (by linarith [hθ.1, Real.pi_pos]),
          le_of_lt (by linarith [hθ.2, Real.pi_pos])⟩
      have hΓ : 0 < Work.Spaces.Gam α θ := by
        have hsin : 0 < Real.sin θ :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
            (by linarith [hθ.2, Real.pi_pos])
        have hcos : 0 < Real.cos θ :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
            by linarith [hθ.2, Real.pi_pos]⟩
        rw [Work.Spaces.Gam]
        exact Real.rpow_pos_of_pos (mul_pos hsin (pow_pos hcos 2)) _
      have hs2 : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
          (by linarith [hθ.2, Real.pi_pos])
      have hw : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      refine ⟨?_, hθI⟩
      rw [Function.mem_support, hSθdef]
      refine pow_ne_zero 2 (mul_ne_zero ?_ ?_)
      · rw [Work.Spaces.DzIter_zero, witF_apply]
        exact mul_ne_zero (hrad z hz) (ne_of_gt hΓ)
      · rw [div_ne_zero_iff]
        exact ⟨ne_of_gt hw, ne_of_gt (Real.rpow_pos_of_pos hs2 _)⟩
    refine lt_of_lt_of_le ?_ (MeasureTheory.measure_mono hsub)
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])
  have hSpos : ∀ z ∈ Set.Ioo a b,
      0 < ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (witF α) z θ := by
    intro z hz
    have hz0 : 0 < z := lt_trans ha hz.1
    have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz0
    refine lt_of_lt_of_le (hslot_pos z hz) ?_
    refine MeasureTheory.integral_mono_ae (hslot_int z hzI) (hmem.1 z hzI) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [hSθdef]
    exact Work.Spaces.sq_le_HkIntegrand_z α 4 (witF α) z θ 0 (by norm_num)
  have houter : 0 < ∫ z in Set.Ioo a b,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (witF α) z θ) := by
    have hintab : IntegrableOn (fun z =>
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (witF α) z θ)
        (Set.Ioo a b) := hmem.2.mono_set (fun z hz => by
          rw [Work.Spaces.Iz, Set.mem_Ici]; linarith [hz.1])
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ =>
          Work.Spaces.HkIntegrand_nonneg α 4 (witF α) z θ) hintab]
    have hsub : Set.Ioo a b ⊆
        Function.support (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (witF α) z θ) :=
      fun z hz => (hSpos z hz).ne'
    refine lt_of_lt_of_le ?_ (MeasureTheory.measure_mono (fun z hz => ⟨hsub hz, hz⟩))
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
  refine lt_of_lt_of_le houter ?_
  refine MeasureTheory.setIntegral_mono_set hmem.2 ?_ ?_
  · filter_upwards with z
    exact MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 (witF α) z θ
  · filter_upwards with z hz
    rw [Work.Spaces.Iz, Set.mem_Ici]; linarith [hz.1]

/-! ## The witness lies in `CoerAdm` -/

theorem CoerAdm_witF (α : ℝ) (hα : 0 < α) : Work.FTS.Nonlin.CoerAdm α (witF α) := by
  obtain ⟨R, hR, hB⟩ := radW_bound
  obtain ⟨CΓ, hCΓ, hΓ⟩ := witGam_bound α hα
  exact ⟨⟨smoothQuad_witF α, HkMem_witF α hα (by norm_num),
      bdryTraces_witF α hα hR hCΓ hB hΓ⟩,
    vanishTheta_witF α hα, axis_witF α, L12_witF_zero α⟩

theorem exists_coerAdm_pos (α : ℝ) (hα : 0 < α) :
    ∃ f : ℝ → ℝ → ℝ,
      Work.FTS.Nonlin.CoerAdm α f ∧ 0 < Work.Spaces.HkSq α 4 f :=
  ⟨witF α, CoerAdm_witF α hα, witF_HkSq_pos α hα (HkMem_witF α hα (by norm_num))⟩

end Work.FTS.CoercivityFix.Assembly
