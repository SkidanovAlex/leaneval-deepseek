import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.HardyTheta
import Submission.Work.Spaces.Linf_H2_of_decay
import Submission.Work.Spaces.HkSq_mixed_le
import Submission.Work.Spaces.HkMem_mixed_le
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.H2.MinLeAvg
import Submission.Work.FTS.H2.OscSqLe
import Submission.Work.FTS.H2.HkSqSwap

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Elementary a.e. facts -/

/-- Almost everywhere on `Iθ = [0,π/2]`, `sin (2σ) > 0`. -/
lemma ae_sin_two_pos :
    ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), 0 < Real.sin (2 * σ) := by
  have h : ∀ᵐ σ ∂(MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))),
      0 < Real.sin (2 * σ) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => ?_)
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  have hset : MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0:ℝ)) (b := Real.pi/2))
  rwa [hset] at h

/-- Strong measurability with respect to `volume.restrict Iz` from continuity on the open
half-line `(0,∞)` (which is a.e. equal to `Iz`). -/
lemma aestronglyMeasurable_restrict_Iz {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi (0:ℝ))) :
    MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h1 : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    hg.aestronglyMeasurable measurableSet_Ioi
  have h2 : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) := by
    rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ)))).symm
  rwa [h2]

/-- `1 ≤ x ^ (-p)` for `0 < x ≤ 1` and `p ≥ 0`. -/
lemma one_le_rpow_neg {x p : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hp : 0 ≤ p) :
    1 ≤ x ^ (-p) := by
  rw [Real.rpow_neg (le_of_lt hx0) p]
  have h1 : x ^ p ≤ 1 := Real.rpow_le_one (le_of_lt hx0) hx1 hp
  have h2 : 0 < x ^ p := Real.rpow_pos_of_pos hx0 p
  exact (one_le_inv₀ h2).mpr h1

/-- `(a / x ^ (c/2)) ^ 2 = a ^ 2 * x ^ (-c)` for `x ≥ 0` and `c ≠ 0`. -/
lemma div_rpow_sq (a x c : ℝ) (hx : 0 ≤ x) (hc : c ≠ 0) :
    (a / x ^ (c / 2)) ^ 2 = a ^ 2 * x ^ (-c) := by
  have h2 : x ^ (-c) = ((x ^ (c/2))⁻¹) ^ 2 := by
    rw [← Real.rpow_neg hx (c / 2)]
    exact (Work.Spaces.bt_rpow_sq c x hx hc).symm
  rw [h2, div_eq_mul_inv, mul_pow]

/-! ## The angular-weight identities -/

/-- `mixed b 1 f z θ = sin(2θ) ∂_θ (D_z^b f)` on the closed quadrant. -/
lemma mixed_one_eq_sin_mul_pth {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (b : ℕ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.mixed b 1 f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ := by
  have hy : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθ
  have hc : Work.Spaces.DthIter 1 (Work.Spaces.DzIter b f) z θ
      = Work.Spaces.DzIter b (Work.Spaces.DthIter 1 f) z θ := by
    have h := Work.Spaces.DthIter_DzIter_comm_eqOn hsm b 1 hy
    simpa [Function.uncurry] using h
  show Work.Spaces.DzIter b (Work.Spaces.DthIter 1 f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ
  rw [← hc]
  rfl

/-- The pointwise identification of the angular Hardy weight:
`(∂_θ D_z^b f)² sin(2θ)^{2-γ} = (D_z^b D_θ f)² sin(2θ)^{-γ}` on the closed quadrant. -/
lemma pth_sq_sin_eq {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (b : ℕ) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.mixed b 1 f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.bt_sin_nonneg hθ
  have hne : (2:ℝ) + (-(Work.Spaces.gam α)) ≠ 0 := by
    have h : Work.Spaces.gam α < 2 := by rw [Work.Spaces.gam]; linarith
    intro hh; linarith
  have hkey : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [show (2:ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
        Real.rpow_add' hs hne, Real.rpow_two]
  rw [mixed_one_eq_sin_mul_pth hsm b hz hθ, hkey]
  ring

/-! ## Continuity and differentiability of the angular slices -/

lemma contDiffOn_slice_DzIter {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (b : ℕ)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContDiffOn ℝ ⊤ (fun σ : ℝ => Work.Spaces.DzIter b f z σ) (Set.Ioo (-1) (Real.pi/2 + 1)) := by
  have hz1 : (-1:ℝ) < z := by rw [Work.Spaces.Iz, Set.mem_Ici] at hz; linarith
  have hsm' : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter b f) :=
    Work.Spaces.SmoothNbhd.DzIter hsm b
  have hp : ContDiffOn ℝ ⊤ (fun σ : ℝ => (z, σ)) (Set.Ioo (-1) (Real.pi/2 + 1)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have h := hsm'.comp hp (fun σ hσ => ⟨hz1, hσ⟩)
  simpa [Function.comp_def, Function.uncurry] using h

lemma hasDerivAt_slice_DzIter {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (b : ℕ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    HasDerivAt (fun σ => Work.Spaces.DzIter b f z σ)
      (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) θ := by
  have hcd := contDiffOn_slice_DzIter hsm b hz
  have hd : DifferentiableOn ℝ (fun σ => Work.Spaces.DzIter b f z σ)
      (Set.Ioo (-1) (Real.pi/2 + 1)) := hcd.differentiableOn (by simp)
  have hmem : θ ∈ Set.Ioo (-1:ℝ) (Real.pi/2 + 1) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have := hd.hasDerivAt (isOpen_Ioo.mem_nhds hmem)
  simpa [Work.Spaces.pth] using this

lemma continuousOn_pth_slice {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (b : ℕ)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) Work.Spaces.Iθ := by
  have hcd := contDiffOn_slice_DzIter hsm b hz
  have hcont := hcd.continuousOn_deriv_of_isOpen isOpen_Ioo le_top
  have hsub : Work.Spaces.Iθ ⊆ Set.Ioo (-1:ℝ) (Real.pi/2 + 1) :=
    fun σ hσ => ⟨by linarith [hσ.1], by linarith [hσ.2, Real.pi_pos]⟩
  simpa [Work.Spaces.pth] using hcont.mono hsub

/-! ## Pointwise domination of single terms of the `ℋ⁴`-integrand -/

/-- On the open quadrant, `(D_z^j f)² w² ≤ HkIntegrand α 4 f` for `j ≤ 4`. -/
lemma dzIter_sq_w_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hsin : 0 < Real.sin (2 * θ)) (j : ℕ) (hj : j ≤ 4) :
    (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    one_le_rpow_neg hsin hs1 Work.Spaces.eta_nonneg
  have hrew : (Work.Spaces.DzIter j f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * θ)) Work.Spaces.eta
      (le_of_lt hsin) (ne_of_gt Work.Spaces.eta_pos)]
    ring
  have hzle := Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ j hj
  rw [hrew] at hzle
  calc (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h1
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ := hzle

/-- `(w z)² ≤ (Wt α z θ)²` on the open quadrant. -/
lemma w_sq_le_Wt_sq (α : ℝ) (hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hsin : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.w z) ^ 2 ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  have hs := Work.Spaces.bt_sin_nonneg hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    one_le_rpow_neg hsin hs1 (le_of_lt (Work.Spaces.gam_pos hα))
  rw [Work.Spaces.bt_Wt_sq α z θ hα hθ]
  calc (Work.Spaces.w z) ^ 2 = (Work.Spaces.w z) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)



/-! ## Continuity of the `D_z`-slice of the weighted integrand -/

lemma continuousOn_dzIter_sq_slice (f : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd f)
    (j : ℕ) {σ : ℝ} (hσ : σ ∈ Work.Spaces.Iθ) :
    ContinuousOn (fun s : ℝ => (Work.Spaces.DzIter j f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      (Set.Ioi (0:ℝ)) := by
  have h1 : ContinuousOn (fun s : ℝ => Work.Spaces.DzIter j f s σ) (Set.Ioi (-1:ℝ)) :=
    (Work.Spaces.hardyZ_contDiffOn_slice (Work.Spaces.DzIter j f)
      (Work.Spaces.SmoothNbhd.DzIter hsm j) hσ).continuousOn
  have h2 : ContinuousOn (fun s : ℝ => Work.Spaces.w s) (Set.Ioi (0:ℝ)) := by
    unfold Work.Spaces.w
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) ?_
    intro s hs
    simp only [Set.mem_Ioi] at hs
    exact pow_ne_zero 2 (ne_of_gt hs)
  refine ((h1.mono ?_).pow 2).mul (h2.pow 2)
  intro s hs
  simp only [Set.mem_Ioi] at hs ⊢
  linarith

/-! ## The two `L²` bounds at fixed `z` -/

/-- The angular average of `|D_z^b f(z,·)|²` is controlled by `|f|²_{ℋ⁴}`. -/
lemma avg_le_HkSq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd f) (hdec : Work.Spaces.DecayAll 4 f)
    (hmem : Work.Spaces.HkMem α 4 f) (b : ℕ) (hb : b ≤ 2) :
    ∀ z ∈ Work.Spaces.Iz,
      ∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z σ) ^ 2 ≤ Work.Spaces.HkSq α 4 f := by
  obtain ⟨hswap, hΨint, hsliceae⟩ := HkSqSwap α f hsm hmem
  intro z hz
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hcontσ : ContinuousOn (fun σ : ℝ => Work.Spaces.DzIter b f z σ) Work.Spaces.Iθ :=
    (contDiffOn_slice_DzIter hsm b hz).continuousOn.mono
      (fun σ hσ => ⟨by linarith [hσ.1], by linarith [hσ.2, Real.pi_pos]⟩)
  have hLHS : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.DzIter b f z σ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hcontσ.pow 2).integrableOn_compact isCompact_Icc
  have hpoint : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.DzIter b f z σ) ^ 2
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
    filter_upwards [hsliceae, ae_sin_two_pos, MeasureTheory.ae_restrict_mem hIθm]
      with σ hslice hσpos hσmem
    have hGint : MeasureTheory.IntegrableOn
        (fun s : ℝ => (Work.Spaces.Dz (Work.Spaces.DzIter b f) s σ) ^ 2
          * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
      refine MeasureTheory.Integrable.mono' hslice ?_ ?_
      · refine aestronglyMeasurable_restrict_Iz ?_
        rw [show Work.Spaces.Dz (Work.Spaces.DzIter b f) = Work.Spaces.DzIter (b + 1) f from rfl]
        exact continuousOn_dzIter_sq_slice f hsm (b + 1) hσmem
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s _ => ?_)
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
          show Work.Spaces.Dz (Work.Spaces.DzIter b f) = Work.Spaces.DzIter (b + 1) f from rfl]
        exact dzIter_sq_w_le_HkIntegrand α f hσpos (b + 1) (by omega)
    have hHZ := Work.Spaces.HardyZ (Work.Spaces.DzIter b f) σ
      (Work.Spaces.SmoothNbhd.DzIter hsm b) hσmem
      (hdec.2 0 b (by omega) σ hσmem) hGint z hz
    refine le_trans hHZ ?_
    refine MeasureTheory.integral_mono_ae hGint hslice ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with s _
    rw [show Work.Spaces.Dz (Work.Spaces.DzIter b f) = Work.Spaces.DzIter (b + 1) f from rfl]
    exact dzIter_sq_w_le_HkIntegrand α f hσpos (b + 1) (by omega)
  have hmain := MeasureTheory.integral_mono_ae hLHS hΨint hpoint
  calc ∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z σ) ^ 2
      ≤ ∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 4 f s σ := hmain
    _ = Work.Spaces.HkSq α 4 f := hswap

/-- At almost every `σ`, the weighted square of `D_z^b D_θ f` is controlled by the
angular integral of the `ℋ⁴`-integrand. -/
lemma mixed_sq_sin_le_avg (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd f) (hdec : Work.Spaces.DecayAll 4 f)
    (hmem : Work.Spaces.HkMem α 4 f) (b : ℕ) (hb : b ≤ 2)
    {z σ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hσ : σ ∈ Work.Spaces.Iθ)
    (hslice : MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ)
      Work.Spaces.Iz) (hσpos : 0 < Real.sin (2 * σ)) :
    (Work.Spaces.mixed b 1 f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
  have hg_sm : Work.Spaces.SmoothNbhd (Work.Spaces.mixed b 1 f) :=
    Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.DthIter hsm 1) b
  have hg_dec : Filter.Tendsto (fun s => Work.Spaces.mixed b 1 f s σ) Filter.atTop (nhds 0) :=
    hdec.2 1 b (by omega) σ hσ
  have hDzg : MeasureTheory.IntegrableOn
      (fun s : ℝ => (Work.Spaces.Dz (Work.Spaces.mixed b 1 f) s σ) ^ 2
        * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hslice ?_ ?_
    · refine aestronglyMeasurable_restrict_Iz ?_
      exact continuousOn_dzIter_sq_slice (Work.Spaces.mixed b 1 f) hg_sm 1 hσ
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s _ => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      calc (Work.Spaces.Dz (Work.Spaces.mixed b 1 f) s σ) ^ 2 * (Work.Spaces.w s) ^ 2
          ≤ (Work.Spaces.Dz (Work.Spaces.mixed b 1 f) s σ) ^ 2
              * (Work.Spaces.Wt α s σ) ^ 2 :=
            mul_le_mul_of_nonneg_left (w_sq_le_Wt_sq α hα hσ hσpos) (sq_nonneg _)
        _ = (Work.Spaces.mixed (b + 1) 1 f s σ * Work.Spaces.Wt α s σ) ^ 2 := by
            rw [show Work.Spaces.Dz (Work.Spaces.mixed b 1 f) = Work.Spaces.mixed (b + 1) 1 f
              from rfl, mul_pow]
        _ ≤ Work.Spaces.HkIntegrand α 4 f s σ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s σ 1 (b + 1) le_rfl (by omega)
  have hHZ := Work.Spaces.HardyZ (Work.Spaces.mixed b 1 f) σ hg_sm hσ hg_dec hDzg z hz
  have hsnn : 0 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
    Real.rpow_nonneg (le_of_lt hσpos) _
  have hstep : (Work.Spaces.mixed b 1 f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      ≤ (∫ s in Work.Spaces.Iz, (Work.Spaces.Dz (Work.Spaces.mixed b 1 f) s σ) ^ 2
            * (Work.Spaces.w s) ^ 2) * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
    mul_le_mul_of_nonneg_right hHZ hsnn
  refine le_trans hstep ?_
  rw [← MeasureTheory.integral_mul_const]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hslice ?_
  · exact Filter.Eventually.of_forall (fun s =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsnn)
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s _ => ?_)
    show (Work.Spaces.Dz (Work.Spaces.mixed b 1 f) s σ) ^ 2 * (Work.Spaces.w s) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) ≤ Work.Spaces.HkIntegrand α 4 f s σ
    rw [show (Work.Spaces.Dz (Work.Spaces.mixed b 1 f) s σ) ^ 2 * (Work.Spaces.w s) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        = (Work.Spaces.Dz (Work.Spaces.mixed b 1 f) s σ) ^ 2
          * (Work.Spaces.Wt α s σ) ^ 2 by
      rw [Work.Spaces.bt_Wt_sq α s σ hα hσ]; ring]
    rw [show Work.Spaces.Dz (Work.Spaces.mixed b 1 f) = Work.Spaces.mixed (b + 1) 1 f from rfl,
      ← mul_pow]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s σ 1 (b + 1) le_rfl (by omega)



/-- The angular Hardy integral of `∂_θ D_z^b f` at fixed `z` is controlled by `|f|²_{ℋ⁴}`. -/
lemma ang_le_HkSq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd f) (hdec : Work.Spaces.DecayAll 4 f)
    (hmem : Work.Spaces.HkMem α 4 f) (b : ℕ) (hb : b ≤ 2) :
    ∀ z ∈ Work.Spaces.Iz,
      ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) ≤ Work.Spaces.HkSq α 4 f := by
  obtain ⟨hswap, hΨint, hsliceae⟩ := HkSqSwap α f hsm hmem
  intro z hz
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hγ2 : 0 < 2 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hcont0 : ContinuousOn
      (fun σ : ℝ => (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
      (fun x => Or.inr hγ2.le)).continuousOn
  have hIntA : MeasureTheory.Integrable
      (fun σ : ℝ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (ContinuousOn.mul ((continuousOn_pth_slice hsm b hz).pow 2) hcont0).integrableOn_compact
      isCompact_Icc
  have hpoint : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
    filter_upwards [hsliceae, ae_sin_two_pos, MeasureTheory.ae_restrict_mem hIθm]
      with σ hslice hσpos hσmem
    rw [pth_sq_sin_eq hsm α hα hα1 b hz hσmem]
    exact mixed_sq_sin_le_avg α hα hα1 f hsm hdec hmem b hb hz hσmem hslice hσpos
  have hmain := MeasureTheory.integral_mono_ae hIntA hΨint hpoint
  calc ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      ≤ ∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 4 f s σ := hmain
    _ = Work.Spaces.HkSq α 4 f := hswap

/-- Pointwise bound on the `D_z`-derivatives of order at most `2`, **without** any vanishing
hypothesis at the angular boundary. -/
lemma dzIter_sq_le_HkSq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd f) (hdec : Work.Spaces.DecayAll 4 f)
    (hmem : Work.Spaces.HkMem α 4 f) (b : ℕ) (hb : b ≤ 2) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ (202 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by
  intro z hz θ hθ
  have hAvg := avg_le_HkSq α hα hα1 f hsm hdec hmem b hb z hz
  have hAng := ang_le_HkSq α hα hα1 f hsm hdec hmem b hb z hz
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγ2 : 0 < 2 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hcontσ : ContinuousOn (fun σ : ℝ => (Work.Spaces.DzIter b f z σ) ^ 2)
      Work.Spaces.Iθ :=
    ((contDiffOn_slice_DzIter hsm b hz).continuousOn.mono
      (fun σ hσ => ⟨by linarith [hσ.1], by linarith [hσ.2, Real.pi_pos]⟩)).pow 2
  obtain ⟨θ₀, hθ₀mem, hθ₀le⟩ := MinLeAvg hcontσ
  have hIntOsc : MeasureTheory.IntegrableOn
      (fun σ : ℝ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    (ContinuousOn.mul ((continuousOn_pth_slice hsm b hz).pow 2)
      (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
        (fun x => Or.inr hγ2.le)).continuousOn)).integrableOn_compact isCompact_Icc
  have hsub : Set.uIcc θ θ₀ ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans hθ.1 h1, le_trans h2 hθ₀mem.2⟩
    · exact ⟨le_trans hθ₀mem.1 h1, le_trans h2 hθ.2⟩
  have hosc := OscSqLe α hα hα1 (fun σ => Work.Spaces.DzIter b f z σ) hθ hθ₀mem
    (fun x hx => hasDerivAt_slice_DzIter hsm b hz (hsub hx))
    ((continuousOn_pth_slice hsm b hz).mono hsub) hIntOsc
  have h1 : (Work.Spaces.DzIter b f z θ) ^ 2
      ≤ 2 * (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀) ^ 2
        + 2 * (Work.Spaces.DzIter b f z θ₀) ^ 2 := by
    nlinarith [sq_nonneg (Work.Spaces.DzIter b f z θ - 2 * Work.Spaces.DzIter b f z θ₀)]
  have h2 := mul_le_mul_of_nonneg_left hosc (by norm_num : (0:ℝ) ≤ 2)
  have h3 := mul_le_mul_of_nonneg_left hθ₀le (by norm_num : (0:ℝ) ≤ 2)
  have hcoef : 2 * (100 / (Work.Spaces.gam α - 1)) + 2 * (2 / Real.pi)
      ≤ 202 / (Work.Spaces.gam α - 1) := by
    have hγ1le : Work.Spaces.gam α - 1 ≤ 1 := by rw [Work.Spaces.gam_sub_one]; linarith
    have h3' : (4:ℝ) / Real.pi ≤ 2 / (Work.Spaces.gam α - 1) := by
      rw [div_le_div_iff₀ Real.pi_pos hγ1]
      nlinarith [Real.pi_gt_three, hγ1le, hγ1]
    have h4 : 2 * (2 / Real.pi) = 4 / Real.pi := by ring
    rw [h4, show 2 * (100 / (Work.Spaces.gam α - 1)) = 200 / (Work.Spaces.gam α - 1) by ring]
    linarith [h3', show 200 / (Work.Spaces.gam α - 1) + 2 / (Work.Spaces.gam α - 1)
      = 202 / (Work.Spaces.gam α - 1) by ring]
  calc (Work.Spaces.DzIter b f z θ) ^ 2
      ≤ 2 * (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀) ^ 2
        + 2 * (Work.Spaces.DzIter b f z θ₀) ^ 2 := h1
    _ ≤ 2 * ((100 / (Work.Spaces.gam α - 1)) * ∫ σ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
        + 2 * ((2 / Real.pi) * ∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z σ) ^ 2) :=
        add_le_add h2 h3
    _ = (2 * (100 / (Work.Spaces.gam α - 1))) * (∫ σ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
        + (2 * (2 / Real.pi)) * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z σ) ^ 2) := by
        ring
    _ ≤ (2 * (100 / (Work.Spaces.gam α - 1))) * Work.Spaces.HkSq α 4 f
        + (2 * (2 / Real.pi)) * Work.Spaces.HkSq α 4 f := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hAng
            (mul_nonneg (by norm_num) (div_nonneg (by norm_num) (le_of_lt hγ1)))
        · exact mul_le_mul_of_nonneg_left hAvg
            (mul_nonneg (by norm_num) (div_nonneg (by norm_num) (le_of_lt Real.pi_pos)))
    _ = (2 * (100 / (Work.Spaces.gam α - 1)) + 2 * (2 / Real.pi)) * Work.Spaces.HkSq α 4 f := by
        ring
    _ ≤ (202 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f :=
        mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α 4 f)



/-- The `a ≥ 1` case: `D_z^b D_θ^a f` vanishes on the angular boundary, and the paper's
`Linf_H2` applies verbatim. -/
lemma supAbs_mixed_vanish_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd f) (hdec : Work.Spaces.DecayAll 4 f)
    (hmem : Work.Spaces.HkMem α 4 f) (b a : ℕ) (ha : 1 ≤ a) (hab : a + b ≤ 2) :
    Work.Spaces.supAbs (Work.Spaces.mixed b a f)
      ≤ 202 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := by
  have hvt : Work.Spaces.VanishTheta (Work.Spaces.mixed b a f) := by
    have h1 : Work.Spaces.VanishTheta (Work.Spaces.DthIter a f) := by
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      constructor
      · intro z
        show Real.sin (2 * 0) * Work.Spaces.pth (Work.Spaces.DthIter a' f) z 0 = 0
        simp
      · intro z
        show Real.sin (2 * (Real.pi / 2))
          * Work.Spaces.pth (Work.Spaces.DthIter a' f) z (Real.pi / 2) = 0
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, zero_mul]
    obtain ⟨h2, h3⟩ := Work.Spaces.bt_DzIter_vanish h1 b
    exact ⟨h2, h3⟩
  have hsm' : Work.Spaces.SmoothNbhd (Work.Spaces.mixed b a f) :=
    Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.DthIter hsm a) b
  have hmem' : Work.Spaces.HkMem α 2 (Work.Spaces.mixed b a f) :=
    Work.Spaces.HkMem_mixed_le α hα hα1 f hsm hmem b a hab
  have hdec' : ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z => Work.Spaces.mixed b a f z θ) Filter.atTop (nhds 0) :=
    fun θ hθ => hdec.2 a b (by omega) θ hθ
  have h1 := Work.Spaces.Linf_H2_of_decay α hα hα1 (Work.Spaces.mixed b a f) hsm' hvt hdec' hmem'
  have h2 : Work.Spaces.HkNorm α 2 (Work.Spaces.mixed b a f) ≤ Work.Spaces.HkNorm α 4 f :=
    Real.sqrt_le_sqrt (Work.Spaces.HkSq_mixed_le α hα hα1 f hsm hmem b a hab)
  calc Work.Spaces.supAbs (Work.Spaces.mixed b a f)
      ≤ 100 / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 2 (Work.Spaces.mixed b a f) := h1
    _ ≤ 100 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f :=
        mul_le_mul_of_nonneg_left h2 (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
    _ ≤ 202 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _))
          (Work.Spaces.HkNorm_nonneg α 4 f)

/-- **Elgindi's Corollary `SecondDerivativesBounded` without the angular vanishing hypothesis.**
Every `D_z`/`D_θ`-derivative of order at most `2` of a function of `ℋ⁴` is bounded by
`C/√(γ-1)·|f|_{ℋ⁴}`. -/
theorem SupMixedNB : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ), 0 < α → α ≤ 1 →
    a + b ≤ 2 → Work.Spaces.SmoothNbhd f → Work.Spaces.DecayAll 4 f → Work.Spaces.HkMem α 4 f →
    Work.Spaces.supAbs (Work.Spaces.mixed b a f)
      ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := by
  refine ⟨202, by norm_num, ?_⟩
  intro α f b a hα hα1 hab hsm hdec hmem
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hb : b ≤ 2 := by omega
    have hpoint := dzIter_sq_le_HkSq α hα hα1 f hsm hdec hmem b hb
    have hsup : Work.Spaces.supAbs (Work.Spaces.mixed b 0 f)
        ≤ Real.sqrt ((202 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f) := by
      refine Work.Spaces.supAbs_le (fun z hz θ hθ => ?_)
      exact Real.abs_le_sqrt (hpoint z hz θ hθ)
    have hAle : (202 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f
        ≤ (202 / Real.sqrt (Work.Spaces.gam α - 1)) ^ 2 * Work.Spaces.HkSq α 4 f := by
      rw [div_pow, Real.sq_sqrt hγ1.le]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by norm_num : (202:ℝ) ≤ 202 ^ 2) hγ1.le)
        (Work.Spaces.HkSq_nonneg α 4 f)
    calc Work.Spaces.supAbs (Work.Spaces.mixed b 0 f)
        ≤ Real.sqrt ((202 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f) := hsup
      _ ≤ Real.sqrt ((202 / Real.sqrt (Work.Spaces.gam α - 1)) ^ 2 * Work.Spaces.HkSq α 4 f) :=
          Real.sqrt_le_sqrt hAle
      _ = (202 / Real.sqrt (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 4 f := by
          rw [Real.sqrt_mul (sq_nonneg _),
            Real.sqrt_sq (div_nonneg (by norm_num) (Real.sqrt_nonneg _))]
          rfl
  · exact supAbs_mixed_vanish_le α hα hα1 f hsm hdec hmem b a ha hab

end Work.FTS.H2
