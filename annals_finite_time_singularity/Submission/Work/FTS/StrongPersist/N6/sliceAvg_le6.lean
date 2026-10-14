import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.StrongPersist.N6.Slots
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.H2.T1Q.PwBdQ
-- ===== merged: Submission.Work.FTS.OpenPkg.ProdOpen.PwOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.ProdOpen

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0)

/-- `sin (2σ) > 0` for `σ` in the open angular interval. -/
theorem sin_two_pos {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * σ) :=
  Real.sin_pos_of_mem_Ioo ⟨by linarith [hσ.1], by linarith [hσ.2, Real.pi_pos]⟩

/-! ## The shift identity `D_θ(D_z^bD_θ^a f) = sin(2·) ∂_θ(D_z^bD_θ^a f)` -/

theorem mixed_succ_eq_sin_pth {f : ℝ → ℝ → ℝ} (hF : SmoothOpen f) (b a : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.mixed b (a + 1) f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed b a f) z θ := by
  have hQ : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h1 : Work.Spaces.DthIter (a + 1) f = Work.Spaces.Dth (Work.Spaces.DthIter a f) :=
    Work.Spaces.DthIter_succ a f
  have h2 : Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter a f)) z θ
      = Real.sin (2 * θ)
        * Work.Spaces.DzIter b (Work.Spaces.pth (Work.Spaces.DthIter a f)) z θ := by
    have hfun : Work.Spaces.Dth (Work.Spaces.DthIter a f)
        = fun z' θ' => Real.sin (2 * θ') * Work.Spaces.pth (Work.Spaces.DthIter a f) z' θ' :=
      rfl
    rw [hfun]
    exact Work.FTS.TransportS.SupDzAux.sda_DzIter_const_mul_th (fun θ' => Real.sin (2 * θ'))
      (Work.Spaces.pth (Work.Spaces.DthIter a f)) b z θ
  have h3 : Work.Spaces.DzIter b (Work.Spaces.pth (Work.Spaces.DthIter a f)) z θ
      = Work.Spaces.pth (Work.Spaces.mixed b a f) z θ := by
    simpa only [Function.uncurry, Work.Spaces.mixed] using
      (Work.Blocks.pth_DzIter_eqOn_Q0 (hF.DthIter a) b hQ).symm
  show Work.Spaces.DzIter b (Work.Spaces.DthIter (a + 1) f) z θ = _
  rw [h1, h2, h3]

/-! ## The weight identity for the angular derivative -/

theorem deriv_mixed_weight (α : ℝ) {f : ℝ → ℝ → ℝ} (hF : SmoothOpen f) (b a : ℕ) {z σ : ℝ}
    (hz : 0 < z) (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (deriv (fun σ' : ℝ => Work.Spaces.mixed b a f z σ') σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
  have hsin : 0 < Real.sin (2 * σ) := sin_two_pos hσ
  have hd : deriv (fun σ' : ℝ => Work.Spaces.mixed b a f z σ') σ
      = Work.Spaces.pth (Work.Spaces.mixed b a f) z σ := rfl
  have hshift : Work.Spaces.mixed b (a + 1) f z σ
      = Real.sin (2 * σ) * Work.Spaces.pth (Work.Spaces.mixed b a f) z σ :=
    mixed_succ_eq_sin_pth hF b a hz hσ
  have hsp : Real.sin (2 * σ) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * σ)) ^ 2 * Real.sin (2 * σ) ^ (-(Work.Spaces.gam α)) := by
    rw [show (2 : ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
      Real.rpow_add hsin, Real.rpow_two]
  rw [hd, hshift, mul_pow, hsp]
  ring

/-! ## Integrability of the `θ`-slices of the mixed slots -/

/-- The `θ`-slice of a mixed slot with the `sin(2·)^{-γ}` weight is integrable. -/
theorem integrableOn_slice_neg_gam {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (hF : SmoothOpen f)
    (hmem : HkMem α 4 f) (b a : ℕ) (ha : 1 ≤ a) (hab : a + b ≤ 4) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun σ => (Work.Spaces.mixed b a f z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) Iθ := by
  have hwpos : 0 < w z := w_pos_of_pos hz
  have hmeas : AEStronglyMeasurable (fun σ : ℝ => (Work.Spaces.mixed b a f z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) (volume.restrict Iθ) := by
    refine Work.H2.T1Q.aesm_Iθ_of_continuousOn ?_
    have hbase : Continuous fun σ : ℝ => Real.sin (2 * σ) := by fun_prop
    refine ContinuousOn.mul (((hF.mixed b a).curry_θ hz).continuousOn.pow 2)
      (hbase.continuousOn.rpow_const ?_)
    intro σ hσ
    exact Or.inl (ne_of_gt (sin_two_pos hσ))
  refine Integrable.mono' ((hmem.1 z hz.le).const_mul ((w z) ^ 2)⁻¹) hmeas ?_
  filter_upwards [ae_mem_Ioo_Iθ] with σ hσ
  have hsin : 0 < Real.sin (2 * σ) := Real.sin_pos_of_mem_Ioo
    ⟨by linarith [hσ.1], by linarith [hσ.2, Real.pi_pos]⟩
  have hnn : 0 ≤ (Work.Spaces.mixed b a f z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
  rw [Real.norm_of_nonneg hnn]
  have hid : (Work.Spaces.mixed b a f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      = ((Work.Spaces.mixed b a f z σ) * Work.Spaces.Wt α z σ) ^ 2 * ((w z) ^ 2)⁻¹ := by
    rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z σ hsin]
    field_simp
  rw [hid, mul_comm ((w z) ^ 2)⁻¹]
  exact mul_le_mul_of_nonneg_right
    (sq_le_HkIntegrand_mixed α 4 f z σ a b ha (by omega))
    (inv_nonneg.mpr (by positivity))

/-- The `θ`-slice of a mixed slot is integrable. -/
theorem integrableOn_slice_sq {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (hF : SmoothOpen f)
    (hmem : HkMem α 4 f) (b a : ℕ) (hab : a + b ≤ 4) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun σ => (Work.Spaces.mixed b a f z σ) ^ 2) Iθ := by
  have hmeas : AEStronglyMeasurable (fun σ : ℝ => (Work.Spaces.mixed b a f z σ) ^ 2)
      (volume.restrict Iθ) :=
    Work.H2.T1Q.aesm_Iθ_of_continuousOn
      (((hF.mixed b a).curry_θ hz).continuousOn.pow 2)
  refine Integrable.mono' (hmem.1 z hz.le) hmeas ?_
  filter_upwards [ae_mem_Ioo_Iθ] with σ hσ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact Work.H2.T1Q.mixed_sq_le_HkIntegrand α hα f b a hab hz hσ.1 hσ.2

/-! ## The pointwise bound -/

/-- **The pointwise bound for mixed derivatives of order `≤ 2` in the open-quadrant class.**

For `f` with `SmoothOpen f` and `HkMem α 4 f`, every mixed derivative `D_z^bD_θ^a f` with
`a + b ≤ 2` is bounded on the open quadrant by `C (γ-1)⁻¹ |f|²_{ℋ⁴}`, `C` universal. -/
theorem PwAny : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ),
    0 < α → α ≤ 1 → SmoothOpen f → HkMem α 4 f → a + b ≤ 2 → ∀ z : ℝ, 0 < z →
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.mixed b a f z θ) ^ 2 ≤ C / (Work.Spaces.gam α - 1)
        * Work.Spaces.HkSq α 4 f := by
  obtain ⟨C1, hC1pos, hC1⟩ := sob_theta_mean
  obtain ⟨C2, hC2pos, hC2⟩ := sliceAvg_le
  obtain ⟨C3, hC3pos, hC3⟩ := sliceAng_le
  set M : ℝ := max C2 (max C3 1) with hM
  have hMpos : 0 < M := lt_of_lt_of_le hC2pos (le_max_left _ _)
  refine ⟨2 * C1 * M, by positivity, ?_⟩
  intro α f b a hα hα1 hF hmem hab z hz θ hθ
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγle : gam α - 1 ≤ 1 := by rw [gam_sub_one]; linarith
  have hHk : 0 ≤ HkSq α 4 f := HkSq_nonneg α 4 f
  -- the mean term
  have hA : (∫ σ in Iθ, (mixed b a f z σ) ^ 2) ≤ M * HkSq α 4 f := by
    refine le_trans (hC2 α f b a hα hα1 hF hmem (by omega) z hz) ?_
    rw [hM]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hHk
  -- the derivative term
  have hB : (∫ σ in Iθ, (deriv (fun σ' : ℝ => mixed b a f z σ') σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - gam α)) ≤ M * HkSq α 4 f := by
    have hbeq : (∫ σ in Iθ, (deriv (fun σ' : ℝ => mixed b a f z σ') σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - gam α))
        = ∫ σ in Iθ, (mixed b (a + 1) f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(gam α)) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_mem_Ioo_Iθ] with σ hσ
      exact deriv_mixed_weight α hF b a hz hσ
    rw [hbeq]
    refine le_trans (hC3 α f b (a + 1) hα hα1 hF hmem (by omega) (by omega) z hz) ?_
    rw [hM]
    exact mul_le_mul_of_nonneg_right
      (le_trans (le_max_left C3 1) (le_max_right C2 (max C3 1))) hHk
  -- integrability of the two integrands
  have hint1 : IntegrableOn (fun σ => (mixed b a f z σ) ^ 2) Iθ :=
    integrableOn_slice_sq hα hF hmem b a (by omega) hz
  have hint2 : IntegrableOn (fun σ => (deriv (fun σ' : ℝ => mixed b a f z σ') σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ := by
    refine Integrable.mono' ((hmem.1 z hz.le).const_mul ((w z) ^ 2)⁻¹)
      (Work.H2.T1Q.aesm_Iθ_of_continuousOn ?_) ?_
    · have hbase : Continuous fun σ : ℝ => Real.sin (2 * σ) := by fun_prop
      refine ContinuousOn.mul (((hF.mixed b a).pth.curry_θ hz).continuousOn.pow 2)
        (hbase.continuousOn.rpow_const ?_)
      intro σ hσ
      exact Or.inl (ne_of_gt (sin_two_pos hσ))
    · filter_upwards [ae_mem_Ioo_Iθ] with σ hσ
      have hsin : 0 < Real.sin (2 * σ) := sin_two_pos hσ
      have hwpos : 0 < w z := w_pos_of_pos hz
      have hwe := deriv_mixed_weight α hF b a hz hσ
      have hnn : 0 ≤ (deriv (fun σ' : ℝ => mixed b a f z σ') σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - gam α) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
      rw [Real.norm_of_nonneg hnn, hwe]
      have hid : (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          = ((Work.Spaces.mixed b (a + 1) f z σ) * Work.Spaces.Wt α z σ) ^ 2
            * ((w z) ^ 2)⁻¹ := by
        rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z σ hsin]
        field_simp
      rw [hid, mul_comm ((w z) ^ 2)⁻¹]
      exact mul_le_mul_of_nonneg_right
        (sq_le_HkIntegrand_mixed α 4 f z σ (a + 1) b (by omega) (by omega))
        (inv_nonneg.mpr (by positivity))
  -- the angular inequality at the fixed `z`
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun σ' : ℝ => mixed b a f z σ')
        (deriv (fun σ' : ℝ => mixed b a f z σ') x) x := by
    intro x hx
    exact (((hF.mixed b a).curry_θ hz).differentiableOn
      (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hx) |>.hasDerivAt
  have hcontd : ContinuousOn (deriv (fun σ' : ℝ => mixed b a f z σ'))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h : ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.mixed b a f) z σ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ((hF.mixed b a).pth.curry_θ hz).continuousOn
    simpa only [Work.Spaces.pth] using h
  have hmain := hC1 α (fun σ' : ℝ => mixed b a f z σ') θ hα hα1 hθ hder hcontd hint1 hint2
  -- assemble
  have hsum : (mixed b a f z θ) ^ 2 ≤ C1 * (M * HkSq α 4 f
      + (gam α - 1)⁻¹ * (M * HkSq α 4 f)) := by
    refine le_trans hmain ?_
    refine mul_le_mul_of_nonneg_left (add_le_add hA ?_) hC1pos.le
    exact mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr hγ.le)
  have hfac : C1 * (M * HkSq α 4 f + (gam α - 1)⁻¹ * (M * HkSq α 4 f))
      ≤ (2 * C1 * M) / (gam α - 1) * HkSq α 4 f := by
    have h1 : (1 : ℝ) ≤ (gam α - 1)⁻¹ := by
      rw [one_le_inv₀ hγ]
      simpa using hγle
    have hMH : 0 ≤ M * HkSq α 4 f := mul_nonneg hMpos.le hHk
    have hkey : M * HkSq α 4 f + (gam α - 1)⁻¹ * (M * HkSq α 4 f)
        ≤ 2 * ((gam α - 1)⁻¹ * (M * HkSq α 4 f)) := by
      have h2 : (gam α - 1)⁻¹ * (M * HkSq α 4 f)
          ≤ 2 * ((gam α - 1)⁻¹ * (M * HkSq α 4 f)) :=
        le_mul_of_one_le_left (mul_nonneg (inv_nonneg.mpr hγ.le) hMH) (by norm_num)
      nlinarith [hMH, h2]
    calc C1 * (M * HkSq α 4 f + (gam α - 1)⁻¹ * (M * HkSq α 4 f))
        ≤ C1 * (2 * ((gam α - 1)⁻¹ * (M * HkSq α 4 f))) :=
          mul_le_mul_of_nonneg_left hkey hC1pos.le
      _ = (2 * C1 * M) / (gam α - 1) * HkSq α 4 f := by
          rw [div_eq_mul_inv]; ring
  exact le_trans hsum hfac

end Work.FTS.OpenPkg.ProdOpen
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6.sliceAng_le6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0)

/-
Template (verbatim, level 4): `Work.FTS.OpenPkg.ProdOpen.sliceAng_le`
(`Submission/Work/FTS/OpenPkg/ProdOpen/SlicesOpen.lean`, second half).  Same proof with
`4 ↦ 6` and `a + b ≤ 3 ↦ a + b ≤ 5`; the Tonelli input
`Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open` becomes
`Work.FTS.StrongPersist.N6.sda_HkSqSwap_open6` (in `N6/Swap6`), and the slot dominations used
inside are the general `Work.Spaces.sq_le_HkIntegrand_mixed` / `sq_le_HkIntegrand_z` at `k = 6`
(no new hypotheses).

Please put the proof in `Submission/Work/FTS/StrongPersist/N6/sliceAng_le6.lean` (module
`Submission.Work.FTS.StrongPersist.N6.sliceAng_le6`), inside `namespace Work.FTS.StrongPersist.N6`.
-/
theorem sliceAng_le6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    1 ≤ a → a + b ≤ 5 → ∀ z : ℝ, 0 < z →
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ C * Work.Spaces.HkSq α 6 f := by
  refine ⟨4, by norm_num, ?_⟩
  intro α f b a hα hα1 hF hmem ha hab z hz
  obtain ⟨hswap, hGint, hGslice⟩ :=
    Work.FTS.StrongPersist.N6.sda_HkSqSwap_open6 α f hF hmem
  have hHknn : 0 ≤ HkSq α 6 f := HkSq_nonneg α 6 f
  set R₀ : ℝ := max z 1 with hR₀def
  have hzR : z ≤ R₀ := le_max_left _ _
  have hR1 : (1 : ℝ) ≤ R₀ := le_max_right _ _
  have hRpos : 0 < R₀ := lt_of_lt_of_le hz hzR
  have hz2R : z ≤ 2 * R₀ := by linarith
  have hR2R : R₀ ≤ 2 * R₀ := by linarith
  have hbound : ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      IntegrableOn (fun s => HkIntegrand α 6 f s θ) Iz →
      (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
        ≤ (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 6 f s θ := by
    intro θ hθ hθint
    have hθIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsinpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hlamnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(gam α)) := Real.rpow_nonneg hsinpos.le _
    have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
        HasDerivAt (fun x' : ℝ => mixed b a f x' θ) (pz (mixed b a f) x θ) x :=
      fun x hx => (hF.mixed b a).hasDerivAt_slice hθ (lt_of_lt_of_le hz hx.1)
    have hcont : ContinuousOn (fun x : ℝ => mixed b a f x θ) (Set.Icc R₀ (2 * R₀)) :=
      ((hF.mixed b a).curry_z hθ).continuousOn.mono
        (fun x hx => lt_of_lt_of_le hRpos hx.1)
    have hcont' : ContinuousOn (fun x : ℝ => pz (mixed b a f) x θ) (Set.Icc z (2 * R₀)) :=
      (((hF.mixed b a).pz).curry_z hθ).continuousOn.mono
        (fun x hx => lt_of_lt_of_le hz hx.1)
    have hint : IntegrableOn (fun x : ℝ => (mixed b a f x θ) ^ 2)
        (Set.Icc R₀ (2 * R₀)) :=
      ContinuousOn.integrableOn_compact isCompact_Icc (hcont.pow 2)
    have hwin := Work.FTS.TransportS.half_line_window_bound
      (h := fun x : ℝ => mixed b a f x θ)
      (h' := fun x : ℝ => pz (mixed b a f) x θ) hz hzR hderiv hcont hcont' hint
    -- domination of the two summands by the `ℋ⁶`-integrand
    have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
        (Real.sin (2 * θ)) ^ (-(gam α)) * (x * pz (mixed b a f) x θ * w x) ^ 2
          ≤ HkIntegrand α 6 f x θ := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hz hx.1
      have heq : x * pz (mixed b a f) x θ = mixed (b + 1) a f x θ := rfl
      rw [heq, mul_pow]
      have hkey : (Real.sin (2 * θ)) ^ (-(gam α))
            * ((mixed (b + 1) a f x θ) ^ 2 * (w x) ^ 2)
          = (mixed (b + 1) a f x θ * Wt α x θ) ^ 2 := by
        rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α x θ hsinpos]
        ring
      calc (Real.sin (2 * θ)) ^ (-(gam α)) * ((mixed (b + 1) a f x θ) ^ 2 * (w x) ^ 2)
          = (mixed (b + 1) a f x θ * Wt α x θ) ^ 2 := hkey
        _ ≤ HkIntegrand α 6 f x θ :=
            sq_le_HkIntegrand_mixed α 6 f x θ a (b + 1) ha (by omega)
    have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
        (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2
          ≤ HkIntegrand α 6 f x θ := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hRpos hx.1
      have hw : (1 : ℝ) ≤ w x := Work.FTS.TransportS.one_le_w hxpos
      have hcmp : (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2
          ≤ (mixed b a f x θ) ^ 2 * (w x) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
        have hw2 : (1 : ℝ) ≤ (w x) ^ 2 := by nlinarith [hw]
        have h1 : (mixed b a f x θ) ^ 2 ≤ (mixed b a f x θ) ^ 2 * (w x) ^ 2 := by
          calc (mixed b a f x θ) ^ 2 = (mixed b a f x θ) ^ 2 * 1 := by ring
            _ ≤ (mixed b a f x θ) ^ 2 * (w x) ^ 2 :=
                mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
        have h2 : (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2
            ≤ (Real.sin (2 * θ)) ^ (-(gam α)) * ((mixed b a f x θ) ^ 2 * (w x) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hlamnn
        calc (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2
            ≤ (Real.sin (2 * θ)) ^ (-(gam α)) * ((mixed b a f x θ) ^ 2 * (w x) ^ 2) := h2
          _ = (mixed b a f x θ) ^ 2 * (w x) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by ring
      refine le_trans hcmp ?_
      have hkey : (mixed b a f x θ) ^ 2 * (w x) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
          = (mixed b a f x θ * Wt α x θ) ^ 2 := by
        rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α x θ hsinpos]
        ring
      calc (mixed b a f x θ) ^ 2 * (w x) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
          = (mixed b a f x θ * Wt α x θ) ^ 2 := hkey
        _ ≤ HkIntegrand α 6 f x θ :=
            sq_le_HkIntegrand_mixed α 6 f x θ a b ha (by omega)
    -- interval integrals
    have hIntA : IntervalIntegrable
        (fun x : ℝ => (x * pz (mixed b a f) x θ * w x) ^ 2) volume z (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => (x * pz (mixed b a f) x θ * w x) ^ 2)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      refine (ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_).pow 2
      unfold w
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))
    have hIntAw : IntervalIntegrable
        (fun x : ℝ => (Real.sin (2 * θ)) ^ (-(gam α)) * (x * pz (mixed b a f) x θ * w x) ^ 2)
        volume z (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * θ)) ^ (-(gam α))
        * (x * pz (mixed b a f) x θ * w x) ^ 2) (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      refine ContinuousOn.mul continuousOn_const ?_
      refine (ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_).pow 2
      unfold w
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))
    have hIntBw : IntervalIntegrable
        (fun x : ℝ => (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2)
        volume R₀ (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * θ)) ^ (-(gam α))
        * (mixed b a f x θ) ^ 2) (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hR2R]
      exact ContinuousOn.mul continuousOn_const (hcont.pow 2)
    have hHkcont : ∀ {a' b' : ℝ}, 0 < a' →
        ContinuousOn (fun x : ℝ => HkIntegrand α 6 f x θ) (Set.Icc a' b') := by
      intro a' b' ha'
      have hmap : MapsTo (fun x : ℝ => (x, θ)) (Set.Icc a' b') Q0 := fun x hx =>
        mem_Q0.mpr ⟨lt_of_lt_of_le ha' hx.1, hθ.1, hθ.2⟩
      have hc := (hF.continuousOn_HkIntegrand α 6).comp
        (continuousOn_id.prodMk continuousOn_const) hmap
      simpa only [Function.comp_def, id_eq] using hc
    have hIntA' : IntervalIntegrable (fun x : ℝ => HkIntegrand α 6 f x θ) volume z (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => HkIntegrand α 6 f x θ)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      exact hHkcont hz
    have hIntB' : IntervalIntegrable (fun x : ℝ => HkIntegrand α 6 f x θ) volume R₀ (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => HkIntegrand α 6 f x θ)
        (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hR2R]
      exact hHkcont hRpos
    have hbigA : ∫ x in z..(2 * R₀), HkIntegrand α 6 f x θ
        ≤ ∫ s in Iz, HkIntegrand α 6 f s θ := by
      rw [intervalIntegral.integral_of_le hz2R]
      refine setIntegral_mono_set hθint
        (Eventually.of_forall fun x => HkIntegrand_nonneg α 6 f x θ) ?_
      exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
    have hbigB : ∫ x in R₀..(2 * R₀), HkIntegrand α 6 f x θ
        ≤ ∫ s in Iz, HkIntegrand α 6 f s θ := by
      rw [intervalIntegral.integral_of_le hR2R]
      refine setIntegral_mono_set hθint
        (Eventually.of_forall fun x => HkIntegrand_nonneg α 6 f x θ) ?_
      exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
    have hmA := intervalIntegral.integral_mono_on hz2R hIntAw hIntA' hptA
    have hmB := intervalIntegral.integral_mono_on hR2R hIntBw hIntB' hptB
    have hsplitA : (Real.sin (2 * θ)) ^ (-(gam α))
        * (∫ x in z..(2 * R₀), (x * pz (mixed b a f) x θ * w x) ^ 2)
        = ∫ x in z..(2 * R₀), (Real.sin (2 * θ)) ^ (-(gam α))
            * (x * pz (mixed b a f) x θ * w x) ^ 2 :=
      (intervalIntegral.integral_const_mul _ _).symm
    have hsplitB : (Real.sin (2 * θ)) ^ (-(gam α))
        * (∫ x in R₀..(2 * R₀), (mixed b a f x θ) ^ 2)
        = ∫ x in R₀..(2 * R₀), (Real.sin (2 * θ)) ^ (-(gam α))
            * (mixed b a f x θ) ^ 2 :=
      (intervalIntegral.integral_const_mul _ _).symm
    calc (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
        = (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f z θ) ^ 2 := by ring
      _ ≤ (Real.sin (2 * θ)) ^ (-(gam α))
            * (2 * (∫ x in z..(2 * R₀), (x * pz (mixed b a f) x θ * w x) ^ 2)
              + (2 / R₀) * ∫ x in R₀..(2 * R₀), (mixed b a f x θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hwin hlamnn
      _ = 2 * ((Real.sin (2 * θ)) ^ (-(gam α))
              * (∫ x in z..(2 * R₀), (x * pz (mixed b a f) x θ * w x) ^ 2))
            + (2 / R₀) * ((Real.sin (2 * θ)) ^ (-(gam α))
              * (∫ x in R₀..(2 * R₀), (mixed b a f x θ) ^ 2)) := by ring
      _ = 2 * (∫ x in z..(2 * R₀), (Real.sin (2 * θ)) ^ (-(gam α))
              * (x * pz (mixed b a f) x θ * w x) ^ 2)
            + (2 / R₀) * (∫ x in R₀..(2 * R₀), (Real.sin (2 * θ)) ^ (-(gam α))
              * (mixed b a f x θ) ^ 2) := by rw [hsplitA, hsplitB]
      _ ≤ 2 * (∫ s in Iz, HkIntegrand α 6 f s θ)
            + (2 / R₀) * (∫ s in Iz, HkIntegrand α 6 f s θ) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left (le_trans hmA hbigA) (by norm_num)
          · exact mul_le_mul_of_nonneg_left (le_trans hmB hbigB) (by positivity)
      _ = (2 + 2 / R₀) * (∫ s in Iz, HkIntegrand α 6 f s θ) := by ring
  have hle : (fun θ : ℝ => (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)))
      ≤ᵐ[volume.restrict Iθ]
      fun θ : ℝ => (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 6 f s θ := by
    filter_upwards [hGslice, Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθint hθ
    exact hbound θ hθ hθint
  have hfae : 0 ≤ᵐ[volume.restrict Iθ]
      (fun θ : ℝ => (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) :=
    ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
        (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _)
  calc ∫ θ in Iθ, (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
      ≤ ∫ θ in Iθ, (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 6 f s θ :=
        integral_mono_of_nonneg hfae (hGint.const_mul _) hle
    _ = (2 + 2 / R₀) * HkSq α 6 f := by
        rw [MeasureTheory.integral_const_mul, hswap]
    _ ≤ 4 * HkSq α 6 f := by
        refine mul_le_mul_of_nonneg_right ?_ hHknn
        have : 2 / R₀ ≤ 2 := by
          rw [div_le_iff₀ hRpos]; linarith
        linarith

end Work.FTS.StrongPersist.N6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.Spaces

/-- Almost every angle of `Iθ` lies in the open interval `(0, π/2)`. -/
theorem ae_mem_Ioo_Iθ6 :
    ∀ᵐ σ ∂(volume.restrict Iθ), σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [MeasureTheory.ae_restrict_iff' (s := Iθ) measurableSet_Icc]
  filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)]
    with σ h
  exact fun hmem => h.mpr hmem

/-
Template (verbatim, level 4): `Work.FTS.OpenPkg.ProdOpen.sliceAvg_le`
(`Submission/Work/FTS/OpenPkg/ProdOpen/SlicesOpen.lean`).  This is the same proof with `4 ↦ 6`
and `a + b ≤ 3 ↦ a + b ≤ 5`; the level-6 slot dominations are
`Work.FTS.StrongPersist.N6.mixed_sq_w_sq_le_HkIntegrand6` and
`Work.FTS.StrongPersist.N6.mixed_sq_le_HkIntegrand6` (in `N6/Slots`), and the Tonelli input
`Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open` is replaced by
`Work.FTS.StrongPersist.N6.sda_HkSqSwap_open6` (in `N6/Swap6`).

Please put the proof in `Submission/Work/FTS/StrongPersist/N6/sliceAvg_le6.lean` (module
`Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6`), inside `namespace Work.FTS.StrongPersist.N6`.
-/
theorem sliceAvg_le6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    a + b ≤ 5 → ∀ z : ℝ, 0 < z →
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 f := by
  refine ⟨4, by norm_num, ?_⟩
  intro α f b a hα hα1 hF hmem hab z hz
  obtain ⟨hswap, hGint, hGslice⟩ := Work.FTS.StrongPersist.N6.sda_HkSqSwap_open6 α f hF hmem
  have hHknn : 0 ≤ HkSq α 6 f := HkSq_nonneg α 6 f
  set R₀ : ℝ := max z 1 with hR₀def
  have hzR : z ≤ R₀ := le_max_left _ _
  have hR1 : (1 : ℝ) ≤ R₀ := le_max_right _ _
  have hRpos : 0 < R₀ := lt_of_lt_of_le hz hzR
  have hz2R : z ≤ 2 * R₀ := by linarith
  have hR2R : R₀ ≤ 2 * R₀ := by linarith
  -- the pointwise-in-θ bound on a slice
  have hbound : ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      IntegrableOn (fun s => HkIntegrand α 6 f s θ) Iz →
      (mixed b a f z θ) ^ 2 ≤ (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 6 f s θ := by
    intro θ hθ hθint
    have hθIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    -- the window bound at the angle `θ`
    have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
        HasDerivAt (fun x' : ℝ => mixed b a f x' θ) (pz (mixed b a f) x θ) x :=
      fun x hx => (hF.mixed b a).hasDerivAt_slice hθ (lt_of_lt_of_le hz hx.1)
    have hcont : ContinuousOn (fun x : ℝ => mixed b a f x θ) (Set.Icc R₀ (2 * R₀)) :=
      ((hF.mixed b a).curry_z hθ).continuousOn.mono
        (fun x hx => lt_of_lt_of_le hRpos hx.1)
    have hcont' : ContinuousOn (fun x : ℝ => pz (mixed b a f) x θ) (Set.Icc z (2 * R₀)) :=
      (((hF.mixed b a).pz).curry_z hθ).continuousOn.mono
        (fun x hx => lt_of_lt_of_le hz hx.1)
    have hint : IntegrableOn (fun x : ℝ => (mixed b a f x θ) ^ 2)
        (Set.Icc R₀ (2 * R₀)) :=
      ContinuousOn.integrableOn_compact isCompact_Icc (hcont.pow 2)
    have hwin := Work.FTS.TransportS.half_line_window_bound
      (h := fun x : ℝ => mixed b a f x θ)
      (h' := fun x : ℝ => pz (mixed b a f) x θ) hz hzR hderiv hcont hcont' hint
    -- the two summands are dominated by the `ℋ⁶`-integrand
    have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
        (x * pz (mixed b a f) x θ * w x) ^ 2 ≤ HkIntegrand α 6 f x θ := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hz hx.1
      have heq : x * pz (mixed b a f) x θ = mixed (b + 1) a f x θ := rfl
      rw [heq, mul_pow]
      exact Work.FTS.StrongPersist.N6.mixed_sq_w_sq_le_HkIntegrand6 α hα f (b + 1) a
        (by omega) hxpos hθ.1 hθ.2
    have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
        (mixed b a f x θ) ^ 2 ≤ HkIntegrand α 6 f x θ := fun x hx =>
      Work.FTS.StrongPersist.N6.mixed_sq_le_HkIntegrand6 α hα f b a (by omega)
        (lt_of_lt_of_le hRpos hx.1) hθ.1 hθ.2
    -- interval integrals
    have hIntA : IntervalIntegrable
        (fun x : ℝ => (x * pz (mixed b a f) x θ * w x) ^ 2) volume z (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => (x * pz (mixed b a f) x θ * w x) ^ 2)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      refine (ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_).pow 2
      unfold w
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))
    have hHkcont : ∀ {a' b' : ℝ}, 0 < a' →
        ContinuousOn (fun x : ℝ => HkIntegrand α 6 f x θ) (Set.Icc a' b') := by
      intro a' b' ha'
      have hmap : MapsTo (fun x : ℝ => (x, θ)) (Set.Icc a' b') Work.FTS.EllipticEst.Q0 :=
        fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le ha' hx.1, hθ.1, hθ.2⟩
      have hc := (hF.continuousOn_HkIntegrand α 6).comp
        (continuousOn_id.prodMk continuousOn_const) hmap
      simpa only [Function.comp_def, id_eq] using hc
    have hIntA' : IntervalIntegrable (fun x : ℝ => HkIntegrand α 6 f x θ) volume z (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => HkIntegrand α 6 f x θ)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      exact hHkcont hz
    have hIntB : IntervalIntegrable (fun x : ℝ => (mixed b a f x θ) ^ 2) volume R₀ (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => (mixed b a f x θ) ^ 2)
        (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hR2R]
      exact hcont.pow 2
    have hIntB' : IntervalIntegrable (fun x : ℝ => HkIntegrand α 6 f x θ) volume R₀ (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => HkIntegrand α 6 f x θ)
        (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hR2R]
      exact hHkcont hRpos
    -- extend the interval integrals to `Iz`
    have hbigA : ∫ x in z..(2 * R₀), HkIntegrand α 6 f x θ
        ≤ ∫ s in Iz, HkIntegrand α 6 f s θ := by
      rw [intervalIntegral.integral_of_le hz2R]
      refine setIntegral_mono_set hθint
        (Eventually.of_forall fun x => HkIntegrand_nonneg α 6 f x θ) ?_
      exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
    have hbigB : ∫ x in R₀..(2 * R₀), HkIntegrand α 6 f x θ
        ≤ ∫ s in Iz, HkIntegrand α 6 f s θ := by
      rw [intervalIntegral.integral_of_le hR2R]
      refine setIntegral_mono_set hθint
        (Eventually.of_forall fun x => HkIntegrand_nonneg α 6 f x θ) ?_
      exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
    have hmA := intervalIntegral.integral_mono_on hz2R hIntA hIntA' hptA
    have hmB := intervalIntegral.integral_mono_on hR2R hIntB hIntB' hptB
    calc (mixed b a f z θ) ^ 2
        ≤ 2 * (∫ x in z..(2 * R₀), (x * pz (mixed b a f) x θ * w x) ^ 2)
          + (2 / R₀) * ∫ x in R₀..(2 * R₀), (mixed b a f x θ) ^ 2 := hwin
      _ ≤ 2 * (∫ s in Iz, HkIntegrand α 6 f s θ)
          + (2 / R₀) * (∫ s in Iz, HkIntegrand α 6 f s θ) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left (le_trans hmA hbigA) (by norm_num)
          · exact mul_le_mul_of_nonneg_left (le_trans hmB hbigB) (by positivity)
      _ = (2 + 2 / R₀) * (∫ s in Iz, HkIntegrand α 6 f s θ) := by ring
  -- integrate the pointwise (a.e.) bound over `θ`
  have hle : (fun θ : ℝ => (mixed b a f z θ) ^ 2)
      ≤ᵐ[volume.restrict Iθ]
      fun θ : ℝ => (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 6 f s θ := by
    filter_upwards [hGslice, ae_mem_Ioo_Iθ6] with θ hθint hθ
    exact hbound θ hθ hθint
  have hfae : 0 ≤ᵐ[volume.restrict Iθ] (fun θ : ℝ => (mixed b a f z θ) ^ 2) :=
    ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => sq_nonneg _
  calc ∫ θ in Iθ, (mixed b a f z θ) ^ 2
      ≤ ∫ θ in Iθ, (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 6 f s θ :=
        integral_mono_of_nonneg hfae (hGint.const_mul _) hle
    _ = (2 + 2 / R₀) * HkSq α 6 f := by
        rw [MeasureTheory.integral_const_mul, hswap]
    _ ≤ 4 * HkSq α 6 f := by
        refine mul_le_mul_of_nonneg_right ?_ hHknn
        have : 2 / R₀ ≤ 2 := by
          rw [div_le_iff₀ hRpos]; linarith
        linarith

end Work.FTS.StrongPersist.N6
end
end
