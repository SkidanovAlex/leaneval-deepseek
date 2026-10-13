/-
# `Work.FTS.OpenPkg.ProdOpen.PwOpen`

The pointwise bound of the open-quadrant product rule: for `f` of class
`Work.FTS.VocabO.HQo α 4` (`SmoothOpen` + `HkMem`),

  `(D_z^b D_θ^a f(z,θ))² ≤ C (γ-1)⁻¹ |f|²_{ℋ⁴}`,  `a + b ≤ 2`,

with `C` universal.  This is Elgindi's Corollary `SecondDerivativesBounded` in the interior
class, in the squared form the product rule consumes.

Route.  The classical proof pulls the orbit out of the boundary value at `θ = 0`; here nothing
vanishes at the boundary, so the missing term is paid for by a *mean*:

* the angular inequality `sob_theta_mean` at the fixed `z`:
  `(h θ)² ≤ C (∫_θ h² + (γ-1)⁻¹ ∫_θ (h')² sin(2·)^{2-γ})` for the slice `h = D_z^bD_θ^a f(z,·)`;
* the two θ-slice integrals are bounded *uniformly in `z`* by `|f|²_{ℋ⁴}` (`sliceAvg_le` for
  the mean term and `sliceAng_le` for the derivative term, which is the next mixed slot with
  the `sin^{-γ}` weight).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.OpenPkg.ProdOpen.SlicesOpen
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.H2.T1Q.PwBdQ

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
