import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.FTS.EllipticEst.H2W.I4Open
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.H2W.Ae.hkMem_ang1
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_upper
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem
import Submission.Work.FTS.EllipticEst.remov.AeIPMemsSlim
import Submission.Work.FTS.EllipticEst.Honest.sliceInterp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

/-!
# `aeI4_open`: the `I₄` upper bound of Step 2 of `prop:H2` in the a.e. class

Target: for `AeData α u G`, `HkMem α 0 u` and `HkMem α 0 (z ∂_z u)`,

  `IP (∂_θ(tan θ·u)) (∂_θθu) ≤ IP u (∂_θθu) + C · IP u u`.

Route: instantiate the *proved* `Work.FTS.EllipticEst.H2W.I4Open` (`H2W/I4Open.lean`), which
performs the whole assembly (the slicewise inequality `H2W.sliceI4Open` at each `z > 0`, then the
`z`-integration, with the three pairings honest), giving

  `IP (∂_θ(tan θ·u)) (∂_θθu) - IP u (∂_θθu) ≤ (1 - η) · IP u u`,   `η = 99/100`.

It remains to supply, for every `z > 0`:

* the three honesty statements `IPMem (∂_θ(tan θ·u)) (∂_θθu)`, `IPMem u (∂_θθu)`, `IPMem u u`
  (from the proved `remov.aeIPMemsSlim : AngAWeak.AeIPMems` and the diagonal
  `AngClean.HkMem_zero_IPMem`);
* the four slicewise integrability facts
  `∫ (u z ·/cos θ)²σ`, `∫ (∂_θ(u z ·/cos ·))²σ`, `∫ (∂_θθu(z,·))²σ`,
  `∫ sin²θ·(∂_θ(u z ·/cos ·))²σ` over `θ ∈ Iθ`.

The first is `psiDivCosSq_integrable` of `TT/weakI4Psi.lean` transplanted to the a.e. class (its
only class-dependent ingredient is the right-endpoint rate, which in the a.e. class is the proved
`H2W.AeProof.AeSliceRightTendsto`); the second is `TT.psiDerivSq_lower`/`TT.psiDerivSq_upper`
transplanted (the upper half needs `HkMem α 0 (∂_θ(tan θ·u))`, which in the a.e. class is the
proved `H2W.Ae.hkMem_ang1`); the third is immediate slicewise `HkMem`; the fourth follows from the
second by the pointwise domination `sin²θ ≤ 1`.
-/

/-! ## `IntegrableOn` book-keeping for the gluing of the two halves of `Iθ` -/

/-- `IntegrableOn` only sees the set up to a null set. -/
private theorem integrableOn_congr_set {f : ℝ → ℝ} {s t : Set ℝ}
    (h : IntegrableOn f s volume) (hst : s =ᵐ[volume] t) : IntegrableOn f t volume := by
  have hμ : volume.restrict s = volume.restrict t := Measure.restrict_congr_set hst
  rw [MeasureTheory.IntegrableOn] at h ⊢
  rwa [hμ] at h

/-- The two halves of `Ioo 0 (π/2)` (up to the null point `π/4`). -/
private theorem Ioo_ae_eq_halves :
    Set.Ioo (0 : ℝ) (Real.pi / 2)
      =ᵐ[volume] (Set.Ioo 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2) : Set ℝ) := by
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ Real.pi / 4 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hne] with x hx
  apply propext
  simp only [Set.mem_Ioo, Set.mem_union]
  constructor
  · intro h
    rcases lt_or_gt_of_ne hx with h4 | h4
    · exact Or.inl ⟨h.1, h4⟩
    · exact Or.inr ⟨h4, h.2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, by linarith [h2, Real.pi_pos]⟩
    · exact ⟨by linarith [h1, Real.pi_pos], h2⟩

/-- Integrability on the two halves gives integrability on `Iθ`. -/
private theorem integrableOn_Iθ_of_halves {f : ℝ → ℝ}
    (h1 : IntegrableOn f (Set.Ioo 0 (Real.pi / 4)) volume)
    (h2 : IntegrableOn f (Set.Ioo (Real.pi / 4) (Real.pi / 2)) volume) :
    IntegrableOn f Work.Spaces.Iθ volume := by
  have hunion : IntegrableOn f (Set.Ioo 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2))
      volume := h1.union h2
  have hIoo : IntegrableOn f (Set.Ioo 0 (Real.pi / 2)) volume :=
    integrableOn_congr_set hunion Ioo_ae_eq_halves.symm
  have hIcc : IntegrableOn f (Set.Icc 0 (Real.pi / 2)) volume :=
    integrableOn_congr_set hIoo (MeasureTheory.Ioo_ae_eq_Icc (a := 0) (b := Real.pi / 2))
  simpa only [Work.Spaces.Iθ] using hIcc

/-! ## The angular weight -/

private theorem sig_continuousOn_Ioo :
    ContinuousOn Work.FTS.EllipticEst.AngSecond.sig (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hc : Continuous (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hsinpos : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * x) := by
    intro x hx
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])
  change ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (Set.Ioo (0 : ℝ) (Real.pi / 2))
  exact hc.continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt (hsinpos x hx)))

private theorem sig_integrableOn_Iθ : IntegrableOn Work.FTS.EllipticEst.AngSecond.sig
    Work.Spaces.Iθ volume :=
  Work.FTS.EllipticEst.AngClean.integrableOn_sig

/-! ## The slice data available from the a.e. class -/

/-- The `θ`-slice of a datum of `AeData` is `C²` on the open interval. -/
private theorem slice_contDiffOn_ae {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
  Work.FTS.EllipticEst.TT.contDiffOn_slice_of_strip hA.smooth hz 2

/-- The slice data available from the a.e. class, uniform in `z > 0`. -/
private theorem slice_core_ae {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hu : Work.Spaces.HkMem α 0 u)
    {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) ∧
    IntegrableOn (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ ∧
    IntegrableOn (fun θ => (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ ∧
    IntegrableOn (fun θ => (deriv (fun θ' => u z θ') θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
  have hsm := slice_contDiffOn_ae hA hz
  have h0 := Work.FTS.EllipticEst.TT.integrableOn_sq_mul_sig_of_hkMem (g := u) hz hu
  have h2 : IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
    refine (Work.FTS.EllipticEst.TT.integrableOn_sq_mul_sig_of_hkMem (g := Work.Spaces.pthIter 2 u)
      hz hA.memAng2).congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  have h1 : IntegrableOn (fun θ => (deriv (fun θ' => u z θ') θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.Honest.sliceInterp (fun θ => u z θ) hsm h0 h2).1
  exact ⟨hsm, h0, h2, h1⟩

/-! ## The first slicewise integrability fact: `∫ (u z · / cos)² σ` -/

private theorem ae_psiDivCosSq_integrable {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hu : Work.Spaces.HkMem α 0 u)
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (u z θ / Real.cos θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
  -- the right-endpoint rate of the slice
  obtain ⟨-, K, hK0, hKev⟩ :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G hA z hz
  obtain ⟨θ₀, hθ₀lt, hθ₀sub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hKev
  set θ₁ : ℝ := max θ₀ (Real.pi / 4) with hθ₁def
  have hθ₁lt : θ₁ < Real.pi / 2 := max_lt hθ₀lt (by linarith [Real.pi_pos])
  -- a bound on the compact piece `[π/4, θ₁]`
  obtain ⟨hsm, hf0, -, -⟩ := slice_core_ae hA hu hz
  have hsubIoo : Set.Icc (Real.pi / 4) θ₁ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun θ hθ =>
    ⟨by linarith [hθ.1, Real.pi_pos], lt_of_le_of_lt hθ.2 hθ₁lt⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc).exists_bound_of_continuousOn (hsm.continuousOn.mono hsubIoo)
  set M₂ : ℝ := max M 0 with hM₂def
  have hθ₁ge : Real.pi / 4 ≤ θ₁ := le_max_right _ _
  have hM₂ : ∀ θ ∈ Set.Icc (Real.pi / 4) θ₁, |u z θ| ≤ M₂ := by
    intro θ hθ
    have h1 : |u z θ| ≤ M := by simpa only [Real.norm_eq_abs] using hM θ hθ
    exact h1.trans (le_max_left _ _)
  have hcosθ₁pos : 0 < Real.cos θ₁ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ₁ge, Real.pi_pos], hθ₁lt⟩
  set C₀ : ℝ := (M₂ / Real.cos θ₁) ^ 2 + (K * Real.pi / 2) ^ 2 + 1 with hC₀def
  have hC₀nn : 0 ≤ C₀ := by
    rw [hC₀def]
    have h1 := sq_nonneg (M₂ / Real.cos θ₁)
    have h2 := sq_nonneg (K * Real.pi / 2)
    linarith
  have hC₀ge₁ : (M₂ / Real.cos θ₁) ^ 2 ≤ C₀ := by
    rw [hC₀def]
    have h2 := sq_nonneg (K * Real.pi / 2)
    linarith
  have hC₀ge₂ : (K * Real.pi / 2) ^ 2 ≤ C₀ := by
    rw [hC₀def]
    have h1 := sq_nonneg (M₂ / Real.cos θ₁)
    linarith
  -- the pointwise domination on `(0, π/2)`
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
        ≤ 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
          + C₀ * Work.FTS.EllipticEst.AngSecond.sig θ := by
    intro θ hθ
    have hσnn : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
      Work.FTS.EllipticEst.AngSecond.sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hcospos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hkey : (u z θ / Real.cos θ) ^ 2 ≤ 2 * (u z θ) ^ 2 + C₀ := by
      rcases lt_or_ge θ (Real.pi / 4) with h4 | h4
      · -- the lower quarter: `1/cos θ² ≤ 2`
        have hcle : Real.cos (Real.pi / 4) ≤ Real.cos θ :=
          Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hθ.1)
            (by linarith [Real.pi_pos]) h4.le
        have hc4 : 0 < Real.cos (Real.pi / 4) :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have hsq : (1 / 2 : ℝ) ≤ (Real.cos θ) ^ 2 := by
          have h2 : (Real.cos (Real.pi / 4)) ^ 2 = 1 / 2 := by
            rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
            norm_num
          nlinarith [hcle, h2, hc4.le]
        have hinv : ((Real.cos θ) ^ 2)⁻¹ ≤ 2 := by
          rw [inv_le_iff_one_le_mul₀ (by positivity : (0 : ℝ) < (Real.cos θ) ^ 2)]
          linarith
        rw [div_eq_mul_inv, mul_pow, inv_pow]
        nlinarith [sq_nonneg (u z θ), hinv, hC₀nn]
      · rcases le_or_gt θ θ₁ with h5 | h5
        · -- the compact piece
          have hθIcc : θ ∈ Set.Icc (Real.pi / 4) θ₁ := ⟨h4, h5⟩
          have hcle : Real.cos θ₁ ≤ Real.cos θ :=
            Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
              (by linarith [hθ.2, Real.pi_pos]) h5
          have hM₂nn : 0 ≤ M₂ := le_max_right _ _
          have h1 : |u z θ / Real.cos θ| ≤ M₂ / Real.cos θ₁ := by
            rw [abs_div, abs_of_pos hcospos, div_le_iff₀ hcospos,
              div_mul_eq_mul_div, le_div_iff₀ hcosθ₁pos]
            exact mul_le_mul (hM₂ θ hθIcc) hcle hcosθ₁pos.le hM₂nn
          have h2 : (u z θ / Real.cos θ) ^ 2 ≤ (M₂ / Real.cos θ₁) ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          nlinarith [h2, hC₀ge₁, sq_nonneg (u z θ)]
        · -- the rate region
          have h6 : θ ∈ Set.Ioo θ₁ (Real.pi / 2) := ⟨h5, hθ.2⟩
          have hrate : |u z θ| ≤ K * (Real.pi / 2 - θ) :=
            hθ₀sub ⟨lt_of_le_of_lt (le_max_left _ _) h6.1, h6.2⟩
          have hd : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
          have hj : (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ := by
            have h' := Real.mul_le_sin hd.le (by linarith [hθ.1, Real.pi_pos])
            rwa [Real.sin_pi_div_two_sub] at h'
          have h1 : |u z θ / Real.cos θ| ≤ K * Real.pi / 2 := by
            rw [abs_div, abs_of_pos hcospos, div_le_iff₀ hcospos]
            calc |u z θ| ≤ K * (Real.pi / 2 - θ) := hrate
              _ ≤ K * Real.pi / 2 * Real.cos θ := by
                  have hstep : K * (Real.pi / 2 - θ)
                      = K * Real.pi / 2 * (2 / Real.pi * (Real.pi / 2 - θ)) := by
                    field_simp
                  rw [hstep]
                  have hKπ : (0 : ℝ) ≤ K * Real.pi := mul_nonneg hK0 Real.pi_pos.le
                  exact mul_le_mul_of_nonneg_left hj (by linarith [hKπ])
          have h2 : (u z θ / Real.cos θ) ^ 2 ≤ (K * Real.pi / 2) ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          nlinarith [h2, hC₀ge₂, sq_nonneg (u z θ)]
    calc (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
        ≤ (2 * (u z θ) ^ 2 + C₀) * Work.FTS.EllipticEst.AngSecond.sig θ :=
          mul_le_mul_of_nonneg_right hkey hσnn
      _ = 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
            + C₀ * Work.FTS.EllipticEst.AngSecond.sig θ := by ring
  -- the majorant is integrable on `(0, π/2)` and the integrand is a.e. strongly measurable
  have hD : Integrable (fun θ => 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      + C₀ * Work.FTS.EllipticEst.AngSecond.sig θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    MeasureTheory.Integrable.add
      (MeasureTheory.Integrable.const_mul (hf0.mono_set Set.Ioo_subset_Icc_self) 2)
      (MeasureTheory.Integrable.const_mul
        (sig_integrableOn_Iθ.mono_set Set.Ioo_subset_Icc_self) C₀)
  have hmeas : AEStronglyMeasurable
      (fun θ => (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine ContinuousOn.aestronglyMeasurable (ContinuousOn.mul ?_ sig_continuousOn_Ioo)
      measurableSet_Ioo
    exact ContinuousOn.pow (hsm.continuousOn.div Real.continuous_cos.continuousOn
      (fun x hx => ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩))) 2
  have hIoo : IntegrableOn (fun θ => (u z θ / Real.cos θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) volume := by
    refine Integrable.mono' hD hmeas ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.AngSecond.sig_nonneg
      ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))]
    exact hpt θ hθ
  simpa only [Work.Spaces.Iθ] using
    integrableOn_congr_set hIoo (MeasureTheory.Ioo_ae_eq_Icc (a := 0) (b := Real.pi / 2))

/-! ## The second slicewise integrability fact: `∫ (∂_θ(u z · / cos ·))² σ` -/

/-- The lower half `(0, π/4)`. -/
private theorem ae_psiDerivSq_lower {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hu : Work.Spaces.HkMem α 0 u)
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 4)) := by
  have hslice : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    slice_contDiffOn_ae hA hz
  have h0 : IntegrableOn
      (fun θ => (fun θ' => u z θ') θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.TT.integrableOn_sq_mul_sig_of_hkMem (g := u) hz hu
  have h2 : IntegrableOn (fun θ => (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
    have hbase : IntegrableOn
        (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.TT.integrableOn_sq_mul_sig_of_hkMem (α := α) (z := z)
        (g := Work.Spaces.pthIter 2 u) hz hA.memAng2
    have hpt : ∀ θ : ℝ, Work.Spaces.pthIter 2 u z θ
        = deriv (fun t => deriv (fun θ' => u z θ') t) θ := fun θ => rfl
    refine hbase.congr_fun (fun θ _ => ?_) measurableSet_Icc
    show (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
      = (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ
    rw [hpt θ]
  have h1 : IntegrableOn (fun θ => (deriv (fun θ' => u z θ') θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.Honest.sliceInterp (fun θ' => u z θ') hslice h0 h2).1
  have hsub : Set.Ioo 0 (Real.pi / 4) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hbig : IntegrableOn
      (fun θ => 4 * ((deriv (fun t => u z t) θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ)
        + 4 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
      (Set.Ioo 0 (Real.pi / 4)) :=
    MeasureTheory.Integrable.add
      (MeasureTheory.Integrable.const_mul (MeasureTheory.IntegrableOn.mono_set h1 hsub) 4)
      (MeasureTheory.Integrable.const_mul (MeasureTheory.IntegrableOn.mono_set h0 hsub) 4)
  have hmeas : AEStronglyMeasurable
      (fun θ => (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 4))) := by
    have hcont : ContinuousOn (deriv (fun t => u z t / Real.cos t))
        (Set.Ioo 0 (Real.pi / 2)) :=
      (Work.FTS.EllipticEst.TT.contDiffOn_divCos hslice).continuousOn_deriv_of_isOpen isOpen_Ioo
        (by norm_num)
    have h1' : AEStronglyMeasurable (deriv (fun t => u z t / Real.cos t))
        (volume.restrict (Set.Ioo 0 (Real.pi / 4))) :=
      (hcont.aestronglyMeasurable measurableSet_Ioo).mono_set
        (Set.Ioo_subset_Ioo_right (by linarith [Real.pi_pos]))
    exact (h1'.pow 2).mul (Work.FTS.EllipticEst.TT.measurable_sigEta.aestronglyMeasurable)
  refine hbig.mono' hmeas ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
  have hσθ : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
    Work.FTS.EllipticEst.AngSecond.sig_nonneg
      ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hpt := Work.FTS.EllipticEst.TT.psi_deriv_sq_le hslice hθ
  have hmul : (deriv (fun t => u z t / Real.cos t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ
      ≤ (4 * (deriv (fun t => u z t) θ) ^ 2 + 4 * (u z θ) ^ 2)
        * Work.FTS.EllipticEst.AngSecond.sig θ :=
    mul_le_mul_of_nonneg_right hpt hσθ
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hσθ)]
  nlinarith [hmul]

/-- The upper half `(π/4, π/2)`. -/
private theorem ae_psiDerivSq_upper {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hu : Work.Spaces.HkMem α 0 u)
    (hd : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  -- The angular first-order quantity `U = ∂_θ(tan θ · u)` is again honest.
  set U : ℝ → ℝ → ℝ := fun z θ => deriv (fun θ' => Real.tan θ' * u z θ') θ with hUdef
  have hU : Work.Spaces.HkMem α 0 U := by
    rw [hUdef]
    exact Work.FTS.EllipticEst.H2W.Ae.hkMem_ang1 α u G hA hu hd
  -- Slicewise `σ`-honesty transferred from `HkMem α 0 g` (the `k = 0` integrand).
  have slice_mem : ∀ {g : ℝ → ℝ → ℝ}, Work.Spaces.HkMem α 0 g →
      IntegrableOn (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        Work.Spaces.Iθ := by
    intro g hm
    exact Work.FTS.EllipticEst.TT.integrableOn_sq_mul_sig_of_hkMem (g := g) hz hm
  have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt (by linarith [hθ.1, Real.pi_pos]), le_of_lt hθ.2⟩
  have hUint : IntegrableOn (fun θ => (U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := (slice_mem hU).mono_set hsub
  have hPint : IntegrableOn (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := (slice_mem hu).mono_set hsub
  have hmaj : Integrable
      (fun θ => 4 * ((U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        + 4 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
      (volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :=
    MeasureTheory.Integrable.add (MeasureTheory.Integrable.const_mul hUint 4)
      (MeasureTheory.Integrable.const_mul hPint 4)
  -- a.e. strong measurability of `(ψ')²σ` from the `C¹`-regularity of the slice.
  have hsub' : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun θ hθ => ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hcos_ne : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Real.cos θ ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hslice1 : ContDiffOn ℝ 1 (fun θ' => u z θ') (Set.Ioo 0 (Real.pi / 2)) := by
    have hmap : Set.MapsTo (fun θ' : ℝ => (z, θ')) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ' hθ' => ⟨hz, hθ'⟩
    exact (hA.smooth 1).comp (by fun_prop) hmap
  have hquot : ContDiffOn ℝ 1 (fun θ' => u z θ' / Real.cos θ') (Set.Ioo 0 (Real.pi / 2)) :=
    hslice1.div Real.contDiff_cos.contDiffOn hcos_ne
  have hcontD : ContinuousOn (deriv (fun θ' => u z θ' / Real.cos θ'))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hquot.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcontD' : ContinuousOn (deriv (fun θ' => u z θ' / Real.cos θ'))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hcontD.mono hsub'
  have hsig_cont : ContinuousOn Work.FTS.EllipticEst.AngSecond.sig
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    have hf : ContinuousOn (fun θ => Real.sin (2 * θ)) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    have hne : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
      intro θ hθ
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos]))
    exact hf.rpow_const (p := -(Work.Spaces.eta)) (fun θ hθ => Or.inl (hne θ hθ))
  have haesm : AEStronglyMeasurable
      (fun θ => (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      (volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :=
    ((hcontD'.pow 2).mul hsig_cont).aestronglyMeasurable measurableSet_Ioo
  -- the pointwise bound on `(π/4, π/2)`, where `sin θ ≥ 1/√2`.
  have hpoint : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ
        ≤ 4 * ((U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
          + 4 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    intro θ hθ
    have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hdiff : DifferentiableAt ℝ (fun θ' => u z θ') θ :=
      (hslice1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθI)
    have hid : Real.sin θ * deriv (fun θ' => u z θ' / Real.cos θ') θ = U z θ - u z θ := by
      have h := Work.FTS.EllipticEst.AngSecond.I4_tan_mul_sub_deriv
        (fun θ' => u z θ') hθI hdiff
      rw [← h]
    have hsin2 : (1 / 2 : ℝ) ≤ Real.sin θ ^ 2 := by
      have hmem1 : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, Real.pi_pos], le_of_lt (by linarith [hθ.2, Real.pi_pos])⟩
      have hmem2 : Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have hsin := Real.strictMonoOn_sin hmem2 hmem1 hθ.1
      rw [Real.sin_pi_div_four] at hsin
      have h0 : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
      have hlt := pow_lt_pow_left₀ hsin h0 (by norm_num : (2 : ℕ) ≠ 0)
      have hsq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      linarith [hlt, hsq]
    have hB : (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
        ≤ 4 * (U z θ) ^ 2 + 4 * (u z θ) ^ 2 := by
      have heq : (Real.sin θ) ^ 2 * (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
          = (U z θ - u z θ) ^ 2 := by rw [← hid]; ring
      have hhalf : (1 / 2) * (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
          ≤ (U z θ - u z θ) ^ 2 := by
        rw [← heq]
        nlinarith [hsin2, sq_nonneg (deriv (fun θ' => u z θ' / Real.cos θ') θ)]
      have hB' : (U z θ - u z θ) ^ 2 ≤ 2 * (U z θ) ^ 2 + 2 * (u z θ) ^ 2 := by
        nlinarith [sq_nonneg (U z θ + u z θ)]
      nlinarith [hhalf, hB']
    have hsig : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
      Work.FTS.EllipticEst.AngSecond.sig_nonneg (θ := θ) ⟨le_of_lt hθI.1, le_of_lt hθI.2⟩
    calc (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ
        ≤ (4 * (U z θ) ^ 2 + 4 * (u z θ) ^ 2)
            * Work.FTS.EllipticEst.AngSecond.sig θ :=
          mul_le_mul_of_nonneg_right hB hsig
      _ = 4 * ((U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
            + 4 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg (deriv (fun θ' => u z θ' / Real.cos θ') θ))
      (Work.FTS.EllipticEst.AngSecond.sig_nonneg (θ := θ)
        ⟨le_of_lt (by linarith [hθ.1, Real.pi_pos]), le_of_lt hθ.2⟩))]
  exact hpoint θ hθ

/-- The second slicewise integrability fact, from the two halves. -/
private theorem ae_psiDerivSq_integrable {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hu : Work.Spaces.HkMem α 0 u)
    (hd : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
  integrableOn_Iθ_of_halves (ae_psiDerivSq_lower hA hu hz) (ae_psiDerivSq_upper hA hu hd hz)

/-! ## The fourth slicewise integrability fact: `∫ sin²θ (∂_θ(u z · / cos ·))² σ` -/

private theorem ae_sinSq_psiDerivSq_integrable {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hu : Work.Spaces.HkMem α 0 u)
    (hd : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
  have hD := ae_psiDerivSq_integrable hA hu hd hz
  have hD' : IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * ((deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)) Work.Spaces.Iθ := by
    have hsin : AEStronglyMeasurable (fun θ : ℝ => Real.sin θ ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      ((Real.continuous_sin.pow 2).continuousOn).aestronglyMeasurable measurableSet_Icc
    refine hD.mono' (hsin.mul hD.aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    have hσ : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
      Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
    have hbase : 0 ≤ (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ := mul_nonneg (sq_nonneg _) hσ
    have hsin1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    calc ‖Real.sin θ ^ 2 * ((deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ)‖
        = Real.sin θ ^ 2 * ((deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) :=
          Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hbase)
      _ ≤ (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ := mul_le_of_le_one_left hbase hsin1
  refine hD'.congr_fun (fun θ _ => ?_) measurableSet_Icc
  ring

/-! ## The target -/

theorem aeI4_open : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G → Work.Spaces.HkMem α 0 u →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) →
      Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ)
        (Work.Spaces.pthIter 2 u)
      ≤ Work.FTS.EllipticEst.AngSecond.IP u (Work.Spaces.pthIter 2 u)
        + C * Work.FTS.EllipticEst.AngSecond.IP u u := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.EllipticEst.H2W.I4Open
  refine ⟨C₀, hC₀pos, ?_⟩
  intro α u G hA hu hd
  -- the three honesty statements of the pairing, from the proved `IPMem` bookkeeping
  obtain ⟨-, -, -, hM1, hM2, -⟩ :=
    Work.FTS.EllipticEst.remov.aeIPMemsSlim α u G hA hu hd
  have hM3 : Work.FTS.EllipticEst.AngSecond.IPMem u u :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hu
  have hkey := hC₀ u hA.smooth hA.dirZero hA.dirPi hM1 hM2 hM3
    (fun z hz => ae_psiDivCosSq_integrable hA hu hz)
    (fun z hz => ae_psiDerivSq_integrable hA hu hd hz)
    (fun z hz => Work.FTS.EllipticEst.TT.integrableOn_sq_mul_sig_of_hkMem (g := Work.Spaces.pthIter 2 u)
      hz hA.memAng2)
    (fun z hz => ae_sinSq_psiDerivSq_integrable hA hu hd hz)
  linarith

end

end Work.FTS.EllipticEst.Cores.AeStep2Aux
