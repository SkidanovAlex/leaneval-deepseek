/-
Scratch development file for the assembly of `Work.FTS.EllipticEst.HkNorm_Dz_amgm`.
Not part of the final proof; helper lemmas are moved into the target file as they stabilise.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.DzAmgm.Defs
import Submission.Work.FTS.EllipticEst.HkSq_eq_lintegral
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen
import Submission.Work.FTS.EllipticEst.DzCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.DzAmgm

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Step 1: the identity between the two forms of the pure angular weight -/

/-- On the angular interval `Iθ`, the pure summand of `HkIntegrand` written with the division
`w z / sin(2θ)^{η/2}` equals the same summand written with the product `w z · angZ θ`
(`angZ θ = sin(2θ)^{-η/2}`).  At the two endpoints both sides vanish. -/
theorem mul_angZ_eq_mul_div (z θ x : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    x * Work.Spaces.w z * angZ θ
      = x * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
  rcases eq_or_ne (Real.sin (2 * θ)) 0 with h | h
  · have hη : ((-(Work.Spaces.eta / 2)) : ℝ) ≠ 0 := by
      rw [Work.Spaces.eta]; norm_num
    have hη2 : ((Work.Spaces.eta / 2) : ℝ) ≠ 0 := by
      rw [Work.Spaces.eta]; norm_num
    have hzero : angZ θ = 0 := by rw [angZ, h, Real.zero_rpow hη]
    rw [hzero, mul_zero, h, Real.zero_rpow hη2, div_zero, mul_zero]
  · have hnn : 0 ≤ Real.sin (2 * θ) := by
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
      exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    rw [angZ, div_eq_mul_inv, Real.rpow_neg hnn]
    ring

/-! ## Step 2: a.e. strong measurability of the `z`-slices -/

/-- The `z`-slice of a function continuous on the open quadrant is a.e. strongly measurable on
`Iz = [0,∞)`. -/
theorem aesm_zs (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    MeasureTheory.AEStronglyMeasurable (fun z => g (z, θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun z : ℝ => g (z, θ)) (Set.Ioi 0) :=
    hg.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun z hz => ⟨hz, hθ⟩)
  have h1 : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => g (z, θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  have hset : (Set.Ioi (0 : ℝ)) =ᵐ[MeasureTheory.volume] Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact MeasureTheory.Ioi_ae_eq_Ici
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set hset.symm
  rw [hmeas]
  exact h1

/-! ## Step 3: splitting a finite sum out of the double `lintegral` -/

/-- **Splitting a finite sum of summands continuous on the open quadrant.**  For a finite family
of real functions continuous on `Q0`, the double (`θ`-then-`z`) `lintegral` of the finite sum of
their `ofReal`-lifts is the sum of the individual double `lintegral`s.  Both `ℒ²`-measurability
inputs come from the continuity on `Q0` (the `z`-slices for the inner integral and the joint
a.e. strong measurability for the partial `θ`-integral). -/
theorem lintegral_sum_split {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℝ)
    (hF : ∀ m ∈ s, ContinuousOn (fun p : ℝ × ℝ => F m p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ∑ m ∈ s, ENNReal.ofReal (F m z θ))
      = ∑ m ∈ s, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (F m z θ) := by
  classical
  -- a.e. angle in the open interval
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    have hset : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      refine MeasureTheory.Measure.restrict_congr_set ?_
      rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc.symm
    rw [hset]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  -- the inner integral splits for a.e. angle
  have hsplit : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫⁻ z in Work.Spaces.Iz, ∑ m ∈ s, ENNReal.ofReal (F m z θ))
        = ∑ m ∈ s, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (F m z θ) := by
    filter_upwards [hae] with θ hθ
    exact MeasureTheory.lintegral_finsetSum' s fun m hm =>
      ((aesm_zs _ (hF m hm) hθ).aemeasurable.ennreal_ofReal)
  -- the partial `z`-integrals are a.e. strongly measurable in `θ`
  have hθmeas : ∀ m ∈ s, AEMeasurable
      (fun θ => ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (F m z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro m hm
    have huncurry : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (F m p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      ((Work.Spaces.aesm_of_continuousOn_Qd _ (hF m hm)).aemeasurable).ennreal_ofReal
    exact huncurry.lintegral_prod_left'
  rw [MeasureTheory.lintegral_congr_ae hsplit]
  exact MeasureTheory.lintegral_finsetSum' s hθmeas

/-! ## Step 4: domain conversions -/

theorem lintegral_Iθ_eq_Ioo (f : ℝ → ℝ≥0∞) :
    ∫⁻ θ in Work.Spaces.Iθ, f θ = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), f θ := by
  have h : MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [Work.Spaces.Iθ, h]

theorem lintegral_Iz_eq_Ioi (f : ℝ → ℝ≥0∞) :
    ∫⁻ z in Work.Spaces.Iz, f z = ∫⁻ z in Set.Ioi (0 : ℝ), f z := by
  have h : MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici.symm
  rw [Work.Spaces.Iz, h]

/-- The double integral over `Iθ × Iz` equals the double integral over the open quadrant
(angular variable first). -/
theorem lintegral_prod_eq_open (F : ℝ → ℝ → ℝ≥0∞) :
    (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, F θ z)
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ), F θ z := by
  rw [lintegral_Iθ_eq_Ioo]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  exact lintegral_Iz_eq_Ioi _

/-- The reverse direction of the previous lemma. -/
theorem lintegral_open_eq_prod (F : ℝ → ℝ → ℝ≥0∞) :
    (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ), F θ z)
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, F θ z :=
  (lintegral_prod_eq_open F).symm

/-- The pure summand in the `angZ`-form equals the summand of `HkIntegrand` (division form). -/
theorem pure_ofReal_eq (f : ℝ → ℝ → ℝ) (m : ℕ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    ENNReal.ofReal ((Work.Spaces.DzIter m f z θ * Work.Spaces.w z * angZ θ) ^ 2)
      = ENNReal.ofReal ((Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
  have h1 : Work.Spaces.DzIter m f z θ * Work.Spaces.w z * angZ θ
      = Work.Spaces.DzIter m f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) :=
    mul_angZ_eq_mul_div z θ (Work.Spaces.DzIter m f z θ) hθ
  have h2 : (Work.Spaces.DzIter m f z θ * Work.Spaces.w z * angZ θ) ^ 2
      = (Work.Spaces.DzIter m f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [h1]
  rw [h2]

/-- The mixed summand in the `w · angM`-form equals the summand of `HkIntegrand` (using `Wt`). -/
theorem mixed_ofReal_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (i j : ℕ) (z θ : ℝ) :
    ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ) ^ 2)
      = ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
  have h1 : Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ
      = Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ := by
    rw [mul_assoc]; rfl
  have h2 : (Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ) ^ 2
      = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [h1]
  rw [h2]

/-! ## Step 5: the termwise Agmon–Nirenberg estimate -/

/-- **Termwise AM–GM, pure summands.**  Applying `TermAMGMLintegral` with `V = D_z^m f`,
`wth = angZ` and rewriting `D_z (D_z^m f) = D_z^{m+1} f`,
`z²∂_z²(D_z^m f) = D_z^m (z²∂_z²f)` (`ZsqPz2Comm`) gives the termwise estimate for `TZ`. -/
theorem TZ_termwise (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (f : ℝ → ℝ → ℝ), SmoothOpen f → ∀ (m : ℕ),
      ENNReal.ofReal (α ^ 2) * TZ f (m + 1)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * TZ (zsqPz2 f) m + TZ f m) := by
  intro α hα hα1 f hf m
  have hang : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ angZ θ := fun θ hθ =>
    angZ_nonneg_of_mem (by rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h := hgen α hα hα1 (Work.Spaces.DzIter m f) angZ (hf.DzIter m) hang
  -- the first factor of the left-hand integrand
  have hL : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.DzIter m f) z θ * Work.Spaces.w z
          * angZ θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.DzIter (m + 1) f z θ * Work.Spaces.w z * angZ θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    rw [Work.Spaces.DzIter_succ]
  -- the second-derivative factor of the right-hand side
  have hR2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z θ
          * Work.Spaces.w z * angZ θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.DzIter m (zsqPz2 f) z θ * Work.Spaces.w z * angZ θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hcomm := ZsqPz2Comm f hf m 0 (show (z, θ) ∈ Q0 from ⟨hz, hθ⟩)
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z θ
        = Work.Spaces.DzIter m (zsqPz2 f) z θ := hcomm
    rw [h1]
  rw [hL, hR2] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  exact h

/-- **Termwise AM–GM, mixed summands.**  Applying `TermAMGMLintegral` with
`V = D_z^j D_θ^i f`, `wth = angM α` and rewriting `D_z (D_z^j D_θ^i f) = D_z^{j+1} D_θ^i f`,
`z²∂_z²(D_z^j D_θ^i f) = D_z^j D_θ^i (z²∂_z²f)` (`ZsqPz2Comm`) gives the termwise estimate. -/
theorem TM_termwise (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (f : ℝ → ℝ → ℝ), SmoothOpen f → ∀ (i j : ℕ),
      ENNReal.ofReal (α ^ 2) * TM α f i (j + 1)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) i j + TM α f i j) := by
  intro α hα hα1 f hf i j
  have hang : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ angM α θ := fun θ hθ =>
    angM_nonneg_of_mem (by rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h := hgen α hα hα1 (Work.Spaces.mixed j i f) (angM α) (hf.mixed j i) hang
  have hL : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.mixed j i f) z θ * Work.Spaces.w z
          * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed (j + 1) i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have hdz : Work.Spaces.Dz (Work.Spaces.mixed j i f)
        = Work.Spaces.mixed (j + 1) i f := by
      simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]
    rw [hdz]
    exact mixed_ofReal_eq α f i (j + 1) z θ
  have hR2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed j i f) z θ
          * Work.Spaces.w z * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i (zsqPz2 f) z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hcomm := ZsqPz2Comm f hf j i (show (z, θ) ∈ Q0 from ⟨hz, hθ⟩)
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed j i f) z θ
        = Work.Spaces.mixed j i (zsqPz2 f) z θ := hcomm
    rw [h1, mixed_ofReal_eq α (zsqPz2 f) i j z θ]
  have hR3 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact mixed_ofReal_eq α f i j z θ
  rw [hL, hR2, hR3] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  exact h

/-! ## Step 6: the pure/mixed parts of `HkIntegrand` -/

/-- The pure (`D_z`-) part of `HkIntegrand α k g`, as a real function. -/
def purePart (g : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i g z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The mixed part of `HkIntegrand α k g`, as a real function. -/
def mixedPart (α : ℝ) (g : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
    (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0)

theorem HkIntegrand_eq_parts (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k g z θ = purePart g k z θ + mixedPart α g k z θ := rfl

theorem purePart_nonneg (g : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) : 0 ≤ purePart g k z θ :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

theorem mixedPart_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) : 0 ≤ mixedPart α g k z θ :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> simp [sq_nonneg]

theorem continuousOn_Wt (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by funext p; rfl
  rw [hfun]
  refine hw.mul ?_
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

theorem continuousOn_pureTerm (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) Q0 :=
  (((hg.DzIter i).continuousOn).mul continuousOn_wdivsin_Q0).pow 2

theorem continuousOn_mixedTerm (α : ℝ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) (k i j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
        else 0)) Q0 := by
  by_cases hc : 1 ≤ i ∧ i + j ≤ k
  · simp only [if_pos hc]
    exact (((hg.mixed j i).continuousOn).mul (continuousOn_Wt α)).pow 2
  · simp only [if_neg hc]
    exact continuousOn_const

theorem ofReal_ite_zero {c : Prop} [Decidable c] {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal (if c then x else 0) = if c then ENNReal.ofReal x else 0 := by
  by_cases h : c <;> simp [h]

/-- a.e. angles lie in the open interval. -/
theorem ae_mem_Ioo_theta : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hset : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [hset]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- a.e. radii are positive. -/
theorem ae_mem_Ioi_z : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
    z ∈ Set.Ioi (0 : ℝ) := by
  have hset : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    rw [Work.Spaces.Iz]; exact MeasureTheory.Ioi_ae_eq_Ici.symm
  rw [hset]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-- The family of summands of `HkIntegrand α k g`, indexed by `ℕ ⊕ (ℕ × ℕ)`
(pure indices on the left, mixed indices on the right). -/
def termFamily (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) : ℕ ⊕ (ℕ × ℕ) → ℝ → ℝ → ℝ
  | Sum.inl i => fun z θ => (Work.Spaces.DzIter i g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
  | Sum.inr p => fun z θ => (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
      (Work.Spaces.mixed p.2 p.1 g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)

theorem continuousOn_termFamily (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g)
    (σ : ℕ ⊕ (ℕ × ℕ)) :
    ContinuousOn (fun p : ℝ × ℝ => termFamily α k g σ p.1 p.2) Q0 := by
  rcases σ with i | p
  · exact continuousOn_pureTerm g hg i
  · exact continuousOn_mixedTerm α g hg k p.1 p.2

/-- Summing over a disjoint sum of finsets. -/
theorem sum_disjSum_eq {α β M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β)
    (f : α ⊕ β → M) :
    (∑ σ ∈ s.disjSum t, f σ) = (∑ a ∈ s, f (Sum.inl a)) + (∑ b ∈ t, f (Sum.inr b)) := by
  rw [← Finset.map_inl_disjUnion_map_inr, Finset.sum_disjUnion, Finset.sum_map, Finset.sum_map]
  simp only [Function.Embedding.inl_apply, Function.Embedding.inr_apply]

/-- `ofReal` of a finite sum of nonnegative reals, in one index. -/
theorem ofReal_sum_range (k : ℕ) (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i) :
    (∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (h i))
      = ENNReal.ofReal (∑ i ∈ Finset.range (k + 1), h i) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hh i)]

/-- `ofReal` of a finite double sum of nonnegative reals. -/
theorem ofReal_sum_range₂ (k : ℕ) (h : ℕ → ℕ → ℝ) (hh : ∀ i j, 0 ≤ h i j) :
    (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), ENNReal.ofReal (h i j))
      = ENNReal.ofReal (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), h i j) := by
  have hinner : ∀ i, (∑ j ∈ Finset.range (k + 1), ENNReal.ofReal (h i j))
      = ENNReal.ofReal (∑ j ∈ Finset.range (k + 1), h i j) := fun i =>
    ofReal_sum_range k (h i) (hh i)
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  exact ofReal_sum_range k (fun i => ∑ j ∈ Finset.range (k + 1), h i j)
    (fun i => Finset.sum_nonneg fun j _ => hh i j)

/-- The sum of the `ofReal`-lifts of the summand family is the `ofReal` of `HkIntegrand`. -/
theorem sum_termFamily (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (∑ σ ∈ (Finset.range (k + 1)).disjSum
        ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))),
        ENNReal.ofReal (termFamily α k g σ z θ))
      = ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ) := by
  rw [sum_disjSum_eq]
  have hpure : (∑ a ∈ Finset.range (k + 1), ENNReal.ofReal
        (termFamily α k g (Sum.inl a) z θ)) = ENNReal.ofReal (purePart g k z θ) := by
    simp only [termFamily, purePart]
    exact ofReal_sum_range k _ (fun a => sq_nonneg _)
  have hmixed : (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)), ENNReal.ofReal
        (termFamily α k g (Sum.inr p) z θ)) = ENNReal.ofReal (mixedPart α g k z θ) := by
    rw [Finset.sum_product]
    simp only [termFamily, mixedPart]
    exact ofReal_sum_range₂ k _ (fun i j => by split_ifs <;> simp [sq_nonneg])
  rw [hpure, hmixed, ← ENNReal.ofReal_add (purePart_nonneg g k z θ)
    (mixedPart_nonneg α g k z θ), ← HkIntegrand_eq_parts]

/-- **Decomposition of `LkSq` into its individual summands.**  The honest `lintegral` of the
`H^k`-integrand of `g` is the sum of the honest sizes of its pure and mixed summands. -/
theorem LkSq_eq_sum (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    LkSq α k g
      = (∑ i ∈ Finset.range (k + 1), TZ g i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α g p.1 p.2 else 0) := by
  classical
  have hsplit := lintegral_sum_split
    ((Finset.range (k + 1)).disjSum ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))))
    (termFamily α k g) (fun σ _ => continuousOn_termFamily α k g hg σ)
  have hLHS : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
        ∑ σ ∈ (Finset.range (k + 1)).disjSum
          ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))),
          ENNReal.ofReal (termFamily α k g σ z θ)) = LkSq α k g := by
    show (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
        ∑ σ ∈ (Finset.range (k + 1)).disjSum
          ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))),
          ENNReal.ofReal (termFamily α k g σ z θ))
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact sum_termFamily α k g z θ
  rw [hLHS] at hsplit
  rw [hsplit]
  rw [sum_disjSum_eq]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    show (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
        (termFamily α k g (Sum.inl i) z θ)) = TZ g i
    rw [TZ]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_Ioo_theta] with θ hθ
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact (pure_ofReal_eq g i z θ (by
      rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)).symm
  · refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
    · rw [if_pos hc]
      show (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
        (termFamily α k g (Sum.inr p) z θ)) = TM α g p.1 p.2
      rw [TM]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [termFamily, if_pos hc]
    · rw [if_neg hc]
      have hzero : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (termFamily α k g (Sum.inr p) z θ)) = 0 := by
        have hterm : termFamily α k g (Sum.inr p) = fun _ _ => (0 : ℝ) := by
          funext z θ; simp only [termFamily, if_neg hc]
        rw [hterm]
        simp
      rw [hzero]

/-! ## Step 7: re-indexing `TZ` and `TM` of `D_z f` -/

theorem DzIter_succ_eq (m : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter (m + 1) f = Work.Spaces.DzIter m (Work.Spaces.Dz f) := by
  rw [Work.Spaces.DzIter_add_right m 1 f]
  rfl

/-- `z²∂_z² h = D_z² h − D_z h` on the open quadrant, for `h` smooth there. -/
theorem zsqPz2_eq_sub (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    zsqPz2 g z θ = Work.Spaces.DzIter 2 g z θ - Work.Spaces.Dz g z θ := by
  have h1 : DifferentiableAt ℝ (fun z' => g z' θ) z := (hg.hasDerivAt_slice hθ hz).differentiableAt
  have h2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pz g z' θ) z :=
    (hg.hasDerivAt_slice_pzIter 1 hθ hz).differentiableAt
  simpa only [zsqPz2] using Work.FTS.EllipticEst.zsq_pzIter2_eq g h1 h2

/-- `z²∂_z² (D_z g) = D_z (z²∂_z² g)` on the open quadrant, for smooth `g`. -/
theorem zsqPz2_Dz (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    Set.EqOn (Function.uncurry (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.Dz g) z θ))
      (Function.uncurry (Work.Spaces.Dz (zsqPz2 g))) Q0 := by
  intro y hy
  obtain ⟨hz, hθ⟩ := hy
  -- the identity `z²∂² h = D_z² h - D_z h` at `y` for `h = D_z g`
  have e1 : zsqPz2 (Work.Spaces.Dz g) y.1 y.2
      = Work.Spaces.DzIter 3 g y.1 y.2 - Work.Spaces.DzIter 2 g y.1 y.2 := by
    have h := zsqPz2_eq_sub (Work.Spaces.Dz g) hg.Dz hz hθ
    have h1 : Work.Spaces.DzIter 2 (Work.Spaces.Dz g) = Work.Spaces.DzIter 3 g :=
      (Work.Spaces.DzIter_add_right 2 1 g).symm
    have h2 : Work.Spaces.Dz (Work.Spaces.Dz g) = Work.Spaces.DzIter 2 g := rfl
    rw [h, h1, h2]
  -- the same identity, as an `EqOn` with the difference function
  have hcongr : Set.EqOn (Function.uncurry (zsqPz2 g))
      (Function.uncurry (fun z θ => Work.Spaces.DzIter 2 g z θ - Work.Spaces.Dz g z θ)) Q0 := by
    intro y' hy'
    obtain ⟨hz', hθ'⟩ := hy'
    exact zsqPz2_eq_sub g hg hz' hθ'
  have hDz : Work.Spaces.Dz (zsqPz2 g) y.1 y.2
      = Work.Spaces.Dz (fun z θ => Work.Spaces.DzIter 2 g z θ - Work.Spaces.Dz g z θ)
          y.1 y.2 := by
    have hpz := Work.Spaces.pz_congr_of_isOpen isOpen_Q0 hcongr
      (show y ∈ Q0 from ⟨hz, hθ⟩)
    show y.1 * Work.Spaces.pz (zsqPz2 g) y.1 y.2
      = y.1 * Work.Spaces.pz (fun z θ => Work.Spaces.DzIter 2 g z θ - Work.Spaces.Dz g z θ)
          y.1 y.2
    rw [hpz]
  -- linearity of `D_z`
  have hlin : Work.Spaces.Dz (fun z θ => Work.Spaces.DzIter 2 g z θ - Work.Spaces.Dz g z θ)
        y.1 y.2
      = Work.Spaces.DzIter 3 g y.1 y.2 - Work.Spaces.DzIter 2 g y.1 y.2 := by
    have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter 2 g z' y.2) y.1 :=
      (hg.hasDerivAt_slice_DzIter 2 hθ hz).differentiableAt
    have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.Dz g z' y.2) y.1 :=
      (hg.hasDerivAt_slice_DzIter 1 hθ hz).differentiableAt
    have hpz : Work.Spaces.pz (fun z θ => Work.Spaces.DzIter 2 g z θ - Work.Spaces.Dz g z θ)
          y.1 y.2
        = Work.Spaces.pz (Work.Spaces.DzIter 2 g) y.1 y.2
          - Work.Spaces.pz (Work.Spaces.Dz g) y.1 y.2 := by
      simp only [Work.Spaces.pz]
      exact deriv_sub (by simpa only [Work.Spaces.pz] using hd1)
        (by simpa only [Work.Spaces.pz] using hd2)
    have h3 : Work.Spaces.DzIter 3 g y.1 y.2
        = y.1 * Work.Spaces.pz (Work.Spaces.DzIter 2 g) y.1 y.2 := rfl
    have h2 : Work.Spaces.DzIter 2 g y.1 y.2
        = y.1 * Work.Spaces.pz (Work.Spaces.Dz g) y.1 y.2 := rfl
    show y.1 * Work.Spaces.pz (fun z θ => Work.Spaces.DzIter 2 g z θ - Work.Spaces.Dz g z θ)
        y.1 y.2
      = Work.Spaces.DzIter 3 g y.1 y.2 - Work.Spaces.DzIter 2 g y.1 y.2
    rw [hpz, h3, h2]
    ring
  show zsqPz2 (Work.Spaces.Dz g) y.1 y.2 = Work.Spaces.Dz (zsqPz2 g) y.1 y.2
  rw [hDz, hlin, e1]

theorem TZ_Dz (f : ℝ → ℝ → ℝ) (i : ℕ) :
    TZ (Work.Spaces.Dz f) i = TZ f (i + 1) := by
  simp only [TZ]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  rw [DzIter_succ_eq]

theorem TM_Dz_of_comm (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hcomm : ∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
      Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
        = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ) (a b : ℕ) :
    TM α (Work.Spaces.Dz f) a b = TM α f a (b + 1) := by
  simp only [TM]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_Ioo_theta] with θ hθ
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_Ioi_z] with z hz
  have hpoint : Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
      = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ := hcomm a z θ ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter b (Work.Spaces.Dz (Work.Spaces.DthIter a f)) z θ :=
    SmoothOpen.DzIter_congr (F := Work.Spaces.DthIter a (Work.Spaces.Dz f))
      (G := Work.Spaces.Dz (Work.Spaces.DthIter a f))
      (fun z' θ' hz' h1 h2 => hcomm a z' θ' ⟨hz', ⟨h1, h2⟩⟩) b z θ hz hθ.1 hθ.2
  have hgoal : Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ
      = Work.Spaces.mixed (b + 1) a f z θ := by
    simp only [Work.Spaces.mixed] at hcongr ⊢
    rw [hcongr, DzIter_succ_eq]
  rw [hgoal]

/-- Distributing a constant over a conditionally-defined finite sum of pairs. -/
theorem sum_ite_mul_split {s : Finset (ℕ × ℕ)} {k : ℕ} (B Cc : ℝ≥0∞)
    (x y : ℕ × ℕ → ℝ≥0∞) :
    (∑ p ∈ s, (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then B * (Cc * x p + y p) else 0))
      = (B * Cc) * (∑ p ∈ s, (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then x p else 0))
        + B * (∑ p ∈ s, (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then y p else 0)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
  · rw [if_pos hc, if_pos hc, if_pos hc]; ring
  · rw [if_neg hc, if_neg hc, if_neg hc]; ring

/-! ## Step 8: the main `LkSq` inequality -/

/-! ## Step 8: the main `LkSq` inequality -/

/-- The second radial derivative of a smooth-on-the-quadrant function is smooth. -/
theorem SmoothOpen_zsqPz2 (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f) : SmoothOpen (zsqPz2 f) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2) Q0 := by
    fun_prop
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 f p.1 p.2) Q0 := hf.pzIter 2
  have h3 := h1.mul h2
  have hfun : Function.uncurry (zsqPz2 f)
      = fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 f p.1 p.2 := by
    funext p; rfl
  rw [SmoothOpen, hfun]
  exact h3

private theorem mul_ite_pos {c : Prop} [Decidable c] {x y : ℝ≥0∞} (hy : y = 0) :
    y * (if c then x else 0) = if c then y * x else 0 := by
  by_cases h : c <;> simp [h, hy]

/-- **The `θ`-integrated radial interpolation for `D_z f`, at the level of the honest
`lintegral`s.** -/
theorem LkSq_Dz_le (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (k : ℕ) (f : ℝ → ℝ → ℝ),
      (∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
        Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
          = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ) →
      SmoothOpen f →
      ENNReal.ofReal (α ^ 2) * LkSq α k (Work.Spaces.Dz f)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * LkSq α k (zsqPz2 f) + LkSq α k f) := by
  intro α hα hα1 k f hcomm hf
  have hDz : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
  have hQ : SmoothOpen (zsqPz2 f) := SmoothOpen_zsqPz2 f hf
  have hdec : LkSq α k (Work.Spaces.Dz f)
      = (∑ i ∈ Finset.range (k + 1), TZ f (i + 1))
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0) := by
    rw [LkSq_eq_sum α k (Work.Spaces.Dz f) hDz]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => TZ_Dz f i
    · refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
      · rw [if_pos hc, if_pos hc, TM_Dz_of_comm α f hcomm p.1 p.2]
      · rw [if_neg hc, if_neg hc]
  have hdecQ : LkSq α k (zsqPz2 f)
      = (∑ i ∈ Finset.range (k + 1), TZ (zsqPz2 f) i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α (zsqPz2 f) p.1 p.2 else 0) :=
    LkSq_eq_sum α k (zsqPz2 f) hQ
  have hdecf : LkSq α k f
      = (∑ i ∈ Finset.range (k + 1), TZ f i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 p.2 else 0) :=
    LkSq_eq_sum α k f hf
  -- the termwise bounds
  have hT : ∀ i ∈ Finset.range (k + 1), ENNReal.ofReal (α ^ 2) * TZ f (i + 1)
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * TZ (zsqPz2 f) i + TZ f i) :=
    fun i _ => TZ_termwise C1 hC1 hgen α hα hα1 f hf i
  have hM : ∀ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
      (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then ENNReal.ofReal (α ^ 2) * TM α f p.1 (p.2 + 1) else 0)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
              ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2 else 0) := by
    intro p _
    by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
    · rw [if_pos hc, if_pos hc]
      exact TM_termwise C1 hC1 hgen α hα hα1 f hf p.1 p.2
    · rw [if_neg hc, if_neg hc, mul_zero]
  -- the two sums
  have hS1le : ENNReal.ofReal (α ^ 2) * (∑ i ∈ Finset.range (k + 1), TZ f (i + 1))
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∑ i ∈ Finset.range (k + 1), TZ (zsqPz2 f) i)
            + (∑ i ∈ Finset.range (k + 1), TZ f i)) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum hT) (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.mul_sum]
  have hS2le : ENNReal.ofReal (α ^ 2)
        * (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0))
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4)
              * (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
                  (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α (zsqPz2 f) p.1 p.2 else 0))
            + (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
                  (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 p.2 else 0))) := by
    rw [Finset.mul_sum]
    have hstep : (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
          ENNReal.ofReal (α ^ 2) *
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0))
        = ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
              then ENNReal.ofReal (α ^ 2) * TM α f p.1 (p.2 + 1) else 0) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc, mul_zero]
    rw [hstep]
    refine le_trans (Finset.sum_le_sum hM) (le_of_eq ?_)
    have hflat : ∀ p : ℕ × ℕ,
        ENNReal.ofReal (C1 ^ 2) * (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
            ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2 else 0)
          = (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then ENNReal.ofReal (C1 ^ 2) *
                (ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2)
              else 0) := by
      intro p; by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k <;> simp [hc]
    rw [Finset.sum_congr rfl (fun p _ => hflat p)]
    rw [sum_ite_mul_split (k := k) (ENNReal.ofReal (C1 ^ 2)) (ENNReal.ofReal (α ^ 4))
      (fun p => TM α (zsqPz2 f) p.1 p.2) (fun p => TM α f p.1 p.2)]
    rw [mul_add]
    ring
  -- combine
  rw [hdec, mul_add]
  refine le_trans (add_le_add hS1le hS2le) (le_of_eq ?_)
  rw [hdecQ, hdecf]
  ring

/-! ## Step 9: the bridges between `HkSq` and `LkSq` -/

/-- The `ofReal` of a Bochner integral of a nonnegative function is dominated by the
`lintegral` of the `ofReal`-lift. -/
theorem ofReal_integral_le_lintegral (s : Set ℝ) (u : ℝ → ℝ) (hu : ∀ θ, 0 ≤ u θ) :
    ENNReal.ofReal (∫ θ in s, u θ) ≤ ∫⁻ θ in s, ENNReal.ofReal (u θ) := by
  by_cases hg : IntegrableOn u s
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall hu)]
  · rw [MeasureTheory.integral_undef hg]; simp

/-- The uncurried `H^k`-integrand is a.e. strongly measurable for the product of the restricted
measures (in either order). -/
theorem aesm_HkIntegrand_prod (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  ((Work.Spaces.aesm_of_continuousOn_Qd _ (hg.continuousOn_HkIntegrand α k)).aemeasurable).ennreal_ofReal

theorem HkSq_forall_smooth (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  fun n => (smoothOpen_iff_forall g).mp hg n

/-- `LkSq` written as the `z`-integral of the `ofReal` of the `θ`-integral. -/
theorem LkSq_eq_theta_integral (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g)
    (hmem : Work.Spaces.HkMem α k g) :
    LkSq α k g = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := by
  have hswap : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ) :=
    MeasureTheory.lintegral_lintegral_swap
      ((aesm_HkIntegrand_prod α k g hg).prod_swap)
  have heq : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from
      measurableSet_Ici)] with z hz
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)).symm
  rw [LkSq, hswap, heq]

/-- **`LkSq` is the honest version of `HkSq`** (the `≤` direction, under finiteness of `LkSq`). -/
theorem HkSq_le_LkSq (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g)
    (hfin : LkSq α k g ≠ ⊤) :
    Work.Spaces.HkSq α k g ≤ (LkSq α k g).toReal := by
  have hforall := HkSq_forall_smooth g hg
  have hswap : LkSq α k g
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ) := by
    rw [LkSq]
    exact MeasureTheory.lintegral_lintegral_swap
      ((aesm_HkIntegrand_prod α k g hg).prod_swap)
  have hAB : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ) :=
    lintegral_mono fun z => ofReal_integral_le_lintegral _ _ fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k g z θ
  have hfin' : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)) ≠ ⊤ := by
    rw [← hswap]; exact hfin
  calc Work.Spaces.HkSq α k g
      = ENNReal.toReal (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)) :=
        Work.FTS.EllipticEst.HkSq_eq_lintegral α k g hforall
    _ ≤ ENNReal.toReal (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)) :=
        ENNReal.toReal_mono hfin' hAB
    _ = (LkSq α k g).toReal := by rw [hswap]

/-- Honesty of `LkSq` from `HkMem`. -/
theorem LkSq_lt_top (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g)
    (hmem : Work.Spaces.HkMem α k g) : LkSq α k g < ⊤ := by
  rw [LkSq_eq_theta_integral α k g hg hmem]
  exact MeasureTheory.Integrable.lintegral_lt_top hmem.2

/-- Under honesty (`HkMem`), `LkSq` is the `ofReal` of `HkSq`. -/
theorem LkSq_eq_ofReal_HkSq (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g)
    (hmem : Work.Spaces.HkMem α k g) :
    LkSq α k g = ENNReal.ofReal (Work.Spaces.HkSq α k g) := by
  have hforall := HkSq_forall_smooth g hg
  rw [LkSq_eq_theta_integral α k g hg hmem,
    Work.FTS.EllipticEst.HkSq_eq_lintegral α k g hforall]
  have hA : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)) < ⊤ := by
    rw [← LkSq_eq_theta_integral α k g hg hmem]
    exact LkSq_lt_top α k g hg hmem
  exact (ENNReal.ofReal_toReal (ne_of_lt hA)).symm

/-- `√(x+y) ≤ √x + √y` for nonnegative reals. -/
theorem sqrt_add_le_sqrt (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sq_sqrt hy
    have h3 : 0 ≤ Real.sqrt x * Real.sqrt y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

/-! ## Step 10: from the `LkSq` inequality to the norm inequality -/

/-- The commutation hypothesis of `LkSq_Dz_le`, from the coprime theorem
`DthIterDzCommOpen`. -/
theorem comm_hyp (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f) :
    ∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
      Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
        = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ :=
  fun a z θ h => (DthIterDzCommOpen f hf a h).symm

/-- Finiteness of `LkSq (D_z f)` from the `LkSq` inequality. -/
theorem LkSq_Dz_lt_top (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f) (hmQ : Work.Spaces.HkMem α k (zsqPz2 f)) :
    LkSq α k (Work.Spaces.Dz f) < ⊤ := by
  have hQfin : LkSq α k (zsqPz2 f) < ⊤ := LkSq_lt_top α k _ (SmoothOpen_zsqPz2 f hf) hmQ
  have hffin : LkSq α k f < ⊤ := LkSq_lt_top α k f hf hmf
  have h := LkSq_Dz_le C1 hC1 hgen α hα hα1 k f (comm_hyp f hf) hf
  have hfin : ENNReal.ofReal (C1 ^ 2) *
      (ENNReal.ofReal (α ^ 4) * LkSq α k (zsqPz2 f) + LkSq α k f) < ⊤ := by
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQfin, hffin⟩
  have hlt : ENNReal.ofReal (α ^ 2) * LkSq α k (Work.Spaces.Dz f) < ⊤ := lt_of_le_of_lt h hfin
  have hpos : ENNReal.ofReal (α ^ 2) ≠ 0 := by
    simpa using (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < α ^ 2)).ne'
  rcases ENNReal.mul_lt_top_iff.mp hlt with ⟨-, h2⟩ | h0 | h0
  · exact h2
  · exact absurd h0 hpos
  · exact lt_top_iff_ne_top.mpr (by simp [h0])
/-- **The norm inequality**, given the honesty of `D_z f`. -/
theorem HkNorm_Dz_le_of (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f) (hmQ : Work.Spaces.HkMem α k (zsqPz2 f))
    (hmDz : Work.Spaces.HkMem α k (Work.Spaces.Dz f)) :
    α * Work.Spaces.HkNorm α k (Work.Spaces.Dz f)
      ≤ C1 * (Work.Spaces.HkNorm α k f + α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f)) := by
  have hDzSm : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
  have hQSm : SmoothOpen (zsqPz2 f) := SmoothOpen_zsqPz2 f hf
  have hDzfin := LkSq_Dz_lt_top C1 hC1 hgen α hα hα1 k f hf hmf hmQ
  have hQfin : LkSq α k (zsqPz2 f) < ⊤ := LkSq_lt_top α k _ hQSm hmQ
  have hffin : LkSq α k f < ⊤ := LkSq_lt_top α k f hf hmf
  -- (★) in terms of `HkSq`
  have h := LkSq_Dz_le C1 hC1 hgen α hα hα1 k f (comm_hyp f hf) hf
  rw [LkSq_eq_ofReal_HkSq α k (Work.Spaces.Dz f) hDzSm hmDz,
    LkSq_eq_ofReal_HkSq α k (zsqPz2 f) hQSm hmQ,
    LkSq_eq_ofReal_HkSq α k f hf hmf] at h
  have hnn : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz f) :=
    Work.Spaces.HkSq_nonneg α k _
  have hnnQ : 0 ≤ Work.Spaces.HkSq α k (zsqPz2 f) := Work.Spaces.HkSq_nonneg α k _
  have hnnf : 0 ≤ Work.Spaces.HkSq α k f := Work.Spaces.HkSq_nonneg α k f
  have hL : ENNReal.ofReal (α ^ 2) * ENNReal.ofReal (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      = ENNReal.ofReal (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 2)]
  have hR : ENNReal.ofReal (C1 ^ 2) * (ENNReal.ofReal (α ^ 4) *
        ENNReal.ofReal (Work.Spaces.HkSq α k (zsqPz2 f)) + ENNReal.ofReal (Work.Spaces.HkSq α k f))
      = ENNReal.ofReal (C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)
          + Work.Spaces.HkSq α k f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C1 ^ 2),
      ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)) hnnf,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 4)]
  rw [hL, hR] at h
  have hsq : α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)
      ≤ C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  -- take square roots
  have hsqrt : α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      ≤ C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) := by
    have h1 : α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
        = Real.sqrt (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)) := by
      rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα.le]
    have h2 : C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
        = Real.sqrt (C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)
            + Work.Spaces.HkSq α k f)) := by
      rw [Real.sqrt_mul (sq_nonneg C1), Real.sqrt_sq hC1.le]
    rw [h1, h2]
    exact Real.sqrt_le_sqrt hsq
  have hf1 : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f))
      = α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ α ^ 4), Work.Spaces.HkNorm,
      show Real.sqrt (α ^ 4) = α ^ 2 by
        rw [show α ^ 4 = (α ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ α ^ 2)]]
  have hadd : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
      ≤ α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f := by
    calc Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
        ≤ Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f))
          + Real.sqrt (Work.Spaces.HkSq α k f) :=
          sqrt_add_le_sqrt _ _ (by positivity) (Work.Spaces.HkSq_nonneg α k f)
      _ = α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f := by
          rw [hf1]
          rfl
  calc α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      ≤ C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) := hsqrt
    _ ≤ C1 * (α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f) :=
        mul_le_mul_of_nonneg_left hadd (le_of_lt hC1)
    _ = C1 * (Work.Spaces.HkNorm α k f + α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f)) := by ring

/-! ## Step 11: pointwise decomposition of the `H^k`-integrand of `D_z f` -/

/-- `D_z² X = z²∂_z²X + D_z X` on the open quadrant. -/
theorem DzIter_two_decomp (X : ℝ → ℝ → ℝ) (hX : SmoothOpen X) :
    Set.EqOn (Function.uncurry (fun z θ => Work.Spaces.DzIter 2 X z θ
        - (zsqPz2 X z θ + Work.Spaces.Dz X z θ))) (fun _ : ℝ × ℝ => (0 : ℝ)) Q0 := by
  intro y hy
  obtain ⟨hz, hθ⟩ := hy
  have h := zsqPz2_eq_sub X hX hz hθ
  show Work.Spaces.DzIter 2 X y.1 y.2
    - (zsqPz2 X y.1 y.2 + Work.Spaces.Dz X y.1 y.2) = 0
  rw [h]; ring

/-- `D_z^{m+2} X = D_z^m (z²∂_z²X) + D_z^{m+1} X` on the open quadrant. -/
theorem DzIter_add_two_decomp (X : ℝ → ℝ → ℝ) (hX : SmoothOpen X) (m : ℕ) :
    Set.EqOn (Function.uncurry (fun z θ => Work.Spaces.DzIter (m + 2) X z θ
        - (Work.Spaces.DzIter m (zsqPz2 X) z θ + Work.Spaces.DzIter (m + 1) X z θ)))
      (fun _ : ℝ × ℝ => (0 : ℝ)) Q0 := by
  intro y hy
  obtain ⟨hz, hθ⟩ := hy
  have hcongr : Work.Spaces.DzIter m (Work.Spaces.DzIter 2 X) y.1 y.2
      = Work.Spaces.DzIter m (fun z θ => zsqPz2 X z θ + Work.Spaces.Dz X z θ) y.1 y.2 :=
    SmoothOpen.DzIter_congr (F := Work.Spaces.DzIter 2 X)
      (G := fun z θ => zsqPz2 X z θ + Work.Spaces.Dz X z θ)
      (fun z' θ' hz' h1 h2 => by
        have h := DzIter_two_decomp X hX (show (z', θ') ∈ Q0 from ⟨hz', ⟨h1, h2⟩⟩)
        simpa using sub_eq_zero.mp h)
      m y.1 y.2 hz hθ.1 hθ.2
  have hadd : Work.Spaces.DzIter m (fun z θ => zsqPz2 X z θ + Work.Spaces.Dz X z θ) y.1 y.2
      = Work.Spaces.DzIter m (zsqPz2 X) y.1 y.2
        + Work.Spaces.DzIter m (Work.Spaces.Dz X) y.1 y.2 :=
    SmoothOpen.DzIter_add (SmoothOpen_zsqPz2 X hX) hX.Dz m y.1 y.2 hz hθ.1 hθ.2
  have harith : Work.Spaces.DzIter (m + 2) X y.1 y.2
      = Work.Spaces.DzIter m (Work.Spaces.DzIter 2 X) y.1 y.2 := by
    rw [Work.Spaces.DzIter_add_right m 2 X]
  have hlast : Work.Spaces.DzIter m (Work.Spaces.Dz X) y.1 y.2
      = Work.Spaces.DzIter (m + 1) X y.1 y.2 := by
    rw [← DzIter_succ_eq]
  show Work.Spaces.DzIter (m + 2) X y.1 y.2
    - (Work.Spaces.DzIter m (zsqPz2 X) y.1 y.2 + Work.Spaces.DzIter (m + 1) X y.1 y.2) = 0
  rw [harith, hcongr, hadd, hlast]
  ring

/-- Pointwise form of the re-indexing of a mixed derivative of `D_z f` under the commutation
hypothesis `D_θ^a (D_z f) = D_z (D_θ^a f)`. -/
theorem mixed_Dz_eq_of_comm (f : ℝ → ℝ → ℝ)
    (hc : ∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
      Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
        = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ)
    (j i : ℕ) {z θ : ℝ} (hQ : (z, θ) ∈ Q0) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  obtain ⟨hz, hθ⟩ := hQ
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    SmoothOpen.DzIter_congr
      (F := Work.Spaces.DthIter i (Work.Spaces.Dz f))
      (G := Work.Spaces.Dz (Work.Spaces.DthIter i f))
      (fun z' θ' hz' h1 h2 => hc i z' θ' ⟨hz', h1, h2⟩) j z θ hz hθ.1 hθ.2
  simp only [Work.Spaces.mixed] at hcongr ⊢
  rw [hcongr, DzIter_succ_eq]

/-- Pointwise form of the commutation hypothesis itself. -/
theorem DthIter_eq_of_comm (f : ℝ → ℝ → ℝ)
    (hc : ∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
      Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
        = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ)
    (i : ℕ) {z θ : ℝ} (hQ : (z, θ) ∈ Q0) :
    Work.Spaces.DthIter i (Work.Spaces.Dz f) z θ
      = Work.Spaces.Dz (Work.Spaces.DthIter i f) z θ := hc i z θ hQ

/-- The decomposition of a top-order mixed derivative: for `j ≥ 1`,
`mixed (j+1) i f = mixed (j-1) i (z²∂_z²f) + mixed j i f` on the open quadrant. -/
theorem mixed_succ_decomp (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (j i : ℕ) (hj : 1 ≤ j) {z θ : ℝ} (hQ : (z, θ) ∈ Q0) :
    Work.Spaces.mixed (j + 1) i f z θ
      = Work.Spaces.mixed (j - 1) i (zsqPz2 f) z θ + Work.Spaces.mixed j i f z θ := by
  have hz : 0 < z := hQ.1
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := hQ.2
  have h := DzIter_add_two_decomp (Work.Spaces.DthIter i f) (hf.DthIter i) (j - 1) hQ
  have hz' : Work.Spaces.DzIter (j - 1 + 2) (Work.Spaces.DthIter i f) z θ
      = Work.Spaces.DzIter (j - 1) (zsqPz2 (Work.Spaces.DthIter i f)) z θ
        + Work.Spaces.DzIter (j - 1 + 1) (Work.Spaces.DthIter i f) z θ := by
    have h'' : (fun z θ => Work.Spaces.DzIter (j - 1 + 2) (Work.Spaces.DthIter i f) z θ
        - (Work.Spaces.DzIter (j - 1) (zsqPz2 (Work.Spaces.DthIter i f)) z θ
          + Work.Spaces.DzIter (j - 1 + 1) (Work.Spaces.DthIter i f) z θ)) z θ = 0 := h
    exact sub_eq_zero.mp h''
  have hcongr : Work.Spaces.DzIter (j - 1) (zsqPz2 (Work.Spaces.DthIter i f)) z θ
      = Work.Spaces.DzIter (j - 1) (Work.Spaces.DthIter i (zsqPz2 f)) z θ :=
    SmoothOpen.DzIter_congr
      (F := zsqPz2 (Work.Spaces.DthIter i f))
      (G := Work.Spaces.DthIter i (zsqPz2 f))
      (fun z' θ' hz' h1 h2 => by
        have hh := ZsqPz2Comm f hf 0 i (show (z', θ') ∈ Q0 from ⟨hz', h1, h2⟩)
        change z' ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DthIter i f) z' θ'
          = Work.Spaces.DthIter i (zsqPz2 f) z' θ' at hh
        exact hh)
      (j - 1) z θ hz hθ.1 hθ.2
  have hj2 : j - 1 + 2 = j + 1 := by omega
  have hj1 : j - 1 + 1 = j := by omega
  rw [hj2, hj1] at hz'
  simp only [Work.Spaces.mixed]
  rw [hz', hcongr]

/-- `1 ≤ 4 (k+2)²`. -/
theorem four_mul_sq_ge_one (k : ℕ) : (1 : ℝ) ≤ 4 * (k + 2) ^ 2 := by
  have hk : (2 : ℝ) ≤ (k : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hmul : (2 : ℝ) * 2 ≤ ((k : ℝ) + 2) * ((k : ℝ) + 2) :=
    mul_le_mul hk hk (by norm_num) (by linarith)
  nlinarith [hmul]

/-- `2 ≤ 4 (k+2)²`. -/
theorem four_mul_sq_ge_two (k : ℕ) : (2 : ℝ) ≤ 4 * (k + 2) ^ 2 := by
  have hk : (2 : ℝ) ≤ (k : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hmul : (2 : ℝ) * 2 ≤ ((k : ℝ) + 2) * ((k : ℝ) + 2) :=
    mul_le_mul hk hk (by norm_num) (by linarith)
  nlinarith [hmul]

/-- The `H^k`-integrand of `D_z f` is dominated (a.e. in the angle, at every `z ∈ Iz`) by the
`H^k`-integrands of `f` and `z²∂_z²f` together with the two "order one" families. -/
theorem HkIntegrand_Dz_le_ae (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hc : ∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
      Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
        = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ)
    (hzsq : ∀ (m i : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
      z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z θ
        = Work.Spaces.mixed m i (zsqPz2 f) z θ)
    {z : ℝ} (hzI : z ∈ Work.Spaces.Iz) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ
        ≤ 4 * (k + 2) ^ 2 * (Work.Spaces.HkIntegrand α k f z θ
            + Work.Spaces.HkIntegrand α k (zsqPz2 f) z θ
            + ((Work.Spaces.Dz f z θ * (Work.Spaces.w z
                  / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              + ∑ i ∈ Finset.range (k + 1), (if 1 ≤ i then
                  (Work.Spaces.DthIter i (Work.Spaces.Dz f) z θ * Work.Spaces.Wt α z θ) ^ 2
                else 0))) := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hzI) with hz0 | hzpos
  · subst hz0
    refine Filter.Eventually.of_forall fun θ => ?_
    have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
    have hWt0 : Work.Spaces.Wt α 0 θ = 0 := by simp [Work.Spaces.Wt, hw0]
    have hpure : purePart (Work.Spaces.Dz f) k 0 θ = 0 := by
      simp only [purePart]
      simp [hw0]
    have hmixed : mixedPart α (Work.Spaces.Dz f) k 0 θ = 0 := by
      simp only [mixedPart]
      simp [hWt0]
    rw [HkIntegrand_eq_parts, hpure, hmixed]
    have hsum : (∑ i ∈ Finset.range (k + 1), (if 1 ≤ i then
        (Work.Spaces.DthIter i (Work.Spaces.Dz f) 0 θ * Work.Spaces.Wt α 0 θ) ^ 2
        else 0)) = 0 := by simp [hWt0]
    have hsq : (Work.Spaces.Dz f 0 θ
        * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
      simp [hw0]
    rw [hsum, hsq, add_zero]
    have hA := Work.Spaces.HkIntegrand_nonneg α k f 0 θ
    have hB := Work.Spaces.HkIntegrand_nonneg α k (zsqPz2 f) 0 θ
    positivity
  · filter_upwards [ae_mem_Ioo_theta] with θ hθ
    have hQ : (z, θ) ∈ Q0 := ⟨hzpos, hθ⟩
    set H : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hH
    set T2 : ℝ := ∑ i ∈ Finset.range (k + 1), (if 1 ≤ i then
        (Work.Spaces.DthIter i (Work.Spaces.Dz f) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0) with hT2
    set S : ℝ := Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k (zsqPz2 f) z θ
        + ((Work.Spaces.Dz f z θ * H) ^ 2 + T2) with hS
    set D : ℝ := 2 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k (zsqPz2 f) z θ
        + ((Work.Spaces.Dz f z θ * H) ^ 2 + T2) with hD
    set R : ℝ := 4 * (k + 2) ^ 2 * S with hR
    have hA : 0 ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.HkIntegrand_nonneg α k f z θ
    have hB : 0 ≤ Work.Spaces.HkIntegrand α k (zsqPz2 f) z θ :=
      Work.Spaces.HkIntegrand_nonneg α k _ z θ
    have hP : 0 ≤ (Work.Spaces.Dz f z θ * H) ^ 2 := sq_nonneg _
    have hT2nn : 0 ≤ T2 := by
      rw [hT2]
      exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [sq_nonneg]
    have hDnn : 0 ≤ D := by rw [hD]; linarith
    have hSnn : 0 ≤ S := by rw [hS]; linarith
    have hAleD : Work.Spaces.HkIntegrand α k f z θ ≤ D := by rw [hD]; linarith
    have hBleD : Work.Spaces.HkIntegrand α k (zsqPz2 f) z θ ≤ D := by rw [hD]; linarith
    have hPleD : (Work.Spaces.Dz f z θ * H) ^ 2 ≤ D := by rw [hD]; linarith
    have hT2leD : T2 ≤ D := by rw [hD]; linarith
    have h2ABleD : 2 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k (zsqPz2 f) z θ ≤ D := by rw [hD]; linarith
    -- pure part
    have hbound : ∀ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * H) ^ 2 ≤ D := by
      intro i hi
      have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rcases lt_or_eq_of_le hi' with hlt | heq
      · have h1 : Work.Spaces.DzIter i (Work.Spaces.Dz f) = Work.Spaces.DzIter (i + 1) f :=
          (DzIter_succ_eq i f).symm
        have hb : (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * H) ^ 2
            ≤ Work.Spaces.HkIntegrand α k f z θ := by
          rw [h1, hH]
          exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) (by omega)
        exact le_trans hb hAleD
      · rw [heq]
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          have h0 : Work.Spaces.DzIter 0 (Work.Spaces.Dz f) z θ
              = Work.Spaces.Dz f z θ := rfl
          rw [h0]
          exact hPleD
        · have hdecomp : Work.Spaces.DzIter k (Work.Spaces.Dz f) z θ
              = Work.Spaces.DzIter (k - 1) (zsqPz2 f) z θ + Work.Spaces.DzIter k f z θ := by
            have h := DzIter_add_two_decomp f hf (k - 1) hQ
            have h'' : (fun z θ => Work.Spaces.DzIter (k - 1 + 2) f z θ
                - (Work.Spaces.DzIter (k - 1) (zsqPz2 f) z θ
                  + Work.Spaces.DzIter (k - 1 + 1) f z θ)) z θ = 0 := h
            have hz := sub_eq_zero.mp h''
            rw [show k - 1 + 2 = k + 1 by omega, show k - 1 + 1 = k by omega] at hz
            have h1 : Work.Spaces.DzIter k (Work.Spaces.Dz f) = Work.Spaces.DzIter (k + 1) f :=
              (DzIter_succ_eq k f).symm
            rw [h1]
            exact hz
          have hsplit : (Work.Spaces.DzIter k (Work.Spaces.Dz f) z θ * H) ^ 2
              ≤ 2 * (Work.Spaces.DzIter (k - 1) (zsqPz2 f) z θ * H) ^ 2
                + 2 * (Work.Spaces.DzIter k f z θ * H) ^ 2 := by
            rw [hdecomp]
            nlinarith [sq_nonneg (Work.Spaces.DzIter (k - 1) (zsqPz2 f) z θ * H
              - Work.Spaces.DzIter k f z θ * H)]
          refine le_trans hsplit (le_trans ?_ h2ABleD)
          have hb1 : (Work.Spaces.DzIter (k - 1) (zsqPz2 f) z θ * H) ^ 2
              ≤ Work.Spaces.HkIntegrand α k (zsqPz2 f) z θ := by
            rw [hH]
            exact Work.Spaces.sq_le_HkIntegrand_z α k (zsqPz2 f) z θ (k - 1) (by omega)
          have hb2 : (Work.Spaces.DzIter k f z θ * H) ^ 2
              ≤ Work.Spaces.HkIntegrand α k f z θ := by
            rw [hH]
            exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ k le_rfl
          linarith
    -- mixed part
    have hboundm : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0) ≤ D := by
      intro i hi j hj
      by_cases hcond : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hcond]
        have hmix : Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            = Work.Spaces.mixed (j + 1) i f z θ := mixed_Dz_eq_of_comm f hc j i hQ
        rw [hmix]
        rcases lt_or_eq_of_le (show i + (j + 1) ≤ k + 1 by omega) with hlt | heq
        · have hb : (Work.Spaces.mixed (j + 1) i f z θ * Work.Spaces.Wt α z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α k f z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i (j + 1) hcond.1 (by omega)
          exact le_trans hb hAleD
        · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
          · subst hj0
            have hterm : (Work.Spaces.mixed (0 + 1) i f z θ * Work.Spaces.Wt α z θ) ^ 2
                = (Work.Spaces.DthIter i (Work.Spaces.Dz f) z θ
                    * Work.Spaces.Wt α z θ) ^ 2 := by
              rw [DthIter_eq_of_comm f hc i hQ]
              rfl
            rw [hterm]
            refine le_trans ?_ hT2leD
            rw [hT2]
            have hle : (if 1 ≤ i then (Work.Spaces.DthIter i (Work.Spaces.Dz f) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)
                ≤ ∑ a ∈ Finset.range (k + 1), (if 1 ≤ a then
                    (Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
                      * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
              Finset.single_le_sum (f := fun a => (if 1 ≤ a then
                  (Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
                    * Work.Spaces.Wt α z θ) ^ 2 else 0))
                (fun a _ => by split_ifs <;> simp [sq_nonneg])
                (Finset.mem_range.mpr (by omega))
            rw [if_pos hcond.1] at hle
            exact hle
          · have hdec := mixed_succ_decomp f hf j i hjpos hQ
            rw [hdec]
            have hsplit : ((Work.Spaces.mixed (j - 1) i (zsqPz2 f) z θ
                + Work.Spaces.mixed j i f z θ) * Work.Spaces.Wt α z θ) ^ 2
                ≤ 2 * (Work.Spaces.mixed (j - 1) i (zsqPz2 f) z θ
                    * Work.Spaces.Wt α z θ) ^ 2
                  + 2 * (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
              nlinarith [sq_nonneg (Work.Spaces.mixed (j - 1) i (zsqPz2 f) z θ
                * Work.Spaces.Wt α z θ
                - Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ)]
            refine le_trans hsplit (le_trans ?_ h2ABleD)
            have hb1 : (Work.Spaces.mixed (j - 1) i (zsqPz2 f) z θ
                * Work.Spaces.Wt α z θ) ^ 2
                ≤ Work.Spaces.HkIntegrand α k (zsqPz2 f) z θ :=
              Work.Spaces.sq_le_HkIntegrand_mixed α k (zsqPz2 f) z θ i (j - 1) hcond.1 (by omega)
            have hb2 : (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
                ≤ Work.Spaces.HkIntegrand α k f z θ :=
              Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hcond.1 (by omega)
            linarith
      · rw [if_neg hcond]
        exact hDnn
    -- assemble
    rw [HkIntegrand_eq_parts, hR]
    have hp : purePart (Work.Spaces.Dz f) k z θ ≤ (k + 1 : ℝ) * D := by
      refine le_trans (Finset.sum_le_card_nsmul _ _ _ hbound) (le_of_eq ?_)
      rw [Finset.card_range, nsmul_eq_mul]
      simp only [Nat.cast_add, Nat.cast_one]
    have hm : mixedPart α (Work.Spaces.Dz f) k z θ
        ≤ ((k + 1 : ℝ) * (k + 1 : ℝ)) * D := by
      refine le_trans (Finset.sum_le_card_nsmul _ _ _
        (fun i hi => Finset.sum_le_card_nsmul _ _ _ (fun j hj => hboundm i hi j hj)))
        (le_of_eq ?_)
      rw [Finset.card_range]
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    have hcount : ((k + 1 : ℝ) + (k + 1 : ℝ) * (k + 1 : ℝ)) ≤ 2 * (k + 2 : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (k : ℝ), Nat.cast_nonneg (α := ℝ) k]
    have hDle : D ≤ 2 * S := by rw [hD, hS]; linarith
    have h1 : purePart (Work.Spaces.Dz f) k z θ + mixedPart α (Work.Spaces.Dz f) k z θ
        ≤ ((k + 1 : ℝ) + (k + 1 : ℝ) * (k + 1 : ℝ)) * D := by linarith
    have h2 : ((k + 1 : ℝ) + (k + 1 : ℝ) * (k + 1 : ℝ)) * D
        ≤ 4 * (k + 2 : ℝ) ^ 2 * S := by
      have hb0 : (0 : ℝ) ≤ 2 * (k + 2 : ℝ) ^ 2 := by positivity
      have hmul := mul_le_mul hcount hDle hDnn hb0
      linarith
    linarith

/-- The second `HkMem` conjunct of `g`, from the finiteness of `LkSq α k g`. -/
theorem integrableOn_sliceIntegral_of_LkSq_lt_top (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ)
    (hg : SmoothOpen g) (h : LkSq α k g < ⊤) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g z θ) Work.Spaces.Iz := by
  have hprod : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    aesm_HkIntegrand_prod α k g hg
  have hfin : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)) < ⊤ := by
    rw [← MeasureTheory.lintegral_lintegral_swap (hprod.prod_swap)]
    exact h
  have hA : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hprod.lintegral_prod_right'
  have hint : MeasureTheory.Integrable (fun z => (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)).toReal)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top hA (ne_of_lt hfin)
  refine hint.congr ?_
  filter_upwards [ae_mem_Ioi_z] with z hz
  exact (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
    (Work.Spaces.aesm_slice_of_continuousOn_Qd _
      (hg.continuousOn_HkIntegrand α k) hz)).symm

end Work.FTS.EllipticEst.DzAmgm
