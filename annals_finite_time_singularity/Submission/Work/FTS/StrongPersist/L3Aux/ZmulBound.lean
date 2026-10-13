/-
Copyright: work module for the Elgindi finite-time singularity project.

# The multiplier estimate for the `ℋᵏ`-integrand: `SmoothOpen` data

The `SmoothOpen`-layer of `Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le`, on top of the
algebraic core `ZmulCore.zmul_pt`:

* `zmul_open`: on the open quadrant the two Leibniz expansions needed by `zmul_pt` come from
  `Work.FTS.FinalClock.DzIter_mul_of_contDiffOn` / `mixed_mul_of_contDiffOn` at finite order
  on the open half-line `(0,∞)`; the `z`-slices of `g` and of its `D_θ`-iterates are `C^n`
  there by `SmoothOpen.forall` + `Work.FTS.FinalClock.contDiffOn_zslice`.
* `zmul_quad`: the extension to the closed quadrant `Iz ×ˢ Iθ`; the boundary lines
  `z = 0` and `sin(2θ) = 0` are trivial because the weights kill the integrand
  (`HkIntegrand_zero_fst`, `HkIntegrand_eq_zero_of_sin_eq_zero`) while the right-hand side is
  nonnegative.
* `hkMem_of_open_dominated`: the two honesty requirements of `ℋᵏ`-membership transfer from
  `g` to `F` when the integrand of `F` is continuous on the open quadrant and dominated by a
  multiple of that of `g` on the closed quadrant; the slice at `z = 0` vanishes identically
  and the `z`-integral of the angular slices is measurable by Fubini.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.Coercivity.HkIntegrand_endpoint_zero
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

/-- **The multiplier bound on the open quadrant.** -/
theorem zmul_open (α : ℝ) (k : ℕ) (φ : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ b ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] φ z| ≤ K)
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1)))
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ
        ≤ zmulConst k * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z hz θ hθ
  have hφ : ∀ n : ℕ, ContDiffOn ℝ n φ (Set.Ioi 0) := fun n =>
    (contDiffOn_nat_of_smoothOrder n hsm).mono (fun x hx => by
      simp only [Set.mem_Ioi] at hx ⊢
      linarith)
  have hgz : ∀ n : ℕ, ContDiffOn ℝ n (fun z' => g z' θ) (Set.Ioi 0) := fun n =>
    Work.FTS.FinalClock.contDiffOn_zslice (hg.forall n) hθ
  have hgij : ∀ n i : ℕ,
      ContDiffOn ℝ n (fun z' => Work.Spaces.DthIter i g z' θ) (Set.Ioi 0) := fun n i =>
    Work.FTS.FinalClock.contDiffOn_zslice ((hg.DthIter i).forall n) hθ
  refine zmul_pt α k φ g hK (fun b hb => hB b hb z hz) ?_ ?_
  · intro i _
    exact Work.FTS.FinalClock.DzIter_mul_of_contDiffOn i φ g isOpen_Ioi (hφ i) (hgz i) z hz
  · intro j i _ _
    exact Work.FTS.FinalClock.mixed_mul_of_contDiffOn j i φ g isOpen_Ioi (hφ j) (hgij j i) z hz

/-- **The multiplier bound on the closed quadrant** `Iz ×ˢ Iθ`. -/
theorem zmul_quad (α : ℝ) (k : ℕ) (φ : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ b ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] φ z| ≤ K)
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1)))
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ
        ≤ zmulConst k * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z hz θ hθ
  have hCnn : 0 ≤ zmulConst k * (1 + K) ^ 2 :=
    mul_nonneg (zmulConst_pos k).le (sq_nonneg _)
  have hRnn : 0 ≤ zmulConst k * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ :=
    mul_nonneg hCnn (Work.Spaces.HkIntegrand_nonneg α k g z θ)
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
  · -- `z = 0`: the integrand vanishes (the radial weight is `0`)
    subst h0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst]
    exact mul_nonneg hCnn (Work.Spaces.HkIntegrand_nonneg α k g 0 θ)
  by_cases hs : Real.sin (2 * θ) = 0
  · -- `sin(2θ) = 0`: the integrand vanishes
    rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
      (fun z θ => φ z * g z θ) z θ hs]
    linarith
  · -- interior point of the quadrant
    have hbnd : (0 : ℝ) ≤ θ ∧ θ ≤ Real.pi / 2 := hθ
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      refine ⟨?_, ?_⟩
      · rcases lt_or_eq_of_le hbnd.1 with h | h
        · exact h
        · exact absurd (by rw [← h]; simp) hs
      · rcases lt_or_eq_of_le hbnd.2 with h | h
        · exact h
        · refine absurd ?_ hs
          rw [h]
          have hpi : 2 * (Real.pi / 2) = Real.pi := by ring
          rw [hpi, Real.sin_pi]
    exact zmul_open α k φ g hK hB hsm hg z hzpos θ hθ'

/-- **`ℋᵏ`-membership by domination on the closed quadrant.** -/
theorem hkMem_of_open_dominated (α : ℝ) (k : ℕ) {F g : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hF : Work.FTS.EllipticEst.SmoothOpen F) (hm : Work.Spaces.HkMem α k g)
    (hub : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k F z θ ≤ C * Work.Spaces.HkIntegrand α k g z θ) :
    Work.Spaces.HkMem α k F := by
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[volume]
      Set.Icc (0 : ℝ) (Real.pi / 2) := MeasureTheory.Ioo_ae_eq_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand hF α k
  constructor
  · -- the angular slices of the integrand are integrable on `Iθ`
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · -- `z = 0`: the integrand vanishes identically
      subst h0
      refine MeasureTheory.IntegrableOn.congr_fun integrableOn_zero
        (fun θ _ => (Work.FTS.LocData.HkIntegrand_zero_fst α k F θ).symm) measurableSet_Icc
    · -- `z > 0`: dominate by the (integrable) slice of `g` on the open interval
      have hdom : IntegrableOn (fun θ => C * Work.Spaces.HkIntegrand α k g z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        MeasureTheory.IntegrableOn.congr_set_ae ((hm.1 z hz).const_mul C) hIoo
      have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α k F z θ)
          (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
        (Work.FTS.LocData.continuousOn_slice_theta (G := Work.Spaces.HkIntegrand α k F)
          hcont hz0).aestronglyMeasurable measurableSet_Ioo
      have hle : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
          ‖Work.Spaces.HkIntegrand α k F z θ‖ ≤ C * Work.Spaces.HkIntegrand α k g z θ := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun θ hθ => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k F z θ)]
        exact hub z hz θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      exact MeasureTheory.IntegrableOn.congr_set_ae
        (MeasureTheory.Integrable.mono' hdom haesm hle) hIoo.symm
  · -- the `z`-integral of the angular slices is integrable on `Iz`
    have hdom : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        C * Work.Spaces.HkIntegrand α k g z θ) Work.Spaces.Iz := by
      show MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
        C * Work.Spaces.HkIntegrand α k g z θ) (volume.restrict Work.Spaces.Iz)
      simpa only [MeasureTheory.integral_const_mul] using (hm.2).const_mul C
    have haesm : AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
        (volume.restrict Work.Spaces.Iz) := by
      have hprod : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2)))) := by
        rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact hcont.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      have h1 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Work.Spaces.HkIntegrand α k F z θ) (volume.restrict (Set.Ioi 0)) :=
        hprod.integral_prod_right'
      have h2 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Work.Spaces.HkIntegrand α k F z θ) (volume.restrict Work.Spaces.Iz) := by
        rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
        exact h1
      have hfun : (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.HkIntegrand α k F z θ)
          = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ := by
        funext z
        exact MeasureTheory.setIntegral_congr_set hIoo
      rw [← hfun]
      exact h2
    have hle : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
        ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ‖
          ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k g z θ := by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
      refine Filter.Eventually.of_forall fun z hz => ?_
      have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)
        ((hm.1 z hz).const_mul C) ?_
      exact (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun θ hθ => hub z hz θ hθ)
    exact MeasureTheory.Integrable.mono' hdom haesm hle

end Work.FTS.StrongPersist.L3Aux
