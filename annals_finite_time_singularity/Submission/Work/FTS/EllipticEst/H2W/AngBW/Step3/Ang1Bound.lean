import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Honest.step3Defs
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.Step3PsiBar
import Submission.Work.Blocks.HkMem_of_majorant_aesm
import Submission.Work.FTS.EllipticEst.Final.Step3Helpers

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AngBW.S3

open Work.FTS.EllipticEst.Honest
open Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false


set_option autoImplicit false

/-! ## The level-`0` integrand does not depend on `α`, and the two names of the angular term -/

/-- At level `0` the `ℋ^k`-integrand is `(f·w/sin(2θ)^{η/2})²` (`Honest.HkIntegrand_zero_eq`),
so it does not depend on `α`. -/
theorem HkIntegrand_zero_alpha_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ = Work.Spaces.HkIntegrand 0 0 g z θ := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]

/-- The same for the squared norm. -/
theorem HkSq_zero_alpha_eq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq 0 0 g = Work.Spaces.HkSq α 0 g :=
  (Work.FTS.EllipticEst.Honest.HkSq_zero_eq 0 g).trans
    (Work.FTS.EllipticEst.Honest.HkSq_zero_eq α g).symm

/-- And for the honesty. -/
theorem HkMem_zero_alpha_iff (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkMem α 0 g ↔ Work.Spaces.HkMem 0 0 g := by
  simp only [Work.Spaces.HkMem, Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]

/-- `Ae.ang1` is `Honest.uOf`: both are `∂_θ(tan θ · u)`. -/
theorem ang1_eq_uOf (u : ℝ → ℝ → ℝ) : ang1 u = Work.FTS.EllipticEst.Honest.uOf u := rfl

/-! ## The pointwise majorant for the `I₄`-quantity -/

/-- **The pointwise domination of the integrand of `POf u`.**  On the open quadrant
`POf u = uOf u - u` (`Honest.pth_tan_mul_eq_open`), and the level-`0` integrand is the square of
the weighted profile, so `(x-y)² ≤ 2x²+2y²` gives the bound; on the two boundary lines the
integrand of `POf u` vanishes and the right-hand side is nonnegative. -/
theorem HkIntegrand_POf_le (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.POf u) z θ
      ≤ 2 * (Work.Spaces.HkIntegrand α 0 u z θ
        + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.uOf u) z θ) := by
  have hnn1 : 0 ≤ Work.Spaces.HkIntegrand α 0 u z θ :=
    Work.FTS.EllipticEst.Honest.HkIntegrand_nonneg α 0 u z θ
  have hnn2 : 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.uOf u) z θ :=
    Work.FTS.EllipticEst.Honest.HkIntegrand_nonneg α 0 _ z θ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_boundary α _ (Or.inl hz0.symm)]
    linarith
  · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).1 with hθ0 | hθ0pos
    · rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_boundary α _ (Or.inr (Or.inl hθ0.symm))]
      linarith
    · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).2 with hθπ | hθlt
      · rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_boundary α _ (Or.inr (Or.inr hθπ))]
        linarith
      · rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
          Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
          Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
        have hid := Work.FTS.EllipticEst.Honest.pth_tan_mul_eq_open hsm hzpos hθ0pos hθlt
        have hpof : Work.FTS.EllipticEst.Honest.POf u z θ
            = Work.FTS.EllipticEst.Honest.uOf u z θ - u z θ := by
          have h : Work.FTS.EllipticEst.Honest.uOf u z θ
              = u z θ + Work.FTS.EllipticEst.Honest.POf u z θ := hid
          linarith
        rw [hpof]
        nlinarith [sq_nonneg (Work.FTS.EllipticEst.Honest.uOf u z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          + u z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]

/-! ## Honesty of the `I₄`-quantity from the honesty of `u` and of `∂_θ(tan θ·u)` -/

/-- **`HkMem α 0 (POf u)`**, given `HkMem α 0 u` and `HkMem α 0 (∂_θ(tan θ·u))`.  The proof is
the majorant argument of `Work.Blocks.HkMem_of_majorant_aesm` with the pointwise bound
`HkIntegrand_POf_le`; the a.e. strong measurability hypotheses come from the `C^∞`-regularity
of `POf u` on the open quadrant (`Honest.smoothOpen_POf`). -/
theorem hkMem_POf_of_uOf {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hu : Work.Spaces.HkMem α 0 u)
    (hG : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Honest.uOf u)) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Honest.POf u) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.Honest.POf u) :=
    Work.FTS.EllipticEst.Honest.smoothOpen_POf hsm
  refine Work.Blocks.HkMem_of_majorant_aesm α 0
    (f := Work.FTS.EllipticEst.Honest.POf u)
    (M := fun z θ => 2 * (Work.Spaces.HkIntegrand α 0 u z θ
      + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.uOf u) z θ))
    ?_ ?_ ?_ ?_ ?_
  · -- a.e. strong measurability of every angular slice
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [show (fun θ => Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.POf u) z θ)
          = fun _ : ℝ => (0 : ℝ) from by
        funext θ
        rw [← hz0]
        exact Work.FTS.EllipticEst.Honest.HkIntegrand_zero_boundary α _ (Or.inl rfl)]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.POf u)
          p.1 p.2)
        (hS.continuousOn_HkIntegrand α 0) hzpos
  · -- a.e. strong measurability of the `θ`-integral
    have hprod : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0
          (Work.FTS.EllipticEst.Honest.POf u) p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ (hS.continuousOn_HkIntegrand α 0)
    exact hprod.integral_prod_right'
  · -- integrability of the majorant on every slice
    intro z hz
    exact ((hu.1 z hz).add (hG.1 z hz)).const_mul 2
  · -- integrability of the `z`-integral of the majorant
    have h2 : MeasureTheory.IntegrableOn
        (fun z => 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
          + (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.uOf u) z θ)))
        Work.Spaces.Iz := (hu.2.add hG.2).const_mul 2
    refine MeasureTheory.IntegrableOn.congr_fun h2 (fun z hz => ?_) measurableSet_Ici
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hu.1 z hz) (hG.1 z hz)]
  · -- the pointwise domination
    intro z hz θ hθ
    exact HkIntegrand_POf_le α u hsm z θ hz hθ

/-! ## The estimate -/

theorem ang1_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u : ℝ → ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    (∀ z : ℝ, u z 0 = 0) → (∀ z : ℝ, u z (Real.pi / 2) = 0) →
    Work.Spaces.HkMem α 0 u →
    Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u) →
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 u) →
    Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 u))
      ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 u)
          + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))) := by
  obtain ⟨C₃, hC₃pos, hC₃b⟩ := Work.FTS.EllipticEst.H2W.AngBW.S3.step3PsiBar
  refine ⟨Real.sqrt 2 * (1 + C₃) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) < 1 + C₃ := by linarith
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith [mul_pos h2 h1]
  · intro α u hsm h0 hπ hu hB hG
    -- the honesty of `POf u` and the two estimates
    have hG' : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Honest.uOf u) := by
      rwa [← ang1_eq_uOf u]
    have hPmem : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Honest.POf u) :=
      hkMem_POf_of_uOf hsm hu hG'
    have hu0 : Work.Spaces.HkMem 0 0 u := (HkMem_zero_alpha_iff α u).mp hu
    have hB0 : Work.Spaces.HkMem 0 0 (Work.Spaces.pthIter 2 u) :=
      (HkMem_zero_alpha_iff α _).mp hB
    have hP0 : Work.Spaces.HkMem 0 0 (Work.FTS.EllipticEst.Honest.POf u) :=
      (HkMem_zero_alpha_iff α _).mp hPmem
    have hunion := Work.FTS.EllipticEst.Honest.sqrt_HkSq_uOf_le (α := α) (Ψ := u) hsm hu hPmem
    have hPbar : Real.sqrt (Work.Spaces.HkSq 0 0 (Work.FTS.EllipticEst.Honest.POf u))
        ≤ C₃ * (Real.sqrt (Work.Spaces.HkSq 0 0 u)
          + Real.sqrt (Work.Spaces.HkSq 0 0 (Work.Spaces.pthIter 2 u))) :=
      hC₃b u hsm h0 hπ hu0 hB0 hP0
    have hPbar' : Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Honest.POf u))
        ≤ C₃ * (Real.sqrt (Work.Spaces.HkSq α 0 u)
          + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))) := by
      rw [HkSq_zero_alpha_eq α (Work.FTS.EllipticEst.Honest.POf u),
        HkSq_zero_alpha_eq α u, HkSq_zero_alpha_eq α (Work.Spaces.pthIter 2 u)] at hPbar
      exact hPbar
    -- the arithmetic
    have hsu : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 u) := Real.sqrt_nonneg _
    have hsb : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)) :=
      Real.sqrt_nonneg _
    have hsp : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Honest.POf u)) :=
      Real.sqrt_nonneg _
    have hr : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hC₃le : C₃ ≤ 1 + C₃ := by linarith
    have hC₃0 : 0 ≤ C₃ := le_of_lt hC₃pos
    have hS : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 u)
        + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)) := by linarith
    have s1 : Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 0 u)
          + Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Honest.POf u)))
        ≤ Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 0 u)
          + C₃ * (Real.sqrt (Work.Spaces.HkSq α 0 u)
            + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)))) :=
      mul_le_mul_of_nonneg_left (by linarith) hr
    have s2 : Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 0 u)
          + C₃ * (Real.sqrt (Work.Spaces.HkSq α 0 u)
            + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))))
        ≤ Real.sqrt 2 * (1 + C₃) * (Real.sqrt (Work.Spaces.HkSq α 0 u)
            + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hr
      nlinarith [hsb]
    have s3 : Real.sqrt 2 * (1 + C₃) * (Real.sqrt (Work.Spaces.HkSq α 0 u)
          + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)))
        ≤ (Real.sqrt 2 * (1 + C₃) + 1) * (Real.sqrt (Work.Spaces.HkSq α 0 u)
            + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))) := by
      nlinarith [hS]
    rw [ang1_eq_uOf u]
    linarith [hunion, s1, s2, s3]


end Work.FTS.EllipticEst.H2W.AngBW.S3
