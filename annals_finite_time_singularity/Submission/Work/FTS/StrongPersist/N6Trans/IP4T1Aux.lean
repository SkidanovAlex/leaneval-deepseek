import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.IPGen.ip4SlotDomGen
import Submission.Work.FTS.StrongPersist.N6Trans.HonestSupMixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- `SmoothOpen` is closed under products. -/
theorem SmoothOpen_mul {F G : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h1 : ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.Q0 := hF.forall n
  have h2 : ContDiffOn ℝ n (Function.uncurry G) Work.FTS.EllipticEst.Q0 := hG.forall n
  have hfun : (Function.uncurry fun z θ => F z θ * G z θ)
      = Function.uncurry F * Function.uncurry G := rfl
  rw [hfun]
  exact h1.mul h2

/-- The `IP4`-slot domination with unit coefficients: for `u`, `g` smooth on the open quadrant,
`|IP4 1 1 1 1 1 1 α u g| ≤ (3^3·10^22)·leafSum α u g`. -/
theorem IP4_le_leafSum (α : ℝ) (u g : Work.FTS.Galerkin.Fn) (hα : 0 < α) (hα1 : α ≤ 1)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    |Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1 α u g|
      ≤ (3 ^ 3 * 10 ^ 22) * Work.FTS.TransportS.leafSum α u g := by
  obtain ⟨_, hD⟩ := Work.FTS.IPGen.ip4SlotDomGen (c₁ := 1) (c₂ := 1) (c₁' := 1) (c₂' := 1)
    (c₁'' := 1) (c₂'' := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have h := hD α ⟨hα, hα1⟩ u g hu hg
  simpa only [max_self, one_pow, one_mul] using h

/-- **The reduction of `IP4T1Honest` to the honest `leafSum` bound.**

If the honest-class `leafSum` of the product `f·D_θg` against `g` is bounded by
`Cb/√(γ-1)·|f|_{ℋ⁴}·|g|²_{ℋ⁴}`, then the transport clause holds.  The only inputs are the slot
domination `IP4_le_leafSum` (with `3^3·10^22 = K`) and `1/√(γ-1) = √10/√α ≤ √10·α^{-1/2}`. -/
theorem IP4T1Honest_of_leafSumBound
    (h : ∃ Cb : ℝ, 0 < Cb ∧ ∀ (α : ℝ) (f g : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.DecayAll 4 g →
      Work.FTS.TransportS.leafSum α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g
        ≤ Cb / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
            * Work.Spaces.HkSq α 4 g) :
    ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
        Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
        Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
          Work.Spaces.DecayAll 4 g →
        |Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1 α
            (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
          ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 g) ^ 2 := by
  obtain ⟨Cb, hCbpos, hCb⟩ := h
  refine ⟨(3 ^ 3 * 10 ^ 22) * Cb * Real.sqrt 10, 1, ?_, one_pos, ?_⟩
  · positivity
  · intro α hα f g hf hmemf hg hmemg hdecg
    have hα1 : α ≤ 1 := hα.2
    have hαpos : 0 < α := hα.1
    have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
    have hs : 0 < Real.sqrt (Work.Spaces.gam α - 1) := Real.sqrt_pos.mpr hγ
    -- `1/√(γ-1) = √10·α^{-1/2}` exactly
    have hgam : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
    have hsqrt : 1 / Real.sqrt (Work.Spaces.gam α - 1)
        = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
      rw [hgam, Real.sqrt_div hαpos.le 10, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        Real.rpow_neg hαpos.le]
      field_simp
    have hle := hCb α f g hαpos hα1 hf hmemf hg hmemg hdecg
    have hK := IP4_le_leafSum α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g hαpos hα1
      (SmoothOpen_mul hf (hg.Dth)) hg
    have hmod : Work.Spaces.HkSq α 4 g = (Work.Spaces.HkNorm α 4 g) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 g)]
    have hXn : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
    have hgnn : 0 ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
    have hstep : (3 ^ 3 * 10 ^ 22)
          * Work.FTS.TransportS.leafSum α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g
        ≤ (3 ^ 3 * 10 ^ 22) * (Cb / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 4 g) :=
      mul_le_mul_of_nonneg_left hle (by norm_num)
    have hstep2 : (3 ^ 3 * 10 ^ 22) * (Cb / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 4 g)
        = (3 ^ 3 * 10 ^ 22) * Cb * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))
            * Work.Spaces.HkNorm α 4 f * (Work.Spaces.HkNorm α 4 g) ^ 2 := by
      rw [show Cb / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
            * Work.Spaces.HkSq α 4 g
          = Cb * (1 / Real.sqrt (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 4 f
              * Work.Spaces.HkSq α 4 g by ring]
      rw [hmod, hsqrt]
      ring
    linarith [hK, hstep, hstep2]

end Work.FTS.StrongPersist.N6Trans
