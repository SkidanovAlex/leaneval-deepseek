import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS_BSIdentP.Slim.Dev11
import Submission.Work.FTS_BSIdentP.Slim.Dev5
import Submission.Work.FTS_BSIdentP.Slim.Dev7
import Submission.Work.FTS_BSIdentP.Slim.DevStub
import Submission.Work.FTS_BSIdentP.Slim.MerPsiOriginAux
import Submission.Work.FTS_BSIdentP.Slim.PsiFieldCorrCocompact
import Submission.Work.FTS_BSIdentP.Slim.TendstoSliceQuotient
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.Dev15 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdentP.Dev15

open Work.FTS.BSIdent

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdentP.Dev5 (GG)

variable {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam} {C : Physical.PhysClock} {t : ℝ}
  {τ : ℝ}

/-- The polar coordinates are continuous at `(r₀, 0)`. -/
theorem continuousAt_polar_zero {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ContinuousAt (fun p : ℝ × ℝ => (Work.Cyl.rhoP p.1 p.2, Work.Cyl.thetaP p.1 p.2)) (r₀, 0) := by
  have h1 : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2) (r₀, 0) := by
    have : Continuous (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2) := by
      have hf : Continuous (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) := by fun_prop
      exact Real.continuous_sqrt.comp hf
    exact this.continuousAt
  have h2 : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.thetaP p.1 p.2) (r₀, 0) := by
    have hθr : ContinuousAt (fun p : ℝ × ℝ => p.2 / p.1) (r₀, 0) :=
      continuousAt_snd.div continuousAt_fst (ne_of_gt hr₀)
    exact Real.continuous_arctan.continuousAt.comp hθr
  exact h1.prodMk h2

/-- The polar pair composed with the weight is continuous at `(r₀, 0)`. -/
theorem continuousAt_pair_zero {r₀ : ℝ} (hr₀ : 0 < r₀) (hB : 0 < B τ) :
    ContinuousAt (fun p : ℝ × ℝ =>
      (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ, Work.Cyl.thetaP p.1 p.2))
      (r₀, 0) := by
  have hρ0 : Work.Cyl.rhoP r₀ 0 = r₀ := Dev11.rhoP_zero_snd hr₀
  have hcons := continuousAt_polar_zero hr₀
  refine ContinuousAt.prodMk ?_ ?_
  · exact (hcons.fst.rpow_const (Or.inl (ne_of_gt (by rw [hρ0]; exact hr₀)))).div_const (B τ)
  · exact hcons.snd

/-- The `∂_zψ/r` profile is continuous at `(r₀, 0)`. -/
theorem continuousAt_pdZ_div_zero {r₀ : ℝ} (hr₀ : 0 < r₀) (hτ : τ = Physical.clockInv C t)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hB : 0 < B τ) :
    ContinuousAt (fun p : ℝ × ℝ =>
      Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2 / p.1) (r₀, 0) := by
  have hρ0 : Work.Cyl.rhoP r₀ 0 = r₀ := Dev11.rhoP_zero_snd hr₀
  have hw₀ : 0 < Work.Cyl.rhoP r₀ 0 ^ Work.FTS.Regularity.pExp α / B τ :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos (z := 0) hr₀) _) hB
  have hθ0 : Work.Cyl.thetaP r₀ 0 = 0 := by simp [Work.Cyl.thetaP]
  have hw₀1 : (0:ℝ) < Work.Cyl.rhoP r₀ 0 ^ Work.FTS.Regularity.pExp α / B τ := by linarith
  have hpair := continuousAt_pair_zero (α := α) (B := B) (τ := τ) hr₀ hB
  -- ### value at `(r₀, 0)`
  have hval : Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r₀ 0 / r₀
      = (A τ)⁻¹ * deriv (fun θ => Φ (Work.Cyl.rhoP r₀ 0 ^ Work.FTS.Regularity.pExp α / B τ)
          θ τ) 0 := by
    rw [Dev11.pdZ_merPsiT_zero_snd (α := α) hτ hsm h0 hB hr₀, hρ0]
    field_simp
  -- ### the three composed ingredient functions are continuous
  have hG : ContinuousAt (fun p : ℝ × ℝ => GG Φ τ
      (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (r₀, 0) := by
    refine ContinuousAt.comp (x := (r₀, 0))
      (f := fun p : ℝ × ℝ => (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ,
        Work.Cyl.thetaP p.1 p.2)) (g := fun q : ℝ × ℝ => GG Φ τ q.1 q.2) ?_ hpair
    rw [hθ0]
    exact Dev2.continuousAt_GG_zero (τ := τ) (Φ := Φ) hsm h0 (by linarith)
  have hDW : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ)
      (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (r₀, 0) := by
    refine ContinuousAt.comp (x := (r₀, 0))
      (f := fun p : ℝ × ℝ => (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ,
        Work.Cyl.thetaP p.1 p.2)) (g := fun q : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) q.1 q.2) ?_ hpair
    rw [hθ0]
    exact Dev2.continuousAt_pdR_GG_zero (τ := τ) (Φ := Φ) hsm h0 (by linarith)
  have hDT : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ)
      (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (r₀, 0) := by
    refine ContinuousAt.comp (x := (r₀, 0))
      (f := fun p : ℝ × ℝ => (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ,
        Work.Cyl.thetaP p.1 p.2)) (g := fun q : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) q.1 q.2) ?_ hpair
    rw [hθ0]
    exact DevStub.continuousAt_pdZ_G_zero (τ := τ) (Φ := Φ) hsm h0 (by linarith)
  -- ### the explicit continuous function `H`
  have hwr : ContinuousAt (fun p : ℝ × ℝ =>
      Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (r₀, 0) := hpair.fst
  have hH : ContinuousAt (fun p : ℝ × ℝ =>
      (2 * p.2 * (A τ)⁻¹ * GG Φ τ (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
          (Work.Cyl.thetaP p.1 p.2)
        + (A τ)⁻¹ * (Work.FTS.Regularity.pExp α * p.2
            * (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
          * Work.Cyl.pdR (GG Φ τ) (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              (Work.Cyl.thetaP p.1 p.2)
          + p.1 * Work.Cyl.pdZ (GG Φ τ)
              (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              (Work.Cyl.thetaP p.1 p.2))) / p.1) (r₀, 0) := by
    refine ContinuousAt.div ?_ continuousAt_fst (ne_of_gt hr₀)
    refine ContinuousAt.add ?_ ?_
    · exact ((continuousAt_const.mul continuousAt_snd).mul_const (A τ)⁻¹).mul hG
    · refine ContinuousAt.mul continuousAt_const ?_
      exact (((continuousAt_const.mul continuousAt_snd).mul hwr).mul hDW).add
        (continuousAt_fst.mul hDT)
  -- ### the value of `H` at `(r₀, 0)`
  have hHval : (let H : ℝ × ℝ → ℝ := fun p => (2 * p.2 * (A τ)⁻¹ * GG Φ τ
        (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2)
      + (A τ)⁻¹ * (Work.FTS.Regularity.pExp α * p.2
          * (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
        * Work.Cyl.pdR (GG Φ τ) (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP p.1 p.2)
        + p.1 * Work.Cyl.pdZ (GG Φ τ)
            (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP p.1 p.2))) / p.1; H (r₀, 0))
      = (A τ)⁻¹ * deriv (fun θ => Φ (Work.Cyl.rhoP r₀ 0 ^ Work.FTS.Regularity.pExp α / B τ)
          θ τ) 0 := by
    simp only
    rw [hθ0, hρ0]
    simp only [mul_zero, zero_mul, add_zero, zero_add]
    rw [Dev14.pdZ_GG_zero_eq (τ := τ) (Φ := Φ) hsm h0
      (div_pos (Real.rpow_pos_of_pos hr₀ _) hB),
      show Work.Cyl.pdZ (fun w θ => Φ w θ τ) (r₀ ^ Work.FTS.Regularity.pExp α / B τ) 0
        = deriv (fun θ => Φ (r₀ ^ Work.FTS.Regularity.pExp α / B τ) θ τ) 0 from rfl]
    field_simp
  -- ### the two one-sided limits
  rw [ContinuousAt, hval]
  have hsplit : ({p : ℝ × ℝ | ¬ p.2 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}) = Set.univ := by
    rw [show ({p : ℝ × ℝ | p.2 = 0} : Set (ℝ × ℝ)) = {p : ℝ × ℝ | ¬ p.2 = 0}ᶜ from by
      ext p; simp]
    exact Set.union_compl_self _
  have h1 : Tendsto (fun p : ℝ × ℝ =>
        Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2 / p.1)
      (𝓝[{p : ℝ × ℝ | ¬ p.2 = 0}] (r₀, 0))
      (𝓝 ((A τ)⁻¹ * deriv (fun θ => Φ (Work.Cyl.rhoP r₀ 0 ^ Work.FTS.Regularity.pExp α / B τ)
          θ τ) 0)) := by
    have hrpos : ∀ᶠ p in (𝓝 (r₀, (0:ℝ))), 0 < p.1 :=
      ((continuousAt_fst (p := (r₀, (0:ℝ)))).tendsto).eventually (Ioi_mem_nhds hr₀)
    have hev : (fun p : ℝ × ℝ =>
          (2 * p.2 * (A τ)⁻¹ * GG Φ τ (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              (Work.Cyl.thetaP p.1 p.2)
            + (A τ)⁻¹ * (Work.FTS.Regularity.pExp α * p.2
                * (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              * Work.Cyl.pdR (GG Φ τ) (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
                  (Work.Cyl.thetaP p.1 p.2)
              + p.1 * Work.Cyl.pdZ (GG Φ τ)
                  (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
                  (Work.Cyl.thetaP p.1 p.2))) / p.1)
        =ᶠ[𝓝[{p : ℝ × ℝ | ¬ p.2 = 0}] (r₀, 0)]
        (fun p : ℝ × ℝ =>
          Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2 / p.1) := by
      have hrp : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | ¬ p.2 = 0}] (r₀, 0)), 0 < p.1 :=
        hrpos.filter_mono (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | ¬ p.2 = 0}))
      filter_upwards [self_mem_nhdsWithin, hrp] with p hp hp1
      have hz : p.2 ≠ 0 := hp
      rw [← Dev6.pdZ_merPsiT_eq (α := α) (τ := τ) hτ hsm hB hp1 hz]
    have hH' : Tendsto (fun p : ℝ × ℝ =>
          (2 * p.2 * (A τ)⁻¹ * GG Φ τ (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              (Work.Cyl.thetaP p.1 p.2)
            + (A τ)⁻¹ * (Work.FTS.Regularity.pExp α * p.2
                * (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              * Work.Cyl.pdR (GG Φ τ) (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
                  (Work.Cyl.thetaP p.1 p.2)
              + p.1 * Work.Cyl.pdZ (GG Φ τ)
                  (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
                  (Work.Cyl.thetaP p.1 p.2))) / p.1)
        (𝓝[{p : ℝ × ℝ | ¬ p.2 = 0}] (r₀, 0))
        (𝓝 (let H : ℝ × ℝ → ℝ := fun p => (2 * p.2 * (A τ)⁻¹ * GG Φ τ
              (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2)
            + (A τ)⁻¹ * (Work.FTS.Regularity.pExp α * p.2
                * (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              * Work.Cyl.pdR (GG Φ τ) (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
                  (Work.Cyl.thetaP p.1 p.2)
              + p.1 * Work.Cyl.pdZ (GG Φ τ)
                  (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
                  (Work.Cyl.thetaP p.1 p.2))) / p.1; H (r₀, 0))) :=
      hH.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | ¬ p.2 = 0}))
    rw [hHval] at hH'
    exact hH'.congr' hev
  have h2 : Tendsto (fun p : ℝ × ℝ =>
        Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2 / p.1)
      (𝓝[{p : ℝ × ℝ | p.2 = 0}] (r₀, 0))
      (𝓝 ((A τ)⁻¹ * deriv (fun θ => Φ (Work.Cyl.rhoP r₀ 0 ^ Work.FTS.Regularity.pExp α / B τ)
          θ τ) 0)) := by
    have hrp : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | p.2 = 0}] (r₀, 0)), 0 < p.1 :=
      (((continuousAt_fst (p := (r₀, (0:ℝ)))).tendsto).eventually (Ioi_mem_nhds hr₀)).filter_mono
        (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | p.2 = 0}))
    have hev : (fun p : ℝ × ℝ => (A τ)⁻¹ * deriv (fun θ =>
          Φ (Work.Cyl.rhoP p.1 0 ^ Work.FTS.Regularity.pExp α / B τ) θ τ) 0)
        =ᶠ[𝓝[{p : ℝ × ℝ | p.2 = 0}] (r₀, 0)]
        (fun p : ℝ × ℝ => Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2 / p.1) := by
      filter_upwards [self_mem_nhdsWithin, hrp] with p hp hp1
      have hρp : Work.Cyl.rhoP p.1 0 = p.1 := Dev11.rhoP_zero_snd hp1
      rw [hρp, hp]
      rw [Dev11.pdZ_merPsiT_zero_snd (α := α) hτ hsm h0 hB hp1]
      field_simp
    have hcont0 : ContinuousAt (fun w : ℝ => deriv (fun θ => Φ w θ τ) 0)
        (Work.Cyl.rhoP r₀ 0 ^ Work.FTS.Regularity.pExp α / B τ) := by
      have hslice : ContinuousAt (fun q : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) q.1 q.2)
          (Work.Cyl.rhoP r₀ 0 ^ Work.FTS.Regularity.pExp α / B τ, (0:ℝ)) :=
        Dev2.continuousAt_pdZ_Phi (τ := τ) (Φ := Φ) hsm (by linarith) (by
          rw [abs_zero]; linarith [Real.pi_pos])
      have hpair0 : ContinuousAt (fun w : ℝ =>
          (w, (0:ℝ))) (Work.Cyl.rhoP r₀ 0 ^ Work.FTS.Regularity.pExp α / B τ) :=
        continuousAt_id.prodMk continuousAt_const
      have hthis := ContinuousAt.comp (x := (Work.Cyl.rhoP r₀ 0 ^ Work.FTS.Regularity.pExp α / B τ))
        (f := fun w : ℝ => (w, (0:ℝ)))
        (g := fun q : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) q.1 q.2) hslice hpair0
      simpa [Function.comp_def, Work.Cyl.pdZ] using hthis
    have hmain : ContinuousAt (fun p : ℝ × ℝ => (A τ)⁻¹ * deriv (fun θ =>
        Φ (Work.Cyl.rhoP p.1 0 ^ Work.FTS.Regularity.pExp α / B τ) θ τ) 0) (r₀, 0) := by
      refine ContinuousAt.mul continuousAt_const ?_
      refine ContinuousAt.comp (x := (r₀, 0))
        (f := fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 0 ^ Work.FTS.Regularity.pExp α / B τ)
        (g := fun w : ℝ => deriv (fun θ => Φ w θ τ) 0) hcont0 ?_
      have hρc : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 (0:ℝ)) (r₀, 0) :=
        ContinuousAt.comp (x := (r₀, 0)) (f := fun p : ℝ × ℝ => (p.1, (0:ℝ)))
          (g := fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2)
          (continuousAt_polar_zero hr₀).fst (continuousAt_fst.prodMk continuousAt_const)
      exact (hρc.rpow_const (Or.inl (ne_of_gt (by rw [hρ0]; exact hr₀)))).div_const (B τ)
    exact (hmain.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | p.2 = 0}))).congr' hev
  have hcomb := tendsto_sup.mpr ⟨h1, h2⟩
  rw [← nhdsWithin_union, hsplit, nhdsWithin_univ] at hcomb
  exact hcomb

end Work.FTS.BSIdentP.Dev15
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.MerPsiOriginProfiles =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The meridian stream function and its two first partials vanish at the origin

This file proves `Work.FTS.BSIdentP.Levels.merPsiT_origin_profiles`: along the half-plane
`r > 0`, the quotient `ψ/r` and the partial derivatives `∂_zψ`, `∂_rψ` of the meridian stream
function

  `ψ(r,z) = ρ(r,z)² · A(τ)⁻¹ · Φ̂(ρ(r,z)^p/B(τ), θ(r,z), τ)`,  `p = 3α`,  `τ = clockInv C t`,

tend to `0` as `(r,z) → (0,0)`.

The mechanism is the *vanishing of the coefficients* in the chain rule: with `ρ = rhoP r z`,
`θ = thetaP r z`, `w = ρ^p/B(τ)`, `c = A(τ)⁻¹`, `G = Φ̂(·,·,τ)`,

  `ψ/r = ρ c (G(w,θ)/cos θ)`,
  `∂_zψ = 2 z c G + c (p z w ∂_wG + r ∂_θG)`,
  `∂_rψ = 2 r c G + c (p r w ∂_wG - z ∂_θG)`,

and every coefficient on the right is `O(ρ)` while `G(w,θ)`, `∂_wG(w,θ)`, `∂_θG(w,θ)` stay
bounded.  The quotient `G(w,θ)/cos θ` is bounded because the odd extension loses the factor
`π/2 - |θ|`, which Jordan's inequality compares with `cos θ`.

The partials are computed by `_dev6` on the open quadrant (`z ≠ 0`) and by `_dev11` on the
plane `z = 0`; the half-plane `z < 0` is reduced to `z > 0` by the oddness of `ψ` in `z`.
The limiting step is a squeeze against `K·rhoP r z`, using `rhoP r z → 0`.  The pointwise
bounds live in `merPsiT_origin_aux` and `merPsiT_origin_aux2`; this file assembles them.
-/

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

open Filter Set
open scoped Topology

theorem merPsiT_origin_profiles {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hzeroPlane : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hzeroAxis : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) (Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam)) :
    Filter.Tendsto (fun p : ℝ × ℝ =>
        Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t p.1 p.2 / p.1)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), 0)) (𝓝 0) ∧
    Filter.Tendsto (fun p : ℝ × ℝ =>
        Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), 0)) (𝓝 0) ∧
    Filter.Tendsto (fun p : ℝ × ℝ =>
        Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), 0)) (𝓝 0) := by
  have hp : 0 ≤ Work.FTS.Regularity.pExp α := by
    rw [Work.FTS.Regularity.pExp]; linarith
  have hval : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) :=
    fun w θ hw hθ hθ' => (hrate w θ hw hθ hθ').1
  have hwd : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) :=
    fun w θ hw hθ hθ' => (hrate w θ hw hθ hθ').2.1
  have hth : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ|
        ≤ C₀ * (1 + w) ^ (-lam) :=
    fun w θ hw hθ hθ' => (hrate w θ hw hθ hθ').2.2
  refine ⟨?_, ?_, ?_⟩
  · exact tendsto_zero_of_rhoP_bound
      (abs_div_merPsiT_le (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t)
        hB hlam hC₀.le hzeroPlane hval)
  · exact tendsto_zero_of_rhoP_bound
      (abs_pdR_merPsiT_le (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t)
        hsm hB hzeroPlane hp hlam hC₀.le hval hwd hth)
  · exact tendsto_zero_of_rhoP_bound
      (abs_pdZ_merPsiT_le (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t)
        hsm hB hzeroPlane hp hlam hC₀.le hval hwd hth)

end Work.FTS.BSIdentP.Levels
end
