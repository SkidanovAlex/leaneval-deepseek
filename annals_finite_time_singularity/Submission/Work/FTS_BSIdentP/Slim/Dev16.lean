import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS_BSIdentP.Slim.DevStub
import Submission.Work.FTS_BSIdentP.Slim.Dev5
import Submission.Work.FTS_BSIdentP.Slim.Dev2
import Submission.Work.FTS_BSIdentP.Slim.Dev6
import Submission.Work.FTS_BSIdentP.Slim.Dev11
import Submission.Work.FTS_BSIdentP.Slim.Dev14
import Submission.Work.FTS_BSIdentP.Slim.Dev15

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdentP.Dev16

open Work.FTS.BSIdent

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdentP.Dev5 (GG)

variable {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam} {C : Physical.PhysClock} {t : ℝ}
  {τ : ℝ}

/-- The explicit expression for the axial profile, as a function on `(r,z)`. -/
noncomputable def Qexp (α : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.BSIdent.Fam) (τ : ℝ) :
    ℝ × ℝ → ℝ :=
  fun p => -(Work.Cyl.rhoP p.1 p.2 * (A τ)⁻¹ * (GG Φ τ
        (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
        (Work.Cyl.thetaP p.1 p.2) / Real.cos (Work.Cyl.thetaP p.1 p.2)))
    - (2 * p.1 * (A τ)⁻¹ * GG Φ τ (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
          (Work.Cyl.thetaP p.1 p.2)
      + (A τ)⁻¹ * (Work.FTS.Regularity.pExp α * p.1
          * (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
        * Work.Cyl.pdR (GG Φ τ) (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP p.1 p.2)
        + (-p.2) * Work.Cyl.pdZ (GG Φ τ)
            (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP p.1 p.2)))

theorem pdR_GG_zero_eq {w₀ : ℝ} (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hw₀ : 0 < w₀) :
    Work.Cyl.pdR (GG Φ τ) w₀ 0 = 0 := by
  have hev : (fun w' : ℝ => GG Φ τ w' 0) =ᶠ[𝓝 w₀] (fun _ => (0:ℝ)) := by
    filter_upwards [Ioi_mem_nhds hw₀] with w' hw'
    rw [Dev5.GG_of_nonneg (Φ := Φ) (τ := τ) le_rfl]
    exact h0 w' hw'
  show deriv (fun w' : ℝ => GG Φ τ w' 0) w₀ = 0
  rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]

/-- The axial profile `-(ψ/r) - ∂_rψ` is continuous at `(r₀, 0)`. -/
theorem continuousAt_Q_zero {r₀ : ℝ} (hr₀ : 0 < r₀) (hτ : τ = Physical.clockInv C t)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hB : 0 < B τ) :
    ContinuousAt (fun p : ℝ × ℝ => -(Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t p.1 p.2 / p.1)
      - Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2) (r₀, 0) := by
  have hρ0 : Work.Cyl.rhoP r₀ 0 = r₀ := Dev11.rhoP_zero_snd hr₀
  have hθ0 : Work.Cyl.thetaP r₀ 0 = 0 := by simp [Work.Cyl.thetaP]
  have hpair := Dev15.continuousAt_pair_zero (α := α) (B := B) (τ := τ) hr₀ hB
  have hwr : ContinuousAt (fun p : ℝ × ℝ =>
      Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (r₀, 0) := hpair.fst
  have hw₀ : 0 < Work.Cyl.rhoP r₀ 0 ^ Work.FTS.Regularity.pExp α / B τ :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos (z := 0) hr₀) _) hB
  have hw₀1 : (0:ℝ) < Work.Cyl.rhoP r₀ 0 ^ Work.FTS.Regularity.pExp α / B τ := by linarith
  have hG : ContinuousAt (fun p : ℝ × ℝ => GG Φ τ
      (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (r₀, 0) := by
    refine ContinuousAt.comp (x := (r₀, 0))
      (f := fun p : ℝ × ℝ => (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ,
        Work.Cyl.thetaP p.1 p.2)) (g := fun q : ℝ × ℝ => GG Φ τ q.1 q.2) ?_ hpair
    rw [hθ0]
    exact Dev2.continuousAt_GG_zero (τ := τ) (Φ := Φ) hsm h0 hw₀
  have hDW : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ)
      (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (r₀, 0) := by
    refine ContinuousAt.comp (x := (r₀, 0))
      (f := fun p : ℝ × ℝ => (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ,
        Work.Cyl.thetaP p.1 p.2)) (g := fun q : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) q.1 q.2) ?_ hpair
    rw [hθ0]
    exact Dev2.continuousAt_pdR_GG_zero (τ := τ) (Φ := Φ) hsm h0 hw₀
  have hDT : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ)
      (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (r₀, 0) := by
    refine ContinuousAt.comp (x := (r₀, 0))
      (f := fun p : ℝ × ℝ => (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ,
        Work.Cyl.thetaP p.1 p.2)) (g := fun q : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) q.1 q.2) ?_ hpair
    rw [hθ0]
    exact DevStub.continuousAt_pdZ_G_zero (τ := τ) (Φ := Φ) hsm h0 hw₀
  -- ### continuity of the explicit expression
  have hρc : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2) (r₀, 0) := by
    have : Continuous (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2) := by
      have hf : Continuous (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) := by fun_prop
      exact Real.continuous_sqrt.comp hf
    exact this.continuousAt
  have hH : ContinuousAt (Qexp (α := α) (A := A) (B := B) (Φ := Φ) τ) (r₀, 0) := by
    unfold Qexp
    refine ContinuousAt.sub ?_ ?_
    · refine ContinuousAt.neg ?_
      refine ContinuousAt.mul ?_ ?_
      · exact hρc.mul_const (A τ)⁻¹
      · refine ContinuousAt.div hG (Real.continuous_cos.continuousAt.comp hpair.snd) ?_
        rw [hθ0]; norm_num
    · refine ContinuousAt.add ?_ ?_
      · have hc2 : ContinuousAt (fun p : ℝ × ℝ => 2 * p.1 * (A τ)⁻¹) (r₀, 0) :=
          (continuousAt_const.mul continuousAt_fst).mul_const (A τ)⁻¹
        exact hc2.mul hG
      · refine ContinuousAt.mul continuousAt_const ?_
        exact (((continuousAt_const.mul continuousAt_fst).mul hwr).mul hDW).add
          (continuousAt_snd.neg.mul hDT)
  -- ### the value of the profile at `(r₀, 0)`
  have hval : -(Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r₀ 0 / r₀)
      - Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r₀ 0 = 0 := by
    rw [Dev5.merPsiT_zero_snd (α := α) hτ hB h0 hr₀,
      Dev5.pdR_merPsiT_zero_snd (α := α) hτ hB h0 hr₀]
    simp
  -- ### the value of the explicit expression at `(r₀, 0)`
  have hHval : Qexp (α := α) (A := A) (B := B) (Φ := Φ) τ (r₀, 0) = 0 := by
    unfold Qexp
    rw [hθ0, hρ0]
    have hw₀' : 0 < r₀ ^ Work.FTS.Regularity.pExp α / B τ :=
      div_pos (Real.rpow_pos_of_pos hr₀ _) hB
    rw [Dev5.GG_of_nonneg (Φ := Φ) (τ := τ) le_rfl]
    rw [h0 _ hw₀', pdR_GG_zero_eq (τ := τ) (Φ := Φ) h0 hw₀']
    simp
  -- ### the two one-sided limits
  rw [ContinuousAt, hval]
  have hsplit : ({p : ℝ × ℝ | ¬ p.2 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}) = Set.univ := by
    rw [show ({p : ℝ × ℝ | p.2 = 0} : Set (ℝ × ℝ)) = {p : ℝ × ℝ | ¬ p.2 = 0}ᶜ from by
      ext p; simp]
    exact Set.union_compl_self _
  have h1 : Tendsto (fun p : ℝ × ℝ =>
        -(Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t p.1 p.2 / p.1)
        - Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | ¬ p.2 = 0}] (r₀, 0)) (𝓝 0) := by
    have hrpos : ∀ᶠ p in (𝓝 (r₀, (0:ℝ))), 0 < p.1 :=
      ((continuousAt_fst (p := (r₀, (0:ℝ)))).tendsto).eventually (Ioi_mem_nhds hr₀)
    have hev : (Qexp (α := α) (A := A) (B := B) (Φ := Φ) τ)
        =ᶠ[𝓝[{p : ℝ × ℝ | ¬ p.2 = 0}] (r₀, 0)]
        (fun p : ℝ × ℝ => -(Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t p.1 p.2 / p.1)
          - Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2) := by
      have hrp : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | ¬ p.2 = 0}] (r₀, 0)), 0 < p.1 :=
        hrpos.filter_mono (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | ¬ p.2 = 0}))
      filter_upwards [self_mem_nhdsWithin, hrp] with p hp hp1
      have hz : p.2 ≠ 0 := hp
      unfold Qexp
      rw [Dev5.merPsiT_div_fst (α := α) (τ := τ) hτ hp1,
        Dev6.pdR_merPsiT_eq (α := α) (τ := τ) hτ hsm hB hp1 hz]
    have hH' := hH.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | ¬ p.2 = 0}))
    rw [hHval] at hH'
    exact hH'.congr' hev
  have h2 : Tendsto (fun p : ℝ × ℝ =>
        -(Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t p.1 p.2 / p.1)
        - Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | p.2 = 0}] (r₀, 0)) (𝓝 0) := by
    have hrpos : ∀ᶠ p in (𝓝 (r₀, (0:ℝ))), 0 < p.1 :=
      ((continuousAt_fst (p := (r₀, (0:ℝ)))).tendsto).eventually (Ioi_mem_nhds hr₀)
    have hev : (fun _ : ℝ × ℝ => (0:ℝ)) =ᶠ[𝓝[{p : ℝ × ℝ | p.2 = 0}] (r₀, 0)]
        (fun p : ℝ × ℝ => -(Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t p.1 p.2 / p.1)
          - Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2) := by
      have hrp : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | p.2 = 0}] (r₀, 0)), 0 < p.1 :=
        hrpos.filter_mono (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | p.2 = 0}))
      filter_upwards [self_mem_nhdsWithin, hrp] with p hp hp1
      rw [hp, Dev5.merPsiT_zero_snd (α := α) hτ hB h0 hp1,
        Dev5.pdR_merPsiT_zero_snd (α := α) hτ hB h0 hp1]
      simp
    exact tendsto_const_nhds.congr' hev
  have hcomb := tendsto_sup.mpr ⟨h1, h2⟩
  rw [← nhdsWithin_union, hsplit, nhdsWithin_univ] at hcomb
  exact hcomb

end Work.FTS.BSIdentP.Dev16
