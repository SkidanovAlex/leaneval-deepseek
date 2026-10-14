import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev10
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev5
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev8
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two
import Submission.Work.FTS.FireFix.Firing
import Submission.Work.FTS.MeridianDyn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdent.Weyl.Dev11

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdent.Weyl.Dev5 (GG)

variable {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}

theorem rhoP_zero_snd {r : ℝ} (hr : 0 < r) : Work.Cyl.rhoP r 0 = r := by
  rw [Work.Cyl.rhoP, show r ^ 2 + (0:ℝ) ^ 2 = r ^ 2 from by ring, Real.sqrt_sq_eq_abs,
    abs_of_pos hr]

/-- `GG` is `sign θ` times the profile evaluated at `|θ|`. -/
theorem GG_eq_sign_mul {w θ : ℝ} (hθ : θ ≠ 0) :
    GG Φ τ w θ = (θ / |θ|) * Φ w |θ| τ := by
  rcases lt_or_gt_of_ne hθ with h | h
  · rw [Dev5.GG_of_neg (Φ := Φ) (τ := τ) h, abs_of_neg h]
    have h1 : θ / -θ = -1 := by field_simp
    rw [h1]; ring
  · rw [Dev5.GG_of_nonneg (Φ := Φ) (τ := τ) h.le, abs_of_pos h]
    have h1 : θ / θ = 1 := by field_simp
    rw [h1]; ring

/-- The value of `∂_zψ` on the plane `θ = 0`. -/
theorem pdZ_merPsiT_zero_snd {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} {τ : ℝ} (hτ : τ = Physical.clockInv C t)
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hB : 0 < B τ) {r : ℝ} (hr : 0 < r) :
    Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r 0
      = (A τ)⁻¹ * r * deriv (fun θ => Φ (r ^ Work.FTS.Regularity.pExp α / B τ) θ τ) 0 := by
  set ψ := Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t with hψdef
  set w₁ : ℝ := r ^ Work.FTS.Regularity.pExp α / B τ with hw₁def
  have hρ0 : Work.Cyl.rhoP r 0 = r := rhoP_zero_snd hr
  have hw₁pos : 0 < w₁ := by rw [hw₁def]; positivity
  have hψ0 : ∀ z : ℝ, ψ r z = Work.Cyl.rhoP r z ^ 2 * (A τ)⁻¹
      * GG Φ τ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
          (Work.Cyl.thetaP r z) :=
    fun z => Dev5.merPsiT_apply_core α A B Φ C t hτ r z
  have hψr0 : ψ r 0 = 0 := Dev5.merPsiT_zero_snd hτ hB h0 hr
  -- ### Step 1: the difference-quotient limit of `Φ` along the path
  set δ : ℝ := min (w₁ / 2) (1 / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδw : δ ≤ w₁ / 2 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hwpath : Tendsto (fun z : ℝ => Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
      (𝓝 (0:ℝ)) (𝓝 w₁) := by
    rw [hw₁def]
    have hcont : ContinuousAt
        (fun z : ℝ => Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ) 0 := by
      have h1 : ContinuousAt (fun z : ℝ => Work.Cyl.rhoP r z) 0 := by
        have : Continuous (fun z : ℝ => Work.Cyl.rhoP r z) := by
          have hf : Continuous (fun z : ℝ => r ^ 2 + z ^ 2) := by fun_prop
          exact Real.continuous_sqrt.comp hf
        exact this.continuousAt
      exact (h1.rpow_const (Or.inl (ne_of_gt (by rw [hρ0]; exact hr)))).div_const (B τ)
    simpa [hρ0] using hcont.tendsto
  have hθpath : Tendsto (fun z : ℝ => Work.Cyl.thetaP r z) (𝓝 (0:ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun z : ℝ => Work.Cyl.thetaP r z) 0 := by
      rw [show (fun z : ℝ => Work.Cyl.thetaP r z) = fun z => Real.arctan (z / r) from rfl]
      exact (Real.continuous_arctan.continuousAt.comp (continuousAt_id.div_const r))
    have h0' : (fun z : ℝ => Work.Cyl.thetaP r z) 0 = 0 := by simp [Work.Cyl.thetaP]
    simpa only [h0'] using hcont.tendsto
  have hpath : Tendsto (fun z : ℝ => (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ,
        |Work.Cyl.thetaP r z|)) (𝓝[≠] (0:ℝ))
      (𝓝[{p : ℝ × ℝ | |p.1 - w₁| < δ ∧ |p.2 - 0| < δ ∧ p.2 ≠ 0}] (w₁, 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (hwpath.prodMk_nhds (by simpa using hθpath.abs)).mono_left
        (nhdsWithin_le_nhds (s := {z : ℝ | z ≠ 0}))
    · have hθabs : Tendsto (fun z : ℝ => |Work.Cyl.thetaP r z|) (𝓝 (0:ℝ)) (𝓝 0) := by
        simpa using hθpath.abs
      have e1 : ∀ᶠ z in (𝓝[≠] (0:ℝ)), |Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ - w₁|
          < δ := by
        have hmem : Set.Iio (w₁ + δ) ∈ 𝓝 w₁ := Iio_mem_nhds (by linarith)
        have hmem2 : Set.Ioi (w₁ - δ) ∈ 𝓝 w₁ := Ioi_mem_nhds (by linarith)
        have hw' := hwpath.mono_left (nhdsWithin_le_nhds (s := {z : ℝ | z ≠ 0}))
        filter_upwards [hw'.eventually hmem, hw'.eventually hmem2] with z hz1 hz2
        rw [abs_lt]; exact ⟨by linarith, by linarith⟩
      have e2 : ∀ᶠ z in (𝓝[≠] (0:ℝ)), |Work.Cyl.thetaP r z| < δ :=
        (hθabs.mono_left (nhdsWithin_le_nhds (s := {z : ℝ | z ≠ 0}))).eventually
          (Iio_mem_nhds hδpos)
      have e3 : ∀ᶠ z in (𝓝[≠] (0:ℝ)), |Work.Cyl.thetaP r z| ≠ 0 := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        rw [abs_ne_zero]
        intro hc
        exact hz (by
          have hzr : z / r = 0 := Real.arctan_eq_zero_iff.mp (by simpa [Work.Cyl.thetaP] using hc)
          rcases div_eq_zero_iff.mp hzr with h | h
          · exact h
          · exact absurd h (ne_of_gt hr))
      filter_upwards [e1, e2, e3] with z hz1 hz2 hz3
      exact ⟨hz1, by simpa using hz2, hz3⟩
  have hq : Tendsto (fun z : ℝ => Φ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
        (|Work.Cyl.thetaP r z|) τ / |Work.Cyl.thetaP r z|)
      (𝓝[≠] (0:ℝ)) (𝓝 (deriv (fun θ => Φ w₁ θ τ) 0)) := by
    have hmain := (DevStub.tendsto_slice_quotient (f := fun w θ => Φ w θ τ) (w₀ := w₁) (θ₀ := 0)
      (δ := δ) hδpos ?_ ?_).comp hpath
    · have hthis := hmain
      simp only [Function.comp_def, sub_zero] at hthis
      exact hthis
    · intro w θ hw hθ
      refine hsm w θ ?_ ?_ ?_
      · have := abs_lt.mp hw
        have h2 : w > w₁ - δ := by linarith [this.1]
        have h3 : δ ≤ w₁ / 2 := hδw
        linarith
      · have := abs_lt.mp hθ
        linarith [Real.pi_pos, this.1]
      · have := abs_lt.mp hθ
        linarith [Real.pi_pos, this.2]
    · intro w hw
      apply h0
      have := abs_lt.mp hw
      have h3 : δ ≤ w₁ / 2 := hδw
      linarith [this.1]
  -- ### Step 2: `θ/z → 1/r`
  have hθderiv : HasDerivAt (fun z : ℝ => Work.Cyl.thetaP r z) (1 / r) 0 := by
    have h1 : HasDerivAt (fun z : ℝ => z / r) (1 / r) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).div_const r
    have h2 : HasDerivAt (fun z : ℝ => Real.arctan (z / r))
        ((1 / (1 + ((0:ℝ) / r) ^ 2)) * (1 / r)) 0 :=
      HasDerivAt.comp (x := (0:ℝ)) (h := fun z : ℝ => z / r) (h₂ := Real.arctan)
        (Real.hasDerivAt_arctan ((0:ℝ) / r)) h1
    have hval : (1 / (1 + ((0:ℝ) / r) ^ 2)) * (1 / r) = 1 / r := by norm_num
    rw [hval] at h2
    exact h2
  have hθslope : Tendsto (fun z : ℝ => Work.Cyl.thetaP r z / z) (𝓝[≠] (0:ℝ)) (𝓝 (1 / r)) := by
    have h := hθderiv.tendsto_slope
    have h0' : (fun z : ℝ => Work.Cyl.thetaP r z) 0 = 0 := by simp [Work.Cyl.thetaP]
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [slope_fun_def]
    simp only [h0', vsub_eq_sub, sub_zero, Pi.sub_apply, smul_eq_mul]
    ring
  -- ### Step 3: `ρ² → r²`
  have hρ2 : Tendsto (fun z : ℝ => Work.Cyl.rhoP r z ^ 2) (𝓝[≠] (0:ℝ))
      (𝓝 (Work.Cyl.rhoP r 0 ^ 2)) := by
    have hcont : ContinuousAt (fun z : ℝ => Work.Cyl.rhoP r z ^ 2) 0 := by
      have h1 : ContinuousAt (fun z : ℝ => Work.Cyl.rhoP r z) 0 := by
        have : Continuous (fun z : ℝ => Work.Cyl.rhoP r z) := by
          have hf : Continuous (fun z : ℝ => r ^ 2 + z ^ 2) := by fun_prop
          exact Real.continuous_sqrt.comp hf
        exact this.continuousAt
      exact h1.pow 2
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- ### Step 4: the pointwise identity for `z ≠ 0`
  have hident : ∀ z : ℝ, z ≠ 0 → ψ r z / z
      = Work.Cyl.rhoP r z ^ 2 * (A τ)⁻¹ * (Work.Cyl.thetaP r z / z)
        * (Φ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
            (|Work.Cyl.thetaP r z|) τ / |Work.Cyl.thetaP r z|) := by
    intro z hz
    have hθz : Work.Cyl.thetaP r z ≠ 0 := by
      intro hc
      exact hz (by
        have hzr : z / r = 0 := Real.arctan_eq_zero_iff.mp (by simpa [Work.Cyl.thetaP] using hc)
        rcases div_eq_zero_iff.mp hzr with h | h
        · exact h
        · exact absurd h (ne_of_gt hr))
    rw [hψ0 z, GG_eq_sign_mul (Φ := Φ) (τ := τ) hθz]
    have hne : |Work.Cyl.thetaP r z| ≠ 0 := abs_ne_zero.mpr hθz
    field_simp
  -- ### Step 5: the limit of `ψ r z / z`
  have hmul : Tendsto (fun z : ℝ => Work.Cyl.rhoP r z ^ 2 * (A τ)⁻¹ * (Work.Cyl.thetaP r z / z)
        * (Φ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
            (|Work.Cyl.thetaP r z|) τ / |Work.Cyl.thetaP r z|))
      (𝓝[≠] (0:ℝ))
      (𝓝 (Work.Cyl.rhoP r 0 ^ 2 * (A τ)⁻¹ * (1 / r) * deriv (fun θ => Φ w₁ θ τ) 0)) :=
    ((hρ2.mul_const (A τ)⁻¹).mul hθslope).mul hq
  have hslope : Tendsto (fun z : ℝ => ψ r z / z) (𝓝[≠] (0:ℝ))
      (𝓝 (Work.Cyl.rhoP r 0 ^ 2 * (A τ)⁻¹ * (1 / r) * deriv (fun θ => Φ w₁ θ τ) 0)) := by
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hident z hz).symm
  have hval : Work.Cyl.rhoP r 0 ^ 2 * (A τ)⁻¹ * (1 / r) * deriv (fun θ => Φ w₁ θ τ) 0
      = (A τ)⁻¹ * r * deriv (fun θ => Φ w₁ θ τ) 0 := by
    rw [hρ0]; field_simp
  rw [hval] at hslope
  -- ### Step 6: conclude
  rw [hw₁def] at hslope
  have hslope' : Tendsto (slope (fun z' : ℝ => ψ r z') 0) (𝓝[≠] (0:ℝ))
      (𝓝 ((A τ)⁻¹ * r * deriv (fun θ => Φ (r ^ Work.FTS.Regularity.pExp α / B τ) θ τ) 0)) := by
    refine hslope.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [slope_fun_def]
    simp only [Pi.sub_apply, vsub_eq_sub, hψr0, sub_zero, smul_eq_mul]
    ring
  rw [Work.Cyl.pdZ]
  exact (hasDerivAt_iff_tendsto_slope.mpr hslope').deriv

end Work.FTS.BSIdent.Weyl.Dev11
