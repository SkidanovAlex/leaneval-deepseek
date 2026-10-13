/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/mixed_Jeps_tendsto.lean` — the slots of `J_ε G_ε` converge

Target: `Work.FTS.StrongEps.mixed_Jeps_tendsto`.

The statement combines the *commutation* `E1` (`mixed_Jeps`: the slot of the mollified profile is
the mollified slot) with the *peak estimate* for the mollifier (`Jeps_tendsto_of_tendsto`, or
rather its sequential form): the slot `D_z^j D_θ^i (J_ε G_ε)` at a point of the open quadrant
converges to `D_z^j D_θ^i f` as `ε → 0`, because

  `D_z^j D_θ^i (J_ε G_ε) = J_ε (D_z^j D_θ^i G_ε)`   (`E1`),

the profile `D_z^j D_θ^i G_ε` converges to `D_z^j D_θ^i f` *locally uniformly* on the quadrant
(that is the slot clause of `ConvLocUnifH6`), and `J_ε` reproduces a profile up to an error which
is uniform on the shrinking log-coordinate ball.

## Why a fresh proof of the peak estimate

The peak estimate `abs_Jeps_sub_le_of_bound` of `Jeps_tendsto_of_tendsto.lean` asks for the
mollified profile to be *globally* a.e. strongly measurable.  That is *not* available for the
slots: the profiles `G n` are only known to be smooth on the *open* quadrant, so a slot
`D_z^j D_θ^i (G n)` is a `deriv`-built object whose values outside the open quadrant are junk, and
global measurability cannot be concluded.  It is also never needed: the shifted profile
`p ↦ X (zShift z p.1) (thShift θ p.2)` takes its values in the quadrant (`sPhi` maps everything
into `Quad`) and inherits *continuity* from the continuity of `X` on the quadrant.  So the peak
estimate is reproved here with `ContinuousOn … Quad` in place of the global measurability
hypothesis; everything else is verbatim the argument of `Jeps_tendsto_of_tendsto.lean`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.ConvLev0Defs
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.Jeps_tendsto_of_tendsto
import Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_mixed_Quad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter MeasureTheory Set

namespace Work.FTS.StrongEps

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The peak estimate with local smoothness instead of global measurability -/

/-- **The quantitative core of the peak estimate, in the `ContinuousOn`-form used by the slots.**
If `X` is continuous on the open quadrant and deviates from its value at the base point `(z,θ)` by
at most `η` on the whole ball `‖p‖ ≤ ε` (which contains the support of `Jker ρ ε`), then the
mollified value at `(z,θ)` is within `η` of `X z θ`:

  `|Jeps ρ ε X z θ - X z θ| ≤ η`.

Only `z > 0`, `θ ∈ (0,π/2)` and `ε > 0` are needed; no limit in `ε` is involved.  The hypothesis
`ContinuousOn (uncurry X) Quad` replaces the global a.e. strong measurability of
`abs_Jeps_sub_le_of_bound`: it is exactly what makes the shifted profile continuous (hence
locally bounded and a.e. strongly measurable), and it is what the slots actually satisfy. -/
theorem abs_Jeps_sub_le_of_bound_of_continuousOn (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ)
    {X : ℝ → ℝ → ℝ} {ε z θ η : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hε : 0 < ε)
    (hXc : ContinuousOn (fun q : ℝ × ℝ => X q.1 q.2) Quad)
    (hη : ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → |X (zShift z p.1) (thShift θ p.2) - X z θ| ≤ η) :
    |Jeps ρ ε X z θ - X z θ| ≤ η := by
  have hJint : Integrable (Jker ρ ε) := Jker_integrable hρ hε
  have hJmass : ∫ p : ℝ × ℝ, Jker ρ ε p = 1 := Jker_integral_eq_one ρ hρ hε
  have hJnn : ∀ p : ℝ × ℝ, 0 ≤ Jker ρ ε p := fun p => by
    simp only [Jker]
    exact mul_nonneg (by positivity) (hρ.nonneg (ε⁻¹ • p))
  have hsPhi : ∀ p : ℝ × ℝ, (zShift z p.1, thShift θ p.2) ∈ Quad := fun p =>
    ⟨zShift_pos hz, thShift_mem hθ⟩
  -- the shifted profile is continuous (it is the composition of the continuous shift with a
  -- function continuous on the quadrant, whose image lies in the quadrant)
  have hAcont : Continuous (fun p : ℝ × ℝ => X (zShift z p.1) (thShift θ p.2)) := by
    have h := hXc.comp_continuous (continuous_shift_pair z θ) (fun p => hsPhi p)
    simpa only [Function.comp_def] using h
  have hAesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => X (zShift z p.1) (thShift θ p.2)) volume := hAcont.aestronglyMeasurable
  -- the kernel vanishes off the ball of radius `ε`
  have hle_of_Jker : ∀ p : ℝ × ℝ, Jker ρ ε p ≠ 0 → ‖p‖ ≤ ε := by
    intro p hp
    by_contra hc
    exact hp (Jker_eq_zero_of_not_mem hρ hε (by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact not_le.mpr (not_le.mp hc)))
  -- integrability of the mollified profile: the kernel has compact support and the shifted
  -- profile is bounded there by `η + |X z θ|`
  have hFint : Integrable
      (fun p : ℝ × ℝ => Jker ρ ε p * X (zShift z p.1) (thShift θ p.2)) := by
    refine Integrable.mono' (hJint.mul_const (η + |X z θ|)) ?_ ?_
    · exact (Jker_continuous hρ ε).aestronglyMeasurable.mul hAesm
    · filter_upwards with p
      by_cases hp : Jker ρ ε p = 0
      · simp [hp]
      · have hb := hη p (hle_of_Jker p hp)
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hJnn p)]
        refine mul_le_mul_of_nonneg_left ?_ (hJnn p)
        have h1 : |X (zShift z p.1) (thShift θ p.2)|
            ≤ |X (zShift z p.1) (thShift θ p.2) - X z θ| + |X z θ| := by
          simpa only [sub_add_cancel, Real.norm_eq_abs] using
            norm_add_le (X (zShift z p.1) (thShift θ p.2) - X z θ) (X z θ)
        linarith
  -- `X z θ` is the average of the constant profile `X z θ` against the kernel
  have hsplit : (∫ p : ℝ × ℝ, Jker ρ ε p * X (zShift z p.1) (thShift θ p.2)) - X z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ) := by
    have h2 : (∫ p : ℝ × ℝ, Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ))
        = (∫ p : ℝ × ℝ, Jker ρ ε p * X (zShift z p.1) (thShift θ p.2))
          - ∫ p : ℝ × ℝ, Jker ρ ε p * X z θ := by
      rw [← integral_sub hFint (hJint.mul_const (X z θ))]
      exact integral_congr_ae (Eventually.of_forall fun p => by ring)
    calc (∫ p : ℝ × ℝ, Jker ρ ε p * X (zShift z p.1) (thShift θ p.2)) - X z θ
        = (∫ p : ℝ × ℝ, Jker ρ ε p * X (zShift z p.1) (thShift θ p.2))
          - ∫ p : ℝ × ℝ, Jker ρ ε p * X z θ := by
          rw [integral_mul_const, hJmass, one_mul]
      _ = ∫ p : ℝ × ℝ, Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ) := h2.symm
  -- and the difference is bounded by `η` times the total mass of the kernel
  have hbd : |∫ p : ℝ × ℝ, Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ)| ≤ η := by
    have hae : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
        ‖Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ)‖ ≤ Jker ρ ε p * η := by
      filter_upwards with p
      by_cases hp : Jker ρ ε p = 0
      · simp [hp]
      · have hb := hη p (hle_of_Jker p hp)
        have h1 : ‖Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ)‖
            = Jker ρ ε p * |X (zShift z p.1) (thShift θ p.2) - X z θ| := by
          simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hJnn p)]
        rw [h1]
        exact mul_le_mul_of_nonneg_left hb (hJnn p)
    have h := norm_integral_le_of_norm_le (hJint.mul_const η) hae
    rw [integral_mul_const, hJmass, one_mul] at h
    simpa only [Real.norm_eq_abs] using h
  rw [Jeps_eq_integral ρ ε X hz hθ, hsplit]
  exact hbd

/-- **The sequential peak estimate, `ContinuousOn`-form**: if the profiles `X n` are continuous on
the open quadrant and asymptotically uniformly within `η` of their value at `(z,θ)` on the ball of
radius `ε n`, and `X n z θ → Xlim z θ`, then `Jeps ρ (ε n) (X n) z θ → Xlim z θ`. -/
theorem tendsto_Jeps_of_continuousOn (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ)
    {X : ℕ → ℝ → ℝ → ℝ} {Xlim : ℝ → ℝ → ℝ} {ε : ℕ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hXc : ∀ n : ℕ, ContinuousOn (fun q : ℝ × ℝ => X n q.1 q.2) Quad)
    (hεpos : ∀ n : ℕ, 0 < ε n)
    (huc : ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop, ∀ p : ℝ × ℝ, ‖p‖ ≤ ε n →
      |X n (zShift z p.1) (thShift θ p.2) - X n z θ| ≤ η)
    (hlim : Filter.Tendsto (fun n : ℕ => X n z θ) Filter.atTop (nhds (Xlim z θ))) :
    Filter.Tendsto (fun n : ℕ => Jeps ρ (ε n) (X n) z θ) Filter.atTop (nhds (Xlim z θ)) := by
  have key : ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop,
      |Jeps ρ (ε n) (X n) z θ - X n z θ| ≤ η := by
    intro η hη
    filter_upwards [huc η hη] with n hn
    exact abs_Jeps_sub_le_of_bound_of_continuousOn ρ hρ hz hθ (hεpos n) (hXc n) hn
  rw [Metric.tendsto_atTop]
  intro γ hγ
  have h2 : 0 < γ / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (key (γ / 2) h2)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hlim (γ / 2) h2
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 : dist (Jeps ρ (ε n) (X n) z θ) (X n z θ) ≤ γ / 2 := by
    rw [Real.dist_eq]
    exact hN₁ n (le_trans (le_max_left _ _) hn)
  have hn2 : dist (X n z θ) (Xlim z θ) < γ / 2 :=
    hN₂ n (le_trans (le_max_right _ _) hn)
  calc dist (Jeps ρ (ε n) (X n) z θ) (Xlim z θ)
      ≤ dist (Jeps ρ (ε n) (X n) z θ) (X n z θ) + dist (X n z θ) (Xlim z θ) :=
        dist_triangle _ _ _
    _ < γ / 2 + γ / 2 := add_lt_add_of_le_of_lt hn1 hn2
    _ = γ := by ring

/-! ## The target -/

theorem mixed_Jeps_tendsto {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {α B : ℝ} {G : ℕ → Work.FTS.Galerkin.Fn} {f : Work.FTS.Galerkin.Fn} {ε : ℕ → ℝ}
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B G f)
    (hεpos : ∀ n : ℕ, 0 < ε n) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    {p : ℝ × ℝ} (hp : p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    {j i : ℕ} (hji : j + i ≤ 4) :
    Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ (ε n) (G n))
        p.1 p.2) Filter.atTop (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
  -- the approximating slots are continuous on the open quadrant
  have hXc : ∀ n : ℕ,
      ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i (G n) q.1 q.2) Quad :=
    fun n => Work.FTS.StrongEps.HkSqAux.continuousOn_mixed_Quad (hsm n) j i
  -- a compact neighbourhood of the base point inside the quadrant
  obtain ⟨r, hr, hrsub⟩ : ∃ r : ℝ, 0 < r ∧ Metric.closedBall (p.1, p.2) r ⊆ Quad := by
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp isOpen_Quad (p.1, p.2) hp
    exact ⟨ρ₀ / 2, by linarith, fun x hx =>
      hball (Metric.closedBall_subset_ball (by linarith) hx)⟩
  -- the uniform convergence of the slots on that compact set
  have hKc : IsCompact (Metric.closedBall (p.1, p.2) r) := isCompact_closedBall _ _
  have hU := hconv.1 (Metric.closedBall (p.1, p.2) r) hKc hrsub j i hji
  have hmemK0 : (p.1, p.2) ∈ Metric.closedBall (p.1, p.2) r := by
    rw [Metric.mem_closedBall, dist_self]
    exact hr.le
  -- hence the limit slot is continuous at the base point
  have hKcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2)
      (Metric.closedBall (p.1, p.2) r) :=
    hU.continuousOn (Filter.Frequently.of_forall fun n => (hXc n).mono hrsub)
  have hlimc : ContinuousAt (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2) (p.1, p.2) :=
    hKcont.continuousAt (by
      refine mem_of_superset (Metric.ball_mem_nhds (p.1, p.2) hr) ?_
      exact Metric.ball_subset_closedBall)
  -- the asymptotic uniform closeness of the approximating slots to their value at the base point
  have huc : ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop, ∀ q : ℝ × ℝ, ‖q‖ ≤ ε n →
      |Work.Spaces.mixed j i (G n) (zShift p.1 q.1) (thShift p.2 q.2)
        - Work.Spaces.mixed j i (G n) p.1 p.2| ≤ η := by
    intro η hη
    have hη3 : 0 < η / 3 := by linarith
    have hev : ∀ᶠ n in Filter.atTop, ∀ x ∈ Metric.closedBall (p.1, p.2) r,
        dist (Work.Spaces.mixed j i (G n) x.1 x.2) (Work.Spaces.mixed j i f x.1 x.2)
          < η / 3 := by
      filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) (η / 3) hη3] with n hn x hx
      rw [dist_comm]
      exact hn x hx
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousAt_iff.mp hlimc (η / 3) hη3
    have hsPhi0 : sPhi p.1 p.2 0 = (p.1, p.2) := sPhi_zero hp.2
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
      Metric.continuousAt_iff.mp (continuous_sPhi p.1 p.2).continuousAt (min δ₁ r)
        (lt_min hδ₁pos hr)
    have hεsmall : ∀ᶠ n in Filter.atTop, ε n < δ₂ := by
      obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hε0 δ₂ hδ₂pos
      filter_upwards [Filter.eventually_ge_atTop N₀] with n hn
      have h := hN₀ n hn
      rw [Real.dist_eq, sub_zero, abs_of_pos (hεpos n)] at h
      exact h
    filter_upwards [hεsmall, hev] with n hεn hnN q hq
    have hqq : dist q (0 : ℝ × ℝ) < δ₂ := by
      rw [dist_zero_right]
      exact lt_of_le_of_lt hq hεn
    have hsPhiq : dist (sPhi p.1 p.2 q) (p.1, p.2) < min δ₁ r := by
      have h := hδ₂ hqq
      rwa [hsPhi0] at h
    have hmemK : sPhi p.1 p.2 q ∈ Metric.closedBall (p.1, p.2) r := by
      rw [Metric.mem_closedBall]
      exact le_of_lt (lt_of_lt_of_le hsPhiq (min_le_right _ _))
    have h1 : dist (Work.Spaces.mixed j i (G n) (sPhi p.1 p.2 q).1 (sPhi p.1 p.2 q).2)
        (Work.Spaces.mixed j i f (sPhi p.1 p.2 q).1 (sPhi p.1 p.2 q).2) < η / 3 :=
      hnN _ hmemK
    have h2 : dist (Work.Spaces.mixed j i f (sPhi p.1 p.2 q).1 (sPhi p.1 p.2 q).2)
        (Work.Spaces.mixed j i f p.1 p.2) < η / 3 :=
      hδ₁ (lt_of_lt_of_le hsPhiq (min_le_left _ _))
    have h3 : dist (Work.Spaces.mixed j i f p.1 p.2)
        (Work.Spaces.mixed j i (G n) p.1 p.2) < η / 3 := by
      rw [dist_comm]
      exact hnN _ hmemK0
    have hkey : dist (Work.Spaces.mixed j i (G n) (sPhi p.1 p.2 q).1 (sPhi p.1 p.2 q).2)
        (Work.Spaces.mixed j i (G n) p.1 p.2) < η := by
      have h4 := dist_triangle4
        (Work.Spaces.mixed j i (G n) (sPhi p.1 p.2 q).1 (sPhi p.1 p.2 q).2)
        (Work.Spaces.mixed j i f (sPhi p.1 p.2 q).1 (sPhi p.1 p.2 q).2)
        (Work.Spaces.mixed j i f p.1 p.2)
        (Work.Spaces.mixed j i (G n) p.1 p.2)
      linarith
    have hkey' : |Work.Spaces.mixed j i (G n) (zShift p.1 q.1) (thShift p.2 q.2)
        - Work.Spaces.mixed j i (G n) p.1 p.2| < η := by
      rw [Real.dist_eq] at hkey
      exact hkey
    exact hkey'.le
  -- pointwise convergence of the slots at the base point
  have hlim : Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (G n) p.1 p.2) Filter.atTop
      (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hU) η hη)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn (p.1, p.2) hmemK0
    rwa [dist_comm] at h
  -- assemble: `E1` turns the slot of the mollified profile into the mollified slot
  have hmain : Filter.Tendsto
      (fun n : ℕ => Jeps ρ (ε n) (Work.Spaces.mixed j i (G n)) p.1 p.2) Filter.atTop
      (nhds (Work.Spaces.mixed j i f p.1 p.2)) :=
    tendsto_Jeps_of_continuousOn ρ hρ hp.1 hp.2 hXc hεpos huc hlim
  refine Filter.Tendsto.congr' (Eventually.of_forall fun n => ?_) hmain
  exact (mixed_Jeps ρ hρ (hεpos n) (fun k => hsm n k) hp.1 hp.2 j i).symm

end Work.FTS.StrongEps
