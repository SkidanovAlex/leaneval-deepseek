import Submission.NBody.MarchalLocMinExistence
import Submission.NBody.WeakToStrong

/-!
# Newton data on an open collision-free region

The geometry of the Marchal chapter (F1), fifth layer.  This turns the *minimiser* structure of the
curve into the pointwise Newton data needed by the Rolle--Sperner step
(`MarchalLocMinIsolated.exists_pos_near_of_dense`):
wherever the curve is collision free, it is `C²` there, satisfies the motion equation, and its
derivative is differentiable with the correct second derivative.

The point is that the results of `WeakToStrong` (`minimizer_contDiffOn_two`,
`minimizer_hasDerivAt_deriv`, `minimizer_iteratedDeriv_two`) are stated on a *closed* interval on
which the curve is collision free; here an open collision-free region is turned into such intervals
by a localisation argument (continuity of `γ` and openness of `WithoutCollisions`).
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- Collision-free configurations form an **open** set of the configuration space. -/
lemma isOpen_withoutCollisions : IsOpen {x : EN E N | WithoutCollisions x} := by
  have h := (isClosed_collisionConfigs (E := E) (N := N)).isOpen_compl
  simpa only [Set.compl_setOf, not_not] using h

/-- **Newton data on a collision-free open region.**  Let `γ` be an `h`-minimiser on `[a,b]` and
let `S ⊆ (a,b)` be a region on which `γ` is collision free.  Then at every point of `S` the curve is
differentiable nearby, its derivative is differentiable with second derivative `∇_[m] (U m) (γ t)`,
and the motion equation holds. -/
theorem exists_solution_data_of_minimizer {m : Fin N → ℝ} {h a b : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    {S : Set ℝ} (hSsub : S ⊆ Ioo a b) (hSnc : ∀ t ∈ S, WithoutCollisions (γ t)) :
    ∀ t ∈ S, (∀ᶠ s in 𝓝 t, HasDerivAt γ (deriv γ s) s) ∧
      HasDerivAt (deriv γ) (iteratedDeriv 2 γ t) t ∧
      iteratedDeriv 2 γ t = ∇_[m] (U m) (γ t) := by
  intro t ht
  have htI : t ∈ Ioo a b := hSsub ht
  have hcont : ContinuousOn γ (Icc a b) := by
    have hh' := hac.continuousOn
    rwa [uIcc_of_le hab.le] at hh'
  have hcontAt : ContinuousAt γ t := hcont.continuousAt (Icc_mem_nhds htI.1 htI.2)
  have hnb : {x : EN E N | WithoutCollisions x} ∈ 𝓝 (γ t) :=
    isOpen_withoutCollisions.mem_nhds (hSnc t ht)
  have hpre : γ ⁻¹' {x : EN E N | WithoutCollisions x} ∈ 𝓝 t :=
    hcontAt.preimage_mem_nhds hnb
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hpre
  set ε : ℝ := min δ (min (t - a) (b - t)) / 2 with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact div_pos (lt_min hδpos (lt_min (by linarith [htI.1]) (by linarith [htI.2])))
      (by norm_num)
  have hεδ : ε < δ := by
    rw [hεdef]
    have h1 : min δ (min (t - a) (b - t)) ≤ δ := min_le_left _ _
    linarith
  have hYpos : 0 < min (t - a) (b - t) :=
    lt_min (by linarith [htI.1]) (by linarith [htI.2])
  have hεa : ε < t - a := by
    rw [hεdef]
    have h1 : min δ (min (t - a) (b - t)) ≤ min (t - a) (b - t) := min_le_right _ _
    have h2 : min (t - a) (b - t) ≤ t - a := min_le_left _ _
    linarith
  have hεb : ε < b - t := by
    rw [hεdef]
    have h1 : min δ (min (t - a) (b - t)) ≤ min (t - a) (b - t) := min_le_right _ _
    have h2 : min (t - a) (b - t) ≤ b - t := min_le_right _ _
    linarith
  have hncIcc : ∀ s ∈ Icc (t - ε) (t + ε), WithoutCollisions (γ s) := by
    intro s hs
    refine hδ ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsub : Icc (t - ε) (t + ε) ⊆ Icc a b := by
    intro s hs
    exact ⟨by linarith [hs.1, hεa], by linarith [hs.2, hεb]⟩
  have hmin' : IsHMinimizer m h γ (t - ε) (t + ε) :=
    IsHMinimizer.sub hac hmin (IsHMinimizer.actionOn_lt_top hmin (hfin (γ a) (γ b)))
      (by linarith) (by linarith) (by linarith)
  have hac' : AbsolutelyContinuousOnInterval γ (t - ε) (t + ε) :=
    hac.mono (by
      rw [uIcc_of_le (by linarith : t - ε ≤ t + ε), uIcc_of_le hab.le]
      exact hsub)
  have hlt : t - ε < t + ε := by linarith
  have ht' : t ∈ Ioo (t - ε) (t + ε) := ⟨by linarith, by linarith⟩
  -- the three pieces
  have hmotion := minimizer_iteratedDeriv_two (a := t - ε) (b := t + ε) hm hh hlt hac' hncIcc
    hmin' (hfin _ _) t ht'
  have hderiv := minimizer_hasDerivAt_deriv (a := t - ε) (b := t + ε) hm hh hlt hac' hncIcc
    hmin' (hfin _ _) t ht'
  have hcd := minimizer_contDiffOn_two (a := t - ε) (b := t + ε) hm hh hlt hac' hncIcc
    hmin' (hfin _ _)
  refine ⟨?_, ?_, hmotion⟩
  · filter_upwards [isOpen_Ioo.mem_nhds ht'] with s hs
    exact ((hcd.contDiffAt (isOpen_Ioo.mem_nhds hs)).differentiableAt (by norm_num)).hasDerivAt
  · rw [hmotion]
    exact hderiv

end Submission.NBody
