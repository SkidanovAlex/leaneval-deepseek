/-
# The master estimate from Trudinger's classical interior gradient estimate

`Submission.alexandrov_of_limit` is Proposition 3.1 of Shankar--Yuan for the situation that
actually occurs in `Submission.masterBound_exists`: `g` is the uniform limit, on `closedBall 0 3`,
of the classical solutions `u k` produced by `Submission.extraction` (with a uniform `C¹` bound
`Γ - 4`).  In that situation the weighted interior gradient estimate `(gradp)` is applied to the
*classical* solutions `u k`, where it follows from Trudinger's classical interior gradient
estimate `Submission.InteriorGradientBound` via
`Submission.classical_weighted_estimate` and `Submission.point_estimate_limit`, and then passed to
the limit.  The Chaudhuri--Trudinger Hessian measure and the analytic core (`lem:o(r²)`) are
theorems of the repository (`Submission.HessianMeasure`, `Submission.TaylorCore`).

Consequently `Submission.masterBound_exists_limit` gives the master estimate `∃ B, IsMasterBound B`
from the two remaining inputs

* `InteriorGradientBound` (Trudinger's classical interior gradient estimate, Theorem 3.3 of
  Trudinger--Wang, *Hessian measures II*) and
* `SavinInput` (Savin's small perturbation theorem),

which is the sharpest form of the reduction currently available: the viscosity passage for the
gradient estimate has been removed from the unproven surface.
-/
import Mathlib
import Submission.MasterEstimate
import Submission.HessianMeasure
import Submission.TaylorCore
import Submission.GradFromGradient
import Submission.AlexandrovLimit
import Submission.AlexandrovAssembly
import Submission.SmoothGradientLimit
import Submission.Commons.Measure.Lebesgue.sup_le_of_average_and_slope
import Submission.Commons.Analysis.Asymptotics.isLittleO_of_sup_ball_bound

open HessianEstimates
open Commons.Analysis.Calculus.FDeriv
open Laplacian Metric MeasureTheory Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- **Proposition 3.1 for a uniform limit of classical solutions.**  Let `g` be the uniform limit,
on `closedBall 0 3`, of a sequence of `C⁴` solutions `u k` of `σ₂(D²u) = 1`, `Δu > 0` on open sets
`s k ⊇ closedBall 0 3`, all satisfying the `C¹` bound `|u k|, ‖Du k‖ ≤ Γ - 4`.  Then `g` is twice
differentiable at some point of `ball 0 (1/3)`.

In the application (`Submission.masterBound_exists`) `g` is automatically a viscosity solution of
the equation and of `Δg ≥ 0`, which is why those are hypotheses here. -/
theorem alexandrov_of_limit (hIG : InteriorGradientBound) (hHM : HessianMeasureInput)
    (hT : TaylorCoreInput)
    {g : ℝ⁴ → ℝ} {u : ℕ → ℝ⁴ → ℝ} {s : ℕ → Set ℝ⁴} {Γ : ℝ}
    (hΓ : 4 ≤ Γ) (hadm : ∀ n, Adm Γ (u n) (s n))
    (hconv : ∀ δ > 0, ∀ᶠ k in atTop, ∀ z ∈ closedBall 0 3, |u k z - g z| < δ)
    (hgcont : ContinuousOn g (closedBall 0 3))
    (hvisc : IsViscSolution (fun M => -Gop M) g (ball 0 3))
    (hsub : IsViscSubsolution negTrace g (ball 0 3)) :
    ∃ y ∈ ball 0 (1 / 3), IsTwiceDiffAt g y := by
  have hc : (1:ℝ)/2 < 3 := by norm_num
  have hsubb : ball (0:ℝ⁴) (1/2) ⊆ ball 0 3 := ball_subset_ball hc.le
  have hgcont3 : ContinuousOn g (ball 0 3) := hgcont.mono ball_subset_closedBall
  have h2cv : IsTwoConvexOn g (ball 0 3) :=
    isTwoConvexOn_of_viscSolution isOpen_ball hvisc.1 hsub
  have hclB : closure (ball (0 : ℝ⁴) (1/2)) ⊆ ball 0 3 := by
    intro x hx
    rw [closure_ball (0 : ℝ⁴) (by norm_num), Metric.mem_closedBall, dist_zero_right] at hx
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  obtain ⟨M, σ, hMli, hσsing, hwh⟩ :=
    hHM g (ball 0 3) isOpen_ball (isBounded_ball) hgcont3 h2cv (ball 0 (1/2)) isOpen_ball hclB
  -- ## the Lipschitz bound of the limit, from the `C¹` bounds of the `u k`
  have hpt : ∀ x ∈ closedBall (0:ℝ⁴) 3, Tendsto (fun k => u k x) atTop (𝓝 (g x)) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h' := hconv ε hε
    rw [Filter.eventually_atTop] at h'
    obtain ⟨k0, hk0⟩ := h'
    exact ⟨k0, fun k hk => by
      have h3 := hk0 k hk x hx
      rw [Real.dist_eq]
      exact h3⟩
  have hdiffn : ∀ n x, x ∈ closedBall (0:ℝ⁴) 3 → DifferentiableAt ℝ (u n) x := by
    intro n x hx
    have hsubn : closedBall (0 : ℝ⁴) 3 ⊆ s n := (hadm n).2.1
    have h1 : ContDiffWithinAt ℝ 1 (u n) (s n) x :=
      (((hadm n).2.2.1).contDiffWithinAt (hsubn hx)).of_le (by norm_num)
    exact (h1.differentiableWithinAt (by norm_num)).differentiableAt
      ((hadm n).1.mem_nhds (hsubn hx))
  have hderivn : ∀ n x, x ∈ closedBall (0:ℝ⁴) 3 → ‖fderiv ℝ (u n) x‖ ≤ Γ - 4 :=
    fun n x hx => (hadm n).2.2.2.2.2.2 x hx
  have hlipn : ∀ n y z, y ∈ closedBall (0:ℝ⁴) 3 → z ∈ closedBall (0:ℝ⁴) 3 →
      |u n y - u n z| ≤ (Γ - 4) * dist y z := by
    intro n y z hy hz
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := closedBall (0:ℝ⁴) 3)
      (hdiffn n) (hderivn n) (convex_closedBall (0:ℝ⁴) 3) hy hz
    simpa [Real.norm_eq_abs, abs_sub_comm, dist_eq_norm, norm_sub_rev] using h
  have hLipBd : ∀ y ∈ closedBall (0:ℝ⁴) 3, ∀ z ∈ closedBall (0:ℝ⁴) 3,
      |g y - g z| ≤ (Γ - 4) * dist y z :=
    lipschitzOn_of_tendsto hlipn hpt
  have hLip : ∀ K : Set ℝ⁴, IsCompact K → K ⊆ ball 0 3 →
      ∃ (U : Set ℝ⁴) (C : NNReal), IsOpen U ∧ K ⊆ U ∧ U ⊆ ball 0 3 ∧ LipschitzOnWith C g U := by
    intro K hK hKsub
    refine ⟨ball 0 3, Real.toNNReal (Γ - 4), isOpen_ball, fun x hx => hKsub hx, subset_rfl, ?_⟩
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro y hy z hz
    rw [Real.dist_eq, Real.coe_toNNReal _ (by linarith)]
    exact hLipBd y (ball_subset_closedBall hy) z (ball_subset_closedBall hz)
  set G : ℝ⁴ → ℝ⁴ := (ball (0:ℝ⁴) (1/2)).indicator (gradOf g) with hGdef
  have hGli : LocallyIntegrable G volume := by
    rw [hGdef]; exact locallyIntegrable_gradOf_indicator hLip
  have hwg : HasWeakGradient g (ball 0 (1/2)) G := by
    rw [hGdef]; exact hasWeakGradient_gradOf_indicator hLip
  -- ## the three a.e. conditions
  have hae : ∀ᵐ x ∂(volume : Measure ℝ⁴), IsLebesguePointVec G x
      ∧ (∀ i j, IsLebesguePoint (M i j) x)
      ∧ (∀ i j, IsVanishingPoint (σ i j).totalVariation x) := by
    filter_upwards [Commons.Measure.Lebesgue.ae_isLebesguePoint_vec hGli,
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
        Commons.Measure.Lebesgue.ae_isLebesguePoint (hMli i j),
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
        Commons.Measure.Lebesgue.ae_isVanishingPoint (hσsing i j)]
      with x h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hpos : (volume : Measure ℝ⁴) (ball (0 : ℝ⁴) (1 / 3)) ≠ 0 :=
    ne_of_gt (Metric.measure_ball_pos volume 0 (by norm_num))
  obtain ⟨x₀, hx₀ball, hx₀⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos
      (MeasureTheory.ae_mono Measure.restrict_le_self hae)
  obtain ⟨hGleb, hMleb, hσvan⟩ := hx₀
  have hx₀norm : ‖x₀‖ < 1 / 3 := by
    have h := hx₀ball
    rw [mem_ball, dist_zero_right] at h
    exact h
  have hx₀s : x₀ ∈ ball (0:ℝ⁴) (1/2) := by rw [mem_ball, dist_zero_right]; linarith
  have hx₀3 : x₀ ∈ ball (0:ℝ⁴) 3 := by rw [mem_ball, dist_zero_right]; linarith
  -- ## the pointwise slope estimate
  have hC3 : ∀ k, ContDiffOn ℝ 3 (u k) (ball 0 3) := by
    intro k
    exact ((hadm k).2.2.1.mono (fun x hx => (hadm k).2.1 (ball_subset_closedBall hx))).of_le
      (by norm_num)
  have hσ3 : ∀ k x, x ∈ ball 0 3 → σ₂ (H (u k) (ball 0 3) x) = 1 := by
    intro k x hx
    rw [H_congr_of_mem_nhds (isOpen_ball.mem_nhds hx) ((hadm k).1.mem_nhds ((hadm k).2.1
      (ball_subset_closedBall hx)))]
    exact (hadm k).2.2.2.1 x ((hadm k).2.1 (ball_subset_closedBall hx))
  have hΔ3 : ∀ k x, x ∈ ball 0 3 → 0 < (Δ (u k)) x :=
    fun k x hx => (hadm k).2.2.2.2.1 x ((hadm k).2.1 (ball_subset_closedBall hx))
  have hb3 : ∀ k x, x ∈ closedBall (0:ℝ⁴) 3 → |u k x| ≤ Γ - 4 :=
    fun k x hx => (hadm k).2.2.2.2.2.1 x hx
  obtain ⟨A, hApos, hA⟩ := point_estimate_limit (g := g) (u := u) (G := G) (M := M)
    hIG x₀ hgcont hC3 hσ3 hΔ3 hb3 hconv
  have hR : 0 < 3 - ‖x₀‖ := by linarith
  -- ## the `L¹` average bound (the analytic core)
  set g₁ : ℝ⁴ → ℝ := (Metric.closedBall (0 : ℝ⁴) 3).indicator g with hg₁
  have hg₁g : ∀ x ∈ Metric.closedBall (0 : ℝ⁴) 3, g₁ x = g x := by
    intro x hx
    rw [hg₁]
    exact Set.indicator_of_mem hx g
  have hg₁int : Integrable g₁ volume := by
    rw [hg₁]
    exact (integrable_indicator_iff measurableSet_closedBall).mpr
      (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : ℝ⁴) 3) hgcont)
  have hg₁li : LocallyIntegrable g₁ volume := hg₁int.locallyIntegrable
  have hg₁cont : ContinuousOn g₁ (ball (0:ℝ⁴) (1/2)) :=
    hgcont3.congr_mono (fun x hx => hg₁g x (ball_subset_closedBall (hsubb hx))) hsubb
  have hwg₁ : HasWeakGradient g₁ (ball (0:ℝ⁴) (1/2)) G :=
    HasWeakGradient.congr_of_eqOn hwg
      (fun x hx => (hg₁g x (ball_subset_closedBall (hsubb hx))).symm)
  have hwh₁ : HasWeakHessian g₁ (ball (0:ℝ⁴) (1/2)) M σ :=
    HasWeakHessian.congr_of_eqOn hwh
      (fun x hx => (hg₁g x (ball_subset_closedBall (hsubb hx))).symm)
  have hTay₁ := hT g₁ (ball (0:ℝ⁴) (1/2)) x₀ isOpen_ball hx₀s hg₁cont hg₁li G M σ hGli hMli
    hwg₁ hwh₁ hGleb hMleb hσvan
  have hx₀cl : x₀ ∈ Metric.closedBall (0 : ℝ⁴) 3 := ball_subset_closedBall hx₀3
  have hTay : ∀ ε > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (∫ y in ball x₀ r, |taylorRemainder g G M x₀ y|) / (volume (ball x₀ r)).toReal
        ≤ ε * r ^ 2 := by
    intro ε hε
    filter_upwards [hTay₁ ε hε, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr hrlt
    refine le_of_eq_of_le ?_ hr
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hy3 : y ∈ Metric.closedBall (0 : ℝ⁴) 3 := by
      rw [Metric.mem_closedBall]
      rw [Metric.mem_ball, dist_eq_norm] at hy
      have h1 : ‖y‖ ≤ ‖y - x₀‖ + ‖x₀‖ := by
        calc ‖y‖ = ‖(y - x₀) + x₀‖ := congrArg (fun u => ‖u‖) (by abel)
          _ ≤ _ := norm_add_le _ _
      rw [dist_zero_right]
      linarith [hy, hx₀norm, hrlt.2]
    show |taylorRemainder g G M x₀ y| = |taylorRemainder g₁ G M x₀ y|
    simp only [taylorRemainder, hg₁g y hy3, hg₁g x₀ hx₀cl]
  -- ## the maximum principle `lem:pto(r^2)`
  have hsup := Commons.Measure.Lebesgue.sup_le_of_average_and_slope
    (h := fun y : ℝ⁴ => taylorRemainder g G M x₀ y) (R := 3 - ‖x₀‖)
    hApos.le hR hTay (fun r hr hrR y hy z hz hyz => hA r hr hrR y hy z hz hyz)
  have hsup2 : ∀ ε > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ y ∈ ball x₀ r,
      |taylorRemainder g G M x₀ y| ≤ ε * r ^ 2 := by
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp (hsup (ε / 4) (by positivity))
    have hδ' : ∀ r : ℝ, r ∈ Ioo (0 : ℝ) δ → ∀ y : ℝ⁴, y ∈ ball x₀ (r / 2) →
        |taylorRemainder g G M x₀ y| ≤ (ε / 4) * r ^ 2 := hδ
    refine (nhdsGT_basis (0 : ℝ)).eventually_iff.mpr ⟨δ / 2, by positivity, ?_⟩
    intro r hr y hy
    obtain ⟨hrpos, hrδ⟩ := hr
    have h1 : 2 * r ∈ Ioo (0 : ℝ) δ := ⟨by linarith, by linarith⟩
    have hball : (2 * r) / 2 = r := by ring
    have hmem : y ∈ ball x₀ ((2 * r) / 2) := by rwa [hball]
    have h2 := hδ' (2 * r) h1 y hmem
    have he : ε / 4 * (2 * r) ^ 2 = ε * r ^ 2 := by ring
    rwa [he] at h2
  refine ⟨x₀, hx₀ball, innerSL ℝ (G x₀), quadM M x₀, ?_⟩
  have hEq : (fun z : ℝ⁴ => g z - g x₀ - (innerSL ℝ (G x₀)) (z - x₀)
      - quadM M x₀ (z - x₀) (z - x₀)) = fun z => taylorRemainder g G M x₀ z := by
    funext z
    rw [taylorRemainder_eq]
  rw [hEq]
  exact Commons.Analysis.Asymptotics.isLittleO_of_sup_ball_bound
    (taylorRemainder_self g G M x₀) hsup2

/-- **The master estimate of Section 5**, from Trudinger's classical interior gradient estimate
and Savin's small perturbation theorem. -/
theorem masterBound_exists_limit (hIG : InteriorGradientBound) (hSavin : SavinInput) :
    ∃ B : ℝ → ℝ, IsMasterBound B := by
  classical
  have key : ∀ Γ : ℝ, 4 ≤ Γ → ∃ M : ℝ, ∀ (u : ℝ⁴ → ℝ) (s : Set ℝ⁴),
      Adm Γ u s → (Δ u) 0 ≤ M := by
    intro Γ hΓ
    by_contra hcon
    push_neg at hcon
    choose u s hadm hbig using fun n : ℕ => hcon (n : ℝ)
    obtain ⟨φ, g, hφ, hconv, hsol, hsub⟩ := extraction hΓ hadm
    have hc2 : ∀ k, ContDiffOn ℝ 2 (u (φ k)) (ball (0 : ℝ⁴) 3) := by
      intro k
      have hm := hadm (φ k)
      exact ((hm.2.2.1).mono (fun _ hx => hm.2.1 (ball_subset_closedBall hx))).of_le
        (m := 2) (by norm_num)
    have hcont : ∀ k, ContinuousOn (u (φ k)) (ball (0 : ℝ⁴) 3) := fun k => (hc2 k).continuousOn
    have hconvStab : ∀ K ⊆ ball (0 : ℝ⁴) 3, IsCompact K →
        TendstoUniformlyOn (fun k => u (φ k)) g atTop K := by
      intro K hK _
      rw [Metric.tendstoUniformlyOn_iff]
      intro δ hδ
      filter_upwards [hconv δ hδ] with k hk
      intro z hz
      have h1 := hk z (ball_subset_closedBall (hK hz))
      rw [Real.dist_eq]
      rwa [abs_sub_comm]
    have hvisc : IsViscSolution (fun M => -Gop M) g (ball (0 : ℝ⁴) 3) :=
      isViscSolution_of_tendstoUniformly continuous_Gop.neg isOpen_ball hcont hsol hconvStab
    have hsubharm : IsViscSubsolution negTrace g (ball (0 : ℝ⁴) 3) :=
      isViscSubsolution_of_tendstoUniformly continuous_negTrace isOpen_ball hcont hsub
        hconvStab
    have hgcont : ContinuousOn g (closedBall (0 : ℝ⁴) 3) := by
      have hunif : TendstoUniformlyOn (fun k => u (φ k)) g atTop (closedBall (0 : ℝ⁴) 3) := by
        rw [Metric.tendstoUniformlyOn_iff]
        intro δ hδ
        filter_upwards [hconv δ hδ] with k hk
        intro z hz
        simpa [Real.dist_eq, abs_sub_comm] using hk z hz
      exact hunif.continuousOn (Eventually.of_forall fun k =>
        ((hadm (φ k)).2.2.1.mono (hadm (φ k)).2.1).continuousOn).frequently
    obtain ⟨y, hy, htwice⟩ :=
      alexandrov_of_limit hIG hessianMeasureInput_holds taylorCoreInput_holds hΓ
        (fun k => hadm (φ k)) hconv hgcont hvisc hsubharm
    have hy3' : y ∈ ball (0 : ℝ⁴) 3 := ball_subset_ball (by norm_num) hy
    obtain ⟨ρ₀, η, hρ₀pos, hηpos, hS⟩ := hSavin g y hy3' hvisc htwice
    set ρ : ℝ := min ρ₀ (2 / 3) with hρdef
    have hρpos : 0 < ρ := lt_min hρ₀pos (by norm_num)
    have hρle : ρ ≤ ρ₀ := min_le_left _ _
    have hρ23 : ρ ≤ 2 / 3 := min_le_right _ _
    obtain ⟨C, hCpos, hSbound⟩ := hS ρ hρpos hρle
    have hy3 : ‖y‖ < 1 / 3 := by rw [mem_ball, dist_zero_right] at hy; exact hy
    have hyc : ball y ρ ⊆ closedBall (0 : ℝ⁴) 3 := by
      intro z hz
      rw [Metric.mem_ball] at hz
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖z‖ ≤ dist z y + ‖y‖ := by
        simpa only [dist_zero_right] using dist_triangle z y 0
      linarith
    have hev : ∀ᶠ k in atTop, ∀ z ∈ ball y ρ, |u (φ k) z - g z| ≤ η * ρ ^ 2 := by
      filter_upwards [hconv (η * ρ ^ 2) (by positivity)] with k hk
      intro z hz
      exact le_of_lt (hk z (hyc hz))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨k0, hk0⟩ := hev
    have hδpos : 0 < ρ / 2 := by positivity
    have hρ2lt : ρ / 2 < 4 / 3 := by linarith
    obtain ⟨C', hC'pos, hdouble⟩ :=
      doubling_moving_center_const (Γ := Γ) hΓ (ρ / 2) hδpos
    have hcontr : ∀ k ≥ k0, (Δ (u (φ k))) 0 ≤ C' * C := by
      intro k hk
      have hclose := hk0 k hk
      have hm := hadm (φ k)
      have hbound : ∀ z ∈ closedBall y (ρ / 2), (Δ (u (φ k))) z ≤ C :=
        hSbound (u (φ k)) (s (φ k)) hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2.1
          (fun z hz => hm.2.1 (hyc hz)) hclose
      have hsup : sSup ((fun z : ℝ⁴ => (Δ (u (φ k))) z) '' ball y (ρ / 2)) ≤ C := by
        refine csSup_le ⟨(Δ (u (φ k))) y, y, mem_ball_self hδpos, rfl⟩ ?_
        rintro w ⟨z, hz, rfl⟩
        exact hbound z (ball_subset_closedBall hz)
      have h0 : (0 : ℝ⁴) ∈ ball (0 : ℝ⁴) 2 := by
        rw [Metric.mem_ball, dist_zero_right]; norm_num
      have hd := hdouble (u (φ k)) (s (φ k)) hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2.1
        hm.2.2.2.2.2.1 hm.2.2.2.2.2.2 y hy (ρ / 2) le_rfl hρ2lt 0 h0
      have h1 : C' * sSup ((fun z : ℝ⁴ => (Δ (u (φ k))) z) '' ball y (ρ / 2)) ≤ C' * C :=
        mul_le_mul_of_nonneg_left hsup (le_of_lt hC'pos)
      linarith
    obtain ⟨k, hk⟩ := exists_nat_gt (max (C' * C) (k0 : ℝ))
    have hk0k : k0 ≤ k := by exact_mod_cast le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk)
    have hbig' : (φ k : ℝ) < (Δ (u (φ k))) 0 := hbig (φ k)
    have hφk : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast hφ.id_le k
    have hck : C' * C < (φ k : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hk (by exact_mod_cast (hφ.id_le k)))
    linarith [hcontr k hk0k]
  refine ⟨fun Γ => if h : 4 ≤ Γ then Classical.choose (key Γ h) else 0, ?_⟩
  intro Γ hΓ u s hs hsub hu hσ hΔ hb1 hb2
  dsimp only
  rw [dif_pos hΓ]
  exact Classical.choose_spec (key Γ hΓ) u s ⟨hs, hsub, hu, hσ, hΔ, hb1, hb2⟩

end Submission
