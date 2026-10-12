import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.bsOneBody_eq_dirichlet
import Submission.Work.BoseFixB1S.fsTBumpDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.bsOneBody_sq_ge_dirichlet`

The plateau lower bound for the one-body big-box kinetic form at the symbol `F(r) = r²`:

    `chiPlateau² · Σ_k ∫ (∂_k θ)²  ≤  bsOneBody ℓ (·)² 0 θ`,

for a smooth bump `θ` supported in `Metric.ball 0 r` with `4r ≤ ℓ`.

The point is that `θ` is supported *strictly inside* the plateau of the window
`chiScale ℓ = χ(·/ℓ)`: on `ball 0 (ℓ/4)` the window is the constant `chiPlateau`
(`chiScale_eq_chiPlateau`), and `ball 0 r ⊆ ball 0 (ℓ/4)` by `4r ≤ ℓ`.  So

* for `‖x‖ < ℓ/4` the windowed mean-free state `χ·Q_{Λ}θ` has gradient
  `chiPlateau·∇θ` at `x` (the window is locally constant and the box mean is a
  constant), while
* for `‖x‖ ≥ ℓ/4` the state `θ` vanishes in a neighbourhood of `x` (its support is
  inside `ball 0 r`), so `∇θ x = 0`.

Hence the pointwise inequality `chiPlateau²(∂_kθ x)² ≤ (∂_k(χ·Q_{Λ}θ) x)²`
holds everywhere, and integrating (both functions are continuous with compact
support) plus the finite-sum/積 interchange gives the claim.  The left-hand side
is converted into the Dirichlet word `∫ Σ_k (∂_k(χ·Q_{Λ}θ))²` by the corpus's
Plancherel identity `Work.BSKinetic.bsOneBody_eq_dirichlet`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.BoseFixB1S

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The window `chiScale ℓ` is *locally constant* at every point of the open ball of
radius `ℓ/4`: there it equals the plateau value `chiPlateau`. -/
lemma chiScale_eventuallyEq_chiPlateau {ℓ : ℝ} (hℓ : 0 < ℓ) {x : ℝ³}
    (hx : ‖x‖ < ℓ / 4) :
    Submission.BoseGases.chiScale ℓ =ᶠ[𝓝 x] (fun _ => chiPlateau) := by
  refine Metric.eventually_nhds_iff.mpr ⟨ℓ / 4 - ‖x‖, by linarith, ?_⟩
  intro y hy
  rw [dist_eq_norm] at hy
  exact chiScale_eq_chiPlateau hℓ (by
    have h : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
      calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
    linarith)

/-- **The plateau lower bound, in Dirichlet form.**  For a smooth `θ` supported in
`Metric.ball 0 r` with `4r ≤ ℓ`, the weighted Dirichlet energy of the windowed
mean-free state `bsWin ℓ 0 · bsQ ℓ 0 θ` dominates `chiPlateau²` times that of `θ`. -/
lemma bsWin_bsQ_dirichlet_ge {ℓ r : ℝ} (hr : 0 < r) (hℓ : 4 * r ≤ ℓ)
    {θ : ℝ³ → ℝ} (hθ : ContDiff ℝ (⊤ : ENat) θ)
    (hsupp : tsupport θ ⊆ Metric.ball 0 r) :
    chiPlateau ^ 2 *
        (∑ k : Fin 3, ∫ z : ℝ³,
          (fderiv ℝ θ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
      ≤ ∫ z : ℝ³, ∑ k : Fin 3,
          (fderiv ℝ (fun y : ℝ³ =>
              Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  have hℓpos : 0 < ℓ := by linarith
  have hr4 : r ≤ ℓ / 4 := by linarith
  -- the window at `u = 0` is `chiScale ℓ`
  have hbsWin : Work.BSKinetic.bsWin ℓ 0 = Submission.BoseGases.chiScale ℓ := by
    funext x; simp [Work.BSKinetic.bsWin]
  -- `θ` has compact support (its support lies in `ball 0 r`)
  have hθcs : HasCompactSupport θ := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall (0:ℝ³) r)
      (isCompact_closedBall 0 r) ?_
    intro x hx
    have hx1 : x ∈ tsupport θ := subset_tsupport θ hx
    have hx2 : ‖x‖ < r := by
      have := hsupp hx1
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at this
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using le_of_lt hx2
  -- smoothness and compact support of the window, the mean-free state and their product
  have hχsmooth : ContDiff ℝ (⊤ : ENat) (Work.BSKinetic.bsWin ℓ 0) := by
    rw [hbsWin]; exact Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓpos)
  have hQsmooth : ContDiff ℝ (⊤ : ENat) (Work.BSKinetic.bsQ ℓ 0 θ) := by
    rw [show Work.BSKinetic.bsQ ℓ 0 θ
        = fun x : ℝ³ => θ x - Work.BSKinetic.bsMean ℓ 0 θ from rfl]
    exact hθ.sub contDiff_const
  have hχcs : HasCompactSupport (Work.BSKinetic.bsWin ℓ 0) := by
    rw [hbsWin]
    exact Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓpos)
  have hFsmooth : ContDiff ℝ (⊤ : ENat)
      (fun y : ℝ³ => Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y) :=
    hχsmooth.mul hQsmooth
  have hFcs : HasCompactSupport
      (fun y : ℝ³ => Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y) :=
    hχcs.mul_right
  -- the pointwise inequality
  have hpt : ∀ (k : Fin 3) (x : ℝ³),
      chiPlateau ^ 2 * (fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k)) ^ 2
        ≤ (fderiv ℝ (fun y : ℝ³ =>
              Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y) x
            (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
    intro k x
    by_cases hx : ‖x‖ < ℓ / 4
    · -- on the plateau the window is locally constant and the mean is a constant
      have hevχ := chiScale_eventuallyEq_chiPlateau hℓpos hx
      have hev : (fun y : ℝ³ => Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y)
          =ᶠ[𝓝 x] (fun y : ℝ³ => chiPlateau * (θ y - Work.BSKinetic.bsMean ℓ 0 θ)) := by
        filter_upwards [hevχ] with y hy
        simp [Work.BSKinetic.bsWin, Work.BSKinetic.bsQ, hy]
      have hder : fderiv ℝ (fun y : ℝ³ =>
            Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y) x
            (Submission.BoseGases.kcStdBasis k)
          = chiPlateau * fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k) := by
        rw [hev.fderiv_eq]
        rw [fderiv_const_mul]
        · rw [fderiv_sub_const]
          simp [smul_eq_mul]
        · exact ((hθ.differentiable (by simp)) x).sub_const _
      rw [hder, mul_pow]
    · -- off the plateau `θ` vanishes in a neighbourhood of `x`
      replace hx := not_lt.mp hx
      have hz : fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k) = 0 := by
        have hxr : x ∉ Metric.ball (0:ℝ³) r := by
          intro hmem
          have h1 : ‖x‖ < r := by
            rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hmem
          linarith
        have hxt : x ∉ tsupport θ := fun h => hxr (hsupp h)
        have hmem : (tsupport θ)ᶜ ∈ 𝓝 x :=
          (isClosed_tsupport θ).isOpen_compl.mem_nhds (by simpa using hxt)
        have hev : θ =ᶠ[𝓝 x] (Function.const ℝ³ (0:ℝ)) :=
          Filter.eventually_of_mem hmem (fun y hy => by
            by_contra h
            exact hy (subset_tsupport θ (Function.mem_support.mpr h)))
        rw [hev.fderiv_eq, fderiv_const]
        simp
      rw [hz]
      have h0 : chiPlateau ^ 2 * (0:ℝ) ^ 2 = 0 := by ring
      rw [h0]
      exact sq_nonneg _
  -- integrability of the two families of Dirichlet densities
  have hIntθ : ∀ k : Fin 3, Integrable (fun x : ℝ³ =>
      (fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
    intro k
    have hcs : HasCompactSupport
        (fun x : ℝ³ => fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k)) := by
      have h := (hθcs.fderiv ℝ).comp_left
        (g := fun L : ℝ³ →L[ℝ] ℝ => L (Submission.BoseGases.kcStdBasis k)) (by simp)
      simpa [Function.comp_def] using h
    have hcont : Continuous
        (fun x : ℝ³ => fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k)) :=
      (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hres : Integrable (fun x : ℝ³ => fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k)
        * fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k)) :=
      Continuous.integrable_of_hasCompactSupport (hcont.mul hcont)
        (hcs.mul_right (f' := fun x : ℝ³ => fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k)))
    simpa [pow_two] using hres
  have hIntF : ∀ k : Fin 3, Integrable (fun x : ℝ³ =>
      (fderiv ℝ (fun y : ℝ³ =>
          Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y) x
        (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
    intro k
    have hcs : HasCompactSupport (fun x : ℝ³ =>
        fderiv ℝ (fun y : ℝ³ =>
          Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y) x
          (Submission.BoseGases.kcStdBasis k)) := by
      have h := (hFcs.fderiv ℝ).comp_left
        (g := fun L : ℝ³ →L[ℝ] ℝ => L (Submission.BoseGases.kcStdBasis k)) (by simp)
      simpa [Function.comp_def] using h
    have hcont : Continuous (fun x : ℝ³ =>
        fderiv ℝ (fun y : ℝ³ =>
          Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y) x
          (Submission.BoseGases.kcStdBasis k)) :=
      (hFsmooth.continuous_fderiv (by simp)).clm_apply continuous_const
    have hres : Integrable (fun x : ℝ³ =>
        fderiv ℝ (fun y : ℝ³ =>
            Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y) x
          (Submission.BoseGases.kcStdBasis k)
        * fderiv ℝ (fun y : ℝ³ =>
            Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y) x
          (Submission.BoseGases.kcStdBasis k)) :=
      Continuous.integrable_of_hasCompactSupport (hcont.mul hcont)
        (hcs.mul_right (f' := fun x : ℝ³ => fderiv ℝ (fun y : ℝ³ =>
            Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y) x
            (Submission.BoseGases.kcStdBasis k)))
    simpa [pow_two] using hres
  -- assemble
  calc chiPlateau ^ 2 *
        (∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ θ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = ∑ k : Fin 3, chiPlateau ^ 2 *
          ∫ z : ℝ³, (fderiv ℝ θ z (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
        rw [Finset.mul_sum]
    _ = ∑ k : Fin 3, ∫ z : ℝ³,
          chiPlateau ^ 2 * (fderiv ℝ θ z (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [MeasureTheory.integral_const_mul]
    _ ≤ ∑ k : Fin 3, ∫ z : ℝ³,
          (fderiv ℝ (fun y : ℝ³ =>
              Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
        Finset.sum_le_sum (fun k _ =>
          integral_mono ((hIntθ k).const_mul _) (hIntF k) (fun x => hpt k x))
    _ = ∫ z : ℝ³, ∑ k : Fin 3,
          (fderiv ℝ (fun y : ℝ³ =>
              Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
        exact (MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin 3))
          (f := fun k z => (fderiv ℝ (fun y : ℝ³ =>
              Work.BSKinetic.bsWin ℓ 0 y * Work.BSKinetic.bsQ ℓ 0 θ y) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2)
          (fun k _ => hIntF k)).symm

theorem bsOneBody_sq_ge_dirichlet {ℓ r : ℝ} (hr : 0 < r) (hℓ : 4 * r ≤ ℓ)
    {θ : EuclideanSpace ℝ (Fin 3) → ℝ} (hθ : ContDiff ℝ (⊤ : ENat) θ)
    (hsupp : tsupport θ ⊆ Metric.ball 0 r) :
    Work.BoseFixB1S.chiPlateau ^ 2 *
        (∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
          (fderiv ℝ θ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
      ≤ Work.BSKinetic.bsOneBody ℓ (fun r => r ^ 2) 0 θ := by
  have hℓpos : 0 < ℓ := by linarith
  rw [Work.BSKinetic.bsOneBody_eq_dirichlet hℓpos 0 θ hθ]
  exact bsWin_bsQ_dirichlet_ge hr hℓ hθ hsupp

end Work.BoseFixB1S
