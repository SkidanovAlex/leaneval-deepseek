import Mathlib
import Submission.Work.Whitney.exists_tubular_param_general_smooth

/-!
# Tubular data for a smooth immersion, smoothly

Let `M` be a smooth `n`-manifold modelled on `EuclideanSpace ℝ (Fin n)`, let
`f : M → EuclideanSpace ℝ (Fin (2 * n))` be a smooth immersion, and let
`c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))` be a chart of `M` whose origin is in its
target and whose two directions are smooth (i.e. `c` and `c.symm` are `C^∞`).

Then there is a smooth map `H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
EuclideanSpace ℝ (Fin (2 * n))` together with radii `ρ, L > 0` such that

* `H (u, 0) = f (c.symm u)` for all `u` (so `H` extends the chart representation `f ∘ c.symm`),
* `H` is injective on the ball of radius `ρ` around `0`,
* the Fréchet derivative of `H` is injective at every point of that ball,
* `H` is `L`-Lipschitz on that ball.

The construction is the abstract straightening lemma
`Work.Whitney.exists_tubular_param_general_smooth` applied to the chart representation
`φ = e⁻¹ ∘ (f ∘ c.symm)`, where `e : (ℝⁿ × ℝⁿ) ≃L ℝ^{2n}` is any continuous linear equivalence
(these two spaces have the same finite dimension `2n`).  Writing `H'` for the straightening of
`φ` and putting `H = e ∘ H'`, the first three properties are immediate; the Lipschitz constant is
obtained from the mean value inequality, using that `e` (linear, hence smooth) has bounded
derivative and a bound on `fderiv ℝ H` on a sufficiently small ball.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology Filter

theorem exists_tubular_data_smooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target)
    (hcsm : ∀ y : M, y ∈ c.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hsymm : ∀ u : EuclideanSpace ℝ (Fin n),
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u) :
    ∃ (H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin (2 * n))) (ρ L : ℝ),
      0 < ρ ∧ 0 < L ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H ∧
      (∀ u : EuclideanSpace ℝ (Fin n), H (u, 0) = f (c.symm u)) ∧
      Set.InjOn H (Metric.ball 0 ρ) ∧
      (∀ z ∈ Metric.ball 0 ρ, Function.Injective (fderiv ℝ H z)) ∧
      (∀ z ∈ Metric.ball 0 ρ, ∀ z' ∈ Metric.ball 0 ρ, ‖H z - H z'‖ ≤ L * ‖z - z'‖) := by
  classical
  -- (0) `c.symm` is smooth everywhere, so the chart representation `F := f ∘ c.symm` is smooth.
  have hcsymm : ContMDiff (𝓡 n) (𝓡 n) ∞ c.symm := hsymm
  have hFcd : ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u)) :=
    contMDiff_iff_contDiff.mp (hf.comp hcsymm)
  -- (1) the Fréchet derivative of the chart representation at `0` is injective.
  have hFinj : Function.Injective
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u)) 0) := by
    have hu : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target := h0
    have hxsrc : c.symm 0 ∈ c.source := c.map_target hu
    have hx : c (c.symm 0) = 0 := c.right_inv hu
    -- both directions of `c` are smooth, hence `c` is a differentiable open partial homeomorph
    have hMD : c.MDifferentiable (𝓡 n) (𝓡 n) :=
      ⟨fun x hx => ((hcsm x hx).mdifferentiableAt (by simp)).mdifferentiableWithinAt,
       fun x _ => ((hsymm x).mdifferentiableAt (by simp)).mdifferentiableWithinAt⟩
    have hdc : MDifferentiableAt (𝓡 n) (𝓡 n) c (c.symm 0) := hMD.mdifferentiableAt hxsrc
    have hdsymm : MDifferentiableAt (𝓡 n) (𝓡 n) c.symm 0 := hMD.mdifferentiableAt_symm hu
    have hdf : MDifferentiableAt (𝓡 n) (𝓡 (2 * n)) f (c.symm 0) :=
      (hf (c.symm 0)).mdifferentiableAt (by simp)
    have hdrep : MDifferentiableAt (𝓡 n) (𝓡 (2 * n))
        (fun y : EuclideanSpace ℝ (Fin n) => f (c.symm y)) (c (c.symm 0)) := by
      have h := MDifferentiableAt.comp 0 hdf hdsymm
      rw [← hx] at h
      exact h
    -- chain rule for `((fun y => f (c.symm y)) ∘ c)` at `c.symm 0`
    have hcr := mfderiv_comp (c.symm 0) hdrep hdc
    -- the composite agrees with `f` near `c.symm 0`
    have heq : mfderiv (𝓡 n) (𝓡 (2 * n)) ((fun y => f (c.symm y)) ∘ c) (c.symm 0) =
        mfderiv (𝓡 n) (𝓡 (2 * n)) f (c.symm 0) := by
      apply Filter.EventuallyEq.mfderiv_eq
      filter_upwards [c.open_source.mem_nhds hxsrc] with y hy
      simp only [Function.comp_apply]
      rw [c.left_inv hy]
    -- the chain-rule decomposition of `mfderiv f` through `c`
    have hdecomp : mfderiv (𝓡 n) (𝓡 (2 * n)) f (c.symm 0) =
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => f (c.symm y)) 0) ∘SL
          (mfderiv (𝓡 n) (𝓡 n) c (c.symm 0)) := by
      rw [← heq, hcr, mfderiv_eq_fderiv, hx]
      rfl
    -- the manifold derivative of the chart is onto
    have hsurj : Function.Surjective (mfderiv (𝓡 n) (𝓡 n) c (c.symm 0)) :=
      hMD.mfderiv_surjective hxsrc
    have hmain := himm (c.symm 0)
    intro a b hab
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    refine congrArg (mfderiv (𝓡 n) (𝓡 n) c (c.symm 0)) (hmain ?_)
    rw [hdecomp]
    exact hab
  -- (2) a continuous linear equivalence `ℝⁿ × ℝⁿ ≃L ℝ^{2n}` (same finite dimension `2n`).
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) := by
    rw [Module.finrank_prod]
    simp [Nat.two_mul]
  let e : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)) :=
    (LinearEquiv.ofFinrankEq (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin (2 * n))) hdim).toContinuousLinearEquiv
  let es : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) := e.symm
  let ee : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)) := e
  -- (3) the chart representation, pushed into `ℝⁿ × ℝⁿ`.
  let φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    fun u => es (f (c.symm u))
  have hφcd : ContDiff ℝ ∞ φ := by
    show ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin n) => es (f (c.symm u)))
    exact es.contDiff.comp hFcd
  have hφdInj : Function.Injective (fderiv ℝ φ 0) := by
    have hFd : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u))
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u)) 0) 0 :=
      ((hFcd.differentiable (by simp)).differentiableAt (x := 0)).hasFDerivAt
    have hcomp := (ContinuousLinearMap.hasFDerivAt es).comp 0 hFd
    have hfd : fderiv ℝ φ 0 = es.comp (fderiv ℝ
        (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u)) 0) := by
      have hfun : φ = (⇑es ∘ fun u => f (c.symm u)) := by funext u; rfl
      rw [hfun]
      exact hcomp.fderiv
    rw [hfd]
    have hes_inj : Function.Injective (es : EuclideanSpace ℝ (Fin (2 * n)) →
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) := e.symm.injective
    exact hes_inj.comp hFinj
  -- (4) straighten `φ`.
  obtain ⟨H', ρ', hρ'pos, hH'cd, hH'0, hH'inj, hH'fd⟩ :=
    exists_tubular_param_general_smooth φ hφcd hφdInj
  -- (5) transport back through `e`.
  let H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin (2 * n)) := fun z => ee (H' z)
  have hHcd : ContDiff ℝ ∞ H := by
    show ContDiff ℝ ∞ (fun z => ee (H' z))
    exact ee.contDiff.comp hH'cd
  have hH0 : ∀ u : EuclideanSpace ℝ (Fin n), H (u, 0) = f (c.symm u) := by
    intro u
    show ee (H' (u, 0)) = f (c.symm u)
    rw [hH'0 u]
    have h2 : ee (es (f (c.symm u))) = f (c.symm u) := by
      show (e : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
          EuclideanSpace ℝ (Fin (2 * n)))
          ((e.symm : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
            (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (f (c.symm u))) =
        f (c.symm u)
      simp only [ContinuousLinearEquiv.coe_coe]
      exact e.apply_symm_apply (f (c.symm u))
    exact h2
  have hHinj : Set.InjOn H (Metric.ball 0 ρ') := by
    intro z hz z' hz' h
    exact hH'inj hz hz' (e.injective h)
  have hHfd : ∀ z ∈ Metric.ball 0 ρ', Function.Injective (fderiv ℝ H z) := by
    intro z hz
    have hzd : HasFDerivAt H' (fderiv ℝ H' z) z :=
      ((hH'cd.differentiable (by simp)).differentiableAt (x := z)).hasFDerivAt
    have hcomp := (ContinuousLinearMap.hasFDerivAt ee).comp z hzd
    have hfd : fderiv ℝ H z = ee.comp (fderiv ℝ H' z) := by
      have hfun : H = (⇑ee ∘ H') := by funext z; rfl
      rw [hfun]
      exact hcomp.fderiv
    rw [hfd]
    have hee_inj : Function.Injective (ee :
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →
        EuclideanSpace ℝ (Fin (2 * n))) := e.injective
    exact hee_inj.comp (hH'fd z hz)
  -- (6) shrink the ball so that `fderiv ℝ H` is bounded by `L := ‖fderiv ℝ H 0‖ + 1`.
  have hHcont : Continuous (fderiv ℝ H) := hHcd.continuous_fderiv (by simp)
  let L : ℝ := ‖fderiv ℝ H 0‖ + 1
  have hLpos : 0 < L := by
    have : (0 : ℝ) ≤ ‖fderiv ℝ H 0‖ := norm_nonneg _
    dsimp only [L]; linarith
  have hmem : {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      fderiv ℝ H z ∈ Metric.ball (fderiv ℝ H 0) 1} ∈
      𝓝 (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    hHcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ zero_lt_one)
  obtain ⟨ρ₀, hρ₀pos, hρ₀sub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨H, min ρ' ρ₀, L, lt_min hρ'pos hρ₀pos, hLpos, hHcd, hH0, ?_, ?_, ?_⟩
  · intro z hz z' hz' h
    exact hHinj (Metric.ball_subset_ball (min_le_left _ _) hz)
      (Metric.ball_subset_ball (min_le_left _ _) hz') h
  · intro z hz
    exact hHfd z (Metric.ball_subset_ball (min_le_left _ _) hz)
  · intro z hz z' hz'
    have hdiff : ∀ x ∈ Metric.ball
        (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (min ρ' ρ₀),
        DifferentiableAt ℝ H x :=
      fun x _ => (hHcd.differentiable (by simp)).differentiableAt (x := x)
    have hbound : ∀ x ∈ Metric.ball
        (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (min ρ' ρ₀),
        ‖fderiv ℝ H x‖ ≤ L := by
      intro x hx
      have hx0 : fderiv ℝ H x ∈ Metric.ball (fderiv ℝ H 0) 1 :=
        hρ₀sub (Metric.ball_subset_ball (min_le_right _ _) hx)
      rw [Metric.mem_ball, dist_eq_norm] at hx0
      have hlt : ‖fderiv ℝ H x‖ < L := by
        calc ‖fderiv ℝ H x‖
            = ‖fderiv ℝ H 0 + (fderiv ℝ H x - fderiv ℝ H 0)‖ := by
              congr 1; abel
          _ ≤ ‖fderiv ℝ H 0‖ + ‖fderiv ℝ H x - fderiv ℝ H 0‖ := norm_add_le _ _
          _ < ‖fderiv ℝ H 0‖ + 1 := by linarith
          _ = L := rfl
      exact le_of_lt hlt
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (f := H) (s := Metric.ball
        (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (min ρ' ρ₀)) (C := L)
      hdiff hbound (convex_ball 0 _) hz' hz

end Work.Whitney
