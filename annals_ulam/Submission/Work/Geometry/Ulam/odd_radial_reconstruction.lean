import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Commons.Geometry.Ulam

open Filter
open scoped Topology ContDiff

noncomputable section

/-!
## The odd-dimensional radial reconstruction layer

For odd dimension `d = 2n+1`, the paper's final step replaces the moving
intersection functions `x,y` by radial functions `R(α), r(α)` solving

`R^(2n+2) + r^(2n+2) = Φ_h(α)/cos²α`,
`R^(2n+1) - r^(2n+1) = Ψ_h(α)/cosα`.

This file starts the layer by proving the local inverse of the polynomial map
`(R,r) ↦ (R^(2n+2)+r^(2n+2), R^(2n+1)-r^(2n+1))` near `(1,1)`, and then the
first existence lemma: for small smooth right-hand sides there are smooth
`R,r` close to `1` solving the system on `[0,π/2]`.
-/

/-- The first-row derivative of the radial map at `(1,1)`. -/
def radialLin1 (n : ℕ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  ((2 * n + 2 : ℕ) : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    ((2 * n + 2 : ℕ) : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The second-row derivative of the radial map at `(1,1)`. -/
def radialLin2 (n : ℕ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  ((2 * n + 1 : ℕ) : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ -
    ((2 * n + 1 : ℕ) : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The invertible derivative of the radial map at `(1,1)`. -/
def radialDeriv (n : ℕ) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toLinearMap := (radialLin1 n).prod (radialLin2 n)
  invFun q :=
    (q.1 / (2 * ((2 * n + 2 : ℕ) : ℝ)) + q.2 / (2 * ((2 * n + 1 : ℕ) : ℝ)),
     q.1 / (2 * ((2 * n + 2 : ℕ) : ℝ)) - q.2 / (2 * ((2 * n + 1 : ℕ) : ℝ)))
  left_inv := by
    intro p
    ext <;> simp [radialLin1, radialLin2]
    · field_simp
      ring
    · field_simp
      ring
  right_inv := by
    intro q
    ext <;> simp [radialLin1, radialLin2]
    · field_simp
      ring
    · field_simp
      ring
  continuous_toFun := (radialLin1 n).prod (radialLin2 n) |>.cont
  continuous_invFun := by continuity

/-- The polynomial map `(R,r) ↦ (R^(2n+2)+r^(2n+2), R^(2n+1)-r^(2n+1))`. -/
def radialMap (n : ℕ) : ℝ × ℝ → ℝ × ℝ := fun p =>
  (p.1 ^ (2 * n + 2) + p.2 ^ (2 * n + 2),
   p.1 ^ (2 * n + 1) - p.2 ^ (2 * n + 1))

lemma radialMap_hasFDerivAt (n : ℕ) :
    HasFDerivAt (radialMap n) (radialDeriv n : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (1, 1) := by
  have hfst : HasFDerivAt (fun p : ℝ × ℝ => p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (1, 1) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun p : ℝ × ℝ => p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 1) := hasFDerivAt_snd
  have h4 : HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ (2 * n + 2))
      (((2 * n + 2 : ℕ) : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ) (1, 1) := by
    simpa using hfst.pow (2 * n + 2)
  have h4s : HasFDerivAt (fun p : ℝ × ℝ => p.2 ^ (2 * n + 2))
      (((2 * n + 2 : ℕ) : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 1) := by
    simpa using hsnd.pow (2 * n + 2)
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ (2 * n + 2) + p.2 ^ (2 * n + 2))
      (radialLin1 n) (1, 1) := by
    have h := h4.add h4s
    change HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ (2 * n + 2) + p.2 ^ (2 * n + 2))
      (radialLin1 n) (1, 1) at h
    exact h
  have h3 : HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ (2 * n + 1))
      (((2 * n + 1 : ℕ) : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ) (1, 1) := by
    simpa using hfst.pow (2 * n + 1)
  have h3s : HasFDerivAt (fun p : ℝ × ℝ => p.2 ^ (2 * n + 1))
      (((2 * n + 1 : ℕ) : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 1) := by
    simpa using hsnd.pow (2 * n + 1)
  have h2 : HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ (2 * n + 1) - p.2 ^ (2 * n + 1))
      (radialLin2 n) (1, 1) := by
    have h := h3.sub h3s
    change HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ (2 * n + 1) - p.2 ^ (2 * n + 1))
      (radialLin2 n) (1, 1) at h
    exact h
  have hprod := h1.prodMk h2
  change HasFDerivAt (fun p : ℝ × ℝ =>
      (p.1 ^ (2 * n + 2) + p.2 ^ (2 * n + 2), p.1 ^ (2 * n + 1) - p.2 ^ (2 * n + 1)))
    (radialDeriv n : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (1, 1)
  exact hprod

lemma radialMap_contDiffAt (n : ℕ) : ContDiffAt ℝ (⊤ : ℕ∞) (radialMap n) (1, 1) := by
  unfold radialMap
  fun_prop

lemma radialMap_analyticAt (n : ℕ) : AnalyticAt ℝ (radialMap n) (1, 1) := by
  have hfst : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1) (1, 1) := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun p : ℝ × ℝ => p.2) (1, 1) := analyticAt_snd
  have h4 : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1 ^ (2 * n + 2)) (1, 1) := hfst.pow _
  have h4s : AnalyticAt ℝ (fun p : ℝ × ℝ => p.2 ^ (2 * n + 2)) (1, 1) := hsnd.pow _
  have h3 : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1 ^ (2 * n + 1)) (1, 1) := hfst.pow _
  have h3s : AnalyticAt ℝ (fun p : ℝ × ℝ => p.2 ^ (2 * n + 1)) (1, 1) := hsnd.pow _
  have h1 : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1 ^ (2 * n + 2) + p.2 ^ (2 * n + 2)) (1, 1) :=
    h4.add h4s
  have h2 : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1 ^ (2 * n + 1) - p.2 ^ (2 * n + 1)) (1, 1) :=
    h3.sub h3s
  change AnalyticAt ℝ (fun p : ℝ × ℝ =>
    (p.1 ^ (2 * n + 2) + p.2 ^ (2 * n + 2), p.1 ^ (2 * n + 1) - p.2 ^ (2 * n + 1))) (1, 1)
  exact h1.prod h2

lemma radialHN (n : ℕ) : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp

/-- The local inverse of the radial map near `(1,1)`. -/
noncomputable def radialLocalInv (n : ℕ) : ℝ × ℝ → ℝ × ℝ :=
  (radialMap_contDiffAt n).localInverse (radialMap_hasFDerivAt n) (radialHN n)

lemma radialLocalInv_smooth (n : ℕ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (radialLocalInv n) (radialMap n (1, 1)) :=
  (radialMap_contDiffAt n).to_localInverse (radialMap_hasFDerivAt n) (radialHN n)

lemma radialLocalInv_apply_image (n : ℕ) :
    radialLocalInv n (radialMap n (1, 1)) = (1, 1) :=
  (radialMap_contDiffAt n).localInverse_apply_image (radialMap_hasFDerivAt n) (radialHN n)

lemma radialLocalInv_analyticAt (n : ℕ) :
    AnalyticAt ℝ (radialLocalInv n) (radialMap n (1, 1)) := by
  let f := (radialMap_contDiffAt n).toOpenPartialHomeomorph (radialMap n)
    (radialMap_hasFDerivAt n) (radialHN n)
  have hfun : f.symm = radialLocalInv n := rfl
  have h0 : radialMap n (1, 1) ∈ f.target :=
    (radialMap_contDiffAt n).image_mem_toOpenPartialHomeomorph_target
      (radialMap_hasFDerivAt n) (radialHN n)
  have hsymm : f.symm (radialMap n (1, 1)) = (1, 1) := by
    rw [hfun]
    exact radialLocalInv_apply_image n
  have h_an : AnalyticAt ℝ (radialMap n) (f.symm (radialMap n (1, 1))) := by
    rw [hsymm]
    exact radialMap_analyticAt n
  have h_deriv : fderiv ℝ (radialMap n) (f.symm (radialMap n (1, 1))) = radialDeriv n := by
    rw [hsymm]
    exact (radialMap_hasFDerivAt n).fderiv
  have h := f.analyticAt_symm h0 h_an h_deriv
  rw [hfun] at h
  exact h

lemma radialLocalInv_right_inv_eventually (n : ℕ) :
    ∀ᶠ y in 𝓝 (radialMap n (1, 1)), radialMap n (radialLocalInv n y) = y := by
  have hstrict := (radialMap_contDiffAt n).hasStrictFDerivAt'
    (radialMap_hasFDerivAt n) (radialHN n)
  simpa [radialLocalInv, ContDiffAt.localInverse] using hstrict.eventually_right_inverse

lemma exists_radialLocalInv_right_inv_ball (n : ℕ) :
    ∃ δ > 0, ∀ y : ℝ × ℝ,
      dist y (radialMap n (1, 1)) < δ → radialMap n (radialLocalInv n y) = y := by
  exact Metric.eventually_nhds_iff.mp (radialLocalInv_right_inv_eventually n)

lemma exists_radialLocalInv_close_ball (n : ℕ) :
    ∃ δ > 0, ∀ y : ℝ × ℝ,
      dist y (radialMap n (1, 1)) < δ → dist (radialLocalInv n y) (1, 1) < 1 / 2 := by
  have hcont := (radialLocalInv_smooth n).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont (1 / 2) (by norm_num)
  refine ⟨δ, hδpos, ?_⟩
  intro y hy
  have h := hδ hy
  rwa [radialLocalInv_apply_image n] at h

lemma exists_radialLocalInv_contDiffOn_close (n : ℕ) :
    ∃ u ∈ 𝓝 (radialMap n (1, 1)),
      ContDiffOn ℝ (⊤ : ℕ∞) (radialLocalInv n) u ∧
      Set.MapsTo (radialLocalInv n) u (Metric.ball (1, 1) (1 / 2)) := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_radialLocalInv_close_ball n
  have hω : ContDiffAt ℝ (⊤ : WithTop ℕ∞) (radialLocalInv n) (radialMap n (1, 1)) :=
    (radialLocalInv_analyticAt n).contDiffAt
  obtain ⟨u, hu, hu_cont⟩ := hω.contDiffOn
    (le_rfl : (⊤ : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞)) (by intro _; rfl)
  refine ⟨u ∩ Metric.ball (radialMap n (1, 1)) δ, ?_, ?_, ?_⟩
  · exact Filter.inter_mem hu (Metric.ball_mem_nhds _ hδpos)
  · exact (hu_cont.of_le le_top).mono (Set.inter_subset_left)
  · intro y hy
    exact hδ y hy.2

private lemma dist_y_radialMap (n : ℕ) (A B : ℝ → ℝ) (α : ℝ) :
    dist ((2 + A α, B α)) (radialMap n (1, 1)) = max |A α| |B α| := by
  dsimp [radialMap]
  rw [Prod.dist_eq]
  have h1 : (1 : ℝ) ^ (2 * n + 2) + (1 : ℝ) ^ (2 * n + 2) = 2 := by norm_num
  have h2 : (1 : ℝ) ^ (2 * n + 1) - (1 : ℝ) ^ (2 * n + 1) = 0 := by norm_num
  rw [h1, h2]
  congr 1
  · rw [Real.dist_eq]; congr 1; ring
  · rw [Real.dist_eq]; congr 1; ring

/-- **First existence lemma for the odd radial chapter.**
For every `n ≥ 1` there is `ε > 0` such that for all smooth `A,B` on
`[0,π/2]`, uniformly `< ε`, vanishing at `π/2` with vanishing first
derivatives at `0`, there are smooth `R,r` close to `1` solving
`R^(2n+2)+r^(2n+2) = 2 + A`, `R^(2n+1)-r^(2n+1) = B` on `[0,π/2]`, with
`R(π/2)=r(π/2)=1`. -/
lemma spherical_radon_radial_reconstruction (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε > 0, ∀ A B : ℝ → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) A (Set.Icc 0 (Real.pi / 2)) →
      ContDiffOn ℝ (⊤ : ℕ∞) B (Set.Icc 0 (Real.pi / 2)) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |A α| < ε) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |B α| < ε) →
      A (Real.pi / 2) = 0 →
      B (Real.pi / 2) = 0 →
      deriv A 0 = 0 →
      deriv B 0 = 0 →
      ∃ R r : ℝ → ℝ,
        ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)) ∧
        (∀ α ∈ Set.Icc 0 (Real.pi / 2),
          R α ^ (2 * n + 2) + r α ^ (2 * n + 2) = 2 + A α ∧
          R α ^ (2 * n + 1) - r α ^ (2 * n + 1) = B α) ∧
        R (Real.pi / 2) = 1 ∧
        r (Real.pi / 2) = 1 ∧
        (∀ α ∈ Set.Icc 0 (Real.pi / 2), |R α - 1| < 1 / 2 ∧ |r α - 1| < 1 / 2) := by
  obtain ⟨δ1, hδ1pos, hδ1⟩ := exists_radialLocalInv_right_inv_ball n
  obtain ⟨u, hu_mem, hu_cont, hu_maps⟩ := exists_radialLocalInv_contDiffOn_close n
  obtain ⟨δu, hδupos, hδu⟩ := Metric.mem_nhds_iff.mp hu_mem
  refine ⟨min δ1 δu, lt_min hδ1pos hδupos, ?_⟩
  intro A B hA hB hA_small hB_small hA_end hB_end hA_deriv hB_deriv
  let y : ℝ → ℝ × ℝ := fun α => (2 + A α, B α)
  let R : ℝ → ℝ := fun α => (radialLocalInv n (y α)).1
  let r : ℝ → ℝ := fun α => (radialLocalInv n (y α)).2
  have hy_cont : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Icc 0 (Real.pi / 2)) := by
    dsimp [y]
    exact (contDiffOn_const.add hA).prodMk hB
  have hy_dist_lt : ∀ α ∈ Set.Icc 0 (Real.pi / 2),
      dist (y α) (radialMap n (1, 1)) < min δ1 δu := by
    intro α hα
    rw [show y α = (2 + A α, B α) by rfl, dist_y_radialMap]
    exact max_lt (hA_small α hα) (hB_small α hα)
  have hy_mem : Set.MapsTo y (Set.Icc 0 (Real.pi / 2)) u := by
    intro α hα
    exact hδu (lt_of_lt_of_le (hy_dist_lt α hα) (min_le_right _ _))
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (radialLocalInv n ∘ y) (Set.Icc 0 (Real.pi / 2)) :=
    hu_cont.comp hy_cont hy_mem
  have hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)) := by
    simpa [R, Function.comp_def] using hcomp.fst
  have hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)) := by
    simpa [r, Function.comp_def] using hcomp.snd
  refine ⟨R, r, hR_cont, hr_cont, ?_, ?_, ?_, ?_⟩
  · intro α hα
    have hdist1 : dist (y α) (radialMap n (1, 1)) < δ1 :=
      lt_of_lt_of_le (hy_dist_lt α hα) (min_le_left _ _)
    have heq := hδ1 (y α) hdist1
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    dsimp [R, r, y] at h1 h2 ⊢
    simp only [radialMap] at h1 h2
    exact ⟨h1, h2⟩
  · dsimp [R]
    have hyend : y (Real.pi / 2) = radialMap n (1, 1) := by
      dsimp [y, radialMap]
      rw [hA_end, hB_end]
      norm_num
    rw [hyend, radialLocalInv_apply_image n]
  · dsimp [r]
    have hyend : y (Real.pi / 2) = radialMap n (1, 1) := by
      dsimp [y, radialMap]
      rw [hA_end, hB_end]
      norm_num
    rw [hyend, radialLocalInv_apply_image n]
  · intro α hα
    have hdistu : dist (y α) (radialMap n (1, 1)) < δu :=
      lt_of_lt_of_le (hy_dist_lt α hα) (min_le_right _ _)
    have hsmall := hu_maps (hδu hdistu)
    rw [Metric.mem_ball, Prod.dist_eq] at hsmall
    constructor
    · exact lt_of_le_of_lt (le_max_left _ _) hsmall
    · exact lt_of_le_of_lt (le_max_right _ _) hsmall

end

end Commons.Geometry.Ulam

