import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.FireFix.Clauses.PhysVortAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter Topology
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix.Clauses

/-! ## 1. The product rule for a scalar function times `e_θ` -/

lemma norm_fderiv_smul_eTheta_le {H : R3 → ℝ} {x : R3} (hr : 0 < Work.Cyl.radial x)
    (hH : DifferentiableAt ℝ H x) :
    ‖fderiv ℝ (fun y : R3 => H y • Work.Cyl.eTheta y) x‖
      ≤ |H x| * (2 / Work.Cyl.radial x) + ‖fderiv ℝ H x‖ := by
  have hE : DifferentiableAt ℝ Work.Cyl.eTheta x := (eTheta_deriv_bound x hr).1
  have hEb := (eTheta_deriv_bound x hr).2
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have hkey : fderiv ℝ ((fun y : R3 => H y) • Work.Cyl.eTheta) x
      = H x • fderiv ℝ Work.Cyl.eTheta x + (fderiv ℝ H x).smulRight (Work.Cyl.eTheta x) :=
    fderiv_smul hH hE
  change ‖fderiv ℝ ((fun y : R3 => H y) • Work.Cyl.eTheta) x‖ ≤ _
  rw [hkey]
  calc ‖H x • fderiv ℝ Work.Cyl.eTheta x + (fderiv ℝ H x).smulRight (Work.Cyl.eTheta x)‖
      ≤ ‖H x • fderiv ℝ Work.Cyl.eTheta x‖
        + ‖(fderiv ℝ H x).smulRight (Work.Cyl.eTheta x)‖ := norm_add_le _ _
    _ = |H x| * ‖fderiv ℝ Work.Cyl.eTheta x‖ + ‖fderiv ℝ H x‖ * ‖Work.Cyl.eTheta x‖ := by
        rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
    _ = |H x| * ‖fderiv ℝ Work.Cyl.eTheta x‖ + ‖fderiv ℝ H x‖ := by
        rw [Work.Cyl.norm_eTheta x hrne, mul_one]
    _ ≤ |H x| * (2 / Work.Cyl.radial x) + ‖fderiv ℝ H x‖ := by
        have := mul_le_mul_of_nonneg_left hEb (abs_nonneg (H x))
        linarith

/-! ## 2. Recovering the two-variable differentiability of the profile -/

lemma diffAt2_of_differentiableAt_smul_eTheta {α B : ℝ} (hα : 0 < α) (hB : 0 < B)
    {Ψ : ℝ → ℝ → ℝ} {x : R3} (hr : 0 < Work.Cyl.radial x)
    (hd : DifferentiableAt ℝ (fun y : R3 =>
      Ψ (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y) • Work.Cyl.eTheta y) x) :
    Work.Cyl.DiffAt2 Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x) := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have hE : DifferentiableAt ℝ Work.Cyl.eTheta x := (eTheta_deriv_bound x hr).1
  have hinner := DifferentiableAt.inner ℝ hd hE
  have hmem : {y : R3 | 0 < Work.Cyl.radial y} ∈ 𝓝 x :=
    (Work.Cyl.differentiableAt_radial x hrne).continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hr)
  have hH : DifferentiableAt ℝ
      (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y)) x := by
    refine hinner.congr_of_eventuallyEq ?_
    filter_upwards [hmem] with y hy
    have hnorm : ‖Work.Cyl.eTheta y‖ = 1 := Work.Cyl.norm_eTheta y (ne_of_gt hy)
    show Ψ (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y)
      = inner ℝ (Ψ (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y) • Work.Cyl.eTheta y)
          (Work.Cyl.eTheta y)
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm]
    ring
  exact diffAt2_of_comp_sect hα hB x hr hH

/-! ## 3. The profile vanishes beyond the support radius -/

lemma profile_eq_zero_of_supp {α : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {τ L : ℝ}
    (hsupp : ∀ z θ : ℝ, L ≤ z → Work.FTS.Regularity.profFull α g z θ τ = 0)
    {z θ : ℝ} (hz : L ≤ z) :
    Work.ConstructionInstance.profile (3 * α) (Work.FTS.Regularity.gSlice g τ) z θ = 0 := by
  by_cases hθ : 0 ≤ θ
  · rw [profile_eq_Ppos hθ, Ppos]
    have h := hsupp z θ hz
    rw [Work.FTS.Regularity.profFull_apply] at h
    simpa [Work.FTS.Regularity.pExp] using h
  · rw [profile_eq_neg_Ppos hθ, Ppos]
    have h := hsupp z (-θ) hz
    rw [Work.FTS.Regularity.profFull_apply] at h
    have h' : Work.Construction.Fstar (3 * α) z (-θ) + g z (-θ) τ = 0 := by
      simpa [Work.FTS.Regularity.pExp] using h
    rw [h', neg_zero]

/-! ## 4. The pointwise bounds on the profile slice -/

lemma profile_abs_le_N {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g : ℝ → ℝ → ℝ → ℝ} {τ N : ℝ}
    (hN : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ τ| ≤ N)
    {z θ : ℝ} (hz : 0 ≤ z) (hθ : |θ| ≤ Real.pi / 2) :
    |Work.ConstructionInstance.profile (3 * α) (Work.FTS.Regularity.gSlice g τ) z θ|
      ≤ 20 * (3 * α) + N := by
  have hF := (Fstar_bounds hα hα13).1
  have hθup : θ ≤ Real.pi / 2 := by linarith [abs_le.mp hθ]
  by_cases hθ0 : 0 ≤ θ
  · have hmem : θ ∈ Work.Spaces.Iθ := ⟨hθ0, hθup⟩
    rw [profile_eq_Ppos hθ0, Ppos]
    calc |Work.Construction.Fstar (3 * α) z θ + g z θ τ|
        ≤ |Work.Construction.Fstar (3 * α) z θ| + |g z θ τ| := abs_add_le _ _
      _ ≤ 20 * (3 * α) + N := by
          have h1 := hF z θ hz hmem
          have h2 := hN z θ hz hmem
          nlinarith
  · have hmem : -θ ∈ Work.Spaces.Iθ :=
      ⟨by linarith, by linarith [abs_le.mp hθ]⟩
    rw [show Work.ConstructionInstance.profile (3 * α) (Work.FTS.Regularity.gSlice g τ) z θ
        = -Ppos α g τ z (-θ) from profile_eq_neg_Ppos hθ0, Ppos, abs_neg]
    calc |Work.Construction.Fstar (3 * α) z (-θ) + g z (-θ) τ|
        ≤ |Work.Construction.Fstar (3 * α) z (-θ)| + |g z (-θ) τ| := abs_add_le _ _
      _ ≤ 20 * (3 * α) + N := by
          have h1 := hF z (-θ) hz hmem
          have h2 := hN z (-θ) hz hmem
          nlinarith

lemma profile_pz_le {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {Npz : ℝ}
    {g : ℝ → ℝ → ℝ → ℝ} (hNpz : ∀ z θ τ', 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ' ∈ Set.Icc 0 S →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ') z θ| ≤ Npz)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {z θ : ℝ} (hz : 0 ≤ z) (hθ : |θ| ≤ Real.pi / 2) :
    |Work.Spaces.pz (fun z θ => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z θ) z θ| ≤ 60 * α + Npz := by
  have hθup : θ ≤ Real.pi / 2 := by linarith [abs_le.mp hθ]
  by_cases hθ0 : 0 ≤ θ
  · exact abs_pz_profile_le hα hα13 hNpz hcont hτ hz (⟨hθ0, hθup⟩ : θ ∈ Work.Spaces.Iθ)
  · have hpos : (0:ℝ) ≤ -θ := by linarith
    have hmem : -θ ∈ Work.Spaces.Iθ := ⟨hpos, by linarith [abs_le.mp hθ]⟩
    have hfun : (fun z' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z' θ)
        = fun z' => - Work.ConstructionInstance.profile (3 * α)
            (Work.FTS.Regularity.gSlice g τ) z' (-θ) := by
      funext z'
      rw [profile_eq_neg_Ppos hθ0, profile_eq_Ppos hpos]
    have hd : deriv (fun z' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z' θ) z
        = - deriv (fun z' => Work.ConstructionInstance.profile (3 * α)
            (Work.FTS.Regularity.gSlice g τ) z' (-θ)) z := by
      rw [hfun, Work.FTS.EllipticEst.deriv_neg_apply]
    show |deriv (fun z' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z' θ) z| ≤ 60 * α + Npz
    rw [hd, abs_neg]
    exact abs_pz_profile_le hα hα13 hNpz hcont hτ hz hmem

lemma profile_pth_le {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g : ℝ → ℝ → ℝ → ℝ} {τ z θ : ℝ}
    (hz : 0 ≤ z) (hθ1 : 0 < |θ|) (hθ2 : |θ| < Real.pi / 2)
    (hd : DifferentiableAt ℝ (fun θ' => Work.ConstructionInstance.profile (3 * α)
      (Work.FTS.Regularity.gSlice g τ) z θ') θ) :
    |deriv (fun θ' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z θ') θ|
      ≤ 200 * α ^ 2 * (Real.sin (|θ|)) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1)
        + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z (|θ|)| := by
  have habs := abs_lt.mp hθ2
  by_cases hpos : 0 ≤ θ
  · have hθpos : 0 < θ := lt_of_le_of_ne hpos (by rintro rfl; simp at hθ1)
    have hmem : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hθpos, habs.2⟩
    have heq : (fun θ' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z θ') =ᶠ[𝓝 θ]
        (fun θ' => Ppos α g τ z θ') := by
      filter_upwards [isOpen_Ioi.mem_nhds hθpos] with θ' hθ'
      exact profile_eq_Ppos hθ'.le
    have hPn : DifferentiableAt ℝ (fun θ' => Ppos α g τ z θ') θ :=
      hd.congr_of_eventuallyEq heq.symm
    rw [Filter.EventuallyEq.deriv_eq heq, abs_of_pos hθpos]
    exact abs_pdz_posbranch_le hα hα13 hz hmem hPn
  · have hneg : θ < 0 := not_le.mp hpos
    have hmem : -θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) :=
      ⟨by linarith, by linarith [habs.1]⟩
    have heq : (fun θ' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z θ') =ᶠ[𝓝 θ]
        (fun θ' => - Ppos α g τ z (-θ')) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Iio hneg] with θ' hθ'
      show Work.ConstructionInstance.profile (3 * α) (Work.FTS.Regularity.gSlice g τ) z θ'
        = - Ppos α g τ z (-θ')
      rw [profile_eq_neg_Ppos (not_le.mpr hθ')]
    have hd' : DifferentiableAt ℝ (fun θ' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z θ') (-(-θ)) := by simpa using hd
    have hcomp : DifferentiableAt ℝ (fun w : ℝ => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z (-w)) (-θ) :=
      hd'.comp (-θ) (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => -w) (-θ))
    have hev : (fun w : ℝ => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z (-w)) =ᶠ[𝓝 (-θ)]
        (fun w : ℝ => - Ppos α g τ z w) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi (by linarith : (0:ℝ) < -θ)] with w hw
      have hw' : (0:ℝ) < w := hw
      show Work.ConstructionInstance.profile (3 * α) (Work.FTS.Regularity.gSlice g τ) z (-w)
        = - Ppos α g τ z w
      rw [profile_eq_neg_Ppos (not_le.mpr (by linarith : -w < 0))]
      simp only [neg_neg]
    have hPn : DifferentiableAt ℝ (fun w : ℝ => Ppos α g τ z w) (-θ) := by
      have h1 : DifferentiableAt ℝ (fun w : ℝ => - Ppos α g τ z w) (-θ) :=
        hcomp.congr_of_eventuallyEq hev.symm
      refine (h1.neg).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
      simp
    have hb := abs_pdz_posbranch_le hα hα13 hz hmem hPn
    rw [Real.cos_neg] at hb
    have hder : deriv (fun θ' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z θ') θ
        = deriv (fun w : ℝ => Ppos α g τ z w) (-θ) := by
      rw [Filter.EventuallyEq.deriv_eq heq]
      rw [Work.FTS.EllipticEst.deriv_neg_apply, deriv_comp_neg]
      ring
    rw [hder, abs_of_neg hneg]
    exact hb

/-! ## 5. The frame bound for scalar-valued linear maps -/

lemma norm_le_frame_scalar (L : R3 →L[ℝ] ℝ) (x : R3) (hr : 0 < Work.Cyl.radial x) :
    ‖L‖ ≤ ‖L (Work.Cyl.eR x)‖ + ‖L (Work.Cyl.eTheta x)‖ + ‖L Work.Cyl.eZ‖ := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have heZ : ‖(Work.Cyl.eZ : R3)‖ = 1 := by simp [Work.Cyl.eZ, FiniteTimeSingularity.e]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  have hdecE : inner ℝ u (Work.Cyl.eR x) • Work.Cyl.eR x
      + inner ℝ u (Work.Cyl.eTheta x) • Work.Cyl.eTheta x
      + inner ℝ u Work.Cyl.eZ • Work.Cyl.eZ = u := by
    have h := Work.Cyl.decomposition (fun _ : R3 => u) x hrne
    simpa [Work.Cyl.compR, Work.Cyl.compT, Work.Cyl.compZ] using h.symm
  have hLu : L u = inner ℝ u (Work.Cyl.eR x) • L (Work.Cyl.eR x)
      + inner ℝ u (Work.Cyl.eTheta x) • L (Work.Cyl.eTheta x)
      + inner ℝ u (Work.Cyl.eZ : R3) • L Work.Cyl.eZ := by
    conv_lhs => rw [← hdecE]
    simp only [map_add, map_smul]
  have hcS : |inner ℝ u (Work.Cyl.eR x)| ≤ ‖u‖ := by
    have h := abs_real_inner_le_norm u (Work.Cyl.eR x)
    rwa [Work.Cyl.norm_eR x hrne, mul_one] at h
  have hcT : |inner ℝ u (Work.Cyl.eTheta x)| ≤ ‖u‖ := by
    have h := abs_real_inner_le_norm u (Work.Cyl.eTheta x)
    rwa [Work.Cyl.norm_eTheta x hrne, mul_one] at h
  have hcZ : |inner ℝ u (Work.Cyl.eZ : R3)| ≤ ‖u‖ := by
    have h := abs_real_inner_le_norm u (Work.Cyl.eZ : R3)
    rwa [heZ, mul_one] at h
  calc ‖L u‖
      = ‖inner ℝ u (Work.Cyl.eR x) • L (Work.Cyl.eR x)
          + inner ℝ u (Work.Cyl.eTheta x) • L (Work.Cyl.eTheta x)
          + inner ℝ u (Work.Cyl.eZ : R3) • L Work.Cyl.eZ‖ := by rw [hLu]
    _ ≤ ‖inner ℝ u (Work.Cyl.eR x) • L (Work.Cyl.eR x)
          + inner ℝ u (Work.Cyl.eTheta x) • L (Work.Cyl.eTheta x)‖
        + ‖inner ℝ u (Work.Cyl.eZ : R3) • L Work.Cyl.eZ‖ := norm_add_le _ _
    _ ≤ (‖inner ℝ u (Work.Cyl.eR x) • L (Work.Cyl.eR x)‖
          + ‖inner ℝ u (Work.Cyl.eTheta x) • L (Work.Cyl.eTheta x)‖)
        + ‖inner ℝ u (Work.Cyl.eZ : R3) • L Work.Cyl.eZ‖ := by
        gcongr
        exact norm_add_le _ _
    _ = |inner ℝ u (Work.Cyl.eR x)| * ‖L (Work.Cyl.eR x)‖
        + |inner ℝ u (Work.Cyl.eTheta x)| * ‖L (Work.Cyl.eTheta x)‖
        + |inner ℝ u (Work.Cyl.eZ : R3)| * ‖L Work.Cyl.eZ‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖u‖ * ‖L (Work.Cyl.eR x)‖ + ‖u‖ * ‖L (Work.Cyl.eTheta x)‖
        + ‖u‖ * ‖L Work.Cyl.eZ‖ := by
        have h1 := mul_le_mul_of_nonneg_right hcS (norm_nonneg (L (Work.Cyl.eR x)))
        have h2 := mul_le_mul_of_nonneg_right hcT (norm_nonneg (L (Work.Cyl.eTheta x)))
        have h3 := mul_le_mul_of_nonneg_right hcZ (norm_nonneg (L Work.Cyl.eZ))
        linarith
    _ = (‖L (Work.Cyl.eR x)‖ + ‖L (Work.Cyl.eTheta x)‖ + ‖L Work.Cyl.eZ‖) * ‖u‖ := by
        ring

/-! ## 6. The chain-rule bound for `x ↦ Ψ(ρ(x)^{3α}/B, θ(x))` -/

lemma norm_fderiv_profile_comp_le {α B : ℝ} (hα : 0 < α) (hB : 0 < B)
    {Ψ : ℝ → ℝ → ℝ} {x : R3} (hr : 0 < Work.Cyl.radial x)
    (hD : Work.Cyl.DiffAt2 Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)) :
    ‖fderiv ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y)) x‖
      ≤ 2 * (|Work.Spaces.pz Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)|
              * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B))
        + 2 * |Work.Spaces.pth Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)|
            / Work.Cyl.rho x := by
  set P : ℝ := Work.Spaces.pz Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x) with hP
  set Q : ℝ := Work.Spaces.pth Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x) with hQ
  set A : ℝ := (3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B with hA
  have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x)
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hρpos.le _)) hB.le
  -- the two-variable function `(r,θ) ↦ Ψ(r^{3α}/B, θ)`
  set Ψt : ℝ → ℝ → ℝ := fun r θ' => Ψ (r ^ (3 * α) / B) θ' with hΨt
  have hDt : Work.Cyl.DiffAt2 Ψt (Work.Cyl.rho x) (Work.Cyl.theta x) := by
    have hφ : DifferentiableAt ℝ (fun p : ℝ × ℝ => (p.1 ^ (3 * α) / B, p.2))
        (Work.Cyl.rho x, Work.Cyl.theta x) := by
      have h0 : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ (3 * α))
          (Work.Cyl.rho x, Work.Cyl.theta x) :=
        differentiableAt_fst.rpow_const (Or.inl (ne_of_gt hρpos))
      have h1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ (3 * α) / B)
          (Work.Cyl.rho x, Work.Cyl.theta x) := by
        have h := h0.mul_const B⁻¹
        convert h using 1
        funext p
        rw [div_eq_mul_inv]
      exact h1.prodMk differentiableAt_snd
    have h := hD.comp (Work.Cyl.rho x, Work.Cyl.theta x) hφ
    simpa [Work.Cyl.DiffAt2, hΨt, Function.comp_def] using h
  -- the derivative in the first slot of `Ψt`
  have hpdR : Work.Cyl.pdR Ψt (Work.Cyl.rho x) (Work.Cyl.theta x) = P * A := by
    have hslice : DifferentiableAt ℝ (fun s : ℝ => Ψ s (Work.Cyl.theta x))
        (Work.Cyl.rho x ^ (3 * α) / B) :=
      Work.Cyl.differentiableAt_slice_fst Ψ _ _ hD
    have hder : HasDerivAt (fun s : ℝ => Ψ s (Work.Cyl.theta x)) P
        (Work.Cyl.rho x ^ (3 * α) / B) := by
      rw [hP]
      simpa [Work.Spaces.pz] using hslice.hasDerivAt
    have hbase : HasDerivAt (fun r : ℝ => r ^ (3 * α))
        ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1)) (Work.Cyl.rho x) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hρpos))
    have hbase2 : HasDerivAt (fun r : ℝ => r ^ (3 * α) / B)
        ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B) (Work.Cyl.rho x) :=
      hbase.div_const B
    have hcomp := hder.comp (Work.Cyl.rho x) hbase2
    rw [Work.Cyl.pdR, hA]
    simpa [hΨt, Function.comp_def] using hcomp.deriv
  -- the derivative in the second slot of `Ψt`
  have hpdZ : Work.Cyl.pdZ Ψt (Work.Cyl.rho x) (Work.Cyl.theta x) = Q := by
    rw [hQ]
    rfl
  set H : R3 → ℝ := fun y => Ψ (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y) with hH
  have hHdiff : DifferentiableAt ℝ H x :=
    Work.Cyl.differentiableAt_rho_theta_comp Ψt x hDt hr
  have hER : (fderiv ℝ H x) (Work.Cyl.eR x)
      = Real.cos (Work.Cyl.theta x) * (P * A) - Real.sin (Work.Cyl.theta x) / Work.Cyl.rho x * Q := by
    rw [hH]
    change (fderiv ℝ (fun y : R3 => Ψt (Work.Cyl.rho y) (Work.Cyl.theta y)) x)
        (Work.Cyl.eR x) = _
    rw [Work.Cyl.fderiv_rho_theta_eR Ψt x hDt hr, hpdR, hpdZ]
  have hEZ : (fderiv ℝ H x) Work.Cyl.eZ
      = Real.sin (Work.Cyl.theta x) * (P * A) + Real.cos (Work.Cyl.theta x) / Work.Cyl.rho x * Q := by
    rw [hH]
    change (fderiv ℝ (fun y : R3 => Ψt (Work.Cyl.rho y) (Work.Cyl.theta y)) x)
        Work.Cyl.eZ = _
    rw [Work.Cyl.fderiv_rho_theta_eZ Ψt x hDt hr, hpdR, hpdZ]
  have hETh : (fderiv ℝ H x) (Work.Cyl.eTheta x) = 0 := by
    rw [hH]
    change (fderiv ℝ (fun y : R3 => Ψt (Work.Cyl.rho y) (Work.Cyl.theta y)) x)
        (Work.Cyl.eTheta x) = _
    exact fderiv_rho_theta_eTheta Ψt x hDt hr
  -- the two directional bounds
  have hERb : ‖(fderiv ℝ H x) (Work.Cyl.eR x)‖ ≤ |P| * A + |Q| / Work.Cyl.rho x := by
    rw [hER, Real.norm_eq_abs]
    have h1 : |Real.cos (Work.Cyl.theta x) * (P * A)
        - Real.sin (Work.Cyl.theta x) / Work.Cyl.rho x * Q|
        ≤ |Real.cos (Work.Cyl.theta x) * (P * A)|
          + |Real.sin (Work.Cyl.theta x) / Work.Cyl.rho x * Q| := by
      simpa using abs_sub_le (Real.cos (Work.Cyl.theta x) * (P * A)) 0
        (Real.sin (Work.Cyl.theta x) / Work.Cyl.rho x * Q)
    have h2 : |Real.cos (Work.Cyl.theta x) * (P * A)| ≤ |P| * A := by
      rw [abs_mul, abs_mul, abs_of_nonneg hA0]
      have hc := Real.abs_cos_le_one (Work.Cyl.theta x)
      calc |Real.cos (Work.Cyl.theta x)| * (|P| * A) ≤ 1 * (|P| * A) := by
            gcongr
        _ = |P| * A := by ring
    have h3 : |Real.sin (Work.Cyl.theta x) / Work.Cyl.rho x * Q| ≤ |Q| / Work.Cyl.rho x := by
      rw [abs_mul, abs_div]
      have hs := Real.abs_sin_le_one (Work.Cyl.theta x)
      have hρ : |Work.Cyl.rho x| = Work.Cyl.rho x := abs_of_pos hρpos
      rw [hρ]
      calc |Real.sin (Work.Cyl.theta x)| / Work.Cyl.rho x * |Q| ≤ 1 / Work.Cyl.rho x * |Q| := by
            gcongr
        _ = |Q| / Work.Cyl.rho x := by ring
    linarith
  have hEZb : ‖(fderiv ℝ H x) Work.Cyl.eZ‖ ≤ |P| * A + |Q| / Work.Cyl.rho x := by
    rw [hEZ, Real.norm_eq_abs]
    have h1 : |Real.sin (Work.Cyl.theta x) * (P * A)
        + Real.cos (Work.Cyl.theta x) / Work.Cyl.rho x * Q|
        ≤ |Real.sin (Work.Cyl.theta x) * (P * A)|
          + |Real.cos (Work.Cyl.theta x) / Work.Cyl.rho x * Q| := abs_add_le _ _
    have h2 : |Real.sin (Work.Cyl.theta x) * (P * A)| ≤ |P| * A := by
      rw [abs_mul, abs_mul, abs_of_nonneg hA0]
      have hc := Real.abs_sin_le_one (Work.Cyl.theta x)
      calc |Real.sin (Work.Cyl.theta x)| * (|P| * A) ≤ 1 * (|P| * A) := by gcongr
        _ = |P| * A := by ring
    have h3 : |Real.cos (Work.Cyl.theta x) / Work.Cyl.rho x * Q| ≤ |Q| / Work.Cyl.rho x := by
      rw [abs_mul, abs_div]
      have hs := Real.abs_cos_le_one (Work.Cyl.theta x)
      have hρ : |Work.Cyl.rho x| = Work.Cyl.rho x := abs_of_pos hρpos
      rw [hρ]
      calc |Real.cos (Work.Cyl.theta x)| / Work.Cyl.rho x * |Q| ≤ 1 / Work.Cyl.rho x * |Q| := by
            gcongr
        _ = |Q| / Work.Cyl.rho x := by ring
    linarith
  calc ‖fderiv ℝ H x‖
      ≤ ‖(fderiv ℝ H x) (Work.Cyl.eR x)‖ + ‖(fderiv ℝ H x) (Work.Cyl.eTheta x)‖
        + ‖(fderiv ℝ H x) Work.Cyl.eZ‖ := norm_le_frame_scalar _ x hr
    _ ≤ 2 * (|P| * A) + 2 * |Q| / Work.Cyl.rho x := by
        rw [hETh, norm_zero, mul_div_assoc]
        linarith
    _ = 2 * (|Work.Spaces.pz Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)| * A)
        + 2 * |Work.Spaces.pth Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)|
            / Work.Cyl.rho x := by rw [hP, hQ]
    _ = 2 * (|Work.Spaces.pz Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)|
              * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B))
        + 2 * |Work.Spaces.pth Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)|
            / Work.Cyl.rho x := by rw [hA]

/-! ## 7. Differentiability of the rescaled two-variable function -/

lemma diffAt2_comp_rpow {α B : ℝ} (hB : 0 < B) {Ψ : ℝ → ℝ → ℝ} {x : R3}
    (hr : 0 < Work.Cyl.radial x)
    (hD : Work.Cyl.DiffAt2 Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)) :
    Work.Cyl.DiffAt2 (fun r θ => Ψ (r ^ (3 * α) / B) θ) (Work.Cyl.rho x) (Work.Cyl.theta x) := by
  have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x)
  have hφ : DifferentiableAt ℝ (fun p : ℝ × ℝ => (p.1 ^ (3 * α) / B, p.2))
      (Work.Cyl.rho x, Work.Cyl.theta x) := by
    have h0 : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ (3 * α))
        (Work.Cyl.rho x, Work.Cyl.theta x) :=
      differentiableAt_fst.rpow_const (Or.inl (ne_of_gt hρpos))
    have h1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ (3 * α) / B)
        (Work.Cyl.rho x, Work.Cyl.theta x) := by
      have h := h0.mul_const B⁻¹
      convert h using 1
      funext p
      rw [div_eq_mul_inv]
    exact h1.prodMk differentiableAt_snd
  have h := hD.comp (Work.Cyl.rho x, Work.Cyl.theta x) hφ
  simpa [Work.Cyl.DiffAt2, Function.comp_def] using h

end Work.FTS.FireFix.Clauses
