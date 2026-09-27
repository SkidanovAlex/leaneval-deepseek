import Mathlib
import Submission.Work.Noncompact.ProperLine.flatGlue2
import Submission.Work.Noncompact.ProperLine.rayAssembly
import Submission.Work.Whitney.SmoothArc.Arc

/-!
# The smoothness engine for the proper-ray construction

* `smoothTransition_flat` : `Real.smoothTransition` is flat at `0` (from the right) and at `1`
  (from the left).
* `flatComp` : composing a `C^∞` map (smooth near the image point) with a flat reparametrising
  function is again flat.  This is the missing ingredient which makes the pieces
  `σ ∘ smoothTransition` of the proper-ray construction flat at their ends, so that the assembled
  ray can be glued at its junctions.
-/

open Set Filter
open scoped Topology ContDiff

namespace Work.Noncompact.ProperLine


/-- **`Real.smoothTransition` is flat at `0` from the right and at `1` from the left.** -/
theorem smoothTransition_flat :
    (∀ k : ℕ, 0 < k → iteratedDerivWithin k Real.smoothTransition (Set.Ici 0) 0 = 0) ∧
    (∀ k : ℕ, 0 < k → iteratedDerivWithin k Real.smoothTransition (Set.Iic 1) 1 = 0) := by
  have key : ∀ k : ℕ, 0 < k →
      iteratedDeriv k Real.smoothTransition 0 = 0 ∧
      iteratedDeriv k Real.smoothTransition 1 = 0 := by
    intro k hk
    constructor
    · have hEq : Set.EqOn Real.smoothTransition (fun _ : ℝ => (0 : ℝ)) (Set.Iic 0) :=
        fun t ht => Real.smoothTransition.zero_of_nonpos ht
      have h1 : iteratedDerivWithin k Real.smoothTransition (Set.Iic 0) 0
          = iteratedDerivWithin k (fun _ : ℝ => (0 : ℝ)) (Set.Iic 0) 0 :=
        iteratedDerivWithin_congr (n := k) hEq (Set.mem_Iic.mpr le_rfl)
      rw [iteratedDerivWithin_const] at h1
      simp only [hk.ne', if_false] at h1
      have h2 := iteratedDerivWithin_eq_iteratedDeriv (f := Real.smoothTransition) (n := k)
        (s := Set.Iic 0) (x := 0) (uniqueDiffOn_Iic 0)
        (Real.smoothTransition.contDiffAt (n := (k : ℕ∞))) (Set.mem_Iic.mpr le_rfl)
      rw [h2] at h1
      exact h1
    · have hEq : Set.EqOn Real.smoothTransition (fun _ : ℝ => (1 : ℝ)) (Set.Ici 1) :=
        fun t ht => Real.smoothTransition.one_of_one_le ht
      have h1 : iteratedDerivWithin k Real.smoothTransition (Set.Ici 1) 1
          = iteratedDerivWithin k (fun _ : ℝ => (1 : ℝ)) (Set.Ici 1) 1 :=
        iteratedDerivWithin_congr (n := k) hEq (Set.mem_Ici.mpr le_rfl)
      rw [iteratedDerivWithin_const] at h1
      simp only [hk.ne', if_false] at h1
      have h2 := iteratedDerivWithin_eq_iteratedDeriv (f := Real.smoothTransition) (n := k)
        (s := Set.Ici 1) (x := 1) (uniqueDiffOn_Ici 1)
        (Real.smoothTransition.contDiffAt (n := (k : ℕ∞))) (Set.mem_Ici.mpr le_rfl)
      rw [h2] at h1
      exact h1
  constructor
  · intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv (s := Set.Ici 0) (x := 0) (uniqueDiffOn_Ici 0)
      (Real.smoothTransition.contDiffAt (n := (k : ℕ∞))) (Set.mem_Ici.mpr le_rfl)]
    exact (key k hk).1
  · intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv (s := Set.Iic 1) (x := 1) (uniqueDiffOn_Iic 1)
      (Real.smoothTransition.contDiffAt (n := (k : ℕ∞))) (Set.mem_Iic.mpr le_rfl)]
    exact (key k hk).2


/-- **Flatness is preserved by composition with a smooth map.**

If `ψ` is `C^∞` on `Ici τ`, flat at `τ` from the right, and `H` is `C^∞` near
`0`, then `H ∘ ψ` is flat at `τ` from the right. -/
theorem flatComp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ψ : ℝ → ℝ} {H : ℝ → F} {τ r : ℝ} (hr : 0 < r)
    (hψsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ (Set.Ici τ))
    (hψ : ∀ k : ℕ, 0 < k → iteratedDerivWithin k ψ (Set.Ici τ) τ = 0)
    (hH : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H (Metric.ball (ψ τ) r)) :
    ∀ k : ℕ, 0 < k → iteratedDerivWithin k (H ∘ ψ) (Set.Ici τ) τ = 0 := by
  set s : Set ℝ := Set.Ici τ with hs
  have hτs : τ ∈ s := Set.mem_Ici.mpr le_rfl
  have hud : UniqueDiffOn ℝ s := uniqueDiffOn_Ici τ
  have hudτ : UniqueDiffWithinAt ℝ s τ := uniqueDiffWithinAt_Ici τ
  set φ : ℝ → ℝ := derivWithin ψ s with hφdef
  set A : ℝ → F := fun x => (fderiv ℝ H (ψ x)) (1 : ℝ) with hAdef
  -- `H` is smooth near `ψ τ`
  have hHτ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H (ψ τ) :=
    ContDiffOn.contDiffAt hH (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  -- `H` is smooth at `ψ x` for `x` near `τ` inside `s`
  have hevH : ∀ᶠ x in 𝓝[s] τ, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H (ψ x) := by
    have hcont : Tendsto ψ (𝓝[s] τ) (𝓝 (ψ τ)) := hψsm.continuousOn.continuousWithinAt hτs
    filter_upwards [hcont.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] with u hu
    exact ContDiffOn.contDiffAt hH (Metric.isOpen_ball.mem_nhds hu)
  -- `A` is `C^∞` within `s` at `τ`
  have hAsm : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A s τ := by
    have hinner : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => (fderiv ℝ H u) (1 : ℝ)) (ψ τ) := by
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => fderiv ℝ H u) (ψ τ) :=
        ContDiffAt.fderiv (x₀ := ψ τ) (f := fun (_ : ℝ) (u : ℝ) => H u) (g := fun u : ℝ => u)
          (by
            have hK : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
                (Function.uncurry fun (_ : ℝ) (u : ℝ) => H u) (ψ τ, ψ τ) :=
              hHτ.comp (ψ τ, ψ τ) contDiffAt_snd
            exact hK)
          contDiffAt_id top_add_one_le_withTop
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun L : ℝ →L[ℝ] F => L (1 : ℝ)) (fderiv ℝ H (ψ τ)) :=
        (((ContinuousLinearMap.apply ℝ F) (1 : ℝ)).contDiff).contDiffAt
      exact h2.comp (ψ τ) h1
    have h3 : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => (fderiv ℝ H (ψ x)) (1 : ℝ)) s τ :=
      hinner.comp_contDiffWithinAt τ (hψsm.contDiffWithinAt hτs)
    exact ContDiffWithinAt.congr h3 (fun y _ => by simp only [hAdef]) (by simp only [hAdef])
  have hφsm : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ s τ := by
    have hφOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (derivWithin ψ s) s :=
      hψsm.derivWithin hud top_add_one_le_withTop
    have h : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (derivWithin ψ s) s τ :=
      hφOn.contDiffWithinAt hτs
    exact ContDiffWithinAt.congr h (fun y _ => by simp only [hφdef]) (by simp only [hφdef])
  -- the chain rule, near `τ` inside `s` and at `τ`
  have hderivev : (derivWithin (H ∘ ψ) s) =ᶠ[𝓝[s] τ] (φ • A) := by
    filter_upwards [hevH, self_mem_nhdsWithin] with x hxH hxs
    have hψx : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ s x := hψsm.contDiffWithinAt hxs
    have hdψ : DifferentiableWithinAt ℝ ψ s x := hψx.differentiableWithinAt (by simp)
    have hhf : HasFDerivAt H (fderiv ℝ H (ψ x)) (ψ x) :=
      (hxH.differentiableAt (by simp)).hasFDerivAt
    have hcomp : HasFDerivWithinAt (H ∘ ψ)
        ((fderiv ℝ H (ψ x)).comp (fderivWithin ℝ ψ s x)) s x :=
      hhf.comp_hasFDerivWithinAt x hdψ.hasFDerivWithinAt
    have hcomp' : fderivWithin ℝ (H ∘ ψ) s x
        = (fderiv ℝ H (ψ x)).comp (fderivWithin ℝ ψ s x) := hcomp.fderivWithin (hud x hxs)
    change (fderivWithin ℝ (H ∘ ψ) s x) (1 : ℝ)
      = (derivWithin ψ s x) • ((fderiv ℝ H (ψ x)) (1 : ℝ))
    rw [hcomp', ContinuousLinearMap.comp_apply]
    simp only [derivWithin]
    rw [← ContinuousLinearMap.map_smul]
    congr 1
    rw [smul_eq_mul, mul_one]
  have hderivτ : derivWithin (H ∘ ψ) s τ = (φ • A) τ := by
    have hdψ : DifferentiableWithinAt ℝ ψ s τ :=
      (hψsm.contDiffWithinAt hτs).differentiableWithinAt (by simp)
    have hhf : HasFDerivAt H (fderiv ℝ H (ψ τ)) (ψ τ) :=
      (hHτ.differentiableAt (by simp)).hasFDerivAt
    have hcomp : HasFDerivWithinAt (H ∘ ψ)
        ((fderiv ℝ H (ψ τ)).comp (fderivWithin ℝ ψ s τ)) s τ :=
      hhf.comp_hasFDerivWithinAt τ hdψ.hasFDerivWithinAt
    have hcomp' : fderivWithin ℝ (H ∘ ψ) s τ
        = (fderiv ℝ H (ψ τ)).comp (fderivWithin ℝ ψ s τ) := hcomp.fderivWithin hudτ
    change (fderivWithin ℝ (H ∘ ψ) s τ) (1 : ℝ)
      = (derivWithin ψ s τ) • ((fderiv ℝ H (ψ τ)) (1 : ℝ))
    rw [hcomp', ContinuousLinearMap.comp_apply]
    simp only [derivWithin]
    rw [← ContinuousLinearMap.map_smul]
    congr 1
    rw [smul_eq_mul, mul_one]
  intro k hk
  have hkp : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_pos hk).symm
  rw [hkp, iteratedDerivWithin_succ']
  rw [hderivev.iteratedDerivWithin_eq hderivτ]
  have hφsm' : ContDiffWithinAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) φ s τ := hφsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hAsm' : ContDiffWithinAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) A s τ := hAsm.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedDerivWithin_smul (n := k - 1) hτs hud hφsm' hAsm']
  refine Finset.sum_eq_zero fun i hi => ?_
  have hzero : iteratedDerivWithin i φ s τ = 0 := by
    have hshift : iteratedDerivWithin i φ s τ = iteratedDerivWithin (i + 1) ψ s τ := by
      rw [hφdef]
      exact congrFun (iteratedDerivWithin_succ' (n := i) (f := ψ) (s := s)).symm τ
    rw [hshift]
    exact hψ (i + 1) (Nat.succ_pos i)
  rw [hzero]; simp

/-- **Flatness is preserved by composition with a smooth map.**

If `ψ` is `C^∞` on `Iic τ`, flat at `τ` from the left, and `H` is `C^∞` near
`0`, then `H ∘ ψ` is flat at `τ` from the left. -/
theorem flatComp_left {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ψ : ℝ → ℝ} {H : ℝ → F} {τ r : ℝ} (hr : 0 < r)
    (hψsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ (Set.Iic τ))
    (hψ : ∀ k : ℕ, 0 < k → iteratedDerivWithin k ψ (Set.Iic τ) τ = 0)
    (hH : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H (Metric.ball (ψ τ) r)) :
    ∀ k : ℕ, 0 < k → iteratedDerivWithin k (H ∘ ψ) (Set.Iic τ) τ = 0 := by
  set s : Set ℝ := Set.Iic τ with hs
  have hτs : τ ∈ s := Set.mem_Iic.mpr le_rfl
  have hud : UniqueDiffOn ℝ s := uniqueDiffOn_Iic τ
  have hudτ : UniqueDiffWithinAt ℝ s τ := uniqueDiffWithinAt_Iic τ
  set φ : ℝ → ℝ := derivWithin ψ s with hφdef
  set A : ℝ → F := fun x => (fderiv ℝ H (ψ x)) (1 : ℝ) with hAdef
  -- `H` is smooth near `ψ τ`
  have hHτ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H (ψ τ) :=
    ContDiffOn.contDiffAt hH (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  -- `H` is smooth at `ψ x` for `x` near `τ` inside `s`
  have hevH : ∀ᶠ x in 𝓝[s] τ, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H (ψ x) := by
    have hcont : Tendsto ψ (𝓝[s] τ) (𝓝 (ψ τ)) := hψsm.continuousOn.continuousWithinAt hτs
    filter_upwards [hcont.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] with u hu
    exact ContDiffOn.contDiffAt hH (Metric.isOpen_ball.mem_nhds hu)
  -- `A` is `C^∞` within `s` at `τ`
  have hAsm : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A s τ := by
    have hinner : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => (fderiv ℝ H u) (1 : ℝ)) (ψ τ) := by
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => fderiv ℝ H u) (ψ τ) :=
        ContDiffAt.fderiv (x₀ := ψ τ) (f := fun (_ : ℝ) (u : ℝ) => H u) (g := fun u : ℝ => u)
          (by
            have hK : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
                (Function.uncurry fun (_ : ℝ) (u : ℝ) => H u) (ψ τ, ψ τ) :=
              hHτ.comp (ψ τ, ψ τ) contDiffAt_snd
            exact hK)
          contDiffAt_id top_add_one_le_withTop
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun L : ℝ →L[ℝ] F => L (1 : ℝ)) (fderiv ℝ H (ψ τ)) :=
        (((ContinuousLinearMap.apply ℝ F) (1 : ℝ)).contDiff).contDiffAt
      exact h2.comp (ψ τ) h1
    have h3 : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => (fderiv ℝ H (ψ x)) (1 : ℝ)) s τ :=
      hinner.comp_contDiffWithinAt τ (hψsm.contDiffWithinAt hτs)
    exact ContDiffWithinAt.congr h3 (fun y _ => by simp only [hAdef]) (by simp only [hAdef])
  have hφsm : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ s τ := by
    have hφOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (derivWithin ψ s) s :=
      hψsm.derivWithin hud top_add_one_le_withTop
    have h : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (derivWithin ψ s) s τ :=
      hφOn.contDiffWithinAt hτs
    exact ContDiffWithinAt.congr h (fun y _ => by simp only [hφdef]) (by simp only [hφdef])
  -- the chain rule, near `τ` inside `s` and at `τ`
  have hderivev : (derivWithin (H ∘ ψ) s) =ᶠ[𝓝[s] τ] (φ • A) := by
    filter_upwards [hevH, self_mem_nhdsWithin] with x hxH hxs
    have hψx : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ s x := hψsm.contDiffWithinAt hxs
    have hdψ : DifferentiableWithinAt ℝ ψ s x := hψx.differentiableWithinAt (by simp)
    have hhf : HasFDerivAt H (fderiv ℝ H (ψ x)) (ψ x) :=
      (hxH.differentiableAt (by simp)).hasFDerivAt
    have hcomp : HasFDerivWithinAt (H ∘ ψ)
        ((fderiv ℝ H (ψ x)).comp (fderivWithin ℝ ψ s x)) s x :=
      hhf.comp_hasFDerivWithinAt x hdψ.hasFDerivWithinAt
    have hcomp' : fderivWithin ℝ (H ∘ ψ) s x
        = (fderiv ℝ H (ψ x)).comp (fderivWithin ℝ ψ s x) := hcomp.fderivWithin (hud x hxs)
    change (fderivWithin ℝ (H ∘ ψ) s x) (1 : ℝ)
      = (derivWithin ψ s x) • ((fderiv ℝ H (ψ x)) (1 : ℝ))
    rw [hcomp', ContinuousLinearMap.comp_apply]
    simp only [derivWithin]
    rw [← ContinuousLinearMap.map_smul]
    congr 1
    rw [smul_eq_mul, mul_one]
  have hderivτ : derivWithin (H ∘ ψ) s τ = (φ • A) τ := by
    have hdψ : DifferentiableWithinAt ℝ ψ s τ :=
      (hψsm.contDiffWithinAt hτs).differentiableWithinAt (by simp)
    have hhf : HasFDerivAt H (fderiv ℝ H (ψ τ)) (ψ τ) :=
      (hHτ.differentiableAt (by simp)).hasFDerivAt
    have hcomp : HasFDerivWithinAt (H ∘ ψ)
        ((fderiv ℝ H (ψ τ)).comp (fderivWithin ℝ ψ s τ)) s τ :=
      hhf.comp_hasFDerivWithinAt τ hdψ.hasFDerivWithinAt
    have hcomp' : fderivWithin ℝ (H ∘ ψ) s τ
        = (fderiv ℝ H (ψ τ)).comp (fderivWithin ℝ ψ s τ) := hcomp.fderivWithin hudτ
    change (fderivWithin ℝ (H ∘ ψ) s τ) (1 : ℝ)
      = (derivWithin ψ s τ) • ((fderiv ℝ H (ψ τ)) (1 : ℝ))
    rw [hcomp', ContinuousLinearMap.comp_apply]
    simp only [derivWithin]
    rw [← ContinuousLinearMap.map_smul]
    congr 1
    rw [smul_eq_mul, mul_one]
  intro k hk
  have hkp : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_pos hk).symm
  rw [hkp, iteratedDerivWithin_succ']
  rw [hderivev.iteratedDerivWithin_eq hderivτ]
  have hφsm' : ContDiffWithinAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) φ s τ := hφsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hAsm' : ContDiffWithinAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) A s τ := hAsm.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedDerivWithin_smul (n := k - 1) hτs hud hφsm' hAsm']
  refine Finset.sum_eq_zero fun i hi => ?_
  have hzero : iteratedDerivWithin i φ s τ = 0 := by
    have hshift : iteratedDerivWithin i φ s τ = iteratedDerivWithin (i + 1) ψ s τ := by
      rw [hφdef]
      exact congrFun (iteratedDerivWithin_succ' (n := i) (f := ψ) (s := s)).symm τ
    rw [hshift]
    exact hψ (i + 1) (Nat.succ_pos i)
  rw [hzero]; simp


/-- The chart expression of a smooth curve around a parameter where it hits the chart centre. -/
theorem chartExpr_contDiffOn {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {σ : ℝ → M} (hσ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) σ)
    {z : M} {τ : ℝ} (hz : σ τ = z) :
    ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) z (σ u))
      (Metric.ball τ r) := by
  set I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)) with hI
  have hsrc : (extChartAt I z).source ∈ 𝓝 z := extChartAt_source_mem_nhds z
  have hpre : σ ⁻¹' (extChartAt I z).source ∈ 𝓝 τ :=
    hσ.continuous.continuousAt.preimage_mem_nhds (by rw [hz]; exact hsrc)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ε / 2, by positivity, ?_⟩
  have hsub : Metric.ball τ (ε / 2) ⊆ σ ⁻¹' (extChartAt I z).source := fun u hu =>
    hεsub (by rw [Metric.mem_ball] at hu ⊢; linarith)
  have hExtOn : ContMDiffOn I I ((⊤ : ℕ∞) : WithTop ℕ∞) (extChartAt I z)
      (extChartAt I z).source := by
    simpa [hI] using contMDiffOn_extChartAt (I := I) (x := z) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
  have hσOn : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) σ
      (Metric.ball τ (ε / 2)) := hσ.contMDiffOn
  exact (hExtOn.comp hσOn hsub).contDiffOn

theorem exists_flat_smooth_arc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M]
    {W : Set M} (hW : IsOpen W) (hWc : IsPreconnected W) {p q : M} (hp : p ∈ W) (hq : q ∈ W)
    (hpq : p ≠ q) :
    ∃ γ : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ ∧
      γ 0 = p ∧ γ 1 = q ∧ Set.InjOn γ (Set.Icc (0:ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ W) ∧
      (∀ k : ℕ, 0 < k → iteratedDerivWithin k
        (fun s : ℝ => extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) p (γ s))
        (Set.Ici 0) 0 = 0) ∧
      (∀ k : ℕ, 0 < k → iteratedDerivWithin k
        (fun s : ℝ => extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) q (γ s))
        (Set.Iic 1) 1 = 0) := by
  set I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)) with hI
  obtain ⟨σ, hσc, hσ0, hσ1, hσinj, hσW⟩ :=
    Work.Whitney.exists_smooth_arc_of_isPreconnected (n := n) hW hWc hp hq hpq
  refine ⟨fun t => σ (Real.smoothTransition t), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hσc.comp (contMDiff_iff_contDiff.mpr Real.smoothTransition.contDiff)
  · simp [Real.smoothTransition.zero, hσ0]
  · simp [Real.smoothTransition.one, hσ1]
  · intro a ha b hb hab
    have ha' : Real.smoothTransition a ∈ Set.Icc (0:ℝ) 1 :=
      ⟨Real.smoothTransition.nonneg a, Real.smoothTransition.le_one a⟩
    have hb' : Real.smoothTransition b ∈ Set.Icc (0:ℝ) 1 :=
      ⟨Real.smoothTransition.nonneg b, Real.smoothTransition.le_one b⟩
    exact smoothTransition_injOn ha hb (hσinj ha' hb' hab)
  · intro t ht
    exact hσW _ ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  · intro k hk
    obtain ⟨r, hr, hH⟩ := chartExpr_contDiffOn (n := n) (M := M) hσc hσ0
    refine flatComp (ψ := Real.smoothTransition) (H := fun u => extChartAt I p (σ u))
      (τ := 0) (r := r) hr (Real.smoothTransition.contDiff.contDiffOn)
      smoothTransition_flat.1 (by simpa only [Real.smoothTransition.zero] using hH) k hk
  · intro k hk
    obtain ⟨r, hr, hH⟩ := chartExpr_contDiffOn (n := n) (M := M) hσc hσ1
    refine flatComp_left (ψ := Real.smoothTransition) (H := fun u => extChartAt I q (σ u))
      (τ := 1) (r := r) hr (Real.smoothTransition.contDiff.contDiffOn)
      smoothTransition_flat.2 (by simpa only [Real.smoothTransition.one] using hH) k hk

end Work.Noncompact.ProperLine
