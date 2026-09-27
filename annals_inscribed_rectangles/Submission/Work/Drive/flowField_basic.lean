import Mathlib
import Submission.Work.Drive.BoxParityDefs
import Submission.Work.Drive.contDiff_cofactorVectorF

namespace Work.Drive

open scoped ContDiff Topology
open Filter Set

noncomputable section

/-- **The flow field is smooth.**  It is the product of the smooth bump `boxBump m`, the smooth
positive scalar `(√(1 + ‖cofactorVectorF F‖²))⁻¹` and the smooth cofactor field
`cofactorVectorF F` (smooth by `contDiff_cofactorVectorF`). -/
theorem contDiff_flowField {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.flowField F) := by
  have hcof : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.cofactorVectorF F) :=
    contDiff_cofactorVectorF hF
  have hnsq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Work.Drive.Amb m => ‖Work.Drive.cofactorVectorF F x‖ ^ 2) := by
    rw [show (fun x : Work.Drive.Amb m => ‖Work.Drive.cofactorVectorF F x‖ ^ 2)
        = (fun x : Work.Drive.Amb m =>
            inner ℝ (Work.Drive.cofactorVectorF F x) (Work.Drive.cofactorVectorF F x)) from
        funext (fun x => (real_inner_self_eq_norm_sq _).symm)]
    exact ContDiff.inner ℝ hcof hcof
  have hsqrt : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Work.Drive.Amb m => Real.sqrt (1 + ‖Work.Drive.cofactorVectorF F x‖ ^ 2)) :=
    ContDiff.sqrt (contDiff_const.add hnsq) (fun x => by positivity)
  have hinv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Work.Drive.Amb m => (Real.sqrt (1 + ‖Work.Drive.cofactorVectorF F x‖ ^ 2))⁻¹) :=
    hsqrt.inv (fun x => by positivity)
  have hbump : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Work.Drive.Amb m => boxBump m x) := by
    unfold boxBump
    exact ContDiffBump.contDiff _
  exact ContDiff.smul hbump (hinv.smul hcof)

/-- **The flow field has compact support**, because it is the product (in the sense of `smul`) of the
compactly supported bump `boxBump m` with an arbitrary vector field. -/
theorem hasCompactSupport_flowField {m : ℕ} (F : Work.Drive.Amb m → Work.Drive.Tgt m) :
    HasCompactSupport (Work.Drive.flowField F) := by
  have hbump : HasCompactSupport (boxBump m) := by
    unfold boxBump
    exact ContDiffBump.hasCompactSupport _
  unfold flowField
  exact hbump.smul_right

/-- The derivative of a compactly supported smooth function is compactly supported: it vanishes on
the (open) complement of the topological support. -/
theorem hasCompactSupport_fderiv_of_hasCompactSupport {m : ℕ} {f : Work.Drive.Amb m → Work.Drive.Amb m}
    (hsupp : HasCompactSupport f) :
    HasCompactSupport (fderiv ℝ f) := by
  refine hsupp.mono' ?_
  intro x hx
  simp only [Function.mem_support] at hx
  by_contra hc
  exact hx (by
    have hev : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hc
    rw [hev.fderiv_eq]
    simp)

/-- A compactly supported smooth function is Lipschitz.  Its derivative is continuous and compactly
supported, hence bounded by some `C`, and the mean value inequality gives the Lipschitz bound. -/
theorem exists_lipschitzWith_of_contDiff_hasCompactSupport {m : ℕ}
    {f : Work.Drive.Amb m → Work.Drive.Amb m}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hsupp : HasCompactSupport f) :
    ∃ L : NNReal, LipschitzWith L f := by
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hdiff : Differentiable ℝ f := hf.differentiable hne
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv hne
  obtain ⟨C, hC⟩ :=
    (hasCompactSupport_fderiv_of_hasCompactSupport hsupp).exists_bound_of_continuous hcont
  let L : NNReal := ⟨max C 0, le_max_right _ _⟩
  have hL : (L : ℝ) = max C 0 := rfl
  refine ⟨L, ?_⟩
  refine lipschitzWith_of_nnnorm_fderiv_le hdiff (fun x => ?_)
  rw [← NNReal.coe_le_coe, coe_nnnorm, hL]
  exact (hC x).trans (le_max_left _ _)

theorem flowField_basic {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.flowField F) ∧
      HasCompactSupport (Work.Drive.flowField F) ∧
      ∃ L : NNReal, LipschitzWith L (Work.Drive.flowField F) :=
  ⟨contDiff_flowField hF, hasCompactSupport_flowField F,
    exists_lipschitzWith_of_contDiff_hasCompactSupport (contDiff_flowField hF)
      (hasCompactSupport_flowField F)⟩

end

end Work.Drive
