import Submission.FUP.DbarWeak
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Normed.Lp.SmoothApprox

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Smooth compactly supported elements of the domain of the weak `∂̄`-operator

For a `C¹` weight `φ` and a smooth compactly supported function `f` on `ℂᵈ`, the pointwise
Wirtinger derivative `∂̄f` (as an `L²(μ_φ)`-valued `(0,1)`-form) satisfies the weak `∂̄`-relation
`DbarWeak φ f (∂̄f)`.  Consequently the smooth compactly supported functions form a subspace of
`Dom (dbarOp φ)`, and `Dom (dbarOp φ)` is dense in `L²(μ_φ)`.

The key ingredient is the weighted integration-by-parts identity `integral_dbar_mul_adjoint`
of `Submission.FUP.DbarAdjoint`.
-/

namespace Submission.FUP

variable {d : ℕ}

/-- The pointwise `∂̄` of a function, as a `FormSpace d`-valued function. -/
noncomputable def dbarFormFun (f : FormDu d → ℂ) : FormDu d → FormSpace d :=
  fun z => WithLp.toLp 2 (fun j => partialZbar j f z)

@[simp] lemma toFormFun_dbarFormFun (f : FormDu d → ℂ) :
    toFormFun (dbarFormFun f) = fun z j => partialZbar j f z := rfl

@[simp] lemma dbarFormFun_apply (f : FormDu d → ℂ) (z : FormDu d) (j : Fin d) :
    dbarFormFun f z j = partialZbar j f z := rfl

lemma contDiff_dbarFormFun {f : FormDu d → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dbarFormFun f) := by
  rw [contDiff_piLp]
  intro j
  have h' : ContDiff ℝ ∞ (dbarFun f) := contDiff_dbarFun hf
  rw [contDiff_pi] at h'
  convert h' j using 1
  funext z
  rfl

lemma hasCompactSupport_dbarFormFun {f : FormDu d → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (dbarFormFun f) := by
  refine hf.mono' ?_
  intro z hz
  by_contra hzc
  have hd : fderiv ℝ f z = 0 := (HasFDerivAt.of_notMem_tsupport ℝ hzc).fderiv
  exact hz (by refine PiLp.ext (fun j => ?_); simp [dbarFormFun, partialZbar, hd])

/-- The weighted integration-by-parts identity of `∂̄`, in the form needed for the weak relation:
the `μ_φ`-integral of `∑_j ∂̄_j g · conj(u_j)` equals the `μ_φ`-integral of
`conj(ϑ_φ u) · g`. -/
theorem integral_inner_dbar_eq {g : FormDu d → ℂ} {u : FormDu d → (Fin d → ℂ)}
    {φ : FormDu d → ℝ} (hg : ContDiff ℝ 1 g)
    (hu : ∀ j, ContDiff ℝ 1 (fun w => u w j))
    (hφ : ContDiff ℝ 1 φ) (hsg : HasCompactSupport g)
    (hsu : ∀ j, HasCompactSupport (fun w => u w j)) :
    (∫ z, (∑ j, partialZbar j g z * star (u z j))
        * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)
      = ∫ z, (star (dbarAdjoint φ u z) * g z)
          * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume := by
  have hφ1 : ContDiff ℝ 1 fun w => ((φ w : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp hφ
  have h := integral_dbar_mul_adjoint hg hu hφ1 hsg hsu
  refine h.trans (integral_congr_ae (μ := volume) (Eventually.of_forall fun z => ?_))
  show g z * star (dbarAdjoint φ u z) * Complex.exp (-(((φ z : ℝ) : ℂ)))
      = star (dbarAdjoint φ u z) * g z * Complex.exp (-(((φ z : ℝ) : ℂ)))
  ring



section SmoothDomain

variable {d : ℕ}

/-- Smooth compactly supported functions satisfy the weak `∂̄`-relation with `∂̄f` computed
pointwise. -/
theorem dbarWeak_smooth {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) {f : FormDu d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hsf : HasCompactSupport f)
    (hmem : MemLp f 2 (wtMeasure φ))
    (hwm : MemLp (dbarFormFun f) 2 (wtMeasure φ)) :
    DbarWeak φ (hmem.toLp f) (hwm.toLp (dbarFormFun f)) := by
  intro ψ h1 h2 hψ hθ
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hu1 : ∀ j, ContDiff ℝ 1 (fun w => toFormFun ψ w j) :=
    fun i => (contDiff_toFormFun h1 i).of_le (by simp)
  have hsu : ∀ j, HasCompactSupport (fun w => toFormFun ψ w j) :=
    fun i => (hasCompactSupport_toFormFun h2).comp_left
      (g := fun v : Fin d → ℂ => v i) (by simp)
  have haeA : (fun z => inner ℂ ((↑↑(hψ.toLp ψ) : FormDu d → FormSpace d) z)
        ((↑↑(hwm.toLp (dbarFormFun f)) : FormDu d → FormSpace d) z))
      =ᵐ[wtMeasure φ] (fun z => inner ℂ (ψ z) (dbarFormFun f z)) := by
    filter_upwards [MemLp.coeFn_toLp hψ, MemLp.coeFn_toLp hwm] with z hz1 hz2
    rw [hz1, hz2]
  have hA : inner ℂ (hψ.toLp ψ) (hwm.toLp (dbarFormFun f))
      = ∫ z, (∑ j, partialZbar j f z * star (toFormFun ψ z j))
          * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
    rw [MeasureTheory.L2.inner_def]
    refine (integral_congr_ae haeA).trans ?_
    rw [integral_wtMeasure hφ.continuous]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    change Real.exp (-(φ z)) • inner ℂ (ψ z) (dbarFormFun f z)
      = (∑ j, partialZbar j f z * star ((ψ z).ofLp j)) * Complex.exp (-(((φ z : ℝ) : ℂ)))
    rw [PiLp.inner_apply]
    simp only [WithLp.ofLp_toLp, dbarFormFun_apply, RCLike.inner_apply, starRingEnd_apply,
      Complex.real_smul, Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  have haeB : (fun z => inner ℂ ((↑↑(hθ.toLp (dbarAdjoint φ (toFormFun ψ))) : FormDu d → ℂ) z)
        ((↑↑(hmem.toLp f) : FormDu d → ℂ) z))
      =ᵐ[wtMeasure φ] (fun z => inner ℂ (dbarAdjoint φ (toFormFun ψ) z) (f z)) := by
    filter_upwards [MemLp.coeFn_toLp hθ, MemLp.coeFn_toLp hmem] with z hz1 hz2
    rw [hz1, hz2]
  have hB : inner ℂ (hθ.toLp (dbarAdjoint φ (toFormFun ψ))) (hmem.toLp f)
      = ∫ z, (star (dbarAdjoint φ (toFormFun ψ) z) * f z)
          * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
    rw [MeasureTheory.L2.inner_def]
    refine (integral_congr_ae haeB).trans ?_
    rw [integral_wtMeasure hφ.continuous]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show Real.exp (-(φ z)) • inner ℂ (dbarAdjoint φ (toFormFun ψ) z) (f z)
      = star (dbarAdjoint φ (toFormFun ψ) z) * f z * Complex.exp (-(((φ z : ℝ) : ℂ)))
    simp only [RCLike.inner_apply, starRingEnd_apply, Complex.real_smul, Complex.ofReal_exp,
      Complex.ofReal_neg]
    ring
  rw [hA, hB]
  exact integral_inner_dbar_eq hf1 hu1 hφ hsf hsu

/-- Smooth compactly supported functions lie in the domain of the weak `∂̄`-operator. -/
theorem mem_domain_dbarOp_of_smooth {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {f : FormDu d → ℂ} (hf : ContDiff ℝ ∞ f) (hsf : HasCompactSupport f) :
    (memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous hf hsf).toLp f
      ∈ (dbarOp φ).domain :=
  mem_dbarOp_domain.mpr ⟨_, dbarWeak_smooth hφ hf hsf _
    (memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous
      (contDiff_dbarFormFun hf) (hasCompactSupport_dbarFormFun hsf))⟩

/-- **The domain of the weak `∂̄`-operator is dense** in `L²(μ_φ)`: it contains the smooth
compactly supported functions, which are dense. -/
theorem dense_domain_dbarOp {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Dense ((dbarOp φ).domain : Set (Lp ℂ 2 (wtMeasure φ))) := by
  haveI : IsFiniteMeasureOnCompacts (wtMeasure φ) :=
    isFiniteMeasureOnCompacts_wtMeasure hφ.continuous
  refine (MeasureTheory.Lp.dense_hasCompactSupport_contDiff (p := 2) (μ := wtMeasure φ)
    (E := FormDu d) (F := ℂ) (by norm_num)).mono ?_
  rintro f ⟨g, hfg, hgs, hgc⟩
  have hmem : MemLp g 2 (wtMeasure φ) :=
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous hgc hgs
  have hfeq : f = hmem.toLp g := Lp.ext (hfg.trans (MemLp.coeFn_toLp hmem).symm)
  rw [hfeq]
  exact mem_domain_dbarOp_of_smooth hφ hgc hgs

end SmoothDomain


section AdjointSmooth

variable {d : ℕ}

/-- The defining relation of the adjoint, tested against an element of the domain of `dbarOp φ`:
`⟪ϑ_φx, f⟫ = ⟪x, ∂̄f⟫` for a smooth compactly supported form `x`. -/
theorem dbarOp_adjoint_key_of_smooth {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {x : FormDu d → FormSpace d} (hx : ContDiff ℝ ∞ x) (hxs : HasCompactSupport x)
    (hxm : MemLp x 2 (wtMeasure φ))
    (hxmθ : MemLp (dbarAdjoint φ (toFormFun x)) 2 (wtMeasure φ))
    (f : (dbarOp φ).domain) :
    inner ℂ (hxmθ.toLp (dbarAdjoint φ (toFormFun x))) (f : Lp ℂ 2 (wtMeasure φ))
      = inner ℂ (hxm.toLp x) (dbarOp φ f) := by
  have hw : DbarWeak φ (f : Lp ℂ 2 (wtMeasure φ)) (dbarOp φ f) := by
    have hh := LinearPMap.mem_graph (dbarOp φ) f
    rw [dbarOp_graph hφ, mem_dbarGraph] at hh
    exact hh
  exact (hw x hx hxs hxm hxmθ).symm

/-- A smooth compactly supported form lies in the domain of the adjoint of `dbarOp φ`. -/
theorem mem_adjointDomain_of_smooth {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {x : FormDu d → FormSpace d} (hx : ContDiff ℝ ∞ x) (hxs : HasCompactSupport x)
    (hxm : MemLp x 2 (wtMeasure φ))
    (hxmθ : MemLp (dbarAdjoint φ (toFormFun x)) 2 (wtMeasure φ)) :
    hxm.toLp x ∈ (dbarOp φ).adjoint.domain :=
  LinearPMap.mem_adjoint_domain_of_exists _
    ⟨_, fun f => dbarOp_adjoint_key_of_smooth hφ hx hxs hxm hxmθ f⟩

/-- **The adjoint of the weak `∂̄`-operator is the formal adjoint `ϑ_φ`** on smooth compactly
supported forms. -/
theorem dbarOp_adjoint_apply_of_smooth {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {x : FormDu d → FormSpace d} (hx : ContDiff ℝ ∞ x) (hxs : HasCompactSupport x)
    (hxm : MemLp x 2 (wtMeasure φ))
    (hxmθ : MemLp (dbarAdjoint φ (toFormFun x)) 2 (wtMeasure φ))
    (h : hxm.toLp x ∈ (dbarOp φ).adjoint.domain) :
    (dbarOp φ).adjoint ⟨hxm.toLp x, h⟩ = hxmθ.toLp (dbarAdjoint φ (toFormFun x)) :=
  LinearPMap.adjoint_apply_eq (dense_domain_dbarOp hφ) ⟨_, h⟩
    (fun f => dbarOp_adjoint_key_of_smooth hφ hx hxs hxm hxmθ f)

end AdjointSmooth


end Submission.FUP
