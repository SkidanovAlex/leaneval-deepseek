import Submission.FUP.DbarShift
import Submission.Commons.Analysis.InnerProductSpace.LinearPMap.exists_solution_of_bound
import Submission.Commons.Analysis.InnerProductSpace.LinearPMap.adjoint_adjoint_of_isClosed

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The weak adjoint `ϑ_φ = ∂̄^*` as a closed operator

The abstract existence theorem
`Commons.Analysis.InnerProductSpace.LinearPMap.exists_solution_of_bound` is applied to the pair
`T = ∂̄ : H1 → H2` and `S = ∂̄₂ : H2 → H3`.  Taking for `T` the *maximal* weak `∂̄`-operator
`Submission.FUP.dbarOp φ` would force the proof of `T^† = ϑ_φ` to go through the density of the
smooth compactly supported forms in `Dom T` (a Friedrichs-type argument).  It is cheaper
(and logically cleaner) to take instead for `T` the *minimal* operator

  `T = (ϑ_φ)^†`,  where `ϑ_φ` is defined directly by its weak relation

  `DbarAdjWeak φ y z : ⟪z, f⟫ = ⟪y, ∂̄f⟫` for all smooth compactly supported `f`,

i.e. `y ∈ Dom ϑ_φ` with `ϑ_φ y = z`.  Then `T^† = ϑ_φ` holds *by construction* (adjoint of an
adjoint), `Dom T` is dense (`dense_adjoint_domain_of_adjoint_adjoint`), `T^†† = T` (closed,
densely defined), and the product rule/mollification properties are checked directly against the
test-form relation `DbarAdjWeak`.

# Main declarations

* `dbarAdjWeak φ y z` — the weak-`ϑ` relation;
* `dbarAdjOp φ` — the operator `ϑ_φ : H2 → H1`, its graph is closed (`isClosed_dbarAdjOp`);
* `dbarAdjOp_smooth` — smooth compactly supported forms lie in `Dom ϑ_φ` with `ϑ_φy = ϑ_φ y`
  computed pointwise;
* `dbarOpMin φ := (dbarAdjOp φ).adjoint` — the *minimal* `∂̄` operator, with
  `dbarOpMin_adjoint : (dbarOpMin φ)^† = dbarAdjOp φ`.
-/

namespace Submission.FUP

noncomputable section

variable {d : ℕ}

/-- The Hilbert space of `(0,1)`-forms `L²(μ_φ)`. -/
abbrev H2 (φ : FormDu d → ℝ) := Lp (FormSpace d) 2 (wtMeasure φ)

/-- The Hilbert space `L²(μ_φ)`. -/
abbrev H1 (φ : FormDu d → ℝ) := Lp ℂ 2 (wtMeasure φ)

/-- The Hilbert space of `(0,2)`-forms `L²(μ_φ)`. -/
abbrev H3 (φ : FormDu d → ℝ) := Lp (FormSpace2 d) 2 (wtMeasure φ)

section WeakAdj

/-- **The weak relation defining `ϑ_φ = ∂̄^*`**: `z = ϑ_φ y` means `⟪z, f⟫ = ⟪y, ∂̄f⟫` for every
smooth compactly supported `f`. -/
def dbarAdjWeak (φ : FormDu d → ℝ) (y : H2 φ) (z : H1 φ) : Prop :=
  ∀ (f : FormDu d → ℂ) (h1 : ContDiff ℝ ∞ f) (h2 : HasCompactSupport f)
    (hf : MemLp f 2 (wtMeasure φ)) (hw : MemLp (dbarFormFun f) 2 (wtMeasure φ)),
    inner ℂ z (hf.toLp f) = inner ℂ y (hw.toLp (dbarFormFun f))

lemma dbarAdjWeak.add {φ : FormDu d → ℝ} {y y' : H2 φ} {z z' : H1 φ}
    (h : dbarAdjWeak φ y z) (h' : dbarAdjWeak φ y' z') :
    dbarAdjWeak φ (y + y') (z + z') := by
  intro f h1 h2 hf hw
  rw [inner_add_left, inner_add_left, h f h1 h2 hf hw, h' f h1 h2 hf hw]

lemma dbarAdjWeak.smul {φ : FormDu d → ℝ} (c : ℂ) {y : H2 φ} {z : H1 φ}
    (h : dbarAdjWeak φ y z) : dbarAdjWeak φ (c • y) (c • z) := by
  intro f h1 h2 hf hw
  rw [inner_smul_left, inner_smul_left, h f h1 h2 hf hw]

lemma dbarAdjWeak.zero {φ : FormDu d → ℝ} :
    dbarAdjWeak φ (0 : H2 φ) (0 : H1 φ) := by
  intro f h1 h2 hf hw
  rw [inner_zero_left, inner_zero_left]

/-- The graph of the weak `ϑ_φ`-relation. -/
def dbarAdjGraph (φ : FormDu d → ℝ) : Submodule ℂ (H2 φ × H1 φ) where
  carrier := {p | dbarAdjWeak φ p.1 p.2}
  zero_mem' := dbarAdjWeak.zero
  add_mem' hp hq := dbarAdjWeak.add hp hq
  smul_mem' c _ hp := dbarAdjWeak.smul c hp

@[simp] lemma mem_dbarAdjGraph {φ : FormDu d → ℝ} {p : H2 φ × H1 φ} :
    p ∈ dbarAdjGraph φ ↔ dbarAdjWeak φ p.1 p.2 := Iff.rfl

/-- The graph of the weak `ϑ_φ`-relation is closed: it is an intersection of the equations
`⟪z, f⟫ = ⟪y, ∂̄f⟫` in the continuous functionals `⟪·, f⟫` and `⟪·, ∂̄f⟫`. -/
theorem isClosed_dbarAdjGraph (φ : FormDu d → ℝ) :
    IsClosed (dbarAdjGraph φ : Set (H2 φ × H1 φ)) := by
  have hset : (dbarAdjGraph φ : Set (H2 φ × H1 φ))
      = ⋂ (f : FormDu d → ℂ) (h1 : ContDiff ℝ ∞ f) (h2 : HasCompactSupport f)
          (hf : MemLp f 2 (wtMeasure φ)) (hw : MemLp (dbarFormFun f) 2 (wtMeasure φ)),
        {p | inner ℂ p.2 (hf.toLp f) = inner ℂ p.1 (hw.toLp (dbarFormFun f))} := by
    ext p
    simp only [mem_dbarAdjGraph, Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun h f h1 h2 hf hw => h f h1 h2 hf hw,
      fun h f h1 h2 hf hw => h f h1 h2 hf hw⟩
  rw [hset]
  refine isClosed_iInter fun f => isClosed_iInter fun h1 => isClosed_iInter fun h2 =>
    isClosed_iInter fun hf => isClosed_iInter fun hw => ?_
  exact isClosed_eq (Continuous.inner continuous_snd continuous_const)
    (Continuous.inner continuous_fst continuous_const)

/-- The weak `ϑ_φ`-relation is single-valued: the smooth compactly supported functions are dense
in `L²(μ_φ)`. -/
theorem dbarAdjWeak_unique {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) {y : H2 φ} {z z' : H1 φ}
    (hz : dbarAdjWeak φ y z) (hz' : dbarAdjWeak φ y z') : z = z' := by
  haveI : IsFiniteMeasureOnCompacts (wtMeasure φ) :=
    isFiniteMeasureOnCompacts_wtMeasure hφ.continuous
  have hdense : Dense ({f : H1 φ | ∃ g, f =ᵐ[wtMeasure φ] g ∧ HasCompactSupport g ∧
      ContDiff ℝ ∞ g} : Set (H1 φ)) :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (p := 2) (μ := wtMeasure φ)
      (E := FormDu d) (F := ℂ) (by norm_num)
  have h0 : ∀ f : H1 φ, inner ℂ (z - z') f = 0 := by
    have hclosed : IsClosed {f : H1 φ | inner ℂ (z - z') f = 0} :=
      isClosed_eq (Continuous.inner continuous_const continuous_id) continuous_const
    have hsub : ({f : H1 φ | ∃ g, f =ᵐ[wtMeasure φ] g ∧ HasCompactSupport g ∧
        ContDiff ℝ ∞ g} : Set (H1 φ)) ⊆ {f : H1 φ | inner ℂ (z - z') f = 0} := by
      rintro f ⟨g, hfg, hgs, hgc⟩
      have hgm : MemLp g 2 (wtMeasure φ) :=
        memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous hgc hgs
      have hwm : MemLp (dbarFormFun g) 2 (wtMeasure φ) :=
        memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous
          (contDiff_dbarFormFun hgc) (hasCompactSupport_dbarFormFun hgs)
      have hfeq : f = hgm.toLp g := Lp.ext (hfg.trans (MemLp.coeFn_toLp hgm).symm)
      show inner ℂ (z - z') f = 0
      rw [hfeq, inner_sub_left]
      have h1 := hz g hgc hgs hgm hwm
      have h2 := hz' g hgc hgs hgm hwm
      rw [h1, h2, sub_self]
    have hcl : closure ({f : H1 φ | ∃ g, f =ᵐ[wtMeasure φ] g ∧ HasCompactSupport g ∧
        ContDiff ℝ ∞ g} : Set (H1 φ)) ⊆ {f : H1 φ | inner ℂ (z - z') f = 0} :=
      hclosed.closure_subset_iff.mpr hsub
    intro f
    exact hcl (by rw [hdense.closure_eq]; trivial)
  have := h0 (z - z')
  rw [inner_self_eq_zero] at this
  exact sub_eq_zero.mp this

/-- **The weak adjoint `ϑ_φ` of `∂̄`.** -/
noncomputable def dbarAdjOp (φ : FormDu d → ℝ) : H2 φ →ₗ.[ℂ] H1 φ :=
  (dbarAdjGraph φ).toLinearPMap

end WeakAdj


section Graph

/-- The graph of `dbarAdjOp φ` is `dbarAdjGraph φ`. -/
theorem dbarAdjOp_graph {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (dbarAdjOp φ).graph = dbarAdjGraph φ := by
  show (dbarAdjGraph φ).toLinearPMap.graph = dbarAdjGraph φ
  exact Submodule.toLinearPMap_graph_eq _
    (fun x hx hx1 => by
      rw [mem_dbarAdjGraph] at hx
      rw [hx1] at hx
      exact dbarAdjWeak_unique hφ hx dbarAdjWeak.zero)

/-- `dbarAdjOp φ` is closed. -/
theorem isClosed_dbarAdjOp {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (dbarAdjOp φ).IsClosed := by
  show IsClosed ((dbarAdjOp φ).graph : Set (H2 φ × H1 φ))
  rw [dbarAdjOp_graph hφ]
  exact isClosed_dbarAdjGraph φ

/-- Membership in the domain of `dbarAdjOp φ`, in terms of the weak relation. -/
theorem mem_dbarAdjOp_domain {φ : FormDu d → ℝ} {y : H2 φ} :
    y ∈ (dbarAdjOp φ).domain ↔ ∃ z, dbarAdjWeak φ y z := by
  rw [dbarAdjOp, Submodule.toLinearPMap_domain, Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, hp1⟩
    exact ⟨p.2, hp1 ▸ hp⟩
  · rintro ⟨z, hz⟩
    exact ⟨(y, z), hz, rfl⟩

/-- The value of `dbarAdjOp φ` at `y` is the (unique) `z` with `dbarAdjWeak φ y z`. -/
theorem dbarAdjOp_apply_eq {φ : FormDu d → ℝ} {hφ : ContDiff ℝ 1 φ} {y : H2 φ}
    (hy : y ∈ (dbarAdjOp φ).domain) {z : H1 φ}
    (hz : dbarAdjWeak φ y z) : dbarAdjOp φ ⟨y, hy⟩ = z := by
  have hmem : dbarAdjWeak φ y (dbarAdjOp φ ⟨y, hy⟩) := by
    have h := LinearPMap.mem_graph (dbarAdjOp φ) ⟨y, hy⟩
    rw [dbarAdjOp_graph hφ, mem_dbarAdjGraph] at h
    exact h
  exact dbarAdjWeak_unique hφ hmem hz

end Graph

section Smooth

/-- Smooth compactly supported forms satisfy the weak `ϑ_φ`-relation with `ϑ_φ` computed
pointwise. -/
theorem dbarAdjWeak_smooth {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {y : FormDu d → (Fin d → ℂ)} (hy : ∀ j, ContDiff ℝ ∞ (fun z => y z j))
    (hys : ∀ j, HasCompactSupport (fun z => y z j))
    (hym : MemLp (liftForm y) 2 (wtMeasure φ))
    (hθ : MemLp (dbarAdjoint φ y) 2 (wtMeasure φ)) :
    dbarAdjWeak φ (hym.toLp (liftForm y)) (hθ.toLp (dbarAdjoint φ y)) := by
  intro f h1 h2 hf hw
  have hf1 : ContDiff ℝ 1 f := h1.of_le (by simp)
  have hy1 : ∀ j, ContDiff ℝ 1 (fun z => y z j) := fun j => (hy j).of_le (by simp)
  have haeA : (fun z => inner ℂ ((↑↑(hθ.toLp (dbarAdjoint φ y)) : FormDu d → ℂ) z)
        ((↑↑(hf.toLp f) : FormDu d → ℂ) z))
      =ᵐ[wtMeasure φ] (fun z => inner ℂ (dbarAdjoint φ y z) (f z)) := by
    filter_upwards [MemLp.coeFn_toLp hθ, MemLp.coeFn_toLp hf] with z hz1 hz2
    rw [hz1, hz2]
  have hA : inner ℂ (hθ.toLp (dbarAdjoint φ y)) (hf.toLp f)
      = ∫ z, (star (dbarAdjoint φ y z) * f z) * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
    rw [MeasureTheory.L2.inner_def, integral_congr_ae haeA,
      integral_wtMeasure hφ.continuous]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show Real.exp (-(φ z)) • inner ℂ (dbarAdjoint φ y z) (f z)
      = star (dbarAdjoint φ y z) * f z * Complex.exp (-(((φ z : ℝ) : ℂ)))
    simp only [RCLike.inner_apply, starRingEnd_apply, Complex.real_smul, Complex.ofReal_exp,
      Complex.ofReal_neg]
    ring
  have haeB : (fun z => inner ℂ ((↑↑(hym.toLp (liftForm y)) : FormDu d → FormSpace d) z)
        ((↑↑(hw.toLp (dbarFormFun f)) : FormDu d → FormSpace d) z))
      =ᵐ[wtMeasure φ] (fun z => inner ℂ (liftForm y z) (dbarFormFun f z)) := by
    filter_upwards [MemLp.coeFn_toLp hym, MemLp.coeFn_toLp hw] with z hz1 hz2
    rw [hz1, hz2]
  have hB : inner ℂ (hym.toLp (liftForm y)) (hw.toLp (dbarFormFun f))
      = ∫ z, (∑ j, partialZbar j f z * star (y z j))
          * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
    rw [MeasureTheory.L2.inner_def, integral_congr_ae haeB,
      integral_wtMeasure hφ.continuous]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show Real.exp (-(φ z)) • inner ℂ (liftForm y z) (dbarFormFun f z)
      = (∑ j, partialZbar j f z * star (y z j)) * Complex.exp (-(((φ z : ℝ) : ℂ)))
    rw [PiLp.inner_apply]
    simp only [liftForm_apply, dbarFormFun_apply, RCLike.inner_apply, starRingEnd_apply,
      Complex.real_smul, Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  rw [hA, hB]
  exact (integral_inner_dbar_eq hf1 hy1 hφ h2 hys).symm

/-- Smooth compactly supported forms lie in the domain of `dbarAdjOp φ`. -/
theorem mem_domain_dbarAdjOp_of_smooth {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {y : FormDu d → (Fin d → ℂ)} (hy : ∀ j, ContDiff ℝ ∞ (fun z => y z j))
    (hys : HasCompactSupport y) (hym : MemLp (liftForm y) 2 (wtMeasure φ)) :
    hym.toLp (liftForm y) ∈ (dbarAdjOp φ).domain :=
  mem_dbarAdjOp_domain.mpr ⟨_,
    dbarAdjWeak_smooth hφ hy (fun j => hasCompactSupport_comp j hys) hym
      (memLp_dbarAdjoint hφ (fun j => (hy j).of_le (by simp)) hys)⟩

/-- **The domain of `dbarAdjOp φ` is dense** in `L²(μ_φ)`: it contains the smooth compactly
supported forms. -/
theorem dense_domain_dbarAdjOp {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Dense ((dbarAdjOp φ).domain : Set (H2 φ)) := by
  haveI : IsFiniteMeasureOnCompacts (wtMeasure φ) :=
    isFiniteMeasureOnCompacts_wtMeasure hφ.continuous
  refine (MeasureTheory.Lp.dense_hasCompactSupport_contDiff (p := 2) (μ := wtMeasure φ)
    (E := FormDu d) (F := FormSpace d) (by norm_num)).mono ?_
  rintro f ⟨g, hfg, hgs, hgc⟩
  have hmem : MemLp g 2 (wtMeasure φ) :=
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous hgc hgs
  have hfeq : f = hmem.toLp g := Lp.ext (hfg.trans (MemLp.coeFn_toLp hmem).symm)
  rw [hfeq]
  have hcomp : ∀ j, ContDiff ℝ ∞ (fun z => toFormFun g z j) := contDiff_toFormFun hgc
  have hcs : HasCompactSupport (toFormFun g) := hasCompactSupport_toFormFun hgs
  have hym : MemLp (liftForm (toFormFun g)) 2 (wtMeasure φ) :=
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous (contDiff_liftForm hcomp)
      (hasCompactSupport_liftForm hcs)
  have hlift : liftForm (toFormFun g) = g := by
    funext z; simp only [liftForm, toFormFun_apply, WithLp.equiv_apply, WithLp.toLp_ofLp]
  have heq : hym.toLp (liftForm (toFormFun g)) = hmem.toLp g :=
    MemLp.toLp_congr hym hmem (by rw [hlift])
  rw [← heq]
  exact mem_domain_dbarAdjOp_of_smooth hφ hcomp hcs hym

end Smooth

section Minimal

/-- **The minimal weak `∂̄`-operator** `T = (ϑ_φ)^†`.  Its adjoint is `ϑ_φ` *by construction*, so
the awkward identification of the adjoint of the maximal weak `∂̄`-operator is not needed. -/
noncomputable def dbarOpMin (φ : FormDu d → ℝ) : H1 φ →ₗ.[ℂ] H2 φ :=
  (dbarAdjOp φ).adjoint

/-- The adjoint of the minimal `∂̄`-operator is the weak `ϑ_φ`. -/
theorem dbarOpMin_adjoint {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (dbarOpMin φ).adjoint = dbarAdjOp φ :=
  Commons.Analysis.InnerProductSpace.LinearPMap.adjoint_adjoint_of_isClosed (dbarAdjOp φ)
    (dense_domain_dbarAdjOp hφ) (isClosed_dbarAdjOp hφ)

/-- The minimal `∂̄`-operator is closed and densely defined, so `T^†^† = T`. -/
theorem dbarOpMin_adjoint_adjoint {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (dbarOpMin φ).adjoint.adjoint = dbarOpMin φ := by
  rw [dbarOpMin_adjoint hφ]
  rfl

/-- The domain of the minimal `∂̄`-operator is dense. -/
theorem dense_domain_dbarOpMin {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Dense ((dbarOpMin φ).domain : Set (H1 φ)) :=
  Commons.Analysis.InnerProductSpace.LinearPMap.dense_adjoint_domain (dbarAdjOp φ)
    (dense_domain_dbarAdjOp hφ) (dbarOpMin_adjoint hφ)

end Minimal

end

end Submission.FUP
