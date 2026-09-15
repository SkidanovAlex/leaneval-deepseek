import Submission.FUP.WeightMeasure
import Submission.FUP.DbarAdjoint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Calculus.ContDiff.WithLp

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The weak `∂̄`-operator on `L²(e^{-φ}dvol)`

Design note: the Hilbert space of `(0,1)`-forms must be `Lp (EuclideanSpace ℂ (Fin d)) 2 μ_φ`, not
`Lp (Fin d → ℂ) 2 μ_φ`: the product type `Fin d → ℂ` carries the *sup* norm, which is not induced
by an inner product.  The identifications `EuclideanSpace ℂ (Fin d) = WithLp 2 (Fin d → ℂ)` and the
coercion back to functions `Fin d → ℂ` (with `PiLp.inner_apply` for the inner product) are used
throughout.

NOTE for future edits: in this file the section-variable/local-notation combination
(`variable {d : ℕ}` + `local notation "ℂᵈ"`) breaks typeclass synthesis; the types
`FormSpace d = EuclideanSpace ℂ (Fin d)` and `FormDu d = Fin d → ℂ` are therefore spelled out
explicitly with `{d : ℕ}` bound in every declaration.
-/

namespace Submission.FUP

/-- `ℂ^d` as a real vector space (the domain of the forms). -/
abbrev FormDu (d : ℕ) := Fin d → ℂ

/-- The Hilbert space of `(0,1)`-forms, with the `ℓ²` norm. -/
abbrev FormSpace (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- Forget the `ℓ²` structure of a form. -/
noncomputable def toFormFun {d : ℕ} (ψ : FormDu d → FormSpace d) : FormDu d → (Fin d → ℂ) :=
  fun z => (WithLp.equiv 2 (Fin d → ℂ)) (ψ z)

@[simp] lemma toFormFun_apply {d : ℕ} (ψ : FormDu d → FormSpace d) (z : FormDu d) :
    toFormFun ψ z = (WithLp.equiv 2 (Fin d → ℂ)) (ψ z) := rfl

/-- A component of a vector-valued `L²` function is `L²`. -/
lemma memLp_eval_comp {d : ℕ} {φ : FormDu d → ℝ} (u : Lp (FormSpace d) 2 (wtMeasure φ))
    (j : Fin d) :
    MemLp (fun z => (u : FormDu d → FormSpace d) z j) 2 (wtMeasure φ) := by
  have h : AEMeasurable (fun z : FormDu d => (u : FormDu d → FormSpace d) z) (wtMeasure φ) :=
    AEStronglyMeasurable.aemeasurable (Lp.memLp u).1
  have hc : AEMeasurable (fun z : FormDu d => (u : FormDu d → FormSpace d) z j) (wtMeasure φ) :=
    AEMeasurable.comp_aemeasurable (g := fun x : FormSpace d => x j) (by fun_prop) h
  refine MemLp.mono' (Lp.memLp u).norm hc.aestronglyMeasurable ?_
  filter_upwards with z
  exact PiLp.norm_apply_le ((u : FormDu d → FormSpace d) z) j

section Weak

/-- **The weak `∂̄` relation**: `w = ∂̄ f` in the sense of distributions for the weight
`e^{-φ}dvol`. -/
def DbarWeak {d : ℕ} (φ : FormDu d → ℝ) (f : Lp ℂ 2 (wtMeasure φ))
    (w : Lp (FormSpace d) 2 (wtMeasure φ)) : Prop :=
  ∀ (ψ : FormDu d → FormSpace d) (h1 : ContDiff ℝ ∞ ψ) (h2 : HasCompactSupport ψ)
    (hψ : MemLp ψ 2 (wtMeasure φ))
    (hθ : MemLp (dbarAdjoint φ (toFormFun ψ)) 2 (wtMeasure φ)),
    inner ℂ (hψ.toLp ψ) w = inner ℂ (hθ.toLp (dbarAdjoint φ (toFormFun ψ))) f

/-- The weak relation is additive. -/
lemma DbarWeak.add {d : ℕ} {φ : FormDu d → ℝ} {f f' : Lp ℂ 2 (wtMeasure φ)}
    {w w' : Lp (FormSpace d) 2 (wtMeasure φ)} (hw : DbarWeak φ f w) (hw' : DbarWeak φ f' w') :
    DbarWeak φ (f + f') (w + w') := by
  intro ψ h1 h2 hψ hθ
  rw [inner_add_right, inner_add_right, hw ψ h1 h2 hψ hθ, hw' ψ h1 h2 hψ hθ]

/-- The weak relation is homogeneous. -/
lemma DbarWeak.smul {d : ℕ} {φ : FormDu d → ℝ} (c : ℂ) {f : Lp ℂ 2 (wtMeasure φ)}
    {w : Lp (FormSpace d) 2 (wtMeasure φ)} (hw : DbarWeak φ f w) :
    DbarWeak φ (c • f) (c • w) := by
  intro ψ h1 h2 hψ hθ
  rw [inner_smul_right, inner_smul_right, hw ψ h1 h2 hψ hθ]

/-- The weak relation is negated. -/
lemma DbarWeak.neg {d : ℕ} {φ : FormDu d → ℝ} {f : Lp ℂ 2 (wtMeasure φ)}
    {w : Lp (FormSpace d) 2 (wtMeasure φ)} (hw : DbarWeak φ f w) :
    DbarWeak φ (-f) (-w) := by
  intro ψ h1 h2 hψ hθ
  rw [inner_neg_right, inner_neg_right, hw ψ h1 h2 hψ hθ]

/-- The weak relation is subtracted. -/
lemma DbarWeak.sub {d : ℕ} {φ : FormDu d → ℝ} {f f' : Lp ℂ 2 (wtMeasure φ)}
    {w w' : Lp (FormSpace d) 2 (wtMeasure φ)} (hw : DbarWeak φ f w) (hw' : DbarWeak φ f' w') :
    DbarWeak φ (f - f') (w - w') := by
  have h := (DbarWeak.add hw (DbarWeak.neg hw'))
  simpa only [sub_eq_add_neg] using h

/-- `DbarWeak φ 0 0`. -/
lemma DbarWeak.zero {d : ℕ} {φ : FormDu d → ℝ} :
    DbarWeak φ (0 : Lp ℂ 2 (wtMeasure φ)) (0 : Lp (FormSpace d) 2 (wtMeasure φ)) := by
  intro ψ h1 h2 hψ hθ
  rw [inner_zero_right, inner_zero_right]

end Weak

section Test

variable {d : ℕ}

/-- The `(0,1)`-test form `g dz̄_j`. -/
noncomputable def testForm (j : Fin d) (g : FormDu d → ℂ) : FormDu d → FormSpace d :=
  fun z => WithLp.toLp 2 (Pi.single j (g z))

@[simp] lemma toFormFun_testForm (j : Fin d) (g : FormDu d → ℂ) :
    toFormFun (testForm j g) = fun z => Pi.single j (g z) := rfl

lemma contDiff_testForm {j : Fin d} {g : FormDu d → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (testForm j g) := by
  rw [contDiff_piLp]
  intro i
  have h : (fun z => testForm j g z i)
      = fun z => (if i = j then (1 : ℂ) else 0) * g z := by
    funext z
    simp [testForm, Pi.single_apply]
  rw [h]
  exact contDiff_const.mul hg

lemma hasCompactSupport_testForm {j : Fin d} {g : FormDu d → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (testForm j g) := by
  refine hg.mono' ?_
  intro z hz
  by_contra hzc
  have hz0 : g z = 0 := image_eq_zero_of_notMem_tsupport hzc
  simp [testForm, hz0] at hz

lemma hasCompactSupport_toFormFun {ψ : FormDu d → FormSpace d} (h : HasCompactSupport ψ) :
    HasCompactSupport (toFormFun ψ) := by
  have hc : toFormFun ψ = fun z => (ψ z).ofLp := rfl
  rw [hc]
  refine h.mono' ?_
  intro z hz
  by_contra hzc
  have hz0 : ψ z = 0 := image_eq_zero_of_notMem_tsupport hzc
  simp [hz0] at hz

lemma contDiff_toFormFun {ψ : FormDu d → FormSpace d} (h : ContDiff ℝ ∞ ψ) :
    ∀ i, ContDiff ℝ ∞ (fun z => toFormFun ψ z i) := by
  rw [contDiff_piLp] at h
  intro i
  have hiff : (fun z => toFormFun ψ z i) = fun z => ψ z i := by
    funext z; rfl
  rw [hiff]
  exact h i

end Test

section AdjointLemmas

variable {d : ℕ}

lemma continuous_dbarAdjoint {φ : FormDu d → ℝ} {u : FormDu d → (Fin d → ℂ)}
    (hu : ∀ j, ContDiff ℝ 1 (fun z => u z j))
    (hφ : ContDiff ℝ 1 fun z => ((φ z : ℝ) : ℂ)) :
    Continuous (dbarAdjoint φ u) := by
  have h : dbarAdjoint φ u = fun z => -(∑ j, (partialZ j (fun w => u w j) z
      - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)) := rfl
  rw [h]
  refine Continuous.neg (continuous_finset_sum _ (fun j _ => ?_))
  exact (continuous_partialZ (hu j) j).sub ((hu j).continuous.mul (continuous_partialZ hφ j))

lemma hasCompactSupport_comp {u : FormDu d → (Fin d → ℂ)} (j : Fin d)
    (hs : HasCompactSupport u) : HasCompactSupport (fun z => u z j) := by
  have := hs.comp_left (g := fun v : Fin d → ℂ => v j) (by simp)
  simpa only [Function.comp_def] using this

lemma hasCompactSupport_dbarAdjoint {φ : FormDu d → ℝ} {u : FormDu d → (Fin d → ℂ)}
    (hs : HasCompactSupport u) : HasCompactSupport (dbarAdjoint φ u) := by
  have h1 : ∀ j, HasCompactSupport (fun z => u z j) := fun j => hasCompactSupport_comp j hs
  have h2 : ∀ j, HasCompactSupport (partialZ j (fun z => u z j)) := by
    intro j
    refine (h1 j).mono' ?_
    intro z hz
    by_contra hzc
    have hd : fderiv ℝ (fun w => u w j) z = 0 := (HasFDerivAt.of_notMem_tsupport ℝ hzc).fderiv
    simp [partialZ, hd] at hz
  have h3 : HasCompactSupport (∑ j : Fin d, fun z => (partialZ j (fun w => u w j) z
      - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)) :=
    HasCompactSupport.finset_sum (fun j _ => (h2 j).sub ((h1 j).mul_right (f' := fun z =>
      partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)))
  have h4 : dbarAdjoint φ u = -(∑ j : Fin d, fun z => (partialZ j (fun w => u w j) z
      - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)) := by
    funext z
    simp only [dbarAdjoint, Pi.neg_apply, Finset.sum_apply]
  rw [h4]
  exact h3.neg

/-- The formal adjoint of `∂̄` of a smooth compactly supported `(0,1)`-form is `L²` for the
weighted measure `μ_φ`. -/
lemma memLp_dbarAdjoint {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {u : FormDu d → (Fin d → ℂ)} (hu : ∀ j, ContDiff ℝ 1 (fun z => u z j))
    (hs : HasCompactSupport u) :
    MemLp (dbarAdjoint φ u) 2 (wtMeasure φ) := by
  have hφ1 : ContDiff ℝ 1 fun z => ((φ z : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp hφ
  haveI : IsFiniteMeasureOnCompacts (wtMeasure φ) :=
    isFiniteMeasureOnCompacts_wtMeasure hφ.continuous
  exact (continuous_dbarAdjoint hu hφ1).memLp_of_hasCompactSupport
    (hasCompactSupport_dbarAdjoint hs)

end AdjointLemmas

section Injectivity

variable {d : ℕ}

/-- A weak `∂̄`-closed element with `f = 0` vanishes: the weak `∂̄`-operator is injective. -/
theorem dbarWeak_eq_zero {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {u : Lp (FormSpace d) 2 (wtMeasure φ)} (hw : DbarWeak φ 0 u) : u = 0 := by
  haveI hlf : IsLocallyFiniteMeasure (wtMeasure φ) := isLocallyFiniteMeasure_wtMeasure hφ.continuous
  haveI hfc : IsFiniteMeasureOnCompacts (wtMeasure φ) :=
    isFiniteMeasureOnCompacts_wtMeasure hφ.continuous
  have key : ∀ j : Fin d, (fun z => u z j) =ᵐ[wtMeasure φ] 0 := by
    intro j
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ ?_
    · exact (memLp_eval_comp u j).locallyIntegrable (by norm_num)
    · intro g hg hgs
      set ψ : FormDu d → FormSpace d := testForm j (fun z => ((g z : ℝ) : ℂ)) with hψdef
      have h1 : ContDiff ℝ ∞ ψ :=
        contDiff_testForm (Complex.ofRealCLM.contDiff.comp hg)
      have h2 : HasCompactSupport ψ :=
        hasCompactSupport_testForm (hgs.comp_left (g := fun x : ℝ => ((x : ℝ) : ℂ)) (by simp))
      have hmem : MemLp ψ 2 (wtMeasure φ) :=
        memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous h1 h2
      have hcsf : HasCompactSupport (toFormFun ψ) := hasCompactSupport_toFormFun h2
      have hmemθ : MemLp (dbarAdjoint φ (toFormFun ψ)) 2 (wtMeasure φ) :=
        memLp_dbarAdjoint hφ (fun i => (contDiff_toFormFun h1 i).of_le (by simp)) hcsf
      have hrel := hw ψ h1 h2 hmem hmemθ
      rw [inner_zero_right, MeasureTheory.L2.inner_def] at hrel
      have hinner : ∀ z, inner ℂ (ψ z) (u z) = g z • (u z j) := by
        intro z
        rw [PiLp.inner_apply]
        rw [Finset.sum_eq_single j]
        · simp only [hψdef, testForm, WithLp.ofLp_toLp, Pi.single_eq_same]
          rw [RCLike.inner_apply, Complex.conj_ofReal, Complex.real_smul, mul_comm]
        · intro i _ hi
          simp only [hψdef, testForm, WithLp.ofLp_toLp, Pi.single_eq_of_ne hi, inner_zero_left]
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      have hae1 : (fun z => inner ℂ ((hmem.toLp ψ) z) ((u : FormDu d → FormSpace d) z))
          =ᵐ[wtMeasure φ] (fun z => inner ℂ (ψ z) ((u : FormDu d → FormSpace d) z)) := by
        filter_upwards [MemLp.coeFn_toLp hmem] with z hz
        rw [hz]
      have hEq : (∫ z, inner ℂ ((hmem.toLp ψ) z) (u z) ∂(wtMeasure φ))
          = ∫ z, g z • (u z j) ∂(wtMeasure φ) :=
        (integral_congr_ae hae1).trans
          (integral_congr_ae (μ := wtMeasure φ)
            (f := fun z => inner ℂ (ψ z) ((u : FormDu d → FormSpace d) z))
            (g := fun z => g z • ((u : FormDu d → FormSpace d) z j))
            (Eventually.of_forall hinner))
      rw [← hEq]; exact hrel
  have hall : ∀ᵐ z ∂(wtMeasure φ), ∀ j : Fin d, u z j = 0 :=
    Filter.eventually_all.mpr key
  rw [Lp.ext_iff]
  filter_upwards [hall, Lp.coeFn_zero (FormSpace d) 2 (wtMeasure φ)] with z hz hz0
  refine PiLp.ext (fun i => ?_)
  rw [hz i, hz0]
  rfl

/-- The weak `∂̄`-relation is single-valued: at most one `w` corresponds to a given `f`. -/
theorem dbarWeak_unique {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {f : Lp ℂ 2 (wtMeasure φ)} {w w' : Lp (FormSpace d) 2 (wtMeasure φ)}
    (hw : DbarWeak φ f w) (hw' : DbarWeak φ f w') : w = w' := by
  have h : DbarWeak φ 0 (w - w') := by
    have h2 := DbarWeak.add hw (DbarWeak.smul (-1 : ℂ) hw')
    rw [neg_one_smul, neg_one_smul, add_neg_cancel, ← sub_eq_add_neg] at h2
    exact h2
  exact sub_eq_zero.mp (dbarWeak_eq_zero hφ h)

end Injectivity

section Graph

variable {d : ℕ}

/-- The graph of the weak `∂̄`-relation, as a `ℂ`-submodule of `H1 × H2`. -/
def dbarGraph (φ : FormDu d → ℝ) :
    Submodule ℂ (Lp ℂ 2 (wtMeasure φ) × Lp (FormSpace d) 2 (wtMeasure φ)) where
  carrier := {p | DbarWeak φ p.1 p.2}
  zero_mem' := DbarWeak.zero
  add_mem' hp hq := DbarWeak.add hp hq
  smul_mem' c _ hp := DbarWeak.smul c hp

@[simp] lemma mem_dbarGraph {φ : FormDu d → ℝ}
    {p : Lp ℂ 2 (wtMeasure φ) × Lp (FormSpace d) 2 (wtMeasure φ)} :
    p ∈ dbarGraph φ ↔ DbarWeak φ p.1 p.2 := Iff.rfl

variable (φ : FormDu d → ℝ)

/-- The graph is closed: being in it is an intersection of equations
`⟪ψ, w⟫ = ⟪ϑ_φψ, f⟫` in the continuous functionals `⟪ψ, ·⟫` and `⟪·, ϑ_φψ⟫`. -/
theorem isClosed_dbarGraph :
    IsClosed (dbarGraph φ : Set (Lp ℂ 2 (wtMeasure φ) × Lp (FormSpace d) 2 (wtMeasure φ))) := by
  have hset : (dbarGraph φ : Set (Lp ℂ 2 (wtMeasure φ) × Lp (FormSpace d) 2 (wtMeasure φ)))
      = ⋂ (ψ : FormDu d → FormSpace d) (h1 : ContDiff ℝ ∞ ψ) (h2 : HasCompactSupport ψ)
          (hψ : MemLp ψ 2 (wtMeasure φ))
          (hθ : MemLp (dbarAdjoint φ (toFormFun ψ)) 2 (wtMeasure φ)),
        {p | inner ℂ (hψ.toLp ψ) p.2
              = inner ℂ (hθ.toLp (dbarAdjoint φ (toFormFun ψ))) p.1} := by
    ext p
    simp only [mem_dbarGraph, Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun h ψ h1 h2 hψ hθ => h ψ h1 h2 hψ hθ,
      fun h ψ h1 h2 hψ hθ => h ψ h1 h2 hψ hθ⟩
  rw [hset]
  refine isClosed_iInter fun ψ => isClosed_iInter fun h1 => isClosed_iInter fun h2 =>
    isClosed_iInter fun hψ => isClosed_iInter fun hθ => ?_
  exact isClosed_eq (Continuous.inner continuous_const continuous_snd)
    (Continuous.inner continuous_const continuous_fst)

variable {φ}

/-- **The weak `∂̄`-operator.** -/
noncomputable def dbarOp (φ : FormDu d → ℝ) :
    (Lp ℂ 2 (wtMeasure φ)) →ₗ.[ℂ] (Lp (FormSpace d) 2 (wtMeasure φ)) :=
  (dbarGraph φ).toLinearPMap

/-- The graph of `dbarOp φ` is `dbarGraph φ` (for a `C¹` weight, so that the relation is
single-valued). -/
theorem dbarOp_graph (hφ : ContDiff ℝ 1 φ) : (dbarOp φ).graph = dbarGraph φ := by
  show (dbarGraph φ).toLinearPMap.graph = dbarGraph φ
  exact Submodule.toLinearPMap_graph_eq _
    (fun x hx hx1 => dbarWeak_eq_zero hφ
      (by rw [mem_dbarGraph] at hx; rw [hx1] at hx; exact hx))

/-- `dbarOp φ` is closed. -/
theorem isClosed_dbarOp (hφ : ContDiff ℝ 1 φ) : (dbarOp φ).IsClosed := by
  show IsClosed ((dbarOp φ).graph : Set (Lp ℂ 2 (wtMeasure φ) × Lp (FormSpace d) 2 (wtMeasure φ)))
  rw [dbarOp_graph hφ]
  exact isClosed_dbarGraph φ

/-- Membership in the domain of `dbarOp φ`, in terms of the weak relation. -/
theorem mem_dbarOp_domain {f : Lp ℂ 2 (wtMeasure φ)} :
    f ∈ (dbarOp φ).domain ↔ ∃ w, DbarWeak φ f w := by
  rw [dbarOp, Submodule.toLinearPMap_domain, Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, hp1⟩
    exact ⟨p.2, hp1 ▸ hp⟩
  · rintro ⟨w, hw⟩
    exact ⟨(f, w), hw, rfl⟩

/-- The value of `dbarOp φ` at `f` is the (unique) `w` with `DbarWeak φ f w`. -/
theorem dbarOp_apply_eq {hφ : ContDiff ℝ 1 φ} {f : Lp ℂ 2 (wtMeasure φ)}
    (hf : f ∈ (dbarOp φ).domain) {w : Lp (FormSpace d) 2 (wtMeasure φ)}
    (hw : DbarWeak φ f w) : dbarOp φ ⟨f, hf⟩ = w := by
  have hmem : DbarWeak φ f (dbarOp φ ⟨f, hf⟩) := by
    have h := LinearPMap.mem_graph (dbarOp φ) ⟨f, hf⟩
    rw [dbarOp_graph hφ, mem_dbarGraph] at h
    exact h
  exact dbarWeak_unique hφ hmem hw

end Graph

end Submission.FUP
