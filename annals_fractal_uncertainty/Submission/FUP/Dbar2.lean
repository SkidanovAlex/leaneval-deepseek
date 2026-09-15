import Submission.FUP.DbarSmooth
import Mathlib.Analysis.Calculus.ContDiff.WithLp

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The weak `(0,1) → (0,2)` operator

The Kohn–Morrey estimate `∫ κ |x|² e^{-φ} ≤ ‖∂̄x‖² + ‖ϑ_φ x‖²` is stated for `(0,1)`-forms.  In
order to use the abstract existence theorem
`Commons.Analysis.InnerProductSpace.LinearPMap.exists_solution_of_bound` one needs *two* operators
`T : H1 → H2` (the weak `∂̄` on functions) and `S : H2 → H3` (the weak `∂̄` on `(0,1)`-forms),
so that the "domain of the adjoint" is small enough for the a priori estimate to have content.

This module provides `S`: the weak `∂̄` from `(0,1)`-forms to `(0,2)`-forms.

Conventions: a `(0,2)`-form is a function `ℂᵈ → Fin d × Fin d → ℂ`, made into a Hilbert space by
`FormSpace2 d := EuclideanSpace ℂ (Fin d × Fin d)`.  The formal adjoint
`ϑ₂ : (0,2)-forms → (0,1)-forms` of `∂̄₂` is

  `(ϑ₂Ψ)_j = -∑_k (∂_k Δ_{jk} - Δ_{jk} ∂_kφ)`,  `Δ_{jk} = Ψ_{jk} - Ψ_{kj}`,

and the key algebraic fact `ϑ₁ ϑ₂ = 0` (proved by a pointwise antisymmetry/Clairaut computation)
is what makes the range of `∂̄₁` lie in the kernel of `∂̄₂`.
-/

namespace Submission.FUP

variable {d : ℕ}

/-- The Hilbert space of `(0,2)`-forms. -/
abbrev FormSpace2 (d : ℕ) := EuclideanSpace ℂ (Fin d × Fin d)

/-- Forget the `ℓ²` structure of a `(0,2)`-form. -/
noncomputable def toFormFun2 (Ψ : FormDu d → FormSpace2 d) : FormDu d → (Fin d × Fin d → ℂ) :=
  fun z => (WithLp.equiv 2 (Fin d × Fin d → ℂ)) (Ψ z)

@[simp] lemma toFormFun2_apply (Ψ : FormDu d → FormSpace2 d) (z : FormDu d) :
    toFormFun2 Ψ z = (WithLp.equiv 2 (Fin d × Fin d → ℂ)) (Ψ z) := rfl

/-- Put a `(0,1)`-form given as a plain function into `FormSpace d`. -/
noncomputable def liftForm (u : FormDu d → (Fin d → ℂ)) : FormDu d → FormSpace d :=
  fun z => WithLp.toLp 2 (u z)

@[simp] lemma toFormFun_liftForm (u : FormDu d → (Fin d → ℂ)) :
    toFormFun (liftForm u) = u := rfl

/-- Put a `(0,2)`-form given as a plain function into `FormSpace2 d`. -/
noncomputable def liftForm2 (Ψ : FormDu d → (Fin d × Fin d → ℂ)) : FormDu d → FormSpace2 d :=
  fun z => WithLp.toLp 2 (Ψ z)

@[simp] lemma toFormFun2_liftForm2 (Ψ : FormDu d → (Fin d × Fin d → ℂ)) :
    toFormFun2 (liftForm2 Ψ) = Ψ := rfl

section Adjoint2

/-- The formal adjoint `ϑ₂` of the `(0,1) → (0,2)` operator `∂̄₂` with respect to the weight
`e^{-φ}`:
`(ϑ₂Ψ)_j = -∑_k (∂_k(Ψ_{jk} - Ψ_{kj}) - (Ψ_{jk} - Ψ_{kj}) ∂_kφ)`. -/
noncomputable def dbarAdjoint2 (φ : FormDu d → ℝ)
    (Ψ : FormDu d → (Fin d × Fin d → ℂ)) : FormDu d → (Fin d → ℂ) :=
  fun z j => -∑ k : Fin d,
    (partialZ k (fun w => Ψ w (j, k) - Ψ w (k, j)) z
      - (Ψ z (j, k) - Ψ z (k, j)) * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z)

lemma continuous_dbarAdjoint2 {φ : FormDu d → ℝ} {Ψ : FormDu d → (Fin d × Fin d → ℂ)}
    (hΨ : ∀ i, ContDiff ℝ 1 (fun z => Ψ z i))
    (hφ : ContDiff ℝ 1 fun z => ((φ z : ℝ) : ℂ)) :
    Continuous (dbarAdjoint2 φ Ψ) := by
  have h : dbarAdjoint2 φ Ψ = fun z j => -∑ k : Fin d,
      (partialZ k (fun w => Ψ w (j, k) - Ψ w (k, j)) z
        - (Ψ z (j, k) - Ψ z (k, j)) * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z) := rfl
  rw [h]
  refine continuous_pi (fun j => ?_)
  refine Continuous.neg (continuous_finset_sum _ (fun k _ => ?_))
  have hΔ : ContDiff ℝ 1 (fun z => Ψ z (j, k) - Ψ z (k, j)) :=
    (hΨ (j, k)).sub (hΨ (k, j))
  exact (continuous_partialZ hΔ k).sub (hΔ.continuous.mul (continuous_partialZ hφ k))

end Adjoint2


section Lift

variable {d : ℕ}

lemma contDiff_liftForm {n : WithTop ℕ∞} {u : FormDu d → (Fin d → ℂ)}
    (hu : ∀ j, ContDiff ℝ n (fun z => u z j)) : ContDiff ℝ n (liftForm u) := by
  rw [contDiff_piLp]
  intro j
  have h : (fun z => liftForm u z j) = fun z => u z j := by funext z; rfl
  rw [h]; exact hu j

lemma hasCompactSupport_liftForm {u : FormDu d → (Fin d → ℂ)} (hu : HasCompactSupport u) :
    HasCompactSupport (liftForm u) := by
  refine hu.mono' ?_
  intro z hz
  by_contra hzc
  have hz0 : u z = 0 := image_eq_zero_of_notMem_tsupport hzc
  exact hz (by simp [liftForm, hz0])

lemma contDiff_liftForm2 {n : WithTop ℕ∞} {Ψ : FormDu d → (Fin d × Fin d → ℂ)}
    (hΨ : ∀ i, ContDiff ℝ n (fun z => Ψ z i)) : ContDiff ℝ n (liftForm2 Ψ) := by
  rw [contDiff_piLp]
  intro i
  have h : (fun z => liftForm2 Ψ z i) = fun z => Ψ z i := by funext z; rfl
  rw [h]; exact hΨ i

lemma hasCompactSupport_liftForm2 {Ψ : FormDu d → (Fin d × Fin d → ℂ)}
    (hΨ : HasCompactSupport Ψ) : HasCompactSupport (liftForm2 Ψ) := by
  refine hΨ.mono' ?_
  intro z hz
  by_contra hzc
  have hz0 : Ψ z = 0 := image_eq_zero_of_notMem_tsupport hzc
  exact hz (by simp [liftForm2, hz0])

lemma contDiff_toFormFun2 {Ψ : FormDu d → FormSpace2 d} (h : ContDiff ℝ ∞ Ψ) :
    ∀ i, ContDiff ℝ ∞ (fun z => toFormFun2 Ψ z i) := by
  rw [contDiff_piLp] at h
  intro i
  have hiff : (fun z => toFormFun2 Ψ z i) = fun z => Ψ z i := by funext z; rfl
  rw [hiff]; exact h i

lemma hasCompactSupport_toFormFun2 {Ψ : FormDu d → FormSpace2 d} (h : HasCompactSupport Ψ) :
    HasCompactSupport (toFormFun2 Ψ) := by
  have hc : toFormFun2 Ψ = fun z => (Ψ z).ofLp := rfl
  rw [hc]
  refine h.mono' ?_
  intro z hz
  by_contra hzc
  have hz0 : Ψ z = 0 := image_eq_zero_of_notMem_tsupport hzc
  simp [hz0] at hz

end Lift

section Adjoint2c

variable {d : ℕ}

lemma tsupport_comp_subset {Ψ : FormDu d → (Fin d × Fin d → ℂ)} (i : Fin d × Fin d) :
    tsupport (fun z => Ψ z i) ⊆ tsupport Ψ :=
  closure_mono fun z hz h => hz (congrArg (fun F : Fin d × Fin d → ℂ => F i) h)

lemma hasCompactSupport_comp2 {Ψ : FormDu d → (Fin d × Fin d → ℂ)} (i : Fin d × Fin d)
    (hs : HasCompactSupport Ψ) : HasCompactSupport (fun z => Ψ z i) := by
  have h := hs.comp_left (g := fun v : Fin d × Fin d → ℂ => v i) (by simp)
  simpa only [Function.comp_def] using h

/-- The `ℓ²`-structure on `FormSpace d` is compatible with the product structure: a function into
`FormSpace d` is continuous iff all of its components are. -/
lemma continuous_liftForm {u : FormDu d → (Fin d → ℂ)} (hu : Continuous u) :
    Continuous (liftForm u) := by
  have h : ContDiff ℝ 0 (liftForm u) := (contDiff_piLp (𝕜 := ℝ) (p := 2)).mpr fun j =>
    contDiff_zero.mpr (continuous_pi_iff.mp hu j)
  exact (contDiff_zero (𝕜 := ℝ) (f := liftForm u)).mp h

lemma hasCompactSupport_dbarAdjoint2 {φ : FormDu d → ℝ} {Ψ : FormDu d → (Fin d × Fin d → ℂ)}
    (hs : HasCompactSupport Ψ) : HasCompactSupport (dbarAdjoint2 φ Ψ) := by
  refine hs.mono' ?_
  intro z hz
  by_contra hzc
  have hΨz : Ψ z = 0 := image_eq_zero_of_notMem_tsupport hzc
  have h : dbarAdjoint2 φ Ψ z = 0 := by
    funext j
    show -∑ k : Fin d, _ = (0 : ℂ)
    rw [neg_eq_zero]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hsupp : Function.support (fun w => Ψ w (j, k) - Ψ w (k, j))
        ⊆ Function.support Ψ := by
      intro w hw
      simp only [Function.mem_support] at hw ⊢
      intro hΨw
      exact hw (by simp [hΨw])
    have hd : fderiv ℝ (fun w => Ψ w (j, k) - Ψ w (k, j)) z = 0 :=
      fderiv_of_notMem_tsupport ℝ (fun hh => hzc (closure_mono hsupp hh))
    have h1 : partialZ k (fun w => Ψ w (j, k) - Ψ w (k, j)) z = 0 := by simp [partialZ, hd]
    have h2 : Ψ z (j, k) - Ψ z (k, j) = 0 := by rw [hΨz]; simp
    rw [h1, h2, zero_mul, sub_zero]
  exact hz h

/-- The formal adjoint of `∂̄₂` of a smooth compactly supported `(0,2)`-form is `L²(μ_φ)`. -/
lemma memLp_dbarAdjoint2 {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {Ψ : FormDu d → (Fin d × Fin d → ℂ)} (hΨ : ∀ i, ContDiff ℝ 1 (fun z => Ψ z i))
    (hs : HasCompactSupport Ψ) :
    MemLp (liftForm (dbarAdjoint2 φ Ψ)) 2 (wtMeasure φ) := by
  have hφ1 : ContDiff ℝ 1 fun z => ((φ z : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp hφ
  have hc : Continuous (dbarAdjoint2 φ Ψ) := continuous_dbarAdjoint2 hΨ hφ1
  have hcomp : HasCompactSupport (dbarAdjoint2 φ Ψ) := hasCompactSupport_dbarAdjoint2 hs
  haveI : IsFiniteMeasureOnCompacts (wtMeasure φ) :=
    isFiniteMeasureOnCompacts_wtMeasure hφ.continuous
  exact (continuous_liftForm hc).memLp_of_hasCompactSupport (hasCompactSupport_liftForm hcomp)

end Adjoint2c



section Weak2

variable {d : ℕ}

/-- **The weak `∂̄` relation for `(0,1) → (0,2)` forms**: `ζ = ∂̄₂ w` in the sense of
distributions for the weight `e^{-φ}dvol`. -/
def DbarWeak2 (φ : FormDu d → ℝ) (w : Lp (FormSpace d) 2 (wtMeasure φ))
    (ζ : Lp (FormSpace2 d) 2 (wtMeasure φ)) : Prop :=
  ∀ (Ψ : FormDu d → FormSpace2 d) (h1 : ContDiff ℝ ∞ Ψ) (h2 : HasCompactSupport Ψ)
    (hΨ : MemLp Ψ 2 (wtMeasure φ))
    (hθ : MemLp (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ))) 2 (wtMeasure φ)),
    inner ℂ (hΨ.toLp Ψ) ζ
      = inner ℂ (hθ.toLp (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ)))) w

lemma DbarWeak2.add {φ : FormDu d → ℝ} {w w' : Lp (FormSpace d) 2 (wtMeasure φ)}
    {ζ ζ' : Lp (FormSpace2 d) 2 (wtMeasure φ)} (hw : DbarWeak2 φ w ζ)
    (hw' : DbarWeak2 φ w' ζ') : DbarWeak2 φ (w + w') (ζ + ζ') := by
  intro Ψ h1 h2 hΨ hθ
  rw [inner_add_right, inner_add_right, hw Ψ h1 h2 hΨ hθ, hw' Ψ h1 h2 hΨ hθ]

lemma DbarWeak2.smul {φ : FormDu d → ℝ} (c : ℂ) {w : Lp (FormSpace d) 2 (wtMeasure φ)}
    {ζ : Lp (FormSpace2 d) 2 (wtMeasure φ)} (hw : DbarWeak2 φ w ζ) :
    DbarWeak2 φ (c • w) (c • ζ) := by
  intro Ψ h1 h2 hΨ hθ
  rw [inner_smul_right, inner_smul_right, hw Ψ h1 h2 hΨ hθ]

lemma DbarWeak2.zero {φ : FormDu d → ℝ} :
    DbarWeak2 φ (0 : Lp (FormSpace d) 2 (wtMeasure φ))
      (0 : Lp (FormSpace2 d) 2 (wtMeasure φ)) := by
  intro Ψ h1 h2 hΨ hθ
  rw [inner_zero_right, inner_zero_right]

/-- The `(0,2)`-test form `g dz̄_i` (with `i : Fin d × Fin d`). -/
noncomputable def testForm2 (i : Fin d × Fin d) (g : FormDu d → ℂ) : FormDu d → FormSpace2 d :=
  fun z => WithLp.toLp 2 (Pi.single i (g z))

@[simp] lemma toFormFun2_testForm2 (i : Fin d × Fin d) (g : FormDu d → ℂ) :
    toFormFun2 (testForm2 i g) = fun z => Pi.single i (g z) := rfl

lemma contDiff_testForm2 {i : Fin d × Fin d} {g : FormDu d → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (testForm2 i g) := by
  rw [contDiff_piLp]
  intro l
  have h : (fun z => testForm2 i g z l)
      = fun z => (if l = i then (1 : ℂ) else 0) * g z := by
    funext z
    simp [testForm2, Pi.single_apply]
  rw [h]
  exact contDiff_const.mul hg

lemma hasCompactSupport_testForm2 {i : Fin d × Fin d} {g : FormDu d → ℂ}
    (hg : HasCompactSupport g) : HasCompactSupport (testForm2 i g) := by
  refine hg.mono' ?_
  intro z hz
  by_contra hzc
  have hz0 : g z = 0 := image_eq_zero_of_notMem_tsupport hzc
  simp [testForm2, hz0] at hz

lemma contDiff_toFormFun2' {n : WithTop ℕ∞} {Ψ : FormDu d → FormSpace2 d}
    (h : ContDiff ℝ n Ψ) : ∀ i, ContDiff ℝ n (fun z => toFormFun2 Ψ z i) := by
  rw [contDiff_piLp] at h
  intro i
  have hiff : (fun z => toFormFun2 Ψ z i) = fun z => Ψ z i := by funext z; rfl
  rw [hiff]; exact h i

lemma memLp_eval_comp2 {φ : FormDu d → ℝ} (u : Lp (FormSpace2 d) 2 (wtMeasure φ))
    (i : Fin d × Fin d) :
    MemLp (fun z => (u : FormDu d → FormSpace2 d) z i) 2 (wtMeasure φ) := by
  have h : AEMeasurable (fun z : FormDu d => (u : FormDu d → FormSpace2 d) z) (wtMeasure φ) :=
    AEStronglyMeasurable.aemeasurable (Lp.memLp u).1
  have hc : AEMeasurable (fun z : FormDu d => (u : FormDu d → FormSpace2 d) z i) (wtMeasure φ) :=
    AEMeasurable.comp_aemeasurable (g := fun x : FormSpace2 d => x i) (by fun_prop) h
  refine MemLp.mono' (Lp.memLp u).norm hc.aestronglyMeasurable ?_
  filter_upwards with z
  exact PiLp.norm_apply_le ((u : FormDu d → FormSpace2 d) z) i

end Weak2

section Inject2

variable {d : ℕ} {φ0 : FormDu d → ℝ}

theorem dbarWeak2_eq_zero {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {ζ : Lp (FormSpace2 d) 2 (wtMeasure φ)} (hw : DbarWeak2 φ 0 ζ) : ζ = 0 := by
  haveI hlf : IsLocallyFiniteMeasure (wtMeasure φ) := isLocallyFiniteMeasure_wtMeasure hφ.continuous
  haveI hfc : IsFiniteMeasureOnCompacts (wtMeasure φ) :=
    isFiniteMeasureOnCompacts_wtMeasure hφ.continuous
  have key : ∀ i : Fin d × Fin d, (fun z => ζ z i) =ᵐ[wtMeasure φ] 0 := by
    intro i
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ ?_
    · exact (memLp_eval_comp2 ζ i).locallyIntegrable (by norm_num)
    · intro g hg hgs
      set Ψ : FormDu d → FormSpace2 d := testForm2 i (fun z => ((g z : ℝ) : ℂ)) with hΨdef
      have h1 : ContDiff ℝ ∞ Ψ :=
        contDiff_testForm2 (Complex.ofRealCLM.contDiff.comp hg)
      have h2 : HasCompactSupport Ψ :=
        hasCompactSupport_testForm2 (hgs.comp_left (g := fun x : ℝ => ((x : ℝ) : ℂ)) (by simp))
      have hmem : MemLp Ψ 2 (wtMeasure φ) :=
        memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous h1 h2
      have hcsf : HasCompactSupport (toFormFun2 Ψ) := hasCompactSupport_toFormFun2 h2
      have hmemθ : MemLp (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ))) 2 (wtMeasure φ) :=
        memLp_dbarAdjoint2 hφ (fun i => (contDiff_toFormFun2' h1 i).of_le (by simp)) hcsf
      have hrel := hw Ψ h1 h2 hmem hmemθ
      rw [inner_zero_right, MeasureTheory.L2.inner_def] at hrel
      have hinner : ∀ z, inner ℂ (Ψ z) (ζ z) = g z • (ζ z i) := by
        intro z
        rw [PiLp.inner_apply]
        rw [Finset.sum_eq_single i]
        · simp only [hΨdef, testForm2, WithLp.ofLp_toLp, Pi.single_eq_same]
          rw [RCLike.inner_apply, Complex.conj_ofReal, Complex.real_smul, mul_comm]
        · intro l _ hl
          simp only [hΨdef, testForm2, WithLp.ofLp_toLp, Pi.single_eq_of_ne hl, inner_zero_left]
        · intro hl
          exact absurd (Finset.mem_univ i) hl
      have hae1 : (fun z => inner ℂ ((hmem.toLp Ψ) z) ((ζ : FormDu d → FormSpace2 d) z))
          =ᵐ[wtMeasure φ] (fun z => inner ℂ (Ψ z) ((ζ : FormDu d → FormSpace2 d) z)) := by
        filter_upwards [MemLp.coeFn_toLp hmem] with z hz
        rw [hz]
      have hEq : (∫ z, inner ℂ ((hmem.toLp Ψ) z) (ζ z) ∂(wtMeasure φ))
          = ∫ z, g z • (ζ z i) ∂(wtMeasure φ) :=
        (integral_congr_ae hae1).trans
          (integral_congr_ae (μ := wtMeasure φ)
            (f := fun z => inner ℂ (Ψ z) ((ζ : FormDu d → FormSpace2 d) z))
            (g := fun z => g z • ((ζ : FormDu d → FormSpace2 d) z i))
            (Eventually.of_forall hinner))
      rw [← hEq]; exact hrel
  have hall : ∀ᵐ z ∂(wtMeasure φ), ∀ i : Fin d × Fin d, ζ z i = 0 :=
    Filter.eventually_all.mpr key
  rw [Lp.ext_iff]
  filter_upwards [hall, Lp.coeFn_zero (FormSpace2 d) 2 (wtMeasure φ)] with z hz hz0
  refine PiLp.ext (fun i => ?_)
  rw [hz i, hz0]
  rfl


/-- The weak `(0,2)`-relation is single-valued. -/
theorem dbarWeak2_unique {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {w : Lp (FormSpace d) 2 (wtMeasure φ)} {ζ ζ' : Lp (FormSpace2 d) 2 (wtMeasure φ)}
    (hw : DbarWeak2 φ w ζ) (hw' : DbarWeak2 φ w ζ') : ζ = ζ' := by
  have h : DbarWeak2 φ 0 (ζ - ζ') := by
    have h2 := DbarWeak2.add hw (DbarWeak2.smul (-1 : ℂ) hw')
    rw [neg_one_smul, neg_one_smul, add_neg_cancel, ← sub_eq_add_neg] at h2
    exact h2
  exact sub_eq_zero.mp (dbarWeak2_eq_zero hφ h)

end Inject2



section Graph2

variable {d : ℕ}

/-- The graph of the weak `(0,1) → (0,2)` operator, as a `ℂ`-submodule of `H2 × H3`. -/
def dbarGraph2 (φ : FormDu d → ℝ) :
    Submodule ℂ (Lp (FormSpace d) 2 (wtMeasure φ) × Lp (FormSpace2 d) 2 (wtMeasure φ)) where
  carrier := {p | DbarWeak2 φ p.1 p.2}
  zero_mem' := DbarWeak2.zero
  add_mem' hp hq := DbarWeak2.add hp hq
  smul_mem' c _ hp := DbarWeak2.smul c hp

@[simp] lemma mem_dbarGraph2 {φ : FormDu d → ℝ}
    {p : Lp (FormSpace d) 2 (wtMeasure φ) × Lp (FormSpace2 d) 2 (wtMeasure φ)} :
    p ∈ dbarGraph2 φ ↔ DbarWeak2 φ p.1 p.2 := Iff.rfl

variable (φ : FormDu d → ℝ)

/-- The graph is closed. -/
theorem isClosed_dbarGraph2 :
    IsClosed (dbarGraph2 φ : Set (Lp (FormSpace d) 2 (wtMeasure φ)
      × Lp (FormSpace2 d) 2 (wtMeasure φ))) := by
  have hset : (dbarGraph2 φ : Set (Lp (FormSpace d) 2 (wtMeasure φ)
        × Lp (FormSpace2 d) 2 (wtMeasure φ)))
      = ⋂ (Ψ : FormDu d → FormSpace2 d) (h1 : ContDiff ℝ ∞ Ψ) (h2 : HasCompactSupport Ψ)
          (hΨ : MemLp Ψ 2 (wtMeasure φ))
          (hθ : MemLp (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ))) 2 (wtMeasure φ)),
        {p | inner ℂ (hΨ.toLp Ψ) p.2
              = inner ℂ (hθ.toLp (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ)))) p.1} := by
    ext p
    simp only [mem_dbarGraph2, Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun h Ψ h1 h2 hΨ hθ => h Ψ h1 h2 hΨ hθ,
      fun h Ψ h1 h2 hΨ hθ => h Ψ h1 h2 hΨ hθ⟩
  rw [hset]
  refine isClosed_iInter fun Ψ => isClosed_iInter fun h1 => isClosed_iInter fun h2 =>
    isClosed_iInter fun hΨ => isClosed_iInter fun hθ => ?_
  exact isClosed_eq (Continuous.inner continuous_const continuous_snd)
    (Continuous.inner continuous_const continuous_fst)

variable {φ}

/-- **The weak `(0,1) → (0,2)` operator.** -/
noncomputable def dbarOp2 (φ : FormDu d → ℝ) :
    (Lp (FormSpace d) 2 (wtMeasure φ)) →ₗ.[ℂ] (Lp (FormSpace2 d) 2 (wtMeasure φ)) :=
  (dbarGraph2 φ).toLinearPMap

theorem dbarOp2_graph (hφ : ContDiff ℝ 1 φ) : (dbarOp2 φ).graph = dbarGraph2 φ := by
  show (dbarGraph2 φ).toLinearPMap.graph = dbarGraph2 φ
  exact Submodule.toLinearPMap_graph_eq _
    (fun x hx hx1 => dbarWeak2_eq_zero hφ
      (by rw [mem_dbarGraph2] at hx; rw [hx1] at hx; exact hx))

/-- `dbarOp2 φ` is closed. -/
theorem isClosed_dbarOp2 (hφ : ContDiff ℝ 1 φ) : (dbarOp2 φ).IsClosed := by
  show IsClosed ((dbarOp2 φ).graph : Set (Lp (FormSpace d) 2 (wtMeasure φ)
    × Lp (FormSpace2 d) 2 (wtMeasure φ)))
  rw [dbarOp2_graph hφ]
  exact isClosed_dbarGraph2 φ

/-- Membership in the domain of `dbarOp2 φ`. -/
theorem mem_dbarOp2_domain {φ : FormDu d → ℝ} {w : Lp (FormSpace d) 2 (wtMeasure φ)} :
    w ∈ (dbarOp2 φ).domain ↔ ∃ ζ, DbarWeak2 φ w ζ := by
  rw [dbarOp2, Submodule.toLinearPMap_domain, Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, hp1⟩
    exact ⟨p.2, hp1 ▸ hp⟩
  · rintro ⟨ζ, hζ⟩
    exact ⟨(w, ζ), hζ, rfl⟩

/-- The value of `dbarOp2 φ` at `w`. -/
theorem dbarOp2_apply_eq {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {w : Lp (FormSpace d) 2 (wtMeasure φ)} (hw : w ∈ (dbarOp2 φ).domain)
    {ζ : Lp (FormSpace2 d) 2 (wtMeasure φ)} (hζ : DbarWeak2 φ w ζ) :
    dbarOp2 φ ⟨w, hw⟩ = ζ := by
  have hmem : DbarWeak2 φ w (dbarOp2 φ ⟨w, hw⟩) := by
    have h := LinearPMap.mem_graph (dbarOp2 φ) ⟨w, hw⟩
    rw [dbarOp2_graph hφ, mem_dbarGraph2] at h
    exact h
  exact dbarWeak2_unique hφ hmem hζ
end Graph2


end Submission.FUP
