import Mathlib
import Submission.Work.WilE7.Auxiliary.analyticLevelSetChart

set_option linter.style.haveILetI false

namespace Work.WilE7.Nondrop

open Set
open scoped Topology

theorem analyticLevelSetChartRange {n k : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ)) (p : Fin n → ℝ)
    (hg : ∀ q, AnalyticAt ℝ g q) (hsurj : (fderiv ℝ g p).range = ⊤) :
    ∃ (γ : (fderiv ℝ g p).ker → (Fin n → ℝ)) (V : Set (fderiv ℝ g p).ker)
      (U : Set (Fin n → ℝ)) (χ : (Fin n → ℝ) → (fderiv ℝ g p).ker),
      IsOpen V ∧ IsOpen U ∧ (0 : (fderiv ℝ g p).ker) ∈ V ∧ p ∈ U ∧ γ 0 = p ∧
      AnalyticAt ℝ γ 0 ∧ (∀ v ∈ V, γ v ∈ U) ∧ (∀ v ∈ V, g (γ v) = g p) ∧
      (∀ y ∈ U, g y = g p → ∃ v ∈ V, γ v = y) ∧ Set.InjOn γ V ∧
      (fderiv ℝ γ 0).range = (fderiv ℝ g p).ker ∧
      AnalyticAt ℝ χ p ∧ (∀ y ∈ U, g y = g p → χ y ∈ V ∧ γ (χ y) = y) := by
  let f' : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) := fderiv ℝ g p
  have hgp : HasStrictFDerivAt g f' p := (hg p).hasStrictFDerivAt
  have hker : f'.ker.ClosedComplemented :=
    f'.ker_closedComplemented_of_finiteDimensional_range
  haveI : CompleteSpace f'.ker := f'.isClosed_ker.completeSpace_coe
  let C : (Fin n → ℝ) →L[ℝ] f'.ker := Classical.choose hker
  have hC : ∀ x : f'.ker, C x = x := Classical.choose_spec hker
  let φ : ImplicitFunctionData ℝ (Fin n → ℝ) (Fin k → ℝ) f'.ker :=
    HasStrictFDerivAt.implicitFunctionDataOfComplemented g f' hgp hsurj hker
  have hleft : ∀ x, φ.leftFun x = g x := fun x => rfl
  have hright : ∀ x, φ.rightFun x = C (x - p) := fun x => rfl
  have hpt : φ.pt = p := rfl
  have hrightpt : φ.rightFun φ.pt = 0 := by rw [hright, hpt, sub_self, map_zero]
  let γ : f'.ker → (Fin n → ℝ) := φ.implicitFunction (φ.leftFun φ.pt)
  let χ : (Fin n → ℝ) → f'.ker := fun y => C (y - p)
  let V : Set f'.ker := {v | ((g p, v) : (Fin k → ℝ) × f'.ker) ∈ φ.toOpenPartialHomeomorph.target}
  let U : Set (Fin n → ℝ) := φ.toOpenPartialHomeomorph.source
  have hγapply : ∀ v, γ v = φ.toOpenPartialHomeomorph.symm (g p, v) := by
    intro v
    simp only [γ, ImplicitFunctionData.implicitFunction_apply, hpt, hleft]
  have hTarget : ((g p, (0 : f'.ker)) : (Fin k → ℝ) × f'.ker) ∈
      φ.toOpenPartialHomeomorph.target := by
    have h := φ.toOpenPartialHomeomorph.map_source (φ.pt_mem_toOpenPartialHomeomorph_source)
    simpa [ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright, hpt] using h
  have hpU : p ∈ U := by
    simpa [U, hpt] using φ.pt_mem_toOpenPartialHomeomorph_source
  have hpimg : φ.toOpenPartialHomeomorph p = ((g p, (0 : f'.ker)) : (Fin k → ℝ) × f'.ker) := by
    rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
    simp [hleft, hright, sub_self]
  have hγ0 : γ 0 = p := by
    rw [hγapply, ← hpimg]
    exact φ.toOpenPartialHomeomorph.left_inv (φ.pt_mem_toOpenPartialHomeomorph_source)
  -- the chart `x ↦ (g x, C (x - p))` is analytic at `p`, with invertible derivative
  have hC_an : AnalyticAt ℝ (fun x : Fin n → ℝ => C (x - p)) p := by
    have h3 := (C.analyticAt p).sub (analyticAt_const (v := C p) (x := p))
    have heq : (⇑C) - (fun _ : Fin n → ℝ => C p) = (fun x : Fin n → ℝ => C (x - p)) := by
      funext x; simp
    rwa [heq] at h3
  have hΦ : AnalyticAt ℝ φ.prodFun p := by
    have h := (hg p).prod hC_an
    have heq : φ.prodFun = (fun x : Fin n → ℝ => (g x, C (x - p))) := by
      funext x
      rw [ImplicitFunctionData.prodFun_apply, hleft, hright]
    rw [heq]
    exact h
  let e : (Fin n → ℝ) ≃L[ℝ] (Fin k → ℝ) × f'.ker :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.range_leftDeriv
      φ.range_rightDeriv φ.isCompl_ker
  have hfderiv : fderiv ℝ φ.prodFun p =
      (e : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) × f'.ker) := by
    have h := φ.hasStrictFDerivAt.hasFDerivAt.fderiv
    rw [hpt] at h
    exact h
  have hsymm : AnalyticAt ℝ (⇑φ.toOpenPartialHomeomorph.symm)
      ((g p, (0 : f'.ker)) : (Fin k → ℝ) × f'.ker) := by
    have h1 : AnalyticAt ℝ (⇑φ.toOpenPartialHomeomorph) p := by
      simpa [ImplicitFunctionData.toOpenPartialHomeomorph_coe] using hΦ
    have h2 : fderiv ℝ (⇑φ.toOpenPartialHomeomorph) p = e := by
      simpa [ImplicitFunctionData.toOpenPartialHomeomorph_coe] using hfderiv
    have h3 := φ.toOpenPartialHomeomorph.analyticAt_symm'
      (φ.pt_mem_toOpenPartialHomeomorph_source) h1 h2
    simpa [ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright, hpt] using h3
  have hγ_an : AnalyticAt ℝ γ 0 := by
    have h2 : AnalyticAt ℝ (fun v : f'.ker => ((g p, v) : (Fin k → ℝ) × f'.ker)) 0 := by
      have h := (analyticAt_const (v := g p) (x := (0 : f'.ker))).prod
        (analyticAt_id (𝕜 := ℝ) (z := (0 : f'.ker)))
      simpa using h
    have heq : γ = fun v : f'.ker => φ.toOpenPartialHomeomorph.symm (g p, v) := funext hγapply
    rw [heq]
    simpa [Function.comp_def] using hsymm.comp h2
  -- `γ` is strictly differentiable at `0` with derivative the inclusion of `ker` in `ℝⁿ`
  have hγ_fderiv : fderiv ℝ γ 0 = (f'.ker.subtypeL : f'.ker →L[ℝ] (Fin n → ℝ)) := by
    have h := hgp.to_implicitFunctionOfComplemented hsurj hker
    have h' : HasStrictFDerivAt γ (f'.ker.subtypeL) 0 := by
      simpa [γ, φ, HasStrictFDerivAt.implicitFunctionOfComplemented,
        ImplicitFunctionData.implicitFunction] using h
    exact h'.hasFDerivAt.fderiv
  have hγ_range : (fderiv ℝ γ 0).range = f'.ker := by
    rw [hγ_fderiv, Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
  have hχ_an : AnalyticAt ℝ χ p := by
    simpa [χ] using hC_an
  refine ⟨γ, V, U, χ, ?_, ?_, ?_, ?_, hγ0, hγ_an, ?_, ?_, ?_, ?_, hγ_range, hχ_an, ?_⟩
  · show IsOpen ((fun v : f'.ker => ((g p, v) : (Fin k → ℝ) × f'.ker)) ⁻¹'
      φ.toOpenPartialHomeomorph.target)
    exact φ.toOpenPartialHomeomorph.open_target.preimage
      (continuous_const.prodMk continuous_id)
  · exact φ.toOpenPartialHomeomorph.open_source
  · exact hTarget
  · exact hpU
  · intro v hv
    have h := φ.toOpenPartialHomeomorph.map_target hv
    rw [hγapply v]
    exact h
  · intro v hv
    have h := congr_arg Prod.fst (φ.toOpenPartialHomeomorph.right_inv hv)
    have key : g (φ.toOpenPartialHomeomorph.symm (g p, v)) = g p := by
      simpa [ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft] using h
    rwa [hγapply v]
  · intro y hy hgy
    have hy' : φ.toOpenPartialHomeomorph y =
        ((g p, C (y - p)) : (Fin k → ℝ) × f'.ker) := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright, hgy]
    refine ⟨C (y - p), ?_, ?_⟩
    · have h := φ.toOpenPartialHomeomorph.map_source hy
      rwa [hy'] at h
    · rw [hγapply, ← hy']
      exact φ.toOpenPartialHomeomorph.left_inv hy
  · intro v1 hv1 v2 hv2 hvv
    have h1 := φ.toOpenPartialHomeomorph.right_inv hv1
    have h2 := φ.toOpenPartialHomeomorph.right_inv hv2
    have : ((g p, v1) : (Fin k → ℝ) × f'.ker) = (g p, v2) := by
      rw [← h1, ← h2, ← hγapply v1, ← hγapply v2, hvv]
    exact congr_arg Prod.snd this
  · intro y hy hgy
    have hy' : φ.toOpenPartialHomeomorph y = ((g p, χ y) : (Fin k → ℝ) × f'.ker) := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright, hgy, χ]
    constructor
    · have h := φ.toOpenPartialHomeomorph.map_source hy
      rwa [hy'] at h
    · rw [hγapply, ← hy']
      exact φ.toOpenPartialHomeomorph.left_inv hy

end Work.WilE7.Nondrop
