import Mathlib

namespace Work.WilE7.Aux

open Set
open scoped Topology

theorem analyticLevelSetChart {n k : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ)) (p : Fin n → ℝ)
    (hg : ∀ q, AnalyticAt ℝ g q) (hsurj : (fderiv ℝ g p).range = ⊤) :
    ∃ (γ : (fderiv ℝ g p).ker → (Fin n → ℝ)) (V : Set (fderiv ℝ g p).ker) (U : Set (Fin n → ℝ)),
      IsOpen V ∧ IsOpen U ∧ (0 : (fderiv ℝ g p).ker) ∈ V ∧ p ∈ U ∧ γ 0 = p ∧
      AnalyticAt ℝ γ 0 ∧ (∀ v ∈ V, γ v ∈ U) ∧ (∀ v ∈ V, g (γ v) = g p) ∧
      (∀ y ∈ U, g y = g p → ∃ v ∈ V, γ v = y) := by
  let f' : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) := fderiv ℝ g p
  have hgp : HasStrictFDerivAt g f' p := (hg p).hasStrictFDerivAt
  have hker : f'.ker.ClosedComplemented :=
    f'.ker_closedComplemented_of_finiteDimensional_range
  haveI : CompleteSpace f'.ker := f'.isClosed_ker.completeSpace_coe
  let C : (Fin n → ℝ) →L[ℝ] f'.ker := Classical.choose hker
  let φ : ImplicitFunctionData ℝ (Fin n → ℝ) (Fin k → ℝ) f'.ker :=
    HasStrictFDerivAt.implicitFunctionDataOfComplemented g f' hgp hsurj hker
  have hleft : ∀ x, φ.leftFun x = g x := fun x => rfl
  have hright : ∀ x, φ.rightFun x = C (x - p) := fun x => rfl
  have hpt : φ.pt = p := rfl
  -- the map `x ↦ (g x, C (x - p))` is analytic at `p`
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
  -- its derivative is the linear equivalence `x ↦ (f' x, C x)`
  let e : (Fin n → ℝ) ≃L[ℝ] (Fin k → ℝ) × f'.ker :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.range_leftDeriv
      φ.range_rightDeriv φ.isCompl_ker
  have hfderiv : fderiv ℝ φ.prodFun p =
      (e : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) × f'.ker) := by
    have h := φ.hasStrictFDerivAt.hasFDerivAt.fderiv
    rw [hpt] at h
    exact h
  -- the inverse of a local analytic homeomorphism is analytic
  have hsymm : AnalyticAt ℝ (⇑φ.toOpenPartialHomeomorph.symm)
      ((g p, (0 : f'.ker)) : (Fin k → ℝ) × f'.ker) := by
    have h1 : AnalyticAt ℝ (⇑φ.toOpenPartialHomeomorph) p := by
      simpa [ImplicitFunctionData.toOpenPartialHomeomorph_coe] using hΦ
    have h2 : fderiv ℝ (⇑φ.toOpenPartialHomeomorph) p = e := by
      simpa [ImplicitFunctionData.toOpenPartialHomeomorph_coe] using hfderiv
    have h3 := φ.toOpenPartialHomeomorph.analyticAt_symm'
      (φ.pt_mem_toOpenPartialHomeomorph_source) h1 h2
    simpa [ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright, hpt] using h3
  let γ : f'.ker → (Fin n → ℝ) := fun v => φ.toOpenPartialHomeomorph.symm (g p, v)
  have hγ_an : AnalyticAt ℝ γ 0 := by
    have h2 : AnalyticAt ℝ (fun v : f'.ker => ((g p, v) : (Fin k → ℝ) × f'.ker)) 0 := by
      have h := (analyticAt_const (v := g p) (x := (0 : f'.ker))).prod
        (analyticAt_id (𝕜 := ℝ) (z := (0 : f'.ker)))
      simpa using h
    simpa [γ, Function.comp_def] using hsymm.comp h2
  let V : Set f'.ker := {v | ((g p, v) : (Fin k → ℝ) × f'.ker) ∈ φ.toOpenPartialHomeomorph.target}
  let U : Set (Fin n → ℝ) := φ.toOpenPartialHomeomorph.source
  have hTarget : ((g p, (0 : f'.ker)) : (Fin k → ℝ) × f'.ker) ∈
      φ.toOpenPartialHomeomorph.target := by
    have h := φ.toOpenPartialHomeomorph.map_source (φ.pt_mem_toOpenPartialHomeomorph_source)
    simpa [ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright, hpt] using h
  refine ⟨γ, V, U, ?_, ?_, ?_, ?_, ?_, hγ_an, ?_, ?_, ?_⟩
  · exact φ.toOpenPartialHomeomorph.open_target.preimage
      (continuous_const.prodMk continuous_id)
  · exact φ.toOpenPartialHomeomorph.open_source
  · exact hTarget
  · simpa [hpt] using φ.pt_mem_toOpenPartialHomeomorph_source
  · show φ.toOpenPartialHomeomorph.symm (g p, (0 : f'.ker)) = p
    have h0 : ((g p, (0 : f'.ker)) : (Fin k → ℝ) × f'.ker) = φ.toOpenPartialHomeomorph p := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright]
    rw [h0]
    exact φ.toOpenPartialHomeomorph.left_inv (φ.pt_mem_toOpenPartialHomeomorph_source)
  · intro v hv
    exact φ.toOpenPartialHomeomorph.map_target hv
  · intro v hv
    have h := congr_arg Prod.fst (φ.toOpenPartialHomeomorph.right_inv hv)
    simpa [ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright, γ] using h
  · intro y hy hgy
    have hEq : ((g p, C (y - p)) : (Fin k → ℝ) × f'.ker) = φ.toOpenPartialHomeomorph y := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright, hgy]
    refine ⟨C (y - p), ?_, ?_⟩
    · show ((g p, C (y - p)) : (Fin k → ℝ) × f'.ker) ∈ φ.toOpenPartialHomeomorph.target
      rw [hEq]
      exact φ.toOpenPartialHomeomorph.map_source hy
    · show φ.toOpenPartialHomeomorph.symm (g p, C (y - p)) = y
      rw [hEq]
      exact φ.toOpenPartialHomeomorph.left_inv hy

end Work.WilE7.Aux
