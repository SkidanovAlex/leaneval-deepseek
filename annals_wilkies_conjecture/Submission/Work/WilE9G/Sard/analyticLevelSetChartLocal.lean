import Mathlib
import Submission.Work.WilE7.Auxiliary.analyticLevelSetChart

namespace Work.WilE9G.Sard

open Set
open scoped Topology

/-- **Local analytic chart of a level set.**  Let `g : ℝⁿ → ℝᵏ` be analytic at `p` and suppose its
differential at `p` is surjective.  Then the level set `{g = g p}` is, near `p`, the analytic image
of an open subset of the kernel `W = ker (fderiv ℝ g p)` under a chart `γ`, whose inverse is given
by a fixed projection `C` onto `W`.  Concretely: `C` is the identity on `W`, `γ 0 = p`, `γ` is
analytic at `0`, `g (γ v) = g p` and `C (γ v - p) = v` for `v ∈ V`, and conversely every `y` in the
open neighbourhood `U` of `p` with `g y = g p` is the image `γ (C (y - p))` of its own
`C`-coordinate. -/
theorem analyticLevelSetChartLocal {n k : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ)) (p : Fin n → ℝ)
    (hg : AnalyticAt ℝ g p) (hsurj : (fderiv ℝ g p).range = ⊤) :
    ∃ (C : (Fin n → ℝ) →L[ℝ] (fderiv ℝ g p).ker)
      (γ : (fderiv ℝ g p).ker → (Fin n → ℝ))
      (V : Set (fderiv ℝ g p).ker) (U : Set (Fin n → ℝ)),
      (∀ x : (fderiv ℝ g p).ker, C x = x) ∧
      IsOpen V ∧ IsOpen U ∧ (0 : (fderiv ℝ g p).ker) ∈ V ∧ p ∈ U ∧ γ 0 = p ∧
      AnalyticAt ℝ γ 0 ∧ (∀ v ∈ V, γ v ∈ U) ∧ (∀ v ∈ V, g (γ v) = g p) ∧
      (∀ v ∈ V, C (γ v - p) = v) ∧
      (∀ y ∈ U, g y = g p → γ (C (y - p)) = y) := by
  let f' : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) := fderiv ℝ g p
  have hgp : HasStrictFDerivAt g f' p := hg.hasStrictFDerivAt
  have hker : f'.ker.ClosedComplemented :=
    f'.ker_closedComplemented_of_finiteDimensional_range
  haveI : CompleteSpace f'.ker := f'.isClosed_ker.completeSpace_coe
  -- the projection `C` onto the kernel, satisfying `C x = x` for `x` in the kernel
  let C : (Fin n → ℝ) →L[ℝ] f'.ker := Classical.choose hker
  have hC_id : ∀ x : f'.ker, C x = x := Classical.choose_spec hker
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
    have h := hg.prod hC_an
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
  refine ⟨C, γ, V, U, hC_id, ?_, ?_, ?_, ?_, ?_, hγ_an, ?_, ?_, ?_, ?_⟩
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
  · intro v hv
    have h := congr_arg Prod.snd (φ.toOpenPartialHomeomorph.right_inv hv)
    simpa [ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright, γ] using h
  · intro y hy hgy
    have hEq : ((g p, C (y - p)) : (Fin k → ℝ) × f'.ker) = φ.toOpenPartialHomeomorph y := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright, hgy]
    show φ.toOpenPartialHomeomorph.symm (g p, C (y - p)) = y
    rw [hEq]
    exact φ.toOpenPartialHomeomorph.left_inv hy

end Work.WilE9G.Sard
