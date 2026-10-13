import Mathlib

namespace Work.WilE7.Nondrop

open Filter
open scoped Topology

/-- If two analytic submersions `g`, `g'` at `p` (with `g p = g' p = 0`) have kernels of the
same dimension and the zero set of `g'` is contained in that of `g` near `p`, then the zero sets
coincide near `p`; in particular `g = 0` implies `g' = 0` near `p`.

The proof: the inclusion of the zero sets forces `ker (fderiv ℝ g' p) ≤ ker (fderiv ℝ g p)`
(differentiate `g ∘ γ'` for a local parametrisation `γ'` of the `g'`-level set), hence equality
of kernels by the dimension hypothesis.  Fixing one projection `L` onto the common kernel, the
level sets of `g` and `g'` are both parametrised as `u ↦ L(x - p) = u`, and the hypothesis
identifies the two parametrisations. -/
theorem levelSet_eq_near_of_subset {n k k' : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ))
    (g' : (Fin n → ℝ) → (Fin k' → ℝ)) (p : Fin n → ℝ)
    (hg : ∀ y, AnalyticAt ℝ g y) (hg' : ∀ y, AnalyticAt ℝ g' y)
    (hgp : g p = 0) (hg'p : g' p = 0)
    (hs : (fderiv ℝ g p).range = ⊤) (hs' : (fderiv ℝ g' p).range = ⊤)
    (hdim : Module.finrank ℝ (fderiv ℝ g' p).ker = Module.finrank ℝ (fderiv ℝ g p).ker)
    (hsub : ∀ᶠ y in nhds p, g' y = 0 → g y = 0) :
    ∀ᶠ y in nhds p, g y = 0 → g' y = 0 := by
  classical
  set A : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) := fderiv ℝ g p with hA
  set A' : (Fin n → ℝ) →L[ℝ] (Fin k' → ℝ) := fderiv ℝ g' p with hA'
  set E : Submodule ℝ (Fin n → ℝ) := A.ker with hE
  set E' : Submodule ℝ (Fin n → ℝ) := A'.ker with hE'
  haveI : CompleteSpace E := A.isClosed_ker.completeSpace_coe
  haveI : CompleteSpace E' := A'.isClosed_ker.completeSpace_coe
  have hdg : HasStrictFDerivAt g A p := (hg p).hasStrictFDerivAt
  have hdg' : HasStrictFDerivAt g' A' p := (hg' p).hasStrictFDerivAt
  -- ## Step 1: the kernels satisfy `E' ≤ E`
  have hE'_le : E' ≤ E := by
    set γ₀ : E' → (Fin n → ℝ) :=
      HasStrictFDerivAt.implicitFunction g' A' hdg' hs' (g' p) with hγ₀
    have hγ₀_strict : HasStrictFDerivAt γ₀ E'.subtypeL 0 :=
      HasStrictFDerivAt.to_implicitFunction hdg' hs'
    have hγ₀0 : γ₀ 0 = p := HasStrictFDerivAt.implicitFunction_apply_image hdg' hs'
    have hγ₀_tend : Tendsto γ₀ (nhds (0 : E')) (nhds p) := by
      have h : Tendsto γ₀ (nhds (0 : E')) (nhds (γ₀ 0)) := hγ₀_strict.continuousAt
      rwa [hγ₀0] at h
    have hleft : ∀ᶠ u in nhds (0 : E'), g' (γ₀ u) = g' p := by
      have ht : Tendsto (fun u : E' => ((g' p, u) : (Fin k' → ℝ) × E')) (nhds (0 : E'))
          (nhds (g' p, (0 : E'))) := tendsto_const_nhds.prodMk_nhds tendsto_id
      have h := ht.eventually (HasStrictFDerivAt.map_implicitFunction_eq hdg' hs')
      simpa [γ₀] using h
    have hgz : ∀ᶠ u in nhds (0 : E'), g (γ₀ u) = 0 := by
      filter_upwards [hleft, hγ₀_tend.eventually hsub] with u h1 h2
      rw [h1, hg'p] at h2
      exact h2 rfl
    have hcomp : HasStrictFDerivAt (fun u : E' => g (γ₀ u)) (A ∘SL E'.subtypeL) 0 := by
      have hdg₀ : HasStrictFDerivAt g A (γ₀ 0) := by simpa [hγ₀0] using hdg
      exact hdg₀.comp (0 : E') hγ₀_strict
    have hcomp' : HasStrictFDerivAt (fun _ : E' => (0 : Fin k → ℝ)) (A ∘SL E'.subtypeL) 0 :=
      hcomp.congr_of_eventuallyEq hgz
    have hA0 : A ∘SL E'.subtypeL = 0 :=
      hcomp'.hasFDerivAt.unique (hasStrictFDerivAt_const (0 : Fin k → ℝ) (0 : E')).hasFDerivAt
    intro x hx
    have h2 : A (E'.subtypeL ⟨x, hx⟩) = 0 := by
      have := congrArg (fun f : E' →L[ℝ] (Fin k → ℝ) => f ⟨x, hx⟩) hA0
      simpa using this
    rw [hE]
    simpa using h2
  -- ## Step 2: equality of kernels
  have hEq_or : E' = E := Submodule.eq_of_le_of_finrank_eq hE'_le hdim
  have hEE : E = E' := hEq_or.symm
  -- ## Step 3: a common projection onto the common kernel
  have hker : E.ClosedComplemented := A.ker_closedComplemented_of_finiteDimensional_range
  let L : (Fin n → ℝ) →L[ℝ] E := Classical.choose hker
  have hL : ∀ x : E, L x = x := Classical.choose_spec hker
  have hLid : L ∘SL E.subtypeL = ContinuousLinearMap.id ℝ E :=
    ContinuousLinearMap.ext fun x => hL x
  have hLrange : L.range = ⊤ :=
    LinearMap.range_eq_of_proj (f := (L : (Fin n → ℝ) →ₗ[ℝ] E)) hL
  have hLcompl : IsCompl E L.ker := LinearMap.isCompl_of_proj (f := (L : (Fin n → ℝ) →ₗ[ℝ] E)) hL
  have hstrictR : HasStrictFDerivAt (fun x : Fin n → ℝ => L (x - p)) L p :=
    L.hasStrictFDerivAt.comp p ((hasStrictFDerivAt_id p).sub_const p)
  -- ## Step 4: the two implicit-function data, using the *same* projection `L`
  let Φ : ImplicitFunctionData ℝ (Fin n → ℝ) (Fin k → ℝ) E :=
    { leftFun := g
      leftDeriv := A
      rightFun := fun x => L (x - p)
      rightDeriv := L
      pt := p
      hasStrictFDerivAt_leftFun := hdg
      hasStrictFDerivAt_rightFun := hstrictR
      range_leftDeriv := hs
      range_rightDeriv := hLrange
      isCompl_ker := hLcompl }
  let Φ' : ImplicitFunctionData ℝ (Fin n → ℝ) (Fin k' → ℝ) E :=
    { leftFun := g'
      leftDeriv := A'
      rightFun := fun x => L (x - p)
      rightDeriv := L
      pt := p
      hasStrictFDerivAt_leftFun := hdg'
      hasStrictFDerivAt_rightFun := hstrictR
      range_leftDeriv := hs'
      range_rightDeriv := hLrange
      isCompl_ker := by
        show IsCompl E' L.ker
        rw [hEq_or]
        exact hLcompl }
  let γ : E → (Fin n → ℝ) := Φ.implicitFunction (g p)
  let γ' : E → (Fin n → ℝ) := Φ'.implicitFunction (g' p)
  have h0R : L (p - p) = (0 : E) := by simp
  have hΦpt : Φ.prodFun Φ.pt = ((g p, 0) : (Fin k → ℝ) × E) := by
    simp [Φ, ImplicitFunctionData.prodFun, sub_self]
  have hΦ'pt : Φ'.prodFun Φ'.pt = ((g' p, 0) : (Fin k' → ℝ) × E) := by
    simp [Φ', ImplicitFunctionData.prodFun, sub_self]
  have hγ0 : γ 0 = p := by
    have h := Φ.implicitFunction_apply_image.self_of_nhds
    have h0 : Φ.rightFun Φ.pt = (0 : E) := by show L (p - p) = 0; exact h0R
    rw [h0] at h
    simpa [γ, Φ] using h
  have hγ'0 : γ' 0 = p := by
    have h := Φ'.implicitFunction_apply_image.self_of_nhds
    have h0 : Φ'.rightFun Φ'.pt = (0 : E) := by show L (p - p) = 0; exact h0R
    rw [h0] at h
    simpa [γ', Φ'] using h
  -- ## Step 5: derivatives of the parametrisations
  have hA0 : A ∘SL E.subtypeL = 0 := by
    ext x
    simpa using ContinuousLinearMap.apply_val_ker A x
  have hγ_strict : HasStrictFDerivAt γ E.subtypeL 0 := by
    have h := Φ.hasStrictFDerivAt_implicitFunction E.subtypeL hLid hA0
    have h0 : Φ.rightFun Φ.pt = (0 : E) := by show L (p - p) = 0; exact h0R
    rw [h0] at h
    simpa [γ] using h
  have hA'0 : A' ∘SL E.subtypeL = 0 := by
    have hle : E ≤ A'.ker := by
      show E ≤ E'
      exact le_of_eq hEE
    refine ContinuousLinearMap.ext fun x => ?_
    simpa using hle x.2
  have hγ'_strict : HasStrictFDerivAt γ' E.subtypeL 0 := by
    have h := Φ'.hasStrictFDerivAt_implicitFunction E.subtypeL hLid hA'0
    have h0 : Φ'.rightFun Φ'.pt = (0 : E) := by show L (p - p) = 0; exact h0R
    rw [h0] at h
    simpa [γ'] using h
  have hγ_tend : Tendsto γ (nhds (0 : E)) (nhds p) := by
    have h : Tendsto γ (nhds (0 : E)) (nhds (γ 0)) := hγ_strict.continuousAt
    rwa [hγ0] at h
  have hγ'_tend : Tendsto γ' (nhds (0 : E)) (nhds p) := by
    have h : Tendsto γ' (nhds (0 : E)) (nhds (γ' 0)) := hγ'_strict.continuousAt
    rwa [hγ'0] at h
  -- ## Step 6: the two parametrisations of the two level sets
  have hpush_Φ : Tendsto (fun u : E => ((g p, u) : (Fin k → ℝ) × E)) (nhds (0 : E))
      (nhds (Φ.prodFun Φ.pt)) := by
    rw [hΦpt]
    exact tendsto_const_nhds.prodMk_nhds tendsto_id
  have hpush_Φ' : Tendsto (fun u : E => ((g' p, u) : (Fin k' → ℝ) × E)) (nhds (0 : E))
      (nhds (Φ'.prodFun Φ'.pt)) := by
    rw [hΦ'pt]
    exact tendsto_const_nhds.prodMk_nhds tendsto_id
  have hleft_Φ : ∀ᶠ u in nhds (0 : E), g (γ u) = g p := by
    have h := hpush_Φ.eventually Φ.leftFun_implicitFunction
    simpa [γ, Φ] using h
  have hright_Φ : ∀ᶠ u in nhds (0 : E), L (γ u - p) = u := by
    have h := hpush_Φ.eventually Φ.rightFun_implicitFunction
    simpa [γ, Φ] using h
  have hleft_Φ' : ∀ᶠ u in nhds (0 : E), g' (γ' u) = g' p := by
    have h := hpush_Φ'.eventually Φ'.leftFun_implicitFunction
    simpa [γ', Φ'] using h
  have himg_Φ : ∀ᶠ x in nhds p, g x = g p → γ (L (x - p)) = x := by
    filter_upwards [Φ.implicitFunction_apply_image] with x hx hgx
    rw [show γ (L (x - p)) = Φ.implicitFunction (g p) (L (x - p)) from rfl, ← hgx]
    exact hx
  have himg_Φ' : ∀ᶠ x in nhds p, g' x = g' p → γ' (L (x - p)) = x := by
    filter_upwards [Φ'.implicitFunction_apply_image] with x hx hgx
    rw [show γ' (L (x - p)) = Φ'.implicitFunction (g' p) (L (x - p)) from rfl, ← hgx]
    exact hx
  -- ## Step 7: the level set of `g'` is contained in that of `g` near `p`
  have hzero' : ∀ᶠ u in nhds (0 : E), g (γ' u) = 0 := by
    filter_upwards [hγ'_tend.eventually hsub, hleft_Φ'] with u hu hu'
    rw [hu', hg'p] at hu
    exact hu rfl
  -- ## Step 8: `γ = γ' ∘ Ψ` near `0`, where `Ψ` inverts `u ↦ L (γ' u - p)`
  have hχ : HasStrictFDerivAt (fun x : Fin n → ℝ => L (x - p)) L p := hstrictR
  have hχ' : HasStrictFDerivAt (fun x : Fin n → ℝ => L (x - p)) L (γ' 0) := by
    rw [hγ'0]; exact hχ
  have hΘ_strict : HasStrictFDerivAt (fun u : E => L (γ' u - p)) (L ∘SL E.subtypeL) 0 :=
    hχ'.comp (0 : E) hγ'_strict
  have hΘ0 : L (γ' 0 - p) = (0 : E) := by rw [hγ'0]; exact h0R
  have hΘ' : HasStrictFDerivAt (fun u : E => L (γ' u - p))
      (↑(ContinuousLinearEquiv.refl ℝ E) : E →L[ℝ] E) 0 := by
    simpa [hLid] using hΘ_strict
  let Ψ : E → E :=
    hΘ'.localInverse (fun u : E => L (γ' u - p)) (ContinuousLinearEquiv.refl ℝ E) 0
  have hΨ_right : ∀ᶠ v in nhds (0 : E), L (γ' (Ψ v) - p) = v := by
    have h := hΘ'.eventually_right_inverse
    rw [hΘ0] at h
    simpa [Ψ] using h
  have hΨ0 : Ψ 0 = 0 := by
    have h := hΘ'.localInverse_apply_image
    rw [hΘ0] at h
    simpa [Ψ] using h
  have hΨtend : Tendsto Ψ (nhds (0 : E)) (nhds (0 : E)) := by
    have h : Tendsto Ψ (nhds (L (γ' 0 - p))) (nhds (Ψ (L (γ' 0 - p)))) :=
      hΘ'.localInverse_continuousAt
    rw [hΘ0, hΨ0] at h
    exact h
  have hγ_Θ : ∀ᶠ w in nhds (0 : E), γ (L (γ' w - p)) = γ' w := by
    filter_upwards [hzero', hγ'_tend.eventually himg_Φ] with w hw hw'
    exact hw' (by rw [hw, hgp])
  have hγ_Ψ : ∀ᶠ v in nhds (0 : E), γ v = γ' (Ψ v) := by
    have h2 : ∀ᶠ v in nhds (0 : E), γ (L (γ' (Ψ v) - p)) = γ' (Ψ v) :=
      hΨtend.eventually hγ_Θ
    filter_upwards [hΨ_right, h2] with v hv1 hv2
    rw [hv1] at hv2
    exact hv2
  -- ## Step 9: transport to a neighbourhood of `p`
  have htendL : Tendsto (fun x : Fin n → ℝ => L (x - p)) (nhds p) (nhds (0 : E)) := by
    have h : Tendsto (fun x : Fin n → ℝ => L (x - p)) (nhds p) (nhds (L (p - p))) :=
      hχ.continuousAt
    rwa [h0R] at h
  have htendΨL : Tendsto (fun x : Fin n → ℝ => Ψ (L (x - p))) (nhds p) (nhds (0 : E)) :=
    hΨtend.comp htendL
  have hγΨ_push : ∀ᶠ x in nhds p, γ (L (x - p)) = γ' (Ψ (L (x - p))) :=
    htendL.eventually hγ_Ψ
  have hγ'Ψ_stay : ∀ᶠ x in nhds p, g' (γ' (Ψ (L (x - p)))) = g' p :=
    htendΨL.eventually hleft_Φ'
  filter_upwards [himg_Φ, hγΨ_push, hγ'Ψ_stay] with x hx1 hx2 hx3 hgx
  have hxg : g x = g p := by rw [hgx, hgp]
  have h1 : γ (L (x - p)) = x := hx1 hxg
  calc g' x = g' (γ (L (x - p))) := by rw [h1]
    _ = g' (γ' (Ψ (L (x - p)))) := by rw [hx2]
    _ = g' p := hx3
    _ = 0 := hg'p

end Work.WilE7.Nondrop
