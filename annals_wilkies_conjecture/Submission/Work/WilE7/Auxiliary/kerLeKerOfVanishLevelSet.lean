import Mathlib

open Filter

namespace Work.WilE7.Auxiliary

/-- If `g` is strictly differentiable at `y₀` with surjective derivative `L`, if `g y₀ = 0`, and
if a function `F`, differentiable at `y₀` with derivative `M`, is constant (equal to `F y₀`) on
the zero set of `g` near `y₀`, then `L.ker ≤ M.ker`, i.e. `M` vanishes on the kernel of `L`.

The zero set of a submersion is a submanifold whose tangent space at `y₀` is `L.ker`.  Strict
differentiability of `g` gives, through the implicit function theorem
(`HasStrictFDerivAt.to_implicitFunction`), a parametrization `γ : L.ker → E` of that zero set
near `y₀`, strictly differentiable at `0` with derivative the inclusion `L.ker ↪ E`.  For
`v ∈ L.ker` the curve `t ↦ γ (t • v)` then lies on the zero set and has tangent vector `v` at
`t = 0`; since `F` is constant along it, its derivative at `0` vanishes, which gives `M v = 0`. -/
theorem kerLeKerOfVanishLevelSet {q k : ℕ} (g : (Fin q → ℝ) → (Fin k → ℝ))
    (F : (Fin q → ℝ) → ℝ) (y₀ : Fin q → ℝ) (L : (Fin q → ℝ) →L[ℝ] (Fin k → ℝ))
    (M : (Fin q → ℝ) →L[ℝ] ℝ)
    (hg : HasStrictFDerivAt g L y₀) (hF : HasFDerivAt F M y₀)
    (hsurj : L.range = ⊤) (hg0 : g y₀ = 0)
    (hvan : ∀ᶠ y in nhds y₀, g y = 0 → F y = F y₀) :
    L.ker ≤ M.ker := by
  intro x hx
  -- A parametrization of the zero set of `g` near `y₀`, over `L.ker`.
  let v : L.ker := ⟨x, hx⟩
  let γ : L.ker → (Fin q → ℝ) := hg.implicitFunction g L hsurj (g y₀)
  have hγ0 : γ 0 = y₀ := hg.implicitFunction_apply_image hsurj
  have hγfd : HasStrictFDerivAt γ L.ker.subtypeL 0 := hg.to_implicitFunction hsurj
  -- The curve `t ↦ γ (t • v)`, tangent to `v` at `t = 0`.
  let c : ℝ → (Fin q → ℝ) := fun t => γ (t • v)
  have hc0 : c 0 = y₀ := by simp [c, hγ0]
  have hs : HasStrictFDerivAt (fun t : ℝ => t • v)
      (ContinuousLinearMap.toSpanSingleton ℝ v) 0 :=
    (ContinuousLinearMap.toSpanSingleton ℝ v).hasStrictFDerivAt
  have hγ' : HasStrictFDerivAt γ L.ker.subtypeL ((fun t : ℝ => t • v) 0) := by
    simpa using hγfd
  have hc : HasStrictFDerivAt c
      (L.ker.subtypeL.comp (ContinuousLinearMap.toSpanSingleton ℝ v)) 0 := by
    have h := hγ'.comp (x := (0 : ℝ)) hs
    simpa [c] using h
  -- The curve stays on the zero set of `g`.
  have hlev : ∀ᶠ t in nhds (0 : ℝ), g (c t) = g y₀ := by
    have h1 : Tendsto (fun t : ℝ => t • v) (nhds 0) (nhds (0 : L.ker)) := by
      simpa using hs.continuousAt.tendsto
    have hcomp : Tendsto (fun t : ℝ => (g y₀, t • v)) (nhds 0)
        (nhds (g y₀, (0 : L.ker))) :=
      tendsto_const_nhds.prodMk_nhds h1
    have h2 := hcomp.eventually (hg.map_implicitFunction_eq hsurj)
    simpa [c, γ] using h2
  have hct : Tendsto c (nhds 0) (nhds y₀) := by
    rw [← hc0]; exact hc.continuousAt.tendsto
  have hFF : ∀ᶠ t in nhds (0 : ℝ), F (c t) = F y₀ := by
    have h1 := hct.eventually hvan
    filter_upwards [h1, hlev] with t ht1 ht2
    exact ht1 (by rw [ht2, hg0])
  -- `F ∘ c` is eventually constant, hence has zero derivative at `0`.
  have hconst : HasFDerivAt (fun _ : ℝ => F y₀) (0 : ℝ →L[ℝ] ℝ) 0 :=
    hasFDerivAt_const (F y₀) (0 : ℝ)
  have hzero : HasFDerivAt (fun t : ℝ => F (c t)) (0 : ℝ →L[ℝ] ℝ) 0 :=
    hconst.congr_of_eventuallyEq hFF
  -- By the chain rule its derivative is `M` composed with the inclusion of `L.ker`.
  have hFc : HasFDerivAt (fun t : ℝ => F (c t))
      (M.comp (L.ker.subtypeL.comp (ContinuousLinearMap.toSpanSingleton ℝ v))) 0 := by
    have hF' : HasFDerivAt F M (c 0) := by rw [hc0]; exact hF
    exact hF'.comp (x := (0 : ℝ)) hc.hasFDerivAt
  have hkey : M.comp (L.ker.subtypeL.comp (ContinuousLinearMap.toSpanSingleton ℝ v)) =
      (0 : ℝ →L[ℝ] ℝ) := hFc.unique hzero
  have hB1 : (L.ker.subtypeL.comp (ContinuousLinearMap.toSpanSingleton ℝ v)) 1 = x := by
    simp [v]
  have : M x = 0 := by
    have h3 := congrArg (fun (A : ℝ →L[ℝ] ℝ) => A 1) hkey
    simpa [ContinuousLinearMap.comp_apply, hB1] using h3
  simpa [LinearMap.mem_ker] using this

end Work.WilE7.Auxiliary
