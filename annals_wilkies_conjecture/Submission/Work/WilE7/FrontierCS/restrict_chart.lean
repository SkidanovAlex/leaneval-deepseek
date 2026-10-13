import Mathlib

namespace Work.WilE7.FrontierCS

open Filter Topology

/-- The linear map `(Fin d → ℝ) →ₗ[ℝ] (Fin n → ℝ)` sending a function on `Fin d` to its
extension by zero on `Fin n` (using the first `d` coordinates of `Fin n`). -/
private noncomputable def extendZero (n d : ℕ) : (Fin d → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun s := fun j => if h : (j : ℕ) < d then s ⟨(j : ℕ), h⟩ else 0
  map_add' s t := by
    funext j
    by_cases h : (j : ℕ) < d <;> simp [h]
  map_smul' c s := by
    funext j
    by_cases h : (j : ℕ) < d <;> simp [h]

/-- **N9a.** Restriction of an analytic chart to its first `d ≤ n` coordinates.

Given `γ : ℝⁿ → ℝ^N` analytic on all of `ℝⁿ` with injective derivative at `0`, and a property `P`
which holds eventually along `γ` near `0`, we can compress the source to `ℝ^d` (`d ≤ n`),
retaining analyticity, injectivity of the derivative at `0`, and the eventual property.

The compression is `γ' = γ ∘ e` where `e : ℝ^d → ℝⁿ` is the linear extension by zero onto the
first `d` coordinates.  Since `e` is an injective continuous linear map with `e 0 = 0`,
`fderiv ℝ γ' 0 = (fderiv ℝ γ 0).comp e` is injective, `γ'` is analytic (composition of an
analytic map with a linear one) and the eventual property pulls back through `e`. -/
theorem restrict_chart {N n d : ℕ} (hdn : d ≤ n) {γ : (Fin n → ℝ) → (Fin N → ℝ)}
    (hγ : AnalyticOnNhd ℝ γ Set.univ) (hγinj : Function.Injective (fderiv ℝ γ 0))
    {P : (Fin N → ℝ) → Prop} (hP : Filter.Eventually (fun s => P (γ s)) (nhds (0 : Fin n → ℝ))) :
    ∃ γ' : (Fin d → ℝ) → (Fin N → ℝ), AnalyticOnNhd ℝ γ' Set.univ ∧
      Function.Injective (fderiv ℝ γ' 0) ∧
      Filter.Eventually (fun s => P (γ' s)) (nhds (0 : Fin d → ℝ)) := by
  let e : (Fin d → ℝ) →L[ℝ] (Fin n → ℝ) :=
    LinearMap.toContinuousLinearMap (extendZero n d)
  -- Evaluation of `e` at the coordinate `Fin.castLE hdn i`.
  have he_eval : ∀ (s : Fin d → ℝ) (i : Fin d), (e s) (Fin.castLE hdn i) = s i := by
    intro s i
    simp only [e, LinearMap.coe_toContinuousLinearMap', extendZero]
    exact dite_eq_left i.isLt
  -- `e` is injective.
  have he_inj : Function.Injective (fun s : Fin d → ℝ => e s) := by
    intro s t h
    funext i
    have h' : e s = e t := h
    have hh : e s (Fin.castLE hdn i) = e t (Fin.castLE hdn i) := by rw [h']
    rw [he_eval s i, he_eval t i] at hh
    exact hh
  refine ⟨fun s => γ (e s), ?_, ?_, ?_⟩
  · -- analyticity: `γ ∘ e`, composition of an analytic map with a continuous linear map.
    exact hγ.comp (fun x _ => e.analyticAt x) (fun x _ => trivial)
  · -- injectivity of the derivative: chain rule at `0`.
    have hder : fderiv ℝ (fun s : Fin d → ℝ => γ (e s)) 0
        = (fderiv ℝ γ 0).comp e := by
      rw [show (fun s : Fin d → ℝ => γ (e s)) = γ ∘ (fun s : Fin d → ℝ => e s) from rfl]
      rw [fderiv_comp (g := γ) (f := fun s : Fin d → ℝ => e s) (x := 0)
        ((hγ (e 0) trivial).differentiableAt) e.differentiableAt]
      simp
    rw [hder]
    intro s t h
    exact he_inj (hγinj h)
  · -- the eventual property pulls back through the continuous map `e`, `e 0 = 0`.
    have htend : Filter.Tendsto (fun s : Fin d → ℝ => e s) (nhds 0) (nhds (0 : Fin n → ℝ)) := by
      have h := e.continuous.tendsto (0 : Fin d → ℝ)
      simpa using h
    simpa using htend.eventually hP

end Work.WilE7.FrontierCS
