import Mathlib

namespace Work.WilE7.FrontierCS

open Module

/-- **Linear complement.**  An injective continuous linear map `A : ℝ^d → ℝ^N` with `d + j = N`
admits a continuous linear `B : ℝ^j → ℝ^N` whose image is a linear complement of `A.range`, so
that `(u, v) ↦ A u + B v` is a bijection `ℝ^d × ℝ^j → ℝ^N`. -/
theorem exists_complement {N d j : ℕ} (hdj : d + j = N)
    (A : (Fin d → ℝ) →L[ℝ] (Fin N → ℝ)) (hA : Function.Injective A) :
    ∃ B : (Fin j → ℝ) →L[ℝ] (Fin N → ℝ),
      Function.Bijective (fun p : (Fin d → ℝ) × (Fin j → ℝ) => A p.1 + B p.2) := by
  have hA' : Function.Injective A.toLinearMap := hA
  let W : Submodule ℝ (Fin N → ℝ) := A.toLinearMap.range
  -- `W = range A` has dimension `d`
  have hAdim : finrank ℝ W = d := by
    have h := LinearMap.finrank_range_add_finrank_ker A.toLinearMap
    have hker : A.toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.mpr hA'
    rw [hker, finrank_bot, add_zero, Module.finrank_fin_fun] at h
    exact h
  -- choose a linear complement `q` of `W`
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl W
  have hqsum : finrank ℝ q = j := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq W q
    rw [hq.sup_eq_top, hq.inf_eq_bot, finrank_top, finrank_bot, hAdim,
      Module.finrank_fin_fun] at h
    omega
  have hcond : finrank ℝ (Fin j → ℝ) = finrank ℝ q := by
    rw [Module.finrank_fin_fun, hqsum]
  -- a linear equivalence `ℝ^j ≃ q`, and `B` its inclusion into `ℝ^N`
  let e : (Fin j → ℝ) ≃L[ℝ] q := ContinuousLinearEquiv.ofFinrankEq hcond
  let B : (Fin j → ℝ) →L[ℝ] (Fin N → ℝ) := q.subtypeL.comp (e : (Fin j → ℝ) →L[ℝ] q)
  refine ⟨B, ?_⟩
  -- `A` identifies `ℝ^d` with `W`
  let Ae : (Fin d → ℝ) ≃ₗ[ℝ] W := LinearEquiv.ofInjective A.toLinearMap hA'
  -- the sum map `W × q → ℝ^N` is bijective
  have h1 : Function.Bijective
      (fun z : W × q => ((z.1 : W) : Fin N → ℝ) + ((z.2 : q) : Fin N → ℝ)) :=
    (Submodule.prodEquivOfIsCompl W q hq).bijective
  -- the pairing `ℝ^d × ℝ^j → W × q` is bijective
  have h2 : Function.Bijective
      (fun x : (Fin d → ℝ) × (Fin j → ℝ) => (Ae x.1, (e x.2 : q))) :=
    Function.Bijective.prodMap Ae.bijective e.bijective
  have hcomp : Function.Bijective
      ((fun z : W × q => ((z.1 : W) : Fin N → ℝ) + ((z.2 : q) : Fin N → ℝ)) ∘
        (fun x : (Fin d → ℝ) × (Fin j → ℝ) => (Ae x.1, (e x.2 : q)))) :=
    h1.comp h2
  have hAe_apply : ∀ x : Fin d → ℝ, ((Ae x : W) : Fin N → ℝ) = A x := fun _ => rfl
  have hB_apply : ∀ v : Fin j → ℝ, B v = ((e v : q) : Fin N → ℝ) := fun _ => rfl
  have hgoal : (fun p : (Fin d → ℝ) × (Fin j → ℝ) => A p.1 + B p.2) =
      ((fun z : W × q => ((z.1 : W) : Fin N → ℝ) + ((z.2 : q) : Fin N → ℝ)) ∘
        (fun x : (Fin d → ℝ) × (Fin j → ℝ) => (Ae x.1, (e x.2 : q)))) := by
    funext x
    simp only [Function.comp_apply]
    rw [hAe_apply x.1, ← hB_apply x.2]
  rw [hgoal]
  exact hcomp

end Work.WilE7.FrontierCS
