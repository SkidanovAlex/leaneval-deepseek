/-
  WilE7 / CS-slice: the slice derivative is invertible near the origin.

  The chart `Φ (t,e) = γ t + B e` has `t`-directional derivative `sliceDeriv γ B t`.  The
  hypothesis `hB` says that at `t = 0` this linear map is a bijection, i.e. `(τ,0) ↦ Φ(τ+·,·)`
  is a local diffeomorphism at `(0,0)`.

  Analyticity of `γ` makes `t ↦ fderiv ℝ γ t` continuous (`ContDiff.continuous_fderiv`), hence
  so is `t ↦ sliceDeriv γ B t`.  Invertibility of continuous linear maps between Banach spaces
  is an open property (`ContinuousLinearMap.isOpen_setOfPred_isInvertible`, Banach's open mapping
  theorem), so the set of `t` with `sliceDeriv γ B t` bijective is a neighbourhood of `0`.
-/
import Mathlib
import Submission.Work.WilE7.FrontierCS.Defs
import Submission.Work.WilE7.FrontierCS.gc_defs

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.FrontierCS

/-- A bijective continuous linear map between complete normed spaces over `ℝ` is invertible (the
forward direction of a continuous linear equivalence): the inverse linear map is continuous by the
Banach open mapping theorem, which is packaged in `ContinuousLinearEquiv.ofBijective`. -/
lemma isInvertible_of_bijective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E →L[ℝ] F) (hf : Function.Bijective f) : f.IsInvertible := by
  have hinj : (f : E →ₗ[ℝ] F).ker = ⊥ := LinearMap.ker_eq_bot.mpr hf.1
  have hsurj : (f : E →ₗ[ℝ] F).range = ⊤ := LinearMap.range_eq_top.mpr hf.2
  exact ⟨ContinuousLinearEquiv.ofBijective f hinj hsurj, rfl⟩

theorem gc_bijective_eventually {N d j : ℕ} {γ : (Fin d → ℝ) → (Fin N → ℝ)}
    (hγ : AnalyticOnNhd ℝ γ Set.univ) {B : (Fin j → ℝ) →L[ℝ] (Fin N → ℝ)}
    (hB : Function.Bijective
      (fun p : (Fin d → ℝ) × (Fin j → ℝ) => fderiv ℝ γ 0 p.1 + B p.2)) :
    Filter.Eventually (fun t : Fin d → ℝ =>
      Function.Bijective (Work.WilE7.FrontierCS.sliceDeriv γ B t)) (nhds 0) := by
  -- The slice derivative at `0` is exactly the map of the hypothesis, hence bijective.
  have hbij0 : Function.Bijective (sliceDeriv γ B (0 : Fin d → ℝ)) := by
    have hfun : ⇑(sliceDeriv γ B (0 : Fin d → ℝ)) =
        fun p : (Fin d → ℝ) × (Fin j → ℝ) => fderiv ℝ γ 0 p.1 + B p.2 := by
      funext p; simp
    rw [hfun]; exact hB
  -- hence invertible, as a continuous linear map.
  have hinv0 : (sliceDeriv γ B (0 : Fin d → ℝ)).IsInvertible :=
    isInvertible_of_bijective _ hbij0
  -- `t ↦ sliceDeriv γ B t` is continuous, because `fderiv ℝ γ` is (analyticity).
  have hcont : Continuous fun t : Fin d → ℝ => sliceDeriv γ B t := by
    have hfd : Continuous (fderiv ℝ γ) :=
      (hγ.contDiff (n := 1)).continuous_fderiv one_ne_zero
    simp only [sliceDeriv]
    fun_prop
  -- invertibility of continuous linear maps is an open condition.
  have hopen :
      IsOpen {T : ((Fin d → ℝ) × (Fin j → ℝ)) →L[ℝ] (Fin N → ℝ) | T.IsInvertible} :=
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  exact (hcont.continuousAt.eventually (hopen.eventually_mem hinv0)).mono
    (fun t ht => ht.bijective)

end Work.WilE7.FrontierCS
