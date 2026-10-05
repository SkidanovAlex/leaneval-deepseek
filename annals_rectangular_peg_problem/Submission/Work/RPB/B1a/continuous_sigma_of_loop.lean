import Mathlib
import Submission.Work.RPB.B1a.Defs
import Submission.Work.RPB1a.exists_smooth_embedding_descend

/-!
# A continuous curve in the image of a smooth loop lifts to a continuous parameter

`Work.RPB.B1a.continuous_sigma_of_loop`: for a smooth loop `v : ℝ → ℂ`
(`Work.RPB.B1a.IsSmoothLoop`: `C^∞`, `2π`-periodic, injective mod `2π`, immersed) and a continuous
`G : ℝ → ℂ` taking values in `Set.range v`, there is a continuous `σ : ℝ → ℝ` with
`G t = v (σ t)`.

The image `Set.range v` is an embedded circle: descending `v` through the covering map
`Circle.exp : ℝ → Circle` (`Work.RPB1a.exists_smooth_embedding_descend`) produces a continuous
injective `γ : Circle → ℝ × ℝ` with `γ ∘ Circle.exp = e ∘ v` and `range γ = e '' range v`, where
`e = Complex.equivRealProdCLM`.  As `Circle` is compact and `range γ` Hausdorff, `γ` is a
homeomorphism onto its range, so `G` composed with `e` and the inverse of `γ` is a continuous map
`H : ℝ → Circle`.  Finally `ℝ` is simply connected and locally path connected, so the covering
`Circle.exp` admits a continuous lift `σ` of `H` (`IsCoveringMap.existsUnique_continuousMap_lifts`);
composing the defining identities gives `v (σ t) = e.symm (γ (Circle.exp (σ t))) = e.symm (γ (H t))
= e.symm (e (G t)) = G t`.
-/

open Complex Set Metric
open scoped ContDiff Real

namespace Work.RPB.B1a

theorem continuous_sigma_of_loop (v : ℝ → ℂ) (hv : Work.RPB.B1a.IsSmoothLoop v)
    (G : ℝ → ℂ) (hG : Continuous G) (hGr : ∀ t, G t ∈ Set.range v) :
    ∃ σ : ℝ → ℝ, Continuous σ ∧ ∀ t, G t = v (σ t) := by
  -- Descend the smooth loop to an embedded circle `γ : Circle → ℝ × ℝ`.
  obtain ⟨γ, _hemb, hγcont, hγinj, hγexp, hrange⟩ :=
    Work.RPB1a.exists_smooth_embedding_descend v hv
  -- The bijection `Circle ≃ range γ` induced by `γ`.
  let φ : Circle → Set.range γ := fun z => ⟨γ z, Set.mem_range_self z⟩
  have hφcont : Continuous φ := Continuous.subtype_mk hγcont (fun z => Set.mem_range_self z)
  have hφinj : Function.Injective φ := by
    intro z w h
    exact hγinj (congrArg Subtype.val h)
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨z, hz⟩ := y.2
    exact ⟨z, Subtype.ext hz⟩
  let φe : Circle ≃ Set.range γ := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hφecont : Continuous φe := hφcont
  -- `Circle` is compact and `range γ` is Hausdorff, so `γ` is a homeomorphism onto its range.
  let φh : Circle ≃ₜ Set.range γ := Continuous.homeoOfEquivCompactToT2 (f := φe) hφecont
  -- `e (G t)` lies in `range γ`.
  have heG : ∀ t, Complex.equivRealProdCLM (G t) ∈ Set.range γ := by
    intro t
    rw [hrange]
    exact ⟨G t, hGr t, rfl⟩
  -- The map `H : ℝ → Circle` corresponding to `G`.
  let H : ℝ → Circle := fun t => φh.symm ⟨Complex.equivRealProdCLM (G t), heG t⟩
  have hHcont : Continuous H :=
    φh.symm.continuous.comp
      (Continuous.subtype_mk (Complex.equivRealProdCLM.continuous.comp hG) heG)
  -- Lift `H` through the universal cover `Circle.exp : ℝ → Circle`.
  obtain ⟨e₀, he₀⟩ := Circle.exp_surjective (H 0)
  obtain ⟨σ, hσ⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    (⟨H, hHcont⟩ : C(ℝ, Circle)) 0 e₀ he₀
  have hσexp : ∀ t, Circle.exp (σ t) = H t := fun t => congrFun hσ.1.2 t
  -- `γ` inverts the descent on `H`.
  have hγH : ∀ t, γ (H t) = Complex.equivRealProdCLM (G t) := by
    intro t
    have h2 : φh (H t) = ⟨Complex.equivRealProdCLM (G t), heG t⟩ :=
      φh.apply_symm_apply ⟨Complex.equivRealProdCLM (G t), heG t⟩
    exact congrArg Subtype.val h2
  refine ⟨σ, σ.continuous, fun t => ?_⟩
  have h4 : Complex.equivRealProdCLM (v (σ t)) = γ (H t) := by
    rw [← hσexp t]
    exact (hγexp (σ t)).symm
  have hfin : v (σ t) = G t := by
    apply Complex.equivRealProdCLM.injective
    rw [h4, hγH t]
  exact hfin.symm

end Work.RPB.B1a
