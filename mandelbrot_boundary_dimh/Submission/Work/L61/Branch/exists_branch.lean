import Mathlib
import Submission.Work.L61.Basic
import Submission.Work.L61.Push.gdom_open_ball
import Submission.Work.L61.Branch.deriv_eq_zero_imp_critVal
import Submission.Work.L61.Branch.analyticAt_of_lift

/-!
# Lemma 6.1 (Shishikura §6) — the holomorphic inverse branch

`Work.L61.Branch.exists_branch`: given the horn map `g = pushdown Ẽ_{f₀}` of `d` (with `HornData`),
whose restriction to `gdom ∩ {g ≠ critVal}` is a covering map onto `(Kset)ᶜ`, every holomorphic `f`
on a simply connected open `U` with values in `(Kset)ᶜ`, together with a single lift `e₀ ∈ gdom` of
`f z₀`, has a holomorphic lift `ψ` on `U` with `ψ z₀ = e₀`, `g ∘ ψ = f`,
`ψ(U) ⊆ gdom ∖ Kset` and `deriv g (ψ z) ≠ 0` on `U`.

The proof is the standard monodromy argument:
* the covering map produces a *continuous* lift `F : U → gdom ∩ {g ≠ critVal}`
  (`IsCoveringMapOn.existsUnique_continuousMap_lifts`, `U` simply connected and locally path
  connected);
* `F` is holomorphic because it is locally of the form (local inverse of `g`) ∘ `f`
  (`Work.L61.Branch.analyticAt_of_lift`);
* the derivative of `g` does not vanish on the lift, because `g` has the single critical value
  `critVal = π v` (`Work.L61.Branch.deriv_eq_zero_imp_critVal`).
-/

namespace Work.L61.Branch

open MandelDim Set Function Filter
open scoped Topology

noncomputable section


theorem exists_branch {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀} (hd : MandelDim.HornData d)
    (hcov : IsCoveringMapOn (fun ζ : {ζ : ℂ // ζ ∈ Work.L61.gdom d hd ∧ Work.L61.g d ζ ≠ Work.L61.critVal hd} =>
      Work.L61.g d ζ) (Work.L61.Kset d hd)ᶜ)
    {U : Set ℂ} (hUo : IsOpen U) (hUsc : IsSimplyConnected U)
    {f : ℂ → ℂ} (hfhol : DifferentiableOn ℂ f U) (hfK : ∀ z ∈ U, f z ∉ Work.L61.Kset d hd)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {e₀ : ℂ} (he₀ : Work.L61.g d e₀ = f z₀)
    (he₀d : e₀ ∈ Work.L61.gdom d hd) :
    ∃ ψ : ℂ → ℂ, ψ z₀ = e₀ ∧ (∀ z ∈ U, Work.L61.g d (ψ z) = f z) ∧ DifferentiableOn ℂ ψ U ∧
      (∀ z ∈ U, ψ z ∈ Work.L61.gdom d hd) ∧ (∀ z ∈ U, ψ z ∉ Work.L61.Kset d hd) ∧
      (∀ z ∈ U, deriv (Work.L61.g d) (ψ z) ≠ 0) := by
  classical
  have hU_lpc : LocallyPathConnectedSpace U := hUo.locallyPathConnectedSpace
  have hU_sc : SimplyConnectedSpace U := hUsc.simplyConnectedSpace
  -- the base point is not the critical value
  have hcrit : Work.L61.g d e₀ ≠ Work.L61.critVal hd := by
    intro hc
    refine hfK z₀ hz₀ ?_
    rw [← he₀, hc]
    exact Work.L61.critVal_mem_Kset d hd
  -- ## the continuous lift
  have hcont : ContinuousOn f U := hfhol.continuousOn
  let fCM : C(U, ℂ) := ⟨U.domRestrict f, continuousOn_iff_continuous_domRestrict.mp hcont⟩
  have hflift : ∀ a : U, fCM a ∈ (Work.L61.Kset d hd)ᶜ := fun a => hfK a.1 a.2
  obtain ⟨F, ⟨hF0, hFcomp⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts fCM (a₀ := ⟨z₀, hz₀⟩)
      (e₀ := ⟨e₀, he₀d, hcrit⟩) (by simpa [fCM] using he₀) hflift
  let ψ : ℂ → ℂ := fun z => if hz : z ∈ U then (F ⟨z, hz⟩ : ℂ) else 0
  have hψz₀ : ψ z₀ = e₀ := by
    simp only [ψ, dite_eq_left hz₀]
    exact congrArg Subtype.val hF0
  have hψcomp : ∀ z ∈ U, Work.L61.g d (ψ z) = f z := by
    intro z hz
    simp only [ψ, dite_eq_left hz]
    exact congrFun hFcomp ⟨z, hz⟩
  have hψcont : ContinuousOn ψ U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h₁ : U.domRestrict ψ = fun z : U => (F z : ℂ) := by
      funext z
      simp only [Set.domRestrict, ψ, dite_eq_left z.2]
    rw [h₁]
    exact continuous_subtype_val.comp F.continuous
  have hψgdom : ∀ z ∈ U, ψ z ∈ Work.L61.gdom d hd := by
    intro z hz
    simp only [ψ, dite_eq_left hz]
    exact (F ⟨z, hz⟩).2.1
  have hψKset : ∀ z ∈ U, ψ z ∉ Work.L61.Kset d hd := by
    intro z hz hmem
    have h2 : Work.L61.g d (ψ z) ∈ Work.L61.Kset d hd := Work.L61.mapsTo_Kset d hd hmem
    rw [hψcomp z hz] at h2
    exact hfK z hz h2
  have hψne_zero : ∀ z ∈ U, ψ z ≠ 0 := by
    intro z hz h0
    have h0K : (0 : ℂ) ∈ Work.L61.Kset d hd := Work.L61.zero_mem_Kset d hd
    rw [← h0] at h0K
    exact hψKset z hz h0K
  -- ## the derivative never vanishes on the lift
  have hderiv_ne : ∀ z ∈ U, deriv (Work.L61.g d) (ψ z) ≠ 0 := by
    intro z hz hder
    have hcritval : Work.L61.g d (ψ z) = Work.L61.critVal hd :=
      deriv_eq_zero_imp_critVal hd (hψgdom z hz) (hψne_zero z hz) hder
    have hmem : Work.L61.g d (ψ z) ∈ Work.L61.Kset d hd := by
      rw [hcritval]
      exact Work.L61.critVal_mem_Kset d hd
    rw [hψcomp z hz] at hmem
    exact hfK z hz hmem
  refine ⟨ψ, hψz₀, hψcomp, ?_, hψgdom, hψKset, hderiv_ne⟩
  -- ## holomorphy
  intro z hz
  have hgan : AnalyticAt ℂ (Work.L61.g d) (ψ z) :=
    (show DifferentiableOn ℂ (Work.L61.g d) (Work.L61.gdom d hd) from hd.g_holo).analyticAt
      ((Work.L61.Push.gdom_open_ball hd).1.mem_nhds (hψgdom z hz))
  have hfan : AnalyticAt ℂ f z := hfhol.analyticAt (hUo.mem_nhds hz)
  have hψan : AnalyticAt ℂ ψ z :=
    analyticAt_of_lift hUo hz hgan (hderiv_ne z hz) hfan hψcomp hψcont rfl
  exact hψan.differentiableAt.differentiableWithinAt

end

end Work.L61.Branch
