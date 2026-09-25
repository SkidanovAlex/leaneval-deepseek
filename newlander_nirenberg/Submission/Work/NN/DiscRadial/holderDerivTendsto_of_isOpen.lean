import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Final.holderDerivTendsto

noncomputable section

open scoped NNReal ENNReal

namespace Work.NN.DiscRadial

open scoped Topology
open Set Filter Metric

/-- **One-sided continuity of the iterated derivatives on an open set.**  If `g : E → ℂ` has
finite `C^{k,α}` norm on an open set `Ω ⊆ E` with `α > 0`, then for every `i ≤ k` the `i`-th
iterated Fréchet derivative of `g` has a limit at every point `p` of the closure of `Ω`, as one
approaches `p` inside `Ω`.

The reason is that the finite Hölder seminorm at order `i` makes `x ↦ D^i g(x)` Hölder
continuous on `Ω`, hence uniformly continuous; a uniformly continuous map on a set with values in
a complete space has a limit at every point of the closure of the set. -/
theorem holderDerivTendsto_of_isOpen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} (hα : 0 < α) {k : ℕ} {Ω : Set E} (hΩ : IsOpen Ω) (g : E → ℂ)
    (hfin : Work.CR.Flat.holderNorm k α g Ω ≠ ⊤)
    {i : ℕ} (hi : i ≤ k) {p : E} (hp : p ∈ closure Ω) :
    ∃ L : ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℂ,
      Filter.Tendsto (fun x : E => iteratedFDeriv ℝ i g x) (𝓝[Ω] p) (𝓝 L) := by
  set C : ℝ := (Work.CR.Flat.holderNorm k α g Ω).toReal with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; exact ENNReal.toReal_nonneg
  -- the `i`-th iterated derivatives are Hölder on `Ω`
  have hholder : ∀ x ∈ Ω, ∀ y ∈ Ω,
      dist (iteratedFDeriv ℝ i g x) (iteratedFDeriv ℝ i g y) ≤ C * dist x y ^ α := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy
      simp [dist_self, Real.zero_rpow hα.ne']
    · have hxd : iteratedFDerivWithin ℝ i g Ω x = iteratedFDeriv ℝ i g x :=
        iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) i hΩ hx
      have hyd : iteratedFDerivWithin ℝ i g Ω y = iteratedFDeriv ℝ i g y :=
        iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) i hΩ hy
      have hsemi := Work.CR.Flat.le_holderSeminorm i α g Ω hx hy hxy
      rw [hxd, hyd] at hsemi
      have hle : ENNReal.ofReal
          (‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ / ‖x - y‖ ^ α)
          ≤ Work.CR.Flat.holderNorm k α g Ω :=
        le_trans hsemi (Work.CR.Flat.holderSeminorm_le_holderNorm k α g Ω hi)
      have hreal : ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ / ‖x - y‖ ^ α ≤ C := by
        rw [hCdef]
        exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hle
      have hpos : 0 < ‖x - y‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      rw [dist_eq_norm, dist_eq_norm]
      exact (div_le_iff₀ hpos).mp hreal
  have hunif : UniformContinuousOn (fun x : E => iteratedFDeriv ℝ i g x) Ω :=
    Work.NN.Final.uniformContinuousOn_of_holder hα hC0 hholder
  -- the filter `𝓝[Ω] p` is Cauchy, and the derivatives are uniformly continuous on `Ω`
  have hnb : (nhdsWithin p Ω).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hCau : Cauchy (nhdsWithin p Ω) :=
    ⟨hnb,
      le_trans (Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds)
        (cauchy_nhds (a := p)).2⟩
  have hCauMap : Cauchy (Filter.map (fun x : E => iteratedFDeriv ℝ i g x) (nhdsWithin p Ω)) :=
    Cauchy.map_of_le hCau hunif (le_principal_iff.mpr self_mem_nhdsWithin)
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.mp hCauMap
  exact ⟨L, hL⟩

end Work.NN.DiscRadial
