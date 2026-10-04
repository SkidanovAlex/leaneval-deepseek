import Mathlib.Analysis.ODE.ExistUnique

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.Analysis.ODE

open Filter Set
open scoped Topology

/-- **Uniqueness for the second-order ODE `u'' = G(u,u')` on a whole interval.**

Two solutions of the first-order system `u' = v`, `v' = G (u, v)` on the same interval
`Set.Ioo (-ε) ε` that agree in value and derivative at `0` agree on the whole interval, provided
`G` is `C¹` at the points `(u₁ t, v₁ t)` of the first solution (this is all that the standard
open-and-closed argument needs; in particular it applies to a chart geodesic spray, which is only
`C¹` on the chart, not on all of `E × E`).

Suggested proof: the set `s := {t ∈ Set.Ioo (-ε) ε | u₁ t = u₂ t}` contains `0`, is open by the
local uniqueness lemma `Commons.Analysis.ODE.secondOrderODE_solution_unique` (applied to the
time-shifted solutions at a point of `s`), and is closed in `Set.Ioo (-ε) ε` by continuity of
`u₁` and `u₂`; as `Set.Ioo (-ε) ε` is preconnected, `s` is everything. -/
theorem secondOrderODE_eqOn_of_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {G : E × E → E} {u₁ v₁ u₂ v₂ : ℝ → E} {ε : ℝ} (hε : 0 < ε)
    (h0 : u₁ 0 = u₂ 0 ∧ v₁ 0 = v₂ 0)
    (hG : ∀ t ∈ Set.Ioo (-ε) ε, ContDiffAt ℝ 1 G (u₁ t, v₁ t))
    (h₁ : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt u₁ (v₁ t) t ∧ HasDerivAt v₁ (G (u₁ t, v₁ t)) t)
    (h₂ : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt u₂ (v₂ t) t ∧ HasDerivAt v₂ (G (u₂ t, v₂ t)) t) :
    Set.EqOn u₁ u₂ (Set.Ioo (-ε) ε) := by
  classical
  set X : Set ℝ := Set.Ioo (-ε) ε with hXdef
  -- Local uniqueness of the first-order system `(u, v)' = (v, G(u,v))` around any point where
  -- the two solutions agree.
  have key : ∀ t₀ ∈ X, (u₁ t₀, v₁ t₀) = (u₂ t₀, v₂ t₀) →
      (fun t : ℝ => (u₁ t, v₁ t)) =ᶠ[𝓝 t₀] (fun t : ℝ => (u₂ t, v₂ t)) := by
    intro t₀ ht₀ heq
    set F : E × E → E × E := fun z => (z.2, G z) with hFdef
    have hFt₀ : ContDiffAt ℝ 1 F (u₁ t₀, v₁ t₀) := by
      rw [hFdef]
      exact (contDiffAt_snd (𝕜 := ℝ) (n := 1) (p := (u₁ t₀, v₁ t₀))).prodMk (hG t₀ ht₀)
    obtain ⟨K, s, hs, hlip⟩ := hFt₀.exists_lipschitzOnWith
    have hs₂ : s ∈ 𝓝 (u₂ t₀, v₂ t₀) := by rw [← heq]; exact hs
    refine ODE_solution_unique_of_eventually (v := fun _ => F) (s := fun _ => s) (K := K)
      (f := fun t => (u₁ t, v₁ t)) (g := fun t => (u₂ t, v₂ t)) (t₀ := t₀)
      (Eventually.of_forall fun _ => hlip) ?_ ?_ heq
    · have hc : ContinuousAt (fun t : ℝ => (u₁ t, v₁ t)) t₀ :=
        ((h₁ t₀ ht₀).1.prodMk (h₁ t₀ ht₀).2).continuousAt
      filter_upwards [Ioo_mem_nhds ht₀.1 ht₀.2, hc.eventually hs] with t ht hmem
      exact ⟨(h₁ t ht).1.prodMk (h₁ t ht).2, hmem⟩
    · have hc : ContinuousAt (fun t : ℝ => (u₂ t, v₂ t)) t₀ :=
        ((h₂ t₀ ht₀).1.prodMk (h₂ t₀ ht₀).2).continuousAt
      filter_upwards [Ioo_mem_nhds ht₀.1 ht₀.2, hc.eventually hs₂] with t ht hmem
      exact ⟨(h₂ t ht).1.prodMk (h₂ t ht).2, hmem⟩
  -- `X` is preconnected.
  haveI : PreconnectedSpace X :=
    isPreconnected_iff_preconnectedSpace.mp (isPreconnected_Ioo (a := -ε) (b := ε))
  -- The set where the two first-order systems agree.
  set S : Set X := {x | (u₁ (x : ℝ), v₁ (x : ℝ)) = (u₂ (x : ℝ), v₂ (x : ℝ))} with hSdef
  have hne : S.Nonempty := by
    refine ⟨⟨0, ?_⟩, ?_⟩
    · exact ⟨by linarith, hε⟩
    · exact Prod.ext h0.1 h0.2
  have hcu₁ : Continuous (fun x : X => u₁ (x : ℝ)) :=
    continuousOn_iff_continuous_domRestrict.mp
      (fun t ht => (h₁ t ht).1.continuousAt.continuousWithinAt)
  have hcv₁ : Continuous (fun x : X => v₁ (x : ℝ)) :=
    continuousOn_iff_continuous_domRestrict.mp
      (fun t ht => (h₁ t ht).2.continuousAt.continuousWithinAt)
  have hcu₂ : Continuous (fun x : X => u₂ (x : ℝ)) :=
    continuousOn_iff_continuous_domRestrict.mp
      (fun t ht => (h₂ t ht).1.continuousAt.continuousWithinAt)
  have hcv₂ : Continuous (fun x : X => v₂ (x : ℝ)) :=
    continuousOn_iff_continuous_domRestrict.mp
      (fun t ht => (h₂ t ht).2.continuousAt.continuousWithinAt)
  have hclosed : IsClosed S := by
    have h1 : IsClosed {x : X | u₁ (x : ℝ) = u₂ (x : ℝ)} := isClosed_eq hcu₁ hcu₂
    have h2 : IsClosed {x : X | v₁ (x : ℝ) = v₂ (x : ℝ)} := isClosed_eq hcv₁ hcv₂
    have heqS : S = {x : X | u₁ (x : ℝ) = u₂ (x : ℝ)} ∩
        {x : X | v₁ (x : ℝ) = v₂ (x : ℝ)} := by
      ext x; constructor
      · intro h; exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
    rw [heqS]; exact h1.inter h2
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨W, hWl, hWT⟩ := (key (x : ℝ) x.2 hx).exists_mem
    obtain ⟨U, hUW, hUopen, hxU⟩ := mem_nhds_iff.mp hWl
    refine mem_of_superset (IsOpen.mem_nhds (hUopen.preimage continuous_subtype_val) hxU) ?_
    intro y hy
    exact hWT (hUW hy)
  have hS : S = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hne
  intro t ht
  have : (⟨t, ht⟩ : X) ∈ S := by rw [hS]; exact Set.mem_univ _
  exact congrArg Prod.fst this

end Commons.Analysis.ODE