import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.balayageBridge

/-!
# The maximum principle on a relatively compact *preconnected* region

`Submission.SubharmonicOnX.le_of_frontier_limsup` (in `Submission/MaxPrincipleRegion.lean`)
proves the limsup form of the maximum principle on a relatively compact open set `U` of a
Riemann surface, under the hypothesis that the *whole* surface `X` is preconnected.

The present lemma removes that global hypothesis: the proof only ever uses the preconnectedness
of the level set argument *inside* `U`, so it suffices to assume `IsPreconnected U`.  Concretely,
in the proof below the set `S = {v = M} ∩ U` is shown to be clopen in `X` (in the case where
`closure S` misses `frontier U`), and `IsPreconnected.subset_isClopen` applied to the
preconnected set `U` then forces `S = U` — so that `U` is clopen, hence `frontier U = ∅`,
contradicting `hne`.  Every other step of the argument is local and unchanged.
-/

open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Filter Set Classical

namespace Work.SimplyConnected.ABS

theorem le_of_frontier_limsup_preconnected_region {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : Set X} (hU : IsOpen U) (hUpc : IsPreconnected U) {v : X → ℝ}
    (hv : Submission.SubharmonicOnX v U) (hcomp : IsCompact (closure U))
    (hne : (frontier U).Nonempty) {a : ℝ}
    (hlim : ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in nhdsWithin ξ U, v z ≤ a + ε) :
    ∀ z ∈ U, v z ≤ a := by
  rintro z₀ hz₀
  by_contra hcon
  simp only [not_le] at hcon
  have hza : a < v z₀ := hcon
  set δ : ℝ := (v z₀ - a) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδle : a + δ ≤ v z₀ := by rw [hδdef]; linarith
  set A : Set X := {z : X | z ∈ U ∧ a + δ ≤ v z} with hAdef
  have hz₀A : z₀ ∈ A := ⟨hz₀, hδle⟩
  have hAne : A.Nonempty := ⟨z₀, hz₀A⟩
  have hAU : A ⊆ U := fun z hz => hz.1
  have hAsub : A ⊆ closure U := fun z hz => subset_closure hz.1
  -- `A` is closed in `X`
  have hAclosed : IsClosed A := by
    rw [← closure_subset_iff_isClosed]
    intro x hx
    by_cases hxU : x ∈ U
    · have hcont : ContinuousAt v x := (hv.2 x hxU).continuousAt
      haveI : NeBot (𝓝[A] x) := (mem_closure_iff_nhdsWithin_neBot).mp hx
      have henv : ∀ᶠ z in 𝓝[A] x, a + δ ≤ v z :=
        Filter.mem_of_superset self_mem_nhdsWithin (fun z hz => hz.2)
      have hT : Tendsto (fun z : X => -v z) (𝓝[A] x) (𝓝 (-(v x))) :=
        hcont.neg.tendsto.mono_left nhdsWithin_le_nhds
      have henv' : ∀ᶠ z in 𝓝[A] x, -v z ≤ -(a + δ) :=
        henv.mono (fun z hz => neg_le_neg hz)
      have h1 : -(v x) ≤ -(a + δ) := le_of_tendsto hT henv'
      exact ⟨hxU, by linarith⟩
    · exfalso
      have hxfront : x ∈ frontier U := by
        have hxUcl : x ∈ closure U := closure_mono hAU hx
        refine ⟨hxUcl, fun hxint => hxU (interior_subset hxint)⟩
      have hlim' := hlim x hxfront (δ / 2) (by linarith)
      haveI : NeBot (𝓝[A] x) := (mem_closure_iff_nhdsWithin_neBot).mp hx
      have hlim'' : ∀ᶠ z in 𝓝[A] x, v z ≤ a + δ / 2 :=
        Filter.le_def.mp (nhdsWithin_mono x hAU) _ hlim'
      have h2 : ∀ᶠ z in 𝓝[A] x, z ∈ A ∧ v z ≤ a + δ / 2 :=
        (show ∀ᶠ z in 𝓝[A] x, z ∈ A from self_mem_nhdsWithin).and hlim''
      obtain ⟨z, hzA, hzle⟩ := h2.exists
      have hzge : a + δ ≤ v z := hzA.2
      linarith
  -- `v` attains its maximum on `A`, and that maximum is the maximum over `U`
  have hAcomp : IsCompact A :=
    IsCompact.of_isClosed_subset hcomp hAclosed hAsub
  obtain ⟨p, hpA, hpMax⟩ := hAcomp.exists_isMaxOn hAne (hv.1.mono hAU)
  set M : ℝ := v p with hMdef
  have hAle : a + δ ≤ M := by rw [hMdef]; exact hpA.2
  have hleM : ∀ z ∈ U, v z ≤ M := by
    intro z hz
    by_cases hzA : z ∈ A
    · exact hpMax hzA
    · have hlt : v z < a + δ := not_le.mp (fun h => hzA ⟨hz, h⟩)
      rw [hMdef]; linarith
  -- the level set `S = {v = M} ∩ U` is open in `X`
  set S : Set X := {z : X | z ∈ U ∧ v z = M} with hSdef
  have hpS : p ∈ S := ⟨hpA.1, by rw [hMdef]⟩
  have hSne : S.Nonempty := ⟨p, hpS⟩
  have hSU : S ⊆ U := fun z hz => hz.1
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hzS
    obtain ⟨V, hVn, hVeq⟩ := Submission.SubharmonicOnXAt.eqOn_of_le (hv.2 z hzS.1)
      (hU.mem_nhds hzS.1) (fun y hy => by simpa [hzS.2] using hleM y hy)
    exact Filter.mem_of_superset (inter_mem hVn (hU.mem_nhds hzS.1))
      (fun y hy => ⟨hy.2, by rw [hVeq y hy.1, hzS.2]⟩)
  have hclU : closure U = U ∪ frontier U := by
    rw [closure_eq_interior_union_frontier, hU.interior_eq]
  by_cases hcl : closure S ∩ frontier U = ∅
  · -- `S` is clopen in `X`; preconnectedness of `U` forces `S = U`, so `U` is clopen
    have hcl_sub : closure S ⊆ U := by
      intro x hx
      have hxUcl : x ∈ closure U := closure_mono hSU hx
      rw [hclU] at hxUcl
      rcases hxUcl with h | h
      · exact h
      · have : x ∈ (∅ : Set X) := by rw [← hcl]; exact ⟨hx, h⟩
        exact this.elim
    have hSclosedX : IsClosed S := by
      rw [← closure_subset_iff_isClosed]
      intro x hx
      have hxU : x ∈ U := hcl_sub hx
      haveI : NeBot (𝓝[S] x) := (mem_closure_iff_nhdsWithin_neBot).mp hx
      have hT : Tendsto v (𝓝[S] x) (𝓝 (v x)) :=
        ((hv.2 x hxU).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
      have henv : ∀ᶠ z in 𝓝[S] x, v z = M :=
        Filter.mem_of_superset self_mem_nhdsWithin (fun z hz => hz.2)
      have hT2 : Tendsto v (𝓝[S] x) (𝓝 M) :=
        tendsto_const_nhds.congr' (henv.mono fun z hz => hz.symm)
      have hM : v x = M := tendsto_nhds_unique hT hT2
      exact ⟨hxU, hM⟩
    have hUS : U ⊆ S :=
      hUpc.subset_isClopen ⟨hSclosedX, hSopen⟩ ⟨p, hpS.1, hpS⟩
    have hSeq : S = U := Subset.antisymm hSU hUS
    have hUclosed : IsClosed U := hSeq ▸ hSclosedX
    have hfront : frontier U = ∅ := IsClopen.frontier_eq ⟨hUclosed, hU⟩
    exact hne.ne_empty hfront
  · -- a frontier point of `U` in the closure of `S` contradicts the boundary condition
    obtain ⟨ξ, hξ⟩ := Set.nonempty_iff_ne_empty.mpr hcl
    have hξcl : ξ ∈ closure S := hξ.1
    have hξfront : ξ ∈ frontier U := hξ.2
    have hlim' := hlim ξ hξfront ((M - a) / 2) (by linarith)
    haveI : NeBot (𝓝[S] ξ) := (mem_closure_iff_nhdsWithin_neBot).mp hξcl
    have hlim'' : ∀ᶠ z in 𝓝[S] ξ, v z ≤ a + (M - a) / 2 :=
      Filter.le_def.mp (nhdsWithin_mono ξ hSU) _ hlim'
    have henv : ∀ᶠ z in 𝓝[S] ξ, v z = M :=
      Filter.mem_of_superset self_mem_nhdsWithin (fun z hz => hz.2)
    have h3 : ∀ᶠ z in 𝓝[S] ξ, M ≤ a + (M - a) / 2 :=
      (henv.and hlim'').mono (fun z hz => by linarith [hz.1, hz.2])
    obtain ⟨z, hz⟩ := h3.exists
    linarith

end Work.SimplyConnected.ABS
