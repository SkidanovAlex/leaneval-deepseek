import Mathlib
import Submission.Work.Collar3D.Chart.Equiv

namespace Work.Collar3D.Chart

open Set
open Work.Collar3D

set_option linter.style.haveILetI false

/-- **Continuity of the chart-supported extension.**  Let `U ⊆ ℝ³` be open, `Φ : U ≃ₜ M` a chart
of `ℝ³`, and `g : M ≃ₜ M` a homeomorphism of the model which is the identity outside a set `S`
whose `Φ`-preimage in `ℝ³` is closed; then the map which is `Φ.symm ∘ g ∘ Φ` on `U` and the
identity outside `U` is continuous. -/
theorem chartToFun_continuous {M : Type*} [TopologicalSpace M] (U : Set R3) (hU : IsOpen U)
    (Φ : U ≃ₜ M) (g : M ≃ₜ M) {S : Set M} (hS : IsClosed (chartSupport U Φ S))
    (hg : ∀ y : M, y ∉ S → g y = y) :
    Continuous (chartToFun U Φ g) := by
  -- The model is Hausdorff because it is homeomorphic to a subspace of `ℝ³`.
  haveI : T2Space M := Φ.t2Space
  set K : Set R3 := chartSupport U Φ S with hKdef
  have hKsub : K ⊆ U := chartSupport_subset U Φ S
  have hKcl : IsClosed K := by rw [hKdef]; exact hS
  -- The chart conjugate `Φ.symm ∘ g ∘ Φ`, a homeomorphism of `U`.
  set ψ : U ≃ₜ U := (Φ.trans g).trans Φ.symm with hψ
  have hψapp : ∀ u : U, ψ u = Φ.symm (g (Φ u)) := by
    intro u; rw [hψ]; rfl
  -- `chartToFun` agrees with `ψ` (coerced to `ℝ³`) on the closed support `K`.
  have h1 : ContinuousOn (chartToFun U Φ g) K := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hj : Continuous (fun x : K => (⟨(x : R3), hKsub x.2⟩ : U)) :=
      Continuous.subtype_mk continuous_subtype_val (fun x => hKsub x.2)
    have hcc : Continuous (fun x : K => ((ψ ⟨(x : R3), hKsub x.2⟩ : U) : R3)) :=
      continuous_subtype_val.comp (ψ.continuous.comp hj)
    have hEq : K.domRestrict (chartToFun U Φ g) =
        fun x : K => ((ψ ⟨(x : R3), hKsub x.2⟩ : U) : R3) := by
      funext x
      rw [Set.domRestrict_apply, chartToFun_of_mem (hKsub x.2), hψapp]
    rw [hEq]; exact hcc
  -- `chartToFun` is the identity on the closure of the complement of `K`.
  have hfix : EqOn (chartToFun U Φ g) id (closure Kᶜ) := by
    intro x hxcl
    by_cases hxK : x ∈ K
    · rw [chartToFun_of_mem (hKsub hxK)]
      -- It suffices that `g` fixes `Φ x`, which is a limit of points outside `S`.
      have hz : Φ ⟨x, hKsub hxK⟩ ∈ closure Sᶜ := by
        have hAe : Φ '' {u : U | (u : R3) ∈ Kᶜ} = Sᶜ := by
          ext m; constructor
          · rintro ⟨u, hu, rfl⟩
            intro hmS
            exact hu (by rw [mem_chartSupport]; exact ⟨u.2, hmS⟩)
          · intro hm
            refine ⟨Φ.symm m, ?_, Homeomorph.apply_symm_apply Φ m⟩
            intro hK
            rw [mem_chartSupport] at hK
            obtain ⟨hxU, hxS⟩ := hK
            have : (⟨((Φ.symm m : U) : R3), hxU⟩ : U) = Φ.symm m := Subtype.ext rfl
            rw [this, Homeomorph.apply_symm_apply] at hxS
            exact hm hxS
        have hAU : (⟨x, hKsub hxK⟩ : U) ∈ closure {u : U | (u : R3) ∈ Kᶜ} := by
          rw [closure_subtype]
          have hset : Subtype.val '' {u : U | (u : R3) ∈ Kᶜ} = U ∩ Kᶜ := by
            ext y; constructor
            · rintro ⟨u, hu, rfl⟩; exact ⟨u.2, hu⟩
            · rintro ⟨hyU, hyK⟩; exact ⟨⟨y, hyU⟩, hyK, rfl⟩
          rw [hset, mem_closure_iff]
          intro o ho hxo
          rw [← inter_assoc]
          exact mem_closure_iff.mp hxcl (o ∩ U) (ho.inter hU) ⟨hxo, hKsub hxK⟩
        have hmem : Φ ⟨x, hKsub hxK⟩ ∈ Φ '' closure {u : U | (u : R3) ∈ Kᶜ} :=
          ⟨⟨x, hKsub hxK⟩, hAU, rfl⟩
        rw [Homeomorph.image_closure, hAe] at hmem
        exact hmem
      have hgz : g (Φ ⟨x, hKsub hxK⟩) = Φ ⟨x, hKsub hxK⟩ := by
        have hne : (nhdsWithin (Φ ⟨x, hKsub hxK⟩) Sᶜ).NeBot :=
          mem_closure_iff_nhdsWithin_neBot.mp hz
        refine tendsto_nhds_unique' (f := g) hne ?_ ?_
        · exact (g.continuous.continuousAt).mono_left nhdsWithin_le_nhds
        · have heq : id =ᶠ[nhdsWithin (Φ ⟨x, hKsub hxK⟩) Sᶜ] g :=
            Filter.eventuallyEq_iff_exists_mem.mpr
              ⟨Sᶜ, self_mem_nhdsWithin, fun y hy => (hg y hy).symm⟩
          exact Filter.Tendsto.congr' heq
            ((Filter.tendsto_id : Filter.Tendsto id _ _).mono_right nhdsWithin_le_nhds)
      rw [hgz, Homeomorph.symm_apply_apply]
      rfl
    · exact chartToFun_eq_self_of_notMem_support U Φ hg hxK
  have h2 : ContinuousOn (chartToFun U Φ g) (closure Kᶜ) :=
    ContinuousOn.congr continuousOn_id hfix
  have hunion : K ∪ closure Kᶜ = univ := by
    rw [eq_univ_iff_forall]
    intro x
    by_cases h : x ∈ K
    · exact Or.inl h
    · exact Or.inr (subset_closure h)
  have hc : ContinuousOn (chartToFun U Φ g) (K ∪ closure Kᶜ) :=
    ContinuousOn.union_of_isClosed h1 h2 hKcl isClosed_closure
  rw [← continuousOn_univ, ← hunion]
  exact hc

end Work.Collar3D.Chart
