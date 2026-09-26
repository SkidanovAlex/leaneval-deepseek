import Mathlib
import Submission.Work.Collar3D.Chart.Equiv

namespace Work.Collar3D.Chart

open Set
open Work.Collar3D

set_option linter.style.haveILetI false

/-- **Joint continuity of a chart-supported family of extensions.**  Let `U ⊆ ℝ³` be open,
`Φ : U ≃ₜ M` a chart, and `g : ℝ → M ≃ₜ M` a continuous family of homeomorphisms of the model,
each of which is the identity outside a fixed set `S` whose `Φ`-preimage is closed.  Then
`(t,x) ↦ chartToFun U Φ (g t) x` is continuous. -/
theorem chartToFun_family_continuous {M : Type*} [TopologicalSpace M] (U : Set R3) (hU : IsOpen U)
    (Φ : U ≃ₜ M) (g : ℝ → M ≃ₜ M) {S : Set M} (hS : IsClosed (chartSupport U Φ S))
    (hg : ∀ (t : ℝ) (y : M), y ∉ S → g t y = y)
    (hcont : Continuous fun p : ℝ × M => g p.1 p.2) :
    Continuous (fun p : ℝ × R3 => chartToFun U Φ (g p.1) p.2) := by
  -- The model is Hausdorff because it is homeomorphic to a subspace of `ℝ³`.
  haveI : T2Space M := Φ.t2Space
  set K : Set R3 := chartSupport U Φ S with hKdef
  have hKsub : K ⊆ U := chartSupport_subset U Φ S
  have hKcl : IsClosed K := by rw [hKdef]; exact hS
  set F : ℝ × R3 → R3 := (fun p => chartToFun U Φ (g p.1) p.2) with hFdef
  -- Key pointwise fact: on the closure of the complement of the support, `F t` is the identity.
  have hfixpt : ∀ (t : ℝ) (x : R3), x ∈ closure Kᶜ → chartToFun U Φ (g t) x = x := by
    intro t x hxcl
    by_cases hxU : x ∈ U
    · -- `Φ x` lies in the closure of `Sᶜ`.
      have hAe : Φ '' {u : U | (u : R3) ∈ Kᶜ} = Sᶜ := by
        ext m; constructor
        · rintro ⟨u, hu, rfl⟩
          intro hmS
          exact hu (by rw [mem_chartSupport]; exact ⟨u.2, hmS⟩)
        · intro hm
          refine ⟨Φ.symm m, ?_, Homeomorph.apply_symm_apply Φ m⟩
          intro hKc
          rw [mem_chartSupport] at hKc
          obtain ⟨hxU', hxS⟩ := hKc
          have h1 : (⟨((Φ.symm m : U) : R3), hxU'⟩ : U) = Φ.symm m := Subtype.ext rfl
          rw [h1, Homeomorph.apply_symm_apply] at hxS
          exact hm hxS
      have hAU : (⟨x, hxU⟩ : U) ∈ closure {u : U | (u : R3) ∈ Kᶜ} := by
        rw [closure_subtype]
        have hset : Subtype.val '' {u : U | (u : R3) ∈ Kᶜ} = U ∩ Kᶜ := by
          ext y; constructor
          · rintro ⟨u, hu, rfl⟩; exact ⟨u.2, hu⟩
          · rintro ⟨hyU, hyK⟩; exact ⟨⟨y, hyU⟩, hyK, rfl⟩
        rw [hset, mem_closure_iff]
        intro o ho hxo
        rw [← inter_assoc]
        exact mem_closure_iff.mp hxcl (o ∩ U) (ho.inter hU) ⟨hxo, hxU⟩
      have hz : Φ ⟨x, hxU⟩ ∈ closure Sᶜ := by
        have hmem : Φ ⟨x, hxU⟩ ∈ Φ '' closure {u : U | (u : R3) ∈ Kᶜ} :=
          ⟨⟨x, hxU⟩, hAU, rfl⟩
        rw [Homeomorph.image_closure, hAe] at hmem
        exact hmem
      -- A continuous function which fixes `Sᶜ` pointwise fixes its closure.
      have hgz : g t (Φ ⟨x, hxU⟩) = Φ ⟨x, hxU⟩ :=
        Set.EqOn.closure (f := g t) (g := id) (fun y hy => hg t y hy)
          (g t).continuous continuous_id hz
      rw [chartToFun_of_mem hxU, hgz, Homeomorph.symm_apply_apply]
    · exact chartToFun_of_notMem hxU
  -- `F` agrees with the chart conjugate on `univ ×ˢ K`, hence is continuous there.
  have h1 : ContinuousOn F (univ ×ˢ K) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : (univ ×ˢ K).domRestrict F =
        fun p : ↥(univ ×ˢ K) =>
          (Φ.symm (g p.1.1 (Φ ⟨p.1.2, hKsub p.2.2⟩)) : R3) := by
      funext p
      simp only [hFdef, Set.domRestrict_apply, chartToFun_of_mem (hKsub p.2.2)]
    rw [hEq]
    exact (continuous_subtype_val.comp (Homeomorph.continuous Φ.symm)).comp
      (hcont.comp (Continuous.prodMk continuous_subtype_val.fst
        ((Homeomorph.continuous Φ).comp
          (Continuous.subtype_mk continuous_subtype_val.snd (fun p => hKsub p.2.2)))))
  -- On `univ ×ˢ closure Kᶜ`, `F` is the second projection.
  have h2 : ContinuousOn F (univ ×ˢ closure Kᶜ) := by
    refine ContinuousOn.congr continuous_snd.continuousOn ?_
    intro p hp
    exact hfixpt p.1 p.2 hp.2
  -- The two closed pieces cover `ℝ × ℝ³`.
  have hKunion : K ∪ closure Kᶜ = univ := by
    rw [eq_univ_iff_forall]
    intro x
    by_cases h : x ∈ K
    · exact Or.inl h
    · exact Or.inr (subset_closure h)
  have hunion : (univ : Set ℝ) ×ˢ K ∪ (univ : Set ℝ) ×ˢ closure Kᶜ = univ := by
    ext p; constructor
    · intro _; exact mem_univ _
    · intro _
      have hp : p.2 ∈ K ∪ closure Kᶜ := by rw [hKunion]; exact mem_univ _
      rcases hp with hp | hp
      · exact Or.inl ⟨mem_univ _, hp⟩
      · exact Or.inr ⟨mem_univ _, hp⟩
  have hc : ContinuousOn F (univ ×ˢ K ∪ univ ×ˢ closure Kᶜ) :=
    ContinuousOn.union_of_isClosed h1 h2 (isClosed_univ.prod hKcl)
      (isClosed_univ.prod isClosed_closure)
  rw [hunion] at hc
  exact continuousOn_univ.mp hc

end Work.Collar3D.Chart
