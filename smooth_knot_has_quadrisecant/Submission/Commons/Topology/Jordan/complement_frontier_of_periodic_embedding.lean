import Mathlib
import Submission.Commons.Topology.Jordan.plane_separation
import Submission.Commons.Topology.Connected.frontier_component_compl_range

namespace Commons.Topology.Jordan

open Set

/-- Two real numbers that differ by an integer have the same image in `AddCircle 1`. -/
private lemma addcircle_coe_fract (x : ℝ) :
    ((x : ℝ) : AddCircle (1:ℝ)) = ((Int.fract x : ℝ) : AddCircle (1:ℝ)) := by
  have hx0 : (((⌊x⌋ : ℤ) : ℝ) : AddCircle (1:ℝ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨⌊x⌋, by simp⟩
  calc ((x : ℝ) : AddCircle (1:ℝ))
      = ((Int.fract x + (⌊x⌋ : ℝ) : ℝ) : AddCircle (1:ℝ)) := by
        congr 1
        exact (Int.fract_add_floor x).symm
    _ = ((Int.fract x : ℝ) : AddCircle (1:ℝ)) + (((⌊x⌋ : ℤ) : ℝ) : AddCircle (1:ℝ)) := by
        rw [AddCircle.coe_add]
    _ = ((Int.fract x : ℝ) : AddCircle (1:ℝ)) := by rw [hx0, add_zero]

/-- For a continuous `1`-periodic parametrisation that is injective on `[0,1)`, the complement of
its image in the plane is disconnected, and every connected component of that complement has the
image as its frontier. -/
theorem complement_frontier_of_periodic_embedding
    (γ : ℝ → ℂ) (hcont : Continuous γ) (hper : Function.Periodic γ 1)
    (hinj : Set.InjOn γ (Set.Ico (0:ℝ) 1)) :
    (∃ y : ℂ, y ∈ (Set.range γ)ᶜ ∧
        connectedComponentIn (Set.range γ)ᶜ y ≠ (Set.range γ)ᶜ) ∧
      (∀ y : ℂ, y ∈ (Set.range γ)ᶜ →
        frontier (connectedComponentIn (Set.range γ)ᶜ y) = Set.range γ) := by
  classical
  haveI : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
  set γc : AddCircle (1:ℝ) → ℂ := AddCircle.liftIco (1:ℝ) 0 γ with hγcdef
  -- the descended curve agrees with `γ` on the whole line
  have hγc_coe : ∀ x : ℝ, γc ((x : ℝ) : AddCircle (1:ℝ)) = γ x := by
    intro x
    have hx : Int.fract x ∈ Set.Ico (0:ℝ) (0 + 1) :=
      ⟨Int.fract_nonneg x, by simpa using Int.fract_lt_one x⟩
    rw [addcircle_coe_fract x, hγcdef, AddCircle.liftIco_coe_apply (a := (0:ℝ)) hx]
    rw [← Function.Periodic.sub_int_mul_eq (x := x) hper ⌊x⌋, mul_one, Int.self_sub_floor]
  have hγc_cont : Continuous γc := by
    rw [hγcdef]
    exact AddCircle.liftIco_zero_continuous (p := (1:ℝ)) (f := γ)
      (by simpa using (hper 0).symm) hcont.continuousOn
  have hsurj : Function.Surjective (fun x : ℝ => (x : AddCircle (1:ℝ))) := by
    intro a
    obtain ⟨b, _, hba⟩ := AddCircle.eq_coe_Ico (p := (1:ℝ)) a
    exact ⟨b, hba⟩
  have hrangec : Set.range γc = Set.range γ := by
    have h1 : Set.range γ = Set.range (γc ∘ (fun x : ℝ => (x : AddCircle (1:ℝ)))) := by
      rw [show (γc ∘ (fun x : ℝ => (x : AddCircle (1:ℝ)))) = γ from funext hγc_coe]
    rw [h1, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
  have hγc_inj : Function.Injective γc := by
    intro u v huv
    obtain ⟨x, hx, hxu⟩ := AddCircle.eq_coe_Ico (p := (1:ℝ)) u
    obtain ⟨y, hy, hyv⟩ := AddCircle.eq_coe_Ico (p := (1:ℝ)) v
    have hxy : γ x = γ y := by
      rw [← hγc_coe x, ← hγc_coe y, hxu, hyv, huv]
    have hxyeq : x = y := hinj hx hy hxy
    rw [← hxu, ← hyv, hxyeq]
  -- transport to a continuous injection on `Circle`
  let e : AddCircle (1:ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (T := (1:ℝ)) (by norm_num)
  let γ' : C(Circle, ℂ) := ⟨fun z => γc (e.symm z), hγc_cont.comp e.symm.continuous⟩
  have hrange' : Set.range γ' = Set.range γ := by
    have h1 : Set.range γ' = Set.range γc := by
      change Set.range (fun z => γc (e.symm z)) = Set.range γc
      rw [show (fun z => γc (e.symm z)) = γc ∘ (e.symm : Circle → AddCircle (1:ℝ)) from rfl,
        Set.range_comp, Set.range_eq_univ.mpr e.symm.surjective, Set.image_univ]
    rw [h1, hrangec]
  have hγ'inj : Function.Injective γ' := by
    intro z w hzw
    change γc (e.symm z) = γc (e.symm w) at hzw
    exact e.symm.injective (hγc_inj hzw)
  -- the Jordan curve separation
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hdisj, hUb, hVb, hUV⟩ := plane_separation γ' hγ'inj
  have hUsub : U ⊆ (Set.range γ')ᶜ := fun u hu => by rw [← hUV]; exact Or.inl hu
  have hVsub : V ⊆ (Set.range γ')ᶜ := fun v hv => by rw [← hUV]; exact Or.inr hv
  have hpre' : ¬ IsPreconnected (Set.range γ')ᶜ := by
    intro hcon
    have hsub : (Set.range γ')ᶜ ⊆ U ∪ V := by rw [hUV]
    rcases hcon.subset_or_subset hUo hVo hdisj hsub with h | h
    · obtain ⟨v, hvV⟩ := hVc.nonempty
      exact (Set.disjoint_left.mp hdisj (h (hVsub hvV))) hvV
    · obtain ⟨u, huU⟩ := hUc.nonempty
      exact (Set.disjoint_left.mp hdisj huU) (h (hUsub huU))
  have hpre : ¬ IsPreconnected (Set.range γ)ᶜ := by
    rwa [hrange'] at hpre'
  refine ⟨?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨z, hzU⟩ := hUc.nonempty
    have hzC : z ∈ (Set.range γ)ᶜ := by
      rw [← hrange']
      exact hUsub hzU
    have hzpre : IsPreconnected (Set.range γ)ᶜ :=
      hcon z hzC ▸ isPreconnected_connectedComponentIn
    exact hpre hzpre
  · intro y hy
    have hy' : y ∈ (Set.range γ')ᶜ := by rwa [hrange']
    have hres := Commons.Topology.Connected.frontier_component_compl_range γ' hγ'inj hpre' y hy'
    rwa [hrange'] at hres

end Commons.Topology.Jordan
