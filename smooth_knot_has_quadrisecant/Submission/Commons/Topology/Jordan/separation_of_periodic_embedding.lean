import Mathlib
import Submission.Commons.Topology.Jordan.plane_separation
import Submission.Commons.Topology.Jordan.complement_frontier_of_periodic_embedding

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

/-- A continuous `1`-periodic injection on `[0,1)` descends to an injective continuous map on the
circle, with the same range. -/
private lemma exists_injective_circle_map_range_eq
    (γ : ℝ → ℂ) (hcont : Continuous γ) (hper : Function.Periodic γ 1)
    (hinj : Set.InjOn γ (Set.Ico (0:ℝ) 1)) :
    ∃ γ' : C(Circle, ℂ), Function.Injective γ' ∧ Set.range γ' = Set.range γ := by
  classical
  haveI : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
  set γc : AddCircle (1:ℝ) → ℂ := AddCircle.liftIco (1:ℝ) 0 γ with hγcdef
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
  exact ⟨γ', hγ'inj, hrange'⟩

/-- Jordan separation for a continuous `1`-periodic injection: the complement of its image is the
disjoint union of two nonempty connected open sets, one bounded and one unbounded. -/
theorem separation_of_periodic_embedding
    (γ : ℝ → ℂ) (hcont : Continuous γ) (hper : Function.Periodic γ 1)
    (hinj : Set.InjOn γ (Set.Ico (0:ℝ) 1)) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ U ∪ V = (Set.range γ)ᶜ := by
  obtain ⟨γ', hγ'inj, hrange'⟩ := exists_injective_circle_map_range_eq γ hcont hper hinj
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hdisj, hUb, hVb, hUV⟩ := plane_separation γ' hγ'inj
  exact ⟨U, V, hUo, hVo, hUc, hVc, hdisj, hUb, hVb, by rw [hUV, hrange']⟩

end Commons.Topology.Jordan
