import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option linter.unusedVariables false

namespace Commons.Topology.Jordan

open Set

/-- Injectivity of a path is preserved by reversing it (`Path.symm`). -/
private lemma injective_symm_iff {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y) :
    Function.Injective ⇑γ.symm ↔ Function.Injective ⇑γ := by
  have h : ⇑γ.symm = ⇑γ ∘ unitInterval.symm := funext (Path.symm_apply γ)
  rw [h, Function.Injective.of_comp_iff' _ unitInterval.symm_bijective]

theorem two_arcs_through (γ : C(Circle, ℂ)) (hγ : Function.Injective γ)
    (l : ℂ) (hl : l ∈ Set.range γ) (hl1 : l ≠ 1) (hlm1 : l ≠ -1)
    (h1 : (1:ℂ) ∈ Set.range γ) (hm1 : (-1:ℂ) ∈ Set.range γ) :
    ∃ P Q : Path (-1 : ℂ) 1,
      Set.range P ∪ Set.range Q = Set.range γ ∧
      Set.range P ∩ Set.range Q = {(1:ℂ), -1} ∧
      Function.Injective (⇑P) ∧ Function.Injective (⇑Q) ∧ l ∈ Set.range P := by
  obtain ⟨a, ha⟩ := hm1
  obtain ⟨b, hb⟩ := h1
  obtain ⟨c, hc⟩ := hl
  have hab : a ≠ b := by
    intro h
    rw [h] at ha
    rw [ha] at hb
    norm_num at hb
  let P : Path (-1 : ℂ) 1 := ((Circle.path a b).map γ.continuous).cast ha.symm hb.symm
  let Q : Path (-1 : ℂ) 1 := (((Circle.path b a).map γ.continuous).cast hb.symm ha.symm).symm
  have hP_range : Set.range ⇑P = γ '' Set.range ⇑(Circle.path a b) := by
    simp only [P]
    rw [Path.cast_coe, Path.map_coe, Set.range_comp]
  have hQ_range : Set.range ⇑Q = γ '' Set.range ⇑(Circle.path b a) := by
    simp only [Q]
    rw [Path.symm_range, Path.cast_coe, Path.map_coe, Set.range_comp]
  have hunion : Set.range ⇑P ∪ Set.range ⇑Q = Set.range γ := by
    rw [hP_range, hQ_range, ← Set.image_union, Circle.range_path_union_range_path hab,
      Set.image_univ]
  have hinter : Set.range ⇑P ∩ Set.range ⇑Q = {(1:ℂ), -1} := by
    rw [hP_range, hQ_range, ← Set.image_inter hγ, Circle.range_path_inter_range_path hab,
      Set.image_pair, ha, hb]
    exact Set.pair_comm _ _
  have hP_inj : Function.Injective ⇑P := by
    simp only [P]
    rw [Path.cast_coe, Path.map_coe]
    exact hγ.comp (Circle.path_injective_of_ne hab)
  have hQ_inj : Function.Injective ⇑Q := by
    simp only [Q]
    rw [injective_symm_iff, Path.cast_coe, Path.map_coe]
    exact hγ.comp (Circle.path_injective_of_ne hab.symm)
  by_cases hcP : c ∈ Set.range ⇑(Circle.path a b)
  · refine ⟨P, Q, hunion, hinter, hP_inj, hQ_inj, ?_⟩
    rw [hP_range]
    exact ⟨c, hcP, hc⟩
  · have hcQ : c ∈ Set.range ⇑(Circle.path b a) := by
      have hmem : c ∈ Set.range ⇑(Circle.path a b) ∪ Set.range ⇑(Circle.path b a) := by
        rw [Circle.range_path_union_range_path hab]
        exact Set.mem_univ c
      exact hmem.resolve_left hcP
    refine ⟨Q, P, ?_, ?_, hQ_inj, hP_inj, ?_⟩
    · rw [Set.union_comm]; exact hunion
    · rw [Set.inter_comm]; exact hinter
    · rw [hQ_range]
      exact ⟨c, hcQ, hc⟩

end Commons.Topology.Jordan