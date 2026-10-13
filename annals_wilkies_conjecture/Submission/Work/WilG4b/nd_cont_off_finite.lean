import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4b.isCell_one_dichotomy
import Submission.Work.WilG4b.isCell_two_graph
import Submission.Work.WilG4b.continuousAt_of_graphCell

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4b
open WilkiesDesign WilkiesConjecture

theorem nd_cont_off_finite (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) :
    {x : ℝ | ¬ ContinuousAt g x}.Finite := by
  obtain ⟨a, b, c, H⟩ := hcd F 2
  obtain ⟨C, hdec, hsh, hcard, hmem⟩ :=
    H D 1 (fun _ : Fin 1 => WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)))
      (fun i => by simpa using hg)
  have hdec' : (∀ c ∈ C, WilkiesDesign.IsCell 2 c ∧ c.Nonempty) ∧
      (C : Set (Set (Fin 2 → ℝ))).PairwiseDisjoint id ∧
      (∀ z : Fin 2 → ℝ, ∃ c ∈ C, z ∈ c) ∧
      WilkiesDesign.IsCylDecomp 1 (C.image (fun c : Set (Fin 2 → ℝ) => Fin.init '' c)) := hdec
  obtain ⟨hcell2, hdisj2, hcover2, hdec1⟩ := hdec'
  have hdec1' : (∀ c ∈ C.image (fun c : Set (Fin 2 → ℝ) => Fin.init '' c),
        WilkiesDesign.IsCell 1 c ∧ c.Nonempty) ∧
      ((C.image (fun c : Set (Fin 2 → ℝ) => Fin.init '' c)) : Set (Set (Fin 1 → ℝ))).PairwiseDisjoint id ∧
      (∀ z : Fin 1 → ℝ, ∃ c ∈ C.image (fun c : Set (Fin 2 → ℝ) => Fin.init '' c), z ∈ c) ∧
      WilkiesDesign.IsCylDecomp 0
        ((C.image (fun c : Set (Fin 2 → ℝ) => Fin.init '' c)).image
          (fun c : Set (Fin 1 → ℝ) => Fin.init '' c)) := hdec1
  obtain ⟨hcell1, hdisj1, hcover1, hdec0⟩ := hdec1'
  let pt : ℝ → (Fin 2 → ℝ) := fun x => Fin.snoc (fun _ : Fin 1 => x) (g x)
  have hpt_graph : ∀ x : ℝ, pt x ∈ WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) := by
    intro x
    simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq, pt, Fin.init_snoc, Fin.snoc_last]
  let φ : ℝ → Set (Fin 2 → ℝ) := fun x => (hcover2 (pt x)).choose
  have hφ_mem : ∀ x : ℝ, φ x ∈ C := fun x => (hcover2 (pt x)).choose_spec.1
  have hφ_pt : ∀ x : ℝ, pt x ∈ φ x := fun x => (hcover2 (pt x)).choose_spec.2
  let P : Set ℝ := {x | Fin.init '' (φ x) = {fun _ : Fin 1 => x}}
  have hPfin : P.Finite := by
    refine Set.Finite.of_finite_image (s := P) (f := φ) ?_ ?_
    · refine C.finite_toSet.subset ?_
      rintro c ⟨x, hxP, rfl⟩
      exact hφ_mem x
    · intro x hx y hy hxy
      have hx1 : Fin.init '' (φ x) = {fun _ : Fin 1 => x} := hx
      have hy1 : Fin.init '' (φ y) = {fun _ : Fin 1 => y} := hy
      have hEqSet : ({fun _ : Fin 1 => x} : Set (Fin 1 → ℝ)) = {fun _ : Fin 1 => y} := by
        rw [← hx1, hxy, hy1]
      have hmem : (fun _ : Fin 1 => x) ∈ ({fun _ : Fin 1 => y} : Set (Fin 1 → ℝ)) := by
        rw [← hEqSet]; exact Set.mem_singleton _
      have hEq : (fun _ : Fin 1 => x) = (fun _ : Fin 1 => y) := Set.mem_singleton_iff.mp hmem
      simpa using congrFun hEq 0
  have hcont : ∀ x : ℝ, x ∉ P → ContinuousAt g x := by
    intro x hxP
    let κ : Set (Fin 2 → ℝ) := φ x
    have hκmem : κ ∈ C := hφ_mem x
    have hptκ : pt x ∈ κ := hφ_pt x
    have hsubG : κ ⊆ WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) := by
      rcases hsh 0 κ hκmem with h | h
      · exact h
      · exact absurd (hpt_graph x) (Set.disjoint_left.mp h hptκ)
    have hcellκ : WilkiesDesign.IsCell 2 κ := (hcell2 κ hκmem).1
    have hneκ : κ.Nonempty := ⟨pt x, hptκ⟩
    obtain ⟨C0, ψ, hC0, hψcont, hκeq, hproj, hagree⟩ := isCell_two_graph hcellκ hneκ hsubG
    have hbase : (fun _ : Fin 1 => x) ∈ C0 := by
      rw [← hproj]
      exact ⟨pt x, hptκ, by simp [pt, Fin.init_snoc]⟩
    rcases isCell_one_dichotomy hC0 with ⟨q, hq⟩ | hopen
    · exfalso
      apply hxP
      have hq' : q = (fun _ : Fin 1 => x) := by
        have hh := hbase
        rw [hq] at hh
        exact (Set.mem_singleton_iff.mp hh).symm
      show Fin.init '' (φ x) = {fun _ : Fin 1 => x}
      have hstep : Fin.init '' (φ x) = Fin.init '' κ := rfl
      rw [hstep, hproj, hq, hq']
    · exact continuousAt_of_graphCell hopen hψcont hbase hagree
  exact hPfin.subset (fun x hx => by
    by_contra hxP
    exact hx (hcont x hxP))

end Work.WilG4b
