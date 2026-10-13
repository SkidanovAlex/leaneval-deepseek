import Mathlib
import Submission.Work.WilE7.Endgame.E2Aux

namespace Work.WilE7.Endgame

set_option autoImplicit false
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)

theorem E2_activeFamily {n m : ℕ} {b : Set (Fin n → ℝ)} (hb : b.Nonempty)
    (Cand : List (WilkiesDesign.E.Stratum 0 (n + (m + 1))))
    (hdec : ∀ S ∈ Cand, b ⊆ WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet S ∨
      Disjoint b (WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet S)) :
    ∃ (r : ℕ) (S' : Fin r → WilkiesDesign.E.Stratum 0 (n + (m + 1))),
      (∀ i : Fin r, S' i ∈ Cand) ∧
      (∀ i : Fin r, b ⊆ WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet (S' i)) ∧
      (∀ S ∈ Cand, b ⊆ WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet S →
        ∃ i : Fin r, S' i = S) ∧
      (∀ S ∈ Cand, (∀ i : Fin r, S' i ≠ S) →
        Disjoint b (WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet S)) := by
  classical
  -- The active subfamily: the members of `Cand` whose `π_n`-image captures `b`.
  let P : WilkiesDesign.E.Stratum 0 (n + (m + 1)) → Prop :=
    fun S => b ⊆ WilkiesDesign.E.projFirst n (m + 1) '' absSet S
  let L : List (WilkiesDesign.E.Stratum 0 (n + (m + 1))) := Cand.filter (fun S => decide (P S))
  have hL : ∀ S, S ∈ L ↔ S ∈ Cand ∧ P S := by
    intro S
    have h1 : S ∈ L ↔ S ∈ Cand ∧ decide (P S) = true := by
      simp only [L, List.mem_filter]
    rw [h1, decide_eq_true_iff]
  refine ⟨L.length, fun i => L.get i, ?_, ?_, ?_, ?_⟩
  · intro i
    exact List.mem_of_mem_filter (List.get_mem L i)
  · intro i
    exact ((hL _).mp (List.get_mem L i)).2
  · intro S hS hbS
    have hSL : S ∈ L := (hL S).mpr ⟨hS, hbS⟩
    obtain ⟨i, hi⟩ := List.exists_mem_iff_get.mp ⟨S, hSL, rfl⟩
    exact ⟨i, hi.symm⟩
  · intro S hS hne
    rcases hdec S hS with hbS | hdis
    · exfalso
      have hSL : S ∈ L := (hL S).mpr ⟨hS, hbS⟩
      obtain ⟨i, hi⟩ := List.exists_mem_iff_get.mp ⟨S, hSL, rfl⟩
      exact hne i hi.symm
    · exact hdis

end Work.WilE7.Endgame
