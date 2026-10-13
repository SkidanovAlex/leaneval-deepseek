/-
  annals_wilkies_conjecture, area C4aL: the target statement `C4a_lift`.

  Everything is assembled from the sub-modules of `Submission.Work.WilC4aL`:
  `Kall_mul_Efun` (the cleared equation identity), `piece_good` (each piece is good),
  `mkZ_mem` (`→` membership of the constructed slice point) and `reconstruct` (`←`).
-/
import Submission.Work.WilC4aL.Main
import Submission.Work.WilC4aL.Kall_mul_Efun
import Submission.Work.WilC4aL.piece_good
import Submission.Work.WilC4aL.mkZ_mem
import Submission.Work.WilC4aL.reconstruct

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilC4aL
open WilkiesDesign WilkiesDesign.CG.C4a
open scoped BigOperators

/-- The forward membership of the constructed point: `piece c (mkCases y w) P ∈ pieceList c P`. -/
theorem mkCases_mem_pieceList {k m : ℕ} (c : Fin k → ℝ) (y : ℝ) (w : Fin m → ℝ)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) :
    piece c (mkCases y w) P ∈ pieceList (k := k) c P := by
  rw [pieceList]
  exact List.mem_map.mpr ⟨mkCases y w, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩

/-- **C4a_lift.** For `x = 1/t > 1`, `rexp x = 0`; splitting every other variable into
`|·| < 1`, `· ^ 2 = 1`, `|·| > 1` (inverting the last) clears denominators and turns the
`rexp` slice of an `RExpExist` set into finitely many bounded basic semianalytic pieces with
entire data. -/
theorem C4a_lift_proved {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (hY : RExpExist Y)
    (c : Fin k → ℝ) : SliceLift Y c := by
  obtain ⟨m, P, hYeq⟩ := hY
  refine ⟨pieceList (k := k) c P, ?_, ?_⟩
  · intro Q hQ
    rw [pieceList, List.mem_map] at hQ
    obtain ⟨σ', _, rfl⟩ := hQ
    exact piece_good c σ' P
  · intro t ht y
    obtain ⟨ht0, ht1⟩ := ht
    rw [hYeq]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨hmem, hrep⟩ := mkZ_mem c y t w ht0 ht1 P hw
      exact ⟨piece c (mkCases y w) P, mkCases_mem_pieceList c y w P, mkZ y w t, hmem,
        mkZ_zero y t w, hrep⟩
    · rintro ⟨Q, hQ, z, hzset, hz0, hrep⟩
      rw [pieceList, List.mem_map] at hQ
      obtain ⟨σ', _, rfl⟩ := hQ
      exact reconstruct c σ' P t y z ht0 ht1 (piece_good c σ' P) hzset hz0 hrep

end Work.WilC4aL
