import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.SemiPfInter
import Submission.Work.WilE7.cylCell_pres
import Submission.Work.WilE8.Extend
import Submission.Work.WilE8.Extend.semipf_set_extend
import Submission.Work.WilE8.Star.lift_right_cube
import Submission.Work.WilE7.BandOpenDefs
import Submission.Work.WilE7.BandOpen.projFirst_bandRel
import Submission.Work.WilE7.BandOpen.connectedComponentIn_bandExt

namespace Work.WilE7

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

theorem cylOpenBand (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ),
      ∀ (p M : ℕ) (Z : WilkiesDesign.E.SemiPf (p + M)) (u₀ : Fin (p + M) → ℝ) (hu₀ : u₀ ∈ Z.set)
        (C : Set (Fin p → ℝ))
        (hC : C = Set.image (WilkiesDesign.E.projFirst p M) (connectedComponentIn Z.set u₀))
        (hCpf : WilkiesDesign.E.SubPf p C) (D : ℕ),
        Z.fmt ≤ F → Z.deg ≤ D →
        (∃ P : WilkiesDesign.E.StarPiece (p + 1),
          P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧ y (Fin.last p) < 1} ∧
          P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D) ∧
        WilkiesDesign.E.SubPf (p + 1)
          {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧ y (Fin.last p) < 1} := by
  -- the format bound is `F + 1` (the lift adds one coordinate) and the degree bound is
  -- `4F + 4 + 5D`: `bandExt` adds at most `4 * max 1 D` to `Z.deg`, and `Z.fmt ≤ F` forces
  -- the `p + M` coordinates below `F`.
  refine ⟨F + 1, Polynomial.C (4 * F + 4) + Polynomial.C 5 * Polynomial.X, ?_⟩
  intro p M Z u₀ hu₀ C hC hCpf D hfmt hdeg
  -- the projected component stays inside the cube
  have hKsub : connectedComponentIn Z.set u₀ ⊆ cubeC (p + M) :=
    fun x hx => Work.WilE8.SemiPf.set_subset_cube Z (connectedComponentIn_subset Z.set u₀ hx)
  have hu₀cube : u₀ ∈ cubeC (p + M) := Work.WilE8.SemiPf.set_subset_cube Z hu₀
  have hnew : Work.WilE8.Star.insCoord p M u₀ 0 (newIdx p M) = 0 := by
    rw [newIdx]
    exact Work.WilE8.Star.insCoord_new p M u₀ 0
  -- the canonical point of the strict band lift lies in it
  have hqmem : Work.WilE8.Star.insCoord p M u₀ 0 ∈ (bandExt Z).set := by
    rw [bandExt_mem]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (fun i => Work.WilE8.Star.insCoord p M u₀ 0 (Work.WilE8.skipInj p M i)) ∈ Z.set
      rw [funext (fun i => Work.WilE8.Star.insCoord_skipInj p M u₀ 0 i)]
      exact hu₀
    · rw [hnew]; norm_num
    · rw [hnew]; norm_num
    · exact Work.WilE8.Star.insCoord_cube p M hu₀cube (by norm_num)
  refine ⟨?_, ?_⟩
  · -- one `*`-piece: the strict band lift of `Z` through its canonical point
    refine ⟨⟨M, bandExt Z, Work.WilE8.Star.insCoord p M u₀ 0⟩, ?_, ?_, ?_⟩
    · have hset : projFirst (p + 1) M ''
          connectedComponentIn (bandExt Z).set (Work.WilE8.Star.insCoord p M u₀ 0) =
          {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
            y (Fin.last p) < 1} := by
        rw [Work.WilE7.BandOpen.connectedComponentIn_bandExt Z u₀ hu₀]
        rw [Work.WilE7.BandOpen.projFirst_bandRel hKsub]
        rw [hC]
      exact hset
    · show (bandExt Z).fmt ≤ F + 1
      rw [bandExt_fmt]
      omega
    · show (bandExt Z).deg ≤ (Polynomial.C (4 * F + 4) + Polynomial.C 5 * Polynomial.X).eval D
      have hev : (Polynomial.C (4 * F + 4) + Polynomial.C 5 * Polynomial.X).eval D =
          4 * F + 4 + 5 * D := by
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [hev]
      have := bandExt_deg_le Z
      omega
  · -- sub-Pfaffianness: lift a semi-Pfaffian presentation of `C`
    obtain ⟨m, X, hX⟩ := hCpf
    refine ⟨m, bandExt X, ?_⟩
    rw [bandExt_set]
    rw [Work.WilE7.BandOpen.projFirst_bandRel (K := X.set) (Work.WilE8.SemiPf.set_subset_cube X)]
    rw [hX]

end Work.WilE7
