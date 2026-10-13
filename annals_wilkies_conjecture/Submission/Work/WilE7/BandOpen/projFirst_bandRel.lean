import Mathlib
import Submission.Work.WilE7.BandOpenDefs
import Submission.Work.WilE8.Star.projFirst_cyl
import Submission.Work.WilE8.Star.LiftDef

namespace Work.WilE7.BandOpen

theorem projFirst_bandRel {n m : ℕ} {K : Set (Fin (n + m) → ℝ)}
    (hK : K ⊆ WilkiesDesign.E.cubeC (n + m)) :
    WilkiesDesign.E.projFirst (n + 1) m ''
        (Work.WilE7.bandRel K ∩ WilkiesDesign.E.cubeC (n + 1 + m)) =
      {y : Fin (n + 1) → ℝ | Fin.init y ∈ WilkiesDesign.E.projFirst n m '' K ∧
        -1 < y (Fin.last n) ∧ y (Fin.last n) < 1} := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzband, hzcube⟩, rfl⟩
    rw [Work.WilE7.mem_bandRel] at hzband
    refine ⟨⟨fun i => z (Work.WilE8.skipInj n m i), hzband.1, ?_⟩, ?_, ?_⟩
    · funext j
      show z (Work.WilE8.skipInj n m (Fin.castAdd m j)) = z (Fin.castAdd m j.castSucc)
      rw [Work.WilE8.Star.skipInj_castAdd_castSucc]
    · exact hzband.2.1
    · exact hzband.2.2
  · rintro ⟨⟨w, hwK, hweq⟩, hlo, hhi⟩
    refine ⟨Work.WilE8.Star.insCoord n m w (y (Fin.last n)), ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · have h1 : (fun i => Work.WilE8.Star.insCoord n m w (y (Fin.last n))
          (Work.WilE8.skipInj n m i)) = w :=
        funext fun i => Work.WilE8.Star.insCoord_skipInj n m w (y (Fin.last n)) i
      rw [h1]; exact hwK
    · simpa only [Work.WilE7.newIdx, Work.WilE8.Star.insCoord_new] using hlo
    · simpa only [Work.WilE7.newIdx, Work.WilE8.Star.insCoord_new] using hhi
    · exact Work.WilE8.Star.insCoord_cube n m (hK hwK) (le_of_lt (abs_lt.mpr ⟨hlo, hhi⟩))
    · rw [Work.WilE8.Star.projFirst_insCoord, hweq]
      exact Fin.snoc_init_self y

end Work.WilE7.BandOpen
