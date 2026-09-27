import Mathlib
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.levelOf_clampedSweep
import Submission.Work.Drive.SeamMeetDefs

namespace Work.Drive

/-- The bottom boundary triple intersections of three clamped radial sweeps are exactly the triples whose three parameters are all at their bottoms and whose three shadows coincide. -/
theorem bottomBdryMeet_clampedSweep_eq
    (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1)
    (hψlt : ∀ t : ℝ, 0 < t → ψ t < 1)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hlvl : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), levelOf (P k y) ≠ c)
    (k : Fin 3) :
    bottomBdryMeet CappingSpace (fun j => clampedSweep c ψ (P j)) k =
      {x | (∀ j : Fin 3, x j ∈ Submission.Drive.unitBox 2) ∧
           (∀ j : Fin 3, x j 2 = 0) ∧
           (∀ j : Fin 3, shadow c hc (P j (mk2 (x j 0) (x j 1))) =
                        shadow c hc (P 0 (mk2 (x 0 0) (x 0 1))))} := by
  ext x
  simp only [bottomBdryMeet, tripleBdryMeet, Set.mem_ofPred_eq]
  constructor
  · -- A bottom triple intersection: the three sweeps meet at a point of the level `c`, hence all three
    -- parameters are at their bottom faces, where the sweeps are the shadows of the planes.
    rintro ⟨⟨hbox, h01, h02, hbd⟩, hk0⟩
    have hall : ∀ j : Fin 3, clampedSweep c ψ (P j) (x j) = clampedSweep c ψ (P k) (x k) := by
      intro j
      fin_cases j <;> fin_cases k <;> simp_all
    have hlevc : levelOf (clampedSweep c ψ (P k) (x k)) = c :=
      (levelOf_clampedSweep_eq_bottom_iff c hc ψ hψ0 hψlt (P k) (x k) (hbox k 2).1
        (hlvl k (mk2 (x k 0) (x k 1)))).mpr hk0
    have hx2 : ∀ j : Fin 3, x j 2 = 0 := by
      intro j
      refine (levelOf_clampedSweep_eq_bottom_iff c hc ψ hψ0 hψlt (P j) (x j) (hbox j 2).1
        (hlvl j (mk2 (x j 0) (x j 1)))).mp ?_
      rw [hall j]; exact hlevc
    refine ⟨hbox, hx2, ?_⟩
    intro j
    have hj := clampedSweep_face_zero c hc ψ (P j) hψ0 (x j) (hx2 j)
    have h0 := clampedSweep_face_zero c hc ψ (P 0) hψ0 (x 0) (hx2 0)
    exact hj.symm.trans ((hall j).trans (hall 0).symm) |>.trans h0
  · -- Conversely, at the bottom faces the three sweeps are the three shadows; if those coincide the
    -- sweeps meet, and the bottom face makes the `k`-th parameter a boundary point of its cube.
    rintro ⟨hbox, h2, hsh⟩
    have hface : ∀ j : Fin 3, clampedSweep c ψ (P j) (x j)
        = shadow c hc (P 0 (mk2 (x 0 0) (x 0 1))) := by
      intro j
      rw [clampedSweep_face_zero c hc ψ (P j) hψ0 (x j) (h2 j), hsh j]
    refine ⟨⟨hbox, ?_, ?_, ⟨hbox k, 2, Or.inl (h2 k)⟩⟩, h2 k⟩
    · exact (hface 0).trans (hface 1).symm
    · exact (hface 0).trans (hface 2).symm

end Work.Drive
