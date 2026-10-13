import Mathlib
import Submission.Work.WilE2.BoxLocDefs

namespace Work.WilE2.BoxLoc

open WilkiesDesign WilkiesDesign.E

theorem boxMap_image_Zset {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) {a b : Fin k → ℝ}
    (hab : ∀ i, a i < b i) (g : Finset (WilkiesDesign.E.EAPoly k r)) :
    Work.WilE2.boxMap a b ''
        (WilkiesDesign.E.cubeC k ∩ Work.WilE2.Zset (Work.WilE2.boxChain c a b)
          (g.image (Work.WilE2.boxSub a b)))
      = Work.WilE2.axBox a b ∩ Work.WilE2.Zset c g := by
  ext w
  constructor
  · -- forward: pull the zero conditions back through `boxSub` and `eaEval_boxSub`
    rintro ⟨z, ⟨hzcube, hzZ⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← Work.WilE2.boxMap_image_cubeC (a := a) (b := b) hab]
      exact ⟨z, hzcube, rfl⟩
    · intro f hf
      have hmem : Work.WilE2.boxSub a b f ∈ g.image (Work.WilE2.boxSub a b) :=
        Finset.mem_image.mpr ⟨f, hf, rfl⟩
      have h0 := hzZ (Work.WilE2.boxSub a b f) hmem
      rw [Work.WilE2.eaEval_boxSub] at h0
      exact h0
  · -- backward: lift a point of the box to its (unique) preimage in the cube
    rintro ⟨hwbox, hwZ⟩
    rw [← Work.WilE2.boxMap_image_cubeC (a := a) (b := b) hab] at hwbox
    obtain ⟨z, hzcube, hzmap⟩ := hwbox
    refine ⟨z, ⟨hzcube, ?_⟩, hzmap⟩
    intro Q hQ
    obtain ⟨f, hf, hfeq⟩ := Finset.mem_image.mp hQ
    rw [← hfeq, Work.WilE2.eaEval_boxSub, hzmap]
    exact hwZ f hf

end Work.WilE2.BoxLoc
