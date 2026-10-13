import Mathlib
import Submission.Work.WilG4a.fiber_defs
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Calc.lt_mem

namespace Work.WilG4a

/-- The pullback `pullZ2 p Z` is the coordinate preimage of `Z` along the embedding `iota1 p`;
so reindexing (`Work.WilG5.coordPre_mem`) applies, and one projection (`SOMin.proj`) then gives
`NE1 p Z`.  Format and degree gains are constants independent of `D` and `F`. -/
theorem NE1_mem (S : WilkiesDesign.SOMin) (p F : ℕ) :
    ∃ (A c c' : ℕ), ∀ (D : ℕ) (Z : Set (Fin (p + 1) → ℝ)), Z ∈ S.Ω F D (p + 1) →
      Work.WilG4a.NE1 p Z ∈ S.Ω (A + F) (c * D + c') (p + 1) := by
  refine ⟨64 * (2 * p + 3) + 65, 1, 32 * (2 * p + 3) + 32, ?_⟩
  intro D Z hZ
  have hpre : pullZ2 p Z ∈
      S.Ω (F + 64 * ((p + 2) + (p + 1)) + 64)
        (D + 32 * ((p + 2) + (p + 1)) + 32) (p + 2) := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := p + 1) (N := p + 2)
      (ι := iota1 p) (A := Z) hZ
    rwa [show Work.WilG5.coordPre (iota1 p) Z = pullZ2 p Z from rfl] at h
  have hproj := S.proj hpre
  exact Work.WilG5.mem_mono hproj (64 * (2 * p + 3) + 65 + F)
    (1 * D + (32 * (2 * p + 3) + 32)) (by omega) (by omega)

end Work.WilG4a
