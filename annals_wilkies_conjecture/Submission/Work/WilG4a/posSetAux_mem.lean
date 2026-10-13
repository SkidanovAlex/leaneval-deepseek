import Mathlib
import Submission.Work.WilG4a.lip_loci_defs

namespace Work.WilG4a

theorem posSetAux_mem {S : WilkiesDesign.SOMin} {p : ℕ} {D : ℕ} {f : (Fin p → ℝ) → ℝ → ℝ}
    {aS : ℕ} {bS : Polynomial ℕ}
    (hSS : Work.WilG4a.derSet f ∈ S.Ω aS (bS.eval D) (p + 2)) :
    Work.WilG4a.posSetAux f ∈ S.Ω (max aS (p + 4) + 2) ((bS + Polynomial.C 3).eval D) (p + 1) := by
  have hpos : posHalf (p + 2) (Fin.last (p + 1)) ∈
      S.Ω (p + 4) ((Polynomial.C 3).eval D) (p + 2) := by
    have h := posHalf_mem (S := S) (p + 2) (Fin.last (p + 1)) D
    simpa [Nat.add_assoc] using h
  have hint : derSet f ∩ posHalf (p + 2) (Fin.last (p + 1)) ∈
      S.Ω (max aS (p + 4) + 1) ((bS + Polynomial.C 3).eval D) (p + 2) :=
    Work.WilG1.Omega.inter₂ (S := S) hSS hpos
  have hproj := Work.WilG1.Omega.projLast_mem (S := S) (n := p + 1) hint
  simpa [posSetAux] using hproj

end Work.WilG4a
