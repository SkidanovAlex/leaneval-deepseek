import Mathlib
import Submission.Work.WilG4a.lip_loci_defs

namespace Work.WilG4a

/-- `negSet f` is the projection of `derSet f ∩ {s < 0}` (definitionally `negSetAux f`), and
the two pieces are `Ω`-sets: `derSet f` by hypothesis, the half-space `{s < 0}` by
`negHalf_mem` with format `(p+2)+2 = p+4` and degree `3`.  Intersection adds one to the
format and the degrees, projection out of the last coordinate adds one more to the format,
leaving format `max aS (p+4) + 2` and degree `bS + 3`. -/
theorem negSetAux_mem {S : WilkiesDesign.SOMin} {p : ℕ} {D : ℕ} {f : (Fin p → ℝ) → ℝ → ℝ}
    {aS : ℕ} {bS : Polynomial ℕ}
    (hSS : Work.WilG4a.derSet f ∈ S.Ω aS (bS.eval D) (p + 2)) :
    Work.WilG4a.negSetAux f ∈ S.Ω (max aS (p + 4) + 2) ((bS + Polynomial.C 3).eval D) (p + 1) := by
  have h1 : Work.WilG4a.negHalf (p + 2) (Fin.last (p + 1)) ∈
      S.Ω (p + 4) ((Polynomial.C 3).eval D) (p + 2) :=
    Work.WilG4a.negHalf_mem (S := S) (p + 2) (Fin.last (p + 1)) D
  have h2 : Work.WilG4a.derSet f ∩ Work.WilG4a.negHalf (p + 2) (Fin.last (p + 1)) ∈
      S.Ω (max aS (p + 4) + 1) ((bS + Polynomial.C 3).eval D) (p + 2) :=
    Work.WilG1.Omega.inter₂ hSS h1
  exact Work.WilG1.Omega.projLast_mem h2

end Work.WilG4a
