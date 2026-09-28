import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.NA.VeroAux
import Submission.Work.HP.NA.exists_lam_gcdMinors2
import Submission.Work.HP.EEupper.gcdMinors_veronese

namespace Work.HP.GamLoc

/-- **Lemma G of Browning--Le Boudec--Sawin** (the gcd of the `2 × 2` minors commutes with the
Veronese map), in the form needed here: for primitive `x, y : ℤ^{n+1}` and `1 ≤ d`,
`𝓖(ν_{d,n}(x), ν_{d,n}(y)) = 𝓖(x, y)`.

This is `Work.HP.EEupper.gcdMinors_veronese` verbatim; the extra hypothesis `1 ≤ n` is not
needed. -/
theorem gcdMinors2_veronese (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (x y : Fin (n + 1) → ℤ) (hx : Work.HP.IsPrim x) (hy : Work.HP.IsPrim y) : Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y) = Work.HP.gcdMinors2 x y := by
  have _hn : 1 ≤ n := hn
  exact Work.HP.EEupper.gcdMinors_veronese d n hd x y hx hy

end Work.HP.GamLoc
