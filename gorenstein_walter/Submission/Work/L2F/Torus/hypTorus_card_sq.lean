import Mathlib
import Submission.Work.L2F.Torus.Defs
import Submission.Work.L2F.Conic.mem_hypTorus
import Submission.Work.L2F.Conic.hypTorus_card_sq

namespace Work.L2F.Torus

/-- For a square `d = s * s` (`s ≠ 0`), the "torus" `hypTorus F d` -- the conic
`{(a,b) | a² - d·b² = 1}` inside `SL(2,F)` -- has `q - 1` elements (whereas for `d` a nonsquare it
has `q + 1`, which is `Work.L2F.Conic.hypTorus_card`). -/
theorem hypTorus_card_sq (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (s : F)
    (hs : s ≠ 0) : Nat.card (Work.L2F.hypTorus F (s * s)) = Nat.card F - 1 :=
  Work.L2F.Conic.hypTorus_card_sq F h2 (s * s) s hs (by ring)

end Work.L2F.Torus
