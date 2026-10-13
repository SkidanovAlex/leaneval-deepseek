import Mathlib
import Submission.Work.WilG4c.FibDiscMain.FibDiscAux

/-!
  `bodyA` is `Ω`-definable with format and degree polynomial *uniform* in the degree parameter
  `D` and in the defining function `H`.

  Recall (see `FibDiscAux`)

    `innerA p N H = ((gxSet p N H ∩ gySet p N H) ∩ ballSet p N) ∩ ineqSet p N`,
    `bodyA p N H  = projN (N+2) (innerA p N H)`,

  where `gxSet`/`gySet` are coordinate reindexings of `graphOf H`, `ballSet` is the positivity set
  of the fixed polynomial `ballPoly p N`, and `ineqSet` is the complement of the positivity set of
  the fixed polynomial `ineqPoly p N`.  Each of these operations is covered by a combinator of the
  `UOA` calculus in `FibDiscAux` (`of_hyp`, `coordPre`, `pos`, `compl`, `inter`, `projN`), none of
  which lets the format or the degree polynomial depend on `D` or on `H`.  The proof below is
  therefore a direct assembly of those combinators.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4c.FibDiscMain

theorem bodyA_mem_uniform (S : WilkiesDesign.SOMin) (p N F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (H : (Fin (p + N) → ℝ) → ℝ),
      WilkiesDesign.graphOf H ∈ S.Ω F D (p + N + 1) →
      Work.WilG4c.FibDiscMain.bodyA p N H ∈ S.Ω a (b.eval D) (p + N + 2) := by
  have hgx : UOA S (p + N) F (bigA p N) (fun _ H => gxSet p N H) :=
    UOA.coordPre (gxMap p N) (UOA.of_hyp (S := S) (m := p + N) (F := F))
  have hgy : UOA S (p + N) F (bigA p N) (fun _ H => gySet p N H) :=
    UOA.coordPre (gyMap p N) (UOA.of_hyp (S := S) (m := p + N) (F := F))
  have hball : UOA S (p + N) F (bigA p N) (fun _ _ => ballSet p N) :=
    UOA.pos (S := S) (m := p + N) (F := F) (ballPoly p N)
  have hineq : UOA S (p + N) F (bigA p N) (fun _ _ => ineqSet p N) :=
    UOA.compl (UOA.pos (S := S) (m := p + N) (F := F) (ineqPoly p N))
  have hinner : UOA S (p + N) F (bigA p N) (fun _ H => innerA p N H) :=
    UOA.inter (UOA.inter (UOA.inter hgx hgy) hball) hineq
  exact UOA.projN (S := S) (m := p + N) (F := F) (n := p + N + 2) (N + 2) hinner

end Work.WilG4c.FibDiscMain
