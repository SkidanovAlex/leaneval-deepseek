import Mathlib
import Submission.Work.Certificates.SDR

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Assembling the sparse `SDR` check from its four pieces

`SDR.check S` is the conjunction of the degree-`0` homotopy equation `checkHomZero` with the
degreewise checks `checkDeg k` for `k` below the bound `S.N` (`SDR.check_eq`), and each
`checkDeg k` is in turn the four-way conjunction `checkZ k && checkRho k && checkRhoZ k &&
checkHom k` (`SDR.checkDeg_eq`).  This file records the corresponding reassembly: if the
degree-`0` piece holds and the four pieces hold in every degree `k < S.N`, then `S.check` holds.

The point is that each piece can be discharged by a cheap sparse computation, and the (much more
expensive) composite check then follows without evaluating it.
-/

namespace Work.Certificates.SDR

variable {C : FinChainCx}

/-- A passing `SDR` check can be assembled from its pieces: the degree-`0` homotopy equation
`checkHomZero` together with the four equations `checkZ`, `checkRho`, `checkRhoZ`, `checkHom` in
every degree `k < S.N`. -/
theorem check_of_pieces (S : SDR C) (h0 : S.checkHomZero = true)
    (h : ∀ k, k < S.N → S.checkZ k = true ∧ S.checkRho k = true ∧ S.checkRhoZ k = true ∧
      S.checkHom k = true) : S.check = true := by
  -- Expand `check` into `checkHomZero` and the degreewise conjunction (`check_eq`).
  rw [S.check_eq]
  rw [h0]
  simp only [Bool.true_and]
  -- `List.all` over `List.range S.N` is the pointwise statement for all `k < S.N`.
  rw [List.all_eq_true]
  intro k hk
  obtain ⟨hZ, hRho, hRhoZ, hHom⟩ := h k (List.mem_range.mp hk)
  simp [hZ, hRho, hRhoZ, hHom]

end Work.Certificates.SDR
