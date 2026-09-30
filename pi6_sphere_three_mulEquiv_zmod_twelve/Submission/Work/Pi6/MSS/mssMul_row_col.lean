import Mathlib
import Submission.Work.Pi6.MSS.mssMulCompat
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `mssMul` on the bottom row and the left column

The product `mssMul` of the assembled multiplicative cohomological Serre spectral sequence
(`Submission/Work/Pi6/MSS/AssembleCore.lean`) is, on bidegrees in the first quadrant, the transport
of the concrete page product `pd_mul` along the index identifications of the assembly
(`mssMul_apply_pos`).  In the special case of the bottom-row bidegree `(s, 0)` and the
left-column bidegree `(0, q)` — the case used for the edge homomorphisms of the spectral sequence —
all the bookkeeping collapses, and the product is *literally* the transport of `pd_mul` from the
concrete `ℕ`-indices `(s, s)` and `(0, q)` to the total degree `s + q`.

The proof is the transport bookkeeping of `mssMulCompat`: replace the index cast of the goal by an
explicit one, apply `mssMul_apply_pos`, merge the two transports (`pCast_comp_apply`), and identify
the merged transport with the transport of the statement (`pCast_congr`), the remaining difference
being the identification `EN (s,0) = s + 0`, `EI (0,q) = 0`, `EN (0,q) = 0 + q` of the *definitions*
`EI`/`EN`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

theorem mssMul_row_col (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s q : ℕ)
    (x : mssE 𝕜 W r ((s : ℤ), (0 : ℤ))) (y : mssE 𝕜 W r ((0 : ℤ), (q : ℤ))) :
    mssMul 𝕜 W r ((s : ℤ), (0 : ℤ)) ((0 : ℤ), (q : ℤ)) ((s : ℤ), (q : ℤ)) (by ext <;> simp) x y
      = (pEcast 𝕜 W r (show s + 0 = s + 0 by omega) (show s + (0 + q) = s + q by omega)).hom
          (pd_mul r s s 0 (0 + q) x y) := by
  have ha : Enn ((s : ℤ), (0 : ℤ)) := Enn_pair s 0
  have hb : Enn ((0 : ℤ), (q : ℤ)) := Enn_pair 0 q
  have hc : ((s : ℤ), (0 : ℤ)) + ((0 : ℤ), (q : ℤ)) = ((s : ℤ), (q : ℤ)) := by ext <;> simp
  -- replace the index cast of the goal by the explicit one `hc`
  rw [mssMul_congr 𝕜 W r ((s : ℤ), (0 : ℤ)) ((0 : ℤ), (q : ℤ)) ((s : ℤ), (q : ℤ)) _ hc x y]
  -- unfold the assembled product into the two transports of the concrete product
  rw [mssMul_apply_pos 𝕜 W r ha hb hc x y]
  -- turn the transport isomorphism of the right hand side into a `pCast`
  rw [pEcast_hom_apply]
  -- merge the two transports of the left hand side
  rw [pCast_comp_apply 𝕜 W r (EI_add ha hb) (congrArg EI hc) (EN_add ha hb) (congrArg EN hc)
    (pd_mul r (EI ((s : ℤ), (0 : ℤ))) (EN ((s : ℤ), (0 : ℤ))) (EI ((0 : ℤ), (q : ℤ)))
      (EN ((0 : ℤ), (q : ℤ))) x y)]
  -- identify the merged index equalities with those of the statement
  rw [pCast_congr 𝕜 W r ((EI_add ha hb).trans (congrArg EI hc)) (show s + 0 = s + 0 by omega)
    ((EN_add ha hb).trans (congrArg EN hc)) (show s + (0 + q) = s + q by omega)]
  rfl

end Work.Pi6.MSS
