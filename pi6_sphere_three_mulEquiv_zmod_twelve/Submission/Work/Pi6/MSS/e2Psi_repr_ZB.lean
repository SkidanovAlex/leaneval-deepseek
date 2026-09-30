import Mathlib
import Submission.Work.Pi6.MSS.e2Asm
import Submission.Work.Pi6.MSS.e2Row_exists
import Submission.Work.Pi6.MSS.e2ColRho
import Submission.Work.Pi6.MSS.mssMulCompat
import Submission.Work.Pi6.MSS.mssNorm_hom_eq_self
import Submission.Work.Pi6.MSS.mssMul_row_col
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The representative of `Ψ (b ⊗ f)` for a skeletal cocycle `b`

For a Serre fibration `p : E → B` with simply connected base and `𝕜` a field, the candidate
inverse `e2Psi : H^s(B;𝕜) ⊗ H^q(F;𝕜) → E_2^{s,q}` of the `E_2`-identification
(`Submission/Work/Pi6/MSS/e2Asm.lean`) is built out of the base row map `e2Row` and the fibre
column map `e2ColAll`.  The unit of the present file computes it on an element
`clsB β ⊗ f` whose base factor is the class of a *skeletal* cocycle `β ∈ ZB 𝕜 B s`: the
normalization `mssNorm` of the class `Ψ (clsB β ⊗ f)` is the concrete page product `pd_mul` of the
class `Rb β` of the pullback of `β` with the normalized column class.

The proof is pure bookkeeping with the pages of the spectral sequence:

* `e2Psi_tmul` (definitional) turns `e2Psi` into `mssMul` of the row and column maps;
* `e2Row_clsB` (`rowMap_clsB`) identifies `e2Row s (clsB β)` with `Rb β`;
* `mssNorm_hom_eq_self` removes the normalization `mssNorm` (it is the identity because `EI`/`EN`
  are definitionally the identity on pairs of natural numbers);
* `mssMul_row_col` rewrites `mssMul` on a row class times a column class as `pd_mul`;
* `pd_mul_pCast_apply` and `pCast_congr` move the transports `pCast` to the outside, and the two
  transports of the two endpoints `s + 0 = s`, `0 + q = q` are absorbed by
  `pEcast_hom_add_zero_self`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits
open Classical

attribute [local instance] Classical.propDecidable

/-- A transport of a page along `s + 0 = s` (the cohomological degree being fixed) is the identity,
because the two endpoints are definitionally equal. -/
lemma pEcast_hom_add_zero_self {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜} (r s n : ℕ)
    (h : s + 0 = s) (h' : n = n) (x : pEraw 𝕜 W r (s + 0) n) :
    (pEcast 𝕜 W r h h').hom x = x := by
  rw [pEcast_hom_apply]
  exact pCast_self_apply 𝕜 W r _ _ x

theorem e2Psi_repr_ZB (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (s q : ℕ) (β : ↥(Work.Pi6.MSS.ZB 𝕜 B s))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    ∃ f' : Work.Pi6.MSS.pEraw 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q,
      (Work.Pi6.MSS.pEcast 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 (show 0 = 0 by omega)
          (show 0 + q = q by omega)).hom
          ((Work.Pi6.MSS.mssNorm 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).hom
            (Work.Pi6.MSS.e2ColAll 𝕜 p e₀ N hfib hconn hfin q f)) = f' ∧
      (Work.Pi6.MSS.mssNorm 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 s q).hom
          (Work.Pi6.MSS.e2Psi 𝕜 E B p e₀ (Work.Pi6.MSS.e2Row 𝕜 p)
            (Work.Pi6.MSS.e2ColAll 𝕜 p e₀ N hfib hconn hfin) s q
            (Work.Pi6.MSS.clsB 𝕜 B s β ⊗ₜ[𝕜] f))
        = (Work.Pi6.MSS.pEcast 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 (show s + 0 = s by omega)
            (show s + q = s + q by omega)).hom
            (Work.Pi6.MSS.pd_mul 2 s s 0 q (Work.Pi6.MSS.Rb 𝕜 p s β) f') := by
  refine ⟨(pEcast 𝕜 (Wc 𝕜 p) 2 (show 0 = 0 by omega) (show 0 + q = q by omega)).hom
      ((mssNorm 𝕜 (Wc 𝕜 p) 2 0 q).hom (e2ColAll 𝕜 p e₀ N hfib hconn hfin q f)), ?_, ?_⟩
  · rfl
  · -- the value of `e2Psi` on the pure tensor, and the base factor `clsB β`
    rw [e2Psi_tmul]
    rw [show e2Row 𝕜 p s (clsB 𝕜 B s β) = Rb 𝕜 p s β from
      rowMap_clsB 𝕜 p s (ker_clsB_le_ker_Rb 𝕜 p s) (clsB_range_top 𝕜 B s) β]
    -- the normalization of the honest bidegree `(s,q)` is the identity, and `mssMul` on
    -- a row class times a column class is `pd_mul`
    rw [mssNorm_hom_eq_self]
    rw [mssMul_row_col]
    rw [pEcast_hom_apply]
    -- the transport of `pd_mul` is the `pd_mul` of the transports
    rw [pd_mul_pCast_apply 𝕜 (Wc 𝕜 p) 2 s s 0 (0 + q) s s 0 q
      (rfl : s = s) (rfl : s = s) (rfl : (0 : ℕ) = 0) (show 0 + q = q by omega)
      (show s + 0 = s + 0 by omega) (show s + (0 + q) = s + q by omega)]
    rw [pCast_self_apply 𝕜 (Wc 𝕜 p) 2 (rfl : s = s) (rfl : s = s) (Rb 𝕜 p s β)]
    -- the witness `f'` is the transported column class
    rw [show (pEcast 𝕜 (Wc 𝕜 p) 2 (show 0 = 0 by omega) (show 0 + q = q by omega)).hom
          ((mssNorm 𝕜 (Wc 𝕜 p) 2 0 q).hom (e2ColAll 𝕜 p e₀ N hfib hconn hfin q f))
        = (pCast 𝕜 (Wc 𝕜 p) 2 (rfl : (0 : ℕ) = 0) (show 0 + q = q by omega))
            (e2ColAll 𝕜 p e₀ N hfib hconn hfin q f) from by
      rw [mssNorm_hom_self 𝕜 E B p q (e2ColAll 𝕜 p e₀ N hfib hconn hfin q f)]
      rw [pEcast_hom_apply]]
    -- the remaining transport `s + 0 = s` is the identity
    rw [pEcast_hom_add_zero_self]

end Work.Pi6.MSS
