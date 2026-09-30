import Mathlib
import Submission.Work.Pi6.MSS.e2PsiCanonN
import Submission.Work.Pi6.MSS.e2Psi_repr_ZB
import Submission.Work.Pi6.MSS.e2Lbar
import Submission.Work.Pi6.MSS.pagesData
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The pairing of `Ψ (clsB β ⊗ f)` with the second page, for `f = rho [y]`

`Work.Pi6.MSS.e2Lbar` is the descent of the pairing `e2L0` (`Work.Pi6.MSS.e2Bar`) to the second
page; `Work.Pi6.MSS.e2Psi` is the candidate edge isomorphism `H^s(B) ⊗ H^q(F) → E_2^{s,q}` built
from the base row map and the fibre column map.

This file proves the bookkeeping identity

`e2Lbar 𝕜 E B p s q (Ψ (clsB β ⊗ rho [y])) = e2L0 𝕜 E B p s q (pairElem β y)`

where `β` is a *skeletal* base cocycle, `y ∈ Z_2^{0,q}` a column `2`-cycle and `pairElem β y` the
concrete page product `pd_mulZ 2 s (s+0) 0 q ⟨pbC β, _⟩ y` (`Work.Pi6.MSS.e2PsiPairDefs`).

The proof rests on the injectivity of `e2Lbar` (`Work.Pi6.MSS.e2Lbar_injective`) and reduces the
assertion to the equality of representatives

`Ψ (clsB β ⊗ rho [y]) = mkQ (pairElem β y)`

of the `E_2`-class.  The latter is the transport bookkeeping of
`e2Psi_tmul` + `rowMap_clsB` + `mssMul_row_col` + `pd_mul_nat` + `pd_pCast`/`pEcast`, together
with the computation `e2ColAll q (rho q [y]) = pCast (q = 0+q) [y]` of the fibre column map
(the inverse of the restriction-to-the-fibre isomorphism `rhoSSEquiv`).
-/

namespace Work.Pi6.MSS

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The final degree transport of the representative computation: the `xcast` of the concrete
product `mul s q (pbC β) y` along a reflexive equality of total degrees is that same product
(whose second index slot is written `s + 0`). -/
lemma e2LbarPairElem_xcast (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s q : ℕ)
    (β : ↥(ZB 𝕜 B s)) (y : ↥(pZ 𝕜 (Wc 𝕜 p) 2 0 q)) (heq : s + q = s + q) :
    (Wc 𝕜 p).xcast heq ((Wc 𝕜 p).mul s q (pbC 𝕜 p s β.1) y.1)
      = (Wc 𝕜 p).mul (s + 0) q (pbC 𝕜 p s β.1) y.1 := by
  rw [show (Wc 𝕜 p).xcast heq ((Wc 𝕜 p).mul s q (pbC 𝕜 p s β.1) y.1)
      = (Wc 𝕜 p).mul s q (pbC 𝕜 p s β.1) y.1 from by
    rw [pageUnit_xcast_congr (h := heq) (h' := rfl), CohFilt.xcast_rfl]
    rfl]
  rfl

theorem e2Lbar_pairElem (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (s q : ℕ) (hq : q ≤ N) (β : ↥(Work.Pi6.MSS.ZB 𝕜 B s))
    (y : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (hf : Work.Pi6.MSS.rho 𝕜 E B p e₀ q
            (Submodule.mkQ
              ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).comap
                (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).subtype)
              y) = f) :
    Work.Pi6.MSS.e2Lbar 𝕜 E B p s q
        (Work.Pi6.MSS.e2Psi 𝕜 E B p e₀ (Work.Pi6.MSS.e2Row 𝕜 p)
          (Work.Pi6.MSS.e2ColAll 𝕜 p e₀ N hfib hconn hfin) s q
          (TensorProduct.tmul 𝕜 (Work.Pi6.MSS.clsB 𝕜 B s β) f))
      = Work.Pi6.MSS.e2L0 𝕜 E B p s q (Work.Pi6.MSS.pairElem 𝕜 p s q β y) := by
  -- replace `f` by its value `rho [y]`
  rw [← hf]
  -- compute `e2L0 (pairElem)` via the descent rule of `e2Lbar`
  rw [← e2Lbar_mkQ 𝕜 E B p s q (pairElem 𝕜 p s q β y)]
  -- it remains to identify the representatives in `E_2`
  refine congrArg (e2Lbar 𝕜 E B p s q) ?_
  rw [e2Psi_tmul]
  rw [show (e2Row 𝕜 p) s (clsB 𝕜 B s β) = Rb 𝕜 p s β from
    rowMap_clsB 𝕜 p s (ker_clsB_le_ker_Rb 𝕜 p s) (clsB_range_top 𝕜 B s) β]
  -- the fibre column factor of `Ψ` at `rho [y]` is `[y]` (up to the index transport `q = 0+q`)
  have hA : e2ColAll 𝕜 p e₀ N hfib hconn hfin q (rho 𝕜 E B p e₀ q
        ((Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 2 0 q).comap (pZ 𝕜 (Wc 𝕜 p) 2 0 q).subtype)) y))
      = pCast 𝕜 (Wc 𝕜 p) 2 (rfl : 0 = 0) (show q = 0 + q by omega)
          ((Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 2 0 q).comap
            (pZ 𝕜 (Wc 𝕜 p) 2 0 q).subtype)) y) := by
    rw [e2ColAll_apply 𝕜 p e₀ N hfib hconn hfin q hq]
    change (rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin hq).symm
        (rho 𝕜 E B p e₀ q ((Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 2 0 q).comap
            (pZ 𝕜 (Wc 𝕜 p) 2 0 q).subtype)) y)) = _
    rw [LinearEquiv.symm_apply_eq]
    rw [rhoSSEquiv_apply 𝕜 E B p e₀ N q hfib hconn hfin hq]
    rw [rho_pCast_snd 𝕜 E B p e₀ (show q = 0 + q by omega)
      ((Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 2 0 q).comap (pZ 𝕜 (Wc 𝕜 p) 2 0 q).subtype)) y)]
    rw [cohXcast_comp_apply]
    rw [show (show q = 0 + q by omega).trans (Nat.zero_add q) = (rfl : q = q) from
      Subsingleton.elim _ _]
    rw [cohXcast_rfl]
    rfl
  -- the base row factor of `Ψ` is the class of `pbC β`
  have hRb : Rb 𝕜 p s β = (Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 2 s s).comap
        (pZ 𝕜 (Wc 𝕜 p) 2 s s).subtype))
        ⟨pbC 𝕜 p s β.1, pbC_mem_pZ_two 𝕜 p s β⟩ :=
    Rb_eq_mkQ 𝕜 p s β (pbC_mem_pZ_two 𝕜 p s β)
  -- the page product `pd_mul` of the two factors is the transport of the "pure" product
  have hstep : pd_mul 2 s s 0 (0 + q) (Rb 𝕜 p s β)
        (e2ColAll 𝕜 p e₀ N hfib hconn hfin q (rho 𝕜 E B p e₀ q
          ((Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 2 0 q).comap (pZ 𝕜 (Wc 𝕜 p) 2 0 q).subtype)) y)))
      = pCast 𝕜 (Wc 𝕜 p) 2 (show s + 0 = s + 0 by omega) (show s + q = s + (0 + q) by omega)
          (pd_mul 2 s s 0 q
            ((Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 2 s s).comap
              (pZ 𝕜 (Wc 𝕜 p) 2 s s).subtype)) ⟨pbC 𝕜 p s β.1, pbC_mem_pZ_two 𝕜 p s β⟩)
            ((Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 2 0 q).comap
              (pZ 𝕜 (Wc 𝕜 p) 2 0 q).subtype)) y)) := by
    rw [hRb, hA, ← pCast_self_apply 𝕜 (Wc 𝕜 p) 2 (rfl : s = s) (rfl : s = s)
      ((Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 2 s s).comap
        (pZ 𝕜 (Wc 𝕜 p) 2 s s).subtype)) ⟨pbC 𝕜 p s β.1, pbC_mem_pZ_two 𝕜 p s β⟩)]
    exact (pd_mul_pCast_apply 𝕜 (Wc 𝕜 p) 2 s s 0 q s s 0 (0 + q)
      (rfl : s = s) (rfl : s = s) (rfl : 0 = 0) (show q = 0 + q by omega)
      (show s + 0 = s + 0 by omega) (show s + q = s + (0 + q) by omega)
      ((Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 2 s s).comap
        (pZ 𝕜 (Wc 𝕜 p) 2 s s).subtype)) ⟨pbC 𝕜 p s β.1, pbC_mem_pZ_two 𝕜 p s β⟩)
      ((Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 2 0 q).comap
        (pZ 𝕜 (Wc 𝕜 p) 2 0 q).subtype)) y)).symm
  -- unfold `mssMul` on a row class times a column class and merge the transports
  rw [mssMul_row_col]
  rw [pEcast_hom_apply]
  rw [hstep]
  rw [pd_mul_nat]
  rw [pCast_comp_apply]
  rw [← pEcast_hom_apply]
  rw [pd_pEcast_mkQ']
  -- it remains to identify the two lifts of `pd_mulZ`/`pairElem` in `Z_2^s`
  apply pd_mkQ_congr
  exact e2LbarPairElem_xcast 𝕜 p s q β y _

end Work.Pi6.MSS
