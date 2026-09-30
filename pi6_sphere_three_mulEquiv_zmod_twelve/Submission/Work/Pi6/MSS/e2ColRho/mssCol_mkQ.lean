import Mathlib
import Submission.Work.Pi6.MSS.AssembleCore
import Submission.Work.Pi6.MSS.pagesData
import Submission.Work.Pi6.MSS.mssBotIter_mkQ
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS.e2ColRho

open Work.Pi6.MSS

/-- The concrete zeroth-column inclusion `mssCol 𝕜 W r q : E_{r+1}^{0,q} → E_r^{0,q}` is the
naive inclusion of subquotients on classes: the class in `E_{r+1}^{0,q}` of a cycle
`z ∈ Z_{r+1}^0` maps to the class of the same element (viewed in `Z_r^0`) in `E_r^{0,q}`.
Here `EI ((0:ℤ),(q:ℤ))` and `EN ((0:ℤ),(q:ℤ))` are the `ℕ`-indices of the bidegree `(0,q)` of
`mssE`.  Ingredients: `mssCol_spec` (or `LinearEquiv.apply_symm_apply` for `mssProjEquiv`),
`mssProj_apply`, `mssProjAux_eq_pd_proj`, `pd_proj_eq_mkQ` (the row analogue, in
`Submission/Work/Pi6/MSS/mssBotIter_mkQ.lean`), `pd_cycR`, `pd_cycR_val`, `Subtype.ext`; the
hypothesis that `pd_cycR r .. z` is a cycle of `d_r` comes from `pd_pZ_succ_le_K`. -/
theorem mssCol_mkQ (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r : ℕ) (hr : 2 ≤ r) (q : ℕ)
    (z : ↥(pZ 𝕜 W (r + 1) (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ))))) :
    mssCol 𝕜 W r (q : ℤ)
        (Submodule.mkQ ((pDen 𝕜 W (r + 1) (EI ((0 : ℤ), (q : ℤ)))
          (EN ((0 : ℤ), (q : ℤ)))).comap
          (pZ 𝕜 W (r + 1) (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ)))).subtype) z)
      = Submodule.mkQ ((pDen 𝕜 W r (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ)))).comap
          (pZ 𝕜 W r (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ)))).subtype)
          (pd_cycR r (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ))) z) := by
  -- `z ∈ Z_{r+1}^0` lies in the preimage `pd_K` of the cycles of `d_r`.
  have hzK : z.1 ∈ pd_K 𝕜 W r (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ))) :=
    pd_pZ_succ_le_K r (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ))) z.2
  -- Its class in `E_r^0` is a cycle of `d_r`, i.e. an element of the source of `mssProj`.
  set w : ↥(LinearMap.ker (pD 𝕜 W r (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ)))).hom) :=
    pd_Phi 𝕜 W r (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ))) ⟨z.1, hzK⟩ with hwdef
  -- `w` is exactly the class of the surviving representative `z` in `E_r^0`.
  have hwval : (w : mssE 𝕜 W r ((0 : ℤ), (q : ℤ)))
      = Submodule.mkQ ((pDen 𝕜 W r (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ)))).comap
          (pZ 𝕜 W r (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ)))).subtype)
          (pd_cycR r (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ))) z) := by
    rw [show (w : mssE 𝕜 W r ((0 : ℤ), (q : ℤ)))
        = Submodule.mkQ _ (pd_cyc r (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ))) ⟨z.1, hzK⟩)
        from pd_Phi_cyc r _ _ _]
    exact congrArg (Submodule.mkQ _) (Subtype.ext rfl)
  have hwker : (w : mssE 𝕜 W r ((0 : ℤ), (q : ℤ)))
      ∈ (mssD 𝕜 W r ((0 : ℤ), (q : ℤ)) (((0 : ℤ), (q : ℤ)) + vr r)).hom.ker := by
    rw [mssD_self]
    exact mem_ker_mssDMain 𝕜 W r _ w.2
  -- The projection `ker d_r → E_{r+1}^0` sends `w` (the class of `z`) to the class of `z`.
  have hproj : mssProj 𝕜 W r ((0 : ℤ), (q : ℤ)) ⟨(w : mssE 𝕜 W r ((0 : ℤ), (q : ℤ))), hwker⟩
      = Submodule.mkQ ((pDen 𝕜 W (r + 1) (EI ((0 : ℤ), (q : ℤ)))
          (EN ((0 : ℤ), (q : ℤ)))).comap
          (pZ 𝕜 W (r + 1) (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ)))).subtype) z := by
    rw [mssProj_apply 𝕜 W r _ hr, mssProjAux_eq_pd_proj 𝕜 W r hr]
    have hE : (⟨(mssKerIncl 𝕜 W r ((0 : ℤ), (q : ℤ))
            ⟨(w : mssE 𝕜 W r ((0 : ℤ), (q : ℤ))), hwker⟩).1,
          mssProjAux_mem 𝕜 W r hr _ (mssKerIncl 𝕜 W r ((0 : ℤ), (q : ℤ))
            ⟨(w : mssE 𝕜 W r ((0 : ℤ), (q : ℤ))), hwker⟩)⟩
        : ↥(LinearMap.ker (pD 𝕜 W r (EI ((0 : ℤ), (q : ℤ)))
            (EN ((0 : ℤ), (q : ℤ)))).hom)) = w := by
      refine Subtype.ext ?_
      rw [mssKerIncl_coe]
    rw [hE]
    exact pd_proj_eq_mkQ 𝕜 W r (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ))) z.1
      (pd_cycR r (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ))) z).2 z.2 w.2
  -- `mssCol` is the inverse of `mssProj` on the cycles, so it recovers the class of `z`.
  rw [← hproj]
  rw [mssCol_spec 𝕜 W r (q : ℤ) hr ⟨(w : mssE 𝕜 W r ((0 : ℤ), (q : ℤ))), hwker⟩]
  exact hwval

end Work.Pi6.MSS.e2ColRho
