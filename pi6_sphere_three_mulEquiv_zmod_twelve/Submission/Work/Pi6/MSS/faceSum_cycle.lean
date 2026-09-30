import Mathlib
import Submission.Work.SSSR.chainCondition_gen
import Submission.Work.SSSR.serreE1Assembly
import Submission.Work.SSSR.hornCok_d_faceLift
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The lifted Eilenberg–Zilber face sum is a cycle

`Work.SSSR.faceSum p hfib k q b σ h z` is the alternating sum of the face chains
`Work.SSSR.faceB` of the lifted Eilenberg–Zilber chain `Work.SSSR.iotaTLin`; it lives in the `k`-th
term `R_k = (Fc p).obj k` of the canonical Serre filtration of `C_*(E)` (the `k` here is the `s` of
the definitions, cf. `Work.SSSR.serreCC p (k+1)`), in total degree `k + q`.

The content of the lemma is that `faceSum` is a **cycle** of that filtered piece whenever `z` is a
cycle of the fibre.  This is the `hvcyc` input consumed by `Work.SSSR.kF_psiCoef_gen`.

Route (all ingredients are already proved in this workspace).

* `Work.SSSR.incF (Fc p) k : (Fc p).obj k ⟶ (Fc p).obj (k+1)` is injective in each degree, being a
  monomorphism of chain complexes (`Work.SSSR.Filtration.mono`, `ModuleCat.mono_iff_injective`), so
  it suffices to check the vanishing after applying it.
* `Work.SSSR.chainMap_comm_apply_elem` moves `incF` inside the differential,
  `incF (d (faceSum)) = d (incF (faceSum))`.
* `Work.SSSR.d_sndToR_iotaTLin` identifies `incF (faceSum)` with the boundary of the lifted chain
  `sCCMap (sndToR σ) (iotaTLin …)`.
* two consecutive differentials compose to zero (`HomologicalComplex.d_comp_d`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial Topology

/-- The elementwise form of `d ≫ d = 0` in a chain complex of modules. -/
private lemma d_comp_d_apply {R : Type} [CommRing R] [Nontrivial R]
    {K : ChainComplex (ModuleCat R) ℕ} {i j l : ℕ} (x : K.X i) :
    (ModuleCat.Hom.hom (K.d j l)) ((ModuleCat.Hom.hom (K.d i j)) x) = 0 := by
  rw [Work.SSSR.hom_comp_apply']
  rw [HomologicalComplex.d_comp_d]
  simp

/-- The alternating sum `Work.SSSR.faceSum` of the face chains of the lifted Eilenberg–Zilber chain
is a cycle of `(Fc p).obj k` as soon as the fibre chain `z` is a cycle. -/
theorem faceSum_cycle (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (k q : ℕ)
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1))
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).d q
      ((ComplexShape.down ℕ).next q))) z = 0) :
    (ModuleCat.Hom.hom (((Work.SSSR.Fc (R := 𝕜) p).obj k).d (k+q)
      ((ComplexShape.down ℕ).next (k+q))))
      (Work.SSSR.faceSum p hfib k q (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
        (Work.SSSR.sigHat σ) rfl z) = 0 := by
  -- Work with the `Work.SSSR.StemsB`-typed version of the fibration structure; the two notions are
  -- definitionally equal, and this keeps all subsequent terms well-typed at any transparency.
  have hfib' : Work.SSSR.StemsB.IsSerreFibration p := hfib
  show (ModuleCat.Hom.hom (((Work.SSSR.Fc (R := 𝕜) p).obj k).d (k+q)
      ((ComplexShape.down ℕ).next (k+q))))
      (Work.SSSR.faceSum p hfib' k q (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
        (Work.SSSR.sigHat σ) rfl z) = 0
  -- The boundary of the lifted chain, whose `incF`-image is `faceSum`.
  have hv := Work.SSSR.d_sndToR_iotaTLin (R := 𝕜) p hfib' k q
    (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) σ rfl z hz
  -- `incF` is a monomorphism of chain complexes, hence injective in each degree.
  haveI : Mono (Work.SSSR.incF (Work.SSSR.Fc (R := 𝕜) p) k) := (Work.SSSR.xiCan (R := 𝕜) p).mono k
  refine (ModuleCat.mono_iff_injective ((Work.SSSR.incF (Work.SSSR.Fc (R := 𝕜) p) k).f
    ((ComplexShape.down ℕ).next (k+q)))).mp inferInstance ?_
  rw [map_zero]
  -- Push `incF` inside the differential, then replace `incF (faceSum)` by the boundary of
  -- `sCCMap (sndToR σ) (iotaTLin …)`.
  rw [← Work.SSSR.chainMap_comm_apply_elem (Work.SSSR.incF (Work.SSSR.Fc (R := 𝕜) p) k)
    (Work.SSSR.faceSum p hfib' k q (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
      (Work.SSSR.sigHat σ) rfl z)]
  rw [← hv]
  -- Two consecutive differentials compose to zero.
  exact d_comp_d_apply _

end Work.Pi6.MSS
