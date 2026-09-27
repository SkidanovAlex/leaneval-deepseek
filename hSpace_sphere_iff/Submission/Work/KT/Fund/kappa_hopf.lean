import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kappa_indep
import Submission.Work.KT.Fund.kappa_hopf_defs
import Submission.Work.KT.Fund.kappa_hopf_pullup
import Submission.Work.KT.Fund.kappa_hopf_pulldn
import Submission.Work.KT.Fund.kappa_hopf_graphproj
import Submission.Work.KT.Fund.kappa_hopf_reciproj
import Submission.Work.KT.Fund.kappa_hopf_F0lift
import Submission.Work.KT.Fund.kappa_hopf_G0lift

/-!
# `Work.KT.Fund.kappa_hopf` — the clutched class of the coordinate unit is the Hopf class

For a compact Hausdorff space `X` the clutched class `κ(z)` of the coordinate unit `z` on the
circle (`Work.KT.Fund.kappa X 1 (zUnitMat X)`) is the pull-back
`K0.mapA (pullAlg snd) (cls hopfIdem)` of the Hopf line bundle from `S²` to `X × S²`.

The two sides are classes of rank-one idempotents over `X × S²`.  Transported along the two-disc
decomposition `glueEquiv : C(X × S², ℂ) ≃ₐ[ℂ] pullAlg2 X` they are the `2 × 2` matrices over the
fibre product `pullAlg2 X` glued from the orthogonal projection onto the graph of the upper lift
`F₀ = !![g]` and the reciprocal graph of the lower lift `G₀ = !![star g]`, `g = c/(1+s)` with
`c` the disc coordinate and `s = √(1-‖c‖²)`:

* `kappa_hopf_graphproj`, `kappa_hopf_reciproj` evaluate the two orthogonal projections,
* `kappa_hopf_pullup`, `kappa_hopf_pulldn` evaluate the two restrictions of the Hopf idempotent,
and the two computations agree entrywise.  `kappa_hopf_F0lift`/`kappa_hopf_G0lift` identify the
lifts with `z` and `z⁻¹` on the boundary circle, so `kappa_indep` (independence of the clutched
class in the lifts) applies.
-/

namespace Work.KT.Fund

open _root_.Matrix

noncomputable section

theorem kappa_hopf (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    Work.KT.Fund.kappa X 1 (Work.KT.Fund.zUnitMat X)
      = Work.KT.K0.mapA (Work.KT.pullAlg (ContinuousMap.snd : C(X × S2, S2)))
          (Work.KT.cls Work.KT.hopfIdem) := by
  -- The boundary values of the two explicit lifts, in the form used by `kappa_indep`.
  have hF0 : (F0 X).map (fun f => bdryRestrict X f)
      = (zUnitMat X : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) := kappa_hopf_F0lift X
  have hG0 : (G0 X).map (fun f => bdryRestrict X f)
      = (((zUnitMat X)⁻¹ : (Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) := by
    simpa using (kappa_hopf_G0lift X)
  -- The canonical `κ` uses Tietze lifts; replace them by the explicit ones.
  have hkey : kappa X 1 (zUnitMat X)
      = (k0Glue X).symm (cls (clutchIdem X 1 (zUnitMat X) (F0 X) (G0 X) hF0 hG0)) := by
    rw [kappa_val X 1 (zUnitMat X)]
    congr 1
    exact kappa_indep X 1 (zUnitMat X) _ (F0 X) _ (G0 X) _ hF0 _ hG0
  -- The two glued idempotents agree.
  have hmat : clutchIdem X 1 (zUnitMat X) (F0 X) (G0 X) hF0 hG0
      = Mat.map ((glueEquiv X) : C(X × S2, ℂ) →+* pullAlg2 X)
          (Mat.map ((pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom) hopfIdem) := by
    have hgraph : (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (graphProj C(X × Ball ℂ, ℂ) (F0 X)))
        = (hopfMat.map ((pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom)).map
            (pullUp X) :=
      (kappa_hopf_graphproj X).trans (kappa_hopf_pullup X).symm
    have hrecip : (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (recipProj C(X × Ball ℂ, ℂ) (G0 X)))
        = (hopfMat.map ((pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom)).map
            (pullDn X) :=
      (kappa_hopf_reciproj X).trans (kappa_hopf_pulldn X).symm
    rw [hopfIdem_eq]
    show (⟨1 + 1, Matrix.reindex finSumFinEquiv finSumFinEquiv
        (pairMat X (graphProj C(X × Ball ℂ, ℂ) (F0 X))
          (recipProj C(X × Ball ℂ, ℂ) (G0 X))
          (clutch_agree X 1 (zUnitMat X) (F0 X) (G0 X) hF0 hG0))⟩ : Mat ↥(pullAlg2 X))
      = (⟨2, (hopfMat.map ((pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom)).map
            ((glueEquiv X) : C(X × S2, ℂ) →+* pullAlg2 X)⟩ : Mat ↥(pullAlg2 X))
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Matrix.ext
      intro i j
      refine Subtype.ext ?_
      refine Prod.ext ?_ ?_
      · show graphProj C(X × Ball ℂ, ℂ) (F0 X) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
            = pullUp X ((pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom (hopfMat i j))
        exact congrFun (congrFun hgraph i) j
      · show recipProj C(X × Ball ℂ, ℂ) (G0 X) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
            = pullDn X ((pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom (hopfMat i j))
        exact congrFun (congrFun hrecip i) j
  -- The right-hand side, in `K0` of the fibre product.
  have hR : k0Glue X (K0.mapA (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem))
      = cls (Mat.map ((glueEquiv X) : C(X × S2, ℂ) →+* pullAlg2 X)
          (Mat.map ((pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom) hopfIdem)) := by
    show K0.map ((glueEquiv X) : C(X × S2, ℂ) →+* pullAlg2 X)
        (K0.map ((pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom) (cls hopfIdem)) = _
    rw [K0.map_cls _ hopfIdem_isIdem, K0.map_cls _ (hopfIdem_isIdem.map _)]
  apply (k0Glue X).injective
  rw [hkey, AddEquiv.apply_symm_apply, hmat, hR]

end

end Work.KT.Fund
