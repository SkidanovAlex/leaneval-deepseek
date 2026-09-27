import Mathlib
import Submission.Work.KT.Fund.kbi_defs
import Submission.Work.KT.Fund.kappa_homotopic
import Submission.Work.KT.Fund.kbi_hopfsq
import Submission.Work.KT.Fund.kappa_hopf_defs
import Submission.Work.KT.Fund.kappa_hopf_graphproj
import Submission.Work.KT.Fund.kappa_hopf_reciproj
import Submission.Work.KT.Fund.kappa_hopf_pullup
import Submission.Work.KT.Fund.kappa_hopf_pulldn
import Submission.Work.KT.Fund.kappa_hopf_F0lift
import Submission.Work.KT.Fund.kappa_indep

/-!
# `Work.KT.Fund.kbi_hopf2`

The class of the clutched idempotent built from the two explicit rank-one projections
`h1e`, `h2e` (the projections onto the lines spanned by `(1, ζ)` and `(ζ̄, 1)` on the two
hemispheres) is the pull-back of the Hopf idempotent to `X × S²`.

Strategy.  The two rank-one projections are the orthogonal projections onto the graph /
reciprocal graph of the *coordinate* `ζ` (resp. `ζ̄`):

* `h1e = graphProj !![ζ]` (`zeta` is the disc coordinate, `h1e` its `Fin 1 ⊕ Fin 1` form),
* `h2e = recipProj !![ζ̄]`.

Since `ζ` restricts to the tautological unit `z` and `ζ̄` to `z⁻¹` on the circle, the pair
`(!![ζ], !![ζ̄])` is a pair of lifts of `(z, z⁻¹)`; so is the pair `(F₀, G₀)` of `kappa_hopf`.
`kappa_indep` then says the two clutched classes agree, and the explicit computation of
`pullUp`/`pullDn` of the Hopf idempotent (`kappa_hopf_graphproj` … `kappa_hopf_pulldn`)
identifies the class with `snd^*(cls hopfIdem)`.
-/

namespace Work.KT.Fund

open _root_.Matrix

noncomputable section

/-! ## `h1e`/`h2e` as graph / reciprocal-graph projections of the disc coordinate -/

/-- `h1e`, the projection onto the line spanned by `(1, ζ)`, is the orthogonal projection
onto the graph of the disc coordinate `ζ`. -/
lemma kbi_h1e_eq_graphProj (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    KBI.h1e X = graphProj (KBI.kdD X) !![KBI.zc X] := by
  have hstar : star (KBI.zc X) = KBI.zcb X := by
    ext p; simp [KBI.zc, KBI.zcb, ContinuousMap.star_apply]
  have h1 : (1 + star (KBI.zc X) * KBI.zc X) * KBI.zcn X = 1 := by
    rw [hstar, mul_comm (KBI.zcb X) (KBI.zc X),
      mul_comm (1 + KBI.zc X * KBI.zcb X) (KBI.zcn X)]
    exact KBI.zcn_mul_one_add X
  have h2 : KBI.zcn X * (1 + star (KBI.zc X) * KBI.zc X) = 1 := by
    rw [hstar, mul_comm (KBI.zcb X) (KBI.zc X)]
    exact KBI.zcn_mul_one_add X
  have hmain : Matrix.reindex finSumFinEquiv finSumFinEquiv
      (graphProj (KBI.kdD X) !![KBI.zc X]) = KBI.h1m X := by
    rw [graphProj_one (KBI.zc X) (KBI.zcn X) h1 h2]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [KBI.h1m, hstar] <;> ring
  rw [KBI.h1e, ← hmain, ← Matrix.reindex_symm]
  exact Equiv.symm_apply_apply _ _

/-- `h2e`, the projection onto the line spanned by `(ζ̄, 1)`, is the orthogonal projection
onto the reciprocal graph of the conjugate coordinate `ζ̄`. -/
lemma kbi_h2e_eq_recipProj (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    KBI.h2e X = recipProj (KBI.kdD X) !![KBI.zcb X] := by
  have hstar : star (KBI.zcb X) = KBI.zc X := by
    ext p; simp [KBI.zc, KBI.zcb, ContinuousMap.star_apply]
  have h1 : (1 + star (KBI.zcb X) * KBI.zcb X) * KBI.zcn X = 1 := by
    rw [hstar, mul_comm (1 + KBI.zc X * KBI.zcb X) (KBI.zcn X)]
    exact KBI.zcn_mul_one_add X
  have h2 : KBI.zcn X * (1 + star (KBI.zcb X) * KBI.zcb X) = 1 := by
    rw [hstar]
    exact KBI.zcn_mul_one_add X
  have hmain : Matrix.reindex finSumFinEquiv finSumFinEquiv
      (recipProj (KBI.kdD X) !![KBI.zcb X]) = KBI.h2m X := by
    rw [recipProj_one (KBI.zcb X) (KBI.zcn X) h1 h2]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [KBI.h2m, hstar] <;> ring
  rw [KBI.h2e, ← hmain, ← Matrix.reindex_symm]
  exact Equiv.symm_apply_apply _ _

/-! ## Boundary values -/

/-- The `1 × 1` matrix of the coordinate lifts to the tautological unit on the circle. -/
lemma bdry_zzc (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    (!![KBI.zc X]).map (fun f => bdryRestrict X f)
      = (↑(zUnitMat X) : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) := by
  apply Matrix.ext
  intro i j
  fin_cases i; fin_cases j
  rw [Matrix.map_apply]
  show bdryRestrict X (KBI.zc X) = (zUnitMat X : Matrix (Fin 1) (Fin 1) _) 0 0
  rw [zUnitMat_apply]
  exact KBI.bdryRestrict_zc X

/-- Entry `(0,0)` of the inverse `1 × 1` matrix. -/
lemma coe_inv_zUnitMat_apply (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    (↑((zUnitMat X)⁻¹) : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) 0 0
      = ↑((Work.KT.zUnit X)⁻¹) := by
  have h : (↑((zUnitMat X)⁻¹) : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ))
      = Matrix.scalar (Fin 1) (↑((Work.KT.zUnit X)⁻¹)) := by
    rw [zUnitMat, Units.coe_map_inv]; rfl
  rw [h, Matrix.scalar_apply, diagonal_apply_eq]

/-- The `1 × 1` matrix of the conjugate coordinate lifts to `z⁻¹` on the circle. -/
lemma bdry_zzcb (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    (!![KBI.zcb X]).map (fun f => bdryRestrict X f)
      = (↑((zUnitMat X)⁻¹) : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) := by
  apply Matrix.ext
  intro i j
  fin_cases i; fin_cases j
  rw [Matrix.map_apply]
  show bdryRestrict X (KBI.zcb X) = (↑((zUnitMat X)⁻¹) : Matrix (Fin 1) (Fin 1) _) 0 0
  rw [coe_inv_zUnitMat_apply X]
  exact KBI.bdryRestrict_zcb X

/-- The lift `G₀ = !![star g]` of `kappa_hopf` restricts to `z⁻¹` on the circle. -/
lemma bdry_G0 (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    (G0 X).map (fun f => bdryRestrict X f)
      = (↑((zUnitMat X)⁻¹) : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) := by
  apply Matrix.ext
  intro i j
  fin_cases i; fin_cases j
  rw [Matrix.map_apply]
  show bdryRestrict X (star (gFun X)) = (↑((zUnitMat X)⁻¹) : Matrix (Fin 1) (Fin 1) _) 0 0
  rw [coe_inv_zUnitMat_apply X]
  rw [bdryRestrict_semiconj_star X (gFun X)]
  rw [show bdryRestrict X (gFun X) = (↑(Work.KT.zUnit X) : C(X × Sph ℂ, ℂ)) from by
        have h1 := congrFun (congrFun (kappa_hopf_F0lift X) 0) 0
        rw [Matrix.map_apply] at h1
        rw [zUnitMat_apply] at h1
        simpa [F0] using h1]
  exact KBI.star_zUnit_eq_inv X

/-! ## The main theorem -/

theorem kbi_hopf2 (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (h : (Work.KT.Fund.KBI.h1e X).map (fun f => Work.KT.Fund.bdryRestrict X f) =
      (Work.KT.Fund.KBI.h2e X).map (fun f => Work.KT.Fund.bdryRestrict X f)) :
    (Work.KT.Fund.k0Glue X) (Work.KT.K0.mapA (Work.KT.pullAlg (ContinuousMap.snd : C(X × Work.KT.S2, Work.KT.S2))) (Work.KT.cls Work.KT.hopfIdem)) =
      Work.KT.cls (Work.KT.Fund.pairIdem X (Work.KT.Fund.KBI.h1e X) (Work.KT.Fund.KBI.h2e X) h) := by
  -- Boundary-value proofs for the four lifts.
  have hF : (!![KBI.zc X]).map (fun f => bdryRestrict X f)
      = (↑(zUnitMat X) : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) := bdry_zzc X
  have hG : (!![KBI.zcb X]).map (fun f => bdryRestrict X f)
      = (↑((zUnitMat X)⁻¹) : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) := bdry_zzcb X
  have hF0 : (F0 X).map (fun f => bdryRestrict X f)
      = (↑(zUnitMat X) : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) := kappa_hopf_F0lift X
  have hG0 : (G0 X).map (fun f => bdryRestrict X f)
      = (↑((zUnitMat X)⁻¹) : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) := bdry_G0 X
  -- The Hopf idempotent's two disc restrictions in disc coordinates.
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
  -- `k0Glue` of the pulled-back Hopf class, in the fibre product.
  have hR : k0Glue X (K0.mapA (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem))
      = cls (Mat.map ((glueEquiv X) : C(X × S2, ℂ) →+* pullAlg2 X)
          (Mat.map ((pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom) hopfIdem)) := by
    show K0.map ((glueEquiv X) : C(X × S2, ℂ) →+* pullAlg2 X)
        (K0.map ((pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom) (cls hopfIdem)) = _
    rw [K0.map_cls _ hopfIdem_isIdem, K0.map_cls _ (hopfIdem_isIdem.map _)]
  -- The two pairs of lifts define the same clutched class.
  have hclutch : clutchIdem X 1 (zUnitMat X) (!![KBI.zc X]) (!![KBI.zcb X]) hF hG
      = pairIdem X (graphProj (KBI.kdD X) !![KBI.zc X]) (recipProj (KBI.kdD X) !![KBI.zcb X])
          (clutch_agree X 1 (zUnitMat X) (!![KBI.zc X]) (!![KBI.zcb X]) hF hG) :=
    clutchIdem_eq_pairIdem X (zUnitMat X) (!![KBI.zc X]) (!![KBI.zcb X]) hF hG
      (clutch_agree X 1 (zUnitMat X) (!![KBI.zc X]) (!![KBI.zcb X]) hF hG)
  have hkindep : cls (clutchIdem X 1 (zUnitMat X) (!![KBI.zc X]) (!![KBI.zcb X]) hF hG)
      = cls (clutchIdem X 1 (zUnitMat X) (F0 X) (G0 X) hF0 hG0) :=
    kappa_indep X 1 (zUnitMat X) (!![KBI.zc X]) (F0 X) (!![KBI.zcb X]) (G0 X) hF hF0 hG hG0
  have hpair : pairIdem X (KBI.h1e X) (KBI.h2e X) h
      = pairIdem X (graphProj (KBI.kdD X) !![KBI.zc X]) (recipProj (KBI.kdD X) !![KBI.zcb X])
          (clutch_agree X 1 (zUnitMat X) (!![KBI.zc X]) (!![KBI.zcb X]) hF hG) :=
    pairIdem_congr X (kbi_h1e_eq_graphProj X) (kbi_h2e_eq_recipProj X) h
      (clutch_agree X 1 (zUnitMat X) (!![KBI.zc X]) (!![KBI.zcb X]) hF hG)
  calc (k0Glue X) (K0.mapA (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem))
      = cls (Mat.map ((glueEquiv X) : C(X × S2, ℂ) →+* pullAlg2 X)
          (Mat.map ((pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom) hopfIdem)) := hR
    _ = cls (clutchIdem X 1 (zUnitMat X) (F0 X) (G0 X) hF0 hG0) := (congrArg cls hmat).symm
    _ = cls (clutchIdem X 1 (zUnitMat X) (!![KBI.zc X]) (!![KBI.zcb X]) hF hG) := hkindep.symm
    _ = cls (pairIdem X (graphProj (KBI.kdD X) !![KBI.zc X]) (recipProj (KBI.kdD X) !![KBI.zcb X])
          (clutch_agree X 1 (zUnitMat X) (!![KBI.zc X]) (!![KBI.zcb X]) hF hG)) :=
        congrArg cls hclutch
    _ = cls (pairIdem X (KBI.h1e X) (KBI.h2e X) h) := (congrArg cls hpair).symm

end

end Work.KT.Fund
