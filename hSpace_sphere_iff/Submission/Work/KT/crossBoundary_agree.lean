import Mathlib
import Submission.Work.KT.Fund.Clutch
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.Fund.map_graphB_recipB
import Submission.Work.KT.Fund.map_orthProj
import Submission.Work.KT.Fund.graphB_recipB_conjTranspose_mul_self
import Submission.Work.KT.Fund.isUnit_one_add_conjTranspose_mul
import Submission.Work.KT.Fund.orthProj_mul_unit
import Submission.Work.KT.Fund.recipB_eq_graphB_mul
import Submission.Work.KT.Fund.clutch_agree

namespace Work.KT

/-- Boundary compatibility of the **mixed** orthogonal projection of the clutching construction:
the outer factor is the graph (resp. reciprocal graph) of one lift, while the Gram matrix that is
inverted comes from a possibly different lift.  As long as the two lifts agree on the boundary
(`hBB'`) and that Gram matrix is a unit, the boundary restriction of the mixed expression is the
orthogonal projection onto the image of the common boundary matrix.

This is the computation underlying `Work.KT.crossBoundary_agree`. -/
theorem map_mix_orthProj {n : ℕ} (X : Type) [TopologicalSpace X]
    (φ : C(X × Ball ℂ, ℂ) →+* C(X × Sph ℂ, ℂ))
    (hφ : Function.Semiconj ⇑φ star star)
    (B B' : Matrix (Fin n ⊕ Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hBB' : B.map ⇑φ = B'.map ⇑φ)
    (hQ : IsUnit (B'.conjTranspose * B')) :
    (B * (Ring.inverse (B'.conjTranspose * B') * B'.conjTranspose)).map ⇑φ
      = Fund.orthProj C(X × Sph ℂ, ℂ) (B.map ⇑φ) := by
  rw [Matrix.map_mul, Matrix.map_mul, Fund.Matrix.map_ringInverse φ _ hQ,
    Matrix.conjTranspose_map ⇑φ hφ, Matrix.map_mul, Matrix.conjTranspose_map ⇑φ hφ, hBB']
  simp only [Fund.orthProj, Matrix.mul_assoc]

/-- On the equator, `graphB F * ((graphB F')ᴴ(graphB F'))⁻¹ * (graphB F')ᴴ` agrees with the
reciprocal analogue for `G, G'`: both restrict to the orthogonal projection onto the graph of `u`.
This is the compatibility of the cross Murray--von Neumann data with the boundary restriction. -/
theorem crossBoundary_agree (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (F G F' G' : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hF : F.map (Fund.bdryRestrict X) = ↑u)
    (hG : G.map (Fund.bdryRestrict X) = ↑(u⁻¹))
    (hF' : F'.map (Fund.bdryRestrict X) = ↑u)
    (hG' : G'.map (Fund.bdryRestrict X) = ↑(u⁻¹)) :
    (Fund.graphB C(X × Ball ℂ, ℂ) F
        * (Ring.inverse (Matrix.conjTranspose (Fund.graphB C(X × Ball ℂ, ℂ) F')
              * Fund.graphB C(X × Ball ℂ, ℂ) F')
            * Matrix.conjTranspose (Fund.graphB C(X × Ball ℂ, ℂ) F'))).map (Fund.bdryRestrict X)
      = (Fund.recipB C(X × Ball ℂ, ℂ) G
        * (Ring.inverse (Matrix.conjTranspose (Fund.recipB C(X × Ball ℂ, ℂ) G')
              * Fund.recipB C(X × Ball ℂ, ℂ) G')
            * Matrix.conjTranspose (Fund.recipB C(X × Ball ℂ, ℂ) G'))).map
          (Fund.bdryRestrict X) := by
  let φ : C(X × Ball ℂ, ℂ) →+* C(X × Sph ℂ, ℂ) := Fund.bdryRestrict X
  let uM : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) := ↑u
  let uI : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) := ↑(u⁻¹)
  have hφstar : Function.Semiconj ⇑φ star star := Fund.bdryRestrict_semiconj_star X
  -- Both Gram matrices `Bᴴ B` are units, being `1 + Aᴴ A` for `A = F'` (resp. `G'`).
  have hQgraph : IsUnit ((Fund.graphB C(X × Ball ℂ, ℂ) F').conjTranspose
      * Fund.graphB C(X × Ball ℂ, ℂ) F') := by
    rw [(Fund.graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) F' G').1]
    exact Fund.isUnit_one_add_conjTranspose_mul F'
  have hQrecip : IsUnit ((Fund.recipB C(X × Ball ℂ, ℂ) G').conjTranspose
      * Fund.recipB C(X × Ball ℂ, ℂ) G') := by
    rw [(Fund.graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) F' G').2]
    exact Fund.isUnit_one_add_conjTranspose_mul G'
  -- The two graph (resp. reciprocal-graph) blocks agree after restriction to the boundary.
  have hFF' : (Fund.graphB C(X × Ball ℂ, ℂ) F).map ⇑φ
      = (Fund.graphB C(X × Ball ℂ, ℂ) F').map ⇑φ := by
    rw [(Fund.map_graphB_recipB φ F).1, (Fund.map_graphB_recipB φ F').1]
    rw [show F.map ⇑φ = F'.map ⇑φ from hF.trans hF'.symm]
  have hGG' : (Fund.recipB C(X × Ball ℂ, ℂ) G).map ⇑φ
      = (Fund.recipB C(X × Ball ℂ, ℂ) G').map ⇑φ := by
    rw [(Fund.map_graphB_recipB φ G).2, (Fund.map_graphB_recipB φ G').2]
    rw [show G.map ⇑φ = G'.map ⇑φ from hG.trans hG'.symm]
  -- The left-hand side restricts to the orthogonal projection onto `im [[1],[u]]`.
  have hL : (Fund.graphB C(X × Ball ℂ, ℂ) F
        * (Ring.inverse (Matrix.conjTranspose (Fund.graphB C(X × Ball ℂ, ℂ) F')
              * Fund.graphB C(X × Ball ℂ, ℂ) F')
            * Matrix.conjTranspose (Fund.graphB C(X × Ball ℂ, ℂ) F'))).map ⇑φ
      = Fund.orthProj C(X × Sph ℂ, ℂ) (Fund.graphB C(X × Sph ℂ, ℂ) uM) := by
    rw [map_mix_orthProj X φ hφstar _ _ hFF' hQgraph, (Fund.map_graphB_recipB φ F).1,
        show F.map ⇑φ = uM from hF]
  -- The right-hand side restricts to the orthogonal projection onto `im [[u⁻¹],[1]]`.
  have hR : (Fund.recipB C(X × Ball ℂ, ℂ) G
        * (Ring.inverse (Matrix.conjTranspose (Fund.recipB C(X × Ball ℂ, ℂ) G')
              * Fund.recipB C(X × Ball ℂ, ℂ) G')
            * Matrix.conjTranspose (Fund.recipB C(X × Ball ℂ, ℂ) G'))).map ⇑φ
      = Fund.orthProj C(X × Sph ℂ, ℂ) (Fund.recipB C(X × Sph ℂ, ℂ) uI) := by
    rw [map_mix_orthProj X φ hφstar _ _ hGG' hQrecip, (Fund.map_graphB_recipB φ G).2,
        show G.map ⇑φ = uI from hG]
  -- On the equator `[[u⁻¹],[1]] = [[1],[u]] u⁻¹`, so the two projections coincide.
  have hstep : Fund.orthProj C(X × Sph ℂ, ℂ) (Fund.recipB C(X × Sph ℂ, ℂ) uI)
      = Fund.orthProj C(X × Sph ℂ, ℂ) (Fund.graphB C(X × Sph ℂ, ℂ) uM) := by
    have hmul : uM * uI = 1 := Units.mul_inv u
    rw [Fund.recipB_eq_graphB_mul C(X × Sph ℂ, ℂ) uI uM hmul]
    exact Fund.orthProj_mul_unit C(X × Sph ℂ, ℂ) (Fund.graphB C(X × Sph ℂ, ℂ) uM) uI ⟨u⁻¹, rfl⟩
  rw [hL, hR, hstep]

end Work.KT
