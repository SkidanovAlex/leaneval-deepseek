import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.Fund.Clutch
import Submission.Work.KT.Fund.orthProj_mul_unit
import Submission.Work.KT.Fund.map_orthProj
import Submission.Work.KT.Fund.isUnit_one_add_conjTranspose_mul
import Submission.Work.KT.Fund.graphB_recipB_conjTranspose_mul_self
import Submission.Work.KT.Fund.map_graphB_recipB
import Submission.Work.KT.Fund.recipB_eq_graphB_mul

namespace Work.KT.Fund


/-- The boundary restriction `C(X × D, ℂ) → C(X × S¹, ℂ)` commutes with the star
(pointwise complex conjugation), i.e. it is a star-compatible ring homomorphism. -/
lemma bdryRestrict_semiconj_star (X : Type) [TopologicalSpace X] :
    Function.Semiconj ⇑(bdryRestrict X) star star := by
  intro f
  ext p
  simp [bdryRestrict_apply, ContinuousMap.star_apply]

/-- The two orthogonal projections used in the clutching construction agree on the equator.  With `u` an invertible matrix over `C(X × S¹, ℂ)`, `F` a lift of `u` to the upper disc, `G` a lift of `u⁻¹` to the lower disc: the orthogonal projection onto `im [[1],[F]]` restricts to the same matrix on the boundary circle as the orthogonal projection onto `im [[G],[1]]`.  Reason: on the equator `im [[1],[u]] = im [[u⁻¹],[1]]` (the graph of `u` is the reciprocal graph of `u⁻¹`); concretely, with `Q = 1 + uᴴu`, one has `[[u⁻¹],[1]] = [[1],[u]] u⁻¹`, hence `orthProj [[u⁻¹],[1]] = orthProj [[1],[u]]` as soon as `Q` is a unit, which it is pointwise (`1 + u(x)ᴴu(x)` is positive definite). -/
theorem clutch_agree (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ)
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (F : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hF : F.map (fun f => bdryRestrict X f) = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hG : G.map (fun f => bdryRestrict X f) = ((↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))) :
    (graphProj C(X × Ball ℂ, ℂ) F).map (fun f => bdryRestrict X f)
      = (recipProj C(X × Ball ℂ, ℂ) G).map (fun f => bdryRestrict X f) := by
  let φ : C(X × Ball ℂ, ℂ) →+* C(X × Sph ℂ, ℂ) := bdryRestrict X
  let uM : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) := ↑u
  let uI : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) := ↑(u⁻¹)
  have hφstar : Function.Semiconj ⇑φ star star := bdryRestrict_semiconj_star X
  have hF' : F.map ⇑φ = uM := hF
  have hG' : G.map ⇑φ = uI := hG
  -- Both Gram matrices `Bᴴ B` are units, being `1 + Aᴴ A` for `A = F` (resp. `G`).
  have hQgraph : IsUnit
      ((graphB C(X × Ball ℂ, ℂ) F).conjTranspose * graphB C(X × Ball ℂ, ℂ) F) := by
    rw [(graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) F G).1]
    exact isUnit_one_add_conjTranspose_mul F
  have hQrecip : IsUnit
      ((recipB C(X × Ball ℂ, ℂ) G).conjTranspose * recipB C(X × Ball ℂ, ℂ) G) := by
    rw [(graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) F G).2]
    exact isUnit_one_add_conjTranspose_mul G
  -- The upper projection restricts to the projection onto `im [[1],[u]]`.
  have hL : (graphProj C(X × Ball ℂ, ℂ) F).map ⇑φ
      = orthProj C(X × Sph ℂ, ℂ) (graphB C(X × Sph ℂ, ℂ) uM) := by
    unfold graphProj
    rw [map_orthProj φ hφstar (graphB C(X × Ball ℂ, ℂ) F) hQgraph,
        (map_graphB_recipB φ F).1, hF']
  -- The lower projection restricts to the projection onto `im [[u⁻¹],[1]]`.
  have hR : (recipProj C(X × Ball ℂ, ℂ) G).map ⇑φ
      = orthProj C(X × Sph ℂ, ℂ) (recipB C(X × Sph ℂ, ℂ) uI) := by
    unfold recipProj
    rw [map_orthProj φ hφstar (recipB C(X × Ball ℂ, ℂ) G) hQrecip,
        (map_graphB_recipB φ G).2, hG']
  -- On the equator `[[u⁻¹],[1]] = [[1],[u]] u⁻¹`, so the two projections coincide.
  have hstep : orthProj C(X × Sph ℂ, ℂ) (recipB C(X × Sph ℂ, ℂ) uI)
      = orthProj C(X × Sph ℂ, ℂ) (graphB C(X × Sph ℂ, ℂ) uM) := by
    have hmul : uM * uI = 1 := Units.mul_inv u
    rw [recipB_eq_graphB_mul C(X × Sph ℂ, ℂ) uI uM hmul]
    exact orthProj_mul_unit C(X × Sph ℂ, ℂ) (graphB C(X × Sph ℂ, ℂ) uM) uI ⟨u⁻¹, rfl⟩
  change (graphProj C(X × Ball ℂ, ℂ) F).map ⇑φ
      = (recipProj C(X × Ball ℂ, ℂ) G).map ⇑φ
  rw [hL, hR, hstep]

end Work.KT.Fund
