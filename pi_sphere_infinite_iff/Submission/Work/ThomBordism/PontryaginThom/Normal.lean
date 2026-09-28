import Submission.Work.ThomBordism.PontryaginThom.Defs

/-!
# The normal Pontryagin numbers of an embedding, from the Whitney formula

For a closed oriented smooth `8`-manifold `V` embedded in `ℝ^{8+k}` with normal bundle `ν`, the
tangent and normal bundles satisfy `TV ⊕ ν ≅ ε^{8+k}`; by the Whitney formula
(`Submission/Work/Whitney/`) the total Pontryagin classes satisfy

`p(ν) ⌣ p(TV) = 1`   in `H^*(V;ℤ)` (truncated at degree `8`).

`NormalBundlData` records the two coefficients of this identity that the dimension forces
(`whitney4`, `whitney8`); here we extract their consequences, which are the classical relations

`p̄₁ = -p₁`,   `p̄₂ = p₁² - p₂`

between the normal classes `p̄₁ = q1`, `p̄₂ = q2` and the tangent classes `p₁`, `p₂`, and then the
**number** identities

`p̄₁²-number = p₁²-number`,   `p̄₂-number = p₁²-number - p₂-number`.

This is the "which are polynomials in the tangent ones" of item 2 of the chapter: the Pontryagin
numbers that the Hurewicz pairing of the Pontryagin–Thom class computes
(`PTRep.hurewicz_p1sq`, `PTRep.hurewicz_p2`) are the *tangent* numbers, so vanishing of the tangent
numbers makes the pairings vanish — with no topological invariance of Pontryagin classes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Work.ThomBordism.PontryaginThom

noncomputable section

open Work.Cohomology

variable {V : Man8}

/-- The normal first Pontryagin class is minus the tangent one, from the degree-`4` coefficient of
`p(ν) ⌣ p(TV) = 1`. -/
theorem NormalBundlData.q1_eq_neg (N : NormalBundlData V) : N.q1 = -V.p1 :=
  eq_neg_of_add_eq_zero_left N.whitney4

/-- The normal second Pontryagin class is `p₁² - p₂`, from the degree-`8` coefficient of
`p(ν) ⌣ p(TV) = 1`. -/
theorem NormalBundlData.q2_eq (N : NormalBundlData V) :
    N.q2 = cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 V.p1 V.p1 - V.p2 := by
  have h := N.whitney8
  rw [N.q1_eq_neg] at h
  have hc : cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 (-V.p1) V.p1
      = -(cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 V.p1 V.p1) := by
    have e : cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 (-V.p1)
        = -(cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 V.p1) := map_neg _ _
    rw [e, LinearMap.neg_apply]
  rw [hc] at h
  have h1 : N.q2
      = -(-(cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 V.p1 V.p1) + V.p2) := by
    have key : N.q2 + (-(cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 V.p1 V.p1) + V.p2) = 0 := by
      rw [← h]
      abel
    exact eq_neg_of_add_eq_zero_left key
  rw [h1]
  abel

/-- The normal `p₁²`-number equals the tangent `p₁²`-number: `⟨q₁ ⌣ q₁, [V]⟩ = ⟨p₁ ⌣ p₁, [V]⟩`. -/
theorem NormalBundlData.normalP1Sq_eq (N : NormalBundlData V) : N.normalP1Sq = V.p1Sq := by
  have h : cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 N.q1 N.q1
      = cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 V.p1 V.p1 := by
    rw [N.q1_eq_neg]
    have e1 : cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 (-V.p1)
        = -(cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 V.p1) := map_neg _ _
    have e2 : (cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 V.p1) (-V.p1)
        = -((cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 V.p1) V.p1) := map_neg _ _
    rw [e1, LinearMap.neg_apply, e2, neg_neg]
  show kronH ℤ (TopCat.toSSet.obj V.X) 8
      (cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 N.q1 N.q1) V.c
    = Work.SignatureBordism.p₁SqNumber (TopCat.toSSet.obj V.X) V.c V.p1
  rw [h, Work.SignatureBordism.p₁SqNumber_apply, Work.SignatureBordism.interForm_apply]

/-- The normal `p₂`-number is `p₁² - p₂` in the tangent numbers:
`⟨q₂, [V]⟩ = ⟨p₁ ⌣ p₁, [V]⟩ - ⟨p₂, [V]⟩`. -/
theorem NormalBundlData.normalP2_eq (N : NormalBundlData V) : N.normalP2 = V.p1Sq - V.p2Num := by
  show kronH ℤ (TopCat.toSSet.obj V.X) 8 N.q2 V.c
    = Work.SignatureBordism.p₁SqNumber (TopCat.toSSet.obj V.X) V.c V.p1
      - Work.SignatureBordism.p₂Number (TopCat.toSSet.obj V.X) V.c V.p2
  rw [N.q2_eq, map_sub, LinearMap.sub_apply,
    Work.SignatureBordism.p₁SqNumber_apply, Work.SignatureBordism.interForm_apply]
  rfl

end

end Work.ThomBordism.PontryaginThom
