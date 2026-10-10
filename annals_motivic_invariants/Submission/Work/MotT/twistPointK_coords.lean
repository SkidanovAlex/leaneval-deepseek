import Mathlib
import Submission.Work.MotT.TwistPointKDefs
import Submission.Work.MotT.evalAtLoc_transAlgEquiv
import Submission.Work.MotT.plugHomAt_pointmap
import Submission.Work.MotT.exists_kleinTw_point_of_fifth_pow
import Submission.Work.MotT.T4Setup
import Submission.Work.MotT.AM2_descent
import Submission.Work.MotT.isGalois_KummerField2
import Submission.Work.MotT.exists_kleinPoint
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.TransPlace
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

set_option maxHeartbeats 3000000

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §0 Lifting the Klein coordinates to the affine coordinate ring -/

section Lift

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

/-- The coordinate-ring counterpart of the basis `1, x, y, x², xy` of `L(5·O)`. -/
noncomputable def kleinBasCoord (D : Work.MotV.KleinData K) :
    Fin 5 → Work.MotC2.Coord (D.E.baseChange L) :=
  ![1, Work.MotC2.coordX (D.E.baseChange L), Work.MotC2.coordY (D.E.baseChange L),
    (Work.MotC2.coordX (D.E.baseChange L)) ^ 2,
    Work.MotC2.coordX (D.E.baseChange L) * Work.MotC2.coordY (D.E.baseChange L)]

lemma genX_eq (D : Work.MotV.KleinData K) :
    Work.MotV.genX (D.E.baseChange L) = Work.MotC2.genX (D.E.baseChange L) := rfl

lemma genY_eq (D : Work.MotV.KleinData K) :
    Work.MotV.genY (D.E.baseChange L) = Work.MotC2.genY (D.E.baseChange L) := rfl

lemma algebraMap_kleinBasCoord (D : Work.MotV.KleinData K) (m : Fin 5) :
    algebraMap (Work.MotC2.Coord (D.E.baseChange L)) (Work.MotC2.Func (D.E.baseChange L))
      (kleinBasCoord D m) = Work.MotV.kleinBas D L m := by
  fin_cases m <;>
    simp [kleinBasCoord, Work.MotV.kleinBas, genX_eq D, genY_eq D] <;> try rfl

/-- The Klein coordinates `κ_i = kleinCoord D L i`, lifted to the affine coordinate ring
`L[E] = L[X,Y]/(W_E)`. -/
noncomputable def kleinCoordRing (D : Work.MotV.KleinData K) (i : Fin 5) :
    Work.MotC2.Coord (D.E.baseChange L) :=
  ∑ m : Fin 5, algebraMap L (Work.MotC2.Coord (D.E.baseChange L))
      (algebraMap K L (D.coord i m)) * kleinBasCoord D m

lemma algebraMap_kleinCoordRing (D : Work.MotV.KleinData K) (i : Fin 5) :
    algebraMap (Work.MotC2.Coord (D.E.baseChange L)) (Work.MotC2.Func (D.E.baseChange L))
      (kleinCoordRing D i) = Work.MotV.kleinCoord D L i := by
  rw [kleinCoordRing, Work.MotV.kleinCoord_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, algebraMap_kleinBasCoord,
    IsScalarTower.algebraMap_apply L (Work.MotC2.Coord (D.E.baseChange L))
      (Work.MotC2.Func (D.E.baseChange L))]

lemma kleinCoordRing_mem_adjoin (D : Work.MotV.KleinData K) (i : Fin 5) :
    kleinCoordRing (L := L) D i ∈ Algebra.adjoin K
      ({Work.MotC2.coordX (D.E.baseChange L), Work.MotC2.coordY (D.E.baseChange L)} :
        Set (Work.MotC2.Coord (D.E.baseChange L))) := by
  rw [kleinCoordRing]
  refine Subalgebra.sum_mem _ fun m _ => Subalgebra.mul_mem _ ?_ ?_
  · rw [← IsScalarTower.algebraMap_apply K L (Work.MotC2.Coord (D.E.baseChange L))]
    exact Subalgebra.algebraMap_mem _ (D.coord i m)
  · fin_cases m
    · exact Subalgebra.one_mem _
    · exact Algebra.subset_adjoin (by simp [kleinBasCoord])
    · exact Algebra.subset_adjoin (by simp [kleinBasCoord])
    · exact pow_mem (Algebra.subset_adjoin (by simp [kleinBasCoord])) 2
    · exact mul_mem (Algebra.subset_adjoin (by simp [kleinBasCoord]))
        (Algebra.subset_adjoin (by simp [kleinBasCoord]))

lemma kleinBas_zero (D : Work.MotV.KleinData K) : Work.MotV.kleinBas D L 0 = 1 := by
  simp [Work.MotV.kleinBas]

lemma kleinBas_three (D : Work.MotV.KleinData K) :
    Work.MotV.kleinBas D L 3 = (Work.MotC2.genX (D.E.baseChange L)) ^ 2 := by
  simp [Work.MotV.kleinBas, genX_eq D]

end Lift

/-! ## §1 Descent of the Galois-fixed elements of `L = KummerField2 K h₁ h₂ hk` -/

section Descent

variable {K : Type} [Field K] (h₁ h₂ : K) (hk : ringChar K ≠ 5)

/-- The fixed field of `Gal(L/K)` is `K` for `L = KummerField2 K h₁ h₂ hk`. -/
theorem kummerField2_mem_range_of_fixed {v : ↥(KummerField2 K h₁ h₂ hk)}
    (hv : ∀ σ : ↥(KummerField2 K h₁ h₂ hk) ≃ₐ[K] ↥(KummerField2 K h₁ h₂ hk), σ v = v) :
    ∃ c : K, algebraMap K ↥(KummerField2 K h₁ h₂ hk) c = v := by
  haveI := (isGalois_KummerField2 K h₁ h₂ hk).1
  haveI := (isGalois_KummerField2 K h₁ h₂ hk).2
  exact (IsGalois.mem_range_algebraMap_iff_fixed v).mpr hv

end Descent

/-! ## §2 The values of the Klein coordinates at an affine point -/

section KleinQ

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

/-- The value `κ_i(Q)` of the `i`-th Klein coordinate at a nonsingular affine point
`Q = (q₁,q₂)`. -/
noncomputable def kleinQ (D : Work.MotV.KleinData K) {q₁ q₂ : L}
    (hns : Work.MotC2.IsNonsingularPoint (D.E.baseChange L) q₁ q₂) (i : Fin 5) : L :=
  (plugHomAt (D.E.baseChange L) q₁ q₂ hns.nonsingular).toRingHom (kleinCoordRing D i)

/-- `plugHomAt` of a constant from `K`, in the `RingHom`-coercion form. -/
lemma plugHomAt_algebraMap_K' (E : WeierstrassCurve L) (a b : L)
    (h : WeierstrassCurve.Affine.Nonsingular E a b) (c : K) :
    (plugHomAt E a b h).toRingHom (algebraMap K (Work.MotC2.Coord E) c) = algebraMap K L c :=
  plugHomAt_algebraMap_K E a b h c

/-- `plugHomAt` of a constant of `L`, in the `RingHom`-coercion form. -/
lemma plugHomAt_algebraMap' (E : WeierstrassCurve L) (a b : L)
    (h : WeierstrassCurve.Affine.Nonsingular E a b) (c : L) :
    (plugHomAt E a b h).toRingHom (algebraMap L (Work.MotC2.Coord E) c) = c :=
  plugHomAt_algebraMap E a b h c

/-- **Some Klein coordinate is nonzero at `Q`.**  This is `KleinData.Good.spans` at `m = 0`
(`1 = Σ_i e 0 i · κ_i`) evaluated at `Q` with `plugHomAt`. -/
lemma exists_kleinQ_ne_zero (D : Work.MotV.KleinData K) (hD : D.Good) {q₁ q₂ : L}
    (hns : Work.MotC2.IsNonsingularPoint (D.E.baseChange L) q₁ q₂) :
    ∃ j : Fin 5, kleinQ (L := L) D hns j ≠ 0 := by
  obtain ⟨e, he⟩ := hD.spans
  have hklein : ∑ i : Fin 5,
      algebraMap L (Work.MotC2.Func (D.E.baseChange L)) (algebraMap K L (e 0 i)) *
        Work.MotV.kleinCoord D L i = 1 := by
    have h := he L 0
    rw [kleinBas_zero] at h
    exact h.symm
  have hcoord' : algebraMap (Work.MotC2.Coord (D.E.baseChange L))
        (Work.MotC2.Func (D.E.baseChange L))
        (∑ i : Fin 5, algebraMap L (Work.MotC2.Coord (D.E.baseChange L))
          (algebraMap K L (e 0 i)) * kleinCoordRing (L := L) D i) = 1 := by
    rw [map_sum]
    trans ∑ i : Fin 5, algebraMap L (Work.MotC2.Func (D.E.baseChange L))
        (algebraMap K L (e 0 i)) * Work.MotV.kleinCoord D L i
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, algebraMap_kleinCoordRing,
        ← IsScalarTower.algebraMap_apply L (Work.MotC2.Coord (D.E.baseChange L))
          (Work.MotC2.Func (D.E.baseChange L))]
    · exact hklein
  have hcoord : ∑ i : Fin 5, algebraMap L (Work.MotC2.Coord (D.E.baseChange L))
        (algebraMap K L (e 0 i)) * kleinCoordRing (L := L) D i = 1 := by
    refine IsFractionRing.injective (Work.MotC2.Coord (D.E.baseChange L))
      (Work.MotC2.Func (D.E.baseChange L)) ?_
    rw [map_one]
    exact hcoord'
  have hplug : ∑ i : Fin 5, algebraMap K L (e 0 i) * kleinQ (L := L) D hns i = 1 := by
    have h := congrArg (plugHomAt (D.E.baseChange L) q₁ q₂ hns.nonsingular).toRingHom hcoord
    simp only [map_sum, map_mul, map_one, plugHomAt_algebraMap', kleinQ] at h
    exact h
  by_contra h
  simp only [not_exists, not_not] at h
  rw [Finset.sum_eq_zero (fun i _ => by rw [h i, mul_zero])] at hplug
  exact one_ne_zero hplug.symm

/-- **The Klein quadrics vanish at `κ(Q)`.**  This is `KleinData.Good.klein_eq` transported
through the evaluation `plugHomAt`. -/
lemma kleinP_kleinQ (D : Work.MotV.KleinData K) (hD : D.Good) {q₁ q₂ : L}
    (hns : Work.MotC2.IsNonsingularPoint (D.E.baseChange L) q₁ q₂) (k : Fin 5) :
    Work.MotK.kleinP (algebraMap K L D.a) (algebraMap K L D.b)
      (fun i => kleinQ (L := L) D hns i) k = 0 := by
  have h1 : algebraMap (Work.MotC2.Coord (D.E.baseChange L))
        (Work.MotC2.Func (D.E.baseChange L))
        (Work.MotK.kleinP (algebraMap K (Work.MotC2.Coord (D.E.baseChange L)) D.a)
          (algebraMap K (Work.MotC2.Coord (D.E.baseChange L)) D.b)
          (fun i => kleinCoordRing (L := L) D i) k) = 0 := by
    rw [Work.MotT.kleinP_map]
    simp only [← IsScalarTower.algebraMap_apply K (Work.MotC2.Coord (D.E.baseChange L))
      (Work.MotC2.Func (D.E.baseChange L)), algebraMap_kleinCoordRing]
    exact hD.klein_eq L k
  have h2 : Work.MotK.kleinP (algebraMap K (Work.MotC2.Coord (D.E.baseChange L)) D.a)
      (algebraMap K (Work.MotC2.Coord (D.E.baseChange L)) D.b)
      (fun i => kleinCoordRing (L := L) D i) k = 0 := by
    refine IsFractionRing.injective (Work.MotC2.Coord (D.E.baseChange L))
      (Work.MotC2.Func (D.E.baseChange L)) ?_
    rw [map_zero]
    exact h1
  have h3 : (plugHomAt (D.E.baseChange L) q₁ q₂ hns.nonsingular).toRingHom
      (Work.MotK.kleinP (algebraMap K (Work.MotC2.Coord (D.E.baseChange L)) D.a)
        (algebraMap K (Work.MotC2.Coord (D.E.baseChange L)) D.b)
        (fun i => kleinCoordRing (L := L) D i) k) = 0 := by
    have h := congrArg (plugHomAt (D.E.baseChange L) q₁ q₂ hns.nonsingular) h2
    simpa using h
  rw [kleinP_map] at h3
  simpa only [map_zero, plugHomAt_algebraMap_K', kleinQ] using h3

end KleinQ

/-! ## §3 The affine case and the case `Q = O` of `Work.MotT.twistPointK_coords` -/

section Core

open WeierstrassCurve WeierstrassCurve.Affine

/-- The affine case of `Work.MotT.twistPointK_coords`: `Q = (q₁,q₂)` is an affine point. -/
private lemma twistPointK_coords_some {K : Type} [Field K] (D : Work.MotV.KleinData K)
    (hD : D.Good) (h₁ h₂ : K) (hk : ringChar K ≠ 5)
    [instDec : DecidableEq ↥(KummerField2 K h₁ h₂ hk)]
    [instEll : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).IsElliptic]
    {h : K} (hh : h ≠ 0) (w : ↥(KummerField2 K h₁ h₂ hk))
    (hw : w ^ 5 = algebraMap K ↥(KummerField2 K h₁ h₂ hk) h)
    {q₁ q₂ : ↥(KummerField2 K h₁ h₂ hk)}
    (hns : Nonsingular (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) q₁ q₂)
    (hQ : ∀ σ : ↥(KummerField2 K h₁ h₂ hk) ≃ₐ[K] ↥(KummerField2 K h₁ h₂ hk),
      ∃ A : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).toAffine.Point,
        WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
            (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk)) σ.toAlgHom
            (WeierstrassCurve.Affine.Point.some q₁ q₂ hns)
          = WeierstrassCurve.Affine.Point.some q₁ q₂ hns + A ∧
        (∀ i : Fin 5,
          Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
                Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
            (algebraMap ↥(KummerField2 K h₁ h₂ hk)
                (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) (σ w / w)) ^ (i : ℕ) *
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
                Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0))) :
    ∃ y : Fin 5 → K, y ≠ 0 ∧ ∀ k, Work.MotV.kleinTw D.a D.b h y k = 0 := by
  haveI hnsI : Work.MotC2.IsNonsingularPoint
      (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) q₁ q₂ := ⟨hns⟩
  have hwne : w ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (5 : ℕ) ≠ 0)] at hw
    refine hh ?_
    have h1 : algebraMap K ↥(KummerField2 K h₁ h₂ hk) h = 0 := hw.symm
    by_contra hne
    have h2 : algebraMap K ↥(KummerField2 K h₁ h₂ hk) (h * h⁻¹) = 1 := by
      rw [mul_inv_cancel₀ hne, map_one]
    rw [map_mul, h1, zero_mul] at h2
    exact one_ne_zero h2.symm
  obtain ⟨j, hj⟩ := exists_kleinQ_ne_zero (L := ↥(KummerField2 K h₁ h₂ hk)) D hD ⟨hns⟩
  have hinj : Function.Injective (algebraMap K ↥(KummerField2 K h₁ h₂ hk)) := by
    intro a b hab
    have h : algebraMap K ↥(KummerField2 K h₁ h₂ hk) (a - b) = 0 := by rw [map_sub, hab, sub_self]
    rcases eq_or_ne (a - b) 0 with h0 | h0
    · exact sub_eq_zero.mp h0
    · exfalso
      have h1 : algebraMap K ↥(KummerField2 K h₁ h₂ hk) ((a - b) * (a - b)⁻¹) = 1 := by
        rw [mul_inv_cancel₀ h0, map_one]
      rw [map_mul, h, zero_mul] at h1
      exact one_ne_zero h1.symm
  have h0 : Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0 ≠ 0 :=
    hD.coord0_ne ↥(KummerField2 K h₁ h₂ hk)
  -- the key relation: for every σ, `(σ w / w)^j · κ_j(Q) · σ(κ_i(Q))` is symmetric
  have hrel : ∀ σ : ↥(KummerField2 K h₁ h₂ hk) ≃ₐ[K] ↥(KummerField2 K h₁ h₂ hk), ∀ i : Fin 5,
      (σ w / w) ^ (j : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j *
          σ (kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ i) =
        (σ w / w) ^ (i : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ i *
          σ (kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j) := by
    intro σ i
    obtain ⟨A, hA, hdiag⟩ := hQ σ
    obtain ⟨hσ', hmap⟩ : ∃ hσ' : Nonsingular (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (σ q₁) (σ q₂),
        WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
          (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk)) σ.toAlgHom
          (WeierstrassCurve.Affine.Point.some q₁ q₂ hns)
          = WeierstrassCurve.Affine.Point.some (σ q₁) (σ q₂) hσ' :=
      ⟨_, WeierstrassCurve.Affine.Point.map_some (W' := D.E) (S := K)
        (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk)) (f := σ.toAlgHom) hns⟩
    haveI hnsI' : Work.MotC2.IsNonsingularPoint
        (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (σ q₁) (σ q₂) := ⟨hσ'⟩
    have hA' : WeierstrassCurve.Affine.Point.some q₁ q₂ hns + A
        = WeierstrassCurve.Affine.Point.some (σ q₁) (σ q₂) hσ' := hA.symm.trans hmap
    -- the values of `τ_A κ_i` at `Q`
    have hmemT : ∀ i : Fin 5,
        (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i)
          ∈ Work.MotC2.affPlaceAt (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) q₁ q₂ := by
      intro i
      obtain ⟨hf, -⟩ := Work.MotT.evalAtLoc_transAlgEquiv
        (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A hA'
        (algebraMap (Work.MotC2.Coord (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
          ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (σ q₁) (σ q₂))
          (kleinCoordRing (L := ↥(KummerField2 K h₁ h₂ hk)) D i))
      rwa [show ((algebraMap (Work.MotC2.Coord (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
            ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (σ q₁) (σ q₂))
            (kleinCoordRing (L := ↥(KummerField2 K h₁ h₂ hk)) D i)) :
              Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) =
          Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i from by
        rw [Work.MotC2.affPlaceAt_algebraMap_val, algebraMap_kleinCoordRing]] at hf
    have hvalT : ∀ i : Fin 5, evalAtLoc (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) q₁ q₂
        ⟨(Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i), hmemT i⟩ =
        σ (kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ i) := by
      intro i
      obtain ⟨hf, hval⟩ := Work.MotT.evalAtLoc_transAlgEquiv
        (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A hA'
        (algebraMap (Work.MotC2.Coord (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
          ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (σ q₁) (σ q₂))
          (kleinCoordRing (L := ↥(KummerField2 K h₁ h₂ hk)) D i))
      have hcoe : ((algebraMap (Work.MotC2.Coord (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
            ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (σ q₁) (σ q₂))
            (kleinCoordRing (L := ↥(KummerField2 K h₁ h₂ hk)) D i)) :
              Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) =
          Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i := by
        rw [Work.MotC2.affPlaceAt_algebraMap_val, algebraMap_kleinCoordRing]
      rw [show (⟨(Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
            (algebraMap (Work.MotC2.Coord (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
              ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (σ q₁) (σ q₂))
              (kleinCoordRing (L := ↥(KummerField2 K h₁ h₂ hk)) D i)), hf⟩ :
            ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) q₁ q₂)) =
          ⟨(Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i), hmemT i⟩
        from Subtype.ext (by
          show (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
              ((algebraMap (Work.MotC2.Coord (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
                ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (σ q₁) (σ q₂))
                (kleinCoordRing (L := ↥(KummerField2 K h₁ h₂ hk)) D i) :
                  Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))) =
            (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i)
          rw [hcoe])] at hval
      rw [hval, evalAtLoc_algebraMap]
      rw [← Work.MotT.plugHomAt_pointmap (W := D.E) σ hns hσ'
        (kleinCoordRing (L := ↥(KummerField2 K h₁ h₂ hk)) D i)
        (kleinCoordRing_mem_adjoin (L := ↥(KummerField2 K h₁ h₂ hk)) D i)]
      rfl
    -- the identity in the function field `M = L(E)`
    set cM : Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) :=
      algebraMap ↥(KummerField2 K h₁ h₂ hk)
        (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) (σ w / w) with hcM
    have hI : ∀ i : Fin 5,
        (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i) *
          Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0 =
        cM ^ (i : ℕ) *
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i *
            (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0)) := by
      intro i
      have h := hdiag i
      rw [map_div₀] at h
      have hτ0 : (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) ≠ 0 := fun hz =>
        h0 ((Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A).injective
          (by rw [hz, map_zero]))
      field_simp at h
      linear_combination (norm := refl_ring1) h
    have hX : ∀ i : Fin 5,
        cM ^ (j : ℕ) * (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) j *
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i)) =
        cM ^ (i : ℕ) * (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i *
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) j)) := by
      intro i
      have hi' : (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i) =
          cM ^ (i : ℕ) * Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i *
            (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0 := by
        rw [eq_div_iff h0]
        linear_combination (norm := refl_ring1) hI i
      have hj' : (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) j) =
          cM ^ (j : ℕ) * Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) j *
            (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0 := by
        rw [eq_div_iff h0]
        linear_combination (norm := refl_ring1) hI j
      rw [hi', hj']
      first | refl_ring1 | ring
    -- evaluate `hX` at `Q`
    have hmemK : ∀ i : Fin 5, Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i
        ∈ Work.MotC2.affPlaceAt (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) q₁ q₂ := by
      intro i
      have h := Work.MotC2.algebraMap_mem_affPlaceAt (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
        q₁ q₂ (kleinCoordRing (L := ↥(KummerField2 K h₁ h₂ hk)) D i)
      rwa [algebraMap_kleinCoordRing] at h
    have hevK : ∀ i : Fin 5, evalAtLoc (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) q₁ q₂
        ⟨Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i, hmemK i⟩ =
        kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ i := by
      intro i
      have hcoe : (⟨Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i, hmemK i⟩ :
          ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) q₁ q₂)) =
          algebraMap (Work.MotC2.Coord (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
            ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) q₁ q₂)
            (kleinCoordRing (L := ↥(KummerField2 K h₁ h₂ hk)) D i) :=
        Subtype.ext (by
          show Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i =
            algebraMap (Work.MotC2.Coord (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
              (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
              (kleinCoordRing (L := ↥(KummerField2 K h₁ h₂ hk)) D i)
          rw [algebraMap_kleinCoordRing])
      rw [hcoe, evalAtLoc_algebraMap]
      rfl
    have hev : (evalAtLoc (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) q₁ q₂)
        ((algebraMap ↥(KummerField2 K h₁ h₂ hk)
            ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) q₁ q₂) (σ w / w)) ^ (j : ℕ) *
          (⟨Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) j, hmemK j⟩ *
            ⟨(Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i), hmemT i⟩)) =
        (evalAtLoc (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) q₁ q₂)
        ((algebraMap ↥(KummerField2 K h₁ h₂ hk)
            ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) q₁ q₂) (σ w / w)) ^ (i : ℕ) *
          (⟨Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i, hmemK i⟩ *
            ⟨(Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) j), hmemT j⟩)) := by
      refine congrArg (evalAtLoc (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) q₁ q₂) ?_
      refine Subtype.ext ?_
      show cM ^ (j : ℕ) * (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) j *
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i)) =
        cM ^ (i : ℕ) * (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i *
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) j))
      exact hX i
    simp only [map_mul, map_pow] at hev
    rw [evalAtLoc_algebraMap_L, hevK j, hevK i, hvalT i, hvalT j] at hev
    ring_nf at hev ⊢
    exact hev
  -- descent
  have hvfix : ∀ σ : ↥(KummerField2 K h₁ h₂ hk) ≃ₐ[K] ↥(KummerField2 K h₁ h₂ hk), ∀ i : Fin 5,
      σ ((w⁻¹) ^ (i : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ i /
          ((w⁻¹) ^ (j : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j)) =
        (w⁻¹) ^ (i : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ i /
          ((w⁻¹) ^ (j : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j) := by
    intro σ i
    have hc : (σ w / w) ≠ 0 :=
      div_ne_zero (fun hz => hwne (σ.injective (by rw [hz, map_zero]))) hwne
    have hwj : (σ w / w) ^ (j : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hc) hj
    have hvj : (w⁻¹) ^ (j : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (inv_ne_zero hwne)) hj
    have hlam : ∀ i : Fin 5, σ ((w⁻¹) ^ (i : ℕ) *
          kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ i) =
        (σ (kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j) /
            ((σ w / w) ^ (j : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j)) *
          ((w⁻¹) ^ (i : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ i) := by
      intro i
      have h := hrel σ i
      have hσw : σ w = (σ w / w) * w := (div_mul_cancel₀ (σ w) hwne).symm
      have hki : σ (kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ i) =
          (σ w / w) ^ (i : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ i *
              σ (kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j) /
            ((σ w / w) ^ (j : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j) := by
        rw [eq_div_iff hwj]
        linear_combination (norm := refl_ring1) h
      rw [map_mul, map_pow, map_inv₀, hσw, mul_inv_rev, mul_pow, hki, inv_pow, inv_pow]
      have hσwne : σ w ≠ 0 := fun hz => hwne (σ.injective (by rw [hz, map_zero]))
      field_simp [hwne, hσwne, hj]
      try ring
    rw [map_div₀, hlam i, hlam j]
    have hσj : σ (kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j) ≠ 0 := fun hz =>
      hj (σ.injective (by rw [hz, map_zero]))
    field_simp [hσj, hvj, hwj]
    try ring
  choose Y hY using fun (i : Fin 5) => kummerField2_mem_range_of_fixed h₁ h₂ hk (v :=
    (w⁻¹) ^ (i : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ i /
      ((w⁻¹) ^ (j : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j))
    (fun σ => hvfix σ i)
  have hvj : (w⁻¹) ^ (j : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (inv_ne_zero hwne)) hj
  have hYj : Y j = 1 := hinj (by
    rw [hY j, div_self hvj, map_one])
  refine ⟨Y, ?_, ?_⟩
  · intro hzero
    have h : Y j = 0 := by rw [hzero]; rfl
    rw [hYj] at h
    exact one_ne_zero h
  · intro k
    have hkq_eq : ∀ i : Fin 5, kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ i =
        w ^ (i : ℕ) * algebraMap K ↥(KummerField2 K h₁ h₂ hk) (Y i) *
          ((w⁻¹) ^ (j : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j) := by
      intro i
      have h := hY i
      rw [eq_div_iff hvj] at h
      rw [mul_assoc, h, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hwne, one_pow, one_mul]
    have hscale : Work.MotK.kleinP (algebraMap K ↥(KummerField2 K h₁ h₂ hk) D.a)
        (algebraMap K ↥(KummerField2 K h₁ h₂ hk) D.b)
        (fun (i : Fin 5) => w ^ (i : ℕ) * algebraMap K ↥(KummerField2 K h₁ h₂ hk) (Y i)) k = 0 := by
      have hsub : Work.MotK.kleinP (algebraMap K ↥(KummerField2 K h₁ h₂ hk) D.a)
          (algebraMap K ↥(KummerField2 K h₁ h₂ hk) D.b)
          (fun (i : Fin 5) => w ^ (i : ℕ) * algebraMap K ↥(KummerField2 K h₁ h₂ hk) (Y i) *
            ((w⁻¹) ^ (j : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j)) k = 0 := by
        rw [show (fun (i : Fin 5) => w ^ (i : ℕ) * algebraMap K ↥(KummerField2 K h₁ h₂ hk) (Y i) *
              ((w⁻¹) ^ (j : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j)) =
            (fun (i : Fin 5) => kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ i) from
          funext fun i => (hkq_eq i).symm]
        exact kleinP_kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D hD ⟨hns⟩ k
      have hsc := Work.MotT.kleinP_scale (algebraMap K ↥(KummerField2 K h₁ h₂ hk) D.a)
        (algebraMap K ↥(KummerField2 K h₁ h₂ hk) D.b)
        ((w⁻¹) ^ (j : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j)
        (fun (i : Fin 5) => w ^ (i : ℕ) * algebraMap K ↥(KummerField2 K h₁ h₂ hk) (Y i)) k
      rw [show (fun (i : Fin 5) => ((w⁻¹) ^ (j : ℕ) *
              kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j) *
            (w ^ (i : ℕ) * algebraMap K ↥(KummerField2 K h₁ h₂ hk) (Y i))) =
          (fun (i : Fin 5) => w ^ (i : ℕ) * algebraMap K ↥(KummerField2 K h₁ h₂ hk) (Y i) *
            ((w⁻¹) ^ (j : ℕ) * kleinQ (L := ↥(KummerField2 K h₁ h₂ hk)) D ⟨hns⟩ j)) from
        funext fun i => by ring] at hsc
      rw [hsub] at hsc
      exact (mul_eq_zero.mp hsc.symm).resolve_left (pow_ne_zero 2 hvj)
    have htw : Work.MotV.kleinTw (algebraMap K ↥(KummerField2 K h₁ h₂ hk) D.a)
        (algebraMap K ↥(KummerField2 K h₁ h₂ hk) D.b) (w ^ 5)
        (fun (i : Fin 5) => algebraMap K ↥(KummerField2 K h₁ h₂ hk) (Y i)) k = 0 := by
      have hsub2 := Work.MotV.kleinTw_subst (algebraMap K ↥(KummerField2 K h₁ h₂ hk) D.a)
        (algebraMap K ↥(KummerField2 K h₁ h₂ hk) D.b) w
        (fun (i : Fin 5) => algebraMap K ↥(KummerField2 K h₁ h₂ hk) (Y i)) k
      rw [hscale] at hsub2
      exact (mul_eq_zero.mp hsub2.symm).resolve_left (pow_ne_zero _ hwne)
    rw [hw] at htw
    exact Work.MotT.kleinTw_of_map_eq (algebraMap K ↥(KummerField2 K h₁ h₂ hk)) hinj
      D.a D.b h Y k htw

/-- The case `Q = O` of `Work.MotT.twistPointK_coords`. -/
private lemma twistPointK_coords_zero {K : Type} [Field K] (D : Work.MotV.KleinData K)
    (hD : D.Good) (h₁ h₂ : K) (hk : ringChar K ≠ 5)
    [instDec : DecidableEq ↥(KummerField2 K h₁ h₂ hk)]
    [instEll : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).IsElliptic]
    {h : K} (hh : h ≠ 0) (w : ↥(KummerField2 K h₁ h₂ hk))
    (hw : w ^ 5 = algebraMap K ↥(KummerField2 K h₁ h₂ hk) h)
    (Q : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).toAffine.Point) (hQ0 : Q = 0)
    (hQ : ∀ σ : ↥(KummerField2 K h₁ h₂ hk) ≃ₐ[K] ↥(KummerField2 K h₁ h₂ hk),
      ∃ A : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).toAffine.Point,
        WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
            (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk)) σ.toAlgHom Q = Q + A ∧
        (∀ i : Fin 5,
          Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
                Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
            (algebraMap ↥(KummerField2 K h₁ h₂ hk)
                (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) (σ w / w)) ^ (i : ℕ) *
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
                Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0))) :
    ∃ y : Fin 5 → K, y ≠ 0 ∧ ∀ k, Work.MotV.kleinTw D.a D.b h y k = 0 := by
  have hinj : Function.Injective (algebraMap K ↥(KummerField2 K h₁ h₂ hk)) := by
    intro a b hab
    have h : algebraMap K ↥(KummerField2 K h₁ h₂ hk) (a - b) = 0 := by rw [map_sub, hab, sub_self]
    rcases eq_or_ne (a - b) 0 with h0 | h0
    · exact sub_eq_zero.mp h0
    · exfalso
      have h1 : algebraMap K ↥(KummerField2 K h₁ h₂ hk) ((a - b) * (a - b)⁻¹) = 1 := by
        rw [mul_inv_cancel₀ h0, map_one]
      rw [map_mul, h, zero_mul] at h1
      exact one_ne_zero h1.symm
  have hwne : w ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (5 : ℕ) ≠ 0)] at hw
    refine hh (hinj ?_)
    rw [map_zero]; exact hw.symm
  by_cases hfix : ∀ σ : ↥(KummerField2 K h₁ h₂ hk) ≃ₐ[K] ↥(KummerField2 K h₁ h₂ hk), σ w = w
  · obtain ⟨c, hc⟩ := kummerField2_mem_range_of_fixed h₁ h₂ hk (v := w) hfix
    have hc5 : c ^ 5 = h := hinj (by
      calc algebraMap K ↥(KummerField2 K h₁ h₂ hk) (c ^ 5)
          = (algebraMap K ↥(KummerField2 K h₁ h₂ hk) c) ^ 5 := by rw [map_pow]
        _ = w ^ 5 := by rw [hc]
        _ = algebraMap K ↥(KummerField2 K h₁ h₂ hk) h := hw)
    exact exists_kleinTw_point_of_fifth_pow D hD hh c hc5
  · obtain ⟨σ, hσ⟩ := not_forall.mp hfix
    -- `A = 0` and hence `τ_A = 1`
    obtain ⟨A, hA, hdiag⟩ := hQ σ
    have hA0 : A = 0 := by
      rw [hQ0, WeierstrassCurve.Affine.Point.map_zero, zero_add] at hA
      exact hA.symm
    have hdiag' : ∀ i : Fin 5, (algebraMap ↥(KummerField2 K h₁ h₂ hk)
          (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) (σ w / w)) ^ (i : ℕ) *
        (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
          Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
        Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
          Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0 := by
      intro i
      have h := hdiag i
      rw [hA0] at h
      simp only [Work.MotC2.transAlgEquiv_zero, AlgEquiv.one_apply] at h
      exact h.symm
    -- the Kummer cocycle `σ w / w` is a primitive fifth root of unity
    have hcw5 : (σ w) ^ 5 = w ^ 5 := by
      calc (σ w) ^ 5 = σ (w ^ 5) := by rw [map_pow]
        _ = σ (algebraMap K ↥(KummerField2 K h₁ h₂ hk) h) := by rw [hw]
        _ = algebraMap K ↥(KummerField2 K h₁ h₂ hk) h := σ.commutes h
        _ = w ^ 5 := hw.symm
    have hc5 : (σ w / w) ^ 5 = 1 := by
      rw [div_pow, hcw5, div_self (pow_ne_zero 5 hwne)]
    have hcne : σ w / w ≠ 1 := fun h1 => hσ (by
      rw [div_eq_iff hwne, one_mul] at h1
      exact h1)
    have hprim : IsPrimitiveRoot (σ w / w) 5 := by
      rw [IsPrimitiveRoot.iff_orderOf]
      have hprime : Nat.Prime 5 := by norm_num
      rcases hprime.eq_one_or_self_of_dvd (orderOf (σ w / w))
        (orderOf_dvd_iff_pow_eq_one.mpr hc5) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hcne
      · exact h
    have hinjM : Function.Injective (algebraMap ↥(KummerField2 K h₁ h₂ hk)
        (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))) := by
      intro a b hab
      have h' : algebraMap ↥(KummerField2 K h₁ h₂ hk)
          (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) (a - b) = 0 := by
        rw [map_sub, hab, sub_self]
      rcases eq_or_ne (a - b) 0 with h0 | h0
      · exact sub_eq_zero.mp h0
      · exfalso
        have h1 : algebraMap ↥(KummerField2 K h₁ h₂ hk)
            (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
            ((a - b) * (a - b)⁻¹) = 1 := by
          rw [mul_inv_cancel₀ h0, map_one]
        rw [map_mul, h', zero_mul] at h1
        exact one_ne_zero h1.symm
    have h0 : Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0 ≠ 0 :=
      hD.coord0_ne ↥(KummerField2 K h₁ h₂ hk)
    -- all `κ_i` with `i ≠ 0` vanish
    have hκzero : ∀ i : Fin 5, i ≠ 0 →
        Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i = 0 := by
      intro i hi
      have hci : (σ w / w) ^ (i : ℕ) ≠ 1 := by
        intro h1
        have hdvd : 5 ∣ (i : ℕ) := (hprim.pow_eq_one_iff_dvd (i : ℕ)).mp h1
        exact hi (Fin.eq_of_val_eq (Nat.eq_zero_of_dvd_of_lt hdvd i.isLt))
      have hcMi : (algebraMap ↥(KummerField2 K h₁ h₂ hk)
          (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) (σ w / w)) ^ (i : ℕ) ≠ 1 := by
        intro hz
        refine hci (hinjM ?_)
        show algebraMap ↥(KummerField2 K h₁ h₂ hk)
            (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) ((σ w / w) ^ (i : ℕ)) =
          algebraMap ↥(KummerField2 K h₁ h₂ hk)
            (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) 1
        rw [map_pow, map_one]
        exact hz
      have h2 : ((algebraMap ↥(KummerField2 K h₁ h₂ hk)
            (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) (σ w / w)) ^ (i : ℕ) - 1) *
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) = 0 := by
        rw [sub_mul, one_mul, hdiag' i, sub_self]
      have hq : Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
          Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0 = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd h (sub_ne_zero.mpr hcMi)
        · exact h
      rcases div_eq_zero_iff.mp hq with h | h
      · exact h
      · exact absurd h h0
    -- `spans` gives `1 = e₀₀ κ₀` and `x² = e₃₀ κ₀`, whence `x` is algebraic
    obtain ⟨e, he⟩ := hD.spans
    have h1 : (1 : Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) =
        algebraMap ↥(KummerField2 K h₁ h₂ hk)
            (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
            (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 0 0)) *
          Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0 := by
      have h := he ↥(KummerField2 K h₁ h₂ hk) 0
      rw [kleinBas_zero] at h
      have h' : (∑ i : Fin 5, algebraMap ↥(KummerField2 K h₁ h₂ hk)
            (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
            (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 0 i)) *
          Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i) =
          algebraMap ↥(KummerField2 K h₁ h₂ hk)
            (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
            (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 0 0)) *
          Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0 := by
        rw [Fin.sum_univ_five, hκzero 1 (by decide), hκzero 2 (by decide),
          hκzero 3 (by decide), hκzero 4 (by decide)]
        simp
      rw [h, h']
    have h3 : (Work.MotC2.genX (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) ^ 2 =
        algebraMap ↥(KummerField2 K h₁ h₂ hk)
            (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
            (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 3 0)) *
          Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0 := by
      have h := he ↥(KummerField2 K h₁ h₂ hk) 3
      rw [kleinBas_three] at h
      have h' : (∑ i : Fin 5, algebraMap ↥(KummerField2 K h₁ h₂ hk)
            (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
            (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 3 i)) *
          Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i) =
          algebraMap ↥(KummerField2 K h₁ h₂ hk)
            (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
            (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 3 0)) *
          Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0 := by
        rw [Fin.sum_univ_five, hκzero 1 (by decide), hκzero 2 (by decide),
          hκzero 3 (by decide), hκzero 4 (by decide)]
        simp
      rw [h, h']
    have hkey : algebraMap ↥(KummerField2 K h₁ h₂ hk)
          (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
          (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 0 0)) *
        (Work.MotC2.genX (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) ^ 2 =
        algebraMap ↥(KummerField2 K h₁ h₂ hk)
          (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
          (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 3 0)) := by
      calc algebraMap ↥(KummerField2 K h₁ h₂ hk)
              (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
              (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 0 0)) *
            (Work.MotC2.genX (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) ^ 2
          = algebraMap ↥(KummerField2 K h₁ h₂ hk)
              (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
              (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 0 0)) *
            (algebraMap ↥(KummerField2 K h₁ h₂ hk)
              (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
              (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 3 0)) *
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) := by rw [h3]
        _ = (algebraMap ↥(KummerField2 K h₁ h₂ hk)
              (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
              (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 0 0)) *
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) *
            algebraMap ↥(KummerField2 K h₁ h₂ hk)
              (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
              (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 3 0)) := by ring
        _ = algebraMap ↥(KummerField2 K h₁ h₂ hk)
              (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
              (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 3 0)) := by
          rw [h1.symm, one_mul]
    by_cases he00 : e 0 0 = 0
    · simp only [he00, map_zero, zero_mul] at h1
      exact absurd h1 one_ne_zero
    · have hKm0 : algebraMap K ↥(KummerField2 K h₁ h₂ hk) 0 = 0 :=
        map_zero (algebraMap K ↥(KummerField2 K h₁ h₂ hk) :
          K →+* ↥(KummerField2 K h₁ h₂ hk))
      have hLm0 : algebraMap ↥(KummerField2 K h₁ h₂ hk)
          (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) 0 = 0 :=
        map_zero (algebraMap ↥(KummerField2 K h₁ h₂ hk)
          (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))))
      have hΔ : algebraMap ↥(KummerField2 K h₁ h₂ hk)
          (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
          (algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 0 0)) ≠ 0 := by
        intro hz
        have hz' : algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 0 0) = 0 :=
          hinjM (hz.trans hLm0.symm)
        exact he00 (hinj (hz'.trans hKm0.symm))
      set c₀ : ↥(KummerField2 K h₁ h₂ hk) :=
        algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 3 0) /
          algebraMap K ↥(KummerField2 K h₁ h₂ hk) (e 0 0) with hc₀
      exfalso
      refine (Work.MotC2.transcendental_genX (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
        ⟨Polynomial.X ^ 2 - Polynomial.C c₀, ?_, ?_⟩
      · intro hz
        have h2 := congrArg (fun p => Polynomial.coeff p 2) hz
        simp [hc₀] at h2
      · have hx2 : (Work.MotC2.genX (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) ^ 2 =
            algebraMap ↥(KummerField2 K h₁ h₂ hk)
              (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) c₀ := by
          rw [hc₀, map_div₀, eq_div_iff hΔ]
          linear_combination (norm := refl_ring1) hkey
        simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hx2, sub_self]

end Core

end

/-- **T4, step 5: the LAM coordinates** (general twist parameter `h ∈ Kˣ`, over the fixed field
`L = KummerField2 K h₁ h₂ hk`).

This is the form in which the LAM assembly uses the coordinate step: the point `Q` produced by
node C2 over `L` (`Work.MotT.c2_over_ML2`) lives in `E(L)` with `L = KummerField2 K h₁ h₂ hk`, and
the twist parameter of the conclusion is `h = h₁^{(-1)^ε}/h₂` — a *different* field from
`KummerField2 K h h hk`, so the statement must be made over the fixed `L`.

Let `h ∈ Kˣ` and `w ∈ L` with `w^5 = h` (in the application `h = h₁^{(-1)^ε}/h₂` and
`w = wL1^{(-1)^ε}/wL2`).  Let `Q ∈ E(L)` be such that for every `σ ∈ Gal(L/K)` the difference
`σQ - Q` is the point `A_σ` whose translation automorphism is the diagonal `Δ_{c(σ,h)}`, i.e.
`τ_{A_σ}` acts on every Klein ratio `κ_i/κ_0` by multiplication by `c(σ,h)^i` where
`c(σ,h) := σ(w)/w` is the Kummer cocycle.  Then the twisted Klein curve `C_h` has a `K`-point, in
coordinates: there is a nonzero `y : Fin 5 → K` with `kleinTw D.a D.b h y = 0`.

This is the conclusion of the LAM arithmetic step: comparing `Θ ρ_γ^{(1)} = ρ_γ^{(2)} Θ` for
`Θ = τ_Q ∘ [-1]^ε` (with `Θ` the extension of `θ` given by `Work.MotT.exists_algEquiv_ML2` and
`ρ^{(i)}_γ = Δ_{c(γ,hᵢ)} ∘ γ̃ = Work.MotT.AM2_rhoFun`) gives
`σQ - Q = (-1)^ε A₁ - A₂ = η(c(σ, h₁^{(-1)^ε}/h₂))`, which is the displayed hypothesis with
`h = h₁^{(-1)^ε}/h₂`, `w = wL1^{(-1)^ε}/wL2`.

Route.
1. `∃ j, κ_j(Q) ≠ 0`: `KleinData.Good.spans` at `m = 0` gives `1 = Σ_i e 0 i • κ_i`, so evaluating
   the ring homomorphism `Work.MotC2.plugHom` at `Q` gives `1 = Σ_i e 0 i * κ_i(Q)`.  Each `κ_i` is
   the image of an element of the coordinate ring (`Work.MotV.kleinCoord_eq_sum`), so `κ_i(Q)` is
   the value of a *polynomial* at `Q`; and `KleinData.Good.klein_eq` applied to `plugHom` gives
   `kleinP a b (κ_i(Q)) = 0`.  **If `Q = O`** then `A_σ = 0`, `τ_{A_σ} = id`, and the displayed
   identity forces `σ w = w` for all `σ`, i.e. `w ∈ L^{Gal} = K`; then `h = w^5` is a fifth power in
   `K` and `Work.MotT.exists_kleinPoint` plus `Work.MotV.kleinTw_subst` finish (take the `K`-point
   `y₀` of `kleinP a b` and set `y_i := w^{-i} y₀ i`).
2. `σ(κ_i(Q)) = κ_i(σQ)` for `σ ∈ Gal(L/K)`: `plugHom` is natural in the base
   (`WeierstrassCurve.Affine.CoordinateRing.map`, `WeierstrassCurve.Affine.Point.map_some`).
3. **The translation identity.**  For the affine case, let `ev_Q` be the evaluation at `Q` (the
   residue map of `Work.MotC2.affPlaceAt E q₁ q₂`; its residue field is `L` by
   `Work.MotC2.AffPlaceResidueField`, and `affPlaceAt` contains the coordinate ring via
   `algebraMap_mem_affPlaceAt`).  The hypothesis clears denominators to
   `c^j · τ_{A_σ}(κ_i) · κ_j = c^i · κ_i · τ_{A_σ}(κ_j)` for all `i, j` (no division by `κ_0`);
   choosing `j` with `κ_j(Q) ≠ 0` and using that `τ_{A_σ}` carries the local ring at
   `σQ = Q + A_σ` onto the local ring at `Q` (consequence of `Work.MotC2.TransPlace`: `τ_P` maps
   `affPlaceAt E a b` onto `infPlace E` for `P = (a,b)`; applying this at the point `Q + A_σ` and
   at `Q` gives the general translation law
   `Subalgebra.map (τ_A) (affPlaceAt at Q+A) = affPlaceAt at Q`), all four elements lie in
   `↥(affPlaceAt E q₁ q₂)` and applying `ev_Q` gives `c^j κ_i(σQ) κ_j(Q) = c^i κ_i(Q) κ_j(σQ)`.
4. Hence `v_i := w^{-i} κ_i(Q) ∈ L` satisfies `σ(v_i) = λ_σ v_i` for all `i`, with the single
   `λ_σ := c(σ,h)^j κ_j(σQ)/κ_j(Q)` (independent of `i` by step 3); so `y_i := v_i / v_j` is fixed
   by every `σ`, hence lies in `K` (finite Galois descent, `IsGalois.mem_bot_iff_fixed`); `y ≠ 0`
   since `y_j = 1`.
5. `kleinP a b (κ_i(Q)) = 0` (step 1) and `κ_i(Q) = w^i y_i · κ_j(Q)`, so by the homogeneity of
   `kleinP` (`Work.MotK.kleinP_scale`) `kleinP a b (w^i y_i) = 0`, and `Work.MotV.kleinTw_subst`
   turns this into `kleinTw D.a D.b (w^5) y = 0`, i.e. `kleinTw D.a D.b h y = 0`. -/
theorem twistPointK_coords {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h₁ h₂ : K) (hk : ringChar K ≠ 5)
    [instDec : DecidableEq ↥(KummerField2 K h₁ h₂ hk)]
    [instEll : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).IsElliptic]
    {h : K} (hh : h ≠ 0)
    (w : ↥(KummerField2 K h₁ h₂ hk))
    (hw : w ^ 5 = algebraMap K ↥(KummerField2 K h₁ h₂ hk) h)
    (Q : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).toAffine.Point)
    (hQ : ∀ σ : ↥(KummerField2 K h₁ h₂ hk) ≃ₐ[K] ↥(KummerField2 K h₁ h₂ hk),
      ∃ A : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).toAffine.Point,
        WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
            (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk)) σ.toAlgHom Q = Q + A ∧
        (∀ i : Fin 5,
          Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
                Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
            (algebraMap ↥(KummerField2 K h₁ h₂ hk)
                (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) (σ w / w)) ^ (i : ℕ) *
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
                Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0))) :
    ∃ y : Fin 5 → K, y ≠ 0 ∧ ∀ k, Work.MotV.kleinTw D.a D.b h y k = 0 := by
  rcases Q with _ | ⟨q₁, q₂, hns⟩
  · exact twistPointK_coords_zero D hD h₁ h₂ hk hh w hw _ rfl hQ
  · exact twistPointK_coords_some D hD h₁ h₂ hk hh w hw hns hQ

end Work.MotT
