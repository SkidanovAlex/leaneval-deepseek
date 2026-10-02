import Mathlib
import Submission.Work.LerayHirsch.Punctum

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibre of the projectivisation is `ℂP^{m-1}`

`Work.LerayHirsch.fibreMap Z b` maps the projectivisation `ℙ ℂ (ℂ^m)` of the *model* fibre
bijectively onto the fibre `π^{-1}(b)` of `π : P(E) → B`, `P(E) = (E∖0)/ℂˣ` being the
projectivisation of the complex gluing-data bundle `Z`.

The inverse is the "class of the fibre coordinate": the total space of the realification of `Z` is a
sigma type `B × ℂ^m`, and the second coordinate of a point of the punctured total space is
well defined up to the `ℂˣ`-action, so it descends to a map

`projClass Z : ProjSpace Z → ℙ ℂ (EuclideanSpace ℂ (Fin m))`,  `[p] ↦ [p.2]`.

The two round trips `projClass Z (fibreMap Z b x).1 = x` and
`fibreMap Z b (projClass Z x) = ⟨x, hx⟩` are proved on representatives.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## The class of the fibre coordinate -/

/-- **The class of the fibre coordinate**: the map `ProjSpace Z → ℙ ℂ (ℂ^m)` sending the class of a
punctured vector to the class of its second coordinate (the coordinate in the model fibre).  It is
well defined because the `ℂˣ`-action scales exactly this coordinate. -/
def projClass (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    ProjSpace Z → ℙ ℂ (EuclideanSpace ℂ (Fin m)) :=
  Quotient.lift (fun p => Projectivization.mk ℂ (show EuclideanSpace ℂ (Fin m) from p.1.2)
      ((mem_zeroComplement p.1).mp p.2))
    (by
      intro p q hpq
      obtain ⟨c, hc⟩ := hpq
      have h2 : (show EuclideanSpace ℂ (Fin m) from p.1.2)
          = (c : ℂ) • (show EuclideanSpace ℂ (Fin m) from q.1.2) := by
        have := congrArg (fun r : ↥(zeroComplement (realification Z)) =>
          (show EuclideanSpace ℂ (Fin m) from r.1.2)) hc
        simpa using this.symm
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨c, h2.symm⟩)

theorem projClass_mkProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) :
    projClass Z (mkProj Z p)
      = Projectivization.mk ℂ (show EuclideanSpace ℂ (Fin m) from p.1.2)
          ((mem_zeroComplement p.1).mp p.2) := by
  rw [projClass]
  exact Quotient.lift_mk _ _ p

/-- Two punctured vectors with the same base point and the same fibre vector have the same class in
`P(E)`; this is the form in which the round trips below are compared. -/
theorem mkProj_congr (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    {p q : ↥(zeroComplement (realification Z))}
    (hbase : p.1.proj = q.1.proj)
    (hvec : (show EuclideanSpace ℂ (Fin m) from p.1.2)
      = (show EuclideanSpace ℂ (Fin m) from q.1.2)) :
    mkProj Z p = mkProj Z q := by
  rw [mkProj_eq_iff]
  refine ⟨1, ?_⟩
  rw [smulPunct_one]
  refine Subtype.ext ?_
  rw [show (↑p : (realification Z).TotalSpace)
      = (⟨p.1.proj, (show EuclideanSpace ℂ (Fin m) from p.1.2)⟩ :
          (realification Z).TotalSpace) from rfl]
  rw [show (↑q : (realification Z).TotalSpace)
      = (⟨q.1.proj, (show EuclideanSpace ℂ (Fin m) from q.1.2)⟩ :
          (realification Z).TotalSpace) from rfl]
  rw [hbase, hvec]

/-! ## The two round trips -/

/-- On a class of a model vector, `projClass` is the tautological inclusion: the class of the model
vector `v` maps to the class of `v` regarded as a point of the fibre over `b`. -/
theorem projClass_fibreOf (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (v : EuclideanSpace ℂ (Fin m)) (hv : v ≠ 0) :
    projClass Z (fibreOf Z b ⟨v, hv⟩).1 = Projectivization.mk ℂ v hv := by
  rw [show (fibreOf Z b ⟨v, hv⟩).1
      = mkProj Z (⟨(⟨b, v⟩ : (realification Z).TotalSpace),
          by rw [mem_zeroComplement]; exact hv⟩ : ↥(zeroComplement (realification Z))) from rfl]
  rw [projClass_mkProj]

/-- `projClass` is a left inverse of `fibreMap Z b`. -/
theorem projClass_fibreMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (x : ℙ ℂ (EuclideanSpace ℂ (Fin m))) :
    projClass Z (fibreMap Z b x).1 = x := by
  refine Projectivization.ind (fun v hv => ?_) x
  rw [fibreMap_mk]
  exact projClass_fibreOf Z b v hv

/-- `projClass` is a right inverse of `fibreMap Z b` on the fibre `π^{-1}(b)`. -/
theorem fibreMap_projClass (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (x : ProjSpace Z) (hx : projMap Z x = b) :
    fibreMap Z b (projClass Z x) = ⟨x, hx⟩ := by
  revert hx
  refine Quotient.inductionOn (motive := fun x =>
    ∀ hx : projMap Z x = b, fibreMap Z b (projClass Z x) = ⟨x, hx⟩) x ?_
  intro p hx
  change fibreMap Z b (projClass Z (mkProj Z p)) = ⟨mkProj Z p, hx⟩
  have hpb : p.1.proj = b := by
    rw [← projMap_mkProj]; exact hx
  rw [projClass_mkProj]
  rw [fibreMap_mk]
  refine Subtype.ext ?_
  rw [show (fibreOf Z b ⟨(show EuclideanSpace ℂ (Fin m) from p.1.2),
      (mem_zeroComplement p.1).mp p.2⟩).1
      = mkProj Z (⟨(⟨b, (show EuclideanSpace ℂ (Fin m) from p.1.2)⟩ :
            (realification Z).TotalSpace),
          by rw [mem_zeroComplement]; exact ((mem_zeroComplement p.1).mp p.2)⟩ :
            ↥(zeroComplement (realification Z))) from rfl]
  exact mkProj_congr Z hpb.symm rfl

/-! ## The fibre of the projectivisation -/

/-- **The fibre of `π : P(E) → B` over `b` is `ℂP^{m-1}`**: the map from the projectivisation of the
model fibre `ℂ^m` which sends `[v]` to the class of the vector `(b, v)` of the fibre of `E` over `b`
is a bijection. -/
theorem fibreMap_bijective {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    Function.Bijective (Work.LerayHirsch.fibreMap Z b) := by
  constructor
  · intro x y hxy
    have h1 := projClass_fibreMap Z b x
    have h2 := projClass_fibreMap Z b y
    rw [hxy] at h1
    exact h1.symm.trans h2
  · intro y
    exact ⟨projClass Z y.1, fibreMap_projClass Z b y.1 y.2⟩

end

end Work.LerayHirsch
