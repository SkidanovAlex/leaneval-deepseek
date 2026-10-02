import Mathlib
import Submission.Work.LerayHirsch.Punctum
import Submission.Work.LerayHirsch.TautLine
import Submission.Work.LerayHirsch.fibreMap_bijective
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_trivial
import Submission.Work.LerayHirsch.nonempty_homeo_projFibre
import Submission.Work.LerayHirsch.Naturality
import Submission.Work.LerayHirsch.ProjIsoOfBundleIso
import Submission.Work.Agree.PlumbDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The restriction of the tautological line bundle to a fibre

This module starts the identification of the restriction of the tautological line bundle `ℓ` of
`P(E)` (`Submission/Work/LerayHirsch/TautLine.lean`) to a fibre `ProjFibre Z b ≅ ℂP^{m-1}`
(`Submission/Work/LerayHirsch/nonempty_homeo_projFibre.lean`) with the **tautological line bundle of
`ℂP^{m-1}` itself**, and hence of the restriction of `ζ = c₁(ℓ)` with the hyperplane class of the
fibre.

The objects are

* `fibreIncl Z b : C(ProjFibre Z b, ProjSpace Z)` — the inclusion of the fibre;
* `projUniv m : C(ℙ ℂ (ℂ^m), ProjSpace (ε^m))` — the canonical identification of `ℂP^{m-1}` with the
  projectivisation `P(ε^m)` of the trivial bundle over `PUnit`, obtained from
  `Work.LerayHirsch.nonempty_homeo_projSpace_trivial`;
* `tautLineP m : VectorBundleCore ℂ (ℙ ℂ (ℂ^m)) (EuclideanSpace ℂ (Fin 1)) (PUnit × Fin m)` — **the
  tautological line bundle over `ℂP^{m-1}`**, the pullback of `ℓ(ε^m)` along `projUniv m`;
* `zetaP m = c₁(tautLineP m)` — **the hyperplane class of `ℂP^{m-1}`**.

The main theorem of the subproject is the bundle isomorphism (proved from these objects)

`π_fibre^*ℓ(E) ≅ (projClass Z)^*ℓ(ε^m)`   over `ProjFibre Z b`,

i.e. "the tautological bundle restricted to a fibre is the fibre's tautological bundle", and its
cohomological shadow `ζ|_fibre = ζ(ε^m)` — see `Submission/Work/LerayHirsch/FibreRestrictIso.lean`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- **The trivial complex bundle of rank `m` over a point** — the model of the fibre `ℂ^m`.  It is
an `abbrev` so that its fibre type reduces. -/
abbrev trivCore (m : ℕ) : VectorBundleCore ℂ PUnit (EuclideanSpace ℂ (Fin m)) PUnit :=
  trivialVectorBundleCore ℂ PUnit (EuclideanSpace ℂ (Fin m)) PUnit

/-! ## The inclusion of a fibre -/

/-- **The inclusion of the fibre of `π : P(E) → B` over `b`** into `P(E)`. -/
def fibreIncl (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    C(ProjFibre Z b, ProjSpace Z) :=
  ⟨fun x => x.1, continuous_subtype_val⟩

@[simp] theorem fibreIncl_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (x : ProjFibre Z b) : fibreIncl Z b x = x.1 := rfl

/-- The composite `projMap ∘ fibreIncl` is the constant map at `b`. -/
@[simp] theorem projMap_fibreIncl (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (x : ProjFibre Z b) : projMap Z (fibreIncl Z b x) = b := x.2

/-! ## The canonical identification `ℂP^{m-1} ≅ P(ε^m)` -/

/-- **The canonical continuous map `ℂP^{m-1} → P(ε^m)`**: the class of a model vector `v` is sent
to the class of `(unit, v)`, i.e. to the point of the fibre of `P(ε^m)` over `unit` that it
represents (`Work.LerayHirsch.fibreMap`).  This is the inverse of the canonical homeomorphism
`P(ε^m) ≃ₜ ℂP^{m-1}` of `Work.LerayHirsch.nonempty_homeo_projSpace_trivial`, made *explicit* (via
`fibreMap`, not via a `Classical.choice` of a `Nonempty`) so that its defining equation
`Work.LerayHirsch.projUniv_mkP` is available. -/
noncomputable def projUniv (m : ℕ) : C(ℙ ℂ (EuclideanSpace ℂ (Fin m)), ProjSpace (trivCore m)) :=
  ⟨fun x => (fibreMap (trivCore m) PUnit.unit x).1,
    continuous_subtype_val.comp (continuous_fibreMap (trivCore m) PUnit.unit)⟩

@[simp] theorem projUniv_apply (m : ℕ) (x : ℙ ℂ (EuclideanSpace ℂ (Fin m))) :
    projUniv m x = (fibreMap (trivCore m) PUnit.unit x).1 := rfl

/-- **The defining equation of `projUniv`**: the class of a nonzero model vector `v` is sent to the
class of the punctured vector `(unit, v)`. -/
theorem projUniv_mkP (m : ℕ) (v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}) :
    projUniv m (mkP m v) = mkProj (trivCore m)
      ⟨(⟨PUnit.unit, v.1⟩ : (realification (trivCore m)).TotalSpace),
        by rw [mem_zeroComplement]; exact v.2⟩ := by
  rw [projUniv_apply]
  change (fibreOf (trivCore m) PUnit.unit v).1 = _
  rfl

/-- **The tautological line bundle over `ℂP^{m-1}`**, as the pullback of the tautological line
bundle of the trivial bundle `ε^m` over `PUnit` along `projUniv m`. -/
noncomputable def tautLineP (m : ℕ) :
    VectorBundleCore ℂ (ℙ ℂ (EuclideanSpace ℂ (Fin m))) (EuclideanSpace ℂ (Fin 1))
      (PUnit × Fin m) :=
  bundleComap (tautLine (trivCore m)) (projUniv m)

/-- **The hyperplane class `ζ` of `ℂP^{m-1}`**: the first Chern class of the tautological line
bundle `Work.LerayHirsch.tautLineP m`. -/
noncomputable def zetaP (m : ℕ) : Coh ℤ 2 (ℙ ℂ (EuclideanSpace ℂ (Fin m))) :=
  cohTransport (by rfl : 2 * 1 = 2) (chernClass 1 1 (tautLineP m))

/-- **The class of the fibre coordinate, as a map on the fibre**: the composite
`ProjFibre Z b → ProjSpace Z → ℙ ℂ (ℂ^m)`. -/
def projClassFibre (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    C(ProjFibre Z b, ℙ ℂ (EuclideanSpace ℂ (Fin m))) :=
  ⟨fun x => projClass Z x.1, continuous_projClass_subtype Z b⟩

@[simp] theorem projClassFibre_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (b : B) (x : ProjFibre Z b) : projClassFibre Z b x = projClass Z x.1 := rfl

/-! ## The charts and the transitions of the restriction of `ℓ` to a fibre -/

/-- **The chart `(Z.indexAt b, k)` of the tautological line bundle restricted to the fibre over
`b`** is the set of points of the fibre whose `k`-th *fibre coordinate* does not vanish. -/
theorem mem_bundleComap_tautLine_fibreIncl (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (b : B) (k : Fin m) (x : ProjFibre Z b) :
    x ∈ (bundleComap (tautLine Z) (fibreIncl Z b)).baseSet (Z.indexAt b, k) ↔
      ∃ p : ↥(zeroComplement (realification Z)), mkProj Z p = x.1 ∧
        (show EuclideanSpace ℂ (Fin m) from p.1.2) k ≠ 0 := by
  have hproj : ∀ p : ↥(zeroComplement (realification Z)), mkProj Z p = x.1 → p.1.proj = b :=
    fun p hp => by rw [← projMap_mkProj Z p, hp]; exact x.2
  rw [bundleComap_baseSet, Set.mem_preimage, fibreIncl_apply]
  simp only [tautLine_baseSet, tautBaseSetProj, Set.mem_image]
  constructor
  · rintro ⟨p, hmem, hp⟩
    rw [mem_tautBaseSet] at hmem
    refine ⟨p, hp, ?_⟩
    have h1 : chartCoord Z ((realification Z).indexAt b) p = p.1.2 :=
      chartCoord_indexAt_eq_snd Z b p (hproj p hp)
    rw [realification_indexAt] at h1
    rw [← h1]; exact hmem.2
  · rintro ⟨p, hp, hk⟩
    refine ⟨p, ?_, hp⟩
    rw [mem_tautBaseSet]
    refine ⟨?_, ?_⟩
    · rw [hproj p hp]; exact Z.mem_baseSet_at b
    · have h1 : chartCoord Z ((realification Z).indexAt b) p = p.1.2 :=
        chartCoord_indexAt_eq_snd Z b p (hproj p hp)
      rw [realification_indexAt] at h1
      rw [h1]; exact hk

/-- **The transition functions of the tautological line bundle on a fibre are the ratios of the
fibre coordinates**: on the fibre over `b`, in the chart `(Z.indexAt b, ·)`, the transition
function of `ℓ` between the `k`-th and the `l`-th coordinate is `(p.2 l)/(p.2 k)`.  This is the
identification of the restriction of `ℓ` with the tautological bundle of the fibre, at the level of
transition functions. -/
theorem tautCoeffLift_fibreIncl (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (k l : Fin m) (p : ↥(zeroComplement (realification Z))) (hp : p.1.proj = b)
    (hk : (show EuclideanSpace ℂ (Fin m) from p.1.2) k ≠ 0) :
    tautCoeffLift Z (Z.indexAt b, k) (Z.indexAt b, l) (mkProj Z p)
      = (show EuclideanSpace ℂ (Fin m) from p.1.2) l
        / (show EuclideanSpace ℂ (Fin m) from p.1.2) k := by
  have h1 : chartCoord Z ((realification Z).indexAt b) p = p.1.2 :=
    chartCoord_indexAt_eq_snd Z b p hp
  rw [realification_indexAt] at h1
  refine (tautLine_coordChange_eq_ratio Z (Z.indexAt b, k) (Z.indexAt b, l) p ?_).trans ?_
  · rw [h1]; exact hk
  · rw [h1]

/-- **The charts of the restriction of `ℓ` to a fibre** are the charts of the tautological bundle
of the fibre: the `k`-th chart is the set of points of the fibre whose `k`-th fibre coordinate does
not vanish. -/
theorem fibreIncl_chart (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (k : Fin m) :
    (bundleComap (tautLine Z) (fibreIncl Z b)).baseSet (Z.indexAt b, k)
      = {x : ProjFibre Z b | ∃ p : ↥(zeroComplement (realification Z)),
          mkProj Z p = x.1 ∧ (show EuclideanSpace ℂ (Fin m) from p.1.2) k ≠ 0} :=
  Set.ext fun x => mem_bundleComap_tautLine_fibreIncl Z b k x

/-! ## The charts and the transitions of the tautological bundle over `ℂP^{m-1}` -/

theorem chartCoord_trivial (m : ℕ) (i : PUnit)
    (p : ↥(zeroComplement (realification (trivCore m)))) :
    chartCoord (trivCore m) i p = (show EuclideanSpace ℂ (Fin m) from p.1.2) := by
  rw [chartCoord_def]
  rfl

/-- **The charts of the tautological line bundle over `ℂP^{m-1}`**: the `k`-th chart of
`Work.LerayHirsch.tautLineP m` is the set of points of `ℂP^{m-1}` having a representative whose
`k`-th coordinate does not vanish. -/
theorem mem_tautLineP_baseSet (m : ℕ) (k : Fin m)
    (x : Projectivization ℂ (EuclideanSpace ℂ (Fin m))) :
    x ∈ (tautLineP m).baseSet (PUnit.unit, k) ↔
      ∃ v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}, mkP m v = x ∧ v.1 k ≠ 0 := by
  revert x
  refine Projectivization.ind (fun v hv => ?_)
  let p : ↥(zeroComplement (realification (trivCore m))) :=
    ⟨(⟨PUnit.unit, v⟩ : (realification (trivCore m)).TotalSpace),
      by rw [mem_zeroComplement]; exact hv⟩
  have hpvec : (show EuclideanSpace ℂ (Fin m) from p.1.2) = v := rfl
  have hp₀ : projUniv m (mkP m ⟨v, hv⟩) = mkProj (trivCore m) p := projUniv_mkP m ⟨v, hv⟩
  have hgoal : (∃ w : {w : EuclideanSpace ℂ (Fin m) // w ≠ 0},
      mkP m w = mkP m ⟨v, hv⟩ ∧ w.1 k ≠ 0) ↔ v k ≠ 0 := by
    constructor
    · rintro ⟨w, hw, hwk⟩
      obtain ⟨c, hc⟩ := (mkP_eq_iff (m := m)).mp hw
      have hcw : (↑w : EuclideanSpace ℂ (Fin m)) k = c * v k := by
        rw [← hc]; rfl
      intro h0
      exact hwk (by rw [hcw, h0, mul_zero])
    · intro hvk
      exact ⟨⟨v, hv⟩, rfl, hvk⟩
  rw [show Projectivization.mk ℂ v hv = mkP m ⟨v, hv⟩ from rfl, hgoal]
  rw [tautLineP, bundleComap_baseSet, Set.mem_preimage, hp₀]
  simp only [tautLine_baseSet, tautBaseSetProj, Set.mem_image]
  constructor
  · rintro ⟨q, hmem, hq⟩
    rw [mem_tautBaseSet] at hmem
    have hqk : (show EuclideanSpace ℂ (Fin m) from q.1.2) k ≠ 0 := by
      rw [← chartCoord_trivial m PUnit.unit q]; exact hmem.2
    obtain ⟨c, hc⟩ := (mkProj_eq_iff (trivCore m)).mp hq
    have hcongr : (show EuclideanSpace ℂ (Fin m) from q.1.2)
        = (c : ℂ) • (show EuclideanSpace ℂ (Fin m) from p.1.2) := by
      have h := congrArg (fun r : ↥(zeroComplement (realification (trivCore m))) =>
        (show EuclideanSpace ℂ (Fin m) from r.1.2)) hc
      rw [smulPunct_snd] at h
      exact h.symm
    have h2 := hcongr
    have h3 : (show EuclideanSpace ℂ (Fin m) from q.1.2) k
        = (c : ℂ) * (show EuclideanSpace ℂ (Fin m) from p.1.2) k := by
      rw [h2]; rfl
    have hvh : (show EuclideanSpace ℂ (Fin m) from p.1.2) k = v k := rfl
    intro h0
    exact hqk (by rw [h3, hvh, h0, mul_zero])
  · intro hvk
    refine ⟨p, ?_, rfl⟩
    rw [mem_tautBaseSet]
    refine ⟨trivial, ?_⟩
    rw [chartCoord_trivial]
    exact hvk

/-- **The transition functions of the tautological line bundle over `ℂP^{m-1}` are the ratios of
the homogeneous coordinates**: between the `k`-th and the `l`-th chart, the transition function of
`Work.LerayHirsch.tautLineP m` at the class of a nonzero vector `v` is multiplication by
`(v l)/(v k)`. -/
theorem tautLineP_coordChange_eq_ratio (m : ℕ) (k l : Fin m)
    (v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}) (hk : v.1 k ≠ 0) :
    (tautLineP m).coordChange (PUnit.unit, k) (PUnit.unit, l) (mkP m v)
      = (v.1 l / v.1 k) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
  let p : ↥(zeroComplement (realification (trivCore m))) :=
    ⟨(⟨PUnit.unit, v.1⟩ : (realification (trivCore m)).TotalSpace),
      by rw [mem_zeroComplement]; exact v.2⟩
  have hpvec : (show EuclideanSpace ℂ (Fin m) from p.1.2) = v.1 := rfl
  have hp₀ : projUniv m (mkP m v) = mkProj (trivCore m) p := projUniv_mkP m v
  have hrat : tautCoeffLift (trivCore m) (PUnit.unit, k) (PUnit.unit, l) (mkProj (trivCore m) p)
      = v.1 l / v.1 k := by
    have h := tautLine_coordChange_eq_ratio (trivCore m) (PUnit.unit, k) (PUnit.unit, l) p
      (by rw [chartCoord_trivial]; exact hk)
    rw [h]
    have h1 : chartCoord (trivCore m) PUnit.unit p = (show EuclideanSpace ℂ (Fin m) from p.1.2) :=
      chartCoord_trivial m PUnit.unit p
    rw [h1, hpvec]
  rw [tautLineP, bundleComap_coordChange, hp₀, tautLine_coordChange, tautCoeffCLM, hrat]

end

end Work.LerayHirsch
