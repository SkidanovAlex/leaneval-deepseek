import Mathlib
import Submission.Work.Drive.strip_cover_defs

/-!
# The covering map of the strip onto the band of secants is an open map

`Work.Drive.stripClass : StripPeriod → OpenMobius` sends a chord parameter
`(x, y)` (`0 < y < period`) to the secant class `{K x, K (x + y)}` of the
Möbius band of secants.  It is the universal covering map of the band in strip
coordinates; in particular it is an **open** map, which is the local fact used
to read off openness/local injectivity of the cover at the level of the strip.

The proof is a composition: `stripClass = mobiusCover ∘ φ` where

* `φ : StripPeriod → OrderedPairs`, `φ (x, y) = (x mod period, (x + y) mod period)`
  is the restriction to the open strip of the (open) quotient map
  `ℝ × ℝ → AddCircle period × AddCircle period` pre-composed with the shear
  homeomorphism `(x, y) ↦ (x, x + y)`; it is open because the quotient map of
  a topological additive group is an open quotient map and the product of two
  such is open, and because restricting an open map to an open source and an
  open target preserves openness (`IsOpenMap.subtype_map`).
* `mobiusCover : OrderedPairs → OpenMobius` is open
  (`isOpenMap_mobiusCover`, from `SecantSpace`).
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- The shear `(x, y) ↦ (x, x + y)` of the plane is a homeomorphism
(inverse `(u, v) ↦ (u, v - u)`). -/
def shearHomeo : ℝ × ℝ ≃ₜ ℝ × ℝ where
  toFun z := (z.1, z.1 + z.2)
  invFun w := (w.1, w.2 - w.1)
  left_inv z := by ext <;> simp
  right_inv w := by ext <;> simp
  continuous_toFun := continuous_fst.prodMk (continuous_fst.add continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_fst)

/-- The strip region `{0 < q.2 < period}` is open in `ℝ × ℝ`. -/
lemma isOpen_stripRegion : IsOpen ({q : ℝ × ℝ | 0 < q.2 ∧ q.2 < period} : Set (ℝ × ℝ)) := by
  rw [Set.ofPred_and]
  exact (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)

/-- The parameter map `(x, y) ↦ (x mod period, (x + y) mod period)` of the
strip into the ordered pairs of distinct parameters is an open map. -/
lemma isOpenMap_stripPairMap :
    IsOpenMap (fun p : StripPeriod => stripPair p.1 p.2.1 p.2.2) := by
  have hcoe : IsOpenQuotientMap (fun x : ℝ => (x : AddCircle period)) :=
    QuotientAddGroup.isOpenQuotientMap_mk (G := ℝ) (N := AddSubgroup.zmultiples (period : ℝ))
  have hprod : IsOpenMap (Prod.map (fun x : ℝ => (x : AddCircle period))
      (fun x : ℝ => (x : AddCircle period))) := (hcoe.prodMap hcoe).isOpenMap
  have hshear : IsOpenMap (fun z : ℝ × ℝ => (z.1, z.1 + z.2)) := shearHomeo.isOpenMap
  have hfun : (fun z : ℝ × ℝ => ((z.1 : AddCircle period), ((z.1 + z.2 : ℝ) : AddCircle period)))
      = (Prod.map (fun x : ℝ => (x : AddCircle period)) (fun x : ℝ => (x : AddCircle period)))
        ∘ (fun z : ℝ × ℝ => (z.1, z.1 + z.2)) := by
    funext z; rfl
  have hf : IsOpenMap (fun z : ℝ × ℝ => ((z.1 : AddCircle period),
      ((z.1 + z.2 : ℝ) : AddCircle period))) := by
    rw [hfun]; exact IsOpenMap.comp hprod hshear
  have hst : ∀ x ∈ ({q : ℝ × ℝ | 0 < q.2 ∧ q.2 < period} : Set (ℝ × ℝ)),
      (fun z : ℝ × ℝ => ((z.1 : AddCircle period), ((z.1 + z.2 : ℝ) : AddCircle period))) x
        ∈ ({q : AddCircle period × AddCircle period | q.1 ≠ q.2} : Set _) := by
    rintro ⟨a, b⟩ ⟨h0, h1⟩
    exact coe_ne_coe_of_lt h0 h1
  have hφ : IsOpenMap (Subtype.map (fun z : ℝ × ℝ => ((z.1 : AddCircle period),
      ((z.1 + z.2 : ℝ) : AddCircle period))) hst) := hf.subtype_map isOpen_stripRegion hst
  have hEq : (fun p : StripPeriod => stripPair p.1 p.2.1 p.2.2) =
      Subtype.map (fun z : ℝ × ℝ => ((z.1 : AddCircle period),
        ((z.1 + z.2 : ℝ) : AddCircle period))) hst := by
    funext p
    apply Subtype.ext
    rfl
  rw [hEq]
  exact hφ

/-- **The strip covering map onto the band of secants is open.** -/
theorem isOpenMap_stripClass : IsOpenMap Work.Drive.stripClass := by
  have hcomp : stripClass = mobiusCover ∘ (fun p : StripPeriod => stripPair p.1 p.2.1 p.2.2) := by
    funext p; rfl
  rw [hcomp]
  exact IsOpenMap.comp isOpenMap_mobiusCover isOpenMap_stripPairMap

end Work.Drive
