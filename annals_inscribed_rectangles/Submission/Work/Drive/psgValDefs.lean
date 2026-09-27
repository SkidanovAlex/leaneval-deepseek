import Mathlib
import Submission.Work.Drive.psgFamilyDefs
import Submission.Work.Drive.FamBox.Defs
import Submission.Work.Drive.sgPiecesDefs

/-!
# The value maps and the corner pieces of the path family of `psg_family_regular`

This module fixes the notation of the Sard-regularity obligation `Work.Drive.psg_family_regular`:

* `Work.Drive.psgLoopPt` — the point of the unit circle at which the loop of the chart is read, as a
  function of the box coordinate `z 1`;
* `Work.Drive.psgLoopVal` — **the loop value** of the path family at the chart shift `q` and the box
  point `z`;
* `Work.Drive.psgChainVal` — **the chain value** of the path family at the chain shift `τ₂` and the
  box point `z`;
* `Work.Drive.cornerLM`, `Work.Drive.cornerSub`, `Work.Drive.cornerPt` — the *corner pieces* of the
  box, used to avoid the meets on two faces at once (the codimension-`2` faces): the map
  `z ↦ (z j, z k)` whose kernel is the corner subspace of the coordinates `j, k`, and the affine
  embedding of that kernel onto the corner `z j = a`, `z k = b`.

The analytic lemmas about these objects live in the sibling modules
(`psgLoopVal_contMDiff`, `psgChainVal_contMDiff`, `hsurj_psgLoopVal`, `cornerSub_data`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology
open Set

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

variable {m : ℕ}

/-- **The point of the unit circle** at which the core loop of the chart is read along the box
coordinate `z 1`. -/
def psgLoopPt (z : Amb 4) : ℂ :=
  Complex.exp (Real.pi * ((z 1 : ℝ) : ℂ) * Complex.I)

/-- **The loop value of the path family** at the chart shift `q` and the box point `z`: the point of
the core loop of the `(z 0)`-shifted chart `Ξ (psgPathL A B (z 0) + q) ∘ Q`, at the loop parameter
`z 1`. -/
def psgLoopVal (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (q : EuclideanSpace ℝ (Fin m)) (z : Amb 4) : CappingSpace :=
  Ξ (psgPathL A B (z 0) + q) (Q (psgLoopPt z))

/-- **The chain value of the path family** at the chain shift `τ₂` and the box point `z`. -/
def psgChainVal (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (tA tB : ℝ) (τ₂ : EuclideanSpace ℝ (Fin m)) (z : Amb 4) : CappingSpace :=
  famChain (psgChainFam Ξ Q c A B tA tB τ₂) z

@[simp] lemma psgLoopPt_apply (z : Amb 4) :
    psgLoopPt z = Complex.exp (Real.pi * ((z 1 : ℝ) : ℂ) * Complex.I) := rfl

/-- The loop value is the `famLoop` of the loop family of the path. -/
lemma psgLoopVal_eq_famLoop (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (q : EuclideanSpace ℝ (Fin m)) (z : Amb 4) :
    psgLoopVal Ξ Q A B q z = famLoop (psgLoopFam Ξ Q A B q) z := by
  rw [psgLoopVal, psgLoopFam_apply]
  rfl

/-- The chain value is the `famChain` of the chain family of the path. -/
@[simp] lemma psgChainVal_eq_famChain (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (tA tB : ℝ) (τ₂ : EuclideanSpace ℝ (Fin m)) (z : Amb 4) :
    psgChainVal Ξ Q c A B tA tB τ₂ z = famChain (psgChainFam Ξ Q c A B tA tB τ₂) z := rfl

/-! ## The corner pieces of the box -/

/-- The `j`-th standard basis vector of `Amb 4 = ℝ^5`. -/
def e5 (j : Fin 5) : Amb 4 := EuclideanSpace.single j (1 : ℝ)

/-- **The linear map whose kernel is the corner subspace of the coordinates `j, k`**: the map
`z ↦ (z j, z k)`.  For `j ≠ k` its kernel is the codimension-`2` subspace `{z | z j = 0 ∧ z k = 0}`
and it is surjective. -/
def cornerLM (j k : Fin 5) : Amb 4 →ₗ[ℝ] (ℝ × ℝ) :=
  ((PiLp.proj 2 (fun _ : Fin 5 => ℝ) j).prod
    (PiLp.proj 2 (fun _ : Fin 5 => ℝ) k)).toLinearMap

/-- **The corner subspace of the coordinates `j, k`**: the kernel of `cornerLM j k`, i.e.
`{z | z j = 0 ∧ z k = 0}`. -/
def cornerSub (j k : Fin 5) : Submodule ℝ (Amb 4) := (cornerLM j k).ker

@[simp] lemma cornerLM_apply (j k : Fin 5) (z : Amb 4) :
    cornerLM j k z = (z j, z k) := rfl

/-- **The corner embedding**: the affine embedding of the corner subspace of `(j, k)` onto the corner
`z j = a`, `z k = b` of the box, sending `y` to `y + a e_j + b e_k`. -/
def cornerPt (j k : Fin 5) (a b : ℝ) (y : cornerSub j k) : Amb 4 :=
  (y : Amb 4) + a • e5 j + b • e5 k

@[simp] lemma cornerPt_coe (j k : Fin 5) (a b : ℝ) (y : cornerSub j k) :
    cornerPt j k a b y = (y : Amb 4) + a • e5 j + b • e5 k := rfl


/-- **The real label of a face value**: `0` and `1` as real numbers. -/
def fin2Real (b : Fin 2) : ℝ := if b = 0 then 0 else 1

@[simp] lemma fin2Real_zero : fin2Real 0 = 0 := by simp [fin2Real]

@[simp] lemma fin2Real_one : fin2Real 1 = 1 := by
  simp only [fin2Real, Fin.isValue, Fin.reduceEq, ↓reduceIte]

lemma exists_fin2Real (t : ℝ) (h : t = 0 ∨ t = 1) : ∃ b : Fin 2, fin2Real b = t := by
  rcases h with h | h
  · exact ⟨0, by rw [h]; simp⟩
  · exact ⟨1, by rw [h]; simp⟩

/-- A point of the corner subspace has vanishing `j`- and `k`-coordinates. -/

lemma cornerSub_apply_eq_zero (j k : Fin 5) (y : cornerSub j k) :
    (y : Amb 4) j = 0 ∧ (y : Amb 4) k = 0 := by
  have h : cornerLM j k (y : Amb 4) = 0 := y.2
  refine ⟨?_, ?_⟩
  · have := congrArg Prod.fst h
    simpa [cornerLM, LinearMap.prod_apply, PiLp.proj_apply] using this
  · have := congrArg Prod.snd h
    simpa [cornerLM, LinearMap.prod_apply, PiLp.proj_apply] using this

end

end Work.Drive
