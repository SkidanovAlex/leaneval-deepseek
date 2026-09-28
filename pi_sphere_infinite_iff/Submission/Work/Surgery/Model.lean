import Mathlib

set_option synthInstance.maxHeartbeats 400000

/-!
# The half-space model for manifolds with boundary, and its frontier

This is the first file of the chapter `Submission/Work/Surgery/`, the geometry of surgery in
dimension `8`.  It fixes the *model* once and for all, in the vocabulary of Mathlib's
`ModelWithCorners`: smooth `n`-manifolds with boundary are manifolds modelled on the half-space
`𝓡∂ n = modelWithCornersEuclideanHalfSpace n`, i.e. on
`H = EuclideanHalfSpace n = {x : ℝⁿ | 0 ≤ x 0}` inside `E = EuclideanSpace ℝ (Fin n)`.

The chapter uses the following conventions (see `README.md`):

* `halfModel n` is `𝓡∂ n`;
* `boundaryModel n hn` is the boundaryless model `𝓡 (n-1)` on `EuclideanSpace ℝ (Fin (n-1))`,
  the model of the boundary `∂M` of an `n`-manifold `M` with boundary;
* for a charted space `M` over `EuclideanHalfSpace n`, the boundary is `(𝓡∂ n).boundary M`, a
  closed subset of `M` (`ModelWithCorners.isClosed_boundary`);
* a *collar* of `M` is a homeomorphism of `∂M × ℝ≥0` onto an open neighbourhood of `∂M`
  (`Submission/Work/Surgery/Collar.lean`);
* when two manifolds with boundary are glued along their boundaries, the identification is a
  diffeomorphism of the boundary manifolds (`Boundary.lean`), and the local model of the gluing
  is the pair of half-spaces `{0 ≤ x 0}` and `{x 0 ≤ 0}` inside the *boundaryless* space `E`,
  glued along the hyperplane `{x 0 = 0}` — the content of this file.

## Main definitions and results

* `Work.Surgery.halfModel`, `Work.Surgery.hyperplane`, `Work.Surgery.boundaryModel`;
* `range_halfModel`, `frontier_range_halfModel`, `interior_range_halfModel` — the model's range,
  frontier and interior in coordinates;
* `flipLin`, `flipCont`, `flipEucl` — the reflection of the first coordinate: an automorphism of
  `E` of order two (`flipEucl_involutive`);
* `flipEucl_image_halfSpacePos`, `union_halfSpace`, `inter_halfSpace` — the reflection exchanges
  the two half-spaces, and the two cover `E` meeting in the hyperplane.  **This is the local
  model of gluing two manifolds with boundary along their boundaries**;
* `dropPi`, `dropEucl` — the linear isomorphism `{x : ℝ^{n+1} | x 0 = 0} ≅ ℝⁿ`, used to chart the
  boundary of a manifold with boundary;
* `tailCont`, `consCont` — the continuous linear maps `ℝ^{n+1} → ℝⁿ` and `ℝⁿ → ℝ^{n+1}` behind it.
-/

open scoped Manifold Topology
open Function

namespace Work.Surgery

noncomputable section

variable {n : ℕ}

/-! ## The model with corners, its range, frontier and interior -/

/-- **The half-space model** for smooth `n`-manifolds with boundary: `𝓡∂ n` for the `Manifold`
notation scope. -/
abbrev halfModel (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

/-- The boundaryless model for the *boundary* of an `n`-manifold with boundary: `ℝ^{n-1}`. -/
abbrev boundaryModel (n : ℕ) (_hn : 1 ≤ n) :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (n - 1))) (EuclideanSpace ℝ (Fin (n - 1))) :=
  𝓡 (n - 1)

/-- **The boundary hyperplane** `{x : ℝⁿ | x 0 = 0}` of the model space: the frontier of the
half-space, and the local model of a boundary. -/
def hyperplane (n : ℕ) [NeZero n] : Set (EuclideanSpace ℝ (Fin n)) := {x | x 0 = 0}

theorem mem_hyperplane_iff {n : ℕ} [NeZero n] {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ hyperplane n ↔ x 0 = 0 := Iff.rfl

theorem range_halfModel (n : ℕ) [NeZero n] : Set.range (halfModel n) = {x | 0 ≤ x 0} :=
  range_modelWithCornersEuclideanHalfSpace n

theorem interior_range_halfModel (n : ℕ) [NeZero n] :
    interior (Set.range (halfModel n)) = {x : EuclideanSpace ℝ (Fin n) | 0 < x 0} :=
  interior_range_modelWithCornersEuclideanHalfSpace n

theorem frontier_range_halfModel (n : ℕ) [NeZero n] :
    frontier (Set.range (halfModel n)) = hyperplane n := by
  rw [frontier_range_modelWithCornersEuclideanHalfSpace n]
  ext x
  exact eq_comm

/-! ## The two half-spaces and the reflection of the first coordinate

The local model of a gluing of two manifolds with boundary along a common boundary is the pair of
closed half-spaces `H⁺ = {0 ≤ x 0}` and `H⁻ = {x 0 ≤ 0}` inside `E`, glued along their common
frontier `{x 0 = 0}`; the reflection `flip` (negating the first coordinate) is an isomorphism of
`E` carrying one onto the other, and the two cover `E` meeting in the hyperplane. -/

/-- The positive half-space of the model: the range of `𝓡∂ n`. -/
def halfSpacePos (n : ℕ) [NeZero n] : Set (EuclideanSpace ℝ (Fin n)) := {x | 0 ≤ x 0}

/-- The negative half-space of the model. -/
def halfSpaceNeg (n : ℕ) [NeZero n] : Set (EuclideanSpace ℝ (Fin n)) := {x | x 0 ≤ 0}

theorem mem_halfSpacePos_iff {n : ℕ} [NeZero n] {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ halfSpacePos n ↔ 0 ≤ x 0 := Iff.rfl

theorem mem_halfSpaceNeg_iff {n : ℕ} [NeZero n] {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ halfSpaceNeg n ↔ x 0 ≤ 0 := Iff.rfl

theorem range_halfModel_eq_halfSpacePos (n : ℕ) [NeZero n] :
    Set.range (halfModel n) = halfSpacePos n := by
  rw [range_halfModel]
  rfl

/-- The canonical continuous linear equivalence `ℝ^m ≃ (Fin m → ℝ)`. -/
abbrev euclToPi (m : ℕ) : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)

/-- The canonical continuous linear equivalence `(Fin m → ℝ) ≃ ℝ^m`. -/
abbrev piToEucl (m : ℕ) : (Fin m → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (euclToPi m).symm

/-- **The first unit vector** `e₀` of the model space `ℝ^{n+1}`, i.e. the inward normal direction of
the half-space. -/
def e₀ (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  piToEucl (n + 1) (Pi.single 0 1)

@[simp] theorem e₀_apply_zero (n : ℕ) : e₀ n 0 = 1 := by
  simp [e₀]

@[simp] theorem e₀_apply_succ (n : ℕ) (k : Fin n) : e₀ n k.succ = 0 := by
  simp [e₀]


/-- **The reflection of the first coordinate** of `ℝ^{n+1}`, as a continuous linear map: it
negates the first coordinate and fixes the others. -/
def flipCLM (n : ℕ) : (Fin (n+1) → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin (n+1) =>
    Fin.cases (-(ContinuousLinearMap.proj (0 : Fin (n+1))))
      (fun k => ContinuousLinearMap.proj k.succ) i

@[simp] theorem flipCLM_apply_zero (n : ℕ) (x : Fin (n+1) → ℝ) : flipCLM n x 0 = -(x 0) := by
  simp [flipCLM]

@[simp] theorem flipCLM_apply_succ (n : ℕ) (x : Fin (n+1) → ℝ) (k : Fin n) :
    flipCLM n x k.succ = x k.succ := by
  simp [flipCLM]

/-- The reflection of the first coordinate on `ℝ^{n+1}` is an involution. -/
theorem flipCLM_invol (n : ℕ) (x : Fin (n+1) → ℝ) : flipCLM n (flipCLM n x) = x := by
  funext i
  induction i using Fin.cases with
  | zero => rw [flipCLM_apply_zero, flipCLM_apply_zero, neg_neg]
  | succ k => rw [flipCLM_apply_succ, flipCLM_apply_succ]

/-- The reflection of the first coordinate on `Fin (n+1) → ℝ`, as a linear equivalence. -/
def flipLin (n : ℕ) : (Fin (n+1) → ℝ) ≃ₗ[ℝ] (Fin (n+1) → ℝ) where
  toFun := flipCLM n
  invFun := flipCLM n
  left_inv := flipCLM_invol n
  right_inv := flipCLM_invol n
  map_add' := fun x y => map_add (flipCLM n) x y
  map_smul' := fun c x => map_smul (flipCLM n) c x

@[simp] theorem flipLin_apply (n : ℕ) (x : Fin (n+1) → ℝ) : flipLin n x = flipCLM n x := rfl

/-- The reflection of the first coordinate, as a continuous linear equivalence of
`Fin (n+1) → ℝ`. -/
def flipCont (n : ℕ) : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ) :=
  (flipLin n).toContinuousLinearEquiv

@[simp] theorem flipCont_apply (n : ℕ) (x : Fin (n+1) → ℝ) : flipCont n x = flipLin n x := rfl

/-- The reflection of the first coordinate, as a continuous linear equivalence of `ℝ^{n+1}`. -/
def flipEucl (n : ℕ) : EuclideanSpace ℝ (Fin (n+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
  (euclToPi (n+1)).trans ((flipCont n).trans (piToEucl (n+1)))

theorem euclToPi_ofLp (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) : euclToPi m x = x.ofLp := by
  funext i
  rw [PiLp.continuousLinearEquiv_apply]

theorem ofLp_piToEucl (m : ℕ) (w : Fin m → ℝ) : ((piToEucl m) w).ofLp = w := by
  rw [piToEucl, PiLp.continuousLinearEquiv_symm_apply, WithLp.ofLp_toLp]

theorem flipEucl_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    flipEucl n x = piToEucl (n+1) (flipLin n (euclToPi (n+1) x)) := rfl

theorem flipEucl_ofLp (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    (flipEucl n x).ofLp = flipLin n x.ofLp := by
  rw [flipEucl_apply, euclToPi_ofLp, ofLp_piToEucl]

@[simp] theorem flipEucl_apply_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    flipEucl n x 0 = -(x 0) := by
  show (flipEucl n x).ofLp 0 = -(x.ofLp 0)
  rw [flipEucl_ofLp, flipLin_apply, flipCLM_apply_zero]

@[simp] theorem flipEucl_apply_succ (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) (k : Fin n) :
    flipEucl n x k.succ = x k.succ := by
  show (flipEucl n x).ofLp k.succ = x.ofLp k.succ
  rw [flipEucl_ofLp, flipLin_apply, flipCLM_apply_succ]

/-- **The reflection of the first coordinate is an involution of `ℝ^{n+1}`.** -/
theorem flipEucl_involutive (n : ℕ) : Function.Involutive (flipEucl n) := by
  intro x
  refine PiLp.ext fun i => ?_
  show (flipEucl n (flipEucl n x)).ofLp i = x.ofLp i
  rw [flipEucl_ofLp, flipEucl_ofLp]
  simp only [flipLin_apply, flipCLM_invol]

/-! ## Dropping the first coordinate: the model of the boundary

The boundary `∂M` of a manifold with boundary is modelled on `ℝ^{n-1}`, via the charts of `M`
followed by the continuous linear isomorphism `ℝⁿ ⊇ {x 0 = 0} ≅ ℝ^{n-1}` which deletes the first
coordinate.  The maps `tailCLM` (delete) and `consCLM` (insert a zero) implement it. -/

/-- `Fin.tail` as a continuous linear map `ℝ^{n+1} → ℝⁿ`: delete the first coordinate. -/
def tailCLM (n : ℕ) : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (piToEucl n).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k : Fin n =>
      (ContinuousLinearMap.proj k.succ).comp (euclToPi (n+1)).toContinuousLinearMap)

theorem tailCLM_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) (k : Fin n) :
    tailCLM n x k = x k.succ := by
  simp [tailCLM, piToEucl, euclToPi]

/-- `Fin.cons` as a continuous linear map `ℝ × ℝⁿ → ℝ^{n+1}`. -/
def consCLM (n : ℕ) : ℝ × EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
  (piToEucl (n+1)).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Fin (n+1) =>
      Fin.cases (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n)))
        (fun k => (ContinuousLinearMap.proj k).comp
          ((euclToPi n).toContinuousLinearMap.comp
            (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))))) j)

theorem consCLM_apply_zero (n : ℕ) (a : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    consCLM n (a, z) 0 = a := by
  simp [consCLM, piToEucl, euclToPi]

theorem consCLM_apply_succ (n : ℕ) (a : ℝ) (z : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    consCLM n (a, z) k.succ = z k := by
  simp [consCLM, piToEucl, euclToPi]

theorem tailCLM_consCLM (n : ℕ) (a : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    tailCLM n (consCLM n (a, z)) = z := by
  ext k
  rw [tailCLM_apply, consCLM_apply_succ]

theorem consCLM_tail (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    consCLM n (x 0, tailCLM n x) = x := by
  apply PiLp.ext
  intro j
  induction j using Fin.cases with
  | zero => rw [consCLM_apply_zero]
  | succ k => rw [consCLM_apply_succ, tailCLM_apply]

/-- Insert a zero in the first coordinate: the inverse of `tailCLM` on the hyperplane. -/
def consZeroCLM (n : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
  (consCLM n).comp
    ((0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ _))

theorem consZeroCLM_apply (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    consZeroCLM n z = consCLM n (0, z) := rfl

theorem tailCLM_consZeroCLM (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    tailCLM n (consZeroCLM n z) = z := by
  rw [consZeroCLM_apply, tailCLM_consCLM]

@[simp] theorem consZeroCLM_apply_zero (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    consZeroCLM n z 0 = 0 := by
  rw [consZeroCLM_apply, consCLM_apply_zero]

theorem consZeroCLM_mem_halfSpace (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    consZeroCLM n z ∈ halfSpacePos (n+1) := by
  rw [mem_halfSpacePos_iff, consZeroCLM_apply_zero]

/-- **The round trip `cons ∘ tail` on the hyperplane**: inserting a zero in front of `Fin.tail x`
recovers `x` for `x` in the hyperplane. -/
theorem consZeroCLM_tailCLM (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) (hx : x 0 = 0) :
    consZeroCLM n (tailCLM n x) = x := by
  rw [consZeroCLM_apply, ← hx]
  exact consCLM_tail n x

end


/-- Adding `t` times the inward unit normal `e₀` to a vector whose first coordinate is zero. -/
theorem consZeroCLM_add_e₀ (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    consZeroCLM n z + t • e₀ n = consCLM n (t, z) := by
  ext k
  induction k using Fin.cases with
  | zero => simp [e₀, consCLM, consZeroCLM, piToEucl, euclToPi]
  | succ k => simp [e₀, consCLM, consZeroCLM, piToEucl, euclToPi]

end Work.Surgery
