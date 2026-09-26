import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.CoreTopology.Disk

/-!
# Cylindrical regions over a plane disc

This file sets up the vocabulary of the target

`Work.Drive.Mono.isEmbeddedSphere_frontier_of_cylindricalRegion`:

the *cylindrical region* over a plane set `S` between two continuous functions `α ≤ β` is

`cReg S α β = {p : ℝ³ | cproj p ∈ S ∧ α (cproj p) < clast p ∧ clast p < β (cproj p)}`,

where `cproj` is the projection of `ℝ³` onto its first two coordinates and `clast` is the third
coordinate.  Its closure is `cCyl S α β` (the same with `≤`) and its interior is `cInt S α β`
(the same with `cproj p ∈ interior S`).

The target asks that the *frontier* of `cReg S α β` be an embedded `2`-sphere whenever `S` is a
plane disc (the image of an injective continuous map of `𝔻` whose boundary circle maps onto
`frontier S`) and `α < β` on `S`.

The main construction (in `Submission/Work/Drive/Mono/isEmbeddedSphere_frontier_of_cylindricalRegion.lean`)
is a homeomorphism from the solid cylinder `cCylBase = 𝔻 × [-1,1]` onto `cCyl S α β`, given by
fiberwise rescaling of the third coordinate (`cCylMap`), transported along the plane disc
parametrisation of `S`; the frontier of the solid cylinder is an embedded sphere because the
cylinder is convex (`exists_homeomorph_image_interior_closure_frontier_eq_unitBall`).

## Main definitions

* `cproj`, `clast`, `cmk` — the projection, the third coordinate, and their section;
* `cCylBase` — the solid cylinder `𝔻 × [-1,1] ⊆ ℝ³` in `cproj`/`clast` coordinates;
* `cCyl`, `cReg`, `cInt` — the closed, open and interior cylindrical regions over `S`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-- The projection of a point of `ℝ³` to its first two coordinates (the map appearing in the
statement of the target). -/
def cproj (p : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i : Fin 2 => p (Fin.castSucc i))

/-- The third coordinate of a point of `ℝ³`. -/
def clast (p : EuclideanSpace ℝ (Fin 3)) : ℝ := p 2

/-- The point of `ℝ³` with first two coordinates `x` and third coordinate `y`. -/
def cmk (x : EuclideanSpace ℝ (Fin 2)) (y : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![x 0, x 1, y]

@[simp] theorem cproj_cmk (x : EuclideanSpace ℝ (Fin 2)) (y : ℝ) : cproj (cmk x y) = x := by
  ext i
  fin_cases i <;> simp [cproj, cmk]

@[simp] theorem clast_cmk (x : EuclideanSpace ℝ (Fin 2)) (y : ℝ) : clast (cmk x y) = y := by
  simp [clast, cmk]

theorem cmk_cproj_clast (p : EuclideanSpace ℝ (Fin 3)) : cmk (cproj p) (clast p) = p := by
  ext i
  fin_cases i <;> simp [cproj, clast, cmk]

theorem cmk_injective : Function.Injective (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => cmk q.1 q.2) := by
  intro a b hab
  have h1 : cproj (cmk a.1 a.2) = cproj (cmk b.1 b.2) := congrArg cproj hab
  have h2 : clast (cmk a.1 a.2) = clast (cmk b.1 b.2) := congrArg clast hab
  simp only [cproj_cmk, clast_cmk] at h1 h2
  exact Prod.ext h1 h2

theorem cmk_eq_cmk_iff (x x' : EuclideanSpace ℝ (Fin 2)) (y y' : ℝ) :
    cmk x y = cmk x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    exact ⟨by rw [← cproj_cmk x y, h, cproj_cmk], by rw [← clast_cmk x y, h, clast_cmk]⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-! ## Linearity of the projection and of the third coordinate -/

theorem cproj_add (p q : EuclideanSpace ℝ (Fin 3)) : cproj (p + q) = cproj p + cproj q := by
  ext i
  fin_cases i <;> simp [cproj]

theorem cproj_sub (p q : EuclideanSpace ℝ (Fin 3)) : cproj (p - q) = cproj p - cproj q := by
  ext i
  fin_cases i <;> simp [cproj]

theorem cproj_smul (c : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : cproj (c • p) = c • cproj p := by
  ext i
  fin_cases i <;> simp [cproj]

theorem cproj_neg (p : EuclideanSpace ℝ (Fin 3)) : cproj (-p) = -cproj p := by
  rw [← neg_one_smul ℝ p, cproj_smul]; simp

theorem clast_add (p q : EuclideanSpace ℝ (Fin 3)) : clast (p + q) = clast p + clast q := by
  simp [clast]

theorem clast_sub (p q : EuclideanSpace ℝ (Fin 3)) : clast (p - q) = clast p - clast q := by
  simp [clast]

theorem clast_smul (c : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : clast (c • p) = c * clast p := by
  simp [clast]

theorem cmk_add (x x' : EuclideanSpace ℝ (Fin 2)) (y y' : ℝ) :
    cmk x y + cmk x' y' = cmk (x + x') (y + y') := by
  rw [← cmk_cproj_clast (cmk x y + cmk x' y'), cproj_add, cproj_cmk, cproj_cmk, clast_add,
    clast_cmk, clast_cmk]

theorem cmk_sub (x x' : EuclideanSpace ℝ (Fin 2)) (y y' : ℝ) :
    cmk x y - cmk x' y' = cmk (x - x') (y - y') := by
  rw [← cmk_cproj_clast (cmk x y - cmk x' y'), cproj_sub, cproj_cmk, cproj_cmk, clast_sub,
    clast_cmk, clast_cmk]

theorem cmk_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) (y : ℝ) :
    c • cmk x y = cmk (c • x) (c * y) := by
  rw [← cmk_cproj_clast (c • cmk x y), cproj_smul, cproj_cmk, clast_smul, clast_cmk]

/-! ## Norm computations -/

theorem norm_sq_cmk (x : EuclideanSpace ℝ (Fin 2)) (y : ℝ) : ‖cmk x y‖ ^ 2 = ‖x‖ ^ 2 + y ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [cmk, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem norm_cproj_le (p : EuclideanSpace ℝ (Fin 3)) : ‖cproj p‖ ≤ ‖p‖ := by
  have h : ‖cmk (cproj p) (clast p)‖ ^ 2 = ‖cproj p‖ ^ 2 + clast p ^ 2 := norm_sq_cmk _ _
  rw [cmk_cproj_clast] at h
  nlinarith [norm_nonneg (cproj p), norm_nonneg p, sq_nonneg (clast p)]

theorem abs_clast_le (p : EuclideanSpace ℝ (Fin 3)) : |clast p| ≤ ‖p‖ := by
  have h : ‖cmk (cproj p) (clast p)‖ ^ 2 = ‖cproj p‖ ^ 2 + clast p ^ 2 := norm_sq_cmk _ _
  rw [cmk_cproj_clast] at h
  nlinarith [norm_nonneg (cproj p), norm_nonneg p, sq_nonneg (clast p), abs_nonneg (clast p),
    sq_abs (clast p), sq_nonneg (‖p‖ - |clast p|)]

theorem norm_mk_sub_le (p q : EuclideanSpace ℝ (Fin 3)) :
    max ‖cproj p - cproj q‖ |clast p - clast q| ≤ ‖p - q‖ := by
  have h1 : ‖cproj (p - q)‖ ≤ ‖p - q‖ := norm_cproj_le _
  have h2 : |clast (p - q)| ≤ ‖p - q‖ := abs_clast_le _
  rw [cproj_sub] at h1
  rw [clast_sub] at h2
  exact max_le h1 h2

/-! ## Continuity -/

theorem continuous_cproj : Continuous cproj := by
  show Continuous fun p : EuclideanSpace ℝ (Fin 3) =>
    (WithLp.toLp 2 (fun i : Fin 2 => p (Fin.castSucc i)) : EuclideanSpace ℝ (Fin 2))
  fun_prop

theorem continuous_clast : Continuous clast := by
  show Continuous fun p : EuclideanSpace ℝ (Fin 3) => p 2
  fun_prop

theorem continuous_cmk :
    Continuous fun q : EuclideanSpace ℝ (Fin 2) × ℝ => cmk q.1 q.2 := by
  have h1 : Continuous fun q : EuclideanSpace ℝ (Fin 2) × ℝ =>
      (![q.1 0, q.1 1, q.2] : Fin 3 → ℝ) := by
    rw [continuous_pi_iff]
    intro i
    fin_cases i <;> simp <;> fun_prop
  have := (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp h1
  exact this

/-! ## The cylindrical regions -/

/-- The solid cylinder `𝔻 × [-1,1]` over the unit disc, in `ℝ³` coordinates. -/
def cCylBase : Set (EuclideanSpace ℝ (Fin 3)) :=
  {p | ‖cproj p‖ ≤ 1 ∧ |clast p| ≤ 1}

/-- The unit disc of `ℂ`, seen in the first two coordinates of `ℝ³`: the base of the solid
cylinder `cCylBase`. -/
def cBase : Set (EuclideanSpace ℝ (Fin 3)) :=
  {p | ‖cproj p‖ ≤ 1}

/-- The **closed cylindrical region** over `S` between `α` and `β`. -/
def cCyl (S : Set (EuclideanSpace ℝ (Fin 2))) (α β : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {p | cproj p ∈ S ∧ α (cproj p) ≤ clast p ∧ clast p ≤ β (cproj p)}

/-- The **open cylindrical region** over `S` between `α` and `β`: the set whose frontier the
target is about. -/
def cReg (S : Set (EuclideanSpace ℝ (Fin 2))) (α β : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {p | cproj p ∈ S ∧ α (cproj p) < clast p ∧ clast p < β (cproj p)}

/-- The interior of the cylindrical region: the points of the open region lying over the interior
of `S`. -/
def cInt (S : Set (EuclideanSpace ℝ (Fin 2))) (α β : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {p | cproj p ∈ interior S ∧ α (cproj p) < clast p ∧ clast p < β (cproj p)}

/-- The upper half of the boundary of the cylinder `cCylBase`: `𝔻 × {1} ∪ ∂𝔻 × [0,1]`. -/
def cCylBaseTop : Set (EuclideanSpace ℝ (Fin 3)) :=
  {p | ‖cproj p‖ ≤ 1 ∧ clast p = 1}

end

end Work.Drive.Mono
