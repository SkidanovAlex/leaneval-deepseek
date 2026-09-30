import Mathlib

set_option synthInstance.maxHeartbeats 400000

/-!
# The model of `Sⁿ` used for Step I of the sphere-specific route

Step I of `CONTRACTS.md` §F computes `H_*(ΩSⁿ; ℚ)`.  The computation is carried out in the
**one-point compactification**

  `SphModel n = OnePoint (EuclideanSpace ℝ (Fin n))`,

which is homeomorphic to `Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1` (Mathlib's
`onePointEquivSphereOfFinrankEq`, packaged in route A as `Work.Stems.onePointSphereHomeo`), and in
which the two pieces of the standard decomposition of the sphere are *explicit*:

* `sphLoopCube n` — the **closed cube** `{v | ∀ i, |v i| ≤ 1}` (the "inner" disc, `D'` in
  `CONTRACTS.md` §F1);
* `sphLoopOut n` — its complement, i.e. the closed disc around the base point `∞` (the "outer"
  disc, `D`).

The two sets cover the model and meet exactly in the boundary of the cube, which is the sphere
`S^{n-1}`; the pair `(sphLoopCube, its boundary)` is *affinely* isomorphic to the cube pair
`((Fin n → I), Cube.boundary (Fin n))` for which the relative Künneth isomorphism
`Work.StemsB.cubePair_iso` is available.

The base point of the path–loop fibration used throughout is `∞ = OnePoint.infty`.

## What is here

Definitions only (each is a `def`, so this module is axiom-free and instant); the geometric
lemmas (`sphLoopCube_union_sphLoopOut`, `sphLoopCube_inter_sphLoopOut`,
`isClosed_sphLoopCube`, `isOpen_sphLoopOut`, the contraction of `sphLoopCube` and the *based*
contraction of `sphLoopOut` to `∞`) and the rest of the computation are described in
`CONTRACTS.md` §H, which records the exact statements to prove.

The contraction of `sphLoopOut` is the content of the reviewed statement
`Work.StemsB.onePoint_radialPush`; the contraction of the cube is `Work.StemsB.cube_contract`.
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

/-- **The model of `Sⁿ`** used for Step I: the one-point compactification of `ℝⁿ` (so that the
"north pole" is the extra point `∞` and the pieces of the standard decomposition are explicit). -/
abbrev SphModel (n : ℕ) : Type := OnePoint (EuclideanSpace ℝ (Fin n))

/-- The **closed cube** `{v | ∀ i, |v i| ≤ 1}` inside `SphModel n` — the "inner disc" `D'` of the
decomposition, whose boundary meets the outer disc.  (This is the cube of the *sup*-norm, not of
the Euclidean norm; it is exactly the image of `Fin n → I` under an affine map.) -/
def sphLoopCube (n : ℕ) : Set (SphModel n) :=
  {x | ∃ v : EuclideanSpace ℝ (Fin n), x = ↑v ∧ ∀ i, |v i| ≤ 1}

/-- The **complement of the open cube**, i.e. the closed disc `D` around the base point `∞`:
the point `∞` together with the vectors having some coordinate of absolute value `≥ 1`. -/
def sphLoopOut (n : ℕ) : Set (SphModel n) :=
  {x | x = OnePoint.infty ∨
    ∃ v : EuclideanSpace ℝ (Fin n), x = ↑v ∧ ∃ i, 1 ≤ |v i|}

/-- The **common boundary** of the two discs: the vectors with some coordinate of absolute value
`1` (the sphere `S^{n-1}`). -/
def sphLoopBdry (n : ℕ) : Set (SphModel n) :=
  {x | ∃ v : EuclideanSpace ℝ (Fin n), x = ↑v ∧ (∀ i, |v i| ≤ 1) ∧ ∃ i, |v i| = 1}

/-- The **outer thickening** `U = {∞} ∪ {v | 1/2 < ‖v‖}` of the outer disc `sphLoopOut n`.  It is
open, contractible (radially to `∞`), contains `sphLoopOut n`, and **avoids the origin**; the latter
is why the compression of §H4 is continuous on `U` (and the retraction of `(T3)` is stated there),
while it is discontinuous at the origin of the model. -/
def sphLoopThick (n : ℕ) : Set (SphModel n) :=
  {x | x = OnePoint.infty ∨
    ∃ v : EuclideanSpace ℝ (Fin n), x = ↑v ∧ (1 / 2 : ℝ) < ‖v‖}

/-- The interior of the cube (the open cube). -/
def sphLoopCubeOpen (n : ℕ) : Set (SphModel n) :=
  {x | ∃ v : EuclideanSpace ℝ (Fin n), x = ↑v ∧ ∀ i, |v i| < 1}

/-! ## The elementary set-theoretic facts of the decomposition -/

theorem sphLoopCube_eq_image (n : ℕ) :
    sphLoopCube n =
      (OnePoint.some : EuclideanSpace ℝ (Fin n) → SphModel n) '' {v | ∀ i, |v i| ≤ 1} := by
  ext x
  constructor
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, rfl, hv⟩

theorem sphLoopCubeOpen_eq_image (n : ℕ) :
    sphLoopCubeOpen n =
      (OnePoint.some : EuclideanSpace ℝ (Fin n) → SphModel n) '' {v | ∀ i, |v i| < 1} := by
  ext x
  constructor
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, rfl, hv⟩

/-- The two discs cover the model. -/
theorem sphLoopCube_union_sphLoopOut (n : ℕ) : sphLoopCube n ∪ sphLoopOut n = Set.univ := by
  ext x
  constructor
  · intro _; exact Set.mem_univ x
  · intro _
    rcases x with _ | v
    · exact Or.inr (Or.inl rfl)
    · by_cases h : ∀ i, |v i| ≤ 1
      · exact Or.inl ⟨v, rfl, h⟩
      · push Not at h
        obtain ⟨i, hi⟩ := h
        exact Or.inr (Or.inr ⟨v, rfl, i, le_of_lt hi⟩)

/-- The two discs meet exactly in the boundary of the cube. -/
theorem sphLoopCube_inter_sphLoopOut (n : ℕ) :
    sphLoopCube n ∩ sphLoopOut n = sphLoopBdry n := by
  ext x
  constructor
  · rintro ⟨⟨v, rfl, hv⟩, hout⟩
    rcases hout with h | ⟨w, hw, i, hi⟩
    · exact absurd h (by simp)
    · have hwv : w = v := by simpa using hw.symm
      rw [hwv] at hi
      exact ⟨v, rfl, hv, i, le_antisymm (hv i) hi⟩
  · rintro ⟨v, rfl, hv, i, hi⟩
    exact ⟨⟨v, rfl, hv⟩, Or.inr ⟨v, rfl, i, le_of_eq hi.symm⟩⟩

/-- The open cube is open in the model. -/
theorem isOpen_sphLoopCubeOpen (n : ℕ) : IsOpen (sphLoopCubeOpen n) := by
  rw [sphLoopCubeOpen_eq_image, OnePoint.isOpen_image_coe]
  have hset : {v : EuclideanSpace ℝ (Fin n) | ∀ i, |v i| < 1}
      = ⋂ i : Fin n, {v : EuclideanSpace ℝ (Fin n) | |v i| < 1} := by ext v; simp
  rw [hset]
  refine isOpen_iInter_of_finite fun i => ?_
  have hcont : Continuous fun v : EuclideanSpace ℝ (Fin n) => |v i| := by fun_prop
  exact isOpen_Iio.preimage hcont

/-- The outer disc is exactly the complement of the open cube. -/
theorem sphLoopOut_eq_compl_cubeOpen (n : ℕ) : sphLoopOut n = (sphLoopCubeOpen n)ᶜ := by
  ext x
  constructor
  · rintro (rfl | ⟨v, rfl, i, hi⟩)
    · intro h
      obtain ⟨w, hw, _⟩ := h
      exact absurd hw (by simp)
    · intro h
      obtain ⟨w, hw, hw'⟩ := h
      have hwv : w = v := by simpa using hw.symm
      rw [hwv] at hw'
      exact absurd (hw' i) (not_lt.mpr hi)
  · intro h
    rcases x with _ | v
    · exact Or.inl rfl
    · by_cases hv : ∀ i, |v i| < 1
      · exact absurd ⟨v, rfl, hv⟩ h
      · push Not at hv
        obtain ⟨i, hi⟩ := hv
        exact Or.inr ⟨v, rfl, i, hi⟩

/-- The outer disc is closed in the model. -/
theorem isClosed_sphLoopOut (n : ℕ) : IsClosed (sphLoopOut n) := by
  rw [sphLoopOut_eq_compl_cubeOpen]
  exact (isOpen_sphLoopCubeOpen n).isClosed_compl

end

end Work.StemsB
