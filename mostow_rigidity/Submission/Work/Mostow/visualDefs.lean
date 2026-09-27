import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.Hyper

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

/-- The cone over a subset of `E n`: the union of the segments `[0,ξ]`, `ξ ∈ B`. -/
def cone {n : ℕ} (B : Set (E n)) : Set (E n) := Set.Ioo (0 : ℝ) 1 • B

/-- The unnormalised surface measure on the unit sphere of `E n`, pushed forward to `E n`. -/
def sphMeas (n : ℕ) : Measure (E n) :=
  (((volume : Measure (E n)).toSphere)).map Subtype.val

/-- The sheet-preserving Minkowski-orthogonal matrix representative of `g : PO n 1`. -/
def sMat {n : ℕ} (g : PO n 1) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  (tsign (rep g)) • mat (rep g)

/-- The lift `ξ ↦ (ξ,1)` of a point of `E n` to `ℝ^{n+1}`. -/
def hvec {n : ℕ} (ξ : E n) : Fin n ⊕ Fin 1 → ℝ := Sum.elim (fun i => ξ i) (fun _ => (1 : ℝ))

/-- The vector `sMat g *ᵥ (ξ,1)` in `ℝ^{n+1}` (the "homogeneous coordinates" of `bd g ξ`). -/
def wvec_visualDefs {n : ℕ} (g : PO n 1) (ξ : E n) : Fin n ⊕ Fin 1 → ℝ :=
  (sMat g).mulVec (hvec ξ)

/-- The denominator `d_ξ` of the boundary formula. -/
def dfun {n : ℕ} (g : PO n 1) (ξ : E n) : ℝ := wvec_visualDefs g ξ (Sum.inr 0)

/-- The explicit boundary formula `ξ ↦ (sMat g (ξ,1))_sp / d_ξ` (agrees with `bd g` on `Sph n`). -/
def phiFun {n : ℕ} (g : PO n 1) (ξ : E n) : E n :=
  WithLp.toLp 2 (fun i => wvec_visualDefs g ξ (Sum.inl i) / dfun g ξ)

/-- The degree-one homogeneous extension of `bd g` to `E n ∖ {0}`. -/
def homoExt {n : ℕ} (g : PO n 1) (x : E n) : E n :=
  ‖x‖ • phiFun g (‖x‖⁻¹ • x)

/-- The Poisson density of the visual measure seen from `u`, as a function of `ξ`. -/
def poissonDens (n : ℕ) (u : E n) (ξ : E n) : ℝ≥0∞ :=
  ENNReal.ofReal ((tpart u - inner ℝ u ξ) ^ (-(n : ℝ) + 1))


end

end Work.Mostow
