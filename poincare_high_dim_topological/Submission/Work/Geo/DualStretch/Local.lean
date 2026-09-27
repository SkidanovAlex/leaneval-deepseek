/-
A6 `Geo/DualStretch` — the *local* (single face) version of the stretch.

For a single face `σ` (a finite affinely independent set of points) we define the barycentric
coordinates `rcoord σ x`, the local masses `lmass`, the local low/high parts `lAOf`, `lBOf`,
`lSOf` and the local stretch `lstretch`.  On `PL.simp σ` these agree with the global objects of
`Defs.lean`; the point of the local version is that it is `ContinuousOn (PL.simp σ)`.
-/
import Submission.Work.Geo.DualStretch.Defs

open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

open PL (E Cx closedCube openCube)

variable {n : ℕ}

/-- Barycentric coordinate of `x` with respect to the fixed face `σ`;
zero off `PL.simp σ` and off `σ`. -/
noncomputable def rcoord (σ : Finset (E n)) (x : E n) (v : E n) : ℝ :=
  if _ : x ∈ PL.simp σ then
    (if _ : v ∈ σ then
      (if h : ∃ μ : E n → ℝ, (∀ w ∈ σ, 0 ≤ μ w) ∧
          (∑ w ∈ σ, μ w = 1) ∧ (∑ w ∈ σ, μ w • w = x) then h.choose else 0) v
    else 0)
  else 0

/-- The local mass of the level set `τ ⊆ σ`. -/
noncomputable def lmass (σ : Finset (E n)) (x : E n) (τ : Finset (E n)) : ℝ :=
  massOf σ (rcoord σ x) τ

/-- The local low part. -/
noncomputable def lAOf (β : ℝ) (p : ℕ) (σ : Finset (E n)) (x : E n) : E n :=
  ∑ τ ∈ σ.powerset, if LowFace β p τ then lmass σ x τ • bary τ else 0

/-- The local high part. -/
noncomputable def lBOf (β : ℝ) (p : ℕ) (σ : Finset (E n)) (x : E n) : E n :=
  ∑ τ ∈ σ.powerset, if LowFace β p τ then 0 else lmass σ x τ • bary τ

/-- The local total high mass. -/
noncomputable def lSOf (β : ℝ) (p : ℕ) (σ : Finset (E n)) (x : E n) : ℝ :=
  ∑ τ ∈ σ.powerset, if LowFace β p τ then 0 else lmass σ x τ

/-- The local stretch. -/
noncomputable def lstretch (β : ℝ) (p : ℕ) (M : ℝ) (σ : Finset (E n)) (x : E n) : E n :=
  (1 + (M - 1) * lSOf β p σ x)⁻¹ • (lAOf β p σ x + M • lBOf β p σ x)

end Work.Geo.DualStretch
