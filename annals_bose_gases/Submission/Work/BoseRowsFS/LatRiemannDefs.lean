import Mathlib.Analysis.InnerProductSpace.PiL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.LatRiemannDefs` — the scaled lattice `h·ℤ³` and its cells

Vocabulary for the lattice-vs-continuum comparison
(`Submission/Work/BoseRowsFS/lattice_riemann_core.lean`):

* `zvec m = (m 0, m 1, m 2) : ℝ³` — the unit lattice point of `m : ℤ³`;
* `latPt h m = h • zvec m` — the scaled lattice `h·ℤ³`;
* `cell h m = ∏ᵢ [h mᵢ − h/2, h mᵢ + h/2]` — the cell of side `h` around `latPt h m`.

The corpus's box momenta are exactly this lattice with `h = 2π/ℓ`:
`Work.BoseBoxFock.kmomLab ℓ N n = latPt (2π/ℓ) (labVec N n)` (up to the coercion
`ZMod.valMinAbs`), and the box's kernel `W₁` is cut at `‖·‖ < 2·uvRad ℓ N`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowsFS

/-- The unit lattice point `(m 0, m 1, m 2) : ℝ³` of `m : ℤ³`. -/
def zvec (m : Fin 3 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ))

/-- The scaled lattice point `h·m ∈ ℝ³`. -/
def latPt (h : ℝ) (m : Fin 3 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i : Fin 3 => h * (m i : ℝ))

/-- The cell of side `h` centred at `latPt h m`. -/
def cell (h : ℝ) (m : Fin 3 → ℤ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {p | ∀ i : Fin 3, |p i - h * (m i : ℝ)| ≤ h / 2}

lemma zvec_smul (h : ℝ) (m : Fin 3 → ℤ) : latPt h m = h • zvec m := by
  ext i
  simp [latPt, zvec]

lemma norm_zvec_nonneg (m : Fin 3 → ℤ) : 0 ≤ ‖zvec m‖ := norm_nonneg _

end Work.BoseRowsFS
