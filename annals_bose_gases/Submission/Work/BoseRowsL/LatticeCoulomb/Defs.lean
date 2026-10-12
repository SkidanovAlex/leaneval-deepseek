import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseRowsL.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.Defs` — the lattice Coulomb comparison, normalised

This module fixes the vocabulary of the *lattice Coulomb approximation*
(`Work.BoseRowsL.LatticeCoulomb.latticeCoulomb_approx`) and of the normalised
`ℓ = 1` kernel bound it reduces to.

## The reduction in one line

With `chat W k = ∫_y W y · cos⟪k,y⟫ dy`, `vec n = 2π·(n as a real vector)` and
`k_n = ℓ⁻¹ • vec n = (2π/ℓ)·(n as a real vector)`, the substitution
`p = (2π/ℓ) • q` in the `p`-integral together with the product-to-sum formula
`cos a cos b = (cos(a+b) + cos(a−b))/2` turns the target's two sides into

  * LHS `= Σ_{n∈S} ℓ²/(8π²) · cos(2π⟪n,z₊⟫)/⟪…⟫`-type terms,
  * RHS `= ℓ²/(8π²) · ∫_{‖q‖≤R} cos(2π⟪q,z⟫)/‖q‖² dq`

with `R = Kℓ/(2π)`, `z = (x±y)/ℓ`, and `‖z‖ ≤ 1/2` because
`supp h ⊆ closedBall 0 (ℓ/2)` (`h = f₁ ∗ f₂`, `supp fᵢ ⊆ closedBall 0 r`,
`4r ≤ ℓ`).  Hence the target follows from the **normalised kernel bound**
`Work.BoseRowsL.LatticeCoulomb.latticeKernel_bound` below, which is stated with
`ℓ = 1` and *no* `chat`, as a statement about the unit lattice `ℤ³` and the unit
ball.

## Why the bound is uniform in the truncation

`Ω_R(z) = Σ_{0<‖n‖≤R} cos(2π⟪n,z⟫)/‖n‖² − ∫_{‖q‖≤R} cos(2π⟪q,z⟫)/‖q‖² dq`
is a *matched* cutoff comparison: both sides are cut at the same radius, so the
`≈ 4πR` growth of the sum and of the integral cancel.  Numerically
`Ω_R(z) ∈ [−9.6, −5.0]` for every `R ∈ [1,120]` and every tested
`‖z‖ ≤ 1/2` (see `FINDING_latticeKernel.md`), in particular it is bounded far
from both `0` and `∞`.
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The integer lattice point `n` as a real vector (so that
`Work.BoseB4.vec n = (2*π) • nvec n`). -/
noncomputable def nvec (n : Fin 3 → ℤ) : E3 := WithLp.toLp 2 (fun i : Fin 3 => (n i : ℝ))

@[simp] lemma nvec_apply (n : Fin 3 → ℤ) (i : Fin 3) : (nvec n).ofLp i = (n i : ℝ) := rfl

lemma nvec_zero : nvec (0 : Fin 3 → ℤ) = 0 := by
  ext i; simp [nvec]

/-- `Work.BoseB4.vec n = (2π) • nvec n`. -/
lemma vec_eq_smul_nvec (n : Fin 3 → ℤ) :
    Work.BoseB4.vec n = (2 * Real.pi) • nvec n := by
  ext i
  simp only [Work.BoseB4.vec, nvec, PiLp.toLp_apply, WithLp.ofLp_smul]
  rfl

lemma norm_vec_eq (n : Fin 3 → ℤ) : ‖Work.BoseB4.vec n‖ = 2 * Real.pi * ‖nvec n‖ := by
  rw [vec_eq_smul_nvec, norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]

lemma norm_eq_zero_iff (n : Fin 3 → ℤ) : ‖nvec n‖ = 0 ↔ n = 0 := by
  constructor
  · intro h
    funext i
    have h2 : (nvec n).ofLp i = 0 := by
      have := norm_eq_zero.mp h
      rw [this]; simp
    simpa [nvec_apply] using h2
  · intro h
    rw [h, nvec_zero, norm_zero]

/-- The unit cube (of side `1`) centred at the lattice point `n`. -/
def ucell (n : Fin 3 → ℤ) : Set E3 := {q | ∀ i : Fin 3, |(q.ofLp i) - (n i : ℝ)| ≤ 1 / 2}

lemma ucell_eq_preimage (n : Fin 3 → ℤ) :
    ucell n = WithLp.ofLp ⁻¹' (Set.pi Set.univ
      (fun i : Fin 3 => Set.Icc ((n i : ℝ) - 1 / 2) ((n i : ℝ) + 1 / 2))) := by
  ext q
  simp only [ucell, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    true_implies, Set.mem_Icc]
  constructor
  · intro h i
    have h' := abs_le.mp (h i)
    constructor <;> linarith [h'.1, h'.2]
  · intro h i
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [h i]

lemma ucell_measurableSet (n : Fin 3 → ℤ) : MeasurableSet (ucell n) := by
  rw [ucell_eq_preimage]
  refine MeasurableSet.preimage ?_ (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).measurable
  exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)

/-- The unit cube has volume `1`. -/
lemma volume_ucell (n : Fin 3 → ℤ) : volume (ucell n) = 1 := by
  have hs : MeasurableSet (Set.pi Set.univ
      (fun i : Fin 3 => Set.Icc ((n i : ℝ) - 1 / 2) ((n i : ℝ) + 1 / 2))) :=
    MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)
  have hmp := PiLp.volume_preserving_ofLp (Fin 3)
  rw [ucell_eq_preimage, ← MeasureTheory.Measure.map_apply hmp.measurable hs,
    hmp.map_eq, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  simp only [Real.volume_Icc]
  rw [Finset.prod_congr rfl (fun i _ => by
    rw [show ((n i : ℝ) + 1 / 2) - ((n i : ℝ) - 1 / 2) = 1 by ring, ENNReal.ofReal_one])]
  simp

/-- The cosine of `2π⟪n,z⟫`, the summand of the lattice side. -/
noncomputable def latCos (n : Fin 3 → ℤ) (z : E3) : ℝ := Real.cos (2 * Real.pi * inner ℝ (nvec n) z)

end Work.BoseRowsL.LatticeCoulomb
