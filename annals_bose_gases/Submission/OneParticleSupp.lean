import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.OneParticleDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Support of the one-particle trial state: `oneParticle L` lives strictly inside
the open cube `openCube L := {y | ∀ m, 0 < y m < L}`.

Definitions (see `Submission.OneParticleDefs`):
  unitCentre : ℝ³          -- the point with all coordinates 1/2
  unitBumpData             -- ContDiffBump unitCentre with rIn = 1/8, rOut = 1/4
  unitBump x := unitBumpData x
  oneCoeff L := (Real.sqrt (L ^ 3 * unitNorm))⁻¹
  oneParticle L x := oneCoeff L * unitBump (L⁻¹ • x)

Mathlib facts at your disposal:
  ContDiffBump.tsupport_eq : tsupport ↑f = closedBall c f.rOut
  PiLp.norm_apply_le x m : ‖x m‖ ≤ ‖x‖     (coordinate bound in PiLp spaces)
  PiLp.toLp_apply / PiLp.ofLp : coordinate access
  Real.norm_eq_abs

Proof strategy:
1. `tsupport unitBump = closedBall unitCentre (1/4)` (`ContDiffBump.tsupport_eq`).
2. Show `closedBall unitCentre (1/4) ⊆ openCube 1`: if `‖y - unitCentre‖ ≤ 1/4`
   then for each coordinate `m`, `|y m - 1/2| ≤ ‖y - unitCentre‖ ≤ 1/4`, so
   `1/4 ≤ y m ≤ 3/4` and in particular `0 < y m < 1`.
3. Multiplying by the constant `oneCoeff L` and composing with the continuous
   scaling map `S x := L⁻¹ • x` only shrink the support, hence
   `tsupport (oneParticle L) ⊆ S⁻¹ (closedBall unitCentre (1/4))`:
   the preimage of the closed ball under the continuous `S` is closed and
   contains the plain support of `oneParticle L`.
4. `S⁻¹ (closedBall unitCentre (1/4)) ⊆ openCube L` for `0 < L`:
   by step 2 `∀ m, 0 < (S x) m < 1`, i.e. `0 < L⁻¹ * x m < 1`; multiply by
   `L > 0` to get `0 < x m < L`.
-/

namespace Submission

set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Topological support of the unit bump: the closed ball of radius `1/4`
about the unit centre. -/
lemma tsupport_unitBump_eq :
    tsupport unitBump = closedBall (unitCentre : ℝ³) (1 / 4) := by
  change tsupport (↑unitBumpData : ℝ³ → ℝ) = closedBall (unitCentre : ℝ³) (1 / 4)
  rw [ContDiffBump.tsupport_eq unitBumpData]
  norm_num [unitBumpData]

/-- The closed ball of radius `1/4` about the unit centre lies strictly inside
the open unit cube: each coordinate is within `1/4` of `1/2`. -/
lemma closedBall_unitCentre_subset_openCube :
    closedBall (unitCentre : ℝ³) (1 / 4) ⊆ openCube 1 := by
  intro y hy m
  have hdist : ‖y - unitCentre‖ ≤ 1 / 4 := by
    have h := Metric.mem_closedBall.mp hy
    simpa [dist_eq_norm] using h
  have hb := PiLp.norm_apply_le (y - unitCentre) m
  have hb' : |y m - (1 / 2 : ℝ)| ≤ ‖y - unitCentre‖ := by
    simpa [unitCentre, PiLp.toLp_apply] using hb
  have hle : |y m - (1 / 2 : ℝ)| ≤ 1 / 4 := le_trans hb' hdist
  constructor
  · have hlo := (abs_le.mp hle).1
    nlinarith
  · have hhi := (abs_le.mp hle).2
    nlinarith

/-- If the scaled point `L⁻¹ • x` lies in the open unit cube then `x` lies in
the open cube of side `L` (coordinatewise `0 < L⁻¹ * x m < 1` multiplied by
`0 < L`). -/
lemma smul_openCube_subset {L : ℝ} (hL : 0 < L) {x : ℝ³}
    (hx : L⁻¹ • x ∈ openCube 1) : x ∈ openCube L := by
  intro m
  have hm : (L⁻¹ • x) m ∈ Set.Ioo (0 : ℝ) 1 := hx m
  have hlo : 0 < L⁻¹ * x m := by simpa using (Set.mem_Ioo.mp hm).1
  have hhi : L⁻¹ * x m < 1 := by simpa using (Set.mem_Ioo.mp hm).2
  have hmm : L * (L⁻¹ * x m) = x m := by
    rw [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
  constructor
  · have hp : 0 < L * (L⁻¹ * x m) := mul_pos hL hlo
    rwa [hmm] at hp
  · have hlt : L * (L⁻¹ * x m) < L * 1 := mul_lt_mul_of_pos_left hhi hL
    rwa [hmm, mul_one] at hlt

/-- The normalised scaled bump is supported strictly inside the open cube. -/
lemma tsupport_oneParticle_subset_openCube {L : ℝ} (hL : 0 < L) :
    tsupport (oneParticle L) ⊆ openCube L := by
  -- The plain support of `oneParticle L` is contained in the preimage under
  -- `S x = L⁻¹ • x` of the closed ball of radius 1/4 about the unit centre.
  have hsupp : Function.support (oneParticle L) ⊆
      (fun x : ℝ³ => L⁻¹ • x) ⁻¹' (closedBall (unitCentre : ℝ³) (1 / 4)) := by
    intro x hx
    have hg : unitBump (L⁻¹ • x) ≠ 0 := by
      change oneCoeff L * unitBump (L⁻¹ • x) ≠ 0 at hx
      intro hz
      apply hx
      rw [hz, mul_zero]
    have htsx : L⁻¹ • x ∈ closedBall (unitCentre : ℝ³) (1 / 4) := by
      rw [← tsupport_unitBump_eq]
      exact subset_tsupport unitBump hg
    exact htsx
  -- The preimage is closed (closed ball under the continuous scaling map), so
  -- the topological support (= closure of the support) is contained in it.
  have hcl : tsupport (oneParticle L) ⊆
      (fun x : ℝ³ => L⁻¹ • x) ⁻¹' (closedBall (unitCentre : ℝ³) (1 / 4)) := by
    change closure (Function.support (oneParticle L)) ⊆
      (fun x : ℝ³ => L⁻¹ • x) ⁻¹' (closedBall (unitCentre : ℝ³) (1 / 4))
    exact closure_minimal hsupp
      (Metric.isClosed_closedBall.preimage (continuous_const_smul (L⁻¹ : ℝ)))
  intro x hx
  -- Inside the closed ball the scaled coordinates satisfy `0 < (L⁻¹ • x) m < 1`;
  -- scaling back by `L > 0` gives `0 < x m < L`.
  exact smul_openCube_subset hL
    (closedBall_unitCentre_subset_openCube (hcl hx))

end BoseGases

end Submission
