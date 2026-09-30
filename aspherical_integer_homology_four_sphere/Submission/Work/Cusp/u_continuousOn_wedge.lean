/-
# Continuity of the perimeter parameter `u` on the wedges

`u p = uPerim (bnd p)` is the perimeter parameter of the ray through `p`, i.e. the (normalised)
counterclockwise arclength coordinate of the direction `bnd p` on the boundary `∂Sq` of the filling
square.  As a function of `p` it is *not* continuous at the ray through the corner `(1,1)`: there
`u` jumps from values near `1` (approaching along the top edge) to values near `0` (approaching
along the right edge).  It is, however, continuous on each of the four open quadrants of directions

`wedge k = {p | 0 < nrm p ∧ u p ∈ (k/4, (k+1)/4)}`,

on which `u` is given by one of the four branches `(1 - q₁)/8`, `(3 - q₀)/8`, `(5 + q₁)/8`,
`(7 + q₀)/8` of `uPerim`, with `q = bnd p` (the branch is selected by the *open* quarter in which
`u p` lies, which is exactly what makes the wedge disjoint from the corner seams).

The proof never unfolds `uPerim` on the source side: it uses the round-trip identity
`bndOfU (u p) = bnd p` (`bndOfU_uPerim` with `nrm (bnd p) = 1`, `nrm_bnd`) together with the
explicit affine form of `bndOfU` on each quarter interval.  Solving that linear identity for `u p`
gives the branch formula, and the right-hand side is continuous on the wedge because
`bnd p = (nrm p)⁻¹ • p` is (`nrm p ≠ 0` there).
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.bndOfU_uPerim
import Submission.Work.Cusp.uPerim_mem
import Submission.Work.Cusp.nrm_continuous

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- The coordinate projection `p ↦ p i` of `E2 = ℝ²` is continuous. -/
private lemma continuous_coord (i : Fin 2) : Continuous (fun p : E2 => p i) :=
  (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ))

/-- Each coordinate of the radial projection `bnd p = (nrm p)⁻¹ • p` is continuous on every wedge,
where `nrm p ≠ 0`. -/
private lemma continuousOn_bnd_coord (k : Fin 4) (i : Fin 2) :
    ContinuousOn (fun p : E2 => (bnd p) i) (wedge k) := by
  have hne : ∀ p ∈ wedge k, nrm p ≠ 0 := fun p hp => ne_of_gt hp.1
  have hinv : ContinuousOn (fun p : E2 => (nrm p)⁻¹) (wedge k) :=
    nrm_continuous.continuousOn.inv₀ hne
  have hcoord : ContinuousOn (fun p : E2 => p i) (wedge k) := (continuous_coord i).continuousOn
  have hmul : ContinuousOn (fun p : E2 => (nrm p)⁻¹ * p i) (wedge k) := hinv.mul hcoord
  refine hmul.congr ?_
  intro p _
  simp [bnd, PiLp.smul_apply]

/-! ### The branch formula of `u` on each wedge -/

/-- On `{u p < 1/4}` (first quarter) the perimeter parameter is `u p = (1 - (bnd p)₁)/8`:
`bndOfU` is affine on `[0,1/4)` and inverts `uPerim` (`bndOfU_uPerim`). -/
private lemma u_eq_of_lt_quarter {p : E2} (hp : 0 < nrm p) (hu : u p < 1/4) :
    u p = (1 - (bnd p) 1) / 8 := by
  have hpne : p ≠ 0 := by intro h; rw [h] at hp; simp [nrm] at hp
  obtain ⟨hu0, hu1⟩ := uPerim_mem (q := bnd p) (nrm_bnd hpne)
  have hu0' : 0 ≤ u p := hu0
  have hu1' : u p < 1 := hu1
  have hbnd : bndOfU (u p) = bnd p := bndOfU_uPerim (nrm_bnd hpne)
  have hbndU : bndOfU (u p) = !₂[(1:ℝ), 1 - 8 * u p] := by
    unfold bndOfU
    rw [Int.fract_eq_self.mpr ⟨hu0', hu1'⟩]
    exact ite_eq_left hu
  have hbfun : bnd p = !₂[(1:ℝ), 1 - 8 * u p] := hbnd.symm.trans hbndU
  have h1 : (bnd p) 1 = 1 - 8 * u p := by rw [hbfun]; simp
  rw [h1]; ring

/-- On `{1/4 < u p ∧ u p < 1/2}` (second quarter) the perimeter parameter is
`u p = (3 - (bnd p)₀)/8`. -/
private lemma u_eq_of_lt_half {p : E2} (hp : 0 < nrm p) (hu0 : 1/4 < u p) (hu1 : u p < 1/2) :
    u p = (3 - (bnd p) 0) / 8 := by
  have hpne : p ≠ 0 := by intro h; rw [h] at hp; simp [nrm] at hp
  obtain ⟨ha, hb⟩ := uPerim_mem (q := bnd p) (nrm_bnd hpne)
  have ha' : 0 ≤ u p := ha
  have hb' : u p < 1 := hb
  have hbnd : bndOfU (u p) = bnd p := bndOfU_uPerim (nrm_bnd hpne)
  have hbndU : bndOfU (u p) = !₂[3 - 8 * u p, (-1:ℝ)] := by
    unfold bndOfU
    rw [Int.fract_eq_self.mpr ⟨ha', hb'⟩]
    rw [ite_eq_right (not_lt.mpr (le_of_lt hu0)), ite_eq_left hu1]
  have hbfun : bnd p = !₂[3 - 8 * u p, (-1:ℝ)] := hbnd.symm.trans hbndU
  have h1 : (bnd p) 0 = 3 - 8 * u p := by rw [hbfun]; simp
  rw [h1]; ring

/-- On `{1/2 < u p ∧ u p < 3/4}` (third quarter) the perimeter parameter is
`u p = (5 + (bnd p)₁)/8`. -/
private lemma u_eq_of_lt_threequarter {p : E2} (hp : 0 < nrm p) (hu0 : 1/2 < u p)
    (hu1 : u p < 3/4) : u p = (5 + (bnd p) 1) / 8 := by
  have hpne : p ≠ 0 := by intro h; rw [h] at hp; simp [nrm] at hp
  obtain ⟨ha, hb⟩ := uPerim_mem (q := bnd p) (nrm_bnd hpne)
  have ha' : 0 ≤ u p := ha
  have hb' : u p < 1 := hb
  have hbnd : bndOfU (u p) = bnd p := bndOfU_uPerim (nrm_bnd hpne)
  have hbndU : bndOfU (u p) = !₂[(-1:ℝ), 8 * u p - 5] := by
    unfold bndOfU
    rw [Int.fract_eq_self.mpr ⟨ha', hb'⟩]
    rw [ite_eq_right (not_lt.mpr (by linarith : (1:ℝ)/4 ≤ u p)),
        ite_eq_right (not_lt.mpr (le_of_lt hu0)), ite_eq_left hu1]
  have hbfun : bnd p = !₂[(-1:ℝ), 8 * u p - 5] := hbnd.symm.trans hbndU
  have h1 : (bnd p) 1 = 8 * u p - 5 := by rw [hbfun]; simp
  rw [h1]; ring

/-- On `{3/4 < u p}` (fourth quarter, up to the seam `u p = 1`) the perimeter parameter is
`u p = (7 + (bnd p)₀)/8`. -/
private lemma u_eq_of_lt_one {p : E2} (hp : 0 < nrm p) (hu0 : 3/4 < u p) :
    u p = (7 + (bnd p) 0) / 8 := by
  have hpne : p ≠ 0 := by intro h; rw [h] at hp; simp [nrm] at hp
  obtain ⟨ha, hb⟩ := uPerim_mem (q := bnd p) (nrm_bnd hpne)
  have ha' : 0 ≤ u p := ha
  have hb' : u p < 1 := hb
  have hbnd : bndOfU (u p) = bnd p := bndOfU_uPerim (nrm_bnd hpne)
  have hbndU : bndOfU (u p) = !₂[8 * u p - 7, (1:ℝ)] := by
    unfold bndOfU
    rw [Int.fract_eq_self.mpr ⟨ha', hb'⟩]
    rw [ite_eq_right (not_lt.mpr (by linarith : (1:ℝ)/4 ≤ u p)),
        ite_eq_right (not_lt.mpr (by linarith : (1:ℝ)/2 ≤ u p)),
        ite_eq_right (not_lt.mpr (le_of_lt hu0))]
  have hbfun : bnd p = !₂[8 * u p - 7, (1:ℝ)] := hbnd.symm.trans hbndU
  have h1 : (bnd p) 0 = 8 * u p - 7 := by rw [hbfun]; simp
  rw [h1]; ring

/-- On each of the four wedges `u` is one of the four continuous branches of `uPerim ∘ bnd`. -/
theorem u_continuousOn_wedge (k : Fin 4) : ContinuousOn u (wedge k) := by
  fin_cases k
  · have hcont : ContinuousOn (fun p : E2 => (1 - (bnd p) 1) / 8) (wedge (0 : Fin 4)) :=
      (((continuous_const : Continuous (fun _ : E2 => (1:ℝ))).continuousOn).sub
        (continuousOn_bnd_coord 0 1)).div_const 8
    refine hcont.congr ?_
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Set.mem_Ioo] at hp2
    exact u_eq_of_lt_quarter hp1 (by norm_num at hp2 ⊢; exact hp2.2)
  · have hcont : ContinuousOn (fun p : E2 => (3 - (bnd p) 0) / 8) (wedge (1 : Fin 4)) :=
      (((continuous_const : Continuous (fun _ : E2 => (3:ℝ))).continuousOn).sub
        (continuousOn_bnd_coord 1 0)).div_const 8
    refine hcont.congr ?_
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Set.mem_Ioo] at hp2
    exact u_eq_of_lt_half hp1 (by norm_num at hp2 ⊢; exact hp2.1)
      (by norm_num at hp2 ⊢; exact hp2.2)
  · have hcont : ContinuousOn (fun p : E2 => (5 + (bnd p) 1) / 8) (wedge (2 : Fin 4)) :=
      (((continuous_const : Continuous (fun _ : E2 => (5:ℝ))).continuousOn).add
        (continuousOn_bnd_coord 2 1)).div_const 8
    refine hcont.congr ?_
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Set.mem_Ioo] at hp2
    exact u_eq_of_lt_threequarter hp1 (by norm_num at hp2 ⊢; exact hp2.1)
      (by norm_num at hp2 ⊢; exact hp2.2)
  · have hcont : ContinuousOn (fun p : E2 => (7 + (bnd p) 0) / 8) (wedge (3 : Fin 4)) :=
      (((continuous_const : Continuous (fun _ : E2 => (7:ℝ))).continuousOn).add
        (continuousOn_bnd_coord 3 0)).div_const 8
    refine hcont.congr ?_
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Set.mem_Ioo] at hp2
    exact u_eq_of_lt_one hp1 (by norm_num at hp2 ⊢; exact hp2.1)

end Work.Cusp
