import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.rayPiece_eq_image
import Submission.Work.Top.Jordan
import Submission.Work.Top.isPreconnected_gt_potential

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The equipotential level curve lies in the unbounded side of a ray polygon

Let `ps` be a list of co-landing pairs of rays of the dynamical plane and `1 < R`.  The
boundary `Work.EL.polyCurve ps R` of the associated ray polygon consists of

* the ray pieces `rayPiece hN P.a 0 R`, `rayPiece hN P.b 0 R` and the landing points `P.y`, and
* the equipotential arcs at level `R` through the *near* arcs,

all of which lie in the sublevel set `{pot ≤ log R}`.  Consequently the whole superlevel set
`{pot > log R}` is a preconnected, unbounded subset of the complement of `polyCurve`, hence is
contained in the unbounded side `O` of the Jordan curve `polyCurve` (`Work.Top.JordanForm`).

The level set `{pot = log R}` is contained in the closure of `{pot > log R}`: every point of the
level `R` is the limit of the points of the same ray at levels slightly above `R`, obtained by
scaling the Böttcher coordinate outward.  Hence the part of the level set off the curve lies in
`closure O = O ∪ polyCurve`, and since it avoids `polyCurve` it lies in `O`.

This is the statement `Work.ELTop.level_eq_subset_sidesO`.
-/

open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

variable {c : ℂ} {φ : ℂ → ℂ}

/-- The boundary of a ray polygon is contained in the sublevel set `{pot ≤ log R}`: the ray
pieces stay at level `≤ log R`, the landing points lie in the filled Julia set (where the
potential vanishes), and the equipotential part is at level exactly `log R`. -/
theorem polyCurve_subset_pot_le (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
    {R : ℝ} (hR : 1 < R) :
    Work.EL.polyCurve ps R ⊆ {z : ℂ | Work.EL.pot hN z ≤ Real.log R} := by
  intro z hz
  change Work.EL.pot hN z ≤ Real.log R
  simp only [Work.EL.polyCurve, Set.mem_ofPred_eq] at hz
  rcases hz with ⟨P, _hP, hyz⟩ | ⟨θ, _hθ, _hne, rfl⟩
  · rcases hyz with rfl | hzr | hzr
    · rw [Work.EL.pot_of_mem hN (landsN_mem_K hN P.lands_a)]
      exact le_of_lt (Real.log_pos hR)
    · exact ((mem_rayPiece_iff hN P.a 0 R z).mp hzr).2.2
    · exact ((mem_rayPiece_iff hN P.b 0 R z).mp hzr).2.2
  · rw [Work.EL.pot_rayPt hN hR]

/-- A point of the level `log R` of the potential is the limit of points of larger potential:
scale its Böttcher coordinate radially outward. -/
theorem mem_closure_gt_pot (hN : Work.EL.DynB c φ) {R : ℝ} (hR : 1 < R) {z : ℂ}
    (hz : Work.EL.pot hN z = Real.log R) :
    z ∈ closure {w : ℂ | Real.log R < Work.EL.pot hN w} := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hznotK : z ∉ Work.EL.K c := by
    intro h
    rw [Work.EL.pot_of_mem hN h] at hz
    exact (ne_of_lt (Real.log_pos hR)) hz
  set W : ℂ := ((hN.e ⟨z, hznotK⟩ : Work.Top.exteriorDisc) : ℂ) with hWdef
  have hPhi_norm : ‖Work.EL.dynPhi c φ z‖ = R := by
    have h := Work.EL.pot_of_notMem hN hznotK
    rw [hz] at h
    have hpos : (0 : ℝ) < ‖Work.EL.dynPhi c φ z‖ :=
      lt_trans zero_lt_one (hN.Phi_mem_exteriorDisc hznotK)
    have h2 := congrArg Real.exp h
    rw [Real.exp_log hRpos, Real.exp_log hpos] at h2
    exact h2.symm
  have hWnorm : ‖W‖ = R := by
    rw [hWdef, ← hN.he ⟨z, hznotK⟩]
    exact hPhi_norm
  have hW1 : 1 < ‖W‖ := by rw [hWnorm]; exact hR
  let s : ℕ → ℝ := fun n => R + 1 / ((n : ℝ) + 1)
  have hsR : ∀ n, R < s n := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    change R < R + 1 / ((n : ℝ) + 1)
    linarith
  have hs1 : ∀ n, 1 < s n := fun n => lt_trans hR (hsR n)
  let Wn : ℕ → ℂ := fun n => (s n / R) • W
  have hWn_norm : ∀ n, ‖Wn n‖ = s n := by
    intro n
    change ‖(s n / R) • W‖ = s n
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (lt_trans zero_lt_one (hs1 n)) hRpos),
      hWnorm, div_mul_cancel₀ _ (ne_of_gt hRpos)]
  have hWn_mem : ∀ n, Wn n ∈ Work.Top.exteriorDisc := by
    intro n
    rw [Work.Top.mem_exteriorDisc, hWn_norm n]
    exact hs1 n
  let P : ℕ → ↥(Work.EL.K c)ᶜ := fun n => hN.e.symm ⟨Wn n, hWn_mem n⟩
  have hdyn : ∀ n, Work.EL.dynPhi c φ (P n : ℂ) = Wn n := by
    intro n
    rw [hN.he (P n)]
    have h1 : hN.e (P n) = ⟨Wn n, hWn_mem n⟩ := by
      change hN.e (hN.e.symm ⟨Wn n, hWn_mem n⟩) = ⟨Wn n, hWn_mem n⟩
      exact Homeomorph.apply_symm_apply hN.e _
    rw [h1]
  have hpotP : ∀ n, Work.EL.pot hN (P n : ℂ) = Real.log (s n) := by
    intro n
    rw [Work.EL.pot_of_notMem hN (P n).2, hdyn n, hWn_norm n]
  have hmem : ∀ n, (P n : ℂ) ∈ {w : ℂ | Real.log R < Work.EL.pot hN w} := by
    intro n
    rw [Set.mem_ofPred_eq, hpotP n]
    exact Real.log_lt_log hRpos (hsR n)
  have hWn_tendsto : Tendsto Wn atTop (𝓝 W) := by
    have hs_t : Tendsto s atTop (𝓝 R) := by
      have h1 : Tendsto (fun n : ℕ => R + 1 / ((n : ℝ) + 1)) atTop (𝓝 (R + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      change Tendsto (fun n : ℕ => R + 1 / ((n : ℝ) + 1)) atTop (𝓝 R)
      simpa using h1
    have hdiv : Tendsto (fun n => s n / R) atTop (𝓝 (R / R)) := hs_t.div_const R
    have hsl : Tendsto (fun n => (s n / R) • W) atTop (𝓝 ((R / R) • W)) := hdiv.smul_const W
    have hRR : (R / R) • W = W := by rw [div_self (ne_of_gt hRpos), one_smul]
    rw [hRR] at hsl
    exact hsl
  have hWn_sub : Tendsto (fun n => (⟨Wn n, hWn_mem n⟩ : Work.Top.exteriorDisc)) atTop
      (𝓝 (⟨W, hW1⟩ : Work.Top.exteriorDisc)) := by
    rw [tendsto_subtype_rng]
    simpa using hWn_tendsto
  have hE : hN.e ⟨z, hznotK⟩ = (⟨W, hW1⟩ : Work.Top.exteriorDisc) :=
    Subtype.ext hWdef.symm
  have hEsymm : hN.e.symm (⟨W, hW1⟩ : Work.Top.exteriorDisc) = ⟨z, hznotK⟩ := by
    rw [← hE, Homeomorph.symm_apply_apply]
  have hP_sub : Tendsto P atTop (𝓝 (⟨z, hznotK⟩ : ↥(Work.EL.K c)ᶜ)) := by
    have h := (hN.e.symm.continuous.tendsto (⟨W, hW1⟩ : Work.Top.exteriorDisc)).comp hWn_sub
    rw [hEsymm] at h
    exact h
  have hP_tendsto : Tendsto (fun n => (P n : ℂ)) atTop (𝓝 z) := by
    have h := (continuous_subtype_val (p := fun w : ℂ => w ∈ (Work.EL.K c)ᶜ)).tendsto
      (⟨z, hznotK⟩ : ↥(Work.EL.K c)ᶜ) |>.comp hP_sub
    exact h
  exact mem_closure_of_tendsto hP_tendsto (Filter.Eventually.of_forall hmem)

/-- The unbounded side of a Jordan curve has closure `O ∪ C`. -/
theorem closure_sides_O_eq (hJ : Work.Top.JordanForm) (C : Set ℂ)
    (hC : Work.Top.IsJordanCurve C) :
    closure (hJ.sides C hC).O = (hJ.sides C hC).O ∪ C := by
  set S := hJ.sides C hC with hS
  rw [closure_eq_self_union_frontier, S.frontier_O]

theorem level_eq_subset_sidesO {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) {R : ℝ} (hR : 1 < R)
    (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) :
    {z : ℂ | Work.EL.pot hN z = Real.log R} ∩ (Work.EL.polyCurve ps R)ᶜ ⊆
      (hJ.sides (Work.EL.polyCurve ps R) hC).O := by
  intro z hz
  obtain ⟨hzpot, hzC⟩ := hz
  set S := hJ.sides (Work.EL.polyCurve ps R) hC with hS
  have hsub : {w : ℂ | Real.log R < Work.EL.pot hN w} ⊆ S.O := by
    refine S.subset_O_of_unbounded ?_ ?_ ?_
    · exact Work.Top.isPreconnected_gt_potential hN hR
    · intro w hw
      rw [Set.mem_compl_iff]
      intro hwC
      have hle : Work.EL.pot hN w ≤ Real.log R := polyCurve_subset_pot_le hN ps hR hwC
      exact (not_le.mpr hw) hle
    · intro n
      obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.mp
        (Work.EL.isCompact_le_pot hN (Real.log R)).isBounded
      refine ⟨((max D (n : ℝ) + 1 : ℝ) : ℂ), ?_, ?_⟩
      · show Real.log R < Work.EL.pot hN (((max D (n : ℝ) + 1 : ℝ)) : ℂ)
        by_contra hcon
        have hle : Work.EL.pot hN (((max D (n : ℝ) + 1 : ℝ)) : ℂ) ≤ Real.log R :=
          not_lt.mp hcon
        have hcontra : ‖(((max D (n : ℝ) + 1 : ℝ)) : ℂ)‖ ≤ D := hD _ hle
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < max D (n : ℝ) + 1)] at hcontra
        linarith [le_max_left D (n : ℝ)]
      · rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < max D (n : ℝ) + 1)]
        linarith [le_max_right D (n : ℝ)]
  have hzcl : z ∈ closure S.O :=
    closure_mono hsub (mem_closure_gt_pot hN hR hzpot)
  have hcl : closure S.O = S.O ∪ Work.EL.polyCurve ps R := by
    rw [hS]; exact closure_sides_O_eq hJ (Work.EL.polyCurve ps R) hC
  rw [hcl] at hzcl
  rcases hzcl with h | h
  · exact h
  · exact absurd h hzC

end Work.ELTop
