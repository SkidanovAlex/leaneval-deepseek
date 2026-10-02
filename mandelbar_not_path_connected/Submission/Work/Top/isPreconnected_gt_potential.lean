import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The superlevel sets of the potential are preconnected

For the endgame of the mandelbar non-path-connectivity theorem one needs to know that the
region `{c | log R < potential c}` inside a given equipotential is connected.  Under the abstract
Nakane interface (`Work.Top.NakaneData`) the Böttcher coordinate `Φ` is a homeomorphism from the
complement of `Mb` onto the exterior disc `{w | 1 < ‖w‖}`, and the potential is `log ‖Φ c‖` off
`Mb` (and `0` on `Mb`).  Since `R > 1` the level `log R` is positive, so the superlevel set misses
`Mb` entirely and, through `Φ`, is the exterior `{w | R < ‖w‖}` of the disc of radius `R`.  That
exterior is path connected (it is the continuous image of the punctured plane under the radial
expansion `w ↦ (‖w‖ + R)/‖w‖ • w`), hence preconnected, and preconnectedness pulls back along the
continuous surjection `Φ`.

* `isPathConnected_norm_gt` : the exterior of a disc of radius `R ≥ 0` is path connected;
* `isPreconnected_gt_potential` : the superlevel set `{log R < potential}` is preconnected.
-/

namespace Work.Top

open Classical Filter Set
open scoped Topology

/-- The exterior of the closed disc of radius `R ≥ 0` in the plane is path connected.  It is the
image of the punctured plane under the radial expansion `w ↦ (‖w‖ + R)/‖w‖ • w`. -/
theorem isPathConnected_norm_gt {R : ℝ} (hR : 0 ≤ R) :
    IsPathConnected {w : ℂ | R < ‖w‖} := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have hP : IsPathConnected ({w : ℂ | 0 < ‖w‖} : Set ℂ) := by
    have heq : ({w : ℂ | 0 < ‖w‖} : Set ℂ) = {0}ᶜ := by
      ext w; simp [norm_pos_iff]
    rw [heq]
    exact isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  let f : ℂ → ℂ := fun w => ((‖w‖ + R) / ‖w‖ : ℝ) • w
  have hcont : ContinuousOn f {w : ℂ | 0 < ‖w‖} := by
    have hnum : ContinuousOn (fun w : ℂ => (‖w‖ + R) / ‖w‖) {w : ℂ | 0 < ‖w‖} :=
      (continuous_norm.add continuous_const).continuousOn.div continuous_norm.continuousOn
        (fun w hw => ne_of_gt hw)
    exact hnum.smul continuous_id.continuousOn
  have himg : f '' {w : ℂ | 0 < ‖w‖} = {w : ℂ | R < ‖w‖} := by
    refine Subset.antisymm ?_ ?_
    · rintro u ⟨w, hw, rfl⟩
      simp only [Set.mem_ofPred_eq]
      have hwpos : 0 < ‖w‖ := hw
      have hcoef : 0 < (‖w‖ + R) / ‖w‖ := div_pos (by linarith) hwpos
      change R < ‖((‖w‖ + R) / ‖w‖ : ℝ) • w‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcoef, div_mul_cancel₀ _ (ne_of_gt hwpos)]
      linarith
    · intro u hu
      have hu' : R < ‖u‖ := hu
      have hupos : 0 < ‖u‖ := lt_of_le_of_lt hR hu'
      have hneR : ‖u‖ - R ≠ 0 := ne_of_gt (by linarith)
      have hneU : ‖u‖ ≠ 0 := ne_of_gt hupos
      refine ⟨((‖u‖ - R) / ‖u‖ : ℝ) • u, ?_, ?_⟩
      · change 0 < ‖((‖u‖ - R) / ‖u‖ : ℝ) • u‖
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by linarith) hupos),
          div_mul_cancel₀ _ hneU]
        linarith
      · change ((‖(((‖u‖ - R)/‖u‖ : ℝ) • u)‖ + R) / ‖(((‖u‖-R)/‖u‖ : ℝ) • u)‖ : ℝ) •
            (((‖u‖-R)/‖u‖ : ℝ) • u) = u
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by linarith) hupos),
          div_mul_cancel₀ _ hneU, smul_smul]
        have h1 : (‖u‖ - R + R) / (‖u‖ - R) * ((‖u‖ - R) / ‖u‖) = 1 := by
          field_simp
          ring
        rw [h1, one_smul]
  rw [← himg]
  exact hP.image' hcont

/-- **The superlevel set of the potential is preconnected.**  For `R > 1` the set
`{c | log R < potential Mb Φ c}` is, via Nakane's Böttcher coordinate, the exterior of the disc of
radius `R`, hence preconnected. -/
theorem isPreconnected_gt_potential {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) {R : ℝ}
    (hR : 1 < R) : IsPreconnected {c : ℂ | Real.log R < Work.Top.potential Mb Φ c} := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  -- the superlevel set is exactly `{c ∉ Mb | R < ‖Φ c‖}`
  have hchar : ∀ c : ℂ, Real.log R < potential Mb Φ c ↔ c ∉ Mb ∧ R < ‖Φ c‖ := by
    intro c
    constructor
    · intro h
      have hc : c ∉ Mb := by
        intro hcm
        rw [potential_of_mem hcm] at h
        exact absurd h (not_lt.mpr (Real.log_pos hR).le)
      refine ⟨hc, ?_⟩
      rw [potential_of_not_mem hc] at h
      exact (Real.log_lt_log_iff hRpos (norm_pos_iff.mpr (hN.Phi_ne_zero hc))).mp h
    · rintro ⟨hc, h⟩
      rw [potential_of_not_mem hc]
      exact (Real.log_lt_log_iff hRpos (norm_pos_iff.mpr (hN.Phi_ne_zero hc))).mpr h
  set S : Set ℂ := {c : ℂ | Real.log R < potential Mb Φ c} with hSdef
  set T : Set ℂ := {w : ℂ | R < ‖w‖} with hTdef
  have hTsub : T ⊆ exteriorDisc := by
    intro w hw
    rw [hTdef] at hw
    rw [mem_exteriorDisc]
    exact lt_trans hR hw
  -- the exterior of the disc of radius `R` is preconnected
  have hTpre : IsPreconnected T :=
    (isPathConnected_norm_gt (le_of_lt hRpos)).isConnected.isPreconnected
  have hpreT : PreconnectedSpace ↥T := isPreconnected_iff_preconnectedSpace.mp hTpre
  -- the Böttcher coordinate, read as a map on `{R < ‖w‖}`, is a continuous surjection onto the
  -- superlevel set
  let g : ↥T → ℂ := fun w => ((hN.e.symm (⟨(w : ℂ), hTsub w.2⟩ : ↥exteriorDisc) : ↥Mbᶜ) : ℂ)
  have hgc : Continuous g := by
    have hincl : Continuous fun w : ↥T => (⟨(w : ℂ), hTsub w.2⟩ : ↥exteriorDisc) :=
      continuous_subtype_val.subtype_mk _
    exact continuous_subtype_val.comp (hN.e.symm.continuous.comp hincl)
  have hrange : Set.range g = S := by
    rw [hSdef]
    ext c
    constructor
    · rintro ⟨w, rfl⟩
      have hc : g w ∉ Mb :=
        (hN.e.symm (⟨(w : ℂ), hTsub w.2⟩ : ↥exteriorDisc) : ↥Mbᶜ).2
      have hPhi : Φ (g w) = (w : ℂ) := by
        rw [hN.he ⟨g w, hc⟩]
        have hx : (⟨g w, hc⟩ : ↥Mbᶜ) =
            hN.e.symm (⟨(w : ℂ), hTsub w.2⟩ : ↥exteriorDisc) := by
          apply Subtype.ext; rfl
        rw [hx, Homeomorph.apply_symm_apply]
      show Real.log R < potential Mb Φ (g w)
      rw [potential_of_not_mem hc, hPhi]
      exact (Real.log_lt_log_iff hRpos (lt_trans hRpos w.2)).mpr w.2
    · intro hc
      have hcMb : c ∉ Mb := (hchar c).mp hc |>.1
      have hRc : R < ‖Φ c‖ := (hchar c).mp hc |>.2
      refine ⟨⟨Φ c, hRc⟩, ?_⟩
      have hx : hN.e ⟨c, hcMb⟩ = (⟨(Φ c : ℂ), hTsub hRc⟩ : ↥exteriorDisc) := by
        apply Subtype.ext
        exact (hN.he ⟨c, hcMb⟩).symm
      show ((hN.e.symm (⟨(Φ c : ℂ), hTsub hRc⟩ : ↥exteriorDisc) : ↥Mbᶜ) : ℂ) = c
      rw [← hx, Homeomorph.symm_apply_apply]
  have hpre : IsPreconnected (Set.range g) := isPreconnected_range hgc
  rw [hrange] at hpre
  exact hpre

end Work.Top
