/-
# The polar chart of the filling piece, as an open partial homeomorphism

`ThetaPolar v : E2 × E2 → E4` is the inner (polar) chart of the `v`-th cusp
(`Work.Cusp.Basic`), `polarSource v k B` and `polarTarget v k B` (`Work.Cusp.Charts`) are the
source and the target of its `k`-th wedge on a chart box `B ⊆ polarBox`.  This file assembles them
into an `OpenPartialHomeomorph` whose underlying map is `ThetaPolar v` itself, refining the four
ingredients proved in the neighbouring modules:

* `ThetaPolar_continuousOn_wedge`: `ThetaPolar v` is continuous on each wedge;
* `cuspInvInner_ThetaPolar`: `cuspInvInner v` is a left inverse of `ThetaPolar v` (everywhere);
* `ThetaPolar_cuspInvInner`: it is a right inverse on `polarBox` at the points whose recovered
  perimeter coordinate `uqOf v q` lies in `[0,1)`;
* `cuspInvInner_continuousOn`: it is continuous where `1/4 < r`.

The two sources/targets are the `c = 0` instances of the shifted chart `ThetaPolarS v c`, and at
`c = 0` the lift `uS 0` is the perimeter parameter `u` itself (`ThetaPolarS_zero`), so that on the
source the shifted chart *is* `ThetaPolar v`; `wedgeS 0 k = wedge k` is the corresponding identity
of wedges.  The target is identified with the *open* condition
`{q | q ∈ B ∧ uqOf v q ∈ (k/4, (k+1)/4)}`, which is what makes it open: the `[0,1)`-membership in
the definition of `polarTargetS` is implied by the fractional-part condition because
`(k/4, (k+1)/4) ⊆ [0,1)` for `k : Fin 4`.

The map from the source to the target is onto because `cuspInvInner v q` is the preimage of `q`,
and the layer parameter of `cuspInvInner v q` is `> 1/24`: it is `> 1/4/r_J` in the inner branch
(`1/4 < q 0 ≤ r_J`) and `> 1/2` in the collar branch, and more directly `1/4 < radial` already
forces `1/24 < ‖p‖∞` because `radial = 2 r_J ‖p‖∞` in the inner region and `‖p‖∞ > 1/2` in the
collar.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.ThetaPolar_continuousOn_wedge
import Submission.Work.Cusp.ThetaPolar_injOn
import Submission.Work.Cusp.ThetaPolar_cuspInvInner
import Submission.Work.Cusp.cuspInvInner_ThetaPolar
import Submission.Work.Cusp.cuspInvInner_continuousOn
import Submission.Work.Cusp.cuspInvInner_uqOf
import Submission.Work.Cusp.ThetaPolarS_zero
import Submission.Work.Cusp.ThetaPolarS_cuspInvInner
import Submission.Work.Cusp.uS_continuousOn_wedgeS
import Submission.Work.Cusp.isOpen_wedge
import Submission.Work.Cusp.isOpen_wedgeS
import Submission.Work.Cusp.isOpen_nrm_gt
import Submission.Work.Cusp.nrm_continuous
import Submission.Work.Cusp.invY_wOf

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace
open Set

/-! ### The `c = 0` wedge

At `c = 0` the shifted lift `uS 0` of the perimeter parameter is the perimeter parameter itself,
so the shifted wedge is the unshifted one. -/

/-- **`wedgeS 0 k = wedge k`.**  The shifted wedge is
`{p | 0 < ‖p‖∞ ∧ fract (u p − c) ∈ (k/4, (k+1)/4)}`; for `c = 0` the perimeter parameter of a
nonzero point already lies in `[0,1)` (`u_mem_of_nrm_pos`), so its fractional part is itself. -/
theorem polarChart_wedgeS_zero (k : Fin 4) : wedgeS 0 k = wedge k := by
  ext p
  simp only [wedgeS, wedge, Set.mem_ofPred_eq, Set.mem_Ioo, sub_zero]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    rwa [Int.fract_eq_self.mpr (u_mem_of_nrm_pos h0)] at h1
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    rwa [Int.fract_eq_self.mpr (u_mem_of_nrm_pos h0)]

/-! ### The recovered perimeter coordinate `uqOf v` -/

/-- **`uqOf v` at a point of the polar chart is the perimeter parameter `u p`.**  `uqOf v q`
recovers `u` from the angle coordinate `q 1 = 2π u p + 2π⟪y,σ_v⟫/‖σ_v‖²` and from the `w`
coordinates `(q 2, q 3) = wOf v y` (inverted by `invY_wOf`); the phase correction cancels. -/
theorem polarChart_uqOf_ThetaPolar (v : Fin 5) (p y : E2) :
    uqOf v (ThetaPolar v p y) = u p := by
  have hy : invY v !₂[(ThetaPolar v p y) 2, (ThetaPolar v p y) 3] = y := by
    rw [show (!₂[(ThetaPolar v p y) 2, (ThetaPolar v p y) 3] : E2) = wOf v y from by
      ext i; fin_cases i <;> simp [ThetaPolar], invY_wOf]
  rw [uqOf, hy]
  rw [show (ThetaPolar v p y) 1
      = 2 * π * u p + 2 * π * (⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2) from by
    simp [ThetaPolar, thetaAng]]
  have hpi : (2 : ℝ) * π ≠ 0 := by positivity
  field_simp
  ring

/-- **`uqOf v` is continuous** (on all of `E4`): it is built from the linear map
`q ↦ (q 2, q 3) ↦ invY v` (whose matrix is the explicit inverse of `wOf v`), the skew torus
coordinate `cuspY v` and the inner product with the slope `σ_v`. -/
theorem polarChart_continuous_uqOf (v : Fin 5) : Continuous (uqOf v) := by
  unfold uqOf cuspY invY
  fun_prop

/-! ### Openness of the source and the target -/

/-- **The source of the polar chart is the set displayed in terms of `ThetaPolar v`**: on the
wedge the shifted chart `ThetaPolarS v 0` agrees with `ThetaPolar v` (`ThetaPolarS_zero`). -/
theorem polarChart_source_eq (v : Fin 5) (k : Fin 4) (B : Set E4) :
    polarSource v k B
      = {z : E2 × E2 | z.1 ∈ wedge k ∧ 1/24 < nrm z.1 ∧ ThetaPolar v z.1 z.2 ∈ B} := by
  ext z
  simp only [polarSource, polarSourceS, Set.mem_ofPred_eq]
  rw [polarChart_wedgeS_zero k]
  constructor
  · rintro ⟨hw, hn, hB⟩
    exact ⟨hw, hn, by rwa [ThetaPolarS_zero v z.1 z.2 hw.1] at hB⟩
  · rintro ⟨hw, hn, hB⟩
    exact ⟨hw, hn, by rwa [ThetaPolarS_zero v z.1 z.2 hw.1]⟩

/-- **The target of the polar chart is the open set `{q ∈ B | uqOf v q ∈ (k/4,(k+1)/4)}`.**
The defining conditions `uqOf v q ∈ [0,1)` and `fract (uqOf v q) ∈ (k/4,(k+1)/4)` of
`polarTargetS` are together equivalent to `uqOf v q ∈ (k/4,(k+1)/4)`, because
`(k/4,(k+1)/4) ⊆ [0,1)` for `k : Fin 4`. -/
theorem polarChart_target_eq (v : Fin 5) (k : Fin 4) (B : Set E4) :
    polarTarget v k B
      = {q : E4 | q ∈ B ∧ uqOf v q ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)} := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) / 4 := by positivity
  have hk1 : ((k : ℝ) + 1) / 4 ≤ 1 := by
    have hk3 : (k : ℝ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ k.isLt
    linarith
  ext q
  simp only [polarTarget, polarTargetS, Set.mem_ofPred_eq, sub_zero, Set.mem_Ico, Set.mem_Ioo]
  constructor
  · rintro ⟨hB, hu, hf⟩
    exact ⟨hB, by rwa [Int.fract_eq_self.mpr hu] at hf⟩
  · rintro ⟨hB, hf⟩
    have h0 : 0 ≤ uqOf v q := by linarith [hf.1]
    have h1 : uqOf v q < 1 := by linarith [hf.2]
    exact ⟨hB, ⟨h0, h1⟩, by rw [Int.fract_eq_self.mpr ⟨h0, h1⟩]; exact hf⟩

/-- **The source of the polar chart is open**: it is the intersection of the open wedge
(`isOpen_wedge`), the open superlevel set `1/24 < ‖p‖∞` (`isOpen_nrm_gt`) and the preimage of the
open set `B` under `ThetaPolar v`, which is continuous on the wedge. -/
theorem polarChart_isOpen_source (v : Fin 5) (k : Fin 4) (B : Set E4) (hB : IsOpen B) :
    IsOpen (polarSource v k B) := by
  rw [polarChart_source_eq]
  have hs1 : IsOpen {z : E2 × E2 | z.1 ∈ wedge k} := (isOpen_wedge k).preimage continuous_fst
  have hs2 : IsOpen {z : E2 × E2 | 1 / 24 < nrm z.1} :=
    isOpen_lt continuous_const (nrm_continuous.comp continuous_fst)
  have hs3 : IsOpen ({z : E2 × E2 | z.1 ∈ wedge k} ∩
      (fun z : E2 × E2 => ThetaPolar v z.1 z.2) ⁻¹' B) :=
    (ThetaPolar_continuousOn_wedge v k).isOpen_inter_preimage hs1 hB
  have hset : {z : E2 × E2 | z.1 ∈ wedge k ∧ 1 / 24 < nrm z.1 ∧ ThetaPolar v z.1 z.2 ∈ B}
      = ({z : E2 × E2 | z.1 ∈ wedge k} ∩ (fun z : E2 × E2 => ThetaPolar v z.1 z.2) ⁻¹' B)
        ∩ {z : E2 × E2 | 1 / 24 < nrm z.1} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
    tauto
  rw [hset]
  exact hs3.inter hs2

/-- **The target of the polar chart is open**, by `polarChart_target_eq`: `B` is open and
`uqOf v` is continuous (`polarChart_continuous_uqOf`). -/
theorem polarChart_isOpen_target (v : Fin 5) (k : Fin 4) (B : Set E4) (hB : IsOpen B) :
    IsOpen (polarTarget v k B) := by
  rw [polarChart_target_eq]
  have h1 : IsOpen {q : E4 | uqOf v q ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)} :=
    isOpen_Ioo.preimage (polarChart_continuous_uqOf v)
  have hset : {q : E4 | q ∈ B ∧ uqOf v q ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)}
      = B ∩ {q : E4 | uqOf v q ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)} := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [hset]
  exact hB.inter h1

/-- **`1/24 < ‖p‖∞` from `1/4 < radial v p y`.**  In the inner region `radial = 2 r_J ‖p‖∞ = 6‖p‖∞`,
so `radial > 1/4` gives `‖p‖∞ > 1/24`; in the collar `‖p‖∞ > 1/2 > 1/24`. -/
theorem polarChart_nrm_of_radial (v : Fin 5) (p y : E2) (h : 1 / 4 < radial v p y) :
    1 / 24 < nrm p := by
  rw [radial] at h
  split_ifs at h with hc
  · rw [rJ] at h; linarith
  · linarith [not_le.mp hc]

/-! ### The chart -/

/-- **The polar chart is an open partial homeomorphism of the `(p,y)`-cover onto the polar box.**
Its source is `polarSource v k B` and its target `polarTarget v k B`, and its underlying map is
`ThetaPolar v`.  The forward map is `ThetaPolar v` (continuous on the wedge, and the source lies in
the wedge), the inverse is the explicit `cuspInvInner v` (continuous where `1/4 < r`, which holds
on `B ⊆ polarBox`), and the two round trips are `cuspInvInner_ThetaPolar` (left, everywhere) and
`ThetaPolar_cuspInvInner` (right, on `polarBox` with `uqOf v q ∈ [0,1)`, which holds on the
target). -/
theorem exists_polarChart (v : Fin 5) (k : Fin 4) (B : Set E4) (hB : IsOpen B)
    (hBs : B ⊆ polarBox) :
    ∃ Φ : OpenPartialHomeomorph (E2 × E2) E4,
      Φ.source = polarSource v k B ∧ Φ.target = polarTarget v k B ∧
        ∀ z, Φ z = ThetaPolar v z.1 z.2 := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) / 4 := by positivity
  have hk1 : ((k : ℝ) + 1) / 4 ≤ 1 := by
    have hk3 : (k : ℝ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ k.isLt
    linarith
  have hS := polarChart_source_eq v k B
  have hT := polarChart_target_eq v k B
  have huqT := polarChart_uqOf_ThetaPolar v
  have hnrm := polarChart_nrm_of_radial v
  refine ⟨{ toFun := fun z : E2 × E2 => ThetaPolar v z.1 z.2
            invFun := cuspInvInner v
            source := polarSource v k B
            target := polarTarget v k B
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            continuousOn_toFun := ?_
            continuousOn_invFun := ?_
            open_source := ?_
            open_target := ?_ }, rfl, rfl, fun z => rfl⟩
  · -- `map_source'`
    intro z hz
    rw [hS] at hz
    rw [hT]
    exact ⟨hz.2.2, by rw [huqT z.1 z.2]; exact hz.1.2⟩
  · -- `map_target'`
    intro q hq
    rw [hT] at hq
    obtain ⟨hqB, hqIoo⟩ := hq
    rw [hS]
    have hbox : q ∈ polarBox := hBs hqB
    have hq0 : 0 ≤ uqOf v q := by linarith [hqIoo.1, hk0]
    have hq1 : uqOf v q < 1 := by linarith [hqIoo.2, hk1]
    have hTP : ThetaPolar v (cuspInvInner v q).1 (cuspInvInner v q).2 = q :=
      ThetaPolar_cuspInvInner v q hbox ⟨hq0, hq1⟩
    have hrad : radial v (cuspInvInner v q).1 (cuspInvInner v q).2 = q 0 := by
      have h := congrArg (fun w : E4 => w 0) hTP
      simpa [ThetaPolar] using h
    have hgt : 1 / 24 < nrm (cuspInvInner v q).1 :=
      hnrm (cuspInvInner v q).1 (cuspInvInner v q).2 (by rw [hrad]; exact hbox.1)
    refine ⟨?_, hgt, ?_⟩
    · rw [wedge, Set.mem_ofPred_eq, Set.mem_Ioo]
      exact ⟨lt_trans (by norm_num) hgt, by
        rw [cuspInvInner_uqOf v q hbox, Int.fract_eq_self.mpr ⟨hq0, hq1⟩]
        exact hqIoo⟩
    · rw [hTP]; exact hqB
  · -- `left_inv'`
    rintro ⟨p, y⟩ _
    exact cuspInvInner_ThetaPolar v p y
  · -- `right_inv'`
    intro q hq
    rw [hT] at hq
    exact ThetaPolar_cuspInvInner v q (hBs hq.1)
      ⟨by linarith [hq.2.1, hk0], by linarith [hq.2.2, hk1]⟩
  · -- `continuousOn_toFun`
    refine (ThetaPolar_continuousOn_wedge v k).mono ?_
    intro z hz
    rw [hS] at hz
    exact hz.1
  · -- `continuousOn_invFun`
    refine (cuspInvInner_continuousOn v).mono ?_
    intro q hq
    rw [hT] at hq
    exact (hBs hq.1).1
  · -- `open_source`
    exact polarChart_isOpen_source v k B hB
  · -- `open_target`
    exact polarChart_isOpen_target v k B hB

end Work.Cusp
