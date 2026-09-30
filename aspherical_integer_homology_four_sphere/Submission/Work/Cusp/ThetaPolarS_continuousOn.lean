/-
# Continuity of the `c`-shifted polar chart `ThetaPolarS` on the shifted wedges

`ThetaPolarS v c` (`Charts.lean`) is the polar chart of the `v`-th cusp with the angle coordinate
read off the *lift* `uS c p = c + Int.fract (u p - c)` of the perimeter parameter instead of the
perimeter parameter `u p` itself.  The point of the shift is exactly continuity: while `u` jumps by
`1` on the ray through the corner `(1,1)` of the square, the lift `uS c` is continuous on each
`c`-shifted wedge `wedgeS c k`, and the jump of `u` does not disturb the *radial* coordinate either,
because `σ_v ∈ Λ_v ⊂ ℤ³` is a period of the ceiling `β` and `u p - uS c p = ⌊u p - c⌋` is an integer.

Here we prove the standing regularity fact for the polar chart: `ThetaPolarS v c z.1 z.2` is
continuous on `{z | z.1 ∈ wedgeS c k}` (no restriction on the phase variable `z.2`).  The proof is
componentwise:

* the radial coordinate: on `{‖p‖∞ ≤ 1/2}` it is `2 r_J ‖p‖∞`, on `{‖p‖∞ ≥ 1/2}` it is
  `R₀ − log (collarHeight ‖p‖∞ (β (uS c p • σ_v + y₂λ₂ + y₃λ₃)))`; the two branches agree at
  `‖p‖∞ = 1/2` (`collarHeight_half`), and the second one is written with the continuous lift `uS c`
  (`beta_cuspX_eq`);
* the angle coordinate: `2π·uS c p + 2π⟪y₂λ₂ + y₃λ₃, σ_v⟫/‖σ_v‖²` (`ThetaPolarS_uScont`);
* the two `w`-coordinates: `⟪y₂λ₂ + y₃λ₃, frame2 v⟫`, `⟪y₂λ₂ + y₃λ₃, frame3 v⟫`, linear in `y`.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.ThetaPolarS_uScont
import Submission.Work.Cusp.beta_continuous
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_lattice_periodic
import Submission.Work.Cusp.collarHeight_half
import Submission.Work.Cusp.collarHeight_pos
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

/-! ### The slope lies in the cusp lattice -/

/-- Every generator `κ_{v,i}` of the cusp lattice `Λ_v` lies in `Λ_v`. -/
lemma kv_mem_lattice (v : Fin 5) (i : Fin 3) : kv v i ∈ lattice v :=
  AddSubgroup.subset_closure ⟨i, rfl⟩

/-- **The slope `σ_v` lies in the cusp lattice `Λ_v`**: `σ_v = κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}`
is an integer (`slopeB v`, `slopeC v`) combination of the lattice generators.  In particular `σ_v`
is a period of the ceiling `β` (`beta_lattice_periodic`). -/
theorem slope_mem_lattice (v : Fin 5) : slope v ∈ lattice v := by
  have h0 : kv v 0 ∈ lattice v := kv_mem_lattice v 0
  have h1 : kv v 1 ∈ lattice v := kv_mem_lattice v 1
  have h2 : kv v 2 ∈ lattice v := kv_mem_lattice v 2
  have h1' : (slopeB v : ℝ) • kv v 1 ∈ lattice v := by
    rw [Int.cast_smul_eq_zsmul ℝ (slopeB v) (kv v 1)]
    exact AddSubgroup.zsmul_mem (lattice v) h1 (slopeB v)
  have h2' : (slopeC v : ℝ) • kv v 2 ∈ lattice v := by
    rw [Int.cast_smul_eq_zsmul ℝ (slopeC v) (kv v 2)]
    exact AddSubgroup.zsmul_mem (lattice v) h2 (slopeC v)
  rw [slope]
  exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _ h0 h1') h2'

/-! ### The lift `uS c` differs from `u` by an integer -/

/-- `uS c p` is `u p` shifted by the integer `⌊u p − c⌋`. -/
lemma uS_sub_floor (c : ℝ) (p : E2) : uS c p = u p - (⌊u p - c⌋ : ℝ) := by
  rw [uS, ← Int.self_sub_floor]
  ring

/-- **The ceiling along the `σ_v`-direction is unchanged when `u p` is replaced by the lift
`uS c p`.**  This is what lets the polar chart be written with the continuous lift `uS c` even
though `u` itself jumps (by `1`) on the corner ray through `(1,1)`: the jump is an integer multiple
of `σ_v ∈ ℤ³`, hence a period of `β`. -/
theorem beta_cuspX_eq (v : Fin 5) (c : ℝ) (p y : E2) :
    beta (cuspX v (u p) y) = beta (uS c p • slope v + cuspY v y) := by
  have hm : u p = uS c p + ((⌊u p - c⌋ : ℤ) : ℝ) := by
    rw [uS_sub_floor]; ring
  have hx : u p • slope v + cuspY v y
      = (uS c p • slope v + cuspY v y) + (⌊u p - c⌋ : ℤ) • slope v := by
    have h1 : u p • slope v = uS c p • slope v + ((⌊u p - c⌋ : ℤ) : ℝ) • slope v := by
      conv_lhs => rw [hm]
      rw [add_smul]
    rw [h1, Int.cast_smul_eq_zsmul ℝ (⌊u p - c⌋) (slope v)]
    abel
  rw [cuspX, hx]
  exact beta_lattice_periodic v (uS c p • slope v + cuspY v y) ((⌊u p - c⌋ : ℤ) • slope v)
    (AddSubgroup.zsmul_mem (lattice v) (slope_mem_lattice v) _)

/-! ### Continuity of the ingredient maps -/

/-- The coordinate projection `y ↦ y i` of `E2 = ℝ²` is continuous. -/
lemma continuous_coord_E2 (i : Fin 2) : Continuous (fun y : E2 => y i) :=
  (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ))

/-- The `y`-part `cuspY v y = y 0 • λ₂ + y 1 • λ₃` of the cusp coordinate is continuous in `y`. -/
lemma continuous_cuspY (v : Fin 5) : Continuous (fun y : E2 => cuspY v y) := by
  have h : Continuous (fun y : E2 => y 0 • lam2 v + y 1 • lam3 v) :=
    ((continuous_coord_E2 0).smul continuous_const).add
      ((continuous_coord_E2 1).smul continuous_const)
  simpa [cuspY] using h

/-! ### The main theorem -/

theorem ThetaPolarS_continuousOn (v : Fin 5) (c : ℝ) (k : Fin 4) :
    ContinuousOn (fun z : E2 × E2 => ThetaPolarS v c z.1 z.2) {z | z.1 ∈ wedgeS c k} := by
  set s : Set (E2 × E2) := {z | z.1 ∈ wedgeS c k} with hs
  -- the projection to the layer/direction variable
  have hpr : ContinuousOn (fun z : E2 × E2 => z.1) s :=
    (ContinuousOn.fst continuous_id.continuousOn).mono (Set.subset_univ s)
  have hnrm : ContinuousOn (fun z : E2 × E2 => nrm z.1) s :=
    nrm_continuous.comp_continuousOn hpr
  -- the lift `uS c ∘ fst` is continuous on the wedge
  have hU : ContinuousOn (fun z : E2 × E2 => uS c z.1) s :=
    (ThetaPolarS_uScont c k).comp hpr (fun z hz => hz)
  -- the phase map
  have hYc : Continuous (fun z : E2 × E2 => cuspY v z.2) :=
    (continuous_cuspY v).comp continuous_snd
  have hY : ContinuousOn (fun z : E2 × E2 => cuspY v z.2) s := hYc.continuousOn
  -- the argument of the ceiling
  have hargS : ContinuousOn (fun z : E2 × E2 => uS c z.1 • slope v + cuspY v z.2) s :=
    (hU.smul continuousOn_const).add hY
  have hbetaS : ContinuousOn (fun z : E2 × E2 => beta (uS c z.1 • slope v + cuspY v z.2)) s :=
    beta_continuous.comp_continuousOn hargS
  -- the collar height written with the lift `uS c`
  have hlogS : ContinuousOn
      (fun z : E2 × E2 => Real.log (beta (uS c z.1 • slope v + cuspY v z.2))) s :=
    hbetaS.log (fun z _ => ne_of_gt (beta_pos _))
  have hA : ContinuousOn (fun z : E2 × E2 => 2 * nrm z.1 - 1) s :=
    (hnrm.const_mul 2).sub continuousOn_const
  have hAB : ContinuousOn
      (fun z : E2 × E2 => (2 * nrm z.1 - 1) * Real.log (beta (uS c z.1 • slope v + cuspY v z.2))) s :=
    hA.mul hlogS
  have hC : ContinuousOn (fun z : E2 × E2 => 2 - 2 * nrm z.1) s :=
    continuousOn_const.sub (hnrm.const_mul 2)
  have hCD : ContinuousOn (fun z : E2 × E2 => (2 - 2 * nrm z.1) * Real.log sJ) s :=
    hC.mul continuousOn_const
  have hCHS : ContinuousOn
      (fun z : E2 × E2 => collarHeight (nrm z.1) (beta (uS c z.1 • slope v + cuspY v z.2))) s := by
    unfold collarHeight
    exact Real.continuous_exp.comp_continuousOn (hAB.add hCD)
  have hlogCHS : ContinuousOn
      (fun z : E2 × E2 => Real.log (collarHeight (nrm z.1) (beta (uS c z.1 • slope v + cuspY v z.2)))) s :=
    hCHS.log (fun z _ => ne_of_gt (collarHeight_pos _ _ (beta_pos _)))
  -- the radial coordinate as a piecewise function with the substituted collar height
  have hfront : ∀ a ∈ s ∩ frontier {z : E2 × E2 | nrm z.1 ≤ 1 / 2},
      (2 * rJ * nrm a.1) = R0 - Real.log (collarHeight (nrm a.1)
        (beta (uS c a.1 • slope v + cuspY v a.2))) := by
    intro a ha
    have h1 : nrm a.1 = 1 / 2 :=
      frontier_le_subset_eq (nrm_continuous.comp continuous_fst) continuous_const ha.2
    rw [h1, collarHeight_half, sJ, Real.log_exp, R0, rJ]
    norm_num
  have hrad' : ContinuousOn (fun z : E2 × E2 => if nrm z.1 ≤ 1 / 2 then 2 * rJ * nrm z.1
      else R0 - Real.log (collarHeight (nrm z.1)
        (beta (uS c z.1 • slope v + cuspY v z.2)))) s :=
    ContinuousOn.if hfront
      (((continuous_const.mul (nrm_continuous.comp continuous_fst)) :
        Continuous (fun z : E2 × E2 => 2 * rJ * nrm z.1)).continuousOn.mono Set.inter_subset_left)
      (((continuousOn_const (c := R0)).sub hlogCHS).mono Set.inter_subset_left)
  have hrad : ContinuousOn (fun z : E2 × E2 => radial v z.1 z.2) s := by
    refine hrad'.congr ?_
    intro z hz
    simp only [radial]
    by_cases h : nrm z.1 ≤ 1 / 2
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, collarS, beta_cuspX_eq]
  -- the angle coordinate
  have hinnerSL : Continuous (fun z : E2 × E2 => inner ℝ (cuspY v z.2) (slope v)) :=
    continuous_inner.comp (hYc.prodMk continuous_const)
  have hth : ContinuousOn (fun z : E2 × E2 =>
      2 * π * uS c z.1 + 2 * π * inner ℝ (cuspY v z.2) (slope v) / ‖slope v‖ ^ 2) s :=
    (hU.const_mul (2 * π)).add (((continuous_const.mul hinnerSL).div_const _).continuousOn)
  -- the two `w`-coordinates
  have hw0 : ContinuousOn (fun z : E2 × E2 => inner ℝ (cuspY v z.2) (frame2 v)) s :=
    (continuous_inner.comp (hYc.prodMk continuous_const)).continuousOn
  have hw1 : ContinuousOn (fun z : E2 × E2 => inner ℝ (cuspY v z.2) (frame3 v)) s :=
    (continuous_inner.comp (hYc.prodMk continuous_const)).continuousOn
  -- assembly
  have hpi : ContinuousOn (fun z : E2 × E2 => fun i : Fin 4 => ThetaPolarS v c z.1 z.2 i) s := by
    rw [continuousOn_pi]
    intro i
    fin_cases i
    · simpa [ThetaPolarS] using hrad
    · simpa [ThetaPolarS] using hth
    · simpa [ThetaPolarS, wOf] using hw0
    · simpa [ThetaPolarS, wOf] using hw1
  have htoLp : ContinuousOn
      (fun z : E2 × E2 => WithLp.toLp 2 (fun i : Fin 4 => ThetaPolarS v c z.1 z.2 i)) s :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp_continuousOn hpi
  refine htoLp.congr ?_
  intro z _
  exact (WithLp.toLp_ofLp 2 (ThetaPolarS v c z.1 z.2)).symm

end Work.Cusp
