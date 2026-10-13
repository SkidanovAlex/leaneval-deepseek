/-
# `Work.FTS.LocData.SmoothChain` — the `C^∞`-calculus of the localisation chapter

The localised data of the route live in `SmoothQuad` (genuine `C^∞` on the open quadrant
`z > -1`, `0 < θ < π/2`), **not** in `Work.Spaces.SmoothNbhd`: in this Mathlib
`ContDiffOn ℝ ⊤` is *analyticity*, and a compactly supported analytic function vanishes
identically (`Work.Stability.ZcutSmoothCompact`), so every membership statement phrased with
`SmoothNbhd` is either vacuous or false for the cut-off `χ(z/L)`.  `SmoothQuad` uses the genuine
smooth order `Work.Stability.smoothOrder = ((⊤ : ℕ∞) : ℕ∞ω)`.

This module provides the calculus that the rest of the chapter runs on:

* `Work.Spaces.pz`, `Work.Spaces.pth`, `DzIter`, `DthIter`, `mixed` preserve `C^∞`-smoothness on
  an open set (`contDiffOn_pz`, … , `contDiffOn_mixed`);
* the same for `SmoothQuad` (`SmoothQuad.DzIter`, `SmoothQuad.mixed`, …);
* `SmoothQuad` is closed under `+`, `-`, `*`, constant multiples (`smoothQuad_add`, …);
* the slices of a `SmoothQuad` function are `C^∞` on `Ioi (-1)` resp. `Ioo 0 (π/2)`
  (`contDiffOn_slice_z`, `contDiffOn_slice_θ`), hence the iterated `D`-derivatives are
  differentiable at every point of the open quadrant (`SmoothQuad.differentiableAt_slice_mixed`),
  which is what the Leibniz rules of `Leibniz.lean` and the additivity rules of `HkApi.lean` need;
* the `ℋ^k`-integrand of a `SmoothQuad` function is continuous on the open quadrant
  (`continuousOn_HkIntegrand_smoothQuad`), the measurability input of `HkMem_of_majorant`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-- The open quadrant `(0,∞) × (0,π/2)`, on which the `ℋ^k`-weights are continuous. -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem isOpen_quadU : IsOpen Work.Spaces.quadU := Work.Spaces.isOpen_quadU

/-! ## `D_z` and `D_θ` preserve `C^∞`-smoothness -/

/-- `Work.Spaces.pz` preserves `C^∞`-smoothness on an open set.  (The `⊤`-statement is
`Work.Spaces.contDiffOn_uncurry_pz`; this is the genuine smooth order.) -/
theorem contDiffOn_pz {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv ((h.differentiableOn (n := Work.Stability.smoothOrder)
      (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := Work.Stability.smoothOrder) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `Work.Spaces.pth` preserves `C^∞`-smoothness on an open set, with the genuine smooth order. -/
theorem contDiffOn_pth {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv ((h.differentiableOn (n := Work.Stability.smoothOrder)
      (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := Work.Stability.smoothOrder) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `Work.Spaces.Dz` preserves `C^∞`-smoothness on an open set. -/
theorem contDiffOn_Dz {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dz G)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact contDiffOn_fst.mul (contDiffOn_pz hV h)

/-- `Work.Spaces.Dth` preserves `C^∞`-smoothness on an open set. -/
theorem contDiffOn_Dth {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dth G)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  exact hsin.mul (contDiffOn_pth hV h)

/-- `D_z^i` preserves `C^∞`-smoothness on an open set. -/
theorem contDiffOn_DzIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) (i : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.DzIter i G)) V := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ]
      exact contDiffOn_Dz hV ih

/-- `D_θ^i` preserves `C^∞`-smoothness on an open set. -/
theorem contDiffOn_DthIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) (i : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.DthIter i G)) V := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ]
      exact contDiffOn_Dth hV ih

/-- `D_z^j D_θ^i` preserves `C^∞`-smoothness on an open set. -/
theorem contDiffOn_mixed {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) (j i : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.mixed j i G)) V :=
  contDiffOn_DzIter hV (contDiffOn_DthIter hV h i) j

/-! ## The closure of `SmoothQuad` -/

theorem smoothQuad_of_contDiffOn_uncurry {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Work.Spaces.quadU) :
    SmoothQuad f := h

theorem smoothQuad_add {a b : ℝ → ℝ → ℝ} (ha : SmoothQuad a) (hb : SmoothQuad b) :
    SmoothQuad (fun z θ => a z θ + b z θ) := by
  have hfun : Function.uncurry (fun z θ => a z θ + b z θ)
      = fun p : ℝ × ℝ => Function.uncurry a p + Function.uncurry b p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [SmoothQuad, hfun]
  exact ContDiffOn.add ha hb

theorem smoothQuad_neg {a : ℝ → ℝ → ℝ} (ha : SmoothQuad a) :
    SmoothQuad (fun z θ => -a z θ) := by
  have hfun : Function.uncurry (fun z θ => -a z θ)
      = fun p : ℝ × ℝ => -Function.uncurry a p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [SmoothQuad, hfun]
  exact ContDiffOn.neg ha

theorem smoothQuad_sub {a b : ℝ → ℝ → ℝ} (ha : SmoothQuad a) (hb : SmoothQuad b) :
    SmoothQuad (fun z θ => a z θ - b z θ) := by
  simpa only [sub_eq_add_neg] using smoothQuad_add ha (smoothQuad_neg hb)

theorem smoothQuad_const_mul (c : ℝ) {a : ℝ → ℝ → ℝ} (ha : SmoothQuad a) :
    SmoothQuad (fun z θ => c * a z θ) := by
  have hfun : Function.uncurry (fun z θ => c * a z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry a p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [SmoothQuad, hfun]
  exact ((contDiffOn_const : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => c)
    Work.Spaces.quadU)).mul ha

theorem smoothQuad_mul {a b : ℝ → ℝ → ℝ} (ha : SmoothQuad a) (hb : SmoothQuad b) :
    SmoothQuad (fun z θ => a z θ * b z θ) := by
  have hfun : Function.uncurry (fun z θ => a z θ * b z θ)
      = fun p : ℝ × ℝ => Function.uncurry a p * Function.uncurry b p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [SmoothQuad, hfun]
  exact ContDiffOn.mul ha hb

theorem SmoothQuad.DzIter {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) (i : ℕ) :
    SmoothQuad (Work.Spaces.DzIter i G) :=
  contDiffOn_DzIter isOpen_quadU hG i

theorem SmoothQuad.DthIter {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) (i : ℕ) :
    SmoothQuad (Work.Spaces.DthIter i G) :=
  contDiffOn_DthIter isOpen_quadU hG i

theorem SmoothQuad.mixed {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) (j i : ℕ) :
    SmoothQuad (Work.Spaces.mixed j i G) :=
  contDiffOn_mixed isOpen_quadU hG j i

/-! ## Slices and differentiability on the open quadrant -/

/-- The `z`-slice of a `C^∞` function on a product of sets is `C^∞`. -/
theorem contDiffOn_slice_z {G : ℝ → ℝ → ℝ} {s t : Set ℝ}
    (hG : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) (s ×ˢ t))
    {θ : ℝ} (hθ : θ ∈ t) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => G z θ) s :=
  (hG.comp (((contDiffOn_id : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => z) s)).prodMk
    (contDiffOn_const (c := θ))) (fun z hz => ⟨hz, hθ⟩)).congr (fun z _ => rfl)

/-- The `θ`-slice of a `C^∞` function on a product of sets is `C^∞`. -/
theorem contDiffOn_slice_θ {G : ℝ → ℝ → ℝ} {s t : Set ℝ}
    (hG : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) (s ×ˢ t))
    {z : ℝ} (hz : z ∈ s) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => G z θ) t :=
  (hG.comp ((contDiffOn_const (c := z)).prodMk
    ((contDiffOn_id : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => θ) t)))
    (fun θ hθ => ⟨hz, hθ⟩)).congr (fun θ _ => rfl)

/-- The `z`-slice of a `SmoothQuad` function at `θ ∈ (0,π/2)` is `C^∞` on `Ioi (-1)`. -/
theorem SmoothQuad.curry_z {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => G z θ) (Set.Ioi (-1)) :=
  contDiffOn_slice_z hG hθ

/-- The `θ`-slice of a `SmoothQuad` function at `z > -1` is `C^∞` on `(0,π/2)`. -/
theorem SmoothQuad.curry_θ {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) {z : ℝ}
    (hz : z ∈ Set.Ioi (-1)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => G z θ) (Set.Ioo 0 (π / 2)) :=
  contDiffOn_slice_θ hG hz

theorem smoothOrder_ne_zero : Work.Stability.smoothOrder ≠ 0 := by simp

/-- The `z`-slice of any mixed derivative of a `SmoothQuad` function is differentiable at
every `z > -1`, for every `θ ∈ (0,π/2)`. -/
theorem SmoothQuad.differentiableAt_slice_mixed {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) (b i : ℕ)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.mixed b i G z' θ) z :=
  (((hG.mixed b i).curry_z hθ).differentiableOn smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioi.mem_nhds hz)

/-- The `z`-slice of any `D_z`-iterate of a `SmoothQuad` function is differentiable at every
`z > -1`, for every `θ ∈ (0,π/2)`. -/
theorem SmoothQuad.differentiableAt_slice_DzIter {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) (b : ℕ)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter b G z' θ) z :=
  (((hG.DzIter b).curry_z hθ).differentiableOn smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioi.mem_nhds hz)

/-- The `θ`-slice of any `D_θ`-iterate of a `SmoothQuad` function is differentiable at every
`θ ∈ (0,π/2)`, for every `z > -1`. -/
theorem SmoothQuad.differentiableAt_slice_DthIter {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) (b : ℕ)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter b G z θ') θ :=
  (((hG.DthIter b).curry_θ hz).differentiableOn smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioo.mem_nhds hθ)

/-! ## Continuity of the `ℋ^k`-integrand -/

/-- The uncurried `ℋ^k`-integrand of a `SmoothQuad` function is continuous on the open
quadrant `(0,∞) × (0,π/2)`.  (The `⊤`-version is `Work.Spaces.continuousOn_HkIntegrand_Qd`.) -/
theorem continuousOn_HkIntegrand_smoothQuad (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothQuad F) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2) Qd := by
  have hq : ∀ p ∈ Qd, p ∈ Work.Spaces.quadU := by
    intro p hp
    simp only [Qd, Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2.1, hp.2.2⟩
  have hsinpos : ∀ p ∈ Qd, 0 < Real.sin (2 * p.2) :=
    fun p hp =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinpow : ∀ c : ℝ, ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd :=
    fun c => ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qd := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.w p.1
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [hfun]
    exact hw.mul (hsinpow _)
  have hwdiv : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Qd :=
    hw.div (hsinpow _) (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))
  have hDzC : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2) Qd :=
    fun i => ((contDiffOn_DzIter isOpen_quadU hF i).continuousOn).mono hq
  have hmC : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2) Qd :=
    fun j i => ((contDiffOn_mixed isOpen_quadU hF j i).continuousOn).mono hq
  have hHk : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i F p.1 p.2
                * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
                else 0 := by
    funext p; rfl
  rw [hHk]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ => ?_)
    exact ((hDzC i).mul hwdiv).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j _ => ?_))
    split_ifs with h
    · exact ((hmC j i).mul hWt).pow 2
    · exact continuousOn_const

end Work.FTS.LocData
