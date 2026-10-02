/-
# SeedExist — the α-pairs of the root portrait and their landing points

At the root-parabolic seed the two root rays `α₁, α₂` co-land at `z₁`; the pair
`P_j = {T^j α₁, T^j α₂}` therefore lands at the `j`-th point `(T_c)^[j] z₁` of the parabolic
cycle (`Work.ELTop.landsN_map`), and the pair of rays bounding the wake arc
`W_j = (wakeLo j, wakeHi j)` lands there as well (for `j ≤ 4`).

## Main results

* `Work.SeedExist.landsN_alphaPair` — `P_j` lands at `(T_c)^[j] z₁`;
* `Work.SeedExist.landsN_wake` — the two ends of the wake arc `W_j` land at `(T_c)^[j] z₁`;
* `Work.SeedExist.landsN_neg_wake` — the antipodal pair (the ends of `W_j` shifted by `1/2`)
  lands at `-(T_c)^[j] z₁`.
-/
import Submission.Work.SeedExist.Antipodal
import Submission.Work.ELTop.landsN_map

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

noncomputable section

namespace Work.SeedExist

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The level-`j` portrait pair lands at the `j`-th point of the parabolic cycle**: the rays
`T^j α₁`, `T^j α₂` land at `(T_c)^[j] z₁`. -/
theorem landsN_alphaPair {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    {z₁ : ℂ} (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) (j : ℕ) :
    Work.EL.LandsN hN ((Work.EL.T^[j]) Work.EL.alpha1) ((Tantibar c)^[j] z₁) ∧
    Work.EL.LandsN hN ((Work.EL.T^[j]) Work.EL.alpha2) ((Tantibar c)^[j] z₁) := by
  have hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
    Work.ELPull.isDynBottcher_dynPhiOf_of_dynB' hN
  have key : ∀ (θ : ℝ) (y : ℂ), Work.EL.LandsN hN θ y → ∀ n : ℕ,
      Work.EL.LandsN hN ((Work.EL.T^[n]) θ) ((Tantibar c)^[n] y) := by
    intro θ y hy n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact Work.ELTop.landsN_map hN hφ ih
  have L1 : Work.EL.LandsN hN Work.EL.alpha1 z₁ :=
    (Work.ELTop.landsN_iff_landsAt hN hφ _ _).mpr h1
  have L2 : Work.EL.LandsN hN Work.EL.alpha2 z₁ :=
    (Work.ELTop.landsN_iff_landsAt hN hφ _ _).mpr h2
  exact ⟨key _ _ L1 j, key _ _ L2 j⟩

/-- `LandsN` only depends on the angle modulo `1`. -/
theorem landsN_fract_iff {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (θ : ℝ) (y : ℂ) :
    Work.EL.LandsN hN (Int.fract θ) y ↔ Work.EL.LandsN hN θ y := by
  have h : (fun t : ℝ => hN.rayPt (Int.fract θ) t) = (fun t : ℝ => hN.rayPt θ t) := by
    funext t
    by_cases ht : 1 < t
    · exact Work.ELPull.rayPt_fract_eq hN θ t ht
    · rw [Work.Top.NakaneData.rayPt, Work.Top.NakaneData.rayPt, dif_neg ht, dif_neg ht]
  show Filter.Tendsto (fun t : ℝ => hN.rayPt (Int.fract θ) t) _ _ ↔
    Filter.Tendsto (fun t : ℝ => hN.rayPt θ t) _ _
  rw [h]

/-- **The ends of the wake arc `W_j` land at `(T_c)^[j] z₁`**, for `j ≤ 4`. -/
theorem landsN_wake {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    {z₁ : ℂ} (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁)
    (j : ℕ) (hj : j ≤ 4) :
    Work.EL.LandsN hN (Work.EL.wakeLo j) ((Tantibar c)^[j] z₁) ∧
    Work.EL.LandsN hN (Work.EL.wakeHi j) ((Tantibar c)^[j] z₁) := by
  have hα := landsN_alphaPair hN h1 h2 j
  have hfr : ∀ {θ : ℝ} {y : ℂ}, Work.EL.LandsN hN (Int.fract θ) y → Work.EL.LandsN hN θ y :=
    fun {θ y} h => (landsN_fract_iff hN θ y).mp h
  interval_cases j
  · have e1 : (Work.EL.T^[0]) Work.EL.alpha1 = Int.fract (Work.EL.wakeLo 0) := by
      norm_num [Work.EL.wakeLo, Work.EL.alpha1, Int.fract, Function.iterate_zero]
    have e2 : (Work.EL.T^[0]) Work.EL.alpha2 = Int.fract (Work.EL.wakeHi 0) := by
      norm_num [Work.EL.wakeHi, Work.EL.alpha2, Int.fract, Function.iterate_zero]
    exact ⟨hfr (by rw [← e1]; exact hα.1), hfr (by rw [← e2]; exact hα.2)⟩
  · have e1 : (Work.EL.T^[1]) Work.EL.alpha2 = Int.fract (Work.EL.wakeLo 1) := by
      norm_num [Work.EL.wakeLo, Work.EL.alpha2, Work.EL.T, Int.fract,
        Function.iterate_succ_apply', Function.iterate_zero]
    have e2 : (Work.EL.T^[1]) Work.EL.alpha1 = Int.fract (Work.EL.wakeHi 1) := by
      norm_num [Work.EL.wakeHi, Work.EL.alpha1, Work.EL.T, Int.fract,
        Function.iterate_succ_apply', Function.iterate_zero]
    exact ⟨hfr (by rw [← e1]; exact hα.2), hfr (by rw [← e2]; exact hα.1)⟩
  · have e1 : (Work.EL.T^[2]) Work.EL.alpha1 = Int.fract (Work.EL.wakeLo 2) := by
      norm_num [Work.EL.wakeLo, Work.EL.alpha1, Work.EL.T, Int.fract,
        Function.iterate_succ_apply', Function.iterate_zero]
    have e2 : (Work.EL.T^[2]) Work.EL.alpha2 = Int.fract (Work.EL.wakeHi 2) := by
      norm_num [Work.EL.wakeHi, Work.EL.alpha2, Work.EL.T, Int.fract,
        Function.iterate_succ_apply', Function.iterate_zero]
    exact ⟨hfr (by rw [← e1]; exact hα.1), hfr (by rw [← e2]; exact hα.2)⟩
  · have e1 : (Work.EL.T^[3]) Work.EL.alpha2 = Int.fract (Work.EL.wakeLo 3) := by
      norm_num [Work.EL.wakeLo, Work.EL.alpha2, Work.EL.T, Int.fract,
        Function.iterate_succ_apply', Function.iterate_zero]
    have e2 : (Work.EL.T^[3]) Work.EL.alpha1 = Int.fract (Work.EL.wakeHi 3) := by
      norm_num [Work.EL.wakeHi, Work.EL.alpha1, Work.EL.T, Int.fract,
        Function.iterate_succ_apply', Function.iterate_zero]
    exact ⟨hfr (by rw [← e1]; exact hα.2), hfr (by rw [← e2]; exact hα.1)⟩
  · have e1 : (Work.EL.T^[4]) Work.EL.alpha1 = Int.fract (Work.EL.wakeLo 4) := by
      norm_num [Work.EL.wakeLo, Work.EL.alpha1, Work.EL.T, Int.fract,
        Function.iterate_succ_apply', Function.iterate_zero]
    have e2 : (Work.EL.T^[4]) Work.EL.alpha2 = Int.fract (Work.EL.wakeHi 4) := by
      norm_num [Work.EL.wakeHi, Work.EL.alpha2, Work.EL.T, Int.fract,
        Function.iterate_succ_apply', Function.iterate_zero]
    exact ⟨hfr (by rw [← e1]; exact hα.1), hfr (by rw [← e2]; exact hα.2)⟩

/-- **The antipodal wake pair lands at the antipode**: for `j ≤ 4`, the rays at the angles
`wakeLo j + 1/2` and `wakeHi j + 1/2` land at `-(T_c)^[j] z₁`. -/
theorem landsN_neg_wake {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    {z₁ : ℂ} (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁)
    (j : ℕ) (hj : j ≤ 4) :
    Work.EL.LandsN hN (Work.EL.wakeLo j + 1 / 2) (-(Tantibar c)^[j] z₁) ∧
    Work.EL.LandsN hN (Work.EL.wakeHi j + 1 / 2) (-(Tantibar c)^[j] z₁) :=
  ⟨landsN_add_half hN (landsN_wake hN h1 h2 j hj).1,
    landsN_add_half hN (landsN_wake hN h1 h2 j hj).2⟩

end Work.SeedExist

end
