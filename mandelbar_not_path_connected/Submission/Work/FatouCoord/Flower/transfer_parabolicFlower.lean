/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib
import Submission.Work.FatouCoord.Flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Transfer of the Leau–Fatou flower along an affine chart

`Work.FatouCoord.ParabolicFlower F g z₀` is a *local* object at `z₀`: its fields are all phrased in
terms of the dynamics of `F` near `z₀`, of the antiholomorphic square root `g`, and of the two
charts `φa` (attracting) and `Ψ` (repelling).  Consequently it is invariant under an affine
conjugacy of the germ.  This file records the resulting transfer:

if `F` and `g` are conjugate to `f` and `gU` through the affine chart `u ↦ z₀ + lam * u`
(`lam ≠ 0`) and the flower of `(f, gU)` at `0` is known, then the flower of `(F, g)` at `z₀`
exists.  Concretely, with `Θ u = z₀ + lam * u` and `Θ⁻¹ z = (z - z₀)/lam`,

* `Pa ↦ Θ '' Pa`,  `φa ↦ φa ∘ Θ⁻¹`,  `Ψ ↦ Θ ∘ Ψ`,

and every field is transported: the petal is carried along by the homeomorphism `Θ`, the orbits
`F^[n] (Θ u) = Θ (f^[n] u)` correspond, and the size conditions `‖·- z₀‖ < ε` rescale by the
factor `‖lam‖`.  This is what lets the *whole* flower machinery be built once in the normalized
germ plane and then moved to the dynamical plane of the family.

The affine chart and its inverse are `trChart` and `trChartInv` below; the elementary facts about
them are collected first, and the transfer is `transfer_parabolicFlower`.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord.Flower

noncomputable section

/-! ## The affine chart `u ↦ z₀ + lam * u` and its inverse -/

/-- The affine chart `u ↦ z₀ + lam * u` putting the germ plane at the parabolic fixed point `z₀`
of the dynamical plane. -/
def trChart (z₀ lam : ℂ) (u : ℂ) : ℂ := z₀ + lam * u

/-- The inverse affine chart `z ↦ (z - z₀) / lam`. -/
def trChartInv (z₀ lam : ℂ) (z : ℂ) : ℂ := (z - z₀) / lam

lemma trChart_apply (z₀ lam u : ℂ) : trChart z₀ lam u = z₀ + lam * u := rfl

lemma trChartInv_apply (z₀ lam z : ℂ) : trChartInv z₀ lam z = (z - z₀) / lam := rfl

lemma trChart_trChartInv {z₀ lam : ℂ} (hlam : lam ≠ 0) (z : ℂ) :
    trChart z₀ lam (trChartInv z₀ lam z) = z := by
  rw [trChart_apply, trChartInv_apply, mul_div_cancel₀ (z - z₀) hlam]
  ring

lemma trChartInv_trChart {z₀ lam : ℂ} (hlam : lam ≠ 0) (u : ℂ) :
    trChartInv z₀ lam (trChart z₀ lam u) = u := by
  rw [trChartInv_apply, trChart_apply, add_sub_cancel_left]
  exact mul_div_cancel_left₀ u hlam

lemma trChart_injective {z₀ lam : ℂ} (hlam : lam ≠ 0) : Injective (trChart z₀ lam) := by
  intro u v huv
  have h := congrArg (trChartInv z₀ lam) huv
  rwa [trChartInv_trChart hlam, trChartInv_trChart hlam] at h

/-- Membership in the image of `trChart` is membership of the image point in the source set. -/
lemma mem_trChart_image {z₀ lam : ℂ} (hlam : lam ≠ 0) {s : Set ℂ} {z : ℂ} :
    z ∈ trChart z₀ lam '' s ↔ trChartInv z₀ lam z ∈ s := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rwa [trChartInv_trChart hlam]
  · intro hz
    exact ⟨trChartInv z₀ lam z, hz, trChart_trChartInv hlam z⟩

lemma continuous_trChart (z₀ lam : ℂ) : Continuous (trChart z₀ lam) :=
  continuous_const.add (continuous_const.mul continuous_id)

lemma continuous_trChartInv (z₀ lam : ℂ) : Continuous (trChartInv z₀ lam) :=
  (continuous_id.sub continuous_const).div_const lam

lemma differentiable_trChart (z₀ lam : ℂ) : Differentiable ℂ (trChart z₀ lam) :=
  (differentiable_const z₀).add ((differentiable_const lam).mul differentiable_id)

lemma differentiable_trChartInv (z₀ lam : ℂ) : Differentiable ℂ (trChartInv z₀ lam) :=
  (differentiable_id.sub (differentiable_const z₀)).div_const lam

/-- The iterates of `F` on a conjugate orbit are the images of the iterates of `f`. -/
lemma iterate_trChart {F f : ℂ → ℂ} {z₀ lam : ℂ}
    (hFf : ∀ u : ℂ, F (trChart z₀ lam u) = trChart z₀ lam (f u)) (u : ℂ) (n : ℕ) :
    F^[n] (trChart z₀ lam u) = trChart z₀ lam (f^[n] u) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ_apply']; rw [ih, hFf]

/-! ## The transfer -/

/-- **The Leau–Fatou flower transfers along an affine chart.**  If `F` and `g` are conjugate to
`f` and `gU` through `u ↦ z₀ + lam * u` (`lam ≠ 0`), then a flower for `(f, gU)` at `0` yields a
flower for `(F, g)` at `z₀`. -/
theorem transfer_parabolicFlower {F g f gU : ℂ → ℂ} {z₀ lam : ℂ} (hlam : lam ≠ 0)
    (hg_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (g z)) z)
    (hFf : ∀ u : ℂ, F (z₀ + lam * u) = z₀ + lam * f u)
    (hGg : ∀ u : ℂ, g (z₀ + lam * u) = z₀ + lam * gU u)
    (h : Work.FatouCoord.ParabolicFlower f gU 0) : Nonempty (Work.FatouCoord.ParabolicFlower F g z₀) := by
  have hFf' : ∀ u : ℂ, F (trChart z₀ lam u) = trChart z₀ lam (f u) := fun u => hFf u
  have hGg' : ∀ u : ℂ, g (trChart z₀ lam u) = trChart z₀ lam (gU u) := fun u => hGg u
  have hnorm : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  refine ⟨{
    Pa := trChart z₀ lam '' h.Pa
    φa := fun z => h.φa (trChartInv z₀ lam z)
    Ψ := fun w => trChart z₀ lam (h.Ψ w)
    isOpen_Pa := ?_
    isPreconnected_Pa := ?_
    z₀_not_mem := ?_
    mapsTo_Pa := ?_
    tendsto_Pa := ?_
    enters_Pa := ?_
    φa_fatou := ?_
    Ψ_diff := ?_
    Ψ_shift := ?_
    Ψ_anti := ?_
    Ψ_small := ?_
    Ψ_inj := ?_
    Ψ_ends := ?_
    cover := ?_ }⟩
  -- `Pa` is open, being the preimage of the open `Pa` of `h` under the continuous inverse chart
  · rw [show trChart z₀ lam '' h.Pa = trChartInv z₀ lam ⁻¹' h.Pa from by
        ext z; exact mem_trChart_image hlam]
    exact h.isOpen_Pa.preimage (continuous_trChartInv z₀ lam)
  -- `Pa` is preconnected, being the image of the preconnected `Pa` of `h`
  · exact h.isPreconnected_Pa.image _ (continuous_trChart z₀ lam).continuousOn
  -- the centre of the flower of `h` is `0`, which is not in `h.Pa`
  · intro hmem
    rw [mem_trChart_image hlam] at hmem
    have h0 : trChartInv z₀ lam z₀ = 0 := by simp [trChartInv]
    rw [h0] at hmem
    exact h.z₀_not_mem hmem
  · rintro z ⟨u, hu, rfl⟩
    rw [hFf']
    exact ⟨f u, h.mapsTo_Pa hu, rfl⟩
  -- orbits in the new petal converge to `z₀`, by continuity of the chart
  · rintro z ⟨u, hu, rfl⟩
    have hiter : ∀ n : ℕ, F^[n] (trChart z₀ lam u) = trChart z₀ lam (f^[n] u) :=
      fun n => iterate_trChart hFf' u n
    have h1 : Tendsto (fun v : ℂ => trChart z₀ lam v) (nhds 0) (nhds (trChart z₀ lam 0)) :=
      (continuous_trChart z₀ lam).tendsto 0
    have h2 : trChart z₀ lam (0 : ℂ) = z₀ := by simp [trChart]
    rw [h2] at h1
    exact Tendsto.congr (fun n => (hiter n).symm) (h1.comp (h.tendsto_Pa u hu))
  -- an orbit converging to `z₀` and avoiding it is, in the chart, an orbit converging to `0`
  -- and avoiding it, hence eventually enters the petal
  · intro z hzlim hzne
    set u := trChartInv z₀ lam z with hu
    have hz_eq : z = trChart z₀ lam u := by rw [hu]; exact (trChart_trChartInv hlam z).symm
    have hiter : ∀ n : ℕ, F^[n] z = trChart z₀ lam (f^[n] u) := by
      intro n; rw [hz_eq]; exact iterate_trChart hFf' u n
    have hlim : Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => trChartInv z₀ lam (F^[n] z)) atTop
          (nhds (trChartInv z₀ lam z₀)) :=
        ((continuous_trChartInv z₀ lam).tendsto z₀).comp hzlim
      have h2 : trChartInv z₀ lam z₀ = 0 := by simp [trChartInv]
      rw [h2] at h1
      refine Tendsto.congr (fun n => ?_) h1
      rw [hiter n, trChartInv_trChart hlam]
    have hne' : ∀ n : ℕ, f^[n] u ≠ 0 := by
      intro n h0
      refine hzne n ?_
      rw [hiter n, h0]
      simp [trChart]
    obtain ⟨n, hn⟩ := h.enters_Pa u hlim hne'
    exact ⟨n, by rw [hiter n]; exact ⟨f^[n] u, hn, rfl⟩⟩
  · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact fun z _ => (hg_anti z).differentiableWithinAt
    · exact h.φa_fatou.1.2.1.comp (differentiable_trChartInv z₀ lam).differentiableOn
        (fun z hz => (mem_trChart_image hlam).mp hz)
    · intro z hz
      obtain ⟨u, hu, rfl⟩ := hz
      show h.φa (trChartInv z₀ lam (g (trChart z₀ lam u))) =
        star (h.φa (trChartInv z₀ lam (trChart z₀ lam u))) + 1 / 2
      rw [hGg', trChartInv_trChart hlam, trChartInv_trChart hlam]
      exact h.φa_fatou.1.2.2 u hu
    · intro a ha b hb hab
      have h1 := h.φa_fatou.2 ((mem_trChart_image hlam).mp ha)
        ((mem_trChart_image hlam).mp hb) hab
      have h2 := congrArg (trChart z₀ lam) h1
      rwa [trChart_trChartInv hlam, trChart_trChartInv hlam] at h2
  · exact (differentiable_trChart z₀ lam).comp h.Ψ_diff
  · intro w
    rw [h.Ψ_shift, hFf']
  · intro w
    rw [h.Ψ_anti, ← hGg']
  · intro ε hε
    obtain ⟨R, hR⟩ := h.Ψ_small (ε / ‖lam‖) (div_pos hε hnorm)
    refine ⟨R, fun w hw => ⟨?_, ?_⟩⟩
    · intro hcontra
      have h1 : trChartInv z₀ lam (trChart z₀ lam (h.Ψ w)) = trChartInv z₀ lam z₀ :=
        congrArg (trChartInv z₀ lam) hcontra
      rw [trChartInv_trChart hlam] at h1
      have h0 : trChartInv z₀ lam z₀ = 0 := by simp [trChartInv]
      rw [h0] at h1
      exact (hR w hw).1 h1
    · have h2 : ‖h.Ψ w‖ < ε / ‖lam‖ := by simpa using (hR w hw).2
      have hlt : ‖h.Ψ w‖ * ‖lam‖ < ε := (lt_div_iff₀ hnorm).mp h2
      show ‖trChart z₀ lam (h.Ψ w) - z₀‖ < ε
      rw [trChart_apply]
      calc ‖z₀ + lam * h.Ψ w - z₀‖ = ‖lam * h.Ψ w‖ := by rw [add_sub_cancel_left]
        _ = ‖lam‖ * ‖h.Ψ w‖ := norm_mul lam (h.Ψ w)
        _ = ‖h.Ψ w‖ * ‖lam‖ := mul_comm _ _
        _ < ε := hlt
  · obtain ⟨R₀, hR₀⟩ := h.Ψ_inj
    exact ⟨R₀, fun a ha b hb hab => hR₀ ha hb (trChart_injective hlam hab)⟩
  · obtain ⟨R₀, hR₀⟩ := h.Ψ_ends
    exact ⟨R₀, fun w hw hwim => ⟨h.Ψ w, hR₀ w hw hwim, rfl⟩⟩
  -- the covering property rescales by `‖lam‖`
  · intro R
    obtain ⟨r, hr_pos, hr⟩ := h.cover R
    refine ⟨‖lam‖ * r, mul_pos hnorm hr_pos, ?_⟩
    intro z hz0 hzlt
    set u := trChartInv z₀ lam z with hu
    have hu_norm : ‖u‖ = ‖z - z₀‖ / ‖lam‖ := by rw [hu]; simp only [trChartInv, norm_div]
    have hu_pos : 0 < ‖u‖ := by rw [hu_norm]; exact div_pos hz0 hnorm
    have hu_lt : ‖u‖ < r := by
      rw [hu_norm]
      exact (div_lt_iff₀ hnorm).mpr (by rw [mul_comm]; exact hzlt)
    have hmem := hr u (by simpa using hu_pos) (by simpa using hu_lt)
    rcases hmem with hu_Pa | ⟨w, hw, hwΨ⟩
    · exact Or.inl ⟨u, hu_Pa, by rw [hu]; exact trChart_trChartInv hlam z⟩
    · exact Or.inr ⟨w, hw, by rw [hwΨ]; rw [hu]; exact trChart_trChartInv hlam z⟩

end

end Work.FatouCoord.Flower
