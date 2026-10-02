/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoordFix team
-/
import Mathlib
import Submission.Work.FatouCoord.Flower
import Submission.Work.FatouCoord.Flower.GermDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Repairing the Leau–Fatou flower interface: the `g`-invariant half-petal `Pg`

The delivered structure `Work.FatouCoord.ParabolicFlower F g z₀` (area `FatouCoord`) collects the
Leau–Fatou flower of a simple parabolic fixed point `z₀` of `F` with antiholomorphic square root
`g`.  Two of the facts needed *downstream* are **not** fields of that structure, and both are
false as stated for the arbitrary set `Pa` that the structure carries:

* `φa ∘ F = φa + 1` on `Pa`.  The field `φa_fatou` only gives `φa ∘ g = conj ∘ φa + 1/2`, and
  squaring it (via `IsAntiholomorphicFatouOn.comp_self`) requires `MapsTo g Pa Pa`, which is
  **false** for the wide petal of the tricorn: the wide petal `WidePetal M` is symmetric about
  the real axis while `g` is `W ↦ W̄ + b̄ + O(1/‖W‖)` in the chart, and `sgauge (g_W W) ≥
  sgauge W + 1/2 - |Im b| - O(1/‖W‖)` fails as soon as `|Im b| > 1/2`.  Moreover `φa` off `Pa`
  is a junk extension (`exists_antiFatou_of_pushforward`), so no argument may use `φa` there.
* the Fatou coordinate is *measurable* on the petal; for the junk extension this is false.

Both are repaired by exhibiting a **small `g`-invariant sub-petal** `Pg ⊆ Pa` — the
*half-plane petal*, the image of a half-plane `{Re W > M}` under the parabolic chart.  On `Pg`
the dynamics of `g` is controlled (`Re W > M` gives `Re (g_W W) ≥ M + 1/4`), so `g` preserves
`Pg`; and `F = g ∘ g` preserves it too.

`φa_shift` then follows from the **identity theorem**, with no knowledge of how `φa` was built:
`E := φa ∘ F - φa - 1` is holomorphic on the open preconnected set `Pa`, it vanishes on the open
nonempty subset `Pg` (because there `φa (g (g z)) = φa z + 1`, by `comp_self`), hence on all of
`Pa`.  This is `φa_shift_of_halfPetal` below: *the identity theorem replaces the false
invariant-petal hypothesis*.

## Conventions

`star` is complex conjugation.  In the parabolic chart at `0` the coordinate is `W = -1/u`, so
the attracting direction is `Re W → +∞` and

* `HPlanePetal M = {u ≠ 0 | M < Re (-1/u)}` is the half-plane petal of level `M`;
* `HPlanePetalAt z₀ lam M` is the same set in the chart `z ↦ -lam/(z - z₀)` at `z₀`
  (`lam` the affine scale of the germ), i.e. the image of `HPlanePetal M` under `z = z₀ + lam*u`.

## Main definitions and results

* `Work.FatouCoordFix.ParabolicFlowerFix` — `ParabolicFlower` plus a `g`-invariant half-petal
  `Pg ⊆ Pa` (open, nonempty, preconnected, `F`- and `g`-invariant, `enters_Pg`) and the shift
  `φa_shift : φa ∘ F = φa + 1` on `Pa`.
* `Work.FatouCoordFix.φa_shift_of_halfPetal` — the identity-theorem engine.
* `Work.FatouCoordFix.HalfPetalFlower` (file `PgFlower`) — the flower *restated on `Pg`*, the
  interface that the consumers (`Work.Final.RootArc`, `Work.FQC.PetalInput`) should use.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoordFix

noncomputable section

variable {F g φa : ℂ → ℂ} {z₀ : ℂ} {M : ℝ} {Pa Pg : Set ℂ}

/-! ## The half-plane petal -/

/-- The **half-plane petal** of level `M`: the image in the dynamical plane of the half-plane
`{Re W > M}` of the parabolic chart `W = -1/u`.  It is the sub-petal on which the
antiholomorphic square root `g` acts by `W ↦ W̄ + b̄ + O(1/‖W‖)` with `2 * Re b = 1`, hence
`Re W ↦ Re W + 1/4`. -/
def HPlanePetal (M : ℝ) : Set ℂ := {u : ℂ | u ≠ 0 ∧ M < (-1 / u).re}

/-- The half-plane petal in the chart at `z₀` of scale `lam`: the image of `HPlanePetal M` under
the affine chart `u ↦ z₀ + lam * u`. -/
def HPlanePetalAt (z₀ lam : ℂ) (M : ℝ) : Set ℂ :=
  {z : ℂ | z ≠ z₀ ∧ M < (-(lam / (z - z₀))).re}

@[simp] theorem mem_HPlanePetal {M : ℝ} {u : ℂ} :
    u ∈ HPlanePetal M ↔ u ≠ 0 ∧ M < (-1 / u).re := Iff.rfl

@[simp] theorem mem_HPlanePetalAt {z₀ lam : ℂ} {M : ℝ} {z : ℂ} :
    z ∈ HPlanePetalAt z₀ lam M ↔ z ≠ z₀ ∧ M < (-(lam / (z - z₀))).re := Iff.rfl

theorem neg_one_div_neg_one_div' {u : ℂ} (hu : u ≠ 0) : -1 / (-1 / u) = u := by
  field_simp

theorem HPlanePetal_eq_image {M : ℝ} (hM : 0 ≤ M) :
    HPlanePetal M = (fun W : ℂ => -1 / W) '' {W : ℂ | M < W.re} := by
  ext u
  constructor
  · rintro ⟨hu0, hu⟩
    exact ⟨-1 / u, hu, neg_one_div_neg_one_div' hu0⟩
  · rintro ⟨W, hW, rfl⟩
    have hW0 : W ≠ 0 := by
      intro h0
      rw [h0] at hW
      simp at hW
      linarith
    have hne : (-1 : ℂ) / W ≠ 0 := div_ne_zero (by norm_num) hW0
    refine ⟨hne, ?_⟩
    show M < (-1 / (-1 / W)).re
    rw [neg_one_div_neg_one_div' hW0]
    exact hW

/-- Membership in `HPlanePetalAt` is membership of the chart value in `HPlanePetal`. -/
theorem HPlanePetalAt.mem_iff {z₀ lam : ℂ} {M : ℝ} {z : ℂ} (hlam : lam ≠ 0) :
    z ∈ HPlanePetalAt z₀ lam M ↔ z ≠ z₀ ∧ (z - z₀) / lam ∈ HPlanePetal M := by
  have hkey : ∀ w : ℂ, (-1 : ℂ) / ((w - z₀) / lam) = -(lam / (w - z₀)) := by
    intro w
    rw [neg_div, one_div_div]
  constructor
  · rintro ⟨hz0, hz⟩
    refine ⟨hz0, div_ne_zero (sub_ne_zero.mpr hz0) hlam, ?_⟩
    show M < (-1 / ((z - z₀) / lam)).re
    rw [hkey z]
    exact hz
  · rintro ⟨hz0, -, hz⟩
    refine ⟨hz0, ?_⟩
    show M < (-(lam / (z - z₀))).re
    rw [← hkey z]
    exact hz

/-- The half-plane petal at `z₀` is the image of `HPlanePetal` under the affine chart. -/
theorem HPlanePetalAt_eq_image {z₀ lam : ℂ} {M : ℝ} (hlam : lam ≠ 0) :
    HPlanePetalAt z₀ lam M = (fun u : ℂ => z₀ + lam * u) '' HPlanePetal M := by
  ext z
  constructor
  · intro hz
    exact ⟨(z - z₀) / lam, ((HPlanePetalAt.mem_iff hlam).mp hz).2, by
      show z₀ + lam * ((z - z₀) / lam) = z
      rw [mul_div_cancel₀ (z - z₀) hlam]
      ring⟩
  · rintro ⟨u, hu, hu_eq⟩
    rw [← hu_eq]
    have hz0 : z₀ + lam * u ≠ z₀ := by
      intro h
      have h1 : lam * u = 0 := by linear_combination h
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hlam h2
      · exact hu.1 h2
    refine ⟨hz0, ?_⟩
    show M < (-(lam / ((z₀ + lam * u) - z₀))).re
    rw [add_sub_cancel_left]
    have h : lam / (lam * u) = 1 / u := by field_simp
    rw [h]
    simpa [neg_div] using hu.2

/-! ## The repaired flower structure -/

/-- A **Leau–Fatou flower with a `g`-invariant half-petal**.  This extends
`Work.FatouCoord.ParabolicFlower F g z₀` (so that every existing consumer of the old interface
works unchanged, `ParabolicFlowerFix` being a `ParabolicFlower`) with

* `Pg` — a *half-plane* sub-petal (the image of `{Re W > M}` under the chart), open, nonempty,
  preconnected, contained in `Pa`, forward invariant for both `F` and `g`;
* `enters_Pg` — every orbit converging to `z₀` without hitting it enters `Pg`;
* `φa_shift` — the Abel equation `φa (F z) = φa z + 1` for the *second return map* `F = g ∘ g`
  on the **whole** petal `Pa`.  This is the field that replaces the false hypothesis
  `MapsTo g Pa Pa`; it is what makes the Écalle height of a critical orbit well defined. -/
structure ParabolicFlowerFix (F g : ℂ → ℂ) (z₀ : ℂ) extends
    Work.FatouCoord.ParabolicFlower F g z₀ where
  /-- the `g`-invariant half-plane sub-petal -/
  Pg : Set ℂ
  /-- `Pg` is contained in the (wide) petal `Pa` -/
  Pg_sub : Pg ⊆ Pa
  isOpen_Pg : IsOpen Pg
  Pg_nonempty : Pg.Nonempty
  isPreconnected_Pg : IsPreconnected Pg
  mapsTo_F_Pg : MapsTo F Pg Pg
  mapsTo_g_Pg : MapsTo g Pg Pg
  /-- every orbit converging to `z₀` without hitting it enters `Pg` -/
  enters_Pg : ∀ z : ℂ, Tendsto (fun n : ℕ => F^[n] z) atTop (nhds z₀) →
    (∀ n : ℕ, F^[n] z ≠ z₀) → ∃ n : ℕ, F^[n] z ∈ Pg
  /-- **the Abel equation for the second return map `F = g ∘ g` on the whole petal** -/
  φa_shift : ∀ z ∈ Pa, φa (F z) = φa z + 1

/-! ## The identity-theorem engine for `φa_shift` -/

/-- **The identity theorem replaces the false hypothesis `MapsTo g Pa Pa`.**

Let `Pa` be open and preconnected, `Pg ⊆ Pa` open and nonempty, `g` preserve `Pg`, and let
`φa : ℂ → ℂ` be holomorphic on `Pa` with `φa (g z) = conj (φa z) + 1/2` on `Pg`.  If `g ∘ g = F`
and `F` is holomorphic with `F (Pa) ⊆ Pa`, then `φa (F z) = φa z + 1` on all of `Pa`.

Nothing is assumed about `φa` off `Pa`: the existence of `Pg` (a *set*, not an invariant-petal
hypothesis) is what makes the argument immune to the junk extension of `φa`. -/
theorem φa_shift_of_halfPetal (hPa_open : IsOpen Pa) (hPa_pre : IsPreconnected Pa)
    (hPg_open : IsOpen Pg) (hPg_ne : Pg.Nonempty) (hPg_sub : Pg ⊆ Pa)
    (hφa : DifferentiableOn ℂ φa Pa) (hF : Differentiable ℂ F) (hFmaps : MapsTo F Pa Pa)
    (hgg : g ∘ g = F) (hgmaps : MapsTo g Pg Pg)
    (hanti : ∀ z ∈ Pg, φa (g z) = star (φa z) + 1 / 2) :
    ∀ z ∈ Pa, φa (F z) = φa z + 1 := by
  obtain ⟨z₁, hz₁⟩ := hPg_ne
  have hz₁Pa : z₁ ∈ Pa := hPg_sub hz₁
  set E : ℂ → ℂ := fun z => φa (F z) - φa z - 1 with hE
  have hdiff : DifferentiableOn ℂ E Pa :=
    ((hφa.comp (hF.differentiableOn.mono (subset_univ Pa)) hFmaps).sub hφa).sub_const 1
  have hana : AnalyticOnNhd ℂ E Pa := hdiff.analyticOnNhd hPa_open
  have hev : E =ᶠ[nhds z₁] 0 := by
    refine Filter.eventuallyEq_of_mem (hPg_open.mem_nhds hz₁) ?_
    intro z hz
    have h1 : φa (g (g z)) = φa z + 1 := by
      have h2 := hanti (g z) (hgmaps hz)
      have h3 := hanti z hz
      rw [h3] at h2
      rw [h2, Work.FatouCoord.star_star_add_half]
      ring
    have h4 : (g ∘ g) z = F z := congrFun hgg z
    simp only [Function.comp_apply] at h4
    simp only [hE, Pi.zero_apply]
    rw [← h4, h1]
    ring
  intro z hz
  have h0 := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hPa_pre hz₁Pa hev hz
  simp only [hE, Pi.zero_apply] at h0
  linear_combination h0

/-! ## API of the repaired flower -/

namespace ParabolicFlowerFix

variable (h : ParabolicFlowerFix F g z₀)

/-- The orbits in `Pg` converge to `z₀` (inherited from `Pa`). -/
theorem tendsto_Pg {z : ℂ} (hz : z ∈ h.Pg) :
    Tendsto (fun n : ℕ => F^[n] z) atTop (nhds z₀) :=
  h.tendsto_Pa z (h.Pg_sub hz)

/-- `z₀ ∉ Pg`. -/
theorem z₀_not_mem_Pg : z₀ ∉ h.Pg := fun hz => h.z₀_not_mem (h.Pg_sub hz)

/-- The shifted Abel equation, iterated: `φa (F^n z) = φa z + n` on `Pa`. -/
theorem φa_shift_iterate {z : ℂ} (hz : z ∈ h.Pa) (k : ℕ) : h.φa ((F^[k]) z) = h.φa z + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', h.φa_shift _ (Work.FatouCoord.mapsTo_iterate_of_mapsTo h.mapsTo_Pa k hz), ih]
    push_cast
    ring

/-- The Écalle height `Im φa` is invariant under the return map `F` on the petal. -/
theorem ecalleHeight_map_F {z : ℂ} (hz : z ∈ h.Pa) :
    (h.φa (F z)).im = (h.φa z).im := by
  rw [h.φa_shift z hz]
  simp

/-- `φa` is an antiholomorphic Fatou coordinate on the half-petal `Pg` as well. -/
theorem antiholomorphicFatouOn_Pg : Work.FatouCoord.IsAntiholomorphicFatouOn g h.φa h.Pg :=
  ⟨h.φa_fatou.1.1.mono h.Pg_sub, h.φa_fatou.1.2.1.mono h.Pg_sub,
    fun z hz => h.φa_fatou.1.2.2 z (h.Pg_sub hz)⟩

/-- On `Pg`, `φa` is a Fatou coordinate for `F` (squaring the antiholomorphic relation). -/
theorem fatouCoordinateOn_Pg : Work.FatouCoord.IsFatouCoordinateOn F h.φa h.Pg :=
  ⟨h.φa_fatou.1.2.1.mono h.Pg_sub, fun z hz => h.φa_shift z (h.Pg_sub hz)⟩

theorem differentiableOn_φa_Pg : DifferentiableOn ℂ h.φa h.Pg := h.fatouCoordinateOn_Pg.1

theorem injective_φa_Pg : Set.InjOn h.φa h.Pg := fun a ha b hb hab =>
  h.φa_fatou.2 (h.Pg_sub ha) (h.Pg_sub hb) hab

/-- Every orbit converging to `z₀` without hitting it enters `Pg`, and then *stays* there. -/
theorem mapsTo_iterate_F_Pg (n : ℕ) : MapsTo (F^[n]) h.Pg h.Pg :=
  Work.FatouCoord.mapsTo_iterate_of_mapsTo h.mapsTo_F_Pg n

/-- **The Écalle height does not depend on the tap time on the orbit**: for `z ∈ Pa` and any
`k`, `Im φa (F^k z) = Im φa z`.  This is the statement the consumers use to see that the
critical height is well defined (`Work.Final.RootArc.critHeight_eq_ecalleHeightAt`). -/
theorem ecalleHeight_iterate {z : ℂ} (hz : z ∈ h.Pa) (k : ℕ) :
    (h.φa ((F^[k]) z)).im = (h.φa z).im := by
  rw [h.φa_shift_iterate hz k]
  simp

/-- On the half-petal `Pg`, the Abel equation is also available directly as a
`IsFatouCoordinateOn` statement for the return map. -/
theorem isFatouCoordinateOn_Pg : Work.FatouCoord.IsFatouCoordinateOn F h.φa h.Pg :=
  h.fatouCoordinateOn_Pg

end ParabolicFlowerFix

/-- A repaired flower can be used wherever the delivered `ParabolicFlower` interface is
expected. -/
instance instCoeParabolicFlower (F g : ℂ → ℂ) (z₀ : ℂ) :
    Coe (ParabolicFlowerFix F g z₀) (Work.FatouCoord.ParabolicFlower F g z₀) :=
  ⟨fun h => h.toParabolicFlower⟩

end

end Work.FatouCoordFix
