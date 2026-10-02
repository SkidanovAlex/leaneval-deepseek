/-
# `Work.GATE2.Escape.disc_half_shift` — a leak disc survives the half shift `x + 1 ↦ x + 1/2`

Area **GATE2**, residual 3 (SHIFTED ESCAPE).  The `ι b`-tongue of the gate is controlled by the
*half-integer* translate `x* - j₀ + 1/2` of the leak level `x* - j₀` of the `b`-tongue.  This file
proves that the robustness of a *leak disc* (`Ψ` maps a closed disc out of the filled Julia set
`K c`) is invariant under the half shift of the centre, so that a robustness datum at the level
`x + 1` — the form in which PARIMPL's design produces it — transfers to the level `x + 1/2`.

## The mathematics

Let `g = (T_c)^5`, so that the second return map is `F c = (T_c)^{10} = g ∘ g`, and let
`Ψ : ℂ → ℂ` be the entire repelling coordinate of the flower (`ParabolicFlower.Ψ`), with

* `Ψ (w + 1) = F c (Ψ w)`   (`Ψ_shift`),
* `Ψ (w̄ + 1/2) = g (Ψ w)`   (`Ψ_anti`, HS Lemma 2.3).

Both are *elementary* consequences of the two structural facts above, together with the
**complete invariance** of the filled Julia set `K c = {z | BoundedOrbit c z}` of the
antipolynomial `T_c (z) = z̄² + c`:  `z ∈ K c ↔ T_c z ∈ K c` (the orbit of `T_c z` is the tail of
the orbit of `z`, and conversely `‖z‖² ≤ ‖T_c z‖ + ‖c‖` bounds `z` by the orbit of `T_c z`).

*Write `Clean a` for `∀ y ∈ closedBall a r, Ψ y ∉ K c`.*

1. **`Clean` is `1`-periodic in the centre** (this uses only `Ψ_shift`):  `y ∈ closedBall a r`
   iff `y + 1 ∈ closedBall (a+1) r`, and `Ψ (y+1) = F c (Ψ y)`, so by complete invariance
   `Ψ (y+1) ∈ K c ↔ Ψ y ∈ K c`.  Hence `Clean a ↔ Clean (a+1)`.
2. **The half shift** (this uses `Ψ_anti`):  for `y ∈ closedBall (a + 1/2) r` the point
   `z = ȳ - 1/2` lies in `closedBall a r` (because `‖ȳ - 1/2 - a‖ = ‖y - (a + 1/2)‖`), and
   `Ψ_anti` at `z` reads `Ψ y = Ψ (z̄ + 1/2) = g (Ψ z)`.  Complete invariance then gives
   `Ψ y ∈ K c ↔ Ψ z ∈ K c`.

The hypothesis is `Clean (x+1)`.  By (1) this is `Clean x`, and by (2) (with `a = x`) it implies
`Clean (x + 1/2)` — the desired conclusion.  (Note that we cannot simply *reduce* the disc
`closedBall (x+1/2) r` to `closedBall (x+1) r`: the two discs have the same radius and neither
contains the other; the half shift of the *centre* is what makes the argument work.)

All the facts used are the fields `Ψ_shift`, `Ψ_anti` of `ParabolicFlower` and the elementary
invariance of the filled Julia set proved below.
-/
import Mathlib
import Submission.Work.ELRig.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.ParamRays

namespace Work.GATE2.Escape

/-! ## Complete invariance of the filled Julia set of `T_c` -/

/-- **Forward and backward invariance.**  The orbit of `T_c z` is the tail of the orbit of `z`,
and conversely `z` is recovered from the orbit of `T_c z` (its `0`-th term); hence the orbit of
`z` is bounded if and only if the orbit of `T_c z` is. -/
theorem boundedOrbit_tantibar_iff (c z : ℂ) :
    BoundedOrbit c z ↔ BoundedOrbit c (Tantibar c z) := by
  constructor
  · intro h
    simpa [orbit] using h.shift 1
  · intro h
    obtain ⟨M, hM⟩ := h
    refine ⟨max ‖z‖ M, fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact le_max_left _ _
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [orbit_one_add]
      exact le_trans (hM m) (le_max_right _ _)

/-- Iterated form: `z ∈ K c ↔ (T_c)^[n] z ∈ K c`. -/
theorem boundedOrbit_iterate_iff (c z : ℂ) (n : ℕ) :
    BoundedOrbit c z ↔ BoundedOrbit c (((Tantibar c)^[n]) z) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← boundedOrbit_tantibar_iff c (((Tantibar c)^[k]) z)]
    exact ih

/-- **Complete invariance of `Work.EL.K`**:  `z ∈ K c ↔ (T_c)^[n] z ∈ K c`. -/
theorem mem_K_iff_iterate (c z : ℂ) (n : ℕ) :
    z ∈ Work.EL.K c ↔ ((Tantibar c)^[n]) z ∈ Work.EL.K c := by
  simp only [Work.EL.K, Work.ParamRays.filledJulia, Set.mem_ofPred_eq]
  exact boundedOrbit_iterate_iff c z n

/-! ## The half shift of a disc centred on the real axis -/

/-- **The half shift is an isometry between the two discs**:  the map `y ↦ ȳ - 1/2` sends the
closed disc of centre `x + 1/2` and radius `r` **onto** the closed disc of centre `x` and radius
`r`; on the level of distances,
`dist (ȳ - 1/2) x = dist y (x + 1/2)`. -/
theorem dist_star_sub_half (y : ℂ) (x : ℝ) :
    dist (star y - 1/2) ((x:ℝ):ℂ) = dist y (((x + 1/2 : ℝ)):ℂ) := by
  rw [dist_eq_norm, dist_eq_norm]
  have hhalf : star (1/2 : ℂ) = (1/2 : ℂ) := by norm_num [map_div₀]
  have hxs : star ((x:ℝ):ℂ) = ((x:ℝ):ℂ) := by
    rw [show star (((x:ℝ):ℂ)) = (starRingEnd ℂ) (((x:ℝ):ℂ)) from rfl, Complex.conj_ofReal]
  have h1 : star y - (1/2:ℂ) - ((x:ℝ):ℂ) = star (y - (1/2:ℂ) - ((x:ℝ):ℂ)) := by
    rw [star_sub, star_sub, hhalf, hxs]
  have hnorm : ‖star (y - (1/2:ℂ) - ((x:ℝ):ℂ))‖ = ‖y - (1/2:ℂ) - ((x:ℝ):ℂ)‖ :=
    Complex.norm_conj _
  rw [h1, hnorm]
  congr 1
  push_cast
  ring

/-! ## The half shift of a leak disc -/

/-- **The leak disc survives the half shift.**  If the repelling coordinate `Ψ` of the flower
maps the closed disc of centre `x + 1` and radius `r` out of the filled Julia set `K c`, then it
does the same for the closed disc of centre `x + 1/2` and radius `r`.

Proof:  the hypothesis says that `Ψ` is clean on `closedBall (x+1) r`.  Since `Ψ (y+1) =
(T_c)^{10} (Ψ y)` and `K c` is completely invariant under `T_c`, cleanness is `1`-periodic in
the centre, so `Ψ` is clean on `closedBall x r` as well.  Finally, for `y` in the half-shifted
disc, `z = ȳ - 1/2` lies in `closedBall x r` and `Ψ_anti` gives `Ψ y = (T_c)^5 (Ψ z)`;
complete invariance of `K c` under `T_c` then transports the cleanness at `z` back to `y`. -/
theorem disc_half_shift {c : ℂ} {z₁ : ℂ}
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z₁)
    {x r : ℝ}
    (h : ∀ y ∈ Metric.closedBall (((x + 1 : ℝ)) : ℂ) r, fl.Ψ y ∉ Work.EL.K c) :
    ∀ y ∈ Metric.closedBall (((x + 1 / 2 : ℝ)) : ℂ) r, fl.Ψ y ∉ Work.EL.K c := by
  -- Step 1: `Ψ` is clean on the disc centred at `x`:  cleanness is `1`-periodic, via
  -- `Ψ (y + 1) = (T_c)^{10} (Ψ y)` and the complete invariance of `K c`.
  have hx : ∀ y ∈ Metric.closedBall ((x : ℝ) : ℂ) r, fl.Ψ y ∉ Work.EL.K c := by
    intro y hy
    have hy1 : y + 1 ∈ Metric.closedBall (((x + 1 : ℝ)) : ℂ) r := by
      rw [Metric.mem_closedBall] at hy ⊢
      rw [dist_eq_norm] at hy ⊢
      have hc : (((x + 1 : ℝ)) : ℂ) = ((x : ℝ) : ℂ) + 1 := by push_cast; ring
      rw [hc]
      have heq : ‖y + 1 - (((x : ℝ) : ℂ) + 1)‖ = ‖y - ((x : ℝ) : ℂ)‖ := by
        congr 1; ring
      rw [heq]; exact hy
    have h2 := h (y + 1) hy1
    intro hmem
    apply h2
    have hFF : fl.Ψ (y + 1) = (Tantibar c)^[10] (fl.Ψ y) := by
      rw [fl.Ψ_shift]
      exact congrFun (Work.EL.F_eq_tantibar c) (fl.Ψ y)
    rw [hFF]
    exact (mem_K_iff_iterate c (fl.Ψ y) 10).mp hmem
  -- Step 2: the half shift, via conjugation (`Ψ_anti`).
  intro y hy
  set z : ℂ := star y - 1/2 with hz
  have hzball : z ∈ Metric.closedBall ((x : ℝ) : ℂ) r := by
    rw [Metric.mem_closedBall] at hy ⊢
    rw [dist_star_sub_half]
    exact hy
  have hclean : fl.Ψ z ∉ Work.EL.K c := hx z hzball
  intro hmem
  apply hclean
  have hanti := fl.Ψ_anti z
  have hsz : star z + 1/2 = y := by
    rw [hz, star_sub, star_star]
    have hhalf : star (1/2 : ℂ) = (1/2 : ℂ) := by norm_num [map_div₀]
    rw [hhalf]; ring
  rw [hsz] at hanti
  rw [hanti] at hmem
  exact (mem_K_iff_iterate c (fl.Ψ z) 5).mpr hmem

end Work.GATE2.Escape
