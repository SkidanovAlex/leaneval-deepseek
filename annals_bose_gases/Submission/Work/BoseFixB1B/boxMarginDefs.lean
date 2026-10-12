import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.DLInfra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.boxMarginDefs` — the coordinate margin of the sliding box `B(u)`

Holder of `Work.BoseFixB1B.perSectorBoundG_of_sectorCount`.

## Why this file exists

The target `Work.BoseFixB1B.perSectorBoundG_of_sectorCount` reduces the count-indexed core
`SectorCountSmallbox` (an inequality for **smooth** states all of whose particles lie in the
sliding box `B(u) = dlBox ℓ d u`) to the termwise per-sector residual `PerSectorBoundG` (an
inequality whose states are the **sector pieces** `1_{n_{B(u)} = k}·Φ`, whose *fibres* are the
sharp functions `1_{B(u)^{|S|}}·(smooth fibre)`).

The intended route is: slot decomposition of the sector piece, Fubini splitting of the outside
configuration (the fibre), the fibre factorisation of the word
(`Work.SlotWord.WordFibreFactorisation`, PROVED), and the count inequality at the fibre.  The last
step needs the count inequality for the **sharp** fibre `1_{B(u)^{|S|}}·ψ`, while
`SectorCountSmallbox` is stated only for `BoxState` (i.e. `ContDiff ℝ ∞`) states.  The repair is to
approximate the sharp fibre by `Ψ_δ := γ_δ^{|S|}·ψ` with `γ_δ` a smooth cutoff that equals `1` on
the inner box `{boxMargin ≥ δ}` and is supported in `dlBox`, and to pass the count inequality to
the limit.

The two geometric inputs of that passage are, with `m(x) := boxMargin ℓ d u x`:

* **(F1)** `|chiB ℓ d u x| ≤ C·m(x)` for `x ∈ dlBox` — the first-order vanishing of the window at
  the boundary of the box (it follows from
  `|chiBase y| ≤ C·(1/2 − ‖y‖)`, a one-line consequence of the mean value inequality and the fact
  that `chiBase` is `C^∞` and supported in `closedBall 0 (1/2)`), and
* **(F2)** `volume ({x | m x < δ} ∩ support (chiB ℓ d u)) ≤ C·δ` — the *linear* collar bound, which
  together with (F1) gives `∫ χ²·|∇γ_δ|² ≤ (C'/δ²)·C²δ²·(Cδ) = O(δ) → 0`.

(This `O(δ)` is all that is needed: it makes both the `L²`- and the `H¹`-distance between the
windowed slit function of `Ψ_δ` and that of the sharp fibre vanish, hence the sliding word of
`Ψ_δ` converges to that of the sharp fibre.  No tangency/cap estimate is required.)

## What is in this file

The definition of the margin and its elementary API; the estimates (F1), (F2) live in their own
modules.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open Submission.BoseGases

set_option autoImplicit false

/-- **The box margin** of `x` for the sliding box `B(u) = acube ℓ ∩ ((ℓd)•u + acube (ℓd))`: the
smallest coordinate margin among the six faces of the two cubes.  It is `≥ 0` exactly on
`dlBox ℓ d u` and vanishes on the boundary of the box. -/
noncomputable def boxMargin (ℓ d : ℝ) (u x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  min (Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 3 => ℓ / 2 - |x i|))
    (Finset.univ.inf' Finset.univ_nonempty
      (fun i : Fin 3 => ℓ * d / 2 - |(x - (ℓ * d) • u) i|))

/-- **`boxMargin` is `≥ 0` exactly on the sliding box.** -/
theorem boxMargin_nonneg_iff {ℓ d : ℝ} {u x : EuclideanSpace ℝ (Fin 3)} :
    0 ≤ boxMargin ℓ d u x ↔ x ∈ dlBox ℓ d u := by
  rw [dlBox, acube, acube, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · intro h
    have hA : 0 ≤ Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 3 => ℓ / 2 - |x i|) :=
      (le_min_iff.mp h).1
    have hB : 0 ≤ Finset.univ.inf' Finset.univ_nonempty
        (fun i : Fin 3 => ℓ * d / 2 - |(x - (ℓ * d) • u) i|) := (le_min_iff.mp h).2
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have h1 := Finset.inf'_le (s := Finset.univ) (fun i : Fin 3 => ℓ / 2 - |x i|)
        (Finset.mem_univ i)
      have h2 : 0 ≤ ℓ / 2 - |x i| := le_trans hA h1
      have h3 : x i ≤ |x i| := le_abs_self _
      have h4 : -(|x i|) ≤ x i := neg_abs_le _
      exact ⟨by linarith, by linarith⟩
    · have h1 := Finset.inf'_le (s := Finset.univ)
        (fun i : Fin 3 => ℓ * d / 2 - |(x - (ℓ * d) • u) i|) (Finset.mem_univ i)
      have h2 : 0 ≤ ℓ * d / 2 - |(x - (ℓ * d) • u) i| := le_trans hB h1
      have h3 : (x - (ℓ * d) • u) i ≤ |(x - (ℓ * d) • u) i| := le_abs_self _
      have h4 : -(|(x - (ℓ * d) • u) i|) ≤ (x - (ℓ * d) • u) i := neg_abs_le _
      exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine le_min_iff.mpr ⟨Finset.le_inf' Finset.univ_nonempty _ (fun i _ => ?_),
      Finset.le_inf' Finset.univ_nonempty _ (fun i _ => ?_)⟩
    · have h := h1 i
      have h5 : |x i| ≤ ℓ / 2 := abs_le.mpr ⟨by linarith [h.1], h.2⟩
      linarith
    · have h := h2 i
      have h5 : |(x - (ℓ * d) • u) i| ≤ ℓ * d / 2 := abs_le.mpr ⟨by linarith [h.1], h.2⟩
      linarith

/-- The margin vanishes outside the box. -/
theorem boxMargin_nonpos_of_notMem {ℓ d : ℝ} {u x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∉ dlBox ℓ d u) : boxMargin ℓ d u x ≤ 0 :=
  not_lt.mp fun h => hx (boxMargin_nonneg_iff.mp h.le)

/-- **Coordinate margin**: the margin is at most the margin of the face `x i = ±ℓ/2`. -/
theorem boxMargin_le_coord {ℓ d : ℝ} (u x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    boxMargin ℓ d u x ≤ ℓ / 2 - |x i| :=
  le_trans (min_le_left _ _)
    (Finset.inf'_le (s := Finset.univ) (fun i : Fin 3 => ℓ / 2 - |x i|) (Finset.mem_univ i))

/-- **Translated-coordinate margin**: the same for the second cube. -/
theorem boxMargin_le_transCoord {ℓ d : ℝ} (u x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    boxMargin ℓ d u x ≤ ℓ * d / 2 - |(x - (ℓ * d) • u) i| :=
  le_trans (min_le_right _ _)
    (Finset.inf'_le (s := Finset.univ) (fun i : Fin 3 => ℓ * d / 2 - |(x - (ℓ * d) • u) i|)
      (Finset.mem_univ i))

/-- The margin is bounded above by `ℓ/2`. -/
theorem boxMargin_le_half {ℓ d : ℝ} (u x : EuclideanSpace ℝ (Fin 3)) :
    boxMargin ℓ d u x ≤ ℓ / 2 := by
  have h := boxMargin_le_coord (ℓ := ℓ) (d := d) u x (0 : Fin 3)
  have h2 := abs_nonneg (x (0 : Fin 3))
  linarith

end Work.BoseFixB1B
