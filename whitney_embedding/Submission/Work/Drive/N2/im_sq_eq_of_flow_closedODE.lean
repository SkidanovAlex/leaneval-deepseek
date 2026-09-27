import Mathlib
import Submission.Work.Drive.N2.modelOrbitInvariant

/-!
# The `Im (Z ·)²` invariant for a flow whose chart ODE holds on a confinement set

`Work.Drive.N2.im_sq_eq_of_flow_chartODE` proves the invariant `Im (Z ·)² = const` for a flow `Φ`
whose chart coordinates solve the model saddle ODE

    u₀' = chartMult r (‖u‖²) · u₀,      u₁' = chartMult r (‖u‖²) · (-u₁),

*provided the whole trace from `0` to `t` stays in the chart source* `φ.source`.

The statement proved here is the same invariant with the chart source replaced by an **arbitrary**
confinement set `C : Set M`: the ODE is only assumed at the parameters whose trace up to that
parameter stays inside `C`, and the trace from `0` to `t` is assumed to stay in `C`.  This is the
form produced by the level-flow construction, where what has to be confined is a collar/window
region and not the chart source.

The proof is the one of `im_sq_eq_of_flow_chartODE`, with `φ.source` systematically replaced by `C`:
the ODE hypothesis holds at every intermediate parameter because the sub-trace up to an intermediate
parameter is a subset of the given trace.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function

theorem im_sq_eq_of_flow_closedODE {M : Type*} [TopologicalSpace M]
    {Φ : ℝ × M → M} (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (Z : M → ℂ) (hZ : ∀ m : M, Z m = (φ m 0 : ℂ) + (φ m 1 : ℂ) * Complex.I)
    (r : ℝ) {C : Set M}
    (hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C) →
      HasDerivAt (fun σ : ℝ => φ (Φ (σ, y)) 0)
        (Work.Drive.N2.chartMult r (‖φ (Φ (t, y))‖ ^ 2) * ((1 : ℝ) * φ (Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ (Φ (σ, y)) 1)
        (Work.Drive.N2.chartMult r (‖φ (Φ (t, y))‖ ^ 2) * ((-1 : ℝ) * φ (Φ (t, y)) 1)) t)
    (hΦ0 : ∀ m : M, Φ (0, m) = m)
    (y : M) (t : ℝ) (hconf : ∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C) :
    ((Z (Φ (t, y))) ^ 2).im = ((Z y) ^ 2).im := by
  -- The sub-trace up to an intermediate parameter stays in `C`, so the ODE holds there.
  have hsub : ∀ τ ∈ Set.uIcc (0 : ℝ) t,
      Set.Icc (min 0 τ) (max 0 τ) ⊆ Set.Icc (min 0 t) (max 0 t) := by
    intro τ hτ s hs
    obtain ⟨hs1, hs2⟩ := hs
    obtain ⟨hτ1, hτ2⟩ := hτ
    constructor
    · rcases le_total 0 τ with h | h
      · rw [min_eq_left h] at hs1
        linarith [min_le_left (0 : ℝ) t]
      · rw [min_eq_right h] at hs1
        linarith [min_le_left (0 : ℝ) t]
    · rcases le_total 0 τ with h | h
      · rw [max_eq_right h] at hs2
        linarith [le_max_right (0 : ℝ) t]
      · rw [max_eq_left h] at hs2
        exact le_trans hs2 (le_max_left (0 : ℝ) t)
  have hmain : ∀ τ ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun σ : ℝ => φ (Φ (σ, y)) 0)
        (chartMult r (‖φ (Φ (τ, y))‖ ^ 2) * ((1 : ℝ) * φ (Φ (τ, y)) 0)) τ ∧
      HasDerivAt (fun σ : ℝ => φ (Φ (σ, y)) 1)
        (chartMult r (‖φ (Φ (τ, y))‖ ^ 2) * ((-1 : ℝ) * φ (Φ (τ, y)) 1)) τ := by
    intro τ hτ
    exact hODE y τ (fun u hu => hconf u (hsub τ hτ hu))
  have hprod := im_sq_eq_of_chartODE (w := fun σ : ℝ => φ (Φ (σ, y))) (β := chartMult r)
    (s₁ := 1) (s₂ := -1) (by norm_num) hmain
  rw [hΦ0 y] at hprod
  rw [hZ (Φ (t, y)), hZ y]
  exact hprod

end Work.Drive.N2
