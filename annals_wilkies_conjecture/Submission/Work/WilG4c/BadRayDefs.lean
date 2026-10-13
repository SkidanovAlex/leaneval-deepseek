/-
  WilG4c — vocabulary for `badRay_interior_eq_empty`.

  For a set `T ⊆ ℝ^N` and a point `u`, the *bad ray set* of `T` at `u` consists of the points
  `x` whose segment `[u,x]` meets `T` in infinitely many points:

      `badRay T u = {x | {t ∈ (0,1] | u + t • (x - u) ∈ T}.Infinite}`.

  The main theorem `Work.WilG4c.badRay_interior_eq_empty` says that for `T` in an `Ω`-format of
  a sharply o-minimal structure, `interior T = ∅` forces `interior (badRay T u) = ∅`.

  The proof runs through the "cone" set

      `Vpt u T = {(x,t) | u + t • (x - u) ∈ T} ⊆ ℝ^{N+1}`,

  whose `t`-fibre over `x` is exactly the set of parameters `t` with `u + t • (x-u) ∈ T`.  The
  two ingredients about `Vpt` are that it is again `Ω`-definable with bounds independent of
  `u` and `T` (module `Submission.Work.WilG4c.Vpt_mem`) and that it has empty interior whenever
  `T` does (module `Submission.Work.WilG4c.Vpt_interior_eq_empty`).
-/
import Mathlib
import Submission.Work.Wilkies.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-- The "bad ray" of `T` at `u`: the points `x` such that the segment `[u,x]` meets `T` in
infinitely many points. -/
def badRay {N : ℕ} (T : Set (Fin N → ℝ)) (u : Fin N → ℝ) : Set (Fin N → ℝ) :=
  {x | {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧ u + t • (x - u) ∈ T}.Infinite}

/-- The cone over `T` from `u`: the pairs `(x,t)` such that `u + t • (x - u) ∈ T`.
Its last coordinate is the parameter `t` and its other coordinates are `x`. -/
def Vpt {N : ℕ} (u : Fin N → ℝ) (T : Set (Fin N → ℝ)) : Set (Fin (N + 1) → ℝ) :=
  {w | u + (w (Fin.last N)) • (Fin.init w - u) ∈ T}

theorem mem_Vpt {N : ℕ} {u : Fin N → ℝ} {T : Set (Fin N → ℝ)} {w : Fin (N + 1) → ℝ} :
    w ∈ Vpt u T ↔ u + (w (Fin.last N)) • (Fin.init w - u) ∈ T := Iff.rfl

theorem mem_Vpt_snoc {N : ℕ} {u : Fin N → ℝ} {T : Set (Fin N → ℝ)} {x : Fin N → ℝ} {t : ℝ} :
    (Fin.snoc x t : Fin (N + 1) → ℝ) ∈ Vpt u T ↔ u + t • (x - u) ∈ T := by
  rw [mem_Vpt, Fin.init_snoc, Fin.snoc_last]

/-- The `t`-fibre of `Vpt u T` over `x` contains the parameter set defining `badRay T u`. -/
theorem badRay_subset_fibre {N : ℕ} (T : Set (Fin N → ℝ)) (u : Fin N → ℝ) :
    badRay T u ⊆ {x : Fin N → ℝ |
      {t : ℝ | (Fin.snoc x t : Fin (N + 1) → ℝ) ∈ Vpt u T}.Infinite} := by
  intro x hx
  refine Set.Infinite.mono ?_ hx
  intro t ht
  rw [Set.mem_ofPred_eq] at ht ⊢
  exact mem_Vpt_snoc.mpr ht.2

end Work.WilG4c
