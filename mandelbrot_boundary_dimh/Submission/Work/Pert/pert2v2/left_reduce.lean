import Mathlib
import Submission.Work.Pert.pert2v2.orbit_pieces

/-!
# `Work.Pert.pert2v2.orbit_mem_left_reduce` — the leftward reduction of the membership clause

`PertData.orbit`'s conclusion carries the clause `∀ i < n, f^[i] (φ w) ∈ Df` for the **contract's**
shift `n`, which the sector condition makes as large as `≈ Re (1/α)`.  The mechanism that produces
it (see `pert2v2/orbit_mem.lean`) works at a *chart* point `x` of the walk, with `w = x + k` and
`k` the chart shift:

* the crux's clause gives `f^j (φ x) ∈ Df` for `j ≤ mₓ`;
* the level structure of the next walk point gives `j ∈ [mₓ, lo)`;
* hence `φ w = f^k (φ x)` gives the memberships of `φ w` only on `[0, mₓ − k]` and `[mₓ, lo)` —
  a **gap** of length `k` when `k > 0`.

So the first chart shift `k 0` must be `≤ 0`, i.e. `w` must first be translated **left** into the
window `|Re| ≲ 1`.  This file provides the translation step: the memberships at `w` follow from
those at `w − s` (`s` a natural), because `φ w = f^s (φ (w − s))` along the ray (the Abel equation
iterated), so `f^i (φ w) = f^{i+s} (φ (w−s))` and the range shifts by `s`.
-/

namespace Work.Pert.pert2v2

open Work.Pert Complex Set

noncomputable section

/-- **The membership clause transfers from `w − s` to `w`.**  If the ray
`(w − s), (w − s) + 1, …, w` lies in `Dφ` and the orbit memberships are known at `w − s` for
`i < N + s`, then they hold at `w` for `i < N`. -/
theorem orbit_mem_left_reduce {f φ : ℂ → ℂ} {Dφ Df : Set ℂ} {w : ℂ} {s N : ℕ}
    (hAbel : ∀ z ∈ Dφ, z + 1 ∈ Dφ → φ z ∈ Df ∧ φ (z + 1) = f (φ z))
    (hray : ∀ i : ℕ, i ≤ s → (w - (s : ℂ)) + (i : ℂ) ∈ Dφ)
    (hmem : ∀ i : ℕ, i < N + s → f^[i] (φ (w - (s : ℂ))) ∈ Df) :
    ∀ i : ℕ, i < N → f^[i] (φ w) ∈ Df := by
  have hval : φ ((w - (s : ℂ)) + (s : ℂ)) = f^[s] (φ (w - (s : ℂ))) :=
    abel_iterate (fun z hz hz1 => (hAbel z hz hz1).2) (w - (s : ℂ)) s hray
  have hw : (w - (s : ℂ)) + (s : ℂ) = w := by ring
  rw [hw] at hval
  intro i hi
  have h1 : f^[i] (φ w) = f^[i] (f^[s] (φ (w - (s : ℂ)))) := by rw [← hval]
  rw [h1, ← Function.iterate_add_apply]
  exact hmem (i + s) (by omega)

/-- The value statement transfers the same way: `φ w = f^s (φ (w − s))`. -/
theorem phi_left_reduce {f φ : ℂ → ℂ} {Dφ Df : Set ℂ} {w : ℂ} {s : ℕ}
    (hAbel : ∀ z ∈ Dφ, z + 1 ∈ Dφ → φ z ∈ Df ∧ φ (z + 1) = f (φ z))
    (hray : ∀ i : ℕ, i ≤ s → (w - (s : ℂ)) + (i : ℂ) ∈ Dφ) :
    φ w = f^[s] (φ (w - (s : ℂ))) := by
  have hval : φ ((w - (s : ℂ)) + (s : ℂ)) = f^[s] (φ (w - (s : ℂ))) :=
    abel_iterate (fun z hz hz1 => (hAbel z hz hz1).2) (w - (s : ℂ)) s hray
  rwa [show (w - (s : ℂ)) + (s : ℂ) = w from by ring] at hval

end

end Work.Pert.pert2v2
