import Mathlib
import Submission.Work.RatHurewicz.exists_killed_tower
import Submission.Work.RatHurewicz.pair_les

/-!
# The truncation tower, in the form the stem induction consumes

`Work.RatHurewicz.exists_killed_tower` produces, for `2 ≤ k ≤ N`, a map `inc : X → Z` whose homotopy
fibre is `k`-connected and which kills `π_j` for `k < j ≤ N`.  This module adds the identification of
the homotopy groups of `X` with those of that fibre in the range above `k`: for `k < m ≤ N` the map
`π_m(homotopyFibre inc x₀) → π_m(X)` induced by the projection is a bijection, so that the induction
of the rational Hurewicz statement can be run on the fibre (which is `k`-connected, one connectivity
class higher than `X`).

The identification is the exactness of the long exact sequence of the pair
(`Work.RatHurewicz.pair_les`) at `π_m`: `π_m(F) → π_m(X)` is surjective as soon as `π_m(Z)` vanishes
and injective as soon as `π_{m+1}(Z)` vanishes.  The tower is therefore instantiated at `N + 1`, so
that both vanishings are available up to `m = N`.

The index of the map is written `m - 2 + 1` (the index produced by `pair_les` at parameter `m - 2`,
whose conclusions concern `Work.StemsB.πmap … (k + 1)`) rather than the propositionally equal `m - 1`;
the two are equal because `k < m` with `k ≥ 2` gives `3 ≤ m`.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **The truncation tower, with the identification of `π_m` of the fibre.** -/
theorem tower_fibre_pi_bijective (X : Type) [TopologicalSpace X] (x₀ : X) (k N : ℕ) (hk : 2 ≤ k)
    (hN : k ≤ N) :
    ∃ (Z : Type) (_ : TopologicalSpace Z) (inc : C(X, Z)),
      (∀ j : ℕ, j ≤ k → Subsingleton (RelHomotopyGroup inc x₀ j)) ∧
        (∀ j : ℕ, k < j → j ≤ N → Subsingleton (HomotopyGroup (Fin j) Z (inc x₀))) ∧
        (∀ m : ℕ, k < m → m ≤ N →
          Function.Bijective (Work.StemsB.πmap (homotopyFibreFst inc x₀) (m - 2 + 1)
            (homotopyFibreBasepoint inc x₀))) := by
  obtain ⟨Z, tZ, inc, hconn, hkill⟩ := exists_killed_tower X x₀ k (N + 1) hk (by omega)
  letI := tZ
  refine ⟨Z, tZ, inc, hconn, fun j hj hjN => hkill j hj (by omega), ?_⟩
  intro m hm hmN
  have hkm : 1 ≤ m - 2 := by omega
  obtain ⟨del, d, hdel, h2, h3, h4⟩ := pair_les inc x₀ (m - 2) hkm
  have hkill2 : Subsingleton (HomotopyGroup (Fin (m - 2 + 2)) Z (inc x₀)) :=
    hkill (m - 2 + 2) (by omega) (by omega)
  have hkill3 : Subsingleton (HomotopyGroup (Fin (m - 2 + 3)) Z (inc x₀)) :=
    hkill (m - 2 + 3) (by omega) (by omega)
  constructor
  · intro a b hab
    have hker : Work.StemsB.πmap (homotopyFibreFst inc x₀) (m - 2 + 1)
        (homotopyFibreBasepoint inc x₀) (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    obtain ⟨u, hu⟩ := (hdel (a * b⁻¹)).mp hker
    have hu1 : u = 1 := hkill3.elim u 1
    have hab1 : a * b⁻¹ = 1 := by
      rw [← hu, hu1, map_one]
    exact mul_inv_eq_one.mp hab1
  · intro x
    obtain ⟨a, ha⟩ := (h2 x).mp (hkill2.elim
      (Work.StemsB.πmap inc (m - 2 + 1) x₀ x) 1)
    exact ⟨a, ha⟩

end

end Work.RatHurewicz
