import Mathlib
import Submission.Work.RatHurewicz.exists_killed_tower
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.tower_fibre_pi_bijective

/-!
# The homotopy fibre of a truncation step carries the *same* `π_m` as the base

`Work.RatHurewicz.TowerState X x₀ k s` records a space `Y`, an embedding `incl : X → Y` and the
killing of `π_j(Y)` for `k < j ≤ k + s`.  This module proves the precise structural statement used
by the stem induction: in the range where both `π_{m+1}(Y)` and `π_{m+2}(Y)` have already been
killed, the projection of the homotopy fibre induces an **isomorphism of groups**
`π_{m+1}(homotopyFibre incl x₀) ≃* π_{m+1}(X)` (not merely a bijection of sets).

The mathematics is the long exact sequence of the pair `(Y, X)` in the form of
`Work.RatHurewicz.pair_les`, applied with parameter `m - 1`:

`π_{m+2}(Y) → π_{m+1}(F) → π_{m+1}(X) → π_{m+1}(Y)`,

which is exact at `π_{m+1}(F)` and at `π_{m+1}(X)`.  Since `π_{m+1}(Y) = π_{m+2}(Y) = 0` by the
`killed` record of the tower, the middle map `π_{m+1}(F) → π_{m+1}(X)` is injective (its kernel is
the image of the trivial group `π_{m+2}(Y)`) and surjective (its range is the kernel of the trivial
map `π_{m+1}(X) → π_{m+1}(Y)`), hence an isomorphism.

The abstract form of the argument is isolated as `πmap_homotopyFibreFst_bijective`, which needs only
the two vanishings of `π_{N+1}` and `π_{N+2}` of the *codomain*; the statement about a tower state is
then an immediate instance.
-/

open scoped Topology

namespace Work.FGThm

noncomputable section

/-- **The projection of a homotopy fibre is an isomorphism on `π_{N+1}` once `π_{N+1}` and
`π_{N+2}` of the target vanish.**

For `i : C(A, X)` with base point `a₀ : A` and `2 ≤ N`, if `π_{N+1}(X, i a₀)` and `π_{N+2}(X, i a₀)`
are trivial, then the map `π_{N+1}(homotopyFibre i a₀) → π_{N+1}(A)` induced by the first projection
`homotopyFibreFst` is a bijection.  This is the exactness of the long exact sequence of the pair
`Work.RatHurewicz.pair_les` at the two relevant terms. -/
theorem πmap_homotopyFibreFst_bijective {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (a₀ : A) (N : ℕ) (hN : 2 ≤ N)
    (hkill1 : Subsingleton (HomotopyGroup (Fin (N + 1)) X (i a₀)))
    (hkill2 : Subsingleton (HomotopyGroup (Fin (N + 2)) X (i a₀))) :
    Function.Bijective (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a₀) N
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) := by
  -- Write `N = M + 1` so that the parameter of `pair_les` is `M` and no index arithmetic remains.
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨del, _d, hdel, h2, _h3, _h4⟩ :=
    Work.RatHurewicz.pair_les i a₀ M (by omega)
  -- `hdel : Function.MulExact del (πmap (homotopyFibreFst i a₀) (M + 1) _)`
  -- `h2   : Function.MulExact (πmap (homotopyFibreFst i a₀) (M + 1) _) (πmap i (M + 1) a₀)`
  constructor
  · -- Injectivity: the kernel of the projection is the image of the connecting map `del`, whose
    -- source `π_{M+3}(X) = π_{N+2}(X)` is trivial.
    intro a b hab
    have hker : (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a₀) (M + 1)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    obtain ⟨u, hu⟩ := (hdel (a * b⁻¹)).mp hker
    have hu1 : u = 1 := Subsingleton.elim u 1
    have hab1 : a * b⁻¹ = 1 := by rw [← hu, hu1, map_one]
    exact mul_inv_eq_one.mp hab1
  · -- Surjectivity: the range of the projection is the kernel of `πmap i (M+1) a₀`, which takes
    -- values in the trivial group `π_{M+2}(X) = π_{N+1}(X)`.
    intro x
    have h1 : (Work.StemsB.πmap i (M + 1) a₀) x = 1 := Subsingleton.elim _ _
    exact Set.mem_range.mp ((h2 x).mp h1)

/-- **The homotopy fibre of a truncation stage has the same `π_{m+1}` as the base.**

Given a stage `st : TowerState X x₀ k s` of the truncation tower and `m` in the range
`k ≤ m ≤ k + s - 2` (encoded as `k < m + 1` and `m + 2 ≤ k + s`), both `π_{m+1}(st.Y)` and
`π_{m+2}(st.Y)` have been killed, so the projection of the homotopy fibre of `st.incl` induces an
isomorphism of groups
`π_{m+1}(homotopyFibre st.incl x₀) ≃* π_{m+1}(X)`. -/
theorem towerState_fibre_pi_mulEquiv {X : Type} [TopologicalSpace X] {x₀ : X} {k s m : ℕ}
    (hk : 2 ≤ k) (st : Work.RatHurewicz.TowerState X x₀ k s) (hm : k < m + 1) (hm2 : m + 2 ≤ k + s) :
    Nonempty (HomotopyGroup (Fin (m + 1)) (Work.RatHurewicz.homotopyFibre st.incl x₀)
        (Work.RatHurewicz.homotopyFibreBasepoint st.incl x₀) ≃*
      HomotopyGroup (Fin (m + 1)) X x₀) := by
  have hmge : 2 ≤ m := by omega
  have hkill1 : Subsingleton (HomotopyGroup (Fin (m + 1)) st.Y (st.incl x₀)) :=
    st.killed (m + 1) (by omega) (by omega)
  have hkill2 : Subsingleton (HomotopyGroup (Fin (m + 2)) st.Y (st.incl x₀)) :=
    st.killed (m + 2) (by omega) (by omega)
  exact ⟨MulEquiv.ofBijective _
    (πmap_homotopyFibreFst_bijective st.incl x₀ m hmge hkill1 hkill2)⟩

end

end Work.FGThm
