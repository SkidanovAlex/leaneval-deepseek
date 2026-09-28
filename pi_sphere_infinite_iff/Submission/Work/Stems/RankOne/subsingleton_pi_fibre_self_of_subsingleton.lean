import Mathlib
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.Stems.homotopyFibre_conn

/-!
# `π_{m+1}` of the homotopy fibre of a `π_{m+1}`-injective map whose `π_{m+2}` vanishes

Let `f : S^{m+1} → X` be a based map whose induced map `π_{m+1}(f)` on `π_{m+1}` is *injective*,
and suppose that `π_{m+2}(X) = 0` (`hvan`).  Then the homotopy fibre `F` of `f` has
`π_{m+1}(F) = 0`.

This is `Work.Stems.RankOne.subsingleton_pi_fibre_self` with the hypothesis
`π_j(X) = 0 for all j ≠ m + 1` weakened to the single vanishing statement `π_{m+2}(X) = 0`: in the
long exact sequence of the fibration `F → S^{m+1} → X`, namely

`π_{m+2}(X) →^{∂} π_{m+1}(F) →^{ι} π_{m+1}(S^{m+1}) →^{π_{m+1}(f)} π_{m+1}(X)`,

injectivity of `π_{m+1}(f)` forces `ι = 0`, hence `π_{m+1}(F) = ker ι = im ∂`, and `im ∂ = 0`
because `π_{m+2}(X) = 0`.  The vanishing of `π_{m+2}(X)` is the *only* vanishing of homotopy groups
of `X` that the argument uses.

This is the fibre input for the bottom cell of a rank-one space
(`Work.Stems.rankOne_bottomCell`), where precisely the two degrees `m+1` (injectivity) and `m+2`
(vanishing) of `X` are available.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems.RankOne

/-- **Triviality of `π_{m+1}` of the homotopy fibre of a `π_{m+1}`-injective map with
`π_{m+2}(X) = 0`.** -/
theorem subsingleton_pi_fibre_self_of_subsingleton {m : ℕ} (hm : 2 ≤ m) {X : Type} [TopologicalSpace X]
    (s₀ : Work.Serre.Sph (m + 1)) (f : C(Work.Serre.Sph (m + 1), X))
    (hvan : Subsingleton (HomotopyGroup (Fin (m + 2)) X (f s₀)))
    (hinj : Function.Injective (Work.StemsB.πmap f m s₀)) :
    Subsingleton (HomotopyGroup (Fin (m + 1)) (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) := by
  -- peel two successors off `m`, so that all the index arithmetic below is definitional
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  -- the two relevant stretches of the long exact sequence of the pair `(X, S^{k+3})`
  obtain ⟨_, d₁, _, _, h3₁, h4₁⟩ :=
    Work.RatHurewicz.pair_les f s₀ (k + 2) (by omega)
  obtain ⟨_, _, _, h2₂, _, _⟩ :=
    Work.RatHurewicz.pair_les f s₀ (k + 1) (by omega)
  -- the top-degree exactness at `π_{k+3}(S^{k+3})`: the image of `π_{k+3}(F)` lies in
  -- `ker π_{k+3}(f) = 0`
  have hι : ∀ y : HomotopyGroup (Fin (k + 3)) (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀),
      Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst f s₀) (k + 2)
        (Work.RatHurewicz.homotopyFibreBasepoint f s₀) y = 1 := by
    intro y
    have hker : Work.StemsB.πmap f (k + 2) s₀
        ((Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst f s₀) (k + 2)
          (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) y) = 1 :=
      (h2₂ _).mpr (Set.mem_range_self y)
    have hone : (Work.StemsB.πmap f (k + 2) s₀)
        (1 : HomotopyGroup (Fin (k + 2 + 1)) (Work.Serre.Sph (k + 2 + 1)) s₀) = 1 :=
      map_one _
    exact (hinj.eq_iff).mp (hker.trans hone.symm)
  -- the connecting map `π_{k+4}(X) → π_{k+3}(F)` is trivial, since `π_{k+4}(X) = 0`
  have hd : ∀ x : HomotopyGroup (Fin (k + 4)) X (f s₀), d₁ x = 1 := by
    intro x
    refine (h3₁ x).mpr ⟨1, ?_⟩
    rw [map_one]
    exact @Subsingleton.elim _ hvan _ _
  refine ⟨fun y z => ?_⟩
  have hy : y = 1 := by
    obtain ⟨x, hx⟩ := (h4₁ y).mp (hι y)
    rw [← hx, hd x]
  have hz : z = 1 := by
    obtain ⟨x, hx⟩ := (h4₁ z).mp (hι z)
    rw [← hx, hd x]
  rw [hy, hz]

end Work.Stems.RankOne
