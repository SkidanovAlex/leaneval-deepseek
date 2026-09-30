import Mathlib
import Submission.Work.RatHurewicz.SerreHurewicz
import Submission.Work.Drive.RationalHurewicz
import Submission.Work.Drive.Interfaces
import Submission.Work.Stems.Hurewicz
import Submission.Work.Cohomology.sphereVanishing

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option synthInstance.maxHeartbeats 400000

/-!
# The contract for spheres: the stable stems are torsion

The corollary of the drive's contract for `Sⁿ` (`Work.Drive.StableStemsTorsion`, the target of the
area STEMS), as requested of this area.  See `README.md` §4.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **The contract for spheres: the stable stems are torsion.**  The rational Hurewicz result in
the stable range, applied to `X = Sⁿ` (which is `(n-1)`-connected by `SphereConnected`) in degree
`n + i + 1 ≤ 2n - 2`, gives that every class in `π_{n+i+1}(Sⁿ)` is of finite order, because
`H_{n+i+1}(Sⁿ;ℤ) = 0` (`n + i + 1 ∉ {0, n}`).  This is the corollary for the area STEMS
(`Work.Drive.StableStemsTorsion`). -/
theorem stableStemsTorsion_of_rationalHurewiczStable (h : Work.Drive.RationalHurewiczStable)
    (hc : SphereConnected) : Work.Drive.StableStemsTorsion := by
  intro i _hi n hn x₀ α
  have hn1 : 1 ≤ n := by omega
  obtain ⟨p, hp⟩ := Quotient.exists_rep α
  have hprem : ∃ N : ℕ, 0 < N ∧ (N : ℤ) •
      Work.Stems.hurewiczChain (n + i + 1) (Nat.succ_le_succ (Nat.zero_le (n + i))) x₀ p = 0 := by
    refine ⟨1, one_pos, ?_⟩
    have h1 : ((1 : ℕ) : ℤ) = 1 := by norm_num
    rw [h1, one_zsmul]
    have hzero : CategoryTheory.Limits.IsZero
        ((Work.Cohomology.singularChains ℤ
          (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))).homology
            (n + i + 1)) :=
      Work.Cohomology.sphereVanishing n (n + i + 1) hn1 (by omega) (by omega)
    exact (ModuleCat.subsingleton_of_isZero hzero).elim _ _
  obtain ⟨N, hN, hNp⟩ := h n (by omega)
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x₀
      (fun j hj => hc n hn1 x₀ j hj) (n + i) (by omega) p hprem
  exact ⟨N, hN, by rw [← hp]; exact hNp⟩

end

end Work.RatHurewicz
