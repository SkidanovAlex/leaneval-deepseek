import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.RationalHurewicz
import Submission.Work.Cohomology.sphereHomologyZero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.Drive.StableStemsTorsion` from the rational Hurewicz theorem in the stable range

This file contains the reduction of the area contract `Work.Drive.StableStemsTorsion` (Serre: the
stable stems `π_{n+j}(Sⁿ)`, `1 ≤ j ≤ 8`, are torsion) to

* the shared contract `Work.Drive.RationalHurewiczStable`
  (`Submission/Work/Drive/RationalHurewicz.lean`; the injectivity half of the rational Hurewicz
  theorem, proved by the subproject `Submission/Work/RatHurewicz/`), and
* the connectivity of spheres, `SphereConnectivity` below (`πᵢ(Sⁿ) = 0` for `i < n`).

The argument is the classical one: apply the shared contract to `X = Sⁿ` with `k = n`.  Its
hypothesis is exactly `πᵢ(Sⁿ) = 0` for `i < n`, its degree range `d ≤ 2k - 2 = 2n - 2` covers the
stable range `n + 1 ≤ d ≤ 2n - 2`, and its conclusion is what we need *provided* the Hurewicz class
of the representative is zero: for `n < d` the integral homology `H_d(Sⁿ;ℤ)` vanishes
(`Work.Cohomology.sphereHomologyZero`), so the hypothesis of the injectivity statement is automatic
and every class in `π_d(Sⁿ)` is of finite order.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

/-- **Connectivity of spheres**: `πᵢ(Sⁿ) = 0` for `i < n` (including `i = 0`, i.e. path
connectedness).  This is the classical statement that `Sⁿ` is `(n-1)`-connected; it is the
hypothesis of `Work.Drive.RationalHurewiczStable` at `X = Sⁿ`, `k = n`. -/
def SphereConnectivity : Prop :=
  ∀ (n i : ℕ), i < n → ∀ x₀ : Work.Stems.sphere n,
    Subsingleton (HomotopyGroup (Fin i) (Work.Stems.sphere n) x₀)

/-- **The stable stems are torsion, from the rational Hurewicz theorem in the stable range.**

Applied to `X = Sⁿ` with `k = n` and degree `n + i + 1 ≤ 2n - 2`: the Hurewicz class of a class in
`π_{n+i+1}(Sⁿ)` lies in `H_{n+i+1}(Sⁿ;ℤ) = 0`, hence is zero, hence the class is of finite order. -/
theorem stableStemsTorsion_of_rationalHurewiczStable (h : Work.Drive.RationalHurewiczStable)
    (hc : SphereConnectivity) : Work.Drive.StableStemsTorsion := by
  intro i hi n hn x₀ α
  have hn2 : 2 ≤ n := by omega
  -- the connectivity hypothesis of the shared contract, at `k = n`
  have hconn : ∀ j < n, Subsingleton (HomotopyGroup (Fin j) (Work.Stems.sphere n) x₀) :=
    fun j hj => hc n j hj x₀
  -- the Hurewicz class of any representative vanishes: `H_{n+i+1}(Sⁿ;ℤ) = 0`
  have hzero : ∀ q : Ω^ (Fin (n + i + 1)) (Work.Stems.sphere n) x₀,
      Work.Stems.hurewiczChain (n + i + 1) (Nat.succ_le_succ (Nat.zero_le (n + i))) x₀ q = 0 := by
    intro q
    haveI : Subsingleton
        ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Stems.sphere n))).homology
          (n + i + 1)) :=
      ModuleCat.subsingleton_of_isZero
        (Work.Cohomology.sphereHomologyZero n (n + i + 1) (by omega) (by omega) (by omega))
    exact Subsingleton.elim _ _
  induction α using Quotient.inductionOn with
  | h p =>
    obtain ⟨N, hN, hpow⟩ := h n hn2 (Work.Stems.sphere n) x₀ hconn (n + i) (by omega) p
      ⟨1, Nat.one_pos, by simp [hzero p]⟩
    exact ⟨N, hN, hpow⟩
end

end Work.Stems
