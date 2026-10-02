import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.RationalHurewicz
import Submission.Work.Stems.Hurewicz
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Stems.rationalHurewiczStable_of_contract
import Submission.Work.Stems.sphereConnectivity

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The stable stems from the *one-short* rational Hurewicz theorem, plus Freudenthal

Area STEMS' contract `Work.Drive.StableStemsTorsion` (every `π_{n+i+1}(Sⁿ)`, `i ≤ 7`, `n ≥ i + 3`, is
torsion) follows from the **weaker** contract `Work.Drive.RationalHurewiczStable3` (whose range
stops one degree short of the boundary, `i + 1 ≤ 2k - 3`) and Freudenthal's suspension theorem.

This is the link that the blueprint's `S2` needs and that the drive's `RationalHurewiczStable`
(whose *top* degree `2k-2` is the genuinely stable case) is not needed for: the top-degree case of
the stems `π_{2n-2}(Sⁿ)` is obtained by suspending one step up, where it *is* the boundary degree
`2k-3` of `S^{n+1}`.

Concretely, for the target case `(n,i)`:

* if `i + 4 ≤ n` (`n + i + 1 ≤ 2n - 3`), apply `h3` to `X = Sⁿ` with `k = n`: the Hurewicz class
  vanishes because `H_{n+i+1}(Sⁿ;ℤ) = 0`;
* if `i + 3 = n`, suspend: `FreudenthalTorsionTransfer n i` reduces torsion of `π_{n+i+1}(Sⁿ)` to
  torsion of `π_{n+i+2}(S^{n+1})` (the suspension isomorphism), and that is `π_{2n-1}(S^{n+1})`,
  which is the boundary degree `2(n+1) - 3` of `h3` at `X = S^{n+1}`, `k = n + 1`.

Everything is phrased in the model `Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`, which is
*definitionally* the model of both `Work.Drive.RationalHurewiczStable3` and
`Work.Serre.SerreFreudenthal`, so no comparison of sphere models is needed.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

/-- **Freudenthal's suspension transfer, in the form the stems need.**  This is
`Work.Serre.SerreFreudenthal` of the subproject SERRE with the same sphere model
(`Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`, so that `sphere n` *is* their `Sph n`); the
two `Prop`s differ only in the way the degree is written (`n + i + 2` versus `(n+1+i) + 1`, which
`Nat` arithmetic identifies — they are *logically* equivalent, not syntactically equal).

For `1 ≤ n` and `i + 3 ≤ n`, torsion of `π_{n+i+2}(S^{n+1})` implies torsion of `π_{n+i+1}(Sⁿ)`:
the suspension `π_{n+i+1}(Sⁿ) → π_{n+i+2}(S^{n+1})` is an isomorphism in the range
`n + i + 1 ≤ 2n - 2`, i.e. `i + 3 ≤ n` (derivable from the now-proved
`Work.RatHurewicz.homotopyExcision` via the two-disc model of the sphere). -/
def FreudenthalTorsionTransfer : Prop :=
  ∀ (n i : ℕ), 1 ≤ n → i + 3 ≤ n →
    (∀ y₀ : sphere (n + 1), ∀ β : HomotopyGroup (Fin (n + i + 2)) (sphere (n + 1)) y₀,
      ∃ N : ℕ, 0 < N ∧ β ^ N = 1) →
    ∀ x₀ : sphere n, ∀ α : HomotopyGroup (Fin (n + i + 1)) (sphere n) x₀,
      ∃ N : ℕ, 0 < N ∧ α ^ N = 1

/-- **The stable stems follow from the one-short rational Hurewicz theorem and Freudenthal.** -/
theorem stableStemsTorsion_of_stable3 (h3 : Work.Drive.RationalHurewiczStable3)
    (hF : FreudenthalTorsionTransfer) : Work.Drive.StableStemsTorsion := by
  intro i hi n hn x₀ α
  -- the connectivity of `Sⁿ`
  have hconn : ∀ j < n, Subsingleton (HomotopyGroup (Fin j) (sphere n) x₀) :=
    fun j hj => sphereConnectivity n j hj x₀
  -- the Hurewicz class of a cube vanishes in every degree `d > n` (`H_d(Sⁿ;ℤ) = 0`)
  have hzero : ∀ (d : ℕ) (hd : n < d) (q : Ω^ (Fin d) (sphere n) x₀),
      hurewiczChain d (by omega) x₀ q = 0 := by
    intro d hd q
    haveI : Subsingleton
        ((Work.Cohomology.singularChains ℤ (TopCat.of (sphere n))).homology d) :=
      ModuleCat.subsingleton_of_isZero
        (Work.Cohomology.sphereHomologyZero n d (by omega) (by omega) (by omega))
    exact Subsingleton.elim _ _
  by_cases hle : i + 4 ≤ n
  · -- interior case: `n + i + 1 ≤ 2n - 3`, so `h3` at `Sⁿ` applies directly
    have hn2 : 2 ≤ n := by omega
    induction α using Quotient.inductionOn with
    | h p =>
      obtain ⟨N, hN, hpow⟩ := h3 n hn2 (sphere n) x₀ hconn (n + i) (by omega) p
        ⟨1, Nat.one_pos, by simp [hzero (n + i + 1) (by omega) p]⟩
      exact ⟨N, hN, hpow⟩
  · -- boundary case: `n = i + 3`; suspend one step, where the degree is `2k - 3`
    have hn_eq : n = i + 3 := by omega
    have htop : ∀ y₀ : sphere (n + 1),
        ∀ β : HomotopyGroup (Fin (n + i + 2)) (sphere (n + 1)) y₀,
          ∃ N : ℕ, 0 < N ∧ β ^ N = 1 := by
      intro y₀ β
      have hconn' : ∀ j < n + 1, Subsingleton (HomotopyGroup (Fin j) (sphere (n + 1)) y₀) :=
        fun j hj => sphereConnectivity (n + 1) j hj y₀
      have hzero' : ∀ q : Ω^ (Fin (n + i + 2)) (sphere (n + 1)) y₀,
          hurewiczChain (n + i + 2) (by omega) y₀ q = 0 := by
        intro q
        haveI : Subsingleton
            ((Work.Cohomology.singularChains ℤ (TopCat.of (sphere (n + 1)))).homology
              (n + i + 2)) :=
          ModuleCat.subsingleton_of_isZero
            (Work.Cohomology.sphereHomologyZero (n + 1) (n + i + 2) (by omega) (by omega)
              (by omega))
        exact Subsingleton.elim _ _
      induction β using Quotient.inductionOn with
      | h p =>
        obtain ⟨N, hN, hpow⟩ := h3 (n + 1) (by omega) (sphere (n + 1)) y₀ hconn' (n + i + 1)
          (by omega) p ⟨1, Nat.one_pos, by simp [hzero' p]⟩
        exact ⟨N, hN, hpow⟩
    exact hF n i (by omega) (by omega) htop x₀ α

end

end Work.Stems
