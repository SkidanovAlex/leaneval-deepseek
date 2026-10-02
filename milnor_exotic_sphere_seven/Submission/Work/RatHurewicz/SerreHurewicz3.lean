import Mathlib
import Submission.Work.RatHurewicz.SerreHurewicz
import Submission.Work.RatHurewicz.rationalHurewiczStable_of_range
import Submission.Work.RatHurewicz.range_of_rationalHurewiczStable
import Submission.Work.Drive.RationalHurewicz
import Submission.Work.Stems.HurewiczNeutral

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The rational Hurewicz theorem one degree short of the stable boundary

Area **RATHUREWICZ**.  The drive's contract comes in two forms
(`Submission/Work/Drive/RationalHurewicz.lean`):

* `Work.Drive.RationalHurewiczStable` — range `i + 1 ≤ 2k - 2` (the classical range for a
  `(k-1)`-connected space), and
* `Work.Drive.RationalHurewiczStable3` — range `i + 1 ≤ 2k - 3`, the weakening by one degree which
  is what area THOM actually consumes (`Work.Drive.rationalHurewiczStable3_of_stable` converts).

This module provides the *map form* of the second statement, in the vocabulary of this area (the
Hurewicz map `Work.Stems.hurewiczMapN` on homotopy groups), together with the two proved
equivalences with the drive's contract:

* `HurewiczModTorsionRange3` — the map form at range `n + 1 ≤ 2k - 3`;
* `HurewiczModTorsionRange3_of_range` — the full-range form implies it;
* `rationalHurewiczStable3_iff_range3` — it is equivalent to `Work.Drive.RationalHurewiczStable3`;
* `rationalHurewiczStable3_of_range` — the full-range map form implies the weak contract.

The equivalence `Work.Drive.rationalHurewiczStable3_of_stable` shows that a proof of
`Work.Drive.RationalHurewiczStable` also settles `Work.Drive.RationalHurewiczStable3`; the point of
the weaker contract is that a consumer (area THOM) only needs the one-short range, where the
top-degree `2k-2` — the genuinely stable degree — does not occur.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **The rational Hurewicz theorem in the stable range, one degree short.**  The statement of
`Work.RatHurewicz.HurewiczModTorsionRange` with the range hypothesis `n + 1 ≤ 2k - 2` replaced by
the strictly weaker `n + 1 ≤ 2k - 3`: for a `(k-1)`-connected space `X` (`k ≥ 2`) and a class
`a ∈ π_{n+1}(X,x₀)` whose Hurewicz image is of finite order, `a` is of finite order.

Equivalently it is the injectivity-modulo-torsion half of `π_i(X) ⊗ ℚ ≅ H_i(X;ℚ)` for
`i = n + 1 ≤ 2k - 3`; it is the exact mathematical content of
`Work.Drive.RationalHurewiczStable3` in the Hurewicz-map language
(`rationalHurewiczStable3_iff_range3`). -/
def HurewiczModTorsionRange3 : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (X : Type) [TopologicalSpace X] (x₀ : X),
    (∀ i < k, Subsingleton (HomotopyGroup (Fin i) X x₀)) →
    ∀ (n : ℕ), n + 1 ≤ 2 * k - 3 →
      ∀ a : HomotopyGroup (Fin (n + 1)) X x₀,
        (∃ N : ℕ, 0 < N ∧
            (N : ℤ) • Work.Stems.hurewiczMapN (n + 1)
              (Nat.succ_le_succ (Nat.zero_le n)) x₀ a = 0) →
          ∃ N : ℕ, 0 < N ∧ a ^ N = 1

/-- The full-range map form of the rational Hurewicz theorem implies the one-short form: the range
hypothesis `n + 1 ≤ 2k - 3` is stronger than `n + 1 ≤ 2k - 2`. -/
theorem HurewiczModTorsionRange3_of_range (h : HurewiczModTorsionRange) :
    HurewiczModTorsionRange3 :=
  fun k hk X _ x₀ hconn n hn a ha => h k hk X x₀ hconn n (by omega) a ha

/-- **The map form at range `n + 1 ≤ 2k - 3` implies the drive's contract
`Work.Drive.RationalHurewiczStable3`.**  Same proof as `rationalHurewiczStable_of_range`: the
contract is phrased on the cube-level Hurewicz class `Work.Stems.hurewiczChain`, the range form on
the induced map `Work.Stems.hurewiczMapN` of homotopy groups, and the two agree on the class of a
cube (`Work.Stems.hurewiczMapN_mk`). -/
theorem rationalHurewiczStable3_of_range3 (h : HurewiczModTorsionRange3) :
    Work.Drive.RationalHurewiczStable3 := by
  intro k hk X _ x₀ hconn i hi p hp
  refine h k hk X x₀ hconn i hi
    (show HomotopyGroup (Fin (i + 1)) X x₀ from Quotient.mk _ p) ?_
  obtain ⟨N, hN, hNp⟩ := hp
  exact ⟨N, hN, by rw [Work.Stems.hurewiczMapN_mk]; exact hNp⟩

/-- **The drive's contract `Work.Drive.RationalHurewiczStable3` implies the map form at range
`n + 1 ≤ 2k - 3`.**  Same proof as `range_of_rationalHurewiczStable`: apply the contract to a
representative cube `Quotient.out a` of the class, whose Hurewicz image is that of `a`
(`Work.Stems.hurewiczMapN_out`). -/
theorem range3_of_rationalHurewiczStable3 (h : Work.Drive.RationalHurewiczStable3) :
    HurewiczModTorsionRange3 := by
  intro k hk X _ x₀ hconn n hn a ha
  obtain ⟨N, hN, hNa⟩ := ha
  have hout := Work.Stems.hurewiczMapN_out (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀ a
  rw [hout] at hNa
  obtain ⟨M, hM, hMpow⟩ :=
    h k hk X x₀ hconn n hn (Quotient.out a) ⟨N, hN, hNa⟩
  exact ⟨M, hM, by rwa [← Quotient.out_eq a]⟩

/-- **The map form at range `2k - 3` is exactly the drive's contract
`Work.Drive.RationalHurewiczStable3`.** -/
theorem rationalHurewiczStable3_iff_range3 :
    HurewiczModTorsionRange3 ↔ Work.Drive.RationalHurewiczStable3 :=
  ⟨rationalHurewiczStable3_of_range3, range3_of_rationalHurewiczStable3⟩

/-- **The full-range map form implies the weak contract**: compose
`rationalHurewiczStable3_of_range3` with `HurewiczModTorsionRange3_of_range`. -/
theorem rationalHurewiczStable3_of_range (h : HurewiczModTorsionRange) :
    Work.Drive.RationalHurewiczStable3 :=
  rationalHurewiczStable3_of_range3 (HurewiczModTorsionRange3_of_range h)

end

end Work.RatHurewicz
