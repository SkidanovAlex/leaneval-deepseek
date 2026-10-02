import Mathlib
import Submission.Work.RatHurewicz.SerreHurewicz
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.hurewiczKerTorsionFirstDegree
import Submission.Work.Stems.HurewiczMap
import Submission.Work.Stems.HurewiczNeutralAgree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Hurewicz map modulo torsion in the first non-vanishing degree

This file proves `Work.RatHurewicz.hurewiczModTorsionFirstDegree` (the proposition
`Work.RatHurewicz.HurewiczModTorsionFirstDegree` of `SerreHurewicz.lean`), the base case of the
inductive proof of the rational Hurewicz statement in the stable range.  See
`Submission/Work/RatHurewicz/ROUTE_hurewicz.md` for the route (Hutchings' elementary cubical proof
of the Hurewicz result, which is fully within reach of this workspace's API and needs neither CW
complexes nor homotopy excision nor a spectral sequence).

The mathematical content is the hypothesis-free form of the statement, proved in the module
`Submission/Work/RatHurewicz/hurewiczKerTorsionFirstDegree.lean`: a class in the first
non-vanishing homotopy degree whose Hurewicz image is *zero* is trivial.  What is proved *here* is
the reduction of the requested statement to that form: the Hurewicz map is additive
(`Work.Stems.hurewiczMap_mul`, via `Work.Stems.hurewiczMapN_eq_hurewiczMap`), so
`hurewiczMapN (m+1) … x₀ (a^N) = N • hurewiczMapN (m+1) … x₀ a`, and a class whose Hurewicz image is
of finite order can be replaced by a power whose Hurewicz image is zero. -/

namespace Work.RatHurewicz

/-- **The `N`-th power of a class has `N` times the Hurewicz image.**  This is the form of
additivity of the Hurewicz map that the reduction needs: it is `N • h(a) = h(a^N)`, proved by
induction on `N` from `Work.Stems.hurewiczMap_mul` (and `Work.Stems.hurewiczMap_one` at `N = 0`),
transported to the fork-neutral map `Work.Stems.hurewiczMapN` by
`Work.Stems.hurewiczMapN_eq_hurewiczMap`.-/
theorem hurewiczModTorsionFirstDegree_pow_aux (m : ℕ) (X : Type) [TopologicalSpace X] (x₀ : X)
    (a : HomotopyGroup (Fin (m + 1)) X x₀) (N : ℕ) :
    Work.Stems.hurewiczMapN (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) x₀ (a ^ N) =
      (N : ℤ) • Work.Stems.hurewiczMapN (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) x₀ a := by
  have h1 : Work.Stems.hurewiczMapN (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) x₀ (a ^ N) =
      N • Work.Stems.hurewiczMapN (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) x₀ a := by
    have h2 := map_nsmul (Work.Stems.hurewiczHom m x₀) N (Additive.ofMul a)
    rw [← ofMul_pow] at h2
    exact h2
  rw [h1]
  simp

/-- **The requested statement follows from its hypothesis-free form.**  Given the statement
`H` that a class in the first non-vanishing degree whose Hurewicz image is *zero* is trivial (the
Hurewicz result modulo torsion, in the sharper "kernel = 0" form), the torsion form follows: a
class `a` with `N • h(a) = 0` has `h(a^N) = N • h(a) = 0`, so `a^N` is trivial, hence `a` is
torsion. -/
theorem hurewiczModTorsionFirstDegree_of_ker_torsion
    (H : ∀ (m : ℕ), 1 ≤ m → ∀ (X : Type) [TopologicalSpace X] (x₀ : X),
      (∀ i < m + 1, Subsingleton (HomotopyGroup (Fin i) X x₀)) →
        ∀ a : HomotopyGroup (Fin (m + 1)) X x₀,
          Work.Stems.hurewiczMapN (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) x₀ a = 0 →
            ∃ N : ℕ, 0 < N ∧ a ^ N = 1) :
    Work.RatHurewicz.HurewiczModTorsionFirstDegree := by
  intro m hm X _ x₀ hconn a ha
  obtain ⟨N, hN, hNa⟩ := ha
  have hzero :
      Work.Stems.hurewiczMapN (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) x₀ (a ^ N) = 0 := by
    rw [hurewiczModTorsionFirstDegree_pow_aux, hNa]
  obtain ⟨M, hM, hM1⟩ := H m hm X x₀ hconn (a ^ N) hzero
  exact ⟨N * M, Nat.mul_pos hN hM, by rw [pow_mul]; exact hM1⟩

/-- **The classical Hurewicz statement modulo torsion in the first non-vanishing degree.**  The
proposition `Work.RatHurewicz.HurewiczModTorsionFirstDegree`
(`Submission/Work/RatHurewicz/SerreHurewicz.lean`) states: for `m ≥ 1` and a space `X` whose
homotopy groups `π_i(X,x₀)`, `i < m+1`, all vanish, the kernel of the Hurewicz map
`π_{m+1}(X,x₀) → H_{m+1}(X;ℤ)` consists of torsion elements — i.e. a class in the first
non-vanishing homotopy degree whose Hurewicz image has finite order has finite order.  Classically
the Hurewicz map is an isomorphism in this degree (Hatcher 4.32 / the absolute Hurewicz result); the
torsion form recorded here is the base case of the inductive proof of the rational Hurewicz
statement in the stable range (`Work.Drive.RationalHurewiczStable3`, one degree short of the
boundary).

The cubical Hurewicz map and its additivity and naturality are `Work.Stems.hurewiczMapN`
(`HurewiczNeutral.lean`), `Work.Stems.hurewiczChain_transAt`, `Work.Stems.hurewiczMap_mul`; the
relative homotopy groups and their long exact sequence (the classical proof's tool, applied to the
pair `(X, {x₀})`) are `Work.RatHurewicz.RelHomotopyGroup` and `Work.RatHurewicz.pair_les`, with
exactness consequences in `LESConsequences.lean`; the singular homology chapter
`Submission/Work/Cohomology/` supplies the homological side. -/
theorem hurewiczModTorsionFirstDegree : Work.RatHurewicz.HurewiczModTorsionFirstDegree :=
  hurewiczModTorsionFirstDegree_of_ker_torsion hurewiczKerTorsionFirstDegree

end Work.RatHurewicz
