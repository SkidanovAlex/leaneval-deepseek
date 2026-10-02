import Mathlib
import Submission.Work.Gen.CruxDefs
import Submission.Work.Gen.cupChern_zeta_lhTerm
import Submission.Work.Gen.LhCalc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Gen

open Work.TangentClasses Work.Thom in
/-- **Multiplying a Leray–Hirsch summand by `ζ` on the *right* shifts the index.**
`Work.Gen.cupChern_zeta_lhTerm` is the same statement with `ζ` on the left; the two are exchanged
by the commutativity of the graded product in even degrees
(`Work.Whitney.ChernRel.cupChern_comm`), the two degree casts cancelling.  Since
`ζ ⌣ lhTerm Z k i x = π^*(x) ⌣ ζ^{i+1}` is the summand of `lhMap Z (k+1)` at the index `i + 1`,
this is the elementary step of the multiplication by `ζ` on the free `H^*(B)`-module
`H^*(P(Z))`. -/
theorem cupChern_lhTerm_zeta {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    {k : ℕ} (i : Fin m) (hi : (i : ℕ) ≤ k) (j : Fin m) (hj : (j : ℕ) = (i : ℕ) + 1)
    (x : Coh ℤ (2 * (k - (i : ℕ))) B) :
    Work.Whitney.cupChern k 1 (Work.LerayHirsch.lhTerm Z k ⟨i, hi⟩ x) (Work.LerayHirsch.zeta Z)
      = Work.LerayHirsch.lhTerm Z (k + 1) ⟨j, by omega⟩
          (cohTransport (by omega : 2 * (k - (i : ℕ)) = 2 * ((k + 1) - (j : ℕ))) x) := by
  rw [Work.Whitney.ChernRel.cupChern_comm]
  rw [Work.Gen.cupChern_zeta_lhTerm Z i j hi hj x]
  rw [Work.Whitney.cohTransport_trans]
  exact Work.Thom.cohTransport_self _ _

open Work.TangentClasses Work.Thom in
/-- **The double `ζ`-shift of a Leray–Hirsch summand, away from the top index.**  Multiplying the
summand `π^*(y) ⌣ ζ^j` of `lhMap W (n-1)` twice by `ζ` gives the summand of `lhMap W (n+1)` at the
index `j + 2`, with the same coefficient (transported along the degree equality
`(n-1) - j = (n+1) - (j+2)`).  Both sides lie in `H^{2(n+1)}(P(W))`, so no outer transport is
needed; the inner transport `2*((n-1)+1) = 2*n` merely matches the degree argument of the second
`cupChern`.  There is no index overflow because `j + 2 ≤ n` (equivalently `j ≠ n-1`). -/
theorem cupChern_lhTerm_zeta2 {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {n : ℕ}
    (hn : 1 ≤ n) (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)
    (j j2 : Fin (n + 1)) (hj : (j : ℕ) ≤ n - 1) (hj2 : (j2 : ℕ) = (j : ℕ) + 2)
    (y : Work.Thom.Coh ℤ (2 * ((n - 1) - (j : ℕ))) B) :
    Work.Whitney.cupChern n 1
        (Work.Thom.cohTransport (by omega : 2 * ((n - 1) + 1) = 2 * n)
          (Work.Whitney.cupChern (n - 1) 1
            (Work.LerayHirsch.lhTerm W (n - 1) ⟨j, hj⟩ y) (Work.LerayHirsch.zeta W)))
        (Work.LerayHirsch.zeta W)
      = Work.LerayHirsch.lhTerm W (n + 1) ⟨j2, by omega⟩
          (Work.Thom.cohTransport (by omega : 2 * ((n - 1) - (j : ℕ)) = 2 * ((n + 1) - (j2 : ℕ))) y) := by
  -- Since `hn : 1 ≤ n`, write `n = k + 1`; the reducible identity `(k+1) - 1 = k` then makes the
  -- two index sets of `lhTerm` (`n - 1` and `n`) syntactically the same, so that the index shift
  -- lemma can be applied twice in a row.
  rcases n with _ | k
  · omega
  -- Step 1: the outer transport `2 * ((n-1)+1) = 2 * n` is the identity (the two degrees are
  -- definitionally equal after `n = k + 1`), so it can be discarded.
  rw [Work.Gen.cupChern_cast_left]
  rw [Work.Thom.cohTransport_self]
  -- `j1` is the intermediate index `j + 1`.
  obtain ⟨j1, hj1val⟩ : ∃ j1 : Fin (k + 1 + 1), (j1 : ℕ) = (j : ℕ) + 1 :=
    ⟨⟨(j : ℕ) + 1, by omega⟩, rfl⟩
  -- Step 2: first shift, from the index `j` in `lhMap W (n-1)` to the index `j + 1` in
  -- `lhMap W n`.
  rw [cupChern_lhTerm_zeta W j hj j1 hj1val y]
  -- Step 3: second shift, from the index `j + 1` in `lhMap W n` to the index `j + 2` in
  -- `lhMap W (n+1)` (the given index `j2`, since `(j2 : ℕ) = (j : ℕ) + 2`).
  rw [cupChern_lhTerm_zeta W j1 (by omega) j2 (by omega) _]
  -- The two coefficient transports compose to the transport of the statement.
  rw [Work.Whitney.cohTransport_trans]
  rfl

end Work.Gen
