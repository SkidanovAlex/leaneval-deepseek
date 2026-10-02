import Mathlib
import Submission.Work.Gen.CruxDefs
import Submission.Work.Gen.cupChern_zeta_lhTerm
import Submission.Work.Gen.cupChern_zero_lhMap
import Submission.Work.Gen.LhCalc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000

namespace Work.Gen

open Work.TangentClasses Work.Thom in
/-- **The double `ζ`-shift of the top summand of a Leray–Hirsch decomposition, in the abstract.**
With `zPow z j = z^j` the powers of a degree-`2` class (`Work.Whitney.ChernRel.zPow`) and
`cupChern a b u v = u ⌣ v` the graded product in the degrees `2a`, `2b`, the top summand
`π^*(Y) ⌣ z^j = cupChern 0 j Y (zPow z j)` — the shape in which `Work.LerayHirsch.lhTerm` produces
the summand at the top index — satisfies, after multiplying twice by `z`, the identity
`z ⌣ (z ⌣ (Y ⌣ z^j)) = Y ⌣ z^{j+2}` of the graded product (associativity, with the intermediate
degree casts made explicit).  The two sides have degrees `2*(((0+j)+1)+1)` and `2*(0+((j+1)+1))`,
which are equal but not definitionally equal, so the transport is the outer `cohTransport`. -/
theorem cupChern_zPow_top_doubleShift_aux {P : Type} [TopologicalSpace P] (j : ℕ)
    (Y : Coh ℤ 0 P) (z : Coh ℤ 2 P) :
    Work.Whitney.cupChern ((0+j)+1) 1
        (Work.Whitney.cupChern (0+j) 1
          (Work.Whitney.cupChern 0 j Y (Work.Whitney.ChernRel.zPow z j)) z) z
      = Work.Thom.cohTransport (by omega : 2 * (0 + ((j+1)+1)) = 2 * (((0+j)+1)+1))
          (Work.Whitney.cupChern 0 ((j+1)+1) Y (Work.Whitney.ChernRel.zPow z ((j+1)+1))) := by
  rw [Work.Gen.cupChern_assoc 0 j 1 Y (Work.Whitney.ChernRel.zPow z j) z]
  rw [Work.Gen.cupChern_cast_left]
  rw [Work.Gen.cupChern_assoc 0 (j+1) 1 Y
        (Work.Whitney.cupChern j 1 (Work.Whitney.ChernRel.zPow z j) z) z]
  rw [Work.Whitney.cohTransport_trans]
  exact Work.LerayHirsch.cohTransport_congr_proof _ _

open Work.TangentClasses Work.Thom in
/-- **The double `ζ`-shift of the top Leray–Hirsch summand, via the Chern-root relation.**  At the
top index `j = n-1` the coefficient has degree `0`, so the summand is `π^*(y) ⌣ ζ^{n-1}` with
`y ∈ H⁰(B)`; multiplying twice by `ζ` gives `π^*(y) ⌣ ζ^{n+1}`, which has index overflow at level
`n+1` and is expanded using the Chern-root relation
`hc : lhMap W (n+1) c = ζ^{n+1}` and the `H⁰(B)`-module structure of `lhMap`
(`Work.Gen.cupChern_zero_lhMap`).  Both sides lie in `H^{2(n+1)}(P(W))`. -/
theorem cupChern_lhTerm_zeta_top {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {n : ℕ}
    (hn : 1 ≤ n) (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)
    (y : Work.Thom.Coh ℤ 0 B)
    (c : (i : {i : Fin (n + 1) // (i : ℕ) ≤ n + 1}) → Work.Thom.Coh ℤ (2 * ((n + 1) - (i : ℕ))) B)
    (hc : Work.LerayHirsch.lhMap W (n + 1) c = Work.LerayHirsch.zetaPow W (n + 1)) :
    Work.Whitney.cupChern n 1
        (Work.Thom.cohTransport (by omega : 2 * ((n - 1) + 1) = 2 * n)
          (Work.Whitney.cupChern (n - 1) 1
            (Work.LerayHirsch.lhTerm W (n - 1) Work.Gen.topCoeffIdx
              (Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree' (n := n)) y))
            (Work.LerayHirsch.zeta W)))
        (Work.LerayHirsch.zeta W)
      = Work.LerayHirsch.lhMap W (n + 1)
          (fun i => Work.Thom.cohTransport
            (by omega : 2 * (0 + ((n + 1) - (i : ℕ))) = 2 * ((n + 1) - (i : ℕ)))
            (Work.Whitney.cupChern 0 ((n + 1) - (i : ℕ)) y (c i))) := by
  -- Split off the degenerate case `n = 0` (excluded by `hn`).
  rcases n with _ | k
  · omega
  -- RHS: expand the Leray–Hirsch combination via the Chern-root relation `hc` and the
  -- `H⁰(B)`-module structure of `lhMap` (`Work.Gen.cupChern_zero_lhMap`).
  have hR : Work.LerayHirsch.lhMap W (k+1+1)
      (fun i => Work.Thom.cohTransport
        (by omega : 2 * (0 + ((k + 1 + 1) - (i : ℕ))) = 2 * ((k + 1 + 1) - (i : ℕ)))
        (Work.Whitney.cupChern 0 ((k + 1 + 1) - (i : ℕ)) y (c i)))
      = Work.Thom.cohTransport (by omega : 2 * (0 + (k + 1 + 1)) = 2 * (k + 1 + 1))
          (Work.Whitney.cupChern 0 (k + 1 + 1)
            ((CohMap (Work.LerayHirsch.projMap W) ℤ 0).hom y)
            (Work.LerayHirsch.zetaPow W (k + 1 + 1))) := by
    rw [← hc]
    exact (Work.Whitney.ChernRel.cohTransport_apply_symm _ _).symm.trans
      (congrArg (Work.Thom.cohTransport (by omega : 2 * (0 + (k + 1 + 1)) = 2 * (k + 1 + 1)))
        (Work.Gen.cupChern_zero_lhMap W y c).symm)
  rw [hR]
  -- LHS: unfold the top `lhTerm`, transport the coefficient through `π^*`, and push all the
  -- resulting degree casts out of the graded products.
  rw [Work.Whitney.ChernRel.cohTransport_self]
  rw [Work.LerayHirsch.lhTerm_def]
  rw [Work.Whitney.cohTransport_CohMap]
  rw [Work.Gen.cupChern_cast_left]
  rw [Work.Gen.cupChern_cast_left]
  rw [Work.Gen.cupChern_cast_left]
  rw [Work.Gen.cupChern_cast_left]
  rw [Work.Gen.cupChern_cast_left]
  simp only [Work.Whitney.cohTransport_trans]
  -- Replace `zetaPow` by the abstract power series `zPow` and apply the abstract double shift.
  rw [Work.Whitney.ChernRel.zetaPow_eq_zPow W]
  rw [cupChern_zPow_top_doubleShift_aux (↑↑Work.Gen.topCoeffIdx)
        ((CohMap (Work.LerayHirsch.projMap W) ℤ 0).hom y) (Work.LerayHirsch.zeta W)]
  simp only [Work.Whitney.cohTransport_trans]
  -- LHS: unfold the two powers of `ζ` and reassociate.
  rw [Work.Whitney.ChernRel.zPow_succ (Work.LerayHirsch.zeta W) (↑↑Work.Gen.topCoeffIdx + 1)]
  rw [Work.Whitney.ChernRel.zPow_succ (Work.LerayHirsch.zeta W) (↑↑Work.Gen.topCoeffIdx)]
  rw [Work.Gen.cupChern_assoc (↑↑Work.Gen.topCoeffIdx) 1 1
        (Work.Whitney.ChernRel.zPow (Work.LerayHirsch.zeta W) (↑↑Work.Gen.topCoeffIdx))
        (Work.LerayHirsch.zeta W) (Work.LerayHirsch.zeta W)]
  rw [Work.Gen.cupChern_cast_right]
  -- RHS: the same unfolding and reassociation, at the index `k` (the two top indices differ only
  -- by the definitional identity `k + 1 - 1 = k`).
  rw [Work.Whitney.ChernRel.zPow_succ (Work.LerayHirsch.zeta W) (k+1)]
  rw [Work.Whitney.ChernRel.zPow_succ (Work.LerayHirsch.zeta W) k]
  rw [Work.Gen.cupChern_assoc k 1 1
        (Work.Whitney.ChernRel.zPow (Work.LerayHirsch.zeta W) k)
        (Work.LerayHirsch.zeta W) (Work.LerayHirsch.zeta W)]
  rw [Work.Gen.cupChern_cast_right]
  -- Both sides are now the same class, written with propositionally equal degree casts.
  simp only [Work.Whitney.cohTransport_trans]
  exact Work.LerayHirsch.cohTransport_congr_proof _ _

end Work.Gen
