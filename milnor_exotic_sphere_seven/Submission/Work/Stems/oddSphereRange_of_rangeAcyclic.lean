import Mathlib
import Submission.Work.Stems.Engine.C2Range
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.Stems.ratH_isEMSpace_self
import Submission.Work.Serre.serreE0Range

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Stems

/-- **The odd side of the `C2` layer in range form, from the rational acyclicity of range models of
`K(A,k)`.**

`Work.Stems.Engine.OddSphereRange (fun n => 2 * n)` says: for every *odd* `n ≥ 1`, every model `X`
of `K(ℤ,n)` is rationally `Sⁿ` below degree `2n` — `H_n(X;ℚ) ≅ ℚ` and `H_j(X;ℚ) = 0` for
`0 < j < 2n`, `j ≠ n`.

The two halves of the vanishing come from the two halves of the range in which a `K(ℤ,n)` is
understood:

* degrees `0 < j < n`: `X` is `(n-1)`-connected (`IsEMSpace` trivialises `π_i(X)` for `i ≠ n`), so
  `Work.Serre.SerreE0Range` — **proved** in `Submission/Work/Serre/serreE0Range.lean`, imported
  here — makes the rational homology vanish below `n`;
* degrees `n < j < 2n`: these are exactly the degrees `n < j ≤ 2n-1` of the input
  `Work.RatHurewicz.RangeModelRatAcyclic` applied with `k = n` to `X` itself.  (The hypothesis
  `IsRangeKModel n (2n-1) pt` — `π_i(X) = 0` for `i ≤ 2n-1`, `i ≠ n` — is exactly the `IsEMSpace`
  vanishing, which holds in *all* degrees because `X` is a *genuine* model of `K(ℤ,n)`, not only a
  range model.)

The degree `n` itself is `Work.Stems.ratH_isEMSpace_self` for `n ≥ 2`, and the base case `n = 1` is
`Work.Stems.Engine.ratSphereBelow_one` (whose input is `Work.Serre.SerreC1`): a model of `K(ℤ,1)` is
rationally `S¹`, so the vanishing conjunct of `RatSphereBelow X 1 2` is vacuous and only
`H_1(X;ℚ) ≅ ℚ` has content. -/
theorem oddSphereRange_of_rangeAcyclic (h : Work.RatHurewicz.RangeModelRatAcyclic)
    (hC1 : Work.Serre.SerreC1) :
    Work.Stems.Engine.OddSphereRange (fun n => 2 * n) := by
  intro n hn hodd X _ pt hX
  have hn' : n = 1 ∨ 2 ≤ n := by omega
  rcases hn' with h1 | h2
  · -- base case: `n = 1`, where `RatSphereBelow X 1 2` reduces to `H_1(X;ℚ) ≅ ℚ` (`C1`)
    subst h1
    exact Work.Stems.Engine.ratSphereBelow_one hC1 X pt hX 2
  · change Work.Stems.Engine.RatSphereBelow X n (2 * n)
    refine ⟨?_, ?_⟩
    · -- the generator in degree `n`: `H_n(X;ℚ) ≅ ℚ` for `n ≥ 2` (Hurewicz in degree `n`)
      exact Work.Stems.ratH_isEMSpace_self (n := n) (by omega) pt hX
    · -- the vanishing: below `n` from E0-range and connectivity, above `n` from the input
      intro j hj0 hjN hjn
      rcases lt_or_ge j n with hjl | hjl
      · exact (Work.Serre.serreE0Range X pt (n - 1)
          (fun i _ => hX.2 i (by omega))) j hj0 (by omega)
      · have hjn' : n < j := lt_of_le_of_ne hjl (Ne.symm hjn)
        exact h n (by omega) X pt (fun i _ hin => hX.2 i hin) j hjn' (by omega)

end Work.Stems
