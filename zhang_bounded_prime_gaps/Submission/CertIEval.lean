import Submission.CertEval2

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# The packed evaluation of the certificate's `I`-form, III

`Submission/CertEval2.lean` proves `contMath v v' R = contPack v v' R` (the packed sign
combination computing the `a`-contraction of two coefficient vectors against the kernel).

Here we assemble the whole `I`-form: `certISum` (the integer double sum over the 1780-element
basis, grouped by signature) is rewritten into the *packed* evaluation `certIval`, in which
* `Ssum p.1 p'.1 50` is replaced by the DP table value `mc 50 (mult p'.1) · unpack (packedRow
  (mult p'.1)) (mult p.1)` (the table `Ssum_50_eq` of `Submission/CertRow.lean`), and
* `Hc p p'` is replaced by the four block extractions `contPack p.2 p'.2 _`.

The rows `packedRow (mult p'.1)` are computed once per *outer* index (the list
`cSigs.zip (cSigs.map (fun p => packedRow (mult p.1)))`), so that the whole double sum costs
a single pass over the pack.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- **The packed evaluation of the `I`-form.**  Outer index: the signature group `p'` whose
packed row is used; inner index: the group `p` supplying the coefficient vector. -/
def certIval : ℤ :=
  ((cSigs.zip (cSigs.map (fun p => packedRow (mult p.1)))).map (fun q =>
    (cSigs.map (fun p =>
      contPack p.2 q.1.2 (p.1.sum + q.1.1.sum) *
        ((mc 50 (mult q.1.1) * unpack q.2 (mult p.1) : ℕ) : ℤ))).sum)).sum

theorem certIval_rfl :
    certIval = ((cSigs.zip (cSigs.map (fun p => packedRow (mult p.1)))).map (fun q =>
      (cSigs.map (fun p =>
        contPack p.2 q.1.2 (p.1.sum + q.1.1.sum) *
          ((mc 50 (mult q.1.1) * unpack q.2 (mult p.1) : ℕ) : ℤ))).sum)).sum := rfl

/-- **The pointwise evaluation of a signature-group pair.** -/
theorem certPair_eq (p p' : List ℕ × List ℤ)
    (h1 : p.1 ∈ certGroupSigs) (h2 : p.2 ∈ certGroupCoefs)
    (h1' : p'.1 ∈ certGroupSigs) (h2' : p'.2 ∈ certGroupCoefs) :
    Hc p p' * (Ssum p.1 p'.1 50 : ℤ)
      = contPack p.2 p'.2 (p.1.sum + p'.1.sum) *
          ((mc 50 (mult p'.1) * unpack (packedRow (mult p'.1)) (mult p.1) : ℕ) : ℤ) := by
  rw [Hc_eq_contMath,
    contMath_eq_contPack p.2 p'.2 (p.1.sum + p'.1.sum) (certGroupCoefs_len h2)
      (certGroupCoefs_len h2') (certGroupCoefs_abs h2) (certGroupCoefs_abs h2')]
  rw [Ssum_50_eq p.1 p'.1 (certGroupSigs_support h1) (certGroupSigs_support h1')
    (certGroupSigs_sum_le h1) (certGroupSigs_sum_le h1')]

/-- **The `I`-form is computed by the packed evaluation.** -/
theorem certISum_eq_certIval : certISum = certIval := by
  rw [certISum_reindex]
  rw [list_sum_comm cSigs cSigs (fun p p' => Hc p p' * (Ssum p.1 p'.1 50 : ℤ))]
  rw [certIval_rfl, map_zip_map_self]
  refine congrArg List.sum (List.map_congr_left (fun p' hp' => ?_))
  refine congrArg List.sum (List.map_congr_left (fun p hp => ?_))
  exact certPair_eq p p' (mem_cSigs_fst hp) (mem_cSigs_snd hp)
    (mem_cSigs_fst hp') (mem_cSigs_snd hp')

end Commons.NumberTheory.MaynardSieve
