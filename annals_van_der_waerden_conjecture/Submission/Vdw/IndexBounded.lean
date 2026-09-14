import Mathlib
import Submission.Vdw.ResidueIndex
import Submission.Commons.FieldTheory.Polynomial.radical_deg_pos_of_monic_deg_pos

open Polynomial
open scoped BigOperators

set_option autoImplicit false

/-!
# The index of a degree-`n` monic polynomial is at most `n−1`

For monic `f` of degree `n ≥ 1` over a field, Bhargava's index
`polyIndex f = n − deg(rad f)` is at most `n−1`: the radical is a monic
divisor of degree at least `1` (commons:
`radical_deg_pos_of_monic_deg_pos`), so `deg rad ≥ 1`.  Consequently no
degree-`n` polynomial has index `≥ n` — `indexClass n n v` is false — which
makes the per-`D` Case-I index conditions *empty* as soon as some prime
satisfies `n ≤ v_p(D)` (see `CaseIExact.perDiscriminant_zero_of_exponent_ge`).
-/

namespace Submission.Vdw

noncomputable section

open UniqueFactorizationMonoid

variable {F : Type*} [Field F] [DecidableEq F]

/-- For monic `f` of degree at least `1`, the index is at most `deg f − 1`
(the radical has degree at least `1`). -/
theorem polyIndex_le_sub_one (f : F[X]) (hf : f.Monic) (hdeg : 1 ≤ f.natDegree) :
    polyIndex f ≤ f.natDegree - 1 := by
  dsimp [polyIndex]
  have h1 : 1 ≤ (UniqueFactorizationMonoid.radical f).natDegree :=
    Commons.FieldTheory.Polynomial.radical_deg_pos_of_monic_deg_pos f hf hdeg
  have h2 : (UniqueFactorizationMonoid.radical f).natDegree ≤ f.natDegree :=
    Commons.FieldTheory.Polynomial.natDegree_radical_le f hf.ne_zero
  omega

/-- No degree-`n` vector is in the index class `(n,n)` for `n ≥ 1`: the index
of a monic degree-`n` polynomial is `< n`. -/
theorem indexClass_self_false (n : ℕ) (hn : 1 ≤ n) (v : Fin n → F) :
    ¬ indexClass n n v := by
  intro h
  unfold indexClass at h
  have hdeg : 1 ≤ (monicOfTrail n v).natDegree := by
    rw [monicOfTrail_natDegree]
    exact hn
  have hle : polyIndex (monicOfTrail n v) ≤ (monicOfTrail n v).natDegree - 1 :=
    polyIndex_le_sub_one (monicOfTrail n v) (monicOfTrail_monic n v) hdeg
  have hdeg' : (monicOfTrail n v).natDegree = n := monicOfTrail_natDegree n v
  rw [hdeg'] at hle
  omega

end
end Submission.Vdw
