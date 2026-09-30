import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.omegaCount_mul_prime
import Submission.Work.BMF.mr_direct.card_primeSet_filter_dvd
import Submission.Work.BMF.mr_direct.dirPolyM_eq_mainA_add_ep2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the mean-square bound on the `p²`-correction term `ep2`

`Work.BMF.mrDirect.ep2` is a double sum over pairs `⟨p, m⟩` with `p` a prime in `[P,Q]`,
`m ∈ [X/p, 2X/p]` and `p ∣ m`.  We record the pair as a single index of the sigma-type
`pSetE P Q X`, give the *frequency* `freq ⟨p,m⟩ = m·p` and the *coefficient* `coef ⟨p,m⟩`,
so that

`ep2 a b c P Q X t = Σ_{x ∈ pSetE P Q X} coef x · (freq x)^{-(1+it)}`.

Merging equal frequencies (all indices with the same `freq` are the different primes of `n`
that divide `n` to order `≥ 2`) produces the merged coefficient `dd`.
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open Finset
open scoped BigOperators

noncomputable section

/-- The frequency `m·p` attached to a pair `⟨p, m⟩`. -/
def freq (x : Σ _ : ℕ, ℕ) : ℕ := x.2 * x.1

/-- The coefficient of the pair `⟨p, m⟩` in the `p²`-correction term `ep2`. -/
def coef (a b c : ℕ → ℂ) (P Q : ℝ) (x : Σ _ : ℕ, ℕ) : ℂ :=
  a (x.2 * x.1) * (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ) : ℂ))⁻¹ -
    b x.2 * c x.1 * (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ) : ℂ))⁻¹

/-- The merged coefficient over the fibre of `freq`: the total coefficient of
`(n)^{-(1+it)}` in `ep2`. -/
def dd (a b c : ℕ → ℂ) (P Q X : ℝ) (n : ℕ) : ℂ :=
  ∑ x ∈ (Work.BMF.mrDirect.pSetE P Q X).filter (fun x => freq x = n), coef a b c P Q x

end

end Work.BMF.mr_direct
