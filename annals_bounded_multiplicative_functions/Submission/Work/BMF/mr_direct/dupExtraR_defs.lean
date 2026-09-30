import Mathlib
import Submission.Work.BMF.mr_direct.range_defs
import Submission.Work.BMF.mr_direct.dupExtra_defs
import Submission.Work.BMF.mr_direct.buchstab_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the mean-square bound of `dupExtraR`

`dupExtraR` is the range-generalised analogue of `dupExtra`
(`Submission/Work/BMF/mr_direct/range_defs.lean`); the `m`'s of its remainder polynomials are
indexed by the *range* windows `winIdxR K A B j = ℕ ∩ [A e^{-(j+1)/K}, B e^{-j/K}]` instead of
the dyadic windows `winIdx K X j = ℕ ∩ [X e^{-(j+1)/K}, 2X e^{-j/K}]`.

This file only fixes the notation: `pSetDR K P Q A B` is the set of triples `x = ⟨⟨j,p⟩,m⟩`
occurring in the expansion of `dupExtraR` (i.e. `(j,p) ∈ pairSetD K P Q`, `m ∈ winIdxR K A B j`),
and `primeImgDR K P Q A B` is the set of primes occurring in it.  The frequency and coefficient
of an index are the same as for `dupExtra`: `nnD x = p·m` and `gamD x = c p·b m·(ω(m;P,Q)+1)^{-1}`.
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open scoped BigOperators
open Work.BMF.mrDirect

noncomputable section

/-- The set of triples `x = ⟨⟨j,p⟩,m⟩` occurring in `dupExtraR`: `(j,p)` is a non-canonical pair
of `pairSetD K P Q` and `m` lies in the range window `winIdxR K A B j`. -/
def pSetDR (K P Q A B : ℝ) : Finset (Σ _ : Σ _ : ℕ, ℕ, ℕ) :=
  (pairSetD K P Q).sigma (fun y : Σ _ : ℕ, ℕ => winIdxR K A B y.1)

/-- The set of primes occurring in `dupExtraR`. -/
def primeImgDR (K P Q A B : ℝ) : Finset ℕ := (pSetDR K P Q A B).image (fun x => x.1.2)

lemma pSetDR_eq_sigma (K P Q A B : ℝ) :
    pSetDR K P Q A B = (pairSetD K P Q).sigma (fun y : Σ _ : ℕ, ℕ => winIdxR K A B y.1) := rfl

lemma primeImgDR_eq_image (K P Q A B : ℝ) :
    primeImgDR K P Q A B = (pSetDR K P Q A B).image (fun x => x.1.2) := rfl

end

end Work.BMF.mr_direct
