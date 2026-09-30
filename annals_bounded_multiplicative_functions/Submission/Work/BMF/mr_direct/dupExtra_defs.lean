import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.buchstab_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the mean-square bound of the non-canonical window error `dupExtra`

`dupExtra b c K P Q X t = Σ_{j ∈ indexSet K P Q} (Σ_{p ∈ winPrimes K j, non-canonical}
c p · p^{-(1+it)}) · remPoly b P Q K X j t`.

Writing `x = ⟨⟨j,p⟩,m⟩`, the triple ranges over `pSetD K P Q X`, the frequency is
`nnD x = p * m`, and the coefficient is `gamD x = c p · b m · (ω(m;P,Q)+1)^{-1}`, so that

`dupExtra t = Σ_{x ∈ pSetD} gamD x · (nnD x)^{-(1+it)}`.

The "extra range" `extraRange K P Q` is the set of primes that can occur in a window
`winPrimes K j` (`j ∈ indexSet K P Q`) while lying *outside* `[P,Q]`; it consists of the two
short multiplicative intervals `[P e^{-1/K}, P]` and `[Q, Q e^{1/K}]`.
-/

set_option autoImplicit false

namespace Work.BMF
namespace mr_direct

open scoped BigOperators
open Work.BMF.mrDirect

noncomputable section

/-- The primes which can appear in a window `winPrimes K j` (`j ∈ indexSet K P Q`) but lie
outside `[P,Q]`: the two short multiplicative intervals `[P e^{-1/K}, P]` and `[Q, Q e^{1/K}]`. -/
def extraRange (K P Q : ℝ) : Finset ℕ :=
  Work.BMF.primesIn (P * Real.exp (-(1 / K))) P ∪ Work.BMF.primesIn Q (Q * Real.exp (1 / K))

/-- The integer `p * m` attached to the index `⟨⟨j,p⟩,m⟩` of `dupExtra`. -/
def nnD (x : Σ _ : Σ _ : ℕ, ℕ, ℕ) : ℕ := x.1.2 * x.2

/-- The coefficient `γ x = c p · b m · (ω(m;P,Q)+1)^{-1}` of the index `x = ⟨⟨j,p⟩,m⟩`. -/
def gamD (b c : ℕ → ℂ) (P Q : ℝ) (x : Σ _ : Σ _ : ℕ, ℕ, ℕ) : ℂ :=
  c x.1.2 * b x.2 * ((((omegaCount P Q x.2 : ℕ) + 1 : ℕ)) : ℂ)⁻¹

/-- The set of pairs `(j,p)` occurring in `dupExtra`: `j ∈ indexSet K P Q`, `p ∈ winPrimes K j`,
and `p` is *not* in its canonical window. -/
def pairSetD (K P Q : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (indexSet K P Q).sigma (fun (j : ℕ) => (winPrimes K j).filter
      (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p)))

/-- The set of primes occurring in `dupExtra`. -/
def primeImgD (K P Q X : ℝ) : Finset ℕ := (pSetD K P Q X).image (fun x => x.1.2)

lemma pairSetD_eq (K P Q : ℝ) :
    pairSetD K P Q = (indexSet K P Q).sigma (fun (j : ℕ) => (winPrimes K j).filter
      (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p))) := rfl

lemma pSetD_eq_sigma (K P Q X : ℝ) :
    pSetD K P Q X = (pairSetD K P Q).sigma (fun (y : Σ _ : ℕ, ℕ) => winIdx K X y.1) := rfl

end

end mr_direct
end Work.BMF
