import Mathlib
import Submission.Work.BMF.mr_direct.buchstab_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Merged-frequency vocabulary for the range-extension error `ebound`

The range-extension error `ebound` is a double sum indexed by pairs `(p, m)`.  To apply the
Montgomery–Vaughan mean value theorem we merge the pairs with equal product `p * m`: they
all contribute the *same* frequency `log (p * m)` of the Dirichlet polynomial
`Σ γ i · (nn i)^{-(1+it)}`.

* `ebnn ⟨p,m⟩ = p * m` is the merged frequency;
* `ebγ` is the coefficient attached to a pair;
* `ebFiber K P Q X n` is the set of pairs in `pSetB K P Q X` with product `n`;
* `ebD b c K P Q X n` is the merged coefficient `Σ_{ebnn i = n} ebγ i`;
* `ebImg K P Q X` is the set of products actually occurring, i.e. the support of `ebD`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.BMF.mr_direct

open scoped BigOperators

noncomputable section

/-- The merged frequency `nn ⟨p, m⟩ = p * m` of a pair in `pSetB`. -/
def ebnn (i : Σ _ : ℕ, ℕ) : ℕ := i.1 * i.2

/-- The coefficient multiplying `(ebnn i)^{-(1+it)}` in the sum defining `ebound`. -/
def ebγ (b c : ℕ → ℂ) (P Q : ℝ) (i : Σ _ : ℕ, ℕ) : ℂ :=
  c i.1 * b i.2 * (((Work.BMF.mrDirect.omegaCount P Q i.2 : ℕ) + 1 : ℕ) : ℂ)⁻¹

/-- The fibre of `ebnn` over `n` inside `pSetB K P Q X`. -/
def ebFiber (K P Q X : ℝ) (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Work.BMF.mrDirect.pSetB K P Q X).filter (fun i => ebnn i = n)

/-- The merged coefficient `d n = Σ_{ebnn i = n} ebγ i`. -/
def ebD (b c : ℕ → ℂ) (K P Q X : ℝ) (n : ℕ) : ℂ :=
  ∑ i ∈ ebFiber K P Q X n, ebγ b c P Q i

/-- The set of products `p * m` actually occurring in `pSetB K P Q X`. -/
def ebImg (K P Q X : ℝ) : Finset ℕ := (Work.BMF.mrDirect.pSetB K P Q X).image ebnn

end

end Work.BMF.mr_direct
