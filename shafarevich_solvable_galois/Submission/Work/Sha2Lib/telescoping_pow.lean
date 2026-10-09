import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Sha2Lib

/-- **The telescoping identity of the Shapiro cocycle.**

Let `Γ` be a group, `H ≤ Γ` a subgroup, and `c : Γ → Γ → ↥H` satisfy the multiplicative cocycle
identity `c g (γ * γ') = c g γ * c (g * γ) γ'` and the unit condition `c g 1 = 1` (for the section
cocycle `c g γ = ⟨s g * γ * (s (g * γ))⁻¹, _⟩` both hold).

Then the product of the `c`-terms along the orbit of `x` under right multiplication by `d`
telescopes to the single term at `d ^ f`:
`∏_{j < f} c (x * d ^ j) d = c x (d ^ f)`. -/
theorem telescoping_pow {Γ : Type} [Group Γ] {H : Subgroup Γ} (c : Γ → Γ → ↥H)
    (hcmul : ∀ g γ γ' : Γ,
      ((c g (γ * γ') : ↥H) : Γ) = ((c g γ : ↥H) : Γ) * ((c (g * γ) γ' : ↥H) : Γ))
    (hcunit : ∀ g : Γ, ((c g 1 : ↥H) : Γ) = 1)
    (x d : Γ) (f : ℕ) :
    (((List.range f).map (fun j => ((c (x * d ^ j) d : ↥H) : Γ))).prod)
      = ((c x (d ^ f) : ↥H) : Γ) := by
  induction f with
  | zero => simp [hcunit]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← hcmul x (d ^ n) d, pow_succ]

end Work.Sha2Lib
