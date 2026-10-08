import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.Models.Abstract.ModelData

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Suzuki torus is abelian

`Submission.Sz.szTS n` is the maximal torus of `Sz(2^(2n+1))`, cut out as the range of the
diagonal monoid homomorphism `szTgHom n : (SzField n)ˣ →* GL(4, SzField n)`, restricted to
`SzModel n`.  Since `(SzField n)ˣ` is abelian, every two elements of that range commute;
transporting this through `Subgroup.subgroupOf` gives the claim.

This is the `hTab` field of the model data for the Suzuki family.
-/
namespace Work.Models.Sz

/-- The Suzuki torus is abelian. -/
theorem szTS_comm (n : ℕ) :
    ∀ x ∈ Submission.Sz.szTS n, ∀ y ∈ Submission.Sz.szTS n, x * y = y * x := by
  intro x hx y hy
  -- `szTS n` is `(szTgHom n).range` restricted to `SzModel n`, so both elements are
  -- diagonal matrices `t a`, `t b` for units `a`, `b` of `SzField n`.
  obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.mp hx
  obtain ⟨b, hb⟩ := Subgroup.mem_subgroupOf.mp hy
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm a b]

end Work.Models.Sz
