import Submission.Work.ConeSwitch.MathlibNoHG

set_option autoImplicit false

/-!
# Functions depending on a prescribed set of coordinates

A real-valued function on a product type **depends only on the coordinates in `S`** if its
value is unchanged whenever two points agree on `S`.  This is the function-level companion of
`Work.Deep.Reed.DependsOn` (which is stated for events), and it is the hypothesis under which
expectations factorise over disjoint coordinate sets in a product measure.
-/

namespace Work.Deep.Reed.Prob

/-- `f` depends only on the coordinates in `S`. -/
def FunDepends {ι : Type*} {Ω : ι → Type*} (S : Finset ι) (f : (∀ i, Ω i) → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

end Work.Deep.Reed.Prob
