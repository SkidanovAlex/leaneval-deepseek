import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.ASRulV2M

theorem injective_of_trdeg_of_subfield_closure {K : Type*} [Field K] {A : Type*} [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (hA : Algebra.trdeg K (FractionRing A) ≤ 1)
    {k : Type*} [Field k] [Algebra K k] (f : Polynomial A →ₐ[K] k)
    (hcl : Subfield.closure (Set.range f) = ⊤)
    (htr : Algebra.trdeg K k = 2) :
    Function.Injective f := by sorry

end Work.MotAS.ASRulV2M
