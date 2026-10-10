import Mathlib.Algebra.FiveLemma
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- The five lemma (bijectivity of the middle map) for a commutative ladder of
additive abelian groups with exact rows

```
A1 --f1--> A2 --f2--> A3 --f3--> A4 --f4--> A5
|          |          |          |          |
a1         a2         a3         a4         a5
v          v          v          v          v
B1 --g1--> B2 --g2--> B3 --g3--> B4 --g4--> B5
```

If `a1` is surjective, `a2` and `a4` are bijective and `a5` is injective, then `a3`
is bijective. -/
theorem five_lemma_exact {A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 : Type*}
    [AddCommGroup A1] [AddCommGroup A2] [AddCommGroup A3] [AddCommGroup A4] [AddCommGroup A5]
    [AddCommGroup B1] [AddCommGroup B2] [AddCommGroup B3] [AddCommGroup B4] [AddCommGroup B5]
    (f1 : A1 →+ A2) (f2 : A2 →+ A3) (f3 : A3 →+ A4) (f4 : A4 →+ A5)
    (g1 : B1 →+ B2) (g2 : B2 →+ B3) (g3 : B3 →+ B4) (g4 : B4 →+ B5)
    (a1 : A1 →+ B1) (a2 : A2 →+ B2) (a3 : A3 →+ B3) (a4 : A4 →+ B4) (a5 : A5 →+ B5)
    (h1 : ∀ x, a2 (f1 x) = g1 (a1 x)) (h2 : ∀ x, a3 (f2 x) = g2 (a2 x))
    (h3 : ∀ x, a4 (f3 x) = g3 (a3 x)) (h4 : ∀ x, a5 (f4 x) = g4 (a4 x))
    (hf1 : Function.Exact f1 f2) (hf2 : Function.Exact f2 f3) (hf3 : Function.Exact f3 f4)
    (hg1 : Function.Exact g1 g2) (hg2 : Function.Exact g2 g3) (hg3 : Function.Exact g3 g4)
    (ha1 : Function.Surjective a1) (ha2 : Function.Bijective a2) (ha4 : Function.Bijective a4)
    (ha5 : Function.Injective a5) :
    Function.Bijective a3 := by
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    f1 f2 f3 f4 g1 g2 g3 g4 a1 a2 a3 a4 a5
    (AddMonoidHom.ext h1).symm (AddMonoidHom.ext h2).symm
    (AddMonoidHom.ext h3).symm (AddMonoidHom.ext h4).symm
    hf1 hf2 hf3 hg1 hg2 hg3 ha1 ha2 ha4 ha5

end Work.SSGRoute.PT
