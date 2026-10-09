/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Vanishing of Tate cohomology on finite products of coinduced modules

The vanishings `Ĥ⁰(G, Coind R) = Ĥ⁻¹(G, Coind R) = 0` of `Work.Tate.coind_H0_subsingleton`
and `Work.Tate.coind_Hm1_subsingleton` are inherited by finite products (equivalently, by
finite direct sums of copies) of coinduced modules, because fixed points, the norm and the
augmentation submodule are computed componentwise.

This is the form needed for `𝔽_p[G]^r ≅ (G → 𝔽_p)^r` in the embedding-problem input of
Shafarevich's theorem.
-/
import Mathlib
import Submission.Work.Tate.CoindModule
import Submission.Work.Tate.coind_H0_subsingleton
import Submission.Work.Tate.coind_Hm1_subsingleton
import Submission.Work.Tate.H0_pi_subsingleton
import Submission.Work.Tate.Hm1_pi_subsingleton
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Tate

open scoped BigOperators

/-- `Ĥ⁰` of a finite product of copies of the coinduced module vanishes. -/
theorem coind_pi_H0_subsingleton (G : Type u) [Group G] [Fintype G] (R : Type v)
    [AddCommGroup R] (ι : Type*) [Fintype ι] :
    Subsingleton (H0 G (ι → (G → R))) :=
  H0_pi_subsingleton (G := G) (A := G → R) ι (coind_H0_subsingleton (G := G) (R := R))

/-- `Ĥ⁻¹` of a finite product of copies of the coinduced module vanishes. -/
theorem coind_pi_Hm1_subsingleton (G : Type u) [Group G] [Fintype G] (R : Type v)
    [AddCommGroup R] (ι : Type*) [Fintype ι] :
    Subsingleton (Hm1 G (ι → (G → R))) :=
  Hm1_pi_subsingleton (G := G) (A := G → R) ι (coind_Hm1_subsingleton (G := G) (R := R))

end Work.Tate
