import Mathlib
import Submission.Work.Tate.CoindModule
import Submission.Work.Tate.coind_fixed_iff_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

open scoped BigOperators

/-!
# `Ĥ⁰(G, G → R) = 0` for the coinduced module `G → R`

Let `G` be a finite group and `R` an abelian group, and let `G` act on `G → R` by the coinduced
action `(g • f) x = f (x * g)` (Shapiro's setting: `G → R = Coind_1^G R`).

The fixed points of this action are the constant functions
(`Work.Tate.coind_fixed_iff_const`).  The norm of an arbitrary function is again a constant
function, namely the constant `∑ g, f g` (`Work.Tate.norm_coind_eq_const`), and as `f` ranges
over all of `G → R` this sum ranges over all of `R` — explicitly, the "delta function at `1`"
`g ↦ if g = 1 then c else 0` has norm the constant function `c`.  Consequently the norm maps
onto the fixed points, so

  `Ĥ⁰(G, G → R) = (G → R)^G / N(G → R) = 0`,

i.e. `Subsingleton (H0 G (G → R))`.  This is the `i = 0` case of Shapiro's lemma
(`Ĥ⁰(G, Coind_1^G R) = Ĥ⁰(1, R) = R/R = 0`).
-/

/-- **The norm of a coinduced function is a constant function.**  For `G` a finite group acting
on `G → R` by `(g • f) x = f (x * g)`, the norm `N f = ∑_g g • f` is the constant function with
value the total sum `∑_g f g`:

  `(N f) x = ∑_g f (x * g) = ∑_h f h`.
-/
theorem norm_coind_eq_const {G : Type*} [Group G] [Fintype G] {R : Type*} [AddCommGroup R]
    (f : G → R) :
    norm G (G → R) f = Function.const G (∑ g : G, f g) := by
  funext x
  rw [norm_apply, Function.const_apply]
  rw [Finset.sum_apply]
  simp only [coind_smul_eq]
  exact Fintype.sum_equiv (Equiv.mulLeft x) (fun g => f (x * g)) (fun h => f h) (fun _ => rfl)

/-- The total sum of the "delta function at `1`" with value `c` is `c`. -/
theorem sum_ite_one_eq {G : Type*} [Group G] [Fintype G] [DecidableEq G] {R : Type*}
    [AddCommGroup R] (c : R) :
    (∑ g : G, (if g = 1 then c else 0)) = c := by
  rw [Finset.sum_ite_eq']
  simp

/-- **`Ĥ⁰` of the coinduced module `G → R` vanishes** for `G` finite: the norm
`N : (G → R) → (G → R)^G` is surjective onto the fixed points (both consist of the constant
functions, and every constant `c` is `N` of the delta function `g ↦ if g = 1 then c else 0`),
so `Ĥ⁰(G, G → R) = (G → R)^G / N(G → R) = 0`. -/
theorem coind_H0_subsingleton {G : Type*} [Group G] [Fintype G] {R : Type*} [AddCommGroup R] :
    Subsingleton (Work.Tate.H0 G (G → R)) := by
  classical
  refine ⟨fun x y => ?_⟩
  have hzero : ∀ z : H0 G (G → R), z = 0 := by
    intro z
    refine H0_induction_on (C := fun z => z = 0) z ?_
    intro a
    rw [H0π_eq_zero_iff]
    obtain ⟨c, hc⟩ := (coind_fixed_iff_const (a : G → R)).mp a.2
    refine ⟨(fun g => if g = 1 then c else 0), ?_⟩
    refine Subtype.ext ?_
    rw [normToFixed_apply, norm_coind_eq_const, sum_ite_one_eq, hc]
  rw [hzero x, hzero y]

end Work.Tate
