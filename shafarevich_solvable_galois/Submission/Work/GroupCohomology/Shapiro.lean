import Mathlib.Tactic.Abel
import Mathlib.Data.FunLike.IsApply
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.InducedModules
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.GroupCohomology

/-- The module induced from the trivial subgroup: `G → A` with the shift action
`(g • f) x = f (x * g)`. -/
abbrev Ind (G : Type u) (A : Type v) : Type (max u v) := G → A

namespace Ind

variable {G : Type u} {A : Type v} [Group G] [AddCommGroup A]

instance : AddCommGroup (Ind G A) := inferInstanceAs (AddCommGroup (G → A))

/-- The shift action `(g • f) x = f (x * g)` on the induced module.  The `SMul`/`DistribMulAction`
instances on `G → A` are the *coinduced* ones registered in `Submission.InducedModules`; this
lemma is the computation rule for them. -/
@[simp] theorem smul_apply (g : G) (f : Ind G A) (x : G) : (g • f) x = f (x * g) := rfl

end Ind

section Shapiro

variable (G : Type u) (A : Type v) [Group G] [AddCommGroup A]

/-- **Shapiro, degree 1, trivial subgroup.**  Every `1`-cocycle of `G` with values in the induced
module `Ind G A` is a coboundary, with the explicit formula `a x = f x 1`. -/
theorem induced_cocycle1_is_coboundary (f : G → Ind G A) (hf : f ∈ Z1 G (Ind G A)) :
    ∃ a : Ind G A, d0 G (Ind G A) a = f := by
  refine ⟨fun x => f x 1, ?_⟩
  funext g x
  have h : f (x * g) 1 = f g x + f x 1 := by
    have h2 := congrFun (hf x g) 1
    simpa only [Pi.add_apply, Ind.smul_apply, one_mul] using h2
  simp only [d0_apply, Pi.sub_apply, Ind.smul_apply]
  rw [h]
  abel

/-- `H¹(G, Ind G A) = 0`. -/
instance H1_induced_subsingleton : Subsingleton (H1 G (Ind G A)) := by
  refine Subsingleton.intro (fun x y => ?_)
  induction x using H1_induction_on with | h f =>
  induction y using H1_induction_on with | h f' =>
  rw [← sub_eq_zero, ← map_sub, H1π, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
  obtain ⟨a, ha⟩ := induced_cocycle1_is_coboundary G A
    ((f - f' : Z1 G (Ind G A)) : G → Ind G A) (f - f').2
  exact ⟨a, ha⟩

theorem H1_induced_eq_zero (x : H1 G (Ind G A)) : x = 0 :=
  Subsingleton.elim x 0

/-- **Shapiro, degree 2, trivial subgroup.**  Every `2`-cocycle of `G` with values in the induced
module `Ind G A` is a coboundary, with the explicit formula `f g x = c (x, g) 1`. -/
theorem induced_cocycle2_is_coboundary (c : G × G → Ind G A) (hc : c ∈ Z2 G (Ind G A)) :
    ∃ f : G → Ind G A, d1 G (Ind G A) f = c := by
  refine ⟨fun g x => c (x, g) 1, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  funext x
  have h3 : c (x * g, h) 1 + c (x, g) 1 = c (g, h) x + c (x, g * h) 1 := by
    have h4 := congrFun (hc x g h) 1
    simpa only [Pi.add_apply, Ind.smul_apply, one_mul] using h4
  have h3' : c (g, h) x = c (x * g, h) 1 + c (x, g) 1 - c (x, g * h) 1 := by
    rw [h3]; abel
  simp only [d1_apply, Pi.sub_apply, Pi.add_apply, Ind.smul_apply]
  rw [h3']
  abel

/-- `H²(G, Ind G A) = 0`. -/
instance H2_induced_subsingleton : Subsingleton (H2 G (Ind G A)) := by
  refine Subsingleton.intro (fun x y => ?_)
  induction x using H2_induction_on with | h c =>
  induction y using H2_induction_on with | h c' =>
  rw [← sub_eq_zero, ← map_sub, H2π, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
  obtain ⟨f, hf⟩ := induced_cocycle2_is_coboundary G A
    ((c - c' : Z2 G (Ind G A)) : G × G → Ind G A) (c - c').2
  exact ⟨f, hf⟩

theorem H2_induced_eq_zero (x : H2 G (Ind G A)) : x = 0 :=
  Subsingleton.elim x 0

end Shapiro

end Work.GroupCohomology
