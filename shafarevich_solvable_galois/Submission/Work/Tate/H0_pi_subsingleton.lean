import Mathlib
import Submission.Work.Tate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

open scoped BigOperators

/-- The norm on a product module `ι → A` (with the pointwise action) is computed pointwise. -/
theorem norm_pi_apply {G : Type*} {A : Type*} {ι : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (b : ι → A) (i : ι) :
    norm G (ι → A) b i = norm G A (b i) := by
  simp only [norm_apply, Finset.sum_apply, Pi.smul_apply]

/-- If `Ĥ⁰(G, A)` is a subsingleton then every fixed point of `A` is a norm. -/
theorem mem_range_normToFixed_of_subsingleton {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (h : Subsingleton (H0 G A))
    (x : fixedSubgroup G A) : x ∈ (normToFixed G A).range := by
  have hx : H0π G A x = 0 := Subsingleton.elim _ _
  exact (H0π_eq_zero_iff x).mp hx

/-- Vanishing of `Ĥ⁰(G, A)` is inherited by products `ι → A` with the pointwise action:
a fixed point of a product is a family of fixed points, and it is a norm as soon as each of its
components is. -/
theorem H0_pi_subsingleton {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (ι : Type*) [Fintype ι]
    (h : Subsingleton (Work.Tate.H0 G A)) : Subsingleton (Work.Tate.H0 G (ι → A)) := by
  have hzero : ∀ z : H0 G (ι → A), z = 0 := by
    intro z
    refine H0_induction_on (C := fun w => w = 0) z ?_
    intro a
    rw [H0π_eq_zero_iff]
    -- each component of the fixed point `a` is a fixed point of `A`
    have hfix : ∀ i : ι, ∀ g : G, g • (a : ι → A) i = (a : ι → A) i := by
      intro i g
      have := congrFun (a.2 g) i
      rwa [Pi.smul_apply] at this
    -- choose a componentwise preimage under the norm
    let b : ι → A := fun i => Classical.choose (mem_range_normToFixed_of_subsingleton h ⟨(a : ι → A) i, hfix i⟩)
    have hb : ∀ i : ι, norm G A (b i) = (a : ι → A) i := by
      intro i
      have := congrArg Subtype.val
        (Classical.choose_spec (mem_range_normToFixed_of_subsingleton h ⟨(a : ι → A) i, hfix i⟩))
      simpa using this
    have hnorm : norm G (ι → A) b = (a : ι → A) := by
      funext i
      rw [norm_pi_apply, hb i]
    exact ⟨b, Subtype.ext hnorm⟩
  exact ⟨fun x y => by rw [hzero x, hzero y]⟩

end Work.Tate
