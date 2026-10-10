import Mathlib.Analysis.Normed.Group.Uniform
import Submission.Work.Tate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- Along a `G`-equivariant bijection `f : A →+ B`, an element of `B` is a norm (i.e. lies in the
range of the norm `N_B`) if and only if it is the image of an element of `A` that is a norm
(lies in the range of `N_A`).  This is the computation behind the injectivity of the induced map
on `Ĥ⁰`. -/
theorem mem_range_norm_iff {G : Type*} {A : Type*} {B : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B] [Fintype G] (f : A →+ B)
    (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a) (hfb : Function.Bijective f) (b : B) :
    b ∈ (norm G B).range ↔ ∃ a : A, f a = b ∧ a ∈ (norm G A).range := by
  constructor
  · rintro ⟨b₀, rfl⟩
    obtain ⟨c, hc⟩ := hfb.2 b₀
    have hval : f (norm G A c) = norm G B b₀ := by
      rw [← norm_map f hf c, hc]
    exact ⟨norm G A c, hval, ⟨c, rfl⟩⟩
  · rintro ⟨a, rfl, c, hc⟩
    rw [← hc]
    exact ⟨f c, norm_map f hf c⟩

/-- An equivariant bijection of `G`-modules induces a bijection on the `0`-th Tate cohomology
groups `Ĥ⁰(G, A) → Ĥ⁰(G, B)`.

Injectivity is reduced to triviality of the kernel: if `H0Map f z = 0`, then a representative
`a ∈ A^G` of `z` has `f a` a norm of `B`, and `mem_range_norm_iff` together with injectivity of
`f` shows that `a` itself is a norm of `A`.  Surjectivity comes from lifting a fixed point of `B`
along `f` and observing that the lift is again fixed. -/
theorem H0Map_bijective {G : Type*} {A : Type*} {B : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B] [Fintype G] (f : A →+ B)
    (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a) (hfb : Function.Bijective f) :
    Function.Bijective (Work.Tate.H0Map G A B f hf) := by
  -- Injectivity is proved by showing that the kernel is trivial.
  have key : ∀ z : H0 G A, H0Map G A B f hf z = 0 → z = 0 := by
    intro z
    refine H0_induction_on (C := fun w => H0Map G A B f hf w = 0 → w = 0) z (fun a h => ?_)
    rw [H0Map_H0π] at h
    rw [H0π_eq_zero_iff] at h
    -- `mapFixed f a` is a norm of `B`, hence so is `f a`.
    obtain ⟨b, hb⟩ := h
    have hfb' : f (a : A) ∈ (norm G B).range :=
      ⟨b, by
        have := congrArg (fun z : fixedSubgroup G B => (z : B)) hb
        simpa using this⟩
    -- hence `f a = f a'` for some norm `a'` of `A`; injectivity gives `a' = a`.
    obtain ⟨a', ha', ha'₀⟩ := (mem_range_norm_iff f hf hfb (f (a : A))).mp hfb'
    have ha'' : a' = (a : A) := hfb.1 ha'
    obtain ⟨c, hc⟩ := ha'₀
    rw [H0π_eq_zero_iff]
    exact ⟨c, Subtype.ext (hc.trans ha'')⟩
  constructor
  · intro x y hxy
    have h : H0Map G A B f hf (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (key (x - y) h)
  · -- Surjectivity: every fixed point of `B` is the image of a fixed point of `A`.
    intro y
    obtain ⟨b, rfl⟩ := H0π_surjective (G := G) (A := B) y
    obtain ⟨a, ha⟩ := hfb.2 (b : B)
    have hafix : a ∈ fixedSubgroup G A := by
      rw [mem_fixedSubgroup]
      intro γ
      apply hfb.1
      rw [hf γ a, ha]
      exact b.2 γ
    refine ⟨H0π G A ⟨a, hafix⟩, ?_⟩
    rw [H0Map_H0π]
    apply congrArg (H0π G B)
    apply Subtype.ext
    simp [ha]

end Work.Tate
