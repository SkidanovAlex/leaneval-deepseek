/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Ĥ⁻¹` of a finite product: subsingleton `Ĥ⁻¹(G, A)` implies subsingleton `Ĥ⁻¹(G, ι → A)`

`Ĥ⁻¹(G, ·) = ker N / I_G·(·)` is an additive functor that commutes with finite products:
for a finite index type `ι` one has, pointwise, `ker N_{A^ι} = (ker N_A)^ι` and
`I_G·(A^ι) = (I_G·A)^ι`, hence `Ĥ⁻¹(G, A^ι) ≃ Ĥ⁻¹(G, A)^ι`.  Consequently `Ĥ⁻¹(G, A)`
being a subsingleton forces `Ĥ⁻¹(G, ι → A)` to be a subsingleton.

The proof below avoids building the full product decomposition: it suffices to observe that
any `y : ι → A` lying in `ker N_{A^ι}` has *every* coordinate in `ker N_A`; since `Ĥ⁻¹(G, A)`
is a subsingleton, every element of `ker N_A` lies in the augmentation submodule `I_G·A`, and
then `y = ∑_i Pi.single i (y i)` exhibits `y` as a sum of elements of `I_G·(A^ι)`.
-/
import Mathlib
import Submission.Work.Tate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

open scoped BigOperators

/-- The additive homomorphism `A →+ (ι → A)` putting `a` in the `i`-th coordinate and `0`
everywhere else.  It is `G`-equivariant for the pointwise action on `ι → A` (see
`Pi.single_smul`). -/
noncomputable def hm1PiSingleAddHom (ι : Type*) (A : Type*) [AddCommGroup A] [DecidableEq ι]
    (i : ι) : A →+ (ι → A) where
  toFun a := Pi.single i a
  map_zero' := by
    funext j
    by_cases hji : j = i
    · subst hji; simp
    · simp [Pi.single_eq_of_ne hji]
  map_add' a b := by
    funext j
    by_cases hji : j = i
    · subst hji; simp
    · simp [Pi.single_eq_of_ne hji]

@[simp] theorem hm1PiSingleAddHom_apply {ι : Type*} {A : Type*} [AddCommGroup A]
    [DecidableEq ι] (i : ι) (a : A) : hm1PiSingleAddHom ι A i a = Pi.single i a := rfl

/-- The norm on a function type `ι → A` is computed pointwise. -/
theorem Hm1_pi_norm_apply {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] {ι : Type*} (y : ι → A) (i : ι) :
    (norm G (ι → A) y) i = norm G A (y i) := by
  rw [norm_apply, norm_apply]
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]

theorem Hm1_pi_subsingleton {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (ι : Type*) [Fintype ι]
    (h : Subsingleton (Work.Tate.Hm1 G A)) : Subsingleton (Work.Tate.Hm1 G (ι → A)) := by
  classical
  -- Every element of `ker N_{A^ι}` has all of its coordinates in `ker N_A`.
  have key : ∀ y : ι → A, norm G (ι → A) y = 0 → y ∈ augmentation G (ι → A) := by
    intro y hy
    have hcoord : ∀ i, norm G A (y i) = 0 := by
      intro i
      have h2 := congrFun hy i
      rw [Hm1_pi_norm_apply y i] at h2
      simpa using h2
    -- Each coordinate lies in `I_G·A`, because `Ĥ⁻¹(G, A)` is a subsingleton.
    have haug : ∀ i, y i ∈ augmentation G A := by
      intro i
      have h1 : Hm1π G A ⟨y i, hcoord i⟩ = 0 :=
        @Subsingleton.elim (Hm1 G A) h _ _
      rw [Hm1π_eq_zero_iff] at h1
      exact h1
    -- Reassemble `y` as the sum of its coordinate embeddings.
    rw [← Finset.univ_sum_single y]
    exact AddSubgroup.sum_mem (augmentation G (ι → A)) (fun i _ =>
      map_mem_augmentation (hm1PiSingleAddHom ι A i)
        (fun g a => by
          simp only [hm1PiSingleAddHom]
          exact Pi.single_smul (f := fun _ => A) i g a)
        (haug i))
  -- Hence `ker N_{A^ι} ⊆ I_G·(A^ι)` and the quotient `Ĥ⁻¹(G, ι → A)` is trivial.
  have hzero : ∀ x : Hm1 G (ι → A), x = 0 := by
    intro x
    refine Hm1_induction_on (C := fun z => z = 0) x (fun a => ?_)
    rw [Hm1π_eq_zero_iff]
    exact key a a.2
  exact ⟨fun x z => (hzero x).trans (hzero z).symm⟩

end Work.Tate
