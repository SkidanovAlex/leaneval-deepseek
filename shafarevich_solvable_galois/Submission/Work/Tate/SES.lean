/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Short exact sequences of `G`-modules and the connecting map

For the six-term exact sequence of Tate cohomology in degrees `-1, 0` one needs a short exact
sequence of `G`-modules

`0 → A --f--> B --g--> C → 0`

with `G`-equivariant maps, `f` injective, `g` surjective and `f.range = g.ker`.

This file sets up the structure `Work.Tate.SES`, the set-theoretic section of `g`, and the
auxiliary element `deltaLiftFun` whose class is the image of a class in `Ĥ⁻¹(G, C)` under the
connecting map `Ĥ⁻¹(G, C) → Ĥ⁰(G, A)`.
-/
import Mathlib
import Submission.Work.Tate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w x

namespace Work.Tate


/-- A short exact sequence of `G`-modules `0 → A --f--> B --g--> C → 0` with `G`-equivariant
additive maps. -/
structure SES (G : Type u) (A : Type v) (B : Type w) (C : Type x) [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] where
  /-- the inclusion `A → B` -/
  f : A →+ B
  /-- the projection `B → C` -/
  g : B →+ C
  /-- `f` is `G`-equivariant -/
  f_equiv : ∀ (γ : G) (a : A), f (γ • a) = γ • f a
  /-- `g` is `G`-equivariant -/
  g_equiv : ∀ (γ : G) (b : B), g (γ • b) = γ • g b
  /-- `f` is injective -/
  f_injective : Function.Injective f
  /-- `g` is surjective -/
  g_surjective : Function.Surjective g
  /-- exactness in the middle -/
  range_f_eq_ker_g : f.range = g.ker

variable {G : Type u} {A : Type v} {B : Type w} {C : Type x} [Group G] [AddCommGroup A]
  [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
  [DistribMulAction G C]

theorem SES.g_comp_f (S : SES G A B C) (a : A) : S.g (S.f a) = 0 := by
  have h : S.f a ∈ S.f.range := AddMonoidHom.mem_range.mpr ⟨a, rfl⟩
  rw [S.range_f_eq_ker_g] at h
  exact h

theorem SES.exists_of_g_eq_zero (S : SES G A B C) {b : B} (hb : S.g b = 0) : ∃ a : A, S.f a = b := by
  have h : b ∈ S.g.ker := hb
  rw [← S.range_f_eq_ker_g] at h
  exact AddMonoidHom.mem_range.mp h

theorem SES.g_eq_zero_of_eq_f (S : SES G A B C) {a : A} {b : B} (h : S.f a = b) : S.g b = 0 := by
  rw [← h]
  exact S.g_comp_f a

section Fintype

variable [Fintype G]

/-! ## The set-theoretic section of `g` -/

/-- A set-theoretic section of the surjection `g`. -/
noncomputable def SES.sec (S : SES G A B C) : C → B := fun c => Classical.choose (S.g_surjective c)

theorem SES.sec_spec (S : SES G A B C) (c : C) : S.g (S.sec c) = c :=
  Classical.choose_spec (S.g_surjective c)

/-- The section of `0` lies in the kernel of `g`. -/
theorem SES.sec_zero_mem_ker (S : SES G A B C) : S.sec 0 ∈ S.g.ker := by
  rw [AddMonoidHom.mem_ker, S.sec_spec]

/-- The norm of the section of an element of `ker N_C` lies in the kernel of `g`. -/
theorem SES.norm_sec_mem_ker (S : SES G A B C) (c : (norm G C).ker) :
    norm G B (S.sec (c : C)) ∈ S.g.ker := by
  rw [AddMonoidHom.mem_ker, ← norm_map S.g S.g_equiv (S.sec (c : C)), S.sec_spec c]
  exact c.2

/-- For `c ∈ ker N_C` the norm of a lift of `c` lies in the image of `f`. -/
theorem SES.exists_f_eq_norm_sec (S : SES G A B C) (c : (norm G C).ker) :
    ∃ a : A, S.f a = norm G B (S.sec (c : C)) := by
  have h : norm G B (S.sec (c : C)) ∈ S.f.range := by
    rw [S.range_f_eq_ker_g]
    exact S.norm_sec_mem_ker c
  exact AddMonoidHom.mem_range.mp h

/-- The unique preimage in `A` of the norm of the section of `c`. -/
noncomputable def SES.preimage (S : SES G A B C) (c : (norm G C).ker) : A :=
  Classical.choose (S.exists_f_eq_norm_sec c)

theorem SES.f_preimage (S : SES G A B C) (c : (norm G C).ker) :
    S.f (S.preimage c) = norm G B (S.sec (c : C)) :=
  Classical.choose_spec (S.exists_f_eq_norm_sec c)

/-- The preimage `preimage c` is a fixed point. -/
theorem SES.preimage_mem_fixed (S : SES G A B C) (c : (norm G C).ker) :
    S.preimage c ∈ fixedSubgroup G A := by
  rw [mem_fixedSubgroup]
  intro γ
  apply S.f_injective
  rw [S.f_equiv, S.f_preimage, (norm_mem_fixed (S.sec (c : C))) γ]

/-- The underlying element of `Ĥ⁰(G, A)` of the connecting map applied to the class of `c`. -/
noncomputable def SES.deltaLiftFun (S : SES G A B C) (c : (norm G C).ker) : H0 G A :=
  H0π G A ⟨S.preimage c, S.preimage_mem_fixed c⟩

@[simp] theorem deltaLiftFun_apply (S : SES G A B C) (c : (norm G C).ker) :
    S.deltaLiftFun c = H0π G A ⟨S.preimage c, S.preimage_mem_fixed c⟩ := rfl

/-! ## The induced maps on `Ĥ⁰` and `Ĥ⁻¹` -/

/-- The map `Ĥ⁰(G, A) → Ĥ⁰(G, B)` induced by `f`. -/
noncomputable def SES.H0f (S : SES G A B C) : H0 G A →+ H0 G B :=
  H0Map G A B S.f S.f_equiv

/-- The map `Ĥ⁰(G, B) → Ĥ⁰(G, C)` induced by `g`. -/
noncomputable def SES.H0g (S : SES G A B C) : H0 G B →+ H0 G C :=
  H0Map G B C S.g S.g_equiv

/-- The map `Ĥ⁻¹(G, A) → Ĥ⁻¹(G, B)` induced by `f`. -/
noncomputable def SES.Hm1f (S : SES G A B C) : Hm1 G A →+ Hm1 G B :=
  Hm1Map G A B S.f S.f_equiv

/-- The map `Ĥ⁻¹(G, B) → Ĥ⁻¹(G, C)` induced by `g`. -/
noncomputable def SES.Hm1g (S : SES G A B C) : Hm1 G B →+ Hm1 G C :=
  Hm1Map G B C S.g S.g_equiv

@[simp] theorem H0f_H0π (S : SES G A B C) (a : fixedSubgroup G A) :
    S.H0f (H0π G A a) = H0π G B (mapFixed G A B S.f S.f_equiv a) := rfl

@[simp] theorem H0g_H0π (S : SES G A B C) (b : fixedSubgroup G B) :
    S.H0g (H0π G B b) = H0π G C (mapFixed G B C S.g S.g_equiv b) := rfl

@[simp] theorem Hm1f_Hm1π (S : SES G A B C) (a : (norm G A).ker) :
    S.Hm1f (Hm1π G A a) = Hm1π G B (mapKer G A B S.f S.f_equiv a) := rfl

@[simp] theorem Hm1g_Hm1π (S : SES G A B C) (b : (norm G B).ker) :
    S.Hm1g (Hm1π G B b) = Hm1π G C (mapKer G B C S.g S.g_equiv b) := rfl

end Fintype

end Work.Tate
