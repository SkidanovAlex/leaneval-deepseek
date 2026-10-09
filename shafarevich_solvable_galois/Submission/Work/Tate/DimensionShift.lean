/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dimension shifting for Tate cohomology in low degrees

Let `0 → A --f--> B --g--> C → 0` be a short exact sequence of `G`-modules with `B`
*cohomologically trivial in degrees `-1, 0`*, i.e. `Ĥ⁻¹(G, B) = Ĥ⁰(G, B) = 0`.  Then the
connecting map of the six-term exact sequence

`Ĥ⁻¹(G, A) → Ĥ⁻¹(G, B) → Ĥ⁻¹(G, C) --δ--> Ĥ⁰(G, A) → Ĥ⁰(G, B) → Ĥ⁰(G, C)`

has vanishing kernel and full range, hence is an isomorphism

`δ : Ĥ⁻¹(G, C) ≅ Ĥ⁰(G, A)`.

This is *dimension shifting*: it moves classes from degree `0` to degree `-1` (or back),
at the cost of twisting the coefficients by the kernel of the shift.

The standard instantiation is the sequence `0 → A → Coind(A) → A^* → 0`, where
`Coind(A) = (G → A)` is the coinduced module (acyclic in all degrees by Shapiro's lemma) and
`A^* = Coind(A)/A`; it is provided here as

* `Work.Tate.coindShift` : the shifted module `A^* = Coind(A)/A`;
* `Work.Tate.coindSES` : the short exact sequence, in `Work.Tate.SES` form;
* `Work.Tate.dimensionShiftCoind : Ĥ⁻¹(G, A^*) ≃+ Ĥ⁰(G, A)`.

In the notation of Shafarevich's shrinking procedure, `A^*` plays the role of the `I_G`-twist:
`A^* ≅ A ⊗ I_G^*` where `I_G^* = Hom(I_G, 𝔽_p)`, so `Ĥ⁰(G, M) ≅ Ĥ⁻¹(G, M ⊗ I_G^*)` is the
`k = 0` case of `Ĥ^k(G, M) ≅ Ĥ⁻¹(G, M ⊗ A_k)`, `A_k = I_G^{-(k+1)}`.
-/
import Mathlib
import Submission.Work.Tate.Delta
import Submission.Work.Tate.ker_Hm1g_eq_range_Hm1f
import Submission.Work.Tate.ker_delta_eq_range_Hm1g
import Submission.Work.Tate.range_delta_eq_ker_H0f
import Submission.Work.Tate.Shift
import Submission.Work.Tate.coind_H0_subsingleton
import Submission.Work.Tate.coind_Hm1_subsingleton
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w x

namespace Work.Tate

variable {G : Type u} {A : Type v} {B : Type w} {C : Type x} [Group G] [AddCommGroup A]
  [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
  [DistribMulAction G C] [Fintype G]

/-- **Dimension shifting, abstract form.**  If the middle term `B` of a short exact sequence of
`G`-modules has vanishing `Ĥ⁻¹` and `Ĥ⁰`, the connecting map `Ĥ⁻¹(G, C) → Ĥ⁰(G, A)` is
bijective. -/
theorem SES.delta_bijective (S : SES G A B C) (h0 : Subsingleton (H0 G B))
    (h1 : Subsingleton (Hm1 G B)) : Function.Bijective S.delta := by
  have hHm1g : S.Hm1g = 0 :=
    AddMonoidHom.ext (fun y => by
      have hy : y = 0 := h1.elim y 0
      simpa [hy] using map_zero S.Hm1g)
  have hH0f : S.H0f = 0 :=
    AddMonoidHom.ext (fun y => h0.elim (S.H0f y) 0)
  have hker : S.delta.ker = ⊥ := by
    rw [ker_delta_eq_range_Hm1g S, hHm1g, AddMonoidHom.range_zero]
  have hrange : S.delta.range = ⊤ := by
    rw [range_delta_eq_ker_H0f S, hH0f, AddMonoidHom.ker_zero]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hmem : x - y ∈ S.delta.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, hxy, sub_self]
    rw [hker] at hmem
    exact sub_eq_zero.mp (by simpa using hmem)
  · intro y
    have hmem : y ∈ S.delta.range := by rw [hrange]; exact AddSubgroup.mem_top y
    exact AddMonoidHom.mem_range.mp hmem

/-- **Dimension shifting, abstract form.**  The connecting map is an isomorphism
`Ĥ⁻¹(G, C) ≃+ Ĥ⁰(G, A)` whenever `Ĥ⁻¹(G, B) = Ĥ⁰(G, B) = 0`. -/
noncomputable def SES.dimensionShift (S : SES G A B C) (h0 : Subsingleton (H0 G B))
    (h1 : Subsingleton (Hm1 G B)) : Hm1 G C ≃+ H0 G A :=
  AddEquiv.ofBijective S.delta (S.delta_bijective h0 h1)

@[simp] theorem SES.dimensionShift_apply (S : SES G A B C) (h0 : Subsingleton (H0 G B))
    (h1 : Subsingleton (Hm1 G B)) (c : Hm1 G C) :
    S.dimensionShift h0 h1 c = S.delta c := rfl

/-! ## The concrete shift `A^* = Coind(A)/A` -/

/-- **Dimension shifting with the coinduced module.**  For the short exact sequence
`0 → A → Coind(A) → A^* → 0`, whose middle term is coinduced (hence acyclic), the connecting
map is an isomorphism `Ĥ⁻¹(G, A^*) ≃+ Ĥ⁰(G, A)`. -/
noncomputable def dimensionShiftCoind (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] : Hm1 G (coindShift G A) ≃+ H0 G A :=
  (coindSES G A).dimensionShift (coind_H0_subsingleton (G := G) (R := A))
    (coind_Hm1_subsingleton (G := G) (R := A))

/-- The inverse of the dimension-shifting isomorphism: `Ĥ⁰(G, A) ≃+ Ĥ⁻¹(G, A^*)`. -/
noncomputable def dimensionShiftCoindSymm (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] : H0 G A ≃+ Hm1 G (coindShift G A) :=
  (dimensionShiftCoind G A).symm

@[simp] theorem dimensionShiftCoind_apply (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (c : Hm1 G (coindShift G A)) :
    dimensionShiftCoind G A c = (coindSES G A).delta c := rfl

end Work.Tate
