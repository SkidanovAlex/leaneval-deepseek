import Mathlib
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Chapter V: the conjugation action data on `Q₀`, `K = J(D,t)`, `D`

Peterfalvi II Ch. V uses the conjugation actions of `K = J(D,t)` and of `V = C_D(t)`
on the elementary abelian 2-group `Q₀ = ⟨Inv H⟩`, and of `V` on `K`, together with the
compatibility of these actions.  This file records that these actions exist as honest
group homomorphisms into `MulAut`:

* `Φ : K →* Aut(Q₀)` is conjugation by `K ≤ H` (which normalises `Q₀` because `H` does);
* `Ψ : V →* Aut(Q₀)` is conjugation by `V ≤ H`;
* `T : V →* Aut(K)` is conjugation by `V`, using that `K ⊴ D` (hypothesis `hKn`) and
  `V ≤ D`;
* and the compatibility `Ψ u (Φ k x) = Φ (T u k) (Ψ u x)` is just the associativity of
  conjugation in `G`.

The first hypothesis `hcomm` (the involutions of `H` commute) is not needed for the
existence of the actions; it is kept because the caller states the lemma in that form.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV12

variable {G : Type*} [Group G]

/-! ## Conjugation as an automorphism of a normalised subgroup -/

/-- Conjugation by an element `g` of the normalizer of `S`, as an automorphism of `S`. -/
noncomputable def conjAutOfMem {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) : MulAut S where
  toFun x := ⟨g * (x : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp x.2⟩
  invFun x := ⟨g⁻¹ * (x : G) * g, by
    refine (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * (x : G) * g)).mpr ?_
    show g * (g⁻¹ * (x : G) * g) * g⁻¹ ∈ S
    rw [show g * (g⁻¹ * (x : G) * g) * g⁻¹ = (x : G) by group]
    exact x.2⟩
  left_inv x := Subtype.ext (by group)
  right_inv x := Subtype.ext (by group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[simp] theorem conjAutOfMem_apply {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (x : S) :
    ((conjAutOfMem hg x : S) : G) = g * (x : G) * g⁻¹ := rfl

/-- The conjugation map `T →* MulAut S` for a subgroup `T` normalizing `S`. -/
noncomputable def conjAutOfLe (S T : Subgroup G)
    (h : T ≤ Subgroup.normalizer (S : Set G)) : T →* MulAut S where
  toFun t := conjAutOfMem (h t.2)
  map_one' := by
    refine MulEquiv.ext fun x => Subtype.ext (by simp [conjAutOfMem_apply])
  map_mul' a b := by
    refine MulEquiv.ext fun x => Subtype.ext (by
      rw [MulAut.mul_apply]
      simp only [conjAutOfMem_apply, Subgroup.coe_mul]
      group)

@[simp] theorem conjAutOfLe_apply (S T : Subgroup G) (h : T ≤ Subgroup.normalizer (S : Set G))
    (t : T) (x : S) :
    ((conjAutOfLe S T h t x : S) : G) = (t : G) * (x : G) * (t : G)⁻¹ := rfl

/-! ## `H` normalises `Q₀` -/

theorem Q0_conj_mem {H : Subgroup G} {h x : G} (hh : h ∈ H) (hx : x ∈ Q0 H) :
    h * x * h⁻¹ ∈ Q0 H := by
  rcases mem_Q0_iff.mp hx with ⟨hxH, hx2⟩ | rfl
  · refine mem_Q0_iff.mpr (Or.inl ⟨?_, ?_⟩)
    · exact H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh)
    · obtain ⟨hx2', hxne⟩ := orderOf_eq_prime_iff.mp hx2
      refine orderOf_eq_prime_iff.mpr ⟨?_, ?_⟩
      · have hx2'' : x * x = 1 := by rw [← pow_two]; exact hx2'
        rw [pow_two,
          show h * x * h⁻¹ * (h * x * h⁻¹) = h * (x * x) * h⁻¹ by group, hx2'']
        simp
      · intro hc
        apply hxne
        have h1 : x = h⁻¹ * (h * x * h⁻¹) * h := by group
        rw [hc] at h1
        simpa using h1
  · simp

theorem H_le_normalizer_Q0sub (H : Subgroup G) :
    H ≤ Subgroup.normalizer (Q0sub H : Set G) := by
  have h1 : H ≤ Subgroup.normalizer (Q0 H : Set G) :=
    Subgroup.le_set_normalizer_iff.mpr (fun h hh x hx => Q0_conj_mem hh hx)
  exact h1.trans (Subgroup.normalizer_le_normalizer_closure (Q0 H))

/-! ## The action data -/

-- to be placed in namespace Work.ThmF.ChV12
theorem conj_action_data {G : Type} [Group G] (H : Subgroup G) (t : G)
    (hcomm : ∀ u ∈ Submission.Blueprint.involutions (H : Set G), ∀ v ∈ Submission.Blueprint.involutions (H : Set G), u * v = v * u)
    (hKn : ((Work.ThmF.Ksub H t).subgroupOf (Submission.Blueprint.twoPoint H t)).Normal) :
    ∃ (Φ : ↥(Work.ThmF.Ksub H t) →* (↥(Work.ThmF.Q0sub H) ≃* ↥(Work.ThmF.Q0sub H)))
      (Ψ : ↥(Submission.Blueprint.centD H t) →* (↥(Work.ThmF.Q0sub H) ≃* ↥(Work.ThmF.Q0sub H)))
      (T : ↥(Submission.Blueprint.centD H t) →* MulAut ↥(Work.ThmF.Ksub H t)),
      (∀ (k : ↥(Work.ThmF.Ksub H t)) (x : ↥(Work.ThmF.Q0sub H)),
        ((Φ k x : ↥(Work.ThmF.Q0sub H)) : G) = (k : G) * (x : G) * (k : G)⁻¹) ∧
      (∀ (u : ↥(Submission.Blueprint.centD H t)) (x : ↥(Work.ThmF.Q0sub H)),
        ((Ψ u x : ↥(Work.ThmF.Q0sub H)) : G) = (u : G) * (x : G) * (u : G)⁻¹) ∧
      (∀ (u : ↥(Submission.Blueprint.centD H t)) (k : ↥(Work.ThmF.Ksub H t)),
        ((T u k : ↥(Work.ThmF.Ksub H t)) : G) = (u : G) * (k : G) * (u : G)⁻¹) ∧
      (∀ (u : ↥(Submission.Blueprint.centD H t)) (k : ↥(Work.ThmF.Ksub H t)) (x : ↥(Work.ThmF.Q0sub H)),
        Ψ u (Φ k x) = Φ (T u k) (Ψ u x)) := by
  have hKsub_le_D : Ksub H t ≤ twoPoint H t :=
    (Subgroup.closure_le (twoPoint H t)).mpr (Kset_subset H t)
  have hcentD_le_D : centD H t ≤ twoPoint H t := inf_le_left
  have hD_le_H : twoPoint H t ≤ H := inf_le_left
  have hH_le := H_le_normalizer_Q0sub H
  have hKq : Ksub H t ≤ Subgroup.normalizer (Q0sub H : Set G) :=
    (hKsub_le_D.trans hD_le_H).trans hH_le
  have hDq : centD H t ≤ Subgroup.normalizer (Q0sub H : Set G) :=
    (hcentD_le_D.trans hD_le_H).trans hH_le
  have hDk : centD H t ≤ Subgroup.normalizer (Ksub H t : Set G) :=
    hcentD_le_D.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKsub_le_D).mp hKn)
  refine ⟨conjAutOfLe (Q0sub H) (Ksub H t) hKq,
          conjAutOfLe (Q0sub H) (centD H t) hDq,
          conjAutOfLe (Ksub H t) (centD H t) hDk, ?_, ?_, ?_, ?_⟩
  · intro k x; simp
  · intro u x; simp
  · intro u k; simp
  · intro u k x
    apply Subtype.ext
    simp only [conjAutOfLe_apply]
    group

end Work.ThmF.ChV12
