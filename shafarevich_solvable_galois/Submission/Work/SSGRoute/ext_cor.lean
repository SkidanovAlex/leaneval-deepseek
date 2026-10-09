import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_coind_exact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The trace `Coind_S^G (Res_S^G A) ⟶ A` and corestriction on derived `Ext`

This file adapts `Commons.RepresentationTheory.TateCohomology.coindTrace` (there for `Rep ℤ G` and
group cohomology) to the coefficient ring `Coeff = ULift ℤ` used by the `Ext` core, and records the
key identity `η ≫ coindTrace = [G : S] • 𝟙`, where `η` is the unit of the adjunction
`Rep.resCoindAdjunction Coeff S.subtype : Res_S^G ⊣ Coind_S^G`.
-/

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

variable {G : Type} [Group G] [Fintype G] (S : Subgroup G) [DecidableRel (QuotientGroup.rightRel S)]
  [Fintype (G ⧸ S)] (A : Rep Coeff G)

/-- The `q`-th coordinate functional `coindV → A`. -/
noncomputable def projFun (q : Quotient (QuotientGroup.rightRel S)) :
    (Representation.coindV S.subtype (Rep.res S.subtype A).ρ) →ₗ[Coeff] A :=
  (LinearMap.proj (Quotient.out q)).comp
    (Submodule.subtype (Representation.coindV S.subtype (Rep.res S.subtype A).ρ))

/-- The trace `coind_S^G(res_S^G A) → A`, `f ↦ ∑_q ρ(out q)⁻¹ (f (out q))`. -/
noncomputable def traceLin :
    (Representation.coindV S.subtype (Rep.res S.subtype A).ρ) →ₗ[Coeff] A :=
  ∑ q : Quotient (QuotientGroup.rightRel S), (A.ρ (Quotient.out q)⁻¹).comp (projFun S A q)

lemma traceLin_apply (f : ↥(Representation.coindV S.subtype (Rep.res S.subtype A).ρ)) :
    traceLin S A f = ∑ q : Quotient (QuotientGroup.rightRel S),
      A.ρ (Quotient.out q)⁻¹ (f.1 (Quotient.out q)) := by
  simp only [traceLin, LinearMap.sum_apply, LinearMap.comp_apply, projFun, LinearMap.proj_apply,
    Submodule.subtype_apply]

/-- Right multiplication by `g` on the space of right cosets of `S`. -/
noncomputable def cosetMul (g : G) :
    Quotient (QuotientGroup.rightRel S) → Quotient (QuotientGroup.rightRel S) :=
  Quotient.map (· * g) (fun x y h => QuotientGroup.rightRel_apply.2 (by
    have hh : y * x⁻¹ ∈ S := QuotientGroup.rightRel_apply.1 h
    simpa [mul_assoc] using hh))

lemma cosetMul_mk (g x : G) :
    cosetMul S g (Quotient.mk'' (s₁ := QuotientGroup.rightRel S) x) =
      Quotient.mk'' (s₁ := QuotientGroup.rightRel S) (x * g) := rfl

lemma cosetMul_bijective (g : G) : Function.Bijective (cosetMul S g) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h x =>
      induction b using Quotient.inductionOn with
      | h y =>
        simp only [cosetMul_mk] at hab
        have h : y * g * (x * g)⁻¹ ∈ S := QuotientGroup.rightRel_apply.1 (Quotient.exact hab)
        have h' : y * x⁻¹ ∈ S := by simpa [mul_assoc] using h
        exact Quotient.sound (QuotientGroup.rightRel_apply.2 h')
  · intro b
    induction b using Quotient.inductionOn with
    | h x =>
      refine ⟨Quotient.mk'' (s₁ := QuotientGroup.rightRel S) (x * g⁻¹), ?_⟩
      simp only [cosetMul_mk]
      simp

/-- The element of `S` measuring the failure of `Quotient.out` to be a section. -/
noncomputable def sval (g : G) (q : Quotient (QuotientGroup.rightRel S)) : S :=
  ⟨((Quotient.out (cosetMul S g q)) * (Quotient.out q * g)⁻¹)⁻¹, by
    have h : Quotient.mk'' (s₁ := QuotientGroup.rightRel S) (Quotient.out q * g) =
        Quotient.mk'' (s₁ := QuotientGroup.rightRel S) (Quotient.out (cosetMul S g q)) := by
      rw [show Quotient.mk'' (s₁ := QuotientGroup.rightRel S) (Quotient.out q * g) =
        cosetMul S g (Quotient.mk'' (s₁ := QuotientGroup.rightRel S) (Quotient.out q)) from rfl,
        Quotient.out_eq']
      exact (Quotient.out_eq' _).symm
    have hh := QuotientGroup.rightRel_apply.1 (Quotient.exact h)
    exact S.inv_mem hh⟩

lemma sval_spec (g : G) (q : Quotient (QuotientGroup.rightRel S)) :
    Quotient.out q * g = (sval S g q : G) * Quotient.out (cosetMul S g q) := by
  have hgt : (sval S g q : G) = ((Quotient.out (cosetMul S g q)) * (Quotient.out q * g)⁻¹)⁻¹ := rfl
  rw [hgt]
  group

/-- The summand reindexing identity underlying `traceLin_intertwines`. -/
lemma traceLin_summand (g : G) (f : ↥(Representation.coindV S.subtype (Rep.res S.subtype A).ρ))
    (q : Quotient (QuotientGroup.rightRel S)) :
    A.ρ (Quotient.out q)⁻¹ (f.1 (Quotient.out q * g)) =
      A.ρ g (A.ρ (Quotient.out (cosetMul S g q))⁻¹ (f.1 (Quotient.out (cosetMul S g q)))) := by
  have hco : f.1 ((sval S g q : G) * Quotient.out (cosetMul S g q)) =
      A.ρ (sval S g q : G) (f.1 (Quotient.out (cosetMul S g q))) := by
    have h := (Representation.mem_coindV (φ := S.subtype)
      (σ := (Rep.res S.subtype A).ρ) (f := f.1)).1 f.2 (sval S g q) (Quotient.out (cosetMul S g q))
    simpa [Rep.coe_res_obj_ρ', MonoidHom.comp_apply] using h
  have key : (Quotient.out q)⁻¹ * (sval S g q : G) = g * (Quotient.out (cosetMul S g q))⁻¹ := by
    have h := sval_spec S g q
    have h' : (sval S g q : G) = Quotient.out q * g * (Quotient.out (cosetMul S g q))⁻¹ := by
      rw [h]; group
    rw [h']; group
  calc A.ρ (Quotient.out q)⁻¹ (f.1 (Quotient.out q * g))
      = A.ρ (Quotient.out q)⁻¹ (f.1 ((sval S g q : G) * Quotient.out (cosetMul S g q))) := by
          rw [sval_spec S g q]
    _ = A.ρ (Quotient.out q)⁻¹ (A.ρ ((sval S g q : G)) (f.1 (Quotient.out (cosetMul S g q)))) := by
          rw [hco]
    _ = A.ρ ((Quotient.out q)⁻¹ * (sval S g q : G)) (f.1 (Quotient.out (cosetMul S g q))) := by
          simp only [map_mul, Module.End.mul_apply]
    _ = A.ρ (g * (Quotient.out (cosetMul S g q))⁻¹) (f.1 (Quotient.out (cosetMul S g q))) := by
          rw [key]
    _ = A.ρ g (A.ρ (Quotient.out (cosetMul S g q))⁻¹ (f.1 (Quotient.out (cosetMul S g q)))) := by
          simp only [map_mul, Module.End.mul_apply]

/-- The trace is `G`-equivariant. -/
lemma traceLin_intertwines (g : G) :
    traceLin S A ∘ₗ (Representation.coind S.subtype (Rep.res S.subtype A).ρ) g =
      (A.ρ g) ∘ₗ traceLin S A := by
  ext f
  rw [LinearMap.comp_apply, LinearMap.comp_apply, traceLin_apply, traceLin_apply, map_sum]
  refine Fintype.sum_bijective (cosetMul S g) (cosetMul_bijective S g) _ _
    (fun q => traceLin_summand S A g f q)

/-- The trace `coind_S^G (res_S^G A) ⟶ A` as a morphism of `G`-representations. -/
noncomputable def coindTrace : Rep.coind S.subtype (Rep.res S.subtype A) ⟶ A :=
  Rep.ofHom ⟨traceLin S A, traceLin_intertwines S A⟩

lemma resCoind_unit_eq :
    (Rep.resCoindAdjunction Coeff S.subtype).unit.app A =
      Rep.resCoindToHom S.subtype A (Rep.res S.subtype A) (𝟙 (Rep.res S.subtype A)) := rfl

lemma resCoind_unit_apply_coe (m : A.V) (i : G) :
    (((Rep.resCoindAdjunction Coeff S.subtype).unit.app A).hom m).1 i = A.ρ i m := by
  rw [resCoind_unit_eq S A]
  have h := Rep.resCoindToHom_hom_apply_coe S.subtype A (Rep.res S.subtype A)
    (𝟙 (Rep.res S.subtype A)) m i
  simpa using h

lemma card_quotient_rightRel_eq_index :
    Fintype.card (Quotient (QuotientGroup.rightRel S)) = S.index := by
  rw [QuotientGroup.card_quotient_rightRel S, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

/-- **The trace identity** `η ≫ coindTrace = [G : S] • 𝟙`. -/
lemma unit_comp_coindTrace :
    (Rep.resCoindAdjunction Coeff S.subtype).unit.app A ≫ coindTrace S A = S.index • 𝟙 A := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro m
  have hcomp :
      (Rep.Hom.hom ((Rep.resCoindAdjunction Coeff S.subtype).unit.app A ≫ coindTrace S A)).toLinearMap
        = (coindTrace S A).hom.toLinearMap ∘ₗ
          ((Rep.resCoindAdjunction Coeff S.subtype).unit.app A).hom.toLinearMap := rfl
  rw [hcomp]
  show (traceLin S A (((Rep.resCoindAdjunction Coeff S.subtype).unit.app A).hom m)) = _
  rw [traceLin_apply]
  have hsum : (∑ q : Quotient (QuotientGroup.rightRel S),
      A.ρ (Quotient.out q)⁻¹
        ((((Rep.resCoindAdjunction Coeff S.subtype).unit.app A).hom m).1 (Quotient.out q)))
      = ∑ _q : Quotient (QuotientGroup.rightRel S), m := by
    apply Finset.sum_congr rfl
    intro q _
    rw [resCoind_unit_apply_coe S A m (Quotient.out q)]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hsum, Finset.sum_const, Finset.card_univ, card_quotient_rightRel_eq_index S]
  rw [Rep.nsmul_hom]
  rfl

end Work.SSGRoute
