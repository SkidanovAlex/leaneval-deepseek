import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic.Have
import Mathlib.Algebra.Torsor.Defs
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Submission.Commons.RepresentationTheory.GroupCohomology.groupCohomology_two_int_iso_one_qmodz
import Submission.Commons.RepresentationTheory.GroupCohomology.unit_coindIso_eq_resNatTrans
import Submission.Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_of_subsingleton_H1_H2_of_solvable
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open CategoryTheory Limits

namespace NU

variable {G : Type} [Group G] [Fintype G]

section Trace
variable (S : Subgroup G) (M : Rep ℤ G)

noncomputable local instance instMV : Module ℤ M.V := M.hV2

noncomputable abbrev coindMid : Rep ℤ G := Rep.coind S.subtype (Rep.res S.subtype M)

noncomputable local instance instCoindV : Module ℤ (coindMid S M).V := (coindMid S M).hV2

/-- The `q`-th coordinate functional `coindV → M`. -/
noncomputable def projFun (q : Quotient (QuotientGroup.rightRel S)) :
    (Representation.coindV S.subtype (Rep.res S.subtype M).ρ) →ₗ[ℤ] M :=
  (LinearMap.proj (Quotient.out q)).comp
    (Submodule.subtype (Representation.coindV S.subtype (Rep.res S.subtype M).ρ))

/-- The trace `coind_S^G(res_S^G M) → M`, `f ↦ ∑_q ρ(out q)⁻¹ (f (out q))`. -/
noncomputable def traceLin :
    (Representation.coindV S.subtype (Rep.res S.subtype M).ρ) →ₗ[ℤ] M :=
  ∑ q : Quotient (QuotientGroup.rightRel S), (M.ρ (Quotient.out q)⁻¹).comp (projFun S M q)

lemma traceLin_apply (f : ↥(Representation.coindV S.subtype (Rep.res S.subtype M).ρ)) :
    traceLin S M f = ∑ q : Quotient (QuotientGroup.rightRel S),
      M.ρ (Quotient.out q)⁻¹ (f.1 (Quotient.out q)) := by
  simp only [traceLin, LinearMap.sum_apply, LinearMap.comp_apply, projFun, LinearMap.proj_apply,
    Submodule.subtype_apply]

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

noncomputable def sval (g : G) (q : Quotient (QuotientGroup.rightRel S)) : S :=
  ⟨((Quotient.out (cosetMul S g q)) * (Quotient.out q * g)⁻¹)⁻¹, by
    have h : Quotient.mk'' (s₁ := QuotientGroup.rightRel S) (Quotient.out q * g) =
        Quotient.mk'' (s₁ := QuotientGroup.rightRel S) (Quotient.out (cosetMul S g q)) := by
      rw [← cosetMul_mk S g (Quotient.out q), Quotient.out_eq']
      exact (Quotient.out_eq' _).symm
    have hh := QuotientGroup.rightRel_apply.1 (Quotient.exact h)
    exact S.inv_mem hh⟩

lemma sval_spec (g : G) (q : Quotient (QuotientGroup.rightRel S)) :
    Quotient.out q * g = (sval S g q : G) * Quotient.out (cosetMul S g q) := by
  have h : Quotient.mk'' (s₁ := QuotientGroup.rightRel S) (Quotient.out q * g) =
      Quotient.mk'' (s₁ := QuotientGroup.rightRel S) (Quotient.out (cosetMul S g q)) := by
    rw [← cosetMul_mk S g (Quotient.out q), Quotient.out_eq']
    exact (Quotient.out_eq' _).symm
  have hh : Quotient.out (cosetMul S g q) * (Quotient.out q * g)⁻¹ ∈ S :=
    QuotientGroup.rightRel_apply.1 (Quotient.exact h)
  have hgt : (sval S g q : G) = ((Quotient.out (cosetMul S g q)) * (Quotient.out q * g)⁻¹)⁻¹ := rfl
  rw [hgt]
  group

lemma traceLin_summand (g : G) (f : ↥(Representation.coindV S.subtype (Rep.res S.subtype M).ρ))
    (q : Quotient (QuotientGroup.rightRel S)) :
    M.ρ (Quotient.out q)⁻¹ (f.1 (Quotient.out q * g)) =
      M.ρ g (M.ρ (Quotient.out (cosetMul S g q))⁻¹ (f.1 (Quotient.out (cosetMul S g q)))) := by
  have hco : f.1 ((sval S g q : G) * Quotient.out (cosetMul S g q)) =
      M.ρ ((sval S g q : G)) (f.1 (Quotient.out (cosetMul S g q))) := by
    have h := (Representation.mem_coindV (φ := S.subtype)
      (σ := (Rep.res S.subtype M).ρ) (f := f.1)).1 f.2 (sval S g q) (Quotient.out (cosetMul S g q))
    simpa [Rep.coe_res_obj_ρ', MonoidHom.comp_apply] using h
  have key : (Quotient.out q)⁻¹ * (sval S g q : G) =
      g * (Quotient.out (cosetMul S g q))⁻¹ := by
    have h := sval_spec S g q
    have h' : (sval S g q : G) = Quotient.out q * g * (Quotient.out (cosetMul S g q))⁻¹ := by
      rw [h]; group
    rw [h']; group
  calc M.ρ (Quotient.out q)⁻¹ (f.1 (Quotient.out q * g))
      = M.ρ (Quotient.out q)⁻¹ (f.1 ((sval S g q : G) * Quotient.out (cosetMul S g q))) := by
          rw [sval_spec S g q]
    _ = M.ρ (Quotient.out q)⁻¹ (M.ρ ((sval S g q : G)) (f.1 (Quotient.out (cosetMul S g q)))) := by
          rw [hco]
    _ = M.ρ ((Quotient.out q)⁻¹ * (sval S g q : G)) (f.1 (Quotient.out (cosetMul S g q))) := by
          simp only [map_mul, Module.End.mul_apply]
    _ = M.ρ (g * (Quotient.out (cosetMul S g q))⁻¹) (f.1 (Quotient.out (cosetMul S g q))) := by
          rw [key]
    _ = M.ρ g (M.ρ (Quotient.out (cosetMul S g q))⁻¹ (f.1 (Quotient.out (cosetMul S g q)))) := by
          simp only [map_mul, Module.End.mul_apply]

lemma traceLin_intertwines (g : G) :
    traceLin S M ∘ₗ (Representation.coind S.subtype (Rep.res S.subtype M).ρ) g =
      (M.ρ g) ∘ₗ traceLin S M := by
  ext f
  rw [LinearMap.comp_apply, LinearMap.comp_apply, traceLin_apply, traceLin_apply, map_sum]
  refine Fintype.sum_bijective (cosetMul S g) (cosetMul_bijective S g) _ _
    (fun q => traceLin_summand S M g f q)

noncomputable def coindTrace : Rep.coind S.subtype (Rep.res S.subtype M) ⟶ M :=
  Rep.ofHom ⟨traceLin S M, traceLin_intertwines S M⟩

end Trace

variable {G : Type} [Group G] [Fintype G]

section Units
variable (S : Subgroup G) (M : Rep ℤ G)

noncomputable local instance instMV2 : Module ℤ M.V := M.hV2

noncomputable abbrev coindMid2 : Rep ℤ G := Rep.coind S.subtype (Rep.res S.subtype M)

noncomputable local instance instCoindV2 : Module ℤ (coindMid2 S M).V := (coindMid2 S M).hV2

lemma resCoind_unit_eq :
    (Rep.resCoindAdjunction ℤ S.subtype).unit.app M =
      Rep.resCoindToHom S.subtype M (Rep.res S.subtype M) (𝟙 (Rep.res S.subtype M)) := rfl

lemma resCoind_unit_apply_coe (m : M.V) (i : G) :
    (((Rep.resCoindAdjunction ℤ S.subtype).unit.app M).hom m).1 i = M.ρ i m := by
  rw [resCoind_unit_eq S M]
  have h := Rep.resCoindToHom_hom_apply_coe S.subtype M (Rep.res S.subtype M)
    (𝟙 (Rep.res S.subtype M)) m i
  simpa using h

end Units

variable {G : Type} [Group G] [Fintype G]

section Main
variable (S : Subgroup G) (M : Rep ℤ G)

noncomputable local instance instMV3 : Module ℤ M.V := M.hV2

noncomputable abbrev coindMid3 : Rep ℤ G := Rep.coind S.subtype (Rep.res S.subtype M)

noncomputable local instance instCoindV3 : Module ℤ (coindMid3 S M).V := (coindMid3 S M).hV2

lemma card_quotient_rightRel_eq_index :
    Fintype.card (Quotient (QuotientGroup.rightRel S)) = S.index := by
  rw [QuotientGroup.card_quotient_rightRel, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

lemma unit_comp_coindTrace :
    (Rep.resCoindAdjunction ℤ S.subtype).unit.app M ≫ coindTrace S M = S.index • 𝟙 M := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro m
  have hcomp :
      (Rep.Hom.hom ((Rep.resCoindAdjunction ℤ S.subtype).unit.app M ≫ coindTrace S M)).toLinearMap
        = (coindTrace S M).hom.toLinearMap ∘ₗ
          ((Rep.resCoindAdjunction ℤ S.subtype).unit.app M).hom.toLinearMap := rfl
  rw [hcomp]
  show (traceLin S M (((Rep.resCoindAdjunction ℤ S.subtype).unit.app M).hom m)) = _
  rw [traceLin_apply]
  have hsum : (∑ q : Quotient (QuotientGroup.rightRel S),
      M.ρ (Quotient.out q)⁻¹
        ((((Rep.resCoindAdjunction ℤ S.subtype).unit.app M).hom m).1 (Quotient.out q)))
      = ∑ _q : Quotient (QuotientGroup.rightRel S), m := by
    apply Finset.sum_congr rfl
    intro q _
    rw [resCoind_unit_apply_coe S M m (Quotient.out q)]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hsum, Finset.sum_const, Finset.card_univ]
  rw [card_quotient_rightRel_eq_index S]
  rfl

end Main

variable {G : Type} [Group G] [Fintype G]

section Cor
variable (S : Subgroup G) (M : Rep ℤ G)

noncomputable local instance instMV4 : Module ℤ M.V := M.hV2

noncomputable abbrev coindMid4 : Rep ℤ G := Rep.coind S.subtype (Rep.res S.subtype M)

noncomputable local instance instCoindV4 : Module ℤ (coindMid4 S M).V := (coindMid4 S M).hV2

instance functorAdditive (n : ℕ) : (groupCohomology.functor ℤ G n).Additive where
  map_add {X Y f g} := by
    rw [groupCohomology.functor_map, groupCohomology.functor_map, groupCohomology.functor_map]
    simp only [groupCohomology.map]
    have h : groupCohomology.cochainsMap (MonoidHom.id G) (f + g)
        = groupCohomology.cochainsMap (MonoidHom.id G) f
          + groupCohomology.cochainsMap (MonoidHom.id G) g := by
      have h2 := Functor.map_add (groupCohomology.cochainsFunctor ℤ G) (f := f) (g := g)
      simp only [groupCohomology.cochainsFunctor_map] at h2
      exact h2
    rw [h, HomologicalComplex.homologyMap_add]

lemma map_id_nsmul (n m : ℕ) :
    groupCohomology.map (MonoidHom.id G) (m • 𝟙 M) n =
      m • 𝟙 (groupCohomology M n) := by
  change (groupCohomology.functor ℤ G n).map (m • 𝟙 M) =
    m • 𝟙 ((groupCohomology.functor ℤ G n).obj M)
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]

noncomputable def cor (n : ℕ) :
    groupCohomology (Rep.res S.subtype M) n ⟶ groupCohomology M n :=
  (groupCohomology.coindIso (Rep.res S.subtype M) n).inv ≫
    groupCohomology.map (MonoidHom.id G) (coindTrace S M) n

theorem resNatTrans_comp_cor (n : ℕ) :
    (groupCohomology.resNatTrans ℤ (G := S) (H := G) S.subtype n).app M ≫ cor S M n =
      S.index • 𝟙 (groupCohomology M n) := by
  rw [cor, ← Commons.RepresentationTheory.GroupCohomology.unit_coindIso_eq_resNatTrans S M n]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id]
  rw [← groupCohomology.map_id_comp, unit_comp_coindTrace S M]
  exact map_id_nsmul (G := G) (M := M) n S.index

theorem cor_resNatTrans_comp_apply (n : ℕ)
    (x : (groupCohomology.functor ℤ G n).obj M) :
    ((groupCohomology.resNatTrans ℤ (G := S) (H := G) S.subtype n).app M ≫ cor S M n) x =
      S.index • x :=
  congrArg (fun f => f x) (resNatTrans_comp_cor S M n)

end Cor

variable {G : Type} [Group G] [Fintype G]

section Gen
variable (S : Subgroup G) (M : Rep.{0,0,0} ℤ G)

noncomputable local instance instMV5 : Module ℤ M.V := M.hV2

noncomputable abbrev coindMid5 : Rep ℤ G := Rep.coind S.subtype (Rep.res S.subtype M)

noncomputable local instance instCoindV5 : Module ℤ (coindMid5 S M).V := (coindMid5 S M).hV2

lemma index_ne_zero : S.index ≠ 0 := by
  intro h
  have hG := Subgroup.index_mul_card S
  rw [h, zero_mul] at hG
  exact absurd hG.symm (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)

theorem addOrderOf_resNatTrans_two (α : groupCohomology M 2) (hα : addOrderOf α = Nat.card G)
    (h2 : Nat.card (groupCohomology (Rep.res S.subtype M) 2) = Nat.card S) :
    addOrderOf ((groupCohomology.resNatTrans ℤ (G := S) (H := G) S.subtype 2).app M α) =
      Nat.card S := by
  set β := (groupCohomology.resNatTrans ℤ (G := S) (H := G) S.subtype 2).app M α with hβ
  have hcor : (cor S M 2) β = S.index • α := by
    have h := cor_resNatTrans_comp_apply S M 2
      (show (groupCohomology.functor ℤ G 2).obj M from α)
    rw [ConcreteCategory.comp_apply] at h
    exact h
  have hord : addOrderOf ((cor S M 2) β) = Nat.card S := by
    rw [hcor, addOrderOf_nsmul' α (index_ne_zero S), hα, ← Subgroup.card_mul_index S,
      Nat.gcd_eq_right (dvd_mul_left S.index (Nat.card ↥S))]
    exact Nat.mul_div_cancel (Nat.card ↥S) (Nat.pos_of_ne_zero (index_ne_zero S))
  have hdvd1 : addOrderOf ((cor S M 2) β) ∣ addOrderOf β :=
    addOrderOf_map_dvd (ModuleCat.Hom.hom (cor S M 2)).toAddMonoidHom β
  rw [hord] at hdvd1
  have hdvd2 : addOrderOf β ∣ Nat.card S := by
    rw [← h2]
    exact addOrderOf_dvd_natCard β
  exact Nat.dvd_antisymm hdvd2 hdvd1

end Gen




variable {G : Type} [Group G] [Fintype G]

noncomputable def augLin : MonoidAlgebra ℤ G →ₗ[ℤ] ℤ :=
  (MonoidAlgebra.lift ℤ ℤ G (1 : G →* ℤ)).toLinearMap

@[simp] lemma augLin_single (h : G) (r : ℤ) : augLin (MonoidAlgebra.single h r) = r := by
  simp [augLin]

lemma augLin_mul (g : G) (x : MonoidAlgebra ℤ G) :
    augLin ((Representation.ofMulAction ℤ G G) g x) = augLin x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb]
  | single h r =>
      rw [Representation.ofMulAction_single]
      simp

noncomputable def aug : Rep.leftRegular ℤ G ⟶ Rep.trivial ℤ G ℤ :=
  Rep.ofHom (show (Rep.leftRegular ℤ G).ρ.IntertwiningMap (Rep.trivial ℤ G ℤ).ρ from
    ⟨augLin, by
      intro g
      ext x
      simp only [LinearMap.comp_apply]
      rw [augLin_mul]
      simp⟩)

lemma aug_surjective : Function.Surjective (aug (G := G)).hom := by
  intro n
  refine ⟨MonoidAlgebra.single (1 : G) n, ?_⟩
  simp [aug]

noncomputable def augShort : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (kernel.ι (aug (G := G))) (aug (G := G)) (kernel.condition _)

lemma augShort_shortExact : (augShort (G := G)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  · exact inferInstanceAs (Mono (kernel.ι (aug (G := G))))
  · exact (Rep.epi_iff_surjective _).2 aug_surjective



set_option maxHeartbeats 800000


variable {G : Type} [Group G]

/-- The left regular representation `ℤ[G]` of a finite group `G` is the coinduction from the
trivial subgroup of the trivial representation (`G → ℤ` with the action `(g • f) x = f (x * g)`),
via the intertwining `f ↦ (x ↦ f.coeff x⁻¹)` (which converts the right regular action into the
left regular one). -/
noncomputable def leftRegularIsoCoind (G : Type) [Group G] [Fintype G] :
    Rep.leftRegular ℤ G ≅
      Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial ℤ (↥(⊥ : Subgroup G)) ℤ) := by
  classical
  set W : Rep ℤ (↥(⊥ : Subgroup G)) := Rep.trivial ℤ (↥(⊥ : Subgroup G)) ℤ with hW
  set σ : Representation ℤ G (Representation.coindV (⊥ : Subgroup G).subtype W.ρ) :=
    (Rep.coind (⊥ : Subgroup G).subtype W).ρ with hσ
  -- the linear map `ℤ[G] → (G → ℤ)`, `f ↦ (x ↦ f.coeff x⁻¹)`
  let pinv : (G → ℤ) ≃ₗ[ℤ] (G → ℤ) := LinearEquiv.funCongrLeft ℤ ℤ (Equiv.inv G)
  have hpinv : ∀ h : G → ℤ, pinv h = fun x => h x⁻¹ := fun h => by ext x; rfl
  let eLin : MonoidAlgebra ℤ G →ₗ[ℤ] (G → ℤ) :=
    ((MonoidAlgebra.coeffLinearEquiv (R := ℤ) (S := ℤ) (M := G)).trans
      (Finsupp.linearEquivFunOnFinite ℤ ℤ G)).trans pinv |>.toLinearMap
  have heLin_aux : ∀ f : MonoidAlgebra ℤ G,
      eLin f = pinv (Finsupp.linearEquivFunOnFinite ℤ ℤ G (MonoidAlgebra.coeff f)) :=
    fun _ => rfl
  have heLin : ∀ f : MonoidAlgebra ℤ G, eLin f = fun x => (MonoidAlgebra.coeff f) x⁻¹ := by
    intro f
    rw [heLin_aux, hpinv]
    rfl
  have hinj : Function.Injective eLin := by
    intro f g h
    apply MonoidAlgebra.coeff_injective
    ext y
    have h2 := congrFun h y⁻¹
    rw [heLin f, heLin g] at h2
    simpa using h2
  have hsurj : Function.Surjective eLin := by
    intro h
    refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm (fun x => h x⁻¹)), ?_⟩
    ext x
    rw [heLin]
    simp
  have hmem : ∀ f : MonoidAlgebra ℤ G,
      eLin f ∈ Representation.coindV (⊥ : Subgroup G).subtype W.ρ := by
    intro f
    rw [Representation.mem_coindV]
    intro s h
    rw [show ((⊥ : Subgroup G).subtype s : G) = 1 from Subgroup.mem_bot.mp s.2, one_mul]
    simp [heLin, W, Rep.trivial]
  let e : MonoidAlgebra ℤ G →ₗ[ℤ] Representation.coindV (⊥ : Subgroup G).subtype W.ρ :=
    eLin.codRestrict _ hmem
  have he : ∀ f : MonoidAlgebra ℤ G,
      ((e f : Representation.coindV (⊥ : Subgroup G).subtype W.ρ) : G → ℤ)
        = fun x => (MonoidAlgebra.coeff f) x⁻¹ := fun f => rfl
  have hbij : Function.Bijective e := by
    constructor
    · intro f g hfg
      apply hinj
      have h2 := congrArg (Subtype.val) hfg
      simpa [e] using h2
    · intro g
      obtain ⟨f, hf⟩ := hsurj (g : G → ℤ)
      refine ⟨f, ?_⟩
      apply Subtype.ext
      simpa [e] using hf
  let eL : MonoidAlgebra ℤ G ≃ₗ[ℤ] Representation.coindV (⊥ : Subgroup G).subtype W.ρ :=
    LinearEquiv.ofBijective e hbij
  have heL : ∀ f : MonoidAlgebra ℤ G,
      ((eL f : Representation.coindV (⊥ : Subgroup G).subtype W.ρ) : G → ℤ)
        = fun x => (MonoidAlgebra.coeff f) x⁻¹ := fun f => he f
  refine Rep.mkIso (Representation.Equiv.mk eL ?_)
  intro g
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [heL]
  change (MonoidAlgebra.coeff ((Representation.ofMulAction ℤ G G) g f)) x⁻¹
      = ((eL f : Representation.coindV (⊥ : Subgroup G).subtype W.ρ) : G → ℤ) (x * g)
  rw [heL]
  show (MonoidAlgebra.coeff ((Representation.ofMulAction ℤ G G) g f)) x⁻¹
      = (fun y => (MonoidAlgebra.coeff f) y⁻¹) (x * g)
  rw [Representation.coeff_ofMulAction]
  simp only [smul_eq_mul, mul_inv_rev]

/-- The Tate cohomology of the left regular representation `ℤ[G]` vanishes in every degree. -/
theorem subsingleton_tateCohomology_res_leftRegular {G : Type} [Group G] [Fintype G]
    (K : Subgroup G) (r : ℤ) :
    Subsingleton (tateCohomology (Rep.res K.subtype (Rep.leftRegular ℤ G)) r) := by
  haveI h := Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_coind_bot_restrict_all
    (G := G) K (Rep.trivial ℤ (↥(⊥ : Subgroup G)) ℤ) r
  exact ((tateCohomologyFunctor (R := ℤ) (G := K) r).mapIso
    ((Rep.resFunctor K.subtype).mapIso (leftRegularIsoCoind G))).toLinearEquiv.injective.subsingleton

theorem subsingleton_tateCohomology_leftRegular (G : Type) [Group G] [Fintype G] (r : ℤ) :
    Subsingleton (tateCohomology (Rep.leftRegular ℤ G) r) := by
  have h := Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_coind_bot (G := G)
    (Rep.trivial ℤ (↥(⊥ : Subgroup G)) ℤ) r
  haveI : Subsingleton (tateCohomology (Rep.coind (⊥ : Subgroup G).subtype
    (Rep.trivial ℤ (↥(⊥ : Subgroup G)) ℤ)) r) := h
  exact ((tateCohomologyFunctor r).mapIso (leftRegularIsoCoind G)).toLinearEquiv.injective.subsingleton




lemma invariants_trivial (K : Type) [Group K] [Fintype K] :
    Representation.invariants (Rep.trivial ℤ K ℤ).ρ = ⊤ := by
  ext v
  rw [Representation.mem_invariants]
  simp

lemma norm_trivial (K : Type) [Group K] [Fintype K] :
    Representation.norm (Rep.trivial ℤ K ℤ).ρ = Nat.card K • (1 : ℤ →ₗ[ℤ] ℤ) := by
  rw [Representation.norm]
  show (∑ _g : K, (1 : ℤ →ₗ[ℤ] ℤ)) = _
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

lemma range_nsmul_one (n : ℕ) :
    LinearMap.range (n • (1 : ℤ →ₗ[ℤ] ℤ)) = Submodule.span ℤ ({(n : ℤ)} : Set ℤ) := by
  ext x
  rw [LinearMap.mem_range, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    simp [nsmul_eq_mul, mul_comm]
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    simp [nsmul_eq_mul, mul_comm]



lemma natCard_int_quotient_span (n : ℕ) :
    Nat.card (ℤ ⧸ Submodule.span ℤ ({(n : ℤ)} : Set ℤ)) = n := by
  rw [show Submodule.span ℤ ({(n : ℤ)} : Set ℤ) = (Ideal.span {(n : ℤ)} : Ideal ℤ) from rfl]
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod n).toEquiv]
  rcases eq_or_ne n 0 with h | h
  · subst h
    rw [Nat.card_eq_zero_of_infinite]
  · haveI : NeZero n := ⟨h⟩
    rw [Nat.card_eq_fintype_card, ZMod.card n]

lemma natCard_tateCohomology_zero_trivial (K : Type) [Group K] [Fintype K] :
    Nat.card (tateCohomology (Rep.trivial ℤ K ℤ) 0) = Nat.card K := by
  obtain ⟨e⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
    (Rep.trivial ℤ K ℤ).ρ
  rw [Nat.card_congr e.toEquiv]
  rw [invariants_trivial, norm_trivial, range_nsmul_one]
  rw [Nat.card_congr (Submodule.Quotient.equiv _ _ (Submodule.topEquiv) ?_).toEquiv]
  · exact natCard_int_quotient_span (Nat.card K)
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨⟨y, trivial⟩, hy, rfl⟩


variable {G : Type} [Group G] [Fintype G]

theorem natCard_groupCohomology_res_augKernel_one (K : Subgroup G) :
    Nat.card (groupCohomology (Rep.res K.subtype (kernel (aug (G := G)))) 1) = Nat.card K := by
  set S : ShortComplex (Rep ℤ K) := (augShort (G := G)).map (Rep.resFunctor K.subtype) with hS
  have hX1 : S.X₁ = Rep.res K.subtype (kernel (aug (G := G))) := rfl
  have hX2 : S.X₂ = Rep.res K.subtype (Rep.leftRegular ℤ G) := rfl
  have hX3 : S.X₃ = Rep.res K.subtype (Rep.trivial ℤ G ℤ) := rfl
  have hse : S.ShortExact := (Rep.shortExact_res K.subtype).mpr (augShort_shortExact (G := G))
  have h0 : Subsingleton (tateCohomology S.X₂ 0) := by
    rw [hX2]; exact subsingleton_tateCohomology_res_leftRegular K 0
  have h1 : Subsingleton (tateCohomology S.X₂ 1) := by
    rw [hX2]; exact subsingleton_tateCohomology_res_leftRegular K 1
  obtain ⟨e⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_iso_of_acyclic_middle_of_subsingleton
    S hse 0 h0 h1
  have h3 : Nat.card (tateCohomology S.X₃ 0) = Nat.card K := by
    rw [hX3]
    exact natCard_tateCohomology_zero_trivial K
  have h1' : Nat.card (tateCohomology S.X₁ 1) = Nat.card K := by
    have h := Nat.card_congr e.symm.toEquiv
    rw [h3] at h
    exact h
  rw [hX1] at h1'
  have key : Nat.card (tateCohomology (Rep.res K.subtype (kernel (aug (G := G)))) 1) =
      Nat.card (groupCohomology (Rep.res K.subtype (kernel (aug (G := G)))) 1) :=
    Nat.card_congr (((TateCohomology.isoGroupCohomology (R := ℤ) (G := K) 1).app
      (Rep.res K.subtype (kernel (aug (G := G))))).toLinearEquiv.toEquiv)
  rw [← key]
  exact h1'




variable {G : Type} [Group G] [Fintype G]

section
variable (C : Rep ℤ G)
noncomputable local instance instCV : Module ℤ C.V := C.hV2

noncomputable def PhiLin (φ : G → G → C.V) (g : G) : MonoidAlgebra ℤ G →ₗ[ℤ] C.V :=
  (Finsupp.linearCombination ℤ (φ g)).comp
    (MonoidAlgebra.coeffLinearEquiv (R := ℤ) (M := G)).toLinearMap

lemma PhiLin_single (φ : G → G → C.V) (g σ : G) (r : ℤ) :
    PhiLin C φ g (MonoidAlgebra.single σ r) = r • φ g σ := by
  show (Finsupp.linearCombination ℤ (φ g))
    ((MonoidAlgebra.coeffLinearEquiv (R := ℤ) (M := G)) (MonoidAlgebra.single σ r)) = r • φ g σ
  rw [MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single,
    Finsupp.linearCombination_single]
  exact int_smul_eq_zsmul C.hV2 r (φ g σ)

noncomputable def FLin (φ : G → G → C.V) (g h : G) : MonoidAlgebra ℤ G →ₗ[ℤ] C.V :=
  C.ρ g ∘ₗ PhiLin C φ h + PhiLin C φ g ∘ₗ (Representation.ofMulAction ℤ G G) h
    - PhiLin C φ (g * h)

lemma FLin_apply (φ : G → G → C.V) (g h : G) (x : MonoidAlgebra ℤ G) :
    FLin C φ g h x = C.ρ g (PhiLin C φ h x)
      + PhiLin C φ g ((Representation.ofMulAction ℤ G G) h x) - PhiLin C φ (g * h) x := by
  simp only [FLin, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply]

lemma FLin_generator (φ : G → G → C.V)
    (hφ : ∀ g h k, C.ρ g (φ h k) + φ g (h * k) = φ (g * h) k + φ g h)
    (hφ1 : ∀ g, φ g 1 = 0) (g h σ : G) :
    FLin C φ g h (MonoidAlgebra.single σ 1 - MonoidAlgebra.single 1 1) = 0 := by
  rw [map_sub, FLin_apply, FLin_apply]
  simp only [PhiLin_single, one_smul, Representation.ofMulAction_single, hφ1, smul_zero,
    sub_zero, map_zero, add_zero, smul_eq_mul, mul_one, zero_add]
  rw [show C.ρ g (φ h σ) + φ g (h * σ) - φ (g * h) σ - φ g h
      = (C.ρ g (φ h σ) + φ g (h * σ)) - (φ (g * h) σ + φ g h) from by abel]
  rw [hφ g h σ, sub_self]

end

variable {G : Type} [Group G] [Fintype G]

section
variable (C : Rep ℤ G)
noncomputable local instance instCV3 : Module ℤ C.V := C.hV2

lemma coeff_sum_eq (x : MonoidAlgebra ℤ G) :
    (∑ σ : G, x.coeff σ • (MonoidAlgebra.single σ 1 - MonoidAlgebra.single 1 1))
      = x - (augLin x) • MonoidAlgebra.single 1 1 := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      have h1 : (a + b).coeff = a.coeff + b.coeff := rfl
      rw [h1, map_add]
      simp only [Finsupp.add_apply, add_smul, Finset.sum_add_distrib, add_smul]
      rw [ha, hb]
      module
  | single τ r =>
      rw [Finset.sum_eq_single τ]
      · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same, augLin_single]
        rw [smul_sub, MonoidAlgebra.smul_single, MonoidAlgebra.smul_single]
        simp
      · intro σ _ hσ
        rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hσ)]
        exact zero_smul _ _
      · intro h
        exact absurd (Finset.mem_univ τ) h

lemma FLin_eq_zero_of_augLin_eq_zero (φ : G → G → C.V)
    (hφ : ∀ g h k, C.ρ g (φ h k) + φ g (h * k) = φ (g * h) k + φ g h)
    (hφ1 : ∀ g, φ g 1 = 0) (g h : G) (x : MonoidAlgebra ℤ G) (hx : augLin x = 0) :
    FLin C φ g h x = 0 := by
  have hx' : x = ∑ σ : G, x.coeff σ • (MonoidAlgebra.single σ 1 - MonoidAlgebra.single 1 1) := by
    have h := coeff_sum_eq (G := G) x
    rw [hx, zero_smul, sub_zero] at h
    exact h.symm
  rw [hx', map_sum]
  apply Finset.sum_eq_zero
  intro σ _
  rw [LinearMap.map_smul, FLin_generator C φ hφ hφ1 g h σ, smul_zero]

end


variable {G : Type} [Group G] [Fintype G]

noncomputable abbrev augKer : Submodule ℤ (MonoidAlgebra ℤ G) := LinearMap.ker (augLin (G := G))

noncomputable def Iρ : Representation ℤ G ↥(augKer (G := G)) where
  toFun g := ((Representation.ofMulAction ℤ G G) g).restrict (fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [augLin_mul]
    exact hx)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [mul_smul]

section
variable (C : Rep ℤ G) (φ : G → G → C.V)
noncomputable local instance instCV4 : Module ℤ C.V := C.hV2
noncomputable local instance instProd : Module ℤ (C.V × ↥(augKer (G := G))) := Prod.instModule

lemma phi_one_left (hφ : ∀ g h k, C.ρ g (φ h k) + φ g (h * k) = φ (g * h) k + φ g h)
    (hφ1 : ∀ g, φ g 1 = 0) (g : G) : φ 1 g = 0 := by
  have h := hφ 1 1 g
  simp only [hφ1 1, one_mul, mul_one] at h
  rw [map_one, Module.End.one_apply] at h
  have h2 : φ 1 g + φ 1 g = φ 1 g + 0 := by rw [h, add_zero]
  exact add_left_cancel h2

lemma PhiLin_one (h1 : ∀ g, φ 1 g = 0) : PhiLin C φ 1 = 0 := by
  have hzero : (Finsupp.linearCombination ℤ (φ 1) : (G →₀ ℤ) →ₗ[ℤ] C.V) = 0 := by
    rw [show (φ 1) = (0 : G → C.V) from funext h1, Finsupp.linearCombination_zero]
  rw [PhiLin, hzero, LinearMap.zero_comp]

noncomputable def PhiKer (φ : G → G → C.V) (g : G) : ↥(augKer (G := G)) →ₗ[ℤ] C.V :=
  (PhiLin C φ g) ∘ₗ (Submodule.subtype (augKer (G := G)))

lemma PhiKer_apply (φ : G → G → C.V) (g : G) (x : ↥(augKer (G := G))) :
    PhiKer C φ g x = PhiLin C φ g x.1 := rfl

lemma PhiKer_one (hφ : ∀ g h k, C.ρ g (φ h k) + φ g (h * k) = φ (g * h) k + φ g h)
    (hφ1 : ∀ g, φ g 1 = 0) : PhiKer C φ 1 = 0 := by
  rw [PhiKer, PhiLin_one C φ (phi_one_left C φ hφ hφ1), LinearMap.zero_comp]

noncomputable def Aact (φ : G → G → C.V) (g : G) :
    (C.V × ↥(augKer (G := G))) →ₗ[ℤ] (C.V × ↥(augKer (G := G))) :=
  LinearMap.prod
    (LinearMap.coprod (C.ρ g) (PhiKer C φ g))
    ((Iρ (G := G) g) ∘ₗ (LinearMap.snd ℤ C.V ↥(augKer (G := G))))

lemma Aact_fst (φ : G → G → C.V) (g : G) (p : C.V × ↥(augKer (G := G))) :
    (Aact C φ g p).1 = C.ρ g p.1 + PhiKer C φ g p.2 := by
  simp [Aact, LinearMap.prod_apply, LinearMap.coprod_apply, LinearMap.comp_apply]

lemma Aact_snd (φ : G → G → C.V) (g : G) (p : C.V × ↥(augKer (G := G))) :
    (Aact C φ g p).2 = Iρ (G := G) g p.2 := by
  simp [Aact, LinearMap.prod_apply, LinearMap.comp_apply]

lemma Aact_mul_apply (φ : G → G → C.V) (g h : G) (p : C.V × ↥(augKer (G := G))) :
    (Aact C φ g) ((Aact C φ h) p) = Aact C φ g (Aact C φ h p) := rfl

noncomputable def Aρ
    (hφ : ∀ g h k, C.ρ g (φ h k) + φ g (h * k) = φ (g * h) k + φ g h)
    (hφ1 : ∀ g, φ g 1 = 0) : Representation ℤ G (C.V × ↥(augKer (G := G))) where
  toFun g := Aact C φ g
  map_one' := by
    apply LinearMap.ext
    intro p
    have h1 : ((Aact C φ 1) p).1 = p.1 := by
      rw [Aact_fst, PhiKer_one C φ hφ hφ1, LinearMap.zero_apply, add_zero,
        map_one, Module.End.one_apply]
    have h2 : ((Aact C φ 1) p).2 = p.2 := by
      rw [Aact_snd, map_one, Module.End.one_apply]
    rw [show (1 : (C.V × ↥(augKer (G := G))) →ₗ[ℤ] (C.V × ↥(augKer (G := G)))) p = p from
      Module.End.one_apply p]
    exact Prod.ext h1 h2
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    have hid : (C.ρ g) (PhiKer C φ h p.2) + PhiKer C φ g (Iρ (G := G) h p.2)
        = PhiKer C φ (g * h) p.2 := by
      rw [PhiKer_apply, PhiKer_apply, PhiKer_apply]
      exact sub_eq_zero.mp
        ((FLin_apply C φ g h p.2.1).symm.trans
          (FLin_eq_zero_of_augLin_eq_zero C φ hφ hφ1 g h p.2.1 p.2.2))
    have hI : Iρ (G := G) (g * h) p.2 = Iρ (G := G) g (Iρ (G := G) h p.2) := by
      rw [show Iρ (G := G) (g * h) = Iρ (G := G) g * Iρ (G := G) h from
        (Iρ (G := G)).map_mul' g h]
      rw [Module.End.mul_apply]
    rw [Module.End.mul_apply]
    apply Prod.ext
    · rw [Aact_fst, Aact_fst, Aact_fst, Aact_snd, map_add, map_mul, Module.End.mul_apply]
      have hassoc : (C.ρ g) ((C.ρ h) p.1) + (C.ρ g) (PhiKer C φ h p.2)
            + PhiKer C φ g (Iρ (G := G) h p.2)
          = (C.ρ g) ((C.ρ h) p.1)
            + ((C.ρ g) (PhiKer C φ h p.2) + PhiKer C φ g (Iρ (G := G) h p.2)) := by
        abel
      rw [hassoc, hid]
    · rw [Aact_snd, Aact_snd, Aact_snd, hI]

end


variable {G : Type} [Group G] [Fintype G]

section
variable (C : Rep ℤ G) (φ : G → G → C.V)
noncomputable local instance instCV5 : Module ℤ C.V := C.hV2
noncomputable local instance instProd5 : Module ℤ (C.V × ↥(augKer (G := G))) := Prod.instModule

noncomputable abbrev ARep (hφ : ∀ g h k, C.ρ g (φ h k) + φ g (h * k) = φ (g * h) k + φ g h)
    (hφ1 : ∀ g, φ g 1 = 0) : Rep ℤ G := Rep.of (Aρ C φ hφ hφ1)

noncomputable abbrev IRep : Rep ℤ G := Rep.of (Iρ (G := G))

noncomputable def Aincl (hφ : ∀ g h k, C.ρ g (φ h k) + φ g (h * k) = φ (g * h) k + φ g h)
    (hφ1 : ∀ g, φ g 1 = 0) : C ⟶ ARep C φ hφ hφ1 :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap C.ρ (Aρ C φ hφ hφ1)
    (LinearMap.inl ℤ C.V ↥(augKer (G := G)))
    (fun g c => by
      have h : (Aρ C φ hφ hφ1) g (LinearMap.inl ℤ C.V ↥(augKer (G := G)) c)
          = LinearMap.inl ℤ C.V ↥(augKer (G := G)) (C.ρ g c) := by
        change Aact C φ g (c, 0) = (C.ρ g c, 0)
        apply Prod.ext
        · rw [Aact_fst]; simp
        · rw [Aact_snd]; simp
      rw [h]))

noncomputable def Aproj (hφ : ∀ g h k, C.ρ g (φ h k) + φ g (h * k) = φ (g * h) k + φ g h)
    (hφ1 : ∀ g, φ g 1 = 0) : ARep C φ hφ hφ1 ⟶ IRep (G := G) :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap (Aρ C φ hφ hφ1) (Iρ (G := G))
    (LinearMap.snd ℤ C.V ↥(augKer (G := G)))
    (fun g p => by
      change (Aact C φ g p).2 = Iρ (G := G) g p.2
      rw [Aact_snd]))

noncomputable def AShort (hφ : ∀ g h k, C.ρ g (φ h k) + φ g (h * k) = φ (g * h) k + φ g h)
    (hφ1 : ∀ g, φ g 1 = 0) : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (Aincl C φ hφ hφ1) (Aproj C φ hφ hφ1) (by
    ext c
    simp [Aincl, Aproj])

end


variable {G : Type} [Group G] [Fintype G]

section
variable (C : Rep ℤ G) (φ : G → G → C.V)
noncomputable local instance instCV6 : Module ℤ C.V := C.hV2
noncomputable local instance instProd6 : Module ℤ (C.V × ↥(augKer (G := G))) := Prod.instModule

lemma Aincl_apply (hφ : ∀ g h k, C.ρ g (φ h k) + φ g (h * k) = φ (g * h) k + φ g h)
    (hφ1 : ∀ g, φ g 1 = 0) (c : C.V) :
    (Aincl C φ hφ hφ1) c = LinearMap.inl ℤ C.V ↥(augKer (G := G)) c := rfl

lemma Aproj_apply (hφ : ∀ g h k, C.ρ g (φ h k) + φ g (h * k) = φ (g * h) k + φ g h)
    (hφ1 : ∀ g, φ g 1 = 0) (a : C.V × ↥(augKer (G := G))) :
    (Aproj C φ hφ hφ1) a = LinearMap.snd ℤ C.V ↥(augKer (G := G)) a := rfl

theorem AShort_shortExact (hφ : ∀ g h k, C.ρ g (φ h k) + φ g (h * k) = φ (g * h) k + φ g h)
    (hφ1 : ∀ g, φ g 1 = 0) : (AShort C φ hφ hφ1).ShortExact := by
  refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise
    (AShort C φ hφ hφ1) ?_ ?_ ?_
  · refine (Rep.mono_iff_injective _).2 (fun x y h => ?_)
    have h1 : (LinearMap.inl ℤ C.V ↥(augKer (G := G)) x).1
        = (LinearMap.inl ℤ C.V ↥(augKer (G := G)) y).1 := congrArg Prod.fst h
    exact h1
  · refine (Rep.epi_iff_surjective _).2 (fun y => ⟨?_, ?_⟩)
    · exact ((0 : C.V), y)
    · change (LinearMap.snd ℤ C.V ↥(augKer (G := G))) (((0 : C.V), y)) = y
      rfl
  · intro a ha
    refine ⟨a.1, ?_⟩
    have h2 : a.2 = 0 := ha
    show (Aincl C φ hφ hφ1) a.1 = a
    rw [Aincl_apply, LinearMap.inl_apply]
    exact Prod.ext rfl h2.symm

end


variable {G : Type} [Group G] [Fintype G]

noncomputable abbrev Iincl : IRep (G := G) ⟶ Rep.leftRegular ℤ G :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap (Iρ (G := G)) (Rep.leftRegular ℤ G).ρ
    (Submodule.subtype (LinearMap.ker (augLin (G := G))))
    (fun g x => rfl))

lemma Iincl_apply (x : ↥(augKer (G := G))) :
    (Iincl (G := G)) x = Submodule.subtype (LinearMap.ker (augLin (G := G))) x := rfl

noncomputable abbrev IShort : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (Iincl (G := G)) (aug (G := G)) (by
    ext x
    show aug (G := G) ((Iincl (G := G)) x) = 0
    rw [Iincl_apply]
    exact x.2)

theorem IShort_shortExact : (IShort (G := G)).ShortExact := by
  refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise
    (IShort (G := G)) ?_ ?_ ?_
  · refine (Rep.mono_iff_injective _).2 (fun x y h => ?_)
    exact Subtype.ext h
  · exact (Rep.epi_iff_surjective _).2 aug_surjective
  · intro x hx
    refine ⟨⟨x, hx⟩, ?_⟩
    rfl


variable {G : Type} [Group G] [Fintype G]

theorem natCard_groupCohomology_res_IRep_one (K : Subgroup G) :
    Nat.card (groupCohomology (Rep.res K.subtype (IRep (G := G))) 1) = Nat.card K := by
  set S : ShortComplex (Rep ℤ K) := (IShort (G := G)).map (Rep.resFunctor K.subtype) with hS
  have hX1 : S.X₁ = Rep.res K.subtype (IRep (G := G)) := rfl
  have hX2 : S.X₂ = Rep.res K.subtype (Rep.leftRegular ℤ G) := rfl
  have hX3 : S.X₃ = Rep.trivial ℤ K ℤ := rfl
  have hse : S.ShortExact := (Rep.shortExact_res K.subtype).mpr (IShort_shortExact (G := G))
  have h0 : Subsingleton (tateCohomology S.X₂ 0) := by
    rw [hX2]; exact subsingleton_tateCohomology_res_leftRegular K 0
  have h1 : Subsingleton (tateCohomology S.X₂ 1) := by
    rw [hX2]; exact subsingleton_tateCohomology_res_leftRegular K 1
  obtain ⟨e⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_iso_of_acyclic_middle_of_subsingleton
    S hse 0 h0 h1
  have h3 : Nat.card (tateCohomology S.X₃ 0) = Nat.card K := by
    rw [hX3]
    exact natCard_tateCohomology_zero_trivial K
  have h1' : Nat.card (tateCohomology S.X₁ 1) = Nat.card K := by
    have h := Nat.card_congr e.symm.toEquiv
    rw [h3] at h
    exact h
  rw [hX1] at h1'
  have key : Nat.card (tateCohomology (Rep.res K.subtype (IRep (G := G))) 1) =
      Nat.card (groupCohomology (Rep.res K.subtype (IRep (G := G))) 1) :=
    Nat.card_congr (((TateCohomology.isoGroupCohomology (R := ℤ) (G := K) 1).app
      (Rep.res K.subtype (IRep (G := G)))).toLinearEquiv.toEquiv)
  rw [← key]
  exact h1'

set_option maxHeartbeats 800000
attribute [local instance 100] AddCommGroup.toIntModule

-- ===== from p90 =====
variable {G : Type} [Group G] (C : Rep.{0,0,0} ℤ G)

open groupCohomology in
/-- The `d₁₂`-differential evaluated at `(g,h)`. -/
lemma d12_apply (s : G → C.V) (g h : G) :
    (groupCohomology.d₁₂ C) s (g, h) = C.ρ g (s h) - s (g * h) + s g := rfl

open groupCohomology in
/-- For a 2-cocycle `z`, the function `z (g*h, 1)` is `ρ g (z (h,1))`. -/
lemma cocycle_fst_one_mul (z : groupCohomology.cocycles₂ C) (g h : G) :
    z (g * h, 1) = C.ρ g (z (h, 1)) := by
  have hh := (groupCohomology.mem_cocycles₂_iff (⇑z)).1 z.2 g h 1
  simp only [mul_one] at hh
  exact add_right_cancel hh

open groupCohomology in
/-- Normalisation of a 2-cocycle: `φ (g,h) = z (g,h) - z (g,1)`.  It is again a 2-cocycle and
`φ (g,1) = 0`. -/
noncomputable def normCocycle (z : groupCohomology.cocycles₂ C) : groupCohomology.cocycles₂ C :=
  ⟨fun p : G × G => z p - z (p.1, 1), by
    rw [groupCohomology.mem_cocycles₂_iff]
    intro g h j
    have hz := (groupCohomology.mem_cocycles₂_iff (⇑z)).1 z.2 g h j
    have h1 := cocycle_fst_one_mul C z g h
    simp only [Pi.sub_apply, map_sub]
    have hL : z (g * h, j) - z (g * h, 1) + (z (g, h) - z (g, 1))
        = (z (g * h, j) + z (g, h)) - (z (g * h, 1) + z (g, 1)) := by abel
    have hR : (C.ρ g) (z (h, j)) - (C.ρ g) (z (h, 1)) + (z (g, h * j) - z (g, 1))
        = ((C.ρ g) (z (h, j)) + z (g, h * j)) - ((C.ρ g) (z (h, 1)) + z (g, 1)) := by abel
    rw [hL, hR, ← hz, ← h1]⟩

open groupCohomology in
lemma coe_normCocycle (z : groupCohomology.cocycles₂ C) :
    ⇑(normCocycle C z) = fun p : G × G => z p - z (p.1, 1) := rfl

open groupCohomology in
lemma normCocycle_fst_one (z : groupCohomology.cocycles₂ C) (g : G) :
    (normCocycle C z) (g, 1) = 0 := by
  rw [coe_normCocycle]
  simp

open groupCohomology in
lemma d12_aux_eq (z : groupCohomology.cocycles₂ C) :
    (groupCohomology.d₁₂ C) (fun h => z (h, 1)) = fun p : G × G => z (p.1, 1) := by
  funext p
  obtain ⟨g, h⟩ := p
  rw [d12_apply]
  have h1 := cocycle_fst_one_mul C z g h
  rw [h1, sub_self, zero_add]

open groupCohomology in
lemma normCocycle_H2π (z : groupCohomology.cocycles₂ C) :
    groupCohomology.H2π C (normCocycle C z) = groupCohomology.H2π C z := by
  rw [groupCohomology.H2π_eq_iff]
  rw [show (⇑(normCocycle C z) - ⇑z : G × G → C.V) = -(fun p : G × G => z (p.1, 1)) from by
    funext p
    rw [Pi.sub_apply, coe_normCocycle]
    simp]
  exact Submodule.neg_mem _ ⟨_, d12_aux_eq C z⟩


variable {G : Type} [Group G] (C : Rep.{0,0,0} ℤ G)

open groupCohomology in
/-- **Normalised representative.**  Every class `α ∈ H²(G,C)` is represented by a normalised
2-cocycle, i.e. a 2-cocycle `z` with `z (g,1) = 0` for all `g`. -/
theorem exists_normalized_cocycle (α : groupCohomology C 2) :
    ∃ z : groupCohomology.cocycles₂ C,
      groupCohomology.H2π C z = α ∧ (∀ g : G, z (g, 1) = 0) := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π C)).1 inferInstance α
  exact ⟨normCocycle C z, by rw [normCocycle_H2π, hz], normCocycle_fst_one C z⟩

open groupCohomology in
/-- The cocycle condition, in the "curried" form used by the splitting-module construction. -/
lemma cocycle_condition (z : groupCohomology.cocycles₂ C) :
    ∀ g h k : G, C.ρ g (z (h, k)) + z (g, h * k) = z (g * h, k) + z (g, h) := by
  intro g h k
  exact ((groupCohomology.mem_cocycles₂_iff (⇑z)).1 z.2 g h k).symm


-- ===== from p91 =====
variable {G : Type} [Group G] [Fintype G] (C : Rep.{0,0,0} ℤ G)

section
variable (z : groupCohomology.cocycles₂ C)
noncomputable local instance instCV7 : Module ℤ C.V := C.hV2
noncomputable local instance instProd7 : Module ℤ (C.V × ↥(augKer (G := G))) := Prod.instModule

/-- The curried cocycle attached to a `2`-cocycle `z`. -/
noncomputable abbrev phiZ : G → G → C.V := fun g h => ⇑z (g, h)

omit [Fintype G] in
lemma phiZ_apply (g h : G) : phiZ C z g h = z (g, h) := rfl

lemma phiZ_cocycle :
    ∀ g h k : G, C.ρ g (phiZ C z h k) + phiZ C z g (h * k) = phiZ C z (g * h) k + phiZ C z g h := by
  intro g h k
  exact cocycle_condition C z g h k

omit [Fintype G] in
lemma phiZ_one (hz : ∀ g : G, z (g, 1) = 0) : ∀ g : G, phiZ C z g 1 = 0 := hz

/-- The element `g - 1` of the augmentation ideal. -/
noncomputable def genI (g : G) : ↥(augKer (G := G)) :=
  ⟨MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1, by
    rw [LinearMap.mem_ker, map_sub, augLin_single, augLin_single]
    simp⟩

lemma genI_coe (g : G) :
    ((genI (G := G) g : ↥(augKer (G := G))) : MonoidAlgebra ℤ G)
      = MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1 := rfl

/-- The section `s (g) = (0, g - 1)` of `A = C ⊕ I_G`. -/
noncomputable def secA (K : Subgroup G) (g : ↥K) : C.V × ↥(augKer (G := G)) :=
  (0, genI (G := G) g.1)

lemma Iρ_genI (g h : G) :
    ((Iρ (G := G) g (genI (G := G) h) : ↥(augKer (G := G))) : MonoidAlgebra ℤ G)
      = MonoidAlgebra.single (g * h) 1 - MonoidAlgebra.single g 1 := by
  rw [show ((Iρ (G := G) g (genI (G := G) h) : ↥(augKer (G := G))) : MonoidAlgebra ℤ G)
      = ((Representation.ofMulAction ℤ G G) g) (((genI (G := G) h : ↥(augKer (G := G))) : MonoidAlgebra ℤ G))
      from rfl]
  rw [genI_coe, map_sub, Representation.ofMulAction_single, Representation.ofMulAction_single]
  simp

lemma secA_d12 (z : groupCohomology.cocycles₂ C) (hz : ∀ g : G, z (g, 1) = 0)
    (K : Subgroup G) (g h : ↥K) :
    Aact C (phiZ C z) g.1 (secA C K h) - secA C K (g * h) + secA C K g
      = (Aincl C (phiZ C z) (phiZ_cocycle C z) (phiZ_one C z hz)) (z (g.1, h.1)) := by
  have hPhi : PhiKer C (phiZ C z) g.1 (genI (G := G) h.1) = z (g.1, h.1) := by
    rw [PhiKer_apply]
    show PhiLin C (phiZ C z) g.1
      (MonoidAlgebra.single h.1 1 - MonoidAlgebra.single 1 1) = z (g.1, h.1)
    rw [map_sub, PhiLin_single, PhiLin_single]
    show (1 : ℤ) • phiZ C z g.1 h.1 - (1 : ℤ) • phiZ C z g.1 1 = z (g.1, h.1)
    rw [phiZ_one C z hz g.1, one_smul, one_smul, sub_zero, phiZ_apply]
  have hI := Iρ_genI (G := G) g.1 h.1
  apply Prod.ext
  · rw [Prod.fst_add, Prod.fst_sub, Aact_fst]
    rw [show (secA C K h).2 = genI (G := G) h.1 from rfl]
    rw [hPhi, show (secA C K h).1 = (0 : C.V) from rfl,
        show (secA C K (g * h)).1 = (0 : C.V) from rfl,
        show (secA C K g).1 = (0 : C.V) from rfl,
        Aincl_apply, LinearMap.inl_apply]
    simp
  · rw [Prod.snd_add, Prod.snd_sub, Aact_snd]
    rw [show (secA C K h).2 = genI (G := G) h.1 from rfl,
        show (secA C K (g * h)).2 = genI (G := G) (g * h).1 from rfl,
        show (secA C K g).2 = genI (G := G) g.1 from rfl,
        Aincl_apply, LinearMap.inl_apply]
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_sub, hI, genI_coe, genI_coe, Submodule.coe_zero,
      Subgroup.coe_mul]
    abel

end

-- ===== from p92 =====

theorem closure_singleton_eq_top_of_addOrderOf_eq_natCard {A : Type} [AddCommGroup A] [Finite A]
    (x : A) (h : addOrderOf x = Nat.card A) : AddSubgroup.closure ({x} : Set A) = ⊤ := by
  rw [← AddSubgroup.zmultiples_eq_closure]
  apply AddSubgroup.eq_top_of_card_eq
  rw [Nat.card_zmultiples, h]

theorem subsingleton_monoidHom_to_multiplicative_int {G : Type} [Group G] [Fintype G] :
    Subsingleton (G →* Multiplicative ℤ) := by
  have hroot : ∀ (f : G →* Multiplicative ℤ) (x : G), f x = 1 := by
    intro f x
    have h : f x ^ Fintype.card G = 1 := by rw [← map_pow, pow_card_eq_one, map_one]
    rcases (pow_eq_one_iff (M := Multiplicative ℤ) (a := f x) (n := Fintype.card G)).1 h with
      h' | h'
    · exact h'
    · exact absurd h' Fintype.card_ne_zero
  exact ⟨fun f g => MonoidHom.ext fun x => by rw [hroot f x, hroot g x]⟩

theorem subsingleton_groupCohomology_trivial_int_one {G : Type} [Group G] [Fintype G] :
    Subsingleton (groupCohomology (Rep.trivial ℤ G ℤ) 1) := by
  have htriv : ∀ (g : G) (x : (Rep.trivial ℤ G ℤ).V), (Rep.trivial ℤ G ℤ).ρ g x = x :=
    fun g x => rfl
  have hmul : ∀ (z : groupCohomology.cocycles₁ (Rep.trivial ℤ G ℤ)) (g h : G),
      z (g * h) = z g + z h := by
    intro z g h
    have hc := (groupCohomology.mem_cocycles₁_def (⇑z)).1 z.2 g h
    rw [htriv] at hc
    have h2 : z h + z g = z (g * h) := by
      have h3 := hc
      rw [show z h - z (g*h) + z g = z h + z g - z (g*h) from by abel] at h3
      exact sub_eq_zero.mp h3
    exact h2.symm.trans (add_comm _ _)
  have hzero : ∀ z : groupCohomology.cocycles₁ (Rep.trivial ℤ G ℤ), ⇑z = 0 := by
    intro z
    have h1 : z 1 = 0 := by
      have h := hmul z 1 1
      simp only [one_mul] at h
      exact (add_left_cancel (show z 1 + 0 = z 1 + z 1 from by rw [add_zero]; exact h)).symm
    let F : G →* Multiplicative ℤ :=
      { toFun := fun g => Multiplicative.ofAdd (z g)
        map_one' := by
          show Multiplicative.ofAdd (z 1) = 1
          rw [h1]
          rfl
        map_mul' := fun g h => by
          show Multiplicative.ofAdd (z (g * h)) =
            Multiplicative.ofAdd (z g) * Multiplicative.ofAdd (z h)
          rw [hmul z g h]
          rfl }
    funext g
    have hroot : F g = 1 := by
      have h : F g ^ Fintype.card G = 1 := by rw [← map_pow, pow_card_eq_one, map_one]
      rcases (pow_eq_one_iff (M := Multiplicative ℤ) (a := F g) (n := Fintype.card G)).1 h with
        h' | h'
      · exact h'
      · exact absurd h' Fintype.card_ne_zero
    have h2 := congrArg Multiplicative.toAdd hroot
    simpa [F] using h2
  have key : ∀ z : groupCohomology.cocycles₁ (Rep.trivial ℤ G ℤ),
      groupCohomology.H1π (Rep.trivial ℤ G ℤ) z = 0 := by
    intro z
    rw [groupCohomology.H1π_eq_zero_iff, hzero z]
    exact Submodule.zero_mem _
  refine ⟨fun x y => ?_⟩
  revert y
  refine groupCohomology.H1_induction_on x ?_
  intro z y
  refine groupCohomology.H1_induction_on y ?_
  intro w
  rw [key z, key w]


-- ===== from p93 =====

theorem Subsingleton.of_equiv {α β : Sort*} (e : α ≃ β) (h : Subsingleton β) : Subsingleton α :=
  ⟨fun x y => e.injective (h.elim (e x) (e y))⟩

variable {G : Type} [Group G] [Fintype G]

theorem subsingleton_tateCohomology_trivial_int_one (K : Subgroup G) :
    Subsingleton (tateCohomology (Rep.trivial ℤ K ℤ) 1) :=
  Subsingleton.of_equiv
    (((TateCohomology.isoGroupCohomology (R := ℤ) (G := K) 1).app
      (Rep.trivial ℤ K ℤ)).toLinearEquiv.toEquiv)
    (subsingleton_groupCohomology_trivial_int_one (G := K))

theorem subsingleton_groupCohomology_res_IRep_two (K : Subgroup G) :
    Subsingleton (groupCohomology (Rep.res K.subtype (IRep (G := G))) 2) := by
  set S : ShortComplex (Rep ℤ K) := (IShort (G := G)).map (Rep.resFunctor K.subtype) with hS
  have hX1 : S.X₁ = Rep.res K.subtype (IRep (G := G)) := rfl
  have hX2 : S.X₂ = Rep.res K.subtype (Rep.leftRegular ℤ G) := rfl
  have hX3 : S.X₃ = Rep.trivial ℤ K ℤ := rfl
  have hse : S.ShortExact := (Rep.shortExact_res K.subtype).mpr (IShort_shortExact (G := G))
  have h1 : Subsingleton (tateCohomology S.X₂ 1) := by
    rw [hX2]; exact subsingleton_tateCohomology_res_leftRegular K 1
  have h2 : Subsingleton (tateCohomology S.X₂ 2) := by
    rw [hX2]; exact subsingleton_tateCohomology_res_leftRegular K 2
  obtain ⟨e⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_iso_of_acyclic_middle_of_subsingleton
      S hse 1 h1 h2
  rw [hX3] at e
  rw [hX1] at e
  have hT : Subsingleton (tateCohomology (Rep.res K.subtype (IRep (G := G))) 2) :=
    Subsingleton.of_equiv e.symm.toEquiv (subsingleton_tateCohomology_trivial_int_one K)
  exact Subsingleton.of_equiv
    (((TateCohomology.isoGroupCohomology (R := ℤ) (G := K) 2).app
      (Rep.res K.subtype (IRep (G := G)))).toLinearEquiv.toEquiv.symm) hT


-- ===== from p94 =====
variable {G : Type} [Group G] {H : Type} [Group H]
variable {C : Rep.{0,0,0} ℤ H} {D : Rep.{0,0,0} ℤ G} (f : G →* H)

/-- Pointwise description of `cochainsMap₂`. -/
lemma cochainsMap₂_apply (φ : Rep.res f C ⟶ D) (x : H × H → C.V) (g h : G) :
    (groupCohomology.cochainsMap₂ f φ x) (g, h) = φ.hom (x (f g, f h)) := by
  simp only [groupCohomology.cochainsMap₂, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearMap.compLeft_apply, LinearMap.funLeft_apply, Function.comp_apply, Prod.map_apply,
    Representation.IntertwiningMap.toLinearMap_apply]

/-- Pointwise description of `mapCocycles₂`. -/
lemma mapCocycles₂_apply (φ : Rep.res f C ⟶ D) (x : groupCohomology.cocycles₂ C) (g h : G) :
    (groupCohomology.mapCocycles₂ f φ x) (g, h) = φ.hom (x (f g, f h)) := by
  rw [groupCohomology.coe_mapCocycles₂, cochainsMap₂_apply]


-- ===== from p95 =====
variable {G : Type} [Group G] [Fintype G] (C : Rep.{0,0,0} ℤ G)
noncomputable local instance instCV95 : Module ℤ C.V := C.hV2
noncomputable local instance instProd95 : Module ℤ (C.V × ↥(augKer (G := G))) := Prod.instModule

/-- Restriction to a subgroup computed on a cocycle: `Res_K (H2π z) = H2π (z|_K)`. -/
lemma resNatTrans_H2π_apply (z : groupCohomology.cocycles₂ C) (K : Subgroup G) :
    (groupCohomology.resNatTrans ℤ (G := K) (H := G) K.subtype 2).app C
        (groupCohomology.H2π C z) =
      groupCohomology.H2π (Rep.res K.subtype C)
        (groupCohomology.mapCocycles₂ K.subtype (𝟙 (Rep.res K.subtype C)) z) := by
  rw [groupCohomology.resNatTrans_app]
  exact groupCohomology.H2π_comp_map_apply K.subtype (𝟙 (Rep.res K.subtype C)) z

/-- The restriction of a cocycle to a subgroup, evaluated. -/
lemma mapCocycles₂_subtype_apply (z : groupCohomology.cocycles₂ C) (K : Subgroup G) (g h : ↥K) :
    (groupCohomology.mapCocycles₂ K.subtype (𝟙 (Rep.res K.subtype C)) z) (g, h)
      = z (g.1, h.1) := by
  rw [mapCocycles₂_apply]
  rfl


-- ===== from p96 =====
variable {K : Type} [Group K]

/-- If a 2-cocycle is the coboundary of a function, then its class vanishes. -/
lemma H2π_eq_zero_of_d12_eq (B : Rep.{0,0,0} ℤ K) (z : groupCohomology.cocycles₂ B)
    (s : K → B.V) (h : (groupCohomology.d₁₂ B).hom s = ⇑z) :
    groupCohomology.H2π B z = 0 := by
  rw [groupCohomology.H2π_eq_zero_iff]
  exact LinearMap.mem_range.mpr ⟨s, h⟩


variable {G : Type} [Group G] [Fintype G] (C : Rep.{0,0,0} ℤ G)
noncomputable local instance instCV96 : Module ℤ C.V := C.hV2
noncomputable local instance instProd96 : Module ℤ (C.V × ↥(augKer (G := G))) := Prod.instModule

section
variable (z : groupCohomology.cocycles₂ C) (hz : ∀ g : G, z (g, 1) = 0) (K : Subgroup G)

theorem map_Aincl_resNatTrans_H2π_eq_zero :
    (groupCohomology.map (MonoidHom.id K)
        (Rep.resMap K.subtype
          (Aincl C (phiZ C z) (phiZ_cocycle C z) (phiZ_one C z hz))) 2)
      ((groupCohomology.resNatTrans ℤ (G := K) (H := G) K.subtype 2).app C
        (groupCohomology.H2π C z)) = 0 := by
  set zK := groupCohomology.mapCocycles₂ K.subtype (𝟙 (Rep.res K.subtype C)) z with hzK
  have hMap := groupCohomology.H2π_comp_map_apply (MonoidHom.id K)
    (Rep.resMap K.subtype (Aincl C (phiZ C z) (phiZ_cocycle C z) (phiZ_one C z hz))) zK
  have hw : groupCohomology.H2π (Rep.res K.subtype
      (ARep C (phiZ C z) (phiZ_cocycle C z) (phiZ_one C z hz)))
      (groupCohomology.mapCocycles₂ (MonoidHom.id K)
        (Rep.resMap K.subtype (Aincl C (phiZ C z) (phiZ_cocycle C z) (phiZ_one C z hz))) zK) = 0 := by
    refine H2π_eq_zero_of_d12_eq _ _ (secA C K) ?_
    rw [hzK]
    funext p
    obtain ⟨g, h⟩ := p
    rw [mapCocycles₂_apply]
    simp only [MonoidHom.id_apply]
    rw [mapCocycles₂_apply, Rep.hom_id, Representation.IntertwiningMap.id_apply]
    rw [Rep.resMap_hom_apply, d12_apply]
    exact secA_d12 C z hz K g h
  rw [resNatTrans_H2π_apply C z K, ← hzK]
  rw [hMap]
  exact hw

end

-- ===== from p97 =====

/-- A morphism into a subsingleton module is zero. -/
lemma hom_eq_zero_of_subsingleton {M N : ModuleCat ℤ} (f : M ⟶ N) [Subsingleton ↥N] : f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

/-- A `ℤ`-linear map vanishing on a generating element is zero. -/
lemma hom_eq_zero_of_closure_eq_top {M N : ModuleCat ℤ} (f : M ⟶ N) (x : M)
    (hx : AddSubgroup.closure ({x} : Set M) = ⊤) (hfx : f.hom x = 0) : f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  have hy : y ∈ AddSubgroup.closure ({x} : Set M) := by rw [hx]; trivial
  rw [AddSubgroup.mem_closure_singleton] at hy
  obtain ⟨n, hn⟩ := hy
  show f.hom y = 0
  rw [← hn, map_zsmul, hfx, zsmul_zero]

/-- A surjective `ℤ`-linear map between finite modules of equal cardinality is injective. -/
lemma ker_eq_bot_of_surjective_of_natCard_eq {M N : ModuleCat ℤ} [Finite ↥M] [Finite ↥N]
    (f : M ⟶ N) (hsurj : Function.Surjective f.hom) (hcard : Nat.card ↥M = Nat.card ↥N) :
    f.hom.ker = ⊥ := by
  have hrange : f.hom.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have h1 : Nat.card ↥M = Nat.card ↥(f.hom.ker) * Nat.card ↥(f.hom.range) := by
    rw [Submodule.card_eq_card_quotient_mul_card f.hom.ker]
    congr 1
    exact Nat.card_congr (LinearMap.quotKerEquivRange f.hom).toEquiv
  rw [hrange, Nat.card_congr (Submodule.topEquiv (R := ℤ) (M := ↥N)).toEquiv,
    hcard] at h1
  have hN : 0 < Nat.card ↥N := Nat.pos_of_ne_zero (Nat.card_ne_zero.mpr ⟨⟨0⟩, ‹Finite ↥N›⟩)
  have h2 : Nat.card ↥(f.hom.ker) = 1 :=
    Nat.eq_of_mul_eq_mul_right hN (by rw [one_mul]; exact h1.symm)
  haveI : Subsingleton ↥(f.hom.ker) := (Nat.card_eq_one_iff_unique.mp h2).1
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥(f.hom.ker)) = 0 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val hx'


variable {G : Type} [Group G] [Fintype G] (C : Rep.{0,0,0} ℤ G)
noncomputable local instance instCV97 : Module ℤ C.V := C.hV2
noncomputable local instance instProd97 : Module ℤ (C.V × ↥(augKer (G := G))) := Prod.instModule

section
variable (z : groupCohomology.cocycles₂ C) (hz : ∀ g : G, z (g, 1) = 0)

/-- The splitting module attached to a normalised cocycle. -/
noncomputable abbrev Sprint : Rep ℤ G := ARep C (phiZ C z) (phiZ_cocycle C z) (phiZ_one C z hz)

noncomputable abbrev AinclZ : C ⟶ Sprint C z hz :=
  Aincl C (phiZ C z) (phiZ_cocycle C z) (phiZ_one C z hz)

noncomputable abbrev AprojZ : Sprint C z hz ⟶ IRep (G := G) :=
  Aproj C (phiZ C z) (phiZ_cocycle C z) (phiZ_one C z hz)

noncomputable abbrev AShortZ : ShortComplex (Rep ℤ G) :=
  AShort C (phiZ C z) (phiZ_cocycle C z) (phiZ_one C z hz)

theorem AShortZ_shortExact : (AShortZ C z hz).ShortExact :=
  AShort_shortExact C (phiZ C z) (phiZ_cocycle C z) (phiZ_one C z hz)

theorem map_AinclZ_resNatTrans_H2π_eq_zero (K : Subgroup G) :
    (groupCohomology.map (MonoidHom.id K) (Rep.resMap K.subtype (AinclZ C z hz)) 2)
      ((groupCohomology.resNatTrans ℤ (G := K) (H := G) K.subtype 2).app C
        (groupCohomology.H2π C z)) = 0 :=
  map_Aincl_resNatTrans_H2π_eq_zero C z hz K

end

-- ===== from p99 =====
variable {G : Type} [Group G] [Fintype G] (C : Rep.{0,0,0} ℤ G)
noncomputable local instance instCV99 : Module ℤ C.V := C.hV2
noncomputable local instance instProd99 : Module ℤ (C.V × ↥(augKer (G := G))) := Prod.instModule

section
variable (z : groupCohomology.cocycles₂ C) (hz : ∀ g : G, z (g, 1) = 0)

/-- The restriction to `K` of the short exact sequence `0 → C → A → I → 0`. -/
noncomputable abbrev SZ (K : Subgroup G) : ShortComplex (Rep ℤ K) :=
  ShortComplex.mk (Rep.resMap K.subtype (AinclZ C z hz))
    (Rep.resMap K.subtype (AprojZ C z hz)) (by
      have h : (AinclZ C z hz) ≫ (AprojZ C z hz) = 0 := (AShortZ C z hz).zero
      have h2 : (Rep.resFunctor K.subtype).map ((AinclZ C z hz) ≫ (AprojZ C z hz)) = 0 := by
        rw [h, Functor.map_zero]
      rw [← (Rep.resFunctor K.subtype).map_comp (AinclZ C z hz) (AprojZ C z hz)]
      exact h2)

theorem SZ_shortExact (K : Subgroup G) : (SZ C z hz K).ShortExact := by
  refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise
    (SZ C z hz K) ?_ ?_ ?_
  · refine (Rep.mono_iff_injective _).2 (fun x y h => ?_)
    have h1 : (Aincl C (phiZ C z) (phiZ_cocycle C z) (phiZ_one C z hz)) x
        = (Aincl C (phiZ C z) (phiZ_cocycle C z) (phiZ_one C z hz)) y := h
    have h2 : (LinearMap.inl ℤ C.V ↥(augKer (G := G))) x
        = (LinearMap.inl ℤ C.V ↥(augKer (G := G))) y := h1
    rw [LinearMap.inl_apply, LinearMap.inl_apply] at h2
    exact (Prod.ext_iff.mp h2).1
  · refine (Rep.epi_iff_surjective _).2 (fun y => ⟨((0 : C.V), y), ?_⟩)
    show (Aproj C (phiZ C z) (phiZ_cocycle C z) (phiZ_one C z hz)) ((0 : C.V), y) = y
    rw [Aproj_apply, LinearMap.snd_apply]
  · intro a ha
    refine ⟨a.1, ?_⟩
    have h2 : a.2 = 0 := ha
    show (Aincl C (phiZ C z) (phiZ_cocycle C z) (phiZ_one C z hz)) a.1 = a
    rw [Aincl_apply, LinearMap.inl_apply]
    exact Prod.ext rfl h2.symm

end

-- ===== from p98t =====
variable {G : Type} [Group G] [Fintype G] (C : Rep.{0,0,0} ℤ G)
noncomputable local instance instCV98 : Module ℤ C.V := C.hV2
noncomputable local instance instProd98 : Module ℤ (C.V × ↥(augKer (G := G))) := Prod.instModule

section
variable (z : groupCohomology.cocycles₂ C) (hz : ∀ g : G, z (g, 1) = 0)

theorem subsingleton_H1_H2_res_ARep
    (α : groupCohomology C 2) (hzα : groupCohomology.H2π C z = α)
    (hα : addOrderOf α = Nat.card G)
    (h1 : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype C) 1))
    (h2 : ∀ H : Subgroup G, Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H)
    (K : Subgroup G) :
    Subsingleton (groupCohomology (Rep.res K.subtype (Sprint C z hz)) 1) ∧
    Subsingleton (groupCohomology (Rep.res K.subtype (Sprint C z hz)) 2) := by
  haveI h1K : Subsingleton ↥(groupCohomology (Rep.res K.subtype C) 1) := h1 K
  haveI hI2 : Subsingleton ↥(groupCohomology (Rep.res K.subtype (IRep (G := G))) 2) :=
    subsingleton_groupCohomology_res_IRep_two K
  haveI hfinC : Finite ↥(groupCohomology (Rep.res K.subtype C) 2) :=
    (Nat.card_ne_zero.mp (by rw [h2 K]; exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)).2
  haveI hfinI : Finite ↥(groupCohomology (Rep.res K.subtype (IRep (G := G))) 1) :=
    (Nat.card_ne_zero.mp (by
      rw [natCard_groupCohomology_res_IRep_one K]
      exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)).2
  have hord : addOrderOf ((groupCohomology.resNatTrans ℤ (G := K) (H := G) K.subtype 2).app C α)
      = Nat.card ↥(groupCohomology (Rep.res K.subtype C) 2) := by
    rw [h2 K]
    exact addOrderOf_resNatTrans_two (S := K) (M := C) α hα (h2 K)
  have hgen : AddSubgroup.closure
      ({((groupCohomology.resNatTrans ℤ (G := K) (H := G) K.subtype 2).app C α)} :
        Set ↥(groupCohomology (Rep.res K.subtype C) 2)) = ⊤ :=
    closure_singleton_eq_top_of_addOrderOf_eq_natCard _ hord
  have hSse : (SZ C z hz K).ShortExact := SZ_shortExact C z hz K
  have hconvf : (groupCohomology.mapShortComplex₂ (SZ C z hz K) 2).f
      = groupCohomology.map (MonoidHom.id K) (Rep.resMap K.subtype (AinclZ C z hz)) 2 := rfl
  have hconvg : (groupCohomology.mapShortComplex₂ (SZ C z hz K) 2).g
      = groupCohomology.map (MonoidHom.id K) (Rep.resMap K.subtype (AprojZ C z hz)) 2 := rfl
  have hf2 : (groupCohomology.mapShortComplex₂ (SZ C z hz K) 2).f = 0 := by
    rw [hconvf]
    apply hom_eq_zero_of_closure_eq_top _ _ hgen
    rw [← hzα]
    exact map_AinclZ_resNatTrans_H2π_eq_zero C z hz K
  have hg2 : (groupCohomology.mapShortComplex₂ (SZ C z hz K) 2).g = 0 := by
    rw [hconvg]
    apply hom_eq_zero_of_subsingleton
  have hE4 : ((groupCohomology.mapShortComplex₂ (SZ C z hz K) 2).f).hom.range
      = ((groupCohomology.mapShortComplex₂ (SZ C z hz K) 2).g).hom.ker :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
      (groupCohomology.mapShortComplex₂_exact hSse 2)
  have hSub2' : Subsingleton ↥(groupCohomology (SZ C z hz K).X₂ 2) := by
    have htopbot : (⊤ : Submodule ℤ ↥(groupCohomology (SZ C z hz K).X₂ 2)) = ⊥ := by
      have h2' : ((groupCohomology.mapShortComplex₂ (SZ C z hz K) 2).g).hom.ker = ⊤ := by
        rw [hg2]; exact LinearMap.ker_zero
      have h1' : ((groupCohomology.mapShortComplex₂ (SZ C z hz K) 2).f).hom.range = ⊥ := by
        rw [hf2]; exact LinearMap.range_zero
      exact h2'.symm.trans (hE4.symm.trans h1')
    have hx0 : ∀ x : ↥(groupCohomology (SZ C z hz K).X₂ 2), x = 0 := by
      intro x
      have hx1 : x ∈ (⊤ : Submodule ℤ ↥(groupCohomology (SZ C z hz K).X₂ 2)) := trivial
      rw [htopbot, Submodule.mem_bot] at hx1
      exact hx1
    exact ⟨fun x y => by rw [hx0 x, hx0 y]⟩
  have hE3 : (groupCohomology.δ hSse 1 2 rfl).hom.range
      = ((groupCohomology.mapShortComplex₂ (SZ C z hz K) 2).f).hom.ker :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
      (groupCohomology.mapShortComplex₁_exact hSse rfl)
  have hδsurj : Function.Surjective (groupCohomology.δ hSse 1 2 rfl).hom := by
    rw [← LinearMap.range_eq_top, hE3, hf2]
    exact LinearMap.ker_zero
  have hδker : (groupCohomology.δ hSse 1 2 rfl).hom.ker = ⊥ :=
    ker_eq_bot_of_surjective_of_natCard_eq _
      hδsurj (by rw [natCard_groupCohomology_res_IRep_one K, h2 K])
  have hδinj : Function.Injective (groupCohomology.δ hSse 1 2 rfl).hom :=
    LinearMap.ker_eq_bot.mp hδker
  have hE2 : ((groupCohomology.mapShortComplex₂ (SZ C z hz K) 1).g).hom.range
      = (groupCohomology.δ hSse 1 2 rfl).hom.ker :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
      (groupCohomology.mapShortComplex₃_exact hSse (show 1 + 1 = 2 from rfl))
  have hg1range : ((groupCohomology.mapShortComplex₂ (SZ C z hz K) 1).g).hom.range = ⊥ :=
    hE2.trans (LinearMap.ker_eq_bot.mpr hδinj)
  have hg1 : (groupCohomology.mapShortComplex₂ (SZ C z hz K) 1).g = 0 := by
    apply ModuleCat.hom_ext
    exact LinearMap.range_eq_bot.mp hg1range
  have hE1 : ((groupCohomology.mapShortComplex₂ (SZ C z hz K) 1).f).hom.range
      = ((groupCohomology.mapShortComplex₂ (SZ C z hz K) 1).g).hom.ker :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
      (groupCohomology.mapShortComplex₂_exact hSse 1)
  have hSub1' : Subsingleton ↥(groupCohomology (SZ C z hz K).X₂ 1) := by
    have hsurj : Function.Surjective ((groupCohomology.mapShortComplex₂ (SZ C z hz K) 1).f).hom := by
      rw [← LinearMap.range_eq_top, hE1, hg1]
      exact LinearMap.ker_zero
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, ha⟩ := hsurj x
    obtain ⟨b, hb⟩ := hsurj y
    rw [← ha, ← hb]
    exact congrArg (fun t => ((groupCohomology.mapShortComplex₂ (SZ C z hz K) 1).f) t) (h1K.elim a b)
  have hSub1 : Subsingleton ↥(groupCohomology (Rep.res K.subtype (Sprint C z hz)) 1) := hSub1'
  have hSub2 : Subsingleton ↥(groupCohomology (Rep.res K.subtype (Sprint C z hz)) 2) := hSub2'
  exact ⟨hSub1, hSub2⟩

end

-- ===== from p100 =====
variable {G : Type} [Group G] [Fintype G] (C : Rep.{0,0,0} ℤ G)
noncomputable local instance instCV100 : Module ℤ C.V := C.hV2
noncomputable local instance instProd100 : Module ℤ (C.V × ↥(augKer (G := G))) := Prod.instModule

section
variable (z : groupCohomology.cocycles₂ C) (hz : ∀ g : G, z (g, 1) = 0)

/-- **Acyclicity of the splitting module.** -/
theorem subsingleton_tateCohomology_Sprint [Group.IsSolvable G]
    (α : groupCohomology C 2) (hzα : groupCohomology.H2π C z = α)
    (hα : addOrderOf α = Nat.card G)
    (h1 : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype C) 1))
    (h2 : ∀ H : Subgroup G, Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H) :
    ∀ r : ℤ, Subsingleton (tateCohomology (Sprint C z hz) r) :=
  Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_of_subsingleton_H1_H2_of_solvable
    (Sprint C z hz) (fun H => subsingleton_H1_H2_res_ARep C z hz α hzα hα h1 h2 H)

end
end NU

namespace Commons.RepresentationTheory.TateCohomology

theorem natCard_tateCohomology_eq_of_fundamental_class {G : Type} [Group G] [Fintype G]
    [Group.IsSolvable G] (C : Rep.{0,0,0} ℤ G)
    (h1 : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype C) 1))
    (h2 : ∀ H : Subgroup G, Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H)
    (α : groupCohomology C 2) (hα : addOrderOf α = Nat.card G) :
    Nat.card (tateCohomology (Rep.trivial ℤ G ℤ) (-2)) =
      Nat.card (tateCohomology C 0) := by
  obtain ⟨z, hzα, hz⟩ := NU.exists_normalized_cocycle C α
  have hacyc := NU.subsingleton_tateCohomology_Sprint C z hz α hzα hα h1 h2
  have hA1 : Subsingleton ↥(tateCohomology (NU.AShortZ C z hz).X₂ (-1)) := hacyc (-1)
  have hA2 : Subsingleton ↥(tateCohomology (NU.AShortZ C z hz).X₂ ((-1 : ℤ) + 1)) :=
    hacyc ((-1 : ℤ) + 1)
  obtain ⟨e2⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_iso_of_acyclic_middle_of_subsingleton
      (NU.AShortZ C z hz) (NU.AShortZ_shortExact C z hz) (-1) hA1 hA2
  have hL1 : Subsingleton ↥(tateCohomology (NU.IShort (G := G)).X₂ (-2)) :=
    NU.subsingleton_tateCohomology_leftRegular G (-2)
  have hL2 : Subsingleton ↥(tateCohomology (NU.IShort (G := G)).X₂ ((-2 : ℤ) + 1)) :=
    NU.subsingleton_tateCohomology_leftRegular G ((-2 : ℤ) + 1)
  obtain ⟨e1⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_iso_of_acyclic_middle_of_subsingleton
      (NU.IShort (G := G)) (NU.IShort_shortExact (G := G)) (-2) hL1 hL2
  exact Nat.card_congr (e1.trans e2).toEquiv

end Commons.RepresentationTheory.TateCohomology
