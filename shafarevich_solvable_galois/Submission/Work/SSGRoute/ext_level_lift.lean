import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_idele_defs
import Submission.NK.HassePrinciple.RepOfMonoidHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finitely generated representations and the level lifting (E2, step 2)

Every class of `Ext^r_G(M, 𝕀_K)`, with `M` finitely generated as a `ℤ`-module, is the image of a
class living on a finite level `𝕀_K^S`, for `S` a finite `Gal(K/k)`-stable superset of a prescribed
finite set of places.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

noncomputable section

variable {G : Type} [Group G] [Fintype G]

/-- The free representation on a finite type is a finitely generated `ℤ`-module. -/
theorem freeRep_moduleFinite_int (α : Type) [Finite α] :
    Module.Finite ℤ (Rep.free Coeff G α).V := inferInstance

/-- A representation of a finite group which is finitely generated as a `ℤ`-module. -/
def RepFG (X : Rep.{0} Coeff G) : Prop := Module.Finite ℤ X.V

/-- The value of `Rep.freeLift` at a free generator. -/
theorem rep_freeLift_apply_single (X : Rep.{0} Coeff G) (α : Type) (f : α → X.V) (i : α) :
    (Rep.freeLift (k := Coeff) (G := G) X f)
      (Finsupp.single i (MonoidAlgebra.single 1 1)) = f i := by
  change (X.ρ.freeLift f) (Finsupp.single i (MonoidAlgebra.single 1 1)) = f i
  rw [← Representation.freeLiftLEquiv_apply (σ := X.ρ) (α := α)
    (f := X.ρ.freeLift f) (i := i)]
  rw [show (X.ρ.freeLiftLEquiv α) (X.ρ.freeLift f) = f from
    LinearEquiv.right_inv (X.ρ.freeLiftLEquiv α) f]

/-- The kernel of a morphism from a finite free representation is finitely generated. -/
theorem repFG_kernel {α : Type} [Finite α] (X : Rep.{0} Coeff G)
    (p : Rep.free Coeff G α ⟶ X) : RepFG (Limits.kernel p) := by
  have hmono : Function.Injective (Rep.Hom.hom (Limits.kernel.ι p)) :=
    (Rep.mono_iff_injective _).mp inferInstance
  have hN : IsNoetherian ℤ (Rep.free Coeff G α).V :=
    isNoetherian_of_isNoetherianRing_of_finite ℤ _
  exact Module.Finite.of_injective
    ((Rep.Hom.hom (Limits.kernel.ι p)).toLinearMap.toAddMonoidHom.toIntLinearMap) hmono

/-- Every finitely generated representation admits a surjection from a finite free one. -/
theorem repFG_free_cover (X : Rep.{0} Coeff G) (hX : RepFG X) :
    ∃ n : ℕ, ∃ p : Rep.free Coeff G (Fin n) ⟶ X, Epi p := by
  haveI : Module.Finite ℤ X.V := hX
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := X.V)
  refine ⟨n, Rep.freeLift (k := Coeff) (G := G) X s, ?_⟩
  rw [Rep.epi_iff_surjective]
  intro y
  have hle : Submodule.span ℤ (Set.range s) ≤
      LinearMap.range ((Rep.Hom.hom (Rep.freeLift (k := Coeff) (G := G) X s)).toLinearMap.toAddMonoidHom.toIntLinearMap) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Finsupp.single i (MonoidAlgebra.single 1 1),
      rep_freeLift_apply_single (G := G) X (Fin n) s i⟩
  have hy : y ∈ LinearMap.range
      ((Rep.Hom.hom (Rep.freeLift (k := Coeff) (G := G) X s)).toLinearMap.toAddMonoidHom.toIntLinearMap) :=
    hle (by rw [hs]; trivial)
  obtain ⟨z, hz⟩ := hy
  exact ⟨z, hz⟩

end

section Main

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- A finite representation is finitely generated. -/
theorem repFG_of_finite (X : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite X.V] : RepFG X :=
  by first | exact inferInstance | exact Module.Finite.of_finite

/-- **E2, step 2 (finite-level lifting).**  Every class of `Ext^r_G(M, 𝕀_K)`, with `M` finitely
generated as a `ℤ`-module, is the image of a class living on a finite level `𝕀_K^S` with `S` a
finite `Gal(K/k)`-stable superset of the prescribed finite set `T`. -/
theorem ext_level_lift_aux (r : ℕ) :
    ∀ (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)), RepFG M →
      ∀ (T : Set (NK.GlobalCFT.Place K)) (hT : T.Finite)
        (x : Abelian.Ext M (idelesK k K) r),
        ∃ (S : NK.HassePrinciple.GStableSet k K) (xS : Abelian.Ext M (lvl k K S) r),
          T ⊆ S.carrier ∧ S.carrier.Finite ∧ pushLevel k K M r S xS = x := by
  induction r with
  | zero =>
    intro M hM T hT x
    haveI : Module.Finite ℤ M.V := hM
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := M.V)
    let φ : M ⟶ idelesK k K := Abelian.Ext.addEquiv₀ x
    have hx : Abelian.Ext.mk₀ φ = x := Abelian.Ext.mk₀_addEquiv₀_apply x
    let Φ : M.V → Additive (NK.GlobalCFT.Idele K) := fun m => φ.hom m
    let ψ : M.V → NK.GlobalCFT.Idele K := fun m => Additive.toMul (Φ m)
    have hΦ0 : Φ 0 = (0 : Additive (NK.GlobalCFT.Idele K)) := by
      simp only [Φ]; exact map_zero φ.hom
    have hΦadd : ∀ a b : M.V, Φ (a + b) = Φ a + Φ b := by
      intro a b; simp only [Φ]; exact map_add φ.hom a b
    have hΦzsmul : ∀ (c : ℤ) (a : M.V), Φ (c • a) = c • Φ a := by
      intro c a; simp only [Φ]; exact map_zsmul φ.hom c a
    have hΦsmul : ∀ (σ : K ≃ₐ[k] K) (m : M.V),
        Φ ((M.ρ σ) m) = (idelesK k K).ρ σ (Φ m) := by
      intro σ m; simp only [Φ]; exact LinearMap.congr_fun (φ.hom.2 σ) m
    have ψ_zero : ψ 0 = 1 := by
      simp only [ψ, hΦ0, toMul_zero]
    have ψ_add : ∀ a b : M.V, ψ (a + b) = ψ a * ψ b := by
      intro a b
      simp only [ψ, hΦadd a b, toMul_add]
    have ψ_pow : ∀ (c : ℤ) (a : M.V), ψ (c • a) = (ψ a) ^ c := by
      intro c a
      simp only [ψ, hΦzsmul c a, toMul_zsmul]
    have ψ_csmul : ∀ (c : Coeff) (m : M.V), ψ (c • m) = (ψ m) ^ c.down := by
      intro c m
      have h : Φ (c • m) = c • Φ m := by
        simp only [Φ]
        exact φ.hom.map_smul' c m
      have h2 : ψ (c • m) = Additive.toMul (c • Φ m) := by
        show Additive.toMul (Φ (c • m)) = Additive.toMul (c • Φ m)
        rw [h]
      rw [h2]
      rfl
    have ψ_smul : ∀ (σ : K ≃ₐ[k] K) (m : M.V), ψ ((M.ρ σ) m) = σ • ψ m := by
      intro σ m
      simp only [ψ, hΦsmul σ m]
      rfl
    obtain ⟨S, hSfin, hSsub⟩ :=
      NK.HassePrinciple.exists_gstable_finite_superset (K := k) (L := K)
        (T ∪ ⋃ i : Fin n, {v : NK.GlobalCFT.Place K |
          (ψ (s i)) v ∉ NK.GlobalCFT.Place.localUnits K v})
        (hT.union (Set.finite_iUnion fun i =>
          Filter.eventually_cofinite.mp (ψ (s i)).2))
    have hgen : ∀ i : Fin n, ψ (s i) ∈ NK.HassePrinciple.levelSubgroup S.carrier := by
      intro i
      rw [NK.HassePrinciple.mem_levelSubgroup]
      intro v hv
      by_contra hcon
      exact hv (hSsub (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, hcon⟩)))
    have hmem : ∀ m : M.V, ψ m ∈ NK.HassePrinciple.levelSubgroup S.carrier := by
      intro m
      have hm : m ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; trivial
      refine Submodule.span_induction (s := Set.range s) (p := fun m _ =>
        ψ m ∈ NK.HassePrinciple.levelSubgroup S.carrier) ?_ ?_ ?_ ?_ hm
      · rintro x ⟨i, rfl⟩
        exact hgen i
      · show ψ 0 ∈ _
        rw [ψ_zero]
        exact (NK.HassePrinciple.levelSubgroup S.carrier).one_mem
      · intro a b _ _ ha hb
        show ψ (a + b) ∈ _
        rw [ψ_add]
        exact mul_mem ha hb
      · intro c a _ ha
        show ψ (c • a) ∈ _
        rw [ψ_pow]
        exact Subgroup.zpow_mem _ ha c
    let φS : M ⟶ lvl k K S := Rep.ofHom
      { toFun := fun m => Additive.ofMul ⟨ψ m, hmem m⟩
        map_add' := fun a b => by
          change Additive.ofMul (⟨ψ (a + b), hmem (a + b)⟩ :
              ↥(NK.HassePrinciple.levelSubgroup S.carrier))
            = Additive.ofMul ((⟨ψ a, hmem a⟩ : ↥(NK.HassePrinciple.levelSubgroup S.carrier)) *
              ⟨ψ b, hmem b⟩)
          congr 1
          exact Subtype.ext (ψ_add a b)
        map_smul' := fun a b => by
          rw [show (RingHom.id Coeff) a •
                Additive.ofMul (⟨ψ b, hmem b⟩ : ↥(NK.HassePrinciple.levelSubgroup S.carrier))
              = Additive.ofMul (Additive.toMul (Additive.ofMul
                  (⟨ψ b, hmem b⟩ : ↥(NK.HassePrinciple.levelSubgroup S.carrier))) ^
                  ((RingHom.id Coeff) a).down) from rfl]
          congr 1
          rw [toMul_ofMul, RingHom.id_apply]
          apply Subtype.ext
          rw [Subgroup.coe_zpow]
          simp only [Subtype.coe_mk]
          exact ψ_csmul a b
        isIntertwining' := fun σ => by
          apply LinearMap.ext
          intro m
          apply congrArg Additive.ofMul
          apply Subtype.ext
          exact ψ_smul σ m }
    have hfac : φS ≫ NK.HassePrinciple.levelIncl k K S = φ := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro m
      rfl
    refine ⟨S, Abelian.Ext.mk₀ φS, Set.subset_union_left.trans hSsub, hSfin, ?_⟩
    rw [pushLevel, Abelian.Ext.mk₀_comp_mk₀, hfac, ← hx]
  | succ r ih =>
    intro M hM T hT x
    haveI : Module.Finite ℤ M.V := hM
    obtain ⟨n, p, hp⟩ := repFG_free_cover (G := K ≃ₐ[k] K) M hM
    have hK : RepFG (Limits.kernel p) := repFG_kernel M p
    let S : ShortComplex (Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) :=
      ShortComplex.mk (Limits.kernel.ι p) p (Limits.kernel.condition p)
    have hSe : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel S (CategoryTheory.Limits.kernelIsKernel p) }
    have h1 : 1 + r = r + 1 := by omega
    have hsub : Subsingleton
        (Abelian.Ext (Rep.free Coeff (K ≃ₐ[k] K) (Fin n)) (idelesK k K) (r + 1)) :=
      Abelian.Ext.subsingleton_of_projective _ _ r
    obtain ⟨x₁, hx₁⟩ := Abelian.Ext.contravariant_sequence_exact₃ hSe (idelesK k K)
      (n₁ := r + 1) x (@Subsingleton.elim _ hsub _ _) (n₀ := r) h1
    obtain ⟨S', x₁S, hTS', hS'fin, hpush'⟩ := ih (Limits.kernel p) hK T hT x₁
    refine ⟨S', hSe.extClass.comp x₁S h1, hTS', hS'fin, ?_⟩
    rw [pushLevel, Abelian.Ext.comp_assoc_of_third_deg_zero]
    change hSe.extClass.comp (pushLevel k K (Limits.kernel p) r S' x₁S) h1 = x
    rw [hpush']
    exact hx₁

end Main

end Work.SSGRoute
