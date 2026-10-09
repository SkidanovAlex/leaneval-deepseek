import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_idele_defs
import Submission.NK.HassePrinciple.IdeleCocycle
import Submission.NK.HassePrinciple.RepOfMonoidHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The degree-zero level decomposition (E2, base case)

For a **finite** `Gal(K/k)`-stable set `S` of places and a transversal `R` of the
`Gal(K/k)`-orbits, the evaluation map
`thetaL : Hom_G(M, 𝕀_K^S) → ∏_{w ∈ R} Hom_{D_w}(res_w M, B_w^S)`
is a bijection, where `B_w^S = K_wˣ` for `w ∈ S` and `𝒪_wˣ` otherwise.
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

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-! ## The degree-zero decomposition map -/

/-- **The degree-zero decomposition map**: `φ ↦ (w ↦ res_w φ ≫ levelEval_w)`. -/
noncomputable def thetaL0Map (R : Set (NK.GlobalCFT.Place K))
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K) :
    (M ⟶ lvl k K S) → (w : R) →
      (Rep.res (decompK (k := k) w.1).subtype M ⟶ BOf k K w.1 S) :=
  fun φ w => Rep.resMap (decompK (k := k) w.1).subtype φ ≫ levelEval k K w.1 S

/-- `thetaL` in degree `0` is `mk₀` applied to `thetaL0Map` coordinatewise. -/
theorem thetaL_zero_eq_mk₀ (R : Set (NK.GlobalCFT.Place K))
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
    (φ : M ⟶ lvl k K S) :
    thetaL k K R M 0 S (Abelian.Ext.mk₀ φ)
      = fun w => Abelian.Ext.mk₀ (thetaL0Map k K R M S φ w) := by
  funext w
  simp only [thetaL, thetaL0Map, extRes]
  rw [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]

/-- Casting along an equality of representations applied to its inverse is the identity. -/
theorem eqToHom_symm_apply_cancel {G : Type} [Group G] {A B : Rep Coeff G} (e : A = B)
    (z : B.V) :
    (Rep.Hom.hom (eqToHom e)) ((Rep.Hom.hom (eqToHom e.symm)) z) = z := by
  cases e
  simp

/-- The value of `levelEval` at a place is the `w`-component of the idèle. -/
theorem levelEval_eq_zero_apply_one {w : NK.GlobalCFT.Place K}
    {S : NK.HassePrinciple.GStableSet k K}
    (y : (Rep.res (decompK (k := k) w).subtype (lvl k K S)).V)
    (h : levelEval k K w S y = 0) :
    ((Additive.toMul y : ↥(NK.HassePrinciple.levelSubgroup S.carrier)) :
      NK.GlobalCFT.Idele K) w = 1 := by
  classical
  by_cases hw : w ∈ S.carrier
  · rw [levelEval, dif_pos hw] at h
    rw [Rep.comp_apply] at h
    have h2 := congrArg (fun t => (Rep.Hom.hom (eqToHom (BOf_of_mem (k := k) (K := K) hw))) t) h
    rw [eqToHom_symm_apply_cancel (BOf_of_mem (k := k) (K := K) hw)] at h2
    simp only [map_zero] at h2
    rw [levelEvalA_apply] at h2
    have h3 : Additive.ofMul (((Additive.toMul y :
        ↥(NK.HassePrinciple.levelSubgroup S.carrier)) : NK.GlobalCFT.Idele K) w)
        = Additive.ofMul (1 : (NK.GlobalCFT.Place.localField K w)ˣ) := by
      rw [ofMul_one]
      exact h2
    exact Additive.ofMul.injective h3
  · rw [levelEval, dif_neg hw] at h
    rw [Rep.comp_apply] at h
    have h2 := congrArg (fun t => (Rep.Hom.hom (eqToHom (BOf_of_notMem (k := k) (K := K) hw))) t) h
    rw [eqToHom_symm_apply_cancel (BOf_of_notMem (k := k) (K := K) hw)] at h2
    simp only [map_zero] at h2
    rw [levelEvalSub_apply] at h2
    have h3 : Additive.ofMul (⟨((Additive.toMul y :
        ↥(NK.HassePrinciple.levelSubgroup S.carrier)) : NK.GlobalCFT.Idele K) w,
          NK.HassePrinciple.mem_levelSubgroup.mp (Additive.toMul y).2 w hw⟩ :
            ↥(NK.GlobalCFT.Place.localUnits K w))
        = Additive.ofMul (1 : ↥(NK.GlobalCFT.Place.localUnits K w)) := by
      rw [ofMul_one]
      exact h2
    have h4 := Additive.ofMul.injective h3
    simpa using congrArg (fun t : ↥(NK.GlobalCFT.Place.localUnits K w) =>
      (t : (NK.GlobalCFT.Place.localField K w)ˣ)) h4


/-- The action on a local component is injective. -/
theorem actVal_injective (g : K ≃ₐ[k] K) (w : NK.GlobalCFT.Place K) :
    Function.Injective (NK.HassePrinciple.actVal g w) := by
  intro u v h
  refine Units.ext ?_
  have h2 : ((NK.HassePrinciple.actVal g w u : (NK.GlobalCFT.Place.localField K (g • w))ˣ) :
      NK.GlobalCFT.Place.localField K (g • w)) =
      ((NK.HassePrinciple.actVal g w v : (NK.GlobalCFT.Place.localField K (g • w))ˣ) :
        NK.GlobalCFT.Place.localField K (g • w)) := congrArg Units.val h
  simp only [NK.HassePrinciple.actVal, Units.coe_map] at h2
  exact RingEquiv.injective (NK.GlobalCFT.Place.localRingEquiv g w) h2

/-- An idèle is determined by the components of its translates at a transversal. -/
theorem idele_eq_of_translate_eq (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    {x y : NK.GlobalCFT.Idele K}
    (h : ∀ (w : R) (τ : K ≃ₐ[k] K), (τ • x) w.1 = (τ • y) w.1) : x = y := by
  apply NK.GlobalCFT.Idele.ext
  intro v
  obtain ⟨w, σ, hσ⟩ := exists_eq_smul_of_mem k K hR v
  have h3 : NK.HassePrinciple.actVal σ⁻¹ (σ • w.1) (x (σ • w.1))
      = NK.HassePrinciple.actVal σ⁻¹ (σ • w.1) (y (σ • w.1)) := by
    rw [← NK.HassePrinciple.smul_apply_smul_place (σ⁻¹) (σ • w.1) x,
      ← NK.HassePrinciple.smul_apply_smul_place (σ⁻¹) (σ • w.1) y,
      show σ⁻¹ • (σ • w.1) = w.1 from inv_smul_smul σ w.1]
    exact h w σ⁻¹
  have h4 := actVal_injective k K σ⁻¹ (σ • w.1) h3
  rw [hσ] at h4
  exact h4


/-- **Injectivity of the degree-zero decomposition map.** -/
theorem thetaL0Map_injective (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K) :
    Function.Injective (thetaL0Map k K R M S) := by
  intro φ ψ h
  have hcoord : ∀ (w : R) (m : M.V),
      ((Additive.toMul (φ.hom m) : ↥(NK.HassePrinciple.levelSubgroup S.carrier)) :
        NK.GlobalCFT.Idele K) w.1
      = ((Additive.toMul (ψ.hom m) : ↥(NK.HassePrinciple.levelSubgroup S.carrier)) :
        NK.GlobalCFT.Idele K) w.1 := by
    intro w m
    have h1 : Rep.resMap (decompK (k := k) w.1).subtype φ ≫ levelEval k K w.1 S
        = Rep.resMap (decompK (k := k) w.1).subtype ψ ≫ levelEval k K w.1 S := congrFun h w
    have hA : Rep.resMap (decompK (k := k) w.1).subtype φ ≫ levelEvalA k K w.1 S
        = Rep.resMap (decompK (k := k) w.1).subtype ψ ≫ levelEvalA k K w.1 S := by
      rw [← levelEval_comp_BOfIncl k K w.1 S, ← Category.assoc, h1, Category.assoc]
    have hA2 : (Rep.Hom.hom (Rep.resMap (decompK (k := k) w.1).subtype φ ≫ levelEvalA k K w.1 S)) m
        = (Rep.Hom.hom (Rep.resMap (decompK (k := k) w.1).subtype ψ ≫ levelEvalA k K w.1 S)) m := by
      rw [hA]
    rw [Rep.comp_apply, Rep.comp_apply, Rep.resMap_hom_apply, Rep.resMap_hom_apply,
      levelEvalA_apply, levelEvalA_apply] at hA2
    exact Additive.ofMul.injective hA2
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro m
  apply Additive.toMul.injective
  apply Subtype.ext
  refine idele_eq_of_translate_eq k K R hR ?_
  intro w τ
  show (τ • ((Additive.toMul (φ.hom m) : ↥(NK.HassePrinciple.levelSubgroup S.carrier)) :
      NK.GlobalCFT.Idele K)) w.1
    = (τ • ((Additive.toMul (ψ.hom m) : ↥(NK.HassePrinciple.levelSubgroup S.carrier)) :
      NK.GlobalCFT.Idele K)) w.1
  have keyφ : τ • ((Additive.toMul (φ.hom m) : ↥(NK.HassePrinciple.levelSubgroup S.carrier)) :
      NK.GlobalCFT.Idele K)
      = ((Additive.toMul (φ.hom ((M.ρ τ) m)) : ↥(NK.HassePrinciple.levelSubgroup S.carrier)) :
        NK.GlobalCFT.Idele K) := by
    have heq : φ.hom ((M.ρ τ) m) = (lvl k K S).ρ τ (φ.hom m) :=
      LinearMap.congr_fun (φ.hom.2 τ) m
    rw [heq]
    rfl
  have keyψ : τ • ((Additive.toMul (ψ.hom m) : ↥(NK.HassePrinciple.levelSubgroup S.carrier)) :
      NK.GlobalCFT.Idele K)
      = ((Additive.toMul (ψ.hom ((M.ρ τ) m)) : ↥(NK.HassePrinciple.levelSubgroup S.carrier)) :
        NK.GlobalCFT.Idele K) := by
    have heq : ψ.hom ((M.ρ τ) m) = (lvl k K S).ρ τ (ψ.hom m) :=
      LinearMap.congr_fun (ψ.hom.2 τ) m
    rw [heq]
    rfl
  rw [keyφ, keyψ]
  exact hcoord w ((M.ρ τ) m)


/-! ## The gluing construction (surjectivity of `thetaL0Map`) -/

/-- The point of the transversal `R` representing the orbit of `v`. -/
noncomputable def reprW (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (v : NK.GlobalCFT.Place K) : R :=
  Classical.choose (exists_eq_smul_of_mem k K hR v)

/-- The Galois element carrying `reprW v` to `v`. -/
noncomputable def reprσ (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (v : NK.GlobalCFT.Place K) : K ≃ₐ[k] K :=
  Classical.choose (Classical.choose_spec (exists_eq_smul_of_mem k K hR v))

theorem reprσ_smul_reprW (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (v : NK.GlobalCFT.Place K) : reprσ k K R hR v • (reprW k K R hR v).1 = v :=
  Classical.choose_spec (Classical.choose_spec (exists_eq_smul_of_mem k K hR v))

/-- The value of the inclusion `𝒪_wˣ ↪ K_wˣ` on units. -/
theorem localUnitsIncl_apply_toMul (w : NK.GlobalCFT.Place K)
    (u : (NK.HassePrinciple.localUnitsSubRep k K w).V) :
    Additive.toMul ((NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w).hom u)
      = ((Additive.toMul u : ↥(NK.GlobalCFT.Place.localUnits K w)) :
          (NK.GlobalCFT.Place.localField K w)ˣ) := rfl

/-- The membership in `𝒪_wˣ` of the local value attached to `w` by a family `a` at a place
outside the level. -/
theorem BOfIncl_apply_toMul_mem {w : NK.GlobalCFT.Place K}
    {S : NK.HassePrinciple.GStableSet k K} (hw : w ∉ S.carrier)
    (z : (BOf k K w S).V) :
    Additive.toMul ((BOfIncl k K w S).hom z) ∈ NK.GlobalCFT.Place.localUnits K w := by
  rw [BOfIncl_of_notMem (k := k) (K := K) hw, Rep.comp_apply, localUnitsIncl_apply_toMul]
  exact (Additive.toMul ((Rep.Hom.hom (eqToHom (BOf_of_notMem (k := k) (K := K) hw))) z)).2

/-- The local value at `v` attached to the representative place `reprW k K R hR v`. -/
noncomputable def localVal (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
    (a : ∀ w : R, Rep.res (decompK (k := k) w.1).subtype M ⟶ BOf k K w.1 S)
    (m : M.V) (v : NK.GlobalCFT.Place K) :
    (NK.GlobalCFT.Place.localField K (reprW k K R hR v).1)ˣ :=
  Additive.toMul ((BOfIncl k K (reprW k K R hR v).1 S).hom
    (a (reprW k K R hR v) (M.ρ (reprσ k K R hR v)⁻¹ m)))

/-- Outside the level the local value is a local unit. -/
theorem localVal_mem_localUnits (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
    (a : ∀ w : R, Rep.res (decompK (k := k) w.1).subtype M ⟶ BOf k K w.1 S)
    (m : M.V) {v : NK.GlobalCFT.Place K} (hv : v ∉ S.carrier) :
    localVal k K R hR M S a m v ∈
      NK.GlobalCFT.Place.localUnits K (reprW k K R hR v).1 :=
  BOfIncl_apply_toMul_mem (k := k) (K := K)
    (fun hmem => hv (by rw [← reprσ_smul_reprW k K R hR v]; exact S.smul_mem' _ hmem)) _

/-- **The glued idèle**: combine the local data `a w` on the orbits of the transversal `R`. -/
noncomputable def glueIdele (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
    (hS : S.carrier.Finite)
    (a : ∀ w : R, Rep.res (decompK (k := k) w.1).subtype M ⟶ BOf k K w.1 S)
    (m : M.V) : NK.GlobalCFT.Idele K :=
  ⟨fun v => ((reprσ k K R hR v) • NK.HassePrinciple.onePlace (reprW k K R hR v).1
      (localVal k K R hR M S a m v)) v, by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset hS (fun v hv => ?_)
    by_contra hvS
    exact hv (NK.HassePrinciple.smul_onePlace_mem_localUnits
      (localVal_mem_localUnits k K R hR M S a m hvS) v)⟩

/-- The value of the glued idèle, expressed through `actVal`. -/
theorem glueIdele_apply (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
    (hS : S.carrier.Finite)
    (a : ∀ w : R, Rep.res (decompK (k := k) w.1).subtype M ⟶ BOf k K w.1 S)
    (m : M.V) (v : NK.GlobalCFT.Place K) :
    (glueIdele k K R hR M S hS a m) v
      = (reprσ_smul_reprW k K R hR v) ▸
        NK.HassePrinciple.actVal (reprσ k K R hR v) (reprW k K R hR v).1
          (localVal k K R hR M S a m v) :=
  NK.HassePrinciple.smul_onePlace_apply_of_eq (reprσ_smul_reprW k K R hR v) _

/-! ### Cast lemmas for the local fields -/

/-- `Additive.toMul` with the local field made explicit (the implicit `α` of `Additive.toMul`
otherwise confuses the elaborator under `rw`). -/
abbrev toLocal (w : NK.GlobalCFT.Place K) (z : (localUnitsK (k := k) w).V) :
    (NK.GlobalCFT.Place.localField K w)ˣ :=
  Additive.toMul (α := (NK.GlobalCFT.Place.localField K w)ˣ) z

theorem cast_symm_trans {L : Type} [Field L] [NumberField L] {a b c : NK.GlobalCFT.Place L}
    (h : a = b) (h' : b = c) (x : (NK.GlobalCFT.Place.localField L c)ˣ) :
    (h.trans h').symm ▸ x = h.symm ▸ (h'.symm ▸ x) := by
  cases h; cases h'; rfl

theorem cast_symm_self {L : Type} [Field L] [NumberField L] {a b : NK.GlobalCFT.Place L}
    (h : a = b) (x : (NK.GlobalCFT.Place.localField L a)ˣ) : h.symm ▸ (h ▸ x) = x := by
  cases h; rfl

/-- The value of the `D_w`-action on the local units, in the `localUnitsEquiv` form. -/
theorem units_map_localAut_eq_localUnitsEquiv (w : NK.GlobalCFT.Place K)
    (d : MulAction.stabilizer (K ≃ₐ[k] K) w) (u : (NK.GlobalCFT.Place.localField K w)ˣ) :
    Units.map (NK.HassePrinciple.localAut w d).toMonoidHom u
      = NK.HassePrinciple.localUnitsEquiv (K := k) w d u := by
  apply Units.ext
  rw [NK.HassePrinciple.coe_localUnitsEquiv, Units.coe_map]
  rfl

/-- The action of the `D_w`-action on the local value, with the stabiliser transport explicit. -/
theorem actVal_stabilizer_eq_units_map (w : NK.GlobalCFT.Place K)
    (d : MulAction.stabilizer (K ≃ₐ[k] K) w) (u : (NK.GlobalCFT.Place.localField K w)ˣ) :
    (MulAction.mem_stabilizer_iff.mp d.2) ▸ NK.HassePrinciple.actVal d.1 w u
      = NK.HassePrinciple.localUnitsEquiv (K := k) w d u :=
  (NK.HassePrinciple.actVal_stabilizer w d u).trans
    (units_map_localAut_eq_localUnitsEquiv k K w d u)

/-- The `toLocal` form of the `ρ`-action on the local units. -/
theorem toLocal_ρ (w : NK.GlobalCFT.Place K) (σ : decompK (k := k) w)
    (z : (localUnitsK (k := k) w).V) :
    toLocal k K w ((localUnitsK (k := k) w).ρ σ z)
      = NK.HassePrinciple.localUnitsEquiv (K := k) w σ (toLocal k K w z) := rfl

/-! ## The local gluing map -/

/-- The local value attached to a place `w` of the transversal and a Galois element `σ`, evaluated
in the local field at `σ • w`. -/
noncomputable def glueAt (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
    (a : ∀ w : R, Rep.res (decompK (k := k) w.1).subtype M ⟶ BOf k K w.1 S)
    (w : R) (σ : K ≃ₐ[k] K) (m : M.V) :
    (NK.GlobalCFT.Place.localField K (σ • w.1))ˣ :=
  NK.HassePrinciple.actVal σ w.1
    (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w ((M.ρ σ⁻¹) m))))

/-- The glued idèle is assembled from `glueAt` at the chosen representatives. -/
theorem glueIdele_eq_glueAt (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
    (hS : S.carrier.Finite)
    (a : ∀ w : R, Rep.res (decompK (k := k) w.1).subtype M ⟶ BOf k K w.1 S)
    (m : M.V) (v : NK.GlobalCFT.Place K) :
    (glueIdele k K R hR M S hS a m) v
      = (reprσ_smul_reprW k K R hR v) ▸
        glueAt k K R hR M S a (reprW k K R hR v) (reprσ k K R hR v) m :=
  glueIdele_apply k K R hR M S hS a m v

/-! ### Well-definedness of the gluing over the `D_w`-cosets -/

/-- **Well-definedness of the gluing over the `D_w`-cosets.** -/
theorem glueAt_coset (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
    (a : ∀ w : R, Rep.res (decompK (k := k) w.1).subtype M ⟶ BOf k K w.1 S)
    (m : M.V) (w : R) (σ : K ≃ₐ[k] K)
    (d : MulAction.stabilizer (K ≃ₐ[k] K) w.1) :
    glueAt k K R hR M S a w (σ * d.1) m
      = ((mul_smul σ d.1 w.1).trans (congrArg (fun u => σ • u)
          (MulAction.mem_stabilizer_iff.mp d.2))).symm
          ▸ glueAt k K R hR M S a w σ m := by
  have hinv : ((σ * d.1))⁻¹ = d.1⁻¹ * σ⁻¹ := mul_inv_rev σ d.1
  have hMm : (M.ρ ((σ * d.1))⁻¹) m = (M.ρ d.1⁻¹) ((M.ρ σ⁻¹) m) := by
    rw [hinv, map_mul]
    rfl
  have ha : (a w).hom ((M.ρ d.1⁻¹) ((M.ρ σ⁻¹) m))
      = ((BOf k K w.1 S).ρ d⁻¹) ((a w).hom ((M.ρ σ⁻¹) m)) :=
    LinearMap.congr_fun ((a w).hom.2 d⁻¹) ((M.ρ σ⁻¹) m)
  have hb := LinearMap.congr_fun ((BOfIncl k K w.1 S).hom.2 d⁻¹)
    ((a w).hom ((M.ρ σ⁻¹) m))
  have hlocal : toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ ((σ * d.1))⁻¹ m)))
      = NK.HassePrinciple.localUnitsEquiv (K := k) w.1 d⁻¹
          (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w ((M.ρ σ⁻¹) m)))) := by
    rw [hMm]
    have hHa : toLocal k K w.1 ((BOfIncl k K w.1 S).hom
          ((a w).hom ((M.ρ d.1⁻¹) ((M.ρ σ⁻¹) m))))
        = toLocal k K w.1 ((BOfIncl k K w.1 S).hom
            (((BOf k K w.1 S).ρ d⁻¹) ((a w).hom ((M.ρ σ⁻¹) m)))) :=
      congrArg (fun zz => toLocal k K w.1 ((BOfIncl k K w.1 S).hom zz)) ha
    rw [hHa]
    have hHb : toLocal k K w.1 ((BOfIncl k K w.1 S).hom
          (((BOf k K w.1 S).ρ d⁻¹) ((a w).hom ((M.ρ σ⁻¹) m))))
        = toLocal k K w.1 (((localUnitsK (k := k) w.1).ρ d⁻¹)
            ((BOfIncl k K w.1 S).hom ((a w).hom ((M.ρ σ⁻¹) m)))) :=
      congrArg (fun zz => toLocal k K w.1 zz) hb
    rw [hHb, toLocal_ρ]
  have hstep1 : (MulAction.mem_stabilizer_iff.mp d.2)
        ▸ NK.HassePrinciple.actVal d.1 w.1
          (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ ((σ * d.1))⁻¹ m))))
      = NK.HassePrinciple.localUnitsEquiv (K := k) w.1 d
          (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ ((σ * d.1))⁻¹ m)))) :=
    actVal_stabilizer_eq_units_map k K w.1 d _
  have hstep2 : NK.HassePrinciple.localUnitsEquiv (K := k) w.1 d
        (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ ((σ * d.1))⁻¹ m))))
      = toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w ((M.ρ σ⁻¹) m))) := by
    rw [hlocal]
    rw [show NK.HassePrinciple.localUnitsEquiv (K := k) w.1 d
          (NK.HassePrinciple.localUnitsEquiv (K := k) w.1 d⁻¹
            (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w ((M.ρ σ⁻¹) m)))))
        = (NK.HassePrinciple.localUnitsEquiv (K := k) w.1 d
            * NK.HassePrinciple.localUnitsEquiv (K := k) w.1 d⁻¹)
            (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w ((M.ρ σ⁻¹) m)))) from rfl,
      ← NK.HassePrinciple.localUnitsEquiv_mul, mul_inv_cancel,
      NK.HassePrinciple.localUnitsEquiv_one]
    rfl
  have hx2 : (MulAction.mem_stabilizer_iff.mp d.2)
        ▸ NK.HassePrinciple.actVal d.1 w.1
          (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ ((σ * d.1))⁻¹ m))))
      = toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w ((M.ρ σ⁻¹) m))) :=
    hstep1.trans hstep2
  have hmain : NK.HassePrinciple.actVal σ (d.1 • w.1)
        (NK.HassePrinciple.actVal d.1 w.1
          (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ ((σ * d.1))⁻¹ m)))))
      = (congrArg (fun u => σ • u) (MulAction.mem_stabilizer_iff.mp d.2)).symm
          ▸ NK.HassePrinciple.actVal σ w.1
            (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w ((M.ρ σ⁻¹) m)))) := by
    rw [← hx2]
    rw [NK.HassePrinciple.actVal_cast (MulAction.mem_stabilizer_iff.mp d.2)
      (NK.HassePrinciple.actVal d.1 w.1
        (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ ((σ * d.1))⁻¹ m)))))]
    rw [cast_symm_self]
  unfold glueAt
  rw [NK.HassePrinciple.actVal_comp σ d.1 w.1
      (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ ((σ * d.1))⁻¹ m)))),
    cast_symm_trans (mul_smul σ d.1 w.1)
      (congrArg (fun u => σ • u) (MulAction.mem_stabilizer_iff.mp d.2))
      (NK.HassePrinciple.actVal σ w.1
        (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w ((M.ρ σ⁻¹) m))))), hmain]

/-- The representatives of `σ • w` and of `w` agree. -/
theorem reprW_smul_mem (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (w : R) (σ : K ≃ₐ[k] K) :
    reprW k K R hR (σ • w.1) = w := by
  obtain ⟨u, -, huniq⟩ := hR (σ • w.1)
  have h1 : reprW k K R hR (σ • w.1) = u :=
    huniq _ ⟨(reprσ k K R hR (σ • w.1))⁻¹,
      inv_smul_eq_iff.mpr (reprσ_smul_reprW k K R hR (σ • w.1)).symm⟩
  have h2 : w = u := huniq _ ⟨σ⁻¹, inv_smul_smul σ w.1⟩
  exact h1.trans h2.symm

/-- The representative of `τ⁻¹ • v` is the representative of `v`. -/
theorem reprW_smul_inv (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (v : NK.GlobalCFT.Place K) (τ : K ≃ₐ[k] K) :
    reprW k K R hR (τ⁻¹ • v) = reprW k K R hR v := by
  obtain ⟨u, -, huniq⟩ := hR (τ⁻¹ • v)
  have h1 : reprW k K R hR (τ⁻¹ • v) = u :=
    huniq _ ⟨(reprσ k K R hR (τ⁻¹ • v))⁻¹,
      inv_smul_eq_iff.mpr (reprσ_smul_reprW k K R hR (τ⁻¹ • v)).symm⟩
  have h2 : reprW k K R hR v = u :=
    huniq _ ⟨(reprσ k K R hR v)⁻¹ * τ, by
      rw [mul_smul, smul_inv_smul]
      exact inv_smul_eq_iff.mpr (reprσ_smul_reprW k K R hR v).symm⟩
  exact h1.trans h2.symm

/-- The Galois element at `τ⁻¹ • v` acts on the representative of `v` by `τ⁻¹`. -/
theorem reprσ_smul_inv_eq (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (v : NK.GlobalCFT.Place K) (τ : K ≃ₐ[k] K) :
    reprσ k K R hR (τ⁻¹ • v) • (reprW k K R hR v).1 = τ⁻¹ • v := by
  rw [← congrArg Subtype.val (reprW_smul_inv k K R hR v τ)]
  exact reprσ_smul_reprW k K R hR (τ⁻¹ • v)

/-- The correcting element lies in the decomposition group of `reprW v`. -/
theorem reprσ_smul_inv_mem (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (v : NK.GlobalCFT.Place K) (τ : K ≃ₐ[k] K) :
    ((τ⁻¹ * reprσ k K R hR v)⁻¹ * reprσ k K R hR (τ⁻¹ • v))
      ∈ MulAction.stabilizer (K ≃ₐ[k] K) (reprW k K R hR v).1 := by
  rw [MulAction.mem_stabilizer_iff, mul_smul, reprσ_smul_inv_eq k K R hR v τ,
    mul_inv_rev, mul_smul, inv_inv, smul_inv_smul]
  exact inv_smul_eq_iff.mpr (reprσ_smul_reprW k K R hR v).symm


variable (R : Set (NK.GlobalCFT.Place K))
  (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
  (M : Rep.{0,0,0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
  (hS : S.carrier.Finite)
  (a : ∀ w : R, Rep.res (decompK (k := k) w.1).subtype M ⟶ BOf k K w.1 S)

theorem glueAt_add (w : R) (σ : K ≃ₐ[k] K) (m₁ m₂ : M.V) :
    glueAt k K R hR M S a w σ (m₁ + m₂)
      = glueAt k K R hR M S a w σ m₁ * glueAt k K R hR M S a w σ m₂ := by
  have key : toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w ((M.ρ σ⁻¹) (m₁ + m₂))))
      = toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w ((M.ρ σ⁻¹) m₁)))
        * toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w ((M.ρ σ⁻¹) m₂))) := by
    rw [map_add, map_add, map_add]
    rfl
  unfold glueAt
  rw [key, NK.HassePrinciple.actVal_mul]

theorem glueIdele_add (m₁ m₂ : M.V) :
    glueIdele k K R hR M S hS a (m₁ + m₂)
      = glueIdele k K R hR M S hS a m₁ * glueIdele k K R hR M S hS a m₂ := by
  apply NK.GlobalCFT.Idele.ext
  intro v
  rw [NK.GlobalCFT.Idele.mul_apply, glueIdele_eq_glueAt k K R hR M S hS a (m₁ + m₂) v,
    glueIdele_eq_glueAt k K R hR M S hS a m₁ v, glueIdele_eq_glueAt k K R hR M S hS a m₂ v,
    glueAt_add k K R hR M S a (reprW k K R hR v) (reprσ k K R hR v) m₁ m₂]
  rw [NK.HassePrinciple.cast_mul]

theorem glueIdele_zero :
    glueIdele k K R hR M S hS a (0 : M.V) = 1 := by
  have h : glueIdele k K R hR M S hS a (0 : M.V)
      = glueIdele k K R hR M S hS a (0:M.V) * glueIdele k K R hR M S hS a (0:M.V) := by
    have h2 := glueIdele_add k K R hR M S hS a (0:M.V) (0:M.V)
    simpa using h2
  exact (mul_left_cancel (show glueIdele k K R hR M S hS a (0:M.V) * 1
    = glueIdele k K R hR M S hS a (0:M.V) * glueIdele k K R hR M S hS a (0:M.V) by
      rw [← h, mul_one])).symm

theorem glueIdele_mem (m : M.V) :
    glueIdele k K R hR M S hS a m ∈ NK.HassePrinciple.levelSubgroup S.carrier := by
  intro v hv
  show ((reprσ k K R hR v) • NK.HassePrinciple.onePlace (reprW k K R hR v).1
      (localVal k K R hR M S a m v)) v ∈ NK.GlobalCFT.Place.localUnits K v
  exact NK.HassePrinciple.smul_onePlace_mem_localUnits
    (localVal_mem_localUnits k K R hR M S a m hv) v

theorem glueIdele_zsmul (n : ℤ) (m : M.V) :
    glueIdele k K R hR M S hS a (n • m)
      = (glueIdele k K R hR M S hS a m) ^ n := by
  let Φ : M.V →+ Additive (NK.GlobalCFT.Idele K) :=
    { toFun := fun x => Additive.ofMul (glueIdele k K R hR M S hS a x)
      map_zero' := by
        rw [ofMul_eq_zero]
        exact glueIdele_zero k K R hR M S hS a
      map_add' := fun x y => by
        rw [glueIdele_add k K R hR M S hS a x y, ofMul_mul] }
  have h2 := congrArg Additive.toMul (AddMonoidHom.map_zsmul Φ n m)
  rw [show Additive.toMul (Φ (n • m)) = glueIdele k K R hR M S hS a (n • m) from rfl,
    toMul_zsmul, show Additive.toMul (Φ m) = glueIdele k K R hR M S hS a m from rfl] at h2
  exact h2

theorem coeff_smul_eq_zsmul (n : ℤ) (m : M.V) :
    (ULift.up n : Coeff) • m = n • m := by
  have h1 : (ULift.up n : Coeff) = (n : Coeff) := ULift.up_intCast (R := ℤ) n
  rw [h1]
  exact Int.cast_smul_eq_zsmul (R := Coeff) n m


theorem reprW_self (w : R) : reprW k K R hR w.1 = w := by
  obtain ⟨u, -, huniq⟩ := hR w.1
  have h1 : reprW k K R hR w.1 = u :=
    huniq _ ⟨(reprσ k K R hR w.1)⁻¹,
      inv_smul_eq_iff.mpr (reprσ_smul_reprW k K R hR w.1).symm⟩
  have h2 : w = u := huniq _ ⟨1, one_smul _ _⟩
  exact h1.trans h2.symm

theorem reprW_self_smul (w : R) : reprσ k K R hR w.1 • w.1 = w.1 := by
  have h := reprσ_smul_reprW k K R hR w.1
  rw [reprW_self k K R hR w] at h
  exact h

theorem cast_glueAt_congr {w w' : R} (h : w = w') (σ : K ≃ₐ[k] K) (m : M.V)
    (e : σ • w.1 = w'.1) (hsm : σ • w'.1 = w'.1) :
    e ▸ glueAt k K R hR M S a w σ m = hsm ▸ glueAt k K R hR M S a w' σ m := by
  subst h
  rw [Subsingleton.elim e hsm]

theorem toLocal_coset {m : M.V} (w : R) (σ : K ≃ₐ[k] K)
    (d : MulAction.stabilizer (K ≃ₐ[k] K) w.1) :
    toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ ((σ * d.1))⁻¹ m)))
      = NK.HassePrinciple.localUnitsEquiv (K := k) w.1 d⁻¹
          (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ σ⁻¹ m)))) := by
  have hinv : ((σ * d.1))⁻¹ = d.1⁻¹ * σ⁻¹ := mul_inv_rev σ d.1
  have hMm : (M.ρ ((σ * d.1))⁻¹) m = (M.ρ d.1⁻¹) ((M.ρ σ⁻¹) m) := by
    rw [hinv, map_mul]
    rfl
  have ha : (a w).hom ((M.ρ d.1⁻¹) ((M.ρ σ⁻¹) m))
      = ((BOf k K w.1 S).ρ d⁻¹) ((a w).hom ((M.ρ σ⁻¹) m)) :=
    LinearMap.congr_fun ((a w).hom.2 d⁻¹) ((M.ρ σ⁻¹) m)
  have hb := LinearMap.congr_fun ((BOfIncl k K w.1 S).hom.2 d⁻¹)
    ((a w).hom ((M.ρ σ⁻¹) m))
  rw [hMm]
  have hHa : toLocal k K w.1 ((BOfIncl k K w.1 S).hom
        ((a w).hom ((M.ρ d.1⁻¹) ((M.ρ σ⁻¹) m))))
      = toLocal k K w.1 ((BOfIncl k K w.1 S).hom
          (((BOf k K w.1 S).ρ d⁻¹) ((a w).hom ((M.ρ σ⁻¹) m)))) :=
    congrArg (fun zz => toLocal k K w.1 ((BOfIncl k K w.1 S).hom zz)) ha
  rw [hHa]
  have hHb : toLocal k K w.1 ((BOfIncl k K w.1 S).hom
        (((BOf k K w.1 S).ρ d⁻¹) ((a w).hom ((M.ρ σ⁻¹) m))))
      = toLocal k K w.1 (((localUnitsK (k := k) w.1).ρ d⁻¹)
          ((BOfIncl k K w.1 S).hom ((a w).hom ((M.ρ σ⁻¹) m)))) :=
    congrArg (fun zz => toLocal k K w.1 zz) hb
  rw [hHb, toLocal_ρ]

theorem localUnitsEquiv_coset {m : M.V} (w : R) (σ : K ≃ₐ[k] K)
    (d : MulAction.stabilizer (K ≃ₐ[k] K) w.1) :
    NK.HassePrinciple.localUnitsEquiv (K := k) w.1 d
        (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ ((σ * d.1))⁻¹ m))))
      = toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ σ⁻¹ m))) := by
  rw [toLocal_coset k K R M S a w σ d]
  rw [show NK.HassePrinciple.localUnitsEquiv (K := k) w.1 d
        (NK.HassePrinciple.localUnitsEquiv (K := k) w.1 d⁻¹
          (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ σ⁻¹ m)))))
      = (NK.HassePrinciple.localUnitsEquiv (K := k) w.1 d
          * NK.HassePrinciple.localUnitsEquiv (K := k) w.1 d⁻¹)
          (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ σ⁻¹ m)))) from rfl,
    ← NK.HassePrinciple.localUnitsEquiv_mul, mul_inv_cancel,
    NK.HassePrinciple.localUnitsEquiv_one]
  rfl

theorem actVal_glueAt_eq {m : M.V} (w : R) (σ : K ≃ₐ[k] K)
    (d : MulAction.stabilizer (K ≃ₐ[k] K) w.1) :
    (MulAction.mem_stabilizer_iff.mp d.2) ▸ NK.HassePrinciple.actVal d.1 w.1
        (toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ ((σ * d.1))⁻¹ m))))
      = toLocal k K w.1 ((BOfIncl k K w.1 S).hom (a w (M.ρ σ⁻¹ m))) :=
  (actVal_stabilizer_eq_units_map k K w.1 d _).trans
    (localUnitsEquiv_coset k K R M S a w σ d)

theorem glueAt_reprW_eq (v : NK.GlobalCFT.Place K) (m : M.V) :
    glueAt k K R hR M S a (reprW k K R hR v) (reprσ k K R hR v) m
      = NK.HassePrinciple.actVal (reprσ k K R hR v) (reprW k K R hR v).1
          (localVal k K R hR M S a m v) := rfl

theorem glueIdele_apply_repr (w : R) (m : M.V) :
    (glueIdele k K R hR M S hS a m) w.1
      = toLocal k K w.1 ((BOfIncl k K w.1 S).hom ((a w) m)) := by
  rw [glueIdele_apply k K R hR M S hS a m w.1, ← glueAt_reprW_eq k K R hR M S a w.1 m]
  rw [cast_glueAt_congr k K R hR M S a (reprW_self k K R hR w)
      (reprσ k K R hR w.1) m (reprσ_smul_reprW k K R hR w.1)
      (reprW_self_smul k K R hR w)]
  unfold glueAt
  set d : MulAction.stabilizer (K ≃ₐ[k] K) w.1 :=
    ⟨reprσ k K R hR w.1, MulAction.mem_stabilizer_iff.mpr (reprW_self_smul k K R hR w)⟩
    with hd
  have hkey := actVal_glueAt_eq k K R M S a w (1 : K ≃ₐ[k] K) d (m := m)
  rw [show (M.ρ ((1 : K ≃ₐ[k] K)⁻¹)) m = m from by rw [inv_one, map_one]; rfl] at hkey
  rw [show (MulAction.mem_stabilizer_iff.mp d.2) = reprW_self_smul k K R hR w from
    Subsingleton.elim _ _] at hkey
  exact hkey


theorem repEqToHom_hom_apply {G : Type} [Group G] {A B : Rep.{0,0,0} Coeff G}
    (e : A = B) (x : A.V) :
    (Rep.Hom.hom (eqToHom e)) x = (e ▸ x : B.V) := by cases e; rfl

theorem cast_symm_self_gen (α : Type) (F : α → Type) (a b : α) (h : a = b) (x : F a) :
    h.symm ▸ (h ▸ x) = x := by cases h; rfl

/-! ## The glued morphism `M ⟶ lvl k K S` -/

include R hR hS a in
/-- **The glued morphism**: combine the local data `a` on the orbits of `R` into a
`Gal(K/k)`-equivariant map `M → 𝕀_K^S`.  The equivariance of the glued idèle is taken as a
hypothesis (it is `glueIdele_smul`). -/
noncomputable def glueHomOf
    (hs : ∀ (m : M.V) (τ : K ≃ₐ[k] K),
      glueIdele k K R hR M S hS a ((M.ρ τ) m) = τ • glueIdele k K R hR M S hS a m) :
    M ⟶ lvl k K S :=
  Rep.ofHom
  { toFun := fun m => Additive.ofMul
      ⟨glueIdele k K R hR M S hS a m, glueIdele_mem k K R hR M S hS a m⟩
    map_add' := fun m₁ m₂ => by
      change Additive.ofMul (⟨glueIdele k K R hR M S hS a (m₁ + m₂), _⟩ :
          ↥(NK.HassePrinciple.levelSubgroup S.carrier))
        = Additive.ofMul ((⟨glueIdele k K R hR M S hS a m₁, _⟩ :
            ↥(NK.HassePrinciple.levelSubgroup S.carrier)) *
          ⟨glueIdele k K R hR M S hS a m₂, _⟩)
      congr 1
      exact Subtype.ext (glueIdele_add k K R hR M S hS a m₁ m₂)
    map_smul' := fun c m => by
      rw [show (RingHom.id Coeff) c •
            Additive.ofMul (⟨glueIdele k K R hR M S hS a m, _⟩ :
              ↥(NK.HassePrinciple.levelSubgroup S.carrier))
          = Additive.ofMul ((⟨glueIdele k K R hR M S hS a m, _⟩ :
              ↥(NK.HassePrinciple.levelSubgroup S.carrier)) ^ c.down) from rfl]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      show glueIdele k K R hR M S hS a (c • m)
        = (glueIdele k K R hR M S hS a m) ^ c.down
      have hc : c • m = c.down • m := by
        have h1 : c = (c.down : Coeff) := by
          cases c with
          | up n => rw [← ULift.up_intCast (R := ℤ) n]; rfl
        rw [h1]
        exact Int.cast_smul_eq_zsmul (R := Coeff) c.down m
      rw [hc, glueIdele_zsmul]
    isIntertwining' := fun σ => by
      apply LinearMap.ext
      intro m
      apply congrArg Additive.ofMul
      apply Subtype.ext
      exact hs m σ }


end

end Work.SSGRoute
