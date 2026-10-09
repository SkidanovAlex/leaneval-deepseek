import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.phi1_defs
import Submission.Work.SSGRoute.e0b_bridge
import Submission.NK.HassePrinciple.subsingleton_classGroupRep_one
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Ext`-algebra spine of the base case `φ¹` (node E3 `phi1_trivial_mono`)

Extracted from `Submission/Work/SSGRoute/phi1_trivial_mono.lean` (unchanged content) into its own
namespace `Work.SSGRoute.E3Ext` so that the names do not collide with the other `pushClass`
(`Work.SSGRoute.phiPushClass`, used by node E4).

The coefficient sequence `S : 0 → ℤ --p--> ℤ → 𝔽_p → 0` of `SSGRoute.Phi1` is a partial free
resolution of `𝔽_p` in `Rep Coeff G`, so its long exact sequence computes `Ext¹_G(𝔽_p, -)`:
every class is the pushout `pushClass φ` of a `G`-map `φ : ℤ → C` as soon as `H¹(G, C)` vanishes
(`Subsingleton (extH C 1)`), i.e. `Ext¹_G(𝔽_p, C) ≅ C^G/pC^G`; and the pushout vanishes whenever
`φ` factors through multiplication by `p` on `ℤ`.  `phiAt_pushClass_eq` computes the pairing at a
higher level, `bridge_pairing_eq_zero_iff` identifies its vanishing with the vanishing of the
group-cohomology expression, and `subsingleton_extH_classesK` is the `H¹(C_K) = 0` input (through
the `E0b` bridge of `Submission.Work.SSGRoute.Bridge`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

namespace E3Ext

section ExtSpine

variable (p : ℕ) [Fact p.Prime] (G : Type) [Group G]

/-- The **pushout** of the coefficient sequence along a `G`-map `φ : ℤ → C`: the class of
`0 → C → E → 𝔽_p → 0` in `Ext¹_G(𝔽_p, C)`. -/
noncomputable def pushClass (C : Rep SSGRoute.PTExt.Coeff G) (φ : unitRep G ⟶ C) :
    Abelian.Ext (Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p)) C 1 :=
  ((SSGRoute.Phi1.coeffSES_shortExact G p).extClass).comp (Abelian.Ext.mk₀ φ) (add_zero 1)

variable {G}

/-- If `φ` factors through multiplication by `p` on `ℤ`, its pushout class vanishes. -/
lemma pushClass_eq_zero_of_factors (C : Rep SSGRoute.PTExt.Coeff G) (φ : unitRep G ⟶ C)
    (ψ : (SSGRoute.Phi1.coeffSES G p).X₂ ⟶ C)
    (h : φ = SSGRoute.Phi1.unitMulByP G p ≫ ψ) :
    pushClass p G C φ = 0 := by
  have h1 : ((SSGRoute.Phi1.coeffSES_shortExact G p).extClass).comp
      (Abelian.Ext.mk₀ ((SSGRoute.Phi1.coeffSES G p).f)) (add_zero 1) = 0 :=
    ShortComplex.ShortExact.extClass_comp (SSGRoute.Phi1.coeffSES_shortExact G p)
  have key := Abelian.Ext.comp_assoc_of_second_deg_zero
      ((SSGRoute.Phi1.coeffSES_shortExact G p).extClass)
      (Abelian.Ext.mk₀ ((SSGRoute.Phi1.coeffSES G p).f)) (Abelian.Ext.mk₀ ψ) (add_zero 1)
  have h' : φ = (SSGRoute.Phi1.coeffSES G p).f ≫ ψ := h
  rw [pushClass, h']
  rw [← Abelian.Ext.mk₀_comp_mk₀]
  rw [← key, h1]
  simp

/-- **Surjectivity of the pushout**, given `H¹(G, C) = 0`: every class in `Ext¹_G(𝔽_p, C)` is the
pushout of a `G`-map `ℤ → C`. -/
theorem exists_pushClass (C : Rep SSGRoute.PTExt.Coeff G) (hs : Subsingleton (extH C 1))
    (x : Abelian.Ext (Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p)) C 1) :
    ∃ φ : unitRep G ⟶ C, x = pushClass p G C φ := by
  have hs' : Subsingleton (Abelian.Ext (SSGRoute.Phi1.coeffSES G p).X₂ C 1) := hs
  haveI := hs'
  have h0 : ((Abelian.Ext.mk₀ ((SSGRoute.Phi1.coeffSES G p).g)).comp x (zero_add 1)) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨x₁, hx₁⟩ := Abelian.Ext.contravariant_sequence_exact₃
    (S := SSGRoute.Phi1.coeffSES G p) (SSGRoute.Phi1.coeffSES_shortExact G p) C x h0
    (n₀ := 0) (by rfl)
  refine ⟨Abelian.Ext.addEquiv₀ x₁, ?_⟩
  rw [pushClass]
  exact hx₁.symm.trans (congrArg (fun t =>
    ((SSGRoute.Phi1.coeffSES_shortExact G p).extClass).comp t (add_zero 1))
    (Abelian.Ext.mk₀_addEquiv₀_apply x₁).symm)

/-- The `H⁰`-slot map `n ↦ n • a` factors through multiplication by `p` on `ℤ` when
`a = p • b`. -/
lemma powHomCls_eq_unitMulByP_comp (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] (a b : classesK k K)
    (ha : ∀ σ : K ≃ₐ[k] K, (classesK k K).ρ σ a = a)
    (hb : ∀ σ : K ≃ₐ[k] K, (classesK k K).ρ σ b = b) (h : a = (p : Coeff) • b) :
    SSGRoute.Phi1.powHomCls k K a ha
      = SSGRoute.Phi1.unitMulByP (K ≃ₐ[k] K) p ≫ SSGRoute.Phi1.powHomCls k K b hb := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro n
  show n • a = (SSGRoute.Phi1.powHomCls k K b hb)
    ((SSGRoute.Phi1.unitMulByP (K ≃ₐ[k] K) p) n)
  rw [SSGRoute.Phi1.unitMulByP_apply]
  show n • a = ((p : Coeff) * n) • b
  rw [h, mul_comm, mul_smul]

/-- **If `a` is a `p`-th power in `C_k = C_K^{Gal(K/k)}`, then `pushClass` of the `H⁰`-slot of `a`
vanishes.**  This is the final step of the Ext-side computation: the extension class of
`0 → C_K → E → 𝔽_p → 0` built from `a` splits. -/
theorem pushClass_powHomCls_eq_zero_of_eq_smul (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (a b : classesK k K)
    (ha : ∀ σ : K ≃ₐ[k] K, (classesK k K).ρ σ a = a)
    (hb : ∀ σ : K ≃ₐ[k] K, (classesK k K).ρ σ b = b) (h : a = (p : Coeff) • b) :
    pushClass p (K ≃ₐ[k] K) (classesK k K) (SSGRoute.Phi1.powHomCls k K a ha) = 0 :=
  pushClass_eq_zero_of_factors p (classesK k K) (SSGRoute.Phi1.powHomCls k K a ha)
    (SSGRoute.Phi1.powHomCls k K b hb)
    (powHomCls_eq_unitMulByP_comp p k K a b ha hb h)

/-- **`Ext¹_{G_K}(ℤ, C_K) = 0`**: the degree-one case of the `E0b` bridge applied to
`NK.HassePrinciple.subsingleton_classGroupRep_one` (the class formation's `H¹` vanishes). This is
the input of `exists_pushClass`: it exhibits every class of `Ext¹_{G_K}(𝔽_p, C_K)` as the pushout
of a coefficient map `ℤ → C_K`. -/
theorem subsingleton_extH_classesK (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] :
    Subsingleton (extH (classesK k K) 1) :=
  Bridge.subsingleton_extH_of_subsingleton_groupCohomology 1 (K ≃ₐ[k] K) (classesK k K)
    (NK.HassePrinciple.subsingleton_classGroupRep_one NK.GlobalCFTdeep.cyclicHasseInput)

/-- **The pairing at a higher level, computed**: for `x = pushClass φ` at the level `K`, the value
of `phiAt x h` at the level `L ⊇ K` is the Yoneda product of `h` with the coefficient sequence at
the level `L`, composed with the coefficient map `ℤ → C_L`, `1 ↦ (the image of φ 1)`.

This is the `Ext`-algebra heart of the level computation: the coefficient sequences of the two
levels agree definitionally, so `Abelian.Ext.mapExactFunctor` sends the level-`K` class to the
level-`L` one, and everything reduces to associativity of `Abelian.Ext.comp`. -/
theorem phiAt_pushClass_eq {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (φ : unitRep (K ≃ₐ[k] K) ⟶ classesK k K)
    (h : extH (Rep.res (galRes k K L) (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))) 1) :
    phiAt (k := k) (K := K) (L := L) (pushClass p (K ≃ₐ[k] K) (classesK k K) φ) h =
      (h.comp ((SSGRoute.Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p).extClass) (rfl)).comp
        (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map φ ≫ classIncl k K L))
        (add_zero (1 + 1)) := by
  have hext : ((SSGRoute.Phi1.coeffSES_shortExact (K ≃ₐ[k] K) p).extClass).mapExactFunctor
      (Rep.resFunctor (galRes k K L))
      = (SSGRoute.Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p).extClass := by
    rw [Abelian.Ext.mapExactFunctor_extClass]
  simp only [phiAt, levelPair, pushClass, extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀, hext,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero]

/-- **The bridge form of the level pairing**: modulo the bridge `b` (`E0b`), the Ext-side pairing
value at the level `L` vanishes exactly when its group-cohomology counterpart
`groupCohomology.map (id) Φ_L 2 (δ χ)` vanishes, where `Φ_L = res φ ≫ classIncl` is the coefficient
map and `χ` is the group-cohomology class corresponding to `h` under the bridge.

This is the interface at which the CFT input (`Work.SSGRoute.CFTSide.cyclicNormCriterion_classesK`
and its level form) is consumed by the assembly. -/
theorem bridge_pairing_eq_zero_iff (b : SSGRoute.Phi1.ExtGroupCohomologyBridge)
    {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (φ : unitRep (K ≃ₐ[k] K) ⟶ classesK k K)
    (h : extH (Rep.res (galRes k K L) (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))) 1) :
    phiAt (k := k) (K := K) (L := L) (pushClass p (K ≃ₐ[k] K) (classesK k K) φ) h = 0 ↔
      groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L))
        ((Rep.resFunctor (galRes k K L)).map φ ≫ classIncl k K L) 2
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) 1 2 rfl).hom
          ((b.e 1 (L ≃ₐ[k] L) (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p))).symm h)) = 0 := by
  set G := L ≃ₐ[k] L with hG
  set C := classesK k L with hC
  set χ : groupCohomology (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 1 :=
    (b.e 1 G (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p))).symm h with hχ
  have hχe : b.e 1 G (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) χ = h := by
    rw [hχ]; exact (b.e 1 G (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p))).apply_symm_apply h
  have hχe' : b.e 1 G (SSGRoute.Phi1.coeffSES G p).X₃ χ = h := hχe
  have hd := b.delta 1 G (SSGRoute.Phi1.coeffSES G p)
    (SSGRoute.Phi1.coeffSES_shortExact G p) χ
  have hnat := b.naturality 2 G (SSGRoute.Phi1.coeffSES G p).X₁ C
    ((Rep.resFunctor (galRes k K L)).map φ ≫ classIncl k K L)
    ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom χ)
  have hval : (b.e 2 G C)
        (groupCohomology.map (MonoidHom.id G)
          ((Rep.resFunctor (galRes k K L)).map φ ≫ classIncl k K L) 2
          ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom χ)) =
        ((h.comp ((SSGRoute.Phi1.coeffSES_shortExact G p).extClass) (rfl)).comp
          (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map φ ≫ classIncl k K L))
          (add_zero (1 + 1))) ∨
      (b.e 2 G C)
        (groupCohomology.map (MonoidHom.id G)
          ((Rep.resFunctor (galRes k K L)).map φ ≫ classIncl k K L) 2
          ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom χ)) =
        -(((h.comp ((SSGRoute.Phi1.coeffSES_shortExact G p).extClass) (rfl)).comp
          (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map φ ≫ classIncl k K L))
          (add_zero (1 + 1)))) := by
    rw [hnat]
    rcases hd with hh | hh
    · left; rw [hh, hχe']
    · right; rw [hh, hχe']
      exact Abelian.Ext.neg_comp (h.comp ((SSGRoute.Phi1.coeffSES_shortExact G p).extClass) (rfl))
        (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map φ ≫ classIncl k K L))
        (add_zero (1 + 1))
  rw [phiAt_pushClass_eq (p := p) (k := k) (K := K) (L := L) φ h]
  constructor
  · intro hzero
    rcases hval with hv | hv
    · rw [hzero] at hv
      exact (b.e 2 G C).injective (by rw [hv, map_zero])
    · rw [hzero, neg_zero] at hv
      exact (b.e 2 G C).injective (by rw [hv, map_zero])
  · intro hzero
    rcases hval with hv | hv
    · rw [hzero, map_zero] at hv
      exact hv.symm
    · rw [hzero, map_zero] at hv
      exact neg_eq_zero.mp hv.symm

end ExtSpine

end E3Ext

end Work.SSGRoute
