import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.E1aClean.decompFieldHenselEmb_relAlgClosed
import Submission.Work.SSGRoute.E1aClean.decompField_hensel_groupIso
import Submission.Work.SSGRoute.E1aClean.henselEmb_equivariant
import Submission.Work.SSGRoute.E1aClean.unitsQuotient_pow_bijective_fixed
import Submission.Work.SSGRoute.ExtChain.exists_primeUnder_hAq
import Submission.Work.SSGRoute.ExtChain.ext1_p_divisible
import Submission.Work.SSGRoute.ExtChain.extLoc_extToIdeles_e1aSyzShift_eq_zero_imp
import Submission.Work.SSGRoute.ExtChain.push_injective_syzygy
import Submission.Work.SSGRoute.PT.e1aBetaCan_hAq_decomp_map
import Submission.Work.SSGRoute.PT.pt_pairing_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

noncomputable section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]

/-- **The group isomorphism `D_q ≃* Gal(K^h/k^h)` computed by the global action.**
If `σ ∈ D_A` and `τ ∈ D_q` have the same image in `Gal(K/k)`, then `e τ` and `σ` agree on `K^h`. -/
theorem henselGroupIso_apply_eq_of_res_eq
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (E1aClean.henselOverDecomp k Ω K A ≃ₐ[E1aClean.decompField k Ω A]
        E1aClean.henselOverDecomp k Ω K A))
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : K),
      ((e τ) ⟨(x : Ω), E1aClean.le_henselField k Ω K A x.2⟩ : Ω) = ((τ : K ≃ₐ[k] K) x : Ω))
    (σ : ↥(SSGRoute.decomp k A))
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (hστ : (τ : K ≃ₐ[k] K) = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) :
    ∀ x : ↥(E1aClean.henselOverDecomp k Ω K A),
      ((e τ) x : Ω) = (σ : Ω ≃ₐ[k] Ω) (x : Ω) := by
  intro x
  have hσfix : ∀ z : ↥(E1aClean.decompField k Ω A),
      (σ : Ω ≃ₐ[k] Ω) (z : Ω) = (z : Ω) := by
    intro z
    have hmem : (σ : Ω ≃ₐ[k] Ω) ∈ (E1aClean.decompField k Ω A).fixingSubgroup := by
      rw [E1aClean.decompField_fixingSubgroup_via k Ω K A rfl]
      exact σ.2
    exact hmem z
  let f₁ : ↥(E1aClean.henselOverDecomp k Ω K A) →+* Ω :=
    { toFun := fun y => ((e τ) y : Ω)
      map_one' := by rw [map_one]; rfl
      map_mul' := fun a b => by rw [map_mul]; rfl
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun a b => by rw [map_add]; rfl }
  let f₂ : ↥(E1aClean.henselOverDecomp k Ω K A) →+* Ω :=
    { toFun := fun y => (σ : Ω ≃ₐ[k] Ω) (y : Ω)
      map_one' := by rw [IntermediateField.coe_one, map_one]
      map_mul' := fun a b => by rw [IntermediateField.coe_mul, map_mul]
      map_zero' := by rw [IntermediateField.coe_zero, map_zero]
      map_add' := fun a b => by rw [IntermediateField.coe_add, map_add] }
  have hS_le : IntermediateField.adjoin k (↑(E1aClean.decompField k Ω A) ∪ (↑K : Set Ω))
      ≤ E1aClean.henselField k Ω K A :=
    IntermediateField.adjoin_le_iff.mpr (by
      rintro z (hz | hz)
      · exact E1aClean.decompField_le_henselField k Ω K A hz
      · exact E1aClean.le_henselField k Ω K A hz)
  have keyK : ∀ (y : ↥K) (hy : (y : Ω) ∈ E1aClean.henselField k Ω K A),
      f₁ ⟨(y : Ω), hy⟩ = f₂ ⟨(y : Ω), hy⟩ := by
    intro y hy
    show ((e τ) ⟨(y : Ω), hy⟩ : Ω) = (σ : Ω ≃ₐ[k] Ω) (y : Ω)
    rw [show (⟨(y : Ω), hy⟩ : ↥(E1aClean.henselOverDecomp k Ω K A)) =
        ⟨(⟨y, y.2⟩ : ↥K), E1aClean.le_henselField k Ω K A y.2⟩ from Subtype.ext rfl]
    rw [he τ ⟨y, y.2⟩]
    have h2 := AlgEquiv.restrictNormalHom_apply K (σ : Ω ≃ₐ[k] Ω) ⟨y, y.2⟩
    rw [← hστ] at h2
    exact h2
  have keyKH : ∀ (z : ↥(E1aClean.decompField k Ω A))
      (hz : (z : Ω) ∈ E1aClean.henselField k Ω K A),
      f₁ ⟨(z : Ω), hz⟩ = f₂ ⟨(z : Ω), hz⟩ := by
    intro z hz
    show ((e τ) ⟨(z : Ω), hz⟩ : Ω) = (σ : Ω ≃ₐ[k] Ω) (z : Ω)
    rw [show (⟨(z : Ω), hz⟩ : ↥(E1aClean.henselOverDecomp k Ω K A)) =
        algebraMap ↥(E1aClean.decompField k Ω A) ↥(E1aClean.henselOverDecomp k Ω K A)
          z from Subtype.ext rfl]
    rw [AlgEquiv.commutes, hσfix z]
    rfl
  have hgen : (x : Ω) ∈ IntermediateField.adjoin k
      (↑(E1aClean.decompField k Ω A) ∪ (↑K : Set Ω)) := by
    have hy : (x : Ω) ∈ E1aClean.henselField k Ω K A := x.2
    rw [E1aClean.henselField_eq_sup k Ω K A] at hy
    exact hy
  have key : ∀ z ∈ IntermediateField.adjoin k (↑(E1aClean.decompField k Ω A) ∪ (↑K : Set Ω)),
      ∀ hz : z ∈ E1aClean.henselField k Ω K A, f₁ ⟨z, hz⟩ = f₂ ⟨z, hz⟩ := by
    intro z hz0
    refine IntermediateField.adjoin_induction (p := fun z _ =>
      ∀ hz : z ∈ E1aClean.henselField k Ω K A, f₁ ⟨z, hz⟩ = f₂ ⟨z, hz⟩)
      (mem := ?_) (algebraMap := ?_) (add := ?_) (inv := ?_) (mul := ?_) (h := hz0)
    · intro z hzg hz
      rcases hzg with hzD | hzK
      · exact keyKH ⟨z, hzD⟩ hz
      · exact keyK ⟨z, hzK⟩ hz
    · intro c hz
      have hmemK : algebraMap k Ω c ∈ (K : Set Ω) := K.algebraMap_mem c
      rw [show (⟨algebraMap k Ω c, hz⟩ : ↥(E1aClean.henselOverDecomp k Ω K A)) =
          ⟨(⟨algebraMap k Ω c, hmemK⟩ : ↥K), E1aClean.le_henselField k Ω K A hmemK⟩
        from Subtype.ext rfl]
      exact keyK ⟨algebraMap k Ω c, hmemK⟩ (E1aClean.le_henselField k Ω K A hmemK)
    · intro a b ha hb iha ihb hz
      rw [show (⟨a + b, hz⟩ : ↥(E1aClean.henselOverDecomp k Ω K A)) =
        ⟨a, hS_le ha⟩ + ⟨b, hS_le hb⟩ from Subtype.ext rfl]
      simp only [map_add]
      rw [iha (hS_le ha), ihb (hS_le hb)]
    · intro a ha iha hz
      rw [show (⟨a⁻¹, hz⟩ : ↥(E1aClean.henselOverDecomp k Ω K A)) =
        (⟨a, hS_le ha⟩)⁻¹ from Subtype.ext rfl]
      simp only [map_inv₀]
      rw [iha (hS_le ha)]
    · intro a b ha hb iha ihb hz
      rw [show (⟨a * b, hz⟩ : ↥(E1aClean.henselOverDecomp k Ω K A)) =
        ⟨a, hS_le ha⟩ * ⟨b, hS_le hb⟩ from Subtype.ext rfl]
      simp only [map_mul]
      rw [iha (hS_le ha), ihb (hS_le hb)]
  exact key (x : Ω) hgen x.2


/-- The canonical inclusion `K ↪ K^h` as a ring homomorphism. -/
noncomputable def khIncl (A : ValuationSubring Ω) :
    ↥K →+* ↥(E1aClean.henselOverDecomp k Ω K A) :=
  { toFun := fun x => ⟨(x : Ω), E1aClean.le_henselField k Ω K A x.2⟩
    map_one' := Subtype.ext rfl
    map_mul' := fun a b => Subtype.ext rfl
    map_zero' := Subtype.ext rfl
    map_add' := fun a b => Subtype.ext rfl }

@[simp] theorem khIncl_apply (A : ValuationSubring Ω) (x : ↥K) :
    ((khIncl (k := k) (Ω := Ω) (K := K) A x : ↥(E1aClean.henselOverDecomp k Ω K A)) : Ω)
      = (x : Ω) := rfl

/-- **The `D_q`-representation `(K^h)ˣ`** of the henselisation `K^h = Ω^{D_A ⊓ G_K}`, where
`D_q = decompK q` acts through the group isomorphism `e : D_q ≃* Gal(K^h/k^h)`, i.e. through the
*global* action of `D_A` on `K^h ⊆ Ω`. -/
abbrev khUnits (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (E1aClean.henselOverDecomp k Ω K A ≃ₐ[E1aClean.decompField k Ω A]
        E1aClean.henselOverDecomp k Ω K A)) :
    Rep.{0} SSGRoute.PTExt.Coeff
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
  Rep.res e.toMonoidHom (SSGRoute.PTExt.unitsK ↥(E1aClean.decompField k Ω A)
    ↥(E1aClean.henselOverDecomp k Ω K A))

theorem khUnits_rho_ofMul (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (E1aClean.henselOverDecomp k Ω K A ≃ₐ[E1aClean.decompField k Ω A]
        E1aClean.henselOverDecomp k Ω K A))
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (u : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ) :
    (khUnits (k := k) (Ω := Ω) (K := K) A q e).ρ τ (Additive.ofMul u)
      = Additive.ofMul (e τ • u) := rfl

theorem khUnits_rho_ofMul_coe (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (E1aClean.henselOverDecomp k Ω K A ≃ₐ[E1aClean.decompField k Ω A]
        E1aClean.henselOverDecomp k Ω K A))
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (u : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ) :
    ((Additive.toMul ((khUnits (k := k) (Ω := Ω) (K := K) A q e).ρ τ (Additive.ofMul u))
        : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ) :
        ↥(E1aClean.henselOverDecomp k Ω K A))
      = (e τ) ((Additive.toMul (Additive.ofMul u) :
          (↥(E1aClean.henselOverDecomp k Ω K A))ˣ) :
          ↥(E1aClean.henselOverDecomp k Ω K A)) := by
  rw [khUnits_rho_ofMul]
  rfl

/-- The intertwining identity for `khIota` at the level of units. -/
theorem khIota_intertwining_units (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (E1aClean.henselOverDecomp k Ω K A ≃ₐ[E1aClean.decompField k Ω A]
        E1aClean.henselOverDecomp k Ω K A))
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : K),
      ((e τ) ⟨(x : Ω), E1aClean.le_henselField k Ω K A x.2⟩ : Ω) = ((τ : K ≃ₐ[k] K) x : Ω))
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (u : (↥K)ˣ) :
    Units.map (khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom ((τ : K ≃ₐ[k] K) • u)
      = (e τ) • (Units.map (khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom u) := by
  apply Units.ext
  apply Subtype.ext
  show (((τ : K ≃ₐ[k] K) (u : ↥K) : ↥K) : Ω)
    = ((e τ) ⟨((u : ↥K) : Ω), E1aClean.le_henselField k Ω K A (u : ↥K).2⟩ : Ω)
  rw [he τ (u : ↥K)]

/-- **The `D_q`-equivariant inclusion** `Kˣ ↪ (K^h)ˣ`, with `D_q` acting on `Kˣ` through
`D_q ≤ Gal(K/k)` and on `(K^h)ˣ` through `e : D_q ≃* Gal(K^h/k^h)`. -/
noncomputable def khIota (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (E1aClean.henselOverDecomp k Ω K A ≃ₐ[E1aClean.decompField k Ω A]
        E1aClean.henselOverDecomp k Ω K A))
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : K),
      ((e τ) ⟨(x : Ω), E1aClean.le_henselField k Ω K A x.2⟩ : Ω) = ((τ : K ≃ₐ[k] K) x : Ω)) :
    Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
        (SSGRoute.PTExt.unitsK k K) ⟶ khUnits (k := k) (Ω := Ω) (K := K) A q e :=
  Rep.ofHom
    { toFun := ⇑(Units.map (khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom).toAdditive
      map_add' := fun a b =>
        map_add (Units.map (khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom).toAdditive a b
      map_smul' := fun n a => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul
          (Units.map (khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom).toAdditive z a
      isIntertwining' := fun τ => by
        apply LinearMap.ext
        intro x
        obtain ⟨u, hu⟩ : ∃ u : (↥K)ˣ, x = Additive.ofMul u :=
          ⟨Additive.toMul x, by simp⟩
        rw [hu]
        change Additive.ofMul (Units.map (khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom
            ((τ : K ≃ₐ[k] K) • u))
          = (khUnits (k := k) (Ω := Ω) (K := K) A q e).ρ τ
              (Additive.ofMul (Units.map (khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom u))
        rw [khUnits_rho_ofMul]
        exact congrArg Additive.ofMul
          (khIota_intertwining_units (k := k) (Ω := Ω) (K := K) A q e he τ u) }

theorem khIota_apply (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (E1aClean.henselOverDecomp k Ω K A ≃ₐ[E1aClean.decompField k Ω A]
        E1aClean.henselOverDecomp k Ω K A))
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : K),
      ((e τ) ⟨(x : Ω), E1aClean.le_henselField k Ω K A x.2⟩ : Ω) = ((τ : K ≃ₐ[k] K) x : Ω))
    (u : (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
      (SSGRoute.PTExt.unitsK k K)).V) :
    (Rep.Hom.hom (khIota (k := k) (Ω := Ω) (K := K) A q e he)) u
      = Additive.ofMul (Units.map (khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom
          (Additive.toMul u)) :=
  rfl

/-- **The coefficient change `(K^h)ˣ ⟶ K_qˣ`** at the finite place `q`, as a morphism of
`D_q`-representations; its equivariance is `E1aClean.henselEmb_equivariant`. -/
noncomputable def khTheta (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (E1aClean.henselOverDecomp k Ω K A ≃ₐ[E1aClean.decompField k Ω A]
        E1aClean.henselOverDecomp k Ω K A))
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : K),
      ((e τ) ⟨(x : Ω), E1aClean.le_henselField k Ω K A x.2⟩ : Ω) = ((τ : K ≃ₐ[k] K) x : Ω))
    (φ : ↥(E1aClean.henselOverDecomp k Ω K A) →+* (q.adicCompletion ↥K))
    (hφ : ∀ x : ↥K, φ ⟨(x : Ω), E1aClean.le_henselField k Ω K A x.2⟩ =
      algebraMap ↥K (q.adicCompletion ↥K) x)
    (hfix : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
      (x : ↥(E1aClean.decompField k Ω A)),
      NK.HassePrinciple.localAutHom (K := k) (L := ↥K) (NK.GlobalCFT.Place.ofFinite q) τ
        (φ ⟨(x : Ω), E1aClean.decompField_le_henselField k Ω K A x.2⟩)
      = φ ⟨(x : Ω), E1aClean.decompField_le_henselField k Ω K A x.2⟩) :
    khUnits (k := k) (Ω := Ω) (K := K) A q e ⟶
      SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q) :=
  Rep.ofHom
    { toFun := ⇑(Units.map φ.toMonoidHom).toAdditive
      map_add' := fun a b => map_add (Units.map φ.toMonoidHom).toAdditive a b
      map_smul' := fun n a => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul (Units.map φ.toMonoidHom).toAdditive z a
      isIntertwining' := fun τ => by
        apply LinearMap.ext
        intro x
        obtain ⟨u, hu⟩ : ∃ u : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ,
            x = Additive.ofMul u :=
          ⟨Additive.toMul x, by simp⟩
        rw [hu]
        change Additive.ofMul (Units.map φ.toMonoidHom (e τ • u))
          = (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)).ρ τ
              (Additive.ofMul (Units.map φ.toMonoidHom u))
        rw [show (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)).ρ τ
            (Additive.ofMul (Units.map φ.toMonoidHom u))
            = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
                (NK.GlobalCFT.Place.ofFinite q) τ (Units.map φ.toMonoidHom u)) from rfl]
        congr 1
        apply Units.ext
        simp only [Units.coe_map, Units.coe_smul, AlgEquiv.smul_def]
        exact E1aClean.henselEmb_equivariant k Ω K A hA q hAq e he φ hφ hfix τ u }

theorem khTheta_apply (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (E1aClean.henselOverDecomp k Ω K A ≃ₐ[E1aClean.decompField k Ω A]
        E1aClean.henselOverDecomp k Ω K A))
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : K),
      ((e τ) ⟨(x : Ω), E1aClean.le_henselField k Ω K A x.2⟩ : Ω) = ((τ : K ≃ₐ[k] K) x : Ω))
    (φ : ↥(E1aClean.henselOverDecomp k Ω K A) →+* (q.adicCompletion ↥K))
    (hφ : ∀ x : ↥K, φ ⟨(x : Ω), E1aClean.le_henselField k Ω K A x.2⟩ =
      algebraMap ↥K (q.adicCompletion ↥K) x)
    (hfix : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
      (x : ↥(E1aClean.decompField k Ω A)),
      NK.HassePrinciple.localAutHom (K := k) (L := ↥K) (NK.GlobalCFT.Place.ofFinite q) τ
        (φ ⟨(x : Ω), E1aClean.decompField_le_henselField k Ω K A x.2⟩)
      = φ ⟨(x : Ω), E1aClean.decompField_le_henselField k Ω K A x.2⟩)
    (a : (khUnits (k := k) (Ω := Ω) (K := K) A q e).V) :
    (Rep.Hom.hom (khTheta (k := k) (Ω := Ω) (K := K) A hA q hAq e he φ hφ hfix)) a
      = Additive.ofMul (Units.map φ.toMonoidHom (Additive.toMul a)) := rfl

/-- **`p •` is bijective on `Additive L ⧸ S`** when `S` is the range of a group hom whose cokernel
is uniquely `p`-divisible (a version of `E1aClean.nsmul_bijective_quotient_of_uniqueDivisible` with
the subgroup left as a *variable*, so that it can be instantiated at a subgroup only *equal* to the
range of the units-coefficient map). -/
theorem bijective_nsmul_quotient_of_eq_range {E L : Type*} [Group E] [CommGroup L] (f : E →* L)
    (p : ℕ) (hp : 0 < p) (S : AddSubgroup (Additive L))
    (hS : S = (MonoidHom.range f).toAddSubgroup)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ z : L, ∃ (w : L) (u : E), z = f u * w ^ n)
    (hpur : ∀ n : ℕ, 0 < n → ∀ (z : L) (u : E), z ^ n = f u → ∃ u' : E, z = f u') :
    Function.Bijective (fun z : Additive L ⧸ S => p • z) := by
  have aux1 : ∀ a b : L, (QuotientAddGroup.mk (Additive.ofMul a) : Additive L ⧸ S)
      = QuotientAddGroup.mk (Additive.ofMul b) ↔ a⁻¹ * b ∈ MonoidHom.range f := by
    intro a b
    rw [QuotientAddGroup.eq, hS, Additive.mem_toAddSubgroup]
    constructor <;> intro h <;> simpa using h
  have aux2 : ∀ (n : ℕ) (A : Additive L),
      n • (QuotientAddGroup.mk A : Additive L ⧸ S)
        = QuotientAddGroup.mk (Additive.ofMul (A.toMul ^ n)) := by
    intro n A
    rw [← QuotientAddGroup.mk_nsmul]
    rfl
  refine ⟨?_, ?_⟩
  · intro x
    refine QuotientAddGroup.induction_on x ?_
    intro A y
    refine QuotientAddGroup.induction_on y ?_
    intro B h
    simp only [] at h
    rw [aux2 p A, aux2 p B] at h
    have hmem : (A.toMul ^ p)⁻¹ * B.toMul ^ p ∈ MonoidHom.range f :=
      (aux1 (A.toMul ^ p) (B.toMul ^ p)).mp h
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hmem
    have hkey : (A.toMul⁻¹ * B.toMul) ^ p = f u := by
      rw [mul_pow, inv_pow, ← hu]
    obtain ⟨u', hu'⟩ := hpur p hp (A.toMul⁻¹ * B.toMul) u hkey
    exact (aux1 A.toMul B.toMul).mpr
      (by rw [hu']; exact MonoidHom.mem_range.mpr ⟨u', rfl⟩)
  · intro z
    refine QuotientAddGroup.induction_on z ?_
    intro A
    obtain ⟨w, u, hw⟩ := hdiv p hp A.toMul
    refine ⟨QuotientAddGroup.mk (Additive.ofMul w), ?_⟩
    show p • QuotientAddGroup.mk (Additive.ofMul w) = QuotientAddGroup.mk A
    rw [aux2 p (Additive.ofMul w)]
    simp only [toMul_ofMul]
    have key : (w ^ p)⁻¹ * A.toMul = f u := by
      rw [hw, mul_comm (f u) (w ^ p), inv_mul_cancel_left]
    exact (aux1 (w ^ p) A.toMul).mpr
      (by rw [key]; exact MonoidHom.mem_range.mpr ⟨u, rfl⟩)

theorem exists_khLift_of_extToIdeles_eq_zero
    {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    [Module.Finite ℤ ↥(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))]
    (hN : ∀ x : N.V, (p : SSGRoute.PTExt.Coeff) • x = 0)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hns : ¬ (SSGRoute.decomp k A ≤ (SSGRoute.res k K).ker))
    (w : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
      (SSGRoute.PTExt.unitsK k K) 0)
    (hz : SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) w)) = 0) :
    ∃ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (hAq : ∀ x : NumberField.RingOfIntegers K,
        x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
      (ξ : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K)
            (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).V
          → (↥(Work.SSGRoute.E1aClean.henselField k Ω K A))ˣ),
      (∀ a b : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).V,
        ξ (a + b) = ξ a * ξ b) ∧
      (∀ (δ : ↥(SSGRoute.decomp k A))
        (v : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).V),
        ((ξ ((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K)
              (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).ρ
              (SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω)) v)
            : ↥(Work.SSGRoute.E1aClean.henselField k Ω K A)) : Ω)
          = (δ : Ω ≃ₐ[k] Ω)
              (((ξ v : ↥(Work.SSGRoute.E1aClean.henselField k Ω K A)) : Ω))) ∧
      (∀ x : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).V,
        ((ξ (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K)
              (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) x)
            : ↥(Work.SSGRoute.E1aClean.henselField k Ω K A)) : Ω)
          = (((Additive.toMul
                (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ w) x) : (↥K)ˣ) : ↥K) : Ω)) := by
  classical
  obtain ⟨q, hAq⟩ := Work.SSGRoute.ExtChain.exists_primeUnder_hAq K A hA
  haveI hgalΩ : IsGalois k Ω := inferInstance
  haveI hssepK : IsSepClosure ↥K Ω :=
    ⟨(inferInstance : IsSepClosure k Ω).sep_closed, inferInstance⟩
  have hAqK : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q :=
    Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq
  letI : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion q A hAqK).toAlgebra
  have halgK : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A hAqK z := fun z => rfl
  obtain ⟨e, he⟩ := E1aClean.decompField_hensel_groupIso (k := k) (Ω := Ω) K A hA q hAq
  let φ : ↥(E1aClean.henselOverDecomp k Ω K A) →+* (q.adicCompletion ↥K) :=
    E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halgK
  have hlink2 : ∀ c : ↥K,
      NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A (algebraMap ↥K Ω c) =
        algebraMap (q.adicCompletion ↥K)
          ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)
          (algebraMap ↥K (q.adicCompletion ↥K) c) := by
    intro c
    apply Subtype.ext
    rw [NK.NeukirchUchida.coe_coInAdjoin]
    rw [show ((algebraMap (q.adicCompletion ↥K)
          ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)
          (algebraMap ↥K (q.adicCompletion ↥K) c) :
            ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)) :
          NK.NeukirchUchida.placeCompletion A) =
        algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)
          (algebraMap ↥K (q.adicCompletion ↥K) c) from rfl]
    rw [halgK, NK.NeukirchUchida.adicCompletionToPlaceCompletion_algebraMap]
  have hφK : ∀ x : ↥K, φ ⟨(x : Ω), E1aClean.le_henselField k Ω K A x.2⟩ =
      algebraMap ↥K (q.adicCompletion ↥K) x := by
    intro x
    refine RingHom.injective (algebraMap (q.adicCompletion ↥K)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)) ?_
    show algebraMap (q.adicCompletion ↥K)
        ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)
        (E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halgK
          ⟨(x : Ω), E1aClean.le_henselField k Ω K A x.2⟩)
      = algebraMap (q.adicCompletion ↥K)
          ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)
          (algebraMap ↥K (q.adicCompletion ↥K) x)
    rw [E1aClean.decompFieldHenselEmb_spec k Ω K A hA q hAq halgK
      ⟨(x : Ω), E1aClean.le_henselField k Ω K A x.2⟩]
    exact hlink2 x
  have hφinj : Function.Injective φ := RingHom.injective φ
  have hfix := E1aClean.decompFieldHenselEmb_fixes_decomp k Ω K A hA q hAq halgK
  have hrelalg : ∀ z : q.adicCompletion ↥K,
      (∃ r : Polynomial ↥(E1aClean.henselOverDecomp k Ω K A),
        r ≠ 0 ∧ Polynomial.eval₂ φ z r = 0) →
      ∃ x : ↥(E1aClean.henselOverDecomp k Ω K A), φ x = z :=
    E1aClean.decompFieldHenselEmb_relAlgClosed k Ω K A hA q hAq halgK
  have hquot : Function.Bijective (fun z : Additive (q.adicCompletion ↥K)ˣ ⧸
      (MonoidHom.range (Units.map φ.toMonoidHom)).toAddSubgroup => p • z) :=
    E1aClean.unitsQuotient_pow_bijective_fixed k Ω K A hA q φ hφinj hrelalg p
  -- ## the coefficient change and the short exact sequence `0 → (K^h)ˣ → K_qˣ → Q → 0`
  let θ := khTheta (k := k) (Ω := Ω) (K := K) A hA q hAq e he φ hφK hfix
  let M : Rep.{0} SSGRoute.PTExt.Coeff
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
    SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)
  let W : Submodule SSGRoute.PTExt.Coeff M.V := LinearMap.range (Rep.Hom.hom θ).toLinearMap
  have hWmem : ∀ y : M.V, y ∈ W ↔ ∃ a : (khUnits (k := k) (Ω := Ω) (K := K) A q e).V,
      (Rep.Hom.hom θ) a = y := fun y => Iff.rfl
  have hW : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))),
      W ≤ Submodule.comap (M.ρ τ) W := by
    intro τ y hy
    rw [Submodule.mem_comap]
    rw [hWmem] at hy ⊢
    obtain ⟨a, ha⟩ := hy
    refine ⟨(khUnits (k := k) (Ω := Ω) (K := K) A q e).ρ τ a, ?_⟩
    rw [← ha]
    exact Representation.IntertwiningMap.isIntertwining (f := Rep.Hom.hom θ) (g := τ) (v := a)
  have hzero : θ ≫ Work.CohomologicallyTrivial.quotRepProj M W hW = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    show (Submodule.mkQ W) ((Rep.Hom.hom θ) v) = 0
    exact (Submodule.Quotient.mk_eq_zero (p := W)).mpr ⟨v, rfl⟩
  have hexact : (ShortComplex.mk θ (Work.CohomologicallyTrivial.quotRepProj M W hW) hzero).Exact :=
    quotRepProj_exact_aux W hW θ hzero (fun y hy => (hWmem y).mp hy)
  haveI hmonoθ : Mono θ := by
    rw [Rep.mono_iff_injective]
    intro a b hab
    have h3 : (Rep.Hom.hom θ) a = (Rep.Hom.hom θ) b := hab
    have h4 := khTheta_apply (k := k) (Ω := Ω) (K := K) A hA q hAq e he φ hφK hfix a
    have h5 := khTheta_apply (k := k) (Ω := Ω) (K := K) A hA q hAq e he φ hφK hfix b
    rw [h4, h5] at h3
    have h3' : Units.map φ.toMonoidHom (Additive.toMul a)
        = Units.map φ.toMonoidHom (Additive.toMul b) := by
      simpa using congrArg Additive.toMul h3
    have h6 : φ ((Additive.toMul a : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ) :
          ↥(E1aClean.henselOverDecomp k Ω K A))
        = φ ((Additive.toMul b : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ) :
          ↥(E1aClean.henselOverDecomp k Ω K A)) := by
      have hh := congrArg (fun w : (q.adicCompletion ↥K)ˣ => (w : q.adicCompletion ↥K)) h3'
      simpa [Units.coe_map] using hh
    have h7 : (Additive.toMul a : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ)
        = (Additive.toMul b : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ) :=
      Units.ext (hφinj h6)
    have h8 : Additive.ofMul (Additive.toMul a) = Additive.ofMul (Additive.toMul b) :=
      congrArg Additive.ofMul h7
    simpa using h8
  haveI hepi : Epi (Work.CohomologicallyTrivial.quotRepProj M W hW) := by
    rw [Rep.epi_iff_surjective]
    intro z
    obtain ⟨y, hy⟩ := Submodule.mkQ_surjective W z
    exact ⟨y, hy⟩
  let S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) :=
    ShortComplex.mk θ (Work.CohomologicallyTrivial.quotRepProj M W hW) hzero
  have hS : S.ShortExact := ShortComplex.ShortExact.mk' hexact inferInstance inferInstance
  have hmem_range : ∀ y : Additive ((NK.GlobalCFT.Place.localField K
        (NK.GlobalCFT.Place.ofFinite q))ˣ),
      y ∈ (MonoidHom.range (Units.map φ.toMonoidHom)).toAddSubgroup ↔
        ∃ u : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ,
          Additive.toMul y = Units.map φ.toMonoidHom u := by
    intro y
    rw [Additive.mem_toAddSubgroup]
    constructor
    · intro hy
      obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hy
      exact ⟨u, hu.symm⟩
    · rintro ⟨u, hu⟩
      exact MonoidHom.mem_range.mpr ⟨u, hu.symm⟩
  have hWS : W.toAddSubgroup = (MonoidHom.range (Units.map φ.toMonoidHom)).toAddSubgroup := by
    apply AddSubgroup.ext
    intro y
    rw [hmem_range y]
    constructor
    · intro hy
      rw [Submodule.mem_toAddSubgroup, hWmem] at hy
      obtain ⟨a, ha⟩ := hy
      refine ⟨(Additive.toMul a : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ), ?_⟩
      rw [← ha]
      exact congrArg Additive.toMul
        (khTheta_apply (k := k) (Ω := Ω) (K := K) A hA q hAq e he φ hφK hfix a)
    · rintro ⟨u, hu⟩
      rw [Submodule.mem_toAddSubgroup, hWmem]
      refine ⟨Additive.ofMul u, ?_⟩
      have h : (Rep.Hom.hom θ) (Additive.ofMul u)
          = Additive.ofMul (Units.map φ.toMonoidHom (Additive.toMul (Additive.ofMul u))) :=
        khTheta_apply (k := k) (Ω := Ω) (K := K) A hA q hAq e he φ hφK hfix (Additive.ofMul u)
      rw [show Additive.toMul (Additive.ofMul u) = u from rfl] at h
      rw [← hu] at h
      exact h
  have hUD := E1aClean.completion_quotient_uniqueDivisible k Ω K A hA q φ hφinj hrelalg
  have hQ : Function.Bijective (fun z : S.X₃.V => p • z) := by
    change Function.Bijective (fun z : M.V ⧸ W.toAddSubgroup => p • z)
    exact bijective_nsmul_quotient_of_eq_range (Units.map φ.toMonoidHom) p
      (Fact.out : p.Prime).pos W.toAddSubgroup hWS hUD.1 hUD.2
  -- ## the engine: the coefficient push `(K^h)ˣ → K_qˣ` is injective on `Ext¹_{D_q}(res R, ·)`
  haveI hfin : Fintype ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
    Fintype.ofFinite _
  let F : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ⥤
      Rep.{0} SSGRoute.PTExt.Coeff
        ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
    Rep.resFunctor (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
  haveI hprojF : F.PreservesProjectiveObjects := inferInstance
  -- ## the syzygy `R = ker (freeCover N)`
  let R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) := CategoryTheory.Limits.kernel (freeCover N)
  let w0 : E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) R ⟶ SSGRoute.PTExt.unitsK k K :=
    CategoryTheory.Abelian.Ext.addEquiv₀ w
  have hw0 : w = CategoryTheory.Abelian.Ext.mk₀ w0 :=
    (CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply w).symm
  have hw0' : CategoryTheory.Abelian.Ext.addEquiv₀ w = w0 := rfl
  rw [hw0] at hz
  have hstep1 : (SSGRoute.PTExt.extRes
        (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
        (E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) R (CategoryTheory.Abelian.Ext.mk₀ w0))).comp
      (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k K
        (NK.GlobalCFT.Place.ofFinite q))) (add_zero 1) = 0 := by
    refine Work.SSGRoute.ExtChain.extLoc_extToIdeles_e1aSyzShift_eq_zero_imp (k := k) (Ω := Ω)
      (K := K) N (NK.GlobalCFT.Place.ofFinite q)
      (E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) R (CategoryTheory.Abelian.Ext.mk₀ w0)) ?_
    rw [hz]
    exact SSGRoute.PTExt.extLoc_zero (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q)
  let Ym : F.obj (E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) R) ⟶
      khUnits (k := k) (Ω := Ω) (K := K) A q e :=
    F.map w0 ≫ khIota (k := k) (Ω := Ω) (K := K) A q e he
  let ζ : CategoryTheory.Abelian.Ext (F.obj R)
      (khUnits (k := k) (Ω := Ω) (K := K) A q e) 1 :=
    (SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
      (E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) R (CategoryTheory.Abelian.Ext.mk₀ w0))).comp
      (CategoryTheory.Abelian.Ext.mk₀ (khIota (k := k) (Ω := Ω) (K := K) A q e he)) (add_zero 1)
  have hSN : ((freeCoverSES N).map F).ShortExact := (freeCoverSES_shortExact N).map_of_exact F
  haveI hprojSN : Projective ((freeCoverSES N).map F).X₂ :=
    Functor.projective_obj F (freeCoverSES N).X₂
  have hNt : ∀ x : ((freeCoverSES N).map F).X₃.V, p • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul SSGRoute.PTExt.Coeff p x]
    exact hN x
  have hinj := Work.SSGRoute.ExtChain.ext1_coeffPush_injective_of_ptorsion_uniqueDivisible
    (G := ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) p
    ((freeCoverSES N).map F) hSN hNt S hS hQ
  have hcompiot : khIota (k := k) (Ω := Ω) (K := K) A q e he ≫ θ
      = NK.HassePrinciple.unitsToLocalUnits k K (NK.GlobalCFT.Place.ofFinite q) := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    obtain ⟨u, hu⟩ : ∃ u : (↥K)ˣ, x = Additive.ofMul u :=
      ⟨Additive.toMul x, by simp⟩
    rw [hu]
    show Additive.ofMul (Units.map φ.toMonoidHom
        (Units.map (khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom u))
      = Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom
          (NK.GlobalCFT.Place.ofFinite q) u)
    congr 1
    apply Units.ext
    rw [Units.coe_map, Units.coe_map]
    exact hφK u
  have hζpush : ζ.comp (CategoryTheory.Abelian.Ext.mk₀ θ) (add_zero 1) = 0 := by
    have hζdef : ζ = (SSGRoute.PTExt.extRes
        (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
        (E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) R (CategoryTheory.Abelian.Ext.mk₀ w0))).comp
        (CategoryTheory.Abelian.Ext.mk₀
          (khIota (k := k) (Ω := Ω) (K := K) A q e he)) (add_zero 1) := rfl
    rw [hζdef, CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero,
      CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, hcompiot]
    exact hstep1
  have hζ0 : ζ = 0 := by
    refine hinj ?_
    show ζ.comp (CategoryTheory.Abelian.Ext.mk₀ θ) (add_zero 1)
      = (0 : CategoryTheory.Abelian.Ext (F.obj R)
          (khUnits (k := k) (Ω := Ω) (K := K) A q e) 1).comp
        (CategoryTheory.Abelian.Ext.mk₀ θ) (add_zero 1)
    rw [hζpush, CategoryTheory.Abelian.Ext.zero_comp]
  -- ## (R3): `ζ` is the connecting class of the restricted `K`-valued datum
  have hT : ((freeCoverSES R).map F).ShortExact := (freeCoverSES_shortExact R).map_of_exact F
  haveI hprojT : Projective ((freeCoverSES R).map F).X₂ :=
    Functor.projective_obj F (freeCoverSES R).X₂
  let Yext : CategoryTheory.Abelian.Ext (F.obj (E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) R))
      (khUnits (k := k) (Ω := Ω) (K := K) A q e) 0 := CategoryTheory.Abelian.Ext.mk₀ Ym
  have hmapz : SSGRoute.PTExt.extRes
        (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
        (E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) R (CategoryTheory.Abelian.Ext.mk₀ w0))
      = hT.extClass.comp (CategoryTheory.Abelian.Ext.mk₀ (F.map w0))
          (by norm_num : 1 + 0 = 1) := by
    have hPhi : E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) R (CategoryTheory.Abelian.Ext.mk₀ w0)
        = (freeCoverSES_shortExact R).extClass.comp (CategoryTheory.Abelian.Ext.mk₀ w0)
            (by norm_num : 1 + 0 = 1) := rfl
    rw [hPhi, SSGRoute.PTExt.extRes, CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
      CategoryTheory.Abelian.Ext.mapExactFunctor_extClass (F := F) (freeCoverSES_shortExact R),
      CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
  have hPhiEY : (hT.extClass.precomp (khUnits (k := k) (Ω := Ω) (K := K) A q e)
      (by norm_num : 1 + 0 = 1)) Yext = ζ := by
    have hYdef : Yext = CategoryTheory.Abelian.Ext.mk₀ Ym := rfl
    have hζdef : ζ = (SSGRoute.PTExt.extRes
        (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
        (E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) R (CategoryTheory.Abelian.Ext.mk₀ w0))).comp
        (CategoryTheory.Abelian.Ext.mk₀
          (khIota (k := k) (Ω := Ω) (K := K) A q e he)) (add_zero 1) := rfl
    rw [hYdef, hζdef, hmapz, CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero,
      CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
    rfl
  have hker : Yext ∈ (hT.extClass.precomp (khUnits (k := k) (Ω := Ω) (K := K) A q e)
      (by norm_num : 1 + 0 = 1)).ker := by
    rw [AddMonoidHom.mem_ker]
    exact hPhiEY.trans hζ0
  rw [show (hT.extClass.precomp (khUnits (k := k) (Ω := Ω) (K := K) A q e)
      (by norm_num : 1 + 0 = 1)).ker
      = ((CategoryTheory.Abelian.Ext.mk₀ ((freeCoverSES R).map F).f).precomp
          (khUnits (k := k) (Ω := Ω) (K := K) A q e) (by norm_num : 0 + 0 = 0)).range
      from (Work.SSGRoute.ext_connecting_range_ker hT
        (khUnits (k := k) (Ω := Ω) (K := K) A q e)).2] at hker
  obtain ⟨ξ₀, hξ₀⟩ := AddMonoidHom.mem_range.mp hker
  let f : F.obj (E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R) ⟶
      khUnits (k := k) (Ω := Ω) (K := K) A q e := CategoryTheory.Abelian.Ext.addEquiv₀ ξ₀
  have hfmk : CategoryTheory.Abelian.Ext.mk₀ f = ξ₀ :=
    CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply ξ₀
  have hmorph : ((freeCoverSES R).map F).f ≫ f = Ym := by
    refine (CategoryTheory.Abelian.Ext.mk₀_bijective (X := ((freeCoverSES R).map F).X₁)
      (Y := khUnits (k := k) (Ω := Ω) (K := K) A q e)).1 ?_
    show CategoryTheory.Abelian.Ext.mk₀ (((freeCoverSES R).map F).f ≫ f) = Yext
    rw [← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, hfmk]
    exact hξ₀
  have hκapply : ∀ bas : (E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) R).V,
      f ((E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) R bas)) = Ym bas := by
    intro bas
    have h := congrArg (fun (m : ((freeCoverSES R).map F).X₁ ⟶
      khUnits (k := k) (Ω := Ω) (K := K) A q e) => (Rep.Hom.hom m) bas) hmorph
    rw [Rep.comp_apply] at h
    have hmap : (Rep.Hom.hom (((freeCoverSES R).map F).f)) bas
        = E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) R bas := rfl
    rw [hmap] at h
    exact h
  -- ## the three clauses
  refine ⟨q, hAq, fun v => Additive.toMul (f.hom v), ?_, ?_, ?_⟩
  · intro a b
    have h1 : (Additive.toMul (f.hom (a + b)) : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ)
        = (Additive.toMul (f.hom a) : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ)
          * (Additive.toMul (f.hom b) : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ) := by
      rw [map_add]
      rfl
    exact h1
  · intro δ v
    have hmem : SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω) ∈
        SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q) := by
      rw [← Work.SSGRoute.PT.e1aBetaCan_hAq_decomp_map k Ω K A hA q hAq]
      exact Subgroup.mem_map_of_mem _ δ.2
    let τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
      ⟨SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω), hmem⟩
    have hτ : (τ : K ≃ₐ[k] K) = SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω) := rfl
    let u1 : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ := (Rep.Hom.hom f) v
    have htw : (Rep.Hom.hom f)
        ((F.obj (E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R)).ρ τ v)
        = (khUnits (k := k) (Ω := Ω) (K := K) A q e).ρ τ u1 :=
      Representation.IntertwiningMap.isIntertwining (f := Rep.Hom.hom f) (g := τ) (v := v)
    let Z : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ :=
      Additive.toMul (f.hom ((E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R).ρ
        (SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω)) v))
    have hZval : Z = Additive.toMul ((khUnits (k := k) (Ω := Ω) (K := K) A q e).ρ τ u1) := by
      show Additive.toMul (f.hom ((E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R).ρ
        (SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω)) v)) = _
      rw [show (E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R).ρ
          (SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω)) v
          = (F.obj (E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R)).ρ τ v from rfl]
      exact congrArg Additive.toMul htw
    have hL : (Z : ↥(E1aClean.henselOverDecomp k Ω K A))
        = (e τ) (u1 : ↥(E1aClean.henselOverDecomp k Ω K A)) := by
      rw [hZval]
      exact khUnits_rho_ofMul_coe (k := k) (Ω := Ω) (K := K) A q e τ u1
    have hcompat := henselGroupIso_apply_eq_of_res_eq (k := k) (Ω := Ω) (K := K) A hA q hAq
      e he δ τ hτ
    show ((Z : ↥(E1aClean.henselOverDecomp k Ω K A)) : Ω)
      = (δ : Ω ≃ₐ[k] Ω)
          (((Additive.toMul (f.hom v) : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ) :
            ↥(E1aClean.henselOverDecomp k Ω K A)) : Ω)
    rw [hL]
    exact hcompat (u1 : ↥(E1aClean.henselOverDecomp k Ω K A))
  · intro x
    have hx := hκapply x
    have hYm : (Rep.Hom.hom Ym) x = (Rep.Hom.hom (khIota (k := k) (Ω := Ω) (K := K) A q e he))
        ((Rep.Hom.hom (F.map w0)) x) := by
      rw [show Ym = F.map w0 ≫ khIota (k := k) (Ω := Ω) (K := K) A q e he from rfl,
        Rep.comp_apply]
    have hFw : (Rep.Hom.hom (F.map w0)) x = (Rep.Hom.hom w0) x := rfl
    let u2 : (↥K)ˣ := (Rep.Hom.hom w0) x
    have hι : (Rep.Hom.hom (khIota (k := k) (Ω := Ω) (K := K) A q e he))
          (Additive.ofMul u2)
        = Additive.ofMul (Units.map (khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom
            (Additive.toMul (Additive.ofMul u2))) :=
      khIota_apply (k := k) (Ω := Ω) (K := K) A q e he (Additive.ofMul u2)
    have hstep : (Rep.Hom.hom Ym) x
        = Additive.ofMul (Units.map (khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom
            (Additive.toMul (Additive.ofMul u2))) := by
      rw [hYm, hFw]
      exact hι
    let Z3 : (↥(E1aClean.henselOverDecomp k Ω K A))ˣ :=
      Additive.toMul (f.hom (E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) R x))
    have hZ3val : Z3 = Units.map (khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom
        (Additive.toMul (Additive.ofMul u2)) := by
      show Additive.toMul (f.hom (E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) R x))
        = Units.map (khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom
            (Additive.toMul (Additive.ofMul u2))
      rw [show f.hom (E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) R x)
          = Additive.ofMul (Units.map (khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom
              (Additive.toMul (Additive.ofMul u2)))
          from by rw [hx]; exact hstep]
      rfl
    have hL3 : (Z3 : ↥(E1aClean.henselOverDecomp k Ω K A))
        = (khIncl (k := k) (Ω := Ω) (K := K) A u2 :
            ↥(E1aClean.henselOverDecomp k Ω K A)) := by
      rw [hZ3val]
      rfl
    have hcoe : (((khIncl (k := k) (Ω := Ω) (K := K) A u2 :
          ↥(E1aClean.henselOverDecomp k Ω K A))) : Ω) = ((u2 : ↥K) : Ω) := rfl
    show ((Z3 : ↥(E1aClean.henselOverDecomp k Ω K A)) : Ω)
      = (((Additive.toMul (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ w) x) :
          (↥K)ˣ) : ↥K) : Ω)
    rw [hL3]
    rw [show (((Additive.toMul (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ w) x) :
          (↥K)ˣ) : ↥K) : Ω) = ((u2 : ↥K) : Ω) from by
      rw [hw0']
      rfl]
    exact hcoe

end

end Work.SSGRoute.ExtChain
