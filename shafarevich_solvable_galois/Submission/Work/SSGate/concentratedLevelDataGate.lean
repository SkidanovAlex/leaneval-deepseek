import Mathlib.Computability.Reduce
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.Sha2Lib.coprime_ramificationIdx_of_inertia_eq_bot
import Submission.Work.SSGRoute.Sha2Lib.exists_cyclic_p_level_split_inert
import Submission.Work.SSGRoute.Sha2Lib.normalClosureEqTop
import Submission.Work.SSGRoute.TPatom.EL_split_inert_dictionary
import Submission.Work.SSGate.conjNormalClosure
import Submission.Work.SSGate.fixedField_ramificationIdx_eq_one
import Submission.Work.SSGate.inertia_eq_bot_of_concentrated_level
import Submission.Work.SSGate.normalClosure_inertia_le_fixingSubgroup
import Submission.Work.SSGcrux.exists_char_ker_fixingSubgroup
import Submission.Work.SSGcrux.levelDatumAux
import Submission.Work.SSGcrux.under_eq_iff_mem_concSet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGate

open scoped NumberField Pointwise
open NumberField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section GroupHelpers

variable {Γ : Type} [Group Γ]

/-- The normalised transversal `sect H` is unchanged when the argument is multiplied on the right
by an element of `H` (for `H` normal). -/
theorem gate_sect_mul_of_mem (H : Subgroup Γ) [hHN : H.Normal] {x γ : Γ} (hγ : γ ∈ H) :
    Work.SSGRoute.TatePoitouRoute.sect H (x * γ) = Work.SSGRoute.TatePoitouRoute.sect H x := by
  have h : x * γ * x⁻¹ ∈ H := hHN.conj_mem γ hγ x
  have h1 := Work.SSGRoute.TatePoitouRoute.sect_const H (⟨x * γ * x⁻¹, h⟩ : ↥H) x
  rw [show (⟨x * γ * x⁻¹, h⟩ : ↥H) * x = x * γ from by rw [Subgroup.coe_mk]; group] at h1
  exact h1

/-- **The Shapiro transition function at an element of `H`.**  For `γ ∈ H` the coefficient of
`cfunc H x γ` is the conjugate `sect H x * γ * (sect H x)⁻¹`. -/
theorem gate_coe_cfunc_mem (H : Subgroup Γ) [hHN : H.Normal] {x γ : Γ} (hγ : γ ∈ H) :
    ((Work.SSGRoute.TatePoitouRoute.cfunc H x γ : ↥H) : Γ)
      = Work.SSGRoute.TatePoitouRoute.sect H x * γ * (Work.SSGRoute.TatePoitouRoute.sect H x)⁻¹ := by
  rw [Work.SSGRoute.TatePoitouRoute.coe_cfunc, gate_sect_mul_of_mem H hγ]

/-- **Group-theoretic core of the inertia clause.**  If every conjugate `g * i * g⁻¹` of every
element `i ∈ s` lies in a subgroup `S`, then the whole normal closure of `s` lies in `S`. -/
theorem gate_normalClosure_le_of_conj {G : Type} [Group G] (s : Set G) (S : Subgroup G)
    (h : ∀ (g : G) {i : G}, i ∈ s → g * i * g⁻¹ ∈ S) :
    Subgroup.normalClosure s ≤ S := by
  let T : Subgroup G :=
    { carrier := {x | ∀ g : G, g * x * g⁻¹ ∈ S}
      one_mem' := by intro g; simpa using S.one_mem
      mul_mem' := by
        intro x y hx hy g
        have h1 : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        rw [h1]; exact S.mul_mem (hx g) (hy g)
      inv_mem' := by
        intro x hx g
        have h1 : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
        rw [h1]; exact S.inv_mem (hx g) }
  have hTN : T.Normal := by
    refine ⟨fun x hx g => ?_⟩
    intro g'
    have h1 : g' * (g * x * g⁻¹) * g'⁻¹ = (g' * g) * x * (g' * g)⁻¹ := by group
    rw [h1]; exact hx (g' * g)
  have hsT : s ⊆ (T : Set G) := fun i hi g => h g hi
  have h1 : Subgroup.normalClosure s ≤ T := Subgroup.normalClosure_le_normal hsT
  intro x hx
  simpa using h1 hx 1

end GroupHelpers

theorem concentratedLevelDataGate (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ)
    (γ : K ≃ₐ[k] K) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (hcop : Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p)
      (d : ↥L ≃ₐ[k] ↥L) (f : ℕ)
      (hdH : d ^ f ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L))
      (y : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)) →* Multiplicative (ZMod p)),
      d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
      0 < f ∧
      (∀ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q'),
        ∃ m : ℕ, δ⁻¹ * d ^ m ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L)) ∧
      (∀ m : ℕ, 0 < m → m < f → d ^ m ∉ N.comap (SSGRoute.PTExt.galRes k K ↥L)) ∧
      (∀ x : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)),
        (x : ↥L ≃ₐ[k] ↥L) ∈
          Subgroup.normalClosure {σ : ↥L ≃ₐ[k] ↥L | SSGRoute.PTExt.IsInertiaAt q' σ} →
        y x = 1) ∧
      (∀ x : ↥L ≃ₐ[k] ↥L,
        y (Work.SSGRoute.TatePoitouRoute.cfunc (N.comap (SSGRoute.PTExt.galRes k K ↥L)) x
            (⟨d ^ f, hdH⟩ : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)))) = 1 ↔
          SSGRoute.PTExt.galRes k K ↥L x ∉ Work.SSGRoute.TPatom.concSet k K w N γ) := by
  classical
  -- ## Step 0: the fixed field `K₁ = K^N`, the primes `l = q ∩ k`, `u₀ = (γ q) ∩ K₁`
  let K1 : IntermediateField k K := IntermediateField.fixedField N
  let l : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    ⟨q.asIdeal.under (NumberField.RingOfIntegers k), inferInstance,
      Ideal.under_ne_bot _ q.ne_bot⟩
  have hq_l : q.asIdeal.LiesOver l.asIdeal := Ideal.over_under q.asIdeal
  let γq : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    NK.GlobalCFT.Place.smulHeightOneSpectrum γ q
  have hγq_l : γq.asIdeal.LiesOver l.asIdeal := by
    have h : γq.asIdeal = γ • q.asIdeal := rfl
    rw [h]; infer_instance
  let u₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1) :=
    ⟨γq.asIdeal.under (NumberField.RingOfIntegers ↥K1), inferInstance,
      Ideal.under_ne_bot _ γq.ne_bot⟩
  have hu₀_l : u₀.asIdeal.LiesOver l.asIdeal := by
    haveI : γq.asIdeal.LiesOver u₀.asIdeal := Ideal.over_under γq.asIdeal
    exact Ideal.LiesOver.tower_bot γq.asIdeal u₀.asIdeal l.asIdeal
  have hpu₀ : ((p : NumberField.RingOfIntegers ↥K1) ∉ u₀.asIdeal) := by
    intro hmem
    have h1 : ((p : NumberField.RingOfIntegers k)) ∈ l.asIdeal := by
      have h2 := (Ideal.mem_of_liesOver (A := NumberField.RingOfIntegers k)
        (B := NumberField.RingOfIntegers ↥K1) (p := l.asIdeal) (P := u₀.asIdeal)
        (x := (p : NumberField.RingOfIntegers k)))
      rw [map_natCast] at h2
      exact h2.mpr hmem
    have h3 : ((p : NumberField.RingOfIntegers K)) ∈ q.asIdeal := by
      rw [show l.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers k) from rfl] at h1
      rw [Ideal.mem_under] at h1
      rwa [map_natCast] at h1
    exact hpq h3
  -- ## Step 1: the Grünwald–Wang concentrated extension `E/K₁`
  let S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1)) :=
    (NK.GlobalCFT.Place.primesOverFinite l).erase u₀
  have hqS : u₀ ∉ S := by simp [S]
  obtain ⟨E, hnfE, hfdE, hgalE, hrankE, hsplitE, hinertE⟩ :=
    Work.SSGRoute.Sha2Lib.exists_cyclic_p_level_split_inert p ↥K1 Ω S u₀ hqS hpu₀
  -- ## Step 2: the level `L = normalClosure k (K ⊔ E)` and its instances
  let Kf : IntermediateField k Ω := (IsScalarTower.toAlgHom k K Ω).fieldRange
  let E' : IntermediateField k Ω := E.restrictScalars k
  let MM : IntermediateField k Ω := Kf ⊔ E'
  let Nc : IntermediateField k Ω := IntermediateField.normalClosure k ↥MM Ω
  have hKfM : Kf ≤ MM := le_sup_left
  have hMleN : MM ≤ Nc := IntermediateField.le_normalClosure MM
  have hKM : ∀ x : K, algebraMap K Ω x ∈ Nc := fun x =>
    hMleN (hKfM (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩))
  let L : IntermediateField K Ω := Nc.toSubfield.toIntermediateField hKM
  haveI hfdKf : FiniteDimensional k ↥Kf :=
    (AlgHom.equivFieldRange (IsScalarTower.toAlgHom k K Ω)).toLinearEquiv.finiteDimensional
  haveI hfdE' : FiniteDimensional k ↥E' := FiniteDimensional.trans k ↥K1 ↥E
  haveI hfdMM : FiniteDimensional k ↥MM := inferInstance
  haveI hAlgMM : Algebra.IsAlgebraic k ↥MM := Algebra.IsAlgebraic.of_finite k ↥MM
  haveI hNC : IsNormalClosure k ↥MM ↥Nc :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure
      (fun x => IsAlgClosed.splits ((minpoly k x).map (algebraMap k Ω)))
  haveI hNcnorm : Normal k ↥Nc := IsNormalClosure.normal (K := ↥MM)
  haveI hLnorm : Normal k ↥L := hNcnorm
  haveI hfdL : FiniteDimensional k ↥L := normalClosure.is_finiteDimensional k ↥MM Ω
  haveI hnfL : NumberField ↥L := NumberField.of_module_finite k ↥L
  haveI hsepL : Algebra.IsSeparable k ↥L := Algebra.IsSeparable.of_integral k ↥L
  haveI hgalL : IsGalois k ↥L := ⟨⟩
  haveI hfdKL : FiniteDimensional K ↥L := Module.Finite.of_restrictScalars_finite k K ↥L
  haveI hgalKL : IsGalois K ↥L := IsGalois.tower_top_of_isGalois k K ↥L
  -- ## Step 3: a place `q'` of `L` over `q`
  obtain ⟨q', hq'lies⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := ↥L) q
  have hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w := by
    rw [hwq]; exact NK.GlobalCFT.Place.liesOver_ofFinite hq'lies
  -- ## Step 4: `E` viewed inside `L` over `K₁`, and the character `y : H →* Multiplicative (ZMod p)`
  let Lk : IntermediateField k Ω := L.restrictScalars k
  let K1f : IntermediateField k Ω := K1.map (IsScalarTower.toAlgHom k K Ω)
  have hK1f_le_E' : K1f ≤ E' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map (S := K1)).mp hx
    rw [IntermediateField.mem_restrictScalars]
    exact E.algebraMap_mem ⟨y, hy⟩
  have hMM_le_L : MM ≤ Lk := fun x hx => hMleN hx
  have hE'_le_L : E' ≤ Lk := le_trans le_sup_right hMM_le_L
  haveI hSTL : IsScalarTower k ↥L Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply k K Ω, IsScalarTower.algebraMap_apply k K ↥L,
        IsScalarTower.algebraMap_apply K ↥L Ω])
  let K1L : IntermediateField k ↥L := K1.map (IsScalarTower.toAlgHom k K ↥L)
  let E0 : IntermediateField k ↥L := E'.comap (IsScalarTower.toAlgHom k ↥L Ω)
  have hK1L_le_E0 : K1L ≤ E0 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map (S := K1)).mp hx
    exact hK1f_le_E' ((IntermediateField.mem_map (S := K1)).mpr ⟨y, hy, rfl⟩)
  let EL : IntermediateField ↥K1L ↥L := IntermediateField.extendScalars hK1L_le_E0
  haveI hfdK1 : FiniteDimensional k ↥K1 :=
    Module.Finite.of_injective (IntermediateField.val K1).toLinearMap
      (IntermediateField.val K1).injective
  let eK1 : ↥K1 ≃ₐ[k] ↥K1L :=
    IntermediateField.equivMap K1 (IsScalarTower.toAlgHom k K ↥L)
  let eK1O : NumberField.RingOfIntegers ↥K1 ≃ₐ[NumberField.RingOfIntegers k]
      NumberField.RingOfIntegers ↥K1L := NumberField.RingOfIntegers.mapAlgEquiv eK1
  have hcompatK1O' : (eK1O : NumberField.RingOfIntegers ↥K1 →+*
      NumberField.RingOfIntegers ↥K1L).comp (algebraMap (NumberField.RingOfIntegers k)
        (NumberField.RingOfIntegers ↥K1)) = algebraMap (NumberField.RingOfIntegers k)
          (NumberField.RingOfIntegers ↥K1L) :=
    RingHom.ext fun c => eK1O.commutes c
  have hkeyO : ∀ x : NumberField.RingOfIntegers ↥K1,
      algebraMap (NumberField.RingOfIntegers ↥K1L) (NumberField.RingOfIntegers ↥L) (eK1O x)
        = algebraMap (NumberField.RingOfIntegers ↥K1) (NumberField.RingOfIntegers ↥L) x := by
    intro x
    apply NumberField.RingOfIntegers.coe_injective
    rw [← IsScalarTower.algebraMap_apply (R := NumberField.RingOfIntegers ↥K1L)
          (S := NumberField.RingOfIntegers ↥L) (A := ↥L) (eK1O x),
        ← IsScalarTower.algebraMap_apply (R := NumberField.RingOfIntegers ↥K1)
          (S := NumberField.RingOfIntegers ↥L) (A := ↥L) x]
    change (((eK1O x : NumberField.RingOfIntegers ↥K1L) : ↥K1L) : ↥L)
        = algebraMap K ↥L (((x : NumberField.RingOfIntegers ↥K1) : ↥K1) : K)
    rw [show ((eK1O x : NumberField.RingOfIntegers ↥K1L) : ↥K1L) = eK1 (x : ↥K1) from
      NumberField.RingOfIntegers.mapRingHom_apply (f := (eK1 : ↥K1 →+* ↥K1L)) x]
    rw [show (eK1 (x : ↥K1) : ↥L)
          = algebraMap K ↥L (((x : NumberField.RingOfIntegers ↥K1) : ↥K1) : K) from
        IntermediateField.coe_equivMap_apply (L := K1)
          (f := IsScalarTower.toAlgHom k K ↥L) (x : ↥K1)]
  haveI hfdK1L : FiniteDimensional k ↥K1L := eK1.toLinearEquiv.finiteDimensional
  haveI hnfK1L : NumberField ↥K1L := NumberField.of_module_finite k ↥K1L
  haveI hgalK1LL : IsGalois ↥K1L ↥L := inferInstance
  haveI hfinK1LL : FiniteDimensional ↥K1L ↥L := by
    haveI : IsScalarTower k ↥K1L ↥L := inferInstance
    exact Module.Finite.of_restrictScalars_finite k ↥K1L ↥L
  haveI hfdEL : FiniteDimensional ↥K1L ↥EL :=
    Module.Finite.of_injective EL.val.toLinearMap EL.val.injective
  have hELmem : ∀ (y : ↥L), y ∈ EL ↔ (y : Ω) ∈ E := by
    intro y
    rw [show y ∈ EL ↔ y ∈ E0 from (IntermediateField.mem_extendScalars (h := hK1L_le_E0))]
    rw [show y ∈ E0 ↔ (IsScalarTower.toAlgHom k ↥L Ω) y ∈ E' from Iff.rfl]
    rw [show (IsScalarTower.toAlgHom k ↥L Ω) y = (y : Ω) from rfl]
    rw [IntermediateField.mem_restrictScalars]
  let eEL : ↥E ≃ₐ[k] ↥EL :=
    { toFun := fun x => Subtype.mk
        (Subtype.mk x.1 (hE'_le_L ((IntermediateField.mem_restrictScalars (K := k) (E := E)).mpr x.2)))
        ((hELmem (Subtype.mk x.1
          (hE'_le_L ((IntermediateField.mem_restrictScalars (K := k) (E := E)).mpr x.2)))).mpr x.2)
      invFun := fun y => Subtype.mk (y.1.1) ((hELmem y.1).mp y.2)
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext (Subtype.ext rfl)
      map_mul' := fun x y => Subtype.ext (Subtype.ext rfl)
      map_add' := fun x y => Subtype.ext (Subtype.ext rfl)
      commutes' := fun c => Subtype.ext (Subtype.ext rfl) }
  have hcompatEL : ∀ (a : ↥K1) (y : ↥E), eEL (a • y) = eK1 a • eEL y := by
    intro a y
    apply Subtype.ext
    apply Subtype.ext
    simp only [Algebra.smul_def, IntermediateField.coe_mul, IntermediateField.coe_algebraMap_apply,
      map_mul]
    rw [show (↑↑(eEL (algebraMap ↥K1 ↥E a)) : Ω) = (↑((algebraMap ↥K1 ↥E) a) : Ω) from rfl]
    rw [show (↑((algebraMap ↥K1 ↥E) a) : Ω) = (algebraMap ↥K1 Ω) a from rfl]
    rw [show (↑((algebraMap ↥K1L ↥L) (eK1 a)) : Ω) = (algebraMap ↥K1L Ω) (eK1 a) from rfl]
    have hkey : (algebraMap ↥K1L Ω) (eK1 a) = (algebraMap ↥K1 Ω) a := by
      rw [show (algebraMap ↥K1L Ω) (eK1 a) = ((eK1 a : ↥K1L) : ↥L).1 from rfl]
      rw [show ((eK1 a : ↥K1L) : ↥L) = ((IsScalarTower.toAlgHom k K ↥L) a : ↥L) from by
        rw [show (eK1 a : ↥K1L) = IntermediateField.equivMap K1
          (IsScalarTower.toAlgHom k K ↥L) a from rfl, IntermediateField.coe_equivMap_apply]]
      rw [show ((IsScalarTower.toAlgHom k K ↥L) a : ↥L) = algebraMap K ↥L ((a : ↥K1) : K) from rfl]
      rw [IntermediateField.coe_algebraMap_apply]
      rw [IsScalarTower.algebraMap_apply ↥K1 K Ω a]
      rw [show (algebraMap ↥K1 K) a = ((a : ↥K1) : K) from rfl]
    rw [hkey]
  haveI hgalEL : IsGalois ↥K1L ↥EL :=
    IsGalois.of_equiv_equiv (F := ↥K1) (E := ↥E) (f := (eK1 : ↥K1 ≃+* ↥K1L)) (g := eEL) (by
      apply RingHom.ext
      intro x
      apply Subtype.ext
      apply Subtype.ext
      simp only [IntermediateField.coe_algebraMap_apply, IntermediateField.algebraMap_apply,
        IntermediateField.coe_equivMap_apply, eEL]
      rfl)
  have hrankEL : Module.finrank ↥K1L ↥EL = p := by
    rw [← hrankE]
    exact (Algebra.finrank_eq_of_equiv_equiv (eK1 : ↥K1 ≃+* ↥K1L) eEL (by
      apply RingHom.ext
      intro x
      apply Subtype.ext
      apply Subtype.ext
      simp only [IntermediateField.coe_algebraMap_apply, IntermediateField.algebraMap_apply,
        IntermediateField.coe_equivMap_apply, eEL]
      rfl)).symm
  obtain ⟨χ, hχker⟩ :=
    Work.SSGcrux.exists_char_ker_fixingSubgroup (K := ↥K1L) (L := ↥L) EL p hrankEL
  -- ## Step 5: `H = galRes⁻¹ N = Gal(L/K₁)` and the character `y : H →* Multiplicative (ZMod p)`
  have hK1fix : K1.fixingSubgroup = N := IntermediateField.fixingSubgroup_fixedField N
  have hHmem : ∀ σ : ↥L ≃ₐ[k] ↥L,
      SSGRoute.PTExt.galRes k K ↥L σ ∈ N ↔ σ ∈ K1L.fixingSubgroup := by
    intro σ
    rw [← hK1fix, IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map (S := K1)).mp hx
      show σ (algebraMap K ↥L y) = algebraMap K ↥L y
      rw [show σ (algebraMap K ↥L y) = algebraMap K ↥L (SSGRoute.PTExt.galRes k K ↥L σ y)
        from (AlgEquiv.restrictNormal_commutes σ K y).symm]
      rw [h y hy]
    · intro h y hy
      have hx : (IsScalarTower.toAlgHom k K ↥L) y ∈ K1L :=
        (IntermediateField.mem_map (S := K1)).mpr ⟨y, hy, rfl⟩
      have hfix := h _ hx
      rw [show (IsScalarTower.toAlgHom k K ↥L) y = algebraMap K ↥L y from rfl] at hfix
      rw [show σ (algebraMap K ↥L y) = algebraMap K ↥L (SSGRoute.PTExt.galRes k K ↥L σ y)
        from (AlgEquiv.restrictNormal_commutes σ K y).symm] at hfix
      exact (algebraMap K ↥L).injective hfix
  have hH : N.comap (SSGRoute.PTExt.galRes k K ↥L) = K1L.fixingSubgroup := by
    ext σ
    rw [Subgroup.mem_comap]
    exact hHmem σ
  let y : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)) →* Multiplicative (ZMod p) :=
    χ.comp (MulEquiv.toMonoidHom
      ((MulEquiv.subgroupCongr hH).trans (IntermediateField.fixingSubgroupEquiv K1L)))
  have hy_iff : ∀ (σ : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L))),
      y σ = 1 ↔ ∀ x : ↥L, x ∈ EL → (σ : ↥L ≃ₐ[k] ↥L) x = x := by
    intro σ
    have hcoe : (((MulEquiv.subgroupCongr hH).trans
        (IntermediateField.fixingSubgroupEquiv K1L)) σ : ↥L → ↥L)
          = ⇑(σ : ↥L ≃ₐ[k] ↥L) := rfl
    rw [show y σ = χ (((MulEquiv.subgroupCongr hH).trans
        (IntermediateField.fixingSubgroupEquiv K1L)) σ) from rfl,
      ← MonoidHom.mem_ker, hχker, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx; rw [← hcoe]; exact h x hx
    · intro h x hx; rw [hcoe]; exact h x hx
  -- ## Step 6: the prime `u = q ∩ K₁` of `K₁` over `l`, and its unramifiedness over `k`
  let u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1) :=
    ⟨q.asIdeal.under (NumberField.RingOfIntegers ↥K1), inferInstance,
      Ideal.under_ne_bot _ q.ne_bot⟩
  have hq_u : q.asIdeal.LiesOver u.asIdeal := Ideal.over_under q.asIdeal
  have hu_l : u.asIdeal.LiesOver l.asIdeal := by
    have h : l.asIdeal = u.asIdeal.under (NumberField.RingOfIntegers k) := by
      show q.asIdeal.under (NumberField.RingOfIntegers k) =
        (q.asIdeal.under (NumberField.RingOfIntegers ↥K1)).under (NumberField.RingOfIntegers k)
      rw [Ideal.under_under]
    exact ⟨h⟩
  haveI hgalK1 : IsGalois k ↥K1 := inferInstance
  have hu_inertia_bot : Ideal.inertia (↥K1 ≃ₐ[k] ↥K1) u.asIdeal = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro τ hτ
    exact Work.SSGRoute.TPatom.fixedField_inertia_eq_bot N q u hq_u hNI τ
      ((Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k) (K := ↥K1) u τ).mpr hτ)
  have hu_unr : u.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    haveI : u.asIdeal.LiesOver l.asIdeal := hu_l
    haveI : u.asIdeal.IsPrime := u.isPrime
    haveI : l.asIdeal.IsPrime := l.isPrime
    exact (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      (F := k) (K := ↥K1) l.asIdeal u.asIdeal).mp hu_inertia_bot
  -- A2: *every* prime of `K₁` over `l` is unramified over `k` (proved helper)
  have hK1unr_all : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1),
      𝔭.asIdeal.LiesOver l.asIdeal →
        𝔭.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    intro 𝔭 h𝔭
    exact Work.SSGate.fixedField_ramificationIdx_eq_one N q hNI 𝔭 (by
      rwa [show q.asIdeal.under (NumberField.RingOfIntegers k) = l.asIdeal from rfl])
  -- ## Step 7: an arithmetic Frobenius `d` at `q'` for `L/k`
  have hq'l : q'.asIdeal.LiesOver l.asIdeal := by
    refine ⟨?_⟩
    rw [show l.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers k) from rfl, hq'lies.over]
    exact Ideal.under_under q'.asIdeal
  obtain ⟨d, hdFrob⟩ := NK.Chebotarev.exists_isFrobAt (K := k) (L := ↥L) l q' hq'l
  have hdD : d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') := by
    exact (Work.SSGcrux.mem_decompK_ofFinite_iff q' d).mpr (by
      apply IsDedekindDomain.HeightOneSpectrum.ext
      rw [← Work.SSGcrux.smul_primeIdeal_eq_smulHeightOneSpectrum' d q',
        NK.Chebotarev.smul_primeIdeal_asIdeal]
      exact NK.Chebotarev.IsFrobAtStabilizes hdFrob)
  -- ## Step 8: `q1 = q' ∩ K₁L`, its unramifiedness over `k`, and the Frobenius bookkeeping
  let q1 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L) :=
    ⟨q'.asIdeal.under (NumberField.RingOfIntegers ↥K1L), inferInstance,
      Ideal.under_ne_bot _ q'.ne_bot⟩
  have hq1_l : q1.asIdeal.LiesOver l.asIdeal := by
    refine ⟨?_⟩
    rw [show l.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers k) from rfl, hq'lies.over]
    exact Ideal.under_under q'.asIdeal
  have hu_eq : u.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥K1) q'.asIdeal := by
    rw [show u.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers ↥K1) from rfl,
      hq'lies.over, Ideal.under_under]
  have hcomap1 : Ideal.comap eK1O q1.asIdeal = u.asIdeal := by
    apply Ideal.ext
    intro x
    rw [Ideal.mem_comap]
    show eK1O x ∈ q1.asIdeal ↔ x ∈ u.asIdeal
    rw [show q1.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥K1L) q'.asIdeal from rfl,
      Ideal.mem_under, hkeyO x, hu_eq, Ideal.mem_under]
  have hq1_unr : q1.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    haveI : q1.asIdeal.LiesOver l.asIdeal := hq1_l
    haveI : q1.asIdeal.IsPrime := q1.isPrime
    haveI : l.asIdeal.IsPrime := l.isPrime
    rw [← Work.SSGRoute.Sha2Lib.ramificationIdx_comap_algEquiv ↥K1 ↥K1L eK1O l
      q1.asIdeal, hcomap1]
    exact hu_unr
  haveI hgalK1L : IsGalois k ↥K1L := IsGalois.of_algEquiv eK1
  have hd1 : NK.Chebotarev.IsFrobAt (K := k) (L := ↥K1L) q1
      (AlgEquiv.restrictNormalHom ↥K1L d) :=
    NK.Chebotarev.IsFrobAtRestrictNormalHom (K := k) (M := ↥L) K1L hq'l hdFrob
  have hcyc : SSGRoute.PTExt.decompK (k := k) (K := ↥K1L) (NK.GlobalCFT.Place.ofFinite q1)
      = Subgroup.zpowers (AlgEquiv.restrictNormalHom ↥K1L d) :=
    Work.SSGRoute.Sha2Lib.stabilizer_ofFinite_eq_zpowers_of_isFrobAt (K := k) (L := ↥K1L)
      q1 hq1_unr (AlgEquiv.restrictNormalHom ↥K1L d) hd1
  let f : ℕ := orderOf (AlgEquiv.restrictNormalHom ↥K1L d)
  have hfpos : 0 < f := orderOf_pos _
  have hd1f : (AlgEquiv.restrictNormalHom ↥K1L d) ^ f = 1 := pow_orderOf_eq_one _
  have hker : (AlgEquiv.restrictNormalHom ↥K1L).ker = N.comap (SSGRoute.PTExt.galRes k K ↥L) := by
    rw [hH, IntermediateField.restrictNormalHom_ker]
  have hmemK : ∀ δ : ↥L ≃ₐ[k] ↥L,
      δ ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') →
      AlgEquiv.restrictNormalHom ↥K1L δ ∈ Subgroup.zpowers (AlgEquiv.restrictNormalHom ↥K1L d) := by
    intro δ hδ
    rw [← hcyc, Work.SSGcrux.mem_decompK_ofFinite_iff]
    have hδ' : NK.GlobalCFT.Place.smulHeightOneSpectrum δ q' = q' :=
      (Work.SSGcrux.mem_decompK_ofFinite_iff q' δ).mp hδ
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
    have hnat := Work.SSGRoute.Sha2Lib.under_smul_heightOneSpectrum (k := k) (K := ↥K1L)
      (L := ↥L) δ q'
    have h2 : Ideal.map (NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormalHom ↥K1L δ))
        (Ideal.under (NumberField.RingOfIntegers ↥K1L) q'.asIdeal)
        = Ideal.under (NumberField.RingOfIntegers ↥K1L)
            (NK.GlobalCFT.Place.smulHeightOneSpectrum δ q').asIdeal := hnat.symm
    rw [show q1.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥K1L) q'.asIdeal from rfl,
      h2, hδ']
  have hdgen : ∀ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L)
      (NK.GlobalCFT.Place.ofFinite q'),
      ∃ m : ℕ, δ⁻¹ * d ^ m ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L) := by
    intro δ hδ
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hmemK δ hδ)
    refine ⟨(n % (f : ℤ)).toNat, ?_⟩
    have hm : (((n % (f : ℤ)).toNat : ℕ) : ℤ) = n % (f : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg n (by exact_mod_cast hfpos.ne'))
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_pow, ← hn]
    rw [← zpow_natCast, hm, ← zpow_eq_zpow_emod' n hd1f]
    group
  have hfmin : ∀ m : ℕ, 0 < m → m < f →
      d ^ m ∉ N.comap (SSGRoute.PTExt.galRes k K ↥L) := by
    intro m hm0 hmf hmem
    rw [← hker, MonoidHom.mem_ker, map_pow] at hmem
    have hdvd : f ∣ m := by
      rw [show f = orderOf (AlgEquiv.restrictNormalHom ↥K1L d) from rfl]
      exact orderOf_dvd_iff_pow_eq_one.mpr hmem
    exact absurd (Nat.le_of_dvd hm0 hdvd) (Nat.not_le.mpr hmf)
  have hdH : d ^ f ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L) := by
    rw [← hker, MonoidHom.mem_ker, map_pow, hd1f]
  -- ## Step 9: the inertia degree of `q1` over `k` is `f`
  have hfdeg : f = q1.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    rw [show f = orderOf (AlgEquiv.restrictNormalHom ↥K1L d) from rfl]
    exact NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg (p := l) (P := q1)
      hq1_l hq1_unr hd1
  -- ## Step 10: the detecting prime `u₀'` and the split/inert dictionary
  have hmapPrime : (Ideal.map (eK1O : NumberField.RingOfIntegers ↥K1 →+*
      NumberField.RingOfIntegers ↥K1L) u₀.asIdeal).IsPrime :=
    Ideal.map_isPrime_of_surjective (f := (eK1O : NumberField.RingOfIntegers ↥K1 →+*
      NumberField.RingOfIntegers ↥K1L)) eK1O.surjective (by
        intro x hx
        rw [RingHom.mem_ker] at hx
        have hx0 : x = 0 := eK1O.injective (by simpa using hx)
        rw [hx0]
        exact u₀.asIdeal.zero_mem)
  have hmapNe : Ideal.map (eK1O : NumberField.RingOfIntegers ↥K1 →+*
      NumberField.RingOfIntegers ↥K1L) u₀.asIdeal ≠ ⊥ := by
    intro hbot
    exact u₀.ne_bot ((Ideal.map_eq_bot_iff_of_injective (f := (eK1O :
      NumberField.RingOfIntegers ↥K1 →+* NumberField.RingOfIntegers ↥K1L))
      eK1O.injective).mp hbot)
  let u₀' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L) :=
    ⟨Ideal.map (eK1O : NumberField.RingOfIntegers ↥K1 →+* NumberField.RingOfIntegers ↥K1L)
        u₀.asIdeal, hmapPrime, hmapNe⟩
  have hu₀'eq : u₀'.asIdeal = Ideal.map (eK1O : NumberField.RingOfIntegers ↥K1 →+*
      NumberField.RingOfIntegers ↥K1L) u₀.asIdeal := rfl
  have hK1unr_all_L : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L),
      𝔭.asIdeal.LiesOver l.asIdeal →
        𝔭.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    intro 𝔭 h𝔭
    haveI : 𝔭.asIdeal.LiesOver l.asIdeal := h𝔭
    haveI : 𝔭.asIdeal.IsPrime := 𝔭.isPrime
    haveI : l.asIdeal.IsPrime := l.isPrime
    let 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1) :=
      IsDedekindDomain.HeightOneSpectrum.comap (eK1O : NumberField.RingOfIntegers ↥K1 →+*
        NumberField.RingOfIntegers ↥K1L) eK1O.surjective 𝔭
    have h𝔮 : 𝔮.asIdeal.LiesOver l.asIdeal := by
      refine Ideal.LiesOver.mk ?_
      rw [h𝔭.over, show 𝔮.asIdeal = Ideal.comap (eK1O : NumberField.RingOfIntegers ↥K1 →+*
        NumberField.RingOfIntegers ↥K1L) 𝔭.asIdeal from rfl]
      simp only [Ideal.under_def, Ideal.comap_comap, hcompatK1O']
    rw [← Work.SSGRoute.Sha2Lib.ramificationIdx_comap_algEquiv ↥K1 ↥K1L eK1O l 𝔭.asIdeal]
    exact hK1unr_all 𝔮 h𝔮
  have hsplit : ∀ p' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L),
      p'.asIdeal.LiesOver l.asIdeal →
      ∀ 𝔮' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥EL),
        𝔮'.asIdeal.LiesOver p'.asIdeal →
          𝔮'.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K1L) = 1 ∧
          (𝔮'.asIdeal.inertiaDeg (NumberField.RingOfIntegers ↥K1L) = 1 ↔ p' ≠ u₀') := by
    classical
    have hSu : ∀ u' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1),
        u'.asIdeal.LiesOver l.asIdeal → u' ≠ u₀ → u' ∈ S := by
      intro u' hu' hne
      simp only [S, Finset.mem_erase, NK.GlobalCFT.Place.mem_primesOverFinite]
      exact ⟨hne, hu'⟩
    exact Work.SSGRoute.TPatom.EL_split_inert_dictionary (k := k) (K1 := ↥K1) (K1L := ↥K1L)
      (L := ↥L) (E := ↥E) (EL := ↥EL) p eK1 eEL hcompatEL l u₀ u₀' (by rw [hu₀'eq])
      hu₀_l S hSu hsplitE hinertE
  have hl_eq : l.asIdeal = q'.asIdeal.under (NumberField.RingOfIntegers k) := by
    rw [show l.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers k) from rfl, hq'lies.over,
      Ideal.under_under]
  have hsplit6 : ∀ p' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L),
      p'.asIdeal.LiesOver (q'.asIdeal.under (NumberField.RingOfIntegers k)) →
      ∀ 𝔮' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥EL),
        𝔮'.asIdeal.LiesOver p'.asIdeal →
          𝔮'.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K1L) = 1 ∧
          (𝔮'.asIdeal.inertiaDeg (NumberField.RingOfIntegers ↥K1L) = 1 ↔ p' ≠ u₀') := by
    intro p' hp' 𝔮' h𝔮'
    exact hsplit p' (Ideal.LiesOver.mk (by rw [hl_eq, hp'.over])) 𝔮' h𝔮'
  -- `K₁L` is Galois over `k` (it is the fixed field of `N.comap galRes`)
  have hK1L_eq : K1L = IntermediateField.fixedField (N.comap (SSGRoute.PTExt.galRes k K ↥L)) := by
    rw [hH, IsGalois.fixedField_fixingSubgroup]
  haveI hgalK1L : IsGalois k ↥K1L := hK1L_eq ▸ (inferInstance : IsGalois k
    ↥(IntermediateField.fixedField (N.comap (SSGRoute.PTExt.galRes k K ↥L))))
  -- ## Step 11: `L/K` is unramified at `q'` (giving `hcop`)
  have hNcEq : L.restrictScalars k = IntermediateField.normalClosure k ↥MM Ω := by
    ext x
    exact Iff.rfl
  have hIbot : Ideal.inertia (↥L ≃ₐ[K] ↥L) q'.asIdeal = ⊥ := by
    haveI hNormL : Normal k ↥L := IsGalois.to_normal
    -- The generation of `L` over `k` by the image of `K` and the conjugates of `MM ∩ L`.
    have hgen0 := Work.SSGRoute.Sha2Lib.normalClosureEqTop (k := k) (K := K) (Ω := Ω) MM L
      hMM_le_L hNcEq
    -- `MM ∩ L` is `K · E` inside `L`
    have hval : (IsScalarTower.toAlgHom k ↥L Ω).comp (IsScalarTower.toAlgHom k K ↥L)
        = IsScalarTower.toAlgHom k K Ω :=
      AlgHom.ext fun x => IsScalarTower.algebraMap_apply K ↥L Ω x
    have hE0 : EL.restrictScalars k = E'.comap (IsScalarTower.toAlgHom k ↥L Ω) :=
      IntermediateField.extendScalars_restrictScalars hK1L_le_E0
    have hLk : Lk = (IsScalarTower.toAlgHom k ↥L Ω).fieldRange := by
      ext x
      exact ⟨fun hx => AlgHom.mem_fieldRange.mpr ⟨⟨x, hx⟩, rfl⟩,
        fun hx => (AlgHom.mem_fieldRange.mp hx).elim fun y hy => hy ▸ y.2⟩
    have hMMle : MM ≤ (IsScalarTower.toAlgHom k ↥L Ω).fieldRange := hLk ▸ hMM_le_L
    have hE'le : E' ≤ (IsScalarTower.toAlgHom k ↥L Ω).fieldRange := hLk ▸ hE'_le_L
    have hcomap : MM.comap (IsScalarTower.toAlgHom k ↥L Ω)
        = (IsScalarTower.toAlgHom k K ↥L).fieldRange ⊔ EL.restrictScalars k := by
      refine IntermediateField.map_injective (IsScalarTower.toAlgHom k ↥L Ω) ?_
      rw [IntermediateField.map_comap_eq_self hMMle, IntermediateField.map_sup, hE0,
        IntermediateField.map_comap_eq_self hE'le, AlgHom.map_fieldRange, hval]
    -- the generation hypothesis in the shape required by the concentrated-level lemma
    have hgen : (⊤ : IntermediateField k ↥L) ≤ (IsScalarTower.toAlgHom k K ↥L).fieldRange ⊔
        K1L ⊔ ⨆ τ : (↥L ≃ₐ[k] ↥L), (EL.restrictScalars k).map (τ : ↥L →ₐ[k] ↥L) := by
      haveI hgalA : IsGalois k ↥((IsScalarTower.toAlgHom k K ↥L).fieldRange) :=
        IsGalois.of_algEquiv (AlgHom.equivFieldRange (IsScalarTower.toAlgHom k K ↥L))
      have hnormA : Normal k ↥((IsScalarTower.toAlgHom k K ↥L).fieldRange) := IsGalois.to_normal
      have hAmap : ∀ τ : (↥L ≃ₐ[k] ↥L),
          ((IsScalarTower.toAlgHom k K ↥L).fieldRange).map (τ : ↥L →ₐ[k] ↥L)
            = (IsScalarTower.toAlgHom k K ↥L).fieldRange :=
        fun τ => (IntermediateField.normal_iff_forall_map_eq.mp hnormA) τ
      rw [show (⊤ : IntermediateField k ↥L) = (IsScalarTower.toAlgHom k K ↥L).fieldRange ⊔
          ⨆ τ : (↥L ≃ₐ[k] ↥L),
            (MM.comap (IsScalarTower.toAlgHom k ↥L Ω)).map (τ : ↥L →ₐ[k] ↥L)
          from hgen0.symm]
      refine sup_le (le_trans le_sup_left le_sup_left) ?_
      rw [iSup_le_iff]
      intro τ
      refine le_trans (IntermediateField.map_mono (τ : ↥L →ₐ[k] ↥L) hcomap.le) ?_
      rw [IntermediateField.map_sup, hAmap τ]
      refine sup_le (le_trans le_sup_left le_sup_left) ?_
      exact le_trans (le_iSup (fun σ : (↥L ≃ₐ[k] ↥L) =>
        (EL.restrictScalars k).map (σ : ↥L →ₐ[k] ↥L)) τ) le_sup_right
    exact Work.SSGate.inertia_eq_bot_of_concentrated_level (k := k) (K := K) (L := ↥L)
      l K1L EL hgen q q' hq'lies hq'l hK1unr_all_L
      (fun 𝔭 h𝔭 𝔮 h𝔮 => (hsplit6 𝔭 (Ideal.LiesOver.mk (by rw [← hl_eq, h𝔭.over])) 𝔮 h𝔮).1)
  have hcop : Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p :=
    Work.SSGRoute.Sha2Lib.coprime_ramificationIdx'_of_inertia_eq_bot (k := k) p q q' hq'lies hIbot
  -- ## Step 12: the `concSet` dictionary for the detecting prime
  have hu₀'_dict : ∀ x : ↥L ≃ₐ[k] ↥L,
      ((NK.GlobalCFT.Place.smulHeightOneSpectrum x q').asIdeal.under
          (NumberField.RingOfIntegers ↥K1L) = u₀'.asIdeal ↔
        SSGRoute.PTExt.galRes k K ↥L x ∈ Work.SSGRoute.TPatom.concSet k K w N γ) := by
    obtain ⟨σ₀, hσ₀⟩ :=
      AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) (E := ↥L) γ
    obtain ⟨u₁', hu₁'img, hu₁'conc⟩ :=
      Work.SSGcrux.under_eq_iff_mem_concSet (N := N) (K1 := K1) (K1L := K1L) eK1
        (fun x => IntermediateField.coe_equivMap_apply (L := K1)
          (f := IsScalarTower.toAlgHom k K ↥L) x) hH w q hwq γ q' hq'lies σ₀ hσ₀
    have hu₁'eq : u₁'.asIdeal = u₀'.asIdeal := by
      rw [hu₁'img]
    have hu₁'eq' : u₁' = u₀' := IsDedekindDomain.HeightOneSpectrum.ext hu₁'eq
    rw [hu₁'eq'] at hu₁'conc
    exact hu₁'conc
  -- ## Step 13: the inertia clause
  have hcl5 : ∀ x : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)),
      (x : ↥L ≃ₐ[k] ↥L) ∈
        Subgroup.normalClosure {σ : ↥L ≃ₐ[k] ↥L | SSGRoute.PTExt.IsInertiaAt q' σ} →
      y x = 1 := by
    have hunrK1L : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L),
        𝔭.asIdeal.LiesOver (q'.asIdeal.under (NumberField.RingOfIntegers k)) →
        𝔭.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 :=
      fun 𝔭 h𝔭 => hK1unr_all_L 𝔭 (Ideal.LiesOver.mk (by rw [hl_eq, h𝔭.over]))
    -- any conjugate of an inertia element at `q'` fixes `EL` pointwise
    have hnc : Subgroup.normalClosure {σ : ↥L ≃ₐ[k] ↥L | SSGRoute.PTExt.IsInertiaAt q' σ} ≤
        (EL.restrictScalars k).fixingSubgroup := by
      refine Work.SSGate.normalClosure_le_of_conj _ _ (fun g i hi => ?_)
      -- `i` fixes `K₁L` pointwise, hence so does `g * i * g⁻¹`
      have hIK : i ∈ K1L.fixingSubgroup :=
        Work.SSGate.isInertiaAt_le_fixingSubgroup K1L q' hunrK1L i hi
      have hσH : g * i * g⁻¹ ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L) :=
        (Subgroup.Normal.comap (inferInstance : N.Normal)
          (SSGRoute.PTExt.galRes k K ↥L)).conj_mem i (hH.symm ▸ hIK) g
      have hσK : g * i * g⁻¹ ∈ K1L.fixingSubgroup := hH ▸ hσH
      -- `g * i * g⁻¹` is inertial at the conjugate prime `Q = g • q'`
      let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L) :=
        NK.GlobalCFT.Place.smulHeightOneSpectrum g q'
      have hσI : SSGRoute.PTExt.IsInertiaAt Q (g * i * g⁻¹) := by
        have h1 : i ∈ Ideal.inertia (↥L ≃ₐ[k] ↥L) q'.asIdeal :=
          (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k) (K := ↥L) q' i).mp hi
        have h2 := Work.SSGRoute.TPatom.mem_inertia_mul_conj q'.asIdeal g h1
        rw [Work.SSGRoute.TPatom.pointwise_smul_asIdeal g q'] at h2
        exact (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k) (K := ↥L) Q
          (g * i * g⁻¹)).mpr h2
      -- `Q` has the same contraction to `𝓞 k` as `q'`
      have hbelow : Ideal.under (NumberField.RingOfIntegers k) Q.asIdeal =
          Ideal.under (NumberField.RingOfIntegers k) q'.asIdeal := by
        rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal, Ideal.under_def, Ideal.under_def,
          ← Ideal.map_coe]
        exact Work.SSGRoute.Sha2Lib.comap_map_eq_comap_of_comp_eq _ _
          (fun x => Work.SSGRoute.Sha2Lib.ringOfIntegersEquiv_algebraMap g x) q'.asIdeal
      let p' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L) :=
        ⟨Q.asIdeal.under (NumberField.RingOfIntegers ↥K1L), inferInstance,
          Ideal.under_ne_bot _ Q.ne_bot⟩
      let 𝔮' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥EL) :=
        ⟨Q.asIdeal.under (NumberField.RingOfIntegers ↥EL), inferInstance,
          Ideal.under_ne_bot _ Q.ne_bot⟩
      have hp' : p'.asIdeal.LiesOver (q'.asIdeal.under (NumberField.RingOfIntegers k)) :=
        Ideal.LiesOver.mk (by
          show Ideal.under (NumberField.RingOfIntegers k) q'.asIdeal =
            Ideal.under (NumberField.RingOfIntegers k) p'.asIdeal
          rw [show p'.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥K1L) Q.asIdeal from rfl,
            Ideal.under_under, hbelow])
      have h𝔮' : 𝔮'.asIdeal.LiesOver p'.asIdeal :=
        Ideal.LiesOver.mk (by
          show p'.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥K1L) 𝔮'.asIdeal
          rw [show 𝔮'.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥EL) Q.asIdeal from rfl,
            show p'.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥K1L) Q.asIdeal from rfl,
            Ideal.under_under])
      -- the inertia of `Q` in `Gal(L/K₁L)` fixes `EL` pointwise (the concentrated split/inert data)
      have hram := (hsplit6 p' hp' 𝔮' h𝔮').1
      have hIF := Work.SSGRoute.TPatom.inertia_le_fixingSubgroup_of_ramificationIdx_eq_one
        (k := ↥K1L) (M := ↥L) EL Q hram
      let σ' : ↥L ≃ₐ[↥K1L] ↥L := IntermediateField.fixingSubgroupEquiv K1L ⟨g * i * g⁻¹, hσK⟩
      have hσ'i : SSGRoute.PTExt.IsInertiaAt Q σ' := hσI
      have hσ'EL : σ' ∈ EL.fixingSubgroup :=
        hIF ((Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := ↥K1L) (K := ↥L) Q
          σ').mp hσ'i)
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      exact (IntermediateField.mem_fixingSubgroup_iff (K := EL) σ').mp hσ'EL z hz
    intro x hx
    rw [hy_iff x]
    intro z hz
    exact (IntermediateField.mem_fixingSubgroup_iff (K := EL.restrictScalars k)
      (x : ↥L ≃ₐ[k] ↥L)).mp (hnc hx) z hz
  -- ## Step 14: the concentration clause
  have hcl6 : ∀ x : ↥L ≃ₐ[k] ↥L,
      y (Work.SSGRoute.TatePoitouRoute.cfunc (N.comap (SSGRoute.PTExt.galRes k K ↥L)) x
          (⟨d ^ f, hdH⟩ : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)))) = 1 ↔
        SSGRoute.PTExt.galRes k K ↥L x ∉ Work.SSGRoute.TPatom.concSet k K w N γ :=
    Work.SSGcrux.aux_concentrationClause (k := k) (K := K) (L := ↥L) p N K1L EL
      hH hgalEL hgalK1LL y hy_iff q' d f hdFrob hdH hfdeg w γ u₀' hu₀'_dict hsplit6
  exact ⟨L, hnfL, hfdL, hgalL, q', hq', hcop, d, f, hdH, y,
    hdD, hfpos, hdgen, hfmin, hcl5, hcl6⟩

end Work.SSGate
