import Mathlib
import Submission.Work.MotV5.RigAS.residueAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-!
# Galois-theoretic residue lifting

Let `F ⊆ L` be a field extension of degree `5`, `V` a valuation of `L` extending a valuation `v`
of `F`, and `σ` an order-`5` automorphism of `L` that fixes `F` pointwise and preserves `V`,
whose action on the residue field is non-trivial (hypothesis `hσne`).  Then every `V`-integral
element `x` whose residue class is fixed by `σ` is congruent modulo the maximal ideal to an
element of `F`.

The proof is the standard one.  Write `κ(V)` for the residue field of `V` and `κ(v)` for its
subfield coming from `F` (`ResidueAux.kappaBase`).  Since `σ` preserves `V` it induces an
automorphism `σ̄` of `κ(V)`; the hypothesis `hσne` says precisely that `σ̄ ≠ 1`, so `σ̄` has
order `5`.  By Artin's theorem the fixed field `κ(V)^{σ̄}` has degree `5` over `κ(V)`, while
`[κ(V) : κ(v)] ≤ [L : F] = 5` (linearly independent residue classes lift to `F`-independent
elements).  Hence `κ(v) = κ(V)^{σ̄}` and every `σ̄`-fixed residue class is a residue class of `F`.
-/

namespace Work.MotV5.RigAS

open ResidueAux

section GaloisAut

/-- The ring automorphism of the valuation ring induced by a valuation-preserving ring
automorphism of the field. -/
noncomputable def valRingAut {L : Type*} [Field L]
    (V : Valuation L (WithZero (Multiplicative ℤ))) (σ : L ≃+* L)
    (hstab : ∀ x : L, V (σ x) = V x) : ↥(V.valuationSubring) ≃+* ↥(V.valuationSubring) where
  toFun a := ⟨σ (a : L), (Valuation.mem_valuationSubring_iff V (σ (a : L))).mpr (by
    rw [hstab]
    exact (Valuation.mem_valuationSubring_iff V (a : L)).mp a.2)⟩
  invFun a := ⟨σ.symm (a : L), (Valuation.mem_valuationSubring_iff V (σ.symm (a : L))).mpr (by
    have h := hstab (σ.symm (a : L))
    rw [σ.apply_symm_apply] at h
    rw [← h]
    exact (Valuation.mem_valuationSubring_iff V (a : L)).mp a.2)⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv a := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp

@[simp]
theorem valRingAut_coe {L : Type*} [Field L]
    (V : Valuation L (WithZero (Multiplicative ℤ))) (σ : L ≃+* L)
    (hstab : ∀ x : L, V (σ x) = V x) (a : ↥(V.valuationSubring)) :
    ((valRingAut V σ hstab a : ↥(V.valuationSubring)) : L) = σ (a : L) := rfl

/-- The `5`-th power of `valRingAut` is the identity if `σ ^ 5 = 1`. -/
theorem valRingAut_pow_five {L : Type*} [Field L]
    (V : Valuation L (WithZero (Multiplicative ℤ))) (σ : L ≃+* L)
    (hstab : ∀ x : L, V (σ x) = V x) (hσ5 : ∀ x : L, (σ ^ 5) x = x) :
    valRingAut V σ hstab ^ 5 = 1 := by
  ext a
  change (((valRingAut V σ hstab ^ 5) a : ↥(V.valuationSubring)) : L) = (a : L)
  have e1 : (valRingAut V σ hstab ^ 5) a
      = valRingAut V σ hstab (valRingAut V σ hstab (valRingAut V σ hstab
          (valRingAut V σ hstab (valRingAut V σ hstab a)))) := by
    simp [show (5 : ℕ) = 4 + 1 from rfl, pow_succ]
  rw [e1]
  simp only [valRingAut_coe]
  simpa [show (5 : ℕ) = 4 + 1 from rfl, pow_succ] using hσ5 (a : L)

/-- The automorphism of the residue field induced by a valuation-preserving ring automorphism. -/
noncomputable def residueAut {L : Type*} [Field L]
    (V : Valuation L (WithZero (Multiplicative ℤ))) (σ : L ≃+* L)
    (hstab : ∀ x : L, V (σ x) = V x) :
    IsLocalRing.ResidueField ↥(V.valuationSubring) ≃+*
      IsLocalRing.ResidueField ↥(V.valuationSubring) :=
  IsLocalRing.ResidueField.mapAut (valRingAut V σ hstab)

/-- `residueAut` acts on residue classes by applying `valRingAut`. -/
theorem residueAut_residue {L : Type*} [Field L]
    (V : Valuation L (WithZero (Multiplicative ℤ))) (σ : L ≃+* L)
    (hstab : ∀ x : L, V (σ x) = V x) (a : ↥(V.valuationSubring)) :
    residueAut V σ hstab (IsLocalRing.residue _ a)
      = IsLocalRing.residue _ (valRingAut V σ hstab a) := by
  change (IsLocalRing.ResidueField.mapEquiv (valRingAut V σ hstab))
      (IsLocalRing.residue _ a) = _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

theorem residueAut_pow_five {L : Type*} [Field L]
    (V : Valuation L (WithZero (Multiplicative ℤ))) (σ : L ≃+* L)
    (hstab : ∀ x : L, V (σ x) = V x) (hσ5 : ∀ x : L, (σ ^ 5) x = x) :
    residueAut V σ hstab ^ 5 = 1 := by
  change (IsLocalRing.ResidueField.mapAut (valRingAut V σ hstab)) ^ 5 = 1
  rw [← map_pow, valRingAut_pow_five V σ hstab hσ5, map_one]

/-- `valRingAut` fixes the base valuation ring `baseVS F V`. -/
theorem valRingAut_baseIncl {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L]
    (V : Valuation L (WithZero (Multiplicative ℤ))) (σ : L ≃+* L)
    (hstab : ∀ x : L, V (σ x) = V x) (hσfix : ∀ x : F, σ (algebraMap F L x) = algebraMap F L x)
    (x : ↥(baseVS F V)) :
    valRingAut V σ hstab (baseIncl F V x) = baseIncl F V x := by
  apply Subtype.ext
  rw [valRingAut_coe, baseIncl_apply]
  exact hσfix (x : F)

end GaloisAut

theorem residueLiftGalois {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L]
    (v : Valuation F (WithZero (Multiplicative ℤ))) (V : Valuation L (WithZero (Multiplicative ℤ)))
    (σ : L ≃+* L) (hσfix : ∀ x : F, σ (algebraMap F L x) = algebraMap F L x)
    (hstab : ∀ x : L, V (σ x) = V x)
    (hσ5 : ∀ x : L, (σ ^ 5) x = x)
    (hσne : ∃ z : L, V z ≤ 1 ∧ V (σ z - z) = 1)
    (hfin : Module.finrank F L = 5)
    (hVext : ∀ x : F, V (algebraMap F L x) = v x) :
    ∀ x : L, V x ≤ 1 → V (σ x - x) < 1 → ∃ y : F, V (algebraMap F L y - x) < 1 := by
  classical
  let K := IsLocalRing.ResidueField ↥(V.valuationSubring)
  let κ : Subfield K := ResidueAux.kappaBase F V
  let σbar : K ≃+* K := residueAut V σ hstab
  -- ## `σbar` fixes `κ`
  have hfixκ : ∀ c : ↥κ, σbar (algebraMap ↥κ K c) = algebraMap ↥κ K c := by
    intro c
    show σbar (c : K) = (c : K)
    obtain ⟨x, hx⟩ := (ResidueAux.mem_kappaBase V (c : K)).mp c.2
    rw [← hx, residueAut_residue]
    congr 1
    exact valRingAut_baseIncl V σ hstab hσfix x
  -- ## the `κ`-algebra automorphism `σA`
  let σA : K ≃ₐ[↥κ] K := { σbar with commutes' := hfixκ }
  have hσA5 : σA ^ 5 = 1 := by
    ext y
    have hsq : (σA ^ 5) y = (σbar ^ 5) y := rfl
    rw [hsq, residueAut_pow_five V σ hstab hσ5]
    rfl
  have hσAne : σA ≠ 1 := by
    intro hone
    obtain ⟨z, hzle, hzval⟩ := hσne
    let zO : ↥(V.valuationSubring) := ⟨z, (Valuation.mem_valuationSubring_iff V z).mpr hzle⟩
    have hres : IsLocalRing.residue _ (valRingAut V σ hstab zO) = IsLocalRing.residue _ zO := by
      have h1 : σA (IsLocalRing.residue _ zO) = IsLocalRing.residue _ zO := by
        have h2 := congrArg (fun f : K ≃ₐ[↥κ] K => f (IsLocalRing.residue _ zO)) hone
        rw [show (1 : K ≃ₐ[↥κ] K) (IsLocalRing.residue _ zO)
          = IsLocalRing.residue _ zO from rfl] at h2
        exact h2
      rw [show σA (IsLocalRing.residue _ zO) = σbar (IsLocalRing.residue _ zO) from rfl,
        residueAut_residue] at h1
      exact h1
    have hmem : valRingAut V σ hstab zO - zO ∈ IsLocalRing.maximalIdeal ↥(V.valuationSubring) := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
    have hv := (Valuation.mem_maximalIdeal_iff L V).mp hmem
    have hcoe : ((valRingAut V σ hstab zO - zO : ↥(V.valuationSubring)) : L) = σ z - z := rfl
    rw [hcoe, hzval] at hv
    exact lt_irrefl _ hv
  -- ## Artin's theorem for `⟨σA⟩`
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf σA = 5 := orderOf_eq_prime hσA5 hσAne
  let H : Subgroup (K ≃ₐ[↥κ] K) := Subgroup.zpowers σA
  let E : IntermediateField ↥κ K := IntermediateField.fixedField H
  have hcardH : Nat.card ↥H = 5 := by
    show Nat.card ↥(Subgroup.zpowers σA) = 5
    rw [Nat.card_zpowers, hord]
  -- ## the residue degree bound and finiteness
  have hrank : Module.rank ↥κ K ≤ 5 := by
    refine rank_le (fun s hs => ?_)
    choose z hz using fun i : s => IsLocalRing.residue_surjective (i : K)
    have hlin : LinearIndependent F (fun i : s => ((z i : ↥(V.valuationSubring)) : L)) :=
      ResidueAux.linearIndependent_of_lift V (fun i : s => (i : K)) z hz hs
    have hc := hlin.cardinalMk_le_finrank
    rw [hfin] at hc
    rw [Cardinal.mk_fintype, Fintype.card_coe] at hc
    exact_mod_cast hc
  haveI hFinK : FiniteDimensional ↥κ K :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0)
  have hfinrankκ : Module.finrank ↥κ K ≤ 5 := Module.finrank_le_of_rank_le hrank
  have hfinE : Module.finrank ↥E K = 5 := by
    show Module.finrank ↥(IntermediateField.fixedField H) K = 5
    rw [IntermediateField.finrank_fixedField_eq_card H, hcardH]
  -- ## `⊥ ≤ E`
  have hbot : (⊥ : IntermediateField ↥κ K) ≤ E := by
    intro x hx
    rw [IntermediateField.mem_bot] at hx
    obtain ⟨c, rfl⟩ := hx
    show (algebraMap ↥κ K c : K) ∈ E
    rw [show E = IntermediateField.fixedField H from rfl, IntermediateField.mem_fixedField_iff]
    intro f _hf
    exact f.commutes c
  have hfincmp : Module.finrank ↥(⊥ : IntermediateField ↥κ K) K ≤ Module.finrank ↥E K := by
    rw [IntermediateField.finrank_bot', hfinE]
    exact hfinrankκ
  have hEbot' : (⊥ : IntermediateField ↥κ K) = E :=
    IntermediateField.eq_of_le_of_finrank_le' hbot hfincmp
  have hEbot : E = ⊥ := hEbot'.symm
  -- ## conclusion
  intro x hx hxσ
  let xO : ↥(V.valuationSubring) := ⟨x, (Valuation.mem_valuationSubring_iff V x).mpr hx⟩
  let a : K := IsLocalRing.residue _ xO
  have hafix : σA a = a := by
    show σbar (IsLocalRing.residue _ xO) = IsLocalRing.residue _ xO
    rw [residueAut_residue]
    have hmem : valRingAut V σ hstab xO - xO ∈ IsLocalRing.maximalIdeal ↥(V.valuationSubring) := by
      rw [Valuation.mem_maximalIdeal_iff]
      have hcoe : ((valRingAut V σ hstab xO - xO : ↥(V.valuationSubring)) : L) = σ x - x := rfl
      rw [hcoe]
      exact hxσ
    have hz := (IsLocalRing.residue_eq_zero_iff (valRingAut V σ hstab xO - xO)).mpr hmem
    rwa [map_sub, sub_eq_zero] at hz
  have haE : a ∈ E := by
    show a ∈ IntermediateField.fixedField H
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have hle : Subgroup.zpowers σA ≤ MulAction.stabilizer (K ≃ₐ[↥κ] K) a :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (by show σA a = a; exact hafix))
    have h2 := hle hf
    rwa [MulAction.mem_stabilizer_iff] at h2
  have haκ : a ∈ κ := by
    have h := haE
    rw [hEbot] at h
    rw [IntermediateField.mem_bot] at h
    obtain ⟨c, hc⟩ := h
    rw [← hc]
    exact c.2
  obtain ⟨b, hb⟩ := (ResidueAux.mem_kappaBase V a).mp haκ
  refine ⟨(b : F), ?_⟩
  have hmem : ResidueAux.baseIncl F V b - xO ∈ IsLocalRing.maximalIdeal ↥(V.valuationSubring) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hb]
    show a - a = 0
    rw [sub_self]
  have hv := (Valuation.mem_maximalIdeal_iff L V).mp hmem
  have hcoe : ((ResidueAux.baseIncl F V b - xO : ↥(V.valuationSubring)) : L)
      = algebraMap F L (b : F) - x := rfl
  rwa [hcoe] at hv

end Work.MotV5.RigAS
