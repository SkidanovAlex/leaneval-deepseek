import Mathlib
import Submission.NK.RamificationAdic.exists_valuationRingData
import Submission.NK.TameStructureDeep.Tame.TameClosure
import Submission.NK.TameStructureDeep.Tame.exists_valuationRing_henselian
import Submission.NK.Ramification.Defs
import Submission.NK.LocalAnabelian.ResidueField.Defs
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.TameStructureDeep.Tame.isPrimitiveRoot_residue
import Submission.NK.TameStructureDeep.Support.mem_unramifiedClosure_of_isPrimitiveRoot
import Submission.NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
import Submission.NK.TameStructureDeep.Tame.isUnit_natCast_of_card_eq_prime_pow
import Submission.NK.Mine.ResidueCharAutomatic
import Submission.Commons.RingTheory.Henselian.kummer_root_lift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Tame

open scoped Classical

/-! ## Teichmüller lifting in a Henselian local ring -/

/-- In a local ring whose residue field has cardinality `p ^ f` with `p` prime, the natural
number `p ^ f - 1` is a unit.

The residue field `k` is a finite field; its characteristic `r` satisfies `r ^ n = p ^ f`, hence
`r = p`, so that `(p ^ f : k) = 0` and `(p ^ f - 1 : k) = -1 ≠ 0`.  As `A` is local, an integer
is a unit of `A` exactly when its residue is nonzero. -/
theorem isUnit_natCast_pow_sub_one_of_card_eq_prime_pow {A : Type*} [CommRing A] [IsLocalRing A]
    {p f : ℕ} (hp : p.Prime) (hcard : Nat.card (IsLocalRing.ResidueField A) = p ^ f) :
    IsUnit ((p ^ f - 1 : ℕ) : A) := by
  have hne : Nat.card (IsLocalRing.ResidueField A) ≠ 0 := by
    rw [hcard]; exact pow_ne_zero f hp.ne_zero
  haveI : Finite (IsLocalRing.ResidueField A) := (Nat.card_ne_zero.mp hne).2
  haveI : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
  have hk2 : 2 ≤ Nat.card (IsLocalRing.ResidueField A) := by
    rw [Nat.card_eq_fintype_card]
    have h := Fintype.one_lt_card (α := IsLocalRing.ResidueField A)
    omega
  have hcardK : Fintype.card (IsLocalRing.ResidueField A) = p ^ f := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  obtain ⟨r, hCharP, n, hrn, hncard⟩ := FiniteField.card' (IsLocalRing.ResidueField A)
  haveI : CharP (IsLocalRing.ResidueField A) r := hCharP
  have heq : r ^ (n : ℕ) = p ^ f := by rw [← hncard, hcardK]
  have hdvd : r ∣ p ^ f := heq ▸ dvd_pow_self r n.ne_zero
  have hrp : r = p := by
    have hdvd_p : r ∣ p := hrn.dvd_of_dvd_pow hdvd
    rcases (Nat.dvd_prime hp).mp hdvd_p with h1 | h1
    · exact absurd h1 hrn.ne_one
    · exact h1
  have hpr : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := hrp ▸ CharP.cast_eq_zero _ r
  have hfpos : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | hpos
    · rw [h0, pow_zero] at hcard; omega
    · exact hpos
  have hpow : ((p : ℕ) : IsLocalRing.ResidueField A) ^ f = 0 := by
    rw [hpr]; exact zero_pow (by omega)
  have hpf : ((p ^ f : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [Nat.cast_pow]; exact hpow
  have hQ : ((p ^ f - 1 : ℕ) : IsLocalRing.ResidueField A) = -1 := by
    rw [Nat.cast_sub (Nat.one_le_pow f p hp.pos), hpf]
    ring
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  rw [map_natCast]
  rw [hQ]
  exact neg_ne_zero.mpr one_ne_zero

/-- **Teichmüller lifting.**  In a Henselian local ring `A` in which the natural number `Q` is a
unit, every `Q`-th root of unity `ā` of the residue field lifts to a `Q`-th root of unity `ζ ∈ A`
with the same residue.

This is Hensel's lemma applied to the polynomial `X ^ Q - 1` at a lift `a₀` of `ā`: the derivative
`Q * a₀ ^ (Q - 1)` is a unit because `Q` and `a₀` are. -/
theorem exists_rootOfUnity_lift {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    {Q : ℕ} (hQ : Q ≠ 0) (hunit : IsUnit (Q : A)) {ā : IsLocalRing.ResidueField A}
    (hā : ā ^ Q = 1) : ∃ ζ : A, ζ ^ Q = 1 ∧ IsLocalRing.residue A ζ = ā := by
  have hā0 : ā ≠ 0 := by
    intro h
    rw [h, zero_pow hQ] at hā
    exact zero_ne_one hā
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective ā
  have ha₀unit : IsUnit a₀ := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ha₀]
    exact hā0
  set F : Polynomial A := Polynomial.X ^ Q - Polynomial.C 1 with hFdef
  have hFmonic : F.Monic := Polynomial.monic_X_pow_sub_C (1 : A) hQ
  have heval : ∀ x : A, F.eval x = x ^ Q - 1 := by intro x; simp [hFdef]
  have h1 : F.eval a₀ ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff (F.eval a₀), heval a₀]
    rw [map_sub, map_pow, map_one, ha₀, hā]
    simp
  have h2 : IsUnit (F.derivative.eval a₀) := by
    have hder : F.derivative.eval a₀ = (Q : A) * a₀ ^ (Q - 1) := by
      simp [hFdef, Polynomial.derivative_X_pow]
    rw [hder]
    exact hunit.mul (ha₀unit.pow (Q - 1))
  obtain ⟨b, hbroot, hbmod⟩ := HenselianLocalRing.is_henselian F hFmonic a₀ h1 h2
  refine ⟨b, ?_, ?_⟩
  · rw [Polynomial.IsRoot.def, heval b] at hbroot
    exact sub_eq_zero.mp hbroot
  · have hc : IsLocalRing.residue A b = IsLocalRing.residue A a₀ := by
      have hz : IsLocalRing.residue A (b - a₀) = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff]; exact hbmod
      rwa [map_sub, sub_eq_zero] at hz
    rw [hc, ha₀]

/-- **A ring automorphism fixing a generator of the units is the identity.**  If `ā` generates the
group `kˣ` of units of a field `k` and `τ : k ≃+* k` fixes `ā`, then `τ = 1`: every nonzero
element of `k` is a `ℤ`-power of `ā`. -/
theorem ringEquiv_eq_one_of_forall_mem_zpowers {k : Type*} [Field k] {ā : kˣ}
    (hgen : ∀ x : kˣ, x ∈ Subgroup.zpowers ā) (τ : k ≃+* k)
    (hτ : τ (ā : k) = (ā : k)) : τ = 1 := by
  refine RingEquiv.ext fun r => ?_
  change τ r = r
  by_cases hr : r = 0
  · rw [hr, map_zero]
  · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hgen (Units.mk0 r hr))
    have hr_eq : r = (ā : k) ^ n := by
      rw [← Units.val_zpow_eq_zpow_val ā n, hn, Units.val_mk0]
    calc τ r = τ ((ā : k) ^ n) := by rw [hr_eq]
      _ = (τ (ā : k)) ^ n := map_zpow₀ τ (ā : k) n
      _ = (ā : k) ^ n := by rw [hτ]
      _ = r := hr_eq.symm

/-! ## The inertia field of a `p`-adic extension is unramified -/

/-- **The inertia field of a finite Galois extension of a `p`-adic field is unramified.**

Let `κ = K_𝔭` be the `𝔭`-adic completion of a number field `K`, `K'` a separable closure of `κ`,
`M/κ` a finite dimensional Galois extension inside `K'`, and `A` a Galois-stable discrete
valuation ring of `M` (`hdec`), which is Henselian and whose residue field is a finite field of
cardinality `p ^ f`, `p = resCharAt 𝔭`.

Then the fixed field of the inertia subgroup `G_0 = ramificationSubgroup A 0` is contained in the
maximal unramified extension `κ^{ur} = unramifiedClosure p` — the classical statement that the
inertia field of a finite extension of local fields is unramified, in the form in which the tame
ramification theory of `κ^{tr}` uses it.

Proof sketch: the residue field `k = A ⧸ 𝔪_A` is a finite field of order `p ^ h`; by Hensel the
generator of `k ^×` lifts to a primitive `(p ^ h - 1)`-th root of unity `ζ ∈ A`, and
`μ_{p^h - 1} ∩ (1 + 𝔪_A) = 1` (the geometric series `1 + ω + ⋯ + ω^{N-1} = 0` with `p ∤ N`)
shows that `G_0` fixes `ζ`, while an element of `Gal(M/κ)` fixing `ζ` acts trivially on `k` (since
`ζ` generates `k ^×`), hence lies in `G_0 = A.inertiaSubgroup κ`.  So
`M ^ {G_0} = κ⟮ζ⟯ ⊆ κ^{ur}`. -/
theorem inertiaFixedField_le_unramifiedClosure {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    (M : IntermediateField (𝔭.adicCompletion K) K') [FiniteDimensional (𝔭.adicCompletion K) M]
    [IsGalois (𝔭.adicCompletion K) M]
    (A : ValuationSubring M) [IsDiscreteValuationRing A] [HenselianLocalRing A]
    (hdec : A.decompositionSubgroup (𝔭.adicCompletion K) = ⊤)
    (hcard : ∃ f : ℕ, Nat.card (IsLocalRing.ResidueField A) =
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f) :
    (IntermediateField.fixedField
      (((NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 0).map
        (A.decompositionSubgroup (𝔭.adicCompletion K)).subtype) :
          Subgroup (M ≃ₐ[𝔭.adicCompletion K] M))).map (IntermediateField.val M) ≤
      NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) := by
  classical
  obtain ⟨f, hf⟩ := hcard
  have hp : Nat.Prime (NK.TameStructureDeep.Tame.resCharAt 𝔭) :=
    NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hunit : IsUnit (((NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f - 1 : ℕ) : A) :=
    isUnit_natCast_pow_sub_one_of_card_eq_prime_pow hp hf
  have hne : Nat.card (IsLocalRing.ResidueField A) ≠ 0 := by
    rw [hf]; exact pow_ne_zero f hp.ne_zero
  haveI : Finite (IsLocalRing.ResidueField A) := (Nat.card_ne_zero.mp hne).2
  haveI : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
  have hk2 : 2 ≤ Nat.card (IsLocalRing.ResidueField A) := by
    rw [Nat.card_eq_fintype_card]
    have h := Fintype.one_lt_card (α := IsLocalRing.ResidueField A)
    omega
  have hpf2 : 2 ≤ (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f := by rw [← hf]; exact hk2
  have hfpos : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | hpos
    · rw [h0, pow_zero] at hpf2; omega
    · exact hpos
  have hQ0 : (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f - 1 ≠ 0 := by omega
  -- a generator of the unit group of the residue field
  obtain ⟨ā, hāgen⟩ := IsCyclic.exists_generator (α := (IsLocalRing.ResidueField A)ˣ)
  have hord : orderOf ā = (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hāgen, Nat.card_units, hf]
  have hāpow : ((ā : IsLocalRing.ResidueField A)) ^
      ((NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f - 1) = 1 := by
    have h1 : ā ^ ((NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f - 1) = 1 := by
      have h := IsPrimitiveRoot.pow_eq_one (IsPrimitiveRoot.orderOf ā)
      rwa [hord] at h
    have h2 := congrArg (fun u : (IsLocalRing.ResidueField A)ˣ =>
      (u : IsLocalRing.ResidueField A)) h1
    simpa using h2
  -- the Teichmüller lift of `ā`
  obtain ⟨ζ, hζpow, hζres⟩ := exists_rootOfUnity_lift hQ0 hunit hāpow
  have hζprim : IsPrimitiveRoot ζ ((NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f - 1) := by
    refine ⟨hζpow, fun l hl => ?_⟩
    have h1 : IsLocalRing.residue A (ζ ^ l) = 1 := by rw [hl, map_one]
    rw [map_pow, hζres] at h1
    have h2 : ā ^ l = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact h1
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one h2
  have hζprimM : IsPrimitiveRoot ((algebraMap A M) ζ) ((NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f - 1) :=
    hζprim.map_of_injective (fun a b h => Subtype.ext h)
  have hζprimK' : IsPrimitiveRoot ((IntermediateField.val M) ((algebraMap A M) ζ))
      ((NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f - 1) :=
    hζprimM.map_of_injective (fun a b h => Subtype.ext h)
  have hQcop : ¬ (NK.TameStructureDeep.Tame.resCharAt 𝔭) ∣
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f - 1 := by
    intro hdiv
    have hfne : f ≠ 0 := by omega
    have hpdiv : (NK.TameStructureDeep.Tame.resCharAt 𝔭) ∣
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f := dvd_pow_self _ hfne
    have h1 : (NK.TameStructureDeep.Tame.resCharAt 𝔭) ∣
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f - ((NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f - 1) :=
      Nat.dvd_sub hpdiv hdiv
    rw [Nat.sub_sub_self (Nat.one_le_pow f _ hp.pos)] at h1
    exact hp.not_dvd_one h1
  -- `ζ` lies in the unramified closure
  have hζE : ((algebraMap A M) ζ) ∈
      IntermediateField.comap (IntermediateField.val M)
        (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭)) := by
    change (IntermediateField.val M) ((algebraMap A M) ζ) ∈
      NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭)
    exact mem_unramifiedClosure_of_isPrimitiveRoot hQcop hζprimK'
  -- every element fixing `ζ` lies in the inertia subgroup
  have hle : (IntermediateField.comap (IntermediateField.val M)
      (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭))).fixingSubgroup ≤
      (((NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 0).map
        (A.decompositionSubgroup (𝔭.adicCompletion K)).subtype) :
          Subgroup (M ≃ₐ[𝔭.adicCompletion K] M)) := by
    intro σ hσ
    rw [Subgroup.mem_map]
    refine ⟨⟨σ, hdec.symm ▸ Subgroup.mem_top σ⟩, ?_, rfl⟩
    rw [NK.Ramification.ramificationSubgroup_zero, ValuationSubring.inertiaSubgroup,
      MonoidHom.mem_ker]
    apply ringEquiv_eq_one_of_forall_mem_zpowers hāgen
    have hζfix : (⟨σ, hdec.symm ▸ Subgroup.mem_top σ⟩ :
        A.decompositionSubgroup (𝔭.adicCompletion K)) • ζ = ζ := by
      apply Subtype.ext
      rw [NK.Ramification.coe_smul]
      exact (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ ((algebraMap A M) ζ) hζE
    have hact : (MulSemiringAction.toRingAut (A.decompositionSubgroup (𝔭.adicCompletion K))
        (IsLocalRing.ResidueField A)) ⟨σ, hdec.symm ▸ Subgroup.mem_top σ⟩
        (IsLocalRing.residue A ζ)
        = (IsLocalRing.residue A)
          ((⟨σ, hdec.symm ▸ Subgroup.mem_top σ⟩ : A.decompositionSubgroup (𝔭.adicCompletion K)) • ζ) := by
      rw [IsLocalRing.ResidueField.residue_smul]
      rfl
    rw [← hζres, hact, hζfix, hζres]
  -- Galois correspondence
  have key : IntermediateField.fixedField
      ((((NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 0).map
        (A.decompositionSubgroup (𝔭.adicCompletion K)).subtype) :
          Subgroup (M ≃ₐ[𝔭.adicCompletion K] M))) ≤
      IntermediateField.comap (IntermediateField.val M)
        (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭)) := by
    have h2 := IntermediateField.fixedField_le hle
    rw [IsGalois.fixedField_fixingSubgroup
      (IntermediateField.comap (IntermediateField.val M)
        (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭)))] at h2
    exact h2
  rw [IntermediateField.map_le_iff_le_comap]
  exact key

end NK.TameStructureDeep.Tame
