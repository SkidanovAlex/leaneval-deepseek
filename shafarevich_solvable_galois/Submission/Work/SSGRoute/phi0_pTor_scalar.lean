import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.LF.classLevelMap_pTorsion_surj
import Submission.Work.SSGRoute.classFormation_ext
import Submission.Work.SSGRoute.exists_galois_level_p_dvd
import Submission.Work.SSGRoute.phi0_defs

namespace Work.SSGRoute

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open SSGRoute.PTExt CategoryTheory

/-! ## Auxiliary facts: cyclotomic levels of degree divisible by `p`

The workspace file `Submission/Work/SSGRoute/exists_galois_level_p_dvd.lean` proves that a
finite Galois intermediate field of degree divisible by `p` exists, but only under the hypothesis
`IsAlgClosure k Ω` (i.e. `Ω` algebraic over `k`).  Here we need the same statement for an
arbitrary algebraically closed `Ω` containing `k` (`Ω = ℂ`, `k = ℚ` being the motivating case), so
we redo the two cyclotomic degree estimates without the integrality of the ambient field. -/

/-- The adjoin of a primitive `n`-th root of unity is a cyclotomic extension.  Unlike
`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension` no integrality of the ambient
field is needed: the only integrality input is that `ζ` itself is algebraic. -/
theorem adjoin_primitiveRoot_isCyclotomicExtension {K L : Type} [Field K] [Field L] [Algebra K L]
    {n : ℕ} [NeZero n] {ζ : L} (hζ : IsPrimitiveRoot ζ n) :
    IsCyclotomicExtension {n} K ↥(IntermediateField.adjoin K ({ζ} : Set L)) := by
  have halg : IsAlgebraic K ζ := by
    refine ⟨Polynomial.X ^ n - 1, ?_, ?_⟩
    · simpa using (Polynomial.monic_X_pow_sub_C (1 : K) (NeZero.ne n)).ne_zero
    · rw [map_sub, Polynomial.aeval_X_pow, map_one, hζ.pow_eq_one, sub_self]
  change IsCyclotomicExtension {n} K (IntermediateField.adjoin K ({ζ} : Set L)).toSubalgebra
  rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (S := ({ζ} : Set L)) (fun x hx => by
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact halg)]
  exact hζ.adjoin_isCyclotomicExtension K

/-- **`[k(ζ) : k] ∣ n.totient`** for an algebraically closed ambient field `Ω ⊇ k` (no integrality
of `Ω` over `k`): `Gal(k(ζ)/k)` embeds into `(ℤ/nℤ)ˣ` via `IsPrimitiveRoot.autToPow`. -/
theorem finrank_adjoin_primitiveRoot_dvd_totient' (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] {n : ℕ} [NeZero n] (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ n) :
    Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set Ω)) ∣ n.totient := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  let E := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hcyc : IsCyclotomicExtension {n} k ↥E := adjoin_primitiveRoot_isCyclotomicExtension hζ
  haveI : IsGalois k ↥E := IsCyclotomicExtension.isGalois {n} k ↥E
  haveI : FiniteDimensional k ↥E := IsCyclotomicExtension.finiteDimensional {n} k ↥E
  let z : ↥E := ⟨ζ, IntermediateField.mem_adjoin_simple_self k ζ⟩
  have hz : IsPrimitiveRoot z n := by
    apply IsPrimitiveRoot.of_map_of_injective
      (f := (IntermediateField.val (S := E) : ↥E →ₐ[k] Ω)) (ζ := z)
    · simpa [z, E] using hζ
    · exact Subtype.val_injective
  have hinj : Function.Injective ⇑(IsPrimitiveRoot.autToPow k hz) := hz.autToPow_injective k
  have h1 : Nat.card ↥(MonoidHom.range (IsPrimitiveRoot.autToPow k hz)) =
      Nat.card (E ≃ₐ[k] E) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_coeSort_range hinj]
  have h2 : Nat.card ↥(MonoidHom.range (IsPrimitiveRoot.autToPow k hz)) ∣ Nat.card ((ZMod n)ˣ) :=
    (MonoidHom.range (IsPrimitiveRoot.autToPow k hz)).card_subgroup_dvd_card
  have h3 : Nat.card ((ZMod n)ˣ) = n.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have h4 : Nat.card (E ≃ₐ[k] E) = Module.finrank k ↥E := IsGalois.card_aut_eq_finrank k ↥E
  rw [h1, h4, h3] at h2
  exact h2

/-- **`φ(p^N) ≤ [k:ℚ] · [k(ζ_{p^N}):k]`** for an algebraically closed ambient field `Ω ⊇ k`. -/
theorem totient_prime_pow_le_finrank_mul_base' (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] {N : ℕ} (hN : 1 ≤ N) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (p ^ N)) :
    (p ^ N).totient ≤ Module.finrank ℚ k *
      Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set Ω)) := by
  haveI hp : p.Prime := Fact.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  haveI hst : IsScalarTower ℚ k Ω :=
    IsScalarTower.of_algebraMap_eq fun x => (RingHom.map_rat_algebraMap (algebraMap k Ω) x).symm
  let E := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hne : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  haveI hcyc : IsCyclotomicExtension {p ^ N} k ↥E := adjoin_primitiveRoot_isCyclotomicExtension hζ
  haveI hfinE : FiniteDimensional k ↥E := IsCyclotomicExtension.finiteDimensional {p ^ N} k ↥E
  haveI : CharZero ↥E := inferInstance
  haveI : FiniteDimensional ℚ ↥E := inferInstance
  let z : ↥E := ⟨ζ, IntermediateField.mem_adjoin_simple_self k ζ⟩
  have hz : IsPrimitiveRoot z (p ^ N) := by
    apply IsPrimitiveRoot.of_map_of_injective
      (f := (IntermediateField.val (S := E) : ↥E →ₐ[k] Ω)) (ζ := z)
    · simpa [z, E] using hζ
    · exact Subtype.val_injective
  have hzp : IsPrimitiveRoot (z ^ p ^ (N - 1)) p := by
    have hd : p ^ (N - 1) ∣ p ^ N := pow_dvd_pow p (Nat.sub_le N 1)
    have := hz.pow_of_dvd (pow_ne_zero (N - 1) hp.ne_zero) hd
    rwa [Nat.pow_div (Nat.sub_le N 1) hp.pos, Nat.sub_sub_self hN, pow_one] at this
  have hlow : (p ^ N).totient ≤ Module.finrank ℚ ↥E := by
    have h := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) (L := ↥E) hzp hz
      (Polynomial.cyclotomic.irreducible_rat
        (Nat.lcm_pos (Nat.pos_of_ne_zero hp.ne_zero) (pow_pos hp.pos N)))
    rwa [Nat.lcm_eq_right (dvd_pow_self p (by omega))] at h
  have htow : Module.finrank ℚ k * Module.finrank k ↥E = Module.finrank ℚ ↥E :=
    Module.finrank_mul_finrank ℚ k ↥E
  exact hlow.trans (le_of_eq htow.symm)

/-- **A `k`-level of degree divisible by `p`** for an algebraically closed `Ω ⊇ k`. -/
theorem exists_cyclo_level_p_dvd (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] :
    ∃ E : IntermediateField k Ω, FiniteDimensional k E ∧ IsGalois k E ∧ p ∣ Module.finrank k E := by
  haveI hp : p.Prime := Fact.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  haveI : IsSepClosed Ω := inferInstance
  let n₀ := Module.finrank ℚ k
  have hn₀ : 0 < n₀ := Module.finrank_pos
  let N : ℕ := n₀ + 1
  have hN : 1 ≤ N := by simp [N]
  have hlt : n₀ < p ^ (N - 1) := by
    have h1 : N - 1 = n₀ := by simp [N]
    rw [h1]
    calc n₀ < 2 ^ n₀ := Nat.lt_two_pow_self
      _ ≤ p ^ n₀ := Nat.pow_le_pow_left hp.two_le n₀
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ N)
  let E : IntermediateField k Ω := IntermediateField.adjoin k ({ζ} : Set Ω)
  have hdvd : Module.finrank k ↥E ∣ (p ^ N).totient :=
    finrank_adjoin_primitiveRoot_dvd_totient' k Ω ζ hζ
  have hle : (p ^ N).totient ≤ n₀ * Module.finrank k ↥E :=
    totient_prime_pow_le_finrank_mul_base' p k Ω hN ζ hζ
  haveI hcyc : IsCyclotomicExtension {p ^ N} k ↥E := adjoin_primitiveRoot_isCyclotomicExtension hζ
  haveI hgalE : IsGalois k ↥E := IsCyclotomicExtension.isGalois {p ^ N} k ↥E
  haveI hfinE : FiniteDimensional k ↥E := IsCyclotomicExtension.finiteDimensional {p ^ N} k ↥E
  exact ⟨E, hfinE, hgalE, dvd_of_dvd_totient_prime_pow hp hN hlt hdvd hle⟩

/-- **A Galois level of degree divisible by `p`.**  For a number field `k`, a finite Galois
extension `k ⊆ K`, and an algebraically closed field `Ω` containing `K` over `k`, there is a finite
Galois level `K ≤ L ≤ Ω` whose degree over `k` is divisible by `p`. -/
theorem exists_lvl_finrank_dvd (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω] :
    ∃ L : Lvl k K Ω, p ∣ Module.finrank k ↥L.1 := by
  obtain ⟨E, hEfin, hEgal, hEdvd⟩ := exists_cyclo_level_p_dvd p k Ω
  haveI := hEfin
  haveI := hEgal
  -- the image `KI` of `K` in `Ω`, as a `k`-intermediate field
  let KI : IntermediateField k Ω := (⊥ : IntermediateField K Ω).restrictScalars k
  haveI hbotgal : IsGalois k ↥(⊥ : IntermediateField K Ω) :=
    IsGalois.of_algEquiv ((IntermediateField.botEquiv K Ω).symm.restrictScalars k)
  haveI hKIfin : FiniteDimensional k KI :=
    inferInstanceAs (FiniteDimensional k ↥(⊥ : IntermediateField K Ω))
  haveI hKIgal : IsGalois k KI :=
    inferInstanceAs (IsGalois k ↥(⊥ : IntermediateField K Ω))
  haveI hKIsep : Algebra.IsSeparable k KI := (isGalois_iff.mp hKIgal).1
  haveI hKInorm : Normal k KI := (isGalois_iff.mp hKIgal).2
  haveI hEsep : Algebra.IsSeparable k E := (isGalois_iff.mp hEgal).1
  haveI hEnorm : Normal k E := (isGalois_iff.mp hEgal).2
  -- the compositum `N = KI ⊔ E`
  let N : IntermediateField k Ω := KI ⊔ E
  haveI hNfin : FiniteDimensional k N := IntermediateField.finiteDimensional_sup KI E
  haveI hNgal : IsGalois k N := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have hNdvd : p ∣ Module.finrank k N :=
    dvd_trans hEdvd (IntermediateField.finrank_dvd_of_le_right (le_sup_right : E ≤ KI ⊔ E))
  -- regard `N` as an `IntermediateField K Ω`
  have hKN : (⊥ : IntermediateField K Ω).restrictScalars k ≤ N := by
    change (⊥ : IntermediateField K Ω).restrictScalars k ≤ KI ⊔ E
    exact le_sup_left
  have hmemL : ∀ t : K, algebraMap K Ω t ∈ (N : Set Ω) := fun t =>
    hKN (by rw [IntermediateField.mem_restrictScalars]; exact IntermediateField.mem_bot.mpr ⟨t, rfl⟩)
  let L' : IntermediateField K Ω := { N.toSubfield with algebraMap_mem' := hmemL }
  haveI hL'fin : FiniteDimensional k L' := inferInstanceAs (FiniteDimensional k ↥N)
  haveI hL'gal : IsGalois k L' := inferInstanceAs (IsGalois k ↥N)
  haveI hL'cz : CharZero L' := inferInstanceAs (CharZero ↥N)
  haveI hL'fdq : FiniteDimensional ℚ L' := FiniteDimensional.trans ℚ k L'
  haveI hL'NF : NumberField L' := NumberField.mk
  refine ⟨⟨L', hL'NF, hL'fin, hL'gal⟩, ?_⟩
  change p ∣ Module.finrank k ↥N
  exact hNdvd

/-! ## The main lemma -/

/-- **Every additive endomorphism of a quotient of `ℤ/p` is scalar.**  If `f : ZMod p →+ G` is a
surjective additive map, then `G` is a quotient of the cyclic group `ℤ/p`, hence trivial or cyclic
of order `p`; in either case every additive endomorphism of `G` is multiplication by a natural
number.  The number is `w.val` where `f w = φ (f 1)`. -/
theorem endo_scalar_of_surj_zmod {p : ℕ} [NeZero p] {G : Type} [AddCommGroup G]
    (f : ZMod p →+ G) (hf : Function.Surjective f) (φ : G →+ G) :
    ∃ n : ℕ, ∀ y, φ y = n • y := by
  let g0 : G := f 1
  obtain ⟨w, hw⟩ := hf (φ g0)
  have hfgen : ∀ z : ZMod p, f z = z.val • g0 := by
    intro z
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [show ((z.val : ℕ) : ZMod p) = z.val • (1 : ZMod p) by rw [nsmul_eq_mul, mul_one]]
    rw [map_nsmul]
  have hw' : φ g0 = w.val • g0 := by rw [← hw, hfgen]
  refine ⟨w.val, fun y => ?_⟩
  obtain ⟨z, rfl⟩ := hf y
  rw [hfgen z, map_nsmul, hw']
  exact smul_comm z.val w.val g0

/-- Every element of the class-group colimit is the image of an element of a single level. -/
theorem ClassLevelLimit.exists_of {k K Ω : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [IsGalois k K] (x : ClassLevelLimit (k := k) (K := K) (Ω := Ω)) :
    ∃ (L : Lvl k K Ω) (z : ClassLevel L),
      ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L z = x :=
  ClassLevelLimit.induction (k := k) (K := K) (Ω := Ω)
    (C := fun x => ∃ (L : Lvl k K Ω) (z : ClassLevel L),
      ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L z = x)
    (fun L z => ⟨L, z, rfl⟩) x

/-- **The `p`-torsion of the colimit is generated by the `p`-torsion of any level of degree
divisible by `p`.**  If `p ∣ [L₀ : k]` then every `p`-torsion class of
`A = colim_L H²(Gal(L/k), C_L)` is the image of a `p`-torsion class of the level `L₀`. -/
theorem pTor_classLevel_surj (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L₀ : Lvl k K Ω) (hp₀ : p ∣ Module.finrank k ↥L₀.1)
    (y : ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω)))) :
    ∃ v : ClassLevel L₀, p • v = 0 ∧
      ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L₀ v
        = (y : ClassLevelLimit (k := k) (K := K) (Ω := Ω)) := by
  have hy : p • (y : ClassLevelLimit (k := k) (K := K) (Ω := Ω)) = 0 := y.2
  obtain ⟨L, z, hz⟩ := ClassLevelLimit.exists_of (k := k) (K := K) (Ω := Ω)
    (y : ClassLevelLimit (k := k) (K := K) (Ω := Ω))
  -- `p • z` is killed in the colimit, hence at some higher level `L'`.
  have h1 : ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L (p • z) = 0 := by
    rw [map_nsmul, hz]
    exact hy
  obtain ⟨L', hLL', hz'⟩ :=
    (ClassLevelLimit.of_eq_zero_iff (k := k) (K := K) (Ω := Ω) L (p • z)).mp h1
  -- pick a common upper bound `M ≥ L₀, L'` (the compositum of the two levels)
  let M : Lvl k K Ω :=
    ⟨L₀.1 ⊔ L'.1, inferInstance, inferInstance, isGalois_sup (L := L₀.1) (L' := L'.1)⟩
  have hL₀M : L₀ ≤ M := by change L₀.1 ≤ (L₀.1 ⊔ L'.1); exact le_sup_left
  have hL'M : L' ≤ M := by change L'.1 ≤ (L₀.1 ⊔ L'.1); exact le_sup_right
  -- the `p`-torsion class at `M`
  have hz'' : p • (classLevelMap (k := k) L L' hLL' z) = 0 := by
    simpa only [map_nsmul] using hz'
  have hw : p • (classLevelMap (k := k) L' M hL'M (classLevelMap (k := k) L L' hLL' z)) = 0 := by
    rw [← map_nsmul, hz'', map_zero]
  obtain ⟨v, hv, hvEq⟩ :=
    LF.classLevelMap_pTorsion_surj p L₀ M hL₀M hp₀
      (classLevelMap (k := k) L' M hL'M (classLevelMap (k := k) L L' hLL' z)) hw
  refine ⟨v, hv, ?_⟩
  rw [← hz]
  calc ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L₀ v
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) M
          (classLevelMap (k := k) L₀ M hL₀M v) :=
        (ClassLevelLimit.of_levelMap (k := k) (K := K) (Ω := Ω) hL₀M v).symm
    _ = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) M
          (classLevelMap (k := k) L' M hL'M (classLevelMap (k := k) L L' hLL' z)) := by
        rw [hvEq]
    _ = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L'
          (classLevelMap (k := k) L L' hLL' z) :=
        ClassLevelLimit.of_levelMap (k := k) (K := K) (Ω := Ω) hL'M _
    _ = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L z :=
        ClassLevelLimit.of_levelMap (k := k) (K := K) (Ω := Ω) hLL' z

/-- The additive map `P → A[p]` induced by the colimit map of the level `L₀`, for `P` a subgroup
of the `p`-torsion of `ClassLevel L₀`. -/
noncomputable def pTorClassLevelHom {k K Ω : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [IsGalois k K] (p : ℕ) (L₀ : Lvl k K Ω) (P : AddSubgroup (ClassLevel L₀))
    (hP : ∀ v : ClassLevel L₀, v ∈ P ↔ p • v = 0) :
    ↥P →+ ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) where
  toFun v := ⟨ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L₀ v.1, by
    rw [mem_pTor, ← map_nsmul, (hP v.1).mp v.2, map_zero]⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; simp [map_add]

/-- **E4Ω cyclicity.**  The `p`-torsion `A[p]` of the class-group colimit `A = colim_L H²(Gal(L/k),C_L)` is cyclic of order dividing `p` (the class formation gives `A[p] ≃ ℤ/p`): every additive endomorphism of `A[p]` is multiplication by a natural number. -/
theorem phi0_pTor_scalar (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (φ : ↥(Work.SSGRoute.pTor p (Work.SSGRoute.ClassLevelLimit (k := k) (K := K) (Ω := Ω))) →+
         ↥(Work.SSGRoute.pTor p (Work.SSGRoute.ClassLevelLimit (k := k) (K := K) (Ω := Ω)))) :
    ∃ n : ℕ, ∀ y, φ y = n • y := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- a level whose degree over `k` is divisible by `p`
  obtain ⟨L₀, hp₀⟩ := exists_lvl_finrank_dvd p k K Ω
  -- the `p`-torsion of `H²(Gal(L₀/k),C_{L₀})` is `𝔽_p`
  obtain ⟨P, χ, hP, hχ⟩ := pt_char_pTorsion p k K ↥L₀.1 hp₀
  let χe : ↥P ≃+ ZMod p := AddEquiv.ofBijective χ hχ
  let gP : ↥P →+ ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) :=
    pTorClassLevelHom p L₀ P hP
  let g : ZMod p →+ ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) :=
    gP.comp χe.symm.toAddMonoidHom
  have hgP : Function.Surjective gP := by
    intro y
    obtain ⟨v, hv, hvy⟩ := pTor_classLevel_surj p k K Ω L₀ hp₀ y
    refine ⟨⟨v, (hP v).mpr hv⟩, ?_⟩
    apply Subtype.ext
    change (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L₀ v
      : ClassLevelLimit (k := k) (K := K) (Ω := Ω)) = (y : ClassLevelLimit (k := k) (K := K) (Ω := Ω))
    exact hvy
  have hg : Function.Surjective g := hgP.comp χe.symm.surjective
  exact endo_scalar_of_surj_zmod g hg φ

end Work.SSGRoute
