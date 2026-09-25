import Mathlib
import Submission.NK.LocalReciprocityLubinTate.All
import Submission.NK.LocalReciprocity.NormGroup

/-!
# `NK.NUV2.LC.cylArtinValues`

The values of the local Artin map on the cyclotomic tower of `ℚ_l`: for a prime `l`, `n ≥ 1` and a
primitive `l ^ n`-th root of unity `ζ` in the algebraic closure of `ℚ_l`, there is a surjective
monoid homomorphism

  `Φ : ℚ_lˣ →* Gal(ℚ_l(ζ_{l ^ n})/ℚ_l)`

with kernel `⟨l⟩ · U ^ n` (`U ^ n` the `n`-th higher unit group) and the normalisation
`Φ(u)(ζ) = ζ ^ m` for every integral unit `u` whose class modulo `𝔪 ^ n` is the class of `m`.

The mathematical content is Milne, *Classical Field Theory*, I.3.13(b): the explicit reciprocity
law for the cyclotomic extension of `ℚ_l`, together with the irreducibility of the `l ^ n`-th
cyclotomic polynomial over `ℚ_l` (Eisenstein at `l` after the substitution `X ↦ X + 1`).
-/

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open Polynomial
open scoped ValuativeRel Topology

namespace NK.NUV2.LC

universe u

noncomputable section

/-! ## The translation `X ↦ X + 1` on polynomials

The irreducibility transfer: `p` is irreducible if and only if `p(X + 1)` is, since translation is
a ring automorphism of `K[X]`. -/

section Shift

variable {K : Type*} [Field K]

theorem comp_X_add_C_one_comp_X_sub_C_one (p : K[X]) :
    (p.comp (X + C 1)).comp (X - C 1) = p := by
  rw [comp_assoc]
  have h : (X + C (1:K)).comp (X - C 1) = X := by
    rw [add_comp, X_comp, C_comp, sub_add_cancel]
  rw [h, comp_X]

theorem comp_X_sub_C_one_comp_X_add_C_one (p : K[X]) :
    (p.comp (X - C 1)).comp (X + C 1) = p := by
  rw [comp_assoc]
  have h : (X - C (1:K)).comp (X + C 1) = X := by
    rw [sub_comp, X_comp, C_comp, add_sub_cancel_right]
  rw [h, comp_X]

/-- The ring automorphism `p ↦ p(X + 1)` of `K[X]`. -/
noncomputable def compShiftEquiv (K : Type*) [Field K] : K[X] ≃+* K[X] :=
  RingEquiv.ofBijective (Polynomial.compRingHom (X + C (1:K)))
    ⟨fun p q h => by
       have h2 : p.comp (X + C 1) = q.comp (X + C 1) := h
       have h3 := congrArg (fun r : K[X] => r.comp (X - C 1)) h2
       rwa [comp_X_add_C_one_comp_X_sub_C_one p, comp_X_add_C_one_comp_X_sub_C_one q] at h3,
     fun q => ⟨q.comp (X - C 1), by
       show (Polynomial.compRingHom (X + C (1:K))) (q.comp (X - C 1)) = q
       rw [show (Polynomial.compRingHom (X + C (1:K))) (q.comp (X - C 1))
            = (q.comp (X - C 1)).comp (X + C 1) from rfl,
         comp_X_sub_C_one_comp_X_add_C_one]⟩⟩

@[simp] theorem compShiftEquiv_apply (p : K[X]) :
    compShiftEquiv K p = p.comp (X + C 1) := rfl

theorem compShiftEquiv_symm_apply (p : K[X]) :
    (compShiftEquiv K).symm p = p.comp (X - C 1) := by
  rw [RingEquiv.symm_apply_eq]
  show p = (Polynomial.compRingHom (X + C (1:K))) (p.comp (X - C 1))
  rw [show (Polynomial.compRingHom (X + C (1:K))) (p.comp (X - C 1))
       = (p.comp (X - C 1)).comp (X + C 1) from rfl, comp_X_sub_C_one_comp_X_add_C_one]

theorem irreducible_comp_X_add_C_one_iff (p : K[X]) :
    Irreducible (p.comp (X + C 1)) ↔ Irreducible p := by
  constructor
  · intro h
    have h' := Irreducible.map (compShiftEquiv K).symm.toMulEquiv h
    change Irreducible ((compShiftEquiv K).symm (p.comp (X + C 1))) at h'
    rwa [compShiftEquiv_symm_apply, comp_X_add_C_one_comp_X_sub_C_one] at h'
  · intro h
    have h' := Irreducible.map (compShiftEquiv K).toMulEquiv h
    change Irreducible ((compShiftEquiv K) p) at h'
    rwa [compShiftEquiv_apply] at h'

end Shift

/-! ## The cyclotomic polynomial of a prime power modulo `l` -/

/-- **`cyclotomic (l ^ (k+1)) (X + 1)` modulo `l` is the monomial `X ^ ((l-1) * l ^ k)`.**

This is the classical Frobenius computation: over `𝔽_l` one has
`(X + 1) ^ (l ^ j) = X ^ (l ^ j) + 1`, and the identity
`cyclotomic (l ^ (k+1)) * (X ^ (l ^ k) - 1) = X ^ (l ^ (k+1)) - 1` then gives the claim. -/
theorem cyclotomic_prime_pow_comp_X_add_one {l k : ℕ} (hl : l.Prime) :
    (cyclotomic (l ^ (k + 1)) (ZMod l)).comp (X + C (1 : ZMod l)) = X ^ ((l - 1) * l ^ k) := by
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : CharP (ZMod l) l := ZMod.charP l
  have hfrob : ∀ j : ℕ, (X + C (1 : ZMod l)) ^ l ^ j = X ^ l ^ j + 1 := by
    intro j
    rw [add_pow_char_pow (X : (ZMod l)[X]) (C 1) l j]
    simp
  have h1 := cyclotomic_prime_pow_mul_X_pow_sub_one (ZMod l) l k
  have h3 : ((cyclotomic (l ^ (k+1)) (ZMod l)).comp (X + C 1)) * ((X + C 1) ^ (l^k) - 1)
      = (X + C 1) ^ (l^(k+1)) - 1 := by
    have := congrArg (fun p : (ZMod l)[X] => p.comp (X + C (1 : ZMod l))) h1
    simpa [mul_comp, sub_comp, X_pow_comp] using this
  rw [hfrob k, hfrob (k+1)] at h3
  simp only [add_sub_cancel_right] at h3
  have hle : l ^ k ≤ l ^ (k+1) := Nat.pow_le_pow_right hl.one_le (by omega)
  have hpow : (X : (ZMod l)[X]) ^ (l ^ (k+1)) = X ^ (l ^ (k+1) - l ^ k) * X ^ (l^k) := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hpow] at h3
  have h4 : (cyclotomic (l ^ (k+1)) (ZMod l)).comp (X + C (1 : ZMod l))
      = X ^ (l ^ (k+1) - l ^ k) :=
    mul_right_cancel₀ (pow_ne_zero _ (X_ne_zero (R := ZMod l))) h3
  rw [h4]
  have hsub : l ^ (k+1) - l ^ k = (l - 1) * l ^ k := by
    have h20 : l ^ (k+1) - l ^ k = l^k * l - l^k * 1 := by rw [pow_succ, mul_one]
    rw [h20, ← Nat.mul_sub_left_distrib, mul_comm]
  rw [hsub]

theorem monic_cyclotomic_prime_pow_comp (l k : ℕ) :
    ((cyclotomic (l^(k+1)) ℤ).comp (X + C (1:ℤ))).Monic :=
  (cyclotomic.monic _ ℤ).comp (monic_X_add_C 1) (by rw [natDegree_X_add_C]; norm_num)

/-- The constant term of `cyclotomic (l ^ (k+1)) (X + 1)` is `l`. -/
theorem coeff_zero_cyclotomic_prime_pow_comp {l k : ℕ} (hl : l.Prime) :
    ((cyclotomic (l^(k+1)) ℤ).comp (X + C (1:ℤ))).coeff 0 = (l : ℤ) := by
  haveI : Fact l.Prime := ⟨hl⟩
  rw [coeff_zero_eq_eval_zero, eval_comp]
  have h : eval (0 : ℤ) (X + C (1:ℤ)) = 1 := by simp
  rw [h]
  exact eval_one_cyclotomic_prime_pow k

/-- The degree of `cyclotomic (l ^ (k+1)) (X + 1)` is `(l - 1) * l ^ k`. -/
theorem natDegree_cyclotomic_prime_pow_comp {l k : ℕ} (hl : l.Prime) :
    ((cyclotomic (l^(k+1)) ℤ).comp (X + C (1:ℤ))).natDegree = (l - 1) * l ^ k := by
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hmap : Polynomial.map (Int.castRingHom (ZMod l))
      ((cyclotomic (l^(k+1)) ℤ).comp (X + C (1:ℤ))) = X ^ ((l-1) * l^k) := by
    rw [Polynomial.map_comp, Polynomial.map_cyclotomic]
    have hx : Polynomial.map (Int.castRingHom (ZMod l)) (X + C (1:ℤ)) = X + C (1 : ZMod l) := by
      rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
      simp
    rw [hx]
    exact cyclotomic_prime_pow_comp_X_add_one hl
  have h1 := (monic_cyclotomic_prime_pow_comp l k).natDegree_map (Int.castRingHom (ZMod l))
  rw [hmap, natDegree_X_pow] at h1
  exact h1.symm

/-- All coefficients of `cyclotomic (l ^ (k+1)) (X + 1)` below the leading one are divisible
by `l`. -/
theorem dvd_coeff_cyclotomic_prime_pow_comp {l k : ℕ} (hl : l.Prime) {i : ℕ}
    (hi : i < (l - 1) * l ^ k) :
    (l : ℤ) ∣ ((cyclotomic (l ^ (k+1)) ℤ).comp (X + C (1:ℤ))).coeff i := by
  have hmap : Polynomial.map (Int.castRingHom (ZMod l))
      ((cyclotomic (l^(k+1)) ℤ).comp (X + C (1:ℤ))) = X ^ ((l-1) * l^k) := by
    rw [Polynomial.map_comp, Polynomial.map_cyclotomic]
    have hx : Polynomial.map (Int.castRingHom (ZMod l)) (X + C (1:ℤ)) = X + C (1 : ZMod l) := by
      rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
      simp
    rw [hx]
    exact cyclotomic_prime_pow_comp_X_add_one hl
  have hcoeff : ((((cyclotomic (l^(k+1)) ℤ).comp (X + C (1:ℤ))).coeff i : ℤ) : ZMod l) = 0 := by
    have := congrArg (fun p : (ZMod l)[X] => p.coeff i) hmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_X_pow] at this
    rw [if_neg (by omega : i ≠ (l - 1) * l ^ k)] at this
    exact this
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcoeff

/-! ## Eisenstein's criterion at the maximal ideal of a local DVR -/

/-- **Eisenstein's criterion for the cyclotomic polynomial of a prime power.**

Let `R` be an integrally closed local domain with fraction field `K`, and let `l` be a prime with
`(l : R)` in the maximal ideal of `R` but not in its square.  Then `cyclotomic (l ^ (k+1))` is
irreducible over `K`. -/
theorem irreducible_cyclotomic_prime_pow_of_isLocalRing
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {l k : ℕ} (hl : l.Prime)
    (hmem : (l : R) ∈ IsLocalRing.maximalIdeal R)
    (hnot : (l : R) ∉ IsLocalRing.maximalIdeal R ^ 2) :
    Irreducible (cyclotomic (l ^ (k+1)) K) := by
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  set f : ℤ[X] := (cyclotomic (l^(k+1)) ℤ).comp (X + C (1:ℤ)) with hf
  have hfm : f.Monic := monic_cyclotomic_prime_pow_comp l k
  have hfdeg : f.natDegree = (l-1)*l^k := natDegree_cyclotomic_prime_pow_comp hl
  have hf0 : f.coeff 0 = (l : ℤ) := coeff_zero_cyclotomic_prime_pow_comp hl
  set F : R[X] := f.map (Int.castRingHom R) with hF
  have hFm : F.Monic := hfm.map _
  have hFdeg : F.natDegree = (l-1)*l^k := by
    rw [hF, hfm.natDegree_map (Int.castRingHom R), hfdeg]
  have hEis : F.IsEisensteinAt (IsLocalRing.maximalIdeal R) := by
    refine hFm.isEisensteinAt_of_mem_of_notMem (IsLocalRing.maximalIdeal.isMaximal R).ne_top ?_ ?_
    · intro i hi
      rw [hFdeg] at hi
      obtain ⟨d, hd⟩ := dvd_coeff_cyclotomic_prime_pow_comp hl hi
      have hcoe : F.coeff i = (l : R) * (d : R) := by
        rw [hF, coeff_map, Int.coe_castRingHom, hd]
        push_cast
        ring
      rw [hcoe]
      exact Ideal.mul_mem_right _ _ hmem
    · have hcoe : F.coeff 0 = (l : R) := by
        rw [hF, coeff_map, Int.coe_castRingHom, hf0]
        exact Int.cast_natCast l
      rw [hcoe]; exact hnot
  have hpos : 0 < F.natDegree := by
    rw [hFdeg]
    exact Nat.mul_pos (by have := hl.two_le; omega) (pow_pos hl.pos k)
  have hFirr : Irreducible F :=
    hEis.irreducible ((IsLocalRing.maximalIdeal.isMaximal R).isPrime) hFm.isPrimitive hpos
  have hGauss : Irreducible (F.map (algebraMap R K)) :=
    (hFm.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hFirr
  have hFK : F.map (algebraMap R K) = f.map (Int.castRingHom K) := by
    rw [hF, Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hcomp : f.map (Int.castRingHom K) = (cyclotomic (l^(k+1)) K).comp (X + C (1:K)) := by
    rw [hf, Polynomial.map_comp, Polynomial.map_cyclotomic]
    have hx : Polynomial.map (Int.castRingHom K) (X + C (1:ℤ)) = X + C (1:K) := by
      rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]; simp
    rw [hx]
  rw [hFK, hcomp] at hGauss
  exact (irreducible_comp_X_add_C_one_iff _).mp hGauss

/-! ## The bridge between `Valued.v` and the valuative relation

The `ValuativeRel` instance on `Q.adicCompletion K` is the one induced by the canonical
`Valued.v`-valuation of the completion, but it is an opaque choice, so the two valuations have to be
compared through the common topology: the elements of valuation `< 1` are characterised as the
topologically nilpotent ones, and this gives `valued_v_le_one_iff`, the equality of the two unit
balls (hence of the two rings of integers). -/

open Filter

private lemma exists_lt_one_of_nontrivial {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [Nontrivial G] : ∃ g : G, g < 1 := by
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial G).exists_pair_ne
  have hne : a * b⁻¹ ≠ (1 : G) := by
    intro h
    refine hab ?_
    have h2 : (a * b⁻¹) * b = 1 * b := by rw [h]
    simpa using h2
  obtain ⟨g, hg⟩ : ∃ g : G, g ≠ 1 := ⟨a * b⁻¹, hne⟩
  rcases lt_or_gt_of_ne hg with h | h
  · exact ⟨g, h⟩
  · exact ⟨g⁻¹, by rw [Left.inv_lt_one_iff]; exact h⟩

private lemma exists_pow_lt_of_lt_one {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [IsCyclic G] [Nontrivial G] {a b : G} (ha : a < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a ^ n < b := by
  obtain ⟨g, hgzp⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, Subgroup.zpowers_one_eq_bot] at hgzp
    exact absurd hgzp.symm
      ((Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup G)).mp inferInstance)
  rcases lt_or_gt_of_ne hg1 with hglt | hggt
  · have hg := hglt; have hzg := hgzp
    obtain ⟨k, hk⟩ : ∃ k : ℤ, g ^ k = a :=
      Subgroup.mem_zpowers_iff.mp (hzg ▸ Subgroup.mem_top a)
    have hkpos : 0 < k := by
      by_contra hk0
      push Not at hk0
      have hle : g ^ (0 : ℤ) ≤ g ^ k := (zpow_right_strictAnti hg).antitone hk0
      rw [zpow_zero] at hle
      exact absurd (hk ▸ hle) (not_le.mpr ha)
    obtain ⟨m, hm⟩ : ∃ m : ℤ, g ^ m = b :=
      Subgroup.mem_zpowers_iff.mp (hzg ▸ Subgroup.mem_top b)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → m < k * (n : ℤ) := by
      refine ⟨(m.toNat : ℕ) + 1, fun n hn => ?_⟩
      have hn' : (m.toNat : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
      have hmle : m ≤ (m.toNat : ℤ) := Int.self_le_toNat m
      have hkn : (n : ℤ) ≤ k * (n : ℤ) := by nlinarith [Int.natCast_nonneg n]
      omega
    refine ⟨N, fun n hn => ?_⟩
    have hmn : m < k * (n : ℤ) := hN n hn
    rw [← hk, ← hm, ← zpow_natCast, ← zpow_mul]
    exact (zpow_right_strictAnti hg) hmn
  · set g' : G := g⁻¹ with hg'def
    have hg' : g' < 1 := by rw [hg'def, Left.inv_lt_one_iff]; exact hggt
    have hzg' : Subgroup.zpowers g' = ⊤ := by rw [hg'def, Subgroup.zpowers_inv, hgzp]
    obtain ⟨k, hk⟩ : ∃ k : ℤ, g' ^ k = a :=
      Subgroup.mem_zpowers_iff.mp (hzg' ▸ Subgroup.mem_top a)
    have hkpos : 0 < k := by
      by_contra hk0
      push Not at hk0
      have hle : g' ^ (0 : ℤ) ≤ g' ^ k := (zpow_right_strictAnti hg').antitone hk0
      rw [zpow_zero] at hle
      exact absurd (hk ▸ hle) (not_le.mpr ha)
    obtain ⟨m, hm⟩ : ∃ m : ℤ, g' ^ m = b :=
      Subgroup.mem_zpowers_iff.mp (hzg' ▸ Subgroup.mem_top b)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → m < k * (n : ℤ) := by
      refine ⟨(m.toNat : ℕ) + 1, fun n hn => ?_⟩
      have hn' : (m.toNat : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
      have hmle : m ≤ (m.toNat : ℤ) := Int.self_le_toNat m
      have hkn : (n : ℤ) ≤ k * (n : ℤ) := by nlinarith [Int.natCast_nonneg n]
      omega
    refine ⟨N, fun n hn => ?_⟩
    have hmn : m < k * (n : ℤ) := hN n hn
    rw [← hk, ← hm, ← zpow_natCast, ← zpow_mul]
    exact (zpow_right_strictAnti hg') hmn

/-- In the valuative topology, the topologically nilpotent elements of a field are exactly the
elements of valuation `< 1`. -/
private lemma tendsto_pow_nhds_zero_iff_vlt_one {F : Type*} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsValuativeTopology F]
    [IsCyclic (ValuativeRel.ValueGroupWithZero F)ˣ]
    [Nontrivial (ValuativeRel.ValueGroupWithZero F)ˣ] (y : F) :
    Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0) ↔ (ValuativeRel.valuation F) y < 1 := by
  set v := ValuativeRel.valuation F with hv
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hvy : v y ≠ 0 := fun h0 => absurd (h0 ▸ hcon) (by norm_num)
    obtain ⟨γ, hγ⟩ := exists_lt_one_of_nontrivial
      (G := (ValuativeRel.ValueGroupWithZero F)ˣ)
    have hball : ({z : F | v z < (γ : ValuativeRel.ValueGroupWithZero F)}) ∈ 𝓝 (0 : F) :=
      (IsValuativeTopology.mem_nhds_iff (x := (0 : F))).mpr
        ⟨γ, fun z hz => by
          rcases hz with ⟨w, hw, hzw⟩
          rw [← hzw]
          simpa using hw⟩
    have hpow : ∀ n : ℕ, 1 ≤ n → (1 : ValuativeRel.ValueGroupWithZero F) ≤ (v y) ^ n := by
      intro n _
      have h1 : (1 : (ValuativeRel.ValueGroupWithZero F)ˣ) ≤ Units.mk0 (v y) hvy := by
        rw [← Units.val_le_val]
        simpa [Units.mk0_val] using hcon
      have h2 : (1 : (ValuativeRel.ValueGroupWithZero F)ˣ) ^ n ≤ (Units.mk0 (v y) hvy) ^ n :=
        pow_le_pow_left' h1 n
      rw [one_pow] at h2
      rw [← Units.val_le_val] at h2
      simpa [Units.val_pow_eq_pow_val, Units.mk0_val] using h2
    have hnot : ¬ (∀ᶠ n : ℕ in atTop,
        y ^ n ∈ ({z : F | v z < (γ : ValuativeRel.ValueGroupWithZero F)})) := by
      intro hev
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
      have hn1 : 1 ≤ max N 1 := le_max_right _ _
      have hmem := hN (max N 1) (le_max_left _ _)
      have hlt : v (y ^ max N 1) < (γ : ValuativeRel.ValueGroupWithZero F) := hmem
      have hge : (1 : ValuativeRel.ValueGroupWithZero F) ≤ v (y ^ max N 1) := by
        rw [map_pow]; exact hpow _ hn1
      have hγv : (γ : ValuativeRel.ValueGroupWithZero F) < 1 := by
        simpa using ((Units.val_lt_val (a := γ)
          (b := (1 : (ValuativeRel.ValueGroupWithZero F)ˣ))).mpr hγ)
      exact not_lt_of_ge (le_of_lt hlt) (lt_of_lt_of_le hγv hge)
    exact hnot (h.eventually hball)
  · intro h s hs
    obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_iff (x := (0 : F))).mp hs
    have hγ' : {z : F | v z < (γ : ValuativeRel.ValueGroupWithZero F)} ⊆ s :=
      fun z hz => hγ ⟨z, hz, by simp⟩
    have hgoal : ∀ᶠ n : ℕ in atTop, v (y ^ n) < (γ : ValuativeRel.ValueGroupWithZero F) := by
      rcases eq_or_ne y 0 with hy0 | hy
      · rw [hy0]
        refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
        rw [zero_pow (by omega : n ≠ 0)]
        exact zero_lt_iff.mpr (Units.ne_zero γ)
      · have hvy : v y ≠ 0 := (Valuation.ne_zero_iff v).mpr hy
        have ha : Units.mk0 (v y) hvy < 1 := by
          rw [← Units.val_lt_val]; simpa [Units.mk0_val] using h
        obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
          (G := (ValuativeRel.ValueGroupWithZero F)ˣ) ha (b := γ)
        refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
        have h2 := hN n hn
        rw [← Units.val_lt_val] at h2
        simp only [Units.val_pow_eq_pow_val, Units.mk0_val] at h2
        simpa [map_pow] using h2
    exact hgoal.mono fun n hn => hγ' hn

/-- **The two valuations on a completion have the same unit ball.**  The `ValuativeRel` valuation of
`Q.adicCompletion K` and the canonical `Valued.v`-valuation of the completion define the same ring
of integers. -/
theorem valued_v_le_one_iff {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : Q.adicCompletion K) :
    (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)) x ≤ 1 ↔
      (ValuativeRel.valuation (Q.adicCompletion K)) x ≤ 1 := by
  haveI hnt : Nontrivial (ValuativeRel.ValueGroupWithZero (Q.adicCompletion K))ˣ :=
    ValuativeRel.isNontrivial_iff_nontrivial_units.mp
      (inferInstance : ValuativeRel.IsNontrivial (Q.adicCompletion K))
  set v := ValuativeRel.valuation (Q.adicCompletion K) with hv
  have hsv : ∀ y : Q.adicCompletion K,
      Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0) ↔
        (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)) y < 1 := by
    intro y
    rw [tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
    exact Valued.toNormedField.norm_lt_one_iff ..
  have hvlt : ∀ y : Q.adicCompletion K,
      Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0) ↔ v y < 1 :=
    fun y => tendsto_pow_nhds_zero_iff_vlt_one y
  have hiff : ∀ y : Q.adicCompletion K,
      (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)) y < 1 ↔ v y < 1 :=
    fun y => (hsv y).symm.trans (hvlt y)
  constructor
  · intro hx
    rcases lt_or_eq_of_le hx with h | h
    · exact le_of_lt ((hiff x).mp h)
    · have hxne : x ≠ 0 := by
        intro h0
        rw [h0, map_zero] at h
        exact one_ne_zero h.symm
      have hvu : (ValuativeRel.valuation (Q.adicCompletion K)) x ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr hxne
      have hinv : (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)) x⁻¹ = 1 := by
        rw [map_inv₀, h, inv_one]
      have hnot : ¬ ((ValuativeRel.valuation (Q.adicCompletion K)) x⁻¹ < 1) := by
        rw [← hiff x⁻¹]
        rw [hinv]
        exact lt_irrefl 1
      rw [map_inv₀] at hnot
      exact (one_le_inv₀ (zero_lt_iff.mpr hvu)).mp (not_lt.mp hnot)
  · intro hx
    rcases lt_or_eq_of_le hx with h | h
    · exact le_of_lt ((hiff x).mpr h)
    · have hxne : x ≠ 0 := by
        intro h0
        rw [h0, map_zero] at h
        exact one_ne_zero h.symm
      have hvu : (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)) x ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr hxne
      have hinv : (ValuativeRel.valuation (Q.adicCompletion K)) x⁻¹ = 1 := by
        rw [map_inv₀, h, inv_one]
      have hnot : ¬ ((Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)) x⁻¹ < 1) := by
        rw [hiff x⁻¹]
        rw [hinv]
        exact lt_irrefl 1
      rw [map_inv₀] at hnot
      exact (one_le_inv₀ (zero_lt_iff.mpr hvu)).mp (not_lt.mp hnot)

/-- Membership in the two descriptions of the ring of integers of a completion. -/
theorem mem_adicCompletionIntegers_iff {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : Q.adicCompletion K) :
    x ∈ Q.adicCompletionIntegers K ↔
      x ∈ (ValuativeRel.valuation (Q.adicCompletion K)).integer :=
  valued_v_le_one_iff Q x

/-! ## The arithmetic of a rational place -/

section Arithmetic

open IsDedekindDomain

variable (q : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

/-- The prime number attached to a place `q` of `ℚ` generates the ideal `q`. -/
theorem span_asIdeal_eq_singleton_natGenerator :
    q.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.primesEquiv q).1 :
      NumberField.RingOfIntegers ℚ)} := by
  set e := Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ) with he
  have h1 := Rat.HeightOneSpectrum.span_natGenerator q
  have hmap : Ideal.map e.symm (Ideal.map e q.asIdeal) = q.asIdeal := by
    rw [Ideal.map_symm, Ideal.comap_map_of_bijective e e.bijective]
  have h3 : Ideal.span {e.symm ((Rat.HeightOneSpectrum.natGenerator q : ℤ))} = q.asIdeal := by
    rw [← hmap, ← h1, Ideal.map_span]
    congr 1
    simp
  have h4 : e.symm ((Rat.HeightOneSpectrum.natGenerator q : ℤ))
      = ((Rat.HeightOneSpectrum.natGenerator q : ℕ) : NumberField.RingOfIntegers ℚ) := by
    rw [← map_natCast e (Rat.HeightOneSpectrum.natGenerator q)]
    exact e.symm_apply_apply _
  rw [h4] at h3
  exact h3.symm

/-- The `q`-adic valuation of the prime number attached to `q` is the generator of the value
group: it is a uniformiser of `𝓞 ℚ` at `q`. -/
theorem intValuation_natGenerator :
    q.intValuation (((Rat.HeightOneSpectrum.primesEquiv q).1 : ℕ) :
      NumberField.RingOfIntegers ℚ) = WithZero.exp (-1) :=
  IsDedekindDomain.HeightOneSpectrum.intValuation_singleton q (by
      intro h
      exact q.ne_bot (by rw [span_asIdeal_eq_singleton_natGenerator q, h]; simp))
    (span_asIdeal_eq_singleton_natGenerator q)

/-- The image of the prime number attached to `q` in the completion has `Valued.v`-valuation
`exp (-1)`. -/
theorem valued_v_natGenerator :
    (Valued.v (R := q.adicCompletion ℚ) (Γ₀ := Zstar0))
      ((((Rat.HeightOneSpectrum.primesEquiv q).1 : ℕ) : q.adicCompletionIntegers ℚ) :
        q.adicCompletion ℚ) = WithZero.exp (-1) := by
  have hcoe : ((((Rat.HeightOneSpectrum.primesEquiv q).1 : ℕ) :
        q.adicCompletionIntegers ℚ) : q.adicCompletion ℚ)
      = ((algebraMap (NumberField.RingOfIntegers ℚ) (q.adicCompletionIntegers ℚ)
          (((Rat.HeightOneSpectrum.primesEquiv q).1 : ℕ) : NumberField.RingOfIntegers ℚ) :
            q.adicCompletionIntegers ℚ) : q.adicCompletion ℚ) := by norm_num
  rw [hcoe, Commons.NumberTheory.NumberField.adicCompletion_valued_algebraMap (K := ℚ) q]
  exact intValuation_natGenerator q

/-- The rational prime of `q` lies in the maximal ideal of the completed ring of integers. -/
theorem natGenerator_mem_maximalIdeal :
    (((Rat.HeightOneSpectrum.primesEquiv q).1 : ℕ) : q.adicCompletionIntegers ℚ) ∈
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers ℚ) := by
  rw [← pow_one (IsLocalRing.maximalIdeal (q.adicCompletionIntegers ℚ)),
    Commons.NumberTheory.NumberField.mem_maximalIdeal_pow_iff_valued_le q 1
      (((Rat.HeightOneSpectrum.primesEquiv q).1 : ℕ) : q.adicCompletionIntegers ℚ),
    valued_v_natGenerator q]
  norm_num

/-- The rational prime of `q` does not lie in the square of the maximal ideal. -/
theorem natGenerator_notMem_maximalIdeal_sq :
    (((Rat.HeightOneSpectrum.primesEquiv q).1 : ℕ) : q.adicCompletionIntegers ℚ) ∉
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers ℚ) ^ 2 := by
  intro hcon
  rw [Commons.NumberTheory.NumberField.mem_maximalIdeal_pow_iff_valued_le q 2
      (((Rat.HeightOneSpectrum.primesEquiv q).1 : ℕ) : q.adicCompletionIntegers ℚ),
    valued_v_natGenerator q] at hcon
  have h := WithZero.exp_le_exp.mp hcon
  omega

/-- **The two descriptions of the ring of integers of the completion agree.**  The identity on the
underlying field is a ring isomorphism between `q.adicCompletionIntegers ℚ` and the integer ring of
the valuative relation used by the Lubin–Tate chapter. -/
noncomputable def valSubringEquiv :
    q.adicCompletionIntegers ℚ ≃+*
      ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer where
  toFun x := ⟨(x : q.adicCompletion ℚ), (mem_adicCompletionIntegers_iff q x.1).mp x.2⟩
  invFun x := ⟨(x : q.adicCompletion ℚ), (mem_adicCompletionIntegers_iff q x.1).mpr x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

@[simp] theorem valSubringEquiv_coe (x : q.adicCompletionIntegers ℚ) :
    ((valSubringEquiv q x : ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) :
      q.adicCompletion ℚ) = (x : q.adicCompletion ℚ) := rfl

/-- The ring isomorphism carries the maximal ideal of the completed integers onto the maximal
ideal of the integer ring of the valuative relation. -/
theorem map_valSubringEquiv_maximalIdeal :
    Ideal.map (valSubringEquiv q).toRingHom
        (IsLocalRing.maximalIdeal (q.adicCompletionIntegers ℚ)) =
      IsLocalRing.maximalIdeal
        ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective (I := IsLocalRing.maximalIdeal
      (q.adicCompletionIntegers ℚ)) (f := (valSubringEquiv q).toRingHom)
      (valSubringEquiv q).surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hy
    refine hx ?_
    simpa using IsUnit.map (valSubringEquiv q).symm.toRingHom hy
  · intro hy
    refine ⟨(valSubringEquiv q).symm y, ?_, by simp⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    intro hx
    exact hy (IsUnit.map (valSubringEquiv q).toRingHom hx)

/-- The residue cardinality of the completion of `ℚ` at `q` is the rational prime of `q`. -/
theorem residueCard_adicCompletion_rat :
    NK.LocalReciprocityLubinTate.residueCard (q.adicCompletion ℚ)
      = (Rat.HeightOneSpectrum.primesEquiv q).1 := by
  have h1 : NK.LocalReciprocityLubinTate.residueCard (q.adicCompletion ℚ)
      = Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers ℚ)) :=
    Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (valSubringEquiv q)).symm.toEquiv
  rw [h1]
  obtain ⟨e₁⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists q
  have h2 : Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers ℚ))
      = Nat.card ((NumberField.RingOfIntegers ℚ) ⧸ q.asIdeal) :=
    Nat.card_congr e₁.toEquiv
  rw [h2]
  refine Eq.trans (Nat.card_congr (Ideal.quotientEquiv q.asIdeal
    (Ideal.span {((Rat.HeightOneSpectrum.primesEquiv q).1 : ℤ)})
    (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ))
    (Rat.HeightOneSpectrum.span_natGenerator q)).toEquiv) ?_
  rw [Nat.card_congr
      (Int.quotientSpanNatEquivZMod ((Rat.HeightOneSpectrum.primesEquiv q).1)).toEquiv,
    Nat.card_zmod]

/-- **Cyclotomic irreducibility over the completion of `ℚ` at `q`.** -/
theorem irreducible_cyclotomic_residueCard_pow (n : ℕ) (hn : 1 ≤ n) :
    Irreducible (cyclotomic (NK.LocalReciprocityLubinTate.residueCard (q.adicCompletion ℚ) ^ n)
      (q.adicCompletion ℚ)) := by
  rw [residueCard_adicCompletion_rat q]
  rw [show (Rat.HeightOneSpectrum.primesEquiv q).1 ^ n
      = (Rat.HeightOneSpectrum.primesEquiv q).1 ^ ((n - 1) + 1) from by
    rw [Nat.sub_add_cancel hn]]
  exact irreducible_cyclotomic_prime_pow_of_isLocalRing
    (R := q.adicCompletionIntegers ℚ) (K := q.adicCompletion ℚ)
    (Rat.HeightOneSpectrum.prime_natGenerator q)
    (natGenerator_mem_maximalIdeal q) (natGenerator_notMem_maximalIdeal_sq q)

end Arithmetic

/-! ## The cyclotomic Artin symbol

The remaining ingredients are the quotient isomorphisms `𝒪 ⧸ 𝔪 ^ n ≃+* ZMod (l ^ n)` (in both
descriptions of the ring of integers) and the comparison of their values on the images of natural
numbers. -/

section Main

open IsDedekindDomain

variable (q : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

/-- The quotient `𝓞 ℚ ⧸ q ^ n` is the ring `ZMod (l ^ n)`, where `l` is the prime of `q`. -/
noncomputable def ringOfIntegersQuotEquivZMod (n : ℕ) :
    (NumberField.RingOfIntegers ℚ ⧸ q.asIdeal ^ n) ≃+*
      ZMod ((Rat.HeightOneSpectrum.primesEquiv q).1 ^ n) :=
  (Ideal.quotientEquiv (q.asIdeal ^ n)
      ((Ideal.span {((Rat.HeightOneSpectrum.primesEquiv q).1 : ℤ)}) ^ n)
      (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ))
      (by
        rw [Ideal.map_pow]
        congr 1
        exact Rat.HeightOneSpectrum.span_natGenerator q)).trans
    ((Ideal.quotEquivOfEq (R := ℤ)
        (by rw [Ideal.span_singleton_pow, Nat.cast_pow])).trans
      (Int.quotientSpanNatEquivZMod ((Rat.HeightOneSpectrum.primesEquiv q).1 ^ n)))

theorem ringOfIntegersQuotEquivZMod_mk_natCast (n m : ℕ) :
    ringOfIntegersQuotEquivZMod q n
        (Ideal.Quotient.mk _ (m : NumberField.RingOfIntegers ℚ)) =
      (m : ZMod ((Rat.HeightOneSpectrum.primesEquiv q).1 ^ n)) := by
  rw [ringOfIntegersQuotEquivZMod, RingEquiv.trans_apply, RingEquiv.trans_apply,
    Ideal.quotientEquiv_mk, map_natCast, Ideal.quotEquivOfEq_mk]
  simp [Int.quotientSpanNatEquivZMod]

/-- The reduction `O₂ ⧸ 𝔪₂ ^ n ≃+* ZMod (l ^ n)` of the completed ring of integers. -/
noncomputable def quotientEquivZMod (n : ℕ) :
    (q.adicCompletionIntegers ℚ ⧸
        (IsLocalRing.maximalIdeal (q.adicCompletionIntegers ℚ)) ^ n) ≃+*
      ZMod ((Rat.HeightOneSpectrum.primesEquiv q).1 ^ n) :=
  (Classical.choose
    (Commons.NumberTheory.NumberField.adicCompletionIntegers_quotient_equiv q n)).symm.trans
    (ringOfIntegersQuotEquivZMod q n)

theorem quotientEquivZMod_mk_natCast (n m : ℕ) :
    quotientEquivZMod q n (Ideal.Quotient.mk _ ((m : ℕ) : q.adicCompletionIntegers ℚ)) =
      (m : ZMod ((Rat.HeightOneSpectrum.primesEquiv q).1 ^ n)) := by
  have hspec := Classical.choose_spec
    (Commons.NumberTheory.NumberField.adicCompletionIntegers_quotient_equiv q n)
  rw [quotientEquivZMod, RingEquiv.trans_apply]
  have hcoe : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (q.adicCompletionIntegers ℚ) ^ n)
        ((m : ℕ) : q.adicCompletionIntegers ℚ))
      = (Classical.choose
          (Commons.NumberTheory.NumberField.adicCompletionIntegers_quotient_equiv q n))
          (Ideal.Quotient.mk _ ((m : ℕ) : NumberField.RingOfIntegers ℚ)) := by
    rw [hspec]
    congr 1
    norm_num
  rw [hcoe, RingEquiv.symm_apply_apply]
  exact ringOfIntegersQuotEquivZMod_mk_natCast q n m

/-- The ring isomorphism between the two quotients induced by `valSubringEquiv`. -/
noncomputable def quotientEquivO₂O₁ (n : ℕ) :
    (q.adicCompletionIntegers ℚ ⧸
        (IsLocalRing.maximalIdeal (q.adicCompletionIntegers ℚ)) ^ n) ≃+*
      (↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer ⧸
        (IsLocalRing.maximalIdeal
          ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) ^ n) :=
  Ideal.quotientEquiv ((IsLocalRing.maximalIdeal (q.adicCompletionIntegers ℚ)) ^ n)
    ((IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) ^ n)
    (valSubringEquiv q)
    (by
      rw [Ideal.map_pow]
      congr 1
      exact (map_valSubringEquiv_maximalIdeal q).symm)

@[simp] theorem quotientEquivO₂O₁_mk (n : ℕ) (x : q.adicCompletionIntegers ℚ) :
    quotientEquivO₂O₁ q n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (valSubringEquiv q x) :=
  Ideal.quotientEquiv_mk _ _ _ _ _

/-- The reduction `O₁ ⧸ 𝔪₁ ^ n ≃+* ZMod (l ^ n)`. -/
noncomputable def quotientEquivO₁ (n : ℕ) :
    (↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer ⧸
        (IsLocalRing.maximalIdeal
          ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) ^ n) ≃+*
      ZMod ((Rat.HeightOneSpectrum.primesEquiv q).1 ^ n) :=
  (quotientEquivO₂O₁ q n).symm.trans (quotientEquivZMod q n)

theorem quotientEquivO₁_mk (n : ℕ) (x : q.adicCompletionIntegers ℚ) :
    quotientEquivO₁ q n (Ideal.Quotient.mk _ (valSubringEquiv q x)) =
      quotientEquivZMod q n (Ideal.Quotient.mk _ x) := by
  rw [quotientEquivO₁, RingEquiv.trans_apply]
  have h : (quotientEquivO₂O₁ q n).symm (Ideal.Quotient.mk _ (valSubringEquiv q x)) =
      Ideal.Quotient.mk _ x := by
    rw [← quotientEquivO₂O₁_mk q n x, RingEquiv.symm_apply_apply]
  rw [h]

/-- The uniformiser used by the chapter is a uniformiser. -/
theorem isUniformizer_uniformizerUnit :
    NK.LocalReciprocityLubinTate.IsUniformizer (q.adicCompletion ℚ)
      ((NK.LocalReciprocityLubinTate.uniformizerUnit ℚ q : (q.adicCompletion ℚ)ˣ) :
        q.adicCompletion ℚ) := by
  have hspan₂ := Commons.RingTheory.Henselian.maximalIdeal_eq_span_uniformizer
    (R := NumberField.RingOfIntegers ℚ) (K := ℚ) q
  have hspan₁ : IsLocalRing.maximalIdeal
        ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer =
      Ideal.span {(valSubringEquiv q)
        (Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers ℚ)
          (K := ℚ) q)} := by
    rw [← map_valSubringEquiv_maximalIdeal q, hspan₂, Ideal.map_span]
    congr 1
    simp
  have h := Valuation.isUniformizer_of_maximalIdeal_eq_span
    (ValuativeRel.valuation (q.adicCompletion ℚ)) hspan₁
  have hcoe : (((valSubringEquiv q) (Commons.RingTheory.Henselian.uniformizer
        (R := NumberField.RingOfIntegers ℚ) (K := ℚ) q) :
        ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) : q.adicCompletion ℚ)
      = ((NK.LocalReciprocityLubinTate.uniformizerUnit ℚ q : (q.adicCompletion ℚ)ˣ) :
        q.adicCompletion ℚ) := by
    rw [valSubringEquiv_coe]
    rfl
  rwa [hcoe] at h

end Main

section MainTheorem

open IsDedekindDomain

/-- **The values of the local Artin map on the cyclotomic tower of `ℚ_l`.**  There is a surjective
homomorphism `Φ : ℚ_lˣ →* Gal(ℚ_l(ζ)/ℚ_l)` with kernel `⟨l⟩ · U ^ n` sending an integral unit `u`
congruent to `m` modulo `𝔪 ^ n` to the automorphism `ζ ↦ ζ ^ m`. -/
theorem cylArtinValues (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ)
    (hn : 1 ≤ n)
    {ζ : AlgebraicClosure (q.adicCompletion ℚ)}
    (hζ : IsPrimitiveRoot ζ (NK.LocalReciprocityLubinTate.residueCard (q.adicCompletion ℚ) ^ n)) :
    ∃ Φ : (q.adicCompletion ℚ)ˣ →*
        (↥(IntermediateField.adjoin (q.adicCompletion ℚ) ({ζ} : Set (AlgebraicClosure (q.adicCompletion ℚ))))
          ≃ₐ[(q.adicCompletion ℚ)]
         ↥(IntermediateField.adjoin (q.adicCompletion ℚ) ({ζ} : Set (AlgebraicClosure (q.adicCompletion ℚ))))),
      Function.Surjective Φ ∧
      MonoidHom.ker Φ = Subgroup.zpowers (NK.LocalReciprocityLubinTate.uniformizerUnit ℚ q) ⊔
        NK.LocalReciprocityLubinTate.higherUnits (q.adicCompletion ℚ) n ∧
      (∀ (u : (q.adicCompletionIntegers ℚ)ˣ) (m : ℕ),
        ((m : (q.adicCompletionIntegers ℚ) ⧸ (IsLocalRing.maximalIdeal (q.adicCompletionIntegers ℚ)) ^ n)
          = ((u : q.adicCompletionIntegers ℚ) :
              (q.adicCompletionIntegers ℚ) ⧸ (IsLocalRing.maximalIdeal (q.adicCompletionIntegers ℚ)) ^ n)) →
        (Φ (Units.map (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ)).toMonoidHom u))
            ⟨ζ, IntermediateField.mem_adjoin_simple_self _ _⟩ = ζ ^ m) := by
  classical
  set l : ℕ := (Rat.HeightOneSpectrum.primesEquiv q).1 with hl
  set L : IntermediateField (q.adicCompletion ℚ) (AlgebraicClosure (q.adicCompletion ℚ)) :=
    IntermediateField.adjoin (q.adicCompletion ℚ)
      ({ζ} : Set (AlgebraicClosure (q.adicCompletion ℚ))) with hL
  have hmem : ζ ∈ (L : Set (AlgebraicClosure (q.adicCompletion ℚ))) :=
    IntermediateField.mem_adjoin_simple_self _ _
  have hres : NK.LocalReciprocityLubinTate.residueCard (q.adicCompletion ℚ) = l := by
    rw [hl]; exact residueCard_adicCompletion_rat q
  have hζl : IsPrimitiveRoot ζ (l ^ n) := by rw [← hres]; exact hζ
  have hlne : l ≠ 0 := by rw [hl]; exact (Rat.HeightOneSpectrum.prime_natGenerator q).ne_zero
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero n hlne⟩
  have hirr : Irreducible (cyclotomic (l ^ n) (q.adicCompletion ℚ)) := by
    rw [hl]
    rw [show (Rat.HeightOneSpectrum.primesEquiv q).1 ^ n
        = (Rat.HeightOneSpectrum.primesEquiv q).1 ^ ((n - 1) + 1) from by
      rw [Nat.sub_add_cancel hn]]
    exact irreducible_cyclotomic_prime_pow_of_isLocalRing (R := q.adicCompletionIntegers ℚ)
      (K := q.adicCompletion ℚ) (Rat.HeightOneSpectrum.prime_natGenerator q)
      (natGenerator_mem_maximalIdeal q) (natGenerator_notMem_maximalIdeal_sq q)
  have hcyc : IsCyclotomicExtension {l ^ n} (q.adicCompletion ℚ) ↥L :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (q.adicCompletion ℚ) hζl
  let eGal : (↥L ≃ₐ[(q.adicCompletion ℚ)] ↥L) ≃* (ZMod (l ^ n))ˣ :=
    IsCyclotomicExtension.autEquivPow ↥L hirr
  -- the automorphism group of `L` as the quotient of the units of `O₁`
  let Ω := (↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer ⧸
      (IsLocalRing.maximalIdeal
        ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) ^ n)ˣ
  let mkO₁ : (↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer)ˣ →* Ω :=
    Units.map (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) ^ n)).toMonoidHom
  let e : Ω ≃* (↥L ≃ₐ[(q.adicCompletion ℚ)] ↥L) :=
    (Units.mapEquiv (quotientEquivO₁ q n).toMulEquiv).trans eGal.symm
  let ψ : (↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer)ˣ →*
      (↥L ≃ₐ[(q.adicCompletion ℚ)] ↥L) := e.toMonoidHom.comp mkO₁
  let ρ : (q.adicCompletion ℚ)ˣ →* (↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer)ˣ :=
    NK.LocalReciprocityLubinTate.LubinTate.unitPartHom
      (NK.LocalReciprocityLubinTate.uniformizerUnit ℚ q) (isUniformizer_uniformizerUnit q)
  let Φ : (q.adicCompletion ℚ)ˣ →* (↥L ≃ₐ[(q.adicCompletion ℚ)] ↥L) := ψ.comp ρ
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro σ
    obtain ⟨a, rfl⟩ := e.surjective σ
    obtain ⟨b, rfl⟩ :=
      NK.LocalReciprocityLubinTate.LubinTate.surjective_units_map_quot_maximalIdeal_pow
        (F := q.adicCompletion ℚ) n hn a
    obtain ⟨x, rfl⟩ := NK.LocalReciprocityLubinTate.LubinTate.unitPartHom_surjective
      (NK.LocalReciprocityLubinTate.uniformizerUnit ℚ q) (isUniformizer_uniformizerUnit q) b
    exact ⟨x, rfl⟩
  · have hkerψ : ψ.ker = NK.LocalReciprocityLubinTate.principalUnits (q.adicCompletion ℚ) n := by
      ext a
      rw [MonoidHom.mem_ker]
      show e (mkO₁ a) = 1 ↔ a ∈ NK.LocalReciprocityLubinTate.principalUnits (q.adicCompletion ℚ) n
      rw [MulEquiv.map_eq_one_iff, NK.LocalReciprocityLubinTate.mem_principalUnits_iff,
        Units.ext_iff, Units.coe_map, Units.val_one]
      show ((Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) ^ n)
          (a : ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) :
            ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer ⧸
              (IsLocalRing.maximalIdeal
                ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) ^ n) = 1 ↔
        (a : ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) - 1 ∈
          (IsLocalRing.maximalIdeal
            ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) ^ n)
      rw [← map_one (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) ^ n)),
        Ideal.Quotient.eq]
    ext x
    rw [MonoidHom.mem_ker]
    have h1 : Φ x = 1 ↔ ρ x ∈ NK.LocalReciprocityLubinTate.principalUnits
        (q.adicCompletion ℚ) n := by
      rw [show Φ x = ψ (ρ x) from rfl, ← MonoidHom.mem_ker (f := ψ), hkerψ]
    rw [h1,
      show NK.LocalReciprocityLubinTate.higherUnits (q.adicCompletion ℚ) n
          = (NK.LocalReciprocityLubinTate.principalUnits (q.adicCompletion ℚ) n).map
            (NK.LocalReciprocityLubinTate.Units.unitsIncl (q.adicCompletion ℚ)) from rfl]
    constructor
    · intro hu
      rw [Subgroup.mem_sup]
      refine ⟨(NK.LocalReciprocityLubinTate.Units.unitsIncl (q.adicCompletion ℚ) (ρ x))⁻¹ * x,
        NK.LocalReciprocityLubinTate.LubinTate.unitPartHom_spec
          (NK.LocalReciprocityLubinTate.uniformizerUnit ℚ q)
          (isUniformizer_uniformizerUnit q) x,
        NK.LocalReciprocityLubinTate.Units.unitsIncl (q.adicCompletion ℚ) (ρ x), ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem _ hu
      · rw [mul_assoc, mul_comm x, inv_mul_cancel_left]
    · intro hx
      rw [Subgroup.mem_sup] at hx
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      have ha1 : ρ a = 1 := by
        rw [← MonoidHom.mem_ker,
          NK.LocalReciprocityLubinTate.LubinTate.unitPartHom_ker
            (NK.LocalReciprocityLubinTate.uniformizerUnit ℚ q) (isUniformizer_uniformizerUnit q)]
        exact ha
      rw [Subgroup.mem_map] at hb
      obtain ⟨u, hu, rfl⟩ := hb
      have hρx : ρ x = u := by
        rw [← hab, map_mul, ha1, NK.LocalReciprocityLubinTate.LubinTate.unitPartHom_unitsIncl]
        exact one_mul u
      rw [hρx]; exact hu
  · intro u m hum
    -- the image of `u` in `Kˣ` seen from `O₁ˣ`
    have h1 : Units.map (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ)).toMonoidHom u
        = NK.LocalReciprocityLubinTate.Units.unitsIncl (q.adicCompletion ℚ)
            (Units.mapEquiv (valSubringEquiv q).toMulEquiv u) := by
      ext
      simp [NK.LocalReciprocityLubinTate.Units.unitsIncl]
    -- the value of `Φ` at `u`, in terms of the class of `valSubringEquiv u`
    have h2 : Φ (Units.map (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ)).toMonoidHom u)
        = eGal.symm (Units.mapEquiv (quotientEquivO₁ q n).toMulEquiv
            (mkO₁ (Units.mapEquiv (valSubringEquiv q).toMulEquiv u))) := by
      rw [show Φ (Units.map (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ)).toMonoidHom u)
          = ψ (ρ (Units.map (algebraMap (q.adicCompletionIntegers ℚ)
              (q.adicCompletion ℚ)).toMonoidHom u)) from rfl, h1]
      rw [show ρ (NK.LocalReciprocityLubinTate.Units.unitsIncl (q.adicCompletion ℚ)
            (Units.mapEquiv (valSubringEquiv q).toMulEquiv u))
          = Units.mapEquiv (valSubringEquiv q).toMulEquiv u from
        NK.LocalReciprocityLubinTate.LubinTate.unitPartHom_unitsIncl _ _ _]
      rfl
    -- the exponent attached to `u`
    set t : (ZMod (l ^ n))ˣ := eGal (Φ (Units.map (algebraMap (q.adicCompletionIntegers ℚ)
      (q.adicCompletion ℚ)).toMonoidHom u)) with ht
    have ht' : (t : ZMod (l ^ n))
        = quotientEquivZMod q n (Ideal.Quotient.mk _ ((m : ℕ) : q.adicCompletionIntegers ℚ)) := by
      have hcoe : ((mkO₁ (Units.mapEquiv (valSubringEquiv q).toMulEquiv u) : Ω) :
            (↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer ⧸
              (IsLocalRing.maximalIdeal
                ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) ^ n)) =
          Ideal.Quotient.mk _ ((valSubringEquiv q) ((u : q.adicCompletionIntegers ℚ))) := by
        rw [Units.coe_map, Units.coe_mapEquiv]
        rfl
      rw [ht, h2, MulEquiv.apply_symm_apply, Units.coe_mapEquiv, hcoe]
      rw [show (quotientEquivO₁ q n).toMulEquiv
            ((Ideal.Quotient.mk _ (((valSubringEquiv q) ((u : q.adicCompletionIntegers ℚ))))) :
              ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer ⧸
                (IsLocalRing.maximalIdeal
                  ↥(ValuativeRel.valuation (q.adicCompletion ℚ)).integer) ^ n) =
          (quotientEquivO₁ q n)
            (Ideal.Quotient.mk _ (((valSubringEquiv q) ((u : q.adicCompletionIntegers ℚ))))) from rfl]
      rw [quotientEquivO₁_mk q n (u : q.adicCompletionIntegers ℚ)]
      congr 1
      rw [map_natCast]
      exact hum.symm
    have htm : (t : ZMod (l ^ n)) = (m : ZMod (l ^ n)) := by
      rw [ht', quotientEquivZMod_mk_natCast]
    have hval : (((t : ZMod (l ^ n))).val : ZMod (l ^ n)) = (m : ZMod (l ^ n)) := by
      rw [ZMod.natCast_zmod_val]
      exact htm
    -- the action on the canonical root
    have hzeta : IsCyclotomicExtension.zeta (l ^ n) (q.adicCompletion ℚ) ↥L ^ ((t : ZMod (l ^ n))).val
        = Φ (Units.map (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ)).toMonoidHom u)
            (IsCyclotomicExtension.zeta (l ^ n) (q.adicCompletion ℚ) ↥L) := by
      have ht2 : (IsCyclotomicExtension.zeta_spec (l ^ n) (q.adicCompletion ℚ) ↥L).autToPow
            (q.adicCompletion ℚ)
            (Φ (Units.map (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ)).toMonoidHom u))
          = t := by
        rw [ht]
        exact (IsCyclotomicExtension.autEquivPow_apply ↥L hirr _).symm
      have h := (IsCyclotomicExtension.zeta_spec (l ^ n) (q.adicCompletion ℚ) ↥L).autToPow_spec
        (q.adicCompletion ℚ)
        (Φ (Units.map (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ)).toMonoidHom u))
      rwa [ht2] at h
    -- `ζ` is a power of the canonical root
    have hζL : IsPrimitiveRoot (⟨ζ, hmem⟩ : ↥L) (l ^ n) :=
      (IsPrimitiveRoot.coe_submonoidClass_iff (N := L) (ζ := (⟨ζ, hmem⟩ : ↥L))).mp (by
        show IsPrimitiveRoot ζ (l ^ n)
        exact hζl)
    obtain ⟨c, -, hc⟩ :=
      (IsCyclotomicExtension.zeta_spec (l ^ n) (q.adicCompletion ℚ) ↥L).eq_pow_of_pow_eq_one
        hζL.pow_eq_one
    -- the action on `ζ`
    have hσ : Φ (Units.map (algebraMap (q.adicCompletionIntegers ℚ)
          (q.adicCompletion ℚ)).toMonoidHom u) (⟨ζ, hmem⟩ : ↥L) = (⟨ζ, hmem⟩ : ↥L) ^ ((t : ZMod (l ^ n))).val := by
      calc Φ _ (⟨ζ, hmem⟩ : ↥L)
          = Φ _ ((IsCyclotomicExtension.zeta (l ^ n) (q.adicCompletion ℚ) ↥L) ^ c) := by
            rw [← hc]
        _ = (Φ _ (IsCyclotomicExtension.zeta (l ^ n) (q.adicCompletion ℚ) ↥L)) ^ c := by rw [map_pow]
        _ = ((IsCyclotomicExtension.zeta (l ^ n) (q.adicCompletion ℚ) ↥L) ^ ((t : ZMod (l ^ n))).val) ^ c := by
            rw [← hzeta]
        _ = ((IsCyclotomicExtension.zeta (l ^ n) (q.adicCompletion ℚ) ↥L) ^ c) ^ ((t : ZMod (l ^ n))).val := by
            rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ = (⟨ζ, hmem⟩ : ↥L) ^ ((t : ZMod (l ^ n))).val := by rw [hc]
    have hfinal : ζ ^ ((t : ZMod (l ^ n))).val = ζ ^ m := by
      set a : ℕ := ((t : ZMod (l ^ n))).val with ha
      have ha_lt : a < l ^ n := by rw [ha]; exact ZMod.val_lt _
      have hma : m % (l ^ n) = a := by
        rw [← (ZMod.natCast_eq_natCast_iff a m (l ^ n)).mp hval, Nat.mod_eq_of_lt ha_lt]
      conv_rhs => rw [← Nat.mod_add_div m (l ^ n), hma]
      rw [pow_add, pow_mul, hζl.pow_eq_one, one_pow, mul_one]
    rw [show (Φ (Units.map (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ)).toMonoidHom u))
          ⟨ζ, IntermediateField.mem_adjoin_simple_self _ _⟩
        = (Φ (Units.map (algebraMap (q.adicCompletionIntegers ℚ)
            (q.adicCompletion ℚ)).toMonoidHom u) (⟨ζ, hmem⟩ : ↥L) : AlgebraicClosure (q.adicCompletion ℚ))
        from rfl]
    rw [hσ, SubmonoidClass.coe_pow]
    exact hfinal.trans (by rfl)

end MainTheorem

end

end NK.NUV2.LC
