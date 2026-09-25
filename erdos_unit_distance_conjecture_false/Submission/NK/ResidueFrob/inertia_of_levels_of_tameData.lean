import Mathlib
import Submission.NK.ResidueFrob.LevelOfLocal
import Submission.NK.ResidueFrob.Inertia

namespace NK.ResidueFrob

open scoped Pointwise Classical NumberField
open IntermediateField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **A finite normal intermediate level containing a given integral element.** -/
private theorem exists_normal_level_of_isIntegral_aux {x : K'} (hx : IsIntegral K x) :
    ∃ (L : IntermediateField K K'), FiniteDimensional K L ∧ Normal K L ∧ NumberField ↥L ∧ x ∈ L := by
  haveI : Normal K K' := inferInstance
  let L₀ : IntermediateField K K' := IntermediateField.adjoin K {x}
  haveI : Nonempty (L₀ →ₐ[K] K') := ⟨L₀.val⟩
  haveI hL₀ : FiniteDimensional K L₀ := IntermediateField.adjoin.finiteDimensional hx
  let L : IntermediateField K K' := IntermediateField.normalClosure K L₀ K'
  haveI hLfin : FiniteDimensional K L := normalClosure.is_finiteDimensional K L₀ K'
  haveI hLnorm : Normal K L := inferInstance
  refine ⟨L, hLfin, hLnorm, Commons.NumberTheory.NumberField.numberField_of_intermediateField L, ?_⟩
  exact IntermediateField.le_normalClosure L₀
    (IntermediateField.subset_adjoin K ({x} : Set K') (Set.mem_singleton x))

/-- **A finite domain whose cardinality is a power of `p` has characteristic `p`**, so an integer
not divisible by `p` is nonzero in it. -/
theorem cast_ne_zero_of_natCard_eq_prime_pow {R : Type*} [CommRing R] [IsDomain R] [Fintype R]
    {p f n : ℕ} (hp : p.Prime) (hcard : Nat.card R = p ^ f) (hn : ¬ p ∣ n) : (n : R) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP R p := charP_of_card_eq_prime_pow (by rwa [Nat.card_eq_fintype_card] at hcard)
  exact fun h => hn ((CharP.cast_eq_zero_iff R p n).mp h)

/--
STRATEGY (for the prover).

Step 1 (a finite normal level containing a given root of unity).  Show that for `ζ : K'` there is
`L : IntermediateField K K'` with `FiniteDimensional K L`, `Normal K L`, `NumberField ↥L` and
`ζ ∈ L`: take `L := ⨆ (σ : Gal(K'/K)), K⟮σ ζ⟯`, the compositum of the conjugates of `K⟮ζ⟯` inside
`K'`; it is normal (it is stable under `Gal(K'/K)`), finite-dimensional (use that `K⟮ζ⟯` is
finite-dimensional and that its stabiliser has finite index, or that the orbit of `ζ` is finite
because `minpoly K ζ` is separable and `K(ζ)` is finite-dimensional over `K`) and a number field
(`Commons.NumberTheory.NumberField.numberField_of_intermediateField`).

Step 2 (reduction to the explicit identification).  Apply
`NK.ResidueFrob.mem_inertiaSubgroup_of_fixes_rootsOfUnity A hT hg`, which reduces the goal to
`hfix : ∀ ζ : K', (∃ n, ¬ p ∣ n ∧ IsPrimitiveRoot ζ n) → g ζ = ζ`.  So fix `ζ`, a primitive `n`-th
root of unity with `p ∤ n`.

Step 3 (the key congruence).  Let `L` be as in Step 1, so `ζ ∈ L` and `ζ` is a unit of `𝓞 L`.  By
`hgtriv L`, `g|_L` acts trivially on `𝓞 L ⧸ P_L`, so
`galRestrict ... (AlgEquiv.restrictNormalHom L g) ζ - ζ ∈ P_L.asIdeal`.  Let
`w := g ζ * ζ⁻¹ = (galRestrict ...) ζ * ζ⁻¹`; then `w - 1 ∈ P_L.asIdeal`.

Step 4 (the local-ring argument).  Show `w = 1`.  Let `C = placeCompletion A.1`,
`R = placeCompletionIntegers A.1`, and map `w` into `R` by `placeCompletionCoe A.1` (a root of
unity has valuation `1`, so it lies in `R`, and it is a unit there).  Its residue in
`F̄ = IsLocalRing.ResidueField ↥R` is `1`: use `NK.NeukirchUchida.comap_placeCompletionIntegers`
(which identifies the contraction of the maximal ideal of `R` to `K'` with the maximal ideal of
`A.1`) and `NK.Reconstruct.primeOfLevel_spec`.  Since `w ^ n = 1` and `n` is a unit of `R`,
`NK.ResidueFrob.rootOfUnity_eq_one_of_residue_eq_one` gives `w = 1`.
For `IsUnit (n : R)`: the ring hom `𝓞 K → R → F̄` has kernel `𝔭` (`primeOf_spec` +
`comap_placeCompletionIntegers`), so `F̄` contains a copy of the finite field `𝓞 K ⧸ 𝔭`, whose
cardinality is `q` (`hq`) and which satisfies `q = p ^ f` with `f ≠ 0` (`TameData.q_eq`); a finite
field of cardinality `p ^ f` has characteristic `p`, so `(n : 𝓞K ⧸ 𝔭) ≠ 0` for `p ∤ n`, hence
`(n : F̄) ≠ 0`, hence `n` is a unit of `R` (`IsLocalRing.residue_ne_zero_iff_isUnit`).

Finally `g ζ = w * ζ = ζ`, which is Step 2's requirement.

(The formalised proof below runs the same argument entirely inside `𝓞 L`: the congruence
`w - 1 ∈ P_L` is extracted from `hgtriv L` at the element `z ∈ 𝓞 L` corresponding to `ζ`, and the
local-ring step is replaced by the domain argument in `𝓞 L` — if `w ≠ 1` then the geometric sum
`S = ∑_{i<n} w^i` vanishes, while `S ≡ n (mod P_L)` with `n ∉ P_L` by
`cast_ne_zero_of_natCard_eq_prime_pow` applied to the residue field `𝓞 K ⧸ 𝔭` and
`primeOfLevel_liesOver`.)
-/
theorem inertia_of_levels_of_tameData {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') {p q : ℕ}
    (hT : NK.LocalTame.TameData p q (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A))
    (hq : ResidueCardMatches A q)
    (g : Gal(K'/K))
    (hgtriv : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L],
      NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A L g)
    (hg : g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1) :
    NK.FrobeniusBridge.localGaloisEquiv A ⟨g, hg⟩ ∈
      NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField A)
        (K' := NK.FrobeniusBridge.localClosure A) p := by
  classical
  refine mem_inertiaSubgroup_of_fixes_rootsOfUnity A hT hg ?_
  intro ζ hζ
  obtain ⟨n, hpn, hζprim⟩ := hζ
  -- `p ∤ n` forces `n ≠ 0`
  have hn0 : n ≠ 0 := fun h0 => hpn (h0 ▸ dvd_zero p)
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  -- ## Step 1: a finite normal level containing `ζ`
  have hζint : IsIntegral K ζ :=
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn0, by
      simp [hζprim.pow_eq_one]⟩
  obtain ⟨L, hLfin, hLnorm, hLnf, hζL⟩ := exists_normal_level_of_isIntegral_aux hζint
  haveI : FiniteDimensional K L := hLfin
  haveI : Normal K L := hLnorm
  haveI : NumberField ↥L := hLnf
  -- the prime of the level below the place `A`
  set P : NK.Chebotarev.PrimeIdeal ↥L :=
    NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L) with hPdef
  -- ## Step 2: the element `z ∈ 𝓞 L` attached to `ζ`, and `w = g ζ / ζ`
  have hζLpow : (⟨ζ, hζL⟩ : ↥L) ^ n = 1 := by
    apply (algebraMap ↥L K').injective
    rw [map_pow, map_one, IntermediateField.algebraMap_apply]
    exact hζprim.pow_eq_one
  have hζintZ : IsIntegral ℤ (⟨ζ, hζL⟩ : ↥L) :=
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn0, by
      simp [hζLpow]⟩
  set z : 𝓞 ↥L := ⟨⟨ζ, hζL⟩, hζintZ⟩ with hzdef
  have hzcoe : (algebraMap (𝓞 ↥L) ↥L) z = (⟨ζ, hζL⟩ : ↥L) := by
    rw [hzdef]; rfl
  have hzn : z ^ n = 1 := by
    apply NumberField.RingOfIntegers.ext
    simpa [hzcoe] using hζLpow
  -- the image of `z` under the restriction of `g`
  set z' : 𝓞 ↥L := galRestrict (𝓞 K) K ↥L (𝓞 ↥L) (AlgEquiv.restrictNormalHom L g) z with hz'def
  set w : 𝓞 ↥L := z' * z ^ (n - 1) with hwdef
  -- ## Step 3: the congruence `w - 1 ∈ P`
  have hgal : z' - z ∈ P.asIdeal := by
    have h := hgtriv L z
    rw [← hz'def] at h
    rwa [← hPdef] at h
  have hzmul : z * z ^ (n - 1) = 1 := by
    rw [← pow_succ' z (n - 1), Nat.sub_add_cancel hn1, hzn]
  have hz'pow : z' ^ n = 1 := by
    have h : (galRestrict (𝓞 K) K ↥L (𝓞 ↥L) (AlgEquiv.restrictNormalHom L g)) (z ^ n) =
        ((galRestrict (𝓞 K) K ↥L (𝓞 ↥L) (AlgEquiv.restrictNormalHom L g)) z) ^ n :=
      map_pow _ z n
    rw [hzn, map_one] at h
    rw [hz'def]
    exact h.symm
  have hwpow : w ^ n = 1 := by
    rw [hwdef, mul_pow, hz'pow, one_mul, ← pow_mul, mul_comm (n - 1) n, pow_mul, hzn, one_pow]
  have hwsub : w - 1 ∈ P.asIdeal := by
    rw [hwdef]
    have h1 : z' * z ^ (n - 1) - 1 = (z' - z) * z ^ (n - 1) := by
      rw [sub_mul, hzmul]
    rw [h1]
    exact Ideal.mul_mem_right (z ^ (n - 1)) P.asIdeal hgal
  -- ## Step 4: `n` is invertible modulo the prime of the level
  have hnP : ((n : ℕ) : 𝓞 ↥L) ∉ P.asIdeal := by
    obtain ⟨f, hf, hqf⟩ := hT.structure_input.q_eq
    have hq' : q = Nat.card (𝓞 K ⧸ (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) := hq
    have hcardF : Nat.card (𝓞 K ⧸ (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal)
        = p ^ f := by rw [← hq', hqf]
    haveI : Finite (𝓞 K ⧸ (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
        (Submission.NeukirchUchida.primeOf A.1 A.2)
    haveI : Fintype (𝓞 K ⧸ (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) :=
      Fintype.ofFinite _
    have hn0F : ((n : ℕ) : 𝓞 K ⧸ (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) ≠ 0 :=
      cast_ne_zero_of_natCard_eq_prime_pow hT.structure_input.hp hcardF hpn
    have hn𝔭 : ((n : ℕ) : 𝓞 K) ∉ (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal := by
      intro hmem
      refine hn0F ?_
      rw [← map_natCast (Ideal.Quotient.mk (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) n]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    intro hmem
    refine hn𝔭 ?_
    rw [(primeOfLevel_liesOver A L).over, Ideal.mem_under, map_natCast]
    exact hmem
  -- ## Step 5: the domain argument, giving `w = 1`
  have hw1 : w = 1 := by
    by_contra hne
    have hsub : w - 1 ≠ 0 := sub_ne_zero.mpr hne
    have hgeom : (w - 1) * (∑ i ∈ Finset.range n, w ^ i) = 0 := by
      rw [mul_comm, geom_sum_mul, hwpow, sub_self]
    have hS0 : (∑ i ∈ Finset.range n, w ^ i) = 0 := by
      rcases mul_eq_zero.mp hgeom with h | h
      · exact absurd h hsub
      · exact h
    have hSsub : (∑ i ∈ Finset.range n, w ^ i) - (n : 𝓞 ↥L) ∈ P.asIdeal := by
      have h1 : (∑ i ∈ Finset.range n, w ^ i) - (n : 𝓞 ↥L)
          = ∑ i ∈ Finset.range n, (w ^ i - 1) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [h1]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [show w ^ i - 1 = (∑ j ∈ Finset.range i, w ^ j) * (w - 1) from
        (geom_sum_mul w i).symm]
      exact Ideal.mul_mem_left P.asIdeal _ hwsub
    have hmem : ((n : ℕ) : 𝓞 ↥L) ∈ P.asIdeal := by
      have hneg : -((n : ℕ) : 𝓞 ↥L) ∈ P.asIdeal := by
        rw [hS0] at hSsub
        simpa using hSsub
      simpa using P.asIdeal.neg_mem hneg
    exact hnP hmem
  -- ## Step 6: reading `w = 1` back
  have hzeq : z' = z := by
    calc z' = z' * 1 := (mul_one z').symm
      _ = z' * (z ^ (n - 1) * z) := by
        rw [show z ^ (n - 1) * z = 1 from by
          rw [← pow_succ, Nat.sub_add_cancel hn1, hzn]]
      _ = (z' * z ^ (n - 1)) * z := (mul_assoc _ _ _).symm
      _ = 1 * z := by rw [← hwdef, hw1]
      _ = z := one_mul z
  have hL_eq : (AlgEquiv.restrictNormalHom L g) (⟨ζ, hζL⟩ : ↥L) = ⟨ζ, hζL⟩ := by
    have h1 : (algebraMap (𝓞 ↥L) ↥L) z' = (algebraMap (𝓞 ↥L) ↥L) z := by rw [hzeq]
    rw [hz'def] at h1
    rw [algebraMap_galRestrict_apply] at h1
    rwa [hzcoe] at h1
  have hfin : g ζ = ζ := by
    have h2 := congrArg (fun x : ↥L => (algebraMap ↥L K') x) hL_eq
    rw [Submission.NeukirchUchida.Local.restrictNormalHom_apply_algebraMap] at h2
    simpa [IntermediateField.algebraMap_apply] using h2
  exact hfin

end NK.ResidueFrob
