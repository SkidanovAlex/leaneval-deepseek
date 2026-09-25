import Mathlib
import Submission.Work.CFT.Kummer.Defs

/-!
# The `𝔽_p`-dimension of `𝒪_Kˣ/(𝒪_Kˣ)^p`

This file proves

`Module.finrank (ZMod p) (unitsModPow K p) = NumberField.Units.rank K + deltaK K p`

for a number field `K` and a prime `p`, i.e. the elementary computation of
`dim_{𝔽_p} 𝒪_Kˣ/(𝒪_Kˣ)^p` from Dirichlet's unit theorem: by Dirichlet,
`𝒪_Kˣ ≅ μ(K) × ℤ^r` with `r = NumberField.Units.rank K` and `μ(K)` the (finite, cyclic)
torsion subgroup; modding out by `p`-th powers gives
`μ(K)/μ(K)^p × (ℤ/p)^r`, whose dimension is `r + δ_{K,p}` with
`δ_{K,p} = 1` iff `K` contains a primitive `p`-th root of unity.

## Main result

* `Work.CFT.Kummer.finrank_unitsModPow` — the dimension formula above.

## Implementation

The proof is a cardinality computation `Nat.card (𝒪_Kˣ/(𝒪_Kˣ)^p) = p ^ (r + δ)`:

* `unitsMulEquiv` is the isomorphism `μ(K) × ℤ^r ≃* 𝒪_Kˣ` obtained from
  `NumberField.Units.exist_unique_eq_mul_prod` (the uniqueness part of Dirichlet's theorem);
* `map_pthPowerSubgroup_mulEquiv` and `pthPowerSubgroup_prod` transport the quotient by
  `p`-th powers through products;
* `card_torsionPowKer` computes the cardinality of the `p`-torsion of the roots of unity
  (via `rootsOfUnity`, cyclicity and Cauchy / Lagrange);
* `card_pi_multInt_quotient` computes the cardinality of `(ℤ^r)/(pℤ^r)`;
* `card_quotient_powMonoidHom` is the elementary finite-group identity
  `|G/G^p| = |G[p]|`;
* finally `Module.card_eq_pow_finrank` converts `Nat.card` to `Module.finrank`.

-/

open NumberField

noncomputable section

set_option linter.style.haveILetI false

namespace Work.CFT.Kummer

/-! ## The Dirichlet structure of the unit group -/

/-- The monoid homomorphism `μ(K) × ℤ^r → 𝒪_Kˣ` induced by Dirichlet's unit theorem:
`(ζ, f) ↦ ζ * ∏ i, u_i ^ (f i)` where `u` is the fundamental system of units `fundSystem K`. -/
noncomputable def unitsStructHom (K : Type*) [Field K] [NumberField K] :
    (NumberField.Units.torsion K × (Fin (NumberField.Units.rank K) → Multiplicative ℤ)) →*
      (𝓞 K)ˣ where
  toFun ζf := (ζf.1 : (𝓞 K)ˣ) * ∏ i, NumberField.Units.fundSystem K i ^ (ζf.2 i).toAdd
  map_one' := by simp
  map_mul' ζf ηf := by
    obtain ⟨ζ, f⟩ := ζf
    obtain ⟨η, g⟩ := ηf
    simp only [Prod.mk_mul_mk, Pi.mul_apply, Subgroup.coe_mul]
    rw [show (∏ i, NumberField.Units.fundSystem K i ^ ((f i * g i).toAdd))
          = ∏ i, (NumberField.Units.fundSystem K i ^ (f i).toAdd *
              NumberField.Units.fundSystem K i ^ (g i).toAdd) by
        apply Finset.prod_congr rfl
        intro i _; rw [toAdd_mul, zpow_add]]
    rw [Finset.prod_mul_distrib, mul_mul_mul_comm]

/-- `unitsStructHom K` is a bijection: this is exactly the uniqueness statement of
`NumberField.Units.exist_unique_eq_mul_prod` (Dirichlet's unit theorem). -/
theorem unitsStructHom_bijective (K : Type*) [Field K] [NumberField K] :
    Function.Bijective (unitsStructHom K) := by
  constructor
  · intro a b hab
    obtain ⟨e₀, h0, huniq⟩ :=
      NumberField.Units.exist_unique_eq_mul_prod K (unitsStructHom K a)
    have ha : (unitsStructHom K a) =
        (↑a.1 * ∏ i, NumberField.Units.fundSystem K i ^ (a.2 i).toAdd) := rfl
    have hb : (unitsStructHom K b) =
        (↑b.1 * ∏ i, NumberField.Units.fundSystem K i ^ (b.2 i).toAdd) := rfl
    have hEq : (a.1, fun i => (a.2 i).toAdd) = (b.1, fun i => (b.2 i).toAdd) :=
      (huniq _ (by rw [ha])).trans ((huniq _ (by rw [hab, hb])).symm)
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    simp only [Prod.mk.injEq] at hEq ⊢
    refine ⟨hEq.1, ?_⟩
    funext i
    exact Multiplicative.ofAdd.injective (congrFun hEq.2 i)
  · intro x
    obtain ⟨⟨ζ, f⟩, hf, -⟩ := NumberField.Units.exist_unique_eq_mul_prod K x
    exact ⟨⟨ζ, fun i => Multiplicative.ofAdd (f i)⟩, hf.symm⟩

/-- **Dirichlet's unit theorem** in the form needed below: the group of units of `𝒪_K` is the
product of the torsion subgroup (roots of unity) and a free abelian group of rank
`NumberField.Units.rank K`. -/
noncomputable def unitsMulEquiv (K : Type*) [Field K] [NumberField K] :
    (NumberField.Units.torsion K × (Fin (NumberField.Units.rank K) → Multiplicative ℤ)) ≃*
      (𝓞 K)ˣ :=
  MulEquiv.ofBijective _ (unitsStructHom_bijective K)

/-! ## Transporting the `p`-th power subgroup through isomorphisms and products -/

/-- A group isomorphism carries `p`-th powers to `p`-th powers. -/
lemma map_pthPowerSubgroup_mulEquiv {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (p : ℕ) :
    Subgroup.map (e : G →* H) (pthPowerSubgroup G p) = pthPowerSubgroup H p := by
  rw [pthPowerSubgroup, MonoidHom.map_range]
  have hcomp : (e : G →* H).comp (powMonoidHom p) = (powMonoidHom p).comp (e : G →* H) := by
    ext x; simp [map_pow]
  rw [hcomp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top,
    ← pthPowerSubgroup]

/-- The `p`-th powers in a product are the products of the `p`-th powers. -/
lemma pthPowerSubgroup_prod {G H : Type*} [CommGroup G] [CommGroup H] (p : ℕ) :
    pthPowerSubgroup (G × H) p = (pthPowerSubgroup G p).prod (pthPowerSubgroup H p) := by
  ext x
  simp only [pthPowerSubgroup, MonoidHom.mem_range, Subgroup.mem_prod, Prod.exists]
  constructor
  · rintro ⟨c, d, h⟩
    rw [powMonoidHom_apply, Prod.ext_iff, Prod.pow_fst, Prod.pow_snd] at h
    exact ⟨⟨c, h.1⟩, ⟨d, h.2⟩⟩
  · rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    refine ⟨c, d, ?_⟩
    rw [powMonoidHom_apply, Prod.ext_iff, Prod.pow_fst, Prod.pow_snd]
    exact ⟨hc, hd⟩

/-- For a finite commutative group, the quotient by the `p`-th powers has the same cardinality
as the group of `p`-torsion elements: `|G/G^p| = |G[p]|`. -/
theorem card_quotient_powMonoidHom (G : Type*) [CommGroup G] [Finite G] (p : ℕ) :
    Nat.card (G ⧸ pthPowerSubgroup G p) = Nat.card (MonoidHom.ker (powMonoidHom p : G →* G)) := by
  have h1 : Nat.card (G ⧸ (powMonoidHom p : G →* G).range) *
        Nat.card (powMonoidHom p : G →* G).range = Nat.card G :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup (powMonoidHom p : G →* G).range).symm
  have h2 : Nat.card (MonoidHom.ker (powMonoidHom p : G →* G)) *
        Nat.card (powMonoidHom p : G →* G).range = Nat.card G := by
    rw [mul_comm, Subgroup.card_eq_card_quotient_mul_card_subgroup
      (MonoidHom.ker (powMonoidHom p : G →* G)),
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (powMonoidHom p : G →* G)).toEquiv]
  show Nat.card (G ⧸ (powMonoidHom p : G →* G).range) =
    Nat.card (MonoidHom.ker (powMonoidHom p : G →* G))
  exact (Nat.mul_right_cancel_iff Nat.card_pos).mp (by rw [h1, h2])

/-! ## The `p`-torsion of the roots of unity -/

/-- A primitive `p`-th root of unity in `Kˣ` gives a torsion unit of `𝒪_K` of order `p`.
The root of unity is integral over `ℤ` (it is a root of `X ^ p - 1`). -/
lemma exists_torsion_orderOf_of_primitiveRoot (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (hp : p.Prime) (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ p) :
    ∃ t : NumberField.Units.torsion K, orderOf t = p := by
  have hζK : IsPrimitiveRoot (ζ : K) p :=
    (IsPrimitiveRoot.coe_units_iff (k := p) (ζ := ζ)).mpr hζ
  have hInt : IsIntegral ℤ (ζ : K) := IsPrimitiveRoot.isIntegral hζK hp.pos
  let z : 𝓞 K := ⟨(ζ : K), hInt⟩
  have hz_coe : (algebraMap (𝓞 K) K) z = (ζ : K) := rfl
  have hzp : z ^ p = 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    rw [map_pow, hz_coe, map_one, hζK.pow_eq_one]
  let ν : (𝓞 K)ˣ := Units.ofPowEqOne z p hzp hp.ne_zero
  have hν_tors : ν ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨p, hp.pos, Units.pow_ofPowEqOne hzp hp.ne_zero⟩
  refine ⟨⟨ν, hν_tors⟩, ?_⟩
  have hνprim : IsPrimitiveRoot ν p := by
    rw [← IsPrimitiveRoot.coe_coe_iff]
    have : (algebraMap (𝓞 K) K) ↑ν = (ζ : K) := by
      rw [Units.val_ofPowEqOne]; exact hz_coe
    rw [this]; exact hζK
  have hνprim' : orderOf ν = p := IsPrimitiveRoot.iff_orderOf.mp hνprim
  simpa using hνprim'

/-- Conversely, a torsion unit of order `p` is a primitive `p`-th root of unity of `K`. -/
lemma exists_primitiveRoot_of_orderOf_torsion (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (t : NumberField.Units.torsion K) (ht : orderOf t = p) :
    ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := by
  refine ⟨Units.mk0 ((t : (𝓞 K)ˣ) : K) (NumberField.Units.coe_ne_zero (t : (𝓞 K)ˣ)), ?_⟩
  apply (IsPrimitiveRoot.coe_units_iff (k := p) (ζ := Units.mk0 ((t : (𝓞 K)ˣ) : K)
    (NumberField.Units.coe_ne_zero (t : (𝓞 K)ˣ)))).mp
  rw [Units.val_mk0, IsPrimitiveRoot.iff_orderOf]
  have h1 : orderOf ((t : (𝓞 K)ˣ) : K) = orderOf (t : (𝓞 K)ˣ) :=
    orderOf_injective ((algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K)))
      (NumberField.Units.coe_injective K) (t : (𝓞 K)ˣ)
  rw [h1, Subgroup.orderOf_coe, ht]

/-- The number of `p`-torsion elements of the roots of unity of `K` is `p ^ δ_{K,p}`:
it is `p` exactly when `K` contains a primitive `p`-th root of unity. -/
theorem card_torsionPowKer (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    Nat.card (MonoidHom.ker (powMonoidHom p :
      NumberField.Units.torsion K →* NumberField.Units.torsion K)) =
      p ^ deltaK K p := by
  let φ : NumberField.Units.torsion K →* NumberField.Units.torsion K := powMonoidHom p
  haveI : Fintype (NumberField.Units.torsion K) := Fintype.ofFinite _
  haveI : DecidableEq (NumberField.Units.torsion K) := Classical.decEq _
  have hle : Nat.card (MonoidHom.ker φ) ≤ p := by
    haveI : Fintype ↥(MonoidHom.ker φ) := Fintype.ofFinite _
    haveI : Fintype {t : NumberField.Units.torsion K // t ^ p = 1} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    have he : Fintype.card ↥(MonoidHom.ker φ) =
        Fintype.card {t : NumberField.Units.torsion K // t ^ p = 1} :=
      Fintype.card_congr
        { toFun := fun x => ⟨x.1, by
            have := x.2; rwa [MonoidHom.mem_ker, powMonoidHom_apply] at this⟩
          invFun := fun x => ⟨x.1, by
            rw [MonoidHom.mem_ker, powMonoidHom_apply]; exact x.2⟩
          left_inv := fun x => rfl
          right_inv := fun x => rfl }
    rw [he, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hp.pos
  by_cases hδ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p
  · have hδ1 : deltaK K p = 1 := (deltaK_eq_one_iff K p).mpr hδ
    obtain ⟨ζ, hζ⟩ := hδ
    obtain ⟨t, ht⟩ := exists_torsion_orderOf_of_primitiveRoot K p hp ζ hζ
    have htker : t ∈ MonoidHom.ker φ := by
      rw [MonoidHom.mem_ker, powMonoidHom_apply, ← orderOf_dvd_iff_pow_eq_one, ht]
    have horder : orderOf (⟨t, htker⟩ : ↥(MonoidHom.ker φ)) = p := by
      rw [← Subgroup.orderOf_coe (⟨t, htker⟩ : ↥(MonoidHom.ker φ))]
      exact ht
    have hdvd : p ∣ Nat.card (MonoidHom.ker φ) := by
      have h := Subgroup.card_subgroup_dvd_card
        (Subgroup.zpowers (⟨t, htker⟩ : ↥(MonoidHom.ker φ)))
      rw [Nat.card_zpowers, horder] at h
      exact h
    have hNp : Nat.card (MonoidHom.ker φ) = p :=
      le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)
    rw [hNp, hδ1, pow_one]
  · have hδ0 : deltaK K p = 0 := (deltaK_eq_zero_iff K p).mpr hδ
    have hbot : MonoidHom.ker φ = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro t ht
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at ht
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_iff_pow_eq_one.mpr ht) with h1 | h2
      · exact orderOf_eq_one_iff.mp h1
      · exact absurd (exists_primitiveRoot_of_orderOf_torsion K p t h2) hδ
    rw [hbot, Subgroup.card_bot, hδ0, pow_zero]

/-! ## The quotient `(ℤ^ι)/(pℤ^ι)` -/

/-- `(ι → Multiplicative ℤ) ⧸ (ι → Multiplicative ℤ)^p` has cardinality `p ^ #ι`: it is
`(ℤ/pℤ)^ι`. -/
theorem card_pi_multInt_quotient (ι : Type*) [Fintype ι] (p : ℕ) (hp : p.Prime) :
    Nat.card ((ι → Multiplicative ℤ) ⧸ pthPowerSubgroup (ι → Multiplicative ℤ) p) =
      p ^ Fintype.card ι := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let φ : (ι → Multiplicative ℤ) →* Multiplicative (ι → ZMod p) :=
    { toFun := fun f => Multiplicative.ofAdd (fun i => (((f i).toAdd : ℤ) : ZMod p))
      map_one' := by
        rw [← ofAdd_zero]
        congr 1
        funext i
        simp
      map_mul' := fun f g => by
        rw [← ofAdd_add]
        congr 1
        funext i
        simp [Pi.mul_apply, toAdd_mul] }
  have hφ : ∀ f, φ f = Multiplicative.ofAdd (fun i => (((f i).toAdd : ℤ) : ZMod p)) := fun f => rfl
  have hφeq : ∀ f, φ f = 1 ↔ ∀ i, (((f i).toAdd : ℤ) : ZMod p) = 0 := by
    intro f
    rw [hφ, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, funext_iff]
    simp
  have hker : φ.ker = pthPowerSubgroup (ι → Multiplicative ℤ) p := by
    ext f
    rw [MonoidHom.mem_ker, hφeq f, pthPowerSubgroup, MonoidHom.mem_range]
    constructor
    · intro hA
      choose z hz using fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd (f i).toAdd p).mp (hA i)
      refine ⟨fun i => Multiplicative.ofAdd (z i), ?_⟩
      funext i
      apply Multiplicative.toAdd.injective
      rw [powMonoidHom_apply, Pi.pow_apply, Int.toAdd_pow, toAdd_ofAdd, hz i, mul_comm]
    · rintro ⟨g, hg⟩ i
      have hgp : g ^ p = f := by simpa [powMonoidHom_apply] using hg
      rw [← hgp, Pi.pow_apply, Int.toAdd_pow, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
        mul_zero]
  have hsurj : Function.Surjective φ := by
    intro y
    refine ⟨fun i => Multiplicative.ofAdd ((ZMod.intCast_surjective (y.toAdd i)).choose), ?_⟩
    have h1 : (fun i => (((Multiplicative.ofAdd
        ((ZMod.intCast_surjective (y.toAdd i)).choose)).toAdd : ℤ) : ZMod p)) = y.toAdd := by
      funext i
      rw [toAdd_ofAdd]
      exact (ZMod.intCast_surjective (y.toAdd i)).choose_spec
    rw [hφ, h1, ofAdd_toAdd]
  have h1 : Nat.card ((ι → Multiplicative ℤ) ⧸ pthPowerSubgroup (ι → Multiplicative ℤ) p)
      = Nat.card (Multiplicative (ι → ZMod p)) := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv
  rw [h1, Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_pi]
  simp only [Nat.card_eq_fintype_card, ZMod.card]
  rw [Finset.prod_const, Finset.card_univ]

/-! ## The main theorem -/
/-- **The `𝔽_p`-dimension of `𝒪_Kˣ/(𝒪_Kˣ)^p`.**  By Dirichlet's unit theorem
`𝒪_Kˣ ≅ μ_K × ℤ^{r₁+r₂-1}`, and `μ_K` is finite cyclic, so the quotient by the `p`-th powers has
dimension `(r₁+r₂-1) + δ_{K,p} = NumberField.Units.rank K + deltaK K p` over `𝔽_p`. -/
theorem finrank_unitsModPow (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    Module.finrank (ZMod p) (Work.CFT.Kummer.unitsModPow K p) =
      NumberField.Units.rank K + Work.CFT.Kummer.deltaK K p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hT : Nat.card (NumberField.Units.torsion K ⧸
      pthPowerSubgroup (NumberField.Units.torsion K) p) = p ^ deltaK K p := by
    rw [card_quotient_powMonoidHom (NumberField.Units.torsion K) p, card_torsionPowKer K p hp]
  have h1 : Nat.card ((𝓞 K)ˣ ⧸ pthPowerSubgroup (𝓞 K)ˣ p)
      = Nat.card ((NumberField.Units.torsion K ×
          (Fin (NumberField.Units.rank K) → Multiplicative ℤ)) ⧸
          pthPowerSubgroup (NumberField.Units.torsion K ×
            (Fin (NumberField.Units.rank K) → Multiplicative ℤ)) p) :=
    Nat.card_congr (QuotientGroup.congr _ _ (unitsMulEquiv K)
      (map_pthPowerSubgroup_mulEquiv (unitsMulEquiv K) p)).toEquiv.symm
  have hcard : Nat.card ((𝓞 K)ˣ ⧸ pthPowerSubgroup (𝓞 K)ˣ p)
      = p ^ (NumberField.Units.rank K + deltaK K p) := by
    rw [h1, pthPowerSubgroup_prod]
    rw [Nat.card_congr (QuotientGroup.prodMulEquiv (pthPowerSubgroup (NumberField.Units.torsion K) p)
      (pthPowerSubgroup ((Fin (NumberField.Units.rank K) → Multiplicative ℤ)) p)).toEquiv]
    rw [Nat.card_prod, hT, card_pi_multInt_quotient _ p hp, Fintype.card_fin, ← pow_add,
      Nat.add_comm]
  have hcard' : Nat.card (unitsModPow K p)
      = p ^ (NumberField.Units.rank K + deltaK K p) := by
    show Nat.card (Additive ((𝓞 K)ˣ ⧸ pthPowerSubgroup (𝓞 K)ˣ p)) = _
    rw [Nat.card_congr Additive.ofMul.symm, hcard]
  haveI : Fintype (ZMod p) := ZMod.fintype p
  have hfin : Finite (unitsModPow K p) :=
    Nat.finite_of_card_ne_zero (by rw [hcard']; exact pow_ne_zero _ hp.ne_zero)
  haveI : Fintype (unitsModPow K p) := Fintype.ofFinite _
  have hmain := Module.card_eq_pow_finrank (K := ZMod p) (V := unitsModPow K p)
  rw [ZMod.card p, ← Nat.card_eq_fintype_card, hcard'] at hmain
  exact Nat.pow_right_injective hp.two_le hmain.symm

end Work.CFT.Kummer
