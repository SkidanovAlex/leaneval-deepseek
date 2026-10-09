import Mathlib
import Submission.Work.SSGRoute.E7aAux
import Submission.Work.SSGRoute.mup_local_defs
import Submission.Work.SSGRoute.E7Fin.localAutHomAt_valued
import Submission.Work.SSGRoute.E7Fin.lamQuotAction
import Submission.Work.SSGRoute.E7Fin.lamQuotFinrank
import Submission.NK.LocalInputs.PowerQuotient.Setup
import Submission.NK.LocalInputs.PowerQuotient.Lam
import Submission.NK.LocalInputs.PowerQuotient.natCard_pu_quot_pow
import Submission.NK.LocalInputs.PowerQuotient.natCard_KummerGroup_eq_pow_of_principalUnits
import Submission.NK.LocalInputs.PowerQuotient.natCard_residueUnits_quot_pow_eq_one
import Submission.Work.ArtinInduction.LatticeModp.Infra
import Submission.Work.ArtinInduction.LatticeModp.coprime_reduce
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `𝔽_p[Γ]`-modules of the local Kummer group at a finite place

Lane `Work.SSGRoute.EulerSymm` (the `eulerCharDCresOfUniform` assignment).

This file supplies the vocabulary in which the two remaining pieces (**VAL** and **LOG**) of the
arithmetic chapter of Milne *ADT* I.2.11
(`E7Fin/PING_session39_epsilon_chapter_closed.md` §2, `EulerSymm/NOTE_harith_frontier_H3309.md` §2)
are stated.

Let `k` be a number field, `K/k` finite Galois, `𝔮` a finite place of `K` and
`Γ = MulAction.stabilizer Gal(K/k) (Place.ofFinite 𝔮)` the decomposition group of `𝔮`, which is
canonically the full local Galois group `Gal(κ/k_𝔭)` of the completion `κ = 𝔮.adicCompletion K`.
Write `U¹ = pu 𝔮 1 = 1 + 𝔪` for the principal units and `Λ = log U¹`
(`NK.LocalInputs.PowerQuotient.Lam`).

Milne's arithmetic chapter decomposes the `p`-Kummer group of `κ` as `𝔽_p[Γ]`-modules:

  `κˣ/(κˣ)ᵖ ≅ 𝔽_p ⊕ μ_p ⊕ 𝔽_p[Γ]^{[k_𝔭:ℚ_p]}`,

which splits into **VAL** (`κˣ/(κˣ)ᵖ ≅ ℤ/p ⊕ 𝒪ˣ/(𝒪ˣ)ᵖ`, the valuation sequence, split by Maschke
because `ℤ/p` is trivial and `p ∤ |Γ|`) and **LOG** (`U¹/(U¹)ᵖ ≅ μ_p ⊕ Λ/pΛ`, the `p`-adic
logarithm with kernel the `p`-power roots of unity); the Teichmüller step
`𝒪ˣ/(𝒪ˣ)ᵖ ≅ U¹/(U¹)ᵖ` (the residue units have no `p`-power quotient) removes the middle term.
The **LATTICE** step `Λ/pΛ ≅ 𝔽_p[Γ]^{[k_𝔭:ℚ_p]}` is already available on the `E7Fin.RedLattice`
side (`RedRhoF_localLevelIntegers_invDim_of_commensurable`).

## Contents

* `DecompGroup`, `localAutHomAt_mem_integers`, `intAut`, `oUnitsMulDistribMulAction`,
  `unitsMulDistribMulAction`, `puMulDistribMulAction` — the local Galois action on `𝒪ˣ`, `κˣ` and
  `U¹`;
* `additiveDistribMulAction` — the `DistribMulAction` on `Additive A` induced by a
  `MulDistribMulAction` on `A` (no instance transfer exists in this pin);
* `unitsQuotRho`, `puQuotRho`, `oUnitsQuotRho`, `lamQuotRho` — the values of an additive invariant
  `ρ : Inv p Γ` on the four `𝔽_p[Γ]`-modules of the chapter, with the canonical
  `quotZMod`/`quotDMA`/`quotSCC` instances of `Work.ArtinInduction.LatticeModp.quotRho`.
-/

open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero
open IsDedekindDomain

namespace Work.SSGRoute.EulerSymm

noncomputable section

/-! ## Additive actions induced by multiplicative ones -/

section Induced

variable {G A : Type} [Group G] [CommMonoid A] [MulDistribMulAction G A]

/-- A multiplicative action commutes with powers. -/
lemma smul_pow' {G A : Type} [Group G] [Monoid A] [MulDistribMulAction G A]
    (g : G) (a : A) (n : ℕ) : g • a ^ n = (g • a) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, smul_one]
  | succ k ih => rw [pow_succ, pow_succ, ← ih, MulDistribMulAction.smul_mul]

/-- The additive group underlying a commutative monoid with a multiplicative action inherits a
distributive action.  (There is no instance transfer from `MulDistribMulAction G A` to
`DistribMulAction G (Additive A)` in this pin, so it is given here.) -/
def additiveDistribMulAction (G A : Type) [Group G] [CommMonoid A] [MulDistribMulAction G A] :
    DistribMulAction G (Additive A) where
  smul g x := Additive.ofMul (g • Additive.toMul x)
  one_smul x := by
    show Additive.ofMul ((1 : G) • Additive.toMul x) = x
    rw [one_smul G]
    rfl
  mul_smul g h x := by
    show Additive.ofMul ((g * h) • Additive.toMul x) =
      Additive.ofMul (g • (h • Additive.toMul x))
    rw [mul_smul]
  smul_zero g := by
    show Additive.ofMul (g • (1 : A)) = 0
    rw [smul_one]
    rfl
  smul_add g x y := by
    show Additive.ofMul (g • (Additive.toMul x * Additive.toMul y)) =
      Additive.ofMul (g • Additive.toMul x) + Additive.ofMul (g • Additive.toMul y)
    rw [MulDistribMulAction.smul_mul]
    rfl

end Induced

section Restrict

variable {G A : Type} [Group G] [Group A] [MulDistribMulAction G A]

/-- A multiplicative action restricts to a stable subgroup. -/
def mulDistribMulAction_subtype {G A : Type} [Group G] [Group A] [MulDistribMulAction G A]
    (H : Subgroup A) (hH : ∀ (g : G) (a : A), a ∈ H → g • a ∈ H) :
    MulDistribMulAction G ↥H where
  smul g x := ⟨g • (x : A), hH g (x : A) x.2⟩
  one_smul x := Subtype.ext (by
    show (1 : G) • (x : A) = (x : A)
    exact one_smul G (x : A))
  mul_smul g h x := Subtype.ext (by
    show (g * h) • (x : A) = g • (h • (x : A))
    exact mul_smul g h (x : A))
  smul_mul g x y := Subtype.ext (by
    show g • ((x : A) * (y : A)) = g • (x : A) * g • (y : A)
    exact MulDistribMulAction.smul_mul g (x : A) (y : A))
  smul_one g := Subtype.ext (by
    show g • (1 : A) = 1
    exact smul_one g)


end Restrict

/-! ## The local Galois action -/

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]
variable {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K)}

/-- The decomposition group of `𝔮` in `Gal(K/k)`, canonically the local Galois group
`Gal(κ/k_𝔭)` of the completion `κ = 𝔮.adicCompletion K`. -/
abbrev DecompGroup (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K)) : Type :=
  ↥(MulAction.stabilizer (K ≃ₐ[k] K) (NK.GlobalCFT.Place.ofFinite 𝔮))

/-- The local Galois action preserves the ring of integers. -/
theorem localAutHomAt_mem_integers (γ : DecompGroup k K 𝔮) {x : 𝔮.adicCompletion K}
    (hx : x ∈ 𝔮.adicCompletionIntegers K) :
    Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ x ∈
      𝔮.adicCompletionIntegers K := by
  have h := Work.SSGRoute.E7Fin.localAutHomAt_valuation k K 𝔮 γ x
  rw [show (𝔮.adicCompletionIntegers K) =
      (NK.LocalInputs.PowerQuotient.vv 𝔮).valuationSubring from rfl,
    Valuation.mem_valuationSubring_iff] at hx ⊢
  rw [h]; exact hx

/-- The automorphism induced by `γ` on the ring of integers. -/
def intAut (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [IsGalois k K] (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (γ : DecompGroup k K 𝔮) :
    𝔮.adicCompletionIntegers K ≃+* 𝔮.adicCompletionIntegers K where
  toFun x := ⟨Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ x,
    localAutHomAt_mem_integers γ x.2⟩
  invFun x := ⟨Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ⁻¹ x,
    localAutHomAt_mem_integers γ⁻¹ x.2⟩
  left_inv x := by
    apply Subtype.ext
    show Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ⁻¹
      (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ x) = x
    have h1 : (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ⁻¹
        * Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have h2 := congrArg (fun e : 𝔮.adicCompletion K ≃+* 𝔮.adicCompletion K => e x) h1
    simpa using h2
  right_inv x := by
    apply Subtype.ext
    show Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ
      (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ⁻¹ x) = x
    have h1 : (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ
        * Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have h2 := congrArg (fun e : 𝔮.adicCompletion K ≃+* 𝔮.adicCompletion K => e x) h1
    simpa using h2
  map_add' x y := Subtype.ext (by
    show Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ (x + y) = _
    rw [map_add]; rfl)
  map_mul' x y := Subtype.ext (by
    show Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ (x * y) = _
    rw [map_mul]; rfl)

/-- `intAut` at `1` is the identity. -/
lemma intAut_one_apply (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [IsGalois k K] (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (y : 𝔮.adicCompletionIntegers K) :
    intAut k K 𝔮 (1 : DecompGroup k K 𝔮) y = y := by
  apply Subtype.ext
  show Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) (1 : DecompGroup k K 𝔮)
    ((y : 𝔮.adicCompletionIntegers K) : 𝔮.adicCompletion K) = _
  rw [map_one]
  rfl

/-- `intAut` is multiplicative in the group variable. -/
lemma intAut_mul_apply (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [IsGalois k K] (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (γ δ : DecompGroup k K 𝔮) (y : 𝔮.adicCompletionIntegers K) :
    intAut k K 𝔮 (γ * δ) y = intAut k K 𝔮 γ (intAut k K 𝔮 δ y) := by
  apply Subtype.ext
  show Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) (γ * δ)
      ((y : 𝔮.adicCompletionIntegers K) : 𝔮.adicCompletion K) =
    Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ
      (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) δ
        ((y : 𝔮.adicCompletionIntegers K) : 𝔮.adicCompletion K))
  rw [map_mul]
  rfl

/-- The multiplicative action of `Γ` on the units of the ring of integers. -/
instance oUnitsMulDistribMulAction (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [IsGalois k K] (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulDistribMulAction (DecompGroup k K 𝔮) (𝔮.adicCompletionIntegers K)ˣ where
  smul γ x := Units.mkOfMulEqOne
    (intAut k K 𝔮 γ (x : 𝔮.adicCompletionIntegers K))
    (intAut k K 𝔮 γ (((x⁻¹ : (𝔮.adicCompletionIntegers K)ˣ) :
      𝔮.adicCompletionIntegers K)))
    (by rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one])
  one_smul x := by
    apply Units.ext
    show intAut k K 𝔮 (1 : DecompGroup k K 𝔮) (x : 𝔮.adicCompletionIntegers K) =
      (x : 𝔮.adicCompletionIntegers K)
    rw [intAut_one_apply]
  mul_smul γ δ x := by
    apply Units.ext
    show intAut k K 𝔮 (γ * δ) (x : 𝔮.adicCompletionIntegers K) =
      intAut k K 𝔮 γ (intAut k K 𝔮 δ (x : 𝔮.adicCompletionIntegers K))
    rw [intAut_mul_apply]
  smul_mul γ x y := by
    apply Units.ext
    show intAut k K 𝔮 γ ((x : 𝔮.adicCompletionIntegers K) * (y : 𝔮.adicCompletionIntegers K)) =
      intAut k K 𝔮 γ (x : 𝔮.adicCompletionIntegers K) *
        intAut k K 𝔮 γ (y : 𝔮.adicCompletionIntegers K)
    rw [map_mul]
  smul_one γ := by
    apply Units.ext
    show intAut k K 𝔮 γ (1 : 𝔮.adicCompletionIntegers K) = 1
    rw [map_one]

/-- The multiplicative action of `Γ` on the units `κˣ` of the completion. -/
instance unitsMulDistribMulAction (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [IsGalois k K] (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulDistribMulAction (DecompGroup k K 𝔮) (𝔮.adicCompletion K)ˣ where
  smul γ x := Units.map (RingEquiv.toMonoidHom (Work.SSGRoute.localAutHomAt k
    (NK.GlobalCFT.Place.ofFinite 𝔮) γ)) x
  one_smul x := by
    change Units.map (RingEquiv.toMonoidHom (Work.SSGRoute.localAutHomAt k
      (NK.GlobalCFT.Place.ofFinite 𝔮) (1 : DecompGroup k K 𝔮))) x = x
    rw [show Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮)
        (1 : DecompGroup k K 𝔮) =
        (1 : 𝔮.adicCompletion K ≃+* 𝔮.adicCompletion K) from map_one _]
    apply Units.ext
    rw [Units.coe_map]
    rfl
  mul_smul γ δ x := by
    change Units.map (RingEquiv.toMonoidHom (Work.SSGRoute.localAutHomAt k
        (NK.GlobalCFT.Place.ofFinite 𝔮) (γ * δ))) x =
      Units.map (RingEquiv.toMonoidHom (Work.SSGRoute.localAutHomAt k
        (NK.GlobalCFT.Place.ofFinite 𝔮) γ))
        (Units.map (RingEquiv.toMonoidHom (Work.SSGRoute.localAutHomAt k
          (NK.GlobalCFT.Place.ofFinite 𝔮) δ)) x)
    rw [map_mul]
    apply Units.ext
    rw [Units.coe_map, Units.coe_map, Units.coe_map]
    rfl
  smul_mul γ x y := by
    change Units.map (RingEquiv.toMonoidHom (Work.SSGRoute.localAutHomAt k
      (NK.GlobalCFT.Place.ofFinite 𝔮) γ)) (x * y) = _
    rw [map_mul]
    rfl
  smul_one γ := by
    change Units.map (RingEquiv.toMonoidHom (Work.SSGRoute.localAutHomAt k
      (NK.GlobalCFT.Place.ofFinite 𝔮) γ)) 1 = 1
    rw [map_one]

/-- The `Γ`-image of a principal unit is a principal unit. -/
lemma puMap_mem (γ : DecompGroup k K 𝔮) {u : (𝔮.adicCompletionIntegers K)ˣ}
    (hu : u ∈ NK.LocalInputs.PowerQuotient.pu 𝔮 1) :
    (oUnitsMulDistribMulAction k K 𝔮).smul γ u ∈ NK.LocalInputs.PowerQuotient.pu 𝔮 1 := by
  rw [NK.LocalInputs.PowerQuotient.mem_pu_iff_val] at hu ⊢
  have hcoe : ((((oUnitsMulDistribMulAction k K 𝔮).smul γ u :
        (𝔮.adicCompletionIntegers K)ˣ) : 𝔮.adicCompletionIntegers K) :
      𝔮.adicCompletion K) =
      Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ
        (((u : (𝔮.adicCompletionIntegers K)ˣ) : 𝔮.adicCompletionIntegers K) :
          𝔮.adicCompletion K) := rfl
  rw [hcoe]
  have hsub : Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ
        (((u : (𝔮.adicCompletionIntegers K)ˣ) : 𝔮.adicCompletionIntegers K) :
          𝔮.adicCompletion K) - 1 =
      Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ
        ((((u : (𝔮.adicCompletionIntegers K)ˣ) : 𝔮.adicCompletionIntegers K) :
          𝔮.adicCompletion K) - 1) := by
    rw [map_sub, map_one]
  rw [hsub, Work.SSGRoute.E7Fin.localAutHomAt_valuation k K 𝔮 γ]
  exact hu

/-- The local Galois action on the principal units `U¹ = 1 + 𝔪`. -/
instance puMulDistribMulAction (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [IsGalois k K] (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulDistribMulAction (DecompGroup k K 𝔮) ↥(NK.LocalInputs.PowerQuotient.pu 𝔮 1) where
  smul γ u := ⟨(oUnitsMulDistribMulAction k K 𝔮).smul γ u.1, puMap_mem γ u.2⟩
  one_smul u := Subtype.ext (by
    letI := oUnitsMulDistribMulAction k K 𝔮
    change (1 : DecompGroup k K 𝔮) • u.1 = u.1
    rw [one_smul])
  mul_smul γ δ u := Subtype.ext (by
    letI := oUnitsMulDistribMulAction k K 𝔮
    change (γ * δ) • u.1 = γ • δ • u.1
    rw [mul_smul])
  smul_mul γ u v := Subtype.ext (by
    letI := oUnitsMulDistribMulAction k K 𝔮
    change γ • (u.1 * v.1) = γ • u.1 * γ • v.1
    rw [MulDistribMulAction.smul_mul])
  smul_one γ := Subtype.ext (by
    letI := oUnitsMulDistribMulAction k K 𝔮
    change γ • (1 : (𝔮.adicCompletionIntegers K)ˣ) = 1
    rw [smul_one])

/-! ## The `p`-power quotient of a commutative group with a multiplicative action -/

section PowQuotAction

variable {G A : Type} [Group G] [CommGroup A] [MulDistribMulAction G A]

/-- The subgroup `Aᵖ` of `p`-th powers. -/
abbrev powSub (p : ℕ) (A : Type) [CommGroup A] : Subgroup A :=
  (powMonoidHom p : A →* A).range

/-- Additive `nsmul` in `Additive A` is the group power in `A`. -/
lemma toMul_nsmul {A : Type} [Group A] (n : ℕ) (y : Additive A) :
    Additive.toMul (n • y) = Additive.toMul y ^ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [succ_nsmul]
    show Additive.toMul (k • y) * Additive.toMul y = Additive.toMul y ^ (k + 1)
    rw [ih, pow_succ]

/-- The additive zero of `Additive A` is the group identity of `A`. -/
lemma toMul_zero {A : Type} [Group A] : Additive.toMul (0 : Additive A) = 1 := rfl

/-- `Aᵖ` is stable under the multiplicative action. -/
lemma smul_mem_powSub (p : ℕ) (g : G) {a : A} (ha : a ∈ powSub p A) : g • a ∈ powSub p A := by
  rw [powSub, MonoidHom.mem_range] at ha ⊢
  obtain ⟨b, rfl⟩ := ha
  refine ⟨(MulDistribMulAction.toMonoidHom A g) b, ?_⟩
  show ((MulDistribMulAction.toMonoidHom A g) b) ^ p =
    (MulDistribMulAction.toMonoidHom A g) (b ^ p)
  rw [map_pow]

/-- Well-definedness of the induced map on `A ⧸ Aᵖ`. -/
lemma powQuotMap'_eq (p : ℕ) (g : G) {a b : A}
    (hab : QuotientGroup.leftRel (powSub p A) a b) :
    QuotientGroup.leftRel (powSub p A) (g • a) (g • b) := by
  rw [QuotientGroup.leftRel_apply] at hab ⊢
  have h1 : (g • a)⁻¹ * (g • b) = (MulDistribMulAction.toMonoidHom A g) (a⁻¹ * b) := by
    rw [map_mul, map_inv]
    rfl
  rw [h1]
  show (g : G) • (a⁻¹ * b) ∈ powSub p A
  exact smul_mem_powSub p g hab

/-- **The multiplicative action of `G` on the `p`-power quotient `A ⧸ Aᵖ`** (the quotient of a
`MulDistribMulAction` group, acting by the induced homomorphisms). -/
instance powQuotMulDistribMulAction (p : ℕ) : MulDistribMulAction G (A ⧸ powSub p A) where
  smul g := Quotient.map' (fun a => g • a) (fun a b hab => powQuotMap'_eq p g hab)
  one_smul a := Quotient.inductionOn' a (fun x => by
    show Quotient.mk'' ((1 : G) • x) = Quotient.mk'' x
    rw [one_smul])
  mul_smul g h a := Quotient.inductionOn' a (fun x => by
    show Quotient.mk'' ((g * h) • x) = Quotient.mk'' (g • (h • x))
    rw [mul_smul])
  smul_mul g a b := Quotient.inductionOn' a (fun x => Quotient.inductionOn' b (fun y => by
    show Quotient.mk'' (g • (x * y)) = Quotient.mk'' (g • x * g • y)
    rw [MulDistribMulAction.smul_mul]))
  smul_one g := by
    show Quotient.mk'' (g • (1 : A)) = Quotient.mk'' (1 : A)
    rw [smul_one]

/-- The induced `DistribMulAction` on `Additive (A ⧸ Aᵖ)`. -/
noncomputable def powQuotDistribMulAction (p : ℕ) :
    DistribMulAction G (Additive (A ⧸ powSub p A)) :=
  additiveDistribMulAction G (A ⧸ powSub p A)

/-- The `𝔽_p`-module structure on `A ⧸ Aᵖ` (the quotient has exponent dividing `p`). -/
noncomputable def powQuotModule (p : ℕ) [NeZero p] :
    Module (ZMod p) (Additive (A ⧸ powSub p A)) :=
  AddCommGroup.zmodModule (n := p) (G := Additive (A ⧸ powSub p A)) (fun x => by
    refine Additive.toMul.injective ?_
    rw [toMul_nsmul, toMul_zero]
    refine QuotientGroup.induction_on (Additive.toMul x) fun a => ?_
    show (QuotientGroup.mk (a ^ p) : A ⧸ powSub p A) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨a, rfl⟩))

/-- The `G`-action and the `𝔽_p`-action on `A ⧸ Aᵖ` commute. -/
noncomputable def powQuotSMulCommClass (p : ℕ) [NeZero p] :
    @SMulCommClass G (ZMod p) (Additive (A ⧸ powSub p A))
      (powQuotDistribMulAction (G := G) (A := A) p).toSMul
      (powQuotModule (A := A) p).toSMul := by
  letI := powQuotModule (A := A) p
  refine ⟨fun g c x => ?_⟩
  rw [Work.ArtinInduction.LatticeModp.zmod_smul_eq_nsmul p c,
    Work.ArtinInduction.LatticeModp.zmod_smul_eq_nsmul p c]
  exact (DistribMulAction.toAddMonoidEnd G (Additive (A ⧸ powSub p A)) g).map_nsmul c.val x

end PowQuotAction

/-! ## Finiteness of the quotients, and the value functionals -/

/-- **Finiteness of `κˣ/(κˣ)ᵖ`** from the cardinality computation
`NK.LocalInputs.PowerQuotient.natCard_KummerGroup_eq_pow_of_principalUnits`. -/
theorem finite_powQuot_units (p : ℕ) [Fact p.Prime]
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p)
    (M : ℕ) (D : NK.LocalInputs.PowerQuotient.LogData 𝔮 M) :
    Finite (Additive ((𝔮.adicCompletion K)ˣ ⧸ powSub p ((𝔮.adicCompletion K)ˣ))) := by
  have hU : Nat.card (NK.LocalInputs.principalUnits K 𝔮 ⧸
      (powMonoidHom p : NK.LocalInputs.principalUnits K 𝔮 →*
        NK.LocalInputs.principalUnits K 𝔮).range) =
      p ^ (NK.LocalInputs.localDegree K 𝔮 + NK.LocalInputs.zetaIndicator p (𝔮.adicCompletion K)) := by
    rw [← NK.LocalInputs.PowerQuotient.pu_one (K := K) 𝔮]
    exact NK.LocalInputs.PowerQuotient.natCard_pu_quot_pow 𝔮 (Fact.out : p.Prime) hres D
  have hcard : Nat.card ((𝔮.adicCompletion K)ˣ ⧸ powSub p ((𝔮.adicCompletion K)ˣ)) =
      p ^ (NK.LocalInputs.localDegree K 𝔮 + 1 +
        NK.LocalInputs.zetaIndicator p (𝔮.adicCompletion K)) :=
    NK.LocalInputs.PowerQuotient.natCard_KummerGroup_eq_pow_of_principalUnits
      (K := K) 𝔮 (Fact.out : p.Prime)
      (NK.LocalInputs.PowerQuotient.natCard_residueUnits_quot_pow_eq_one 𝔮 (Fact.out : p.Prime)
        hres)
      hU
  refine Finite.of_not_infinite ?_
  intro hinf
  have h0 : Nat.card ((𝔮.adicCompletion K)ˣ ⧸ powSub p ((𝔮.adicCompletion K)ˣ)) = 0 :=
    Nat.card_eq_zero.mpr (Or.inr hinf)
  rw [h0] at hcard
  exact (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hcard.symm

/-- **Finiteness of `U¹/(U¹)ᵖ`** from `NK.LocalInputs.PowerQuotient.natCard_pu_quot_pow`. -/
theorem finite_powQuot_pu (p : ℕ) [Fact p.Prime]
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p)
    (M : ℕ) (D : NK.LocalInputs.PowerQuotient.LogData 𝔮 M) :
    Finite (Additive (↥(NK.LocalInputs.PowerQuotient.pu 𝔮 1) ⧸
      powSub p ↥(NK.LocalInputs.PowerQuotient.pu 𝔮 1))) := by
  have hcard := NK.LocalInputs.PowerQuotient.natCard_pu_quot_pow 𝔮 (Fact.out : p.Prime) hres D
  refine Finite.of_not_infinite ?_
  intro hinf
  have h0 : Nat.card (↥(NK.LocalInputs.PowerQuotient.pu 𝔮 1) ⧸
      powSub p ↥(NK.LocalInputs.PowerQuotient.pu 𝔮 1)) = 0 :=
    Nat.card_eq_zero.mpr (Or.inr hinf)
  rw [h0] at hcard
  exact (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hcard.symm

/-- **Finiteness of `Λ/pΛ`** from `E7Fin.natCard_LamQuot`. -/
theorem finite_lamQuot (p : ℕ) [Fact p.Prime]
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p)
    (M : ℕ) (D : Work.SSGRoute.E7Fin.CanonLogData 𝔮 M) :
    Finite (Work.SSGRoute.E7Fin.LamQuot D (Fact.out : p.Prime) hres) := by
  have hcard := Work.SSGRoute.E7Fin.natCard_LamQuot D (Fact.out : p.Prime) hres
  refine Finite.of_not_infinite ?_
  intro hinf
  have h0 : Nat.card (Work.SSGRoute.E7Fin.LamQuot D (Fact.out : p.Prime) hres) = 0 :=
    Nat.card_eq_zero.mpr (Or.inr hinf)
  rw [h0] at hcard
  exact (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hcard.symm

/-- The value of an additive invariant `ρ` on the `𝔽_p[Γ]`-module `κˣ/(κˣ)ᵖ`. -/
noncomputable def unitsQuotRho (p : ℕ) [Fact p.Prime]
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p)
    (M : ℕ) (D : NK.LocalInputs.PowerQuotient.LogData 𝔮 M)
    (ρ : Work.ArtinInduction.LatticeModp.Inv p (DecompGroup k K 𝔮)) : ℚ :=
  @ρ (Additive ((𝔮.adicCompletion K)ˣ ⧸ powSub p ((𝔮.adicCompletion K)ˣ))) _
    (powQuotModule (A := (𝔮.adicCompletion K)ˣ) p)
    (powQuotDistribMulAction (G := DecompGroup k K 𝔮) (A := (𝔮.adicCompletion K)ˣ) p)
    (powQuotSMulCommClass (A := (𝔮.adicCompletion K)ˣ) p)
    (finite_powQuot_units p hres M D)

/-- The value of an additive invariant `ρ` on the `𝔽_p[Γ]`-module `U¹/(U¹)ᵖ`. -/
noncomputable def puQuotRho (p : ℕ) [Fact p.Prime]
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p)
    (M : ℕ) (D : NK.LocalInputs.PowerQuotient.LogData 𝔮 M)
    (ρ : Work.ArtinInduction.LatticeModp.Inv p (DecompGroup k K 𝔮)) : ℚ :=
  @ρ (Additive (↥(NK.LocalInputs.PowerQuotient.pu 𝔮 1) ⧸
      powSub p ↥(NK.LocalInputs.PowerQuotient.pu 𝔮 1))) _
    (powQuotModule (A := ↥(NK.LocalInputs.PowerQuotient.pu 𝔮 1)) p)
    (powQuotDistribMulAction (G := DecompGroup k K 𝔮)
      (A := ↥(NK.LocalInputs.PowerQuotient.pu 𝔮 1)) p)
    (powQuotSMulCommClass (A := ↥(NK.LocalInputs.PowerQuotient.pu 𝔮 1)) p)
    (finite_powQuot_pu p hres M D)

/-- The value of an additive invariant `ρ` on the `𝔽_p[Γ]`-module `Λ/pΛ` (`Λ = log U¹`). -/
noncomputable def lamQuotRho (p : ℕ) [Fact p.Prime]
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p)
    (M : ℕ) (D : Work.SSGRoute.E7Fin.CanonLogData 𝔮 M)
    (ρ : Work.ArtinInduction.LatticeModp.Inv p (DecompGroup k K 𝔮)) : ℚ :=
  @ρ (Work.SSGRoute.E7Fin.LamQuot D (Fact.out : p.Prime) hres) _
    (Work.SSGRoute.E7Fin.lamQuotModule D (Fact.out : p.Prime) hres)
    (Work.SSGRoute.E7Fin.lamQuotAction D (Fact.out : p.Prime) hres)
    (Work.SSGRoute.E7Fin.lamQuotSmulComm D (Fact.out : p.Prime) hres)
    (finite_lamQuot p hres M D)

/-! ## The `p`-torsion subgroup of `κˣ` (the `μ_p`-summand of the logarithm step) -/

/-- The `p`-torsion subgroup `μ_p(κ) = {x ∈ κˣ | x^p = 1}` of the units of the completion. -/
abbrev mupKernel (p : ℕ) (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Subgroup (𝔮.adicCompletion K)ˣ :=
  (powMonoidHom p : (𝔮.adicCompletion K)ˣ →* (𝔮.adicCompletion K)ˣ).ker

/-- `μ_p(κ)` is stable under the local Galois action. -/
lemma mupKernel_smul_mem (p : ℕ) (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [IsGalois k K]
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (γ : DecompGroup k K 𝔮) {x : (𝔮.adicCompletion K)ˣ} (hx : x ∈ mupKernel p k K 𝔮) :
    (unitsMulDistribMulAction k K 𝔮).smul γ x ∈ mupKernel p k K 𝔮 := by
  rw [mupKernel, MonoidHom.mem_ker] at hx ⊢
  show ((unitsMulDistribMulAction k K 𝔮).smul γ x) ^ p = 1
  change (Units.map (RingEquiv.toMonoidHom (Work.SSGRoute.localAutHomAt k
    (NK.GlobalCFT.Place.ofFinite 𝔮) γ)) x) ^ p = 1
  rw [← map_pow (Units.map (RingEquiv.toMonoidHom (Work.SSGRoute.localAutHomAt k
    (NK.GlobalCFT.Place.ofFinite 𝔮) γ)))]
  rw [show x ^ p = 1 from hx, map_one]

instance mupKernelMulDistribMulAction (p : ℕ) (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [IsGalois k K]
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulDistribMulAction (DecompGroup k K 𝔮) ↥(mupKernel p k K 𝔮) :=
  mulDistribMulAction_subtype (mupKernel p k K 𝔮)
    (fun γ x hx => mupKernel_smul_mem p k K 𝔮 γ hx)

/-- The induced distributive action on `Additive ↥(μ_p(κ))`. -/
noncomputable def mupKernelDistribMulAction (p : ℕ) (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [IsGalois k K]
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    DistribMulAction (DecompGroup k K 𝔮) (Additive ↥(mupKernel p k K 𝔮)) :=
  additiveDistribMulAction (DecompGroup k K 𝔮) ↥(mupKernel p k K 𝔮)

/-- The `𝔽_p`-module structure on `μ_p(κ)`. -/
noncomputable def mupKernelModule (p : ℕ) [NeZero p] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [IsGalois k K]
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Module (ZMod p) (Additive ↥(mupKernel p k K 𝔮)) :=
  AddCommGroup.zmodModule (n := p) (G := Additive ↥(mupKernel p k K 𝔮)) (fun x => by
    refine Additive.toMul.injective ?_
    rw [toMul_nsmul, toMul_zero]
    apply Subtype.ext
    rw [show (((Additive.toMul x) ^ p : ↥(mupKernel p k K 𝔮)) :
        (𝔮.adicCompletion K)ˣ) =
        (((Additive.toMul x : ↥(mupKernel p k K 𝔮)) : (𝔮.adicCompletion K)ˣ)) ^ p from
      map_pow (Subgroup.subtype (mupKernel p k K 𝔮)) _ p]
    exact (Additive.toMul x).2)

/-- The `Γ`-action and the `𝔽_p`-action on `μ_p(κ)` commute. -/
noncomputable def mupKernelSMulCommClass (p : ℕ) [NeZero p] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [IsGalois k K]
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    @SMulCommClass (DecompGroup k K 𝔮) (ZMod p) (Additive ↥(mupKernel p k K 𝔮))
      (mupKernelDistribMulAction p k K 𝔮).toSMul
      (mupKernelModule p k K 𝔮).toSMul := by
  letI := mupKernelModule p k K 𝔮
  refine ⟨fun g c x => ?_⟩
  rw [Work.ArtinInduction.LatticeModp.zmod_smul_eq_nsmul p c,
    Work.ArtinInduction.LatticeModp.zmod_smul_eq_nsmul p c]
  exact (DistribMulAction.toAddMonoidEnd (DecompGroup k K 𝔮)
    (Additive ↥(mupKernel p k K 𝔮)) g).map_nsmul c.val x

/-- The value of an additive invariant `ρ` on the `𝔽_p[Γ]`-module `μ_p(κ)` (the `p`-torsion of
`κˣ`, with its cyclotomic `Γ`-action). -/
noncomputable def mupKernelRho (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [IsGalois k K]
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ρ : Work.ArtinInduction.LatticeModp.Inv p (DecompGroup k K 𝔮))
    [Finite (Additive ↥(mupKernel p k K 𝔮))] : ℚ :=
  @ρ (Additive ↥(mupKernel p k K 𝔮)) _
    (mupKernelModule p k K 𝔮) (mupKernelDistribMulAction p k K 𝔮)
    (mupKernelSMulCommClass p k K 𝔮)
    ‹Finite (Additive ↥(mupKernel p k K 𝔮))›

end

end Work.SSGRoute.EulerSymm
