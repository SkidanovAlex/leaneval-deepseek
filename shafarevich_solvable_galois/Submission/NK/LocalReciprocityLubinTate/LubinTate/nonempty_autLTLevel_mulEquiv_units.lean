import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.LocalReciprocityLubinTate.Eval.ltLevelIsSimple
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_algEquiv
import Submission.NK.LocalReciprocityLubinTate.LubinTate.exists_primitive_LTdivisionSet
import Submission.NK.LocalReciprocityLubinTate.LubinTate.exists_unit_smulDiv_eq_of_primitive
import Submission.NK.LocalReciprocityLubinTate.LubinTate.ext_of_eqOn_LTdivisionSet
import Submission.NK.LocalReciprocityLubinTate.LubinTate.smulDiv_eq_iff_sub_mem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Galois group of a Lubin–Tate level is the group of local units

For a nonarchimedean local field `F` of characteristic zero, a uniformiser `π` and `n ≥ 1`, the
group of `F`-algebra automorphisms of the `n`-th Lubin–Tate level `K_n = F(Λ_n)` is isomorphic to
the group of units of the truncated ring of integers,

`Gal(K_n/F) ≅ (𝒪[F]/𝔪[F]^n)ˣ`

(Milne, *Classical Field Theory*, Theorem I.3.6 (b); Serre, *Local Fields*, Ch. XV §4).  This is the
Lubin–Tate reciprocity isomorphism at the level of the torsion points: an automorphism `σ` of the
level is determined by its value on a *primitive* division point `y ∈ Λ_n ∖ Λ_{n-1}`, which by
Milne I.3.1 is a generator of the free `𝒪[F]/π^n`-module `Λ_n`, so that

`σ(y) = u_σ · y`

for a unique unit `u_σ ∈ (𝒪[F]/π^n)ˣ`.  The map `σ ↦ u_σ` is then a group homomorphism
(`𝒪[F]` is commutative), and it is injective because `y` generates `K_n` over `F`.  Both groups
have `(q-1)q^{n-1}` elements — `card_aut_LTLevel_eq` and
`Units.natCard_units_quot_pow_maximalIdeal` — so an injective homomorphism between finite groups of
equal cardinality is bijective, and gives the required `MulEquiv`.

## Main results

* `NK.LocalReciprocityLubinTate.LubinTate.mem_LTdivisionSet_algEquiv_iff`;
* `NK.LocalReciprocityLubinTate.LubinTate.nonempty_autLTLevel_mulEquiv_units`.
-/

open Polynomial

set_option linter.style.haveILetI false

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

/-- **The division points are invariant under `F`-algebra automorphisms of the algebraic
closure.**  For `σ ∈ Gal(F̄/F)`, a point `x` is a `π^n`-division point if and only if `σ x` is:
`σ` fixes the coefficients of the iterate `f^{(n)}`, so `f^{(n)}(σ x) = σ(f^{(n)}(x))`. -/
theorem mem_LTdivisionSet_algEquiv_iff {F : Type*} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (π : F) (q m : ℕ) (hq : 2 ≤ q)
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (x : AlgebraicClosure F) :
    σ x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F π q m ↔
      x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F π q m := by
  rw [NK.LocalReciprocityLubinTate.mem_LTdivisionSet_iff π q m hq,
    NK.LocalReciprocityLubinTate.mem_LTdivisionSet_iff π q m hq,
    Polynomial.aeval_algHom_apply]
  exact ⟨fun h => σ.injective (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

/-- **The Galois group of the `n`-th Lubin–Tate level is the group of units of `𝒪[F]/𝔪[F]^n`**
(Milne, *CFT*, Theorem I.3.6 (b)): for `n ≥ 1` there is a group isomorphism

  `Gal(F(Λ_n)/F) ≃* (𝒪[F]/𝔪[F]^n)ˣ`,

sending `σ` to the unit `u_σ` with `σ(π_n) = u_σ · π_n` on a primitive division point `π_n`. -/
theorem nonempty_autLTLevel_mulEquiv_units {F : Type*} [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ((↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n) ≃ₐ[F]
        ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
          (NK.LocalReciprocityLubinTate.residueCard F) n)) ≃*
      ((↥(ValuativeRel.valuation F).integer ⧸
        (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer) ^ n)ˣ)) := by
  classical
  -- the canonical Lubin–Tate module over `𝒪[F]` and a primitive division point
  obtain ⟨M, hpi⟩ := NK.LocalReciprocityLubinTate.lubinTateModule_integers F π hπ
  obtain ⟨y, hy, hy'⟩ := exists_primitive_LTdivisionSet π hπ n hn
  have hq : 2 ≤ NK.LocalReciprocityLubinTate.residueCard F :=
    NK.LocalReciprocityLubinTate.two_le_residueCard F
  let L := NK.LocalReciprocityLubinTate.LTLevel F (π : F)
    (NK.LocalReciprocityLubinTate.residueCard F) n
  let O := ↥(ValuativeRel.valuation F).integer
  let I : Ideal O := (IsLocalRing.maximalIdeal O) ^ n
  let mkq : O →* (O ⧸ I) := (Ideal.Quotient.mk I).toMonoidHom
  change Nonempty ((↥L ≃ₐ[F] ↥L) ≃* (O ⧸ I)ˣ)
  let yL : ↥L := ⟨y, NK.LocalReciprocityLubinTate.LTdivisionSet_subset_LTLevel F (π : F)
    (NK.LocalReciprocityLubinTate.residueCard F) n hy⟩
  -- the `𝒪[F]`-action is injective on the multiples of a primitive point
  have hSM : ∀ a b : O, Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M
        hy a = Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy b ↔
        a - b ∈ I :=
    fun a b => smulDiv_eq_iff_sub_mem π hπ n hn M hpi hy hy' a b
  -- the action of `σ` on the primitive point `y`
  have hlift : ∀ σ : ↥L ≃ₐ[F] ↥L,
      (σ.liftNormal (AlgebraicClosure F)) y = ((σ yL : ↥L) : AlgebraicClosure F) := by
    intro σ
    rw [show y = algebraMap ↥L (AlgebraicClosure F) yL from rfl,
      AlgEquiv.liftNormal_commutes]
    rfl
  have hmemσ : ∀ σ : ↥L ≃ₐ[F] ↥L,
      (σ.liftNormal (AlgebraicClosure F)) y ∈
        NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
          (NK.LocalReciprocityLubinTate.residueCard F) n :=
    fun σ => (mem_LTdivisionSet_algEquiv_iff (π : F) (NK.LocalReciprocityLubinTate.residueCard F)
      n hq (σ.liftNormal (AlgebraicClosure F)) y).mpr hy
  have hprimσ : ∀ σ : ↥L ≃ₐ[F] ↥L,
      (σ.liftNormal (AlgebraicClosure F)) y ∉
        NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
          (NK.LocalReciprocityLubinTate.residueCard F) (n - 1) :=
    fun σ h => hy' ((mem_LTdivisionSet_algEquiv_iff (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) (n - 1) hq
      (σ.liftNormal (AlgebraicClosure F)) y).mp h)
  -- the unit attached to `σ` by the orbit of `y`
  have hex : ∀ σ : ↥L ≃ₐ[F] ↥L, ∃ u : Oˣ,
      Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy (u : O) =
        (σ.liftNormal (AlgebraicClosure F)) y :=
    fun σ => exists_unit_smulDiv_eq_of_primitive π hπ n hn M hpi hy hy'
      (hmemσ σ) (hprimσ σ)
  let uOf : (↥L ≃ₐ[F] ↥L) → Oˣ := fun σ => Classical.choose (hex σ)
  have huOf : ∀ σ, Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy
      (uOf σ : O) = (σ.liftNormal (AlgebraicClosure F)) y :=
    fun σ => Classical.choose_spec (hex σ)
  -- the class of `uOf σ` in `(𝒪[F]/𝔪^n)ˣ` depends only on `σ`
  have hwd : ∀ (σ : ↥L ≃ₐ[F] ↥L) (v : Oˣ),
      Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy (v : O) =
        (σ.liftNormal (AlgebraicClosure F)) y →
      Units.map mkq (uOf σ) = Units.map mkq v := by
    intro σ v hv
    apply Units.ext
    simp only [Units.coe_map]
    show Ideal.Quotient.mk I ((uOf σ : O)) = Ideal.Quotient.mk I ((v : O))
    rw [Ideal.Quotient.eq]
    exact (hSM (uOf σ : O) (v : O)).mp (by rw [huOf σ, hv])
  have hφ_one : Units.map mkq (uOf 1) = 1 := by
    have h := hwd 1 1 ?_
    · rw [h, map_one]
    · show Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy (1 : O) =
        ((1 : ↥L ≃ₐ[F] ↥L).liftNormal (AlgebraicClosure F)) y
      rw [Eval.smulDiv_one, hlift 1, AlgEquiv.one_apply]
  -- the value of the lift of a composite
  have hlift_mul : ∀ σ τ : ↥L ≃ₐ[F] ↥L,
      ((σ * τ).liftNormal (AlgebraicClosure F)) y =
        (σ.liftNormal (AlgebraicClosure F)) ((τ.liftNormal (AlgebraicClosure F)) y) := by
    intro σ τ
    rw [hlift (σ * τ), hlift τ,
      show ((τ yL : ↥L) : AlgebraicClosure F) = algebraMap ↥L (AlgebraicClosure F) (τ yL)
        from rfl,
      AlgEquiv.liftNormal_commutes]
    rfl
  -- `𝒪[F]`-linearity of an automorphism of the level, on the orbit of `y`
  have hOlin : ∀ (σ : ↥L ≃ₐ[F] ↥L) (a : O),
      Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M (hmemσ σ) a =
        (σ.liftNormal (AlgebraicClosure F))
          (Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy a) :=
    fun σ a => (Eval.smulDiv_algEquiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M
      y hy (σ.liftNormal (AlgebraicClosure F)) (hmemσ σ) a).symm
  -- `uOf σ * uOf τ` is a valid representative for `σ * τ`
  have hkey : ∀ σ τ : ↥L ≃ₐ[F] ↥L,
      Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy
          ((uOf σ * uOf τ : Oˣ) : O) =
        ((σ * τ).liftNormal (AlgebraicClosure F)) y := by
    intro σ τ
    rw [hlift_mul σ τ, ← huOf τ]
    rw [show ((uOf σ * uOf τ : Oˣ) : O) = (uOf σ : O) * (uOf τ : O) from rfl, mul_comm]
    rw [← Eval.smulDiv_smul2 π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi
      y hy (uOf τ : O) (uOf σ : O)]
    rw [show Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M
          (Eval.smulDiv_mem π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi y hy
            (uOf σ : O)) (uOf τ : O) =
        Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M (hmemσ σ)
          (uOf τ : O) from
      Eval.smulDiv_congr π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M _
        (hmemσ σ) (huOf σ) (uOf τ : O)]
    exact hOlin σ (uOf τ : O)
  have hφ_mul : ∀ σ τ : ↥L ≃ₐ[F] ↥L,
      Units.map mkq (uOf (σ * τ)) =
        Units.map mkq (uOf σ) * Units.map mkq (uOf τ) := by
    intro σ τ
    rw [hwd (σ * τ) (uOf σ * uOf τ) (hkey σ τ), map_mul]
  let φ : (↥L ≃ₐ[F] ↥L) →* (O ⧸ I)ˣ :=
    { toFun := fun σ => Units.map mkq (uOf σ)
      map_one' := hφ_one
      map_mul' := hφ_mul }
  -- injectivity: `u_σ ≡ 1` forces `σ` to fix the whole orbit `Λ_n = {a · y}`
  have htriv : ∀ σ : ↥L ≃ₐ[F] ↥L, φ σ = 1 → σ = 1 := by
    intro σ hσ
    have hsub : (uOf σ : O) - 1 ∈ I := by
      have h1 : (Ideal.Quotient.mk I) ((uOf σ : O)) = (Ideal.Quotient.mk I) (1 : O) := by
        show mkq ((uOf σ : O)) = mkq (1 : O)
        rw [map_one]
        have h := congrArg (fun u : (O ⧸ I)ˣ => (u : O ⧸ I)) hσ
        simpa [φ, Units.coe_map] using h
      exact (Ideal.Quotient.eq).mp h1
    have hfix : ∀ x : AlgebraicClosure F,
        x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
          (NK.LocalReciprocityLubinTate.residueCard F) n →
        (σ.liftNormal (AlgebraicClosure F)) x = x := by
      intro x hx
      have hrange := Eval.range_smulDiv_eq_LTdivisionSet π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n hq hn rfl M hpi hy hy'
      have hx' : x ∈ Set.range (fun a : O =>
          Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy a) := by
        rw [hrange]; exact hx
      obtain ⟨a, rfl⟩ := hx'
      rw [← hOlin σ a]
      have step1 : Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M
            (hmemσ σ) a =
          Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy
            (a * (uOf σ : O)) := by
        rw [show Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M
              (hmemσ σ) a =
            Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M
              (Eval.smulDiv_mem π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi y hy
                (uOf σ : O)) a from
          (Eval.smulDiv_congr π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M _
            (hmemσ σ) (huOf σ) a).symm]
        exact Eval.smulDiv_smul2 π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi
          y hy a (uOf σ : O)
      rw [step1]
      have step2 : Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy
            (a * (uOf σ : O)) =
          Eval.smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy a := by
        rw [hSM (a * (uOf σ : O)) a]
        have hmem : a * ((uOf σ : O) - 1) ∈ I := Ideal.mul_mem_left I a hsub
        rw [mul_sub, mul_one] at hmem
        exact hmem
      rw [step2]
    apply ext_of_eqOn_LTdivisionSet F (π : F) (NK.LocalReciprocityLubinTate.residueCard F) n hq
    intro x hx
    have h2 : ((σ x : ↥L) : AlgebraicClosure F) = (x : AlgebraicClosure F) := by
      rw [← hfix (x : AlgebraicClosure F) hx,
        show (x : AlgebraicClosure F) = algebraMap ↥L (AlgebraicClosure F) x from rfl,
        AlgEquiv.liftNormal_commutes]
      rfl
    simpa using Subtype.coe_injective h2
  have hinj : Function.Injective φ := by
    intro σ τ h
    have h1 : φ (σ * τ⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    have h2 := htriv (σ * τ⁻¹) h1
    rwa [mul_inv_eq_one] at h2
  -- both groups have `(q-1)q^{n-1}` elements
  have hcardL : Nat.card (↥L ≃ₐ[F] ↥L)
      = (NK.LocalReciprocityLubinTate.residueCard F - 1) *
        NK.LocalReciprocityLubinTate.residueCard F ^ (n - 1) :=
    NK.LocalReciprocityLubinTate.card_aut_LTLevel_eq π hπ n hn
  have hcardΓ : Nat.card ((O ⧸ I)ˣ)
      = (NK.LocalReciprocityLubinTate.residueCard F - 1) *
        NK.LocalReciprocityLubinTate.residueCard F ^ (n - 1) := by
    simpa [O, I, NK.LocalReciprocityLubinTate.maximalIdealOfIntegers] using
      NK.LocalReciprocityLubinTate.Units.natCard_units_quot_pow_maximalIdeal F n hn
  have hne : (NK.LocalReciprocityLubinTate.residueCard F - 1) *
      NK.LocalReciprocityLubinTate.residueCard F ^ (n - 1) ≠ 0 := by
    have h2 : 0 < NK.LocalReciprocityLubinTate.residueCard F := by omega
    exact Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  haveI hfinL : Finite (↥L ≃ₐ[F] ↥L) := by
    rw [← not_infinite_iff_finite]
    intro hInf
    haveI : Infinite (↥L ≃ₐ[F] ↥L) := hInf
    rw [Nat.card_eq_zero_of_infinite] at hcardL
    exact hne hcardL.symm
  haveI hfinΓ : Finite ((O ⧸ I)ˣ) := by
    rw [← not_infinite_iff_finite]
    intro hInf
    haveI : Infinite ((O ⧸ I)ˣ) := hInf
    rw [Nat.card_eq_zero_of_infinite] at hcardΓ
    exact hne hcardΓ.symm
  haveI : Fintype (↥L ≃ₐ[F] ↥L) := Fintype.ofFinite _
  haveI : Fintype ((O ⧸ I)ˣ) := Fintype.ofFinite _
  have hcard_eq : Fintype.card (↥L ≃ₐ[F] ↥L) = Fintype.card ((O ⧸ I)ˣ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardL, hcardΓ]
  exact ⟨MulEquiv.ofBijective φ
    ((Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard_eq⟩)⟩

end NK.LocalReciprocityLubinTate.LubinTate
