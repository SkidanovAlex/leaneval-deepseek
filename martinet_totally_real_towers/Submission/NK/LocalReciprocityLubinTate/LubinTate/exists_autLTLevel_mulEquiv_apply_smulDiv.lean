import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.nonempty_autLTLevel_mulEquiv_units
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

/-! ### Plan for the prover

`NK.LocalReciprocityLubinTate.LubinTate.nonempty_autLTLevel_mulEquiv_units` states only that
`Gal(K_n/F)` is *isomorphic* to `(𝒪[F]/𝔪[F]^n)^×`.  For the explicit reciprocity law one needs the
canonical isomorphism, characterised by its action on a primitive division point:
`σ_u(y) = [u](y)`.

**Three traps already caught by review.**
(1) The domain must be the **quotient** `(↥𝒪[F] ⧸ 𝔪[F]^n)ˣ` — `(↥𝒪[F])ˣ` is infinite while
`Gal(K_n/F)` has `(q-1)q^{n-1}` elements.
(2) The right-hand side must be the **Lubin–Tate action** `Eval.smulDiv`, *not* the field product
`(↑u : F) * y`: the group law is only `[u](X) ≡ uX (mod deg 2)`, so e.g. `[1+πⁿ](y) = y` while
`(1+πⁿ)·y ≠ y`.
(3) **The Lubin–Tate module `M` is a hypothesis, not an inner binder** (this was the defect in the
first version of this statement, caught by review): `LubinTateModule` carries `toLaw` and `action` as
data and `hpi` pins only the `π`-series, so `∃ e, ∀ M hpi, …` would demand an unproved independence
of the action from `M`.  The statement below therefore takes `M` and `hpi` as hypotheses, exactly as
`nonempty_autLTLevel_mulEquiv_units` does.

Sketch of the proof.

* For `u : ↥𝒪[F]` whose class in `𝒪[F]/𝔪[F]^n` is a unit, the assignment `x ↦ u · x = smulDiv … u`
  is a bijection of `Λ_n` (inverse given by any lift of `u⁻¹`; use `Eval.smulDiv_smul2`,
  `Eval.smulDiv_one`), so it extends to a unique `F`-algebra automorphism of `K_n = F(y)`:
  `ltLevelIsSimple_residueCard`, `LTLevel_eq_adjoin_singleton_of_isSimple`,
  `IntermediateField.algHom_ext_of_eq_adjoin`, `LubinTate.ext_of_eqOn_LTdivisionSet`.
* Well-definedness in `u` uses `Eval.smulDiv_eq_iff_sub_mem` (`a · y = b · y ↔ a - b ∈ 𝔪[F]^n`).
* Multiplicativity: `σ_u(σ_v(y)) = σ_u(v·y) = v·(σ_u y) = v·(u·y) = (uv)·y` by
  `Eval.smulDiv_algEquiv` and `Eval.smulDiv_smul2` (plus commutativity of `𝒪[F]`).
* Bijectivity by the cardinality count `Units.natCard_units_quot_pow_maximalIdeal` together with
  `card_aut_LTLevel_eq` (both `(q-1)q^{n-1}`); alternatively reuse the inverse homomorphism
  constructed inside `nonempty_autLTLevel_mulEquiv_units` and identify it by extensionality at `y`.

`hyp` is genuinely needed (`y = 0` would trivialise the action). -/

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

/-- **The canonical Lubin–Tate reciprocity isomorphism, normalised at a primitive division point.**

Let `F` be a nonarchimedean local field of characteristic zero, `π ∈ 𝒪[F]` irreducible (a
uniformiser), `M` a Lubin–Tate module for `π` with `π`-series `πX + X^q`, and `y ∈ Λ_n ∖ Λ_{n-1}` a
*primitive* `π^n`-division point, so that `K_n = F(y)`.

Then the reciprocity isomorphism `(𝒪[F]/𝔪[F]^n)ˣ ≃* Gal(K_n/F)` can be chosen so that the
automorphism attached to a unit class `u` acts on `y` by the Lubin–Tate group law:

  `σ_u(y) = [u](y)`   (`Eval.smulDiv`).

This pins down the isomorphism of `nonempty_autLTLevel_mulEquiv_units` uniquely. -/
theorem exists_autLTLevel_mulEquiv_apply_smulDiv {F : Type u} [Field F] [CharZero F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (P : ↥(ValuativeRel.valuation F).integer) (hP : Irreducible P) (n : ℕ) (hn : 1 ≤ n)
    (M : NK.LocalReciprocityLubinTate.LubinTateModule ↥(ValuativeRel.valuation F).integer P
          (NK.LocalReciprocityLubinTate.residueCard F))
    (hpi : M.toLaw.piEndo = NK.LocalReciprocityLubinTate.piXAddXq P
          (NK.LocalReciprocityLubinTate.residueCard F))
    (y : AlgebraicClosure F)
    (hy : y ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (P : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n)
    (hyp : y ∉ NK.LocalReciprocityLubinTate.LTdivisionSet F (P : F)
      (NK.LocalReciprocityLubinTate.residueCard F) (n - 1)) :
    ∃ e : (↥(ValuativeRel.valuation F).integer ⧸
            (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer) ^ n)ˣ ≃*
          (↥(NK.LocalReciprocityLubinTate.LTLevel F (P : F)
              (NK.LocalReciprocityLubinTate.residueCard F) n) ≃ₐ[F]
            ↥(NK.LocalReciprocityLubinTate.LTLevel F (P : F)
              (NK.LocalReciprocityLubinTate.residueCard F) n)),
      ∀ (u : ↥(ValuativeRel.valuation F).integer)
        (hu : IsUnit (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer) ^ n) u)),
        ((e hu.unit) ⟨y, NK.LocalReciprocityLubinTate.LTdivisionSet_subset_LTLevel F (P : F)
            (NK.LocalReciprocityLubinTate.residueCard F) n hy⟩ :
            AlgebraicClosure F) =
          NK.LocalReciprocityLubinTate.Eval.smulDiv P hP
            (NK.LocalReciprocityLubinTate.residueCard F) n
            (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hy u := by
  classical
  have hq : 2 ≤ residueCard F := two_le_residueCard F
  let L := LTLevel F (P : F) (residueCard F) n
  let O := ↥(ValuativeRel.valuation F).integer
  let I : Ideal O := (IsLocalRing.maximalIdeal O) ^ n
  let mkq : O →* (O ⧸ I) := (Ideal.Quotient.mk I).toMonoidHom
  change ∃ e : (O ⧸ I)ˣ ≃* (↥L ≃ₐ[F] ↥L),
      ∀ (u : O) (hu : IsUnit (Ideal.Quotient.mk I u)),
        (((e hu.unit) ⟨y, LTdivisionSet_subset_LTLevel F (P : F) (residueCard F) n hy⟩ : ↥L) :
            AlgebraicClosure F) = Eval.smulDiv P hP (residueCard F) n hq M hy u
  let yL : ↥L := ⟨y, LTdivisionSet_subset_LTLevel F (P : F) (residueCard F) n hy⟩
  -- the `𝒪[F]`-action is injective on the multiples of a primitive point
  have hSM : ∀ a b : O,
      Eval.smulDiv P hP (residueCard F) n hq M hy a
        = Eval.smulDiv P hP (residueCard F) n hq M hy b ↔ a - b ∈ I :=
    fun a b => smulDiv_eq_iff_sub_mem P hP n hn M hpi hy hyp a b
  -- an automorphism of the level, read on the primitive point `y`
  have hlift : ∀ σ : ↥L ≃ₐ[F] ↥L,
      (σ.liftNormal (AlgebraicClosure F)) y = ((σ yL : ↥L) : AlgebraicClosure F) := by
    intro σ
    rw [show y = algebraMap ↥L (AlgebraicClosure F) yL from rfl, AlgEquiv.liftNormal_commutes]
    rfl
  have hmemσ : ∀ σ : ↥L ≃ₐ[F] ↥L,
      (σ.liftNormal (AlgebraicClosure F)) y ∈ LTdivisionSet F (P : F) (residueCard F) n :=
    fun σ => (mem_LTdivisionSet_algEquiv_iff (P : F) (residueCard F) n hq
      (σ.liftNormal (AlgebraicClosure F)) y).mpr hy
  have hprimσ : ∀ σ : ↥L ≃ₐ[F] ↥L,
      (σ.liftNormal (AlgebraicClosure F)) y ∉ LTdivisionSet F (P : F) (residueCard F) (n - 1) :=
    fun σ h => hyp ((mem_LTdivisionSet_algEquiv_iff (P : F) (residueCard F) (n - 1) hq
      (σ.liftNormal (AlgebraicClosure F)) y).mp h)
  -- the unit attached to `σ` by the orbit of `y`
  have hex : ∀ σ : ↥L ≃ₐ[F] ↥L, ∃ u : Oˣ,
      Eval.smulDiv P hP (residueCard F) n hq M hy (u : O)
        = (σ.liftNormal (AlgebraicClosure F)) y :=
    fun σ => exists_unit_smulDiv_eq_of_primitive P hP n hn M hpi hy hyp (hmemσ σ) (hprimσ σ)
  let uOf : (↥L ≃ₐ[F] ↥L) → Oˣ := fun σ => Classical.choose (hex σ)
  have huOf : ∀ σ, Eval.smulDiv P hP (residueCard F) n hq M hy (uOf σ : O)
      = (σ.liftNormal (AlgebraicClosure F)) y := fun σ => Classical.choose_spec (hex σ)
  -- the class of `uOf σ` in `(𝒪[F]/𝔪^n)ˣ` depends only on `σ`
  have hwd : ∀ (σ : ↥L ≃ₐ[F] ↥L) (v : Oˣ),
      Eval.smulDiv P hP (residueCard F) n hq M hy (v : O)
        = (σ.liftNormal (AlgebraicClosure F)) y →
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
    · show Eval.smulDiv P hP (residueCard F) n hq M hy (1 : O) =
        ((1 : ↥L ≃ₐ[F] ↥L).liftNormal (AlgebraicClosure F)) y
      rw [Eval.smulDiv_one, hlift 1, AlgEquiv.one_apply]
  -- the value of the lift of a composite
  have hlift_mul : ∀ σ τ : ↥L ≃ₐ[F] ↥L,
      ((σ * τ).liftNormal (AlgebraicClosure F)) y =
        (σ.liftNormal (AlgebraicClosure F)) ((τ.liftNormal (AlgebraicClosure F)) y) := by
    intro σ τ
    rw [hlift (σ * τ), hlift τ,
      show ((τ yL : ↥L) : AlgebraicClosure F) = algebraMap ↥L (AlgebraicClosure F) (τ yL)
        from rfl, AlgEquiv.liftNormal_commutes]
    rfl
  -- `𝒪[F]`-linearity of an automorphism of the level, on the orbit of `y`
  have hOlin : ∀ (σ : ↥L ≃ₐ[F] ↥L) (a : O),
      Eval.smulDiv P hP (residueCard F) n hq M (hmemσ σ) a =
        (σ.liftNormal (AlgebraicClosure F))
          (Eval.smulDiv P hP (residueCard F) n hq M hy a) :=
    fun σ a => (Eval.smulDiv_algEquiv P hP (residueCard F) n hq M
      y hy (σ.liftNormal (AlgebraicClosure F)) (hmemσ σ) a).symm
  -- `uOf σ * uOf τ` is a valid representative for `σ * τ`
  have hkey : ∀ σ τ : ↥L ≃ₐ[F] ↥L,
      Eval.smulDiv P hP (residueCard F) n hq M hy ((uOf σ * uOf τ : Oˣ) : O) =
        ((σ * τ).liftNormal (AlgebraicClosure F)) y := by
    intro σ τ
    rw [hlift_mul σ τ, ← huOf τ]
    rw [show ((uOf σ * uOf τ : Oˣ) : O) = (uOf σ : O) * (uOf τ : O) from rfl, mul_comm]
    rw [← Eval.smulDiv_smul2 P hP (residueCard F) n hq M hpi y hy (uOf τ : O) (uOf σ : O)]
    rw [show Eval.smulDiv P hP (residueCard F) n hq M
          (Eval.smulDiv_mem P hP (residueCard F) n hq M hpi y hy (uOf σ : O)) (uOf τ : O) =
        Eval.smulDiv P hP (residueCard F) n hq M (hmemσ σ) (uOf τ : O) from
      Eval.smulDiv_congr P hP (residueCard F) n hq M _ (hmemσ σ) (huOf σ) (uOf τ : O)]
    exact hOlin σ (uOf τ : O)
  have hφ_mul : ∀ σ τ : ↥L ≃ₐ[F] ↥L, Units.map mkq (uOf (σ * τ)) =
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
      have h1 : Ideal.Quotient.mk I ((uOf σ : O)) = Ideal.Quotient.mk I (1 : O) := by
        show mkq ((uOf σ : O)) = mkq (1 : O)
        rw [map_one]
        have h := congrArg (fun u : (O ⧸ I)ˣ => (u : O ⧸ I)) hσ
        simpa [φ, Units.coe_map] using h
      exact (Ideal.Quotient.eq).mp h1
    have hfix : ∀ x : AlgebraicClosure F,
        x ∈ LTdivisionSet F (P : F) (residueCard F) n →
        (σ.liftNormal (AlgebraicClosure F)) x = x := by
      intro x hx
      have hrange := Eval.range_smulDiv_eq_LTdivisionSet P hP (residueCard F) n hq hn rfl M hpi hy hyp
      have hx' : x ∈ Set.range (fun a : O => Eval.smulDiv P hP (residueCard F) n hq M hy a) := by
        rw [hrange]; exact hx
      obtain ⟨a, rfl⟩ := hx'
      rw [← hOlin σ a]
      have step1 : Eval.smulDiv P hP (residueCard F) n hq M (hmemσ σ) a =
          Eval.smulDiv P hP (residueCard F) n hq M hy (a * (uOf σ : O)) := by
        rw [show Eval.smulDiv P hP (residueCard F) n hq M (hmemσ σ) a =
            Eval.smulDiv P hP (residueCard F) n hq M
              (Eval.smulDiv_mem P hP (residueCard F) n hq M hpi y hy (uOf σ : O)) a from
          (Eval.smulDiv_congr P hP (residueCard F) n hq M _ (hmemσ σ) (huOf σ) a).symm]
        exact Eval.smulDiv_smul2 P hP (residueCard F) n hq M hpi y hy a (uOf σ : O)
      rw [step1]
      have step2 : Eval.smulDiv P hP (residueCard F) n hq M hy (a * (uOf σ : O)) =
          Eval.smulDiv P hP (residueCard F) n hq M hy a := by
        rw [hSM (a * (uOf σ : O)) a]
        have hmem : a * ((uOf σ : O) - 1) ∈ I := Ideal.mul_mem_left I a hsub
        rw [mul_sub, mul_one] at hmem
        exact hmem
      rw [step2]
    apply ext_of_eqOn_LTdivisionSet F (P : F) (residueCard F) n hq
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
  have hcardL : Nat.card (↥L ≃ₐ[F] ↥L) = (residueCard F - 1) * residueCard F ^ (n - 1) :=
    card_aut_LTLevel_eq P hP n hn
  have hcardΓ : Nat.card ((O ⧸ I)ˣ) = (residueCard F - 1) * residueCard F ^ (n - 1) := by
    simpa [O, I, maximalIdealOfIntegers] using
      NK.LocalReciprocityLubinTate.Units.natCard_units_quot_pow_maximalIdeal F n hn
  have hne : (residueCard F - 1) * residueCard F ^ (n - 1) ≠ 0 := by
    have h2 : 0 < residueCard F := by omega
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
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard_eq⟩
  let E : (↥L ≃ₐ[F] ↥L) ≃* (O ⧸ I)ˣ := MulEquiv.ofBijective φ hbij
  -- the inverse isomorphism and its value at a unit class
  refine ⟨E.symm, ?_⟩
  intro u hu
  have hφσ : φ (E.symm hu.unit) = hu.unit := E.apply_symm_apply hu.unit
  have hclass : Ideal.Quotient.mk I ((uOf (E.symm hu.unit) : O)) = Ideal.Quotient.mk I u := by
    have h1 : Units.map mkq (uOf (E.symm hu.unit)) = hu.unit := hφσ
    have hcoe := congrArg (fun x : (O ⧸ I)ˣ => (x : O ⧸ I)) h1
    rw [Units.coe_map] at hcoe
    show mkq ((uOf (E.symm hu.unit) : O)) = mkq u
    rw [hcoe]
    exact hu.unit_spec
  have hsub : (uOf (E.symm hu.unit) : O) - u ∈ I := (Ideal.Quotient.eq).mp hclass
  have hsm : Eval.smulDiv P hP (residueCard F) n hq M hy (uOf (E.symm hu.unit) : O)
      = Eval.smulDiv P hP (residueCard F) n hq M hy u :=
    (hSM (uOf (E.symm hu.unit) : O) u).mpr hsub
  calc (((E.symm hu.unit) ⟨y, LTdivisionSet_subset_LTLevel F (P : F) (residueCard F) n hy⟩ : ↥L) :
        AlgebraicClosure F)
      = (E.symm hu.unit).liftNormal (AlgebraicClosure F) y := (hlift (E.symm hu.unit)).symm
    _ = Eval.smulDiv P hP (residueCard F) n hq M hy (uOf (E.symm hu.unit) : O) :=
        (huOf (E.symm hu.unit)).symm
    _ = Eval.smulDiv P hP (residueCard F) n hq M hy u := hsm

end NK.LocalReciprocityLubinTate.LubinTate
