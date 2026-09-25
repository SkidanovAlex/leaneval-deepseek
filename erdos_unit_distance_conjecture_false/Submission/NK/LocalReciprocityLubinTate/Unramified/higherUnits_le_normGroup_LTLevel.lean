import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools
import Submission.NK.LocalReciprocityLubinTate.Unramified.mem_normGroup_LTLevel_uniformizer
import Submission.NK.LocalReciprocityLubinTate.LubinTate.exists_ltSymbol_ker_eq
import Submission.NK.LocalReciprocityLubinTate.Unramified.normIndex_of_localField
import Submission.NK.LocalReciprocityLubinTate.Unramified.normGroup_LTLevel_le_higherUnits_sup

namespace NK.LocalReciprocityLubinTate.Unramified

universe u

/-! ### The target

**Honda's reciprocity law, `⊇` half**: every element of the `n`-th higher unit group `U^n = 1+𝔪[F]^n`
is a norm from the `n`-th Lubin–Tate level `K_n = F(Λ_n)`.

Together with `NK.LocalReciprocityLubinTate.Unramified.mem_normGroup_LTLevel_uniformizer`
(`π ∈ N_{K_n}`), the norm index theorem (`[Fˣ : N_{K_n}] = (q-1)q^{n-1}`) and the index computation
`[Fˣ : ⟨π⟩ ⊔ U^n] = (q-1)q^{n-1}` (`Units.natCard_quotient_zpowers_sup_higherUnits`), this *is*
Honda's law `N_{K_n/F}K_nˣ = ⟨π⟩ ⊔ U^n` for every `n ≥ 1`.

### State of the reduction

Everything except the classical **norm computation** is in place and proved:

* the **norm index theorem** at every finite abelian level of a characteristic-zero nonarchimedean
  local field, `normIndex_of_localField` (proved in this workspace, on top of
  `padicAlgebra_finiteDimensional_of_localField` and the commons' fundamental-class chain), which
  yields `[Fˣ : N_{K_n}] = (q-1)q^{n-1}` after transporting `K_n` into the separable closure
  (`index_normGroup_LTLevel_of_normIndex`);
* the **index computation** `[Fˣ : ⟨π⟩ ⊔ U^n] = (q-1)q^{n-1}`
  (`index_zpowers_sup_higherUnits`, from `Units.natCard_quotient_zpowers_sup_higherUnits`);
* the Lubin–Tate symbol with kernel `⟨π⟩ ⊔ U^n` (`LubinTate.exists_ltSymbol_ker_eq`), and
  `π ∈ N_{K_n}` (`mem_normGroup_LTLevel_uniformizer`).

Given these, the two subgroups `N_{K_n}` and `⟨π⟩ ⊔ U^n` of `Fˣ` have the same finite index
`(q-1)q^{n-1}`, so the target is *equivalent* to the containment
`normGroup_LTLevel_le_zpowers_sup_higherUnits` below, i.e. to the **norm computation**
`N_{K_n} ≤ ⟨π⟩ ⊔ U^n` (equivalently `Nm(𝒪[K_n]ˣ) ⊆ U^n`).  That containment is the classical
input: the `⊆` half of Honda's explicit reciprocity law (Serre, *Local Fields*, Ch. XV §5.2;
Neukirch, *ANT*, V.5.5; Yoshida, *Local class field theory via Lubin–Tate theory*, Prop. 5.10,
first inclusion), whose proof is the Coleman-operator computation of `Nm(U¹)`.  It is recorded
below (now proved: the hard input is isolated in the delegated lemma
`resultant_LTpolyEis_sub_one_mem_span` and assembled in
`normGroup_LTLevel_le_higherUnits_sup`); with it, the target is proved
mechanically by the index squeeze at the end of this file. -/

/-!
### A PROVEN-ROUTE NOTE (added after the reduction below was completed)

The classical input `normGroup_LTLevel_le_zpowers_sup_higherUnits` (i.e. `Nm(𝒪[K_n]ˣ) ⊆ U^n`) is
**not** only reachable through the power-series Coleman operator: it has an elementary
*resultant* formulation, spelled out in the docstring of
`Submission/Work/LocalReciprocityLubinTate/Unramified/resultant_LTpolyEis_sub_one_mem_span.lean`
(delegated lemma `resultant_LTpolyEis_sub_one_mem_span`), namely

`Res(LTpolyEis P q (n-1), g) ≡ 1 (mod P^n)` for every `g ∈ 𝒪[F][X]` with `g.coeff 0` a unit.

The operator `R(h)(Y) := Res_X(f(X) - Y, h(X))` (`f = LTpoly P q`) replaces Coleman's `N`: it is
multiplicative, satisfies `R(h) ≡ h (mod P)` (because the residue field is `𝔽_q`), and satisfies the
Coleman gain `h ≡ 1 (mod P^k) ⟹ R(h) ≡ 1 (mod P^{k+1})` (Newton's identities on `X^q + PX - Y`).
Iterating on `h = R(g)·g⁻¹` gives `Res(LTpolyEis P q (n-1), g) ≡ 1 (mod P^n)`, and
`Res(LTpolyEis P q (n-1), g) = Nm_{K_n/F}(g(π_n))`.  No convergence, no formal group law, no
Weierstrass preparation is needed — only `Polynomial.resultant` and the Frobenius on `𝓀[F]`.

The remaining classical step is the *total ramification* input `𝒪[K_n] = 𝒪[F][π_n]` (every integral
unit of `K_n` is a polynomial in the primitive division point), which follows from
`Nm(π_n) = (-1)^{(q-1)q^{n-1}} π = π` (`norm_root_LTpolyEis`).
-/

open scoped ValuativeRel

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

/-! ## The remaining classical input -/

/-- **Honda's norm computation (the classical input).**  The norm group of the `n`-th Lubin–Tate
level is contained in `⟨π⟩ ⊔ U^n`; equivalently `Nm(𝒪[K_n]ˣ) ⊆ U^n`.

This is the `⊆` half of Honda's explicit reciprocity law: Serre, *Local Fields*, Ch. XV §5.2;
Neukirch, *Algebraic Number Theory*, V.5.5; Yoshida, *Local class field theory via Lubin–Tate
theory*, Prop. 5.10 (first inclusion), proved there by the Coleman norm operator
`N(g) ∘ f = ∏_{α ∈ Λ₁} g(X +_f α)` together with
`u ≡ 1 (mod π^k) ⟹ N(u) ≡ 1 (mod π^{k+1})`.  It is the one ingredient of the target that is not
present in this library. -/
theorem normGroup_LTLevel_le_zpowers_sup_higherUnits (F : Type u) [Field F] [CharZero F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F)) (n : ℕ) (hn : 1 ≤ n) :
    NK.LocalReciprocity.normGroup F
        ↥(NK.LocalReciprocityLubinTate.LTLevel F (πu : F)
            (NK.LocalReciprocityLubinTate.residueCard F) n) ≤
      Subgroup.zpowers πu ⊔ NK.LocalReciprocityLubinTate.higherUnits F n :=
  NK.LocalReciprocityLubinTate.Unramified.normGroup_LTLevel_le_higherUnits_sup F πu hπ n hn

/-! ## Auxiliary lemmas (all proved) -/

/-- **Commutativity of a Galois group transports along an `F`-algebra isomorphism.** -/
private theorem commutative_of_algEquiv_local {F : Type*} {Ω Ω' : Type*} [Field F] [Field Ω]
    [Field Ω'] [Algebra F Ω] [Algebra F Ω'] (e : Ω ≃ₐ[F] Ω')
    (h : ∀ σ τ : Ω ≃ₐ[F] Ω, σ * τ = τ * σ) :
    ∀ σ τ : Ω' ≃ₐ[F] Ω', σ * τ = τ * σ := by
  intro σ τ
  apply (AlgEquiv.autCongr e.symm).injective
  rw [map_mul, map_mul]
  exact h _ _

/-- **The group-theoretic index squeeze.**  If `N ≤ A` are subgroups of a group, `N` has finite
index and `[G : N] ≤ [G : A]`, then `A ≤ N` (hence `N = A`): the relative index `[A : N]` divides
the quotient, so it must be `1`. -/
private theorem le_of_le_of_index_eq_local {G : Type*} [Group G] {N A : Subgroup G}
    (h : N ≤ A) (hN : N.index ≠ 0) (hcard : N.index ≤ A.index) : A ≤ N := by
  haveI : N.FiniteIndex := Subgroup.finiteIndex_iff.mpr hN
  have hA : A.index ≠ 0 := (Subgroup.finiteIndex_of_le h).index_ne_zero
  have hidx : A.index ≤ N.index := Subgroup.index_antitone h
  have hidxeq : N.index = A.index := le_antisymm hcard hidx
  have hrel : N.relIndex A = 1 := by
    have h1 : N.relIndex A * A.index = A.index := by
      rw [Subgroup.relIndex_mul_index h, hidxeq]
    have h2 : N.relIndex A * A.index = 1 * A.index := by
      rw [one_mul]
      exact h1
    exact mul_right_cancel₀ hA h2
  exact Subgroup.relIndex_eq_one.mp hrel

/-- **The index of the norm group of the Lubin–Tate level, from the norm index theorem.**

The Lubin–Tate level `K_n = F(Λ_n)` is realised, up to an `F`-isomorphism, inside the separable
closure of `F` (`exists_intermediateField_algEquiv_of_isSepClosed`); being abelian over `F`
(`LTLevel_commutative_of_isUniformizer`) it is a finite normal level of `F^{ab}`, where
`NormIndex F (SeparableClosure F)` applies.  Transporting the norm group back
(`normGroup_eq_of_algEquiv`, `normGroup_restrictLevel`) and using
`[F(Λ_n) : F] = (q-1)q^{n-1}` (`finrank_LTLevel_eq_of_isUniformizer`) gives the index. -/
theorem index_normGroup_LTLevel (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (π : Fˣ)
    (hπ : IsUniformizer F (π : F)) (n : ℕ) (hn : 1 ≤ n) :
    (NK.LocalReciprocity.normGroup F
      ↥(LTLevel F (π : F) (residueCard F) n)).index =
      (residueCard F - 1) * residueCard F ^ (n - 1) := by
  have hN := normIndex_of_localField F
  classical
  have hq2 : 2 ≤ residueCard F := two_le_residueCard F
  haveI : FiniteDimensional F ↥(LTLevel F (π : F) (residueCard F) n) :=
    LubinTate.finiteDimensional_LTLevel F (π : F) (residueCard F) n hq2
  haveI : IsGalois F ↥(LTLevel F (π : F) (residueCard F) n) :=
    LubinTate.isGalois_LTLevel F (π : F) (residueCard F) n hq2
  let F' := SeparableClosure F
  obtain ⟨K', ⟨eK⟩⟩ := exists_intermediateField_algEquiv_of_isSepClosed (F := F) (F' := F')
    (LTLevel F (π : F) (residueCard F) n)
  haveI hK'fd : FiniteDimensional F ↥K' :=
    FiniteDimensional.of_surjective eK.toLinearEquiv.toLinearMap eK.toLinearEquiv.surjective
  haveI hK'gal : IsGalois F ↥K' := IsGalois.of_algEquiv eK
  have hK'comm : ∀ σ τ : ↥K' ≃ₐ[F] ↥K', σ * τ = τ * σ :=
    commutative_of_algEquiv_local eK (LTLevel_commutative_of_isUniformizer F π hπ n hn)
  have hsub : K' ≤ NK.LocalReciprocity.maxAbelianSubext F F' :=
    NK.LocalReciprocity.le_maxAbelianSubext_of_commutative K' hK'comm
  have h1 : (NK.LocalReciprocity.normGroup F
      ↥(LTLevel F (π : F) (residueCard F) n)).index =
      Module.finrank F ↥(LTLevel F (π : F) (residueCard F) n) := by
    rw [NK.LocalReciprocity.normGroup_eq_of_algEquiv eK,
      ← normGroup_restrictLevel K' hsub,
      hN (restrictLevel K' hsub),
      ← LinearEquiv.finrank_eq (restrictLevelEquiv K' hsub).toLinearEquiv,
      ← LinearEquiv.finrank_eq eK.toLinearEquiv]
  rw [h1, finrank_LTLevel_eq_of_isUniformizer F π hπ n hn]

/-- **The index of `⟨π⟩ ⊔ U^n`** is `(q-1)q^{n-1}`, from the index computation
`Units.natCard_quotient_zpowers_sup_higherUnits`. -/
theorem index_zpowers_sup_higherUnits (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (π : Fˣ)
    (hπ : IsUniformizer F (π : F)) (n : ℕ) (hn : 1 ≤ n) :
    (Subgroup.zpowers π ⊔ higherUnits F n).index =
      (residueCard F - 1) * residueCard F ^ (n - 1) := by
  rw [Subgroup.index_eq_card,
    NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_sup_higherUnits F π hπ n hn]

/-! ## The target -/

/-- **Honda's reciprocity law, `⊇` half**: every element of the `n`-th higher unit group
`U^n = 1+𝔪[F]^n` is a norm from the `n`-th Lubin–Tate level `K_n = F(Λ_n)`.

Proved from the norm computation `normGroup_LTLevel_le_zpowers_sup_higherUnits`
(`N_{K_n} ≤ ⟨π⟩ ⊔ U^n`) together with the two index computations: both subgroups have index
`(q-1)q^{n-1}`, and the index squeeze makes the containment an equality. -/
theorem higherUnits_le_normGroup_LTLevel (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F)) (n : ℕ) (hn : 1 ≤ n) :
    NK.LocalReciprocityLubinTate.higherUnits F n ≤
      NK.LocalReciprocity.normGroup F
        ↥(NK.LocalReciprocityLubinTate.LTLevel F (πu : F)
            (NK.LocalReciprocityLubinTate.residueCard F) n) := by
  set N := NK.LocalReciprocity.normGroup F
    ↥(NK.LocalReciprocityLubinTate.LTLevel F (πu : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n) with hNdef
  set A := Subgroup.zpowers πu ⊔ higherUnits F n with hAdef
  have hNA : N ≤ A := by
    rw [hNdef, hAdef]
    exact normGroup_LTLevel_le_zpowers_sup_higherUnits F πu hπ n hn
  have hNidx : N.index = (residueCard F - 1) * residueCard F ^ (n - 1) := by
    rw [hNdef]
    exact index_normGroup_LTLevel F πu hπ n hn
  have hAidx : A.index = (residueCard F - 1) * residueCard F ^ (n - 1) := by
    rw [hAdef]
    exact index_zpowers_sup_higherUnits F πu hπ n hn
  have hAfinite : N.index ≠ 0 := by
    rw [hNidx]
    exact Nat.mul_ne_zero (Nat.sub_ne_zero_of_lt (two_le_residueCard F))
      (pow_ne_zero _ (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two (two_le_residueCard F))))
  have hAN : A ≤ N :=
    le_of_le_of_index_eq_local hNA hAfinite (by rw [hNidx, hAidx])
  calc higherUnits F n ≤ A := le_sup_right
    _ ≤ N := hAN
    _ = NK.LocalReciprocity.normGroup F
        ↥(NK.LocalReciprocityLubinTate.LTLevel F (πu : F)
            (NK.LocalReciprocityLubinTate.residueCard F) n) := hNdef

end

end NK.LocalReciprocityLubinTate.Unramified
