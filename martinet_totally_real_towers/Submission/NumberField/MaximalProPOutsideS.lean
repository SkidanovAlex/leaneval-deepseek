import Mathlib
import Submission.Commons.FieldTheory.Galois.isGalois_iSup_of_charZero
import Submission.Commons.FieldTheory.Galois.isPGroup_aut_of_le_iSup_finite_galois_pGroup
import Submission.Commons.NumberTheory.NumberField.differentIdeal_supp_le_iSup_finset
import Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx
import Submission.Commons.NumberTheory.NumberField.isUnramifiedAtInfinitePlaces_of_le_iSup_finset
import Submission.Commons.NumberTheory.NumberField.isUnramifiedAtInfinitePlaces_of_algEquiv

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The maximal pro-`p` extension of a number field unramified outside a finite set `S`

**STATUS: sorry-free** (this module; ON the `Submission.lean` proof path since SESSION 279 -- the
on-path proof of the benchmark statement runs through `MartinetTameWall` and this file).

This is the TAME analogue of the commons'
`Commons.FieldTheory.Galois.exists_maximal_unramified_proP_field_unramified`: instead of
requiring the extension to be unramified at EVERY finite prime (which forces class field
existence for the tower construction), we only ask that the relative different be SUPPORTED
on the rational primes in a fixed finite set `S`.  Such extensions are available by a pure
sup-construction inside the algebraic closure: no class field theory, no ray class field, no
Hilbert class field.

This is exactly the construction the "tame tower route" needs (see
`Submission/NumberField/TameTowerRoute.lean` and the SESSION 278 blocks of
`Submission/Notes.lean`): the levels are ramified only at the odd primes in `S`, hence TAME,
hence have bounded root discriminant.

## Contents

* `SupportedPField F p S` -- a finite Galois pro-`p` subextension of `AlgebraicClosure F`
  whose relative different is supported over `S`;
* `differentIdeal_supp_of_algEquiv` -- the support property is invariant under `F`-algebra
  isomorphisms;
* `exists_maximal_proP_field_unramifiedOutside` -- the maximal such extension `K/F`, with the
  universal property that every finite pro-`p` extension of `F` with `S`-supported different
  embeds into it, and with the property that every finite dimensional Galois subextension of
  `K/F` is pro-`p` with `S`-supported different.
-/

open scoped Classical
open scoped NumberField
open IntermediateField

noncomputable section

namespace Submission.NumberField

/-- A finite Galois pro-`p` subextension of `AlgebraicClosure F` whose relative different is
supported on the rational primes in `S`. -/
structure SupportedPField (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Finset ℕ) where
  L : IntermediateField F (AlgebraicClosure F)
  [hfd : FiniteDimensional F L]
  [hgal : IsGalois F L]
  [hnum : NumberField ↥L]
  hpg : IsPGroup p (L ≃ₐ[F] L)
  hsupp : ∀ (P : Ideal (NumberField.RingOfIntegers ↥L)), P.IsPrime → P ≠ ⊥ →
    P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L) →
      ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))

/-- **The "different is supported over `S`" property is invariant under `F`-algebra
isomorphisms.** -/
theorem differentIdeal_supp_of_algEquiv {F E E' : Type*} [Field F] [NumberField F] [Field E]
    [NumberField E] [Field E'] [NumberField E'] [Algebra F E] [Algebra F E'] (S : Finset ℕ)
    (e : E ≃ₐ[F] E')
    (h : ∀ (P : Ideal (𝓞 E)), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (𝓞 F) (𝓞 E) → ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) :
    ∀ (P : Ideal (𝓞 E')), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (𝓞 F) (𝓞 E') → ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
  intro P hP hPne hPdvd
  haveI : P.IsPrime := hP
  let φ : 𝓞 E ≃ₐ[𝓞 F] 𝓞 E' := NumberField.RingOfIntegers.mapAlgEquiv e
  let Q : Ideal (𝓞 E) := P.comap φ
  haveI : Q.IsPrime := Ideal.IsPrime.comap φ
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have hPbot : P = ⊥ := by
      have h1 : Ideal.map (φ : 𝓞 E →+* 𝓞 E') (P.comap φ) = ⊥ := by
        change Ideal.map (φ : 𝓞 E →+* 𝓞 E') Q = ⊥
        rw [hbot, Ideal.map_bot]
      have h2 : Ideal.map (φ : 𝓞 E →+* 𝓞 E') (Ideal.comap (φ : 𝓞 E →+* 𝓞 E') P) = P :=
        Ideal.map_comap_of_surjective (f := (φ : 𝓞 E →+* 𝓞 E')) φ.surjective P
      change Ideal.map (φ : 𝓞 E →+* 𝓞 E') (Ideal.comap (φ : 𝓞 E →+* 𝓞 E') P) = ⊥ at h1
      rw [h2] at h1
      exact h1
    exact hPne hPbot
  -- the ramification indices at `Q` and `P` agree
  have htrans : Q.ramificationIdx (𝓞 F) = P.ramificationIdx (𝓞 F) :=
    Commons.NumberTheory.RamificationInertia.ramificationIdx_comap_algEquiv (P.under (𝓞 F))
      (Ideal.under_ne_bot (𝓞 F) (P := P) hPne) φ P
  have hPram : P.ramificationIdx (𝓞 F) ≠ 1 := by
    intro h1
    exact (Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
      (E := F) (K := E') P hP).mpr h1 hPdvd
  have hQram : Q.ramificationIdx (𝓞 F) ≠ 1 := by
    rw [htrans]
    exact hPram
  have hQdvd : Q ∣ differentIdeal (𝓞 F) (𝓞 E) := by
    by_contra hcon
    exact hQram ((Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
      (E := F) (K := E) Q ‹Q.IsPrime›).mp hcon)
  obtain ⟨q, hqS, hqLies⟩ := h Q ‹Q.IsPrime› hQne hQdvd
  -- the contraction along `φ` identifies the `under` ideals over `ℤ`
  have hunder : (P.comap (φ : 𝓞 E →+* 𝓞 E')).under ℤ = P.under ℤ := by
    rw [Ideal.under_def, Ideal.under_def, Ideal.comap_comap]
    congr 1
    ext m
    simp
  have hone : Ideal.span ({(q : ℤ)} : Set ℤ) = (P.comap (φ : 𝓞 E →+* 𝓞 E')).under ℤ :=
    Ideal.LiesOver.over (P := Q) (p := Ideal.span ({(q : ℤ)} : Set ℤ)) (self := hqLies)
  exact ⟨q, hqS, Ideal.LiesOver.mk (hone.trans hunder)⟩

/-- **The maximal pro-`p` extension of `F` unramified outside `S` exists.**  It is the sup,
inside the algebraic closure, of all finite Galois pro-`p` extensions of `F` whose relative
different is supported on `S`; every such extension embeds into it, and every finite
dimensional Galois subextension of it is pro-`p` with `S`-supported different. -/
theorem exists_maximal_proP_field_unramifiedOutside
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (S : Finset ℕ) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : IsGalois F K),
      (∀ (M : Type) [Field M] [NumberField M] [Algebra F M] [IsGalois F M],
         IsPGroup p (M ≃ₐ[F] M) →
         (∀ (P : Ideal (NumberField.RingOfIntegers M)), P.IsPrime → P ≠ ⊥ →
            P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers M) →
              ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) →
         ∃ φ : M →ₐ[F] K, True) ∧
      ∀ L : IntermediateField F K, FiniteDimensional F L → IsGalois F L →
        [NumberField ↥L] →
        IsPGroup p (L ≃ₐ[F] L) ∧
          (∀ (P : Ideal (NumberField.RingOfIntegers ↥L)), P.IsPrime → P ≠ ⊥ →
            P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L) →
              ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) := by
  classical
  let Ω := AlgebraicClosure F
  let ι := SupportedPField F p S
  let f : ι → IntermediateField F Ω := fun i => i.L
  let K : IntermediateField F Ω := ⨆ i, f i
  have hfd_f : ∀ i : ι, FiniteDimensional F ↥(f i) := fun i => i.hfd
  have hgal_f : ∀ i : ι, IsGalois F ↥(f i) := fun i => i.hgal
  have hnum_f : ∀ i : ι, NumberField ↥(f i) := fun i => i.hnum
  have hpg_f : ∀ i : ι, IsPGroup p (↥(f i) ≃ₐ[F] ↥(f i)) := fun i => i.hpg
  have hsupp_f : ∀ i : ι, ∀ (P : Ideal (NumberField.RingOfIntegers ↥(f i))), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥(f i)) →
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := fun i => i.hsupp
  haveI hgal_fI : ∀ i : ι, IsGalois F ↥(f i) := hgal_f
  haveI hfd_fI : ∀ i : ι, FiniteDimensional F ↥(f i) := hfd_f
  haveI hnum_fI : ∀ i : ι, NumberField ↥(f i) := hnum_f
  have hgalK : IsGalois F ↥K := by
    dsimp [K, f]
    exact Commons.FieldTheory.Galois.isGalois_iSup_of_charZero
      (F := F) (K := Ω) (E := f)
  refine ⟨↥K, inferInstance, inferInstance, hgalK, ?_, ?_⟩
  · intro M _ _ _ _ hpg hsupp
    let e : M →ₐ[F] Ω := IsAlgClosed.lift (R := F) (S := M) (M := Ω)
    let eeq : M ≃ₐ[F] e.fieldRange := AlgEquiv.ofInjectiveField e
    haveI hfdL : FiniteDimensional F ↥(e.fieldRange) := eeq.toLinearEquiv.finiteDimensional
    haveI hgalL : IsGalois F ↥(e.fieldRange) := IsGalois.of_algEquiv eeq
    haveI hnumL : NumberField ↥(e.fieldRange) :=
      NumberField.of_module_finite F ↥(e.fieldRange)
    have hpgL : IsPGroup p (↥(e.fieldRange) ≃ₐ[F] ↥(e.fieldRange)) :=
      hpg.of_equiv (AlgEquiv.autCongr eeq)
    have hsuppL : ∀ (P : Ideal (NumberField.RingOfIntegers ↥(e.fieldRange))), P.IsPrime →
        P ≠ ⊥ →
        P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥(e.fieldRange)) →
          ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
      differentIdeal_supp_of_algEquiv (F := F) S eeq hsupp
    have hle : e.fieldRange ≤ K := by
      exact le_iSup f
        { L := e.fieldRange, hfd := hfdL, hgal := hgalL, hnum := hnumL,
          hpg := hpgL, hsupp := hsuppL }
    refine ⟨(IntermediateField.inclusion hle).comp eeq.toAlgHom, trivial⟩
  · intro L hfdL hgalL hnumL
    haveI : FiniteDimensional F ↥L := hfdL
    haveI : IsGalois F ↥L := hgalL
    haveI : NumberField ↥L := hnumL
    let vK : ↥K →ₐ[F] Ω := IntermediateField.val K
    let vL : ↥L →ₐ[F] ↥K := IntermediateField.val L
    let eL : ↥L →ₐ[F] Ω := vK.comp vL
    let L' : IntermediateField F Ω := eL.fieldRange
    let eeqL : ↥L ≃ₐ[F] ↥L' := AlgEquiv.ofInjectiveField eL
    haveI hfdL' : FiniteDimensional F ↥L' := eeqL.toLinearEquiv.finiteDimensional
    haveI hgalL' : IsGalois F ↥L' := IsGalois.of_algEquiv eeqL
    haveI hnumL' : NumberField ↥L' := NumberField.of_module_finite F ↥L'
    have hL'K : L' ≤ K := by
      intro x hx
      rcases hx with ⟨y, rfl⟩
      change ((vL y : ↥K) : Ω) ∈ K
      exact (vL y).2
    have hpgL' : IsPGroup p (↥L' ≃ₐ[F] ↥L') :=
      Commons.FieldTheory.Galois.isPGroup_aut_of_le_iSup_finite_galois_pGroup
        (F := F) (K := Ω) (p := p) (f := f) hfd_f hgal_f hpg_f hL'K
    have hsuppL' : ∀ (P : Ideal (NumberField.RingOfIntegers ↥L')), P.IsPrime → P ≠ ⊥ →
        P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L') →
          ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
      Commons.NumberTheory.NumberField.differentIdeal_supp_le_iSup_finset (F := F) S
        hfd_f hgal_f hsupp_f hL'K
    have hpgL : IsPGroup p (↥L ≃ₐ[F] ↥L) := hpgL'.of_equiv (AlgEquiv.autCongr eeqL).symm
    have hsuppL : ∀ (P : Ideal (NumberField.RingOfIntegers ↥L)), P.IsPrime → P ≠ ⊥ →
        P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L) →
          ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
      differentIdeal_supp_of_algEquiv (F := F) S eeqL.symm hsuppL'
    exact ⟨hpgL, hsuppL⟩

/-- A finite Galois pro-`p` subextension of `AlgebraicClosure F` whose relative different is
supported on `S` and which is unramified at the infinite places of `F` (so that it is TOTALLY
REAL whenever `F` is). -/
structure SupportedPFieldInf (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Finset ℕ) where
  L : IntermediateField F (AlgebraicClosure F)
  [hfd : FiniteDimensional F L]
  [hgal : IsGalois F L]
  [hnum : NumberField ↥L]
  hpg : IsPGroup p (L ≃ₐ[F] L)
  hsupp : ∀ (P : Ideal (NumberField.RingOfIntegers ↥L)), P.IsPrime → P ≠ ⊥ →
    P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L) →
      ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))
  hunrInf : IsUnramifiedAtInfinitePlaces F ↥L

/-- **The maximal pro-`p` extension of `F` unramified outside `S` and unramified at the infinite
places.**  Same construction as `exists_maximal_proP_field_unramifiedOutside`, with the
archimedean condition added, so that every finite dimensional Galois subextension of the maximal
field `K` is pro-`p`, has `S`-supported different, AND is unramified at the infinite places over
`F` -- hence totally real whenever `F` is
(`isTotallyReal_of_isUnramifiedAtInfinitePlaces`). -/
theorem exists_maximal_proP_field_unramifiedOutside_inf
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (S : Finset ℕ) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : IsGalois F K),
      (∀ (M : Type) [Field M] [NumberField M] [Algebra F M] [IsGalois F M],
         IsPGroup p (M ≃ₐ[F] M) →
         (∀ (P : Ideal (NumberField.RingOfIntegers M)), P.IsPrime → P ≠ ⊥ →
            P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers M) →
              ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) →
         IsUnramifiedAtInfinitePlaces F M →
         ∃ φ : M →ₐ[F] K, True) ∧
      ∀ L : IntermediateField F K, FiniteDimensional F L → IsGalois F L →
        [NumberField ↥L] →
        IsPGroup p (L ≃ₐ[F] L) ∧
          (∀ (P : Ideal (NumberField.RingOfIntegers ↥L)), P.IsPrime → P ≠ ⊥ →
            P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L) →
              ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) ∧
          IsUnramifiedAtInfinitePlaces F ↥L := by
  classical
  let Ω := AlgebraicClosure F
  let ι := SupportedPFieldInf F p S
  let f : ι → IntermediateField F Ω := fun i => i.L
  let K : IntermediateField F Ω := ⨆ i, f i
  have hfd_f : ∀ i : ι, FiniteDimensional F ↥(f i) := fun i => i.hfd
  have hgal_f : ∀ i : ι, IsGalois F ↥(f i) := fun i => i.hgal
  have hnum_f : ∀ i : ι, NumberField ↥(f i) := fun i => i.hnum
  have hpg_f : ∀ i : ι, IsPGroup p (↥(f i) ≃ₐ[F] ↥(f i)) := fun i => i.hpg
  have hsupp_f : ∀ i : ι, ∀ (P : Ideal (NumberField.RingOfIntegers ↥(f i))), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥(f i)) →
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := fun i => i.hsupp
  have hinr_f : ∀ i : ι, IsUnramifiedAtInfinitePlaces F ↥(f i) := fun i => i.hunrInf
  haveI hgal_fI : ∀ i : ι, IsGalois F ↥(f i) := hgal_f
  haveI hfd_fI : ∀ i : ι, FiniteDimensional F ↥(f i) := hfd_f
  haveI hnum_fI : ∀ i : ι, NumberField ↥(f i) := hnum_f
  have hgalK : IsGalois F ↥K := by
    dsimp [K, f]
    exact Commons.FieldTheory.Galois.isGalois_iSup_of_charZero (F := F) (K := Ω) (E := f)
  refine ⟨↥K, inferInstance, inferInstance, hgalK, ?_, ?_⟩
  · intro M _ _ _ _ hpg hsupp hinf
    let e : M →ₐ[F] Ω := IsAlgClosed.lift (R := F) (S := M) (M := Ω)
    let eeq : M ≃ₐ[F] e.fieldRange := AlgEquiv.ofInjectiveField e
    haveI hfdL : FiniteDimensional F ↥(e.fieldRange) := eeq.toLinearEquiv.finiteDimensional
    haveI hgalL : IsGalois F ↥(e.fieldRange) := IsGalois.of_algEquiv eeq
    haveI hnumL : NumberField ↥(e.fieldRange) :=
      NumberField.of_module_finite F ↥(e.fieldRange)
    have hpgL : IsPGroup p (↥(e.fieldRange) ≃ₐ[F] ↥(e.fieldRange)) :=
      hpg.of_equiv (AlgEquiv.autCongr eeq)
    have hsuppL : ∀ (P : Ideal (NumberField.RingOfIntegers ↥(e.fieldRange))), P.IsPrime →
        P ≠ ⊥ →
        P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥(e.fieldRange)) →
          ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
      differentIdeal_supp_of_algEquiv (F := F) S eeq hsupp
    have hinrL : IsUnramifiedAtInfinitePlaces F ↥(e.fieldRange) :=
      Commons.NumberTheory.NumberField.isUnramifiedAtInfinitePlaces_of_algEquiv (e := eeq) hinf
    have hle : e.fieldRange ≤ K := by
      exact le_iSup f
        { L := e.fieldRange, hfd := hfdL, hgal := hgalL, hnum := hnumL,
          hpg := hpgL, hsupp := hsuppL, hunrInf := hinrL }
    refine ⟨(IntermediateField.inclusion hle).comp eeq.toAlgHom, trivial⟩
  · intro L hfdL hgalL hnumL
    haveI : FiniteDimensional F ↥L := hfdL
    haveI : IsGalois F ↥L := hgalL
    haveI : NumberField ↥L := hnumL
    let vK : ↥K →ₐ[F] Ω := IntermediateField.val K
    let vL : ↥L →ₐ[F] ↥K := IntermediateField.val L
    let eL : ↥L →ₐ[F] Ω := vK.comp vL
    let L' : IntermediateField F Ω := eL.fieldRange
    let eeqL : ↥L ≃ₐ[F] ↥L' := AlgEquiv.ofInjectiveField eL
    haveI hfdL' : FiniteDimensional F ↥L' := eeqL.toLinearEquiv.finiteDimensional
    haveI hgalL' : IsGalois F ↥L' := IsGalois.of_algEquiv eeqL
    haveI hnumL' : NumberField ↥L' := NumberField.of_module_finite F ↥L'
    have hL'K : L' ≤ K := by
      intro x hx
      rcases hx with ⟨y, rfl⟩
      change ((vL y : ↥K) : Ω) ∈ K
      exact (vL y).2
    have hpgL' : IsPGroup p (↥L' ≃ₐ[F] ↥L') :=
      Commons.FieldTheory.Galois.isPGroup_aut_of_le_iSup_finite_galois_pGroup
        (F := F) (K := Ω) (p := p) (f := f) hfd_f hgal_f hpg_f hL'K
    have hsuppL' : ∀ (P : Ideal (NumberField.RingOfIntegers ↥L')), P.IsPrime → P ≠ ⊥ →
        P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L') →
          ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
      Commons.NumberTheory.NumberField.differentIdeal_supp_le_iSup_finset (F := F) S
        hfd_f hgal_f hsupp_f hL'K
    have hinrL' : IsUnramifiedAtInfinitePlaces F ↥L' :=
      Commons.NumberTheory.NumberField.isUnramifiedAtInfinitePlaces_of_le_iSup_finset
        (F := F) (f := f) hgal_f hinr_f hL'K
    have hpgL : IsPGroup p (↥L ≃ₐ[F] ↥L) := hpgL'.of_equiv (AlgEquiv.autCongr eeqL).symm
    have hsuppL : ∀ (P : Ideal (NumberField.RingOfIntegers ↥L)), P.IsPrime → P ≠ ⊥ →
        P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L) →
          ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
      differentIdeal_supp_of_algEquiv (F := F) S eeqL.symm hsuppL'
    have hinrL : IsUnramifiedAtInfinitePlaces F ↥L :=
      Commons.NumberTheory.NumberField.isUnramifiedAtInfinitePlaces_of_algEquiv
        (e := eeqL.symm) hinrL'
    exact ⟨hpgL, hsuppL, hinrL⟩


end Submission.NumberField
