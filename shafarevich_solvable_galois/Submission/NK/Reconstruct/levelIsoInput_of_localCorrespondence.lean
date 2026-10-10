import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.NK.Reconstruct.exists_aux_imaginary_level_gen
import Submission.NK.Reconstruct.exists_theta_of_prop4f3_data_gen_awayFromL_fixed
import Submission.NK.Reconstruct.levelIsoInput_of_localCorrespondence_complexPrime
import Submission.NK.Reconstruct.levelMap_inf
import Submission.NK.Reconstruct.topologicalClosure_isFrobElement_eq_top
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-pair bridge from the local correspondence, in full generality

This file proves `NK.Reconstruct.LevelIsoInputOfLocalCorrespondence K₁ K₂ ℓ`
(`Submission/Work/Reconstruct/levelPairData.lean`), the form of Shimizu's Theorem 4.0 (arXiv:2009.10431
§4) in which the complex-prime hypothesis of Proposition 4f.5 has been removed.  Shimizu removes it
by the *totally imaginary twist* (his Proposition 4f.6 and the proof of Theorem 4.0): one chooses
totally imaginary fields `L₀`, `L₀'` linearly disjoint from `K₁` and from each other, applies the
machinery of 4f.3–4f.5 to `L₁ = K₁L₀` and to `L₁' = K₁L₀'` with the **same** `τ ∈ G(Lₐᵤₓ/ℚ)`, and
intersects: `K₁ = L₁ ∩ L₁' = τ(L₂ ∩ L₂') = τ(K₂)`.

## The two cases

* if `K₁` has a complex prime, the statement is
  `NK.Reconstruct.levelIsoInput_of_localCorrespondence_complexPrime` (proved);
* if `K₁` is totally real (equivalently *no* complex prime), every finite level `L/K₁` inside `Ω` is
  totally real, and the twist is run with the two imaginary quadratic fields
  `L₀ = ℚ(i)` and `L₀' = ℚ(√(-q))`, where `q` is a rational prime splitting completely in `L`.

## Contents

* `levelGalEquiv_apply_eq` — the level isomorphism of `ψ` is `ψ` itself on underlying automorphisms;
* `levelGalEquiv_restrict` — naturality of the level isomorphism in the level;
* (`twist` section) the machinery of the twist.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. XII, Theorem 12.2.1;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

open scoped Pointwise

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-! ## Viewing a `ℚ`-level as a level over a subfield -/

/-- A `ℚ`-intermediate field of `Ω` containing `K.L` is an intermediate field over `↥K.L`; the
carrier is unchanged, so the two are interchangeable by definitional equality. -/
noncomputable def levelOfLe (K : NumFieldIn ℚ Ω) (E : IntermediateField ℚ Ω) (h : K.L ≤ E) :
    IntermediateField ↥K.L Ω :=
  E.toSubfield.toIntermediateField (fun x => h x.2)

theorem mem_levelOfLe (K : NumFieldIn ℚ Ω) (E : IntermediateField ℚ Ω) (h : K.L ≤ E) {x : Ω} :
    x ∈ levelOfLe K E h ↔ x ∈ E := Iff.rfl

@[simp] theorem levelOfLe_coe (K : NumFieldIn ℚ Ω) (E : IntermediateField ℚ Ω) (h : K.L ≤ E) :
    ((levelOfLe K E h : IntermediateField ↥K.L Ω) : Set Ω) = (E : Set Ω) := rfl

/-- Restriction of automorphisms to a sub-level: for `L ≤ M` levels over the same base,
`Gal(Ω/↥M) →* Gal(Ω/↥L)`. -/
noncomputable def galRestrictLevel {K : NumFieldIn ℚ Ω} {L M : IntermediateField ↥K.L Ω}
    (hLM : L ≤ M) : (Ω ≃ₐ[↥M] Ω) →* (Ω ≃ₐ[↥L] Ω) where
  toFun g := { g.toRingEquiv with commutes' := fun c => g.commutes' ⟨c.1, hLM c.2⟩ }
  map_one' := by ext x; rfl
  map_mul' g g' := by ext x; rfl

@[simp] theorem galRestrictLevel_apply {K : NumFieldIn ℚ Ω} {L M : IntermediateField ↥K.L Ω}
    (hLM : L ≤ M) (g : Ω ≃ₐ[↥M] Ω) : ⇑(galRestrictLevel hLM g) = ⇑g := rfl

/-! ## The level isomorphism attached to `ψ` is `ψ` on underlying automorphisms -/

section LevelIso

variable (K₁ K₂ : NumFieldIn ℚ Ω) [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω]
variable (ψ : Gal(Ω/↥K₁.L) ≃* Gal(Ω/↥K₂.L)) (hψ : IsHomeomorph ψ)

/-- **The level isomorphism of `ψ` is `ψ` on underlying automorphisms.**  For a finite level
`L` over `↥K₁.L` and `g : Gal(Ω/↥L)`, the automorphism `levelGalEquiv ψ hψ L g` of `Ω` is
`ψ (g ↾ ↥K₁.L)`. -/
theorem levelGalEquiv_apply_eq (L : IntermediateField ↥K₁.L Ω) [FiniteDimensional ↥K₁.L L]
    (g : Gal(Ω/↥L)) :
    (NK.ReconstructField.levelGalEquiv ψ hψ L g : Ω → Ω)
      = (ψ (g.restrictScalars ↥K₁.L) : Ω → Ω) := by
  ext x
  rfl

/-- **Naturality of the level isomorphism in the level.**  For levels `L ≤ M` over `↥K₁.L` the
two induced isomorphisms of absolute Galois groups agree on underlying automorphisms. -/
theorem levelGalEquiv_restrict {L M : IntermediateField ↥K₁.L Ω} (hLM : L ≤ M)
    [FiniteDimensional ↥K₁.L L] [FiniteDimensional ↥K₁.L M] (g : Gal(Ω/↥M)) :
    ((NK.ReconstructField.levelGalEquiv ψ hψ L (galRestrictLevel hLM g) : Ω → Ω))
      = (NK.ReconstructField.levelGalEquiv ψ hψ M g : Ω → Ω) := by
  rw [levelGalEquiv_apply_eq, levelGalEquiv_apply_eq]
  rfl

end LevelIso

/-! ## The chain of Shimizu's Proposition 4f.3 along the base change

The `σ̄`'s of the several level pairs used by the totally imaginary twist are *not* independent: each
is induced by the same homeomorphism `ψ`, and the induced isomorphisms `Γ_L ≃* Γ_{levelMap ψ L}` are
compatible with the base changes `π_{M/K}` of Shimizu's Lemma 4f.4.  This is the square

```
   Γ_M  --σ̄_M-->  Γ_{levelMap ψ M}
    |                    |
 π_{M/A}            π_{B_M/B_A}
    v                    v
   Γ_A  --σ̄_A-->  Γ_{levelMap ψ A}
```

(`NK.Reconstruct.sigmaBar_compat_gen` below), from which the identity
`σ̄ ∘ π_{E/K₁} = π_{E/K₂} ∘ τ^*` of Proposition 4f.3 at a large pair descends to every sub-pair with
the *same* `τ` (`NK.Reconstruct.prop4f3_identity_of_le_gen`).  The latter is what makes Shimizu's
intersection argument legitimate.

The two lemmas below are the versions of `NK.Reconstruct.sigmaBar_compat` and its auxiliary
naturality statement for the present file (where `NumFieldIn.ofLevel` is at hand, so that the lemmas
can be stated without importing `sigmaBar_compat.lean`, which would be a circular import). -/

section Chain

variable (K₁ K₂ : NumFieldIn ℚ Ω) [FiniteDimensional ℚ ↥K₁.L] [NumberField ↥K₁.L]
variable [FiniteDimensional ℚ ↥K₂.L] [NumberField ↥K₂.L]
variable [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω]

/-- **The restriction along a `ℚ`-level inclusion and along the same inclusion of levels over
`↥K.L` agree.** -/
theorem galRestrict_ofLevel_eq_galRestrictLevel_gen
    {A M : IntermediateField ↥K₁.L Ω} [FiniteDimensional ↥K₁.L A] [FiniteDimensional ↥K₁.L M]
    (hAM : A ≤ M) (hAM' : (NumFieldIn.ofLevel K₁ A).L ≤ (NumFieldIn.ofLevel K₁ M).L)
    (σ : Gal(Ω/↥M)) :
    galRestrict hAM' σ = galRestrictLevel (K := K₁) hAM σ :=
  AlgEquiv.ext (fun _ => rfl)

/-- **Naturality of the level isomorphism of `ψ` in the level**, in the form used by the base
change: the level isomorphism at `A` applied to the restriction of `σ` is the restriction to
`levelMap ψ A` of the level isomorphism at `M` applied to `σ`. -/
theorem levelGalEquiv_galRestrict_ofLevel_gen
    (ψ : Gal(Ω/↥K₁.L) ≃* Gal(Ω/↥K₂.L)) (hψ : IsHomeomorph ψ)
    {A M : IntermediateField ↥K₁.L Ω} [FiniteDimensional ↥K₁.L A] [FiniteDimensional ↥K₁.L M]
    [NumberField ↥A] [NumberField ↥M]
    [FiniteDimensional ↥K₂.L (levelMap ψ A)] [NumberField ↥(levelMap ψ A)]
    [FiniteDimensional ↥K₂.L (levelMap ψ M)] [NumberField ↥(levelMap ψ M)]
    (hAM : A ≤ M)
    (hAM' : (NumFieldIn.ofLevel K₁ A).L ≤ (NumFieldIn.ofLevel K₁ M).L)
    (hBM' : (NumFieldIn.ofLevel K₂ (levelMap ψ A)).L
      ≤ (NumFieldIn.ofLevel K₂ (levelMap ψ M)).L)
    (σ : Gal(Ω/↥M)) :
    NK.ReconstructField.levelGalEquiv ψ hψ A (galRestrict hAM' σ)
      = galRestrict hBM' (NK.ReconstructField.levelGalEquiv ψ hψ M σ) := by
  have key := levelGalEquiv_restrict K₁ K₂ ψ hψ hAM σ
  refine AlgEquiv.ext (fun x => ?_)
  have e1 : (NK.ReconstructField.levelGalEquiv ψ hψ A (galRestrict hAM' σ)) x
      = (NK.ReconstructField.levelGalEquiv ψ hψ A
          (galRestrictLevel (K := K₁) hAM σ)) x :=
    congrArg (fun f => (NK.ReconstructField.levelGalEquiv ψ hψ A f) x)
      (galRestrict_ofLevel_eq_galRestrictLevel_gen K₁ hAM hAM' σ)
  have e2 : (galRestrict hBM' (NK.ReconstructField.levelGalEquiv ψ hψ M σ)) x
      = (NK.ReconstructField.levelGalEquiv ψ hψ M σ) x :=
    congrFun (galRestrict_apply hBM' _) x
  rw [e1, congrFun key x]
  exact e2.symm

/-- **The compatibility square of the several `σ̄`'s with the base change.** -/
theorem sigmaBar_compat_gen
    (ψ : Gal(Ω/↥K₁.L) ≃* Gal(Ω/↥K₂.L)) (hψ : IsHomeomorph ψ) (ℓ : ℕ) [Fact ℓ.Prime]
    {A M : IntermediateField ↥K₁.L Ω} [FiniteDimensional ↥K₁.L A] [FiniteDimensional ↥K₁.L M]
    [NumberField ↥A] [NumberField ↥M]
    [FiniteDimensional ↥K₂.L (levelMap ψ A)] [NumberField ↥(levelMap ψ A)]
    [FiniteDimensional ↥K₂.L (levelMap ψ M)] [NumberField ↥(levelMap ψ M)]
    [IsSepClosure ↥(levelMap ψ A) Ω] [IsSepClosure ↥(levelMap ψ M) Ω]
    (hAM : A ≤ M)
    (hAM' : (NumFieldIn.ofLevel K₁ A).L ≤ (NumFieldIn.ofLevel K₁ M).L)
    (hBM' : (NumFieldIn.ofLevel K₂ (levelMap ψ A)).L
      ≤ (NumFieldIn.ofLevel K₂ (levelMap ψ M)).L)
    (σbarA : Gamma ↥A Ω ℓ ≃* Gamma ↥(levelMap ψ A) Ω ℓ)
    (σbarM : Gamma ↥M Ω ℓ ≃* Gamma ↥(levelMap ψ M) Ω ℓ)
    (hσbarA : ∀ g : Gal(Ω/↥A),
      σbarA (galToGamma (K := ↥A) (K' := Ω) ℓ g)
        = galToGamma (K := ↥(levelMap ψ A)) (K' := Ω) ℓ
            (NK.ReconstructField.levelGalEquiv ψ hψ A g))
    (hσbarM : ∀ g : Gal(Ω/↥M),
      σbarM (galToGamma (K := ↥M) (K' := Ω) ℓ g)
        = galToGamma (K := ↥(levelMap ψ M)) (K' := Ω) ℓ
            (NK.ReconstructField.levelGalEquiv ψ hψ M g)) :
    ∀ γ : Gamma ↥M Ω ℓ,
      σbarA (generalBaseChange (NumFieldIn.ofLevel K₁ A) (NumFieldIn.ofLevel K₁ M) hAM' ℓ γ)
        = generalBaseChange (NumFieldIn.ofLevel K₂ (levelMap ψ A))
            (NumFieldIn.ofLevel K₂ (levelMap ψ M)) hBM' ℓ (σbarM γ) := by
  intro γ
  haveI : IsSepClosure ↥M Ω := isSepClosure_level M
  haveI : IsGalois ↥M Ω := IsSepClosure.isGalois
  obtain ⟨σ, rfl⟩ := galToGamma_surjective (K := ↥M) (K' := Ω) ℓ γ
  have hnat : NK.ReconstructField.levelGalEquiv ψ hψ A (galRestrict hAM' σ)
      = galRestrict hBM' (NK.ReconstructField.levelGalEquiv ψ hψ M σ) :=
    levelGalEquiv_galRestrict_ofLevel_gen K₁ K₂ ψ hψ hAM hAM' hBM' σ
  have hAtotal : σbarA (generalBaseChange (NumFieldIn.ofLevel K₁ A) (NumFieldIn.ofLevel K₁ M)
        hAM' ℓ (galToGamma (K := ↥M) (K' := Ω) ℓ σ))
      = galToGamma (K := ↥(levelMap ψ A)) (K' := Ω) ℓ
          (NK.ReconstructField.levelGalEquiv ψ hψ A (galRestrict hAM' σ)) :=
    (congrArg σbarA (generalBaseChange_galToGamma (NumFieldIn.ofLevel K₁ A)
      (NumFieldIn.ofLevel K₁ M) hAM' ℓ σ)).trans (hσbarA _)
  have hBtotal : generalBaseChange (NumFieldIn.ofLevel K₂ (levelMap ψ A))
        (NumFieldIn.ofLevel K₂ (levelMap ψ M)) hBM' ℓ
        (σbarM (galToGamma (K := ↥M) (K' := Ω) ℓ σ))
      = galToGamma (K := ↥(levelMap ψ A)) (K' := Ω) ℓ
          (galRestrict hBM' (NK.ReconstructField.levelGalEquiv ψ hψ M σ)) :=
    (congrArg (fun t => generalBaseChange (NumFieldIn.ofLevel K₂ (levelMap ψ A))
        (NumFieldIn.ofLevel K₂ (levelMap ψ M)) hBM' ℓ t) (hσbarM σ)).trans
      (generalBaseChange_galToGamma (NumFieldIn.ofLevel K₂ (levelMap ψ A))
        (NumFieldIn.ofLevel K₂ (levelMap ψ M)) hBM' ℓ
        (NK.ReconstructField.levelGalEquiv ψ hψ M σ))
  exact hAtotal.trans ((congrArg (galToGamma (K := ↥(levelMap ψ A)) (K' := Ω) ℓ) hnat).trans
    hBtotal.symm)


/-! ## Complex infinite places -/

/-- **A number field in which `-1` is a square has a complex infinite place.** -/
theorem exists_isComplex_of_sq_eq_neg_one_gen (K : Type*) [Field K] [NumberField K] {i : K}
    (hi : i ^ 2 = -1) :
    ∃ v : NumberField.InfinitePlace K, NumberField.InfinitePlace.IsComplex v := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨NumberField.InfinitePlace.mk φ, ?_⟩
  rw [NumberField.InfinitePlace.isComplex_mk_iff]
  intro hreal
  have hc : (((hreal.embedding i : ℝ)) : ℂ) ^ 2 = -1 := by
    rw [show (((hreal.embedding i : ℝ)) : ℂ) = φ i by simp]
    rw [← map_pow, hi, map_neg, map_one]
  have h2 : ((hreal.embedding i : ℝ)) ^ 2 = -1 := by exact_mod_cast hc
  nlinarith [sq_nonneg (hreal.embedding i)]

/-- **A number field in which `-q`, `q > 0` rational, is a square has a complex infinite
place.** -/
theorem exists_isComplex_of_sq_eq_neg_gen (K : Type*) [Field K] [NumberField K] {w : K} {q : ℚ}
    (hq : 0 < q) (hw : w ^ 2 = -(q : K)) :
    ∃ v : NumberField.InfinitePlace K, NumberField.InfinitePlace.IsComplex v := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨NumberField.InfinitePlace.mk φ, ?_⟩
  rw [NumberField.InfinitePlace.isComplex_mk_iff]
  intro hreal
  have hz : (((hreal.embedding w : ℝ)) : ℂ) = φ w :=
    NumberField.ComplexEmbedding.IsReal.coe_embedding_apply hreal w
  have hc : (((hreal.embedding w : ℝ)) : ℂ) ^ 2 = -(q : ℂ) := by
    rw [hz, ← map_pow, hw, map_neg, map_ratCast]
  have h2 : ((hreal.embedding w : ℝ)) ^ 2 = -(q : ℝ) := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_ratCast]
    exact hc
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  nlinarith [sq_nonneg (hreal.embedding w), hqR]

set_option maxHeartbeats 8000000 in
/-- **The identity of Shimizu's Proposition 4f.3 descends to sub-pairs, with the same `τ`.**

If the identity `σ̄_M ∘ π_{E/M} = π_{E/levelMap ψ M} ∘ τ^*` holds at the pair `(M, levelMap ψ M)`, then
it holds at every sub-pair `(A, levelMap ψ A)`, `A ≤ M`, with the *same* `τ ∈ Gal(E)`: both sides are
computed by the transitivity of the base change and by the compatibility square
`σ̄_A ∘ π_{M/A} = π_{levelMap ψ M/levelMap ψ A} ∘ σ̄_M` (`sigmaBar_compat_gen`), and the base change
`π_{levelMap ψ M/levelMap ψ A}` carries the identity to the Hausdorff torsion-free quotient because it
is continuous (`gammaHausMk_eq_one_of_continuous`). -/
theorem prop4f3_identity_of_le_gen
    (ψ : Gal(Ω/↥K₁.L) ≃* Gal(Ω/↥K₂.L)) (hψ : IsHomeomorph ψ) (ℓ : ℕ) [Fact ℓ.Prime]
    {A M : IntermediateField ↥K₁.L Ω} (hAM : A ≤ M)
    [FiniteDimensional ↥K₁.L A] [FiniteDimensional ↥K₁.L M]
    [NumberField ↥A] [NumberField ↥M]
    [FiniteDimensional ↥K₂.L (levelMap ψ A)] [NumberField ↥(levelMap ψ A)]
    [FiniteDimensional ↥K₂.L (levelMap ψ M)] [NumberField ↥(levelMap ψ M)]
    [IsSepClosure ↥(levelMap ψ A) Ω] [IsSepClosure ↥(levelMap ψ M) Ω]
    (E : FrobLevel ℚ Ω)
    (hAE : (NumFieldIn.ofLevel K₁ A).L ≤ E.L)
    (hME : (NumFieldIn.ofLevel K₁ M).L ≤ E.L)
    (hBAE : (NumFieldIn.ofLevel K₂ (levelMap ψ A)).L ≤ E.L)
    (hBME : (NumFieldIn.ofLevel K₂ (levelMap ψ M)).L ≤ E.L)
    (Θ : Gal(↥E.L/ℚ) → Ω ≃ₐ[ℚ] Ω)
    (hΘmem : ∀ τ, ∀ x : Ω, x ∈ E.L ↔ Θ τ x ∈ E.L)
    (τ : Gal(↥E.L/ℚ))
    (σbarA : Gamma ↥A Ω ℓ ≃* Gamma ↥(levelMap ψ A) Ω ℓ)
    (σbarM : Gamma ↥M Ω ℓ ≃* Gamma ↥(levelMap ψ M) Ω ℓ)
    (hσbarA : ∀ g : Gal(Ω/↥A),
      σbarA (galToGamma (K := ↥A) (K' := Ω) ℓ g)
        = galToGamma (K := ↥(levelMap ψ A)) (K' := Ω) ℓ
            (NK.ReconstructField.levelGalEquiv ψ hψ A g))
    (hσbarM : ∀ g : Gal(Ω/↥M),
      σbarM (galToGamma (K := ↥M) (K' := Ω) ℓ g)
        = galToGamma (K := ↥(levelMap ψ M)) (K' := Ω) ℓ
            (NK.ReconstructField.levelGalEquiv ψ hψ M g))
    (hbig : ∀ γ : Gamma ↥E.L Ω ℓ,
      gammaHausMk (K := ↥(levelMap ψ M)) (K' := Ω) ℓ
          (σbarM (ambientPi (NumFieldIn.ofLevel K₁ M) E hME ℓ γ))
        = gammaHausMk (K := ↥(levelMap ψ M)) (K' := Ω) ℓ
            (ambientPi (NumFieldIn.ofLevel K₂ (levelMap ψ M)) E hBME ℓ
              (tauStar E.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ))) :
    ∀ γ : Gamma ↥E.L Ω ℓ,
      gammaHausMk (K := ↥(levelMap ψ A)) (K' := Ω) ℓ
          (σbarA (ambientPi (NumFieldIn.ofLevel K₁ A) E hAE ℓ γ))
        = gammaHausMk (K := ↥(levelMap ψ A)) (K' := Ω) ℓ
            (ambientPi (NumFieldIn.ofLevel K₂ (levelMap ψ A)) E hBAE ℓ
              (tauStar E.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ)) := by
  intro γ
  -- instances
  haveI hsepE : IsSepClosure ↥E.L Ω := isSepClosure_of_le E.L
  haveI hsepOA : IsSepClosure ↥(NumFieldIn.ofLevel K₁ A).L Ω := isSepClosure_ofLevel K₁ A
  haveI hsepOM : IsSepClosure ↥(NumFieldIn.ofLevel K₁ M).L Ω := isSepClosure_ofLevel K₁ M
  haveI hsepBA : IsSepClosure ↥(NumFieldIn.ofLevel K₂ (levelMap ψ A)).L Ω :=
    isSepClosure_ofLevel K₂ (levelMap ψ A)
  haveI hsepBM : IsSepClosure ↥(NumFieldIn.ofLevel K₂ (levelMap ψ M)).L Ω :=
    isSepClosure_ofLevel K₂ (levelMap ψ M)
  -- the inclusions of the underlying `ℚ`-levels
  have hAM' : (NumFieldIn.ofLevel K₁ A).L ≤ (NumFieldIn.ofLevel K₁ M).L := fun x hx => hAM hx
  have hBM' : (NumFieldIn.ofLevel K₂ (levelMap ψ A)).L
      ≤ (NumFieldIn.ofLevel K₂ (levelMap ψ M)).L :=
    NK.ReconstructField.levelMap_monotone ψ hAM
  -- the compatibility square of the two `σ̄`'s
  have hsq := sigmaBar_compat_gen K₁ K₂ ψ hψ ℓ (A := A) (M := M) hAM hAM' hBM' σbarA σbarM
    hσbarA hσbarM
  -- the transitivity of the base change on the two sides
  have e1 : ambientPi (NumFieldIn.ofLevel K₁ A) E hAE ℓ γ
      = generalBaseChange (NumFieldIn.ofLevel K₁ A) (NumFieldIn.ofLevel K₁ M) hAM' ℓ
          (ambientPi (NumFieldIn.ofLevel K₁ M) E hME ℓ γ) :=
    (DFunLike.congr_fun (generalBaseChange_comp_ambientPi (NumFieldIn.ofLevel K₁ A)
      (NumFieldIn.ofLevel K₁ M) E hAM' hME ℓ) γ).symm
  have e2 : ambientPi (NumFieldIn.ofLevel K₂ (levelMap ψ A)) E hBAE ℓ
        (tauStar E.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ)
      = generalBaseChange (NumFieldIn.ofLevel K₂ (levelMap ψ A))
          (NumFieldIn.ofLevel K₂ (levelMap ψ M)) hBM' ℓ
          (ambientPi (NumFieldIn.ofLevel K₂ (levelMap ψ M)) E hBME ℓ
            (tauStar E.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ)) :=
    (DFunLike.congr_fun (generalBaseChange_comp_ambientPi (NumFieldIn.ofLevel K₂ (levelMap ψ A))
      (NumFieldIn.ofLevel K₂ (levelMap ψ M)) E hBM' hBME ℓ) _).symm
  -- the identity at the large pair, pushed forward along the continuous base change
  have hcont : Continuous ⇑(generalBaseChange (NumFieldIn.ofLevel K₂ (levelMap ψ A))
      (NumFieldIn.ofLevel K₂ (levelMap ψ M)) hBM' ℓ) :=
    generalBaseChange_continuous _ _ hBM' ℓ
  have hpush : gammaHausMk (K := ↥(levelMap ψ A)) (K' := Ω) ℓ
        (generalBaseChange (NumFieldIn.ofLevel K₂ (levelMap ψ A))
          (NumFieldIn.ofLevel K₂ (levelMap ψ M)) hBM' ℓ
          (σbarM (ambientPi (NumFieldIn.ofLevel K₁ M) E hME ℓ γ)))
      = gammaHausMk (K := ↥(levelMap ψ A)) (K' := Ω) ℓ
        (generalBaseChange (NumFieldIn.ofLevel K₂ (levelMap ψ A))
          (NumFieldIn.ofLevel K₂ (levelMap ψ M)) hBM' ℓ
          (ambientPi (NumFieldIn.ofLevel K₂ (levelMap ψ M)) E hBME ℓ
            (tauStar E.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ))) := by
    -- both sides are the descent `gammaHausLift` of the two `gammaHausMk`-values at the large pair
    have hL := (gammaHausLift_comp (K₁ := ↥(NumFieldIn.ofLevel K₂ (levelMap ψ M)).L) (K₁' := Ω)
      (K₂ := ↥(NumFieldIn.ofLevel K₂ (levelMap ψ A)).L) (K₂' := Ω) ℓ
      (generalBaseChange (NumFieldIn.ofLevel K₂ (levelMap ψ A))
        (NumFieldIn.ofLevel K₂ (levelMap ψ M)) hBM' ℓ) hcont
      (σbarM (ambientPi (NumFieldIn.ofLevel K₁ M) E hME ℓ γ))).symm
    erw [hL, hbig γ]
    exact gammaHausLift_comp (K₁ := ↥(NumFieldIn.ofLevel K₂ (levelMap ψ M)).L) (K₁' := Ω)
      (K₂ := ↥(NumFieldIn.ofLevel K₂ (levelMap ψ A)).L) (K₂' := Ω) ℓ
      (generalBaseChange (NumFieldIn.ofLevel K₂ (levelMap ψ A))
        (NumFieldIn.ofLevel K₂ (levelMap ψ M)) hBM' ℓ) hcont
      (ambientPi (NumFieldIn.ofLevel K₂ (levelMap ψ M)) E hBME ℓ
        (tauStar E.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ))
  calc gammaHausMk (K := ↥(levelMap ψ A)) (K' := Ω) ℓ
        (σbarA (ambientPi (NumFieldIn.ofLevel K₁ A) E hAE ℓ γ))
      = gammaHausMk (K := ↥(levelMap ψ A)) (K' := Ω) ℓ
          (σbarA (generalBaseChange (NumFieldIn.ofLevel K₁ A) (NumFieldIn.ofLevel K₁ M) hAM' ℓ
            (ambientPi (NumFieldIn.ofLevel K₁ M) E hME ℓ γ))) := by rw [e1]
    _ = gammaHausMk (K := ↥(levelMap ψ A)) (K' := Ω) ℓ
          (generalBaseChange (NumFieldIn.ofLevel K₂ (levelMap ψ A))
            (NumFieldIn.ofLevel K₂ (levelMap ψ M)) hBM' ℓ
            (σbarM (ambientPi (NumFieldIn.ofLevel K₁ M) E hME ℓ γ))) := by
        rw [hsq (ambientPi (NumFieldIn.ofLevel K₁ M) E hME ℓ γ)]
    _ = gammaHausMk (K := ↥(levelMap ψ A)) (K' := Ω) ℓ
          (generalBaseChange (NumFieldIn.ofLevel K₂ (levelMap ψ A))
            (NumFieldIn.ofLevel K₂ (levelMap ψ M)) hBM' ℓ
            (ambientPi (NumFieldIn.ofLevel K₂ (levelMap ψ M)) E hBME ℓ
              (tauStar E.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ))) := hpush
    _ = gammaHausMk (K := ↥(levelMap ψ A)) (K' := Ω) ℓ
          (ambientPi (NumFieldIn.ofLevel K₂ (levelMap ψ A)) E hBAE ℓ
            (tauStar E.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ)) :=
        congrArg (fun z => gammaHausMk (K := ↥(levelMap ψ A)) (K' := Ω) ℓ z) e2.symm

end Chain

/-! ## The statement -/

theorem levelIsoInput_of_localCorrespondence {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] (K₁ K₂ : NK.Reconstruct.NumFieldIn ℚ Ω)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] (ℓ : ℕ) [Fact ℓ.Prime] :
    NK.Reconstruct.LevelIsoInputOfLocalCorrespondence K₁ K₂ ℓ := by
  intro ψ hψ a b hH hM hR hc L hLfd
  by_cases hcomplex : ∃ v : NumberField.InfinitePlace ↥K₁.L, NumberField.InfinitePlace.IsComplex v
  · exact levelIsoInput_of_localCorrespondence_complexPrime K₁ K₂ ℓ ψ hψ a b hcomplex hH hM hR hc L
  · -- ## Case 2: `K₁` has no complex prime — the totally imaginary twist
    classical
    -- ## instances at the level `L` and at its image
    haveI hNfd : FiniteDimensional ↥K₂.L (levelMap ψ L) := finiteDimensional_levelMap hψ L
    haveI hNnf : NumberField ↥(levelMap ψ L) := numberField_levelMap hψ L
    haveI hLnf : NumberField ↥L :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField L
    haveI hsepL : IsSepClosure ↥L Ω := isSepClosure_level L
    haveI hsepN : IsSepClosure ↥(levelMap ψ L) Ω := isSepClosure_level (levelMap ψ L)
    -- ## the two auxiliary imaginary quadratic extensions of `L`
    obtain ⟨i, y, q, hi, hy, hqpos, hinf⟩ := exists_aux_imaginary_level_gen K₁ L
    -- ## the enlarged levels over `↥K₁.L`
    haveI hfdi : FiniteDimensional ↥K₁.L (IntermediateField.adjoin ↥K₁.L ({i} : Set Ω)) :=
      IntermediateField.adjoin.finiteDimensional
        ⟨Polynomial.X ^ 2 + Polynomial.C 1, Polynomial.monic_X_pow_add_C (1 : ↥K₁.L) (by norm_num),
          by simp [hi]⟩
    haveI hfdy : FiniteDimensional ↥K₁.L (IntermediateField.adjoin ↥K₁.L ({y} : Set Ω)) :=
      IntermediateField.adjoin.finiteDimensional
        ⟨Polynomial.X ^ 2 + Polynomial.C (q : ↥K₁.L),
          Polynomial.monic_X_pow_add_C (q : ↥K₁.L) (by norm_num), by simp [hy]⟩
    let l₁ : IntermediateField ↥K₁.L Ω := L ⊔ IntermediateField.adjoin ↥K₁.L ({i} : Set Ω)
    let l₁' : IntermediateField ↥K₁.L Ω := L ⊔ IntermediateField.adjoin ↥K₁.L ({y} : Set Ω)
    haveI hl₁fd : FiniteDimensional ↥K₁.L l₁ := IntermediateField.finiteDimensional_sup L _
    haveI hl₁'fd : FiniteDimensional ↥K₁.L l₁' := IntermediateField.finiteDimensional_sup L _
    haveI hl₁nf : NumberField ↥l₁ :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField l₁
    haveI hl₁'nf : NumberField ↥l₁' :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField l₁'
    haveI hfd₁ : FiniteDimensional ↥K₂.L (levelMap ψ l₁) := finiteDimensional_levelMap hψ l₁
    haveI hfd₁' : FiniteDimensional ↥K₂.L (levelMap ψ l₁') := finiteDimensional_levelMap hψ l₁'
    haveI hnf₁ : NumberField ↥(levelMap ψ l₁) := numberField_levelMap hψ l₁
    haveI hnf₁' : NumberField ↥(levelMap ψ l₁') := numberField_levelMap hψ l₁'
    haveI hsepL₁ : IsSepClosure ↥l₁ Ω := isSepClosure_level l₁
    haveI hsepL₁' : IsSepClosure ↥l₁' Ω := isSepClosure_level l₁'
    haveI hsepl₁ : IsSepClosure ↥(levelMap ψ l₁) Ω := isSepClosure_level (levelMap ψ l₁)
    haveI hsepl₁' : IsSepClosure ↥(levelMap ψ l₁') Ω := isSepClosure_level (levelMap ψ l₁')
    -- ## the `NumFieldIn`s of the twisted pairs
    let A₁ : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₁ l₁
    let A₁' : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₁ l₁'
    let B₁ : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₂ (levelMap ψ l₁)
    let B₁' : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₂ (levelMap ψ l₁')
    let m₁ : IntermediateField ↥K₁.L Ω := l₁ ⊔ l₁'
    haveI hm₁fd : FiniteDimensional ↥K₁.L m₁ := IntermediateField.finiteDimensional_sup l₁ l₁'
    haveI hm₁nf : NumberField ↥m₁ :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField m₁
    haveI hfdm : FiniteDimensional ↥K₂.L (levelMap ψ m₁) := finiteDimensional_levelMap hψ m₁
    haveI hnflm : NumberField ↥(levelMap ψ m₁) := numberField_levelMap hψ m₁
    haveI hsepM : IsSepClosure ↥m₁ Ω := isSepClosure_level m₁
    haveI hseplm : IsSepClosure ↥(levelMap ψ m₁) Ω := isSepClosure_level (levelMap ψ m₁)
    let M₁ : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₁ m₁
    let M₂ : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₂ (levelMap ψ m₁)
    -- ## the inclusions of the underlying `ℚ`-levels
    have hl₁m₁ : l₁ ≤ m₁ := le_sup_left
    have hl₁'m₁ : l₁' ≤ m₁ := le_sup_right
    have hA₁M₁ : A₁.L ≤ M₁.L := hl₁m₁
    have hA₁'M₁ : A₁'.L ≤ M₁.L := hl₁'m₁
    have hB₁M₂ : B₁.L ≤ M₂.L := NK.ReconstructField.levelMap_monotone ψ hl₁m₁
    have hB₁'M₂ : B₁'.L ≤ M₂.L := NK.ReconstructField.levelMap_monotone ψ hl₁'m₁
    -- ## an auxiliary finite Galois level of `Ω/ℚ` containing everything
    obtain ⟨E, hM₁E, hM₂E⟩ := exists_frobLevel_sup M₁ M₂
    haveI hsepE : IsSepClosure ↥E.L Ω := isSepClosure_of_le E.L
    have hA₁E : A₁.L ≤ E.L := le_trans hA₁M₁ hM₁E
    have hA₁'E : A₁'.L ≤ E.L := le_trans hA₁'M₁ hM₁E
    have hB₁E : B₁.L ≤ E.L := le_trans hB₁M₂ hM₂E
    have hB₁'E : B₁'.L ≤ E.L := le_trans hB₁'M₂ hM₂E
    -- ## separability of everything
    haveI hsepA₁ : IsSepClosure ↥A₁.L Ω := isSepClosure_ofLevel K₁ l₁
    haveI hsepA₁' : IsSepClosure ↥A₁'.L Ω := isSepClosure_ofLevel K₁ l₁'
    haveI hsepB₁ : IsSepClosure ↥B₁.L Ω := isSepClosure_ofLevel K₂ (levelMap ψ l₁)
    haveI hsepB₁' : IsSepClosure ↥B₁'.L Ω := isSepClosure_ofLevel K₂ (levelMap ψ l₁')
    haveI hsepM₁ : IsSepClosure ↥M₁.L Ω := isSepClosure_ofLevel K₁ m₁
    haveI hsepM₂ : IsSepClosure ↥M₂.L Ω := isSepClosure_ofLevel K₂ (levelMap ψ m₁)
    -- ## the isomorphisms `σ̄` of the ℓ-adic abelianisations of the three pairs
    obtain ⟨σbar₁, hσbar₁cont, hσbar₁compat, -⟩ :=
      exists_gammaEquivOfPhi_continuous (NK.ReconstructField.levelGalEquiv ψ hψ l₁)
        (isHomeomorph_levelGalEquiv ψ hψ l₁) ℓ
    obtain ⟨σbar₁', hσbar₁'cont, hσbar₁'compat, -⟩ :=
      exists_gammaEquivOfPhi_continuous (NK.ReconstructField.levelGalEquiv ψ hψ l₁')
        (isHomeomorph_levelGalEquiv ψ hψ l₁') ℓ
    obtain ⟨σbarM, hσbarMcont, hσbarMcompat, -⟩ :=
      exists_gammaEquivOfPhi_continuous (NK.ReconstructField.levelGalEquiv ψ hψ m₁)
        (isHomeomorph_levelGalEquiv ψ hψ m₁) ℓ
    -- ## the prime correspondence and the Frobenius correspondence of the large pair
    have hbij := NK.ReconstructField.levelPrimeMapGen_bijective ψ hψ a m₁
    let primeMap : NK.Chebotarev.PrimeIdeal ↥M₁.L ≃ NK.Chebotarev.PrimeIdeal ↥M₂.L :=
      Equiv.ofBijective _ hbij
    have hprimeMap (𝔭 : NK.Chebotarev.PrimeIdeal ↥M₁.L) :
        primeMap 𝔭 = NK.ReconstructField.levelPrimeMapGen ψ hψ a m₁ 𝔭 :=
      Equiv.ofBijective_apply _ _ 𝔭
    have hchar : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal ↥M₁.L,
        Ideal.under ℤ (primeMap 𝔭).asIdeal = Ideal.under ℤ 𝔭.asIdeal := by
      intro 𝔭
      have hp : NK.LocalInputs.primeBelowNat ↥M₂.L (primeMap 𝔭) =
          NK.LocalInputs.primeBelowNat ↥M₁.L 𝔭 := by
        rw [hprimeMap 𝔭]
        exact NK.ReconstructField.primeBelowNat_levelPrimeMapGen ψ hψ a m₁ 𝔭
      have hp' : NK.LocalInputs.primeBelow ↥M₂.L (primeMap 𝔭) =
          NK.LocalInputs.primeBelow ↥M₁.L 𝔭 :=
        Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext hp)
      rw [← Ideal.under_under (A := ℤ) (B := NumberField.RingOfIntegers ℚ)
          (C := NumberField.RingOfIntegers ↥M₂.L) (primeMap 𝔭).asIdeal,
        ← Ideal.under_under (A := ℤ) (B := NumberField.RingOfIntegers ℚ)
          (C := NumberField.RingOfIntegers ↥M₁.L) 𝔭.asIdeal,
        ← NK.LocalInputs.primeBelow_asIdeal ↥M₂.L (primeMap 𝔭),
        ← NK.LocalInputs.primeBelow_asIdeal ↥M₁.L 𝔭, hp']
    have hb : ∀ (𝔭 : NK.Chebotarev.PrimeIdeal ↥M₁.L), SplitsCompletelyOverRat 𝔭 →
        ∀ (p : ℕ), CharP (NumberField.RingOfIntegers ↥M₁.L ⧸ 𝔭.asIdeal) p → p ≠ ℓ →
        ∀ (g₁ : Gal(Ω/↥M₁.L)) (g₂ : Gal(Ω/↥M₂.L)),
          IsFrobElementAt 𝔭 g₁ → IsFrobElementAt (primeMap 𝔭) g₂ →
          gammaHausMk (K := ↥M₂.L) (K' := Ω) ℓ
              (σbarM (galToGamma (K := ↥M₁.L) (K' := Ω) ℓ g₁)) =
            gammaHausMk (K := ↥M₂.L) (K' := Ω) ℓ
              (galToGamma (K := ↥M₂.L) (K' := Ω) ℓ g₂) := by
      intro 𝔭 hsplit p hpchar hpne g₁ g₂ hg₁ hg₂
      have hpb : CharP (NumberField.RingOfIntegers ↥M₁.L ⧸ 𝔭.asIdeal)
          (NK.LocalInputs.primeBelowNat ↥M₁.L 𝔭) :=
        NK.ReconstructField.charP_of_liesOver 𝔭 (NK.LocalInputs.primeBelow ↥M₁.L 𝔭)
          (NK.LocalInputs.primeBelow_liesOver ↥M₁.L 𝔭)
      have hprime : p.Prime := by
        rw [← CharP.eq _ hpb hpchar]
        exact (Rat.HeightOneSpectrum.primesEquiv (NK.LocalInputs.primeBelow ↥M₁.L 𝔭)).2
      haveI : Fact p.Prime := ⟨hprime⟩
      have hg2x : IsFrobElementAt (NK.ReconstructField.levelPrimeMapGen ψ hψ a m₁ 𝔭) g₂ :=
        show IsFrobElementAt (primeMap 𝔭) g₂ from hg₂
      exact frobCorrespondenceGammaHaus_levelSplit ℓ ψ hψ a b m₁ σbarM hσbarMcompat p 𝔭 hsplit
        hpchar hpne g₁ g₂ hg₁ hg2x
    -- ## the escaping prime of Proposition 4f.3
    have hescape : ∀ (H : Gal(↥E.L/ℚ) → Subgroup (Gamma ↥E.L Ω ℓ)),
        (∀ i, IsClosed ((H i : Set (Gamma ↥E.L Ω ℓ)))) →
        (∀ i, ¬ IsOpen ((H i : Set (Gamma ↥E.L Ω ℓ)))) →
        ∃ (𝔭 : NK.Chebotarev.PrimeIdeal ↥E.L) (σ : Gal(Ω/↥E.L)),
          SplitsCompletelyOverRat 𝔭 ∧
          (∀ p : ℕ, CharP (NumberField.RingOfIntegers ↥E.L ⧸ 𝔭.asIdeal) p → p ≠ ℓ) ∧
          IsFrobElementAt 𝔭 σ ∧ ∀ i, galToGamma (K := ↥E.L) (K' := Ω) ℓ σ ∉ H i := by
      intro H hcl hopen
      haveI : Finite (Gal(↥E.L/ℚ)) := inferInstance
      obtain ⟨𝔭, σ, hfrob, hsplit, hpne, hout⟩ :=
        exists_splitIsFrobElementAt_notMem_iUnion_closedSubgroup_awayFromL hc E ℓ H hcl hopen
      refine ⟨𝔭, σ, hsplit, ?_, hfrob, hout⟩
      intro p hpchar
      have hpb : CharP (NumberField.RingOfIntegers ↥E.L ⧸ 𝔭.asIdeal)
          (NK.LocalInputs.primeBelowNat ↥E.L 𝔭) :=
        NK.ReconstructField.charP_of_liesOver 𝔭 (NK.LocalInputs.primeBelow ↥E.L 𝔭)
          (NK.LocalInputs.primeBelow_liesOver ↥E.L 𝔭)
      rw [← CharP.eq _ hpb hpchar]
      exact hpne
    -- ## the section `Θ` of the restriction `Gal(Ω/ℚ) → Gal(E.L/ℚ)`
    haveI hEfin := E.finite
    haveI hEnorm : Normal ℚ ↥E.L := by
      have he : (E.L.algebra' : Algebra ℚ ↥E.L) = (inferInstance : Algebra ℚ ↥E.L) :=
        Subsingleton.elim _ _
      exact Eq.mp (congrArg (fun a : Algebra ℚ ↥E.L => @Normal ℚ ↥E.L _ _ a) he) E.normal
    let Θ : Gal(↥E.L/ℚ) → Ω ≃ₐ[ℚ] Ω := fun τ => (exists_algEquiv_extends E.L τ).choose
    have hΘmem : ∀ τ, ∀ x : Ω, x ∈ E.L ↔ Θ τ x ∈ E.L :=
      fun τ => (exists_algEquiv_extends E.L τ).choose_spec.1
    have hΘres : ∀ τ (x : ↥E.L), Θ τ (x : Ω) = ((τ x : ↥E.L) : Ω) :=
      fun τ x => (exists_algEquiv_extends E.L τ).choose_spec.2 x
    -- ## Shimizu's Proposition 4f.3 at the large pair
    obtain ⟨τ, hτM⟩ := prop4f3_awayFromL M₁ M₂ E hM₁E hM₂E ℓ σbarM hσbarMcont primeMap hb hchar
      (fun τ => (Θ τ : Ω ≃+* Ω)) (fun τ => hΘmem τ) (fun τ x => hΘres τ x) hescape
    -- ## the same identity at the two sub-pairs, with the same `τ`
    have hτ₁ : ∀ γ : Gamma ↥E.L Ω ℓ,
        gammaHausMk (K := ↥(levelMap ψ l₁)) (K' := Ω) ℓ (σbar₁ (ambientPi A₁ E hA₁E ℓ γ))
          = gammaHausMk (K := ↥(levelMap ψ l₁)) (K' := Ω) ℓ
              (ambientPi B₁ E hB₁E ℓ (tauStar E.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ)) :=
      prop4f3_identity_of_le_gen K₁ K₂ ψ hψ ℓ (A := l₁) (M := m₁) hl₁m₁ E hA₁E hM₁E hB₁E hM₂E
        Θ hΘmem τ σbar₁ σbarM hσbar₁compat hσbarMcompat hτM
    have hτ₁' : ∀ γ : Gamma ↥E.L Ω ℓ,
        gammaHausMk (K := ↥(levelMap ψ l₁')) (K' := Ω) ℓ (σbar₁' (ambientPi A₁' E hA₁'E ℓ γ))
          = gammaHausMk (K := ↥(levelMap ψ l₁')) (K' := Ω) ℓ
              (ambientPi B₁' E hB₁'E ℓ (tauStar E.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ)) :=
      prop4f3_identity_of_le_gen K₁ K₂ ψ hψ ℓ (A := l₁') (M := m₁) hl₁'m₁ E hA₁'E hM₁E hB₁'E hM₂E
        Θ hΘmem τ σbar₁' σbarM hσbar₁'compat hσbarMcompat hτM
    -- ## the complex primes of the twisted fields
    have hi_l₁ : i ∈ l₁ := by
      have hle : IntermediateField.adjoin ↥K₁.L ({i} : Set Ω) ≤ l₁ := le_sup_right
      exact hle (IntermediateField.subset_adjoin ↥K₁.L ({i} : Set Ω) (by simp))
    have hy_l₁' : y ∈ l₁' := by
      have hle : IntermediateField.adjoin ↥K₁.L ({y} : Set Ω) ≤ l₁' := le_sup_right
      exact hle (IntermediateField.subset_adjoin ↥K₁.L ({y} : Set Ω) (by simp))
    have hi_A₁ : i ∈ A₁.L := hi_l₁
    have hy_A₁' : y ∈ A₁'.L := hy_l₁'
    have hi_M₁ : i ∈ M₁.L := by
      have hle : l₁ ≤ m₁ := le_sup_left
      exact hle hi_l₁
    have hcomplexA₁ : ∃ v : NumberField.InfinitePlace ↥A₁.L,
        NumberField.InfinitePlace.IsComplex v :=
      exists_isComplex_of_sq_eq_neg_one_gen ↥A₁.L (i := ⟨i, hi_A₁⟩) (by
        apply Subtype.ext
        push_cast
        exact hi)
    have hcomplexA₁' : ∃ v : NumberField.InfinitePlace ↥A₁'.L,
        NumberField.InfinitePlace.IsComplex v :=
      exists_isComplex_of_sq_eq_neg_gen ↥A₁'.L (w := ⟨y, hy_A₁'⟩) (q := (q : ℚ))
        (by exact_mod_cast hqpos) (by
          apply Subtype.ext
          push_cast
          exact hy)
    have hcomplexM₁ : ∃ v : NumberField.InfinitePlace ↥M₁.L,
        NumberField.InfinitePlace.IsComplex v :=
      exists_isComplex_of_sq_eq_neg_one_gen ↥M₁.L (i := ⟨i, hi_M₁⟩) (by
        apply Subtype.ext
        push_cast
        exact hi)
    -- ## Shimizu's Theorem 4.0 at the two sub-pairs
    have h45 : Fourf5InputGen Ω ℓ := fourf5_gen_of_rankInputs ℓ hH hM hR
    have hEq₁ : A₁.L = B₁.L.map (Θ τ).symm.toAlgHom :=
      exists_theta_of_prop4f3_data_gen_awayFromL_fixed A₁ B₁ E hA₁E hB₁E ℓ σbar₁ hσbar₁cont
        Θ hΘmem (fun τ x => hΘres τ x) τ hτ₁ hcomplexA₁ h45
    have hEq₁' : A₁'.L = B₁'.L.map (Θ τ).symm.toAlgHom :=
      exists_theta_of_prop4f3_data_gen_awayFromL_fixed A₁' B₁' E hA₁'E hB₁'E ℓ σbar₁' hσbar₁'cont
        Θ hΘmem (fun τ x => hΘres τ x) τ hτ₁' hcomplexA₁' h45
    -- ## the intersection: `L = τ(levelMap ψ L)`
    have hfin : l₁ ⊓ l₁' = L := hinf
    have hAinf : A₁.L ⊓ A₁'.L = (NumFieldIn.ofLevel K₁ L).L := by
      refine le_antisymm ?_ ?_
      · intro x hx
        rw [IntermediateField.mem_inf] at hx
        have hx' : x ∈ l₁ ⊓ l₁' := by
          rw [IntermediateField.mem_inf]
          exact ⟨hx.1, hx.2⟩
        rw [hinf] at hx'
        exact hx'
      · intro x hx
        have hxL : x ∈ L := hx
        have hxl₁ : x ∈ l₁ := (le_sup_left : L ≤ l₁) hxL
        have hxl₁' : x ∈ l₁' := (le_sup_left : L ≤ l₁') hxL
        rw [IntermediateField.mem_inf]
        exact ⟨hxl₁, hxl₁'⟩
    have hXeq : B₁.L ⊓ B₁'.L = (NumFieldIn.ofLevel K₂ (levelMap ψ L)).L := by
      have hlinf : levelMap ψ (l₁ ⊓ l₁') = levelMap ψ l₁ ⊓ levelMap ψ l₁' :=
        levelMap_inf K₁ K₂ ψ hψ l₁ l₁'
      refine le_antisymm ?_ ?_
      · intro x hx
        rw [IntermediateField.mem_inf] at hx
        have hx' : x ∈ levelMap ψ l₁ ⊓ levelMap ψ l₁' := by
          rw [IntermediateField.mem_inf]
          exact ⟨hx.1, hx.2⟩
        rw [← hlinf, hfin] at hx'
        exact hx'
      · intro x hx
        have hx' : x ∈ levelMap ψ l₁ ⊓ levelMap ψ l₁' := by
          rw [← hlinf, hfin]
          exact hx
        rw [IntermediateField.mem_inf] at hx'
        exact ⟨hx'.1, hx'.2⟩
    -- ## the field isomorphism of the level pair
    have hmapinf : (B₁.L ⊓ B₁'.L).map (Θ τ).symm.toAlgHom = A₁.L ⊓ A₁'.L := by
      rw [IntermediateField.map_inf (B₁.L) (B₁'.L) (Θ τ).symm.toAlgHom, ← hEq₁, ← hEq₁']
    have hmain : Nonempty
        (↥((B₁.L ⊓ B₁'.L).map (Θ τ).symm.toAlgHom) ≃+* ↥(B₁.L ⊓ B₁'.L)) := by
      letI : Algebra ℚ ↥(B₁.L ⊓ B₁'.L) := (B₁.L ⊓ B₁'.L).algebra'
      letI : Algebra ℚ ↥((B₁.L ⊓ B₁'.L).map (Θ τ).symm.toAlgHom) :=
        ((B₁.L ⊓ B₁'.L).map (Θ τ).symm.toAlgHom).algebra'
      exact ⟨(IntermediateField.equivMap (B₁.L ⊓ B₁'.L) (Θ τ).symm.toAlgHom).symm.toRingEquiv⟩
    rw [hmapinf, hAinf, hXeq] at hmain
    exact hmain

end NK.Reconstruct
