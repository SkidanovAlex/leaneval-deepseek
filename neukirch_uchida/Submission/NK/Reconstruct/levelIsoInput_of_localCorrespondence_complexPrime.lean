
import Mathlib
import Submission.NK.Reconstruct.levelPairData
import Submission.NK.Reconstruct.assemblyGen
import Submission.NK.Reconstruct.fourf5Gen
import Submission.NK.Reconstruct.prop4f3AwayFromL
import Submission.NK.Reconstruct.frobCorrespondenceGammaHaus_levelSplit
import Submission.NK.Reconstruct.exists_splitIsFrobElementAt_notMem_iUnion_closedSubgroup_awayFromL
import Submission.NK.Reconstruct.exists_ringEquiv_extends
import Submission.NK.Reconstruct.exists_gammaEquivOfPhi_continuous
import Submission.NK.Reconstruct.NumFieldInSup
import Submission.NK.ReconstructField.LevelCandidate
import Submission.NK.ReconstructField.exists_finitePlace_of_prime_level
import Submission.NK.ReconstructField.primeBelowNat_levelPrimeMap
import Submission.NK.Reconstruct.isHomeomorph_levelGalEquiv
import Submission.NK.ReconstructField.levelPrimeMapGen_bijective

/-!
# The level-pair bridge from the local correspondence, with a complex prime

This module proves `NK.Reconstruct.LevelIsoInputOfLocalData K₁ K₂ ℓ`
(`Submission/Work/Reconstruct/levelPairData.lean`): from the local correspondence (a), the Frobenius
correspondence (b), Čebotarev, the three rank inputs and a complex prime of `K₁`, every finite level
`L/↥K₁.L` of `Ω` is isomorphic to its image `levelMap ψ L` under the level correspondence of `ψ`.

The proof runs Shimizu's §4 machinery (`NK.Reconstruct.prop4f3_awayFromL` +
`NK.Reconstruct.exists_isomorphism_of_prop4f3_data_gen_awayFromL`) at every level pair
`(L, levelMap ψ L)`.  The base fields of the assembly being *arbitrary* finite number fields inside
`Ω`, the level pair is first re-read as a pair `A = ` the `ℚ`-level of `L`, `B = ` the `ℚ`-level of
`levelMap ψ L` of `NK.Reconstruct.NumFieldIn ℚ Ω`, with the auxiliary field `E` the normal closure
of `A.L ⊔ B.L` over `ℚ` (`NK.Reconstruct.exists_frobLevel_sup`).

The ingredients of Proposition 4f.3 are supplied by

* the local correspondence `a` restricted to the level pair, i.e. the prime bijection
  `NK.ReconstructField.levelPrimeMapGen ψ hψ a L` (`levelPrimeMapGen_bijective` for the fact that
  it is a bijection — a finite level is in general not normal over the base, which is why the general
  form of the level prime correspondence is needed);
* the isomorphism `σbar : Γ_L ≅ Γ_{levelMap ψ L}` of `ℚ_ℓ`-abelianisations induced by the
  homeomorphism `NK.ReconstructField.levelGalEquiv ψ hψ L` (`isHomeomorph_levelGalEquiv` for the
  fact that it is a homeomorphism of the Krull topologies, `exists_gammaEquivOfPhi_continuous` for
  the induced isomorphism of the abelianisations);
* the Frobenius correspondence at the level pair (`frobCorrespondenceGammaHaus_levelSplit`), which
  is exactly the `hb` of `prop4f3_awayFromL` at the completely split primes of residue
  characteristic `≠ ℓ`;
* the escaping prime of Prop. 4f.3
  (`exists_splitIsFrobElementAt_notMem_iUnion_closedSubgroup_awayFromL`), whose residue
  characteristic is `≠ ℓ`;
* the extension `Θ` of an automorphism of the finite Galois level `E/ℚ` to `Ω`
  (`exists_algEquiv_extends`);
* the complex prime of `K₁`, inherited by every finite level (`numberField_complex_of_le`);
* the rank inputs, through Shimizu's Proposition 4f.5 (`fourf5_gen_of_rankInputs`).

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. XII, Theorem 12.2.1;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

open scoped NumberField Pointwise

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **A finite Galois level of `Ω/ℚ` containing two given finite number-field levels.**  The normal
closure over `ℚ` of the compositum `A.L ⊔ B.L`. -/
theorem exists_frobLevel_sup (A B : NumFieldIn ℚ Ω) :
    ∃ E : FrobLevel ℚ Ω, A.L ≤ E.L ∧ B.L ≤ E.L := by
  classical
  letI : Algebra ℚ ↥(A.L ⊔ B.L) := (A.L ⊔ B.L).algebra'
  have hfin : FiniteDimensional ℚ ↥(IntermediateField.normalClosure ℚ ↥(A.L ⊔ B.L) Ω) :=
    normalClosure.is_finiteDimensional ℚ ↥(A.L ⊔ B.L) Ω
  haveI := hfin
  have hgal := IsGalois.normalClosure ℚ ↥(A.L ⊔ B.L) Ω
  have hnorm := hgal.to_normal
  have hnf : NumberField ↥(IntermediateField.normalClosure ℚ ↥(A.L ⊔ B.L) Ω) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField _
  have hsub : A.L ⊔ B.L ≤ IntermediateField.normalClosure ℚ ↥(A.L ⊔ B.L) Ω :=
    IntermediateField.le_normalClosure (A.L ⊔ B.L)
  exact ⟨⟨_, hfin, hnorm, hnf⟩, le_trans le_sup_left hsub, le_trans le_sup_right hsub⟩

/-! ## The `ℚ`-level underlying a finite level of `Ω/↥K.L` -/


/-- **The `ℚ`-level underlying a finite level `L` of `Ω/↥K.L`.**  The carrier of the level `L`,
regarded as an intermediate field of `Ω/ℚ`; it is a number field because `L` is finite over the
number field `↥K.L`. -/
noncomputable def NumFieldIn.ofLevel (K : NumFieldIn ℚ Ω) (L : IntermediateField ↥K.L Ω)
    [FiniteDimensional ↥K.L L] : NumFieldIn ℚ Ω := by
  classical
  haveI := K.numberField
  haveI := K.finite
  let Lq : IntermediateField ℚ Ω := L.toSubfield.toIntermediateField (fun q => by
    rw [IsScalarTower.algebraMap_apply ℚ ↥K.L Ω]
    exact L.algebraMap_mem (algebraMap ℚ ↥K.L q))
  have hfin : FiniteDimensional ℚ ↥Lq := by
    have h1 : FiniteDimensional ℚ ↥L := FiniteDimensional.trans ℚ ↥K.L ↥L
    let e : ↥L ≃ₗ[ℚ] ↥Lq :=
      { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun y => ⟨y.1, y.2⟩,
        left_inv := fun x => Subtype.ext rfl, right_inv := fun y => Subtype.ext rfl,
        map_add' := fun x y => Subtype.ext rfl, map_smul' := fun a x => Subtype.ext rfl }
    exact Module.Finite.equiv e
  haveI : NumberField ↥L := Commons.NumberTheory.NumberField.numberField_of_intermediateField L
  refine ⟨Lq, hfin, ?_⟩
  exact NumberField.of_ringEquiv (K := ↥L) (L := ↥Lq) (RingEquiv.refl ↥L)

/-- Membership in the `ℚ`-level of a finite level. -/
theorem NumFieldIn.mem_ofLevel (K : NumFieldIn ℚ Ω) (L : IntermediateField ↥K.L Ω)
    [FiniteDimensional ↥K.L L] {x : Ω} :
    x ∈ (NumFieldIn.ofLevel K L).L ↔ x ∈ L := Iff.rfl

/-- The given number field is contained in its `ℚ`-level. -/
theorem NumFieldIn.le_ofLevel (K : NumFieldIn ℚ Ω) (L : IntermediateField ↥K.L Ω)
    [FiniteDimensional ↥K.L L] : K.L ≤ (NumFieldIn.ofLevel K L).L := by
  intro x hx
  rw [NumFieldIn.mem_ofLevel]
  exact L.algebraMap_mem ⟨x, hx⟩

/-- `Ω` is a separable closure of the `ℚ`-level of a finite level. -/
theorem isSepClosure_ofLevel (K : NumFieldIn ℚ Ω) (L : IntermediateField ↥K.L Ω)
    [FiniteDimensional ↥K.L L] [IsSepClosure ↥K.L Ω] :
    IsSepClosure ↥(NumFieldIn.ofLevel K L).L Ω := isSepClosure_level L

/-! ## Extension of an automorphism of a finite Galois level -/

/-- **Extension of an automorphism of a finite normal level**, in the `AlgEquiv` form needed by
Shimizu's Theorem 4.0: for `L ⊆ Ω` a finite normal intermediate field of a separable closure `Ω` of
`ℚ` and `τ ∈ Gal(L/ℚ)`, there is a `ℚ`-algebra automorphism `θ` of `Ω` which preserves `L` setwise
and restricts to `τ` on `L`.  (The proof is the one of
`NK.Reconstruct.exists_ringEquiv_extends`, which returns the underlying ring automorphism.) -/
theorem exists_algEquiv_extends (L : IntermediateField ℚ Ω) [FiniteDimensional ℚ L] [Normal ℚ L]
    (τ : Gal(↥L/ℚ)) :
    ∃ θ : Ω ≃ₐ[ℚ] Ω, (∀ x : Ω, x ∈ L ↔ θ x ∈ L) ∧
      ∀ x : ↥L, θ (x : Ω) = ((τ x : ↥L) : Ω) := by
  haveI : Normal ℚ Ω := inferInstance
  let σ : Gal(Ω/ℚ) := τ.liftNormal Ω
  have hpt : ∀ x : ↥L, σ (x : Ω) = ((τ x : ↥L) : Ω) := fun x => τ.liftNormal_commutes Ω x
  refine ⟨σ, ?_, fun x => hpt x⟩
  intro x
  constructor
  · intro hx
    rw [hpt ⟨x, hx⟩]
    exact (τ ⟨x, hx⟩).2
  · intro hx
    let y : ↥L := τ.symm ⟨σ x, hx⟩
    have hy : σ (y : Ω) = σ x := by
      rw [hpt y]
      simp [y]
    have hyx : (y : Ω) = x := σ.injective hy
    rw [← hyx]
    exact y.2

set_option maxHeartbeats 8000000 in
theorem levelIsoInput_of_localCorrespondence_complexPrime {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] (K₁ K₂ : NK.Reconstruct.NumFieldIn ℚ Ω)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] (ℓ : ℕ) [Fact ℓ.Prime] :
    NK.Reconstruct.LevelIsoInputOfLocalData K₁ K₂ ℓ := by
  classical
  intro ψ hψ a b hcomplex₀ hH hM hR hc
  intro L hLfd
  -- ## Instances
  haveI hNfd : FiniteDimensional ↥K₂.L (levelMap ψ L) := finiteDimensional_levelMap hψ L
  haveI hNnf : NumberField ↥(levelMap ψ L) := numberField_levelMap hψ L
  haveI hLnf : NumberField ↥L := Commons.NumberTheory.NumberField.numberField_of_intermediateField L
  haveI hsepL : IsSepClosure ↥L Ω := isSepClosure_level L
  haveI hsepN : IsSepClosure ↥(levelMap ψ L) Ω := isSepClosure_level (levelMap ψ L)
  -- ## The `ℚ`-levels of the two fields of the level pair
  let A : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₁ L
  let B : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₂ (levelMap ψ L)
  haveI hsepA : IsSepClosure ↥A.L Ω := isSepClosure_ofLevel K₁ L
  haveI hsepB : IsSepClosure ↥B.L Ω := isSepClosure_ofLevel K₂ (levelMap ψ L)
  -- ## An auxiliary finite Galois level of `Ω/ℚ` containing both
  obtain ⟨E, hAE, hBE⟩ := exists_frobLevel_sup A B
  haveI hsepE : IsSepClosure ↥E.L Ω := isSepClosure_of_le E.L
  -- ## The isomorphism `σbar` of ℓ-adic abelianisations induced by `ψ` at the level pair
  have hhomeo : IsHomeomorph (NK.ReconstructField.levelGalEquiv ψ hψ L) :=
    isHomeomorph_levelGalEquiv ψ hψ L
  obtain ⟨σbar, hσbar_cont, hσbar_compat, hσbar_compat_symm⟩ :=
    exists_gammaEquivOfPhi_continuous (NK.ReconstructField.levelGalEquiv ψ hψ L) hhomeo ℓ
  -- ## The prime correspondence of the level pair
  have hbij := NK.ReconstructField.levelPrimeMapGen_bijective ψ hψ a L
  let primeMap : NK.Chebotarev.PrimeIdeal ↥A.L ≃ NK.Chebotarev.PrimeIdeal ↥B.L :=
    Equiv.ofBijective _ hbij
  have hprimeMap (𝔭 : NK.Chebotarev.PrimeIdeal ↥A.L) :
      primeMap 𝔭 = NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭 :=
    Equiv.ofBijective_apply _ _ 𝔭
  -- ## The prime correspondence preserves the rational prime
  have hchar : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal ↥A.L,
      Ideal.under ℤ (primeMap 𝔭).asIdeal = Ideal.under ℤ 𝔭.asIdeal := by
    intro 𝔭
    have hp : NK.LocalInputs.primeBelowNat ↥B.L (primeMap 𝔭) =
        NK.LocalInputs.primeBelowNat ↥A.L 𝔭 := by
      rw [hprimeMap 𝔭]
      exact NK.ReconstructField.primeBelowNat_levelPrimeMapGen ψ hψ a L 𝔭
    have hp' : NK.LocalInputs.primeBelow ↥B.L (primeMap 𝔭) =
        NK.LocalInputs.primeBelow ↥A.L 𝔭 :=
      Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext hp)
    rw [← Ideal.under_under (A := ℤ) (B := NumberField.RingOfIntegers ℚ)
        (C := NumberField.RingOfIntegers ↥B.L) (primeMap 𝔭).asIdeal,
      ← Ideal.under_under (A := ℤ) (B := NumberField.RingOfIntegers ℚ)
        (C := NumberField.RingOfIntegers ↥A.L) 𝔭.asIdeal,
      ← NK.LocalInputs.primeBelow_asIdeal ↥B.L (primeMap 𝔭),
      ← NK.LocalInputs.primeBelow_asIdeal ↥A.L 𝔭, hp']
  -- ## The Frobenius correspondence at the level pair
  have hb : ∀ (𝔭 : NK.Chebotarev.PrimeIdeal ↥A.L), SplitsCompletelyOverRat 𝔭 →
      ∀ (p : ℕ), CharP (NumberField.RingOfIntegers ↥A.L ⧸ 𝔭.asIdeal) p → p ≠ ℓ →
      ∀ (g₁ : Gal(Ω/↥A.L)) (g₂ : Gal(Ω/↥B.L)),
        IsFrobElementAt 𝔭 g₁ → IsFrobElementAt (primeMap 𝔭) g₂ →
        gammaHausMk (K := ↥B.L) (K' := Ω) ℓ
            (σbar (galToGamma (K := ↥A.L) (K' := Ω) ℓ g₁)) =
          gammaHausMk (K := ↥B.L) (K' := Ω) ℓ
            (galToGamma (K := ↥B.L) (K' := Ω) ℓ g₂) := by
    intro 𝔭 hsplit p hpchar hpne g₁ g₂ hg₁ hg₂
    have hpb : CharP (NumberField.RingOfIntegers ↥A.L ⧸ 𝔭.asIdeal)
        (NK.LocalInputs.primeBelowNat ↥A.L 𝔭) :=
      NK.ReconstructField.charP_of_liesOver 𝔭 (NK.LocalInputs.primeBelow ↥A.L 𝔭)
        (NK.LocalInputs.primeBelow_liesOver ↥A.L 𝔭)
    have hprime : p.Prime := by
      rw [← CharP.eq _ hpb hpchar]
      exact (Rat.HeightOneSpectrum.primesEquiv (NK.LocalInputs.primeBelow ↥A.L 𝔭)).2
    haveI : Fact p.Prime := ⟨hprime⟩
    have hg2x : IsFrobElementAt (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭) g₂ :=
      show IsFrobElementAt (primeMap 𝔭) g₂ from hg₂
    have key := frobCorrespondenceGammaHaus_levelSplit ℓ ψ hψ a b L σbar
      hσbar_compat p 𝔭 hsplit hpchar hpne g₁ g₂ hg₁ hg2x
    exact key
  -- ## The escaping prime of Proposition 4f.3
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
  -- ## The section `Θ` of the restriction `Gal(Ω/ℚ) → Gal(E.L/ℚ)`
  haveI hEfin := E.finite
  haveI hEnorm : Normal ℚ ↥E.L := by
    have he : (E.L.algebra' : Algebra ℚ ↥E.L) = (inferInstance : Algebra ℚ ↥E.L) :=
      Subsingleton.elim _ _
    exact Eq.mp (congrArg (fun a : Algebra ℚ ↥E.L => @Normal ℚ ↥E.L _ _ a) he) E.normal
  let Θ : Gal(↥E.L/ℚ) → Ω ≃ₐ[ℚ] Ω :=
    fun τ => (exists_algEquiv_extends E.L τ).choose
  have hΘmem : ∀ τ, ∀ x : Ω, x ∈ E.L ↔ Θ τ x ∈ E.L :=
    fun τ => (exists_algEquiv_extends E.L τ).choose_spec.1
  have hΘres : ∀ τ (x : ↥E.L), Θ τ (x : Ω) = ((τ x : ↥E.L) : Ω) :=
    fun τ x => (exists_algEquiv_extends E.L τ).choose_spec.2 x
  -- ## Shimizu's Proposition 4f.3 gives the `τ` of the theorem
  obtain ⟨τ, hτ⟩ := prop4f3_awayFromL A B E hAE hBE ℓ σbar hσbar_cont primeMap hb hchar
    (fun τ => (Θ τ : Ω ≃+* Ω)) (fun τ => hΘmem τ) (fun τ x => hΘres τ x) hescape
  have hprop : ∃ τ : Gal(↥E.L/ℚ), ∀ γ : Gamma ↥E.L Ω ℓ,
      gammaHausMk (K := ↥B.L) (K' := Ω) ℓ (σbar (ambientPi A E hAE ℓ γ)) =
        gammaHausMk (K := ↥B.L) (K' := Ω) ℓ
          (ambientPi B E hBE ℓ
            (tauStar E.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ)) := ⟨τ, hτ⟩
  -- ## The complex prime, inherited by the level `L`
  have hcomplex : ∃ v : NumberField.InfinitePlace ↥A.L, NumberField.InfinitePlace.IsComplex v :=
    numberField_complex_of_le K₁ A (NumFieldIn.le_ofLevel K₁ L) hcomplex₀
  -- ## The rank inputs give Shimizu's Proposition 4f.5
  have h45 : Fourf5InputGen Ω ℓ := fourf5_gen_of_rankInputs ℓ hH hM hR
  -- ## Shimizu's Theorem 4.0 (the assembly)
  obtain ⟨τ', hne⟩ := exists_isomorphism_of_prop4f3_data_gen_awayFromL A B E hAE hBE ℓ σbar
    hσbar_cont Θ hΘmem hΘres hprop hcomplex h45
  exact hne

end NK.Reconstruct
