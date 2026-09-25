import Mathlib
import Submission.Work.Tower.TowerCut.Main
import Submission.Work.Tower.ProPEndgame.Main
import Submission.Work.Tower.Shafarevich.Defs
import Submission.Work.Tower.MinkowskiGS.Defs

/-!
# The Golod–Šafarevič endgame with the class-group relation bound

This is the variant of `Work.Tower.TowerCutProP.unramified_tower_gs_proP` in which the uniform
Shafarevich hypothesis `proPRelationRank ≤ generatorRank + C₀ + |T|` is replaced by the **per-field**
bound `proPRelationRank ≤ M + |T|` for a fixed natural number `M` (standing for
`dim_{𝔽₃} Cl_F[3] + 2` in the application).  The numerical condition is correspondingly
`m² > 4 (M + |T|)`.

Because the bound no longer involves the *generator rank* of `Gal(K/F)`, the proof is shorter than
the original: no monotonicity of `x ↦ x² - 4x` is needed.  All the remaining machinery — Hermite's
theorem, the compositum of the finitely many "good" extensions, the Frattini splitting condition —
is identical to `Work.Tower.TowerCutProP.unramified_tower_gs_proP`.

The conclusion is the statement consumed by the tower assembly: for every `N` there is an
everywhere-unramified Galois `3`-extension of `F` of degree `≥ N` in which every prime of `T`
splits completely.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.Tower.MinkowskiGS

/-- **Tower cutting with the class-group relation bound.**

`M` is a parameter with the meaning `dim_{𝔽₃} Cl_F[3] + 2`; `hshaf` is the per-field
relation-rank bound for the maximal `T`-split level, and `hnum` is the Golod–Šafarevič numerical
condition.  The conclusion is that `F` has everywhere-unramified Galois `3`-extensions of
arbitrarily large degree in which every prime of `T` splits completely.

If the degrees of all everywhere-unramified Galois `3`-extensions `L/F` in which every prime of `T`
splits completely were bounded by `N`, Hermite's theorem makes their images inside
`AlgebraicClosure F` finite, and their compositum `K` is a finite everywhere-unramified Galois
`3`-extension of `F` which is *maximal*.  The hypothesis `hshaf` bounds
`dim_{𝔽₃} H²(Gal(K/F), 𝔽₃) ≤ M + |T|`.  Since `E` embeds in `K`, `d(Gal(K/F)) ≥ m`, so `Gal(K/F)`
is a nontrivial finite `3`-group and the pro-`p` Golod–Šafarevič inequality gives
`m² ≤ d² < 4 · dim H² ≤ 4(M + |T|)`, contradicting `hnum`. -/
theorem unramified_tower_gs_classGroup
    (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (hF : Module.finrank ℚ F = 3)
    (m : ℕ) (E : Type) [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (hEunram : Work.Tower.IsUnramifiedExtension F E)
    (hE3 : IsPGroup 3 (E ≃ₐ[F] E))
    (hEab : IsAbelianGalois F E)
    (hEexp : ∀ σ : E ≃ₐ[F] E, σ ^ 3 = 1)
    (hm : m ≤ Work.Tower.generatorRank (E ≃ₐ[F] E))
    (T : Finset (Ideal (NumberField.RingOfIntegers F)))
    (hT : ∀ 𝔭 ∈ T, 𝔭.IsPrime)
    (hTsplit : ∀ 𝔭 ∈ T, ∀ (L : Type) [Field L] [NumberField L] [Algebra F L]
      [FiniteDimensional F L] [IsGalois F L],
      Work.Tower.IsUnramifiedExtension F L → IsAbelianGalois F L →
      (∀ σ : L ≃ₐ[F] L, σ ^ 3 = 1) → Work.Tower.SplitsCompletelyIn F L 𝔭)
    (M : ℕ)
    (hshaf : ∀ (K : Type) [Field K] [NumberField K] [Algebra F K]
      [FiniteDimensional F K] [IsGalois F K],
      Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (K ≃ₐ[F] K) →
      (∀ (L : Type) [Field L] [NumberField L] [Algebra F L]
        [FiniteDimensional F L] [IsGalois F L],
        Work.Tower.IsUnramifiedExtension F L → IsPGroup 3 (L ≃ₐ[F] L) →
        (∀ 𝔭 ∈ T, Work.Tower.SplitsCompletelyIn F L 𝔭) →
        ∃ (φ : L →ₐ[F] K), True) →
      Work.Tower.Shafarevich.proPRelationRank 3 (K ≃ₐ[F] K)
        ≤ M + T.card)
    (hnum : m ^ 2 > 4 * (M + T.card)) :
    ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
      (_ : FiniteDimensional F L) (_ : IsGalois F L),
      N ≤ Module.finrank ℚ L ∧ Work.Tower.IsUnramifiedExtension F L ∧
      IsPGroup 3 (L ≃ₐ[F] L) ∧ (∀ 𝔭 ∈ T, Work.Tower.SplitsCompletelyIn F L 𝔭) := by
  classical
  -- `m` is positive, because `m² > 4(M + |T|) ≥ 0`
  have hmpos : 0 < m := by
    have h : 0 < m ^ 2 := lt_of_le_of_lt (Nat.zero_le _) hnum
    exact Nat.pos_of_ne_zero (fun h0 => by rw [h0] at h; simp at h)
  intro N
  by_contra hcon
  -- all good extensions have degree `< N` over `ℚ`
  have deg_bound : ∀ (L : Type) [Field L] [NumberField L] [Algebra F L]
      [FiniteDimensional F L] [IsGalois F L],
      Work.Tower.IsUnramifiedExtension F L → IsPGroup 3 (Gal(L/F)) →
      (∀ 𝔭 ∈ T, Work.Tower.SplitsCompletelyIn F L 𝔭) → Module.finrank ℚ L < N := by
    intro L _ _ _ _ _ hunr h3 hsplit
    by_contra hlt
    exact hcon ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      not_lt.mp hlt, hunr, h3, hsplit⟩
  -- every prime of `T` splits completely in `E`
  have hsplitE : ∀ 𝔭 ∈ T, Work.Tower.SplitsCompletelyIn F E 𝔭 :=
    fun 𝔭 h𝔭 => hTsplit 𝔭 h𝔭 E hEunram hEab hEexp
  -- the image of `E` in the algebraic closure
  obtain ⟨ψE⟩ : Nonempty (E →ₐ[F] AlgebraicClosure F) := ⟨IsAlgClosed.lift⟩
  let ME : IntermediateField F (AlgebraicClosure F) := ψE.fieldRange
  have hME : ME ∈ TowerCut.goodImages F T N :=
    ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ψE,
      hEunram, hE3, hsplitE, deg_bound E hEunram hE3 hsplitE, rfl⟩
  -- the maximal field `K`: the supremum of all the good images
  have hSfin : (TowerCut.goodImages F T N).Finite := TowerCut.goodImages_finite T N
  let s : Finset (IntermediateField F (AlgebraicClosure F)) := hSfin.toFinset
  have hmem : ∀ M : IntermediateField F (AlgebraicClosure F),
      M ∈ s ↔ M ∈ TowerCut.goodImages F T N := by
    intro M
    rw [show s = hSfin.toFinset from rfl, Set.Finite.mem_toFinset]
  have hMEmem : ME ∈ s := (hmem ME).mpr hME
  let K : IntermediateField F (AlgebraicClosure F) :=
    ⨆ i : ↥s, (i : IntermediateField F (AlgebraicClosure F))
  haveI : Nonempty ↥s := ⟨⟨ME, hMEmem⟩⟩
  haveI : ∀ i : ↥s, FiniteDimensional F ((i : IntermediateField F (AlgebraicClosure F))) :=
    fun i => (TowerCut.goodImages_spec (T := T) (N₀ := N) ((hmem _).mp i.2)).1
  have hKfd : FiniteDimensional F ↥K := by
    dsimp only [K]
    exact IntermediateField.finiteDimensional_iSup_of_finite
  haveI : FiniteDimensional F ↥K := hKfd
  haveI : NumberField ↥K := NumberField.of_module_finite F ↥K
  have hKunr : IsUnramifiedExtensionForallPrimes F ↥K := by
    dsimp only [K]
    exact TowerCut.isUnramifiedExtensionForallPrimes_iSup
      (M := fun i : ↥s => (i : IntermediateField F (AlgebraicClosure F)))
      (fun i => (TowerCut.goodImages_spec (T := T) (N₀ := N) ((hmem _).mp i.2)).2.1)
  have hKgal : IsGalois F ↥K := by
    haveI : ∀ i : ↥s, IsGalois F ((i : IntermediateField F (AlgebraicClosure F))) :=
      fun i => (TowerCut.goodImages_spec (T := T) (N₀ := N) ((hmem _).mp i.2)).2.2.1
    dsimp only [K]
    exact IsGalois.mk
  have hK3 : IsPGroup 3 (Gal(↥K/F)) := by
    haveI : ∀ i : ↥s, IsGalois F ((i : IntermediateField F (AlgebraicClosure F))) :=
      fun i => (TowerCut.goodImages_spec (T := T) (N₀ := N) ((hmem _).mp i.2)).2.2.1
    dsimp only [K]
    exact TowerCut.isPGroup_gal_iSup
      (M := fun i : ↥s => (i : IntermediateField F (AlgebraicClosure F)))
      (fun i => (TowerCut.goodImages_spec (T := T) (N₀ := N) ((hmem _).mp i.2)).2.2.2.1)
  -- `K` is maximal: every element of `goodImages` is contained in it
  have hKle : ∀ M ∈ TowerCut.goodImages F T N, M ≤ K := by
    intro M hM
    have hMs : M ∈ s := (hmem M).mpr hM
    exact le_iSup (fun i : ↥s => (i : IntermediateField F (AlgebraicClosure F))) ⟨M, hMs⟩
  -- `K` is maximal: every good extension embeds into it
  have hKmax : ∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
      [IsGalois F L], Work.Tower.IsUnramifiedExtension F L → IsPGroup 3 (Gal(L/F)) →
      (∀ 𝔭 ∈ T, Work.Tower.SplitsCompletelyIn F L 𝔭) → ∃ φ : L →ₐ[F] ↥K, True := by
    intro L _ _ _ _ _ hunr h3 hsplit
    obtain ⟨ψL⟩ : Nonempty (L →ₐ[F] AlgebraicClosure F) := ⟨IsAlgClosed.lift⟩
    have hMem : ψL.fieldRange ∈ TowerCut.goodImages F T N :=
      ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ψL,
        hunr, h3, hsplit, deg_bound L hunr h3 hsplit, rfl⟩
    have hle : ψL.fieldRange ≤ K := hKle _ hMem
    exact ⟨AlgHom.codRestrict ψL K.toSubalgebra (fun x => hle ⟨x, rfl⟩), trivial⟩
  have hMEle : ME ≤ K := hKle ME hME
  -- the relation-rank bound for the maximal `T`-split level `K`
  have hshafK : Shafarevich.proPRelationRank 3 (Gal(↥K/F)) ≤ M + T.card :=
    hshaf ↥K (IsUnramifiedExtension.of_forallPrimes hKunr) hK3 hKmax
  -- the generator rank of `Gal(K/F)` is at least `m`, so `Gal(K/F)` is nontrivial
  haveI : FiniteDimensional F ↥ME := (TowerCut.goodImages_spec (T := T) (N₀ := N) hME).1
  haveI : IsGalois F ↥ME := (TowerCut.goodImages_spec (T := T) (N₀ := N) hME).2.2.1
  haveI : Fintype (Gal(↥K/F)) := AlgEquiv.fintype F ↥K
  haveI : Fintype (Gal(↥ME/F)) := AlgEquiv.fintype F ↥ME
  have eE : E ≃ₐ[F] ↥ME := AlgEquiv.ofInjective ψE ψE.injective
  letI : Algebra ↥ME ↥K := (IntermediateField.inclusion hMEle).toAlgebra
  haveI : IsScalarTower F ↥ME ↥K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmK : m ≤ generatorRank (Gal(↥K/F)) := by
    have h1 : generatorRank (Gal(↥ME/F)) ≤ generatorRank (Gal(↥K/F)) :=
      Shafarevich.Rank.generatorRank_le_of_surjective _
        (AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥ME) (E := ↥K))
    have h2 : generatorRank (Gal(↥ME/F)) = generatorRank (Gal(E/F)) :=
      TowerCut.generatorRank_eq_of_mulEquiv (AlgEquiv.autCongr eE.symm)
    calc m ≤ generatorRank (Gal(E/F)) := hm
      _ = generatorRank (Gal(↥ME/F)) := h2.symm
      _ ≤ generatorRank (Gal(↥K/F)) := h1
  haveI : Nontrivial (Gal(↥K/F)) :=
    TowerCut.nontrivial_of_generatorRank_pos (by omega : 0 < generatorRank (Gal(↥K/F)))
  -- the pro-`p` Golod–Šafarevič inequality for the nontrivial finite `3`-group `Gal(K/F)`
  have hGS : 4 * Shafarevich.proPRelationRank 3 (Gal(↥K/F))
      > generatorRank (Gal(↥K/F)) ^ 2 :=
    ProPEndgame.proP_gs 3 hK3
  -- arithmetic contradiction: `m² ≤ d² < 4 · dim H² ≤ 4(M + |T|)`
  have hcontr : m ^ 2 < 4 * (M + T.card) := by
    have h1 : generatorRank (Gal(↥K/F)) ^ 2 < 4 * (M + T.card) := by
      have h2 : generatorRank (Gal(↥K/F)) ^ 2
          < 4 * Shafarevich.proPRelationRank 3 (Gal(↥K/F)) := hGS
      have h3 : 4 * Shafarevich.proPRelationRank 3 (Gal(↥K/F))
          ≤ 4 * (M + T.card) := Nat.mul_le_mul_left 4 hshafK
      omega
    have h4 : m ^ 2 ≤ generatorRank (Gal(↥K/F)) ^ 2 := Nat.pow_le_pow_left hmK 2
    omega
  omega

end Work.Tower.MinkowskiGS
