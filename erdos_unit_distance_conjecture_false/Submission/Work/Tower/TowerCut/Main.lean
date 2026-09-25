import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.Unramified.Basic
import Submission.Work.Tower.Unramified.Discriminant
import Submission.Work.Tower.TowerCut.Basic
import Submission.Work.Tower.TowerCut.Transfer
import Submission.Work.Tower.TowerCut.Maximal
import Submission.Work.Tower.TowerCut.isUnramifiedExtensionForallPrimes_iSup
import Submission.Work.Tower.TowerCut.isPGroup_gal_iSup
import Submission.Work.Tower.TowerCut.finite_setOf_unramified
import Submission.Work.Tower.Shafarevich.Rank.relationRankWith_le_iff
import Submission.Work.Tower.Shafarevich.Rank.generatorRank_le_iff
import Submission.Work.Tower.Shafarevich.Rank.generatorRank_le_of_surjective
import Submission.Work.GolodShafarevich.Inequality

/-!
# Tower cutting (paper Proposition 3.8, Steps 2-3)

If a totally real cubic field `F` has a large everywhere-unramified elementary abelian
`3`-extension `E/F` (of generator rank at least `m`), and `T` is a finite set of primes in
which every everywhere-unramified elementary abelian `3`-extension of `F` splits completely,
then --- taking Shafarevich's relation-rank estimate as a hypothesis --- for every `N` there is
an everywhere-unramified Galois `3`-extension `L/F` of degree at least `N` over `ℚ` in which
every prime of `T` splits completely, provided `m² > 4 (m + C₀ + |T|)`.

The proof is by contradiction.  If the degrees of all such `L` were bounded by `N`, then by
Hermite's theorem the set of their images inside `AlgebraicClosure F` would be finite, so its
compositum `K` would be a finite everywhere-unramified Galois `3`-group extension of `F` which
is *maximal* (every good `L` embeds into `K`).  Shafarevich's estimate then bounds the relation
rank `r` of `G = Gal(K/F)` by `d + C₀ + |T|` where `d = generatorRank G`.  Since `E` embeds in
`K`, `d ≥ m`; since `K ⊋ F`, `G` is a nontrivial finite `3`-group, so Golod--Shafarevich gives
`4r > d²`, hence `d² < 4(d + C₀ + |T|)`, and monotonicity of `x ↦ x² - 4x` on `[4,∞)` yields
`m² < 4(m + C₀ + |T|)`, contradicting the numerical hypothesis.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower

theorem unramified_tower_gs
    (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (hF : Module.finrank ℚ F = 3)
    (m : ℕ) (E : Type) [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (hEunram : IsUnramifiedExtension F E)
    (hE3 : IsPGroup 3 (Gal(E/F)))
    (hEab : IsAbelianGalois F E)
    (hEexp : ∀ σ : Gal(E/F), σ ^ 3 = 1)
    (hm : m ≤ generatorRank (Gal(E/F)))
    (T : Finset (Ideal (𝓞 F))) (hT : ∀ 𝔭 ∈ T, 𝔭.IsPrime)
    (hTsplit : ∀ 𝔭 ∈ T, ∀ (L : Type) [Field L] [NumberField L] [Algebra F L]
      [FiniteDimensional F L] [IsGalois F L],
      IsUnramifiedExtension F L → IsAbelianGalois F L →
      (∀ σ : Gal(L/F), σ ^ 3 = 1) → SplitsCompletelyIn F L 𝔭)
    (C₀ : ℕ)
    (hshaf : ∀ (K : Type) [Field K] [NumberField K] [Algebra F K]
      [FiniteDimensional F K] [IsGalois F K],
      IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
      (∀ (L : Type) [Field L] [NumberField L] [Algebra F L]
        [FiniteDimensional F L] [IsGalois F L],
        IsUnramifiedExtension F L → IsPGroup 3 (Gal(L/F)) →
        (∀ 𝔭 ∈ T, SplitsCompletelyIn F L 𝔭) →
        ∃ (φ : L →ₐ[F] K), True) →
      relationRankWith (Gal(K/F)) (generatorRank (Gal(K/F)))
        ≤ generatorRank (Gal(K/F)) + C₀ + T.card)
    (hnum : m ^ 2 > 4 * (m + C₀ + T.card)) :
    ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
      (_ : FiniteDimensional F L) (_ : IsGalois F L),
      N ≤ Module.finrank ℚ L ∧ IsUnramifiedExtension F L ∧
      IsPGroup 3 (Gal(L/F)) ∧ (∀ 𝔭 ∈ T, SplitsCompletelyIn F L 𝔭) := by
  -- `m` is large enough that `x ↦ x² - 4x` is increasing at `m`
  have hm4 : 4 < m := by
    by_contra h
    push_neg at h
    have h1 : (m : ℤ) ^ 2 ≤ 4 * (m : ℤ) := by
      nlinarith [show (m : ℤ) ≤ 4 by omega, show (0 : ℤ) ≤ m by omega]
    have h2 : 4 * (m : ℤ) ≤ 4 * ((m : ℤ) + (C₀ : ℤ) + (T.card : ℤ)) := by
      have : (0 : ℤ) ≤ (C₀ : ℤ) + (T.card : ℤ) := by omega
      linarith
    have h3 : (m : ℤ) ^ 2 > 4 * ((m : ℤ) + (C₀ : ℤ) + (T.card : ℤ)) := by
      exact_mod_cast hnum
    linarith
  intro N
  by_contra hcon
  -- all good extensions have degree `< N` over `ℚ`
  have deg_bound : ∀ (L : Type) [Field L] [NumberField L] [Algebra F L]
      [FiniteDimensional F L] [IsGalois F L],
      IsUnramifiedExtension F L → IsPGroup 3 (Gal(L/F)) →
      (∀ 𝔭 ∈ T, SplitsCompletelyIn F L 𝔭) → Module.finrank ℚ L < N := by
    intro L _ _ _ _ _ hunr h3 hsplit
    by_contra hlt
    exact hcon ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      not_lt.mp hlt, hunr, h3, hsplit⟩
  -- every prime of `T` splits completely in `E`
  have hsplitE : ∀ 𝔭 ∈ T, SplitsCompletelyIn F E 𝔭 :=
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
      [IsGalois F L], IsUnramifiedExtension F L → IsPGroup 3 (Gal(L/F)) →
      (∀ 𝔭 ∈ T, SplitsCompletelyIn F L 𝔭) → ∃ φ : L →ₐ[F] ↥K, True := by
    intro L _ _ _ _ _ hunr h3 hsplit
    obtain ⟨ψL⟩ : Nonempty (L →ₐ[F] AlgebraicClosure F) := ⟨IsAlgClosed.lift⟩
    have hMem : ψL.fieldRange ∈ TowerCut.goodImages F T N :=
      ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ψL,
        hunr, h3, hsplit, deg_bound L hunr h3 hsplit, rfl⟩
    have hle : ψL.fieldRange ≤ K := hKle _ hMem
    exact ⟨AlgHom.codRestrict ψL K.toSubalgebra (fun x => hle ⟨x, rfl⟩), trivial⟩
  have hMEle : ME ≤ K := hKle ME hME
  -- Shafarevich's estimate for `K`
  have hshafK : relationRankWith (Gal(↥K/F)) (generatorRank (Gal(↥K/F)))
      ≤ generatorRank (Gal(↥K/F)) + C₀ + T.card :=
    hshaf ↥K (IsUnramifiedExtension.of_forallPrimes hKunr) hK3 hKmax
  -- the generator rank of `Gal(K/F)` is at least `m`, so `Gal(K/F) ≠ 1`
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
  -- an attained presentation of `Gal(K/F)`
  let d : ℕ := generatorRank (Gal(↥K/F))
  let r : ℕ := relationRankWith (Gal(↥K/F)) d
  obtain ⟨φ, hφ⟩ : ∃ φ : FreeGroup (Fin d) →* Gal(↥K/F), Function.Surjective φ :=
    (Shafarevich.Rank.generatorRank_le_iff d).mp le_rfl
  obtain ⟨ψ, hψ, R, hR⟩ :=
    (Shafarevich.Rank.relationRankWith_le_iff d ⟨φ, hφ⟩ r).mp le_rfl
  have hmin : ∀ (d' : ℕ) (ψ : FreeGroup (Fin d') →* Gal(↥K/F)),
      Function.Surjective ψ → d ≤ d' :=
    fun d' ψ hψ => (Shafarevich.Rank.generatorRank_le_iff d').mpr ⟨ψ, hψ⟩
  -- Golod--Shafarevich
  have hGS : 4 * r > d ^ 2 :=
    GolodShafarevich.Inequality (by norm_num) (Gal(↥K/F)) hK3 ψ hψ R hR hmin
  -- arithmetic contradiction
  have hd2 : d ^ 2 < 4 * (d + C₀ + T.card) := by
    have h1 : d ^ 2 < 4 * r := hGS
    have h2 : r ≤ d + C₀ + T.card := hshafK
    omega
  have hcontr : m ^ 2 < 4 * (m + C₀ + T.card) := by
    have h1 : (m : ℤ) ^ 2 - 4 * (m : ℤ) ≤ (d : ℤ) ^ 2 - 4 * (d : ℤ) := by
      have hmd : m ≤ d := hmK
      nlinarith [hmd, hm4]
    have h2 : (d : ℤ) ^ 2 - 4 * (d : ℤ) < 4 * ((C₀ : ℤ) + (T.card : ℤ)) := by
      have hd2' : (d : ℤ) ^ 2 < 4 * ((d : ℤ) + (C₀ : ℤ) + (T.card : ℤ)) := by
        exact_mod_cast hd2
      nlinarith
    have h3 : (m : ℤ) ^ 2 < 4 * ((m : ℤ) + (C₀ : ℤ) + (T.card : ℤ)) := by nlinarith
    exact_mod_cast h3
  omega

end Tower
end Work
