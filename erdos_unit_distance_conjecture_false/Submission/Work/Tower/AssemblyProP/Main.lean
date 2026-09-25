import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Defs.Basic
import Submission.Work.Tower.Assembly.Main
import Submission.Work.Tower.Assembly.exists_tower_intermediateField
import Submission.Work.Tower.TowerCutProP.unramified_tower_gs_proP

set_option linter.style.haveILetI false

namespace Work.Tower.AssemblyProP

open Work.Tower.Assembly (three_not_dvd_prod isPGroup_three_of_exp rootDiscr_eq_exp eq_witness_of_mem_splits)

open NumberField
open scoped Classical nonZeroDivisors IsMulCommutative

/-- The positivity-threaded variant of `Work.Tower.Assembly.exists_tower_of_base_and_shafarevich`.

Its statement and proof are those of `exists_tower_of_base_and_shafarevich` with the two changes
forced by the extra `0 < ℓ` argument of `hbase`: the interface gains that argument, and the single
application of `hbase` (fed by the positive `ℓ` produced by `Glue.exists_tower_params`) supplies
it.  The un-threaded interface cannot be recovered from this one, because its `ℓ = 0` instance is
*false* (it would demand a totally real cubic field of discriminant `1`). -/
theorem exists_tower_of_base_and_shafarevich_pos
    (hbase : ∀ (ℓ : ℕ) (_ : 0 < ℓ) (r : Fin ℓ → ℕ), (∀ i, Nat.Prime (r i)) → (∀ i, r i % 3 = 1) →
      Function.Injective r →
      ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : NumberField.IsTotallyReal F)
        (_ : IsGalois ℚ F)
        (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra F M)
        (_ : FiniteDimensional F M) (_ : IsGalois F M),
        Module.finrank ℚ F = 3 ∧ IsAbelianGalois F M ∧ Module.finrank F M = 3 ^ (ℓ - 1) ∧
        (∀ σ : Gal(M/F), σ ^ 3 = 1) ∧ Work.Tower.IsUnramifiedExtension F M ∧
        |NumberField.discr F| = ((∏ i, r i : ℕ) : ℤ) ^ 2)
    (hshaf : ∃ C₀ : ℕ,
      ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
        Module.finrank ℚ F = 3 →
        ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K],
          Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
          ∀ (T : Finset (Ideal (𝓞 F))), (∀ 𝔭 ∈ T, 𝔭.IsPrime) →
            (∀ 𝔭 ∈ T, ∀ (L : Type) [Field L] [NumberField L] [Algebra F L]
               [FiniteDimensional F L] [IsGalois F L],
               Work.Tower.IsUnramifiedExtension F L → IsAbelianGalois F L →
               (∀ σ : Gal(L/F), σ ^ 3 = 1) → Work.Tower.SplitsCompletelyIn F L 𝔭) →
            (∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
               [IsGalois F L],
               Work.Tower.IsUnramifiedExtension F L → IsPGroup 3 (Gal(L/F)) →
               (∀ 𝔭 ∈ T, Work.Tower.SplitsCompletelyIn F L 𝔭) → ∃ (φ : L →ₐ[F] K), True) →
            Work.Tower.Shafarevich.proPRelationRank 3 (Gal(K/F)) ≤
              Work.Tower.generatorRank (Gal(K/F)) + C₀ + T.card) :
    ∀ (H : ℝ), 0 < H →
    ∃ (t : ℕ) (q : Fin t → ℕ) (C : ℝ), 0 < t ∧ (∀ b, Nat.Prime (q b)) ∧
      Function.Injective q ∧ (∀ b, q b % 4 = 1) ∧ 1 ≤ C ∧
      (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
        N ≤ Module.finrank ℚ K ∧ NumberField.rootDiscr K ≤ C ∧
        (∀ b, Work.Defs.SplitsCompletely (q b) K) := by
  intro H hH
  classical
  obtain ⟨C₀, hC₀⟩ := hshaf
  obtain ⟨ℓ, r, t, C, hr, hrinj, hr3, hℓpos, ht, hC1, hCdef, hnumC, hnumℓ⟩ :=
    Glue.exists_tower_params H hH C₀
  -- ## 1. the base field
  obtain ⟨F, hFF, hFN, hFTR, hFgal, M, hMF, hMN, hFM, hFMD, hFMG,
    hF3, hFab, hFMdeg, hFexp, hFunr, hFdisc⟩ := hbase ℓ hℓpos r hr hr3 hrinj
  letI : Field F := hFF
  letI : NumberField F := hFN
  letI : NumberField.IsTotallyReal F := hFTR
  letI : IsGalois ℚ F := hFgal
  letI : Field M := hMF
  letI : NumberField M := hMN
  letI : Algebra F M := hFM
  letI : FiniteDimensional F M := hFMD
  letI : IsGalois F M := hFMG
  -- ## 2. `3 ∤ disc F`
  have h3disc : ¬ (3 : ℤ) ∣ NumberField.discr F := by
    intro h
    have h1 : (3 : ℤ) ∣ |NumberField.discr F| :=
      (dvd_abs (3 : ℤ) (NumberField.discr F)).mpr h
    rw [hFdisc] at h1
    have h2 : (3 : ℤ) ∣ ((∏ i, r i : ℕ) : ℤ) := by
      have hp : Prime (3 : ℤ) := by norm_num
      exact hp.dvd_of_dvd_pow h1
    exact three_not_dvd_prod r hr hr3 (by exact_mod_cast h2)
  -- ## 3. the Frattini layer `E/F`
  obtain ⟨E, hEF, hEN, hEA, hEFin, hEgal, hEunr, hE3, hEab, hEexp, hEuniv⟩ :=
    Work.Tower.exists_frattini_layer F h3disc
  letI : Field E := hEF
  letI : NumberField E := hEN
  letI : Algebra F E := hEA
  letI : FiniteDimensional F E := hEFin
  letI : IsGalois F E := hEgal
  haveI : Fintype (Gal(E/F)) := Fintype.ofFinite _
  -- ## 4. a finite Galois extension of `ℚ` containing `E`
  obtain ⟨N, hNF, hNN, hNA, hNtow, hNgal, hNfin, φ, hNsplit⟩ :=
    Glue.exists_galois_closure_split F E
  letI : Field N := hNF
  letI : NumberField N := hNN
  letI : Algebra F N := hNA
  letI : IsScalarTower ℚ F N := hNtow
  letI : IsGalois ℚ N := hNgal
  letI : FiniteDimensional F N := hNfin
  -- ## 5. the split primes `q b`, splitting completely in `N`, hence in `E` and in `F`
  obtain ⟨q, hq, hqi, hq4, hqsplit⟩ := Assembly.exists_primes_split N t
  have hsplitE : ∀ b, Work.Defs.SplitsCompletely (q b) E := fun b =>
    hNsplit (q b) (hq b) (hqsplit b)
  have hsplitF : ∀ b, Work.Defs.SplitsCompletely (q b) F := fun b =>
    ((Work.Tower.splitsCompletely_iff_relative (F := F) (L := E) (q b) (hq b)).mp
      (hsplitE b)).1
  have hsplitEin : ∀ b (𝔭 : Ideal (𝓞 F)), 𝔭.IsPrime → ((q b : ℕ) : 𝓞 F) ∈ 𝔭 →
      Work.Tower.SplitsCompletelyIn F E 𝔭 := fun b =>
    ((Work.Tower.splitsCompletely_iff_relative (F := F) (L := E) (q b) (hq b)).mp
      (hsplitE b)).2
  -- ## 6. the set `T` of primes of `F` above the `q b`
  have hsplitFkeep : ∀ b, Work.Defs.SplitsCompletely (q b) F := hsplitF
  choose 𝔮 h𝔮prime h𝔮mem _h𝔮res _h𝔮ne h𝔮prod using hsplitF
  let T : Finset (Ideal (𝓞 F)) :=
    Finset.univ.image (fun bi : Fin t × Fin (Module.finrank ℚ F) => 𝔮 bi.1 bi.2)
  have hTmem : ∀ {𝔭 : Ideal (𝓞 F)}, 𝔭 ∈ T →
      ∃ (b : Fin t) (i : Fin (Module.finrank ℚ F)), 𝔮 b i = 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨⟨b, i⟩, -, hbi⟩ := Finset.mem_image.mp h𝔭
    exact ⟨b, i, hbi⟩
  have hTprime : ∀ 𝔭 ∈ T, 𝔭.IsPrime := by
    intro 𝔭 h𝔭
    obtain ⟨b, i, rfl⟩ := hTmem h𝔭
    exact h𝔮prime b i
  have hTcard : T.card ≤ 3 * t := by
    calc T.card ≤ (Finset.univ : Finset (Fin t × Fin (Module.finrank ℚ F))).card :=
          Finset.card_image_le
      _ = t * Module.finrank ℚ F := by
          rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      _ = 3 * t := by rw [hF3]; ring
  -- ## 7. the Frattini condition for `T`
  have hTsplit : ∀ 𝔭 ∈ T, ∀ (L : Type) [Field L] [NumberField L] [Algebra F L]
      [FiniteDimensional F L] [IsGalois F L],
      Work.Tower.IsUnramifiedExtension F L → IsAbelianGalois F L →
      (∀ σ : Gal(L/F), σ ^ 3 = 1) → Work.Tower.SplitsCompletelyIn F L 𝔭 := by
    intro 𝔭 h𝔭 L _ _ _ _ _ hLunr hLab hLexp
    obtain ⟨b, i, rfl⟩ := hTmem h𝔭
    haveI : Fintype (Gal(L/F)) := Fintype.ofFinite _
    have hL3 : IsPGroup 3 (Gal(L/F)) := isPGroup_three_of_exp (G := Gal(L/F)) hLexp
    obtain ⟨ψ, -⟩ := hEuniv L hLunr hL3 hLab hLexp
    exact Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom (𝔮 b i) ψ
      (hsplitEin b (𝔮 b i) (h𝔮prime b i) (h𝔮mem b i))
  -- ## 8. the tower, via the Golod–Šafarevič inequality
  -- Šafarevič's estimate in the shape expected by `unramified_tower_gs` (where `T` is fixed).
  have hshafT : ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K]
      [IsGalois F K],
      Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
      (∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
        [IsGalois F L],
        Work.Tower.IsUnramifiedExtension F L → IsPGroup 3 (Gal(L/F)) →
        (∀ 𝔭 ∈ T, Work.Tower.SplitsCompletelyIn F L 𝔭) → ∃ (φ : L →ₐ[F] K), True) →
      Work.Tower.Shafarevich.proPRelationRank 3 (Gal(K/F)) ≤
        Work.Tower.generatorRank (Gal(K/F)) + C₀ + T.card :=
    fun K _ _ _ _ _ hKur hK3 hmax => hC₀ F hF3 K hKur hK3 T hTprime hTsplit hmax
  have hm : ℓ - 1 ≤ generatorRank (Gal(M/F)) := Glue.le_generatorRank_galois hFexp hFMdeg
  have hnum : (ℓ - 1) ^ 2 > 4 * ((ℓ - 1) + C₀ + T.card) := by
    have hT3 : ((T.card : ℕ) : ℝ) ≤ 3 * (t : ℝ) := by exact_mod_cast hTcard
    have h1 : (((ℓ - 1 : ℕ) : ℝ)) ^ 2 >
        4 * ((((ℓ - 1 : ℕ) : ℝ)) + (C₀ : ℝ) + 3 * (t : ℝ)) := hnumℓ
    have hcast : ((ℓ - 1 + C₀ + T.card : ℕ) : ℝ) =
        (((ℓ - 1 : ℕ) : ℝ) + (C₀ : ℝ) + (T.card : ℝ)) := by push_cast; ring
    have h2 : ((ℓ - 1 : ℕ) : ℝ) ^ 2 >
        4 * (((ℓ - 1 : ℕ) : ℝ) + (C₀ : ℝ) + (T.card : ℝ)) := by linarith
    rw [← hcast] at h2
    exact_mod_cast h2
  have hM3 : IsPGroup 3 (Gal(M/F)) := isPGroup_three_of_exp (G := Gal(M/F)) hFexp
  obtain htower := Work.Tower.TowerCutProP.unramified_tower_gs_proP F hF3 (ℓ - 1) M hFunr hM3 hFab hFexp hm T
    hTprime hTsplit C₀ hshafT hnum
  -- ## 9. the root discriminant of `F`
  have hrdF : NumberField.rootDiscr F = Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ)) :=
    rootDiscr_eq_exp r (fun i => (hr i).pos) hF3 hFdisc
  have hCF : 2 * NumberField.rootDiscr F ≤ C := by
    have h1 : (1 : ℝ) ≤ Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ)) := by
      rw [← hrdF]
      exact Work.one_le_rootDiscr F
    rw [hCdef, max_eq_right (by linarith : (1 : ℝ) ≤
      2 * Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ)))]
    linarith [hrdF.le]
  -- ## 10. conclusion: the CM field `K = L(i)`
  refine ⟨t, q, C, ht, hq, hqi, hq4, hC1, hnumC, fun N₀ => ?_⟩
  obtain ⟨L, hLF, hLN, hLA, hLfin, hLgal, hLdeg, hLunr, hL3, hLsplit⟩ := htower (2 * N₀)
  letI : Field L := hLF
  letI : NumberField L := hLN
  letI : Algebra F L := hLA
  letI : FiniteDimensional F L := hLfin
  letI : IsGalois F L := hLgal
  haveI : NumberField.IsTotallyReal L :=
    Work.Tower.isTotallyReal_of_isPGroup_three_unramified hFTR hLunr hL3
  have hqL : ∀ b, Work.Defs.SplitsCompletely (q b) L := by
    intro b
    refine (Work.Tower.splitsCompletely_iff_relative (F := F) (L := L) (q b) (hq b)).mpr
      ⟨hsplitFkeep b, ?_⟩
    intro 𝔭 h𝔭 hmem
    obtain ⟨i, hi⟩ := eq_witness_of_mem_splits (q b) (hq b) (𝔮 b) (h𝔮prime b) (h𝔮mem b)
      (h𝔮prod b) 𝔭 h𝔭 hmem
    have hmemT : 𝔮 b i ∈ T :=
      Finset.mem_image.mpr ⟨(b, i), Finset.mem_univ _, rfl⟩
    rw [← hi]
    exact hLsplit (𝔮 b i) hmemT
  obtain ⟨K, hKF, hKN, hKAlg, hKtow, hKCM, _hK2, hKdeg, hKrd, hKsplit⟩ :=
    Work.Tower.exists_cm_adjoin L inferInstance
  letI : Field K := hKF
  letI : NumberField K := hKN
  letI : Algebra L K := hKAlg
  letI : IsScalarTower ℚ L K := hKtow
  letI : NumberField.IsCMField K := hKCM
  have hrdL : NumberField.rootDiscr L = NumberField.rootDiscr F :=
    Work.Tower.rootDiscr_eq_of_isUnramifiedExtension hLunr
  refine ⟨K, hKF, hKN, hKCM, ?_, ?_, ?_⟩
  · rw [hKdeg]; omega
  · rw [hrdL] at hKrd; linarith
  · intro b
    exact hKsplit (q b) (hq b) (hq4 b) (hqL b)

end Work.Tower.AssemblyProP

namespace Work.Tower.AssemblyProP

open Work.Tower.Assembly (three_not_dvd_prod isPGroup_three_of_exp rootDiscr_eq_exp eq_witness_of_mem_splits)

theorem exists_tower_intermediateField_pos
    (hbase : ∀ (ℓ : ℕ) (_ : 0 < ℓ) (r : Fin ℓ → ℕ), (∀ i, Nat.Prime (r i)) →
      (∀ i, r i % 3 = 1) → Function.Injective r →
      ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra ℚ M) (_ : IsGalois ℚ M)
        (F : IntermediateField ℚ M),
        Module.finrank ℚ ↥F = 3 ∧ IsGalois ℚ ↥F ∧ NumberField.IsTotallyReal ↥F ∧
        IsAbelianGalois ↥F M ∧ Module.finrank ↥F M = 3 ^ (ℓ - 1) ∧
        (∀ σ : Gal(M/↥F), σ ^ 3 = 1) ∧ Work.Tower.IsUnramifiedExtension ↥F M ∧
        |NumberField.discr ↥F| = ((∏ i, r i : ℕ) : ℤ) ^ 2)
    (hshaf : ∃ C₀ : ℕ,
      ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
        Module.finrank ℚ F = 3 →
        ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K],
          Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
          ∀ (T : Finset (Ideal (NumberField.RingOfIntegers F))), (∀ 𝔭 ∈ T, 𝔭.IsPrime) →
            (∀ 𝔭 ∈ T, ∀ (L : Type) [Field L] [NumberField L] [Algebra F L]
               [FiniteDimensional F L] [IsGalois F L],
               Work.Tower.IsUnramifiedExtension F L → IsAbelianGalois F L →
               (∀ σ : Gal(L/F), σ ^ 3 = 1) → Work.Tower.SplitsCompletelyIn F L 𝔭) →
            (∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
               [IsGalois F L],
               Work.Tower.IsUnramifiedExtension F L → IsPGroup 3 (Gal(L/F)) →
               (∀ 𝔭 ∈ T, Work.Tower.SplitsCompletelyIn F L 𝔭) → ∃ (φ : L →ₐ[F] K), True) →
            Work.Tower.Shafarevich.proPRelationRank 3 (Gal(K/F)) ≤
              Work.Tower.generatorRank (Gal(K/F)) + C₀ + T.card) :
    ∀ (H : ℝ), 0 < H →
    ∃ (t : ℕ) (q : Fin t → ℕ) (C : ℝ), 0 < t ∧ (∀ b, Nat.Prime (q b)) ∧
      Function.Injective q ∧ (∀ b, q b % 4 = 1) ∧ 1 ≤ C ∧
      (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsCMField K),
        N ≤ Module.finrank ℚ K ∧ NumberField.rootDiscr K ≤ C ∧
        (∀ b, Work.Defs.SplitsCompletely (q b) K) := by
  refine exists_tower_of_base_and_shafarevich_pos ?_ hshaf
  intro ℓ hℓ r hr hr3 hrinj
  obtain ⟨M, hMF, hMN, hMA, hMG, F, hF3, hFgal, hFTR, hFab, hFMdeg, hFexp,
    hFunr, hFdisc⟩ := hbase ℓ hℓ r hr hr3 hrinj
  letI : Field M := hMF
  letI : NumberField M := hMN
  letI : Algebra ℚ M := hMA
  letI : IsGalois ℚ M := hMG
  -- The bridge: package the `IntermediateField` data as the bare-type data, taking `F` to be
  -- the carrier `↥F` of the intermediate field.
  refine ⟨↥F, inferInstance, inferInstance, hFTR, hFgal, M, inferInstance, inferInstance,
    inferInstance, ?_, hFab.toIsGalois, ?_, hFab, hFMdeg, hFexp, hFunr, hFdisc⟩
  · -- `FiniteDimensional ↥F M`, from `Module.finrank ↥F M = 3 ^ (ℓ - 1) > 0`.
    exact Module.finite_of_finrank_pos (by rw [hFMdeg]; positivity)
  · -- the transfer of `Module.finrank ℚ ↥F` between the two canonical module structures
    refine Eq.trans ?_ hF3
    refine Assembly.finrank_congr_of_smul _ _ _ _ ?_
    intro q a
    apply Subtype.ext
    rw [Algebra.smul_def]
    simp only [IntermediateField.coe_mul]
    rw [Assembly.coe_algebraMap_eq F _ q, IntermediateField.coe_smul, Algebra.smul_def]

end Work.Tower.AssemblyProP
