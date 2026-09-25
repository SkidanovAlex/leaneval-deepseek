import Submission.Work.Tower.Assembly.Setup
import Submission.Work.Tower.Assembly.Primes
import Submission.Work.Tower.Assembly.Analysis
import Submission.Work.Tower.Unramified.All
import Submission.Work.Tower.Glue.ElemAb
import Submission.Work.Tower.Glue.exists_galois_closure_split
import Submission.Work.Tower.FrattiniLayer.Main
import Submission.Work.Tower.TowerCut.Main
import Submission.Work.Tower.CMAdjoin.Main

/-!
# The final assembly of `Work.Interface.exists_tower`

From the two remaining inputs — the cyclotomic base of the tower (area `Tower/CyclotomicBase`)
and Šafarevič's relation-rank estimate (area `Tower/Shafarevich`) — together with the already
proved areas, we derive the statement of `Work.Interface.exists_tower`.

## Shape of the base interface (and why it is *not* literally the `IntermediateField` form)

The deliverable asks for a hypothesis

```
∃ (M : Type) … (F : IntermediateField ℚ M),
  Module.finrank ℚ ↥F = 3 ∧ IsGalois ℚ ↥F ∧ NumberField.IsTotallyReal ↥F ∧ …
```

Such a hypothesis cannot be fed directly to the tower argument, for a purely type-class reason
which we record here since it arises for every consumer of the base interface.
For `F : IntermediateField ℚ M` there are two canonical `ℚ`-module structures on the carrier
`↥F`:

* `IntermediateField.module'`, the restriction of the `ℚ`-module structure of `M` along the
  inclusion, whose `SMul` is the restricted one, and
* `Algebra.toModule` for `Algebra ℚ ↥F` (equivalently, `F.algebra'.toModule`), whose `SMul` is
  `q • x = algebraMap ℚ ↥F q * x`.

They are equal as *functions* (`Algebra.smul_def` and the compatibility of `algebraMap` with the
inclusion) but **not definitionally equal**: the first is a restricted scalar action, the second
is a multiplication.  Type-class resolution picks one or the other depending on the surrounding
context, and `Module.finrank ℚ ↥F`, `Work.Defs.SplitsCompletely (q) ↥F` (whose index type is
`Fin (Module.finrank ℚ ↥F)`) and `Module.finrank ↥F M` then disagree on *syntactically* which
instance they use, so that e.g. the index type of a splitting witness cannot be passed to the
corresponding use site.

The fix (checked in this Lean version, and the reason the statement below looks slightly
different from the draft) is to state the interface for a **bare type** `F` carrying the
type-class data as ordinary binders, and to view the field `M` of the tower as an `F`-algebra
sitting above it.  Then every `Module.finrank ℚ F` in the statement and at every use site is
resolved by the *same* local instance, and all the already proved areas apply verbatim (they all
take bare types: `Work.Tower.exists_frattini_layer`, `Work.Tower.Glue.exists_galois_closure_split`,
`Work.Tower.unramified_tower_gs`, `Work.Tower.exists_cm_adjoin`, …).

Concretely, the hypothesis `hbase` below is what the area `Tower/CyclotomicBase` can deliver:
from its natural `IntermediateField` construction (`F := ↥(FMfield r hr hr3)`,
`M := ↥(Mfield r hr hr3)`) one supplies the instances `Field ↥F`, `NumberField ↥F`,
`Algebra ↥F ↥M` (the inclusion), `FiniteDimensional ↥F ↥M` (from
`Module.finrank ↥F ↥M = 3 ^ (ℓ - 1)` via `Module.finite_of_finrank_pos`) and `IsGalois ↥F ↥M`
(from `IsAbelianGalois`), and, for the degree-three condition, any `NumberField ↥F` instance
together with the transfer `Work.Tower.Assembly.finrank_congr_of_smul` of
`Submission/Work/Tower/Assembly/exists_tower_intermediateField.lean`.

That module also proves the `IntermediateField` form of the theorem itself,
`Work.Tower.Assembly.exists_tower_intermediateField`, whose hypothesis `hbase` is *verbatim*
`Work.Tower.Assembly.BaseInterface` (`Submission/Work/Tower/Assembly/Setup.lean`) and which
follows from the theorem below by the bridge just described.  So both shapes of the base
interface are available: use `exists_tower_intermediateField` with `BaseInterface`, or this
theorem with the bare-type interface `Work.Tower.Assembly.PackagedBaseInterface`.

`hshaf` is kept verbatim: it takes `T` explicitly (together with the Frattini condition on `T`
*and* the maximality condition), which is the shape `Tower/Shafarevich` delivers — indeed its
two clauses are *definitionally* `Work.Tower.Shafarevich.IsFrobeniusTrivialInFrattini F T` and
`Work.Tower.Shafarevich.IsMaximalSplittingExtension F K T`.  The adaptation to the shape expected
by `Work.Tower.unramified_tower_gs` (which has already fixed `T`) is done locally in the proof of
the main theorem below (`hshafT`).

## The mathematical skeleton

1. `Work.Tower.Glue.exists_tower_params H hH C₀` produces `ℓ`, the primes `rᵢ ≡ 1 (mod 3)`, `t`,
   `C = max 1 (2 exp ((2/3) ∑ log rᵢ))` with `(H C (1 + log C))² < 2^t` and
   `4((ℓ-1) + C₀ + 3t) < (ℓ-1)²`.
2. `hbase` gives the cubic totally real field `F` with `|disc F| = (∏ rᵢ)²` and the
   everywhere unramified elementary abelian `3`-extension `M/F` of degree `3^(ℓ-1)`.
3. `3 ∤ disc F`, so `Work.Tower.exists_frattini_layer` gives the Frattini layer `E/F`.
4. `Work.Tower.Glue.exists_galois_closure_split` embeds `E` into a finite Galois `N/ℚ` with
   splitting descent.
5. `Work.Tower.Assembly.exists_primes_split` produces `t` primes `q b ≡ 1 (mod 4)` splitting
   completely in `N`, hence in `E` and in `F`.
6. `Work.Tower.splitsCompletely_iff_relative` turns this into relative splitting, and `T` is the
   (at most `3t`) set of primes of `F` above the `q b`.
7. Frattini condition for `T`: an everywhere unramified elementary abelian `3`-extension of `F`
   embeds into `E`; complete splitting then descends along the embedding.
8. `Work.Tower.unramified_tower_gs`, applied to `M` (which has generator rank `≥ ℓ-1`), produces
   for every `N` an everywhere unramified Galois `3`-extension `L/F` of degree `≥ N` in which
   every prime of `T` splits completely.
9. `L` is totally real and `rootDiscr L = rootDiscr F`; the `q b` split completely in `L`.
10. `Work.Tower.exists_cm_adjoin` gives the CM field `K = L(i)`, and
    `2 rootDiscr F = 2 exp ((2/3) ∑ log rᵢ) ≤ C`.
-/

set_option linter.style.haveILetI false

open NumberField
open scoped Classical nonZeroDivisors IsMulCommutative

namespace Work
namespace Tower
namespace Assembly

/-- The primes above a completely split rational prime are exactly the ones exhibited by the
splitting witness. -/
theorem eq_witness_of_mem_splits {F : Type*} [Field F] [NumberField F] (q : ℕ) (hq : Nat.Prime q)
    {n : ℕ} (𝔮 : Fin n → Ideal (𝓞 F)) (h𝔮prime : ∀ i, (𝔮 i).IsPrime)
    (h𝔮mem : ∀ i, ((q : ℕ) : 𝓞 F) ∈ 𝔮 i)
    (h𝔮prod : Ideal.span {((q : ℕ) : 𝓞 F)} = ∏ i, 𝔮 i)
    (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsPrime) (hmem : ((q : ℕ) : 𝓞 F) ∈ 𝔭) :
    ∃ i, 𝔮 i = 𝔭 := by
  have hprod : ∏ i, 𝔮 i ≤ 𝔭 := by
    rw [← h𝔮prod]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  obtain ⟨i, -, hi⟩ := (h𝔭.prod_le).mp hprod
  have hne_bot : 𝔮 i ≠ ⊥ := by
    intro hbot
    have h0 : ((q : ℕ) : 𝓞 F) = 0 := by simpa [hbot] using h𝔮mem i
    exact hq.ne_zero (Nat.cast_eq_zero.mp h0)
  exact ⟨i, Ideal.IsMaximal.eq_of_le ((h𝔮prime i).isMaximal hne_bot) h𝔭.ne_top hi⟩

/-- **Final assembly.**  From the base interface `hbase` (the cubic base field and its
everywhere-unramified elementary abelian `3`-extension `M/F` of degree `3^(ℓ-1)`) and
Šafarevič's relation-rank estimate `hshaf`, conclude the statement of
`Work.Interface.exists_tower`.

The shape of `hbase` is that of the `IntermediateField` interface with `F` replaced by a bare
type carrying its own type-class data; see the module docstring for why this is forced. -/
theorem exists_tower_of_base_and_shafarevich
    (hbase : ∀ (ℓ : ℕ) (r : Fin ℓ → ℕ), (∀ i, Nat.Prime (r i)) → (∀ i, r i % 3 = 1) →
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
            Work.Tower.relationRankWith (Gal(K/F)) (Work.Tower.generatorRank (Gal(K/F))) ≤
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
  obtain ⟨ℓ, r, t, C, hr, hrinj, hr3, _hℓpos, ht, hC1, hCdef, hnumC, hnumℓ⟩ :=
    Glue.exists_tower_params H hH C₀
  -- ## 1. the base field
  obtain ⟨F, hFF, hFN, hFTR, hFgal, M, hMF, hMN, hFM, hFMD, hFMG,
    hF3, hFab, hFMdeg, hFexp, hFunr, hFdisc⟩ := hbase ℓ r hr hr3 hrinj
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
      Work.Tower.relationRankWith (Gal(K/F)) (Work.Tower.generatorRank (Gal(K/F))) ≤
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
  obtain htower := Work.Tower.unramified_tower_gs F hF3 (ℓ - 1) M hFunr hM3 hFab hFexp hm T
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

end Assembly
end Tower
end Work
